import argparse
import json
import os
import re
import shutil
import tempfile
import time
import urllib.error
import urllib.request
from datetime import datetime, timedelta, timezone
from patchright.sync_api import sync_playwright, TimeoutError as PlaywrightTimeoutError

# --- CONFIGURATION ---
BMS_URL = (
    "https://in.bookmyshow.com/movies/chennai/avengers-doomsday/buytickets/"
    "ET00526312/20261217?etCodes=ET00526312&language=tamil&refEventCode=ET00526312"
)

DISTRICT_URL = (
    "https://www.district.in/movies/avengers-doomsday-movie-tickets-in-chennai-MV176735"
    "?frmtid=chjP5dFQh1"
)

TARGET_THEATRES = {
    "Kamala Cinemas, Vadapalani": ["kamala cinemas", "kamala: vadapalani"],
    "Devi Cineplex, Anna Salai": ["devi cineplex", "devi: anna salai", "devi, anna salai"],
    "Kasi Theatre, Ashok Nagar": ["kasi rgb", "kasi theatre", "kasi talkies"],
    "Vettri Theatres, Chrompet": ["vettri"],
    "PVR Grand Galada Mall, Pallavaram": ["grand galada"],
    "PVR Aerohub, Airport": ["aerohub"],
    "PVR Grand Mall, Velachery": ["grand mall"],
    "INOX Phoenix Market City, Velachery": ["phoenix market", "jazz cinemas"],
    "PVR Palazzo, Nexus Vijaya Mall": ["palazzo", "nexus vijaya"],
    "PVR VR Mall, Anna Nagar": ["vr mall", "vr chennai"],
    "PVR Sathyam, Royapettah": ["sathyam"],
}

BLOCK_INDICATORS = [
    "just a moment",
    "verify you are human",
    "attention required",
    "access denied",
    "enable javascript and cookies to continue",
    "cloudflare",
]

# --- BROWSER DOM HELPERS ---
EXTRACT_BMS_DATES_JS = r"""
() => {
  const DATE_RE = /^(MON|TUE|WED|THU|FRI|SAT|SUN)\s+(\d{1,2})\s+(JAN|FEB|MAR|APR|MAY|JUN|JUL|AUG|SEP|OCT|NOV|DEC)$/i;
  const parseRgb = (str) => {
    const m = (str || '').match(/rgba?\((\d+),\s*(\d+),\s*(\d+)(?:,\s*([\d.]+))?\)/i);
    if (!m) return null;
    return { r: +m[1], g: +m[2], b: +m[3], a: m[4] !== undefined ? +m[4] : 1 };
  };

  const candidates = [];
  for (const el of document.querySelectorAll('a, button, div, li')) {
    const rect = el.getBoundingClientRect();
    if (rect.top < 80 || rect.top > 460 || rect.width < 24 || rect.width > 125 || rect.height < 30 || rect.height > 125) continue;
    const txt = (el.innerText || '').replace(/\s+/g, ' ').trim();
    const m = txt.match(DATE_RE);
    if (!m) continue;
    const childHasDate = Array.from(el.children).some(
      ch => DATE_RE.test((ch.innerText || '').replace(/\s+/g, ' ').trim())
    );
    if (childHasDate) continue;
    candidates.push({ el, rect, dow: m[1], day: m[2], month: m[3] });
  }

  candidates.sort((a, b) => a.rect.left - b.rect.left);

  const seen = new Set();
  const dates = [];
  for (const item of candidates) {
    const key = `${item.day}-${item.month.toUpperCase()}`;
    if (seen.has(key)) continue;
    seen.add(key);

    const style = window.getComputedStyle(item.el);
    const link = item.el.closest('a[href]');
    const bg = parseRgb(style.backgroundColor);
    const isSelected = Boolean(bg && bg.a > 0.5 && bg.r > 170 && bg.g < 100 && bg.b < 120);

    const dayNode = Array.from(item.el.querySelectorAll('*')).find(
      n => n.children.length === 0 && (n.innerText || '').trim() === item.day
    ) || item.el;
    const dayStyle = window.getComputedStyle(dayNode);
    const fg = parseRgb(dayStyle.color);
    const opacity = Math.min(parseFloat(style.opacity || '1'), parseFloat(dayStyle.opacity || '1'));

    const pointerBlocked = style.pointerEvents === 'none' || dayStyle.pointerEvents === 'none';
    const ariaDisabled = item.el.getAttribute('aria-disabled') === 'true' || item.el.hasAttribute('disabled');
    const isGreyedOut = Boolean(
      !isSelected && fg &&
      fg.r >= 115 && fg.g >= 115 && fg.b >= 115 &&
      (Math.max(fg.r, fg.g, fg.b) - Math.min(fg.r, fg.g, fg.b) < 25)
    );

    const enabled = isSelected || (!pointerBlocked && !ariaDisabled && opacity >= 0.7 && !isGreyedOut);
    const monthCap = item.month.charAt(0).toUpperCase() + item.month.slice(1).toLowerCase();
    const dowCap = item.dow.charAt(0).toUpperCase() + item.dow.slice(1).toLowerCase();

    dates.push({
      label: `${item.day} ${monthCap} (${dowCap})`,
      short: `${item.day} ${monthCap}`,
      day: item.day,
      dow: item.dow,
      month: item.month,
      selected: isSelected,
      enabled: enabled,
      href: link ? link.href : '',
    });
  }
  return dates;
}
"""

EXTRACT_DISTRICT_DATES_JS = r"""
() => {
  const DATE_RE = /^(\d{1,2})\s+(Mon|Tue|Wed|Thu|Fri|Sat|Sun)$/i;
  const MONTH_RE = /^(JAN|FEB|MAR|APR|MAY|JUN|JUL|AUG|SEP|OCT|NOV|DEC)$/i;
  const parseRgb = (str) => {
    const m = (str || '').match(/rgba?\((\d+),\s*(\d+),\s*(\d+)(?:,\s*([\d.]+))?\)/i);
    if (!m) return null;
    return { r: +m[1], g: +m[2], b: +m[3], a: m[4] !== undefined ? +m[4] : 1 };
  };

  const months = [];
  for (const el of document.querySelectorAll('div, span, p')) {
    const rect = el.getBoundingClientRect();
    if (rect.top < 80 || rect.top > 460 || rect.width > 100 || rect.height > 100) continue;
    const txt = (el.innerText || '').trim();
    if (MONTH_RE.test(txt) && el.children.length === 0) {
      months.push({ text: txt, left: rect.left });
    }
  }
  months.sort((a, b) => a.left - b.left);

  const candidates = [];
  for (const el of document.querySelectorAll('a, button, div, li')) {
    const rect = el.getBoundingClientRect();
    if (rect.top < 80 || rect.top > 460 || rect.width < 20 || rect.width > 125 || rect.height < 25 || rect.height > 125) continue;
    const txt = (el.innerText || '').replace(/\s+/g, ' ').trim();
    const m = txt.match(DATE_RE);
    if (!m) continue;
    const childHasDate = Array.from(el.children).some(
      ch => DATE_RE.test((ch.innerText || '').replace(/\s+/g, ' ').trim())
    );
    if (childHasDate) continue;
    candidates.push({ el, rect, day: m[1], dow: m[2] });
  }

  candidates.sort((a, b) => a.rect.left - b.rect.left);

  const seen = new Set();
  const dates = [];
  for (const item of candidates) {
    const key = `${item.day}-${item.dow.toUpperCase()}`;
    if (seen.has(key)) continue;
    seen.add(key);

    const style = window.getComputedStyle(item.el);
    const bg = parseRgb(style.backgroundColor);
    const isSelected = Boolean(bg && bg.a > 0.5 && bg.r < 60 && bg.g < 60 && bg.b < 60);
    const disabled =
      style.pointerEvents === 'none' ||
      item.el.getAttribute('aria-disabled') === 'true' ||
      item.el.hasAttribute('disabled') ||
      parseFloat(style.opacity || '1') < 0.6;

    let monthTxt = '';
    for (const mo of months) {
      if (mo.left <= item.rect.left + 15) monthTxt = mo.text;
    }
    const monthCap = monthTxt ? (monthTxt.charAt(0).toUpperCase() + monthTxt.slice(1).toLowerCase()) : '';
    const dowCap = item.dow.charAt(0).toUpperCase() + item.dow.slice(1).toLowerCase();
    const shortLabel = monthCap ? `${item.day} ${monthCap}` : `${item.day} ${dowCap}`;
    const fullLabel = monthCap ? `${item.day} ${monthCap} (${dowCap})` : `${item.day} ${dowCap}`;

    dates.push({
      label: fullLabel,
      short: shortLabel,
      day: item.day,
      dow: item.dow,
      month: monthCap,
      selected: isSelected,
      enabled: !disabled,
      href: item.el.closest('a[href]') ? item.el.closest('a[href]').href : '',
    });
  }
  return dates;
}
"""

CLICK_DATE_PILL_JS = r"""
({ site, day, dow, month }) => {
  const bmsTarget = `${dow} ${day} ${month}`.toLowerCase();
  const distTarget = `${day} ${dow}`.toLowerCase();

  for (const el of document.querySelectorAll('a, button, div, li')) {
    const rect = el.getBoundingClientRect();
    if (rect.top < 80 || rect.top > 460 || rect.width < 20 || rect.width > 125 || rect.height < 25 || rect.height > 125) continue;
    const txt = (el.innerText || '').replace(/\s+/g, ' ').trim().toLowerCase();
    const target = site === 'BookMyShow' ? bmsTarget : distTarget;
    if (txt !== target) continue;

    const childMatches = Array.from(el.children).some(
      ch => (ch.innerText || '').replace(/\s+/g, ' ').trim().toLowerCase() === target
    );
    if (childMatches) continue;

    el.click();
    return true;
  }
  return false;
}
"""

EXTRACT_SHOWTIME_CARDS_JS = r"""
() => {
  const TIME_RE = /\b(0?[1-9]|1[0-2]):[0-5]\d\s*(AM|PM)\b/i;
  const TIME_GLOBAL_RE = /\b(0?[1-9]|1[0-2]):[0-5]\d\s*(AM|PM)\b/gi;
  const STOP_BOUNDARY_RE = /(Top Cinemas in Chennai|Frequently Asked|What languages is|Movies Now Showing in Chennai|Advance bookings open|Early morning show)/i;

  const isHeaderBeforeTime = (text) => {
    const lines = text.split('\n').map(s => s.trim()).filter(Boolean);
    for (const line of lines) {
      if (TIME_RE.test(line)) return false;
      if (line.length >= 5) return true;
    }
    return false;
  };

  const allEls = Array.from(document.querySelectorAll('a, button, div, span, li'));
  const timeSlots = allEls.filter(el => {
    const txt = (el.innerText || '').trim();
    if (!txt || txt.length > 70) return false;
    const matches = txt.match(TIME_GLOBAL_RE) || [];
    if (matches.length !== 1) return false;
    const childHasTime = Array.from(el.children).some(ch => TIME_RE.test(ch.innerText || ''));
    if (childHasTime) return false;
    const rect = el.getBoundingClientRect();
    return rect.width > 0 && rect.height > 0;
  });

  const cardSet = new Set();
  for (const slot of timeSlots) {
    let cur = slot.parentElement;
    let bestCard = null;
    for (let depth = 0; depth < 12 && cur && cur !== document.body; depth++) {
      const txt = (cur.innerText || '').trim();
      if (!txt || txt.length > 2500 || STOP_BOUNDARY_RE.test(txt)) break;

      const theatreChildren = Array.from(cur.children).filter(ch => {
        const ctxt = (ch.innerText || '').trim();
        return TIME_RE.test(ctxt) && isHeaderBeforeTime(ctxt);
      });
      if (theatreChildren.length >= 2) break;

      if (isHeaderBeforeTime(txt)) {
        bestCard = cur;
      }
      cur = cur.parentElement;
    }
    if (bestCard) cardSet.add(bestCard);
  }

  const uniqueCards = Array.from(cardSet).filter(card =>
    !Array.from(cardSet).some(other => other !== card && other.contains(card))
  );

  const seenHeaders = new Set();
  const results = [];
  for (const card of uniqueCards) {
    const raw = (card.innerText || '').trim();
    const times = Array.from(new Set(raw.match(TIME_GLOBAL_RE) || []));
    const lines = raw.split('\n').map(s => s.trim()).filter(Boolean);
    const headerLines = [];
    for (const line of lines) {
      if (TIME_RE.test(line)) break;
      if (!/^(INFO|M-Ticket|Food & Beverage|Allows cancellation|Non-cancellable|Cancellation available)$/i.test(line)) {
        headerLines.push(line);
      }
      if (headerLines.length >= 2) break;
    }
    const theatreName = (headerLines[0] || lines[0] || '').trim();
    const key = theatreName.toLowerCase();
    if (theatreName && times.length > 0 && !seenHeaders.has(key)) {
      seenHeaders.add(key);
      results.push({
        theatre: theatreName,
        meta: headerLines.slice(1).join(' | '),
        times: times,
      });
    }
  }
  return results;
}
"""

IST = timezone(timedelta(hours=5, minutes=30))
IS_CI = os.getenv("CI", "").lower() == "true"
TELEGRAM_BOT_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN", "").strip()
TELEGRAM_CHAT_ID = os.getenv("TELEGRAM_CHAT_ID", "").strip()
SCREENSHOT_DIR = "screenshots"
STATE_FILE = "state.json"
FORCE_ALERT = os.getenv("FORCE_ALERT", "false").lower() == "true"


def now_ist() -> str:
    return datetime.now(IST).strftime("%d-%b-%Y %I:%M:%S %p IST")


def log(msg: str) -> None:
    print(msg, flush=True)


def load_alerted_state() -> set[str]:
    if not os.path.exists(STATE_FILE):
        return set()
    try:
        with open(STATE_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        return set(data.get("alerted", []))
    except Exception:
        return set()


def save_alerted_state(alerted: set[str]) -> None:
    with open(STATE_FILE, "w", encoding="utf-8") as f:
        json.dump({"alerted": sorted(alerted)}, f, indent=2)


def send_telegram_alert(message: str) -> bool:
    if not TELEGRAM_BOT_TOKEN or not TELEGRAM_CHAT_ID:
        log("[INFO] Telegram secrets not set — skipping Telegram notification.")
        return False

    api_url = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage"

    # Split safely if message exceeds Telegram's 4096-character limit
    chunks, current = [], ""
    for line in message.splitlines(keepends=True):
        if len(current) + len(line) > 3900:
            chunks.append(current)
            current = line
        else:
            current += line
    if current:
        chunks.append(current)

    all_ok = True
    for chunk in chunks:
        payload = json.dumps({
            "chat_id": TELEGRAM_CHAT_ID,
            "text": chunk,
            "disable_web_page_preview": True,
        }).encode("utf-8")
        req = urllib.request.Request(
            api_url,
            data=payload,
            headers={"Content-Type": "application/json"},
        )
        try:
            with urllib.request.urlopen(req, timeout=15) as resp:
                if resp.status == 200:
                    log("[OK] Telegram alert sent.")
                else:
                    log(f"[WARN] Telegram returned HTTP {resp.status}")
                    all_ok = False
        except urllib.error.HTTPError as exc:
            err_body = exc.read().decode("utf-8", errors="ignore")
            log(f"[ERROR] Telegram API HTTP {exc.code}: {err_body}")
            all_ok = False
        except Exception as exc:
            log(f"[ERROR] Failed to send Telegram alert: {exc}")
            all_ok = False

    return all_ok


def is_blocked_content(title: str, body_text: str) -> bool:
    lower_title = (title or "").lower()
    lower_body = (body_text or "").lower()
    return any(flag in lower_body or flag in lower_title for flag in BLOCK_INDICATORS)


def wait_past_cloudflare(page, max_wait_sec: int = 14) -> tuple[str, str]:
    """Wait briefly in case a Cloudflare JS challenge resolves on its own."""
    for _ in range(max_wait_sec // 2):
        title = page.title()
        try:
            raw_text = page.inner_text("body")
        except Exception:
            raw_text = ""
        if not is_blocked_content(title, raw_text):
            return title, raw_text
        page.wait_for_timeout(2000)

    try:
        return page.title(), page.inner_text("body")
    except Exception:
        return page.title(), ""


def match_target_theatres(cards: list[dict]) -> dict[str, dict]:
    matches: dict[str, dict] = {}
    for card in cards:
        theatre_lower = f"{card['theatre']} {card.get('meta', '')}".lower()
        for display_name, keywords in TARGET_THEATRES.items():
            if display_name in matches:
                continue
            if any(kw in theatre_lower for kw in keywords):
                matches[display_name] = card
    return matches


def scroll_to_load_all(page) -> None:
    """Scroll down briefly to trigger lazy-loaded theatre cards, then return to top."""
    for y in (700, 1400, 2100):
        page.evaluate(f"window.scrollTo(0, {y})")
        page.wait_for_timeout(300)
    page.evaluate("window.scrollTo(0, 0)")
    page.wait_for_timeout(350)


def save_debug_screenshot(page, prefix: str, date_tag: str) -> str:
    if IS_CI:
        return ""
    os.makedirs(SCREENSHOT_DIR, exist_ok=True)
    safe_tag = re.sub(r"[^A-Za-z0-9]+", "_", date_tag).strip("_")
    abs_path = os.path.abspath(os.path.join(SCREENSHOT_DIR, f"{prefix}_{safe_tag}.png"))
    try:
        page.evaluate("window.scrollTo(0, 0)")
        page.wait_for_timeout(300)
        page.screenshot(path=abs_path, full_page=False)
        return abs_path
    except Exception as exc:
        log(f"    -> Could not save screenshot ({safe_tag}): {exc}")
        return ""


def handle_district_language_popup(page) -> None:
    prompt_heading = page.get_by_text("Choose preferred language", exact=False).first
    try:
        prompt_heading.wait_for(state="visible", timeout=4500)
        log("  -> Language popup detected on District; selecting Tamil...")
        modal = (
            page.locator("div")
            .filter(has_text="Choose preferred language")
            .filter(has_text="Proceed")
            .last
        )
        modal.get_by_text("Tamil", exact=True).first.click(timeout=5000)
        page.wait_for_timeout(500)
        proceed_btn = modal.get_by_role("button", name=re.compile(r"proceed", re.I)).first
        if proceed_btn.count() > 0:
            proceed_btn.click(timeout=5000)
        else:
            modal.get_by_text("Proceed", exact=True).first.click(timeout=5000)

        prompt_heading.wait_for(state="hidden", timeout=10000)
        page.wait_for_timeout(3500)
        log("  -> Language set to Tamil.")
    except PlaywrightTimeoutError:
        log("  -> Tamil loaded directly (no language popup).")
    except Exception as exc:
        log(f"  -> [WARN] Popup handling note: {exc}")


def check_site_all_dates(page, site_name: str, url: str, ss_prefix: str) -> dict:
    log(f"\n[{site_name}] Loading initial page...")
    result = {
        "site": site_name,
        "url": url,
        "status": "ERROR",
        "opened_dates": [],
        "by_date": {},
        "theatre_dates": {},
        "screenshots": [],
        "note": "",
    }

    try:
        response = page.goto(url, wait_until="domcontentloaded", timeout=45000)
        http_status = response.status if response else "unknown"
        log(f"  -> HTTP status: {http_status}")
        page.wait_for_timeout(4000)

        title, raw_text = wait_past_cloudflare(page)
        log(f"  -> Page title: {title}")

        if is_blocked_content(title, raw_text):
            result["status"] = "BLOCKED"
            result["note"] = "Anti-bot / Cloudflare challenge detected"
            log(f"  -> [BLOCKED] {result['note']}")
            ss = save_debug_screenshot(page, ss_prefix, "blocked")
            if ss:
                result["screenshots"].append(ss)
            return result

        if site_name == "Zomato District":
            handle_district_language_popup(page)
            result["url"] = page.url

        page.evaluate("window.scrollTo(0, 0)")
        page.wait_for_timeout(300)
        if site_name == "BookMyShow":
            discovered = page.evaluate(EXTRACT_BMS_DATES_JS)
        else:
            discovered = page.evaluate(EXTRACT_DISTRICT_DATES_JS)

        opened_dates = [d for d in discovered if d.get("enabled")]
        disabled_dates = [d["short"] for d in discovered if not d.get("enabled")]

        if not opened_dates:
            log("  -> Could not parse date bar; scanning current page as default date.")
            opened_dates = [{
                "label": "Default Date",
                "short": "Default",
                "day": "",
                "dow": "",
                "month": "",
                "selected": True,
                "enabled": True,
                "href": "",
            }]
        else:
            log(f"  -> Opened dates detected ({len(opened_dates)}): {', '.join(d['short'] for d in opened_dates)}")
            if disabled_dates:
                log(f"  -> Unopened/disabled dates skipped: {', '.join(disabled_dates)}")

        result["opened_dates"] = [d["short"] for d in opened_dates]

        for idx, d in enumerate(opened_dates):
            log(f"\n  [{site_name} | {d['label']}]")

            if idx > 0 or not d["selected"]:
                page.evaluate("window.scrollTo(0, 0)")
                page.wait_for_timeout(250)
                prev_url = page.url

                clicked = page.evaluate(
                    CLICK_DATE_PILL_JS,
                    {"site": site_name, "day": d["day"], "dow": d["dow"], "month": d["month"]},
                )

                if clicked:
                    page.wait_for_timeout(3000)
                elif d.get("href"):
                    page.goto(d["href"], wait_until="domcontentloaded", timeout=45000)
                    page.wait_for_timeout(4000)

                if site_name == "BookMyShow" and page.url == prev_url and d.get("href") and d["href"] != prev_url:
                    page.goto(d["href"], wait_until="domcontentloaded", timeout=45000)
                    page.wait_for_timeout(4000)

                if site_name == "BookMyShow" and page.url == prev_url and not d["selected"]:
                    log("    -> Date did not switch (likely not open yet); skipping.")
                    continue

            scroll_to_load_all(page)
            cards = page.evaluate(EXTRACT_SHOWTIME_CARDS_JS)
            hits = match_target_theatres(cards)

            ss = save_debug_screenshot(page, ss_prefix, d["short"])
            if ss:
                result["screenshots"].append(ss)

            result["by_date"][d["short"]] = {
                "label": d["label"],
                "url": page.url,
                "cards": cards,
                "hits": hits,
            }

            log(f"    -> Active open theatres: {len(cards)}")
            for c in cards:
                log(f"         * {c['theatre']} ({len(c['times'])} shows: {', '.join(c['times'][:5])})")

            for theatre_name, card in hits.items():
                result["theatre_dates"].setdefault(theatre_name, {})[d["short"]] = card["times"]

        result["status"] = "OK"
        return result

    except PlaywrightTimeoutError:
        result["status"] = "TIMEOUT"
        result["note"] = "Page timed out after 45s"
        log(f"  -> [TIMEOUT] {result['note']}")
        ss = save_debug_screenshot(page, ss_prefix, "timeout")
        if ss:
            result["screenshots"].append(ss)
        return result

    except Exception as exc:
        result["status"] = "ERROR"
        result["note"] = str(exc)
        log(f"  -> [ERROR] {exc}")
        ss = save_debug_screenshot(page, ss_prefix, "error")
        if ss:
            result["screenshots"].append(ss)
        return result


def format_date_cell(site_res: dict, theatre: str) -> str:
    if site_res["status"] != "OK":
        return site_res["status"]
    dates_map = site_res["theatre_dates"].get(theatre)
    if not dates_map:
        return "Not open"
    return f"OPEN: {', '.join(dates_map.keys())}"


def print_terminal_report(bms: dict, dist: dict) -> None:
    log("\n" + "=" * 96)
    log(f"AVENGERS: DOOMSDAY (CHENNAI - TAMIL - ALL OPENED DATES) — LIVE UPDATE ({now_ist()})")
    log("=" * 96)
    bms_dates_str = ", ".join(bms["opened_dates"]) if bms["opened_dates"] else "None"
    dist_dates_str = ", ".join(dist["opened_dates"]) if dist["opened_dates"] else "None"
    log(f"BookMyShow      : {bms['status']} | Dates checked: {bms_dates_str}" + (f" ({bms['note']})" if bms["note"] else ""))
    log(f"Zomato District : {dist['status']} | Dates checked: {dist_dates_str}" + (f" ({dist['note']})" if dist["note"] else ""))
    log("-" * 96)
    log(f"{'TARGET THEATRE':<38} | {'BOOKMYSHOW':<26} | {'DISTRICT':<26}")
    log("-" * 96)

    matched_theatres = 0
    for theatre in TARGET_THEATRES:
        bms_cell = format_date_cell(bms, theatre)
        dist_cell = format_date_cell(dist, theatre)
        if bms_cell.startswith("OPEN:") or dist_cell.startswith("OPEN:"):
            matched_theatres += 1
        log(f"{theatre:<38} | {bms_cell:<26} | {dist_cell:<26}")

    log("-" * 96)
    if matched_theatres > 0:
        log(f"ALERT: {matched_theatres} target theatre(s) have open bookings!")
        for res in (bms, dist):
            if not res["theatre_dates"]:
                continue
            log(f"\nDetailed Target Openings on {res['site']}:")
            for theatre_name, dates_map in res["theatre_dates"].items():
                log(f"  * {theatre_name}")
                for short_date, times in dates_map.items():
                    log(f"      {short_date}: {', '.join(times)}")
            log(f"  Book here: {res['url']}")
    else:
        log("SUMMARY: None of your 11 target theatres are open on any available date yet.")

    if not IS_CI:
        log(f"\nScreenshots saved in: {os.path.abspath(SCREENSHOT_DIR)}")
        for path in bms["screenshots"] + dist["screenshots"]:
            log(f"  * {os.path.basename(path)}")
    log("=" * 96)


def build_telegram_message(bms: dict, dist: dict, alerted: set[str]) -> tuple[str, set[str]]:
    new_keys = set()
    lines = []

    for res in (bms, dist):
        site_blocks = []
        for theatre_name, dates_map in res["theatre_dates"].items():
            new_dates = []
            for short_date, times in dates_map.items():
                key = f"{res['site']}|{theatre_name}|{short_date}"
                if key not in alerted:
                    new_keys.add(key)
                    new_dates.append(f"  - {short_date}: {', '.join(times)}")
            if new_dates:
                site_blocks.append(f"* {theatre_name}\n" + "\n".join(new_dates))

        if site_blocks:
            lines.append(f"{res['site']}:")
            lines.extend(site_blocks)
            lines.append(f"Book: {res['url']}\n")

    if new_keys:
        header = (
            f"NEW Avengers: Doomsday (Tamil) Tickets OPEN in Chennai!\n"
            f"Checked: {now_ist()}\n\n"
        )
        return header + "\n".join(lines), alerted | new_keys

    # For manual workflow tests, always send a live status summary
    if FORCE_ALERT:
        bms_info = f"{bms['status']}" + (f" ({bms['note']})" if bms["note"] else "")
        dist_info = f"{dist['status']}" + (f" ({dist['note']})" if dist["note"] else "")
        status_lines = [
            f"Bot Test OK ({now_ist()})",
            f"BookMyShow: {bms_info} | Dates: {', '.join(bms['opened_dates']) or 'None'}",
            f"District: {dist_info} | Dates: {', '.join(dist['opened_dates']) or 'None'}",
            "",
            "Currently open from your 11 target theatres:",
        ]
        found_any = False
        for res in (bms, dist):
            for theatre_name, dates_map in res["theatre_dates"].items():
                found_any = True
                status_lines.append(
                    f"- [{res['site']}] {theatre_name}: {', '.join(dates_map.keys())}"
                )
        if not found_any:
            status_lines.append("- None yet.")
        return "\n".join(status_lines), alerted

    return "", alerted


def run_once() -> None:
    log(f"\nStarting multi-date ticket check at {now_ist()}...")
    profile_dir = tempfile.mkdtemp(prefix="patchright_profile_")

    try:
        with sync_playwright() as p:
            context = p.chromium.launch_persistent_context(
                user_data_dir=profile_dir,
                channel="chrome",
                headless=False,
                no_viewport=True,
                args=["--window-size=1366,768"],
                locale="en-IN",
                timezone_id="Asia/Kolkata",
            )
            page = context.pages[0] if context.pages else context.new_page()

            bms_res = check_site_all_dates(page, "BookMyShow", BMS_URL, "bms")
            dist_res = check_site_all_dates(page, "Zomato District", DISTRICT_URL, "district")

            context.close()
    finally:
        shutil.rmtree(profile_dir, ignore_errors=True)

    print_terminal_report(bms_res, dist_res)

    alerted = load_alerted_state()
    tg_message, updated_alerted = build_telegram_message(bms_res, dist_res, alerted)

    if tg_message:
        sent_ok = send_telegram_alert(tg_message)
        if sent_ok and updated_alerted != alerted:
            save_alerted_state(updated_alerted)
            log(f"[OK] Saved {len(updated_alerted)} alerted slot(s) to {STATE_FILE}.")
    else:
        log("[INFO] No new target theatre/date openings since the last alert.")


def main() -> None:
    parser = argparse.ArgumentParser(description="Check Avengers: Doomsday tickets across all opened dates.")
    parser.add_argument(
        "--watch",
        action="store_true",
        help="Keep running in the terminal every 15 minutes until stopped (Ctrl+C).",
    )
    parser.add_argument(
        "--interval",
        type=int,
        default=15,
        help="Minutes between checks when using --watch (default: 15).",
    )
    args = parser.parse_args()

    if not args.watch:
        run_once()
        return

    log(f"Watch mode active — checking every {args.interval} minute(s). Press Ctrl+C to stop.")
    try:
        while True:
            run_once()
            next_time = (datetime.now(IST) + timedelta(minutes=args.interval)).strftime("%I:%M %p IST")
            log(f"\nNext check at {next_time}...")
            time.sleep(args.interval * 60)
    except KeyboardInterrupt:
        log("\nStopped by user.")


if __name__ == "__main__":
    main()
