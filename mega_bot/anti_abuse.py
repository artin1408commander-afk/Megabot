"""
Advanced Anti-Advertisement & Anti-Link engine for MEGA BOT (Bale).

Pure offline heuristics — no external AI APIs.
Designed to resist spaced letters, ZWSP, Arabic/Persian mix, leetspeak,
markdown/uid links, and common Iranian crypto/member-selling spam patterns.
"""
from __future__ import annotations

import re
import unicodedata
from dataclasses import dataclass

# ── Character maps ──────────────────────────────────────────────────────────
_ARABIC_FA = str.maketrans({
    'ي': 'ی', 'ك': 'ک', 'ة': 'ه', 'ؤ': 'و', 'إ': 'ا', 'أ': 'ا', 'آ': 'ا',
    'ۀ': 'ه', 'ە': 'ه', 'ى': 'ی', 'ؤ': 'و',
    '٠': '0', '١': '1', '٢': '2', '٣': '3', '٤': '4',
    '٥': '5', '٦': '6', '٧': '7', '٨': '8', '٩': '9',
    '۰': '0', '۱': '1', '۲': '2', '۳': '3', '۴': '4',
    '۵': '5', '۶': '6', '۷': '7', '۸': '8', '۹': '9',
})

# Lookalike Latin/Cyrillic → ASCII (for domain/link recovery)
_LOOKALIKE = str.maketrans({
    'а': 'a', 'е': 'e', 'о': 'o', 'р': 'p', 'с': 'c', 'у': 'y', 'х': 'x',
    'і': 'i', 'ј': 'j', 'ѕ': 's', 'һ': 'h',
    'Α': 'A', 'Β': 'B', 'Ε': 'E', 'Ζ': 'Z', 'Η': 'H', 'Ι': 'I', 'Κ': 'K',
    'Μ': 'M', 'Ν': 'N', 'Ο': 'O', 'Ρ': 'P', 'Τ': 'T', 'Υ': 'Y', 'Χ': 'X',
    'а': 'a', 'е': 'e', 'о': 'o', 'р': 'p', 'с': 'c', 'у': 'y', 'х': 'x',
})

_INVISIBLE_RE = re.compile(
    r'[\u200b\u200c\u200d\u200e\u200f\u202a-\u202e\u2060-\u2064\u2066-\u2069'
    r'\ufeff\u00ad\u180e\u034f\u061c\u115f\u1160\u17b4\u17b5\u3164\uffa0]'
)
_SEPARATOR_RE = re.compile(
    r'[\s\.\,\;\:\!\?\-\_\=\*\+\~`\'\"«»\(\)\[\]\{\}\|\\\/'
    r'•·‧∙⋅⋯…‥〰〚〛【】（）『』「」\|]+'
)
# tatweel / kashida and combining marks
_TATWEEL_RE = re.compile(r'[\u0640\u06d4]+')
_COMBINING_RE = re.compile(r'[\u0300-\u036f\u0483-\u0489\u0610-\u061a\u064b-\u065f\u0670\u06d6-\u06ed]+')

# Latin letters (strict anti-link policy)
_LATIN_RE = re.compile(r'[A-Za-z]')

# Markdown / uid patterns
_MD_LINK_RE = re.compile(r'\[[^\]]{0,80}\]\(\s*(https?://[^)\s]+|tg://[^)\s]+|uid:\d+|www\.[^)\s]+)\)', re.I)
_UID_RE = re.compile(r'(?:^|[^\w])uid\s*:\s*\d{3,}', re.I)
_AT_USER_RE = re.compile(r'(?:^|[^\w])@([A-Za-z][\w]{2,31})\b')
_PROTOCOL_SPACED_RE = re.compile(
    r'h\W*t\W*t\W*p\W*s?\W*:?\W*/\W*/',
    re.I,
)

# Domain-ish recovery after collapse
_DOMAIN_RE = re.compile(
    r'(?:'
    r'https?://[^\s<>\"\']{3,}|'
    r'www\.[a-z0-9][\w.-]{1,}\.[a-z]{2,}[^\s<>\"\']*|'
    r'(?:ble\.ir|t\.me|telegram\.me|telegram\.dog|instagram\.com|ig\.me|'
    r'youtube\.com|youtu\.be|x\.com|twitter\.com|facebook\.com|fb\.me|'
    r'rubika\.ir|eitaa\.com|splus\.ir|gap\.im|igap\.net)/[^\s<>\"\']*|'
    r'\b[a-z0-9][\w-]{1,30}\.(?:com|ir|net|org|info|me|io|co|app|dev|site|'
    r'link|xyz|online|shop|pro|tv|cc|tk|ml|ga|cf|click|top|vip)(?:/[^\s]*)?'
    r')',
    re.I,
)

_IP_URL_RE = re.compile(
    r'(?:https?://)?(?:\d{1,3}\.){3}\d{1,3}(?::\d{2,5})?(?:/[^\s]*)?',
    re.I,
)

# ── Advertising lexicon (collapsed forms preferred) ─────────────────────────
# High-weight core commercial tokens
_AD_CORE = {
    'سکه': 3, 'خریدسکه': 6, 'فروشسکه': 6, 'خریدوفروش': 5, 'خریدو فروش': 5,
    'فروش': 2, 'خرید': 2, 'فروشنده': 3, 'خریدار': 3, 'فروش فوری': 4,
    'کافهبله': 6, 'کافه بله': 6, 'کافه': 2, 'عضوبگیر': 6, 'عضوبدم': 6,
    'عضوگیری': 5, 'جذبعضو': 5, 'افزایشممبر': 6, 'ممبرگیری': 6, 'ممبر': 3,
    'عضو': 2, 'ممبر بگیر': 6, 'ممبر بدم': 6, 'افزایش عضو': 5,
    'تومان': 2, 'تومن': 2, 'تمن': 2, 'نقدی': 2, 'نقد': 1, 'قیمت': 2,
    'موجودی': 2, 'عمده': 2, 'ارزان': 2, 'فوری': 1, 'واریز': 3, 'پرداخت': 2,
    'معامله': 3, 'سفارش': 2, 'پکیج': 2, 'پک': 1, 'آفر': 2, 'تخفیف': 2,
    'ویژه': 1, 'رایگان نیست': 3, 'هزینه': 2, 'کمیسیون': 3,
    'پیوی': 3, 'پی وی': 3, 'پی‌وی': 3, 'بیاپیوی': 5, 'بیاپ': 3,
    'بیاپی': 3, 'دایرکت': 3, 'پیام‌خصوصی': 3, 'پیام خصوصی': 3,
    'pv': 3, 'pm': 2, 'dm': 2, 'inbox': 2,
    'کانال ما': 3, 'گروه ما': 2, 'عضویت اجباری': 5, 'فالو': 2,
    'فالوور': 3, 'ویو': 2, 'بازدید': 1, 'تبلیغات': 3, 'تبلیغ': 3,
    'اسپانسری': 3, 'برندینگ': 2, 'مارکت': 2, 'بازار': 1,
    'همکاری در فروش': 4, 'درامدزایی': 4, 'درآمدزایی': 4, 'پولدار شو': 4,
    'کسب درآمد': 4, 'کسب درامد': 4, 'شغل خانگی': 3, 'کاردرمنزل': 3,
    'سرمایه گذاری': 3, 'سرمایه‌گذاری': 3, 'بیتکوین': 2, 'تتر': 2,
    'usdt': 2, 'btc': 2, 'ارزدیجیتال': 3, 'رمز ارز': 3, 'رمزارز': 3,
    'شبا': 2, 'کارت به کارت': 4, 'کارت‌به‌کارت': 4, 'شماره کارت': 3,
    'حساب': 1, 'برداشت': 2, 'شارژ': 2, 'گیفت': 2, 'گیفت کارت': 3,
    'فروشگاه': 2, 'سفارش بگیرید': 4, 'ثبت سفارش': 3, 'ارسال رایگان': 2,
    'حراج': 2, 'آکسیون': 2, 'جایزه': 1, 'لاتاری': 2, 'قرعه کشی': 2,
    'ربات تبلیغ': 4, 'ادمین فروش': 4, 'پشتیبانی فروش': 3,
    'سکه بله': 5, 'سکه روبیکا': 5, 'سکه ایتا': 5, 'سکه گپ': 4,
    'افزایش عضو بله': 6, 'عضو واقعی': 4, 'ممبر واقعی': 4, 'ممبر ایرانی': 4,
    'فالوور ایرانی': 4, 'لایک ایرانی': 3, 'ویو فیک': 4, 'ممبر فیک': 4,
    'فروش اکانت': 5, 'خرید اکانت': 5, 'اکانت آماده': 4, 'هیوری': 3,
    'هک': 2, 'خدمات مجازی': 3, 'پنل فروش': 4, 'سایت فروش': 3,
    'لینک دعوت': 3, 'لینک گروه': 3, 'جوین': 2, 'join': 2,
    'channel': 2, 'group': 1, 'admin': 1, 'sell': 2, 'buy': 2,
    'coin': 2, 'member': 2, 'members': 2, 'followers': 2,
    'cheap': 2, 'price': 2, 'order': 2, 'payment': 2,
}

# Phrase patterns (applied on soft-normalized text with spaces kept loosely)
_AD_PHRASE_PATTERNS: list[tuple[re.Pattern[str], int]] = [
    (re.compile(r'خر[یي]د\s*(و)?\s*فروش'), 5),
    (re.compile(r'فروش\s*فوری'), 4),
    (re.compile(r'(سکه|ممبر|عضو)\s*(می)?فروش'), 6),
    (re.compile(r'(سکه|ممبر|عضو)\s*(می)?خر'), 6),
    (re.compile(r'عضو\s*(بگیر|بد[هم]|میخوام|می\s*خوام)'), 6),
    (re.compile(r'ممبر\s*(بگیر|بد[هم]|میخوام)'), 6),
    (re.compile(r'افزایش\s*(ممبر|عضو|فالوور|ویو)'), 6),
    (re.compile(r'جذب\s*(عضو|ممبر|مشتری)'), 5),
    (re.compile(r'بیا\s*(پی\s*وی|پیوی|پی‌وی|pv|pm)'), 5),
    (re.compile(r'(دایرکت|پیوی|پی وی)\s*(بد[هید]|بدین|کنید|کنین)'), 4),
    (re.compile(r'(کافه\s*بله|کافهبله)'), 6),
    (re.compile(r'سکه\s*(بله|روبیکا|ایتا|گپ|سروش)'), 5),
    (re.compile(r'(کارت\s*به\s*کارت|کارت‌به‌کارت)'), 4),
    (re.compile(r'\d+[\s,._]*\d*\s*(تومان|تومن|تمن|هزار|میلیون)'), 3),
    (re.compile(r'(قیمت|مبلغ)\s*[:：]?\s*\d+'), 3),
    (re.compile(r'(فروش|خرید)\s*(اکانت|حساب|ادمین|ربات)'), 5),
    (re.compile(r'(تبلیغات|اسپانسری|برندینگ)\s*(قبول|انجام|میگیر)'), 4),
    (re.compile(r'(در[اآ]مد|درامد)\s*(زایی|زائی|خانگی|اینترنتی)'), 4),
    (re.compile(r'(فالو|subscribe|join)\s*(کن|کنید|کنین|me|us)'), 3),
    (re.compile(r'(channel|group)\s*(join|invite|link)', re.I), 4),
    (re.compile(r'(buy|sell)\s*(coin|member|account|follower)', re.I), 5),
    (re.compile(r'نقد[یي]\s*(پرداخت|واریز|میاد)'), 3),
    (re.compile(r'(موجودی|انبار)\s*(دار[م|یم]|آماد[ه])'), 3),
    (re.compile(r'عمده\s*(و)?\s*خرده'), 3),
    (re.compile(r'(ربات|بات)\s*(تبلیغ|فروش|عضو)'), 4),
]

# Softeners for educational / non-ad context (reduce score, not zero)
_EDU_SOFTENERS = re.compile(
    r'(قانون|قوانین|آموزش|یادگیری|نباید|ممنوع|جلوگیری|ضد\s*تبلیغ|'
    r'گزارش\s*داد|توجه\s*کنید|هشدار|آگاه[یي]|مراقب|کلاهبردار)',
)

# Contact solicitation bundled with commercial intent
_CONTACT_PUSH = re.compile(
    r'(بیا|بفرما|پیام\s*بده|پیام\s*بدهید|دایرکت|پیوی|پی وی|pv|pm)\b',
    re.I,
)


@dataclass
class DetectionResult:
    hit: bool
    score: int = 0
    reasons: list[str] | None = None
    kind: str = ''  # 'ad' | 'link' | ''


def normalize_text(text: str) -> str:
    """Full soft normalization: NFKC, Arabic→FA, strip invisible, keep spaces."""
    if not text:
        return ''
    t = unicodedata.normalize('NFKC', text)
    t = t.translate(_ARABIC_FA)
    t = t.translate(_LOOKALIKE)
    t = _INVISIBLE_RE.sub('', t)
    t = _TATWEEL_RE.sub('', t)
    t = _COMBINING_RE.sub('', t)
    t = t.replace('‌', ' ')  # ZWNJ → space then collapse
    t = re.sub(r'\s+', ' ', t).strip().lower()
    return t


def collapse_text(text: str) -> str:
    """Hard collapse: remove separators/spaces so ک.ا.ف.ه → کافه."""
    t = normalize_text(text)
    t = _SEPARATOR_RE.sub('', t)
    # collapse repeated letters: سککه → سکه (max 2 kept → 1 for match keys)
    t = re.sub(r'(.)\1{2,}', r'\1\1', t)
    return t


def soft_tokens(text: str) -> str:
    """Normalized with single spaces (for phrase regex)."""
    return normalize_text(text)


def _entity_link_hit(entities: list | None) -> bool:
    if not entities:
        return False
    for e in entities:
        t = (e.get('type') or '').lower()
        if t in ('url', 'text_link', 'mention', 'text_mention'):
            # text_mention / mention often used to hide invites
            if t in ('url', 'text_link'):
                return True
            # mention of @channel style is handled by @ regex too
            if t == 'text_link' or e.get('url'):
                return True
        url = e.get('url') or ''
        if url and re.search(r'(https?://|tg://|ble\.ir|t\.me|uid:)', url, re.I):
            return True
    return False


def detect_links(
    text: str,
    entities: list | None = None,
    *,
    block_latin: bool = True,
    block_at_username: bool = True,
) -> DetectionResult:
    """Advanced anti-link. block_latin=True enforces A-Z ban when lock is on."""
    reasons: list[str] = []
    body = text or ''

    if _entity_link_hit(entities):
        reasons.append('entity-link')

    if body:
        if _MD_LINK_RE.search(body):
            reasons.append('markdown-link')
        if _UID_RE.search(body):
            reasons.append('uid-link')
        if _PROTOCOL_SPACED_RE.search(body):
            reasons.append('spaced-protocol')
        if block_at_username and _AT_USER_RE.search(body):
            reasons.append('at-username')

        soft = soft_tokens(body)
        hard = collapse_text(body)
        # recover domains from both forms
        for form in (body, soft, hard, re.sub(r'[^a-z0-9./:_-]', '', hard)):
            if not form:
                continue
            if _DOMAIN_RE.search(form) or _IP_URL_RE.search(form):
                reasons.append('domain')
                break
            # spaced domain: e x a m p l e . c o m
            spaced = re.sub(r'([a-z0-9])\s+(?=[a-z0-9.])', r'\1', soft)
            if _DOMAIN_RE.search(spaced):
                reasons.append('spaced-domain')
                break

        if block_latin and _LATIN_RE.search(body):
            # Allow pure numbers+persian; any Latin letter triggers under strict policy
            reasons.append('latin-letters')

    # unique reasons
    uniq = list(dict.fromkeys(reasons))
    return DetectionResult(hit=bool(uniq), score=len(uniq) * 3, reasons=uniq, kind='link')


def detect_advertisement(text: str, entities: list | None = None) -> DetectionResult:
    """Score-based ad detection. High threshold avoids pure educational false positives."""
    if not text or len(text.strip()) < 2:
        return DetectionResult(hit=False, score=0, reasons=[], kind='ad')

    soft = soft_tokens(text)
    hard = collapse_text(text)
    hard1 = re.sub(r'(.)\1+', r'\1', hard)
    score = 0
    reasons: list[str] = []

    # Core lexicon on collapsed forms
    for form in (hard, hard1, soft.replace(' ', '')):
        for word, weight in _AD_CORE.items():
            key = collapse_text(word)
            if key and key in form:
                score += weight
                reasons.append(f'kw:{word}')
        # only need one full lexicon pass with hits accumulated carefully
        break

    # Second pass: soft phrase patterns
    for form in (soft, hard):
        for pat, weight in _AD_PHRASE_PATTERNS:
            if pat.search(form):
                score += weight
                reasons.append(f'phrase:{pat.pattern[:24]}')

    # Price + commercial verb combo
    has_price = bool(re.search(r'\d{2,}', soft) and re.search(r'(تومان|تومن|تمن|هزار|میلیون|price|\$)', soft))
    has_trade = bool(re.search(r'(خرید|فروش|معامله|سفارش|بفروش|بخر)', soft))
    if has_price and has_trade:
        score += 5
        reasons.append('price+trade')

    # Contact push + commercial
    if _CONTACT_PUSH.search(soft) and (has_trade or score >= 4):
        score += 4
        reasons.append('contact+trade')

    # Entity invite / text_link boosts ad score slightly when commercial words exist
    if entities and score >= 3 and _entity_link_hit(entities):
        score += 3
        reasons.append('ad+hidden-link')

    # Educational softener — stronger when no hard commercial intent
    if _EDU_SOFTENERS.search(soft):
        if not has_price and not _CONTACT_PUSH.search(soft):
            # Policy / teaching about ads → not an ad itself
            score = min(score, 3)
            reasons.append('edu-blocked')
        else:
            score = max(0, score - 6)
            reasons.append('edu-softened')

    # Threshold: need clear commercial intent
    # Single weak word like «قیمت» alone should not ban.
    threshold = 7
    uniq = list(dict.fromkeys(reasons))
    return DetectionResult(hit=score >= threshold, score=score, reasons=uniq, kind='ad')


def message_has_link(body: str, entities: list | None = None, *, strict_latin: bool = True) -> bool:
    return detect_links(body, entities, block_latin=strict_latin).hit


def message_is_ad(body: str, entities: list | None = None) -> bool:
    return detect_advertisement(body, entities).hit


# Back-compat helpers used by older extract_urls callers
def extract_urls(text: str) -> list[str]:
    if not text:
        return []
    found: list[str] = []
    soft = soft_tokens(text)
    hard = collapse_text(text)
    for form in (text, soft, hard):
        for m in _DOMAIN_RE.finditer(form):
            g = m.group(0).strip().strip('()[].,;:«»"\'')
            if g and g not in found:
                found.append(g)
    return found
