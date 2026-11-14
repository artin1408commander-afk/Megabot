from __future__ import annotations

USER_KEYBOARD = {
    'keyboard': [
        [{'text': '🛰️ ارتباط با مگا'}, {'text': '💜 پشتیبانی از توسعه'}],
        [{'text': '🧑‍💻 سازندگان مگا'}, {'text': '📊 مرکز اطلاعات'}],
        [{'text': '🧩 امکانات بیشتر'}],
    ],
    'resize_keyboard': True,
    'is_persistent': True,
}

STYLE_SUCCESS = 'success'
STYLE_DANGER = 'danger'
STYLE_PRIMARY = 'primary'

_DANGER_LABEL = (
    'لغو', 'انصراف', 'بستن', 'بازگشت', 'برگشت', 'خیر', 'نه', 'حذف', 'پاک',
    'خاموش', 'غیرفعال', 'رد', 'مسدود', 'بن', 'اخطار', 'اخراج', 'کیک',
    '❌', '✖️', '🚫', '⛔', '🗑️', '🛑', '🔴',
)
_SUCCESS_LABEL = (
    'تأیید', 'تایید', 'بله', 'آره', 'ذخیره', 'ارسال', 'ثبت', 'فعال',
    'روشن', 'قبول', 'برداشتن محدودیت', 'آنبن', 'رفع',
    '✅', '✔️', '🟢',
)


def infer_style(label: str | None, data: str | None = None) -> str | None:
    """Only color positive/negative actions. Neutral menu buttons stay glass (no style)."""
    lab = str(label or '')
    dat = str(data or '').lower()

    if '🟢' in lab:
        return STYLE_SUCCESS
    if '🔴' in lab:
        return STYLE_DANGER

    # lock toggles by callback
    if 'lock:tog' in dat or dat.startswith('lock:'):
        if 'خاموش' in lab or '🔴' in lab or ':off' in dat:
            return STYLE_DANGER
        if 'روشن' in lab or '🟢' in lab or ':on' in dat:
            return STYLE_SUCCESS

    for tok in ('ban', 'kick', 'mute', 'delete', 'reject', 'cancel', 'close', 'deny'):
        if tok in dat.split(':') or dat == tok or dat.endswith(':' + tok):
            return STYLE_DANGER
    if 'unban' in dat.split(':') or dat.endswith(':unban') or 'unban' in dat:
        return STYLE_SUCCESS

    for x in _DANGER_LABEL:
        if x in lab:
            if 'برداشتن' in lab or 'رفع' in lab or 'آنبن' in lab:
                return STYLE_SUCCESS
            return STYLE_DANGER
    for x in _SUCCESS_LABEL:
        if x in lab:
            return STYLE_SUCCESS

    # Neutral — no style (real glass)
    return None


def _btn(label: str, data: str, style: str | None = None) -> dict:
    st = style if style is not None else infer_style(label, data)
    b: dict = {'text': label, 'callback_data': str(data)}
    if st in (STYLE_SUCCESS, STYLE_DANGER, STYLE_PRIMARY):
        b['style'] = st
    return b


def _paint_dict(btn: dict) -> dict:
    if not isinstance(btn, dict) or 'text' not in btn:
        return btn
    btn = dict(btn)
    if btn.get('style') in (STYLE_SUCCESS, STYLE_DANGER, STYLE_PRIMARY):
        return btn
    # only add if infer finds positive/negative
    st = infer_style(btn.get('text'), btn.get('callback_data') or btn.get('url'))
    if st:
        btn['style'] = st
    else:
        btn.pop('style', None)
    return btn


def inline(rows: list) -> dict:
    keyboard = []
    for row in rows or []:
        out = []
        for item in row:
            if isinstance(item, dict) and 'text' in item:
                out.append(_paint_dict(item))
            elif isinstance(item, (list, tuple)):
                if len(item) >= 3:
                    label, data, style = item[0], item[1], item[2]
                    if isinstance(data, str) and str(data).startswith('http'):
                        b = {'text': label, 'url': data}
                        if style in (STYLE_SUCCESS, STYLE_DANGER, STYLE_PRIMARY):
                            b['style'] = style
                        out.append(b)
                    else:
                        if style not in (STYLE_SUCCESS, STYLE_DANGER, STYLE_PRIMARY):
                            style = infer_style(label, data)
                        out.append(_btn(label, data, style))
                elif len(item) >= 2:
                    label, data = item[0], item[1]
                    if isinstance(data, str) and str(data).startswith('http'):
                        out.append(_paint_dict({'text': label, 'url': data}))
                    else:
                        out.append(_btn(label, data))
        if out:
            keyboard.append(out)
    return {'inline_keyboard': keyboard}


def paint_keyboard(keyboard: dict | None) -> dict | None:
    if not keyboard or 'inline_keyboard' not in keyboard:
        return keyboard
    new_rows = []
    for row in keyboard.get('inline_keyboard') or []:
        new_rows.append([_paint_dict(b) if isinstance(b, dict) else b for b in row])
    return {'inline_keyboard': new_rows}


def url_button(label: str, url: str) -> dict:
    return {'inline_keyboard': [[{'text': label, 'url': url}]]}


def merge_inline(base: dict | None, extra_row: list[dict]) -> dict:
    if not base or 'inline_keyboard' not in base:
        return paint_keyboard({'inline_keyboard': [extra_row]}) or {'inline_keyboard': [extra_row]}
    rows = [list(r) for r in base['inline_keyboard']]
    rows.append([_paint_dict(b) if isinstance(b, dict) else b for b in extra_row])
    return paint_keyboard({'inline_keyboard': rows}) or {'inline_keyboard': rows}


def menu_page(items: list[tuple[str, str]], page: int, prefix: str, back: str = 'home', page_size: int = 3) -> dict:
    start = page * page_size
    shown = items[start:start + page_size]
    rows = [[(label, data)] for label, data in shown]
    controls: list = []
    if page > 0:
        controls.append(('⬅️ قبلی', f'{prefix}:page:{page-1}'))
    if start + page_size < len(items):
        controls.append(('بعدی ➡️', f'{prefix}:page:{page+1}'))
    if controls:
        rows.append(controls[:2])
    rows.append([
        ('↩️ بازگشت', f'{prefix}:back:{back}', STYLE_DANGER),
        ('✖️ بستن', 'close', STYLE_DANGER),
    ])
    return inline(rows)


def main_admin_menu(owner: bool = False) -> dict:
    items = [
        ('📈 گزارش عملکرد', 'adm:stats'),
        ('🔎 یافتن کاربر', 'adm:search:user'),
        ('🔎 یافتن گروه', 'adm:search:group'),
        ('🎫 رهگیری پرونده', 'adm:case'),
        ('🧾 رخدادهای اخیر', 'adm:logs'),
    ]
    if owner:
        items += [
            ('🛡️ مدیران ربات', 'own:admins'),
            ('🌑 ویرایش هویت مگا', 'own:about'),
            ('🧑‍💻 ویرایش سازندگان', 'own:team'),
            ('⚙️ مرکز کنترل مالک', 'own:settings'),
        ]
    return menu_page(items, 0, 'admin', 'home')


def user_actions(target_type: str, target_id: int, can_ban: bool) -> dict:
    rows = []
    if can_ban:
        rows.append([('⛔ اعمال محدودیت', f'mod:ban:{target_type}:{target_id}', STYLE_DANGER)])
    rows.append([('♻️ برداشتن محدودیت', f'mod:unban:{target_type}:{target_id}', STYLE_SUCCESS)])
    if target_type == 'user':
        rows.append([
            ('👥 گروه‌های مشترک', f'adm:ugroups:{target_id}:0'),
            ('📜 سوابق', f'adm:uhist:{target_id}:0'),
        ])
        rows.append([('⚠️ اخطار به کاربر', f'adm:uwarn:{target_id}', STYLE_DANGER)])
    rows.append([
        ('↩️ بازگشت', f'adm:search:{target_type}', STYLE_DANGER),
        ('✖️ بستن', 'close', STYLE_DANGER),
    ])
    return inline(rows)
