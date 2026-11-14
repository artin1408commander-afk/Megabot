from __future__ import annotations

# Main reply keyboard — MEGA private UI labels (logic unchanged; text is display-only).
USER_KEYBOARD = {
    'keyboard': [
        [{'text': '🛰️ ارتباط با مگا'}, {'text': '💜 پشتیبانی از توسعه'}],
        [{'text': '🧑‍💻 سازندگان مگا'}, {'text': '📊 مرکز اطلاعات'}],
        [{'text': '🧩 امکانات بیشتر'}],
    ],
    'resize_keyboard': True,
    'is_persistent': True,
}

# Telegram Bot API style values (also accepted by Bale when supported):
#   primary | success | danger
STYLE_SUCCESS = 'success'  # green
STYLE_DANGER = 'danger'    # red
STYLE_PRIMARY = 'primary'  # blue


def _btn(label: str, data: str, style: str | None = None) -> dict:
    b: dict = {'text': label, 'callback_data': str(data)}
    if style:
        b['style'] = style
    return b


def inline(rows: list) -> dict:
    """Build inline keyboard.

    Each cell may be:
      (label, callback_data)
      (label, callback_data, style)   # style: success|danger|primary
      dict already shaped for the API
    """
    keyboard = []
    for row in rows:
        out = []
        for item in row:
            if isinstance(item, dict) and 'text' in item:
                out.append(item)
            elif isinstance(item, (list, tuple)):
                if len(item) >= 3:
                    label, data, style = item[0], item[1], item[2]
                    if isinstance(data, str) and data.startswith('http'):
                        b = {'text': label, 'url': data}
                    else:
                        b = _btn(label, data, style)
                    out.append(b)
                elif len(item) >= 2:
                    label, data = item[0], item[1]
                    if isinstance(data, str) and data.startswith('http'):
                        out.append({'text': label, 'url': data})
                    else:
                        # auto color for common cancel/confirm labels
                        style = None
                        low = str(label)
                        if any(x in low for x in ('لغو', 'انصراف', 'بستن', 'بازگشت', 'برگشت', '❌', '✖️', '🚫')):
                            style = STYLE_DANGER
                        elif any(x in low for x in ('تأیید', 'تایید', '✅', 'ذخیره', 'بله', 'ارسال')):
                            style = STYLE_SUCCESS
                        out.append(_btn(label, data, style))
            # else skip malformed
        if out:
            keyboard.append(out)
    return {'inline_keyboard': keyboard}


def url_button(label: str, url: str) -> dict:
    """Single-row inline keyboard with one URL button (Bale-compatible)."""
    return {'inline_keyboard': [[{'text': label, 'url': url}]]}


def merge_inline(base: dict | None, extra_row: list[dict]) -> dict:
    """Append a row of button dicts to an existing inline keyboard without mutating base."""
    if not base or 'inline_keyboard' not in base:
        return {'inline_keyboard': [extra_row]}
    rows = [list(r) for r in base['inline_keyboard']]
    rows.append(extra_row)
    return {'inline_keyboard': rows}


def menu_page(items: list[tuple[str, str]], page: int, prefix: str, back: str = 'home', page_size: int = 3) -> dict:
    """At most 6 buttons per page including navigation and back/close controls."""
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
