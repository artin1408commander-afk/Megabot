from __future__ import annotations
import asyncio, io, os, shutil, subprocess, tempfile
from pathlib import Path
from PIL import Image, ImageDraw, ImageFont, ImageOps

MAX_INPUT_BYTES = 20 * 1024 * 1024
MAX_VIDEO_SECONDS = 20
# Target: most GIFs well under 5MB; long clips may approach this ceiling.
MAX_OUTPUT_BYTES = 5 * 1024 * 1024
MAX_OUTPUT_LONG = 8 * 1024 * 1024  # only for longer source videos
GIF_MAX_SIDE = 560
GIF_FPS = 10
GIF_MAX_FRAMES = 60

# Same family as stats dashboard (Vazirmatn Bold) — never reverse with bidi.
_FONT_DIR = Path(__file__).resolve().parent / 'assets' / 'fonts'
_BOLD_FONT_CANDIDATES = (
    str(_FONT_DIR / 'Vazirmatn-Bold.ttf'),
    str(_FONT_DIR / 'Vazirmatn-Regular.ttf'),
    '/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf',
    '/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf',
)


def _shape_fa(text: str) -> str:
    """Arabic reshape only — no bidi.get_display (that reverses with LTR anchors)."""
    if not text:
        return ''
    try:
        import arabic_reshaper
        return arabic_reshaper.reshape(str(text))
    except Exception:
        return str(text)


def _font(size: int):
    size = max(8, int(size))
    for candidate in _BOLD_FONT_CANDIDATES:
        if os.path.exists(candidate):
            try:
                return ImageFont.truetype(candidate, size)
            except Exception:
                pass
    return ImageFont.load_default()


def _wrap_text(draw: ImageDraw.ImageDraw, text: str, font, max_width: int, stroke_width: int) -> list[str]:
    """Word-wrap so each line fits max_width. Falls back to char-wrap for long tokens."""
    text = (text or '').strip()
    if not text:
        return []
    words = text.split()
    if not words:
        return [text]
    lines: list[str] = []
    current = ''
    for word in words:
        trial = word if not current else f'{current} {word}'
        bbox = draw.textbbox((0, 0), trial, font=font, stroke_width=stroke_width)
        if bbox[2] - bbox[0] <= max_width:
            current = trial
            continue
        if current:
            lines.append(current)
        # single word longer than max_width → char wrap
        if draw.textbbox((0, 0), word, font=font, stroke_width=stroke_width)[2] > max_width:
            chunk = ''
            for ch in word:
                t2 = chunk + ch
                if draw.textbbox((0, 0), t2, font=font, stroke_width=stroke_width)[2] <= max_width:
                    chunk = t2
                else:
                    if chunk:
                        lines.append(chunk)
                    chunk = ch
            current = chunk
        else:
            current = word
    if current:
        lines.append(current)
    return lines or [text]


def _overlay(image: Image.Image, text: str) -> Image.Image:
    """Bold, bright white text, always horizontal, auto-shrink, never leave the frame."""
    if not (text or '').strip():
        return image
    text = (text or '').strip()
    image = image.convert('RGBA')
    draw = ImageDraw.Draw(image)
    margin = max(6, int(min(image.width, image.height) * 0.04))
    max_width = max(20, image.width - 2 * margin)
    max_height = max(20, int(image.height * 0.36))  # text block may use up to ~42% of height

    # ~5% larger than previous baseline, bold Vazirmatn
    size = max(18, int(image.height * 0.168))
    lines: list[str] = []
    font = _font(size)
    stroke = max(2, size // 12)

    # Shrink until wrapped block fits both width and height
    while size >= 10:
        font = _font(size)
        stroke = max(2, size // 12)
        lines = _wrap_text(draw, text, font, max_width, stroke)
        # measure block
        line_heights = []
        max_line_w = 0
        for ln in lines:
            box = draw.textbbox((0, 0), ln, font=font, stroke_width=stroke)
            max_line_w = max(max_line_w, box[2] - box[0])
            line_heights.append(box[3] - box[1])
        gap = max(2, size // 8)
        block_h = sum(line_heights) + gap * max(0, len(lines) - 1)
        if max_line_w <= max_width and block_h <= max_height:
            break
        size -= 2
    else:
        font = _font(10)
        stroke = 2
        lines = _wrap_text(draw, text, font, max_width, stroke)
        line_heights = []
        for ln in lines:
            box = draw.textbbox((0, 0), ln, font=font, stroke_width=stroke)
            line_heights.append(box[3] - box[1])
        gap = 2
        block_h = sum(line_heights) + gap * max(0, len(lines) - 1)

    # Vertical position ~75% down, clamp fully inside frame
    y = int(image.height * 0.86) - block_h // 2
    y = max(margin, min(image.height - block_h - margin, y))

    # Pure white + strong black outline for contrast (reads “whiter / bolder”)
    fill = (255, 255, 255, 255)
    outline = (0, 0, 0, 255)

    for i, ln in enumerate(lines):
        shaped = _shape_fa(ln)
        box = draw.textbbox((0, 0), shaped, font=font, stroke_width=stroke)
        tw = box[2] - box[0]
        th = box[3] - box[1]
        x = (image.width - tw) // 2
        x = max(margin, min(image.width - tw - margin, x))
        draw.text((x, y), shaped, font=font, fill=fill, stroke_width=stroke, stroke_fill=outline)
        y += th + gap

    return image.convert('RGB')


def _quantize_gif_frames(frames: list[Image.Image]) -> list[Image.Image]:
    """Reduce palette for smaller GIF size."""
    out = []
    for fr in frames:
        q = fr.convert('P', palette=Image.ADAPTIVE, colors=192)
        out.append(q)
    return out


def image_to_gif(raw: bytes, text: str = '') -> bytes:
    with Image.open(io.BytesIO(raw)) as source:
        frames = []
        try:
            count = min(getattr(source, 'n_frames', 1), GIF_MAX_FRAMES)
            for i in range(count):
                source.seek(i)
                frame = ImageOps.contain(source.convert('RGB'), (GIF_MAX_SIDE, GIF_MAX_SIDE))
                if text:
                    frame = _overlay(frame, text)
                frames.append(frame.copy())
        except EOFError:
            pass
    if not frames:
        raise ValueError('تصویر قابل پردازش نیست.')
    frames = _quantize_gif_frames(frames)
    out = io.BytesIO()
    frames[0].save(
        out,
        format='GIF',
        save_all=True,
        append_images=frames[1:],
        duration=max(80, int(1000 / GIF_FPS)),
        loop=0,
        optimize=True,
        disposal=2,
    )
    result = out.getvalue()
    if len(result) > MAX_OUTPUT_BYTES:
        # Second pass: smaller side + fewer frames
        smaller = []
        step = max(1, len(frames) // 24)
        for fr in frames[::step][:24]:
            fr_rgb = fr.convert('RGB')
            fr_rgb = ImageOps.contain(fr_rgb, (360, 360))
            if text:
                fr_rgb = _overlay(fr_rgb, text)
            smaller.append(fr_rgb.convert('P', palette=Image.ADAPTIVE, colors=64))
        out2 = io.BytesIO()
        smaller[0].save(
            out2, format='GIF', save_all=True, append_images=smaller[1:],
            duration=120, loop=0, optimize=True, disposal=2,
        )
        result = out2.getvalue()
        if len(result) > MAX_OUTPUT_BYTES:
            raise ValueError('حجم GIF بیش از حد مجاز است (۵ مگابایت).')
    return result


def video_to_gif(raw: bytes, suffix: str = '.mp4', text: str = '') -> bytes:
    """Video → GIF. ffmpeg only for demux/scale; Persian text via Pillow (no drawtext)."""
    if not shutil.which('ffmpeg'):
        raise RuntimeError('ffmpeg روی سرور نصب نیست؛ از Dockerfile همین پروژه برای استقرار استفاده کن.')
    long_source = len(raw) > 3 * 1024 * 1024
    limit = MAX_OUTPUT_LONG if long_source else MAX_OUTPUT_BYTES

    with tempfile.TemporaryDirectory(prefix='megabot-gif-') as tmp:
        tmp_path = Path(tmp)
        src = tmp_path / ('input' + (suffix if suffix.startswith('.') else f'.{suffix}'))
        src.write_bytes(raw)
        frames_dir = tmp_path / 'frames'
        frames_dir.mkdir()

        side = GIF_MAX_SIDE
        fps = GIF_FPS
        # Simple, widely-supported scale (avoid fragile force_original_aspect_ratio flags)
        # scale=w:h with -2 keeps aspect and even dimensions for encoder safety
        vf = f'fps={fps},scale={side}:-2'

        def _run_ffmpeg(vf_expr: str) -> None:
            # Clear previous frames
            for old in frames_dir.glob('f_*.png'):
                old.unlink(missing_ok=True)
            cmd = [
                'ffmpeg', '-nostdin', '-hide_banner', '-loglevel', 'error', '-y',
                '-i', str(src),
                '-t', str(MAX_VIDEO_SECONDS),
                '-vf', vf_expr,
                '-frames:v', str(GIF_MAX_FRAMES),
                str(frames_dir / 'f_%04d.png'),
            ]
            try:
                subprocess.run(cmd, check=True, timeout=60, capture_output=True)
            except subprocess.CalledProcessError as exc:
                err = (exc.stderr or b'').decode('utf-8', 'ignore')[:400]
                raise RuntimeError(f'ffmpeg failed: {err or exc}') from exc
            except subprocess.TimeoutExpired as exc:
                raise RuntimeError('ffmpeg timeout — ویدیو خیلی طولانی یا سنگین است.') from exc

        try:
            _run_ffmpeg(vf)
        except RuntimeError:
            # Fallback: lower res / fps
            _run_ffmpeg(f'fps=6,scale=360:-2')

        paths = sorted(frames_dir.glob('f_*.png'))
        if not paths:
            # Last resort: single-frame extract
            still = tmp_path / 'still.png'
            cmd = [
                'ffmpeg', '-nostdin', '-hide_banner', '-loglevel', 'error', '-y',
                '-i', str(src), '-frames:v', '1', '-q:v', '2', str(still),
            ]
            try:
                subprocess.run(cmd, check=True, timeout=30, capture_output=True)
            except Exception as exc:
                raise RuntimeError(f'استخراج فریم ناموفق: {type(exc).__name__}') from exc
            if not still.exists():
                raise RuntimeError('هیچ فریمی از ویدیو استخراج نشد.')
            paths = [still]

        frames: list[Image.Image] = []
        for fp in paths[:GIF_MAX_FRAMES]:
            with Image.open(fp) as im:
                fr = ImageOps.contain(im.convert('RGB'), (GIF_MAX_SIDE, GIF_MAX_SIDE))
                if text:
                    fr = _overlay(fr, text)
                frames.append(fr.copy())

        if not frames:
            raise RuntimeError('ساخت فریم گیف ناموفق بود.')

        frames_q = _quantize_gif_frames(frames)
        out = io.BytesIO()
        frames_q[0].save(
            out,
            format='GIF',
            save_all=True,
            append_images=frames_q[1:] if len(frames_q) > 1 else [],
            loop=0,
            duration=max(80, int(1000 / max(1, min(fps, 12)))),
            optimize=True,
        )
        result = out.getvalue()

        if len(result) > limit and len(frames) > 1:
            # Shrink: fewer frames + smaller side
            step = max(1, len(frames) // 24)
            small = []
            for fr in frames[::step][:24]:
                fr2 = ImageOps.contain(fr, (360, 360))
                small.append(fr2.convert('P', palette=Image.ADAPTIVE, colors=96))
            out2 = io.BytesIO()
            small[0].save(
                out2, format='GIF', save_all=True, append_images=small[1:],
                loop=0, duration=120, optimize=True,
            )
            result = out2.getvalue()

        hard_cap = MAX_OUTPUT_LONG if long_source else MAX_OUTPUT_BYTES
        if len(result) > hard_cap:
            raise ValueError(f'حجم GIF بیش از حد مجاز است ({hard_cap // (1024 * 1024)} مگابایت).')
        return result


async def convert_media(raw: bytes, filename: str, text: str = '') -> bytes:
    suffix = Path(filename).suffix.lower()
    if suffix in ('.mp4', '.mov', '.webm', '.mkv', '.avi'):
        return await asyncio.to_thread(video_to_gif, raw, suffix, text)
    return await asyncio.to_thread(image_to_gif, raw, text)
