"""TTS for MEGA BOT.

Persian (FA):
  - short text (< PIPER_MAX_CHARS, default 100): Piper offline (Amir) if model available
  - longer text: gTTS → Google HTTP → espeak-ng

English / other:
  - gTTS → Google HTTP → espeak-ng

Soft ceiling: TTS_MAX_CHARS (default 100000).
"""
from __future__ import annotations

import asyncio
import logging
import os
import re
import shutil
import subprocess
import tempfile
import urllib.parse
import urllib.request
from pathlib import Path
from typing import Optional

log = logging.getLogger(__name__)

DEFAULT_TEXT = 'تست'
MAX_CHARS = int(os.getenv('TTS_MAX_CHARS', '100000'))
GTTS_CHUNK = int(os.getenv('TTS_GTTS_CHUNK', '500'))
GOOGLE_CHUNK = int(os.getenv('TTS_GOOGLE_CHUNK', '180'))
GOOGLE_PARALLEL = int(os.getenv('TTS_GOOGLE_PARALLEL', '5'))

# Short Persian → Piper; at/above this length → existing online engines
PIPER_MAX_CHARS = int(os.getenv('TTS_PIPER_MAX_CHARS', '100'))
# medium-low speed (higher length_scale = slower), soft/quiet voice
PIPER_LENGTH_SCALE = float(os.getenv('TTS_PIPER_LENGTH_SCALE', '1.55'))
PIPER_NOISE_SCALE = float(os.getenv('TTS_PIPER_NOISE_SCALE', '0.5'))
PIPER_NOISE_W = float(os.getenv('TTS_PIPER_NOISE_W', '0.7'))
PIPER_VOLUME = float(os.getenv('TTS_PIPER_VOLUME', '0.8'))
PIPER_MODEL_ENV = os.getenv('PIPER_MODEL', '').strip()
PIPER_MODEL_DIR = os.getenv(
    'PIPER_MODEL_DIR',
    str(Path(__file__).resolve().parent / 'assets' / 'piper'),
)
_HF_AMIR_ONNX = (
    'https://huggingface.co/rhasspy/piper-voices/resolve/main/'
    'fa/fa_IR/amir/medium/fa_IR-amir-medium.onnx'
)
_HF_AMIR_JSON = _HF_AMIR_ONNX + '.json'

_piper_voice = None
_piper_lock = asyncio.Lock()
_piper_failed = False


def _which(cmd: str) -> Optional[str]:
    return shutil.which(cmd)


def normalize_tts_text(text: str) -> str:
    t = (text or '').strip()
    t = t.replace('\r\n', '\n').replace('\r', '\n')
    # keep ZWNJ (\u200c) for Persian word joining; only collapse plain spaces
    t = re.sub(r'[ \t\u00a0]+', ' ', t)
    t = re.sub(r'\n{3,}', '\n\n', t)
    return t.strip()


def _prepare_piper_text(text: str) -> str:
    """Help Piper finish words: light spacing + terminal pause marker."""
    t = normalize_tts_text(text)
    if not t:
        return t
    # ensure separation around common Persian punctuation
    t = re.sub(r'\s*([،؛:!?…؟.])\s*', r'\1 ', t)
    t = re.sub(r'\s+', ' ', t).strip()
    # trailing pause so last syllable is not clipped
    if t[-1] not in '،؛:!?…؟.':
        t = t + '.'
    return t


def detect_lang(text: str) -> str:
    latin = len(re.findall(r'[A-Za-z]', text or ''))
    arabic = len(re.findall(r'[\u0600-\u06FF]', text or ''))
    if latin > arabic * 1.2 and latin >= 3:
        return 'en'
    return 'fa'


def estimate_duration_sec(text: str) -> int:
    n = len(normalize_tts_text(text) or '')
    return max(1, int(n / 14) + 1)


def _chunk_text(text: str, size: int) -> list[str]:
    if len(text) <= size:
        return [text]
    chunks: list[str] = []
    buf = ''
    parts = re.split(r'(?<=[.!?…؟!\n،,;؛:])\s+', text)
    for part in parts:
        if not part:
            continue
        if len(part) > size:
            if buf:
                chunks.append(buf.strip())
                buf = ''
            for i in range(0, len(part), size):
                chunks.append(part[i:i + size])
            continue
        if len(buf) + len(part) + 1 <= size:
            buf = f'{buf} {part}'.strip()
        else:
            if buf:
                chunks.append(buf.strip())
            buf = part
    if buf.strip():
        chunks.append(buf.strip())
    return chunks or [text[:size]]


def _ffmpeg_to_ogg(src: str, dst: str, *, volume: float | None = None) -> None:
    ff = _which('ffmpeg')
    if not ff:
        raise RuntimeError('ffmpeg not found')
    cmd = [ff, '-y', '-i', src]
    if volume is not None and 0 < volume < 1.0:
        cmd += ['-af', f'volume={volume:.3f}']
    cmd += ['-c:a', 'libopus', '-b:a', '48k', dst]
    subprocess.run(cmd, check=True, capture_output=True, timeout=120)


def _concat_audio_files(paths: list[str], dst: str) -> None:
    ff = _which('ffmpeg')
    if not ff:
        raise RuntimeError('ffmpeg not found')
    with tempfile.NamedTemporaryFile('w', suffix='.txt', delete=False) as lst:
        for p in paths:
            lst.write(f"file '{p}'\n")
        list_path = lst.name
    try:
        subprocess.run(
            [ff, '-y', '-f', 'concat', '-safe', '0', '-i', list_path, '-c', 'copy', dst],
            check=True, capture_output=True, timeout=180,
        )
    finally:
        try:
            os.unlink(list_path)
        except OSError:
            pass


def _download(url: str, dest: Path) -> None:
    dest.parent.mkdir(parents=True, exist_ok=True)
    tmp = dest.with_suffix(dest.suffix + '.part')
    req = urllib.request.Request(url, headers={'User-Agent': 'mega-bot-tts/1.0'})
    with urllib.request.urlopen(req, timeout=180) as resp:
        data = resp.read()
    tmp.write_bytes(data)
    tmp.replace(dest)


def _resolve_piper_model() -> Optional[str]:
    candidates: list[Path] = []
    if PIPER_MODEL_ENV:
        candidates.append(Path(PIPER_MODEL_ENV))
    base = Path(PIPER_MODEL_DIR)
    candidates.extend([
        base / 'fa_IR-amir-medium.onnx',
        base / 'fa_IR-gyro-medium.onnx',
        Path('/models/fa_IR-amir-medium.onnx'),
        Path('/app/models/fa_IR-amir-medium.onnx'),
        Path('/app/mega_bot/assets/piper/fa_IR-amir-medium.onnx'),
    ])
    for p in candidates:
        try:
            if p.is_file() and p.stat().st_size > 1_000_000:
                return str(p)
        except OSError:
            continue

    target = base / 'fa_IR-amir-medium.onnx'
    json_target = Path(str(target) + '.json')
    try:
        if not target.is_file() or target.stat().st_size < 1_000_000:
            log.info('Downloading Piper FA model Amir medium to %s …', target)
            _download(_HF_AMIR_ONNX, target)
        if not json_target.is_file():
            try:
                _download(_HF_AMIR_JSON, json_target)
            except Exception as je:
                log.warning('Piper model json download failed: %s', je)
        if target.is_file() and target.stat().st_size > 1_000_000:
            return str(target)
    except Exception as exc:
        log.warning('Piper model download failed: %s', exc)
    return None


def _load_piper_sync():
    global _piper_voice, _piper_failed
    if _piper_voice is not None:
        return _piper_voice
    if _piper_failed:
        # allow retry after deploy if model appears later
        model = _resolve_piper_model()
        if not model:
            return None
        _piper_failed = False
    model = _resolve_piper_model()
    if not model:
        _piper_failed = True
        log.warning('Piper model not found; short FA will fall back to gTTS')
        return None
    try:
        from piper import PiperVoice  # type: ignore
        _piper_voice = PiperVoice.load(model)
        log.info('Piper voice loaded: %s', model)
        return _piper_voice
    except Exception as exc:
        log.warning('Piper load failed: %s', exc)
        _piper_failed = True
        return None


def _pad_wav_silence(wav_path: str, ms: int = 350) -> None:
    """Append silence so the last word is not cut off."""
    import wave
    import struct
    with wave.open(wav_path, 'rb') as wf:
        params = wf.getparams()
        frames = wf.readframes(wf.getnframes())
    nchan, sampwidth, rate = params.nchannels, params.sampwidth, params.framerate
    n_sil = int(rate * (ms / 1000.0))
    silence = b'\x00' * (n_sil * nchan * sampwidth)
    with wave.open(wav_path, 'wb') as wf:
        wf.setparams(params)
        wf.writeframes(frames + silence)


def _synthesize_piper_sync(text: str) -> bytes:
    voice = _load_piper_sync()
    if voice is None:
        raise RuntimeError('piper unavailable')

    import wave

    text = _prepare_piper_text(text)

    with tempfile.TemporaryDirectory(prefix='mega-piper-') as td:
        wav_path = os.path.join(td, 'out.wav')
        syn_config = None
        try:
            from piper.config import SynthesisConfig  # type: ignore
            # length_scale > 1 => slower; sentence_silence adds gap between sentences
            kwargs = dict(
                length_scale=PIPER_LENGTH_SCALE,
                noise_scale=PIPER_NOISE_SCALE,
                noise_w=PIPER_NOISE_W,
                volume=PIPER_VOLUME,
            )
            # sentence_silence supported on newer piper-tts
            try:
                syn_config = SynthesisConfig(**kwargs, sentence_silence=0.35)
            except TypeError:
                syn_config = SynthesisConfig(**kwargs)
        except Exception:
            syn_config = None

        with wave.open(wav_path, 'wb') as wf:
            ok = False
            if hasattr(voice, 'synthesize_wav'):
                try:
                    if syn_config is not None:
                        voice.synthesize_wav(text, wf, syn_config=syn_config)
                    else:
                        voice.synthesize_wav(text, wf)
                    ok = True
                except TypeError:
                    try:
                        voice.synthesize_wav(text, wf)
                        ok = True
                    except Exception:
                        ok = False
                except Exception as exc:
                    log.warning('synthesize_wav failed: %s', exc)
                    ok = False
            if not ok:
                rate = 22050
                try:
                    rate = int(getattr(voice.config, 'sample_rate', 22050))
                except Exception:
                    pass
                wf.setnchannels(1)
                wf.setsampwidth(2)
                wf.setframerate(rate)
                kwargs = {}
                if syn_config is not None:
                    kwargs = {
                        'length_scale': PIPER_LENGTH_SCALE,
                        'noise_scale': PIPER_NOISE_SCALE,
                        'noise_w': PIPER_NOISE_W,
                    }
                try:
                    stream = voice.synthesize(text, **kwargs) if kwargs else voice.synthesize(text)
                except TypeError:
                    stream = voice.synthesize(text)
                for chunk in stream:
                    audio = getattr(chunk, 'audio_int16_bytes', None)
                    if audio is None:
                        audio = getattr(chunk, 'audio_bytes', None)
                    if audio:
                        wf.writeframes(audio)

        try:
            _pad_wav_silence(wav_path, ms=400)
        except Exception as exc:
            log.debug('pad silence failed: %s', exc)

        ogg_path = os.path.join(td, 'out.ogg')
        try:
            # mild volume reduce only; do not trim end
            _ffmpeg_to_ogg(wav_path, ogg_path, volume=0.9)
            return open(ogg_path, 'rb').read()
        except Exception:
            return open(wav_path, 'rb').read()


async def synthesize_piper(text: str) -> bytes:
    async with _piper_lock:
        return await asyncio.to_thread(_synthesize_piper_sync, text)


async def synthesize_gtts(text: str, lang: str) -> bytes:
    from gtts import gTTS  # type: ignore

    g_lang = 'fa' if lang == 'fa' else 'en'
    chunks = _chunk_text(text, GTTS_CHUNK)
    with tempfile.TemporaryDirectory(prefix='mega-gtts-') as td:
        mp3s = []
        for i, ch in enumerate(chunks):
            path = os.path.join(td, f'{i}.mp3')

            def _one(c=ch, p=path):
                tts = gTTS(text=c, lang=g_lang, slow=False)
                tts.save(p)

            await asyncio.to_thread(_one)
            mp3s.append(path)
        merged = os.path.join(td, 'm.mp3')
        if len(mp3s) == 1:
            shutil.copy(mp3s[0], merged)
        else:
            _concat_audio_files(mp3s, merged)
        ogg = os.path.join(td, 'o.ogg')
        try:
            _ffmpeg_to_ogg(merged, ogg)
            return open(ogg, 'rb').read()
        except Exception:
            return open(merged, 'rb').read()


async def synthesize_google(text: str, lang: str) -> bytes:
    g_lang = 'fa' if lang == 'fa' else 'en'
    chunks = _chunk_text(text, GOOGLE_CHUNK)
    sem = asyncio.Semaphore(max(1, GOOGLE_PARALLEL))

    async def one(ch: str) -> bytes:
        q = urllib.parse.urlencode({'ie': 'UTF-8', 'q': ch, 'tl': g_lang, 'client': 'tw-ob'})
        url = f'https://translate.google.com/translate_tts?{q}'

        def fetch():
            req = urllib.request.Request(url, headers={'User-Agent': 'Mozilla/5.0'})
            with urllib.request.urlopen(req, timeout=30) as resp:
                return resp.read()

        async with sem:
            return await asyncio.to_thread(fetch)

    parts = await asyncio.gather(*[one(c) for c in chunks])
    with tempfile.TemporaryDirectory(prefix='mega-ghttp-') as td:
        paths = []
        for i, data in enumerate(parts):
            p = os.path.join(td, f'{i}.mp3')
            open(p, 'wb').write(data)
            paths.append(p)
        merged = os.path.join(td, 'm.mp3')
        if len(paths) == 1:
            shutil.copy(paths[0], merged)
        else:
            _concat_audio_files(paths, merged)
        ogg = os.path.join(td, 'o.ogg')
        try:
            _ffmpeg_to_ogg(merged, ogg)
            return open(ogg, 'rb').read()
        except Exception:
            return open(merged, 'rb').read()


async def synthesize_espeak(text: str, lang: str) -> bytes:
    es = _which('espeak-ng') or _which('espeak')
    if not es:
        raise RuntimeError('espeak not found')
    voice = 'fa' if lang == 'fa' else 'en'
    with tempfile.TemporaryDirectory(prefix='mega-esp-') as td:
        chunks = _chunk_text(text, 800)
        wavs = []
        for i, ch in enumerate(chunks):
            p = os.path.join(td, f'{i}.wav')
            await asyncio.to_thread(
                subprocess.run,
                [es, '-v', voice, '-s', '145', '-w', p, ch],
                check=True, capture_output=True, timeout=120,
            )
            wavs.append(p)
        merged = os.path.join(td, 'm.wav')
        if len(wavs) == 1:
            shutil.copy(wavs[0], merged)
        else:
            _concat_audio_files(wavs, merged)
        ogg = os.path.join(td, 'o.ogg')
        try:
            _ffmpeg_to_ogg(merged, ogg)
            return open(ogg, 'rb').read()
        except Exception:
            return open(merged, 'rb').read()


async def synthesize_persian(text: str = DEFAULT_TEXT) -> tuple[bytes, str]:
    text = normalize_tts_text(text or DEFAULT_TEXT) or DEFAULT_TEXT
    if len(text) > MAX_CHARS:
        text = text[:MAX_CHARS]
    lang = detect_lang(text)
    errors: list[str] = []

    # Persian short phrases → Piper (soft, medium-low speed)
    if lang == 'fa' and len(text) <= PIPER_MAX_CHARS:
        try:
            data = await synthesize_piper(text)
            if data and len(data) > 50:
                ext = 'ogg' if data[:4] == b'OggS' else 'wav'
                log.info(
                    'TTS engine=piper-fa chars=%s bytes=%s length_scale=%s',
                    len(text), len(data), PIPER_LENGTH_SCALE,
                )
                return data, f'voice.{ext}'
        except Exception as exc:
            errors.append(f'piper:{type(exc).__name__}')
            log.warning('piper failed (chars=%s): %s', len(text), exc)

    # 1) gTTS
    try:
        data = await synthesize_gtts(text, lang)
        if data and len(data) > 100:
            ext = 'ogg' if data[:4] == b'OggS' else 'mp3'
            log.info('TTS engine=gTTS-%s bytes=%s chars=%s', lang, len(data), len(text))
            return data, f'voice.{ext}'
    except Exception as exc:
        errors.append(f'gTTS:{type(exc).__name__}')
        log.warning('gTTS failed (%s): %s', lang, exc)

    # 2) Google HTTP
    try:
        data = await synthesize_google(text, lang)
        if data and len(data) > 100:
            ext = 'ogg' if data[:4] == b'OggS' else 'mp3'
            log.info('TTS engine=google-http-%s bytes=%s', lang, len(data))
            return data, f'voice.{ext}'
    except Exception as exc:
        errors.append(f'google:{type(exc).__name__}')
        log.warning('google-http failed: %s', exc)

    # 3) espeak
    try:
        data = await synthesize_espeak(text, lang)
        if data and len(data) > 50:
            ext = 'ogg' if data[:4] == b'OggS' else 'wav'
            log.info('TTS engine=espeak-%s bytes=%s', lang, len(data))
            return data, f'voice.{ext}'
    except Exception as exc:
        errors.append(f'espeak:{type(exc).__name__}')
        log.warning('espeak failed: %s', exc)

    raise RuntimeError(f'ساخت ویس ناموفق: {", ".join(errors) or "unknown"}')
