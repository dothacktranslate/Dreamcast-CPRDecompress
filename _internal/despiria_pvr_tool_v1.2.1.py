#!/usr/bin/env python3
"""
deSPIRIA Dreamcast PVR <-> PNG + AFS/CPR/PVP Tool v1.2.1
================================================

A round-trip converter for the Dreamcast PVR texture variants used by deSPIRIA.
It supports:

Pixel formats
  ARGB1555, RGB555, RGB565, ARGB4444
  YUV422 (decode/encode), bump maps (normal-map decode/encode)
  YUV420 (decode only), ARGB8888 and ABGR8888
  PAL4/PAL8 with external raw CLUT, PVP/PVPL, ACT, or PNG palettes

Data/layout formats
  square and rectangular twiddled textures
  linear rectangle and stride textures
  standard VQ and Small VQ
  indexed PAL4/PAL8 layouts
  ABGR8888 layouts
  supported mipmapped variants, including per-level PNG export

Complete edited mip-chain regeneration remains intentionally disabled because
it would require resampling and replacing every level rather than preserving the
original chain. Exported non-base mip levels are therefore inspection assets.

The tool auto-detects deSPIRIA's outer wrapper:
  uint32 decompressed_size + classic 4 KiB LZSS stream

Orientation semantics are explicit and stable:
  Decode: rotate clockwise first, then flip.
  Encode: undo the flip first, then undo the clockwise rotation.

For deSPIRIA's title/menu atlas, use:
  --rotate-cw 90 --flip horizontal

A JSON sidecar is written beside each PNG. It preserves the PVR header, GBIX,
wrapper, orientation, VQ codebook/index data, and palette information needed for
safe reinsertion. PVP/PVPL palette containers can also be inspected, converted
to editable swatch PNGs or ACT palettes, and rebuilt.

Additional decoder behavior for PVP, YUV, bump maps, and uncommon layouts was
implemented with reference to VincentNL's MIT-licensed pvr2image project. The
round-trip, AFS/CPR, sidecar, multi-PVR, and rebuilding architecture remains
specific to this tool.
"""

from __future__ import annotations

import argparse
import base64
import collections
import contextlib
import csv
import io
import tempfile
import hashlib
import json
import math
import os
import struct
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Iterable, Iterator, Optional, Sequence

try:
    from PIL import Image, ImageOps
except ImportError as exc:  # pragma: no cover - friendly CLI error
    raise SystemExit("Pillow is required. Install it with: python -m pip install Pillow") from exc

TOOL_NAME = "deSPIRIA Dreamcast PVR <-> PNG + AFS/CPR/PVP Tool"
TOOL_VERSION = "1.2.1"

# Standard Dreamcast PVR pixel formats plus the extended numeric conventions
# used by VincentNL's MIT-licensed pvr2image decoder. Codes 0x05 and 0x06 are
# ambiguous: indexed textures are identified by their DATA format, while
# non-indexed textures may use the extended RGB555 / YUV420 convention.
PIXEL_FORMATS: dict[int, str] = {
    0x00: "argb1555",
    0x01: "rgb565",
    0x02: "argb4444",
    0x03: "yuv422",
    0x04: "bump",
    0x05: "rgb555_or_pal4",
    0x06: "yuv420_or_pal8",
    0x07: "argb8888",
}
ENCODE_PIXEL_FORMAT_CODES: dict[str, int] = {
    "argb1555": 0x00,
    "rgb565": 0x01,
    "argb4444": 0x02,
    "yuv422": 0x03,
    "bump": 0x04,
    "rgb555": 0x05,
    "yuv420": 0x06,
    "argb8888": 0x07,
    "pal4": 0x05,
    "pal8": 0x06,
}
PALETTE_FORMAT_CODES: dict[str, int] = {
    "argb1555": 0x00,
    "rgb565": 0x01,
    "argb4444": 0x02,
    "rgb555": 0x05,
}

DATA_FORMATS: dict[int, str] = {
    0x01: "twiddled",
    0x02: "twiddled_mipmaps",
    0x03: "vq",
    0x04: "vq_mipmaps",
    0x05: "pal4_twiddled",
    0x06: "pal4_twiddled_mipmaps",
    0x07: "pal8_twiddled",
    0x08: "pal8_twiddled_mipmaps",
    0x09: "linear_rectangle",
    0x0A: "linear_rectangle_mipmaps",
    0x0B: "linear_stride",
    0x0C: "linear_stride_mipmaps",
    0x0D: "twiddled_rectangle",
    0x0E: "abgr8888",
    0x0F: "abgr8888_mipmaps",
    0x10: "small_vq",
    0x11: "small_vq_mipmaps",
    0x12: "twiddled_alias_mipmaps",
}

MIPMAPPED_FORMATS = {0x02, 0x04, 0x06, 0x08, 0x0A, 0x0C, 0x0F, 0x11, 0x12}
VQ_FORMATS = {0x03, 0x04, 0x10, 0x11}
INDEXED_FORMATS = {0x05, 0x06, 0x07, 0x08}
TWIDDLED_FORMATS = {0x01, 0x02, 0x05, 0x06, 0x07, 0x08, 0x0D, 0x12}
LINEAR_FORMATS = {0x09, 0x0A, 0x0B, 0x0C}
ABGR_FORMATS = {0x0E, 0x0F}
SUPPORTED_PIXEL_FORMATS = set(PIXEL_FORMATS)
SUPPORTED_DATA_FORMATS = set(DATA_FORMATS)

# PVP (PVPL) palette-container conventions used by pvr2image.
PVP_PIXEL_TYPES: dict[int, str] = {
    0x00: "rgb555",
    0x01: "rgb565",
    0x02: "argb4444",
    0x06: "argb8888",
}
PVP_PIXEL_TYPE_CODES = {v: k for k, v in PVP_PIXEL_TYPES.items()}


FLIP_NAMES = ("none", "horizontal", "vertical", "both")
ROTATIONS = (0, 90, 180, 270)


class PvrError(RuntimeError):
    """Raised for a controlled PVR conversion failure."""


@dataclass
class PvrChunk:
    chunk_index: int
    start: int
    pvrt_offset: int
    end: int
    gbix_present: bool
    gbix_length: int
    global_index: Optional[int]
    gbix_tail: Optional[int]
    pvrt_length_field: int
    pixel_format: int
    data_format: int
    reserved: int
    width: int
    height: int
    payload: bytes

    @property
    def pixel_format_name(self) -> str:
        if self.is_indexed:
            is_4bit = self.data_format in (0x05, 0x06)
            return "pal4" if is_4bit else "pal8"
        if self.pixel_format == 0x05:
            return "rgb555"
        if self.pixel_format == 0x06:
            return "yuv420"
        return PIXEL_FORMATS.get(self.pixel_format, f"unknown_0x{self.pixel_format:02X}")

    @property
    def data_format_name(self) -> str:
        return DATA_FORMATS.get(self.data_format, f"unknown_0x{self.data_format:02X}")

    @property
    def is_mipmapped(self) -> bool:
        return self.data_format in MIPMAPPED_FORMATS

    @property
    def is_vq(self) -> bool:
        return self.data_format in VQ_FORMATS

    @property
    def is_indexed(self) -> bool:
        return self.data_format in INDEXED_FORMATS


@dataclass
class WrapperInfo:
    kind: str
    compressed_size: int
    decompressed_size: int


@dataclass
class PvpPalette:
    pixel_type: int
    format_name: str
    entry_count: int
    colors: list[tuple[int, int, int, int]]
    header_tail: bytes
    length_field: int



# ---------------------------------------------------------------------------
# General helpers
# ---------------------------------------------------------------------------


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def b64e(data: bytes) -> str:
    return base64.b64encode(data).decode("ascii")


def b64d(text: str | None) -> bytes:
    if not text:
        return b""
    return base64.b64decode(text.encode("ascii"))


def parse_int(text: str) -> int:
    try:
        return int(text, 0)
    except ValueError as exc:
        raise argparse.ArgumentTypeError(f"invalid integer: {text!r}") from exc


def ensure_parent(path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)


def image_data(image: Image.Image) -> list[Any]:
    """Return flattened image data without Pillow's deprecated getdata warning."""
    getter = getattr(image, "get_flattened_data", None)
    if getter is not None:
        return list(getter())
    return list(image.getdata())


def is_power_of_two(value: int) -> bool:
    return value > 0 and (value & (value - 1)) == 0


def require_power_of_two(width: int, height: int, what: str) -> None:
    if not is_power_of_two(width) or not is_power_of_two(height):
        raise PvrError(f"{what} requires power-of-two dimensions; got {width}x{height}")


# ---------------------------------------------------------------------------
# deSPIRIA outer LZSS wrapper
# ---------------------------------------------------------------------------


def lzss_decompress(data: bytes) -> bytes:
    if len(data) < 5:
        raise PvrError("LZSS input is too short")
    target_size = struct.unpack_from("<I", data, 0)[0]
    if target_size <= 0:
        raise PvrError(f"invalid LZSS decompressed size: {target_size}")

    ring = bytearray(4096)
    ring_pos = 0xFEE
    src_pos = 4
    out = bytearray()

    while src_pos < len(data) and len(out) < target_size:
        flags = data[src_pos]
        src_pos += 1
        for bit in range(8):
            if flags & (1 << bit):
                if src_pos >= len(data):
                    raise PvrError("truncated LZSS literal")
                value = data[src_pos]
                src_pos += 1
                out.append(value)
                ring[ring_pos] = value
                ring_pos = (ring_pos + 1) & 0xFFF
            else:
                if src_pos + 1 >= len(data):
                    raise PvrError("truncated LZSS back-reference")
                b0 = data[src_pos]
                b1 = data[src_pos + 1]
                src_pos += 2
                offset = b0 | ((b1 & 0xF0) << 4)
                length = (b1 & 0x0F) + 3
                for i in range(length):
                    value = ring[(offset + i) & 0xFFF]
                    out.append(value)
                    ring[ring_pos] = value
                    ring_pos = (ring_pos + 1) & 0xFFF
                    if len(out) >= target_size:
                        break
            if len(out) >= target_size:
                break

    if len(out) != target_size:
        raise PvrError(
            f"LZSS stream ended at {len(out):,} bytes; expected {target_size:,}"
        )
    return bytes(out)


def _match_length(data: bytes, current: int, candidate: int, max_length: int = 18) -> int:
    """Find an LZSS match, including legal self-overlap/repetition."""
    distance = current - candidate
    if distance <= 0 or distance > 4096:
        return 0
    limit = min(max_length, len(data) - current)
    length = 0
    while length < limit:
        source_index = candidate + (length % distance)
        if data[current + length] != data[source_index]:
            break
        length += 1
    return length


def lzss_compress(raw: bytes) -> bytes:
    """
    Compress using the exact stream grammar used by deSPIRIA.

    The compressor is deterministic and greedy. It does not attempt to reproduce
    ATLUS's original byte stream; decompression is lossless and game-compatible.
    """
    if len(raw) > 0xFFFFFFFF:
        raise PvrError("input is too large for the 32-bit deSPIRIA LZSS wrapper")

    history: dict[bytes, collections.deque[int]] = collections.defaultdict(collections.deque)

    def add_position(pos: int) -> None:
        if pos + 2 >= len(raw):
            return
        key = raw[pos : pos + 3]
        dq = history[key]
        dq.append(pos)
        cutoff = pos - 4096
        while dq and dq[0] < cutoff:
            dq.popleft()
        # A short candidate list is much faster and has negligible size impact.
        while len(dq) > 96:
            dq.popleft()

    out = bytearray(struct.pack("<I", len(raw)))
    pos = 0

    while pos < len(raw):
        flags_pos = len(out)
        out.append(0)
        flags = 0

        for bit in range(8):
            if pos >= len(raw):
                break

            best_length = 0
            best_candidate = -1
            if pos + 2 < len(raw):
                key = raw[pos : pos + 3]
                dq = history.get(key)
                if dq:
                    cutoff = pos - 4096
                    while dq and dq[0] < cutoff:
                        dq.popleft()
                    # Newest candidates usually yield the longest useful match.
                    for candidate in reversed(dq):
                        length = _match_length(raw, pos, candidate)
                        if length > best_length:
                            best_length = length
                            best_candidate = candidate
                            if best_length == 18:
                                break

            if best_length >= 3:
                ring_offset = (0xFEE + best_candidate) & 0xFFF
                out.append(ring_offset & 0xFF)
                out.append(((ring_offset >> 4) & 0xF0) | (best_length - 3))
                old_pos = pos
                pos += best_length
                for p in range(old_pos, pos):
                    add_position(p)
            else:
                flags |= 1 << bit
                out.append(raw[pos])
                add_position(pos)
                pos += 1

        out[flags_pos] = flags

    return bytes(out)


def unwrap_data(data: bytes, requested: str = "auto") -> tuple[bytes, WrapperInfo]:
    if requested not in ("auto", "none", "despiria-lzss"):
        raise PvrError(f"unknown wrapper mode: {requested}")

    if requested == "none":
        return data, WrapperInfo("none", len(data), len(data))

    if requested == "despiria-lzss":
        raw = lzss_decompress(data)
        return raw, WrapperInfo("despiria-lzss", len(data), len(raw))

    # Auto: ordinary PVR/container data has a PVRT near its beginning.
    if data.find(b"PVRT", 0, 64) >= 0:
        return data, WrapperInfo("none", len(data), len(data))

    if len(data) >= 8:
        expected = struct.unpack_from("<I", data, 0)[0]
        if 0x10 <= expected <= 0x40000000 and expected > len(data):
            try:
                raw = lzss_decompress(data)
            except PvrError:
                raw = b""
            if raw.find(b"PVRT", 0, 256) >= 0:
                return raw, WrapperInfo("despiria-lzss", len(data), len(raw))

    return data, WrapperInfo("none", len(data), len(data))


def apply_wrapper(raw: bytes, kind: str) -> bytes:
    if kind == "none":
        return raw
    if kind == "despiria-lzss":
        return lzss_compress(raw)
    raise PvrError(f"unsupported wrapper: {kind}")


# ---------------------------------------------------------------------------
# PVR container parsing
# ---------------------------------------------------------------------------


def scan_pvr_chunks(data: bytes) -> list[PvrChunk]:
    chunks: list[PvrChunk] = []
    search_pos = 0

    while True:
        pvrt = data.find(b"PVRT", search_pos)
        if pvrt < 0:
            break
        if pvrt + 16 > len(data):
            break

        length_field = struct.unpack_from("<I", data, pvrt + 4)[0]
        end = pvrt + 8 + length_field
        if length_field < 8 or end > len(data):
            search_pos = pvrt + 4
            continue

        pixel_format = data[pvrt + 8]
        data_format = data[pvrt + 9]
        reserved = struct.unpack_from("<H", data, pvrt + 10)[0]
        width, height = struct.unpack_from("<HH", data, pvrt + 12)
        if width == 0 or height == 0:
            search_pos = pvrt + 4
            continue

        gbix_present = False
        gbix_length = 0
        global_index: Optional[int] = None
        gbix_tail: Optional[int] = None
        start = pvrt

        # Standard GBIX is 16 bytes immediately before PVRT. A trimmed GBIX may
        # be 12 bytes; preserve either form if present.
        for candidate in (pvrt - 16, pvrt - 12):
            if candidate >= 0 and data[candidate : candidate + 4] == b"GBIX":
                declared = struct.unpack_from("<I", data, candidate + 4)[0]
                candidate_end = candidate + 8 + declared
                if candidate_end == pvrt and declared >= 4:
                    gbix_present = True
                    gbix_length = 8 + declared
                    global_index = struct.unpack_from("<I", data, candidate + 8)[0]
                    if declared >= 8:
                        gbix_tail = struct.unpack_from("<I", data, candidate + 12)[0]
                    start = candidate
                    break

        payload = data[pvrt + 16 : end]
        chunks.append(
            PvrChunk(
                chunk_index=len(chunks),
                start=start,
                pvrt_offset=pvrt,
                end=end,
                gbix_present=gbix_present,
                gbix_length=gbix_length,
                global_index=global_index,
                gbix_tail=gbix_tail,
                pvrt_length_field=length_field,
                pixel_format=pixel_format,
                data_format=data_format,
                reserved=reserved,
                width=width,
                height=height,
                payload=payload,
            )
        )
        search_pos = end

    return chunks


def select_chunk(chunks: Sequence[PvrChunk], index: Optional[int]) -> PvrChunk:
    if not chunks:
        raise PvrError("no valid PVRT chunk was found")
    if index is None:
        if len(chunks) != 1:
            details = ", ".join(
                f"{c.chunk_index}:{c.width}x{c.height}/{c.pixel_format_name}/{c.data_format_name}"
                for c in chunks
            )
            raise PvrError(
                f"the file contains {len(chunks)} PVR chunks ({details}); select one with --index"
            )
        return chunks[0]
    if index < 0 or index >= len(chunks):
        raise PvrError(f"PVR index {index} is out of range; file contains {len(chunks)} chunks")
    return chunks[index]


def build_pvr_chunk(
    payload: bytes,
    *,
    pixel_format: int,
    data_format: int,
    width: int,
    height: int,
    reserved: int = 0,
    gbix_present: bool = True,
    global_index: int = 0,
    gbix_tail: int = 0,
    gbix_length: int = 16,
) -> bytes:
    result = bytearray()
    if gbix_present:
        if gbix_length == 12:
            result += b"GBIX" + struct.pack("<I", 4) + struct.pack("<I", global_index)
        else:
            result += (
                b"GBIX"
                + struct.pack("<I", 8)
                + struct.pack("<I", global_index)
                + struct.pack("<I", gbix_tail)
            )

    pvrt_payload_length = 8 + len(payload)
    result += b"PVRT"
    result += struct.pack("<I", pvrt_payload_length)
    result += bytes((pixel_format & 0xFF, data_format & 0xFF))
    result += struct.pack("<H", reserved & 0xFFFF)
    result += struct.pack("<HH", width, height)
    result += payload
    return bytes(result)


# ---------------------------------------------------------------------------
# Pixel formats
# ---------------------------------------------------------------------------


def unpack_16(value: int, pixel_format: int) -> tuple[int, int, int, int]:
    if pixel_format == 0x00:  # ARGB1555
        a = 255 if value & 0x8000 else 0
        r = ((value >> 10) & 0x1F) * 255 // 31
        g = ((value >> 5) & 0x1F) * 255 // 31
        b = (value & 0x1F) * 255 // 31
        return r, g, b, a
    if pixel_format == 0x01:  # RGB565
        r = ((value >> 11) & 0x1F) * 255 // 31
        g = ((value >> 5) & 0x3F) * 255 // 63
        b = (value & 0x1F) * 255 // 31
        return r, g, b, 255
    if pixel_format == 0x02:  # ARGB4444
        a = ((value >> 12) & 0x0F) * 17
        r = ((value >> 8) & 0x0F) * 17
        g = ((value >> 4) & 0x0F) * 17
        b = (value & 0x0F) * 17
        return r, g, b, a
    if pixel_format == 0x05:  # Extended RGB555 convention
        r = ((value >> 10) & 0x1F) * 255 // 31
        g = ((value >> 5) & 0x1F) * 255 // 31
        b = (value & 0x1F) * 255 // 31
        return r, g, b, 255
    raise PvrError(f"16-bit conversion is unsupported for pixel format 0x{pixel_format:02X}")


def _quantize_channel(value: int, maximum: int) -> int:
    value = 0 if value < 0 else 255 if value > 255 else value
    return (value * maximum + 127) // 255


def pack_16(rgba: Sequence[int], pixel_format: int) -> int:
    r, g, b, a = (int(v) for v in rgba)
    if pixel_format == 0x00:
        return (
            (0x8000 if a >= 128 else 0)
            | (_quantize_channel(r, 31) << 10)
            | (_quantize_channel(g, 31) << 5)
            | _quantize_channel(b, 31)
        )
    if pixel_format == 0x01:
        return (
            (_quantize_channel(r, 31) << 11)
            | (_quantize_channel(g, 63) << 5)
            | _quantize_channel(b, 31)
        )
    if pixel_format == 0x02:
        return (
            (_quantize_channel(a, 15) << 12)
            | (_quantize_channel(r, 15) << 8)
            | (_quantize_channel(g, 15) << 4)
            | _quantize_channel(b, 15)
        )
    if pixel_format == 0x05:
        return (
            (_quantize_channel(r, 31) << 10)
            | (_quantize_channel(g, 31) << 5)
            | _quantize_channel(b, 31)
        )
    raise PvrError(f"16-bit conversion is unsupported for pixel format 0x{pixel_format:02X}")


def unpack_argb8888(value: int) -> tuple[int, int, int, int]:
    a = (value >> 24) & 0xFF
    r = (value >> 16) & 0xFF
    g = (value >> 8) & 0xFF
    b = value & 0xFF
    return r, g, b, a


def pack_argb8888(rgba: Sequence[int]) -> int:
    r, g, b, a = (max(0, min(255, int(v))) for v in rgba)
    return (a << 24) | (r << 16) | (g << 8) | b


def unpack_abgr8888(value: int) -> tuple[int, int, int, int]:
    # pvr2image's ABGR/BMP layout reads a little-endian word as R,G,B,A
    # from most-significant to least-significant bytes.
    r = (value >> 24) & 0xFF
    g = (value >> 16) & 0xFF
    b = (value >> 8) & 0xFF
    a = value & 0xFF
    return r, g, b, a


def pack_abgr8888(rgba: Sequence[int]) -> int:
    r, g, b, a = (max(0, min(255, int(v))) for v in rgba)
    return (r << 24) | (g << 16) | (b << 8) | a


def rgba_bytes_to_packed(image: Image.Image, pixel_format: int) -> list[int]:
    rgba = image.convert("RGBA")
    if pixel_format == 0x07:
        return [pack_argb8888(pixel) for pixel in image_data(rgba)]
    return [pack_16(pixel, pixel_format) for pixel in image_data(rgba)]


def packed_to_rgba_image(values: Sequence[int], width: int, height: int, pixel_format: int) -> Image.Image:
    if len(values) != width * height:
        raise PvrError(f"pixel count mismatch: got {len(values)}, expected {width * height}")
    image = Image.new("RGBA", (width, height))
    if pixel_format == 0x07:
        image.putdata([unpack_argb8888(v) for v in values])
    else:
        image.putdata([unpack_16(v, pixel_format) for v in values])
    return image


def infer_pixel_format(image: Image.Image) -> int:
    rgba = image.convert("RGBA")
    alpha_values = set(image_data(rgba.getchannel("A")))
    if alpha_values == {255}:
        return 0x01
    if alpha_values.issubset({0, 255}):
        return 0x00
    return 0x02


def clamp_u8(value: float | int) -> int:
    return max(0, min(255, int(round(value))))


def yuv422_pair_to_rgba(yuv0: int, yuv1: int) -> tuple[tuple[int, int, int, int], tuple[int, int, int, int]]:
    y0 = (yuv0 >> 8) & 0xFF
    u = yuv0 & 0xFF
    y1 = (yuv1 >> 8) & 0xFF
    v = yuv1 & 0xFF
    c0, c1 = y0 - 16, y1 - 16
    d, e = u - 128, v - 128

    def one(c: int) -> tuple[int, int, int, int]:
        r = clamp_u8((298 * c + 409 * e + 128) / 256)
        g = clamp_u8((298 * c - 100 * d - 208 * e + 128) / 256)
        b = clamp_u8((298 * c + 516 * d + 128) / 256)
        return r, g, b, 255

    return one(c0), one(c1)


def rgb_to_yuv_limited(r: int, g: int, b: int) -> tuple[int, int, int]:
    # ITU-R BT.601 studio-range conversion, matching the decoder above.
    y = 16.0 + (65.738 * r + 129.057 * g + 25.064 * b) / 256.0
    u = 128.0 + (-37.945 * r - 74.494 * g + 112.439 * b) / 256.0
    v = 128.0 + (112.439 * r - 94.154 * g - 18.285 * b) / 256.0
    return clamp_u8(y), clamp_u8(u), clamp_u8(v)


def decode_yuv422_words(words: Sequence[int], width: int, height: int) -> Image.Image:
    if width % 2:
        raise PvrError("YUV422 requires an even texture width")
    if len(words) < width * height:
        raise PvrError("YUV422 payload is shorter than the texture dimensions require")
    pixels: list[tuple[int, int, int, int]] = []
    for i in range(0, width * height, 2):
        p0, p1 = yuv422_pair_to_rgba(words[i], words[i + 1])
        pixels.extend((p0, p1))
    image = Image.new("RGBA", (width, height))
    image.putdata(pixels)
    return image


def encode_yuv422_words(image: Image.Image) -> list[int]:
    rgba = image.convert("RGBA")
    if rgba.width % 2:
        raise PvrError("YUV422 requires an even texture width")
    pixels = image_data(rgba)
    words: list[int] = []
    for y in range(rgba.height):
        row = y * rgba.width
        for x in range(0, rgba.width, 2):
            r0, g0, b0, _ = pixels[row + x]
            r1, g1, b1, _ = pixels[row + x + 1]
            y0, u0, v0 = rgb_to_yuv_limited(r0, g0, b0)
            y1, u1, v1 = rgb_to_yuv_limited(r1, g1, b1)
            u = (u0 + u1 + 1) // 2
            v = (v0 + v1 + 1) // 2
            words.extend(((y0 << 8) | u, (y1 << 8) | v))
    return words


def bump_word_to_normal(value: int) -> tuple[int, int, int, int]:
    # Formula credited by pvr2image to tvspelsfreak. The high byte is the
    # elevation-like S component; the low byte is the azimuth-like R component.
    s = (1.0 - ((value >> 8) / 255.0)) * math.pi / 2.0
    r_byte = value & 0xFF
    angle = (r_byte / 255.0) * 2.0 * math.pi
    nx = math.sin(s) * math.cos(angle)
    ny = math.sin(s) * math.sin(angle)
    nz = math.cos(s)
    return clamp_u8((nx + 1.0) * 127.5), clamp_u8((ny + 1.0) * 127.5), clamp_u8((nz + 1.0) * 127.5), 255


def normal_to_bump_word(rgba: Sequence[int]) -> int:
    r, g, b, _a = (int(v) for v in rgba)
    nx = r / 127.5 - 1.0
    ny = g / 127.5 - 1.0
    nz = b / 127.5 - 1.0
    length = math.sqrt(nx * nx + ny * ny + nz * nz)
    if length <= 1e-8:
        nx, ny, nz = 0.0, 0.0, 1.0
    else:
        nx, ny, nz = nx / length, ny / length, nz / length
    s = math.acos(max(-1.0, min(1.0, nz)))
    s_byte = clamp_u8((1.0 - (s / (math.pi / 2.0))) * 255.0)
    angle = math.atan2(ny, nx)
    if angle < 0:
        angle += 2.0 * math.pi
    r_byte = clamp_u8(angle / (2.0 * math.pi) * 255.0)
    return (s_byte << 8) | r_byte


def decode_bump_words(words: Sequence[int], width: int, height: int) -> Image.Image:
    if len(words) < width * height:
        raise PvrError("bump-map payload is shorter than the texture dimensions require")
    image = Image.new("RGBA", (width, height))
    image.putdata([bump_word_to_normal(v) for v in words[: width * height]])
    return image


def encode_bump_words(image: Image.Image) -> list[int]:
    return [normal_to_bump_word(pixel) for pixel in image_data(image.convert("RGBA"))]


def decode_yuv420_payload(payload: bytes, width: int, height: int) -> Image.Image:
    """Decode the Naomi/Dreamcast 16x16 macroblock YUV420 layout.

    Each macroblock stores one 8x8 U block, one 8x8 V block, then four 8x8
    luma blocks arranged as the upper-left, upper-right, lower-left, and
    lower-right quadrants of a 16x16 tile. Macroblocks are ordered left to
    right within each 16-pixel-high row.
    """
    if width % 16 or height % 16:
        raise PvrError("YUV420 decoding requires width and height divisible by 16")

    columns, block_rows = width // 16, height // 16
    expected = width * height * 3 // 2
    if len(payload) < expected:
        raise PvrError(f"YUV420 payload has {len(payload)} bytes; {expected} required")

    stream = io.BytesIO(payload)
    u_rows = [bytearray() for _ in range(height // 2)]
    v_rows = [bytearray() for _ in range(height // 2)]
    y_plane = bytearray()

    for block_row in range(block_rows):
        upper_y = [bytearray() for _ in range(8)]
        lower_y = [bytearray() for _ in range(8)]
        chroma_row = block_row * 8

        for _block_col in range(columns):
            for row_index in range(8):
                chunk = stream.read(8)
                if len(chunk) != 8:
                    raise PvrError("truncated YUV420 U macroblock data")
                u_rows[chroma_row + row_index] += chunk

            for row_index in range(8):
                chunk = stream.read(8)
                if len(chunk) != 8:
                    raise PvrError("truncated YUV420 V macroblock data")
                v_rows[chroma_row + row_index] += chunk

            # Two 8x8 luma blocks form the upper half of the 16x16 tile.
            for _quadrant in range(2):
                for row_index in range(8):
                    chunk = stream.read(8)
                    if len(chunk) != 8:
                        raise PvrError("truncated YUV420 upper-luma macroblock data")
                    upper_y[row_index] += chunk

            # Two more 8x8 blocks form the lower half.
            for _quadrant in range(2):
                for row_index in range(8):
                    chunk = stream.read(8)
                    if len(chunk) != 8:
                        raise PvrError("truncated YUV420 lower-luma macroblock data")
                    lower_y[row_index] += chunk

        y_plane += b"".join(upper_y)
        y_plane += b"".join(lower_y)

    u_plane = b"".join(u_rows)
    v_plane = b"".join(v_rows)
    if (
        len(y_plane) != width * height
        or len(u_plane) != width * height // 4
        or len(v_plane) != width * height // 4
    ):
        raise PvrError("YUV420 planes are incomplete")

    pixels: list[tuple[int, int, int, int]] = []
    for y in range(height):
        for x in range(width):
            yy = y_plane[y * width + x]
            uv_index = (y // 2) * (width // 2) + (x // 2)
            u = u_plane[uv_index]
            v = v_plane[uv_index]
            r = clamp_u8(yy + 1.402 * (v - 128))
            g = clamp_u8(yy - 0.344136 * (u - 128) - 0.714136 * (v - 128))
            b = clamp_u8(yy + 1.772 * (u - 128))
            pixels.append((r, g, b, 255))

    image = Image.new("RGBA", (width, height))
    image.putdata(pixels)
    return image


# ---------------------------------------------------------------------------
# Twiddling
# ---------------------------------------------------------------------------


def morton_index(x: int, y: int) -> int:
    result = 0
    bit = 0
    maximum = max(x, y)
    while (1 << bit) <= maximum:
        result |= ((x >> bit) & 1) << (2 * bit)
        result |= ((y >> bit) & 1) << (2 * bit + 1)
        bit += 1
    return result


def twiddled_index(x: int, y: int, width: int, height: int) -> int:
    """Morton order with square tiles along the longer rectangular dimension."""
    require_power_of_two(width, height, "twiddled texture")
    side = min(width, height)
    if width >= height:
        tile = x // side
        local_x = x % side
        local_y = y
    else:
        tile = y // side
        local_x = x
        local_y = y % side
    return tile * side * side + morton_index(local_x, local_y)


def untwiddle_values(stored: Sequence[int], width: int, height: int) -> list[int]:
    if len(stored) < width * height:
        raise PvrError("twiddled payload is shorter than the texture dimensions require")
    linear = [0] * (width * height)
    for y in range(height):
        row = y * width
        for x in range(width):
            linear[row + x] = stored[twiddled_index(x, y, width, height)]
    return linear


def twiddle_values(linear: Sequence[int], width: int, height: int) -> list[int]:
    if len(linear) != width * height:
        raise PvrError("linear pixel count does not match dimensions")
    stored = [0] * (width * height)
    for y in range(height):
        row = y * width
        for x in range(width):
            stored[twiddled_index(x, y, width, height)] = linear[row + x]
    return stored


DETWIDDLE_MODES = ("morton", "reference", "compare", "stride-fallback")


def _reference_square_order(side: int, x0: int = 0, y0: int = 0) -> list[tuple[int, int]]:
    """Independent recursive Z-order generator used to cross-check Morton math."""
    if side == 1:
        return [(x0, y0)]
    half = side // 2
    result: list[tuple[int, int]] = []
    # Morton order interleaves x first, then y: TL, TR, BL, BR.
    result.extend(_reference_square_order(half, x0, y0))
    result.extend(_reference_square_order(half, x0 + half, y0))
    result.extend(_reference_square_order(half, x0, y0 + half))
    result.extend(_reference_square_order(half, x0 + half, y0 + half))
    return result


def reference_twiddled_indices(width: int, height: int) -> list[int]:
    if not is_power_of_two(width) or not is_power_of_two(height):
        return list(range(width * height))
    side = min(width, height)
    coords: list[tuple[int, int]] = []
    if width >= height:
        for tile in range(width // side):
            coords.extend((x + tile * side, y) for x, y in _reference_square_order(side))
    else:
        for tile in range(height // side):
            coords.extend((x, y + tile * side) for x, y in _reference_square_order(side))
    # coords are storage-order coordinates; invert into linear-position -> storage-index.
    result = [0] * (width * height)
    for storage_index, (x, y) in enumerate(coords):
        result[y * width + x] = storage_index
    return result


def untwiddle_values_mode(
    stored: Sequence[int], width: int, height: int, mode: str = "morton"
) -> list[int]:
    if mode not in DETWIDDLE_MODES:
        raise PvrError(f"unknown detwiddle mode: {mode}")
    if not is_power_of_two(width) or not is_power_of_two(height):
        if mode == "stride-fallback":
            if len(stored) < width * height:
                raise PvrError("payload is shorter than the texture dimensions require")
            return list(stored[: width * height])
        raise PvrError(
            f"twiddled decoding requires power-of-two dimensions; got {width}x{height}. "
            "Use --detwiddle stride-fallback only when the source is known to be stored linearly."
        )
    morton = untwiddle_values(stored, width, height)
    if mode == "morton":
        return morton
    indices = reference_twiddled_indices(width, height)
    reference = [stored[index] for index in indices]
    if mode == "reference":
        return reference
    if reference != morton:
        first = next(i for i, (a, b) in enumerate(zip(morton, reference)) if a != b)
        raise PvrError(
            f"detwiddle cross-check failed at linear pixel {first}: "
            f"Morton={morton[first]!r}, reference={reference[first]!r}"
        )
    return morton


# ---------------------------------------------------------------------------
# Palettes / CLUTs
# ---------------------------------------------------------------------------


def decode_palette_bytes(data: bytes, count: int, palette_format: str) -> list[tuple[int, int, int, int]]:
    if palette_format == "argb8888":
        needed = count * 4
        if len(data) < needed:
            raise PvrError(f"palette has {len(data)} bytes; {needed} are required")
        return [unpack_argb8888(struct.unpack_from("<I", data, i * 4)[0]) for i in range(count)]

    pixel_format = PALETTE_FORMAT_CODES.get(palette_format)
    if pixel_format not in (0x00, 0x01, 0x02, 0x05):
        raise PvrError(f"unsupported palette format: {palette_format}")
    needed = count * 2
    if len(data) < needed:
        raise PvrError(f"palette has {len(data)} bytes; {needed} are required")
    values = struct.unpack_from(f"<{count}H", data, 0)
    return [unpack_16(v, pixel_format) for v in values]


def encode_palette_bytes(colors: Sequence[Sequence[int]], palette_format: str) -> bytes:
    if palette_format == "argb8888":
        return struct.pack(f"<{len(colors)}I", *(pack_argb8888(c) for c in colors))

    pixel_format = PALETTE_FORMAT_CODES.get(palette_format)
    if pixel_format not in (0x00, 0x01, 0x02, 0x05):
        raise PvrError(f"unsupported palette format: {palette_format}")
    return struct.pack(f"<{len(colors)}H", *(pack_16(c, pixel_format) for c in colors))


def parse_pvp(data: bytes) -> PvpPalette:
    if len(data) < 16 or data[:4] != b"PVPL":
        raise PvrError("not a valid PVPL/PVP palette container")
    length_field = struct.unpack_from("<I", data, 4)[0]
    pixel_type = data[8]
    format_name = PVP_PIXEL_TYPES.get(pixel_type)
    if format_name is None:
        raise PvrError(f"unsupported PVP pixel type 0x{pixel_type:02X}")
    entry_count = struct.unpack_from("<H", data, 14)[0]
    if entry_count <= 0:
        raise PvrError("PVP palette contains zero entries")
    bytes_per_entry = 4 if format_name == "argb8888" else 2
    needed = 16 + entry_count * bytes_per_entry
    if len(data) < needed:
        raise PvrError(f"PVP is truncated: {len(data)} bytes, {needed} required")
    colors = decode_palette_bytes(data[16:needed], entry_count, format_name)
    return PvpPalette(
        pixel_type=pixel_type,
        format_name=format_name,
        entry_count=entry_count,
        colors=colors,
        header_tail=data[9:14],
        length_field=length_field,
    )


def build_pvp(
    colors: Sequence[Sequence[int]],
    palette_format: str,
    *,
    header_tail: bytes = b"\x00" * 5,
) -> bytes:
    if palette_format not in PVP_PIXEL_TYPE_CODES:
        raise PvrError(
            "PVP supports rgb555, rgb565, argb4444, or argb8888 palettes"
        )
    if len(colors) > 0xFFFF:
        raise PvrError("PVP palette has too many entries")
    tail = bytes(header_tail[:5]).ljust(5, b"\x00")
    palette_data = encode_palette_bytes(colors, palette_format)
    body = bytes((PVP_PIXEL_TYPE_CODES[palette_format],)) + tail + struct.pack("<H", len(colors)) + palette_data
    return b"PVPL" + struct.pack("<I", len(body)) + body


def palette_to_act(colors: Sequence[Sequence[int]]) -> bytes:
    out = bytearray()
    for color in list(colors)[:256]:
        r, g, b, _a = (int(v) for v in color)
        out.extend((r, g, b))
    return bytes(out).ljust(768, b"\x00")


def act_to_palette(data: bytes, count: int) -> list[tuple[int, int, int, int]]:
    if len(data) < min(count * 3, 768):
        raise PvrError("ACT palette is too short")
    return [
        (data[i * 3], data[i * 3 + 1], data[i * 3 + 2], 255)
        for i in range(count)
    ]


def palette_swatch_image(
    colors: Sequence[Sequence[int]], columns: int = 16, cell_size: int = 16
) -> Image.Image:
    if columns <= 0 or cell_size <= 0:
        raise PvrError("palette columns and cell size must be positive")
    count = len(colors)
    rows = max(1, (count + columns - 1) // columns)
    image = Image.new("RGBA", (columns * cell_size, rows * cell_size), (0, 0, 0, 0))
    px = image.load()
    for index, color in enumerate(colors):
        x0 = (index % columns) * cell_size
        y0 = (index // columns) * cell_size
        rgba = tuple(int(v) for v in color)
        for y in range(y0, y0 + cell_size):
            for x in range(x0, x0 + cell_size):
                px[x, y] = rgba
    return image


def palette_from_swatch_image(
    image: Image.Image, count: int, columns: int = 16, cell_size: int = 16
) -> list[tuple[int, int, int, int]]:
    rgba = image.convert("RGBA")
    rows = max(1, (count + columns - 1) // columns)
    if rgba.width < columns * cell_size or rgba.height < rows * cell_size:
        raise PvrError("palette swatch PNG is smaller than the requested grid")
    colors: list[tuple[int, int, int, int]] = []
    for index in range(count):
        x = (index % columns) * cell_size + cell_size // 2
        y = (index // columns) * cell_size + cell_size // 2
        colors.append(tuple(rgba.getpixel((x, y))))
    return colors


def find_companion_pvp(path: Path) -> Optional[Path]:
    for suffix in (".pvp", ".PVP"):
        candidate = path.with_suffix(suffix)
        if candidate.exists():
            return candidate
    return None


def load_palette(path: Path, count: int, palette_format: str) -> list[tuple[int, int, int, int]]:
    if not path.exists():
        raise PvrError(f"palette file does not exist: {path}")
    suffix = path.suffix.lower()
    if suffix == ".pvp":
        pvp = parse_pvp(path.read_bytes())
        if pvp.entry_count < count:
            raise PvrError(
                f"PVP has {pvp.entry_count} colors; the texture requires {count}"
            )
        return pvp.colors[:count]
    if suffix == ".act":
        return act_to_palette(path.read_bytes(), count)
    if suffix == ".png":
        image = Image.open(path)
        if image.mode == "P":
            raw_palette = image.getpalette() or []
            transparency = image.info.get("transparency")
            colors = []
            for i in range(count):
                base = i * 3
                r = raw_palette[base] if base < len(raw_palette) else 0
                g = raw_palette[base + 1] if base + 1 < len(raw_palette) else 0
                b = raw_palette[base + 2] if base + 2 < len(raw_palette) else 0
                if isinstance(transparency, bytes):
                    a = transparency[i] if i < len(transparency) else 255
                elif isinstance(transparency, int):
                    a = 0 if i == transparency else 255
                else:
                    a = 255
                colors.append((r, g, b, a))
            return colors
        rgba = image.convert("RGBA")
        pixels = image_data(rgba)
        if len(pixels) >= count and (rgba.width == 1 or rgba.height == 1):
            return pixels[:count]
        # Accept the default swatch grid emitted by pvp-decode.
        return palette_from_swatch_image(rgba, count)
    return decode_palette_bytes(path.read_bytes(), count, palette_format)


def palette_image(indices: Sequence[int], width: int, height: int, colors: Sequence[Sequence[int]]) -> Image.Image:
    image = Image.new("P", (width, height))
    image.putdata(list(indices))
    rgb_palette: list[int] = []
    alpha = bytearray()
    for i in range(256):
        if i < len(colors):
            r, g, b, a = (int(v) for v in colors[i])
        else:
            r = g = b = 0
            a = 255
        rgb_palette.extend((r, g, b))
        alpha.append(a)
    image.putpalette(rgb_palette)
    if any(a != 255 for a in alpha):
        image.info["transparency"] = bytes(alpha)
    return image


def palette_from_png(image: Image.Image, count: int) -> tuple[list[int], list[tuple[int, int, int, int]]]:
    if image.mode != "P":
        raise PvrError(
            "indexed PVR encoding needs a P-mode PNG or a palette supplied with --palette"
        )
    indices = image_data(image)
    if any(index >= count for index in indices):
        maximum = max(indices)
        raise PvrError(f"PNG uses palette index {maximum}, but the target supports only {count} colors")
    raw_palette = image.getpalette() or []
    transparency = image.info.get("transparency")
    colors: list[tuple[int, int, int, int]] = []
    for i in range(count):
        base = i * 3
        r = raw_palette[base] if base < len(raw_palette) else 0
        g = raw_palette[base + 1] if base + 1 < len(raw_palette) else 0
        b = raw_palette[base + 2] if base + 2 < len(raw_palette) else 0
        if isinstance(transparency, bytes):
            a = transparency[i] if i < len(transparency) else 255
        elif isinstance(transparency, int):
            a = 0 if i == transparency else 255
        else:
            a = 255
        colors.append((r, g, b, a))
    return indices, colors


def nearest_palette_indices(image: Image.Image, colors: Sequence[Sequence[int]]) -> list[int]:
    try:
        import numpy as np
    except ImportError as exc:
        raise PvrError("NumPy is required to map RGBA pixels to an external palette") from exc

    pixels = np.asarray(image.convert("RGBA"), dtype=np.int16).reshape(-1, 4)
    palette = np.asarray(colors, dtype=np.int16)
    output = np.empty(len(pixels), dtype=np.uint16)
    for start in range(0, len(pixels), 8192):
        block = pixels[start : start + 8192].astype(np.int32)
        diff = block[:, None, :] - palette[None, :, :].astype(np.int32)
        distance = np.sum(diff * diff, axis=2)
        output[start : start + len(block)] = np.argmin(distance, axis=1)
    return output.astype(int).tolist()


# ---------------------------------------------------------------------------
# VQ
# ---------------------------------------------------------------------------

# Dreamcast VQ codebook entries store each 2x2 vector in raster order:
# TL, TR, BL, BR.  v1.2.0 incorrectly treated the middle two words as
# column-major and swapped TR/BL.  The index-map twiddle/Morton order was
# already correct; only this intra-vector order changes in v1.2.1.
VQ_MEMORY_TO_SCREEN = (0, 1, 2, 3)
VQ_SCREEN_TO_MEMORY = (0, 1, 2, 3)


def vq_codebook_entries(chunk: PvrChunk) -> int:
    block_count = max(1, chunk.width // 2) * max(1, chunk.height // 2)
    if chunk.data_format in (0x03, 0x04):
        return 256
    if chunk.data_format in (0x10, 0x11):
        # The base-level index map is at the end of mipmapped payloads too.
        if chunk.data_format == 0x10:
            codebook_bytes = len(chunk.payload) - block_count
            if codebook_bytes > 0 and codebook_bytes % 8 == 0:
                return codebook_bytes // 8
        return min(256, max(1, (chunk.width * chunk.height) // 32))
    raise PvrError("not a VQ texture")


def decode_vq(
    chunk: PvrChunk, detwiddle_mode: str = "morton"
) -> tuple[Image.Image, dict[str, Any]]:
    entries = vq_codebook_entries(chunk)
    codebook_bytes = entries * 8
    block_width = max(1, chunk.width // 2)
    block_height = max(1, chunk.height // 2)
    index_count = block_width * block_height
    if len(chunk.payload) < codebook_bytes + index_count:
        raise PvrError(
            f"VQ payload is too short for {entries} codebook entries and {index_count} indices"
        )

    codebook_raw = chunk.payload[:codebook_bytes]
    indices_raw = chunk.payload[-index_count:]
    codebook_values = struct.unpack_from(f"<{entries * 4}H", codebook_raw, 0)

    codebook_screen: list[list[tuple[int, int, int, int]]] = []
    for entry in range(entries):
        raw = list(codebook_values[entry * 4 : entry * 4 + 4])
        if chunk.pixel_format == 0x03:
            p0, p1 = yuv422_pair_to_rgba(raw[0], raw[3])
            p2, p3 = yuv422_pair_to_rgba(raw[1], raw[2])
            # pvr2image's verified YUV-VQ ordering converted to our screen
            # order TL, TR, BL, BR.
            codebook_screen.append([p0, p3, p2, p1])
        elif chunk.pixel_format in (0x00, 0x01, 0x02, 0x05):
            screen_values = [raw[i] for i in VQ_MEMORY_TO_SCREEN]
            codebook_screen.append([unpack_16(v, chunk.pixel_format) for v in screen_values])
        else:
            raise PvrError(
                f"VQ decoding is unsupported for pixel format {chunk.pixel_format_name}"
            )

    linear_indices = untwiddle_values_mode(
        list(indices_raw), block_width, block_height, detwiddle_mode
    )
    image = Image.new("RGBA", (chunk.width, chunk.height))
    pixels = image.load()
    for by in range(block_height):
        for bx in range(block_width):
            code = linear_indices[by * block_width + bx]
            if code >= entries:
                raise PvrError(f"VQ index {code} exceeds codebook size {entries}")
            block = codebook_screen[code]
            x = bx * 2
            y = by * 2
            pixels[x, y] = block[0]
            if x + 1 < chunk.width:
                pixels[x + 1, y] = block[1]
            if y + 1 < chunk.height:
                pixels[x, y + 1] = block[2]
            if x + 1 < chunk.width and y + 1 < chunk.height:
                pixels[x + 1, y + 1] = block[3]

    aux = {
        "vq_codebook_entries": entries,
        "vq_codebook_b64": b64e(codebook_raw),
        "vq_base_indices_b64": b64e(indices_raw),
        "detwiddle_mode": detwiddle_mode,
    }
    return image, aux


def _image_blocks_rgba(image: Image.Image) -> Any:
    try:
        import numpy as np
    except ImportError as exc:
        raise PvrError("NumPy is required for VQ encoding") from exc

    rgba = np.asarray(image.convert("RGBA"), dtype=np.uint8)
    height, width, _ = rgba.shape
    if width % 2 or height % 2:
        raise PvrError(f"VQ requires even dimensions; got {width}x{height}")
    # Screen order TL, TR, BL, BR, each with RGBA.
    return np.concatenate(
        (
            rgba[0::2, 0::2],
            rgba[0::2, 1::2],
            rgba[1::2, 0::2],
            rgba[1::2, 1::2],
        ),
        axis=2,
    ).reshape(-1, 16)


def _codebook_rgba_vectors(codebook_raw: bytes, entries: int, pixel_format: int) -> Any:
    try:
        import numpy as np
    except ImportError as exc:
        raise PvrError("NumPy is required for VQ encoding") from exc
    values = struct.unpack_from(f"<{entries * 4}H", codebook_raw, 0)
    vectors = []
    for entry in range(entries):
        raw = values[entry * 4 : entry * 4 + 4]
        screen = [raw[i] for i in VQ_MEMORY_TO_SCREEN]
        vector: list[int] = []
        for value in screen:
            vector.extend(unpack_16(value, pixel_format))
        vectors.append(vector)
    return np.asarray(vectors, dtype=np.float32)


def _nearest_codebook_indices(blocks: Any, centroids: Any) -> Any:
    import numpy as np

    result = np.empty(len(blocks), dtype=np.uint16)
    centroid_norm = np.sum(centroids * centroids, axis=1)
    for start in range(0, len(blocks), 8192):
        batch = blocks[start : start + 8192].astype(np.float32)
        distances = (
            np.sum(batch * batch, axis=1)[:, None]
            + centroid_norm[None, :]
            - 2.0 * (batch @ centroids.T)
        )
        result[start : start + len(batch)] = np.argmin(distances, axis=1)
    return result


def _twiddle_vq_indices(linear_indices: Sequence[int], block_width: int, block_height: int) -> bytes:
    stored = bytearray(block_width * block_height)
    for by in range(block_height):
        for bx in range(block_width):
            stored[twiddled_index(bx, by, block_width, block_height)] = int(
                linear_indices[by * block_width + bx]
            )
    return bytes(stored)


def encode_vq_preserve(
    image: Image.Image,
    pixel_format: int,
    codebook_raw: bytes,
    original_indices_raw: bytes,
    entries: int,
) -> bytes:
    import numpy as np

    blocks = _image_blocks_rgba(image)
    centroids = _codebook_rgba_vectors(codebook_raw, entries, pixel_format)
    block_width = image.width // 2
    block_height = image.height // 2

    # Recover the original linear index map. Keeping exact matching original
    # indices makes an unedited decode/encode byte-identical even when duplicate
    # codebook entries exist.
    original_linear = np.empty(block_width * block_height, dtype=np.uint16)
    for by in range(block_height):
        for bx in range(block_width):
            original_linear[by * block_width + bx] = original_indices_raw[
                twiddled_index(bx, by, block_width, block_height)
            ]

    nearest = _nearest_codebook_indices(blocks, centroids)
    for i, original_code in enumerate(original_linear):
        if original_code < entries and np.array_equal(blocks[i], centroids[original_code].astype(np.uint8)):
            nearest[i] = original_code

    return codebook_raw + _twiddle_vq_indices(nearest, block_width, block_height)


def _kmeans_codebook(blocks: Any, entries: int, iterations: int, seed: int) -> Any:
    import numpy as np

    if entries <= 0 or entries > 256:
        raise PvrError("VQ codebook entries must be between 1 and 256")
    if len(blocks) == 0:
        raise PvrError("cannot VQ-encode an empty image")

    rng = np.random.default_rng(seed)
    if len(blocks) > 65536:
        sample_indices = np.linspace(0, len(blocks) - 1, 65536, dtype=np.int64)
        training = blocks[sample_indices].astype(np.float32)
    else:
        training = blocks.astype(np.float32)

    if len(training) >= entries:
        initial = rng.choice(len(training), size=entries, replace=False)
    else:
        initial = rng.choice(len(training), size=entries, replace=True)
    centroids = training[initial].copy()

    for _ in range(max(1, iterations)):
        assignments = _nearest_codebook_indices(training, centroids)
        sums = np.zeros_like(centroids, dtype=np.float64)
        counts = np.bincount(assignments, minlength=entries).astype(np.int64)
        np.add.at(sums, assignments, training)
        occupied = counts > 0
        centroids[occupied] = (sums[occupied] / counts[occupied, None]).astype(np.float32)
        if not np.all(occupied):
            replacements = rng.choice(len(training), size=int(np.sum(~occupied)), replace=True)
            centroids[~occupied] = training[replacements]

    return centroids


def _pack_centroid_codebook(centroids: Any, pixel_format: int) -> tuple[bytes, Any]:
    import numpy as np

    entries = len(centroids)
    packed_entries: list[int] = []
    decoded_vectors = np.empty((entries, 16), dtype=np.float32)

    for entry, centroid in enumerate(centroids):
        screen_packed = []
        screen_decoded: list[int] = []
        for pixel in range(4):
            rgba = centroid[pixel * 4 : pixel * 4 + 4]
            value = pack_16(rgba, pixel_format)
            screen_packed.append(value)
            screen_decoded.extend(unpack_16(value, pixel_format))
        memory_packed = [screen_packed[i] for i in VQ_SCREEN_TO_MEMORY]
        packed_entries.extend(memory_packed)
        decoded_vectors[entry] = screen_decoded

    return struct.pack(f"<{len(packed_entries)}H", *packed_entries), decoded_vectors


def encode_vq_rebuild(
    image: Image.Image,
    pixel_format: int,
    entries: int,
    iterations: int,
    seed: int,
) -> bytes:
    blocks = _image_blocks_rgba(image)
    centroids = _kmeans_codebook(blocks, entries, iterations, seed)
    codebook_raw, decoded_vectors = _pack_centroid_codebook(centroids, pixel_format)
    indices = _nearest_codebook_indices(blocks, decoded_vectors)
    block_width = image.width // 2
    block_height = image.height // 2
    return codebook_raw + _twiddle_vq_indices(indices, block_width, block_height)


# ---------------------------------------------------------------------------
# Texture decoding / encoding
# ---------------------------------------------------------------------------


def _mip_level_byte_size(chunk: PvrChunk, width: int, height: int) -> int:
    pixels = width * height
    if chunk.is_vq:
        return max(1, width // 2) * max(1, height // 2)
    if chunk.is_indexed:
        is_4bit = chunk.data_format in (0x05, 0x06)
        return (pixels + 1) // 2 if is_4bit else pixels
    if chunk.data_format in ABGR_FORMATS or chunk.pixel_format == 0x07:
        return pixels * 4
    if chunk.pixel_format == 0x06 and not chunk.is_indexed:  # extended YUV420
        return pixels * 3 // 2
    return pixels * 2


def available_mip_levels(chunk: PvrChunk) -> list[dict[str, int]]:
    """Return safely sliceable mip levels, numbered 0=base, 1=half-size."""
    if not chunk.is_mipmapped:
        return [{"level": 0, "width": chunk.width, "height": chunk.height, "start": 0, "end": len(chunk.payload)}]

    codebook_bytes = vq_codebook_entries(chunk) * 8 if chunk.is_vq else 0
    lower_bound = codebook_bytes
    end = len(chunk.payload)
    result: list[dict[str, int]] = []
    width, height, level = chunk.width, chunk.height, 0
    while width >= 1 and height >= 1:
        size = _mip_level_byte_size(chunk, width, height)
        start = end - size
        if start < lower_bound:
            break
        result.append({"level": level, "width": width, "height": height, "start": start, "end": end})
        end = start
        if width == 1 and height == 1:
            break
        width = max(1, width // 2)
        height = max(1, height // 2)
        level += 1
    if not result:
        raise PvrError("mipmapped payload does not contain a complete base level")
    return result


def chunk_for_mip_level(chunk: PvrChunk, level: int) -> PvrChunk:
    levels = available_mip_levels(chunk)
    match = next((item for item in levels if item["level"] == level), None)
    if match is None:
        maximum = max(item["level"] for item in levels)
        raise PvrError(f"mip level {level} is unavailable; valid range is 0..{maximum}")
    segment = chunk.payload[match["start"] : match["end"]]
    if chunk.is_vq:
        entries = vq_codebook_entries(chunk)
        segment = chunk.payload[: entries * 8] + segment
    # Convert the temporary chunk to its corresponding non-mip data format.
    non_mip = {
        0x02: 0x01,
        0x04: 0x03,
        0x06: 0x05,
        0x08: 0x07,
        0x0A: 0x09,
        0x0C: 0x0B,
        0x0F: 0x0E,
        0x11: 0x10,
        0x12: 0x01,
    }.get(chunk.data_format, chunk.data_format)
    return PvrChunk(
        chunk_index=chunk.chunk_index,
        start=chunk.start,
        pvrt_offset=chunk.pvrt_offset,
        end=chunk.end,
        gbix_present=chunk.gbix_present,
        gbix_length=chunk.gbix_length,
        global_index=chunk.global_index,
        gbix_tail=chunk.gbix_tail,
        pvrt_length_field=chunk.pvrt_length_field,
        pixel_format=chunk.pixel_format,
        data_format=non_mip,
        reserved=chunk.reserved,
        width=match["width"],
        height=match["height"],
        payload=segment,
    )


def base_payload_for_mipmapped(chunk: PvrChunk) -> bytes:
    return chunk_for_mip_level(chunk, 0).payload if chunk.is_mipmapped else chunk.payload


def decode_indexed(
    chunk: PvrChunk,
    palette: Sequence[Sequence[int]],
    detwiddle_mode: str = "morton",
) -> tuple[Image.Image, dict[str, Any]]:
    width, height = chunk.width, chunk.height
    payload = chunk.payload
    is_4bit = chunk.data_format in (0x05, 0x06)
    count = 16 if is_4bit else 256
    if len(palette) < count:
        raise PvrError(f"indexed texture requires {count} palette colors")

    stored_indices: list[int] = []
    if is_4bit:
        needed = (width * height + 1) // 2
        if len(payload) < needed:
            raise PvrError(f"4-bit indexed payload has {len(payload)} bytes; {needed} required")
        for byte in payload[:needed]:
            stored_indices.append(byte & 0x0F)
            stored_indices.append((byte >> 4) & 0x0F)
        stored_indices = stored_indices[: width * height]
    else:
        needed = width * height
        if len(payload) < needed:
            raise PvrError(f"8-bit indexed payload has {len(payload)} bytes; {needed} required")
        stored_indices = list(payload[:needed])

    indices = untwiddle_values_mode(stored_indices, width, height, detwiddle_mode)
    image = palette_image(indices, width, height, palette[:count])
    return image, {
        "palette_colors": [list(c) for c in palette[:count]],
        "detwiddle_mode": detwiddle_mode,
    }


def decode_chunk_image(
    chunk: PvrChunk,
    palette: Optional[Sequence[Sequence[int]]] = None,
    *,
    detwiddle_mode: str = "morton",
    mip_level: int = 0,
) -> tuple[Image.Image, dict[str, Any]]:
    if chunk.pixel_format not in SUPPORTED_PIXEL_FORMATS:
        raise PvrError(
            f"pixel format 0x{chunk.pixel_format:02X} ({chunk.pixel_format_name}) is not supported"
        )
    if chunk.data_format not in SUPPORTED_DATA_FORMATS:
        raise PvrError(
            f"data format 0x{chunk.data_format:02X} ({chunk.data_format_name}) is not supported"
        )

    selected = chunk_for_mip_level(chunk, mip_level) if chunk.is_mipmapped else chunk
    aux: dict[str, Any] = {
        "mip_level": mip_level,
        "mip_level_count": len(available_mip_levels(chunk)),
        "detwiddle_mode": detwiddle_mode,
    }

    if selected.is_vq:
        image, vq_aux = decode_vq(selected, detwiddle_mode)
        aux.update(vq_aux)
        return image, aux

    if selected.is_indexed:
        if palette is None:
            raise PvrError(
                "this PVR uses an external CLUT; supply a raw CLUT, PVP, ACT, or palette PNG"
            )
        image, pal_aux = decode_indexed(selected, palette, detwiddle_mode)
        aux.update(pal_aux)
        return image, aux

    payload = selected.payload
    count = selected.width * selected.height

    if selected.data_format in ABGR_FORMATS:
        needed = count * 4
        if len(payload) < needed:
            raise PvrError(f"ABGR payload has {len(payload)} bytes; {needed} required")
        values = struct.unpack_from(f"<{count}I", payload, 0)
        image = Image.new("RGBA", (selected.width, selected.height))
        image.putdata([unpack_abgr8888(v) for v in values])
        return image, aux

    if selected.pixel_format == 0x06:  # extended YUV420, non-indexed
        return decode_yuv420_payload(payload, selected.width, selected.height), aux

    bytes_per_pixel = 4 if selected.pixel_format == 0x07 else 2
    needed = count * bytes_per_pixel
    if len(payload) < needed:
        raise PvrError(f"texture payload has {len(payload)} bytes; {needed} are required")
    if bytes_per_pixel == 4:
        stored: list[int] = list(struct.unpack_from(f"<{count}I", payload, 0))
    else:
        stored = list(struct.unpack_from(f"<{count}H", payload, 0))

    if selected.data_format in TWIDDLED_FORMATS:
        values = untwiddle_values_mode(stored, selected.width, selected.height, detwiddle_mode)
    elif selected.data_format in LINEAR_FORMATS:
        values = stored
    else:
        raise PvrError(f"unhandled data format: {selected.data_format_name}")

    if selected.pixel_format == 0x03:
        return decode_yuv422_words(values, selected.width, selected.height), aux
    if selected.pixel_format == 0x04:
        return decode_bump_words(values, selected.width, selected.height), aux
    return packed_to_rgba_image(
        values, selected.width, selected.height, selected.pixel_format
    ), aux


def encode_uncompressed(
    image: Image.Image,
    pixel_format: int,
    twiddle: bool,
    source_data_format: Optional[int] = None,
) -> tuple[bytes, int]:
    if source_data_format in ABGR_FORMATS:
        values = [pack_abgr8888(pixel) for pixel in image_data(image.convert("RGBA"))]
        return struct.pack(f"<{len(values)}I", *values), 0x0E
    if pixel_format == 0x06:
        raise PvrError(
            "YUV420 encoding is not enabled; decode is supported, but the macroblock encoder "
            "needs validation against known-good hardware files"
        )
    if pixel_format == 0x03:
        values = encode_yuv422_words(image)
        word_size = 2
    elif pixel_format == 0x04:
        values = encode_bump_words(image)
        word_size = 2
    elif pixel_format == 0x07:
        values = [pack_argb8888(pixel) for pixel in image_data(image.convert("RGBA"))]
        word_size = 4
    else:
        values = rgba_bytes_to_packed(image, pixel_format)
        word_size = 2

    if twiddle:
        values = twiddle_values(values, image.width, image.height)
        data_format = 0x01 if image.width == image.height else 0x0D
    else:
        data_format = 0x0B if source_data_format == 0x0B else 0x09
    code = "I" if word_size == 4 else "H"
    return struct.pack(f"<{len(values)}{code}", *values), data_format


def encode_indexed(
    image: Image.Image,
    pixel_format: int,
    palette: Optional[Sequence[Sequence[int]]],
) -> tuple[bytes, int, list[tuple[int, int, int, int]]]:
    count = 16 if pixel_format == 0x05 else 256
    if image.mode == "P":
        indices, png_colors = palette_from_png(image, count)
        colors = list(tuple(c) for c in (palette if palette is not None else png_colors))
    else:
        if palette is None:
            raise PvrError("RGBA indexed encoding requires --palette or sidecar palette colors")
        colors = [tuple(c) for c in palette[:count]]
        indices = nearest_palette_indices(image, colors)

    stored = twiddle_values(indices, image.width, image.height)
    if pixel_format == 0x05:
        packed = bytearray()
        for i in range(0, len(stored), 2):
            low = stored[i] & 0x0F
            high = (stored[i + 1] & 0x0F) if i + 1 < len(stored) else 0
            packed.append(low | (high << 4))
        return bytes(packed), 0x05, colors
    return bytes(stored), 0x07, colors


# ---------------------------------------------------------------------------
# Orientation
# ---------------------------------------------------------------------------


def apply_edit_transform(image: Image.Image, rotate_cw: int, flip: str) -> Image.Image:
    # Pillow positive angles are counterclockwise, so clockwise is negative.
    result = image.rotate(-rotate_cw, expand=True) if rotate_cw else image.copy()
    if flip in ("horizontal", "both"):
        result = ImageOps.mirror(result)
    if flip in ("vertical", "both"):
        result = ImageOps.flip(result)
    return result


def undo_edit_transform(image: Image.Image, rotate_cw: int, flip: str) -> Image.Image:
    # Inverse order is essential: undo flip first, then undo rotation.
    result = image.copy()
    if flip in ("vertical", "both"):
        result = ImageOps.flip(result)
    if flip in ("horizontal", "both"):
        result = ImageOps.mirror(result)
    if rotate_cw:
        result = result.rotate(rotate_cw, expand=True)
    return result


# ---------------------------------------------------------------------------
# Sidecar metadata
# ---------------------------------------------------------------------------


def default_sidecar_path(png_path: Path) -> Path:
    return Path(str(png_path) + ".pvr.json")


def load_sidecar(path: Optional[Path], png_path: Path) -> tuple[Optional[dict[str, Any]], Optional[Path]]:
    if path is not None:
        if not path.exists():
            raise PvrError(f"metadata sidecar does not exist: {path}")
        return json.loads(path.read_text(encoding="utf-8")), path
    automatic = default_sidecar_path(png_path)
    if automatic.exists():
        return json.loads(automatic.read_text(encoding="utf-8")), automatic
    return None, None


def make_sidecar(
    *,
    input_path: Path,
    source_bytes: bytes,
    raw_container: bytes,
    wrapper: WrapperInfo,
    chunk: PvrChunk,
    image_before_transform: Image.Image,
    image_after_transform: Image.Image,
    rotate_cw: int,
    flip: str,
    aux: dict[str, Any],
    palette_format: Optional[str],
) -> dict[str, Any]:
    info: dict[str, Any] = {
        "tool": TOOL_NAME,
        "version": TOOL_VERSION,
        "source": {
            "file": str(input_path),
            "sha256": sha256_bytes(source_bytes),
            "unwrapped_sha256": sha256_bytes(raw_container),
            "wrapper": wrapper.kind,
            "compressed_size": wrapper.compressed_size,
            "decompressed_size": wrapper.decompressed_size,
            "pvr_chunk_count": len(scan_pvr_chunks(raw_container)),
        },
        "chunk": {
            "index": chunk.chunk_index,
            "start": chunk.start,
            "pvrt_offset": chunk.pvrt_offset,
            "end": chunk.end,
            "gbix_present": chunk.gbix_present,
            "gbix_length": chunk.gbix_length,
            "global_index": chunk.global_index,
            "gbix_tail": chunk.gbix_tail,
            "pvrt_length_field": chunk.pvrt_length_field,
            "pixel_format": chunk.pixel_format,
            "pixel_format_name": chunk.pixel_format_name,
            "data_format": chunk.data_format,
            "data_format_name": chunk.data_format_name,
            "reserved": chunk.reserved,
            "width": chunk.width,
            "height": chunk.height,
            "mipmapped": chunk.is_mipmapped,
            "payload_size": len(chunk.payload),
        },
        "editing_transform": {
            "rotate_cw": rotate_cw,
            "flip": flip,
            "decode_order": ["rotate_clockwise", "flip"],
            "encode_inverse_order": ["undo_flip", "undo_rotation"],
        },
        "png": {
            "mode": image_after_transform.mode,
            "width": image_after_transform.width,
            "height": image_after_transform.height,
            "raw_rgba_sha256": sha256_bytes(image_before_transform.convert("RGBA").tobytes()),
            "edited_orientation_rgba_sha256": sha256_bytes(image_after_transform.convert("RGBA").tobytes()),
        },
    }
    info.update(aux)
    if palette_format:
        info["palette_format"] = palette_format
    return info


# ---------------------------------------------------------------------------
# CLI command implementations
# ---------------------------------------------------------------------------


def command_inspect(args: argparse.Namespace) -> int:
    path = Path(args.input)
    source = path.read_bytes()
    raw, wrapper = unwrap_data(source, args.wrapper)
    chunks = scan_pvr_chunks(raw)
    if not chunks:
        raise PvrError("no PVR chunks found")

    result = {
        "file": str(path),
        "sha256": sha256_bytes(source),
        "wrapper": asdict(wrapper),
        "chunks": [
            {
                "index": c.chunk_index,
                "start": c.start,
                "end": c.end,
                "gbix_present": c.gbix_present,
                "global_index": c.global_index,
                "pixel_format": c.pixel_format,
                "pixel_format_name": c.pixel_format_name,
                "data_format": c.data_format,
                "data_format_name": c.data_format_name,
                "width": c.width,
                "height": c.height,
                "mipmapped": c.is_mipmapped,
                "payload_size": len(c.payload),
                "vq_codebook_entries": vq_codebook_entries(c) if c.is_vq else None,
            }
            for c in chunks
        ],
    }

    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print(f"File: {path}")
        print(f"SHA-256: {result['sha256']}")
        print(
            f"Wrapper: {wrapper.kind} ({wrapper.compressed_size:,} -> {wrapper.decompressed_size:,} bytes)"
        )
        print(f"PVR chunks: {len(chunks)}")
        for item in result["chunks"]:
            print(
                f"  [{item['index']}] {item['width']}x{item['height']} "
                f"{item['pixel_format_name']} / {item['data_format_name']} "
                f"GBIX={item['global_index'] if item['gbix_present'] else 'none'} "
                f"payload={item['payload_size']:,}"
            )
    return 0


def resolve_decode_output(
    input_path: Path,
    output: Optional[str],
    chunk: PvrChunk,
    total: int,
    *,
    mip_level: int = 0,
    multiple_mips: bool = False,
) -> Path:
    chunk_suffix = f"_{chunk.chunk_index:02d}" if total > 1 else ""
    mip_suffix = f"_mip{mip_level:02d}" if multiple_mips or mip_level else ""
    name = input_path.stem + chunk_suffix + mip_suffix + ".png"
    if output:
        out = Path(output)
        if out.exists() and out.is_dir():
            return out / name
        if multiple_mips:
            # An output with an image suffix is treated as a filename pattern;
            # a suffixless output is treated as a directory for the mip set.
            if out.suffix.lower() in {".png", ".bmp", ".tga", ".jpg", ".jpeg"}:
                return out.with_name(out.stem + mip_suffix + out.suffix)
            return out / name
        return out
    return input_path.with_name(name)


def command_decode(args: argparse.Namespace) -> int:
    input_path = Path(args.input)
    source = input_path.read_bytes()
    raw, wrapper = unwrap_data(source, args.wrapper)
    chunks = scan_pvr_chunks(raw)
    chunk = select_chunk(chunks, args.index)

    palette = None
    palette_source: Optional[Path] = None
    palette_count = 16 if chunk.data_format in (0x05, 0x06) else 256
    palette_format = args.palette_format
    if chunk.is_indexed:
        if args.palette:
            palette_source = Path(args.palette)
        else:
            palette_source = find_companion_pvp(input_path)
        if palette_source is None:
            raise PvrError(
                "indexed PVR detected; supply --palette FILE or place a companion PVP beside the PVR"
            )
        if palette_source.suffix.lower() == ".pvp":
            pvp = parse_pvp(palette_source.read_bytes())
            palette_format = pvp.format_name
            palette = pvp.colors[:palette_count]
        else:
            palette = load_palette(palette_source, palette_count, palette_format)

    levels = available_mip_levels(chunk)
    if args.all_mipmaps:
        mip_levels = [item["level"] for item in levels]
    else:
        mip_levels = [args.mip_level]
    multiple_mips = len(mip_levels) > 1

    for mip_level in mip_levels:
        image, aux = decode_chunk_image(
            chunk,
            palette,
            detwiddle_mode=args.detwiddle,
            mip_level=mip_level,
        )
        if palette is not None:
            aux.setdefault("palette_colors", [list(c) for c in palette])
            if palette_source is not None:
                aux["palette_source"] = str(palette_source)

        transformed = apply_edit_transform(image, args.rotate_cw, args.flip)
        output_path = resolve_decode_output(
            input_path,
            args.output,
            chunk,
            len(chunks),
            mip_level=mip_level,
            multiple_mips=multiple_mips,
        )
        ensure_parent(output_path)
        transformed.save(output_path, format="PNG", optimize=False)

        selected_chunk = chunk_for_mip_level(chunk, mip_level) if chunk.is_mipmapped else chunk
        sidecar = make_sidecar(
            input_path=input_path,
            source_bytes=source,
            raw_container=raw,
            wrapper=wrapper,
            chunk=selected_chunk,
            image_before_transform=image,
            image_after_transform=transformed,
            rotate_cw=args.rotate_cw,
            flip=args.flip,
            aux=aux,
            palette_format=palette_format if palette is not None else None,
        )
        sidecar["source_chunk"] = {
            "index": chunk.chunk_index,
            "data_format": chunk.data_format,
            "data_format_name": chunk.data_format_name,
            "width": chunk.width,
            "height": chunk.height,
            "mipmapped": chunk.is_mipmapped,
        }
        if not args.no_sidecar:
            if args.sidecar and not multiple_mips:
                sidecar_path = Path(args.sidecar)
            else:
                sidecar_path = default_sidecar_path(output_path)
            ensure_parent(sidecar_path)
            sidecar_path.write_text(json.dumps(sidecar, indent=2) + "\n", encoding="utf-8")
            print(f"Metadata: {sidecar_path}")

        print(f"PNG: {output_path}")
        print(
            f"Decoded chunk {chunk.chunk_index}, mip {mip_level}: "
            f"{image.width}x{image.height} {chunk.pixel_format_name}/{chunk.data_format_name}; "
            f"detwiddle={args.detwiddle}; rotate CW {args.rotate_cw}, flip {args.flip}"
        )
    return 0


def resolve_auto(value: Any, fallback: Any) -> Any:
    return fallback if value in (None, "auto") else value


def determine_encode_settings(
    args: argparse.Namespace,
    metadata: Optional[dict[str, Any]],
    image: Image.Image,
) -> dict[str, Any]:
    chunk_meta = metadata.get("chunk", {}) if metadata else {}
    source_chunk_meta = metadata.get("source_chunk", {}) if metadata else {}
    transform_meta = metadata.get("editing_transform", {}) if metadata else {}
    source_meta = metadata.get("source", {}) if metadata else {}

    rotate_cw = int(resolve_auto(args.rotate_cw, transform_meta.get("rotate_cw", 0)))
    flip = str(resolve_auto(args.flip, transform_meta.get("flip", "none")))

    source_data_format = source_chunk_meta.get("data_format", chunk_meta.get("data_format"))
    if args.pixel_format == "auto":
        pixel_format = chunk_meta.get("pixel_format")
        if pixel_format is None:
            pixel_format = infer_pixel_format(undo_edit_transform(image, rotate_cw, flip))
        indexed_output = source_data_format in INDEXED_FORMATS
        requested_pixel_name = chunk_meta.get("pixel_format_name", PIXEL_FORMATS.get(pixel_format, "auto"))
    else:
        pixel_format = ENCODE_PIXEL_FORMAT_CODES[args.pixel_format]
        indexed_output = args.pixel_format in ("pal4", "pal8")
        requested_pixel_name = args.pixel_format

    source_vq = source_data_format in VQ_FORMATS
    source_twiddled = source_data_format in TWIDDLED_FORMATS or source_vq

    vq_setting = args.vq
    if vq_setting == "auto":
        vq_setting = "preserve" if source_vq and metadata else ("on" if source_vq else "off")

    twiddle_setting = args.twiddle
    if twiddle_setting == "auto":
        twiddle = source_twiddled if source_data_format is not None else True
    else:
        twiddle = twiddle_setting == "on"

    if vq_setting in ("on", "preserve", "rebuild") and not twiddle:
        raise PvrError("VQ index maps are twiddled; use --twiddle on or disable VQ with --vq off")
    if indexed_output and vq_setting in ("on", "preserve", "rebuild"):
        raise PvrError("indexed and VQ output modes are mutually exclusive")

    wrapper = args.wrapper
    if wrapper == "auto":
        wrapper = source_meta.get("wrapper", "none")

    gbix_arg = args.gbix
    if gbix_arg == "auto":
        gbix_present = bool(chunk_meta.get("gbix_present", True))
        global_index = int(chunk_meta.get("global_index") or 0)
    elif gbix_arg == "none":
        gbix_present = False
        global_index = 0
    else:
        gbix_present = True
        global_index = parse_int(gbix_arg)

    return {
        "rotate_cw": rotate_cw,
        "flip": flip,
        "pixel_format": int(pixel_format),
        "pixel_format_name": requested_pixel_name,
        "indexed_output": indexed_output,
        "vq_setting": vq_setting,
        "twiddle": twiddle,
        "wrapper": wrapper,
        "gbix_present": gbix_present,
        "global_index": global_index,
        "gbix_tail": int(chunk_meta.get("gbix_tail") or 0),
        "gbix_length": int(chunk_meta.get("gbix_length") or 16),
        "reserved": int(chunk_meta.get("reserved") or 0),
        "source_data_format": source_data_format,
    }


def load_template(
    args: argparse.Namespace,
    metadata: Optional[dict[str, Any]],
    sidecar_path: Optional[Path],
) -> tuple[Optional[Path], Optional[bytes], Optional[bytes], Optional[WrapperInfo], Optional[PvrChunk]]:
    template_path: Optional[Path] = Path(args.template) if args.template else None
    if template_path is None and metadata:
        source_name = metadata.get("source", {}).get("file")
        if source_name:
            candidate = Path(source_name)
            if candidate.exists():
                template_path = candidate
            elif sidecar_path:
                relative = sidecar_path.parent / candidate.name
                if relative.exists():
                    template_path = relative

    if template_path is None:
        return None, None, None, None, None

    source = template_path.read_bytes()
    requested_wrapper = args.template_wrapper if args.template_wrapper != "auto" else "auto"
    raw, wrapper = unwrap_data(source, requested_wrapper)
    chunks = scan_pvr_chunks(raw)
    index = args.index
    if index is None and metadata:
        index = metadata.get("chunk", {}).get("index")
    chunk = select_chunk(chunks, index)
    return template_path, source, raw, wrapper, chunk


def command_encode(args: argparse.Namespace) -> int:
    png_path = Path(args.input)
    image = Image.open(png_path)
    metadata_path = Path(args.metadata) if args.metadata else None
    metadata, sidecar_path = load_sidecar(metadata_path, png_path)

    template_path, template_source, template_raw, template_wrapper, template_chunk = load_template(
        args, metadata, sidecar_path
    )

    settings = determine_encode_settings(args, metadata, image)
    raw_image = undo_edit_transform(image, settings["rotate_cw"], settings["flip"])

    if template_chunk is not None:
        expected = (template_chunk.width, template_chunk.height)
    elif metadata:
        cm = metadata.get("chunk", {})
        expected = (int(cm.get("width", raw_image.width)), int(cm.get("height", raw_image.height)))
    else:
        expected = raw_image.size
    if raw_image.size != expected:
        raise PvrError(
            f"after undoing orientation the PNG is {raw_image.width}x{raw_image.height}; "
            f"the target PVR is {expected[0]}x{expected[1]}"
        )

    source_was_mipmapped = bool(
        metadata
        and (
            metadata.get("source_chunk", {}).get("mipmapped")
            or metadata.get("chunk", {}).get("mipmapped")
        )
    )
    if source_was_mipmapped and args.mipmaps != "off":
        raise PvrError(
            "the source PVR is mipmapped. v1.2.1 can export each level, but does not yet "
            "rebuild a complete edited mip chain. Use --mipmaps off to intentionally emit "
            "a non-mipmapped PVR."
        )
    if args.mipmaps == "on":
        raise PvrError("complete mipmap encoding is not enabled in v1.2.1")

    pixel_format = settings["pixel_format"]
    if pixel_format not in SUPPORTED_PIXEL_FORMATS:
        raise PvrError(f"unsupported output pixel format 0x{pixel_format:02X}")

    palette_colors: Optional[list[tuple[int, int, int, int]]] = None
    if settings["indexed_output"]:
        count = 16 if settings["pixel_format_name"] == "pal4" else 256
        if args.palette:
            palette_colors = load_palette(Path(args.palette), count, args.palette_format)
        elif metadata and metadata.get("palette_colors"):
            palette_colors = [tuple(c) for c in metadata["palette_colors"]]
        payload, data_format, palette_colors = encode_indexed(raw_image, pixel_format, palette_colors)
    elif settings["vq_setting"] in ("preserve", "on", "rebuild"):
        if pixel_format not in (0x00, 0x01, 0x02, 0x05):
            raise PvrError(
                "VQ encoding is currently supported for ARGB1555, RGB565, ARGB4444, and RGB555"
            )
        if raw_image.width % 2 or raw_image.height % 2:
            raise PvrError("VQ requires even dimensions")
        vq_mode = settings["vq_setting"]
        source_entries = int(metadata.get("vq_codebook_entries", 0)) if metadata else 0
        codebook_raw = b64d(metadata.get("vq_codebook_b64")) if metadata else b""
        original_indices = b64d(metadata.get("vq_base_indices_b64")) if metadata else b""

        if args.vq_codebook_size == "auto":
            if source_entries:
                entries = source_entries
            else:
                entries = 256
        else:
            entries = int(args.vq_codebook_size)

        if vq_mode == "preserve":
            needed_indices = (raw_image.width // 2) * (raw_image.height // 2)
            if not codebook_raw or len(codebook_raw) != entries * 8:
                raise PvrError(
                    "--vq preserve requires the VQ codebook stored in the decode sidecar; "
                    "use --vq rebuild or --vq off"
                )
            if len(original_indices) != needed_indices:
                raise PvrError(
                    "--vq preserve requires the original base index map stored in the sidecar"
                )
            payload = encode_vq_preserve(
                raw_image, pixel_format, codebook_raw, original_indices, entries
            )
        else:
            payload = encode_vq_rebuild(
                raw_image,
                pixel_format,
                entries,
                args.vq_iterations,
                args.vq_seed,
            )
        data_format = 0x03 if entries == 256 else 0x10
    else:
        payload, data_format = encode_uncompressed(
            raw_image,
            pixel_format,
            settings["twiddle"],
            settings["source_data_format"],
        )

    gbix_present = settings["gbix_present"]
    global_index = settings["global_index"]
    gbix_tail = settings["gbix_tail"]
    gbix_length = settings["gbix_length"]
    reserved = settings["reserved"]

    new_chunk = build_pvr_chunk(
        payload,
        pixel_format=pixel_format,
        data_format=data_format,
        width=raw_image.width,
        height=raw_image.height,
        reserved=reserved,
        gbix_present=gbix_present,
        global_index=global_index,
        gbix_tail=gbix_tail,
        gbix_length=gbix_length,
    )

    if template_raw is not None and template_chunk is not None:
        rebuilt_raw = (
            template_raw[: template_chunk.start]
            + new_chunk
            + template_raw[template_chunk.end :]
        )
    else:
        rebuilt_raw = new_chunk

    output_wrapper = settings["wrapper"]
    output_bytes = apply_wrapper(rebuilt_raw, output_wrapper)
    output_path = Path(args.output) if args.output else png_path.with_suffix(".pvr")
    ensure_parent(output_path)
    output_path.write_bytes(output_bytes)

    if palette_colors is not None:
        palette_format = args.palette_format
        palette_output = (
            Path(args.palette_output)
            if args.palette_output
            else output_path.with_suffix(output_path.suffix + ".clut.bin")
        )
        ensure_parent(palette_output)
        suffix = palette_output.suffix.lower()
        if suffix == ".pvp":
            palette_output.write_bytes(build_pvp(palette_colors, palette_format))
            print(f"PVP: {palette_output}")
        elif suffix == ".act":
            palette_output.write_bytes(palette_to_act(palette_colors))
            print(f"ACT: {palette_output}")
        else:
            palette_output.write_bytes(encode_palette_bytes(palette_colors, palette_format))
            print(f"CLUT: {palette_output}")

    print(f"PVR: {output_path}")
    if template_path:
        print(f"Template: {template_path} (chunk {template_chunk.chunk_index if template_chunk else 0})")
    print(
        f"Encoded {raw_image.width}x{raw_image.height} "
        f"{settings['pixel_format_name']}/{DATA_FORMATS.get(data_format, data_format)}; "
        f"wrapper={output_wrapper}; undo rotate CW {settings['rotate_cw']}, flip {settings['flip']}"
    )
    print(f"SHA-256: {sha256_bytes(output_bytes)}")
    return 0


def command_verify(args: argparse.Namespace) -> int:
    """Decode, encode, and compare an input without needing temporary user files."""
    input_path = Path(args.input)
    source = input_path.read_bytes()
    raw, wrapper = unwrap_data(source, args.wrapper)
    chunks = scan_pvr_chunks(raw)
    chunk = select_chunk(chunks, args.index)
    if chunk.is_mipmapped:
        raise PvrError(
            "byte-identical verify currently targets non-mipmapped chunks; use decode --all-mipmaps "
            "to validate mip extraction"
        )
    palette = None
    if chunk.is_indexed:
        palette_path = Path(args.palette) if args.palette else find_companion_pvp(input_path)
        if palette_path is None:
            raise PvrError("verify for an indexed PVR requires a palette or companion PVP")
        count = 16 if chunk.data_format in (0x05, 0x06) else 256
        palette = load_palette(palette_path, count, args.palette_format)
    image, aux = decode_chunk_image(chunk, palette, detwiddle_mode=args.detwiddle)

    if chunk.pixel_format == 0x06 and not chunk.is_indexed:
        print("Decode successful: YUV420 encoding remains intentionally disabled.")
        print(f"Decoded RGBA SHA-256: {sha256_bytes(image.convert('RGBA').tobytes())}")
        return 0
    if chunk.is_vq:
        if chunk.pixel_format == 0x03:
            print("Decode successful: YUV422 VQ encoding is not yet enabled.")
            return 0
        entries = int(aux["vq_codebook_entries"])
        payload = encode_vq_preserve(
            image,
            chunk.pixel_format,
            b64d(aux["vq_codebook_b64"]),
            b64d(aux["vq_base_indices_b64"]),
            entries,
        )
        data_format = 0x03 if entries == 256 else 0x10
    elif chunk.is_indexed:
        indexed_pf = 0x05 if chunk.data_format == 0x05 else 0x06
        payload, data_format, _ = encode_indexed(image, indexed_pf, palette)
    elif chunk.data_format in TWIDDLED_FORMATS:
        payload, data_format = encode_uncompressed(
            image, chunk.pixel_format, True, chunk.data_format
        )
    elif chunk.data_format in LINEAR_FORMATS or chunk.data_format in ABGR_FORMATS:
        payload, data_format = encode_uncompressed(
            image, chunk.pixel_format, False, chunk.data_format
        )
    else:
        raise PvrError(f"verify is not implemented for {chunk.data_format_name}")

    rebuilt_chunk = build_pvr_chunk(
        payload,
        pixel_format=chunk.pixel_format,
        data_format=data_format,
        width=chunk.width,
        height=chunk.height,
        reserved=chunk.reserved,
        gbix_present=chunk.gbix_present,
        global_index=chunk.global_index or 0,
        gbix_tail=chunk.gbix_tail or 0,
        gbix_length=chunk.gbix_length or 16,
    )
    original_chunk = raw[chunk.start : chunk.end]
    same_chunk = rebuilt_chunk == original_chunk
    print(f"Chunk byte-identical: {'YES' if same_chunk else 'NO'}")
    print(f"Original chunk SHA-256: {sha256_bytes(original_chunk)}")
    print(f"Rebuilt  chunk SHA-256: {sha256_bytes(rebuilt_chunk)}")

    lossy_ok = False
    if not same_chunk and chunk.pixel_format in (0x03, 0x04):
        rebuilt_chunks = scan_pvr_chunks(rebuilt_chunk)
        rebuilt_image, _ = decode_chunk_image(
            rebuilt_chunks[0], palette, detwiddle_mode=args.detwiddle
        )
        original_pixels = image_data(image.convert("RGBA"))
        rebuilt_pixels = image_data(rebuilt_image.convert("RGBA"))
        differences = [
            abs(a - b)
            for p0, p1 in zip(original_pixels, rebuilt_pixels)
            for a, b in zip(p0, p1)
        ]
        max_error = max(differences, default=0)
        mean_error = sum(differences) / max(1, len(differences))
        # YUV422 and bump-normal conversions are mathematically lossy; validate
        # the visible reconstruction rather than requiring identical source words.
        lossy_ok = mean_error <= 3.0 and max_error <= 16
        print(
            f"Lossy visible round-trip: {'PASS' if lossy_ok else 'FAIL'} "
            f"(mean channel error {mean_error:.3f}, max {max_error})"
        )

    if wrapper.kind == "despiria-lzss":
        recompressed = apply_wrapper(
            raw[: chunk.start] + rebuilt_chunk + raw[chunk.end :], wrapper.kind
        )
        redecompressed = lzss_decompress(recompressed)
        same_unwrapped = redecompressed == raw
        print(f"LZSS decompressed content identical: {'YES' if same_unwrapped else 'NO'}")
        print(
            "Compressed byte stream is not expected to match ATLUS's original compressor; "
            "decompressed content is the authoritative comparison."
        )

    return 0 if (same_chunk or lossy_ok) else 2



# ---------------------------------------------------------------------------
# PVP palette-container commands
# ---------------------------------------------------------------------------


def command_pvp_inspect(args: argparse.Namespace) -> int:
    path = Path(args.input)
    palette = parse_pvp(path.read_bytes())
    result = {
        "file": str(path),
        "sha256": sha256_bytes(path.read_bytes()),
        "pixel_type": palette.pixel_type,
        "format": palette.format_name,
        "entry_count": palette.entry_count,
        "length_field": palette.length_field,
        "header_tail_hex": palette.header_tail.hex(),
    }
    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print(f"File: {path}")
        print(f"Format: {palette.format_name} (pixel type 0x{palette.pixel_type:02X})")
        print(f"Entries: {palette.entry_count}")
        print(f"Length field: 0x{palette.length_field:X}")
        print(f"SHA-256: {result['sha256']}")
    return 0


def command_pvp_decode(args: argparse.Namespace) -> int:
    input_path = Path(args.input)
    source = input_path.read_bytes()
    palette = parse_pvp(source)
    image = palette_swatch_image(palette.colors, args.columns, args.cell_size)
    output = Path(args.output) if args.output else input_path.with_suffix(".png")
    ensure_parent(output)
    image.save(output, format="PNG", optimize=False)
    print(f"PNG: {output}")

    if args.act_output:
        act_path = Path(args.act_output)
        ensure_parent(act_path)
        act_path.write_bytes(palette_to_act(palette.colors))
        print(f"ACT: {act_path}")

    if not args.no_sidecar:
        sidecar_path = Path(args.sidecar) if args.sidecar else Path(str(output) + ".pvp.json")
        metadata = {
            "tool": TOOL_NAME,
            "version": TOOL_VERSION,
            "source": {"file": str(input_path), "sha256": sha256_bytes(source)},
            "pvp": {
                "pixel_type": palette.pixel_type,
                "format": palette.format_name,
                "entry_count": palette.entry_count,
                "length_field": palette.length_field,
                "header_tail_b64": b64e(palette.header_tail),
            },
            "swatch": {"columns": args.columns, "cell_size": args.cell_size},
        }
        ensure_parent(sidecar_path)
        sidecar_path.write_text(json.dumps(metadata, indent=2) + "\n", encoding="utf-8")
        print(f"Metadata: {sidecar_path}")
    return 0


def command_pvp_encode(args: argparse.Namespace) -> int:
    input_path = Path(args.input)
    image = Image.open(input_path)
    metadata_path = Path(args.metadata) if args.metadata else Path(str(input_path) + ".pvp.json")
    metadata: dict[str, Any] = {}
    if metadata_path.exists():
        metadata = json.loads(metadata_path.read_text(encoding="utf-8"))
    pvp_meta = metadata.get("pvp", {})
    swatch_meta = metadata.get("swatch", {})

    if args.count == "auto":
        if pvp_meta.get("entry_count"):
            count = int(pvp_meta["entry_count"])
        elif image.mode == "P":
            count = 256
        else:
            count = 256
    else:
        count = int(args.count)
    if count <= 0 or count > 0xFFFF:
        raise PvrError("PVP entry count must be in 1..65535")

    palette_format = (
        str(pvp_meta.get("format", "rgb555"))
        if args.palette_format == "auto"
        else args.palette_format
    )
    columns = int(resolve_auto(args.columns, swatch_meta.get("columns", 16)))
    cell_size = int(resolve_auto(args.cell_size, swatch_meta.get("cell_size", 16)))

    if image.mode == "P":
        _indices, colors = palette_from_png(image, count)
    elif image.width == 1 or image.height == 1:
        pixels = image_data(image.convert("RGBA"))
        if len(pixels) < count:
            raise PvrError(f"palette PNG contains {len(pixels)} pixels; {count} required")
        colors = pixels[:count]
    else:
        colors = palette_from_swatch_image(image, count, columns, cell_size)

    header_tail = b64d(pvp_meta.get("header_tail_b64")) if pvp_meta else b"\x00" * 5
    output_bytes = build_pvp(colors, palette_format, header_tail=header_tail)
    output = Path(args.output) if args.output else input_path.with_suffix(".pvp")
    ensure_parent(output)
    output.write_bytes(output_bytes)
    print(f"PVP: {output}")
    print(f"Format: {palette_format}; entries: {count}")
    print(f"SHA-256: {sha256_bytes(output_bytes)}")

    if args.act_output:
        act_path = Path(args.act_output)
        ensure_parent(act_path)
        act_path.write_bytes(palette_to_act(colors))
        print(f"ACT: {act_path}")
    return 0


# ---------------------------------------------------------------------------
# deSPIRIA AFS / CPR asset containers
# ---------------------------------------------------------------------------


@dataclass
class AfsMember:
    index: int
    offset: int
    size: int
    data: bytes


@dataclass
class AfsArchive:
    count: int
    payload_start: int
    alignment: int
    filename_table_offset: int
    filename_table_size: int
    header: bytes
    members: list[AfsMember]


def align_up(value: int, alignment: int) -> int:
    if alignment <= 0:
        raise PvrError(f"invalid alignment: {alignment}")
    return (value + alignment - 1) // alignment * alignment


def parse_afs(data: bytes) -> AfsArchive:
    if len(data) < 16 or data[:4] != b"AFS\x00":
        raise PvrError("not an AFS archive")
    count = struct.unpack_from("<I", data, 4)[0]
    table_end = 8 + count * 8
    if count <= 0 or table_end > len(data):
        raise PvrError(f"invalid AFS member count/table: {count}")

    members: list[AfsMember] = []
    offsets: list[int] = []
    for index in range(count):
        offset, size = struct.unpack_from("<II", data, 8 + index * 8)
        if offset < table_end or size < 0 or offset + size > len(data):
            raise PvrError(
                f"AFS member {index} range is invalid: offset=0x{offset:X}, size=0x{size:X}"
            )
        members.append(AfsMember(index, offset, size, data[offset : offset + size]))
        offsets.append(offset)

    payload_start = min(offsets)
    filename_table_offset = 0
    filename_table_size = 0
    if table_end + 8 <= payload_start:
        filename_table_offset, filename_table_size = struct.unpack_from("<II", data, table_end)

    # deSPIRIA uses 2,048-byte member alignment. Infer it instead of hard-coding
    # so the parser remains useful on related AFS archives.
    alignment = 2048
    nonzero_offsets = [o for o in offsets if o]
    if nonzero_offsets and not all(o % alignment == 0 for o in nonzero_offsets):
        candidate = 1
        for o in nonzero_offsets:
            candidate = math.gcd(candidate if candidate > 1 else o, o)
        for common in (2048, 1024, 512, 256, 128, 64, 32, 16, 8, 4, 2, 1):
            if all(o % common == 0 for o in nonzero_offsets):
                candidate = common
                break
        alignment = max(1, candidate)

    return AfsArchive(
        count=count,
        payload_start=payload_start,
        alignment=alignment,
        filename_table_offset=filename_table_offset,
        filename_table_size=filename_table_size,
        header=data[:payload_start],
        members=members,
    )


def build_afs(original: bytes, replacement_members: dict[int, bytes]) -> bytes:
    afs = parse_afs(original)
    if afs.filename_table_offset or afs.filename_table_size:
        raise PvrError(
            "AFS rebuilding with a filename table is not enabled. deSPIRIA's supplied "
            "archives have no filename table, so this safeguard should not trigger for them."
        )

    header = bytearray(afs.header)
    output = bytearray(header)
    if len(output) < afs.payload_start:
        output.extend(b"\x00" * (afs.payload_start - len(output)))

    for member in afs.members:
        new_data = replacement_members.get(member.index, member.data)
        new_offset = align_up(len(output), afs.alignment)
        if new_offset > len(output):
            output.extend(b"\x00" * (new_offset - len(output)))
        struct.pack_into("<II", output, 8 + member.index * 8, new_offset, len(new_data))
        output.extend(new_data)

    final_size = align_up(len(output), afs.alignment)
    if final_size > len(output):
        output.extend(b"\x00" * (final_size - len(output)))
    return bytes(output)


def is_probable_cpr(data: bytes) -> bool:
    """Recognize deSPIRIA CPR members without trying LZSS on every AFS member."""
    if len(data) < 8:
        return False
    expected = struct.unpack_from("<I", data, 0)[0]
    # Every confirmed deSPIRIA CPR expands to one ordinary PVR whose length ends
    # in 0x20 (GBIX/PVRT headers plus texture payload). The compressed member is
    # always smaller than the advertised output.
    return 0x820 <= expected <= 0x4000000 and expected > len(data) and expected % 0x20 == 0


def analyze_texture_blob(data: bytes) -> tuple[bytes, WrapperInfo, list[PvrChunk]]:
    direct_chunks = scan_pvr_chunks(data)
    if direct_chunks:
        return data, WrapperInfo("none", len(data), len(data)), direct_chunks

    if is_probable_cpr(data):
        try:
            raw = lzss_decompress(data)
        except PvrError:
            raw = b""
        if raw:
            chunks = scan_pvr_chunks(raw)
            if chunks:
                return raw, WrapperInfo("despiria-lzss", len(data), len(raw)), chunks

    return data, WrapperInfo("none", len(data), len(data)), []


def texture_record(
    *,
    source_name: str,
    member_index: Optional[int],
    member_offset: int,
    member_size: int,
    member_data: bytes,
) -> Optional[dict[str, Any]]:
    raw, wrapper, chunks = analyze_texture_blob(member_data)
    if not chunks:
        return None
    return {
        "source": source_name,
        "member_index": member_index,
        "member_offset": member_offset,
        "member_size": member_size,
        "member_sha256": sha256_bytes(member_data),
        "kind": "cpr" if wrapper.kind == "despiria-lzss" else "pvr-container",
        "wrapper": wrapper.kind,
        "compressed_size": wrapper.compressed_size,
        "decompressed_size": wrapper.decompressed_size,
        "pvr_chunk_count": len(chunks),
        "chunks": [
            {
                "index": c.chunk_index,
                "start": c.start,
                "end": c.end,
                "global_index": c.global_index,
                "pixel_format": c.pixel_format,
                "pixel_format_name": c.pixel_format_name,
                "data_format": c.data_format,
                "data_format_name": c.data_format_name,
                "width": c.width,
                "height": c.height,
                "payload_size": len(c.payload),
            }
            for c in chunks
        ],
    }


def scan_texture_source(path: Path) -> dict[str, Any]:
    source = path.read_bytes()
    result: dict[str, Any] = {
        "tool": TOOL_NAME,
        "version": TOOL_VERSION,
        "source": str(path),
        "source_sha256": sha256_bytes(source),
        "source_size": len(source),
        "source_kind": "afs" if source[:4] == b"AFS\x00" else "file",
        "assets": [],
    }

    if source[:4] == b"AFS\x00":
        afs = parse_afs(source)
        result["afs"] = {
            "member_count": afs.count,
            "payload_start": afs.payload_start,
            "alignment": afs.alignment,
            "filename_table_offset": afs.filename_table_offset,
            "filename_table_size": afs.filename_table_size,
        }
        for member in afs.members:
            record = texture_record(
                source_name=path.name,
                member_index=member.index,
                member_offset=member.offset,
                member_size=member.size,
                member_data=member.data,
            )
            if record:
                result["assets"].append(record)
    else:
        record = texture_record(
            source_name=path.name,
            member_index=None,
            member_offset=0,
            member_size=len(source),
            member_data=source,
        )
        if record:
            result["assets"].append(record)

    result["summary"] = {
        "texture_bearing_members": len(result["assets"]),
        "raw_pvr_members": sum(1 for a in result["assets"] if a["kind"] == "pvr-container"),
        "cpr_members": sum(1 for a in result["assets"] if a["kind"] == "cpr"),
        "pvr_chunks": sum(a["pvr_chunk_count"] for a in result["assets"]),
    }
    return result


def command_inventory(args: argparse.Namespace) -> int:
    path = Path(args.input)
    result = scan_texture_source(path)

    if args.csv:
        csv_path = Path(args.csv)
        ensure_parent(csv_path)
        with csv_path.open("w", encoding="utf-8", newline="") as fh:
            writer = csv.writer(fh)
            writer.writerow(
                [
                    "member_index",
                    "member_offset",
                    "member_size",
                    "container_kind",
                    "wrapper",
                    "chunk_index",
                    "chunk_start",
                    "chunk_end",
                    "width",
                    "height",
                    "pixel_format",
                    "data_format",
                    "global_index",
                ]
            )
            for asset in result["assets"]:
                for chunk in asset["chunks"]:
                    writer.writerow(
                        [
                            "" if asset["member_index"] is None else asset["member_index"],
                            f"0x{asset['member_offset']:X}",
                            asset["member_size"],
                            asset["kind"],
                            asset["wrapper"],
                            chunk["index"],
                            f"0x{chunk['start']:X}",
                            f"0x{chunk['end']:X}",
                            chunk["width"],
                            chunk["height"],
                            chunk["pixel_format_name"],
                            chunk["data_format_name"],
                            "" if chunk["global_index"] is None else chunk["global_index"],
                        ]
                    )
        print(f"CSV: {csv_path}")

    if args.json:
        print(json.dumps(result, indent=2))
        return 0

    print(f"Source: {path}")
    print(f"Kind: {result['source_kind']}")
    if result.get("afs"):
        afs_meta = result["afs"]
        print(
            f"AFS: {afs_meta['member_count']} members; payload=0x{afs_meta['payload_start']:X}; "
            f"alignment={afs_meta['alignment']}"
        )
    summary = result["summary"]
    print(
        f"Texture-bearing members: {summary['texture_bearing_members']} "
        f"({summary['raw_pvr_members']} raw, {summary['cpr_members']} CPR)"
    )
    print(f"PVR chunks: {summary['pvr_chunks']}")
    for asset in result["assets"]:
        member_label = "standalone" if asset["member_index"] is None else f"member {asset['member_index']:04d}"
        print(
            f"  {member_label}: {asset['kind']}; {asset['pvr_chunk_count']} PVR chunk(s); "
            f"{asset['compressed_size']:,} -> {asset['decompressed_size']:,} bytes"
        )
        if args.verbose:
            for chunk in asset["chunks"]:
                print(
                    f"    [{chunk['index']}] {chunk['width']}x{chunk['height']} "
                    f"{chunk['pixel_format_name']}/{chunk['data_format_name']} "
                    f"range=0x{chunk['start']:X}-0x{chunk['end']:X}"
                )
    return 0


def _asset_base_name(member_index: Optional[int], chunk: PvrChunk) -> str:
    member = "standalone" if member_index is None else f"m{member_index:04d}"
    return (
        f"{member}_c{chunk.chunk_index:02d}_{chunk.width}x{chunk.height}_"
        f"{chunk.pixel_format_name}_{chunk.data_format_name}"
    )


def command_extract_assets(args: argparse.Namespace) -> int:
    source_path = Path(args.input)
    source = source_path.read_bytes()
    if args.no_png and args.no_pvr:
        raise PvrError("--no-png and --no-pvr cannot be used together")
    output_dir = Path(args.output)
    if output_dir.exists() and any(output_dir.iterdir()) and not args.overwrite:
        raise PvrError(f"output directory is not empty: {output_dir}; use --overwrite")
    output_dir.mkdir(parents=True, exist_ok=True)
    texture_dir = output_dir / "textures"
    texture_dir.mkdir(parents=True, exist_ok=True)

    wanted_members = set(args.member or [])
    source_kind = "afs" if source[:4] == b"AFS\x00" else "file"
    if source_kind == "afs":
        afs = parse_afs(source)
        candidates = [
            (m.index, m.offset, m.size, m.data) for m in afs.members
            if not wanted_members or m.index in wanted_members
        ]
        afs_meta: Optional[dict[str, Any]] = {
            "member_count": afs.count,
            "payload_start": afs.payload_start,
            "alignment": afs.alignment,
            "filename_table_offset": afs.filename_table_offset,
            "filename_table_size": afs.filename_table_size,
        }
    else:
        if wanted_members:
            raise PvrError("--member is valid only when extracting an AFS archive")
        candidates = [(None, 0, len(source), source)]
        afs_meta = None

    manifest: dict[str, Any] = {
        "tool": TOOL_NAME,
        "version": TOOL_VERSION,
        "source": {
            "file": str(source_path),
            "name": source_path.name,
            "sha256": sha256_bytes(source),
            "size": len(source),
            "kind": source_kind,
        },
        "afs": afs_meta,
        "editing_transform": {
            "rotate_cw": args.rotate_cw,
            "flip": args.flip,
            "decode_order": ["rotate_clockwise", "flip"],
            "encode_inverse_order": ["undo_flip", "undo_rotation"],
        },
        "assets": [],
    }

    skipped_indexed = 0
    written_png = 0
    written_pvr = 0
    for member_index, member_offset, member_size, member_data in candidates:
        raw, wrapper, chunks = analyze_texture_blob(member_data)
        if not chunks:
            continue
        asset_manifest: dict[str, Any] = {
            "member_index": member_index,
            "member_offset": member_offset,
            "member_size": member_size,
            "member_sha256": sha256_bytes(member_data),
            "kind": "cpr" if wrapper.kind == "despiria-lzss" else "pvr-container",
            "wrapper": wrapper.kind,
            "compressed_size": wrapper.compressed_size,
            "decompressed_size": wrapper.decompressed_size,
            "textures": [],
        }

        for chunk in chunks:
            base = _asset_base_name(member_index, chunk)
            chunk_bytes = raw[chunk.start : chunk.end]
            raw_rel: Optional[str] = None
            png_rel: Optional[str] = None
            sidecar_rel: Optional[str] = None

            if not args.no_pvr:
                raw_path = texture_dir / f"{base}.pvr"
                raw_path.write_bytes(chunk_bytes)
                raw_rel = str(raw_path.relative_to(output_dir))
                written_pvr += 1

            if not args.no_png:
                if chunk.is_indexed and not args.palette:
                    print(
                        f"WARNING: {base} is indexed and has no supplied external CLUT; "
                        "raw PVR extracted but PNG skipped",
                        file=sys.stderr,
                    )
                    skipped_indexed += 1
                else:
                    palette = None
                    if chunk.is_indexed:
                        count = 16 if chunk.data_format in (0x05, 0x06) else 256
                        palette = load_palette(Path(args.palette), count, args.palette_format)
                    image, aux = decode_chunk_image(
                        chunk, palette, detwiddle_mode=args.detwiddle
                    )
                    if palette is not None:
                        aux.setdefault("palette_colors", [list(c) for c in palette])
                    transformed = apply_edit_transform(image, args.rotate_cw, args.flip)
                    png_path = texture_dir / f"{base}.png"
                    transformed.save(png_path, format="PNG", optimize=False)
                    sidecar_path = default_sidecar_path(png_path)
                    sidecar = make_sidecar(
                        input_path=Path(raw_rel or f"{base}.pvr"),
                        source_bytes=member_data,
                        raw_container=raw,
                        wrapper=wrapper,
                        chunk=chunk,
                        image_before_transform=image,
                        image_after_transform=transformed,
                        rotate_cw=args.rotate_cw,
                        flip=args.flip,
                        aux=aux,
                        palette_format=args.palette_format if palette is not None else None,
                    )
                    # Point ordinary `encode` at the separately extracted raw PVR
                    # when available, while retaining full AFS/CPR provenance for
                    # `rebuild-assets`.
                    if raw_rel:
                        sidecar["source"]["file"] = str(output_dir / raw_rel)
                    sidecar["asset_container"] = {
                        "source_file": str(source_path),
                        "source_sha256": sha256_bytes(source),
                        "source_kind": source_kind,
                        "afs_member_index": member_index,
                        "afs_member_offset": member_offset,
                        "afs_member_size": member_size,
                        "member_sha256": sha256_bytes(member_data),
                        "member_wrapper": wrapper.kind,
                    }
                    sidecar_path.write_text(json.dumps(sidecar, indent=2) + "\n", encoding="utf-8")
                    png_rel = str(png_path.relative_to(output_dir))
                    sidecar_rel = str(sidecar_path.relative_to(output_dir))
                    written_png += 1

            asset_manifest["textures"].append(
                {
                    "chunk_index": chunk.chunk_index,
                    "chunk_start": chunk.start,
                    "chunk_end": chunk.end,
                    "width": chunk.width,
                    "height": chunk.height,
                    "pixel_format": chunk.pixel_format_name,
                    "data_format": chunk.data_format_name,
                    "raw_pvr": raw_rel,
                    "png": png_rel,
                    "sidecar": sidecar_rel,
                }
            )
        manifest["assets"].append(asset_manifest)

    manifest["summary"] = {
        "texture_bearing_members": len(manifest["assets"]),
        "pvr_chunks": sum(len(a["textures"]) for a in manifest["assets"]),
        "raw_pvr_files_written": written_pvr,
        "png_files_written": written_png,
        "indexed_pngs_skipped": skipped_indexed,
    }
    manifest_path = output_dir / "asset_manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(f"Manifest: {manifest_path}")
    print(
        f"Extracted {manifest['summary']['pvr_chunks']} PVR chunk(s) from "
        f"{manifest['summary']['texture_bearing_members']} texture-bearing member(s): "
        f"{written_pvr} raw PVR, {written_png} PNG"
    )
    return 0


def _png_is_unchanged(png_path: Path, sidecar: dict[str, Any]) -> bool:
    expected = sidecar.get("png", {}).get("edited_orientation_rgba_sha256")
    if not expected:
        return False
    with Image.open(png_path) as image:
        actual = sha256_bytes(image.convert("RGBA").tobytes())
    return actual == expected


def _encode_asset_png(
    *,
    png_path: Path,
    sidecar_path: Path,
    template_path: Path,
    output_path: Path,
    chunk_index: int,
    args: argparse.Namespace,
) -> None:
    encode_args = argparse.Namespace(
        input=str(png_path),
        output=str(output_path),
        metadata=str(sidecar_path),
        template=str(template_path),
        template_wrapper="auto",
        index=chunk_index,
        rotate_cw="auto",
        flip="auto",
        pixel_format="auto",
        twiddle=args.twiddle,
        vq=args.vq,
        vq_codebook_size=args.vq_codebook_size,
        vq_iterations=args.vq_iterations,
        vq_seed=args.vq_seed,
        mipmaps=args.mipmaps,
        gbix="auto",
        palette=args.palette,
        palette_format=args.palette_format,
        palette_output=None,
        wrapper=args.wrapper,
    )
    # Keep the batch rebuild output readable; command_encode's detailed per-file
    # report is still available when users call `encode` directly.
    capture = io.StringIO()
    with contextlib.redirect_stdout(capture):
        rc = command_encode(encode_args)
    if rc:
        raise PvrError(f"failed to encode {png_path}")


def command_rebuild_assets(args: argparse.Namespace) -> int:
    manifest_path = Path(args.manifest)
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    base_dir = manifest_path.parent
    source_path = Path(args.source) if args.source else Path(manifest["source"]["file"])
    if not source_path.exists():
        fallback = base_dir / manifest["source"].get("name", source_path.name)
        if fallback.exists():
            source_path = fallback
        else:
            raise PvrError(f"source container not found: {source_path}; use --source")
    source = source_path.read_bytes()
    expected_sha = manifest["source"].get("sha256")
    if expected_sha and sha256_bytes(source) != expected_sha and not args.force:
        raise PvrError(
            "source SHA-256 does not match the extraction manifest; use the original source "
            "or pass --force after confirming it is structurally compatible"
        )

    source_kind = manifest["source"]["kind"]
    if source_kind == "afs":
        afs = parse_afs(source)
        original_members = {m.index: m.data for m in afs.members}
    else:
        original_members = {None: source}

    replacements: dict[Any, bytes] = {}
    changed_pngs = 0
    changed_members = 0
    with tempfile.TemporaryDirectory(prefix="despiria_pvr_rebuild_") as tmp_name:
        tmp = Path(tmp_name)
        for asset in manifest.get("assets", []):
            member_index = asset.get("member_index")
            if member_index not in original_members:
                raise PvrError(f"manifest references missing member {member_index}")
            current_member = original_members[member_index]
            member_changed = False

            for texture in sorted(asset.get("textures", []), key=lambda x: x["chunk_index"]):
                if not texture.get("png") or not texture.get("sidecar"):
                    continue
                png_path = base_dir / texture["png"]
                sidecar_path = base_dir / texture["sidecar"]
                if not png_path.exists():
                    continue
                if not sidecar_path.exists():
                    raise PvrError(f"sidecar missing for {png_path}: {sidecar_path}")
                sidecar = json.loads(sidecar_path.read_text(encoding="utf-8"))
                if _png_is_unchanged(png_path, sidecar):
                    continue

                template_path = tmp / "member_current.bin"
                output_path = tmp / "member_next.bin"
                template_path.write_bytes(current_member)
                _encode_asset_png(
                    png_path=png_path,
                    sidecar_path=sidecar_path,
                    template_path=template_path,
                    output_path=output_path,
                    chunk_index=int(texture["chunk_index"]),
                    args=args,
                )
                current_member = output_path.read_bytes()
                member_changed = True
                changed_pngs += 1

            if member_changed:
                replacements[member_index] = current_member
                changed_members += 1

    if not replacements:
        output_bytes = source
    elif source_kind == "afs":
        output_bytes = build_afs(source, {int(k): v for k, v in replacements.items()})
    else:
        output_bytes = replacements.get(None, source)

    output_path = Path(args.output)
    ensure_parent(output_path)
    output_path.write_bytes(output_bytes)
    print(f"Output: {output_path}")
    print(f"Changed PNGs: {changed_pngs}; rebuilt members: {changed_members}")
    print(f"SHA-256: {sha256_bytes(output_bytes)}")
    if changed_pngs == 0 and output_bytes == source:
        print("No edited PNGs detected; output is byte-identical to the source.")
    return 0


# ---------------------------------------------------------------------------
# Argument parser
# ---------------------------------------------------------------------------


def add_wrapper_argument(parser: argparse.ArgumentParser, *, encode: bool = False) -> None:
    parser.add_argument(
        "--wrapper",
        choices=("auto", "none", "despiria-lzss"),
        default="auto",
        help=(
            "outer file wrapper; auto detects/preserves deSPIRIA's size+LZSS wrapper"
            if encode
            else "outer file wrapper; default: auto-detect"
        ),
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Convert deSPIRIA/Dreamcast PVR textures to and from editable PNG files.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Orientation example for deSPIRIA's main-menu atlas:
  decode: --rotate-cw 90 --flip horizontal
  encode: the sidecar automatically reverses that as flip first, then 90 CCW.

Examples:
  python despiria_pvr_tool.py inspect titleetc.pvr
  python despiria_pvr_tool.py decode titleetc.pvr -o title.png --rotate-cw 90 --flip horizontal
  python despiria_pvr_tool.py encode title.png -o title_new.pvr
  python despiria_pvr_tool.py encode image.png -o image.pvr --pixel-format argb4444 --twiddle on --vq off
  python despiria_pvr_tool.py encode image.png -o image_vq.pvr --pixel-format rgb565 --vq rebuild
        """,
    )
    parser.add_argument("--version", action="version", version=f"%(prog)s {TOOL_VERSION}")
    sub = parser.add_subparsers(dest="command", required=True)

    inspect = sub.add_parser("inspect", help="show wrapper, PVR chunks, formats, and dimensions")
    inspect.add_argument("input")
    inspect.add_argument("--json", action="store_true", help="emit machine-readable JSON")
    add_wrapper_argument(inspect)
    inspect.set_defaults(func=command_inspect)

    decode = sub.add_parser("decode", help="convert one PVR chunk to PNG and write a sidecar")
    decode.add_argument("input")
    decode.add_argument("-o", "--output")
    decode.add_argument("--index", type=int, help="PVR chunk index when the file contains multiple chunks")
    decode.add_argument("--mip-level", type=int, default=0, help="mip level to decode; 0 is the base level")
    decode.add_argument("--all-mipmaps", action="store_true", help="export every safely sliceable mip level")
    decode.add_argument(
        "--detwiddle", choices=DETWIDDLE_MODES, default="morton",
        help="twiddle decoder: morton, independent reference, compare both, or explicit stride fallback",
    )
    decode.add_argument(
        "--rotate-cw",
        type=int,
        choices=ROTATIONS,
        default=0,
        help="clockwise rotation applied before flip; default: 0",
    )
    decode.add_argument(
        "--flip",
        choices=FLIP_NAMES,
        default="none",
        help="flip applied after rotation; default: none",
    )
    decode.add_argument("--palette", help="external CLUT for PAL4/PAL8 PVRs (.bin, .pvp, .act, or .png); companion PVP is auto-detected")
    decode.add_argument(
        "--palette-format",
        choices=("argb1555", "rgb555", "rgb565", "argb4444", "argb8888"),
        default="argb1555",
        help="external CLUT color format; default: argb1555",
    )
    decode.add_argument("--sidecar", help="metadata JSON output path")
    decode.add_argument("--no-sidecar", action="store_true", help="do not write metadata JSON")
    add_wrapper_argument(decode)
    decode.set_defaults(func=command_decode)

    encode = sub.add_parser("encode", help="convert PNG back to PVR, using its sidecar/template when available")
    encode.add_argument("input")
    encode.add_argument("-o", "--output")
    encode.add_argument("--metadata", help="sidecar JSON; default: INPUT.png.pvr.json if present")
    encode.add_argument("--template", help="original PVR/container whose selected chunk will be replaced")
    encode.add_argument(
        "--template-wrapper",
        choices=("auto", "none", "despiria-lzss"),
        default="auto",
        help="wrapper used by --template; default: auto",
    )
    encode.add_argument("--index", type=int, help="PVR chunk index in --template")
    encode.add_argument(
        "--rotate-cw",
        choices=("auto", "0", "90", "180", "270"),
        default="auto",
        help="editing rotation to undo; auto reads sidecar",
    )
    encode.add_argument(
        "--flip",
        choices=("auto",) + FLIP_NAMES,
        default="auto",
        help="editing flip to undo; auto reads sidecar",
    )
    encode.add_argument(
        "--pixel-format",
        choices=(
            "auto", "argb1555", "rgb555", "rgb565", "argb4444",
            "yuv422", "bump", "yuv420", "argb8888", "pal4", "pal8",
        ),
        default="auto",
        help="PVR color format; auto preserves sidecar or infers from alpha",
    )
    encode.add_argument(
        "--twiddle",
        choices=("auto", "on", "off"),
        default="auto",
        help="twiddling; auto preserves source, on uses twiddled/rectangular-twiddled, off uses linear",
    )
    encode.add_argument(
        "--vq",
        choices=("auto", "off", "on", "preserve", "rebuild"),
        default="auto",
        help=(
            "VQ compression: auto preserves source; preserve reuses original codebook; "
            "rebuild/on generates a new codebook; off writes uncompressed pixels"
        ),
    )
    encode.add_argument(
        "--vq-codebook-size",
        choices=("auto", "8", "16", "32", "64", "128", "256"),
        default="auto",
        help="256 creates standard VQ; smaller values create Small VQ",
    )
    encode.add_argument("--vq-iterations", type=int, default=8, help="VQ k-means iterations; default: 8")
    encode.add_argument("--vq-seed", type=int, default=0, help="deterministic VQ seed; default: 0")
    encode.add_argument(
        "--mipmaps",
        choices=("auto", "on", "off"),
        default="auto",
        help="v1.2.1 exports mip levels and can remove, but does not yet regenerate complete mip chains",
    )
    encode.add_argument(
        "--gbix",
        default="auto",
        help="auto, none, or a decimal/0x global-index value",
    )
    encode.add_argument("--palette", help="external palette/CLUT (.bin, .pvp, .act, or .png)")
    encode.add_argument(
        "--palette-format",
        choices=("argb1555", "rgb555", "rgb565", "argb4444", "argb8888"),
        default="argb1555",
        help="CLUT output color format; default: argb1555",
    )
    encode.add_argument("--palette-output", help="palette output; .pvp writes PVPL, .act writes ACT, otherwise raw CLUT")
    add_wrapper_argument(encode, encode=True)
    encode.set_defaults(func=command_encode)

    verify = sub.add_parser("verify", help="test a no-edit decode/encode round trip")
    verify.add_argument("input")
    verify.add_argument("--index", type=int)
    verify.add_argument(
        "--detwiddle", choices=DETWIDDLE_MODES, default="compare",
        help="twiddle decoder used during verification; default cross-checks both implementations",
    )
    verify.add_argument("--palette", help="external CLUT for PAL4/PAL8 verification")
    verify.add_argument(
        "--palette-format",
        choices=("argb1555", "rgb555", "rgb565", "argb4444", "argb8888"),
        default="argb1555",
        help="external CLUT color format; default: argb1555",
    )
    add_wrapper_argument(verify)
    verify.set_defaults(func=command_verify)


    pvp_inspect = sub.add_parser("pvp-inspect", help="inspect a PVPL/PVP palette container")
    pvp_inspect.add_argument("input")
    pvp_inspect.add_argument("--json", action="store_true")
    pvp_inspect.set_defaults(func=command_pvp_inspect)

    pvp_decode = sub.add_parser("pvp-decode", help="convert a PVP palette to an editable swatch PNG")
    pvp_decode.add_argument("input")
    pvp_decode.add_argument("-o", "--output")
    pvp_decode.add_argument("--columns", type=int, default=16)
    pvp_decode.add_argument("--cell-size", type=int, default=16)
    pvp_decode.add_argument("--act-output", help="also export a 768-byte Adobe ACT palette")
    pvp_decode.add_argument("--sidecar")
    pvp_decode.add_argument("--no-sidecar", action="store_true")
    pvp_decode.set_defaults(func=command_pvp_decode)

    pvp_encode = sub.add_parser("pvp-encode", help="convert an indexed or swatch PNG back to PVP")
    pvp_encode.add_argument("input")
    pvp_encode.add_argument("-o", "--output")
    pvp_encode.add_argument("--metadata", help="PVP sidecar; default INPUT.png.pvp.json")
    pvp_encode.add_argument(
        "--palette-format",
        choices=("auto", "rgb555", "rgb565", "argb4444", "argb8888"),
        default="auto",
    )
    pvp_encode.add_argument("--count", default="auto", help="auto or palette entry count")
    pvp_encode.add_argument("--columns", default="auto", help="auto or swatch columns")
    pvp_encode.add_argument("--cell-size", default="auto", help="auto or swatch cell size")
    pvp_encode.add_argument("--act-output", help="also export a 768-byte Adobe ACT palette")
    pvp_encode.set_defaults(func=command_pvp_encode)


    inventory = sub.add_parser(
        "inventory",
        help="scan a standalone file or AFS archive for raw PVR, concatenated PVR, and CPR assets",
    )
    inventory.add_argument("input")
    inventory.add_argument("--json", action="store_true", help="emit machine-readable JSON")
    inventory.add_argument("--csv", help="write one row per PVR chunk")
    inventory.add_argument("--verbose", action="store_true", help="list every PVR chunk")
    inventory.set_defaults(func=command_inventory)

    extract_assets = sub.add_parser(
        "extract-assets",
        help="extract every PVR chunk from a file or AFS, including CPR members, to PVR/PNG",
    )
    extract_assets.add_argument("input")
    extract_assets.add_argument("-o", "--output", required=True)
    extract_assets.add_argument(
        "--member",
        type=int,
        action="append",
        help="AFS member index to extract; repeat for multiple members; default: all texture members",
    )
    extract_assets.add_argument(
        "--rotate-cw", type=int, choices=ROTATIONS, default=0,
        help="clockwise rotation applied before flip to every decoded PNG",
    )
    extract_assets.add_argument(
        "--flip", choices=FLIP_NAMES, default="none",
        help="flip applied after rotation to every decoded PNG",
    )
    extract_assets.add_argument(
        "--detwiddle", choices=DETWIDDLE_MODES, default="morton",
        help="twiddle decoder used for batch extraction",
    )
    extract_assets.add_argument("--no-png", action="store_true", help="extract raw PVR chunks only")
    extract_assets.add_argument("--no-pvr", action="store_true", help="write PNG/sidecars only")
    extract_assets.add_argument("--palette", help="external CLUT for indexed assets")
    extract_assets.add_argument(
        "--palette-format",
        choices=("argb1555", "rgb555", "rgb565", "argb4444", "argb8888"),
        default="argb1555",
    )
    extract_assets.add_argument("--overwrite", action="store_true")
    extract_assets.set_defaults(func=command_extract_assets)

    rebuild_assets = sub.add_parser(
        "rebuild-assets",
        help="reinsert edited PNGs from an extraction manifest and rebuild CPR/AFS containers",
    )
    rebuild_assets.add_argument("manifest")
    rebuild_assets.add_argument("-o", "--output", required=True)
    rebuild_assets.add_argument("--source", help="original AFS/CPR/PVR source; default: manifest path")
    rebuild_assets.add_argument(
        "--twiddle", choices=("auto", "on", "off"), default="auto",
        help="preserve, force, or remove twiddling for edited textures",
    )
    rebuild_assets.add_argument(
        "--vq", choices=("auto", "off", "on", "preserve", "rebuild"), default="auto",
    )
    rebuild_assets.add_argument(
        "--vq-codebook-size", choices=("auto", "8", "16", "32", "64", "128", "256"), default="auto",
    )
    rebuild_assets.add_argument("--vq-iterations", type=int, default=8)
    rebuild_assets.add_argument("--vq-seed", type=int, default=0)
    rebuild_assets.add_argument(
        "--wrapper", choices=("auto", "none", "despiria-lzss"), default="auto",
        help="preserve, remove, or force the CPR LZSS wrapper for edited members",
    )
    rebuild_assets.add_argument(
        "--mipmaps", choices=("auto", "on", "off"), default="auto",
    )
    rebuild_assets.add_argument("--palette", help="external CLUT for indexed assets")
    rebuild_assets.add_argument(
        "--palette-format",
        choices=("argb1555", "rgb555", "rgb565", "argb4444", "argb8888"),
        default="argb1555",
    )
    rebuild_assets.add_argument("--force", action="store_true", help="allow a source SHA mismatch")
    rebuild_assets.set_defaults(func=command_rebuild_assets)

    return parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    # Encode rotation arrives as a string because it also accepts "auto".
    if args.command == "encode" and args.rotate_cw != "auto":
        args.rotate_cw = int(args.rotate_cw)
    try:
        return int(args.func(args))
    except (PvrError, OSError, ValueError, struct.error, json.JSONDecodeError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
