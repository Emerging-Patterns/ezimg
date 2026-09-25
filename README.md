# ezimg

Images for [Bend 2](https://github.com/bendlang/bend).

## Install

Use with [Bend](https://github.com/bendlang/bend) or install easily with [ez](https://github.com/Emerging-Patterns/ez):

```
ez init
ez add Emerging-Patterns/ezimg
```

## Usage

A picture is a `Raster`: a width, a height, and row-major samples. Bend's own
`Image` is the window quadtree, so a file image lives under this name.
`png_sig` is the eight-byte PNG signature. `parse_signature` returns that
signature when the bytes open with it, and none otherwise. `decode_png` returns a raster for an 8-bit PNG. `decode_jpeg` returns a
raster for a baseline sequential JPEG, and none when the bytes are not one.
`encode_jpeg` writes a baseline sequential 4:4:4 JPEG from packed RGB samples.
`width`,
`height`, `size`, `count`, and `fill` are the pixel helpers.

```
import ./main.bend as Img

def main() -> U32:
  Img.width(Img.raster(2, 3, [0, 1, 2, 3, 4, 5]))
```

## Compliance

[SPEC.md](SPEC.md) lists every behavior ezimg guarantees, each under a stable
ID, against [ISO/IEC 15948](https://www.iso.org/standard/29581.html) and the
[W3C PNG specification](https://www.w3.org/TR/png/) for PNG, and
[ISO/IEC 10918-1](https://www.iso.org/standard/18902.html) | ITU-T T.81 with
JFIF (ITU-T T.871) for JPEG. A requirement is either Proved, by a quantified
law in `LAWS.bend` that `bend PROOF.bend` checks, or Trusted, with the reason
in SPEC.md's trust boundary. Every Proved row is pending today: the laws that
stood here each checked one fixed input and were retired, and the quantified
laws are landing row by row. The plan and the audit behind it are in
[docs/rfc/ezimg-spec.md](docs/rfc/ezimg-spec.md).

Scope today: PNG decode reads 8-bit colour types 0, 2, 3, 4 and 6 without
interlace, and refuses anything else; PNG encode writes colour type 2 or 6.
JPEG decode reads baseline sequential frames and refuses progressive and
arithmetic ones; JPEG encode writes baseline 4:4:4. Full codec conformance is
not claimed.
