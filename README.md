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
signature when the bytes open with it, and none otherwise. `decode_png` and
`decode_jpeg` return none until the codecs land. `width`, `height`, `size`,
`count`, and `fill` are the pixel helpers.

```
import ./ezimg/main.bend as Img

def main() -> U32:
  Img.width(Img.raster(2, 3, [0, 1, 2, 3, 4, 5]))
```

## Compliance

Closed equalities in `ezimg/LAWS.bend`, proved in `ezimg/PROOF.bend`
(`bend ezimg/PROOF.bend`), target:

- [ISO/IEC 15948](https://www.iso.org/standard/29581.html) (PNG) and the
  [W3C PNG specification](https://www.w3.org/TR/png/): the eight-byte
  signature.
- [ISO/IEC 10918-1](https://www.iso.org/standard/18902.html) | ITU-T T.81: the
  JPEG start-of-image marker.
- JFIF, [ISO/IEC 10918-5](https://www.iso.org/standard/54989.html) | ITU-T
  T.871: the interchange format those bytes open.
- [ISO/IEC 15948](https://www.iso.org/standard/29581.html) (PNG) and the
  [W3C PNG specification](https://www.w3.org/TR/png/): chunk layout and CRC-32
  (ISO 3309 / ITU-T V.42) over the chunk type and data.
- IHDR fields: width, height, bit depth, colour type, compression method,
  filter method, and interlace method.
- Scanline filters None, Sub, Up, Average, and Paeth (filter method 0).
- IDAT as zlib-wrapped DEFLATE, PNG compression method 0 (proved on a stored
  block).
- 8-bit colour types 0, 2, 3, 4, and 6, interlace method 0.

Full codec conformance is not claimed yet.
