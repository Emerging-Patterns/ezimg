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

Closed equalities in `LAWS.bend`, proved in `PROOF.bend`
(`bend PROOF.bend`), target:

- [ISO/IEC 15948](https://www.iso.org/standard/29581.html) (PNG) and the
  [W3C PNG specification](https://www.w3.org/TR/png/): the eight-byte
  signature.
- [ISO/IEC 10918-1](https://www.iso.org/standard/18902.html) | ITU-T T.81:
  the SOI, EOI, APP0, SOF0, SOF2, SOF9, DHT, DQT, and SOS marker bytes, and a
  baseline sequential 8-bit Huffman frame (SOF0) decoded to gray and to
  4:4:4 YCbCr samples. Progressive SOF2 and arithmetic SOF9 decode as none.
  A baseline SOF0 encode of the same shape writes SOI, APP0, the JFIF
  identifier, DQT, SOF0, DHT, SOS, and EOI. A 1 by 1 and a 2 by 2 neutral
  solid (packed sample 8421504) round-trip through that encode and decode.
  Annex A.3.3: a constant level-shifted block has no AC coefficient, and the
  forward and inverse transforms restore an 8 by 8 horizontal step. An 8 by 1
  picture of that step round-trips through encode and the all-ones quantiser.
- JFIF, [ISO/IEC 10918-5](https://www.iso.org/standard/54989.html) | ITU-T
  T.871: the APP0 identifier `JFIF`, and the neutral and one saturated
  YCbCr triple converted to a packed RGB sample.
- [ISO/IEC 15948](https://www.iso.org/standard/29581.html) (PNG) and the
  [W3C PNG specification](https://www.w3.org/TR/png/): chunk layout and CRC-32
  (ISO 3309 / ITU-T V.42) over the chunk type and data.
- IHDR fields: width, height, bit depth, colour type, compression method,
  filter method, and interlace method.
- Scanline filters None, Sub, Up, Average, and Paeth (filter method 0).
- IDAT as zlib-wrapped DEFLATE, PNG compression method 0 (proved on a stored
  block).
- 8-bit colour types 0, 2, 3, 4, and 6, interlace method 0.
- Encoding 8-bit colour type 2 when every sample is opaque, and colour type 6
  otherwise, interlace method 0, filter None, a zlib stored-block IDAT
  (compression method 0), and CRC-32 on IHDR, IDAT, and IEND. Decoding that
  encoding returns the picture.

Full codec conformance is not claimed yet.
