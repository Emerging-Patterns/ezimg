# ezimg

Images for [Bend 2](https://github.com/bendlang/bend).

## Install

ezimg is built and checked on bend 2.0.38.

With [Bend](https://github.com/bendlang/bend) alone there is no install
step: import ezimg by its hub name and `bend` fetches it from
[the hub](https://hub.bend-lang.com) into `~/.bend/lib` on the first run.
`emerging-ezimg@1.2.0.0` is ezimg v1.2.0:

```
import emerging-ezimg@1.2.0.0/main.bend as Img
```

That name resolves to `0x57618559b9b26dd8415f821176a3e692`.
To pin by content instead, import `0x57618559b9b26dd8415f821176a3e692/main.bend`.

Or with [ez](https://github.com/Emerging-Patterns/ez), which records the
package in `ez.toml` (`ez init` makes one):

```
ez add Emerging-Patterns/ezimg
```

## Usage

A picture is a `Raster`: a width, a height, and row-major samples. Bend's own
`Image` is the window quadtree, so a file image lives under this name.
`png_sig` is the eight-byte PNG signature. `parse_signature` returns that
signature when the bytes open with it, and none otherwise. `decode_png` returns a raster for an 8-bit PNG. `decode_jpeg` returns a
raster for a baseline sequential JPEG, and none when the bytes are not one.
`encode_jpeg` writes a baseline sequential 4:4:4 JPEG of the samples' colour,
dropping alpha, and returns none for exactly the rasters `encode_png` refuses. Every sample is one `U32` packed `0xAARRGGBB`, whichever
decoder returned it: a JPEG sample has alpha 255, and a gray JPEG sample
repeats its level in R, G and B.
`raster(w, h, px)` takes the samples as they are, and `checked_raster(w, h, px)`
returns none unless there are exactly `w * h` of them. `width`, `height`,
`size`, `count`, `fill`, `get`, `set`, `crop`, `blit` and `map` are the
pixel helpers. `count` is the number of samples as a natural number (`w * h`
for a well-formed raster), and every helper reaches sample `y * w + x` a row
at a time, so no size or index wraps, whatever the sides.

```
import emerging-ezimg@1.2.0.0/main.bend as Img

def main() -> U32:
  Img.width(Img.raster(2, 3, [0, 1, 2, 3, 4, 5]))
```

## Compliance

[LAWS.bend](LAWS.bend) lists every behavior ezimg guarantees, one file under
[laws/](laws/) each, against [ISO/IEC 15948](https://www.iso.org/standard/29581.html)
and the [W3C PNG specification](https://www.w3.org/TR/png/) for PNG, and
[ISO/IEC 10918-1](https://www.iso.org/standard/18902.html) | ITU-T T.81 with
JFIF (ITU-T T.871) for JPEG. Each is proved by the file of the same name
under [proofs/](proofs/) and checked by `bend PROOF.bend` (the first line
must be `ALL PROOFS CHECK`). What ezimg trusts rather than proves, such as
reading other encoders' files, is said on the code that assumes it. The plan
and the audit behind them are in [docs/rfc/ezimg-spec.md](docs/rfc/ezimg-spec.md).

Scope today: PNG decode reads 8-bit colour types 0, 2, 3, 4 and 6 without
interlace, and refuses anything else; PNG encode writes colour type 2 or 6,
for rasters of fewer than 2^28 samples. JPEG decode reads baseline
sequential frames and refuses progressive and arithmetic ones; JPEG encode
writes baseline 4:4:4. Full codec conformance is not claimed.

PNG encode does not compress. Every row has filter type None and the zlib
stream is stored (uncompressed) DEFLATE blocks, so a file is about the size
of its samples: `h * (k * w + 1)` bytes for `k` = 3 (RGB) or 4 (RGBA)
channels, plus 5 bytes per 65535 of them and about 60 bytes of chunks. A
320x260 RGB picture is about 250 KB, where zlib at level 6 makes about
33 KB of the same picture. The round-trip proof rests on the stored blocks;
re-compress the file with another tool when size matters.
