# ezimg specification

This is the list of every behavior ezimg guarantees, each under a stable requirement ID. The public interface is `main.bend`; the modules under `src/` are internal and carry no promise of their own, except where a row names them.

Every requirement has one of two levels. A **Proved** requirement holds for every input, and is backed by a quantified law (a `for` or `exs` binder) in `LAWS.bend` that passes the proof gate. A **Trusted** requirement is an assumption ezimg cannot check from inside its own gate, and it is listed in the trust boundary below. A Proved requirement whose laws have not all landed has status **pending**: we intend to prove it, and until then it is not guaranteed. The proof gate is this check: the first line `bend PROOF.bend` prints is exactly `All terms check.` Tests and fixtures, the Pillow comparison in `bench/` included, are never evidence for a requirement.

A raster is **well formed** when its sample count equals `w * h` computed as a natural number. A **sample** is one `U32`, packed `0xAARRGGBB`.

The reasoning behind each requirement, the verdict of each against the code at `cbc4358`, and the decisions that shaped them are in [docs/rfc/ezimg-spec.md](docs/rfc/ezimg-spec.md). Every law as it stood then, the findings of the audit, and the progress of the rollout are in [docs/rfc/ezimg-law-inventory.md](docs/rfc/ezimg-law-inventory.md).

## Format

A requirement table is any table whose header row is exactly `| ID | Requirement | Level | Status | Law |`. An ID is uppercase segments joined by hyphens, at least two (`[A-Z][A-Z0-9]*(-[A-Z0-9]+)+`), unique within the requirement tables, and never reused once released. Level is `Proved` or `Trusted`. Status is `proved` or `pending` for a Proved row and empty for a Trusted row. A Law cell holds `<path> <law>` entries, paths relative to this file, separated by `; `. A proved row names one or more laws, and together they prove it. A pending row may name laws that each prove part of it; the row stays pending until its requirement is proved in full, and "Left to prove" says what is missing.

A law proves a requirement when a comment line `# <ID>`, alone on its line, sits in the unbroken comment block directly above its `law` line. A law may carry several tags, one per line:

```
# LAW: a well-formed raster round-trips through PNG
# IMG-PNG-2
law png_round_trip:
```

A tag may name a proved or a pending requirement, never a Trusted one or an ID no requirement table lists. bolt's `trace` rule checks all of this over the whole tree, and its `closed` rule rejects a law with no binder; both are errors in `bolt.bend`.

## Requirements

### The raster (IMG-RAS)

`main.bend`: the `Raster` type and its helpers. Every row is stated over well-formed rasters.

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| IMG-RAS-1 | `fill(w, h, c)` is well formed and every sample is `c`, for every `w`, `h` with `w * h < 2^32` and every `c`. | Proved | pending | |
| IMG-RAS-2 | For every well-formed raster `r` and every `x`, `y`: `get(r, x, y)` is `Some` of sample `y * w + x` when `x < w` and `y < h`, and none otherwise; `set(r, x, y, c)` changes exactly that sample to `c` when the point is inside and returns `r` unchanged otherwise. | Proved | pending | |
| IMG-RAS-3 | For every well-formed `r` and rectangle `(x, y, cw, ch)`, `crop` is well formed, its size is the rectangle's intersection with `r` (0 by 0 when that is empty), and its sample at `(i, j)` is `r`'s sample at `(x + i, y + j)`. | Proved | pending | |
| IMG-RAS-4 | For every well-formed `dst` and `src` and offset `(x, y)`, `blit(dst, src, x, y)` has `dst`'s size, takes `src`'s sample at every point of `dst` that `src` covers, and leaves every other sample of `dst` unchanged. | Proved | pending | |
| IMG-RAS-5 | For every raster `r` and function `f`, `map(f, r)` has `r`'s size and its sample `k` is `f` of `r`'s sample `k`. | Proved | proved | LAWS.bend map_size; LAWS.bend map_at |

### One sample format (IMG-PIX)

What a sample means, for every decoder and encoder.

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| IMG-PIX-1 | Every sample `decode_png` and `decode_jpeg` return is packed `0xAARRGGBB`. Every JPEG sample has alpha 255, and a gray JPEG sample carries its Y value in R, G and B. | Proved | pending | LAWS.bend jpeg_rgb_opaque; LAWS.bend jpeg_gray_opaque |
| IMG-PIX-2 | `encode_jpeg` reads only the low 24 bits of each sample: two rasters that differ only in alpha encode to the same bytes. | Proved | proved | LAWS.bend jpeg_alpha_blind |

### PNG (IMG-PNG)

[ISO/IEC 15948](https://www.iso.org/standard/29581.html) and the [W3C PNG specification](https://www.w3.org/TR/png/): `decode_png`, `encode_png`, `parse_signature`, and the CRC-32 and inflate they rest on.

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| IMG-PNG-1 | `parse_signature(xs)` is `Some(png_sig())` exactly when `xs` begins with the eight bytes 137 80 78 71 13 10 26 10, and none otherwise. | Proved | proved | LAWS.bend sig_opens; LAWS.bend sig_only |
| IMG-PNG-2 | For every well-formed raster `r` with both sides nonzero, `decode_png(encode_png(r))` is `Some(r)`. | Proved | pending | |
| IMG-PNG-3 | `encode_png(r)` is none exactly when a side of `r` is 0, `r` is not well formed, or `w * h` is 2^32 or more. | Proved | pending | |
| IMG-PNG-4 | When `encode_png(r)` is some, its IHDR has bit depth 8 and interlace 0, and colour type 2 exactly when every sample of `r` has alpha 255, colour type 6 otherwise. | Proved | pending | |
| IMG-PNG-5 | `Crc.crc32(xs)` equals the bitwise ISO 3309 CRC-32 of `xs` for every byte list, and `decode_png` returns none for every input in which some chunk's stored CRC differs from the CRC-32 of its type and data. | Proved | pending | |
| IMG-PNG-6 | For every filter type 0 to 4 and every scanlines of a given width and bytes per pixel, `Png.unfilter` applied to the rows filtered by the PNG specification's filter function returns `Some` of the rows. | Proved | pending | |
| IMG-PNG-7 | For every byte list `xs` and every block size from 1 to 65535, `Inf.inflate` of the zlib stream of `xs` in stored blocks of that size is `Some(xs)`. | Proved | pending | |
| IMG-PNG-8 | `decode_png` returns none for every input whose IHDR has a bit depth other than 8, an interlace method other than 0, or a colour type outside 0, 2, 3, 4 and 6. | Proved | proved | LAWS.bend png_depth_refused; LAWS.bend png_interlace_refused; LAWS.bend png_colour_refused |
| IMG-PNG-9 | For each colour type, each decoded sample is the packing of the unfiltered bytes the PNG specification gives: gray `g` as `0xFFgggggg`, gray and alpha as `0xAAgggggg`, RGB as `0xFFrrggbb`, RGBA as `0xAArrggbb`, an index as its palette entry with alpha from tRNS or 255, and a colour matching a tRNS key with alpha 0. | Proved | pending | LAWS.bend png_px_grey; LAWS.bend png_px_grey_key; LAWS.bend png_px_ga; LAWS.bend png_px_rgb; LAWS.bend png_px_rgb_key; LAWS.bend png_px_rgba; LAWS.bend png_px_indexed; LAWS.bend png_samples_frame |
| IMG-PNG-10 | `decode_png` reads the fixed and dynamic Huffman DEFLATE streams other encoders (zlib, libpng) write. | Trusted | | |

### JPEG (IMG-JPG)

[ISO/IEC 10918-1](https://www.iso.org/standard/18902.html) / ITU-T T.81 baseline sequential, and JFIF (ITU-T T.871): `decode_jpeg` and `encode_jpeg`.

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| IMG-JPG-1 | `decode_jpeg` returns none for every input whose first frame header is not SOF0, and for every SOF0 frame whose sample precision is not 8. | Proved | pending | |
| IMG-JPG-2 | For a SOF0 frame whose components' sampling factors are each 1, 2 or 4, every sample `decode_jpeg` returns is the frame's sample for that point, each component's samples replicated over the pixels its sampling covers; for a factor outside 1, 2 and 4, `decode_jpeg` returns none. | Proved | pending | |
| IMG-JPG-3 | For every well-formed raster `r` with both sides nonzero, `decode_jpeg(encode_jpeg(r))` is a raster of `r`'s size whose every colour channel is within 3 of `r`'s, with alpha 255. | Proved | pending | |
| IMG-JPG-4 | `encode_jpeg(r)` is none exactly when `encode_png(r)` is none. | Proved | proved | LAWS.bend jpeg_png_refuse_alike |
| IMG-JPG-5 | When `encode_jpeg(r)` is some, it begins with SOI, APP0 with the JFIF identifier, DQT, SOF0 carrying `r`'s width and height, DHT and SOS, and ends with EOI. | Proved | pending | |
| IMG-JPG-6 | `Jpeg.rgb(y, cb, cr)` equals the T.871 YCbCr to RGB conversion, rounded to nearest and clamped to 0 to 255, for every `y`, `cb`, `cr` from 0 to 255. | Proved | pending | |
| IMG-JPG-7 | `decode_jpeg` reads baseline files other encoders (libjpeg, Pillow) write to within the IDCT accuracy of T.81 Annex A.3.3. | Trusted | | |

## Left to prove

| ID | Proved so far | Missing |
| :---- | :---- | :---- |
| IMG-PIX-1 | `Jpeg.rgb` and `Jpeg.gray`, the two functions JPEG decode packs samples with, give alpha 255 for every input (`jpeg_rgb_opaque`, `jpeg_gray_opaque`) | that every sample `decode_jpeg` returns is one of theirs; that `gray` repeats the level in R, G and B; that every sample `decode_png` returns is `0xAARRGGBB` (IMG-PNG-9) |
| IMG-PNG-9 | `Png.px.of`, the pixel stage, packs unfiltered bytes as the row says for every colour type: gray, gray with a tRNS key, gray and alpha, RGB, RGB with a tRNS key, RGBA (`png_px_grey`, `png_px_grey_key`, `png_px_ga`, `png_px_rgb`, `png_px_rgb_key`, `png_px_rgba`), and each index it decodes as its palette entry with alpha from tRNS or 255 (`png_px_indexed`); the decoder's last stage is `px.of` of `Png.unfilter`'s output with the width and height kept (`png_samples_frame`) | that the chunk walker hands that stage the IHDR's colour type, the PLTE and tRNS data, and the concatenated IDAT data inflated, so that the laws reach `decode_png` itself |

Every Proved row but IMG-JPG-4, IMG-PIX-2, IMG-RAS-5 and IMG-PNG-1 is pending; IMG-PIX-1 has the partial laws above. The rollout in [docs/rfc/ezimg-spec.md](docs/rfc/ezimg-spec.md) orders them: the behavior changes first (IMG-PIX-1 needed BC-1, which has landed; IMG-JPG-2 needed BC-2 and IMG-JPG-4 needed BC-3, which have landed), then refusals and frames (IMG-PNG-3, IMG-PNG-8, IMG-JPG-1, IMG-RAS-1, IMG-RAS-2), then content (IMG-PNG-5, IMG-PNG-7, IMG-PNG-6, IMG-PNG-9, IMG-PNG-4, IMG-RAS-3, IMG-RAS-4, and the headline IMG-PNG-2), and the JPEG content rows last (IMG-PIX-1, IMG-JPG-5, IMG-JPG-2, IMG-JPG-6, IMG-JPG-3).

No row is known to fail today. IMG-JPG-2 covers every sampling layout the frame parser accepts, which BC-2 made decode correctly (REVIEW-13).

## Trust boundary

These assumptions sit outside the proofs. They are the complete list of Trusted requirements, and a passing proof gate says nothing about them.

| ID | Assumption | Why it is trusted |
| :---- | :---- | :---- |
| IMG-TRUST-1 | The Bend checker (bend 2.0.25) accepts only proofs of true statements. | The gate is the checker; nothing checks it. |
| IMG-TRUST-2 | `ez test` reports a PROOF.bend as passing only when its first line is exactly `All terms check.` | The runner is the pinned ez's code, proved in ez, not here. |
| IMG-PNG-10 | decode_png reads other encoders' DEFLATE streams. | Needs a reference compressor for dynamic Huffman; exercised by the Pillow check, which is a test. |
| IMG-JPG-7 | decode_jpeg reads other encoders' baseline files within T.81 accuracy. | Needs the other encoder; exercised by the Pillow check. |
