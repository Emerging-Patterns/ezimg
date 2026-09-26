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
| IMG-RAS-1 | `fill(w, h, c)` is well formed and every sample is `c`, for every `w`, `h` with `w * h < 2^32` and every `c`. | Proved | proved | LAWS.bend fill_wf; LAWS.bend fill_every |
| IMG-RAS-2 | For every well-formed raster `r` with `w * h < 2^32` and every `x`, `y`: `get(r, x, y)` is `Some` of sample `y * w + x` when `x < w` and `y < h`, and none otherwise; `set(r, x, y, c)` changes exactly that sample to `c` when the point is inside and returns `r` unchanged otherwise. | Proved | proved | LAWS.bend get_inside; LAWS.bend get_inside_some; LAWS.bend get_outside; LAWS.bend set_inside; LAWS.bend set_outside |
| IMG-RAS-3 | For every well-formed `r` with `w * h < 2^32` and rectangle `(x, y, cw, ch)`, `crop` is well formed, its size is the rectangle's intersection with `r` (0 by 0 when that is empty), and its sample at `(i, j)` is `r`'s sample at `(x + i, y + j)`. | Proved | proved | LAWS.bend crop_size; LAWS.bend crop_wf; LAWS.bend crop_at |
| IMG-RAS-4 | For every well-formed `dst` with `w * h < 2^32`, well-formed `src` and offset `(x, y)`, `blit(dst, src, x, y)` has `dst`'s size, takes `src`'s sample at every point of `dst` that `src` covers, and leaves every other sample of `dst` unchanged. | Proved | proved | LAWS.bend blit_size; LAWS.bend blit_wf; LAWS.bend blit_in; LAWS.bend blit_out |
| IMG-RAS-5 | For every raster `r` and function `f`, `map(f, r)` has `r`'s size and its sample `k` is `f` of `r`'s sample `k`. | Proved | proved | LAWS.bend map_size; LAWS.bend map_at |

### One sample format (IMG-PIX)

What a sample means, for every decoder and encoder.

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| IMG-PIX-1 | Every sample `decode_png` and `decode_jpeg` return is packed `0xAARRGGBB`. Every JPEG sample has alpha 255, and a gray JPEG sample carries its Y value in R, G and B. | Proved | pending | LAWS.bend jpeg_rgb_opaque; LAWS.bend jpeg_gray_opaque; LAWS.bend jpeg_decode_packed; LAWS.bend jpeg_decode_opaque; LAWS.bend jpeg_gray_level |
| IMG-PIX-2 | `encode_jpeg` reads only the low 24 bits of each sample: two rasters that differ only in alpha encode to the same bytes. | Proved | proved | LAWS.bend jpeg_alpha_blind |

### PNG (IMG-PNG)

[ISO/IEC 15948](https://www.iso.org/standard/29581.html) and the [W3C PNG specification](https://www.w3.org/TR/png/): `decode_png`, `encode_png`, `parse_signature`, and the CRC-32 and inflate they rest on.

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| IMG-PNG-1 | `parse_signature(xs)` is `Some(png_sig())` exactly when `xs` begins with the eight bytes 137 80 78 71 13 10 26 10, and none otherwise. | Proved | proved | LAWS.bend sig_opens; LAWS.bend sig_only |
| IMG-PNG-2 | For every well-formed raster `r` with both sides nonzero, `decode_png(encode_png(r))` is `Some(r)`. | Proved | pending | LAWS.bend png_roundtrip_one |
| IMG-PNG-3 | For every raster `r` of fewer than 2^32 samples, `encode_png(r)` is none exactly when a side of `r` is 0, `r` is not well formed, or `w * h` is 2^32 or more. | Proved | proved | LAWS.bend png_encodes; LAWS.bend png_refuses |
| IMG-PNG-4 | When `encode_png(r)` is some, its IHDR has bit depth 8 and interlace 0, and colour type 2 exactly when every sample of `r` has alpha 255, colour type 6 otherwise. | Proved | proved | LAWS.bend png_ihdr |
| IMG-PNG-5 | `Crc.crc32(xs)` equals the bitwise ISO 3309 CRC-32 of `xs` for every byte list, and `decode_png` returns none for every input in which some chunk's stored CRC differs from the CRC-32 of its type and data. | Proved | proved | LAWS.bend crc32_bitwise; LAWS.bend png_crc_refused |
| IMG-PNG-6 | For every filter type 0 to 4 and every scanlines of a given width and bytes per pixel, `Png.unfilter` applied to the rows filtered by the PNG specification's filter function returns `Some` of the rows. | Proved | proved | LAWS.bend unfilter_filter |
| IMG-PNG-7 | For every byte list `xs` shorter than 2^32 bytes and every block size from 1 to 65535, `Inf.inflate` of the zlib stream of `xs` in stored blocks of that size is `Some(xs)`. | Proved | proved | LAWS.bend inflate_stored; LAWS.bend inflate_enc_zlib |
| IMG-PNG-8 | `decode_png` returns none for every input whose IHDR has a bit depth other than 8, an interlace method other than 0, or a colour type outside 0, 2, 3, 4 and 6. | Proved | proved | LAWS.bend png_depth_refused; LAWS.bend png_interlace_refused; LAWS.bend png_colour_refused |
| IMG-PNG-9 | For each colour type, each decoded sample is the packing of the unfiltered bytes the PNG specification gives: gray `g` as `0xFFgggggg`, gray and alpha as `0xAAgggggg`, RGB as `0xFFrrggbb`, RGBA as `0xAArrggbb`, an index as its palette entry with alpha from tRNS or 255, and a colour matching a tRNS key with alpha 0. | Proved | pending | LAWS.bend png_px_grey; LAWS.bend png_px_grey_key; LAWS.bend png_px_ga; LAWS.bend png_px_rgb; LAWS.bend png_px_rgb_key; LAWS.bend png_px_rgba; LAWS.bend png_px_indexed; LAWS.bend png_samples_frame; LAWS.bend png_walk |
| IMG-PNG-10 | `decode_png` reads the fixed and dynamic Huffman DEFLATE streams other encoders (zlib, libpng) write. | Trusted | | |

### JPEG (IMG-JPG)

[ISO/IEC 10918-1](https://www.iso.org/standard/18902.html) / ITU-T T.81 baseline sequential, and JFIF (ITU-T T.871): `decode_jpeg` and `encode_jpeg`.

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| IMG-JPG-1 | `decode_jpeg` returns none for every input that opens with SOI, then segments other than frame headers (DHT, DQT, SOS, DRI, COM, APP0 to APP15) each with a length field that fits its body, then a frame header other than SOF0 or an SOF0 segment whose sample precision is not 8, whatever follows. | Proved | proved | LAWS.bend jpeg_refuse_sofn; LAWS.bend jpeg_refuse_precision |
| IMG-JPG-2 | For a SOF0 frame of at most 2^31 points whose components' sampling factors are each 1, 2 or 4, `decode_jpeg` places each component's samples in the order T.81 A.2.3 gives and replicates each sample over the pixels its sampling covers; for a factor outside 1, 2 and 4, `decode_jpeg` returns none. The sample values themselves are IMG-JPG-7's. | Proved | pending | LAWS.bend jpeg_refuse_factor1; LAWS.bend jpeg_refuse_factor3; LAWS.bend jpeg_refuse_factor1_any; LAWS.bend jpeg_refuse_factor3_any; LAWS.bend jpeg_refuse_count; LAWS.bend jpeg_comp_index; LAWS.bend jpeg_walk_unit; LAWS.bend jpeg_walk_comp; LAWS.bend jpeg_walk_mcu; LAWS.bend jpeg_walk_frame; LAWS.bend jpeg_walk_count; LAWS.bend jpeg_mcu_grid; LAWS.bend jpeg_mcu_grid_comp; LAWS.bend jpeg_block_cover; LAWS.bend jpeg_block_cover_all; LAWS.bend jpeg_points_at; LAWS.bend jpeg_rgbs_at |
| IMG-JPG-3 | For every well-formed raster `r` with both sides nonzero and at most 65535 and at most 2^31 samples, `decode_jpeg(encode_jpeg(r))` is some raster of `r`'s size with alpha 255. | Proved | pending | LAWS.bend jpeg_enc_stuffed; LAWS.bend jpeg_unstuff; LAWS.bend jpeg_enc_header_walk; LAWS.bend jpeg_ent_walk; LAWS.bend jpeg_round_trip_scan; LAWS.bend jpeg_run_sized; LAWS.bend jpeg_round_trip_sized; LAWS.bend jpeg_bits_round_trip; LAWS.bend jpeg_huff_dc; LAWS.bend jpeg_huff_ac |
| IMG-JPG-4 | `encode_jpeg(r)` is none exactly when `encode_png(r)` is none. | Proved | proved | LAWS.bend jpeg_png_refuse_alike |
| IMG-JPG-5 | When `encode_jpeg(r)` is some, it begins with SOI and ends with EOI; when both sides of `r` are at most 65535 it is SOI, APP0 with the JFIF identifier, DQT, SOF0 carrying `r`'s width and height, two DHT, SOS, the entropy-coded data and EOI. | Proved | proved | LAWS.bend jpeg_enc_layout; LAWS.bend jpeg_enc_ends |
| IMG-JPG-6 | `Jpeg.rgb(y, cb, cr)` equals the T.871 YCbCr to RGB conversion, rounded to nearest and clamped to 0 to 255, for every `y`, `cb`, `cr` from 0 to 255. | Trusted | | |
| IMG-JPG-7 | `decode_jpeg` reads baseline files other encoders (libjpeg, Pillow) write to within the IDCT accuracy of T.81 Annex A.3.3. | Trusted | | |
| IMG-JPG-8 | For every well-formed raster `r` with both sides nonzero and at most 65535 and at most 2^31 samples, every colour channel of `decode_jpeg(encode_jpeg(r))` is within 8 of `r`'s. | Trusted | | |

## Left to prove

| ID | Proved so far | Missing |
| :---- | :---- | :---- |
| IMG-JPG-2 | Refusal: a SOF0 segment with a factor outside 1, 2 and 4 makes `decode_jpeg` none, for one component or three, whatever precedes and follows it (`jpeg_refuse_factor1`, `jpeg_refuse_factor3`), and also after fill bytes before its marker and with a length field longer than its components (`jpeg_refuse_factor1_any`, `jpeg_refuse_factor3_any`); a SOF0 segment of any other component count is none whatever its factors (`jpeg_refuse_count`). Placement: a scan component takes the factors of the frame component whose identifier it names, the first with that identifier (`jpeg_comp_index`); the MCU walk goes from data unit `bi` to `bi + 1`, then to the next scan component, then to the next MCU (`jpeg_walk_unit`, `jpeg_walk_comp`, `jpeg_walk_mcu`); from the scan's first block the decoder's own walk visits the frame's MCUs in raster order, `ceil(w / 8 hmax)` to a row, and in each MCU the scan's components and their `hi * vi` units in T.81 order, the unit, component and column counters never wrapping (`jpeg_walk_frame`), and the U32 block count the decoder runs, `decode.nblocks`, is that order's length over `ceil(h / 8 vmax)` MCU rows when the scan carries the frame's data units and the count fits a U32 (`jpeg_walk_count`); the `hi * vi` units of any scan component sit in T.81 A.2.3's grid, `hi` to a row, each sample covering `hmax / hi` by `vmax / vi` pixels (`jpeg_mcu_grid`, `jpeg_mcu_grid_comp`); painting a block writes sample `k` over exactly the `pw` by `ph` pixels at `(ox + (k mod 8) * pw, oy + (k div 8) * ph)` inside the frame, for every sample size, 4 by 4 included, and onto every plane, one earlier blocks painted included (`jpeg_block_cover`, `jpeg_block_cover_all`); the decoder reads a plane out point by point, sample `k` being the value `Array.get` finds at index `k` (`jpeg_points_at`). Colour: sample `k` of the colour pass is `Jpeg.rgb` of point `k`'s Y, Cb and Cr (`jpeg_rgbs_at`) | that `Array.get` at an index finds the value the last `Array.set` at that index wrote, and a set at another index leaves it (the planes are perfect binary trees of `2^d` leaves, and the lemmas must follow the masked index down the tree), which joins the painting laws to `jpeg_points_at`. The row is worded for frames of at most 2^31 points: above that `decode.plane`'s depth, taken from `U32.shl(nn)`, wraps and points alias |
| IMG-JPG-3 | Alpha 255 holds for every sample `decode_jpeg` returns (`jpeg_decode_opaque`, IMG-PIX-1), and `encode_jpeg`'s bytes have the layout IMG-JPG-5 proves. The encoder's entropy-coded bytes have every 255 followed by a 0, for every size and samples (`jpeg_enc_stuffed`), and the decoder's bit reader, reading eight bits at a time from the encoder's stuffing of any bytes, reads the bytes back with the stuffed zeros dropped (`jpeg_unstuff`); the decoder's marker walk over the encoder's header reaches the entropy-coded data with the frame carrying the encoder's width and height, its scan and its tables, a baseline frame read and nothing refused (`jpeg_enc_header_walk`); inside the data the walk keeps every byte of stuffed data and stops at EOI (`jpeg_ent_walk`); so for every well-formed raster with both sides from 1 to 65535, `decode_jpeg(encode_jpeg(r))` is the decoder's scan decode, `decode.run`, of the encoder's own entropy-coded bytes in the frame of `r`'s width and height (`jpeg_round_trip_scan`); that scan decode is none or a picture of its frame's width and height, whatever the bytes (`jpeg_run_sized`); so `decode_jpeg(encode_jpeg(r))` is none or a raster of `r`'s size (`jpeg_round_trip_sized`) | that `decode.run` on the encoder's entropy-coded bytes is not none: that every Huffman lookup finds its symbol and every block ends by 64 coefficients, which is the bit writer (`encode.bits`, `encode.pack`, the pad with 1 bits: that the bytes it writes carry the codes' bits in order) against the bit reader reading codes of 1 to 16 bits across byte boundaries (the byte-aligned case is `jpeg_unstuff`), the Annex K tables `encode.huff` builds against the ones `decode.canon` builds and `decode.look` searches, and the encoder's three paths (neutral, solid, `encode.go`) each writing `ceil(w / 8) * ceil(h / 8)` MCUs of three blocks, each a DC code and magnitude, AC run and size codes and magnitudes, and EOB |
| IMG-PIX-1 | The JPEG side. `Jpeg.rgb` and `Jpeg.gray` give alpha 255 for every input (`jpeg_rgb_opaque`, `jpeg_gray_opaque`); every sample `decode_jpeg` returns is packed by `Jpeg.gray`, or every one by `Jpeg.rgb` (`jpeg_decode_packed`); every sample it returns has alpha 255 (`jpeg_decode_opaque`); a gray sample carries its level's low byte in R, G and B (`jpeg_gray_level`) | that every sample `decode_png` returns is `0xAARRGGBB`: `png_walk` (IMG-PNG-9) reaches `decode_png` for files in the standard chunk order, not yet for files with ancillary chunks. `jpeg_decode_packed` does not say that the gray packing is the one chosen for a one-component frame |
| IMG-PNG-2 | the one-block encoding: every raster `png_ok` accepts (both sides nonzero, `w * h` samples, `w * h` below 2^32) whose scanlines, `h * (1 + w * c)` bytes for c channels (3 when every sample is opaque, 4 otherwise), are at most 65535 decodes from its PNG to itself (`png_roundtrip_one`), through `png_walk`, `inflate_enc_zlib`, `unfilter_filter` with filter None, and `png_px_rgb` / `png_px_rgba` | the two wide paths `encode_png` takes past 65535 scanline bytes: `enc.seal.wide` (colour type 6, `enc.pour`) and `enc.wide.rgb` (colour type 2, `enc.rgb.go`) must be shown to write `zlib.stored(65535, raw)` with the IDAT CRC. And the row is false as worded, even with the approved bound of fewer than 2^32 samples: the scanline count `enc.nbytes` and the IDAT length are U32s, so a raster of 2^32 scanline bytes or more encodes to a file that does not decode (a decision for the maintainer) |
| IMG-PNG-9 | `Png.px.of`, the pixel stage, packs unfiltered bytes as the row says for every colour type: gray, gray with a tRNS key, gray and alpha, RGB, RGB with a tRNS key, RGBA (`png_px_grey`, `png_px_grey_key`, `png_px_ga`, `png_px_rgb`, `png_px_rgb_key`, `png_px_rgba`), and each index it decodes as its palette entry with alpha from tRNS or 255 (`png_px_indexed`); the decoder's last stage is `px.of` of `Png.unfilter`'s output with the width and height kept (`png_samples_frame`); and the walker lift, `png_walk`: a file of the signature, IHDR (any nonzero width and height, bit depth 8, a colour type the row names, methods 0), PLTE and tRNS where section 11 allows them, any IDAT chunks and IEND, each chunk framed with its CRC-32 and shorter than 2^32 bytes, decodes to the raster `px.of` packs, for the IHDR colour type and the PLTE and tRNS data, from `Png.unfilter` of the concatenated IDAT data inflated | files whose chunks come in another order the decoder accepts: ancillary chunks (which the walker skips, closing the IDAT run) between the critical ones |

Every Proved row but IMG-JPG-1, IMG-JPG-4, IMG-JPG-5, IMG-PIX-2, IMG-RAS-1, IMG-RAS-2, IMG-RAS-3, IMG-RAS-4, IMG-RAS-5, IMG-PNG-1, IMG-PNG-3, IMG-PNG-4, IMG-PNG-5, IMG-PNG-6, IMG-PNG-7 and IMG-PNG-8 is pending; IMG-PIX-1, IMG-PNG-2, IMG-PNG-9, IMG-JPG-2 and IMG-JPG-3 have the partial laws above. The rollout in [docs/rfc/ezimg-spec.md](docs/rfc/ezimg-spec.md) orders them: the behavior changes first (IMG-PIX-1 needed BC-1, which has landed; IMG-JPG-2 needed BC-2 and IMG-JPG-4 needed BC-3, which have landed), then refusals and frames (IMG-PNG-3, IMG-PNG-8, IMG-JPG-1, IMG-RAS-1, IMG-RAS-2), then content (IMG-PNG-5, IMG-PNG-7, IMG-PNG-6, IMG-PNG-9, IMG-PNG-4, IMG-RAS-3, IMG-RAS-4, and the headline IMG-PNG-2), and the JPEG content rows last (IMG-PIX-1, IMG-JPG-5, IMG-JPG-2, IMG-JPG-6, IMG-JPG-3).

IMG-PNG-2 is false as worded for rasters of 2^32 scanline bytes or more, which fewer than 2^32 samples do not rule out (above); no other row is known to be false. IMG-JPG-2 covers every sampling layout the frame parser accepts, which BC-2 made decode correctly (REVIEW-13).

## Trust boundary

These assumptions sit outside the proofs. They are the complete list of Trusted requirements, and a passing proof gate says nothing about them.

| ID | Assumption | Why it is trusted |
| :---- | :---- | :---- |
| IMG-TRUST-1 | The Bend checker (bend 2.0.25) accepts only proofs of true statements. | The gate is the checker; nothing checks it. |
| IMG-TRUST-2 | `ez test` reports a PROOF.bend as passing only when its first line is exactly `All terms check.` | The runner is the pinned ez's code, proved in ez, not here. |
| IMG-PNG-10 | decode_png reads other encoders' DEFLATE streams. | Needs a reference compressor for dynamic Huffman; exercised by the Pillow check, which is a test. |
| IMG-JPG-6 | Jpeg.rgb is T.871 rounded and clamped for every input 0 to 255. | Checked outside the gate: a Python copy of `Jpeg.rgb.bits`'s U32 arithmetic, compared with T.871 computed in exact rationals over all 2^24 inputs, differs on none. A proof in the gate needs U32 division and products near 10^9, which the Nat lemmas reach only through unary numerals the checker cannot hold in memory. |
| IMG-JPG-7 | decode_jpeg reads other encoders' baseline files within T.81 accuracy. | Needs the other encoder; exercised by the Pillow check. |
| IMG-JPG-8 | The JPEG round trip keeps every colour channel within 8. | Measured, not proved: the largest error over about 15,000 rasters (random, gradients, saturated colours, checkerboards, sizes 1 to 64) is 7; libjpeg with the same settings (all-ones quantisation, 4:4:4) reaches 4. A proof needs error bounds on the fixed-point DCT and IDCT. |
