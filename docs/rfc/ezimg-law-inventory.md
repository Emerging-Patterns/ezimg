# ezimg law inventory

This is the evidence behind `docs/rfc/ezimg-spec.md`. It was read at
`cbc4358` (release 0.2.1), with bend 2.0.25 (the release the pinned
`bendlang/bend` flake input fetches). The proof gate was run as
`bend PROOF.bend`. The linter was the pinned bolt (`995adc9`,
v0.4.0) built from source, and bolt v1.7.0 for comparison. Probes ran
against the repo's own bench driver (`bench/main.bend`) built natively
from a fresh `git archive` of that commit, with Pillow 12.3.0 as the other
implementation.

Paths and line numbers below are for the `main.bend` and `src/` layout
`ez init` lays out, which the tree moved to after this reading; the code is
otherwise unchanged.

The laws in the inventory table below were deleted in phase 2. The table
stays as the map of what each pointed toward.

The inventory is a progress tracker. When the rollout ends, what still
matters goes into the RFC and this file is deleted.

## How to read the tables

| Column | Values |
| :---- | :---- |
| Kind | `Q` quantified (at least one `for` or `exs` binder), `C` closed |
| Proof | `{==}` when the whole proof is `{==}`, `struct` when it matches, recurses or rewrites |
| Claim | what the law states, in one line, about the input it is really about |
| Points toward | the draft requirement ID it supports (RFC), or `none (<reason>)` |

Reasons for `none`: `definitional` (restates a constant or an accessor),
`wiring` (restates how two defs compose), `wording` (the name claims more
than the statement), `helper pin` (one private helper on one input).

Verdicts on requirements: `holds`, `partly`, `fails`, `as trusted`, each
marked Confirmed (run against the binary) or by reading.

## The gate and the linter on ezimg itself

| Check | Result |
| :---- | :---- |
| `bend PROOF.bend` | first line `All terms check.`, exit 0, 2 min 11 s |
| pinned bolt (v0.4.0) over the tree | `clean`, exit 0, 4 s |
| bolt v1.7.0 over the same tree | 1161 errors: S004 810, S003 177, L001 89, L002 85 |
| `nix flake check` (CI) | runs `ez test` (proofs), bolt v0.4.0, and the Pillow check; not run here (no nix), its three parts were run by hand |
| Pillow correctness check (`bench/compare.nix`) | 36 of 36 cases pass |

The pinned bolt says `clean` because v0.4.0 has no strict closed-law rule:
its `closed` only rejects a law that is neither quantified nor an equality,
so all 85 closed equalities pass. Its `law` rule, at error, requires every
undotted def to be named by some law, and closed laws satisfy it. That rule
is why the tree has a law for each marker constant and why `jpeg_enc.bend`
exports `spots`, a def that only a law uses.

Under bolt v1.7.0 every one of the 85 laws is an L002 (no binder) and 89
defs are L001 (no quantified law reaches them). The 987 style findings are
parameter names of one letter and wrapped headers; none is a behavior
question.

There is no SPEC.md, so `trace` has nothing to check.

## Summary

| File | Laws | Quantified | Closed | Quantified by `{==}` | Points toward nothing |
| :---- | ---: | ---: | ---: | ---: | ---: |
| `LAWS.bend` | 85 | 0 | 85 | 0 | 20 |

What ezimg proves today: that the checker computes the same value as the
law on 85 fixed inputs. No law says anything about a second input. The
README's "Compliance" section lists these laws as conformance evidence, and
each item it names is true of exactly the fixture the law uses. Of the
three things a user would rely on (a PNG it writes reads back as the same
picture; a file it cannot decode is refused rather than misread; samples
from any decoder can go to any encoder), none is proved, and the second
and third are false today (F-1, F-2).

The 65 laws that point toward a requirement are useful as a map: they say
which behavior the author meant to cover. They are not evidence for it.

## Inventory: LAWS.bend

Fixtures (`swatch`, `fix.*`, `enc.*`, `flat.*`, `step.*`) are defs in the
law file, not laws, and are not listed.

| Line | Law | Kind | Proof | Claim | Points toward |
| ---: | :-- | :-: | :-: | :-- | :-- |
| 16 | `png_signature` | C | `{==}` | the signature def is the 8 listed bytes | IMG-PNG-1 (definitional) |
| 20 | `png_signature_len` | C | `{==}` | the signature def has length 8 | none (definitional) |
| 24 | `jpeg_marker` | C | `{==}` | the jpeg_soi def is FF D8 | none (definitional) |
| 28 | `width_reads` | C | `{==}` | width of one 2 by 3 raster is 2 | none (definitional) |
| 32 | `height_reads` | C | `{==}` | height of one 2 by 3 raster is 3 | none (definitional) |
| 36 | `pixels_read` | C | `{==}` | pixels of one raster are its six samples | none (definitional) |
| 40 | `size_pair` | C | `{==}` | size of one raster is (2, 3) | none (definitional) |
| 44 | `count_is_area` | C | `{==}` | count of one 2 by 3 raster is 6 | IMG-RAS-1 |
| 48 | `fill_solid` | C | `{==}` | fill(2, 2, 7) is four 7s | IMG-RAS-1 |
| 52 | `parse_png_sig` | C | `{==}` | the signature alone parses as the signature | IMG-PNG-1 |
| 56 | `parse_png_prefix` | C | `{==}` | the signature plus [1, 2] parses as the signature | IMG-PNG-1 |
| 61 | `parse_jpeg_not_png` | C | `{==}` | FF D8 does not parse as the signature | IMG-PNG-1 |
| 65 | `decode_png_none` | C | `{==}` | decode_png of the bare signature is none (the name says "PNG decode returns none", left from a stub) | none (wording) |
| 69 | `decode_jpeg_none` | C | `{==}` | decode_jpeg of FF D8 alone is none | IMG-JPG-1 |
| 73 | `get_inside` | C | `{==}` | get(swatch, 1, 1) is Some 6 | IMG-RAS-2 |
| 77 | `get_outside_x` | C | `{==}` | get(swatch, 2, 0) is none | IMG-RAS-2 |
| 81 | `get_outside_y` | C | `{==}` | get(swatch, 0, 3) is none | IMG-RAS-2 |
| 85 | `set_inside` | C | `{==}` | set(swatch, 1, 1, 1) replaces sample 3 | IMG-RAS-2 |
| 89 | `set_outside` | C | `{==}` | set(swatch, 4, 1, 1) is swatch | IMG-RAS-2 |
| 93 | `set_get` | C | `{==}` | get after set at (0, 2) on swatch reads 3 | IMG-RAS-2 |
| 97 | `crop_all` | C | `{==}` | crop of swatch to its full size is swatch | IMG-RAS-3 |
| 101 | `crop_rect` | C | `{==}` | one inner 1 by 2 crop of swatch | IMG-RAS-3 |
| 105 | `crop_clip` | C | `{==}` | one crop past the edge of swatch | IMG-RAS-3 |
| 109 | `crop_miss` | C | `{==}` | one crop starting at x = w is 0 by 0 | IMG-RAS-3 |
| 113 | `crop_zero` | C | `{==}` | one crop of height 0 is 0 by 0 | IMG-RAS-3 |
| 117 | `blit_at` | C | `{==}` | one 2 by 2 blit onto a 3 by 2 fill at (1, 0) | IMG-RAS-4 |
| 122 | `blit_clip` | C | `{==}` | one 2 by 2 blit onto a 3 by 2 fill at (2, 1) | IMG-RAS-4 |
| 127 | `blit_miss` | C | `{==}` | one 1 by 1 blit at (5, 5) leaves swatch | IMG-RAS-4 |
| 131 | `map_inc` | C | `{==}` | map of +1 over swatch | IMG-RAS-5 |
| 136 | `premultiply_opaque` | C | `{==}` | premultiply of swatch is swatch (holds because premultiply is the identity) | IMG-RAS-6 (claim false once alpha exists, see F-5) |
| 140 | `straight_opaque` | C | `{==}` | straight of swatch is swatch (identity) | IMG-RAS-6 (as above) |
| 144 | `straight_premultiply` | C | `{==}` | straight after premultiply of swatch is swatch (identity twice) | IMG-RAS-6 (as above) |
| 205 | `crc32_digits` | C | `{==}` | CRC-32 of "123456789" is the standard check value 0xCBF43926 | IMG-PNG-5 |
| 209 | `crc32_ihdr` | C | `{==}` | CRC-32 of one IHDR type and data | IMG-PNG-5 |
| 213 | `crc32_iend` | C | `{==}` | CRC-32 of "IEND" | IMG-PNG-5 |
| 217 | `parse_ihdr_fields` | C | `{==}` | one 13-byte IHDR parses to its seven fields | IMG-PNG-8 |
| 221 | `unfilter_none` | C | `{==}` | one 3-byte row, filter None | IMG-PNG-6 |
| 225 | `unfilter_sub` | C | `{==}` | one 3-byte row, filter Sub | IMG-PNG-6 |
| 229 | `unfilter_up` | C | `{==}` | one pair of 3-byte rows, filter Up | IMG-PNG-6 |
| 233 | `unfilter_average` | C | `{==}` | one 2-byte row, filter Average | IMG-PNG-6 |
| 237 | `unfilter_paeth` | C | `{==}` | one pair of 2-byte rows, filter Paeth | IMG-PNG-6 |
| 241 | `inflate_stored` | C | `{==}` | one stored zlib block inflates to its 4 bytes | IMG-PNG-7 |
| 246 | `decode_chunks` | C | `{==}` | Png.decode of the colour-type-2 fixture body | none (wiring: decode_png_rgb says the same through Img) |
| 250 | `decode_png_rgb` | C | `{==}` | the 1 by 1 colour-type-2 fixture decodes to 0xFFFF0000 | IMG-PNG-9 |
| 254 | `decode_png_rgba` | C | `{==}` | the 1 by 1 colour-type-6 fixture decodes to 0x80FF0000 | IMG-PNG-9 |
| 258 | `decode_png_grey` | C | `{==}` | the 1 by 1 colour-type-0 fixture decodes to 0xFF070707 | IMG-PNG-9 |
| 262 | `decode_png_ga` | C | `{==}` | the 1 by 1 colour-type-4 fixture decodes to 0xC8070707 | IMG-PNG-9 |
| 266 | `decode_png_idx` | C | `{==}` | the 1 by 1 colour-type-3 fixture decodes to 0xFFFF0000 | IMG-PNG-9 |
| 290 | `stored_block` | C | `{==}` | one 4-byte payload as one stored block | IMG-PNG-7 |
| 294 | `stored_split` | C | `{==}` | one 3-byte payload split at 2 bytes | IMG-PNG-7 |
| 298 | `encode_png_rgb` | C | `{==}` | opaque red 1 by 1 encodes to the colour-type-2 fixture | IMG-PNG-4 |
| 302 | `encode_png_rgba` | C | `{==}` | 0x80FF0000 1 by 1 encodes to the colour-type-6 fixture | IMG-PNG-4 |
| 306 | `encode_round_rgb` | C | `{==}` | round trip of one opaque 1 by 1 | IMG-PNG-2 |
| 311 | `encode_round_rgba` | C | `{==}` | round trip of one 1 by 1 with alpha | IMG-PNG-2 |
| 316 | `encode_round_quad` | C | `{==}` | round trip of one opaque 2 by 2 | IMG-PNG-2 |
| 320 | `encode_round_fade` | C | `{==}` | round trip of one 2 by 1 with mixed alpha | IMG-PNG-2 |
| 324 | `encode_round_stack` | C | `{==}` | round trip of one 1 by 2 with alpha | IMG-PNG-2 |
| 328 | `encode_png_empty` | C | `{==}` | 0 by 0 does not encode | IMG-PNG-3 |
| 332 | `encode_png_short` | C | `{==}` | 2 by 1 with one sample does not encode | IMG-PNG-3 |
| 336 | `encode_png_area` | C | `{==}` | 65536 by 65536 (area wraps to 0) does not encode | IMG-PNG-3 |
| 340 | `jpeg_soi_bytes` | C | `{==}` | Jpeg.soi equals Img.jpeg_soi | none (wiring) |
| 344 | `jpeg_eoi_bytes` | C | `{==}` | the eoi def is FF D9 | none (definitional) |
| 348 | `jpeg_app0_bytes` | C | `{==}` | the app0 def is FF E0 | none (definitional) |
| 352 | `jpeg_sof0_bytes` | C | `{==}` | the sof0 def is FF C0 | none (definitional) |
| 356 | `jpeg_sof2_bytes` | C | `{==}` | the sof2 def is FF C2 | none (definitional) |
| 360 | `jpeg_sof9_bytes` | C | `{==}` | the sof9 def is FF C9 | none (definitional) |
| 364 | `jpeg_dht_bytes` | C | `{==}` | the dht def is FF C4 | none (definitional) |
| 368 | `jpeg_dqt_bytes` | C | `{==}` | the dqt def is FF DB | none (definitional) |
| 372 | `jpeg_sos_bytes` | C | `{==}` | the sos def is FF DA | none (definitional) |
| 376 | `jpeg_jfif_id` | C | `{==}` | the jfif def is "JFIF\0" | none (definitional) |
| 380 | `jpeg_rgb_neutral` | C | `{==}` | rgb(128, 128, 128) is 0x808080 | IMG-JPG-6 |
| 384 | `jpeg_rgb_red` | C | `{==}` | rgb(0, 128, 255) is 0xB20000 | IMG-JPG-6 |
| 388 | `jpeg_gray_128` | C | `{==}` | one 1 by 1 gray fixture decodes to lone sample 128 | IMG-PIX-1 (pins the lone-Y format, see F-1) |
| 399 | `jpeg_gray_136` | C | `{==}` | one 1 by 1 gray fixture decodes to lone sample 136 | IMG-PIX-1 (as above) |
| 410 | `jpeg_color_neutral` | C | `{==}` | one 1 by 1 4:4:4 fixture decodes to 0x808080 | IMG-PIX-1 (pins alpha 0, see F-1) |
| 422 | `jpeg_color_red` | C | `{==}` | one 1 by 1 4:4:4 fixture decodes to 0xB20000 | IMG-PIX-1 (as above) |
| 434 | `jpeg_sof2_none` | C | `{==}` | one SOF2 file decodes as none | IMG-JPG-1 |
| 441 | `jpeg_sof9_none` | C | `{==}` | one SOF9 file decodes as none | IMG-JPG-1 |
| 447 | `jpeg_raster_gray` | C | `{==}` | decode_jpeg of the gray fixture is raster [128] | IMG-PIX-1 (as above) |
| 458 | `jpeg_enc_markers` | C | `{==}` | the markers of one 1 by 1 encode, in order | IMG-JPG-5 |
| 464 | `jpeg_enc_dc` | C | `{==}` | round trip of one 1 by 1 neutral solid | IMG-JPG-3 |
| 469 | `jpeg_enc_solid` | C | `{==}` | round trip of one 2 by 2 neutral solid | IMG-JPG-3 |
| 495 | `jpeg_fdct_flat` | C | `{==}` | the forward DCT of one flat block has no AC term | none (helper pin) |
| 500 | `jpeg_dct_step` | C | `{==}` | forward then inverse DCT of one step block | none (helper pin) |
| 505 | `jpeg_enc_step` | C | `{==}` | round trip of one 8 by 1 step | IMG-JPG-3 |

## Coverage by requirement

The draft rows are defined in the RFC. Count of closed laws pointing
toward each, and whether any law is quantified.

| Row | Closed laws | Quantified |
| :---- | ---: | ---: |
| IMG-RAS-1 well formed | 2 | 0 |
| IMG-RAS-2 get and set | 6 | 0 |
| IMG-RAS-3 crop | 5 | 0 |
| IMG-RAS-4 blit | 3 | 0 |
| IMG-RAS-5 map | 1 | 0 |
| IMG-RAS-6 premultiply | 3 | 0 |
| IMG-PIX-1 one sample format | 5 (all pin the current, split format) | 0 |
| IMG-PNG-1 signature | 4 | 0 |
| IMG-PNG-2 round trip | 5 | 0 |
| IMG-PNG-3 encode refusals | 3 | 0 |
| IMG-PNG-4 colour type choice | 2 | 0 |
| IMG-PNG-5 CRC | 3 | 0 |
| IMG-PNG-6 unfilter | 5 | 0 |
| IMG-PNG-7 zlib stored blocks | 3 | 0 |
| IMG-PNG-8 decode scope | 1 | 0 |
| IMG-PNG-9 colour types to samples | 5 | 0 |
| IMG-JPG-1 frame refusals | 3 | 0 |
| IMG-JPG-2 sampling | 0 | 0 |
| IMG-JPG-3 encode round trip | 3 | 0 |
| IMG-JPG-4 encode refusals | 0 | 0 |
| IMG-JPG-5 encode markers | 1 | 0 |
| IMG-JPG-6 colour conversion | 2 | 0 |

## Requirements against code

The README and the module headers are the only statement of intent, so
each claim they make is checked here.

| Claim (source) | Verdict | Evidence |
| :---- | :---- | :---- |
| "A picture is a Raster: a width, a height, and row-major samples" (README) | partly, Confirmed | `raster` (`main.bend:28`) accepts any list. A 2 by 2 raster with one sample is a value every helper accepts, and `blit` of a short source shrinks the destination (F-3). |
| "opaque U32 samples" (`main.bend:11`) | fails, Confirmed | PNG decode returns alpha in the top byte (`0x80FF0000` for colour type 6), and `encode_png` reads it. |
| `premultiply` and `straight` "leave the picture" because samples are opaque (`main.bend:248`) | fails, by reading | both are the identity (`main.bend:249`, `253`), while decoded samples carry alpha (F-5). |
| `fill` is width times height samples (`main.bend:62`) | partly, Confirmed | `U32` product wraps: `fill(65536, 65536, 0)` has count 0. |
| `get`, `set`, `crop`, `blit`, `map` (`main.bend:90` to `246`) | holds on well-formed rasters, by reading | index `y * w + x` stays below `w * h` once both are in range. |
| `decode_png` "returns a raster for an 8-bit PNG" (README) | holds, Confirmed | colour types 0, 2, 3, 4, 6 at depth 8, with tRNS, split IDAT, ancillary chunks, fixed and dynamic Huffman, up to 300 by 300, all equal Pillow's RGBA. |
| decode_png refuses what it cannot read | holds, Confirmed | depth 1, 2, 4, 16, interlace 1, bad CRC on any chunk, unknown critical chunk, trailing or missing IDAT bytes, index past the palette, missing PLTE: all none. Several of these Pillow accepts (F-6). |
| `encode_png` "none when a side is zero or the sample count is not the area" (`main.bend:286`) | holds, Confirmed | 0 by 0, short, long, and a wrapped area (65536 by 65537 with 65536 samples) are all none. |
| PNG encode then decode "returns the picture" (README) | holds on every case run, Confirmed | 5 closed laws and the bench's 3 Pillow round trips; not proved for any other picture. |
| `decode_jpeg`: "a baseline sequential JPEG, and none when the bytes are not one" (README) | fails, Confirmed | 4:2:2 returns a raster whose second luma block of each MCU is never painted: half the samples are `0x000000` (F-2). |
| JPEG decode samples are "packed RGB, the same layout decode returns" (`src/jpeg_enc.bend:3`) | partly, Confirmed | colour decode returns `0x00RRGGBB`; gray decode returns the lone Y value, not packed (F-1). |
| progressive SOF2 and arithmetic SOF9 "decode as none" (README) | holds, Confirmed | also SOF1 and CMYK are none. |
| `encode_jpeg` writes a baseline 4:4:4 JPEG (README) | partly, Confirmed | a 0 by 0 raster gives 4 bytes that nothing decodes; a 2 by 1 raster with one sample gives a valid 2 by 1 file with the missing sample made up (F-4). |
| JPEG encode then decode | holds within 3 levels per channel, Confirmed | Pillow check: PSNR 48 to 51 on 16 by 16 gradient and noise; exact on the solids in the laws. |

## What each entry point reads

ezimg is a library of pure functions. No def in `main.bend` or `src/` performs IO, so
every decision is already a value a law can reach: there is no World or
planner split to make. The only inputs are the arguments.

| Entry | Reads | Notes |
| :---- | :---- | :---- |
| `decode_png(bytes)` | bytes | fuel for the chunk walk is its own counter (`src/png.bend:1175`), not a silent stop |
| `encode_png(img)` | w, h, samples | |
| `decode_jpeg(bytes)` | bytes | |
| `encode_jpeg(img)` | w, h, samples | no quality input: every quantisation step is 1 (`src/jpeg_enc.bend:4`) |
| raster helpers | the raster, coordinates | |

`bench/main.bend` is the only IO, and it is a host driver, not part of the
package (`ez.toml` entry is `main.bend`).

## Findings

Recorded, not resolved. The RFC carries a REVIEW item for each one a
requirement depends on.

### Bugs

- **F-1 (fixed by BC-1). Decoders return three sample formats.** PNG decode returns
  `0xAARRGGBB`; JPEG colour decode returns `0x00RRGGBB`; JPEG gray decode
  returns the Y value alone. `encode_png` reads the top byte as alpha, so a
  JPEG decoded and saved as PNG is fully transparent, and a gray JPEG
  becomes transparent blue: `(220, 40, 41, 0)` and `(0, 0, 128, 0)` from
  Pillow's view of ezimg's PNG. Confirmed through the bench driver
  (`jpeg-dec` then `png-enc`). The bench's own compare script works around
  it (`compare.nix`, "Grayscale JPEG decode yields a lone Y sample").
- **F-2 (fixed by BC-2). 4:2:2 JPEG decodes to the wrong picture instead of none.** A
  24 by 16 and a 32 by 32 gradient at `subsampling=1` return `Some`, and
  exactly half the samples (x = 8 to 15 of every 16) are `0x000000`.
  4:2:0 luma is right; 4:2:0 colour differs from Pillow only where chroma
  changes (up to 53 levels at a red and blue edge, luma within 0.6), which
  is what box upsampling against libjpeg's smoothing looks like. T.81
  leaves the upsampling filter to the application. Confirmed.
- **F-3. No well-formedness invariant.** Every helper accepts a raster
  whose sample count is not `w * h`, and some turn it into a different
  wrong raster: `blit(fill(3, 1, 0), raster(2, 1, [7]), 0, 0)` has 2
  samples for a 3 by 1 picture. Confirmed.
- **F-4 (fixed by BC-3). `encode_jpeg` cannot refuse.** It returns bytes, not `Maybe`, so a
  0 by 0 raster gives a 4-byte file that ezimg's own decoder rejects, and a
  short sample list is padded silently. `encode_png` refuses both.
  Confirmed.

### Behavior that looks accidental

- **F-5 (resolved by BC-4, which removed both). `premultiply` and `straight` are the identity.** They were written
  when samples were opaque. They are now wrong for any sample with alpha
  below 255, and the three laws about them hold only because they are the
  identity.
- **F-6. PNG decode is stricter than Pillow.** It rejects a bad CRC on IEND
  or IDAT, trailing bytes after the last row, a missing
  PLTE, and an index past the palette, all of which Pillow reads. The PNG
  spec lets a decoder reject each of these. Recorded so the maintainer can
  choose; strictness is the easier behavior to prove.
- **F-7. PNG bit depths 1, 2 and 4 are refused.** Pillow writes a palette of
  16 colours or fewer at depth 4 by default, so a common Pillow PNG does
  not load. Confirmed with a 16-colour 17 by 13 image. The README says
  "8-bit", so this is documented scope, not a bug.
- **F-8. `fill` and `count` wrap** at `w * h >= 2^32`.
- **F-9. Test scaffolding in the package.** `Jenc.spots` exists only for
  `jpeg_enc_markers`; the marker defs in `src/jpeg.bend` are named only by
  their own closed laws. Both exist to satisfy bolt v0.4.0's coverage rule.

### Behavior the code guarantees that no statement mentions

- PNG encode is deterministic (same bytes for the same raster, Confirmed)
  and never compresses (stored blocks only).
- JPEG encode has no quality setting and writes quantisation steps of 1.
- `decode_png` refuses every chunk whose CRC disagrees, not only critical
  ones.
- A tRNS colour key yields alpha 0 on matching samples (colour types 0 and
  2), matching Pillow.

### Statements with no corresponding code

- "Full codec conformance is not claimed yet" (README) is accurate; the
  Compliance section above it reads as a list of conformance results but
  each line is one fixture.

## Progress

| Step | State | What landed |
| :---- | :---- | :---- |
| Audit and RFC | done | this inventory and `docs/rfc/ezimg-spec.md`; every REVIEW item accepted as recommended |
| Layout | done | `main.bend` and `src/`, `LAWS.bend` and `PROOF.bend` at the root; `bench/bolt.bend` sets the driver's law rules to warn; ez test, bolt, and the Pillow check pass on a fresh copy |
| Phase 1, bolt v1.7.0 | done | flake.lock pins bolt `38da7d9` (v1.7.0); `bolt.bend` keeps the law rules at warn and `unsafe` at error; 810 short parameter names renamed within their defs, 177 headers reflowed, 3 long lines wrapped; bolt v1.7.0 reports 0 errors and 174 law warnings (89 L001, 85 L002); ez test and the Pillow check pass, and the bench driver's output is byte-identical to master's on all 146 probe cases |
| Phase 2, SPEC.md and the closed laws | done | SPEC.md with 22 Proved rows, all pending, and 4 Trusted assumptions (IMG-PNG-10 and IMG-JPG-7 in the requirement tables, IMG-TRUST-1 and 2 in the trust boundary); all 85 closed laws and their fixtures deleted, with `Jenc.spots` and the marker defs only laws named (`app0`, `sof0`, `sof2`, `sof9`, `dht`, `dqt`, `sos`, `jfif`); `LAWS.bend` still imports every module so the gate type-checks them; `closed` and `trace` at error, `coverage` at warn (80 defs); the README's Compliance section points at SPEC.md |
| BC-1, one sample format | done | JPEG decode returns `0xAARRGGBB` with alpha 255, gray repeated in R, G and B, through `Jpeg.opaque`, `Jpeg.rgb` and `Jpeg.gray`; F-1 fixed. Partial laws `jpeg_rgb_opaque` and `jpeg_gray_opaque` tagged IMG-PIX-1, each caught its own planted mutant. Against the pre-change driver on the audit's probe files: PNG decode and both encoders byte-identical (116 outputs), 23 colour JPEG decodes gained alpha 255, 2 gray JPEG decodes repeat Y; the updated Pillow check fails 11 of 38 on the old driver and passes 38 of 38 on the new |
| BC-2, subsampled JPEG | done | root cause: a block's row in its MCU was `bi div vi`, T.81 A.2.3 says `bi div hi` (`src/jpeg.bend`, `decode.geom.go`). One-line fix. Against `djpeg -nosmooth` over 48 cjpeg files (8 luma layouts by 3 sizes by gradient and noise): every layout within 3 levels after, up to 244 off before except 1x1 and 2x2, which are byte-identical before and after; 4 files with chroma other than 1x1 within 3 after, up to 255 before. The Pillow check gains 4:2:2 and 4:2:0 luma cases: 4:2:2 fails on the old driver (luma off by 140) and passes on the new. IMG-JPG-2's wording is REVIEW-13, resolved as recommended: the row now covers every layout the parser accepts |
| BC-3, `encode_jpeg` refuses | done | `encode_jpeg` returns `Maybe`, branching on the same guard as `encode_png` (`Png.enc.good`); F-4 fixed. `jpeg_png_refuse_alike` proves IMG-JPG-4 for every raster, the first proved row; a weaker guard and an always-refusing branch each fail it |
| BC-4, `premultiply` and `straight` | done | both removed from `main.bend` (F-5): nothing called them, and each was the identity while samples carry alpha. IMG-RAS-6 stays reserved for a correct pair added later through spec-first-feature |
| Phase 4a, IMG-PIX-2 and IMG-RAS-5 | done | `encode_jpeg` clears alpha at entry (`Img.colours`, mask first) so `jpeg_alpha_blind` proves IMG-PIX-2 for every pair of rasters that differ only in alpha; `map_size` and `map_at` prove IMG-RAS-5 pointwise. Mutants: raw samples to the encoder (caught by `jpeg_alpha_blind` alone, `isolate_mutant.py`), alpha kept by `colour`, `map` swapping the sides, `map.go` skipping `f`: each fails its law. Cost: clearing alpha is one more list pass, about 40 ms per million samples; a 1024 by 1024 solid encode goes from about 70 to 110 ms, and a 512 by 512 noise encode is unchanged within noise (about 135 ms). Fusing the pass into the guard's length walk is a follow-up |
| U32 lemma module | done | `proof/u32.bend`: `false_true`, `and_left`, `and_right`, `u32_eq_refl`, and `ueq` (`U32.is_eq(a, b) == True` gives `a == b`, by `weq` over the word, after ezjson and bolt). A literal pattern such as `case 137 <> ...` compiles to a match on the 32 constant bits of the literal (`U32{WCon{...}}`), so no law over a symbolic byte gets past it; `parse_signature` now compares with `U32.is_eq` through `sig.match(want, bytes, ok)`, a tail-recursive walk that carries the answer so far, and `prefix.only` proves by induction on `want` that bytes `sig.match` accepts are `want` followed by the rest. With `sig_only`, IMG-PNG-1 is proved. Mutants (no byte comparison, a short list accepted, the wrong prefix) each fail a law |
| WP3, IMG-PNG-6 | done | `unfilter_filter` proves IMG-PNG-6: for every filter type (a law-side `Ft`, codes 0 to 4), width and height above 0, 1 to 4 bytes per pixel with `w * bpp` not wrapping, and rows of `w * bpp` bytes below 256, `unfilter` of the rows filtered by the law-side filter of PNG section 9.2 (`flt.rows`, Paeth in the specification's tie order a, b, c) is `Some` of the concatenated rows. Code changes, byte-identical on all 224 probe outputs: `uf.add` masks with the constant first; `uf.go` counts the bytes left in a row (`left`, a U32 counted down from `stride - 1`) instead of comparing `xx + 2` with `stride`, and `uf.back` drops its `xx < bpp` test, which the history's length already answers. Lemmas in `proof/wp3-filter.bend`: `sub_add_low` (the low k bits of `(a - b) mod 2^k + b` are those of `a`, by induction over the word with opposite carries), `byte_back`, `byte_low` (a U32 below 256 is its own low byte), `u32_dec` after ezjson, and the row and rows inductions `row_go` and `rows_go`. Eight code mutants each fail the gate: Average rounding up, Paeth preferring b on a tie with a, Paeth preferring c on a tie with b, Sub taking the byte above, `a` taken bpp + 1 bytes back, reconstruction without the mask, a row ending one byte early, and the row above not kept. The law-side filter agrees with a Python transcription of section 9.2 on 39 random images (1 to 5 pixels wide, 1 to 4 rows, 1 to 4 bytes per pixel, all five types). The gate takes about 5 s |
| WP1, IMG-PNG-5 | done | `crc32_bitwise`: `Crc.crc32` equals `crc.ref`, the bitwise CRC-32 written in `LAWS.bend` from ISO 3309 and PNG Annex D (reflected polynomial 0xEDB88320, preset and final xor all ones, eight shift-and-xor steps per byte; it gives 0xCBF43926 on "123456789"), for every U32 list. The code is per bit too, not table driven: `crc.bit` is handed the low bit of the register it is about to shift, and `bit_ref` shows that is the reference's step. Neither masks a byte to 8 bits, so the law holds for every U32 list and is ISO 3309 on bytes 0 to 255. `png_crc_refused`: after the signature, any framed chunks (a law-side `Chunk` whose length field counts its data), then a framed chunk whose stored CRC differs from `crc.ref` of its type and data, `decode_png` is none, whatever follows. The walker `png.go` matches its byte list before its state, so each step needs four known bytes; the data walk (`walk_dat`) case-splits the next three bytes in a helper, and `u32_pred`/`u32_one`/`u32_zero` tie the U32 count to the list length (`u32_dec` after ezjson). `crc.ref.step` takes the register apart before testing its low bit so the checker does not copy an unknown register into both branches at every step (without it the gate did not finish in 5 minutes). Lemmas in `proof/wp1-crc.bend`; no code change. Mutants: a wrong polynomial and seven steps per byte fail `bit_ref`; `png.judge` skipping the comparison fails `crc_bad`; a CRC over the data without the type fails `walk_chunk` |
| WP2, IMG-PNG-7 stored zlib blocks | done | `inflate_stored`: for every block size 1 to 65535 and every byte list (values 0 to 255) whose U32 count does not wrap, `Inf.inflate` of `zlib.stored(sz, xs)` (120 1, `Png.enc.blocks`, big-endian Adler-32) is `Some(xs)`; `inflate_enc_zlib`: the same for `Png.enc.zlib` at 65535. Lemmas in `proof/wp2-inflate.bend`: the bit reader folds a byte's eight bits back to its low byte (`rd8`, `rd16`), LEN and NLEN pass the check (`nlen_pass`), the data loop copies a block while its count runs to zero (`dl`, `blk`), `enc.feed`'s blocks in order (`fl`), the Adler bytes (`adler.ok`), and counting through `U32.to_nat` (`u32_dec`, `u_cmp` from ezjson; `up`, `ncnt`). Code, byte-identical: bit ops with the constant first (`bits.push`, `enc.byte`, `enc.hi`, `enc.be`) and the new bit or'd in first (`rd.raw`, `rd.adler`), so a symbolic byte's bits normalize. Mutants (NLEN written as LEN, a stored block dropping its last byte) fail the gate. The row is false as worded for lists of 2^32 bytes or more; rewording it to shorter lists makes it proved |
| WP5, PNG decode (IMG-PNG-8, IMG-PNG-9) | done, IMG-PNG-9 partial | IMG-PNG-8 proved over every file whose first chunk is a 13-byte IHDR, any width, height, other methods, CRC bytes and rest: `png_depth_refused`, `png_interlace_refused`, `png_colour_refused` walk the chunk reader to the IHDR's CRC and split on whether it holds; either way the chunk is refused, since `png.good` is false. IMG-PNG-9 proved at the pixel stage: one law per colour type over `Png.px.of` (gray, gray key, gray and alpha, RGB, RGB key, RGBA, indexed), each against a law-side packing (`spec.argb`), and a frame law for `png.samples`; lemmas in `proof/wp5-png-decode.bend` (Bool shapes, and ezjson's `u32_dec` for palette lookup by index). Code: the palette packs each entry with its tRNS alpha once (`pal.make` takes tRNS; `pal.tint` and `px.seta` removed), identical on byte input. Mutants: depth 16 accepted, interlace 1 accepted, colour type 5 accepted, RGB as `0x00rrggbb`, a wrong alpha shift in `px.pack`, gray blue 0, the key test inverted, gray and alpha opaque, RGBA with R and B swapped, the RGB key on two channels, tRNS ignored, the palette index off by one: each fails its law. Left: the chunk walker invariant that lifts IMG-PNG-9 to `decode_png` |
| WP7, JPEG structure | done; IMG-JPG-1 and IMG-JPG-5 proved after rewording, IMG-PIX-1 waits on IMG-PNG-9 | IMG-JPG-5: `encode.pick` now calls `encode.finish` once over the entropy-coded bytes `encode.arm` returns, so `jpeg_enc_layout` proves SOI, APP0 with `JFIF`, DQT, SOF0 with `r`'s size, two DHT, SOS, the entropy-coded bytes and EOI for sides up to 65535, and `jpeg_enc_ends` proves SOI first and EOI last for every raster; the row is false for a side above 65535 (a 65536 by 1 raster encodes to SOI EOI). IMG-PIX-1, JPEG side: the colour path maps `rgb` over the three emitted planes (`decode.rgbs`) instead of writing an Array, `decode.done` and `decode.done.nf` branch on `U32.is_eq`; `jpeg_decode_packed`, `jpeg_decode_opaque` and `jpeg_gray_level` (with `or_byte`, since `Bool.or(b, False)` does not reduce). IMG-JPG-1: `read.sof` and `read.app0` compare with `U32.is_eq`; `jpeg_refuse_sofn` and `jpeg_refuse_precision` state the refusal over SOI, well-formed non-frame segments, then the frame header, proved through a walk invariant (kind 0, phase Seek, Ent or Stop). Mutants (encoder without the second DHT, refused size without EOI, SOF1 read as SOF0, precision 12 accepted, gray without blue, colour samples without alpha) each fail a law. Probe outputs 224 identical, 0 differing; Pillow 40 of 40; JPEG decode time unchanged within noise |
| WP4, PNG encode (IMG-PNG-3, IMG-PNG-4) | done; IMG-PNG-3 proved after rewording | IMG-PNG-4 proved: `png_ihdr` shows every encoding opens with the signature and an IHDR chunk of the raster's width and height, depth 8, compression, filter and interlace 0, and colour type 2 exactly when every sample's top byte is 255 (`all_opaque`, a `List.all` of `U32.shrn(c, 24n) == 255`), 6 otherwise. Code: `enc.a` masks with the constant first, so the alpha test reduces once a sample's bits are taken apart; the two wide paths put the signature and IHDR in front of the reversed rest instead of at the bottom of the accumulator, so every path reads `cat(sig, cat(ihdr, rest))`. IMG-PNG-3 proved for every raster of fewer than 2^32 samples (`png_refuses`) and, for the accepting side, for every raster (`png_encodes`). Code: `enc.good` asks `enc.rows`, which takes w from the sample count h times with U32 subtraction (the samples as fuel), in place of the U32 product and the division bound; it answers the same on every input, including a wrapped area (65536 by 65537 with 65536 samples), checked old against new on 26 edge cases. The law states 2^32 as `below(32n, x)`, x halved 32 times is 0: the checker expands a Nat such as `Nat.pow(2n, 32n)` in unary and overflows. Lemmas in `proof/wp4-png-encode.bend` (Nat order and halves, `word_cmp_nat`, `word_sub`, `word_carry`, `u32_sub_nat`, `u32_inc_nat`). Mutants: the old U32 product compare with the area check dropped, the width test dropped (both caught by `good.nat` once the older `good.drop` is stubbed, `isolate_mutant.py`), colour type 6 for an opaque raster (`ct.same`), interlace 1 (`head.seal.at`): each fails the gate. Left: rasters of 2^32 or more samples, where the row is false as worded (the U32 sample count wraps) |
| WP6, the raster (IMG-RAS-1 to IMG-RAS-4) | done; IMG-RAS-2 to IMG-RAS-4 proved after rewording | U32 lemma library `proof/wp6-raster.bend`: `Word.cmp` is `Nat.cmp` of the words' numbers (`word_cmp_nat`, so `u32_lt`, `u32_le`, `u32_eq`); the adder, the subtractor and shift-and-add multiplication read as Nat when the result fits (`adc_nat`, `sbc_nat`, `mulgo_nat`), stated for U32 as `u32_add_below`, `u32_mul_below` (the exact result at most some U32's value) and `u32_sub_nat` (b <= a); `u32_index` (y * w + x does not wrap when x < w, y < h and w * h is some U32's value); Nat order, min, sub, take, drop and append lemmas. A closed 2^32 in a law is expanded in unary by the checker and overflows its stack, so the laws take w * h < 2^32 as a U32 `area` whose value is w * h. IMG-RAS-1: `fill_wf`, `fill_every`. IMG-RAS-2: `get_inside`, `get_inside_some`, `get_outside`, `set_inside`, `set_outside`. IMG-RAS-3: `crop_size`, `crop_wf`, `crop_at`, through a normal form of crop's case tree (`crop.nf_eq`) and the rows walk (`crop.rows_len`, `crop.rows_get`). IMG-RAS-4: `blit_size`, `blit_wf`, `blit_in`, `blit_out`, through the three parts of `blit.join` (`bj.top`, `bj.band`, `bj.bottom`) and one pasted row (`blit.row_left`, `row_mid`, `row_right`). No code change. Mutants: get with x and y swapped, set writing two samples, fill's count off by one and a wrong colour, get and set outside touching sample 0, crop's width off by one at the edge, crop's start and gap off by one, blit ignoring the offset (both axes, and x alone): each fails the gate in its law or its law's helper, and each makes a concrete instance of its law false. Left: IMG-RAS-2 to 4 for well-formed rasters with w * h of 2^32 or more, where they are false as worded (decision) |
| WP8, JPEG numeric rows | done; IMG-JPG-6 and the new IMG-JPG-8 Trusted, IMG-JPG-2 and IMG-JPG-3 pending after rewording | IMG-JPG-6: `Jpeg.rgb.bits` rounded G's two terms separately with 16-bit constants and differed from T.871 on 3,320,385 of the 2^24 inputs, by 1; it now computes each channel exactly in millionths (`rgb.ch`: one division, one rounding, then the clamp), and a Python copy of the new U32 arithmetic matches exact T.871 on all 2^24 inputs; 48 of 108 JPEG probe decodes change, each channel by at most 1. A proof would need U32 division and products near 10^9 in Nat terms, and a unary comparison of 255 * 10^6 against 4 * 10^9 already exhausts the checker's memory, so the row moved to Trusted (maintainer decision). IMG-JPG-3 was false (round-trip error up to 7, a 2 by 2 raster suffices): split into the structural row, pending, and the Trusted bound IMG-JPG-8 (within 8; 7 measured before and after the conversion change, libjpeg reaches 4 with the same settings). IMG-JPG-2 reworded (sample values left to IMG-JPG-7) and proved in parts: `jpeg_refuse_factor1`, `jpeg_refuse_factor3` (a SOF0 segment with a factor outside 1, 2 and 4, after any prefix that leaves the walk at a segment boundary, makes `decode_jpeg` none), `jpeg_comp_index` (a scan component finds its frame component), `jpeg_walk_unit`, `jpeg_walk_comp`, `jpeg_walk_mcu` (the MCU walk's three steps), `jpeg_mcu_grid` (T.81 A.2.3 grid for every factor pair), `jpeg_block_cover` (sample replication, 4 by 4 left out for gate time) and `jpeg_rgbs_at` (the colour pass is pointwise). Code: factor and count checks as `U32.is_eq` Bools, `Comps.ok`, `decode.read.sof.c`; `decode.index` without its dummy accumulator. Lemmas in `proof/wp8-jpeg-numeric.bend` (`walk_app`, `walk_stop`, `fac_elim`). Each new law caught a planted mutant |
| WP9, PNG round trip (IMG-PNG-2, IMG-PNG-9 lift) | done, both partial; IMG-PNG-2 false as worded past 2^32 scanline bytes (decision) | `png_walk` lifts the pixel stage to `decode_png`: a file of the signature, IHDR, PLTE and tRNS where allowed, any IDAT chunks and IEND, each chunk framed (`spec.chunk`: length, type, data, `crc.ref`) and shorter than 2^32 bytes, decodes to the raster `px.of` packs from `Png.unfilter` of the concatenated IDAT data inflated, with the IHDR colour type and the PLTE and tRNS data. `png_roundtrip_one` proves IMG-PNG-2 for every raster `png_ok` accepts whose scanlines fit one stored block (at most 65535 bytes): the encoder's file is `spec.png` with one IDAT (`seal.one.same`), then `png_walk`, `inflate_enc_zlib`, `unfilter_filter` with filter None, and `png_px_rgb` / `png_px_rgba` with the samples read back bit by bit (`be.back`: `be.u32` of `spec.be4`'s bytes is the word, 32 bits taken apart and 24 `Bool.or(b, False)` rewrites). Code, byte-identical on the probe outputs: `enc.r`, `enc.g`, `enc.b` mask with the constant first. Lemmas in `proof/wp9-png-roundtrip.bend`. Mutants (IDAT data appended in the wrong order, PLTE kept reversed, tRNS dropped at finish, IHDR width and height swapped, green written for blue, filter byte 1, alpha written 255): each fails the gate. Left: the wide paths (`enc.seal.wide` / `enc.pour`, `enc.wide.rgb` / `enc.rgb.go`), ancillary chunks for IMG-PNG-9, and the row's wording: `enc.nbytes` and the IDAT length are U32s, so a 32768 by 32768 raster with one non-opaque sample (2^30 samples) counts 32768 scanline bytes and takes the one-block path with a wrong LEN |
| WP10, JPEG placement and the round trip's structure (IMG-JPG-2, IMG-JPG-3) | done, both partial; IMG-JPG-2 false as worded above 2^31 points | IMG-JPG-2: `jpeg_block_cover_all` (every sample size, 4 by 4 included, onto any plane), `jpeg_mcu_grid_comp` (the A.2.3 grid for any scan component), `jpeg_refuse_factor1_any`, `jpeg_refuse_factor3_any` (fill bytes before the marker, a length longer than the components), `jpeg_refuse_count` (any other component count), `jpeg_points_at` (sample k of a plane's read-out is `Array.get` at k), `jpeg_walk_frame` (the decoder's own walk visits every MCU in raster order and each MCU's units in T.81 order, no counter wrapping) and `jpeg_walk_count` (the U32 block count `decode.nblocks` is that order's length when it fits). IMG-JPG-3: `jpeg_enc_stuffed`, `jpeg_unstuff` (the bit reader reads stuffed bytes back, eight bits at a time), `jpeg_enc_header_walk`, `jpeg_ent_walk`, `jpeg_round_trip_scan` (`decode_jpeg(encode_jpeg(r))` is the scan decode of the encoder's entropy-coded bytes in `r`'s frame), `jpeg_run_sized`, `jpeg_round_trip_sized` (none or a raster of `r`'s size). Code, byte-identical on all probe outputs and on crafted fill, marker and truncation cases: block painting written by rows, columns and pixels as the law-side cover is (`decode.splat`), which also drops `jpeg_block_cover`'s 1024-write normalisation from the gate; `decode.emit` reads a plane point by point in order (`decode.points`); `decode.nbits` and the entropy walk compare bytes with `U32.is_eq`, and `decode.nbits` ors the new bit in first; the encoder keeps raw bytes and stuffs once at the flush (`encode.stuff.all`), and dispatches on its tag with `U32.is_eq`; the block count is named (`decode.nblocks`). Lemmas in `proof/wp10-jpeg-finish.bend`, among them `dup` (two copies of an array, each equal to it: proofs are live, so an array cannot go to two lemmas) and the MCU-walk runs (`run.units` to `run.rows`). Mutants: a block column at `col * ph`, a scan component's factors taken from frame component `comp`, factor 3 accepted, a component count of 2 accepted, the read-out starting at point 1, an MCU row skipped, the block count summed from 1, a 255 not stuffed, the SOF width's low byte masked with 254, a stuffed 0 dropped by the walk, the entropy bytes not reversed, a gray picture's sides swapped, a colour picture's height as its width, a stuffed 255 read as 254: each fails its law or that law's lemma. Left: IMG-JPG-2's `Array.get` after `Array.set` lemmas, and the row is false for frames above 2^31 points (`decode.plane`'s depth wraps; decision); IMG-JPG-3's Huffman round trip, that `decode.run` of the encoder's bytes is not none. Gate about 4 m 20 s, main's 4 m 50 s |
| WP13, JPEG planes (IMG-JPG-2) | done; IMG-JPG-2 proved | `jpeg_get_set` (`Array.get` at an index finds what the last `Array.set` there wrote, in any array) and `jpeg_get_set_other` (on a perfect binary tree of 2^d leaves, d below 32, a set at one index below 2^d leaves what `Array.get` finds at another): the lemmas mirror an array as a data tree (`W13.Tr`, so a proof can use it twice), follow the index as `Array.swap.go` and `Array.get.go` walk it, and show the mask `i & (2^d - 1)` is `i` below 2^d (`mask_w`, the size of a perfect tree being the word of bit d, `size_bits`). `jpeg_plane_depth`: for 1 to 2^d points, d at most 31, `decode.depth` is below 32 and its 2^depth leaves are at least the points, the U32 shl wrap at exactly 2^31 points included (a bound on U32.log2 from below and above, `le1`, `le2`). `jpeg_paint_at`: painting a block onto such a plane leaves at pixel (x, y), point y * w + x, the sample whose pw by ph pixels take it in, the last in the block's order, else the old value (`jpg.block.at`). `jpeg_blocks_paint`: `decode.blocks` paints the k-th unit it decodes at `decode.geom` of the k-th place of its walk (`jpg.trace`) onto its component's plane. `jpeg_plane_at`: a plane after those units, read at (x, y), is `jpg.point`. `jpeg_place` composes them over `decode_jpeg`: for a frame of at most 2^31 points, pixel (x, y) of any raster it returns is gray of Y, or rgb of Y, Cb and Cr, each `jpg.point` over the decoded units from a zero plane; with `jpeg_walk_frame` (the walk is T.81 A.2.3's order), `jpeg_mcu_grid_comp` (each unit's A.2.3 grid place and sample size) and `jpeg_paint_at` (replication) that is the row. Where samples of different units would cover one pixel the later one shows; A.2.3's grid tiles the frame so none do, and that tiling arithmetic is not itself a law. Code, byte-identical on every probe: `decode.depth` tests zero with `U32.is_eq` instead of a literal pattern (`decode.depth.of`). Big Nat constants never appear in a checked type: the checker normalises `Nat.pow(2n, 32n)` even against itself, so the bound is `w * h <= 2^d, d <= 31`. Mutants: a pixel written one point on, the depth from nn - 1, Cb painted with component 2's units, a block of another component painted too, Cb and Cr swapped in the colour pass: each fails its law's proof; an `Array.set` one index on fails `jpeg_get_set` and one that also writes the next index fails `jpeg_get_set_other` on a concrete plane. Gate about 4 m 17 s, main's 4 m 25 s |
| Phase 4b, cheap rows | next | IMG-PNG-3, IMG-PNG-8, IMG-JPG-1, IMG-RAS-1, IMG-RAS-2; these need ordering and product lemmas on U32 (`is_lt`, `is_le`, `*` without wrap) next to `ueq` |
