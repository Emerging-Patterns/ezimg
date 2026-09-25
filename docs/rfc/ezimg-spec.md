# ezimg: what the library guarantees, and how we prove it

## Draft Status

Accepted. Written from `cbc4358` (release 0.2.1) and the evidence in
`docs/rfc/ezimg-law-inventory.md`, which this RFC cites by finding number
(F-1 to F-9). The maintainer accepted every recommendation below, and asked
that the package first move to the layout `ez init` lays out (`main.bend`
at the top, the modules under `src/`), which it has. Every requirement is
`pending` until its rollout phase.

The items are numbered because some depend on others. REVIEW-1 comes first
because the rows in the IMG-PIX, IMG-PNG and IMG-JPG groups are worded
against its answer.

- [x] <!-- REVIEW-1 (resolved): One sample format. PNG decode returns 0xAARRGGBB, JPEG colour decode 0x00RRGGBB, JPEG gray decode the Y value alone (F-1), so a JPEG saved as PNG is fully transparent. Options: (a) every decoder returns 0xAARRGGBB, JPEG samples with alpha 255 and gray repeated in R, G, B; (b) keep per-format layouts and document them; (c) a tagged sample type. Recommend (a): it is what the bench and Pillow already compare against, encode_png already reads it, and it makes IMG-PIX-1 one row instead of three. Behavior change for JPEG users (BC-1). Decided: accepted as recommended. -->
- [x] <!-- REVIEW-2 (resolved): 4:2:2 JPEG returns a wrong picture (F-2). Options: (a) fix the MCU layout for H=2, V=1 and keep 4:2:0 and 4:2:2; (b) refuse every sampling other than 1x1 and 2x2 luma. Recommend (a), since the decoder already carries sampling factors in Geom and 4:2:0 luma is right; the fix lands with IMG-JPG-2's law. Either way a sampling the decoder cannot place must be none, never a raster. Decided: accepted as recommended. -->
- [x] <!-- REVIEW-3 (resolved): encode_jpeg cannot refuse (F-4). Options: (a) return Maybe, none exactly when encode_png is none; (b) keep List and make a 0 by 0 or malformed raster encode something fixed. Recommend (a), matching encode_png. API break, so it ships in the same minor release as BC-1 (0.3.0). Decided: accepted as recommended. -->
- [x] <!-- REVIEW-4 (resolved): premultiply and straight are the identity (F-5). Options: (a) implement them on 0xAARRGGBB: each colour channel c becomes (c * a + 127) / 255, and straight divides back where a > 0; (b) delete them. Recommend (b): nothing in ezimg calls them, their only laws hold because they are the identity, and a correct pair is a feature to add later through spec-first-feature with its own row. Deleting is an API break, so it rides 0.3.0. Decided: accepted as recommended. -->
- [x] <!-- REVIEW-5 (resolved): No well-formedness invariant (F-3). Options: (a) state every raster row over well-formed rasters (sample count = w * h as a Nat) and add a Proved row that every helper maps well-formed inputs to well-formed outputs; (b) make raster return Maybe and hide the constructor. Recommend (a): no API change, and the law-side predicate is the invariant. Decided: accepted as recommended. -->
- [x] <!-- REVIEW-6 (resolved): Headline guarantee. Recommend IMG-PNG-2, "a well-formed raster with nonzero sides round-trips through encode_png and decode_png exactly". It is the one lossless promise the library makes, it is what users rely on when they save, and it forces IMG-PIX-1 and IMG-PNG-9 to be stated precisely. Decided: accepted as recommended. -->
- [x] <!-- REVIEW-7 (resolved): PNG strictness (F-6). decode_png rejects a bad CRC on any chunk, trailing IDAT bytes, a missing PLTE and an index past the palette; Pillow reads all four. Recommend keeping strict: the PNG spec allows it, it is easier to state exactly (IMG-PNG-5, IMG-PNG-8), and a lenient mode can be a later feature. No behavior change. Decided: accepted as recommended. -->
- [x] <!-- REVIEW-8 (resolved): PNG bit depths 1, 2, 4 and interlace (F-7). A 16-colour Pillow PNG is depth 4 and does not load. Recommend: out of scope for this rollout, stated as a refusal in IMG-PNG-8 now, and added later through spec-first-feature, which rewords IMG-PNG-8. Decided: accepted as recommended. -->
- [x] <!-- REVIEW-9 (resolved): The JPEG round-trip bound (IMG-JPG-3). The encoder uses quantisation step 1, so decode(encode(r)) is close but not exact: 3 levels per channel on the Pillow check, and (220, 40, 40) comes back as (220, 40, 41). Recommend stating the bound as 3 per channel, Proved and pending, proved last; the law needs error bounds on the fixed-point DCT, the most expensive proof here. The alternative, making it Trusted, would leave the JPEG group with no content guarantee. Decided: accepted as recommended. -->
- [x] <!-- REVIEW-10 (resolved): Retiring the 85 closed laws. Recommend deleting all 85 in one PR once SPEC.md lands (bolt's route), with the inventory's Points toward column as the map. None of them is a guarantee, 20 point toward nothing, and 5 pin the sample format REVIEW-1 changes. With them go Jenc.spots and any marker def only a closed law names (F-9). Decided: accepted as recommended. -->
- [x] <!-- REVIEW-11 (resolved): bolt pin. The flake pins bolt 995adc9 (v0.4.0), whose only law rules are coverage and a weak closed rule; trace needs v1.2.0 or newer. Recommend moving to v1.7.0 first, with laws at warn, and fixing its 987 style findings in that PR, so later PRs are not buried. closed and trace go to error in the PR that deletes the closed laws and lands SPEC.md. Decided: accepted as recommended. The move to the `main.bend` and `src/` layout came first, at the maintainer's request, and brought bench/ under the law rule; `bench/bolt.bend` sets the laws group to warn for the driver alone until the bolt move. -->
- [x] <!-- REVIEW-12 (resolved): fill and count wrap at w * h >= 2^32 (F-8). Recommend no change: state IMG-RAS-1 for w * h < 2^32, since fill cannot refuse without a Maybe and nobody allocates four billion samples in a List. Decided: accepted as recommended. -->

## Abstract

ezimg has 85 laws, and all 85 are closed: each checks one fixed input. The
proof gate passing today tells us that the checker computes those 85 values.
It does not tell us that any PNG round-trips, that a JPEG it cannot decode
is refused, or that samples from one decoder mean the same as samples from
another, and the last two are false today. We propose a SPEC.md with two
levels, Proved and Trusted, where each Proved row is backed by a quantified
law, and a rollout that replaces the closed laws with those laws.

## Glossary

| Term | Meaning |
| :---- | :---- |
| Raster | `Img.Raster{w, h, pixels}`: a width, a height and row-major `U32` samples |
| Well formed | a raster whose sample count equals `w * h` computed as a natural number (`wf`, a law-side def) |
| Sample | one `U32`. After REVIEW-1, packed `0xAARRGGBB` |
| Closed law | a law with no `for` or `exs` binder: a unit test the checker runs |
| Quantified law | a law with at least one binder: a statement about every value of its type |
| Proof gate | `ez test` over `PROOF.bend`, passing only on the exact first line `All terms check.` |
| Proved | a requirement backed by quantified laws tagged with its ID, passing the gate |
| Trusted | a requirement the gate cannot check, with a reason in the trust table |
| Pending | a Proved row whose laws have not all landed |
| Law side | a def in `LAWS.bend` that states the spec (a reference filter, a bitwise CRC) and is used only by laws |

## Background

ezimg is a pure Bend library: a raster type with pixel helpers, a PNG
decoder and encoder (with its own CRC-32 and inflate), and a baseline JPEG
decoder and encoder. It has no IO. Every decision is already a function of
its arguments, so unlike ez and bolt there is no World to define and no
planner to extract. Every behavior is in reach of a law as the code stands.

Today the laws are 85 closed equalities in `LAWS.bend`, each proved by
`{==}` in `PROOF.bend`. The README's Compliance section cites them as
conformance to ISO/IEC 15948 and ITU-T T.81. Each line of that section is
true of the fixture its law uses and of nothing else. The pinned bolt
(v0.4.0) calls the tree `clean` because it has no rule against closed laws,
and its coverage rule, at error, is satisfied by closed laws, which is why
each marker constant has a law of its own.

Beside the laws, the flake runs a Pillow comparison (`bench/compare.nix`)
of 36 cases. It is a useful host check and passes. It is not evidence for a
requirement, and it passes by working around the sample-format split
(F-1) in its own code.

Running the library on inputs a user would have found four bugs in an
afternoon (F-1 to F-4). None of the 85 laws could have caught any of them.

## Problem Statement

For each behavior of ezimg we want two questions answered by reading
SPEC.md: is it guaranteed, and if so is it proved or assumed?

Goals:

- Every requirement a user relies on is a SPEC.md row, Proved by a
  quantified law or Trusted with a reason.
- bolt's `trace` checks SPEC.md against the law tags, at error.
- The four confirmed bugs are fixed, each in the PR that proves the row it
  breaks.
- No closed laws remain.

Non-goals:

- Full codec conformance. Depths below 8, interlace, progressive and
  arithmetic JPEG stay refusals until someone adds them as features.
- Agreeing with Pillow pixel for pixel on 4:2:0 chroma, where T.81 leaves
  the upsampling filter to the decoder.
- Performance. The bench stays as it is.

## Proposal

### Two levels, and the positions carried over from ez and bolt

We adopt the positions both ez and bolt reached:

- **Exactly two levels.** A Proved row is backed by a quantified law tagged
  with its ID. A Trusted row names something the gate cannot see, with a
  reason. Pending is a status of a Proved row.
- **A closed law has no standing.** It is too weak to protect a behavior and
  too strong to let it change.
- **A test is never evidence for a requirement.** The Pillow check stays as
  a host check. Nothing in SPEC.md depends on it.
- **Laws only reach values.** ezimg already satisfies this, since it has no
  IO.
- **One headline guarantee**: IMG-PNG-2 (REVIEW-6).

### The proof gate

CI runs `ez test` through `mkProofs`, and the pinned ez already requires
the exact first line `All terms check.` (`ez/test.bend`, `report.proof`),
so the gate needs no change. `trace` joins it when bolt moves (REVIEW-11).

### Requirements

Each table is followed by the evidence and a law sketch. Names in sketches
are real defs where they exist. Law-side defs that do not exist yet are
marked *new*.

#### IMG-RAS: the raster

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| IMG-RAS-1 | `fill(w, h, c)` is well formed and every sample is `c`, for every `w`, `h` with `w * h < 2^32` and every `c`. | Proved | pending | |
| IMG-RAS-2 | For every well-formed raster `r` and every `x`, `y`: `get(r, x, y)` is `Some` of sample `y * w + x` when `x < w` and `y < h`, and none otherwise; `set(r, x, y, c)` changes exactly that sample to `c` when the point is inside and returns `r` unchanged otherwise. | Proved | pending | |
| IMG-RAS-3 | For every well-formed `r` and rectangle `(x, y, cw, ch)`, `crop` is well formed, its size is the rectangle's intersection with `r` (0 by 0 when that is empty), and its sample at `(i, j)` is `r`'s sample at `(x + i, y + j)`. | Proved | pending | |
| IMG-RAS-4 | For every well-formed `dst` and `src` and offset `(x, y)`, `blit(dst, src, x, y)` has `dst`'s size, takes `src`'s sample at every point of `dst` that `src` covers, and leaves every other sample of `dst` unchanged. | Proved | pending | |
| IMG-RAS-5 | For every raster `r` and function `f`, `map(f, r)` has `r`'s size and its sample `k` is `f` of `r`'s sample `k`. | Proved | pending | |

Evidence: inventory rows for `main.bend:28` to `246`. F-3 shows `blit`
shrinking a destination when the source is malformed, which is why every
row is stated over well-formed rasters (REVIEW-5). REVIEW-4 recommends
deleting `premultiply` and `straight`, so they have no row. IMG-RAS-6 is
reserved for them if the answer is to implement them.

Sketch, with `wf` and `at` *new* law-side defs:

```
# IMG-RAS-2
law set_frame:
  for +r: Img.Raster, +x: U32, +y: U32, +c: U32, +u: U32, +v: U32
  {implies(wf(r), implies(not(same(x, y, u, v)),
    Maybe.eq(Img.get(Img.set(r, x, y, c), u, v), Img.get(r, u, v)))) == True{} : Bool}
```

#### IMG-PIX: one sample format

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| IMG-PIX-1 | Every sample `decode_png` and `decode_jpeg` return is packed `0xAARRGGBB`. Every JPEG sample has alpha 255, and a gray JPEG sample carries its Y value in R, G and B. | Proved | pending | |
| IMG-PIX-2 | `encode_jpeg` reads only the low 24 bits of each sample: two rasters that differ only in alpha encode to the same bytes. | Proved | pending | |

Evidence: F-1, Confirmed through the bench driver. Depends on BC-1.
IMG-PIX-2 holds today by reading (`src/jpeg_enc.bend:802` and `1099` mask each
channel to 8 bits) and on one alpha-0 PNG run through the driver; it
is the frame law that makes IMG-PIX-1 safe for the encoder.

#### IMG-PNG: PNG

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| IMG-PNG-1 | `parse_signature(xs)` is `Some(png_sig())` exactly when `xs` begins with the eight bytes 137 80 78 71 13 10 26 10, and none otherwise. | Proved | pending | |
| IMG-PNG-2 | For every well-formed raster `r` with both sides nonzero, `decode_png(encode_png(r))` is `Some(r)`. | Proved | pending | |
| IMG-PNG-3 | `encode_png(r)` is none exactly when a side of `r` is 0, `r` is not well formed, or `w * h` is 2^32 or more. | Proved | pending | |
| IMG-PNG-4 | When `encode_png(r)` is some, its IHDR has bit depth 8 and interlace 0, and colour type 2 exactly when every sample of `r` has alpha 255, colour type 6 otherwise. | Proved | pending | |
| IMG-PNG-5 | `Crc.crc32(xs)` equals the bitwise ISO 3309 CRC-32 of `xs` for every byte list, and `decode_png` returns none for every input in which some chunk's stored CRC differs from the CRC-32 of its type and data. | Proved | pending | |
| IMG-PNG-6 | For every filter type 0 to 4 and every scanlines of a given width and bytes per pixel, `Png.unfilter` applied to the rows filtered by the PNG specification's filter function returns `Some` of the rows. | Proved | pending | |
| IMG-PNG-7 | For every byte list `xs` and every block size from 1 to 65535, `Inf.inflate` of the zlib stream of `xs` in stored blocks of that size is `Some(xs)`. | Proved | pending | |
| IMG-PNG-8 | `decode_png` returns none for every input whose IHDR has a bit depth other than 8, an interlace method other than 0, or a colour type outside 0, 2, 3, 4 and 6. | Proved | pending | |
| IMG-PNG-9 | For each colour type, each decoded sample is the packing of the unfiltered bytes the PNG specification gives: gray `g` as `0xFFgggggg`, gray and alpha as `0xAAgggggg`, RGB as `0xFFrrggbb`, RGBA as `0xAArrggbb`, an index as its palette entry with alpha from tRNS or 255, and a colour matching a tRNS key with alpha 0. | Proved | pending | |
| IMG-PNG-10 | `decode_png` reads the fixed and dynamic Huffman DEFLATE streams other encoders (zlib, libpng) write. | Trusted | | |

Evidence: all Confirmed except as noted. IMG-PNG-2 holds on every case run
(5 closed laws, 3 Pillow round trips) and is the headline (REVIEW-6).
IMG-PNG-3: a wrapped area (65536 by 65537 with 65536 samples) is refused
today, so the row states current behavior. IMG-PNG-5: every chunk CRC is
checked, IEND and IDAT included (REVIEW-7). IMG-PNG-8 states the current
scope (REVIEW-8). IMG-PNG-9 agreed with Pillow on every colour type
including tRNS.

IMG-PNG-6 and IMG-PNG-5 compare against a law-side reference taken from the
specification (the filter functions of PNG section 9.2, the bitwise CRC of
ISO 3309), so the law has content independent of the implementation.

IMG-PNG-10 is Trusted because stating it needs a reference DEFLATE
compressor for dynamic Huffman. IMG-PNG-7 proves the stored-block path,
which is all ezimg writes, so IMG-PNG-2 does not lean on IMG-PNG-10. Future
Steps narrows it with a law-side fixed-Huffman encoder.

Sketch of the headline:

```
# IMG-PNG-2
law png_round_trip:
  for +r: Img.Raster
  {implies(and(wf(r), nonzero(r)),
    Maybe.eq(Img.decode_png.back(Img.encode_png(r)), Some{r})) == True{} : Bool}
```

`decode_png.back` is the existing `enc.back` fixture renamed as a law-side
def.

#### IMG-JPG: JPEG

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| IMG-JPG-1 | `decode_jpeg` returns none for every input whose first frame header is not SOF0, and for every SOF0 frame whose sample precision is not 8. | Proved | pending | |
| IMG-JPG-2 | For a SOF0 frame, `decode_jpeg` returns none unless every chroma component has sampling factors 1 by 1 and luma has 1 by 1, 2 by 1 or 2 by 2; for those, the luma sample at every point is the one the frame codes for that point. | Proved | pending | |
| IMG-JPG-3 | For every well-formed raster `r` with both sides nonzero, `decode_jpeg(encode_jpeg(r))` is a raster of `r`'s size whose every colour channel is within 3 of `r`'s, with alpha 255. | Proved | pending | |
| IMG-JPG-4 | `encode_jpeg(r)` is none exactly when `encode_png(r)` is none. | Proved | pending | |
| IMG-JPG-5 | When `encode_jpeg(r)` is some, it begins with SOI, APP0 with the JFIF identifier, DQT, SOF0 carrying `r`'s width and height, DHT and SOS, and ends with EOI. | Proved | pending | |
| IMG-JPG-6 | `Jpeg.rgb(y, cb, cr)` equals the T.871 YCbCr to RGB conversion, rounded to nearest and clamped to 0 to 255, for every `y`, `cb`, `cr` from 0 to 255. | Proved | pending | |
| IMG-JPG-7 | `decode_jpeg` reads baseline files other encoders (libjpeg, Pillow) write to within the IDCT accuracy of T.81 Annex A.3.3. | Trusted | | |

Evidence: IMG-JPG-1 holds, Confirmed (SOF1, SOF2, SOF9, CMYK). IMG-JPG-2
fails for 4:2:2 (F-2) and depends on BC-2. IMG-JPG-3 holds within 3 on the
cases run (REVIEW-9). IMG-JPG-4 fails and depends on BC-3. IMG-JPG-5 holds
on the one case `jpeg_enc_markers` checks; the law replaces `Jenc.spots`
with a law-side marker walk. IMG-JPG-2's second clause is stated about
luma only, since chroma upsampling is the decoder's choice.

IMG-JPG-7 is Trusted for the same reason as IMG-PNG-10: a law sees only
ezimg, and a claim about files another program writes needs that program.

### Retiring closed laws

All 85 go in one PR (REVIEW-10), together with `Jenc.spots` and marker defs
no other code uses. The inventory keeps the map. Laws for pending rows are
written fresh, each tagged, in the phase that proves the row.

### Tagging and traceability

SPEC.md uses bolt's format: tables headed
`| ID | Requirement | Level | Status | Law |`, Law cells as
`LAWS.bend <law>` entries joined by `; `, a "Left to prove" section
for pending rows with partial laws, and the trust table. Each law carries
its row's ID on its own comment line directly above `law`. `trace` at error
checks both directions.

### Refactoring contract

A tagged law's statement changes only when its SPEC.md row changes. A
refactor of the codecs (most of ezimg's recent PRs are speed work) may
rewrite any proof and any untagged law, and is mergeable on the gate alone.
That is the practical payoff: the JPEG speed work so far was checked by
closed laws and the Pillow bench, and the next one will be checked by
IMG-PNG-2 and IMG-JPG-3.

### Trust boundary

| ID | Assumption | Why it is trusted |
| :---- | :---- | :---- |
| IMG-TRUST-1 | The Bend checker (bend 2.0.25) accepts only proofs of true statements. | The gate is the checker; nothing checks it. |
| IMG-TRUST-2 | `ez test` reports a PROOF.bend as passing only when its first line is exactly `All terms check.` | The runner is the pinned ez's code, proved in ez, not here. |
| IMG-PNG-10 | decode_png reads other encoders' DEFLATE streams. | Needs a reference compressor for dynamic Huffman; exercised by the Pillow check, which is a test. |
| IMG-JPG-7 | decode_jpeg reads other encoders' baseline files within T.81 accuracy. | Needs the other encoder; exercised by the Pillow check. |

### Decided behavior changes

Decided (REVIEW-1 to REVIEW-4). Each lands as its own PR, with master's
bench driver and the branch's run side by side on the cases that found the
bug.

| Change | Row | REVIEW | Breaks |
| :---- | :---- | :---- | :---- |
| BC-1: JPEG decode returns `0xFFrrggbb`, gray repeated in R, G, B | IMG-PIX-1 | 1 | code reading JPEG samples as `0x00rrggbb` or as a lone Y |
| BC-2: 4:2:2 luma placed correctly, and an unsupported sampling refused | IMG-JPG-2 | 2 | nothing that worked |
| BC-3: `encode_jpeg` returns `Maybe` | IMG-JPG-4 | 3 | every caller of `encode_jpeg` |
| BC-4: `premultiply` and `straight` removed | none | 4 | callers of two identity functions |

BC-1, BC-3 and BC-4 are API breaks and ship together as 0.3.0.

### How we will know it worked

- SPEC.md has no pending rows in IMG-RAS, IMG-PIX and IMG-PNG, and IMG-PNG-2
  is proved.
- `LAWS.bend` has no closed law, and bolt's `closed` and `trace` are
  at error on a bolt of v1.7.0 or newer.
- The four confirmed bugs are fixed, and the inventory's findings are
  folded into this RFC.
- A codec refactor can merge on the gate alone.

IMG-JPG-3 and IMG-JPG-6 may still be pending at that point. They are the
most expensive proofs, and the RFC is done without them as long as
"Left to prove" says what remains.

## Abandoned Ideas

**Keep the Pillow check as evidence.** It is the best check ezimg has of
agreement with other programs, and it did not catch F-1 to F-4. But
it covers 36 fixed files, and it passed through F-1 by converting samples in
its own code. It stays as a host check, and the two rows it exercises are
Trusted.

**Keep the closed laws as regression tests.** They pinned F-1's split
format in five places, so they would have made BC-1 look like a regression.
The ones that describe intended behavior return as quantified laws.

**Prove the decoders equal to a reference decoder written in the law file.**
A second decoder is a second implementation to get wrong, and proving two
large programs equal costs more than proving the properties users need. The
reference defs we do propose (bitwise CRC, the five filters, YCbCr
conversion) are each a few lines taken from the standard.

**Exhaustive laws over small domains.** IMG-JPG-6 ranges over 2^24 inputs,
and a closed law per input is a corpus snapshot. A structural proof over
the fixed-point formula is the route; if it is too slow, the row stays
pending rather than falling back to cases.

**A third level, "agrees with Pillow".** Tried and dropped in both ez and
bolt: it is a test under another name.

## Rollout

| Phase | What lands | Leaves true |
| :---- | :---- | :---- |
| 0 | This RFC and the inventory | nothing changes; the evidence is reviewable |
| layout | `main.bend` at the top and the modules under `src/`, as `ez init` lays them out; `bench/bolt.bend` keeps the driver's law rules at warn | the package has the shape its siblings have; no def changed |
| 1 | bolt v1.7.0 with laws at warn; its 987 style findings fixed | the tree lints clean on a bolt that has `trace` |
| 2 | SPEC.md with every row pending; all 85 closed laws, `spots` and law-only markers deleted; `closed` and `trace` at error; the README's Compliance section points at SPEC.md | the gate says exactly what is proved (nothing yet) |
| 3 | BC-1 to BC-4, one PR each | no confirmed bug remains |
| 4 | cheap rows: IMG-PNG-1, IMG-RAS-5, IMG-PIX-2, IMG-PNG-3, IMG-JPG-4, IMG-PNG-8, IMG-JPG-1, IMG-RAS-1, IMG-RAS-2 | refusals and frames proved |
| 5 | content rows: IMG-PNG-5, IMG-PNG-7, IMG-PNG-6, IMG-PNG-9, IMG-PNG-4, IMG-RAS-3, IMG-RAS-4, then IMG-PNG-2 | the headline proved |
| 6 | JPEG content: IMG-PIX-1, IMG-JPG-5, IMG-JPG-2, IMG-JPG-6, IMG-JPG-3 | the JPEG group proved or listed in Left to prove |

Each PR updates this RFC, SPEC.md and the inventory together.

## Risks

- **Proof effort.** The codecs are 6000 lines of List code. IMG-PNG-2 needs
  inflate of stored blocks, unfilter of filter None and the colour-type
  packing to compose, which is several lemmas deep. We order the rows so
  each lemma lands under a cheaper row first.
- **Checker time.** The 85 closed laws take 2 minutes. Quantified proofs
  over lists may take longer; we will split PROOF.bend per module if the
  gate passes ten minutes.
- **The spec encoding accidents.** F-6's strictness becomes IMG-PNG-5 and
  IMG-PNG-8. REVIEW-7 exists so that is a decision, not a default.
- **Pressure to reintroduce tests.** When a proof stalls, the row stays
  pending with a note; it does not gain a closed law.
- **The headline needs behavior changes around it.** It does not: IMG-PNG-2
  holds today by every measure, and BC-1 changes only JPEG.

## Future Steps

- A law-side fixed-Huffman DEFLATE encoder, so IMG-PNG-10 narrows to
  dynamic Huffman only.
- Cross-format rows once IMG-PIX-1 holds: a raster decoded from JPEG and
  saved as PNG round-trips exactly.
- PNG depths 1, 2, 4, 16 and interlace, and a correct premultiply, each as a
  feature through spec-first-feature.
- ezimg's SPEC.md as the model for sibling libraries with no IO.
