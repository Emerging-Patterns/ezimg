# A faulty tRNS is ignored, as if the file had none. tRNS is ancillary, and
# PNG section 13.1 lets a decoder ignore a faulty ancillary chunk; libpng
# ignores tRNS with a benign error. A gray tRNS that is not two bytes and an
# RGB tRNS that is not six give no key, at every bit depth; gray with alpha
# and RGBA ignore any tRNS (png_px_ga and png_px_rgba of
# laws/PngSamplesFollowColourType.bend); a palette tRNS with more entries than
# PLTE gives no alphas (png_px_indexed there). The chunk walker takes a second
# tRNS, one after IDAT, one for gray with alpha or RGBA, and a palette tRNS
# before PLTE as it takes an unknown ancillary chunk: it closes the IDAT run
# and keeps the state. A file with tRNS chunks after its IDAT chunks decodes
# as the file without them (png_walk_anc of laws/PngAncillaryChunksIgnored.bend).
# Until 2026-11 each of these refused the image; ignoring them is a
# deliberate change.
import Base
import ../src/png.bend as Png
import ./PngSamplesFollowColourType.bend as L1

# a tRNS the walker takes (PNG section 11.3.2.1): for gray or RGB, or for
# indexed colour once PLTE has come
def spec.trns.allowed(+cc: U32, saw_plte: Bool) -> Bool:
  Bool.or(Bool.or(U32.is_eq(cc, 0), U32.is_eq(cc, 2)), Bool.and(U32.is_eq(cc, 3), saw_plte))

# LAW: colour type 0: a tRNS of other than two bytes gives no key, each gray byte decoding to 0xFFgggggg
law png_trns_grey_len:
  for +xs: List<&2, U32>
  for +plte: List<&2, U32>
  for +trns: List<&2, U32>
  for h_len: {Nat.is_eq(List.length(&2, U32, trns), 2n) == False{} : Bool}
  {Png.px.of(0, xs, plte, trns) == Some{L1.spec.grey(xs)} : Maybe<&2, List<&2, U32>>}

# LAW: colour type 2: a tRNS of other than six bytes gives no key, each triple decoding to 0xFFrrggbb
law png_trns_rgb_len:
  for +xs: List<&2, U32>
  for +plte: List<&2, U32>
  for +trns: List<&2, U32>
  for h_len: {Nat.is_eq(List.length(&2, U32, trns), 6n) == False{} : Bool}
  {Png.px.of(2, xs, plte, trns) == L1.spec.rgb(xs) : Maybe<&2, List<&2, U32>>}

# LAW: gray at any bit depth: a tRNS of other than two bytes decodes as no tRNS
law png_trns_grey_deep:
  for +dd: U32
  for +xs: List<&2, U32>
  for +plte: List<&2, U32>
  for +trns: List<&2, U32>
  for h_len: {Nat.is_eq(List.length(&2, U32, trns), 2n) == False{} : Bool}
  {Png.px.deep(0, dd, xs, plte, trns) == Png.px.deep(0, dd, xs, plte, []) : Maybe<&2, List<&2, U32>>}

# LAW: RGB at either of its bit depths, 8 and 16: a tRNS of other than six bytes decodes as no tRNS
law png_trns_rgb_deep:
  for +dd: U32
  for +xs: List<&2, U32>
  for +plte: List<&2, U32>
  for +trns: List<&2, U32>
  for h_dd: {Bool.or(U32.is_eq(dd, 8), U32.is_eq(dd, 16)) == True{} : Bool}
  for h_len: {Nat.is_eq(List.length(&2, U32, trns), 6n) == False{} : Bool}
  {Png.px.deep(2, dd, xs, plte, trns) == Png.px.deep(2, dd, xs, plte, []) : Maybe<&2, List<&2, U32>>}

# LAW: a tRNS chunk after IHDR that comes after IDAT, is a second one, or is not allowed for the colour type yet
# (any for gray with alpha or RGBA, a palette's before PLTE) leaves the walker as an unknown ancillary chunk does
# (laws/PngAncillaryChunksIgnored.bend): the IDAT run closed and the state otherwise kept
law png_trns_placed:
  for +ww: U32
  for +hh: U32
  for +dd: U32
  for +cc: U32
  for +comp: U32
  for +ff: U32
  for +ii: U32
  for +idat: List<&2, U32>
  for +plte: List<&2, U32>
  for +trns: List<&2, U32>
  for +sp: Bool
  for +si: Bool
  for +sd: Bool
  for +st: Bool
  for +data: List<&2, U32>
  for h_bad: {Bool.or(si, Bool.or(st, Bool.not(spec.trns.allowed(cc, sp)))) == True{} : Bool}
  {Png.png.apply(1951551059, data, Png.Pg{ww, hh, dd, cc, comp, ff, ii, idat, plte, trns, True{}, sp, si, sd, st,
    False{}}) == Png.NMore{Png.png.seal(Png.Pg{ww, hh, dd, cc, comp, ff, ii, idat, plte, trns, True{}, sp, si, sd, st,
    False{}})} : Png.Nx}
