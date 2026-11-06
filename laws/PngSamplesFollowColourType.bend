# For each colour type at bit depth 8, each decoded sample is the packing of
# the unfiltered bytes the PNG specification gives: gray `g` as `0xFFgggggg`,
# gray and alpha as `0xAAgggggg`, RGB as `0xFFrrggbb`, RGBA as `0xAArrggbb`,
# an index as its palette entry with alpha from tRNS or 255, and a colour
# matching a tRNS key with alpha 0. Indexed samples decode exactly when every
# index is below the palette's entry count. Gray and alpha and RGBA carry
# their own alpha, so a tRNS there changes nothing, and a palette tRNS
# longer than the palette is ignored (laws/PngIgnoresFaultyTrns.bend).
#
# also rests on: laws/PngAncillaryChunksIgnored.bend
import Base
import ../main.bend as Img
import ../src/inflate.bend as Inf
import ../src/png.bend as Png
import ./defs/PngSpecification.bend as D1

# a sample packed 0xAARRGGBB: alpha in the top byte, then red, green and blue
def spec.argb(+aa: U32, +rr: U32, +gg: U32, +bb: U32) -> U32:
  ((((aa << 24n : U32) .|. (rr << 16n : U32) : U32) .|. (gg << 8n : U32) : U32) .|. bb : U32)

# the alpha of a sample checked against a tRNS key: 0 when it matches, 255 otherwise
def spec.key.alpha(hit: Bool) -> U32:
  match hit:
    case True{}:
      0
    case False{}:
      255

# a list of samples, or none
def spec.cons(+hd: U32, mm: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match mm:
    case None{}:
      None{}
    case Some{tl}:
      Some{hd <> tl}

# colour type 0: each gray byte g is 0xFFgggggg
def spec.grey(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case +gg <> tl:
      spec.argb(255, gg, gg, gg) <> spec.grey(tl)

# colour type 0 with a tRNS key: a gray byte equal to the key has alpha 0
def spec.grey.key(xs: List<&2, U32>, +kk: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case +gg <> tl:
      spec.argb(spec.key.alpha(U32.is_eq(gg, kk)), gg, gg, gg) <> spec.grey.key(tl, kk)

# colour type 4: each gray and alpha pair is 0xAAgggggg; none when a pair is cut short
def spec.ga(xs: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case +gg <> +aa <> tl:
      spec.cons(spec.argb(aa, gg, gg, gg), spec.ga(tl))
    case _xs:
      None{}

# colour type 2: each RGB triple is 0xFFrrggbb; none when a triple is cut short
def spec.rgb(xs: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case +rr <> +gg <> +bb <> tl:
      spec.cons(spec.argb(255, rr, gg, bb), spec.rgb(tl))
    case _xs:
      None{}

# colour type 2 with a tRNS key: a triple equal to the key in all three channels has alpha 0
def spec.rgb.key(xs: List<&2, U32>, +kr: U32, +kg: U32, +kb: U32) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case +rr <> +gg <> +bb <> tl:
      spec.cons(spec.argb(spec.key.alpha(Bool.and(U32.is_eq(rr, kr), Bool.and(U32.is_eq(gg, kg), U32.is_eq(bb, kb)))),
        rr, gg, bb), spec.rgb.key(tl, kr, kg, kb))
    case _xs:
      None{}

# colour type 6: each RGBA quadruple is 0xAArrggbb; none when one is cut short
def spec.rgba(xs: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case +rr <> +gg <> +bb <> +aa <> tl:
      spec.cons(spec.argb(aa, rr, gg, bb), spec.rgba(tl))
    case _xs:
      None{}

# tRNS's alphas for a palette: all of them when tRNS has no more entries
# than PLTE has (PNG section 11.3.2.1), none otherwise, as libpng ignores
# such a tRNS
def spec.alphas.keep(fits: Bool, als: List<&2, U32>) -> List<&2, U32>:
  match fits:
    case True{}:
      als
    case False{}:
      []

# the alphas of tRNS that apply to the palette PLTE holds
def spec.alphas(+plte: List<&2, U32>, +trns: List<&2, U32>) -> List<&2, U32>:
  spec.alphas.keep(Nat.is_le(List.length(&2, U32, trns), Nat.div(List.length(&2, U32, plte), 3n)), trns)

# the palette: entry k is PLTE's triple k packed with alpha tRNS byte k, or
# 255 past the end of tRNS
def spec.pal(xs: List<&2, U32>, als: List<&2, U32>) -> List<&2, U32>:
  match xs als:
    case +rr <> +gg <> +bb <> tl Nil{}:
      spec.argb(255, rr, gg, bb) <> spec.pal(tl, [])
    case +rr <> +gg <> +bb <> tl +aa <> at:
      spec.argb(aa, rr, gg, bb) <> spec.pal(tl, at)
    case _xs _als:
      Nil{}

# one index's entry, if the palette has it, before the rest
def spec.idx.at(me: Maybe<&2, U32>, rest: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match me:
    case None{}:
      None{}
    case Some{+cc}:
      spec.cons(cc, rest)

# colour type 3: each index is its palette entry; none when an index is past the palette
def spec.idx(xs: List<&2, U32>, +pal: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case +ix <> tl:
      spec.idx.at(List.get(&2, U32, pal, U32.to_nat(ix)), spec.idx(tl, pal))

# LAW: colour type 0 without tRNS: each gray byte g decodes to 0xFFgggggg
law png_px_grey:
  for +xs: List<&2, U32>
  {Png.px.of(0, xs, [], []) == Some{spec.grey(xs)} : Maybe<&2, List<&2, U32>>}

# LAW: colour type 0 with tRNS key k: each gray byte g decodes to 0xFFgggggg, alpha 0 when g is k
law png_px_grey_key:
  for +xs: List<&2, U32>
  for +kk: U32
  {Png.px.of(0, xs, [], [0, kk]) == Some{spec.grey.key(xs, kk)} : Maybe<&2, List<&2, U32>>}

# LAW: colour type 4: each gray and alpha pair decodes to 0xAAgggggg, whatever PLTE and tRNS hold
law png_px_ga:
  for +xs: List<&2, U32>
  for +plte: List<&2, U32>
  for +trns: List<&2, U32>
  {Png.px.of(4, xs, plte, trns) == spec.ga(xs) : Maybe<&2, List<&2, U32>>}

# LAW: colour type 2 without tRNS: each RGB triple decodes to 0xFFrrggbb, whatever suggested palette there is
law png_px_rgb:
  for +xs: List<&2, U32>
  for +plte: List<&2, U32>
  {Png.px.of(2, xs, plte, []) == spec.rgb(xs) : Maybe<&2, List<&2, U32>>}

# LAW: colour type 2 with tRNS key (kr, kg, kb): each triple decodes to 0xFFrrggbb, alpha 0 when it is the key
law png_px_rgb_key:
  for +xs: List<&2, U32>
  for +plte: List<&2, U32>
  for +kr: U32
  for +kg: U32
  for +kb: U32
  {Png.px.of(2, xs, plte, [0, kr, 0, kg, 0, kb]) == spec.rgb.key(xs, kr, kg, kb) : Maybe<&2, List<&2, U32>>}

# LAW: colour type 6: each RGBA quadruple decodes to 0xAArrggbb, whatever suggested palette and tRNS there are
law png_px_rgba:
  for +xs: List<&2, U32>
  for +plte: List<&2, U32>
  for +trns: List<&2, U32>
  {Png.px.of(6, xs, plte, trns) == spec.rgba(xs) : Maybe<&2, List<&2, U32>>}

# LAW: colour type 3: the indices decode exactly when each is below the palette's entry count, each to its palette
# entry with alpha from tRNS or 255 (none from a tRNS longer than the palette); otherwise the samples are none
law png_px_indexed:
  for +xs: List<&2, U32>
  for +plte: List<&2, U32>
  for +trns: List<&2, U32>
  {Png.px.of(3, xs, plte, trns) == spec.idx(xs, spec.pal(plte, spec.alphas(plte, trns))) : Maybe<&2, List<&2, U32>>}

# a picture of those samples, when there are some
def spec.pic(mm: Maybe<&2, List<&2, U32>>, +ww: U32, +hh: U32) -> Maybe<&2, Png.Pic>:
  match mm:
    case None{}:
      None{}
    case Some{px}:
      Some{Png.Pic{ww, hh, px}}

# LAW: the decoder's last stage packs the unfiltered bytes of the inflated IDAT data with px.of, for the IHDR's
# colour type, PLTE and tRNS, and keeps the width and height
law png_samples_frame:
  for +raw: List<&2, U32>
  for +ww: U32
  for +hh: U32
  for +colour: U32
  for +plte: List<&2, U32>
  for +trns: List<&2, U32>
  {Png.png.samples(Some{raw}, ww, hh, colour, plte, trns) ==
    spec.pic(D1.spec.px.then(Png.unfilter(raw, ww, hh, Png.png.bpp(colour)), colour, plte, trns), ww, hh)
    : Maybe<&2, Png.Pic>}

# LAW: the chunk walker hands the pixel stage the IHDR's size and colour type,
# the PLTE and tRNS data, and the IDAT data concatenated: a file of the
# signature, IHDR, PLTE and tRNS where allowed, any IDAT chunks and IEND
# decodes to the raster px.of packs from the unfiltered inflated data
law png_walk:
  for +ww: U32
  for +hh: U32
  for +cc: U32
  for +plte: Maybe<&2, List<&2, U32>>
  for +trns: Maybe<&2, List<&2, U32>>
  for +idats: List<&2, List<&2, U32>>
  for h_ww: {U32.is_gt(ww, 0) == True{} : Bool}
  for h_hh: {U32.is_gt(hh, 0) == True{} : Bool}
  for h_cc: {D1.spec.colour.ok(cc) == True{} : Bool}
  for h_pl: {D1.spec.plte.ok(cc, plte) == True{} : Bool}
  for h_tr: {D1.spec.trns.ok(cc, plte, trns) == True{} : Bool}
  for h_fp: D1.spec.fits.opt(plte)
  for h_ft: D1.spec.fits.opt(trns)
  for h_fi: D1.spec.fits.all(idats)
  {Img.decode_png(D1.spec.png(ww, hh, cc, plte, trns, idats)) == D1.spec.decoded(Inf.inflate(List.concat(&2, U32,
      idats)),
    ww, hh, cc, D1.spec.or.nil(plte), D1.spec.or.nil(trns)) : Maybe<&2, Img.Raster>}
