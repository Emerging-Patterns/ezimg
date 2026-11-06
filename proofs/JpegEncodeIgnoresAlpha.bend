# proofs of laws/JpegEncodeIgnoresAlpha.bend
import Base
import ../main.bend as Img
import ../src/png.bend as Png
import ../laws/JpegEncodeIgnoresAlpha.bend as Laws

# the code's colours is the specification's alpha.drop
def colours.drop(+px: List<&2, U32>) -> {Img.colours(px) == Laws.alpha.drop(px) : List<&2, U32>}:
  match px:
    case Nil{}:
      {==}
    case +pp <> rest:
      Equal.cong(List<&2, U32>, List<&2, U32>, tl => {U32.and(16777215, pp) <> tl : List<&2, U32>}, Img.colours(rest),
        Laws.alpha.drop(rest), colours.drop(rest))

# clearing alpha keeps the count Png.enc.len takes
def len.drop(
  +px: List<&2, U32>,
  +nn: U32
) -> {Png.enc.len(Laws.alpha.drop(px), nn) == Png.enc.len(px, nn) : U32}:
  match px:
    case Nil{}:
      {==}
    case _pp <> rest:
      len.drop(rest, (nn + 1 : U32))

# the guard's walk uses the samples only as fuel, so clearing alpha keeps it
def rows.drop(
  px: List<&2, U32>,
  zh: Bool,
  zlt: Bool,
  +ww: U32,
  +hh: U32,
  +cc: U32
) -> {Png.enc.rows(Laws.alpha.drop(px), zh, zlt, ww, hh, cc) == Png.enc.rows(px, zh, zlt, ww, hh, cc) : Bool}:
  match px zh zlt:
    case Nil{} True{} _zlt:
      {==}
    case Nil{} False{} True{}:
      {==}
    case Nil{} False{} False{}:
      {==}
    case _pp <> _rest True{} _zlt:
      {==}
    case _pp <> _rest False{} True{}:
      {==}
    case _pp <> rest False{} False{}:
      +c2 = (cc - ww : U32)
      +h2 = (hh - 1 : U32)
      rows.drop(rest, U32.is_zero(h2), U32.is_lt(c2, ww), ww, h2, c2)

# the guard with a count n and the samples as fuel
def good.at(+ww: U32, +hh: U32, +px: List<&2, U32>, +nn: U32) -> Bool:
  Bool.and(Bool.and(U32.is_gt(ww, 0), U32.is_gt(hh, 0)), Bool.and(Png.enc.rows(px, U32.is_zero(hh), U32.is_lt(nn, ww),
    ww, hh, nn), Png.enc.small(nn)))

# so the guard answers the same for a list and its colours
def good.drop(
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>
) -> {Png.enc.good(ww, hh, Laws.alpha.drop(px)) == Png.enc.good(ww, hh, px) : Bool}:
  +na = Png.enc.len(Laws.alpha.drop(px), 0)
  +nb = Png.enc.len(px, 0)
  Equal.trans(Bool, good.at(ww, hh, Laws.alpha.drop(px), na), good.at(ww, hh, px, na), good.at(ww, hh, px, nb),
    Equal.cong(Bool, Bool, bb => Bool.and(Bool.and(U32.is_gt(ww, 0), U32.is_gt(hh, 0)), Bool.and(bb,
      Png.enc.small(na))),
      Png.enc.rows(Laws.alpha.drop(px), U32.is_zero(hh), U32.is_lt(na, ww), ww, hh, na),
      Png.enc.rows(px, U32.is_zero(hh), U32.is_lt(na, ww), ww, hh, na),
      rows.drop(px, U32.is_zero(hh), U32.is_lt(na, ww), ww, hh, na)),
    Equal.cong(U32, Bool, nn => good.at(ww, hh, px, nn), na, nb, len.drop(px, 0)))

def Laws.jpeg_alpha_blind(ww, hh, pa, pb, same):
  +gab = Equal.trans(Bool, Png.enc.good(ww, hh, pa), Png.enc.good(ww, hh, Laws.alpha.drop(pa)),
    Png.enc.good(ww, hh, pb),
    Equal.sym(Bool, Png.enc.good(ww, hh, Laws.alpha.drop(pa)), Png.enc.good(ww, hh, pa), good.drop(ww, hh, pa)),
    Equal.trans(Bool, Png.enc.good(ww, hh, Laws.alpha.drop(pa)), Png.enc.good(ww, hh, Laws.alpha.drop(pb)),
      Png.enc.good(ww, hh, pb),
      Equal.cong(List<&2, U32>, Bool, ll => Png.enc.good(ww, hh, ll), Laws.alpha.drop(pa), Laws.alpha.drop(pb), same),
      good.drop(ww, hh, pb)))
  +cab = Equal.trans(List<&2, U32>, Img.colours(pa), Laws.alpha.drop(pa), Img.colours(pb), colours.drop(pa),
    Equal.trans(List<&2, U32>, Laws.alpha.drop(pa), Laws.alpha.drop(pb), Img.colours(pb), same,
      Equal.sym(List<&2, U32>, Img.colours(pb), Laws.alpha.drop(pb), colours.drop(pb))))
  Equal.trans(Maybe<&2, List<&2, U32>>,
    Img.encode_jpeg.pick(Png.enc.good(ww, hh, pa), ww, hh, Img.colours(pa)),
    Img.encode_jpeg.pick(Png.enc.good(ww, hh, pb), ww, hh, Img.colours(pa)),
    Img.encode_jpeg.pick(Png.enc.good(ww, hh, pb), ww, hh, Img.colours(pb)),
    Equal.cong(Bool, Maybe<&2, List<&2, U32>>, bb => Img.encode_jpeg.pick(bb, ww, hh, Img.colours(pa)),
      Png.enc.good(ww, hh, pa), Png.enc.good(ww, hh, pb), gab),
    Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>,
      ll => Img.encode_jpeg.pick(Png.enc.good(ww, hh, pb), ww, hh, ll), Img.colours(pa), Img.colours(pb), cab))
