# proofs of laws/JpegEncodeIgnoresAlpha.bend
import Base
import ../main.bend as Img
import ../laws/JpegEncodeIgnoresAlpha.bend as Laws

# the code's colours is the specification's alpha.drop
def colours.drop(+px: List<&2, U32>) -> {Img.colours(px) == Laws.alpha.drop(px) : List<&2, U32>}:
  match px:
    case Nil{}:
      {==}
    case +pp <> rest:
      Equal.cong(List<&2, U32>, List<&2, U32>, tl => {U32.and(16777215, pp) <> tl : List<&2, U32>}, Img.colours(rest),
        Laws.alpha.drop(rest), colours.drop(rest))

# clearing alpha keeps the sample count
def len.drop(+px: List<&2, U32>) -> {List.length(&2, U32, Laws.alpha.drop(px)) == List.length(&2, U32, px) : Nat}:
  match px:
    case Nil{}:
      {==}
    case _pp <> rest:
      Equal.cong(Nat, Nat, nn => 1n+nn, List.length(&2, U32, Laws.alpha.drop(rest)), List.length(&2, U32, rest),
        len.drop(rest))

# encode_jpeg's guard asks the samples only for their count, so it answers the same for a list and its colours
def good.drop(
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>
) -> {Img.encode_jpeg.good(ww, hh, Laws.alpha.drop(px)) == Img.encode_jpeg.good(ww, hh, px) : Bool}:
  Equal.cong(Nat, Bool, nn => Bool.and(Bool.and(Img.encode_jpeg.side(ww), Img.encode_jpeg.side(hh)),
    Bool.and(U32.is_le((ww * hh : U32), 2147483648), Nat.is_eq(nn, Nat.mul(U32.to_nat(ww), U32.to_nat(hh))))),
    List.length(&2, U32, Laws.alpha.drop(px)), List.length(&2, U32, px), len.drop(px))

def Laws.jpeg_alpha_blind(ww, hh, pa, pb, same):
  +gab = Equal.trans(Bool, Img.encode_jpeg.good(ww, hh, pa), Img.encode_jpeg.good(ww, hh, Laws.alpha.drop(pa)),
    Img.encode_jpeg.good(ww, hh, pb),
    Equal.sym(Bool, Img.encode_jpeg.good(ww, hh, Laws.alpha.drop(pa)), Img.encode_jpeg.good(ww, hh, pa),
      good.drop(ww, hh, pa)),
    Equal.trans(Bool, Img.encode_jpeg.good(ww, hh, Laws.alpha.drop(pa)), Img.encode_jpeg.good(ww, hh,
      Laws.alpha.drop(pb)), Img.encode_jpeg.good(ww, hh, pb),
      Equal.cong(List<&2, U32>, Bool, ll => Img.encode_jpeg.good(ww, hh, ll), Laws.alpha.drop(pa),
        Laws.alpha.drop(pb), same),
      good.drop(ww, hh, pb)))
  +cab = Equal.trans(List<&2, U32>, Img.colours(pa), Laws.alpha.drop(pa), Img.colours(pb), colours.drop(pa),
    Equal.trans(List<&2, U32>, Laws.alpha.drop(pa), Laws.alpha.drop(pb), Img.colours(pb), same,
      Equal.sym(List<&2, U32>, Img.colours(pb), Laws.alpha.drop(pb), colours.drop(pb))))
  Equal.trans(Maybe<&2, List<&2, U32>>,
    Img.encode_jpeg.pick(Img.encode_jpeg.good(ww, hh, pa), ww, hh, Img.colours(pa)),
    Img.encode_jpeg.pick(Img.encode_jpeg.good(ww, hh, pb), ww, hh, Img.colours(pa)),
    Img.encode_jpeg.pick(Img.encode_jpeg.good(ww, hh, pb), ww, hh, Img.colours(pb)),
    Equal.cong(Bool, Maybe<&2, List<&2, U32>>, bb => Img.encode_jpeg.pick(bb, ww, hh, Img.colours(pa)),
      Img.encode_jpeg.good(ww, hh, pa), Img.encode_jpeg.good(ww, hh, pb), gab),
    Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>,
      ll => Img.encode_jpeg.pick(Img.encode_jpeg.good(ww, hh, pb), ww, hh, ll), Img.colours(pa), Img.colours(pb), cab))
