# proofs of laws/JpegEncodeRefusesBadRasters.bend
import Base
import ../main.bend as Img
import ../laws/JpegEncodeRefusesBadRasters.bend as Laws

# encode_jpeg's answer is none exactly when its guard fails
def refuse.pick(
  ok: Bool,
  +ww: U32,
  +hh: U32,
  +qx: List<&2, U32>
) -> {Maybe.is_none(&2, List<&2, U32>, Img.encode_jpeg.pick(ok, ww, hh, qx)) == Bool.not(ok) : Bool}:
  match ok:
    case False{}:
      {==}
    case True{}:
      {==}

def Laws.jpeg_refuse_exactly(ww, hh, px):
  refuse.pick(Img.encode_jpeg.good(ww, hh, px), ww, hh, Img.colours(px))
