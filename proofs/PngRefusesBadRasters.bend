# proofs of laws/PngRefusesBadRasters.bend
import Base
import ../src/png.bend as Png
import ../laws/PngRefusesBadRasters.bend as Laws
import ../laws/defs/SizeBounds.bend as D1
import ./lemmas/PngEncoderArithmetic.bend as M1

# enc.open is none exactly when its guard is false
def open.none(
  zz: Bool,
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>
) -> {Maybe.is_none(&2, List<&2, U32>, Png.enc.open(zz, ww, hh, px)) == Bool.not(zz) : Bool}:
  match zz:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.png_refuses(ww, hh, px, h_len):
  Equal.trans(Bool, Maybe.is_none(&2, List<&2, U32>, Png.enc.open(Png.enc.good(ww, hh, px), ww, hh, px)),
    Bool.not(Png.enc.good(ww, hh, px)), Bool.not(D1.png_ok(ww, hh, px)),
    open.none(Png.enc.good(ww, hh, px), ww, hh, px),
    Equal.cong(Bool, Bool, bb => Bool.not(bb), Png.enc.good(ww, hh, px), D1.png_ok(ww, hh, px),
      M1.good.nat(ww, hh, px, h_len)))
