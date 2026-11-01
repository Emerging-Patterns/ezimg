# whether a point lies in a raster, and the value a read of a plane finds
import Base
import ../../main.bend as Img

# is (x, y) a point of the raster: x < w and y < h, as Nats
def inside(img: Img.Raster, +xx: U32, +yy: U32) -> Bool:
  match img:
    case Img.Raster{ww, hh, _px}:
      Bool.and(Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)), Nat.is_lt(U32.to_nat(yy), U32.to_nat(hh)))

# the value a read of a plane finds
def jpg.val(pp: Array<U32> & U32) -> U32:
  (_aa, vv) = pp
  vv
