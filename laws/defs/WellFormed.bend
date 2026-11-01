# a raster is well formed: its sample count is w * h
import Base
import ../../main.bend as Img

# is the raster well formed: its sample count is w * h, computed as a Nat
def wf(img: Img.Raster) -> Bool:
  match img:
    case Img.Raster{ww, hh, px}:
      Nat.is_eq(List.length(&2, U32, px), Nat.mul(U32.to_nat(ww), U32.to_nat(hh)))
