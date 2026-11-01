# whether a raster pasted at (x, y) covers a point
import Base
import ../../main.bend as Img

# does src, pasted at (x, y), cover the point (i, j): x <= i < x + sw and
# y <= j < y + sh, as Nats
def covers(+xx: U32, +yy: U32, src: Img.Raster, +ii: Nat, +jj: Nat) -> Bool:
  match src:
    case Img.Raster{sw, sh, _sp}:
      Bool.and(Bool.and(Nat.is_le(U32.to_nat(xx), ii), Nat.is_lt(ii, Nat.add(U32.to_nat(xx), U32.to_nat(sw)))),
        Bool.and(Nat.is_le(U32.to_nat(yy), jj), Nat.is_lt(jj, Nat.add(U32.to_nat(yy), U32.to_nat(sh)))))
