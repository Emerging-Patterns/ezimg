# how much of a span lies inside one side of a raster
import Base

# how much of the span x .. x + c - 1 lies in 0 .. w - 1: min(c, w - x), and
# 0 when x >= w (Nat.sub stops at 0)
def cut(ww: U32, xx: U32, cc: U32) -> Nat:
  Nat.min(U32.to_nat(cc), Nat.sub(U32.to_nat(ww), U32.to_nat(xx)))
