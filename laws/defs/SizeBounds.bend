# halving, bounds below 2^n, the sizes encode_png takes, and a crop's sides
import Base

# one side of a crop: the intersection's side aa, or 0 when either side of
# the intersection (aa or bb) is 0
def side(aa: Nat, bb: Nat) -> Nat:
  match aa bb:
    case 0n _bb:
      0n
    case 1n+_pa 0n:
      0n
    case 1n+pa 1n+_pb:
      1n+pa

# half of x, rounded down
def half(xx: Nat) -> Nat:
  match xx:
    case 0n:
      0n
    case 1n+pp:
      match pp:
        case 0n:
          0n
        case 1n+qq:
          1n+half(qq)

# x < 2^n: halving x n times leaves 0
def below(nn: Nat, xx: Nat) -> Bool:
  match nn:
    case 0n:
      Nat.is_eq(xx, 0n)
    case 1n+pp:
      below(pp, half(xx))

# the rasters laws/PngRefusesBadRasters.bend calls encodable: neither side
# 0, the area w * h (h rows of w, as natural numbers) below 2^28, and w * h
# samples
def png_ok(+ww: U32, +hh: U32, +px: List<&2, U32>) -> Bool:
  +area = Nat.mul(U32.to_nat(hh), U32.to_nat(ww))
  Bool.and(Bool.and(Bool.not(Nat.is_eq(U32.to_nat(ww), 0n)), Bool.not(Nat.is_eq(U32.to_nat(hh), 0n))),
    Bool.and(below(28n, area), Nat.is_eq(List.length(&2, U32, px), area)))
