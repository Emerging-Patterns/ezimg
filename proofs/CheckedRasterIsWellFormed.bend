# proofs of laws/CheckedRasterIsWellFormed.bend
import Base
import ../main.bend as Img
import ../laws/CheckedRasterIsWellFormed.bend as Laws
import ./lemmas/BasicFacts.bend as M1

# a number below acc is not acc + x
def lt.neq(
  ll: Nat,
  acc: Nat,
  +xx: Nat,
  hh: {Nat.is_lt(ll, acc) == True{} : Bool}
) -> {False{} == Nat.is_eq(ll, Nat.add(acc, xx)) : Bool}:
  match ll acc:
    case 0n 0n:
      Empty.absurd({False{} == Nat.is_eq(0n, xx) : Bool}, M1.false_true(hh))
    case 0n 1n+_qq:
      {==}
    case 1n+_pp 0n:
      Empty.absurd({False{} == Nat.is_eq(1n+_pp, xx) : Bool}, M1.false_true(hh))
    case 1n+pp 1n+qq:
      lt.neq(pp, qq, xx, hh)

# the area walk answers ll == acc + w * h, when over says whether acc is past ll
def area.is.nat(
  wn: Nat,
  over: Bool,
  +hn: Nat,
  +ll: Nat,
  +acc: Nat,
  eo: {Nat.is_lt(ll, acc) == over : Bool}
) -> {Img.area.is(wn, over, hn, ll, acc) == Nat.is_eq(ll, Nat.add(acc, Nat.mul(wn, hn))) : Bool}:
  match wn over:
    case _wn True{}:
      lt.neq(ll, acc, Nat.mul(_wn, hn), eo)
    case 0n False{}:
      Equal.cong(Nat, Bool, kk => Nat.is_eq(ll, kk), acc, Nat.add(acc, 0n),
        Equal.sym(Nat, Nat.add(acc, 0n), acc, M1.ras.add_zero(acc)))
    case 1n+(+pp) False{}:
      +nx = Nat.add(acc, hn)
      Equal.trans(Bool, Img.area.is(pp, Nat.is_lt(ll, nx), hn, ll, nx), Nat.is_eq(ll, Nat.add(nx, Nat.mul(pp, hn))),
        Nat.is_eq(ll, Nat.add(acc, Nat.add(hn, Nat.mul(pp, hn)))),
        area.is.nat(pp, Nat.is_lt(ll, nx), hn, ll, nx, {==}),
        Equal.cong(Nat, Bool, kk => Nat.is_eq(ll, kk), Nat.add(nx, Nat.mul(pp, hn)),
          Nat.add(acc, Nat.add(hn, Nat.mul(pp, hn))), M1.ras.add_assoc(acc, hn, Nat.mul(pp, hn))))

# the count check answers ll == w * h
def area.of.nat(+wn: Nat, hn: Nat, +ll: Nat) -> {Img.area.of(wn, hn, ll) == Nat.is_eq(ll, Nat.mul(wn, hn)) : Bool}:
  match hn:
    case 0n:
      {==}
    case 1n+(+pp):
      area.is.nat(wn, False{}, 1n+pp, ll, 0n, Equal.sym(Bool, False{}, Nat.is_lt(ll, 0n), M1.lt_zero_false(ll)))

# keeping on a check is keep on it
def keep.at(
  ok: Bool,
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>
) -> {Img.checked.keep(ok, ww, hh, px) == Laws.keep(ok, Img.raster(ww, hh, px)) : Maybe<&2, Img.Raster>}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.checked_keeps(ww, hh, px):
  +ll = List.length(&2, U32, px)
  +wh = Nat.mul(U32.to_nat(ww), U32.to_nat(hh))
  Equal.trans(Maybe<&2, Img.Raster>, Img.checked.keep(Img.area.of(U32.to_nat(ww), U32.to_nat(hh), ll), ww, hh, px),
    Img.checked.keep(Nat.is_eq(ll, wh), ww, hh, px), Laws.keep(Nat.is_eq(ll, wh), Img.raster(ww, hh, px)),
    Equal.cong(Bool, Maybe<&2, Img.Raster>, bb => Img.checked.keep(bb, ww, hh, px),
      Img.area.of(U32.to_nat(ww), U32.to_nat(hh), ll), Nat.is_eq(ll, wh), area.of.nat(U32.to_nat(ww), U32.to_nat(hh),
        ll)),
    keep.at(Nat.is_eq(ll, wh), ww, hh, px))
