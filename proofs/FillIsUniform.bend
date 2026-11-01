# proofs of laws/FillIsUniform.bend
import Base
import ../laws/FillIsUniform.bend as Laws
import ./lemmas/BasicFacts.bend as M1
import ./lemmas/RowMajorIndex.bend as M2

# ---- lists ----

# a sample list's value, or d
def some_or(mm: Maybe<&2, U32>, dd: U32) -> U32:
  match mm:
    case None{}:
      dd
    case Some{vv}:
      vv

# is the answer some
def is_some(mm: Maybe<&2, U32>) -> Bool:
  match mm:
    case None{}:
      False{}
    case Some{_vv}:
      True{}

# replicate n c has n elements
law length_replicate:
  for nn: Nat
  for +cc: U32
  {List.length(&2, U32, List.replicate(U32, nn, cc)) == nn : Nat}

# the proof of length_replicate
def length_replicate(nn, cc):
  match nn:
    case 0n:
      {==}
    case 1n+pp:
      Equal.cong(Nat, Nat, xx => 1n+xx, List.length(&2, U32, List.replicate(U32, pp, cc)), pp,
        length_replicate(pp, cc))

# every element of replicate n c is c
law get_replicate:
  for nn: Nat
  for kk: Nat
  for +cc: U32
  for +vv: U32
  for hh: {List.get(&2, U32, List.replicate(U32, nn, cc), kk) == Some{vv} : Maybe<&2, U32>}
  {vv == cc : U32}

# the proof of get_replicate
def get_replicate(nn, kk, cc, vv, hh):
  match nn kk:
    case 0n _kk:
      Empty.absurd({vv == cc : U32}, M1.false_true(Equal.cong(Maybe<&2, U32>, Bool, mm => is_some(mm), None{},
        Some{vv}, hh)))
    case 1n+_pp 0n:
      Equal.sym(U32, cc, vv, Equal.cong(Maybe<&2, U32>, U32, mm => some_or(mm, cc), Some{cc}, Some{vv}, hh))
    case 1n+pp 1n+qq:
      get_replicate(pp, qq, cc, vv, hh)

def Laws.fill_wf(ww, hh, color, area, h_area):
  +wh = Nat.mul(U32.to_nat(ww), U32.to_nat(hh))
  +nn = U32.to_nat(U32.mul(ww, hh))
  +en = {M2.u32_mul_below(ww, hh, area, M1.le_rw_r(wh, wh, U32.to_nat(area), Equal.sym(Nat, U32.to_nat(area), wh,
      h_area),
    M1.le_refl(wh))) : {nn == wh : Nat}}
  +el = {Equal.trans(Nat, List.length(&2, U32, List.replicate(U32, nn, color)), nn, wh,
    length_replicate(nn, color), en) : {List.length(&2, U32, List.replicate(U32, nn, color)) == wh : Nat}}
  Equal.trans(Bool, Nat.is_eq(List.length(&2, U32, List.replicate(U32, nn, color)), wh), Nat.is_eq(wh, wh), True{},
    Equal.cong(Nat, Bool, xx => Nat.is_eq(xx, wh), List.length(&2, U32, List.replicate(U32, nn, color)), wh, el),
    M1.nat_eq_refl(wh))

def Laws.fill_every(ww, hh, color, kk, vv, h_at):
  get_replicate(U32.to_nat(U32.mul(ww, hh)), kk, color, vv, h_at)
