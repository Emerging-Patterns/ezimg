# Nat addition, carries and halving, and the rows the PNG encoder writes
import Base
import ../../src/png.bend as Png
import ../../laws/PngRefusesBadRasters.bend as L1
import ../../laws/defs/SizeBounds.bend as D1
import ./BasicFacts.bend as M1

# ---- Nat ----

# one less, or zero
def npred(xx: Nat) -> Nat:
  match xx:
    case 0n:
      0n
    case 1n+(+pp):
      pp

# the type 0n == n names: Unit for 0, Empty for a successor
def penc.zero_ty(nn: Nat) -> Type:
  match nn:
    case 0n:
      Unit
    case 1n+(+_pp):
      Empty

# zero is no successor
law penc.zero_succ:
  for -xx: Nat
  for +ee: {0n == 1n+xx : Nat}
  Empty

# the proof of penc.zero_succ
def penc.zero_succ(_xx, ee):
  %ee : penc.zero_ty(_)
  Unit{}

# successors are equal only when their predecessors are
law penc.succ_inj:
  for +aa: Nat
  for +bb: Nat
  for +ee: {1n+aa == 1n+bb : Nat}
  {aa == bb : Nat}

# the proof of penc.succ_inj
def penc.succ_inj(aa, bb, ee):
  Equal.cong(Nat, Nat, xx => npred(xx), 1n+aa, 1n+bb, ee)

# adding zero on the right
law add_zero:
  for +xx: Nat
  {Nat.add(xx, 0n) == xx : Nat}

# the proof of add_zero
def add_zero(xx):
  match xx:
    case 0n:
      {==}
    case 1n+(+pp):
      Equal.cong(Nat, Nat, nn => 1n+nn, Nat.add(pp, 0n), pp, add_zero(pp))

# a successor on the right comes out
law add_succ:
  for +xx: Nat
  for +yy: Nat
  {Nat.add(xx, 1n+yy) == 1n+Nat.add(xx, yy) : Nat}

# the proof of add_succ
def add_succ(xx, yy):
  match xx:
    case 0n:
      {==}
    case 1n+(+pp):
      Equal.cong(Nat, Nat, nn => 1n+nn, Nat.add(pp, 1n+yy), 1n+Nat.add(pp, yy), add_succ(pp, yy))

# addition commutes
law add_comm:
  for +xx: Nat
  for +yy: Nat
  {Nat.add(xx, yy) == Nat.add(yy, xx) : Nat}

# the proof of add_comm
def add_comm(xx, yy):
  match xx:
    case 0n:
      Equal.sym(Nat, Nat.add(yy, 0n), yy, add_zero(yy))
    case 1n+(+pp):
      Equal.trans(Nat, 1n+Nat.add(pp, yy), 1n+Nat.add(yy, pp), Nat.add(yy, 1n+pp),
        Equal.cong(Nat, Nat, nn => 1n+nn, Nat.add(pp, yy), Nat.add(yy, pp), add_comm(pp, yy)),
        Equal.sym(Nat, Nat.add(yy, 1n+pp), 1n+Nat.add(yy, pp), add_succ(yy, pp)))

# addition associates
law add_assoc:
  for +xx: Nat
  for +yy: Nat
  for +zz: Nat
  {Nat.add(Nat.add(xx, yy), zz) == Nat.add(xx, Nat.add(yy, zz)) : Nat}

# the proof of add_assoc
def add_assoc(xx, yy, zz):
  match xx:
    case 0n:
      {==}
    case 1n+(+pp):
      Equal.cong(Nat, Nat, nn => 1n+nn, Nat.add(Nat.add(pp, yy), zz), Nat.add(pp, Nat.add(yy, zz)),
        add_assoc(pp, yy, zz))

# a common left summand leaves the order
law cmp_add:
  for +kk: Nat
  for +aa: Nat
  for +bb: Nat
  {Nat.cmp(Nat.add(kk, aa), Nat.add(kk, bb)) == Nat.cmp(aa, bb) : Cmp}

# the proof of cmp_add
def cmp_add(kk, aa, bb):
  match kk:
    case 0n:
      {==}
    case 1n+(+pp):
      cmp_add(pp, aa, bb)

# Nat.is_eq true is equality
law nat_eq_true:
  for +aa: Nat
  for +bb: Nat
  for +ee: {Nat.is_eq(aa, bb) == True{} : Bool}
  {aa == bb : Nat}

# the proof of nat_eq_true
def nat_eq_true(aa, bb, ee):
  match aa bb:
    case 0n 0n:
      {==}
    case 0n 1n+_qb:
      Empty.absurd({0n == 1n+_qb : Nat}, M1.false_true(ee))
    case 1n+_qa 0n:
      Empty.absurd({1n+_qa == 0n : Nat}, M1.false_true(ee))
    case 1n+qa 1n+qb:
      Equal.cong(Nat, Nat, nn => 1n+nn, qa, qb, nat_eq_true(qa, qb, ee))

# below w, so not w and anything
law lt_add:
  for +cc: Nat
  for +ww: Nat
  for +xx: Nat
  for +hl: {Cmp.is_lt(Nat.cmp(cc, ww)) == True{} : Bool}
  {Nat.is_eq(cc, Nat.add(ww, xx)) == False{} : Bool}

# the proof of lt_add
def lt_add(cc, ww, xx, hl):
  match cc ww:
    case 0n 0n:
      Empty.absurd({Nat.is_eq(0n, xx) == False{} : Bool}, M1.false_true(hl))
    case 0n 1n+_qw:
      {==}
    case 1n+_qc 0n:
      Empty.absurd({Nat.is_eq(1n+_qc, xx) == False{} : Bool}, M1.false_true(hl))
    case 1n+(+qc) 1n+(+qw):
      lt_add(qc, qw, xx, hl)

# not below w: w and something
law ge_split:
  for +cc: Nat
  for +ww: Nat
  for +hg: {Cmp.is_lt(Nat.cmp(cc, ww)) == False{} : Bool}
  exs dd: Nat
  {cc == Nat.add(ww, dd) : Nat}

# the rest of ge_split, one more on both sides
def ge_split.up(
  +cc: Nat,
  +ww: Nat,
  pr: &dd: Nat -> {cc == Nat.add(ww, dd) : Nat}
) -> &dd: Nat -> {1n+cc == Nat.add(1n+ww, dd) : Nat}:
  (dd, ed) = pr
  (dd, Equal.cong(Nat, Nat, zz => 1n+zz, cc, Nat.add(ww, dd), ed))

# the proof of ge_split
def ge_split(cc, ww, hg):
  match cc ww:
    case 0n 0n:
      (0n, {==})
    case 0n 1n+_qw:
      Empty.absurd(&dd: Nat -> {0n == Nat.add(1n+_qw, dd) : Nat},
        M1.false_true(Equal.sym(Bool, True{}, False{}, hg)))
    case 1n+(+qc) 0n:
      (1n+qc, {==})
    case 1n+(+qc) 1n+(+qw):
      ge_split.up(qc, qw, ge_split(qc, qw, hg))

# not zero: a successor
law nat_pos:
  for +xx: Nat
  for +hz: {Cmp.is_eq(Nat.cmp(xx, 0n)) == False{} : Bool}
  exs pp: Nat
  {xx == 1n+pp : Nat}

# the proof of nat_pos
def nat_pos(xx, hz):
  match xx:
    case 0n:
      Empty.absurd(&pp: Nat -> {0n == 1n+pp : Nat}, M1.false_true(Equal.sym(Bool, True{}, False{}, hz)))
    case 1n+(+pp):
      (pp, {==})

# above zero is not zero
law gt_zero:
  for +xx: Nat
  {Cmp.is_gt(Nat.cmp(xx, 0n)) == Bool.not(Nat.is_eq(xx, 0n)) : Bool}

# the proof of gt_zero
def gt_zero(xx):
  match xx:
    case 0n:
      {==}
    case 1n+_pp:
      {==}

# ---- halves ----

# half of an even number
law half_double:
  for +xx: Nat
  {D1.half(Nat.double(xx)) == xx : Nat}

# the proof of half_double
def half_double(xx):
  match xx:
    case 0n:
      {==}
    case 1n+(+pp):
      Equal.cong(Nat, Nat, nn => 1n+nn, D1.half(Nat.double(pp)), pp, half_double(pp))

# half of an odd number
law half_odd:
  for +xx: Nat
  {D1.half(1n+Nat.double(xx)) == xx : Nat}

# the proof of half_odd
def half_odd(xx):
  match xx:
    case 0n:
      {==}
    case 1n+(+pp):
      Equal.cong(Nat, Nat, nn => 1n+nn, D1.half(1n+Nat.double(pp)), pp, half_odd(pp))

# halving x and e gives half of x and something more
def half_add.ty(+xx: Nat, +ee: Nat) -> Type:
  &ff: Nat -> {D1.half(Nat.add(xx, ee)) == Nat.add(D1.half(xx), ff) : Nat}

# two more in x is one more in its half
def half_add.up(+xx: Nat, +ee: Nat, pr: half_add.ty(xx, ee)) -> half_add.ty(2n+xx, ee):
  (ff, eh) = pr
  (ff, Equal.cong(Nat, Nat, nn => 1n+nn, D1.half(Nat.add(xx, ee)), Nat.add(D1.half(xx), ff), eh))

# halving a sum leaves at least half the first summand
law half_add:
  for +xx: Nat
  for +ee: Nat
  exs ff: Nat
  {D1.half(Nat.add(xx, ee)) == Nat.add(D1.half(xx), ff) : Nat}

# the proof of half_add
def half_add(xx, ee):
  match xx:
    case 0n:
      (D1.half(ee), {==})
    case 1n+(+x1):
      match x1:
        case 0n:
          (D1.half(1n+ee), {==})
        case 1n+(+x2):
          half_add.up(x2, ee, half_add(x2, ee))

# below 2^(n+1) once the half of x and e is rewritten: the half of x and f
def below_mono.half(
  +pp: Nat,
  +xx: Nat,
  +ee: Nat,
  pr: half_add.ty(xx, ee),
  hb: {D1.below(pp, D1.half(Nat.add(xx, ee))) == True{} : Bool}
) -> &ff: Nat -> {D1.below(pp, Nat.add(D1.half(xx), ff)) == True{} : Bool}:
  (ff, eh) = pr
  (ff, Equal.trans(Bool, D1.below(pp, Nat.add(D1.half(xx), ff)), D1.below(pp, D1.half(Nat.add(xx, ee))), True{},
    Equal.cong(Nat, Bool, zz => D1.below(pp, zz), Nat.add(D1.half(xx), ff), D1.half(Nat.add(xx, ee)),
      Equal.sym(Nat, D1.half(Nat.add(xx, ee)), Nat.add(D1.half(xx), ff), eh)), hb))

# the witness taken out, the rest of below_mono is the call it is given
def below_mono.go(
  +pp: Nat,
  +hx: Nat,
  pr: &ff: Nat -> {D1.below(pp, Nat.add(hx, ff)) == True{} : Bool},
  ih: @ff: Nat -> {D1.below(pp, Nat.add(hx, ff)) == True{} : Bool} -> {D1.below(pp, hx) == True{} : Bool}
) -> {D1.below(pp, hx) == True{} : Bool}:
  (ff, hf) = pr
  ih(ff, hf)

# a number below 2^n with something added keeps its part below 2^n
law below_mono:
  for +nn: Nat
  for +xx: Nat
  for +ee: Nat
  for +hb: {D1.below(nn, Nat.add(xx, ee)) == True{} : Bool}
  {D1.below(nn, xx) == True{} : Bool}

# the proof of below_mono
def below_mono(nn, xx, ee, hb):
  match nn:
    case 0n:
      match xx:
        case 0n:
          {==}
        case 1n+(+qx):
          Empty.absurd({D1.below(0n, 1n+qx) == True{} : Bool}, M1.false_true(hb))
    case 1n+(+pp):
      below_mono.go(pp, D1.half(xx), below_mono.half(pp, xx, ee, half_add(xx, ee), hb), ff => hf =>
        below_mono(pp, D1.half(xx), ff, hf))

# a split one level down, one more on both sides of the second equation
def split.up(
  +dd: Nat,
  +xx: Nat,
  +yy: Nat,
  +ds: Nat,
  pr: {dd == ds : Nat} & {xx == yy : Nat}
) -> {dd == ds : Nat} & {1n+xx == 1n+yy : Nat}:
  (ed, ex) = pr
  (ed, Equal.cong(Nat, Nat, zz => 1n+zz, xx, yy, ex))

# double x is double y and d: d is even, and x is y and half of d
law split_even:
  for +yy: Nat
  for +xx: Nat
  for +dd: Nat
  for +hh: {Nat.double(xx) == Nat.add(Nat.double(yy), dd) : Nat}
  {dd == Nat.double(D1.half(dd)) : Nat} & {xx == Nat.add(yy, D1.half(dd)) : Nat}

# the proof of split_even
def split_even(yy, xx, dd, hh):
  match yy:
    case 0n:
      +eh = {Equal.trans(Nat, D1.half(dd), D1.half(Nat.double(xx)), xx,
        Equal.cong(Nat, Nat, zz => D1.half(zz), dd, Nat.double(xx), Equal.sym(Nat, Nat.double(xx), dd, hh)),
        half_double(xx)) : {D1.half(dd) == xx : Nat}}
      (Equal.trans(Nat, dd, Nat.double(xx), Nat.double(D1.half(dd)), Equal.sym(Nat, Nat.double(xx), dd, hh),
        Equal.cong(Nat, Nat, zz => Nat.double(zz), xx, D1.half(dd), Equal.sym(Nat, D1.half(dd), xx, eh))),
        Equal.sym(Nat, D1.half(dd), xx, eh))
    case 1n+(+qy):
      match xx:
        case 0n:
          Empty.absurd({dd == Nat.double(D1.half(dd)) : Nat} & {0n == Nat.add(1n+qy, D1.half(dd)) : Nat},
            penc.zero_succ(1n+Nat.add(Nat.double(qy), dd), hh))
        case 1n+(+qx):
          +h2 = penc.succ_inj(Nat.double(qx), Nat.add(Nat.double(qy), dd),
            penc.succ_inj(1n+Nat.double(qx), 1n+Nat.add(Nat.double(qy), dd), hh))
          split.up(dd, qx, Nat.add(qy, D1.half(dd)), Nat.double(D1.half(dd)), split_even(qy, qx, dd, h2))

# double x is 1 and double y and d: d is odd, and x is 1, y and half of d
law split_odd:
  for +yy: Nat
  for +xx: Nat
  for +dd: Nat
  for +hh: {Nat.double(xx) == 1n+Nat.add(Nat.double(yy), dd) : Nat}
  {dd == 1n+Nat.double(D1.half(dd)) : Nat} & {xx == 1n+Nat.add(yy, D1.half(dd)) : Nat}

# the proof of split_odd
def split_odd(yy, xx, dd, hh):
  match yy xx:
    case _yy 0n:
      Empty.absurd({dd == 1n+Nat.double(D1.half(dd)) : Nat} & {0n == 1n+Nat.add(_yy, D1.half(dd)) : Nat},
        penc.zero_succ(Nat.add(Nat.double(_yy), dd), hh))
    case 0n 1n+(+qx):
      +h2 = {penc.succ_inj(1n+Nat.double(qx), dd, hh) : {1n+Nat.double(qx) == dd : Nat}}
      +eh = {Equal.trans(Nat, D1.half(dd), D1.half(1n+Nat.double(qx)), qx,
        Equal.cong(Nat, Nat, zz => D1.half(zz), dd, 1n+Nat.double(qx), Equal.sym(Nat, 1n+Nat.double(qx), dd, h2)),
        half_odd(qx)) : {D1.half(dd) == qx : Nat}}
      (Equal.trans(Nat, dd, 1n+Nat.double(qx), 1n+Nat.double(D1.half(dd)), Equal.sym(Nat, 1n+Nat.double(qx), dd, h2),
        Equal.cong(Nat, Nat, zz => 1n+Nat.double(zz), qx, D1.half(dd), Equal.sym(Nat, D1.half(dd), qx, eh))),
        Equal.cong(Nat, Nat, zz => 1n+zz, qx, D1.half(dd), Equal.sym(Nat, D1.half(dd), qx, eh)))
    case 1n+(+qy) 1n+(+qx):
      +h2 = penc.succ_inj(Nat.double(qx), 1n+Nat.add(Nat.double(qy), dd),
        penc.succ_inj(1n+Nat.double(qx), 1n+1n+Nat.add(Nat.double(qy), dd), hh))
      split.up(dd, qx, 1n+Nat.add(qy, D1.half(dd)), 1n+Nat.double(D1.half(dd)), split_odd(qy, qx, dd, h2))

# 1 and double x is double y and d: d is odd, and x is y and half of d
law split_odd2:
  for +yy: Nat
  for +xx: Nat
  for +dd: Nat
  for +hh: {1n+Nat.double(xx) == Nat.add(Nat.double(yy), dd) : Nat}
  {dd == 1n+Nat.double(D1.half(dd)) : Nat} & {xx == Nat.add(yy, D1.half(dd)) : Nat}

# the proof of split_odd2
def split_odd2(yy, xx, dd, hh):
  match yy:
    case 0n:
      +eh = {Equal.trans(Nat, D1.half(dd), D1.half(1n+Nat.double(xx)), xx,
        Equal.cong(Nat, Nat, zz => D1.half(zz), dd, 1n+Nat.double(xx), Equal.sym(Nat, 1n+Nat.double(xx), dd, hh)),
        half_odd(xx)) : {D1.half(dd) == xx : Nat}}
      (Equal.trans(Nat, dd, 1n+Nat.double(xx), 1n+Nat.double(D1.half(dd)), Equal.sym(Nat, 1n+Nat.double(xx), dd, hh),
        Equal.cong(Nat, Nat, zz => 1n+Nat.double(zz), xx, D1.half(dd), Equal.sym(Nat, D1.half(dd), xx, eh))),
        Equal.sym(Nat, D1.half(dd), xx, eh))
    case 1n+(+qy):
      match xx:
        case 0n:
          Empty.absurd({dd == 1n+Nat.double(D1.half(dd)) : Nat} & {0n == Nat.add(1n+qy, D1.half(dd)) : Nat},
            penc.zero_succ(Nat.add(Nat.double(qy), dd), penc.succ_inj(0n, 1n+Nat.add(Nat.double(qy), dd), hh)))
        case 1n+(+qx):
          +h2 = penc.succ_inj(1n+Nat.double(qx), Nat.add(Nat.double(qy), dd),
            penc.succ_inj(1n+1n+Nat.double(qx), 1n+Nat.add(Nat.double(qy), dd), hh))
          split.up(dd, qx, Nat.add(qy, D1.half(dd)), 1n+Nat.double(D1.half(dd)), split_odd2(qy, qx, dd, h2))

# ---- words ----

# the value of a word whose low bit is b and whose rest is x
def dig(bb: Bool, xx: Nat) -> Nat:
  match bb:
    case False{}:
      Nat.double(xx)
    case True{}:
      1n+Nat.double(xx)

# the order of two digits: the rest first, then the low bits
law nat_cmp_dig:
  for +xx: Nat
  for +yy: Nat
  for +ab: Bool
  for +bb: Bool
  {Nat.cmp(dig(ab, xx), dig(bb, yy)) == Word.cmp.fin(ab, bb, Nat.cmp(xx, yy)) : Cmp}

# the proof of nat_cmp_dig
def nat_cmp_dig(xx, yy, ab, bb):
  match xx yy ab bb:
    case 0n 0n False{} False{}:
      {==}
    case 0n 0n False{} True{}:
      {==}
    case 0n 0n True{} False{}:
      {==}
    case 0n 0n True{} True{}:
      {==}
    case 0n 1n+_qy False{} False{}:
      {==}
    case 0n 1n+_qy False{} True{}:
      {==}
    case 0n 1n+_qy True{} False{}:
      {==}
    case 0n 1n+_qy True{} True{}:
      {==}
    case 1n+_qx 0n False{} False{}:
      {==}
    case 1n+_qx 0n False{} True{}:
      {==}
    case 1n+_qx 0n True{} False{}:
      {==}
    case 1n+_qx 0n True{} True{}:
      {==}
    case 1n+(+qx) 1n+(+qy) False{} False{}:
      nat_cmp_dig(qx, qy, False{}, False{})
    case 1n+(+qx) 1n+(+qy) False{} True{}:
      nat_cmp_dig(qx, qy, False{}, True{})
    case 1n+(+qx) 1n+(+qy) True{} False{}:
      nat_cmp_dig(qx, qy, True{}, False{})
    case 1n+(+qx) 1n+(+qy) True{} True{}:
      nat_cmp_dig(qx, qy, True{}, True{})

# a word's value is the digit of its low bit and the rest
law word_dig:
  for +pp: Nat
  for +bb: Bool
  for +tt: Word(pp)
  {Word.to_nat(1n+pp, WCon{bb, tt}) == dig(bb, Word.to_nat(pp, tt)) : Nat}

# the proof of word_dig
def word_dig(_pp, bb, _tt):
  match bb:
    case False{}:
      {==}
    case True{}:
      {==}

# words compare as their values do
law word_cmp_nat:
  for +nn: Nat
  for +aw: Word(nn)
  for +bw: Word(nn)
  {Word.cmp(nn, aw, bw) == Nat.cmp(Word.to_nat(nn, aw), Word.to_nat(nn, bw)) : Cmp}

# the proof of word_cmp_nat
def word_cmp_nat(nn, aw, bw):
  match nn:
    case 0n:
      match aw bw:
        case WNil{} WNil{}:
          {==}
    case 1n+(+pp):
      match aw bw:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          +va = Word.to_nat(pp, at)
          +vb = Word.to_nat(pp, bt)
          Equal.trans(Cmp, Word.cmp.fin(ab, bb, Word.cmp(pp, at, bt)), Word.cmp.fin(ab, bb, Nat.cmp(va, vb)),
            Nat.cmp(Word.to_nat(1n+pp, WCon{ab, at}), Word.to_nat(1n+pp, WCon{bb, bt})),
            Equal.cong(Cmp, Cmp, cc => Word.cmp.fin(ab, bb, cc), Word.cmp(pp, at, bt), Nat.cmp(va, vb),
              word_cmp_nat(pp, at, bt)),
            Equal.trans(Cmp, Word.cmp.fin(ab, bb, Nat.cmp(va, vb)), Nat.cmp(dig(ab, va), dig(bb, vb)),
              Nat.cmp(Word.to_nat(1n+pp, WCon{ab, at}), Word.to_nat(1n+pp, WCon{bb, bt})),
              Equal.sym(Cmp, Nat.cmp(dig(ab, va), dig(bb, vb)), Word.cmp.fin(ab, bb, Nat.cmp(va, vb)),
                nat_cmp_dig(va, vb, ab, bb)),
              Equal.trans(Cmp, Nat.cmp(dig(ab, va), dig(bb, vb)),
                Nat.cmp(Word.to_nat(1n+pp, WCon{ab, at}), dig(bb, vb)),
                Nat.cmp(Word.to_nat(1n+pp, WCon{ab, at}), Word.to_nat(1n+pp, WCon{bb, bt})),
                Equal.cong(Nat, Cmp, xx => Nat.cmp(xx, dig(bb, vb)), dig(ab, va), Word.to_nat(1n+pp, WCon{ab, at}),
                  Equal.sym(Nat, Word.to_nat(1n+pp, WCon{ab, at}), dig(ab, va), word_dig(pp, ab, at))),
                Equal.cong(Nat, Cmp, yy => Nat.cmp(Word.to_nat(1n+pp, WCon{ab, at}), yy), dig(bb, vb),
                  Word.to_nat(1n+pp, WCon{bb, bt}),
                  Equal.sym(Nat, Word.to_nat(1n+pp, WCon{bb, bt}), dig(bb, vb), word_dig(pp, bb, bt))))))

# the value of a carry bit
def bitv(cc: Bool) -> Nat:
  match cc:
    case False{}:
      0n
    case True{}:
      1n

# an odd digit is the value it was split from
def dig.odd(
  +rr: Nat,
  +dd: Nat,
  er: {rr == D1.half(dd) : Nat},
  ed: {dd == 1n+Nat.double(D1.half(dd)) : Nat}
) -> {1n+Nat.double(rr) == dd : Nat}:
  Equal.trans(Nat, 1n+Nat.double(rr), 1n+Nat.double(D1.half(dd)), dd,
    Equal.cong(Nat, Nat, zz => 1n+Nat.double(zz), rr, D1.half(dd), er),
    Equal.sym(Nat, dd, 1n+Nat.double(D1.half(dd)), ed))

# an even digit is the value it was split from
def dig.even(
  +rr: Nat,
  +dd: Nat,
  er: {rr == D1.half(dd) : Nat},
  ed: {dd == Nat.double(D1.half(dd)) : Nat}
) -> {Nat.double(rr) == dd : Nat}:
  Equal.trans(Nat, Nat.double(rr), Nat.double(D1.half(dd)), dd,
    Equal.cong(Nat, Nat, zz => Nat.double(zz), rr, D1.half(dd), er),
    Equal.sym(Nat, dd, Nat.double(D1.half(dd)), ed))

# what word_sub proves one level down, for any borrow and difference
def sub.ih(+pp: Nat, +at: Word(pp), +bt: Word(pp)) -> Type:
  @kk: Bool -> @dd: Nat -> {Word.to_nat(pp, at) == Nat.add(M1.nb(kk), Nat.add(Word.to_nat(pp, bt), dd)) : Nat} ->
    {Word.to_nat(pp, Word.adc(pp, at, bt, True{}, kk)) == dd : Nat}

# d split as the digit ds, and a less the borrow and b is half of d
def sub.split(+pp: Nat, +at: Word(pp), +bt: Word(pp), +kk: Bool, +dd: Nat, +ds: Nat) -> Type:
  {dd == ds : Nat} & {Word.to_nat(pp, at) == Nat.add(M1.nb(kk), Nat.add(Word.to_nat(pp, bt), D1.half(dd))) : Nat}

# an odd split: the low bit is 1, the rest is the rest of the difference
def sub.odd(
  +pp: Nat,
  +at: Word(pp),
  +bt: Word(pp),
  +kk: Bool,
  +dd: Nat,
  ih: sub.ih(pp, at, bt),
  pr: sub.split(pp, at, bt, kk, dd, 1n+Nat.double(D1.half(dd)))
) -> {1n+Nat.double(Word.to_nat(pp, Word.adc(pp, at, bt, True{}, kk))) == dd : Nat}:
  (ed, ex) = pr
  dig.odd(Word.to_nat(pp, Word.adc(pp, at, bt, True{}, kk)), dd, ih(kk, D1.half(dd), ex), ed)

# an even split: the low bit is 0, the rest is the rest of the difference
def sub.even(
  +pp: Nat,
  +at: Word(pp),
  +bt: Word(pp),
  +kk: Bool,
  +dd: Nat,
  ih: sub.ih(pp, at, bt),
  pr: sub.split(pp, at, bt, kk, dd, Nat.double(D1.half(dd)))
) -> {Nat.double(Word.to_nat(pp, Word.adc(pp, at, bt, True{}, kk))) == dd : Nat}:
  (ed, ex) = pr
  dig.even(Word.to_nat(pp, Word.adc(pp, at, bt, True{}, kk)), dd, ih(kk, D1.half(dd), ex), ed)

# one bit of a subtraction: each low bit and borrow, the split that fits it
def sub.step(
  +pp: Nat,
  ab: Bool,
  bb: Bool,
  cc: Bool,
  +at: Word(pp),
  +bt: Word(pp),
  +dd: Nat,
  hd: {Word.to_nat(1n+pp, WCon{ab, at}) == Nat.add(M1.nb(cc), Nat.add(Word.to_nat(1n+pp, WCon{bb, bt}), dd)) : Nat},
  ih: sub.ih(pp, at, bt)
) -> {Word.to_nat(1n+pp, Word.adc(1n+pp, WCon{ab, at}, WCon{bb, bt}, True{}, cc)) == dd : Nat}:
  match ab bb cc:
    case False{} False{} False{}:
      sub.odd(pp, at, bt, False{}, dd, ih, split_odd(Word.to_nat(pp, bt), Word.to_nat(pp, at), dd, hd))
    case False{} False{} True{}:
      sub.even(pp, at, bt, True{}, dd, ih, split_even(Word.to_nat(pp, bt), Word.to_nat(pp, at), dd, hd))
    case False{} True{} False{}:
      sub.even(pp, at, bt, False{}, dd, ih, split_even(1n+Word.to_nat(pp, bt), Word.to_nat(pp, at), dd, hd))
    case False{} True{} True{}:
      sub.odd(pp, at, bt, False{}, dd, ih, split_odd(Word.to_nat(pp, bt), Word.to_nat(pp, at), dd, hd))
    case True{} False{} False{}:
      sub.even(pp, at, bt, True{}, dd, ih,
        split_even(Word.to_nat(pp, bt), Word.to_nat(pp, at), dd, penc.succ_inj(Nat.double(Word.to_nat(pp, at)),
          Nat.add(Nat.double(Word.to_nat(pp, bt)), dd), hd)))
    case True{} False{} True{}:
      sub.odd(pp, at, bt, True{}, dd, ih, split_odd2(Word.to_nat(pp, bt), Word.to_nat(pp, at), dd, hd))
    case True{} True{} False{}:
      sub.odd(pp, at, bt, False{}, dd, ih,
        split_odd(Word.to_nat(pp, bt), Word.to_nat(pp, at), dd, penc.succ_inj(Nat.double(Word.to_nat(pp, at)),
          1n+Nat.add(Nat.double(Word.to_nat(pp, bt)), dd), hd)))
    case True{} True{} True{}:
      sub.even(pp, at, bt, True{}, dd, ih,
        split_even(Word.to_nat(pp, bt), Word.to_nat(pp, at), dd, penc.succ_inj(Nat.double(Word.to_nat(pp, at)),
          Nat.add(Nat.double(Word.to_nat(pp, bt)), dd), hd)))

# no borrow into a word of no bits: the difference is 0
def sub.nil(
  cc: Bool,
  +dd: Nat,
  hd: {0n == Nat.add(M1.nb(cc), Nat.add(0n, dd)) : Nat}
) -> {0n == dd : Nat}:
  match cc:
    case True{}:
      hd
    case False{}:
      Empty.absurd({0n == dd : Nat}, penc.zero_succ(dd, hd))

# a word minus a word, borrow c in, whose value is a - b - (1 - c) = d, is d
law word_sub:
  for +nn: Nat
  for +aw: Word(nn)
  for +bw: Word(nn)
  for +cc: Bool
  for +dd: Nat
  for +hd: {Word.to_nat(nn, aw) == Nat.add(M1.nb(cc), Nat.add(Word.to_nat(nn, bw), dd)) : Nat}
  {Word.to_nat(nn, Word.adc(nn, aw, bw, True{}, cc)) == dd : Nat}

# the proof of word_sub
def word_sub(nn, aw, bw, cc, dd, hd):
  match nn:
    case 0n:
      match aw bw:
        case WNil{} WNil{}:
          sub.nil(cc, dd, hd)
    case 1n+(+pp):
      match aw bw:
        case WCon{ab, +at} WCon{bb, +bt}:
          sub.step(pp, ab, bb, cc, at, bt, dd, hd, kk => d2 => h2 => word_sub(pp, at, bt, kk, d2, h2))

# what word_carry proves one level down, for any carry and sum
def carry.ih(+pp: Nat, +xt: Word(pp)) -> Type:
  @kk: Bool -> @dd: Nat -> {Nat.add(bitv(kk), Word.to_nat(pp, xt)) == dd : Nat} ->
    {D1.below(pp, dd) == True{} : Bool} ->
    {Word.to_nat(pp, Word.adc(pp, xt, Word.zero(pp), False{}, kk)) == dd : Nat}

# the carry into the next bit, and half the sum is what the rest must make
def carry.even(
  +pp: Nat,
  +xt: Word(pp),
  +kk: Bool,
  +dd: Nat,
  ih: carry.ih(pp, xt),
  eh: {D1.half(dd) == Nat.add(bitv(kk), Word.to_nat(pp, xt)) : Nat},
  ed: {dd == Nat.double(D1.half(dd)) : Nat},
  hb: {D1.below(pp, D1.half(dd)) == True{} : Bool}
) -> {Nat.double(Word.to_nat(pp, Word.adc(pp, xt, Word.zero(pp), False{}, kk))) == dd : Nat}:
  +hs = Equal.sym(Nat, D1.half(dd), Nat.add(bitv(kk), Word.to_nat(pp, xt)), eh)
  dig.even(Word.to_nat(pp, Word.adc(pp, xt, Word.zero(pp), False{}, kk)), dd,
    ih(kk, D1.half(dd), hs, hb), ed)

# the same with the low bit 1
def carry.odd(
  +pp: Nat,
  +xt: Word(pp),
  +kk: Bool,
  +dd: Nat,
  ih: carry.ih(pp, xt),
  eh: {D1.half(dd) == Nat.add(bitv(kk), Word.to_nat(pp, xt)) : Nat},
  ed: {dd == 1n+Nat.double(D1.half(dd)) : Nat},
  hb: {D1.below(pp, D1.half(dd)) == True{} : Bool}
) -> {1n+Nat.double(Word.to_nat(pp, Word.adc(pp, xt, Word.zero(pp), False{}, kk))) == dd : Nat}:
  +hs = Equal.sym(Nat, D1.half(dd), Nat.add(bitv(kk), Word.to_nat(pp, xt)), eh)
  dig.odd(Word.to_nat(pp, Word.adc(pp, xt, Word.zero(pp), False{}, kk)), dd,
    ih(kk, D1.half(dd), hs, hb), ed)

# half of d, from d written as a digit
def half.of(
  +dd: Nat,
  +xx: Nat,
  +yy: Nat,
  hd: {xx == dd : Nat},
  eh: {D1.half(xx) == yy : Nat}
) -> {D1.half(dd) == yy : Nat}:
  Equal.trans(Nat, D1.half(dd), D1.half(xx), yy,
    Equal.cong(Nat, Nat, zz => D1.half(zz), dd, xx, Equal.sym(Nat, xx, dd, hd)), eh)

# d, even, written back from its half
def even.back(
  +dd: Nat,
  +yy: Nat,
  hd: {Nat.double(yy) == dd : Nat},
  eh: {D1.half(dd) == yy : Nat}
) -> {dd == Nat.double(D1.half(dd)) : Nat}:
  Equal.trans(Nat, dd, Nat.double(yy), Nat.double(D1.half(dd)), Equal.sym(Nat, Nat.double(yy), dd, hd),
    Equal.cong(Nat, Nat, zz => Nat.double(zz), yy, D1.half(dd), Equal.sym(Nat, D1.half(dd), yy, eh)))

# d, odd, written back from its half
def odd.back(
  +dd: Nat,
  +yy: Nat,
  hd: {1n+Nat.double(yy) == dd : Nat},
  eh: {D1.half(dd) == yy : Nat}
) -> {dd == 1n+Nat.double(D1.half(dd)) : Nat}:
  Equal.trans(Nat, dd, 1n+Nat.double(yy), 1n+Nat.double(D1.half(dd)), Equal.sym(Nat, 1n+Nat.double(yy), dd, hd),
    Equal.cong(Nat, Nat, zz => 1n+Nat.double(zz), yy, D1.half(dd), Equal.sym(Nat, D1.half(dd), yy, eh)))

# one bit of adding a carry: each low bit and carry in
def carry.step(
  +pp: Nat,
  xb: Bool,
  cc: Bool,
  +xt: Word(pp),
  +dd: Nat,
  +hd: {Nat.add(bitv(cc), Word.to_nat(1n+pp, WCon{xb, xt})) == dd : Nat},
  hb: {D1.below(1n+pp, dd) == True{} : Bool},
  ih: carry.ih(pp, xt)
) -> {Word.to_nat(1n+pp, Word.adc(1n+pp, WCon{xb, xt}, Word.zero(1n+pp), False{}, cc)) == dd : Nat}:
  match xb cc:
    case False{} False{}:
      +eh = {half.of(dd, Nat.double(Word.to_nat(pp, xt)), Word.to_nat(pp, xt), hd, half_double(Word.to_nat(pp, xt))) :
        {D1.half(dd) == Word.to_nat(pp, xt) : Nat}}
      carry.even(pp, xt, False{}, dd, ih, eh, even.back(dd, Word.to_nat(pp, xt), hd, eh), hb)
    case False{} True{}:
      +eh = {half.of(dd, 1n+Nat.double(Word.to_nat(pp, xt)), Word.to_nat(pp, xt), hd, half_odd(Word.to_nat(pp, xt))) :
        {D1.half(dd) == Word.to_nat(pp, xt) : Nat}}
      carry.odd(pp, xt, False{}, dd, ih, eh, odd.back(dd, Word.to_nat(pp, xt), hd, eh), hb)
    case True{} False{}:
      +eh = {half.of(dd, 1n+Nat.double(Word.to_nat(pp, xt)), Word.to_nat(pp, xt), hd, half_odd(Word.to_nat(pp, xt))) :
        {D1.half(dd) == Word.to_nat(pp, xt) : Nat}}
      carry.odd(pp, xt, False{}, dd, ih, eh, odd.back(dd, Word.to_nat(pp, xt), hd, eh), hb)
    case True{} True{}:
      +eh = {half.of(dd, Nat.double(1n+Word.to_nat(pp, xt)), 1n+Word.to_nat(pp, xt), hd,
        half_double(1n+Word.to_nat(pp, xt))) : {D1.half(dd) == 1n+Word.to_nat(pp, xt) : Nat}}
      carry.even(pp, xt, True{}, dd, ih, eh, even.back(dd, 1n+Word.to_nat(pp, xt), hd, eh), hb)

# adding a carry to a word of no bits: the sum is below 1, so it is 0
def carry.nil(
  _cc: Bool,
  +dd: Nat,
  hb: {Nat.is_eq(dd, 0n) == True{} : Bool}
) -> {0n == dd : Nat}:
  Equal.sym(Nat, dd, 0n, nat_eq_true(dd, 0n, hb))

# a word and a carry c, whose sum d is below 2^n, add up to d
law word_carry:
  for +nn: Nat
  for +xw: Word(nn)
  for +cc: Bool
  for +dd: Nat
  for +hd: {Nat.add(bitv(cc), Word.to_nat(nn, xw)) == dd : Nat}
  for +hb: {D1.below(nn, dd) == True{} : Bool}
  {Word.to_nat(nn, Word.adc(nn, xw, Word.zero(nn), False{}, cc)) == dd : Nat}

# the proof of word_carry
def word_carry(nn, xw, cc, dd, hd, hb):
  match nn:
    case 0n:
      match xw:
        case WNil{}:
          carry.nil(cc, dd, hb)
    case 1n+(+pp):
      match xw:
        case WCon{xb, +xt}:
          carry.step(pp, xb, cc, xt, dd, hd, hb, kk => d2 => h2 => b2 => word_carry(pp, xt, kk, d2, h2, b2))

# ---- U32 ----

# U32s compare as their values do
law u32_cmp_nat:
  for +aa: U32
  for +bb: U32
  {U32.cmp(aa, bb) == Nat.cmp(U32.to_nat(aa), U32.to_nat(bb)) : Cmp}

# the proof of u32_cmp_nat
def u32_cmp_nat(aa, bb):
  match aa bb:
    case U32{+xw} U32{+yw}:
      word_cmp_nat(32n, xw, yw)

# a U32 minus a U32 it is at least is the difference
law u32_sub_nat:
  for +aa: U32
  for +bb: U32
  for +dd: Nat
  for +hd: {U32.to_nat(aa) == Nat.add(U32.to_nat(bb), dd) : Nat}
  {U32.to_nat((aa - bb : U32)) == dd : Nat}

# the proof of u32_sub_nat
def u32_sub_nat(aa, bb, dd, hd):
  match aa bb:
    case U32{+xw} U32{+yw}:
      word_sub(32n, xw, yw, True{}, dd, hd)

# a U32 plus 1, below 2^32, is one more
law u32_inc_nat:
  for +aa: U32
  for +hb: {D1.below(32n, 1n+U32.to_nat(aa)) == True{} : Bool}
  {U32.to_nat((aa + 1 : U32)) == 1n+U32.to_nat(aa) : Nat}

# the proof of u32_inc_nat
def u32_inc_nat(aa, hb):
  match aa:
    case U32{WCon{False{}, +xt}}:
      +vt = Word.to_nat(31n, xt)
      +b2 = {Equal.trans(Bool, D1.below(31n, vt), D1.below(31n, D1.half(1n+Nat.double(vt))), True{},
        Equal.cong(Nat, Bool, zz => D1.below(31n, zz), vt, D1.half(1n+Nat.double(vt)),
          Equal.sym(Nat, D1.half(1n+Nat.double(vt)), vt, half_odd(vt))), hb) : {D1.below(31n, vt) == True{} : Bool}}
      Equal.cong(Nat, Nat, zz => 1n+Nat.double(zz),
        Word.to_nat(31n, Word.adc(31n, xt, Word.zero(31n), False{}, False{})),
        vt, word_carry(31n, xt, False{}, vt, {==}, b2))
    case U32{WCon{True{}, +xt}}:
      +vt = Word.to_nat(31n, xt)
      +b2 = {Equal.trans(Bool, D1.below(31n, 1n+vt), D1.below(31n, 1n+D1.half(Nat.double(vt))), True{},
        Equal.cong(Nat, Bool, zz => D1.below(31n, 1n+zz), vt, D1.half(Nat.double(vt)),
          Equal.sym(Nat, D1.half(Nat.double(vt)), vt, half_double(vt))), hb) :
        {D1.below(31n, 1n+vt) == True{} : Bool}}
      Equal.cong(Nat, Nat, zz => Nat.double(zz), Word.to_nat(31n, Word.adc(31n, xt, Word.zero(31n), False{}, True{})),
        1n+vt, word_carry(31n, xt, True{}, 1n+vt, {==}, b2))

# U32.is_lt as Nat order
def lt.nat(
  +cc: U32,
  +ww: U32,
  zz: Bool,
  ee: {U32.is_lt(cc, ww) == zz : Bool}
) -> {Cmp.is_lt(Nat.cmp(U32.to_nat(cc), U32.to_nat(ww))) == zz : Bool}:
  Equal.trans(Bool, Cmp.is_lt(Nat.cmp(U32.to_nat(cc), U32.to_nat(ww))), U32.is_lt(cc, ww), zz,
    Equal.cong(Cmp, Bool, xx => Cmp.is_lt(xx), Nat.cmp(U32.to_nat(cc), U32.to_nat(ww)), U32.cmp(cc, ww),
      Equal.sym(Cmp, U32.cmp(cc, ww), Nat.cmp(U32.to_nat(cc), U32.to_nat(ww)), u32_cmp_nat(cc, ww))), ee)

# U32.is_zero as Nat equality with 0
def zero.nat(
  +hh: U32,
  zz: Bool,
  ee: {U32.is_zero(hh) == zz : Bool}
) -> {Cmp.is_eq(Nat.cmp(U32.to_nat(hh), 0n)) == zz : Bool}:
  Equal.trans(Bool, Cmp.is_eq(Nat.cmp(U32.to_nat(hh), 0n)), U32.is_zero(hh), zz,
    Equal.cong(Cmp, Bool, xx => Cmp.is_eq(xx), Nat.cmp(U32.to_nat(hh), 0n), U32.cmp(hh, 0),
      Equal.sym(Cmp, U32.cmp(hh, 0), Nat.cmp(U32.to_nat(hh), 0n), u32_cmp_nat(hh, 0))), ee)

# the count and the rows, rewritten: the question the walk answers is the same
def iseq.mul(
  +aa: Nat,
  +ab: Nat,
  +ha: Nat,
  +hb: Nat,
  +ww: Nat,
  ea: {aa == ab : Nat},
  eh: {ha == hb : Nat}
) -> {Nat.is_eq(aa, Nat.mul(ha, ww)) == Nat.is_eq(ab, Nat.mul(hb, ww)) : Bool}:
  Equal.trans(Bool, Nat.is_eq(aa, Nat.mul(ha, ww)), Nat.is_eq(ab, Nat.mul(ha, ww)), Nat.is_eq(ab, Nat.mul(hb, ww)),
    Equal.cong(Nat, Bool, xx => Nat.is_eq(xx, Nat.mul(ha, ww)), aa, ab, ea),
    Equal.cong(Nat, Bool, xx => Nat.is_eq(ab, Nat.mul(xx, ww)), ha, hb, eh))

# no rows left: the walk asks whether c is 0, and 0 rows of w is 0
def rows.done(
  +hh: U32,
  +cc: U32,
  +ww: U32,
  e_zh: {U32.is_zero(hh) == True{} : Bool}
) -> {U32.is_zero(cc) == Nat.is_eq(U32.to_nat(cc), Nat.mul(U32.to_nat(hh), U32.to_nat(ww))) : Bool}:
  +e0 = {M1.ueq(hh, 0, e_zh) : {hh == 0 : U32}}
  Equal.trans(Bool, U32.is_zero(cc), Nat.is_eq(U32.to_nat(cc), Nat.mul(U32.to_nat(0), U32.to_nat(ww))),
    Nat.is_eq(U32.to_nat(cc), Nat.mul(U32.to_nat(hh), U32.to_nat(ww))),
    Equal.sym(Bool, Cmp.is_eq(Nat.cmp(U32.to_nat(cc), 0n)), U32.is_zero(cc), zero.nat(cc, U32.is_zero(cc), {==})),
    Equal.cong(U32, Bool, uu => Nat.is_eq(U32.to_nat(cc), Nat.mul(U32.to_nat(uu), U32.to_nat(ww))), 0, hh,
      Equal.sym(U32, hh, 0, e0)))

# a row left and fewer than w samples: never h rows of w
def rows.short.go(
  +cc: Nat,
  +hh: Nat,
  +ww: Nat,
  pr: &hp: Nat -> {hh == 1n+hp : Nat},
  hl: {Cmp.is_lt(Nat.cmp(cc, ww)) == True{} : Bool}
) -> {False{} == Nat.is_eq(cc, Nat.mul(hh, ww)) : Bool}:
  (hp, e_h) = pr
  Equal.trans(Bool, False{}, Nat.is_eq(cc, Nat.mul(1n+hp, ww)), Nat.is_eq(cc, Nat.mul(hh, ww)),
    Equal.sym(Bool, Nat.is_eq(cc, Nat.add(ww, Nat.mul(hp, ww))), False{}, lt_add(cc, ww, Nat.mul(hp, ww), hl)),
    Equal.cong(Nat, Bool, xx => Nat.is_eq(cc, Nat.mul(xx, ww)), 1n+hp, hh, Equal.sym(Nat, hh, 1n+hp, e_h)))

# a row left and fewer than w samples
def rows.short(
  +hh: U32,
  +cc: U32,
  +ww: U32,
  e_zh: {U32.is_zero(hh) == False{} : Bool},
  e_zlt: {U32.is_lt(cc, ww) == True{} : Bool}
) -> {False{} == Nat.is_eq(U32.to_nat(cc), Nat.mul(U32.to_nat(hh), U32.to_nat(ww))) : Bool}:
  rows.short.go(U32.to_nat(cc), U32.to_nat(hh), U32.to_nat(ww),
    nat_pos(U32.to_nat(hh), zero.nat(hh, False{}, e_zh)), lt.nat(cc, ww, True{}, e_zlt))

# the fuel ran out with c at least w: c is 0 then, and w is not
def rows.nil(
  +cc: Nat,
  +ef: Nat,
  +wp: Nat,
  hl: {Cmp.is_lt(Nat.cmp(cc, 1n+wp)) == False{} : Bool},
  e0: {0n == Nat.add(cc, ef) : Nat}
) -> Empty:
  match cc:
    case 0n:
      M1.false_true(Equal.sym(Bool, True{}, False{}, hl))
    case 1n+(+qc):
      penc.zero_succ(Nat.add(qc, ef), e0)

# what the walk proves of the rest, for any slack in the fuel
def rows.ih(
  rest: List<&2, U32>,
  +ww: U32,
  +c2: U32,
  +h2: U32
) -> Type:
  @ef2: Nat -> {List.length(&2, U32, rest) == Nat.add(U32.to_nat(c2), ef2) : Nat} ->
    {Png.enc.rows(rest, U32.is_zero(h2), U32.is_lt(c2, ww), ww, h2, c2) ==
      Nat.is_eq(U32.to_nat(c2), Nat.mul(U32.to_nat(h2), U32.to_nat(ww))) : Bool}

# the fuel left after one row: w - 1 more than the count left
def rows.fuel(
  +rl: Nat,
  +wp: Nat,
  +dd: Nat,
  +ef: Nat,
  ee: {1n+rl == Nat.add(Nat.add(1n+wp, dd), ef) : Nat}
) -> {rl == Nat.add(dd, Nat.add(ef, wp)) : Nat}:
  +e1 = {penc.succ_inj(rl, Nat.add(Nat.add(wp, dd), ef), ee) : {rl == Nat.add(Nat.add(wp, dd), ef) : Nat}}
  Equal.trans(Nat, rl, Nat.add(Nat.add(wp, dd), ef), Nat.add(dd, Nat.add(ef, wp)), e1,
    Equal.trans(Nat, Nat.add(Nat.add(wp, dd), ef), Nat.add(Nat.add(dd, wp), ef), Nat.add(dd, Nat.add(ef, wp)),
      Equal.cong(Nat, Nat, xx => Nat.add(xx, ef), Nat.add(wp, dd), Nat.add(dd, wp), add_comm(wp, dd)),
      Equal.trans(Nat, Nat.add(Nat.add(dd, wp), ef), Nat.add(dd, Nat.add(wp, ef)), Nat.add(dd, Nat.add(ef, wp)),
        add_assoc(dd, wp, ef),
        Equal.cong(Nat, Nat, xx => Nat.add(dd, xx), Nat.add(wp, ef), Nat.add(ef, wp), add_comm(wp, ef)))))

# one row taken: c is w and d, h is 1 and hp; the rest answers for d and hp
def rows.step.go(
  +rest: List<&2, U32>,
  +ww: U32,
  +hh: U32,
  +cc: U32,
  +wp: Nat,
  +ef: Nat,
  e_w: {U32.to_nat(ww) == 1n+wp : Nat},
  e_f: {1n+List.length(&2, U32, rest) == Nat.add(U32.to_nat(cc), ef) : Nat},
  pd: &dd: Nat -> {U32.to_nat(cc) == Nat.add(U32.to_nat(ww), dd) : Nat},
  ph: &hp: Nat -> {U32.to_nat(hh) == 1n+hp : Nat},
  ih: rows.ih(rest, ww, (cc - ww : U32), (hh - 1 : U32))
) -> {Png.enc.rows(rest, U32.is_zero((hh - 1 : U32)), U32.is_lt((cc - ww : U32), ww), ww, (hh - 1 : U32),
  (cc - ww : U32)) == Nat.is_eq(U32.to_nat(cc), Nat.mul(U32.to_nat(hh), U32.to_nat(ww))) : Bool}:
  (+dd, e_c0) = pd
  (+hp, e_h0) = ph
  +e_c = {e_c0 : {U32.to_nat(cc) == Nat.add(U32.to_nat(ww), dd) : Nat}}
  +e_h = {e_h0 : {U32.to_nat(hh) == 1n+hp : Nat}}
  +c2 = (cc - ww : U32)
  +h2 = (hh - 1 : U32)
  +e_c2 = {u32_sub_nat(cc, ww, dd, e_c) : {U32.to_nat(c2) == dd : Nat}}
  +e_h2 = {u32_sub_nat(hh, 1, hp, e_h) : {U32.to_nat(h2) == hp : Nat}}
  +vw = U32.to_nat(ww)
  +e_cw = {Equal.trans(Nat, U32.to_nat(cc), Nat.add(vw, dd), Nat.add(1n+wp, dd), e_c,
    Equal.cong(Nat, Nat, xx => Nat.add(xx, dd), vw, 1n+wp, e_w)) : {U32.to_nat(cc) == Nat.add(1n+wp, dd) : Nat}}
  +e_rl = {rows.fuel(List.length(&2, U32, rest), wp, dd, ef,
    Equal.trans(Nat, 1n+List.length(&2, U32, rest), Nat.add(U32.to_nat(cc), ef), Nat.add(Nat.add(1n+wp, dd), ef), e_f,
      Equal.cong(Nat, Nat, xx => Nat.add(xx, ef), U32.to_nat(cc), Nat.add(1n+wp, dd), e_cw))) :
    {List.length(&2, U32, rest) == Nat.add(dd, Nat.add(ef, wp)) : Nat}}
  +e_f2 = {Equal.trans(Nat, List.length(&2, U32, rest), Nat.add(dd, Nat.add(ef, wp)),
    Nat.add(U32.to_nat(c2), Nat.add(ef, wp)), e_rl,
    Equal.cong(Nat, Nat, xx => Nat.add(xx, Nat.add(ef, wp)), dd, U32.to_nat(c2),
      Equal.sym(Nat, U32.to_nat(c2), dd, e_c2))) :
    {List.length(&2, U32, rest) == Nat.add(U32.to_nat(c2), Nat.add(ef, wp)) : Nat}}
  +e_rest = {ih(Nat.add(ef, wp), e_f2) :
    {Png.enc.rows(rest, U32.is_zero(h2), U32.is_lt(c2, ww), ww, h2, c2) ==
      Nat.is_eq(U32.to_nat(c2), Nat.mul(U32.to_nat(h2), vw)) : Bool}}
  Equal.trans(Bool, Png.enc.rows(rest, U32.is_zero(h2), U32.is_lt(c2, ww), ww, h2, c2),
    Nat.is_eq(dd, Nat.mul(hp, vw)), Nat.is_eq(U32.to_nat(cc), Nat.mul(U32.to_nat(hh), vw)),
    Equal.trans(Bool, Png.enc.rows(rest, U32.is_zero(h2), U32.is_lt(c2, ww), ww, h2, c2),
      Nat.is_eq(U32.to_nat(c2), Nat.mul(U32.to_nat(h2), vw)), Nat.is_eq(dd, Nat.mul(hp, vw)), e_rest,
      iseq.mul(U32.to_nat(c2), dd, U32.to_nat(h2), hp, vw, e_c2, e_h2)),
    Equal.trans(Bool, Nat.is_eq(dd, Nat.mul(hp, vw)), Nat.is_eq(Nat.add(vw, dd), Nat.mul(1n+hp, vw)),
      Nat.is_eq(U32.to_nat(cc), Nat.mul(U32.to_nat(hh), vw)),
      Equal.sym(Bool, Nat.is_eq(Nat.add(vw, dd), Nat.add(vw, Nat.mul(hp, vw))), Nat.is_eq(dd, Nat.mul(hp, vw)),
        Equal.cong(Cmp, Bool, xx => Cmp.is_eq(xx), Nat.cmp(Nat.add(vw, dd), Nat.add(vw, Nat.mul(hp, vw))),
          Nat.cmp(dd, Nat.mul(hp, vw)), cmp_add(vw, dd, Nat.mul(hp, vw)))),
      iseq.mul(Nat.add(vw, dd), U32.to_nat(cc), 1n+hp, U32.to_nat(hh), vw,
        Equal.sym(Nat, U32.to_nat(cc), Nat.add(vw, dd), e_c), Equal.sym(Nat, U32.to_nat(hh), 1n+hp, e_h))))

# the walk over the samples answers whether c is h rows of w, for w above 0
# and at most as many as there is fuel for
def rows.nat(
  fuel: List<&2, U32>,
  zh: Bool,
  zlt: Bool,
  +ww: U32,
  +hh: U32,
  +cc: U32,
  +wp: Nat,
  +ef: Nat,
  +e_zh: {U32.is_zero(hh) == zh : Bool},
  +e_zlt: {U32.is_lt(cc, ww) == zlt : Bool},
  +e_w: {U32.to_nat(ww) == 1n+wp : Nat},
  +e_f: {List.length(&2, U32, fuel) == Nat.add(U32.to_nat(cc), ef) : Nat}
) -> {Png.enc.rows(fuel, zh, zlt, ww, hh, cc) ==
  Nat.is_eq(U32.to_nat(cc), Nat.mul(U32.to_nat(hh), U32.to_nat(ww))) : Bool}:
  match fuel zh zlt:
    case Nil{} True{} _zlt:
      rows.done(hh, cc, ww, e_zh)
    case Nil{} False{} True{}:
      rows.short(hh, cc, ww, e_zh, e_zlt)
    case _px <> _rest True{} _zlt:
      rows.done(hh, cc, ww, e_zh)
    case _px <> _rest False{} True{}:
      rows.short(hh, cc, ww, e_zh, e_zlt)
    case Nil{} False{} False{}:
      +hl = Equal.trans(Bool, Cmp.is_lt(Nat.cmp(U32.to_nat(cc), 1n+wp)),
        Cmp.is_lt(Nat.cmp(U32.to_nat(cc), U32.to_nat(ww))), False{},
        Equal.cong(Nat, Bool, xx => Cmp.is_lt(Nat.cmp(U32.to_nat(cc), xx)), 1n+wp, U32.to_nat(ww),
          Equal.sym(Nat, U32.to_nat(ww), 1n+wp, e_w)), lt.nat(cc, ww, False{}, e_zlt))
      Empty.absurd({False{} == Nat.is_eq(U32.to_nat(cc), Nat.mul(U32.to_nat(hh), U32.to_nat(ww))) : Bool},
        rows.nil(U32.to_nat(cc), ef, wp, hl, e_f))
    case _px <> +rest False{} False{}:
      rows.step.go(rest, ww, hh, cc, wp, ef, e_w, e_f,
        ge_split(U32.to_nat(cc), U32.to_nat(ww), lt.nat(cc, ww, False{}, e_zlt)),
        nat_pos(U32.to_nat(hh), zero.nat(hh, False{}, e_zh)),
        ef2 => e2 => rows.nat(rest, U32.is_zero((hh - 1 : U32)), U32.is_lt((cc - ww : U32), ww), ww, (hh - 1 : U32),
          (cc - ww : U32), wp, ef2, {==}, {==}, e_w, e2))

# the count enc.len keeps, below 2^32, is the start and the samples
def len.nat(
  px: List<&2, U32>,
  +nn: U32,
  +hb: {D1.below(32n, Nat.add(U32.to_nat(nn), List.length(&2, U32, px))) == True{} : Bool}
) -> {U32.to_nat(Png.enc.len(px, nn)) == Nat.add(U32.to_nat(nn), List.length(&2, U32, px)) : Nat}:
  match px:
    case Nil{}:
      Equal.sym(Nat, Nat.add(U32.to_nat(nn), 0n), U32.to_nat(nn), add_zero(U32.to_nat(nn)))
    case _pp <> +tl:
      +vn = U32.to_nat(nn)
      +lt = List.length(&2, U32, tl)
      +es = {add_succ(vn, lt) : {Nat.add(vn, 1n+lt) == 1n+Nat.add(vn, lt) : Nat}}
      +hb1 = {Equal.trans(Bool, D1.below(32n, 1n+Nat.add(vn, lt)), D1.below(32n, Nat.add(vn, 1n+lt)), True{},
        Equal.cong(Nat, Bool, xx => D1.below(32n, xx), 1n+Nat.add(vn, lt), Nat.add(vn, 1n+lt),
          Equal.sym(Nat, Nat.add(vn, 1n+lt), 1n+Nat.add(vn, lt), es)), hb) :
        {D1.below(32n, 1n+Nat.add(vn, lt)) == True{} : Bool}}
      +n1 = (nn + 1 : U32)
      +ei = {u32_inc_nat(nn, below_mono(32n, 1n+vn, lt, hb1)) : {U32.to_nat(n1) == 1n+vn : Nat}}
      +hb2 = {Equal.trans(Bool, D1.below(32n, Nat.add(U32.to_nat(n1), lt)), D1.below(32n, 1n+Nat.add(vn, lt)),
        True{},
        Equal.cong(Nat, Bool, xx => D1.below(32n, Nat.add(xx, lt)), U32.to_nat(n1), 1n+vn, ei), hb1) :
        {D1.below(32n, Nat.add(U32.to_nat(n1), lt)) == True{} : Bool}}
      Equal.trans(Nat, U32.to_nat(Png.enc.len(tl, n1)), Nat.add(U32.to_nat(n1), lt), Nat.add(vn, 1n+lt),
        len.nat(tl, n1, hb2),
        Equal.trans(Nat, Nat.add(U32.to_nat(n1), lt), 1n+Nat.add(vn, lt), Nat.add(vn, 1n+lt),
          Equal.cong(Nat, Nat, xx => Nat.add(xx, lt), U32.to_nat(n1), 1n+vn, ei),
          Equal.sym(Nat, Nat.add(vn, 1n+lt), 1n+Nat.add(vn, lt), es)))

# anything and false is false
def and.false(bb: Bool) -> {False{} == Bool.and(bb, False{}) : Bool}:
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# is_eq(L, A) is A below 2^32 and is_eq(L, A), when L is below 2^32
def fits.and(
  zz: Bool,
  +ll: Nat,
  +aa: Nat,
  ez: {Nat.is_eq(ll, aa) == zz : Bool},
  hb: {D1.below(32n, ll) == True{} : Bool}
) -> {zz == Bool.and(D1.below(32n, aa), zz) : Bool}:
  match zz:
    case True{}:
      +eb = {Equal.trans(Bool, D1.below(32n, aa), D1.below(32n, ll), True{},
        Equal.cong(Nat, Bool, xx => D1.below(32n, xx), aa, ll, Equal.sym(Nat, ll, aa, nat_eq_true(ll, aa, ez))),
        hb) : {D1.below(32n, aa) == True{} : Bool}}
      Equal.cong(Bool, Bool, bb => Bool.and(bb, True{}), True{}, D1.below(32n, aa),
        Equal.sym(Bool, D1.below(32n, aa), True{}, eb))
    case False{}:
      and.false(D1.below(32n, aa))

# not x true: x false
def not.true(xx: Bool, ee: {Bool.not(xx) == True{} : Bool}) -> {xx == False{} : Bool}:
  match xx:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, M1.false_true(ee))

# ---- the sample bound, 2^28 ----

# half of a bit plus a double is the double's half
def half.bit(bb: Bool, +xx: Nat) -> {D1.half(Nat.add(M1.bit(bb), Nat.double(xx))) == xx : Nat}:
  match bb:
    case False{}:
      half_double(xx)
    case True{}:
      half_odd(xx)

# a U32 shifted right once is its half
def shr.half(+uu: U32) -> {U32.to_nat(U32.shr(uu)) == D1.half(U32.to_nat(uu)) : Nat}:
  +sv = U32.to_nat(U32.shr(uu))
  +xv = Nat.add(M1.bit(M1.lowb(uu)), Nat.double(sv))
  Equal.sym(Nat, D1.half(U32.to_nat(uu)), sv, Equal.trans(Nat, D1.half(U32.to_nat(uu)), D1.half(xv), sv,
    Equal.cong(Nat, Nat, nn => D1.half(nn), U32.to_nat(uu), xv, M1.shr_split(uu)), half.bit(M1.lowb(uu), sv)))

# x halved k times
def halves(kk: Nat, +xx: Nat) -> Nat:
  match kk:
    case 0n:
      xx
    case 1n+pp:
      D1.half(halves(pp, xx))

# a U32 shifted right k times is its value halved k times
def shrn.halves(kk: Nat, +uu: U32) -> {U32.to_nat(U32.shrn(uu, kk)) == halves(kk, U32.to_nat(uu)) : Nat}:
  match kk:
    case 0n:
      {==}
    case 1n+(+pp):
      Equal.trans(Nat, U32.to_nat(U32.shr(U32.shrn(uu, pp))), D1.half(U32.to_nat(U32.shrn(uu, pp))),
        D1.half(halves(pp, U32.to_nat(uu))), shr.half(U32.shrn(uu, pp)),
        Equal.cong(Nat, Nat, nn => D1.half(nn), U32.to_nat(U32.shrn(uu, pp)), halves(pp, U32.to_nat(uu)),
          shrn.halves(pp, uu)))

# halving once and then k times is halving k times and then once
def halves.half(kk: Nat, +xx: Nat) -> {halves(kk, D1.half(xx)) == D1.half(halves(kk, xx)) : Nat}:
  match kk:
    case 0n:
      {==}
    case 1n+(+pp):
      Equal.cong(Nat, Nat, nn => D1.half(nn), halves(pp, D1.half(xx)), D1.half(halves(pp, xx)), halves.half(pp, xx))

# below 2^k: halving k times leaves 0
def below.halves(kk: Nat, +xx: Nat) -> {D1.below(kk, xx) == Nat.is_eq(halves(kk, xx), 0n) : Bool}:
  match kk:
    case 0n:
      {==}
    case 1n+(+pp):
      Equal.trans(Bool, D1.below(pp, D1.half(xx)), Nat.is_eq(halves(pp, D1.half(xx)), 0n),
        Nat.is_eq(D1.half(halves(pp, xx)), 0n), below.halves(pp, D1.half(xx)),
        Equal.cong(Nat, Bool, nn => Nat.is_eq(nn, 0n), halves(pp, D1.half(xx)), D1.half(halves(pp, xx)),
          halves.half(pp, xx)))

# the guard's bound is the count below 2^28
def small.nat(+nn: U32) -> {Png.enc.small(nn) == D1.below(28n, U32.to_nat(nn)) : Bool}:
  +sv = U32.shrn(nn, 28n)
  +hv = halves(28n, U32.to_nat(nn))
  Equal.trans(Bool, U32.is_zero(sv), Nat.is_eq(U32.to_nat(sv), 0n), D1.below(28n, U32.to_nat(nn)),
    Equal.sym(Bool, Nat.is_eq(U32.to_nat(sv), 0n), U32.is_zero(sv), zero.nat(sv, U32.is_zero(sv), {==})),
    Equal.trans(Bool, Nat.is_eq(U32.to_nat(sv), 0n), Nat.is_eq(hv, 0n), D1.below(28n, U32.to_nat(nn)),
      Equal.cong(Nat, Bool, kk => Nat.is_eq(kk, 0n), U32.to_nat(sv), hv, shrn.halves(28n, nn)),
      Equal.sym(Bool, D1.below(28n, U32.to_nat(nn)), Nat.is_eq(hv, 0n), below.halves(28n, U32.to_nat(nn)))))

# the decoder's bound on chunk lengths, widths and heights is the value below 2^31
def short.nat(+nn: U32) -> {Png.png.short(nn) == D1.below(31n, U32.to_nat(nn)) : Bool}:
  +sv = U32.shrn(nn, 31n)
  +hv = halves(31n, U32.to_nat(nn))
  Equal.trans(Bool, U32.is_zero(sv), Nat.is_eq(U32.to_nat(sv), 0n), D1.below(31n, U32.to_nat(nn)),
    Equal.sym(Bool, Nat.is_eq(U32.to_nat(sv), 0n), U32.is_zero(sv), zero.nat(sv, U32.is_zero(sv), {==})),
    Equal.trans(Bool, Nat.is_eq(U32.to_nat(sv), 0n), Nat.is_eq(hv, 0n), D1.below(31n, U32.to_nat(nn)),
      Equal.cong(Nat, Bool, kk => Nat.is_eq(kk, 0n), U32.to_nat(sv), hv, shrn.halves(31n, nn)),
      Equal.sym(Bool, D1.below(31n, U32.to_nat(nn)), Nat.is_eq(hv, 0n), below.halves(31n, U32.to_nat(nn)))))

# one more on both sides of a gap
def le.gap.up(
  +xp: Nat,
  +yp: Nat,
  pr: &ee: Nat -> {Nat.add(xp, ee) == yp : Nat}
) -> &ee: Nat -> {Nat.add(1n+xp, ee) == 1n+yp : Nat}:
  (+ee, eq) = pr
  (ee, Equal.cong(Nat, Nat, kk => 1n+kk, Nat.add(xp, ee), yp, eq))

# x at most y: y is x and something
def le.gap(xx: Nat, yy: Nat, hh: {Nat.is_le(xx, yy) == True{} : Bool}) -> &ee: Nat -> {Nat.add(xx, ee) == yy : Nat}:
  match xx yy:
    case 0n yy0:
      (yy0, {==})
    case 1n+xp 0n:
      Empty.absurd(&ee: Nat -> {Nat.add(1n+xp, ee) == 0n : Nat}, M1.false_true(hh))
    case 1n+(+xp) 1n+(+yp):
      le.gap.up(xp, yp, le.gap(xp, yp, hh))

# the gap taken out, below_mono
def below.le.go(
  +nn: Nat,
  +xx: Nat,
  +yy: Nat,
  pr: &ee: Nat -> {Nat.add(xx, ee) == yy : Nat},
  hb: {D1.below(nn, yy) == True{} : Bool}
) -> {D1.below(nn, xx) == True{} : Bool}:
  (+ee, eq) = pr
  below_mono(nn, xx, ee, Equal.trans(Bool, D1.below(nn, Nat.add(xx, ee)), D1.below(nn, yy), True{},
    Equal.cong(Nat, Bool, kk => D1.below(nn, kk), Nat.add(xx, ee), yy, eq), hb))

# what is at most a number below 2^n is below 2^n
def below.le(
  +nn: Nat,
  +xx: Nat,
  +yy: Nat,
  hle: {Nat.is_le(xx, yy) == True{} : Bool},
  hb: {D1.below(nn, yy) == True{} : Bool}
) -> {D1.below(nn, xx) == True{} : Bool}:
  below.le.go(nn, xx, yy, le.gap(xx, yy, hle), hb)

# below 2^n is below 2^(n + 1)
law below_up:
  for nn: Nat
  for +xx: Nat
  for hb: {D1.below(nn, xx) == True{} : Bool}
  {D1.below(1n+nn, xx) == True{} : Bool}

# the proof of below_up
def below_up(nn, xx, hb):
  match nn:
    case 0n:
      match xx:
        case 0n:
          {==}
        case 1n+(+qx):
          Empty.absurd({D1.below(1n, 1n+qx) == True{} : Bool}, M1.false_true(hb))
    case 1n+(+pp):
      below_up(pp, D1.half(xx), hb)

# below 2^28 is below 2^32
def below.word(+xx: Nat, hb: {D1.below(28n, xx) == True{} : Bool}) -> {D1.below(32n, xx) == True{} : Bool}:
  below_up(31n, xx, below_up(30n, xx, below_up(29n, xx, below_up(28n, xx, hb))))

# twice a number below 2^n is below 2^(n + 1)
def below.dbl(
  +nn: Nat,
  +xx: Nat,
  hb: {D1.below(nn, xx) == True{} : Bool}
) -> {D1.below(1n+nn, Nat.double(xx)) == True{} : Bool}:
  Equal.trans(Bool, D1.below(nn, D1.half(Nat.double(xx))), D1.below(nn, xx), True{},
    Equal.cong(Nat, Bool, kk => D1.below(nn, kk), D1.half(Nat.double(xx)), xx, half_double(xx)), hb)

# a, false, then c is false, as is b and false
def and3.false(aa: Bool, +bb: Bool, cc: Bool) -> {Bool.and(Bool.and(aa, False{}), cc) == Bool.and(bb, False{}) : Bool}:
  match aa bb:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# a true, true, then b is b and true
def and3.true(
  aa: Bool,
  bb: Bool,
  ea: {aa == True{} : Bool}
) -> {Bool.and(Bool.and(aa, True{}), bb) == Bool.and(bb, True{}) : Bool}:
  match aa bb:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} _bb:
      Empty.absurd({Bool.and(Bool.and(False{}, True{}), _bb) == Bool.and(_bb, True{}) : Bool}, M1.false_true(ea))

# the walk's answer and the bound on the count are the law's test: the area
# below 2^28 and the count the area, when the count is below 2^32
def fits.small(
  zz: Bool,
  +ll: Nat,
  +aa: Nat,
  ez: {Nat.is_eq(ll, aa) == zz : Bool},
  hb: {D1.below(32n, ll) == True{} : Bool}
) -> {Bool.and(Bool.and(D1.below(32n, aa), zz), D1.below(28n, ll)) == Bool.and(D1.below(28n, aa), zz) : Bool}:
  match zz:
    case False{}:
      and3.false(D1.below(32n, aa), D1.below(28n, aa), D1.below(28n, ll))
    case True{}:
      +ela = {nat_eq_true(ll, aa, ez) : {ll == aa : Nat}}
      Equal.trans(Bool, Bool.and(Bool.and(D1.below(32n, aa), True{}), D1.below(28n, ll)),
        Bool.and(Bool.and(D1.below(32n, aa), True{}), D1.below(28n, aa)), Bool.and(D1.below(28n, aa), True{}),
        Equal.cong(Nat, Bool, kk => Bool.and(Bool.and(D1.below(32n, aa), True{}), D1.below(28n, kk)), ll, aa, ela),
        and3.true(D1.below(32n, aa), D1.below(28n, aa), Equal.trans(Bool, D1.below(32n, aa), D1.below(32n, ll), True{},
          Equal.cong(Nat, Bool, kk => D1.below(32n, kk), aa, ll, Equal.sym(Nat, ll, aa, ela)), hb)))

# the two side tests agree, and the rest agrees when the width is above 0
def good.pick(
  nw: Bool,
  nh: Bool,
  +rr: Bool,
  +ss: Bool,
  fn: {nw == True{} : Bool} -> {rr == ss : Bool}
) -> {Bool.and(Bool.and(nw, nh), rr) == Bool.and(Bool.and(nw, nh), ss) : Bool}:
  match nw nh:
    case True{} True{}:
      fn({==})
    case True{} False{}:
      {==}
    case False{} _nh:
      {==}

# a U32 above 0 is one whose value is not 0
def gt.nat(+ww: U32) -> {U32.is_gt(ww, 0) == Bool.not(Nat.is_eq(U32.to_nat(ww), 0n)) : Bool}:
  Equal.trans(Bool, U32.is_gt(ww, 0), Cmp.is_gt(Nat.cmp(U32.to_nat(ww), 0n)), Bool.not(Nat.is_eq(U32.to_nat(ww), 0n)),
    Equal.cong(Cmp, Bool, xx => Cmp.is_gt(xx), U32.cmp(ww, 0), Nat.cmp(U32.to_nat(ww), 0n), u32_cmp_nat(ww, 0)),
    gt_zero(U32.to_nat(ww)))

# with the width 1 and wp: the walk, the count, and the law's test agree
def good.rows(
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  +hb: {D1.below(32n, List.length(&2, U32, px)) == True{} : Bool},
  pw: &wp: Nat -> {U32.to_nat(ww) == 1n+wp : Nat}
) -> {Png.enc.rows(px, U32.is_zero(hh), U32.is_lt(Png.enc.len(px, 0), ww), ww, hh, Png.enc.len(px, 0)) ==
  Bool.and(D1.below(32n, Nat.mul(U32.to_nat(hh), U32.to_nat(ww))),
    Nat.is_eq(List.length(&2, U32, px), Nat.mul(U32.to_nat(hh), U32.to_nat(ww)))) : Bool}:
  (+wp, e_w0) = pw
  +e_w = {e_w0 : {U32.to_nat(ww) == 1n+wp : Nat}}
  +nn = Png.enc.len(px, 0)
  +ll = List.length(&2, U32, px)
  +aa = Nat.mul(U32.to_nat(hh), U32.to_nat(ww))
  +e_n = {len.nat(px, 0, hb) : {U32.to_nat(nn) == ll : Nat}}
  +e_f = {Equal.trans(Nat, ll, U32.to_nat(nn), Nat.add(U32.to_nat(nn), 0n), Equal.sym(Nat, U32.to_nat(nn), ll, e_n),
    Equal.sym(Nat, Nat.add(U32.to_nat(nn), 0n), U32.to_nat(nn), add_zero(U32.to_nat(nn)))) :
    {ll == Nat.add(U32.to_nat(nn), 0n) : Nat}}
  Equal.trans(Bool, Png.enc.rows(px, U32.is_zero(hh), U32.is_lt(nn, ww), ww, hh, nn), Nat.is_eq(ll, aa),
    Bool.and(D1.below(32n, aa), Nat.is_eq(ll, aa)),
    Equal.trans(Bool, Png.enc.rows(px, U32.is_zero(hh), U32.is_lt(nn, ww), ww, hh, nn),
      Nat.is_eq(U32.to_nat(nn), aa), Nat.is_eq(ll, aa),
      rows.nat(px, U32.is_zero(hh), U32.is_lt(nn, ww), ww, hh, nn, wp, 0n, {==}, {==}, e_w, e_f),
      Equal.cong(Nat, Bool, xx => Nat.is_eq(xx, aa), U32.to_nat(nn), ll, e_n)),
    fits.and(Nat.is_eq(ll, aa), ll, aa, {==}, hb))

# with the width 1 and wp: the walk and the bound on the count are the law's test
def good.rest(
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  +hb: {D1.below(32n, List.length(&2, U32, px)) == True{} : Bool},
  pw: &wp: Nat -> {U32.to_nat(ww) == 1n+wp : Nat}
) -> {Bool.and(Png.enc.rows(px, U32.is_zero(hh), U32.is_lt(Png.enc.len(px, 0), ww), ww, hh, Png.enc.len(px, 0)),
  Png.enc.small(Png.enc.len(px, 0))) == Bool.and(D1.below(28n, Nat.mul(U32.to_nat(hh), U32.to_nat(ww))),
    Nat.is_eq(List.length(&2, U32, px), Nat.mul(U32.to_nat(hh), U32.to_nat(ww)))) : Bool}:
  +nn = Png.enc.len(px, 0)
  +ll = List.length(&2, U32, px)
  +aa = Nat.mul(U32.to_nat(hh), U32.to_nat(ww))
  +rw = Png.enc.rows(px, U32.is_zero(hh), U32.is_lt(nn, ww), ww, hh, nn)
  +b32 = Bool.and(D1.below(32n, aa), Nat.is_eq(ll, aa))
  +e_n = {len.nat(px, 0, hb) : {U32.to_nat(nn) == ll : Nat}}
  +e_s = {Equal.trans(Bool, Png.enc.small(nn), D1.below(28n, U32.to_nat(nn)), D1.below(28n, ll), small.nat(nn),
    Equal.cong(Nat, Bool, kk => D1.below(28n, kk), U32.to_nat(nn), ll, e_n)) : {Png.enc.small(nn) == D1.below(28n, ll) :
    Bool}}
  Equal.trans(Bool, Bool.and(rw, Png.enc.small(nn)), Bool.and(b32, Png.enc.small(nn)),
    Bool.and(D1.below(28n, aa), Nat.is_eq(ll, aa)),
    Equal.cong(Bool, Bool, bb => Bool.and(bb, Png.enc.small(nn)), rw, b32, good.rows(ww, hh, px, hb, pw)),
    Equal.trans(Bool, Bool.and(b32, Png.enc.small(nn)), Bool.and(b32, D1.below(28n, ll)),
      Bool.and(D1.below(28n, aa), Nat.is_eq(ll, aa)),
      Equal.cong(Bool, Bool, bb => Bool.and(b32, bb), Png.enc.small(nn), D1.below(28n, ll), e_s),
      fits.small(Nat.is_eq(ll, aa), ll, aa, {==}, hb)))

# for fewer than 2^32 samples, the guard is the law's test
def good.nat(
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  +hb: {D1.below(32n, List.length(&2, U32, px)) == True{} : Bool}
) -> {Png.enc.good(ww, hh, px) == D1.png_ok(ww, hh, px) : Bool}:
  +nn = Png.enc.len(px, 0)
  +rr = Bool.and(Png.enc.rows(px, U32.is_zero(hh), U32.is_lt(nn, ww), ww, hh, nn), Png.enc.small(nn))
  +nw = Bool.not(Nat.is_eq(U32.to_nat(ww), 0n))
  +nh = Bool.not(Nat.is_eq(U32.to_nat(hh), 0n))
  +aa = Nat.mul(U32.to_nat(hh), U32.to_nat(ww))
  +ss = Bool.and(D1.below(28n, aa), Nat.is_eq(List.length(&2, U32, px), aa))
  Equal.trans(Bool, Bool.and(Bool.and(U32.is_gt(ww, 0), U32.is_gt(hh, 0)), rr), Bool.and(Bool.and(nw, nh), rr),
    Bool.and(Bool.and(nw, nh), ss),
    Equal.trans(Bool, Bool.and(Bool.and(U32.is_gt(ww, 0), U32.is_gt(hh, 0)), rr),
      Bool.and(Bool.and(nw, U32.is_gt(hh, 0)), rr), Bool.and(Bool.and(nw, nh), rr),
      Equal.cong(Bool, Bool, bb => Bool.and(Bool.and(bb, U32.is_gt(hh, 0)), rr), U32.is_gt(ww, 0), nw, gt.nat(ww)),
      Equal.cong(Bool, Bool, bb => Bool.and(Bool.and(nw, bb), rr), U32.is_gt(hh, 0), nh, gt.nat(hh))),
    good.pick(nw, nh, rr, ss, en => good.rest(ww, hh, px, hb, nat_pos(U32.to_nat(ww),
      not.true(Nat.is_eq(U32.to_nat(ww), 0n), en)))))

# enc.open with its guard true is some
def open.some(
  zz: Bool,
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  ez: {zz == True{} : Bool}
) -> {Maybe.is_some(&2, List<&2, U32>, Png.enc.open(zz, ww, hh, px)) == True{} : Bool}:
  match zz:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, M1.false_true(ez))

def L1.png_encodes(ww, hh, px, h_ok):
  +aa = Nat.mul(U32.to_nat(hh), U32.to_nat(ww))
  +ll = List.length(&2, U32, px)
  +nw = Bool.not(Nat.is_eq(U32.to_nat(ww), 0n))
  +nh = Bool.not(Nat.is_eq(U32.to_nat(hh), 0n))
  +ok = {h_ok : {D1.png_ok(ww, hh, px) == True{} : Bool}}
  +e_r = {M1.and_right(Bool.and(nw, nh), Bool.and(D1.below(28n, aa), Nat.is_eq(ll, aa)), ok) :
    {Bool.and(D1.below(28n, aa), Nat.is_eq(ll, aa)) == True{} : Bool}}
  +e_la = {nat_eq_true(ll, aa, M1.and_right(D1.below(28n, aa), Nat.is_eq(ll, aa), e_r)) : {ll == aa : Nat}}
  +hb = {Equal.trans(Bool, D1.below(32n, ll), D1.below(32n, aa), True{},
    Equal.cong(Nat, Bool, xx => D1.below(32n, xx), ll, aa, e_la),
    below.word(aa, M1.and_left(D1.below(28n, aa), Nat.is_eq(ll, aa), e_r))) : {D1.below(32n, ll) == True{} : Bool}}
  open.some(Png.enc.good(ww, hh, px), ww, hh, px,
    Equal.trans(Bool, Png.enc.good(ww, hh, px), D1.png_ok(ww, hh, px), True{}, good.nat(ww, hh, px, hb), ok))
