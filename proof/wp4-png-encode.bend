# proof/wp4-png-encode: Nat and Word lemmas for IMG-PNG-3. Each is a law
# proved here; PROOF.bend imports this file, so the gate checks it. None of
# them names 2^32 as a number: the checker expands a big Nat in unary, so a
# bound is `Laws.below(n, x)`, x halved n times is 0.
import Base
import ../LAWS.bend as Laws
import ./u32.bend as U32L

# ---- Nat ----

# one less, or zero
def npred(xx: Nat) -> Nat:
  match xx:
    case 0n:
      0n
    case 1n+(+pp):
      pp

# the type 0n == n names: Unit for 0, Empty for a successor
def zero_ty(nn: Nat) -> Type:
  match nn:
    case 0n:
      Unit
    case 1n+(+_pp):
      Empty

# zero is no successor
law zero_succ:
  for -xx: Nat
  for +ee: {0n == 1n+xx : Nat}
  Empty

# the proof of zero_succ
def zero_succ(_xx, ee):
  %ee : zero_ty(_)
  Unit{}

# successors are equal only when their predecessors are
law succ_inj:
  for +aa: Nat
  for +bb: Nat
  for +ee: {1n+aa == 1n+bb : Nat}
  {aa == bb : Nat}

# the proof of succ_inj
def succ_inj(aa, bb, ee):
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
      Empty.absurd({0n == 1n+_qb : Nat}, U32L.false_true(ee))
    case 1n+_qa 0n:
      Empty.absurd({1n+_qa == 0n : Nat}, U32L.false_true(ee))
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
      Empty.absurd({Nat.is_eq(0n, xx) == False{} : Bool}, U32L.false_true(hl))
    case 0n 1n+_qw:
      {==}
    case 1n+_qc 0n:
      Empty.absurd({Nat.is_eq(1n+_qc, xx) == False{} : Bool}, U32L.false_true(hl))
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
        U32L.false_true(Equal.sym(Bool, True{}, False{}, hg)))
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
      Empty.absurd(&pp: Nat -> {0n == 1n+pp : Nat}, U32L.false_true(Equal.sym(Bool, True{}, False{}, hz)))
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
  {Laws.half(Nat.double(xx)) == xx : Nat}

# the proof of half_double
def half_double(xx):
  match xx:
    case 0n:
      {==}
    case 1n+(+pp):
      Equal.cong(Nat, Nat, nn => 1n+nn, Laws.half(Nat.double(pp)), pp, half_double(pp))

# half of an odd number
law half_odd:
  for +xx: Nat
  {Laws.half(1n+Nat.double(xx)) == xx : Nat}

# the proof of half_odd
def half_odd(xx):
  match xx:
    case 0n:
      {==}
    case 1n+(+pp):
      Equal.cong(Nat, Nat, nn => 1n+nn, Laws.half(1n+Nat.double(pp)), pp, half_odd(pp))

# halving x and e gives half of x and something more
def half_add.ty(+xx: Nat, +ee: Nat) -> Type:
  &ff: Nat -> {Laws.half(Nat.add(xx, ee)) == Nat.add(Laws.half(xx), ff) : Nat}

# two more in x is one more in its half
def half_add.up(+xx: Nat, +ee: Nat, pr: half_add.ty(xx, ee)) -> half_add.ty(2n+xx, ee):
  (ff, eh) = pr
  (ff, Equal.cong(Nat, Nat, nn => 1n+nn, Laws.half(Nat.add(xx, ee)), Nat.add(Laws.half(xx), ff), eh))

# halving a sum leaves at least half the first summand
law half_add:
  for +xx: Nat
  for +ee: Nat
  exs ff: Nat
  {Laws.half(Nat.add(xx, ee)) == Nat.add(Laws.half(xx), ff) : Nat}

# the proof of half_add
def half_add(xx, ee):
  match xx:
    case 0n:
      (Laws.half(ee), {==})
    case 1n+(+x1):
      match x1:
        case 0n:
          (Laws.half(1n+ee), {==})
        case 1n+(+x2):
          half_add.up(x2, ee, half_add(x2, ee))

# below 2^(n+1) once the half of x and e is rewritten: the half of x and f
def below_mono.half(
  +pp: Nat,
  +xx: Nat,
  +ee: Nat,
  pr: half_add.ty(xx, ee),
  hb: {Laws.below(pp, Laws.half(Nat.add(xx, ee))) == True{} : Bool}
) -> &ff: Nat -> {Laws.below(pp, Nat.add(Laws.half(xx), ff)) == True{} : Bool}:
  (ff, eh) = pr
  (ff, Equal.trans(Bool, Laws.below(pp, Nat.add(Laws.half(xx), ff)), Laws.below(pp, Laws.half(Nat.add(xx, ee))), True{},
    Equal.cong(Nat, Bool, zz => Laws.below(pp, zz), Nat.add(Laws.half(xx), ff), Laws.half(Nat.add(xx, ee)),
      Equal.sym(Nat, Laws.half(Nat.add(xx, ee)), Nat.add(Laws.half(xx), ff), eh)), hb))

# the witness taken out, the rest of below_mono is the call it is given
def below_mono.go(
  +pp: Nat,
  +hx: Nat,
  pr: &ff: Nat -> {Laws.below(pp, Nat.add(hx, ff)) == True{} : Bool},
  ih: @ff: Nat -> {Laws.below(pp, Nat.add(hx, ff)) == True{} : Bool} -> {Laws.below(pp, hx) == True{} : Bool}
) -> {Laws.below(pp, hx) == True{} : Bool}:
  (ff, hf) = pr
  ih(ff, hf)

# a number below 2^n with something added keeps its part below 2^n
law below_mono:
  for +nn: Nat
  for +xx: Nat
  for +ee: Nat
  for +hb: {Laws.below(nn, Nat.add(xx, ee)) == True{} : Bool}
  {Laws.below(nn, xx) == True{} : Bool}

# the proof of below_mono
def below_mono(nn, xx, ee, hb):
  match nn:
    case 0n:
      match xx:
        case 0n:
          {==}
        case 1n+(+qx):
          Empty.absurd({Laws.below(0n, 1n+qx) == True{} : Bool}, U32L.false_true(hb))
    case 1n+(+pp):
      below_mono.go(pp, Laws.half(xx), below_mono.half(pp, xx, ee, half_add(xx, ee), hb), ff => hf =>
        below_mono(pp, Laws.half(xx), ff, hf))

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
  {dd == Nat.double(Laws.half(dd)) : Nat} & {xx == Nat.add(yy, Laws.half(dd)) : Nat}

# the proof of split_even
def split_even(yy, xx, dd, hh):
  match yy:
    case 0n:
      +eh = {Equal.trans(Nat, Laws.half(dd), Laws.half(Nat.double(xx)), xx,
        Equal.cong(Nat, Nat, zz => Laws.half(zz), dd, Nat.double(xx), Equal.sym(Nat, Nat.double(xx), dd, hh)),
        half_double(xx)) : {Laws.half(dd) == xx : Nat}}
      (Equal.trans(Nat, dd, Nat.double(xx), Nat.double(Laws.half(dd)), Equal.sym(Nat, Nat.double(xx), dd, hh),
        Equal.cong(Nat, Nat, zz => Nat.double(zz), xx, Laws.half(dd), Equal.sym(Nat, Laws.half(dd), xx, eh))),
        Equal.sym(Nat, Laws.half(dd), xx, eh))
    case 1n+(+qy):
      match xx:
        case 0n:
          Empty.absurd({dd == Nat.double(Laws.half(dd)) : Nat} & {0n == Nat.add(1n+qy, Laws.half(dd)) : Nat},
            zero_succ(1n+Nat.add(Nat.double(qy), dd), hh))
        case 1n+(+qx):
          +h2 = succ_inj(Nat.double(qx), Nat.add(Nat.double(qy), dd),
            succ_inj(1n+Nat.double(qx), 1n+Nat.add(Nat.double(qy), dd), hh))
          split.up(dd, qx, Nat.add(qy, Laws.half(dd)), Nat.double(Laws.half(dd)), split_even(qy, qx, dd, h2))

# double x is 1 and double y and d: d is odd, and x is 1, y and half of d
law split_odd:
  for +yy: Nat
  for +xx: Nat
  for +dd: Nat
  for +hh: {Nat.double(xx) == 1n+Nat.add(Nat.double(yy), dd) : Nat}
  {dd == 1n+Nat.double(Laws.half(dd)) : Nat} & {xx == 1n+Nat.add(yy, Laws.half(dd)) : Nat}

# the proof of split_odd
def split_odd(yy, xx, dd, hh):
  match yy xx:
    case _yy 0n:
      Empty.absurd({dd == 1n+Nat.double(Laws.half(dd)) : Nat} & {0n == 1n+Nat.add(_yy, Laws.half(dd)) : Nat},
        zero_succ(Nat.add(Nat.double(_yy), dd), hh))
    case 0n 1n+(+qx):
      +h2 = {succ_inj(1n+Nat.double(qx), dd, hh) : {1n+Nat.double(qx) == dd : Nat}}
      +eh = {Equal.trans(Nat, Laws.half(dd), Laws.half(1n+Nat.double(qx)), qx,
        Equal.cong(Nat, Nat, zz => Laws.half(zz), dd, 1n+Nat.double(qx), Equal.sym(Nat, 1n+Nat.double(qx), dd, h2)),
        half_odd(qx)) : {Laws.half(dd) == qx : Nat}}
      (Equal.trans(Nat, dd, 1n+Nat.double(qx), 1n+Nat.double(Laws.half(dd)), Equal.sym(Nat, 1n+Nat.double(qx), dd, h2),
        Equal.cong(Nat, Nat, zz => 1n+Nat.double(zz), qx, Laws.half(dd), Equal.sym(Nat, Laws.half(dd), qx, eh))),
        Equal.cong(Nat, Nat, zz => 1n+zz, qx, Laws.half(dd), Equal.sym(Nat, Laws.half(dd), qx, eh)))
    case 1n+(+qy) 1n+(+qx):
      +h2 = succ_inj(Nat.double(qx), 1n+Nat.add(Nat.double(qy), dd),
        succ_inj(1n+Nat.double(qx), 1n+1n+Nat.add(Nat.double(qy), dd), hh))
      split.up(dd, qx, 1n+Nat.add(qy, Laws.half(dd)), 1n+Nat.double(Laws.half(dd)), split_odd(qy, qx, dd, h2))

# 1 and double x is double y and d: d is odd, and x is y and half of d
law split_odd2:
  for +yy: Nat
  for +xx: Nat
  for +dd: Nat
  for +hh: {1n+Nat.double(xx) == Nat.add(Nat.double(yy), dd) : Nat}
  {dd == 1n+Nat.double(Laws.half(dd)) : Nat} & {xx == Nat.add(yy, Laws.half(dd)) : Nat}

# the proof of split_odd2
def split_odd2(yy, xx, dd, hh):
  match yy:
    case 0n:
      +eh = {Equal.trans(Nat, Laws.half(dd), Laws.half(1n+Nat.double(xx)), xx,
        Equal.cong(Nat, Nat, zz => Laws.half(zz), dd, 1n+Nat.double(xx), Equal.sym(Nat, 1n+Nat.double(xx), dd, hh)),
        half_odd(xx)) : {Laws.half(dd) == xx : Nat}}
      (Equal.trans(Nat, dd, 1n+Nat.double(xx), 1n+Nat.double(Laws.half(dd)), Equal.sym(Nat, 1n+Nat.double(xx), dd, hh),
        Equal.cong(Nat, Nat, zz => 1n+Nat.double(zz), xx, Laws.half(dd), Equal.sym(Nat, Laws.half(dd), xx, eh))),
        Equal.sym(Nat, Laws.half(dd), xx, eh))
    case 1n+(+qy):
      match xx:
        case 0n:
          Empty.absurd({dd == 1n+Nat.double(Laws.half(dd)) : Nat} & {0n == Nat.add(1n+qy, Laws.half(dd)) : Nat},
            zero_succ(Nat.add(Nat.double(qy), dd), succ_inj(0n, 1n+Nat.add(Nat.double(qy), dd), hh)))
        case 1n+(+qx):
          +h2 = succ_inj(1n+Nat.double(qx), Nat.add(Nat.double(qy), dd),
            succ_inj(1n+1n+Nat.double(qx), 1n+Nat.add(Nat.double(qy), dd), hh))
          split.up(dd, qx, Nat.add(qy, Laws.half(dd)), 1n+Nat.double(Laws.half(dd)), split_odd2(qy, qx, dd, h2))

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

# the 1 a subtraction takes away when no carry comes in
def nb(cc: Bool) -> Nat:
  match cc:
    case True{}:
      0n
    case False{}:
      1n

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
  er: {rr == Laws.half(dd) : Nat},
  ed: {dd == 1n+Nat.double(Laws.half(dd)) : Nat}
) -> {1n+Nat.double(rr) == dd : Nat}:
  Equal.trans(Nat, 1n+Nat.double(rr), 1n+Nat.double(Laws.half(dd)), dd,
    Equal.cong(Nat, Nat, zz => 1n+Nat.double(zz), rr, Laws.half(dd), er),
    Equal.sym(Nat, dd, 1n+Nat.double(Laws.half(dd)), ed))

# an even digit is the value it was split from
def dig.even(
  +rr: Nat,
  +dd: Nat,
  er: {rr == Laws.half(dd) : Nat},
  ed: {dd == Nat.double(Laws.half(dd)) : Nat}
) -> {Nat.double(rr) == dd : Nat}:
  Equal.trans(Nat, Nat.double(rr), Nat.double(Laws.half(dd)), dd,
    Equal.cong(Nat, Nat, zz => Nat.double(zz), rr, Laws.half(dd), er),
    Equal.sym(Nat, dd, Nat.double(Laws.half(dd)), ed))

# what word_sub proves one level down, for any borrow and difference
def sub.ih(+pp: Nat, +at: Word(pp), +bt: Word(pp)) -> Type:
  @kk: Bool -> @dd: Nat -> {Word.to_nat(pp, at) == Nat.add(nb(kk), Nat.add(Word.to_nat(pp, bt), dd)) : Nat} ->
    {Word.to_nat(pp, Word.adc(pp, at, bt, True{}, kk)) == dd : Nat}

# d split as the digit ds, and a less the borrow and b is half of d
def sub.split(+pp: Nat, +at: Word(pp), +bt: Word(pp), +kk: Bool, +dd: Nat, +ds: Nat) -> Type:
  {dd == ds : Nat} & {Word.to_nat(pp, at) == Nat.add(nb(kk), Nat.add(Word.to_nat(pp, bt), Laws.half(dd))) : Nat}

# an odd split: the low bit is 1, the rest is the rest of the difference
def sub.odd(
  +pp: Nat,
  +at: Word(pp),
  +bt: Word(pp),
  +kk: Bool,
  +dd: Nat,
  ih: sub.ih(pp, at, bt),
  pr: sub.split(pp, at, bt, kk, dd, 1n+Nat.double(Laws.half(dd)))
) -> {1n+Nat.double(Word.to_nat(pp, Word.adc(pp, at, bt, True{}, kk))) == dd : Nat}:
  (ed, ex) = pr
  dig.odd(Word.to_nat(pp, Word.adc(pp, at, bt, True{}, kk)), dd, ih(kk, Laws.half(dd), ex), ed)

# an even split: the low bit is 0, the rest is the rest of the difference
def sub.even(
  +pp: Nat,
  +at: Word(pp),
  +bt: Word(pp),
  +kk: Bool,
  +dd: Nat,
  ih: sub.ih(pp, at, bt),
  pr: sub.split(pp, at, bt, kk, dd, Nat.double(Laws.half(dd)))
) -> {Nat.double(Word.to_nat(pp, Word.adc(pp, at, bt, True{}, kk))) == dd : Nat}:
  (ed, ex) = pr
  dig.even(Word.to_nat(pp, Word.adc(pp, at, bt, True{}, kk)), dd, ih(kk, Laws.half(dd), ex), ed)

# one bit of a subtraction: each low bit and borrow, the split that fits it
def sub.step(
  +pp: Nat,
  ab: Bool,
  bb: Bool,
  cc: Bool,
  +at: Word(pp),
  +bt: Word(pp),
  +dd: Nat,
  hd: {Word.to_nat(1n+pp, WCon{ab, at}) == Nat.add(nb(cc), Nat.add(Word.to_nat(1n+pp, WCon{bb, bt}), dd)) : Nat},
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
        split_even(Word.to_nat(pp, bt), Word.to_nat(pp, at), dd, succ_inj(Nat.double(Word.to_nat(pp, at)),
          Nat.add(Nat.double(Word.to_nat(pp, bt)), dd), hd)))
    case True{} False{} True{}:
      sub.odd(pp, at, bt, True{}, dd, ih, split_odd2(Word.to_nat(pp, bt), Word.to_nat(pp, at), dd, hd))
    case True{} True{} False{}:
      sub.odd(pp, at, bt, False{}, dd, ih,
        split_odd(Word.to_nat(pp, bt), Word.to_nat(pp, at), dd, succ_inj(Nat.double(Word.to_nat(pp, at)),
          1n+Nat.add(Nat.double(Word.to_nat(pp, bt)), dd), hd)))
    case True{} True{} True{}:
      sub.even(pp, at, bt, True{}, dd, ih,
        split_even(Word.to_nat(pp, bt), Word.to_nat(pp, at), dd, succ_inj(Nat.double(Word.to_nat(pp, at)),
          Nat.add(Nat.double(Word.to_nat(pp, bt)), dd), hd)))

# no borrow into a word of no bits: the difference is 0
def sub.nil(
  cc: Bool,
  +dd: Nat,
  hd: {0n == Nat.add(nb(cc), Nat.add(0n, dd)) : Nat}
) -> {0n == dd : Nat}:
  match cc:
    case True{}:
      hd
    case False{}:
      Empty.absurd({0n == dd : Nat}, zero_succ(dd, hd))

# a word minus a word, borrow c in, whose value is a - b - (1 - c) = d, is d
law word_sub:
  for +nn: Nat
  for +aw: Word(nn)
  for +bw: Word(nn)
  for +cc: Bool
  for +dd: Nat
  for +hd: {Word.to_nat(nn, aw) == Nat.add(nb(cc), Nat.add(Word.to_nat(nn, bw), dd)) : Nat}
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
    {Laws.below(pp, dd) == True{} : Bool} ->
    {Word.to_nat(pp, Word.adc(pp, xt, Word.zero(pp), False{}, kk)) == dd : Nat}

# the carry into the next bit, and half the sum is what the rest must make
def carry.even(
  +pp: Nat,
  +xt: Word(pp),
  +kk: Bool,
  +dd: Nat,
  ih: carry.ih(pp, xt),
  eh: {Laws.half(dd) == Nat.add(bitv(kk), Word.to_nat(pp, xt)) : Nat},
  ed: {dd == Nat.double(Laws.half(dd)) : Nat},
  hb: {Laws.below(pp, Laws.half(dd)) == True{} : Bool}
) -> {Nat.double(Word.to_nat(pp, Word.adc(pp, xt, Word.zero(pp), False{}, kk))) == dd : Nat}:
  +hs = Equal.sym(Nat, Laws.half(dd), Nat.add(bitv(kk), Word.to_nat(pp, xt)), eh)
  dig.even(Word.to_nat(pp, Word.adc(pp, xt, Word.zero(pp), False{}, kk)), dd,
    ih(kk, Laws.half(dd), hs, hb), ed)

# the same with the low bit 1
def carry.odd(
  +pp: Nat,
  +xt: Word(pp),
  +kk: Bool,
  +dd: Nat,
  ih: carry.ih(pp, xt),
  eh: {Laws.half(dd) == Nat.add(bitv(kk), Word.to_nat(pp, xt)) : Nat},
  ed: {dd == 1n+Nat.double(Laws.half(dd)) : Nat},
  hb: {Laws.below(pp, Laws.half(dd)) == True{} : Bool}
) -> {1n+Nat.double(Word.to_nat(pp, Word.adc(pp, xt, Word.zero(pp), False{}, kk))) == dd : Nat}:
  +hs = Equal.sym(Nat, Laws.half(dd), Nat.add(bitv(kk), Word.to_nat(pp, xt)), eh)
  dig.odd(Word.to_nat(pp, Word.adc(pp, xt, Word.zero(pp), False{}, kk)), dd,
    ih(kk, Laws.half(dd), hs, hb), ed)

# half of d, from d written as a digit
def half.of(
  +dd: Nat,
  +xx: Nat,
  +yy: Nat,
  hd: {xx == dd : Nat},
  eh: {Laws.half(xx) == yy : Nat}
) -> {Laws.half(dd) == yy : Nat}:
  Equal.trans(Nat, Laws.half(dd), Laws.half(xx), yy,
    Equal.cong(Nat, Nat, zz => Laws.half(zz), dd, xx, Equal.sym(Nat, xx, dd, hd)), eh)

# d, even, written back from its half
def even.back(
  +dd: Nat,
  +yy: Nat,
  hd: {Nat.double(yy) == dd : Nat},
  eh: {Laws.half(dd) == yy : Nat}
) -> {dd == Nat.double(Laws.half(dd)) : Nat}:
  Equal.trans(Nat, dd, Nat.double(yy), Nat.double(Laws.half(dd)), Equal.sym(Nat, Nat.double(yy), dd, hd),
    Equal.cong(Nat, Nat, zz => Nat.double(zz), yy, Laws.half(dd), Equal.sym(Nat, Laws.half(dd), yy, eh)))

# d, odd, written back from its half
def odd.back(
  +dd: Nat,
  +yy: Nat,
  hd: {1n+Nat.double(yy) == dd : Nat},
  eh: {Laws.half(dd) == yy : Nat}
) -> {dd == 1n+Nat.double(Laws.half(dd)) : Nat}:
  Equal.trans(Nat, dd, 1n+Nat.double(yy), 1n+Nat.double(Laws.half(dd)), Equal.sym(Nat, 1n+Nat.double(yy), dd, hd),
    Equal.cong(Nat, Nat, zz => 1n+Nat.double(zz), yy, Laws.half(dd), Equal.sym(Nat, Laws.half(dd), yy, eh)))

# one bit of adding a carry: each low bit and carry in
def carry.step(
  +pp: Nat,
  xb: Bool,
  cc: Bool,
  +xt: Word(pp),
  +dd: Nat,
  +hd: {Nat.add(bitv(cc), Word.to_nat(1n+pp, WCon{xb, xt})) == dd : Nat},
  hb: {Laws.below(1n+pp, dd) == True{} : Bool},
  ih: carry.ih(pp, xt)
) -> {Word.to_nat(1n+pp, Word.adc(1n+pp, WCon{xb, xt}, Word.zero(1n+pp), False{}, cc)) == dd : Nat}:
  match xb cc:
    case False{} False{}:
      +eh = {half.of(dd, Nat.double(Word.to_nat(pp, xt)), Word.to_nat(pp, xt), hd, half_double(Word.to_nat(pp, xt))) :
        {Laws.half(dd) == Word.to_nat(pp, xt) : Nat}}
      carry.even(pp, xt, False{}, dd, ih, eh, even.back(dd, Word.to_nat(pp, xt), hd, eh), hb)
    case False{} True{}:
      +eh = {half.of(dd, 1n+Nat.double(Word.to_nat(pp, xt)), Word.to_nat(pp, xt), hd, half_odd(Word.to_nat(pp, xt))) :
        {Laws.half(dd) == Word.to_nat(pp, xt) : Nat}}
      carry.odd(pp, xt, False{}, dd, ih, eh, odd.back(dd, Word.to_nat(pp, xt), hd, eh), hb)
    case True{} False{}:
      +eh = {half.of(dd, 1n+Nat.double(Word.to_nat(pp, xt)), Word.to_nat(pp, xt), hd, half_odd(Word.to_nat(pp, xt))) :
        {Laws.half(dd) == Word.to_nat(pp, xt) : Nat}}
      carry.odd(pp, xt, False{}, dd, ih, eh, odd.back(dd, Word.to_nat(pp, xt), hd, eh), hb)
    case True{} True{}:
      +eh = {half.of(dd, Nat.double(1n+Word.to_nat(pp, xt)), 1n+Word.to_nat(pp, xt), hd,
        half_double(1n+Word.to_nat(pp, xt))) : {Laws.half(dd) == 1n+Word.to_nat(pp, xt) : Nat}}
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
  for +hb: {Laws.below(nn, dd) == True{} : Bool}
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
  for +hb: {Laws.below(32n, 1n+U32.to_nat(aa)) == True{} : Bool}
  {U32.to_nat((aa + 1 : U32)) == 1n+U32.to_nat(aa) : Nat}

# the proof of u32_inc_nat
def u32_inc_nat(aa, hb):
  match aa:
    case U32{WCon{False{}, +xt}}:
      +vt = Word.to_nat(31n, xt)
      +b2 = {Equal.trans(Bool, Laws.below(31n, vt), Laws.below(31n, Laws.half(1n+Nat.double(vt))), True{},
        Equal.cong(Nat, Bool, zz => Laws.below(31n, zz), vt, Laws.half(1n+Nat.double(vt)),
          Equal.sym(Nat, Laws.half(1n+Nat.double(vt)), vt, half_odd(vt))), hb) : {Laws.below(31n, vt) == True{} : Bool}}
      Equal.cong(Nat, Nat, zz => 1n+Nat.double(zz),
        Word.to_nat(31n, Word.adc(31n, xt, Word.zero(31n), False{}, False{})),
        vt, word_carry(31n, xt, False{}, vt, {==}, b2))
    case U32{WCon{True{}, +xt}}:
      +vt = Word.to_nat(31n, xt)
      +b2 = {Equal.trans(Bool, Laws.below(31n, 1n+vt), Laws.below(31n, 1n+Laws.half(Nat.double(vt))), True{},
        Equal.cong(Nat, Bool, zz => Laws.below(31n, 1n+zz), vt, Laws.half(Nat.double(vt)),
          Equal.sym(Nat, Laws.half(Nat.double(vt)), vt, half_double(vt))), hb) :
        {Laws.below(31n, 1n+vt) == True{} : Bool}}
      Equal.cong(Nat, Nat, zz => Nat.double(zz), Word.to_nat(31n, Word.adc(31n, xt, Word.zero(31n), False{}, True{})),
        1n+vt, word_carry(31n, xt, True{}, 1n+vt, {==}, b2))
