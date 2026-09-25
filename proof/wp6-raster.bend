# proof/wp6-raster: lemmas relating U32 arithmetic and order to Nat, and the
# list lemmas the raster rows use. Each is a law proved here; PROOF.bend
# imports this file, so the gate checks it. A U32 is a 32-bit Word, lowest
# bit first, and Word.to_nat reads it as a Nat; the lemmas say that U32 add,
# mul and sub agree with Nat's when nothing wraps, and that U32 is_lt and
# is_le agree with Nat's always.
import Base
import ./u32.bend as U32L

# ---- Nat arithmetic ----

# a plus zero is a
law add_zero:
  for aa: Nat
  {Nat.add(aa, 0n) == aa : Nat}

# the proof of add_zero
def add_zero(aa):
  match aa:
    case 0n:
      {==}
    case 1n+pp:
      Equal.cong(Nat, Nat, xx => 1n+xx, Nat.add(pp, 0n), pp, add_zero(pp))

# a plus one more than b is one more than a plus b
law add_succ:
  for aa: Nat
  for -bb: Nat
  {Nat.add(aa, 1n+bb) == 1n+Nat.add(aa, bb) : Nat}

# the proof of add_succ
def add_succ(aa, bb):
  match aa:
    case 0n:
      {==}
    case 1n+pp:
      Equal.cong(Nat, Nat, xx => 1n+xx, Nat.add(pp, 1n+bb), 1n+Nat.add(pp, bb), add_succ(pp, bb))

# addition commutes
law add_comm:
  for aa: Nat
  for +bb: Nat
  {Nat.add(aa, bb) == Nat.add(bb, aa) : Nat}

# the proof of add_comm
def add_comm(aa, bb):
  match aa:
    case 0n:
      Equal.sym(Nat, Nat.add(bb, 0n), bb, add_zero(bb))
    case 1n+pp:
      Equal.trans(Nat, 1n+Nat.add(pp, bb), 1n+Nat.add(bb, pp), Nat.add(bb, 1n+pp),
        Equal.cong(Nat, Nat, xx => 1n+xx, Nat.add(pp, bb), Nat.add(bb, pp), add_comm(pp, bb)),
        Equal.sym(Nat, Nat.add(bb, 1n+pp), 1n+Nat.add(bb, pp), add_succ(bb, pp)))

# addition associates
law add_assoc:
  for aa: Nat
  for -bb: Nat
  for -cc: Nat
  {Nat.add(Nat.add(aa, bb), cc) == Nat.add(aa, Nat.add(bb, cc)) : Nat}

# the proof of add_assoc
def add_assoc(aa, bb, cc):
  match aa:
    case 0n:
      {==}
    case 1n+pp:
      Equal.cong(Nat, Nat, xx => 1n+xx, Nat.add(Nat.add(pp, bb), cc), Nat.add(pp, Nat.add(bb, cc)),
        add_assoc(pp, bb, cc))

# the first two of three summands swap
law add_swap:
  for +aa: Nat
  for +bb: Nat
  for +cc: Nat
  {Nat.add(aa, Nat.add(bb, cc)) == Nat.add(bb, Nat.add(aa, cc)) : Nat}

# the proof of add_swap
def add_swap(aa, bb, cc):
  Equal.trans(Nat, Nat.add(aa, Nat.add(bb, cc)), Nat.add(Nat.add(aa, bb), cc), Nat.add(bb, Nat.add(aa, cc)),
    Equal.sym(Nat, Nat.add(Nat.add(aa, bb), cc), Nat.add(aa, Nat.add(bb, cc)), add_assoc(aa, bb, cc)),
    Equal.trans(Nat, Nat.add(Nat.add(aa, bb), cc), Nat.add(Nat.add(bb, aa), cc), Nat.add(bb, Nat.add(aa, cc)),
      Equal.cong(Nat, Nat, xx => Nat.add(xx, cc), Nat.add(aa, bb), Nat.add(bb, aa), add_comm(aa, bb)),
      add_assoc(bb, aa, cc)))

# doubling is adding a number to itself
law double_add:
  for +aa: Nat
  {Nat.double(aa) == Nat.add(aa, aa) : Nat}

# the proof of double_add
def double_add(aa):
  match aa:
    case 0n:
      {==}
    case 1n+pp:
      Equal.trans(Nat, 2n+Nat.double(pp), 2n+Nat.add(pp, pp), 1n+Nat.add(pp, 1n+pp),
        Equal.cong(Nat, Nat, xx => 2n+xx, Nat.double(pp), Nat.add(pp, pp), double_add(pp)),
        Equal.sym(Nat, 1n+Nat.add(pp, 1n+pp), 2n+Nat.add(pp, pp),
          Equal.cong(Nat, Nat, xx => 1n+xx, Nat.add(pp, 1n+pp), 1n+Nat.add(pp, pp), add_succ(pp, pp))))

# doubling distributes over addition
law double_dist:
  for +aa: Nat
  for +bb: Nat
  {Nat.double(Nat.add(aa, bb)) == Nat.add(Nat.double(aa), Nat.double(bb)) : Nat}

# the proof of double_dist
def double_dist(aa, bb):
  match aa:
    case 0n:
      {==}
    case 1n+pp:
      Equal.cong(Nat, Nat, xx => 2n+xx, Nat.double(Nat.add(pp, bb)), Nat.add(Nat.double(pp), Nat.double(bb)),
        double_dist(pp, bb))

# a times zero is zero
law mul_zero:
  for aa: Nat
  {Nat.mul(aa, 0n) == 0n : Nat}

# the proof of mul_zero
def mul_zero(aa):
  match aa:
    case 0n:
      {==}
    case 1n+pp:
      mul_zero(pp)

# a times one more than b is a plus a times b
law mul_succ:
  for +aa: Nat
  for +bb: Nat
  {Nat.mul(aa, 1n+bb) == Nat.add(aa, Nat.mul(aa, bb)) : Nat}

# the proof of mul_succ
def mul_succ(aa, bb):
  match aa:
    case 0n:
      {==}
    case 1n+pp:
      Equal.cong(Nat, Nat, xx => 1n+xx, Nat.add(bb, Nat.mul(pp, 1n+bb)), Nat.add(pp, Nat.add(bb, Nat.mul(pp, bb))),
        Equal.trans(Nat, Nat.add(bb, Nat.mul(pp, 1n+bb)), Nat.add(bb, Nat.add(pp, Nat.mul(pp, bb))),
          Nat.add(pp, Nat.add(bb, Nat.mul(pp, bb))),
          Equal.cong(Nat, Nat, xx => Nat.add(bb, xx), Nat.mul(pp, 1n+bb), Nat.add(pp, Nat.mul(pp, bb)),
            mul_succ(pp, bb)),
          add_swap(bb, pp, Nat.mul(pp, bb))))

# multiplication commutes
law mul_comm:
  for +aa: Nat
  for +bb: Nat
  {Nat.mul(aa, bb) == Nat.mul(bb, aa) : Nat}

# the proof of mul_comm
def mul_comm(aa, bb):
  match aa:
    case 0n:
      Equal.sym(Nat, Nat.mul(bb, 0n), 0n, mul_zero(bb))
    case 1n+pp:
      Equal.trans(Nat, Nat.add(bb, Nat.mul(pp, bb)), Nat.add(bb, Nat.mul(bb, pp)), Nat.mul(bb, 1n+pp),
        Equal.cong(Nat, Nat, xx => Nat.add(bb, xx), Nat.mul(pp, bb), Nat.mul(bb, pp), mul_comm(pp, bb)),
        Equal.sym(Nat, Nat.mul(bb, 1n+pp), Nat.add(bb, Nat.mul(bb, pp)), mul_succ(bb, pp)))

# multiplication distributes over addition on the left operand
law mul_add:
  for aa: Nat
  for +bb: Nat
  for +cc: Nat
  {Nat.mul(Nat.add(aa, bb), cc) == Nat.add(Nat.mul(aa, cc), Nat.mul(bb, cc)) : Nat}

# the proof of mul_add
def mul_add(aa, bb, cc):
  match aa:
    case 0n:
      {==}
    case 1n+pp:
      Equal.trans(Nat, Nat.add(cc, Nat.mul(Nat.add(pp, bb), cc)),
        Nat.add(cc, Nat.add(Nat.mul(pp, cc), Nat.mul(bb, cc))),
        Nat.add(Nat.add(cc, Nat.mul(pp, cc)), Nat.mul(bb, cc)),
        Equal.cong(Nat, Nat, xx => Nat.add(cc, xx), Nat.mul(Nat.add(pp, bb), cc),
          Nat.add(Nat.mul(pp, cc), Nat.mul(bb, cc)), mul_add(pp, bb, cc)),
        Equal.sym(Nat, Nat.add(Nat.add(cc, Nat.mul(pp, cc)), Nat.mul(bb, cc)),
          Nat.add(cc, Nat.add(Nat.mul(pp, cc), Nat.mul(bb, cc))), add_assoc(cc, Nat.mul(pp, cc), Nat.mul(bb, cc))))

# a double times b is the double of a times b
law mul_double:
  for +aa: Nat
  for +bb: Nat
  {Nat.mul(Nat.double(aa), bb) == Nat.double(Nat.mul(aa, bb)) : Nat}

# the proof of mul_double
def mul_double(aa, bb):
  Equal.trans(Nat, Nat.mul(Nat.double(aa), bb), Nat.mul(Nat.add(aa, aa), bb), Nat.double(Nat.mul(aa, bb)),
    Equal.cong(Nat, Nat, xx => Nat.mul(xx, bb), Nat.double(aa), Nat.add(aa, aa), double_add(aa)),
    Equal.trans(Nat, Nat.mul(Nat.add(aa, aa), bb), Nat.add(Nat.mul(aa, bb), Nat.mul(aa, bb)),
      Nat.double(Nat.mul(aa, bb)), mul_add(aa, aa, bb),
      Equal.sym(Nat, Nat.double(Nat.mul(aa, bb)), Nat.add(Nat.mul(aa, bb), Nat.mul(aa, bb)),
        double_add(Nat.mul(aa, bb)))))

# a times the double of b is the double of a times b
law mul_double_r:
  for +aa: Nat
  for +bb: Nat
  {Nat.mul(aa, Nat.double(bb)) == Nat.double(Nat.mul(aa, bb)) : Nat}

# the proof of mul_double_r
def mul_double_r(aa, bb):
  Equal.trans(Nat, Nat.mul(aa, Nat.double(bb)), Nat.mul(Nat.double(bb), aa), Nat.double(Nat.mul(aa, bb)),
    mul_comm(aa, Nat.double(bb)),
    Equal.trans(Nat, Nat.mul(Nat.double(bb), aa), Nat.double(Nat.mul(bb, aa)), Nat.double(Nat.mul(aa, bb)),
      mul_double(bb, aa),
      Equal.cong(Nat, Nat, xx => Nat.double(xx), Nat.mul(bb, aa), Nat.mul(aa, bb), mul_comm(bb, aa))))

# two to one more than p is the double of two to p
law pow2_succ:
  for +pp: Nat
  {Nat.pow(2n, 1n+pp) == Nat.double(Nat.pow(2n, pp)) : Nat}

# the proof of pow2_succ
def pow2_succ(pp):
  Equal.trans(Nat, Nat.add(Nat.pow(2n, pp), Nat.add(Nat.pow(2n, pp), 0n)),
    Nat.add(Nat.pow(2n, pp), Nat.pow(2n, pp)), Nat.double(Nat.pow(2n, pp)),
    Equal.cong(Nat, Nat, xx => Nat.add(Nat.pow(2n, pp), xx), Nat.add(Nat.pow(2n, pp), 0n), Nat.pow(2n, pp),
      add_zero(Nat.pow(2n, pp))),
    Equal.sym(Nat, Nat.double(Nat.pow(2n, pp)), Nat.add(Nat.pow(2n, pp), Nat.pow(2n, pp)),
      double_add(Nat.pow(2n, pp))))

# ---- Nat order, as Bool answers ----

# nothing is below zero
law lt_zero_false:
  for xx: Nat
  {False{} == Nat.is_lt(xx, 0n) : Bool}

# the proof of lt_zero_false
def lt_zero_false(xx):
  match xx:
    case 0n:
      {==}
    case 1n+_pp:
      {==}

# zero is at most every number
law le_zero:
  for nn: Nat
  {Nat.is_le(0n, nn) == True{} : Bool}

# the proof of le_zero
def le_zero(nn):
  match nn:
    case 0n:
      {==}
    case 1n+_pp:
      {==}

# every number is at most itself
law le_refl:
  for nn: Nat
  {Nat.is_le(nn, nn) == True{} : Bool}

# the proof of le_refl
def le_refl(nn):
  match nn:
    case 0n:
      {==}
    case 1n+pp:
      le_refl(pp)

# x < z says the same as x + 1 <= z
law lt_le_succ:
  for xx: Nat
  for zz: Nat
  {Nat.is_lt(xx, zz) == Nat.is_le(1n+xx, zz) : Bool}

# the proof of lt_le_succ
def lt_le_succ(xx, zz):
  match xx zz:
    case 0n 0n:
      {==}
    case 0n 1n+qq:
      Equal.sym(Bool, Nat.is_le(0n, qq), True{}, le_zero(qq))
    case 1n+_pp 0n:
      {==}
    case 1n+pp 1n+qq:
      lt_le_succ(pp, qq)

# below z, the left summand alone is below z
law lt_add_r:
  for xx: Nat
  for yy: Nat
  for zz: Nat
  for hh: {Nat.is_lt(Nat.add(xx, yy), zz) == True{} : Bool}
  {Nat.is_lt(xx, zz) == True{} : Bool}

# the proof of lt_add_r
def lt_add_r(xx, yy, zz, hh):
  match xx zz:
    case 0n 0n:
      Empty.absurd({False{} == True{} : Bool}, U32L.false_true(
        Equal.trans(Bool, False{}, Nat.is_lt(yy, 0n), True{}, lt_zero_false(yy), hh)))
    case 0n 1n+_qq:
      {==}
    case 1n+_pp 0n:
      Empty.absurd({False{} == True{} : Bool}, U32L.false_true(hh))
    case 1n+pp 1n+qq:
      lt_add_r(pp, yy, qq, hh)

# at most z, the left summand alone is at most z
law le_add_r:
  for xx: Nat
  for -yy: Nat
  for zz: Nat
  for hh: {Nat.is_le(Nat.add(xx, yy), zz) == True{} : Bool}
  {Nat.is_le(xx, zz) == True{} : Bool}

# the proof of le_add_r
def le_add_r(xx, yy, zz, hh):
  match xx zz:
    case 0n _zz:
      le_zero(_zz)
    case 1n+_pp 0n:
      Empty.absurd({False{} == True{} : Bool}, U32L.false_true(hh))
    case 1n+pp 1n+qq:
      le_add_r(pp, yy, qq, hh)

# below z, the right summand alone is below z
law lt_add_l:
  for +xx: Nat
  for +yy: Nat
  for zz: Nat
  for hh: {Nat.is_lt(Nat.add(xx, yy), zz) == True{} : Bool}
  {Nat.is_lt(yy, zz) == True{} : Bool}

# the proof of lt_add_l
def lt_add_l(xx, yy, zz, hh):
  lt_add_r(yy, xx, zz, Equal.trans(Bool, Nat.is_lt(Nat.add(yy, xx), zz), Nat.is_lt(Nat.add(xx, yy), zz), True{},
    Equal.cong(Nat, Bool, nn => Nat.is_lt(nn, zz), Nat.add(yy, xx), Nat.add(xx, yy), add_comm(yy, xx)), hh))

# x < y and y <= z give x < z
law lt_le_trans:
  for xx: Nat
  for yy: Nat
  for zz: Nat
  for hxy: {Nat.is_lt(xx, yy) == True{} : Bool}
  for hyz: {Nat.is_le(yy, zz) == True{} : Bool}
  {Nat.is_lt(xx, zz) == True{} : Bool}

# the proof of lt_le_trans
def lt_le_trans(xx, yy, zz, hxy, hyz):
  match xx yy zz:
    case _xx 0n _zz:
      Empty.absurd({Nat.is_lt(_xx, _zz) == True{} : Bool}, U32L.false_true(
        Equal.trans(Bool, False{}, Nat.is_lt(_xx, 0n), True{}, lt_zero_false(_xx), hxy)))
    case _xx 1n+_qq 0n:
      Empty.absurd({Nat.is_lt(_xx, 0n) == True{} : Bool}, U32L.false_true(hyz))
    case 0n 1n+_qq 1n+_rr:
      {==}
    case 1n+pp 1n+qq 1n+rr:
      lt_le_trans(pp, qq, rr, hxy, hyz)

# x < a and a = b give x < b
law lt_rw_r:
  for xx: Nat
  for aa: Nat
  for bb: Nat
  for ee: {aa == bb : Nat}
  for hh: {Nat.is_lt(xx, aa) == True{} : Bool}
  {Nat.is_lt(xx, bb) == True{} : Bool}

# the proof of lt_rw_r
def lt_rw_r(xx, aa, bb, ee, hh):
  Equal.trans(Bool, Nat.is_lt(xx, bb), Nat.is_lt(xx, aa), True{},
    Equal.cong(Nat, Bool, nn => Nat.is_lt(xx, nn), bb, aa, Equal.sym(Nat, aa, bb, ee)), hh)

# a < z and a = b give b < z
law lt_rw_l:
  for aa: Nat
  for bb: Nat
  for zz: Nat
  for ee: {aa == bb : Nat}
  for hh: {Nat.is_lt(aa, zz) == True{} : Bool}
  {Nat.is_lt(bb, zz) == True{} : Bool}

# the proof of lt_rw_l
def lt_rw_l(aa, bb, zz, ee, hh):
  Equal.trans(Bool, Nat.is_lt(bb, zz), Nat.is_lt(aa, zz), True{},
    Equal.cong(Nat, Bool, nn => Nat.is_lt(nn, zz), bb, aa, Equal.sym(Nat, aa, bb, ee)), hh)

# a <= z and a = b give b <= z
law le_rw_l:
  for aa: Nat
  for bb: Nat
  for zz: Nat
  for ee: {aa == bb : Nat}
  for hh: {Nat.is_le(aa, zz) == True{} : Bool}
  {Nat.is_le(bb, zz) == True{} : Bool}

# the proof of le_rw_l
def le_rw_l(aa, bb, zz, ee, hh):
  Equal.trans(Bool, Nat.is_le(bb, zz), Nat.is_le(aa, zz), True{},
    Equal.cong(Nat, Bool, nn => Nat.is_le(nn, zz), bb, aa, Equal.sym(Nat, aa, bb, ee)), hh)

# x <= a and a = b give x <= b
law le_rw_r:
  for xx: Nat
  for aa: Nat
  for bb: Nat
  for ee: {aa == bb : Nat}
  for hh: {Nat.is_le(xx, aa) == True{} : Bool}
  {Nat.is_le(xx, bb) == True{} : Bool}

# the proof of le_rw_r
def le_rw_r(xx, aa, bb, ee, hh):
  Equal.trans(Bool, Nat.is_le(xx, bb), Nat.is_le(xx, aa), True{},
    Equal.cong(Nat, Bool, nn => Nat.is_le(xx, nn), bb, aa, Equal.sym(Nat, aa, bb, ee)), hh)

# x <= y and y <= z give x <= z
law le_trans:
  for xx: Nat
  for yy: Nat
  for zz: Nat
  for hxy: {Nat.is_le(xx, yy) == True{} : Bool}
  for hyz: {Nat.is_le(yy, zz) == True{} : Bool}
  {Nat.is_le(xx, zz) == True{} : Bool}

# the proof of le_trans
def le_trans(xx, yy, zz, hxy, hyz):
  match xx yy zz:
    case 0n _yy _zz:
      le_zero(_zz)
    case 1n+_pp 0n _zz:
      Empty.absurd({Nat.is_le(1n+_pp, _zz) == True{} : Bool}, U32L.false_true(hxy))
    case 1n+_pp 1n+_qq 0n:
      Empty.absurd({False{} == True{} : Bool}, U32L.false_true(hyz))
    case 1n+pp 1n+qq 1n+rr:
      le_trans(pp, qq, rr, hxy, hyz)

# x <= y and y < z give x < z
law le_lt_trans:
  for xx: Nat
  for yy: Nat
  for zz: Nat
  for hxy: {Nat.is_le(xx, yy) == True{} : Bool}
  for hyz: {Nat.is_lt(yy, zz) == True{} : Bool}
  {Nat.is_lt(xx, zz) == True{} : Bool}

# the proof of le_lt_trans
def le_lt_trans(xx, yy, zz, hxy, hyz):
  match xx yy zz:
    case _xx _yy 0n:
      Empty.absurd({Nat.is_lt(_xx, 0n) == True{} : Bool}, U32L.false_true(
        Equal.trans(Bool, False{}, Nat.is_lt(_yy, 0n), True{}, lt_zero_false(_yy), hyz)))
    case 0n _yy 1n+_rr:
      {==}
    case 1n+_pp 0n 1n+_rr:
      Empty.absurd({Nat.is_lt(1n+_pp, 1n+_rr) == True{} : Bool}, U32L.false_true(hxy))
    case 1n+pp 1n+qq 1n+rr:
      le_lt_trans(pp, qq, rr, hxy, hyz)

# x < y gives x <= y
law lt_le:
  for xx: Nat
  for yy: Nat
  for hh: {Nat.is_lt(xx, yy) == True{} : Bool}
  {Nat.is_le(xx, yy) == True{} : Bool}

# the proof of lt_le
def lt_le(xx, yy, hh):
  match xx yy:
    case 0n _yy:
      le_zero(_yy)
    case 1n+_pp 0n:
      Empty.absurd({False{} == True{} : Bool}, U32L.false_true(hh))
    case 1n+pp 1n+qq:
      lt_le(pp, qq, hh)

# adding the same number on the left keeps x < y
law lt_add_mono:
  for mm: Nat
  for -xx: Nat
  for -yy: Nat
  for hh: {Nat.is_lt(xx, yy) == True{} : Bool}
  {Nat.is_lt(Nat.add(mm, xx), Nat.add(mm, yy)) == True{} : Bool}

# the proof of lt_add_mono
def lt_add_mono(mm, xx, yy, hh):
  match mm:
    case 0n:
      hh
    case 1n+pp:
      lt_add_mono(pp, xx, yy, hh)

# adding the same number on the left keeps x <= y
law le_add_mono:
  for mm: Nat
  for -xx: Nat
  for -yy: Nat
  for hh: {Nat.is_le(xx, yy) == True{} : Bool}
  {Nat.is_le(Nat.add(mm, xx), Nat.add(mm, yy)) == True{} : Bool}

# the proof of le_add_mono
def le_add_mono(mm, xx, yy, hh):
  match mm:
    case 0n:
      hh
    case 1n+pp:
      le_add_mono(pp, xx, yy, hh)

# adding more on the right keeps x <= y
law le_add_more:
  for xx: Nat
  for yy: Nat
  for zz: Nat
  for hh: {Nat.is_le(xx, yy) == True{} : Bool}
  {Nat.is_le(xx, Nat.add(yy, zz)) == True{} : Bool}

# the proof of le_add_more
def le_add_more(xx, yy, zz, hh):
  match xx yy:
    case 0n _yy:
      le_zero(Nat.add(_yy, zz))
    case 1n+_pp 0n:
      Empty.absurd({Nat.is_le(1n+_pp, zz) == True{} : Bool}, U32L.false_true(hh))
    case 1n+pp 1n+qq:
      le_add_more(pp, qq, zz, hh)

# a <= b gives a * c <= b * c
law le_mul_mono:
  for aa: Nat
  for bb: Nat
  for +cc: Nat
  for hh: {Nat.is_le(aa, bb) == True{} : Bool}
  {Nat.is_le(Nat.mul(aa, cc), Nat.mul(bb, cc)) == True{} : Bool}

# the proof of le_mul_mono
def le_mul_mono(aa, bb, cc, hh):
  match aa bb:
    case 0n _bb:
      le_zero(Nat.mul(_bb, cc))
    case 1n+_pp 0n:
      Empty.absurd({Nat.is_le(Nat.mul(1n+_pp, cc), 0n) == True{} : Bool}, U32L.false_true(hh))
    case 1n+pp 1n+qq:
      le_add_mono(cc, Nat.mul(pp, cc), Nat.mul(qq, cc), le_mul_mono(pp, qq, cc, hh))

# ---- bits, doubling and compare ----

# a bit as a number: 0 or 1
def bit(bb: Bool) -> Nat:
  match bb:
    case False{}:
      0n
    case True{}:
      1n

# comparing b + 2x with c + 2y: x against y decides, and the bits break a tie,
# as Word.cmp.fin does for a word's lowest bit
law cmp_dbl:
  for xx: Nat
  for yy: Nat
  for aa: Bool
  for bb: Bool
  {Nat.cmp(Nat.add(bit(aa), Nat.double(xx)), Nat.add(bit(bb), Nat.double(yy))) ==
    Word.cmp.fin(aa, bb, Nat.cmp(xx, yy)) : Cmp}

# the proof of cmp_dbl
def cmp_dbl(xx, yy, aa, bb):
  match xx yy aa bb:
    case 0n 0n False{} False{}:
      {==}
    case 0n 0n False{} True{}:
      {==}
    case 0n 0n True{} False{}:
      {==}
    case 0n 0n True{} True{}:
      {==}
    case 0n 1n+_qq False{} False{}:
      {==}
    case 0n 1n+_qq False{} True{}:
      {==}
    case 0n 1n+_qq True{} False{}:
      {==}
    case 0n 1n+_qq True{} True{}:
      {==}
    case 1n+_pp 0n False{} False{}:
      {==}
    case 1n+_pp 0n False{} True{}:
      {==}
    case 1n+_pp 0n True{} False{}:
      {==}
    case 1n+_pp 0n True{} True{}:
      {==}
    case 1n+pp 1n+qq False{} False{}:
      cmp_dbl(pp, qq, False{}, False{})
    case 1n+pp 1n+qq False{} True{}:
      cmp_dbl(pp, qq, False{}, True{})
    case 1n+pp 1n+qq True{} False{}:
      cmp_dbl(pp, qq, True{}, False{})
    case 1n+pp 1n+qq True{} True{}:
      cmp_dbl(pp, qq, True{}, True{})

# a word with its lowest bit split off, as a number
law to_nat_con:
  for -pp: Nat
  for bb: Bool
  for -tt: Word(pp)
  {Word.to_nat(1n+pp, WCon{bb, tt}) == Nat.add(bit(bb), Nat.double(Word.to_nat(pp, tt))) : Nat}

# the proof of to_nat_con
def to_nat_con(_pp, bb, _tt):
  match bb:
    case False{}:
      {==}
    case True{}:
      {==}

# Word.cmp answers as Nat.cmp does on the words' numbers
law word_cmp_nat:
  for nn: Nat
  for aw: Word(nn)
  for bw: Word(nn)
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
          +na = Word.to_nat(pp, at)
          +nb = Word.to_nat(pp, bt)
          Equal.trans(Cmp, Word.cmp.fin(ab, bb, Word.cmp(pp, at, bt)), Word.cmp.fin(ab, bb, Nat.cmp(na, nb)),
            Nat.cmp(Word.to_nat(1n+pp, WCon{ab, at}), Word.to_nat(1n+pp, WCon{bb, bt})),
            Equal.cong(Cmp, Cmp, cc => Word.cmp.fin(ab, bb, cc), Word.cmp(pp, at, bt), Nat.cmp(na, nb),
              word_cmp_nat(pp, at, bt)),
            Equal.trans(Cmp, Word.cmp.fin(ab, bb, Nat.cmp(na, nb)),
              Nat.cmp(Nat.add(bit(ab), Nat.double(na)), Nat.add(bit(bb), Nat.double(nb))),
              Nat.cmp(Word.to_nat(1n+pp, WCon{ab, at}), Word.to_nat(1n+pp, WCon{bb, bt})),
              Equal.sym(Cmp, Nat.cmp(Nat.add(bit(ab), Nat.double(na)), Nat.add(bit(bb), Nat.double(nb))),
                Word.cmp.fin(ab, bb, Nat.cmp(na, nb)), cmp_dbl(na, nb, ab, bb)),
              Equal.trans(Cmp, Nat.cmp(Nat.add(bit(ab), Nat.double(na)), Nat.add(bit(bb), Nat.double(nb))),
                Nat.cmp(Word.to_nat(1n+pp, WCon{ab, at}), Nat.add(bit(bb), Nat.double(nb))),
                Nat.cmp(Word.to_nat(1n+pp, WCon{ab, at}), Word.to_nat(1n+pp, WCon{bb, bt})),
                Equal.cong(Nat, Cmp, xx => Nat.cmp(xx, Nat.add(bit(bb), Nat.double(nb))),
                  Nat.add(bit(ab), Nat.double(na)), Word.to_nat(1n+pp, WCon{ab, at}),
                  Equal.sym(Nat, Word.to_nat(1n+pp, WCon{ab, at}), Nat.add(bit(ab), Nat.double(na)),
                    to_nat_con(pp, ab, at))),
                Equal.cong(Nat, Cmp, xx => Nat.cmp(Word.to_nat(1n+pp, WCon{ab, at}), xx),
                  Nat.add(bit(bb), Nat.double(nb)), Word.to_nat(1n+pp, WCon{bb, bt}),
                  Equal.sym(Nat, Word.to_nat(1n+pp, WCon{bb, bt}), Nat.add(bit(bb), Nat.double(nb)),
                    to_nat_con(pp, bb, bt))))))

# U32.is_lt answers as Nat.is_lt does on the numbers
law u32_lt:
  for au: U32
  for bu: U32
  {U32.is_lt(au, bu) == Nat.is_lt(U32.to_nat(au), U32.to_nat(bu)) : Bool}

# the proof of u32_lt
def u32_lt(au, bu):
  match au bu:
    case U32{xw} U32{yw}:
      Equal.cong(Cmp, Bool, cc => Cmp.is_lt(cc), Word.cmp(32n, xw, yw),
        Nat.cmp(Word.to_nat(32n, xw), Word.to_nat(32n, yw)), word_cmp_nat(32n, xw, yw))

# U32.is_le answers as Nat.is_le does on the numbers
law u32_le:
  for au: U32
  for bu: U32
  {U32.is_le(au, bu) == Nat.is_le(U32.to_nat(au), U32.to_nat(bu)) : Bool}

# the proof of u32_le
def u32_le(au, bu):
  match au bu:
    case U32{xw} U32{yw}:
      Equal.cong(Cmp, Bool, cc => Cmp.is_le(cc), Word.cmp(32n, xw, yw),
        Nat.cmp(Word.to_nat(32n, xw), Word.to_nat(32n, yw)), word_cmp_nat(32n, xw, yw))

# U32.is_eq answers as Nat.is_eq does on the numbers
law u32_eq:
  for au: U32
  for bu: U32
  {U32.is_eq(au, bu) == Nat.is_eq(U32.to_nat(au), U32.to_nat(bu)) : Bool}

# the proof of u32_eq
def u32_eq(au, bu):
  match au bu:
    case U32{xw} U32{yw}:
      Equal.cong(Cmp, Bool, cc => Cmp.is_eq(cc), Word.cmp(32n, xw, yw),
        Nat.cmp(Word.to_nat(32n, xw), Word.to_nat(32n, yw)), word_cmp_nat(32n, xw, yw))

# a lowest bit of zero on the right does not change what is_lt says of the rest
law fin_lt:
  for cc: Bool
  for tt: Cmp
  for hh: {Cmp.is_lt(Word.cmp.fin(cc, False{}, tt)) == True{} : Bool}
  {Cmp.is_lt(tt) == True{} : Bool}

# the proof of fin_lt
def fin_lt(cc, tt, hh):
  match cc tt:
    case False{} LT{}:
      {==}
    case False{} EQ{}:
      Empty.absurd({False{} == True{} : Bool}, U32L.false_true(hh))
    case False{} GT{}:
      Empty.absurd({False{} == True{} : Bool}, U32L.false_true(hh))
    case True{} LT{}:
      {==}
    case True{} EQ{}:
      Empty.absurd({False{} == True{} : Bool}, U32L.false_true(hh))
    case True{} GT{}:
      Empty.absurd({False{} == True{} : Bool}, U32L.false_true(hh))

# c + 2x < 2y gives x < y
law lt_half:
  for +cc: Bool
  for +xx: Nat
  for +yy: Nat
  for hh: {Nat.is_lt(Nat.add(bit(cc), Nat.double(xx)), Nat.double(yy)) == True{} : Bool}
  {Nat.is_lt(xx, yy) == True{} : Bool}

# the proof of lt_half
def lt_half(cc, xx, yy, hh):
  fin_lt(cc, Nat.cmp(xx, yy), Equal.trans(Bool, Cmp.is_lt(Word.cmp.fin(cc, False{}, Nat.cmp(xx, yy))),
    Nat.is_lt(Nat.add(bit(cc), Nat.double(xx)), Nat.double(yy)), True{},
    Equal.cong(Cmp, Bool, tt => Cmp.is_lt(tt), Word.cmp.fin(cc, False{}, Nat.cmp(xx, yy)),
      Nat.cmp(Nat.add(bit(cc), Nat.double(xx)), Nat.double(yy)),
      Equal.sym(Cmp, Nat.cmp(Nat.add(bit(cc), Nat.double(xx)), Nat.double(yy)),
        Word.cmp.fin(cc, False{}, Nat.cmp(xx, yy)), cmp_dbl(xx, yy, cc, False{}))), hh))

# the zero word is the number zero
law word_zero_nat:
  for nn: Nat
  {Word.to_nat(nn, Word.zero(nn)) == 0n : Nat}

# the proof of word_zero_nat
def word_zero_nat(nn):
  match nn:
    case 0n:
      {==}
    case 1n+pp:
      Equal.cong(Nat, Nat, xx => Nat.double(xx), Word.to_nat(pp, Word.zero(pp)), 0n, word_zero_nat(pp))

# (a + b) + (c + d) regrouped as (a + c) + (b + d)
law add4:
  for +aa: Nat
  for +bb: Nat
  for +cc: Nat
  for +dd: Nat
  {Nat.add(Nat.add(aa, bb), Nat.add(cc, dd)) == Nat.add(Nat.add(aa, cc), Nat.add(bb, dd)) : Nat}

# the proof of add4
def add4(aa, bb, cc, dd):
  Equal.trans(Nat, Nat.add(Nat.add(aa, bb), Nat.add(cc, dd)), Nat.add(aa, Nat.add(bb, Nat.add(cc, dd))),
    Nat.add(Nat.add(aa, cc), Nat.add(bb, dd)), add_assoc(aa, bb, Nat.add(cc, dd)),
    Equal.trans(Nat, Nat.add(aa, Nat.add(bb, Nat.add(cc, dd))), Nat.add(aa, Nat.add(cc, Nat.add(bb, dd))),
      Nat.add(Nat.add(aa, cc), Nat.add(bb, dd)),
      Equal.cong(Nat, Nat, xx => Nat.add(aa, xx), Nat.add(bb, Nat.add(cc, dd)), Nat.add(cc, Nat.add(bb, dd)),
        add_swap(bb, cc, dd)),
      Equal.sym(Nat, Nat.add(Nat.add(aa, cc), Nat.add(bb, dd)), Nat.add(aa, Nat.add(cc, Nat.add(bb, dd))),
        add_assoc(aa, cc, Nat.add(bb, dd)))))

# the sum one adder bit sees: carry plus two bits plus the doubled rests is
# the sum bit plus double the carry out and the rests
law sum_regroup:
  for +c0: Nat
  for +a0: Nat
  for +b0: Nat
  for +s0: Nat
  for +k0: Nat
  for +na: Nat
  for +nb: Nat
  for ee: {Nat.add(c0, Nat.add(a0, b0)) == Nat.add(s0, Nat.double(k0)) : Nat}
  {Nat.add(c0, Nat.add(Nat.add(a0, Nat.double(na)), Nat.add(b0, Nat.double(nb)))) ==
    Nat.add(s0, Nat.double(Nat.add(k0, Nat.add(na, nb)))) : Nat}

# the proof of sum_regroup
def sum_regroup(c0, a0, b0, s0, k0, na, nb, ee):
  +da = Nat.double(na)
  +db = Nat.double(nb)
  +dk = Nat.double(k0)
  Equal.trans(Nat, Nat.add(c0, Nat.add(Nat.add(a0, da), Nat.add(b0, db))),
    Nat.add(c0, Nat.add(Nat.add(a0, b0), Nat.add(da, db))),
    Nat.add(s0, Nat.double(Nat.add(k0, Nat.add(na, nb)))),
    Equal.cong(Nat, Nat, xx => Nat.add(c0, xx), Nat.add(Nat.add(a0, da), Nat.add(b0, db)),
      Nat.add(Nat.add(a0, b0), Nat.add(da, db)), add4(a0, da, b0, db)),
    Equal.trans(Nat, Nat.add(c0, Nat.add(Nat.add(a0, b0), Nat.add(da, db))),
      Nat.add(Nat.add(c0, Nat.add(a0, b0)), Nat.add(da, db)),
      Nat.add(s0, Nat.double(Nat.add(k0, Nat.add(na, nb)))),
      Equal.sym(Nat, Nat.add(Nat.add(c0, Nat.add(a0, b0)), Nat.add(da, db)),
        Nat.add(c0, Nat.add(Nat.add(a0, b0), Nat.add(da, db))), add_assoc(c0, Nat.add(a0, b0), Nat.add(da, db))),
      Equal.trans(Nat, Nat.add(Nat.add(c0, Nat.add(a0, b0)), Nat.add(da, db)),
        Nat.add(Nat.add(s0, dk), Nat.add(da, db)),
        Nat.add(s0, Nat.double(Nat.add(k0, Nat.add(na, nb)))),
        Equal.cong(Nat, Nat, xx => Nat.add(xx, Nat.add(da, db)), Nat.add(c0, Nat.add(a0, b0)),
          Nat.add(s0, dk), ee),
        Equal.trans(Nat, Nat.add(Nat.add(s0, dk), Nat.add(da, db)), Nat.add(s0, Nat.add(dk, Nat.add(da, db))),
          Nat.add(s0, Nat.double(Nat.add(k0, Nat.add(na, nb)))), add_assoc(s0, dk, Nat.add(da, db)),
          Equal.cong(Nat, Nat, xx => Nat.add(s0, xx), Nat.add(dk, Nat.add(da, db)),
            Nat.double(Nat.add(k0, Nat.add(na, nb))),
            Equal.trans(Nat, Nat.add(dk, Nat.add(da, db)), Nat.add(dk, Nat.double(Nat.add(na, nb))),
              Nat.double(Nat.add(k0, Nat.add(na, nb))),
              Equal.cong(Nat, Nat, xx => Nat.add(dk, xx), Nat.add(da, db), Nat.double(Nat.add(na, nb)),
                Equal.sym(Nat, Nat.double(Nat.add(na, nb)), Nat.add(da, db), double_dist(na, nb))),
              Equal.sym(Nat, Nat.double(Nat.add(k0, Nat.add(na, nb))), Nat.add(dk, Nat.double(Nat.add(na, nb))),
                double_dist(k0, Nat.add(na, nb)))))))))

# ---- Word add, shift and multiply read as Nat ----

# one bit of the adder: when the low bits sum to s + 2k and the rest adds up,
# the word adds up
law adc.arm:
  for +pp: Nat
  for +at: Word(pp)
  for +bt: Word(pp)
  for +ab: Bool
  for +bb: Bool
  for +cc: Bool
  for +ss: Bool
  for +kk: Bool
  for e_bits: {Nat.add(bit(cc), Nat.add(bit(ab), bit(bb))) == Nat.add(bit(ss), Nat.double(bit(kk))) : Nat}
  for hh: {Nat.is_lt(Nat.add(bit(cc), Nat.add(Word.to_nat(1n+pp, WCon{ab, at}), Word.to_nat(1n+pp, WCon{bb, bt}))),
    Nat.pow(2n, 1n+pp)) == True{} : Bool}
  for ih: {Nat.is_lt(Nat.add(bit(kk), Nat.add(Word.to_nat(pp, at), Word.to_nat(pp, bt))), Nat.pow(2n, pp)) == True{} :
    Bool} -> {Word.to_nat(pp, Word.adc(pp, at, bt, False{}, kk)) ==
    Nat.add(bit(kk), Nat.add(Word.to_nat(pp, at), Word.to_nat(pp, bt))) : Nat}
  {Word.to_nat(1n+pp, WCon{ss, Word.adc(pp, at, bt, False{}, kk)}) ==
    Nat.add(bit(cc), Nat.add(Word.to_nat(1n+pp, WCon{ab, at}), Word.to_nat(1n+pp, WCon{bb, bt}))) : Nat}

# the proof of adc.arm
def adc.arm(pp, at, bt, ab, bb, cc, ss, kk, e_bits, hh, ih):
  +na = Word.to_nat(pp, at)
  +nb = Word.to_nat(pp, bt)
  +mm = Nat.add(bit(kk), Nat.add(na, nb))
  +wa = Word.to_nat(1n+pp, WCon{ab, at})
  +wb = Word.to_nat(1n+pp, WCon{bb, bt})
  +xa = Nat.add(bit(ab), Nat.double(na))
  +xb = Nat.add(bit(bb), Nat.double(nb))
  +e_in = {Equal.trans(Nat, Nat.add(bit(cc), Nat.add(wa, wb)), Nat.add(bit(cc), Nat.add(xa, wb)),
    Nat.add(bit(cc), Nat.add(xa, xb)),
    Equal.cong(Nat, Nat, xx => Nat.add(bit(cc), Nat.add(xx, wb)), wa, xa, to_nat_con(pp, ab, at)),
    Equal.cong(Nat, Nat, xx => Nat.add(bit(cc), Nat.add(xa, xx)), wb, xb, to_nat_con(pp, bb, bt))) :
    {Nat.add(bit(cc), Nat.add(wa, wb)) == Nat.add(bit(cc), Nat.add(xa, xb)) : Nat}}
  +e_all = {Equal.trans(Nat, Nat.add(bit(cc), Nat.add(wa, wb)), Nat.add(bit(cc), Nat.add(xa, xb)),
    Nat.add(bit(ss), Nat.double(mm)), e_in, sum_regroup(bit(cc), bit(ab), bit(bb), bit(ss), bit(kk), na, nb, e_bits)) :
    {Nat.add(bit(cc), Nat.add(wa, wb)) == Nat.add(bit(ss), Nat.double(mm)) : Nat}}
  +h2 = {lt_rw_r(Nat.add(bit(ss), Nat.double(mm)), Nat.pow(2n, 1n+pp), Nat.double(Nat.pow(2n, pp)), pow2_succ(pp),
    lt_rw_l(Nat.add(bit(cc), Nat.add(wa, wb)), Nat.add(bit(ss), Nat.double(mm)), Nat.pow(2n, 1n+pp), e_all, hh)) :
    {Nat.is_lt(Nat.add(bit(ss), Nat.double(mm)), Nat.double(Nat.pow(2n, pp))) == True{} : Bool}}
  +er = {ih(lt_half(ss, mm, Nat.pow(2n, pp), h2)) : {Word.to_nat(pp, Word.adc(pp, at, bt, False{}, kk)) == mm : Nat}}
  Equal.trans(Nat, Word.to_nat(1n+pp, WCon{ss, Word.adc(pp, at, bt, False{}, kk)}),
    Nat.add(bit(ss), Nat.double(Word.to_nat(pp, Word.adc(pp, at, bt, False{}, kk)))),
    Nat.add(bit(cc), Nat.add(wa, wb)),
    to_nat_con(pp, ss, Word.adc(pp, at, bt, False{}, kk)),
    Equal.trans(Nat, Nat.add(bit(ss), Nat.double(Word.to_nat(pp, Word.adc(pp, at, bt, False{}, kk)))),
      Nat.add(bit(ss), Nat.double(mm)), Nat.add(bit(cc), Nat.add(wa, wb)),
      Equal.cong(Nat, Nat, xx => Nat.add(bit(ss), Nat.double(xx)), Word.to_nat(pp, Word.adc(pp, at, bt, False{}, kk)),
        mm, er),
      Equal.sym(Nat, Nat.add(bit(cc), Nat.add(wa, wb)), Nat.add(bit(ss), Nat.double(mm)), e_all)))

# the adder with carry in c, when the sum is below 2^n, is the sum
law adc_nat:
  for nn: Nat
  for aw: Word(nn)
  for bw: Word(nn)
  for cc: Bool
  for hh: {Nat.is_lt(Nat.add(bit(cc), Nat.add(Word.to_nat(nn, aw), Word.to_nat(nn, bw))), Nat.pow(2n, nn)) ==
    True{} : Bool}
  {Word.to_nat(nn, Word.adc(nn, aw, bw, False{}, cc)) ==
    Nat.add(bit(cc), Nat.add(Word.to_nat(nn, aw), Word.to_nat(nn, bw))) : Nat}

# the proof of adc_nat
def adc_nat(nn, aw, bw, cc, hh):
  match nn:
    case 0n:
      match aw bw cc:
        case WNil{} WNil{} False{}:
          {==}
        case WNil{} WNil{} True{}:
          Empty.absurd({0n == 1n : Nat}, U32L.false_true(hh))
    case 1n+(+pp):
      match aw bw cc:
        case WCon{False{}, +at} WCon{False{}, +bt} False{}:
          adc.arm(pp, at, bt, False{}, False{}, False{}, False{}, False{}, {==}, hh,
            xx => adc_nat(pp, at, bt, False{}, xx))
        case WCon{False{}, +at} WCon{False{}, +bt} True{}:
          adc.arm(pp, at, bt, False{}, False{}, True{}, True{}, False{}, {==}, hh,
            xx => adc_nat(pp, at, bt, False{}, xx))
        case WCon{False{}, +at} WCon{True{}, +bt} False{}:
          adc.arm(pp, at, bt, False{}, True{}, False{}, True{}, False{}, {==}, hh,
            xx => adc_nat(pp, at, bt, False{}, xx))
        case WCon{False{}, +at} WCon{True{}, +bt} True{}:
          adc.arm(pp, at, bt, False{}, True{}, True{}, False{}, True{}, {==}, hh,
            xx => adc_nat(pp, at, bt, True{}, xx))
        case WCon{True{}, +at} WCon{False{}, +bt} False{}:
          adc.arm(pp, at, bt, True{}, False{}, False{}, True{}, False{}, {==}, hh,
            xx => adc_nat(pp, at, bt, False{}, xx))
        case WCon{True{}, +at} WCon{False{}, +bt} True{}:
          adc.arm(pp, at, bt, True{}, False{}, True{}, False{}, True{}, {==}, hh,
            xx => adc_nat(pp, at, bt, True{}, xx))
        case WCon{True{}, +at} WCon{True{}, +bt} False{}:
          adc.arm(pp, at, bt, True{}, True{}, False{}, False{}, True{}, {==}, hh,
            xx => adc_nat(pp, at, bt, True{}, xx))
        case WCon{True{}, +at} WCon{True{}, +bt} True{}:
          adc.arm(pp, at, bt, True{}, True{}, True{}, True{}, True{}, {==}, hh,
            xx => adc_nat(pp, at, bt, True{}, xx))

# the empty word shifted with c coming in: c must be 0 to fit below 1
law shl_put_zero:
  for cc: Bool
  for hh: {Nat.is_lt(Nat.add(bit(cc), 0n), 1n) == True{} : Bool}
  {0n == Nat.add(bit(cc), 0n) : Nat}

# the proof of shl_put_zero
def shl_put_zero(cc, hh):
  match cc:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({0n == 1n : Nat}, U32L.false_true(hh))

# shifting a word left with c coming in, when nothing falls off the top, is
# c + 2 w
law shl_put_nat:
  for nn: Nat
  for +cc: Bool
  for ww: Word(nn)
  for hh: {Nat.is_lt(Nat.add(bit(cc), Nat.double(Word.to_nat(nn, ww))), Nat.pow(2n, nn)) == True{} : Bool}
  {Word.to_nat(nn, Word.shl.put(nn, cc, ww)) == Nat.add(bit(cc), Nat.double(Word.to_nat(nn, ww))) : Nat}

# the proof of shl_put_nat
def shl_put_nat(nn, cc, ww, hh):
  match nn:
    case 0n:
      match ww:
        case WNil{}:
          shl_put_zero(cc, hh)
    case 1n+(+pp):
      match ww:
        case WCon{+bb, +tt}:
          +wn = Word.to_nat(1n+pp, WCon{bb, tt})
          +xn = Nat.add(bit(bb), Nat.double(Word.to_nat(pp, tt)))
          +h1 = {lt_half(cc, wn, Nat.pow(2n, pp), lt_rw_r(Nat.add(bit(cc), Nat.double(wn)), Nat.pow(2n, 1n+pp),
            Nat.double(Nat.pow(2n, pp)), pow2_succ(pp), hh)) : {Nat.is_lt(wn, Nat.pow(2n, pp)) == True{} : Bool}}
          +er = {shl_put_nat(pp, bb, tt, lt_rw_l(wn, xn, Nat.pow(2n, pp), to_nat_con(pp, bb, tt), h1)) :
            {Word.to_nat(pp, Word.shl.put(pp, bb, tt)) == xn : Nat}}
          Equal.trans(Nat, Word.to_nat(1n+pp, WCon{cc, Word.shl.put(pp, bb, tt)}),
            Nat.add(bit(cc), Nat.double(Word.to_nat(pp, Word.shl.put(pp, bb, tt)))),
            Nat.add(bit(cc), Nat.double(wn)), to_nat_con(pp, cc, Word.shl.put(pp, bb, tt)),
            Equal.cong(Nat, Nat, xx => Nat.add(bit(cc), Nat.double(xx)), Word.to_nat(pp, Word.shl.put(pp, bb, tt)), wn,
              Equal.trans(Nat, Word.to_nat(pp, Word.shl.put(pp, bb, tt)), xn, wn, er,
                Equal.sym(Nat, wn, xn, to_nat_con(pp, bb, tt)))))

# shifting a word left, when nothing falls off the top, doubles it
law shl_nat:
  for nn: Nat
  for ww: Word(nn)
  for hh: {Nat.is_lt(Nat.double(Word.to_nat(nn, ww)), Nat.pow(2n, nn)) == True{} : Bool}
  {Word.to_nat(nn, Word.shl(nn, ww)) == Nat.double(Word.to_nat(nn, ww)) : Nat}

# the proof of shl_nat
def shl_nat(nn, ww, hh):
  match nn:
    case 0n:
      match ww:
        case WNil{}:
          {==}
    case 1n+(+pp):
      match ww:
        case WCon{+bb, +tt}:
          +wn = Word.to_nat(1n+pp, WCon{bb, tt})
          +xn = Nat.add(bit(bb), Nat.double(Word.to_nat(pp, tt)))
          +h1 = {lt_half(False{}, wn, Nat.pow(2n, pp), lt_rw_r(Nat.double(wn), Nat.pow(2n, 1n+pp),
            Nat.double(Nat.pow(2n, pp)), pow2_succ(pp), hh)) : {Nat.is_lt(wn, Nat.pow(2n, pp)) == True{} : Bool}}
          Equal.cong(Nat, Nat, xx => Nat.double(xx), Word.to_nat(pp, Word.shl.put(pp, bb, tt)), wn,
            Equal.trans(Nat, Word.to_nat(pp, Word.shl.put(pp, bb, tt)), xn, wn,
              shl_put_nat(pp, bb, tt, lt_rw_l(wn, xn, Nat.pow(2n, pp), to_nat_con(pp, bb, tt), h1)),
              Equal.sym(Nat, wn, xn, to_nat_con(pp, bb, tt))))

# one clear bit of the multiplier, as numbers: the accumulator acn, the
# multiplicand bn, its shift sn and the result rn. When the shift is exact
# below the bound, a multiplier of 2a on bn is one of a on sn.
law mulgo.step:
  for aa: Nat
  for +acn: Nat
  for +bn: Nat
  for +sn: Nat
  for +rn: Nat
  for +top: Nat
  for +hh: {Nat.is_lt(Nat.add(acn, Nat.mul(Nat.double(aa), bn)), top) == True{} : Bool}
  for hs: {Nat.is_lt(Nat.double(bn), top) == True{} : Bool} -> {sn == Nat.double(bn) : Nat}
  for ih: {Nat.is_lt(Nat.add(acn, Nat.mul(aa, sn)), top) == True{} : Bool} ->
    {rn == Nat.add(acn, Nat.mul(aa, sn)) : Nat}
  {rn == Nat.add(acn, Nat.mul(Nat.double(aa), bn)) : Nat}

# the proof of mulgo.step
def mulgo.step(aa, acn, bn, sn, rn, top, hh, hs, ih):
  match aa:
    case 0n:
      ih(hh)
    case 1n+(+pa):
      +rr = Nat.mul(Nat.double(pa), bn)
      +h1 = {lt_add_l(acn, Nat.add(bn, Nat.add(bn, rr)), top, hh) :
        {Nat.is_lt(Nat.add(bn, Nat.add(bn, rr)), top) == True{} : Bool}}
      +h2 = {lt_add_r(Nat.add(bn, bn), rr, top, lt_rw_l(Nat.add(bn, Nat.add(bn, rr)), Nat.add(Nat.add(bn, bn), rr), top,
        Equal.sym(Nat, Nat.add(Nat.add(bn, bn), rr), Nat.add(bn, Nat.add(bn, rr)), add_assoc(bn, bn, rr)), h1)) :
        {Nat.is_lt(Nat.add(bn, bn), top) == True{} : Bool}}
      +es = {hs(lt_rw_l(Nat.add(bn, bn), Nat.double(bn), top, Equal.sym(Nat, Nat.double(bn), Nat.add(bn, bn),
        double_add(bn)), h2)) : {sn == Nat.double(bn) : Nat}}
      +em = {Equal.trans(Nat, Nat.mul(1n+pa, sn), Nat.mul(1n+pa, Nat.double(bn)), Nat.mul(Nat.double(1n+pa), bn),
        Equal.cong(Nat, Nat, xx => Nat.mul(1n+pa, xx), sn, Nat.double(bn), es),
        Equal.trans(Nat, Nat.mul(1n+pa, Nat.double(bn)), Nat.double(Nat.mul(1n+pa, bn)), Nat.mul(Nat.double(1n+pa), bn),
          mul_double_r(1n+pa, bn),
          Equal.sym(Nat, Nat.mul(Nat.double(1n+pa), bn), Nat.double(Nat.mul(1n+pa, bn)), mul_double(1n+pa, bn)))) :
        {Nat.mul(1n+pa, sn) == Nat.mul(Nat.double(1n+pa), bn) : Nat}}
      +ea = {Equal.cong(Nat, Nat, xx => Nat.add(acn, xx), Nat.mul(1n+pa, sn), Nat.mul(Nat.double(1n+pa), bn), em) :
        {Nat.add(acn, Nat.mul(1n+pa, sn)) == Nat.add(acn, Nat.mul(Nat.double(1n+pa), bn)) : Nat}}
      Equal.trans(Nat, rn, Nat.add(acn, Nat.mul(1n+pa, sn)), Nat.add(acn, Nat.mul(Nat.double(1n+pa), bn)),
        ih(lt_rw_l(Nat.add(acn, Nat.mul(Nat.double(1n+pa), bn)), Nat.add(acn, Nat.mul(1n+pa, sn)), top,
          Equal.sym(Nat, Nat.add(acn, Nat.mul(1n+pa, sn)), Nat.add(acn, Nat.mul(Nat.double(1n+pa), bn)), ea), hh)),
        ea)

# shift-and-add multiplication, when acc + a * b stays below 2^n, is acc + a * b
law mulgo_nat:
  for +nn: Nat
  for mm: Nat
  for aw: Word(mm)
  for +bw: Word(nn)
  for +acc: Word(nn)
  for hh: {Nat.is_lt(Nat.add(Word.to_nat(nn, acc), Nat.mul(Word.to_nat(mm, aw), Word.to_nat(nn, bw))),
    Nat.pow(2n, nn)) == True{} : Bool}
  {Word.to_nat(nn, Word.mul.go(nn, mm, aw, bw, acc)) ==
    Nat.add(Word.to_nat(nn, acc), Nat.mul(Word.to_nat(mm, aw), Word.to_nat(nn, bw))) : Nat}

# the proof of mulgo_nat
def mulgo_nat(nn, mm, aw, bw, acc, hh):
  match mm:
    case 0n:
      match aw:
        case WNil{}:
          Equal.sym(Nat, Nat.add(Word.to_nat(nn, acc), 0n), Word.to_nat(nn, acc), add_zero(Word.to_nat(nn, acc)))
    case 1n+(+qq):
      match aw:
        case WCon{False{}, +at}:
          mulgo.step(Word.to_nat(qq, at), Word.to_nat(nn, acc), Word.to_nat(nn, bw), Word.to_nat(nn, Word.shl(nn, bw)),
            Word.to_nat(nn, Word.mul.go(nn, qq, at, Word.shl(nn, bw), acc)), Nat.pow(2n, nn), hh,
            xx => shl_nat(nn, bw, xx), yy => mulgo_nat(nn, qq, at, Word.shl(nn, bw), acc, yy))
        case WCon{True{}, +at}:
          +an = Word.to_nat(nn, acc)
          +bn = Word.to_nat(nn, bw)
          +rr = Nat.mul(Nat.double(Word.to_nat(qq, at)), bn)
          +top = Nat.pow(2n, nn)
          +ac2 = Word.add(nn, acc, bw)
          +ex = {add_assoc(an, bn, rr) : {Nat.add(Nat.add(an, bn), rr) == Nat.add(an, Nat.add(bn, rr)) : Nat}}
          +h1 = {lt_rw_l(Nat.add(an, Nat.add(bn, rr)), Nat.add(Nat.add(an, bn), rr), top,
            Equal.sym(Nat, Nat.add(Nat.add(an, bn), rr), Nat.add(an, Nat.add(bn, rr)), ex), hh) :
            {Nat.is_lt(Nat.add(Nat.add(an, bn), rr), top) == True{} : Bool}}
          +ea = {adc_nat(nn, acc, bw, False{}, lt_add_r(Nat.add(an, bn), rr, top, h1)) :
            {Word.to_nat(nn, ac2) == Nat.add(an, bn) : Nat}}
          +h2 = {lt_rw_l(Nat.add(Nat.add(an, bn), rr), Nat.add(Word.to_nat(nn, ac2), rr), top,
            Equal.cong(Nat, Nat, xx => Nat.add(xx, rr), Nat.add(an, bn), Word.to_nat(nn, ac2),
              Equal.sym(Nat, Word.to_nat(nn, ac2), Nat.add(an, bn), ea)), h1) :
            {Nat.is_lt(Nat.add(Word.to_nat(nn, ac2), rr), top) == True{} : Bool}}
          +e1 = {mulgo.step(Word.to_nat(qq, at), Word.to_nat(nn, ac2), bn, Word.to_nat(nn, Word.shl(nn, bw)),
            Word.to_nat(nn, Word.mul.go(nn, qq, at, Word.shl(nn, bw), ac2)), top, h2,
            xx => shl_nat(nn, bw, xx), yy => mulgo_nat(nn, qq, at, Word.shl(nn, bw), ac2, yy)) :
            {Word.to_nat(nn, Word.mul.go(nn, qq, at, Word.shl(nn, bw), ac2)) ==
              Nat.add(Word.to_nat(nn, ac2), rr) : Nat}}
          Equal.trans(Nat, Word.to_nat(nn, Word.mul.go(nn, qq, at, Word.shl(nn, bw), ac2)),
            Nat.add(Word.to_nat(nn, ac2), rr), Nat.add(an, Nat.add(bn, rr)), e1,
            Equal.trans(Nat, Nat.add(Word.to_nat(nn, ac2), rr), Nat.add(Nat.add(an, bn), rr),
              Nat.add(an, Nat.add(bn, rr)),
              Equal.cong(Nat, Nat, xx => Nat.add(xx, rr), Word.to_nat(nn, ac2), Nat.add(an, bn), ea), ex))


# a lowest bit of zero on the right keeps a less-than
law fin_lt_back:
  for cc: Bool
  for tt: Cmp
  for hh: {Cmp.is_lt(tt) == True{} : Bool}
  {Cmp.is_lt(Word.cmp.fin(cc, False{}, tt)) == True{} : Bool}

# the proof of fin_lt_back
def fin_lt_back(cc, tt, hh):
  match tt:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({Cmp.is_lt(Word.cmp.fin(cc, False{}, EQ{})) == True{} : Bool}, U32L.false_true(hh))
    case GT{}:
      Empty.absurd({False{} == True{} : Bool}, U32L.false_true(hh))

# every n-bit word is below 2^n
law word_lt_pow:
  for nn: Nat
  for ww: Word(nn)
  {Nat.is_lt(Word.to_nat(nn, ww), Nat.pow(2n, nn)) == True{} : Bool}

# the proof of word_lt_pow
def word_lt_pow(nn, ww):
  match nn:
    case 0n:
      match ww:
        case WNil{}:
          {==}
    case 1n+(+pp):
      match ww:
        case WCon{+bb, +tt}:
          +tn = Word.to_nat(pp, tt)
          +top = Nat.pow(2n, pp)
          +xn = Nat.add(bit(bb), Nat.double(tn))
          +h1 = {Equal.trans(Bool, Nat.is_lt(xn, Nat.double(top)),
            Cmp.is_lt(Word.cmp.fin(bb, False{}, Nat.cmp(tn, top))), True{},
            Equal.cong(Cmp, Bool, cc => Cmp.is_lt(cc), Nat.cmp(xn, Nat.double(top)),
              Word.cmp.fin(bb, False{}, Nat.cmp(tn, top)), cmp_dbl(tn, top, bb, False{})),
            fin_lt_back(bb, Nat.cmp(tn, top), word_lt_pow(pp, tt))) :
            {Nat.is_lt(xn, Nat.double(top)) == True{} : Bool}}
          lt_rw_l(xn, Word.to_nat(1n+pp, WCon{bb, tt}), Nat.pow(2n, 1n+pp),
            Equal.sym(Nat, Word.to_nat(1n+pp, WCon{bb, tt}), xn, to_nat_con(pp, bb, tt)),
            lt_rw_r(xn, Nat.double(top), Nat.pow(2n, 1n+pp), Equal.sym(Nat, Nat.pow(2n, 1n+pp), Nat.double(top),
              pow2_succ(pp)), h1))

# the adder, when the sum is at most some n-bit word's value, is the sum
law adc_below:
  for +nn: Nat
  for +aw: Word(nn)
  for +bw: Word(nn)
  for +cc: Bool
  for +tw: Word(nn)
  for hh: {Nat.is_le(Nat.add(bit(cc), Nat.add(Word.to_nat(nn, aw), Word.to_nat(nn, bw))), Word.to_nat(nn, tw)) ==
    True{} : Bool}
  {Word.to_nat(nn, Word.adc(nn, aw, bw, False{}, cc)) ==
    Nat.add(bit(cc), Nat.add(Word.to_nat(nn, aw), Word.to_nat(nn, bw))) : Nat}

# the proof of adc_below
def adc_below(nn, aw, bw, cc, tw, hh):
  adc_nat(nn, aw, bw, cc, le_lt_trans(Nat.add(bit(cc), Nat.add(Word.to_nat(nn, aw), Word.to_nat(nn, bw))),
    Word.to_nat(nn, tw), Nat.pow(2n, nn), hh, word_lt_pow(nn, tw)))

# the multiplier, when the product is at most some n-bit word's value, is the product
law mul_below:
  for +nn: Nat
  for +aw: Word(nn)
  for +bw: Word(nn)
  for +tw: Word(nn)
  for hh: {Nat.is_le(Nat.mul(Word.to_nat(nn, aw), Word.to_nat(nn, bw)), Word.to_nat(nn, tw)) == True{} : Bool}
  {Word.to_nat(nn, Word.mul(nn, aw, bw)) == Nat.mul(Word.to_nat(nn, aw), Word.to_nat(nn, bw)) : Nat}

# the proof of mul_below
def mul_below(nn, aw, bw, tw, hh):
  +pr = Nat.mul(Word.to_nat(nn, aw), Word.to_nat(nn, bw))
  +top = Nat.pow(2n, nn)
  +zn = Word.to_nat(nn, Word.zero(nn))
  +ez = {word_zero_nat(nn) : {Word.to_nat(nn, Word.zero(nn)) == 0n : Nat}}
  +h0 = {le_lt_trans(pr, Word.to_nat(nn, tw), top, hh, word_lt_pow(nn, tw)) :
    {Nat.is_lt(pr, top) == True{} : Bool}}
  +h1 = {lt_rw_l(pr, Nat.add(zn, pr), top,
    Equal.cong(Nat, Nat, xx => Nat.add(xx, pr), 0n, zn, Equal.sym(Nat, zn, 0n, ez)), h0) :
    {Nat.is_lt(Nat.add(zn, pr), top) == True{} : Bool}}
  Equal.trans(Nat, Word.to_nat(nn, Word.mul.go(nn, nn, aw, bw, Word.zero(nn))), Nat.add(zn, pr), pr,
    mulgo_nat(nn, nn, aw, bw, Word.zero(nn), h1),
    Equal.cong(Nat, Nat, xx => Nat.add(xx, pr), zn, 0n, ez))

# U32 add, when the sum is at most some U32's value, is Nat add
law u32_add_below:
  for au: U32
  for bu: U32
  for tu: U32
  for hh: {Nat.is_le(Nat.add(U32.to_nat(au), U32.to_nat(bu)), U32.to_nat(tu)) == True{} : Bool}
  {U32.to_nat(U32.add(au, bu)) == Nat.add(U32.to_nat(au), U32.to_nat(bu)) : Nat}

# the proof of u32_add_below
def u32_add_below(au, bu, tu, hh):
  match au bu tu:
    case U32{xw} U32{yw} U32{tw}:
      adc_below(32n, xw, yw, False{}, tw, hh)

# U32 mul, when the product is at most some U32's value, is Nat mul
law u32_mul_below:
  for au: U32
  for bu: U32
  for tu: U32
  for hh: {Nat.is_le(Nat.mul(U32.to_nat(au), U32.to_nat(bu)), U32.to_nat(tu)) == True{} : Bool}
  {U32.to_nat(U32.mul(au, bu)) == Nat.mul(U32.to_nat(au), U32.to_nat(bu)) : Nat}

# the proof of u32_mul_below
def u32_mul_below(au, bu, tu, hh):
  match au bu tu:
    case U32{xw} U32{yw} U32{tw}:
      mul_below(32n, xw, yw, tw, hh)

# ---- Nat equality as a Bool ----

# Nat.is_eq says true of a number and itself
law nat_eq_refl:
  for nn: Nat
  {Nat.is_eq(nn, nn) == True{} : Bool}

# the proof of nat_eq_refl
def nat_eq_refl(nn):
  match nn:
    case 0n:
      {==}
    case 1n+pp:
      nat_eq_refl(pp)

# numbers Nat.is_eq says true of are equal
law nat_eq_true:
  for aa: Nat
  for bb: Nat
  for hh: {Nat.is_eq(aa, bb) == True{} : Bool}
  {aa == bb : Nat}

# the proof of nat_eq_true
def nat_eq_true(aa, bb, hh):
  match aa bb:
    case 0n 0n:
      {==}
    case 0n 1n+_qq:
      Empty.absurd({0n == 1n+_qq : Nat}, U32L.false_true(hh))
    case 1n+_pp 0n:
      Empty.absurd({1n+_pp == 0n : Nat}, U32L.false_true(hh))
    case 1n+pp 1n+qq:
      Equal.cong(Nat, Nat, xx => 1n+xx, pp, qq, nat_eq_true(pp, qq, hh))

# ---- the row-major index ----

# y * w + x is below w * h when x < w and y < h
law index_lt:
  for +xn: Nat
  for +yn: Nat
  for +wn: Nat
  for +hn: Nat
  for hx: {Nat.is_lt(xn, wn) == True{} : Bool}
  for hy: {Nat.is_lt(yn, hn) == True{} : Bool}
  {Nat.is_lt(Nat.add(Nat.mul(yn, wn), xn), Nat.mul(wn, hn)) == True{} : Bool}

# the proof of index_lt
def index_lt(xn, yn, wn, hn, hx, hy):
  +yw = Nat.mul(yn, wn)
  +h1 = {lt_add_mono(yw, xn, wn, hx) : {Nat.is_lt(Nat.add(yw, xn), Nat.add(yw, wn)) == True{} : Bool}}
  +h2 = {le_mul_mono(1n+yn, hn, wn, Equal.trans(Bool, Nat.is_le(1n+yn, hn), Nat.is_lt(yn, hn), True{},
    Equal.sym(Bool, Nat.is_lt(yn, hn), Nat.is_le(1n+yn, hn), lt_le_succ(yn, hn)), hy)) :
    {Nat.is_le(Nat.add(wn, yw), Nat.mul(hn, wn)) == True{} : Bool}}
  +h3 = {le_rw_l(Nat.add(wn, yw), Nat.add(yw, wn), Nat.mul(hn, wn), add_comm(wn, yw), h2) :
    {Nat.is_le(Nat.add(yw, wn), Nat.mul(hn, wn)) == True{} : Bool}}
  lt_rw_r(Nat.add(yw, xn), Nat.mul(hn, wn), Nat.mul(wn, hn), mul_comm(hn, wn),
    lt_le_trans(Nat.add(yw, xn), Nat.add(yw, wn), Nat.mul(hn, wn), h1, h3))

# the U32 index y * w + x does not wrap when x < w, y < h and w * h is some
# U32's value
law u32_index:
  for +ww: U32
  for +xx: U32
  for +yy: U32
  for +hh: U32
  for +area: U32
  for h_area: {U32.to_nat(area) == Nat.mul(U32.to_nat(ww), U32.to_nat(hh)) : Nat}
  for hx: {Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)) == True{} : Bool}
  for hy: {Nat.is_lt(U32.to_nat(yy), U32.to_nat(hh)) == True{} : Bool}
  {U32.to_nat(U32.add(U32.mul(yy, ww), xx)) == Nat.add(Nat.mul(U32.to_nat(yy), U32.to_nat(ww)), U32.to_nat(xx)) : Nat}

# the proof of u32_index
def u32_index(ww, xx, yy, hh, area, h_area, hx, hy):
  +wn = U32.to_nat(ww)
  +xn = U32.to_nat(xx)
  +yn = U32.to_nat(yy)
  +yw = Nat.mul(yn, wn)
  +h1 = {le_rw_r(Nat.add(yw, xn), Nat.mul(wn, U32.to_nat(hh)), U32.to_nat(area),
    Equal.sym(Nat, U32.to_nat(area), Nat.mul(wn, U32.to_nat(hh)), h_area),
    lt_le(Nat.add(yw, xn), Nat.mul(wn, U32.to_nat(hh)), index_lt(xn, yn, wn, U32.to_nat(hh), hx, hy))) :
    {Nat.is_le(Nat.add(yw, xn), U32.to_nat(area)) == True{} : Bool}}
  +em = {u32_mul_below(yy, ww, area, le_add_r(yw, xn, U32.to_nat(area), h1)) :
    {U32.to_nat(U32.mul(yy, ww)) == yw : Nat}}
  +h2 = {le_rw_l(Nat.add(yw, xn), Nat.add(U32.to_nat(U32.mul(yy, ww)), xn), U32.to_nat(area),
    Equal.cong(Nat, Nat, nn => Nat.add(nn, xn), yw, U32.to_nat(U32.mul(yy, ww)),
      Equal.sym(Nat, U32.to_nat(U32.mul(yy, ww)), yw, em)), h1) :
    {Nat.is_le(Nat.add(U32.to_nat(U32.mul(yy, ww)), xn), U32.to_nat(area)) == True{} : Bool}}
  Equal.trans(Nat, U32.to_nat(U32.add(U32.mul(yy, ww), xx)), Nat.add(U32.to_nat(U32.mul(yy, ww)), xn),
    Nat.add(yw, xn), u32_add_below(U32.mul(yy, ww), xx, area, h2),
    Equal.cong(Nat, Nat, nn => Nat.add(nn, xn), U32.to_nat(U32.mul(yy, ww)), yw, em))

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
      Empty.absurd({vv == cc : U32}, U32L.false_true(Equal.cong(Maybe<&2, U32>, Bool, mm => is_some(mm), None{},
        Some{vv}, hh)))
    case 1n+_pp 0n:
      Equal.sym(U32, cc, vv, Equal.cong(Maybe<&2, U32>, U32, mm => some_or(mm, cc), Some{cc}, Some{vv}, hh))
    case 1n+pp 1n+qq:
      get_replicate(pp, qq, cc, vv, hh)

# an index below the length finds an element
law get_some_lt:
  for xs: List<&2, U32>
  for kk: Nat
  for hh: {Nat.is_lt(kk, List.length(&2, U32, xs)) == True{} : Bool}
  {Maybe.is_some(&2, U32, List.get(&2, U32, xs, kk)) == True{} : Bool}

# the proof of get_some_lt
def get_some_lt(xs, kk, hh):
  match xs kk:
    case Nil{} _kk:
      Empty.absurd({Maybe.is_some(&2, U32, List.get(&2, U32, Nil{}, _kk)) == True{} : Bool}, U32L.false_true(
        Equal.trans(Bool, False{}, Nat.is_lt(_kk, 0n), True{}, lt_zero_false(_kk), hh)))
    case _hd <> _tl 0n:
      {==}
    case _hd <> tl 1n+qq:
      get_some_lt(tl, qq, hh)

# ---- Word sub read as Nat ----

# cancel the same number added on the left of both sides of <=
law le_cancel:
  for mm: Nat
  for -xx: Nat
  for -yy: Nat
  for hh: {Nat.is_le(Nat.add(mm, xx), Nat.add(mm, yy)) == True{} : Bool}
  {Nat.is_le(xx, yy) == True{} : Bool}

# the proof of le_cancel
def le_cancel(mm, xx, yy, hh):
  match mm:
    case 0n:
      hh
    case 1n+pp:
      le_cancel(pp, xx, yy, hh)

# a lowest bit of zero on the left does not change what is_le says of the rest
law fin_le:
  for ss: Bool
  for tt: Cmp
  for hh: {Cmp.is_le(Word.cmp.fin(False{}, ss, tt)) == True{} : Bool}
  {Cmp.is_le(tt) == True{} : Bool}

# the proof of fin_le
def fin_le(ss, tt, hh):
  match ss tt:
    case False{} LT{}:
      {==}
    case False{} EQ{}:
      {==}
    case False{} GT{}:
      Empty.absurd({False{} == True{} : Bool}, U32L.false_true(hh))
    case True{} LT{}:
      {==}
    case True{} EQ{}:
      {==}
    case True{} GT{}:
      Empty.absurd({False{} == True{} : Bool}, U32L.false_true(hh))

# 2x <= s + 2y gives x <= y
law le_half:
  for +ss: Bool
  for +xx: Nat
  for +yy: Nat
  for hh: {Nat.is_le(Nat.double(xx), Nat.add(bit(ss), Nat.double(yy))) == True{} : Bool}
  {Nat.is_le(xx, yy) == True{} : Bool}

# the proof of le_half
def le_half(ss, xx, yy, hh):
  fin_le(ss, Nat.cmp(xx, yy), Equal.trans(Bool, Cmp.is_le(Word.cmp.fin(False{}, ss, Nat.cmp(xx, yy))),
    Nat.is_le(Nat.double(xx), Nat.add(bit(ss), Nat.double(yy))), True{},
    Equal.cong(Cmp, Bool, tt => Cmp.is_le(tt), Word.cmp.fin(False{}, ss, Nat.cmp(xx, yy)),
      Nat.cmp(Nat.double(xx), Nat.add(bit(ss), Nat.double(yy))),
      Equal.sym(Cmp, Nat.cmp(Nat.double(xx), Nat.add(bit(ss), Nat.double(yy))),
        Word.cmp.fin(False{}, ss, Nat.cmp(xx, yy)), cmp_dbl(xx, yy, False{}, ss))), hh))

# the subtractor's regrouping: s + 2r + c + b + 2nb is a + 2 na when the low
# bits give s + c + b = a + 2k and the rest gives r + k + nb = na
law diff_regroup:
  for +s0: Nat
  for +c0: Nat
  for +b0: Nat
  for +a0: Nat
  for +k0: Nat
  for +rn: Nat
  for +nb: Nat
  for +na: Nat
  for ee: {Nat.add(s0, Nat.add(c0, b0)) == Nat.add(a0, Nat.double(k0)) : Nat}
  for ih: {Nat.add(rn, Nat.add(k0, nb)) == na : Nat}
  {Nat.add(Nat.add(s0, Nat.double(rn)), Nat.add(c0, Nat.add(b0, Nat.double(nb)))) ==
    Nat.add(a0, Nat.double(na)) : Nat}

# the proof of diff_regroup
def diff_regroup(s0, c0, b0, a0, k0, rn, nb, na, ee, ih):
  +dr = Nat.double(rn)
  +db = Nat.double(nb)
  +e1 = {Equal.trans(Nat, Nat.add(c0, Nat.add(b0, db)), Nat.add(Nat.add(c0, b0), db), Nat.add(Nat.add(c0, b0), db),
    Equal.sym(Nat, Nat.add(Nat.add(c0, b0), db), Nat.add(c0, Nat.add(b0, db)), add_assoc(c0, b0, db)), {==}) :
    {Nat.add(c0, Nat.add(b0, db)) == Nat.add(Nat.add(c0, b0), db) : Nat}}
  +e2 = {add4(s0, dr, Nat.add(c0, b0), db) :
    {Nat.add(Nat.add(s0, dr), Nat.add(Nat.add(c0, b0), db)) == Nat.add(Nat.add(s0, Nat.add(c0, b0)), Nat.add(dr, db)) :
      Nat}}
  +e3 = {Equal.cong(Nat, Nat, xx => Nat.add(xx, Nat.add(dr, db)), Nat.add(s0, Nat.add(c0, b0)),
    Nat.add(a0, Nat.double(k0)), ee) :
    {Nat.add(Nat.add(s0, Nat.add(c0, b0)), Nat.add(dr, db)) == Nat.add(Nat.add(a0, Nat.double(k0)), Nat.add(dr, db)) :
      Nat}}
  +e4 = {add_assoc(a0, Nat.double(k0), Nat.add(dr, db)) :
    {Nat.add(Nat.add(a0, Nat.double(k0)), Nat.add(dr, db)) == Nat.add(a0, Nat.add(Nat.double(k0), Nat.add(dr, db))) :
      Nat}}
  +e5 = {Equal.trans(Nat, Nat.add(Nat.double(k0), Nat.add(dr, db)), Nat.add(dr, Nat.add(Nat.double(k0), db)),
    Nat.double(na), add_swap(Nat.double(k0), dr, db),
    Equal.trans(Nat, Nat.add(dr, Nat.add(Nat.double(k0), db)), Nat.add(dr, Nat.double(Nat.add(k0, nb))),
      Nat.double(na),
      Equal.cong(Nat, Nat, xx => Nat.add(dr, xx), Nat.add(Nat.double(k0), db), Nat.double(Nat.add(k0, nb)),
        Equal.sym(Nat, Nat.double(Nat.add(k0, nb)), Nat.add(Nat.double(k0), db), double_dist(k0, nb))),
      Equal.trans(Nat, Nat.add(dr, Nat.double(Nat.add(k0, nb))), Nat.double(Nat.add(rn, Nat.add(k0, nb))),
        Nat.double(na), Equal.sym(Nat, Nat.double(Nat.add(rn, Nat.add(k0, nb))),
          Nat.add(dr, Nat.double(Nat.add(k0, nb))), double_dist(rn, Nat.add(k0, nb))),
        Equal.cong(Nat, Nat, xx => Nat.double(xx), Nat.add(rn, Nat.add(k0, nb)), na, ih)))) :
    {Nat.add(Nat.double(k0), Nat.add(dr, db)) == Nat.double(na) : Nat}}
  Equal.trans(Nat, Nat.add(Nat.add(s0, dr), Nat.add(c0, Nat.add(b0, db))),
    Nat.add(Nat.add(s0, dr), Nat.add(Nat.add(c0, b0), db)), Nat.add(a0, Nat.double(na)),
    Equal.cong(Nat, Nat, xx => Nat.add(Nat.add(s0, dr), xx), Nat.add(c0, Nat.add(b0, db)),
      Nat.add(Nat.add(c0, b0), db), e1),
    Equal.trans(Nat, Nat.add(Nat.add(s0, dr), Nat.add(Nat.add(c0, b0), db)),
      Nat.add(Nat.add(s0, Nat.add(c0, b0)), Nat.add(dr, db)), Nat.add(a0, Nat.double(na)), e2,
      Equal.trans(Nat, Nat.add(Nat.add(s0, Nat.add(c0, b0)), Nat.add(dr, db)),
        Nat.add(Nat.add(a0, Nat.double(k0)), Nat.add(dr, db)), Nat.add(a0, Nat.double(na)), e3,
        Equal.trans(Nat, Nat.add(Nat.add(a0, Nat.double(k0)), Nat.add(dr, db)),
          Nat.add(a0, Nat.add(Nat.double(k0), Nat.add(dr, db))), Nat.add(a0, Nat.double(na)), e4,
          Equal.cong(Nat, Nat, xx => Nat.add(a0, xx), Nat.add(Nat.double(k0), Nat.add(dr, db)), Nat.double(na), e5)))))

# the subtractor's bound, halved: when c + b + 2nb <= a + 2na and the low bits
# give s + c + b = a + 2k, then k + nb <= na
law diff_half:
  for +ss: Bool
  for +c0: Nat
  for +b0: Nat
  for +a0: Nat
  for +k0: Nat
  for +nb: Nat
  for +na: Nat
  for ee: {Nat.add(bit(ss), Nat.add(c0, b0)) == Nat.add(a0, Nat.double(k0)) : Nat}
  for hh: {Nat.is_le(Nat.add(c0, Nat.add(b0, Nat.double(nb))), Nat.add(a0, Nat.double(na))) == True{} : Bool}
  {Nat.is_le(Nat.add(k0, nb), na) == True{} : Bool}

# the proof of diff_half
def diff_half(ss, c0, b0, a0, k0, nb, na, ee, hh):
  +s0 = bit(ss)
  +db = Nat.double(nb)
  +dn = Nat.double(na)
  +h1 = {le_add_mono(s0, Nat.add(c0, Nat.add(b0, db)), Nat.add(a0, dn), hh) :
    {Nat.is_le(Nat.add(s0, Nat.add(c0, Nat.add(b0, db))), Nat.add(s0, Nat.add(a0, dn))) == True{} : Bool}}
  +el = {Equal.trans(Nat, Nat.add(s0, Nat.add(c0, Nat.add(b0, db))), Nat.add(s0, Nat.add(Nat.add(c0, b0), db)),
    Nat.add(a0, Nat.add(Nat.double(k0), db)),
    Equal.cong(Nat, Nat, xx => Nat.add(s0, xx), Nat.add(c0, Nat.add(b0, db)), Nat.add(Nat.add(c0, b0), db),
      Equal.sym(Nat, Nat.add(Nat.add(c0, b0), db), Nat.add(c0, Nat.add(b0, db)), add_assoc(c0, b0, db))),
    Equal.trans(Nat, Nat.add(s0, Nat.add(Nat.add(c0, b0), db)), Nat.add(Nat.add(s0, Nat.add(c0, b0)), db),
      Nat.add(a0, Nat.add(Nat.double(k0), db)),
      Equal.sym(Nat, Nat.add(Nat.add(s0, Nat.add(c0, b0)), db), Nat.add(s0, Nat.add(Nat.add(c0, b0), db)),
        add_assoc(s0, Nat.add(c0, b0), db)),
      Equal.trans(Nat, Nat.add(Nat.add(s0, Nat.add(c0, b0)), db), Nat.add(Nat.add(a0, Nat.double(k0)), db),
        Nat.add(a0, Nat.add(Nat.double(k0), db)),
        Equal.cong(Nat, Nat, xx => Nat.add(xx, db), Nat.add(s0, Nat.add(c0, b0)), Nat.add(a0, Nat.double(k0)), ee),
        add_assoc(a0, Nat.double(k0), db)))) :
    {Nat.add(s0, Nat.add(c0, Nat.add(b0, db))) == Nat.add(a0, Nat.add(Nat.double(k0), db)) : Nat}}
  +h2 = {le_rw_l(Nat.add(s0, Nat.add(c0, Nat.add(b0, db))), Nat.add(a0, Nat.add(Nat.double(k0), db)),
    Nat.add(s0, Nat.add(a0, dn)), el, h1) :
    {Nat.is_le(Nat.add(a0, Nat.add(Nat.double(k0), db)), Nat.add(s0, Nat.add(a0, dn))) == True{} : Bool}}
  +h3 = {le_rw_r(Nat.add(a0, Nat.add(Nat.double(k0), db)), Nat.add(s0, Nat.add(a0, dn)), Nat.add(a0, Nat.add(s0, dn)),
    add_swap(s0, a0, dn), h2) :
    {Nat.is_le(Nat.add(a0, Nat.add(Nat.double(k0), db)), Nat.add(a0, Nat.add(s0, dn))) == True{} : Bool}}
  +h4 = {le_cancel(a0, Nat.add(Nat.double(k0), db), Nat.add(s0, dn), h3) :
    {Nat.is_le(Nat.add(Nat.double(k0), db), Nat.add(s0, dn)) == True{} : Bool}}
  le_half(ss, Nat.add(k0, nb), na, le_rw_l(Nat.add(Nat.double(k0), db), Nat.double(Nat.add(k0, nb)), Nat.add(s0, dn),
    Equal.sym(Nat, Nat.double(Nat.add(k0, nb)), Nat.add(Nat.double(k0), db), double_dist(k0, nb)), h4))

# one bit of the subtractor: when the low bits give s + c + b = a + 2k and
# the rest subtracts, the word subtracts
law sbc.arm:
  for +pp: Nat
  for +at: Word(pp)
  for +bt: Word(pp)
  for +ab: Bool
  for +bb: Bool
  for +cc: Bool
  for +ss: Bool
  for +kk: Bool
  for +e_bits: {Nat.add(bit(ss), Nat.add(bit(Bool.not(cc)), bit(bb))) == Nat.add(bit(ab),
    Nat.double(bit(Bool.not(kk)))) :
    Nat}
  for hh: {Nat.is_le(Nat.add(bit(Bool.not(cc)), Word.to_nat(1n+pp, WCon{bb, bt})), Word.to_nat(1n+pp, WCon{ab, at})) ==
    True{} : Bool}
  for ih: {Nat.is_le(Nat.add(bit(Bool.not(kk)), Word.to_nat(pp, bt)), Word.to_nat(pp, at)) == True{} : Bool} ->
    {Nat.add(Word.to_nat(pp, Word.adc(pp, at, bt, True{}, kk)), Nat.add(bit(Bool.not(kk)), Word.to_nat(pp, bt))) ==
      Word.to_nat(pp, at) : Nat}
  {Nat.add(Word.to_nat(1n+pp, WCon{ss, Word.adc(pp, at, bt, True{}, kk)}),
    Nat.add(bit(Bool.not(cc)), Word.to_nat(1n+pp, WCon{bb, bt}))) == Word.to_nat(1n+pp, WCon{ab, at}) : Nat}

# the proof of sbc.arm
def sbc.arm(pp, at, bt, ab, bb, cc, ss, kk, e_bits, hh, ih):
  +na = Word.to_nat(pp, at)
  +nb = Word.to_nat(pp, bt)
  +c0 = bit(Bool.not(cc))
  +k0 = bit(Bool.not(kk))
  +xa = Nat.add(bit(ab), Nat.double(na))
  +xb = Nat.add(bit(bb), Nat.double(nb))
  +wa = Word.to_nat(1n+pp, WCon{ab, at})
  +wb = Word.to_nat(1n+pp, WCon{bb, bt})
  +rw = Word.adc(pp, at, bt, True{}, kk)
  +rn = Word.to_nat(pp, rw)
  +ea = {to_nat_con(pp, ab, at) : {wa == xa : Nat}}
  +eb = {to_nat_con(pp, bb, bt) : {wb == xb : Nat}}
  +h1 = {le_rw_r(Nat.add(c0, xb), wa, xa, ea, le_rw_l(Nat.add(c0, wb), Nat.add(c0, xb), wa,
    Equal.cong(Nat, Nat, xx => Nat.add(c0, xx), wb, xb, eb), hh)) :
    {Nat.is_le(Nat.add(c0, xb), xa) == True{} : Bool}}
  +er = {ih(diff_half(ss, c0, bit(bb), bit(ab), k0, nb, na, e_bits, h1)) :
    {Nat.add(rn, Nat.add(k0, nb)) == na : Nat}}
  +eg = {diff_regroup(bit(ss), c0, bit(bb), bit(ab), k0, rn, nb, na, e_bits, er) :
    {Nat.add(Nat.add(bit(ss), Nat.double(rn)), Nat.add(c0, xb)) == xa : Nat}}
  Equal.trans(Nat, Nat.add(Word.to_nat(1n+pp, WCon{ss, rw}), Nat.add(c0, wb)),
    Nat.add(Nat.add(bit(ss), Nat.double(rn)), Nat.add(c0, wb)), wa,
    Equal.cong(Nat, Nat, xx => Nat.add(xx, Nat.add(c0, wb)), Word.to_nat(1n+pp, WCon{ss, rw}),
      Nat.add(bit(ss), Nat.double(rn)), to_nat_con(pp, ss, rw)),
    Equal.trans(Nat, Nat.add(Nat.add(bit(ss), Nat.double(rn)), Nat.add(c0, wb)),
      Nat.add(Nat.add(bit(ss), Nat.double(rn)), Nat.add(c0, xb)), wa,
      Equal.cong(Nat, Nat, xx => Nat.add(Nat.add(bit(ss), Nat.double(rn)), Nat.add(c0, xx)), wb, xb, eb),
      Equal.trans(Nat, Nat.add(Nat.add(bit(ss), Nat.double(rn)), Nat.add(c0, xb)), xa, wa, eg,
        Equal.sym(Nat, wa, xa, ea))))

# the subtractor with carry in c: when b + (1 - c) <= a, the difference r
# gives r + (1 - c) + b = a
law sbc_nat:
  for nn: Nat
  for aw: Word(nn)
  for bw: Word(nn)
  for cc: Bool
  for hh: {Nat.is_le(Nat.add(bit(Bool.not(cc)), Word.to_nat(nn, bw)), Word.to_nat(nn, aw)) == True{} : Bool}
  {Nat.add(Word.to_nat(nn, Word.adc(nn, aw, bw, True{}, cc)), Nat.add(bit(Bool.not(cc)), Word.to_nat(nn, bw))) ==
    Word.to_nat(nn, aw) : Nat}

# the proof of sbc_nat
def sbc_nat(nn, aw, bw, cc, hh):
  match nn:
    case 0n:
      match aw bw cc:
        case WNil{} WNil{} True{}:
          {==}
        case WNil{} WNil{} False{}:
          Empty.absurd({1n == 0n : Nat}, U32L.false_true(hh))
    case 1n+(+pp):
      match aw bw cc:
        case WCon{False{}, +at} WCon{False{}, +bt} False{}:
          sbc.arm(pp, at, bt, False{}, False{}, False{}, True{}, False{}, {==}, hh,
            xx => sbc_nat(pp, at, bt, False{}, xx))
        case WCon{False{}, +at} WCon{False{}, +bt} True{}:
          sbc.arm(pp, at, bt, False{}, False{}, True{}, False{}, True{}, {==}, hh,
            xx => sbc_nat(pp, at, bt, True{}, xx))
        case WCon{False{}, +at} WCon{True{}, +bt} False{}:
          sbc.arm(pp, at, bt, False{}, True{}, False{}, False{}, False{}, {==}, hh,
            xx => sbc_nat(pp, at, bt, False{}, xx))
        case WCon{False{}, +at} WCon{True{}, +bt} True{}:
          sbc.arm(pp, at, bt, False{}, True{}, True{}, True{}, False{}, {==}, hh,
            xx => sbc_nat(pp, at, bt, False{}, xx))
        case WCon{True{}, +at} WCon{False{}, +bt} False{}:
          sbc.arm(pp, at, bt, True{}, False{}, False{}, False{}, True{}, {==}, hh,
            xx => sbc_nat(pp, at, bt, True{}, xx))
        case WCon{True{}, +at} WCon{False{}, +bt} True{}:
          sbc.arm(pp, at, bt, True{}, False{}, True{}, True{}, True{}, {==}, hh,
            xx => sbc_nat(pp, at, bt, True{}, xx))
        case WCon{True{}, +at} WCon{True{}, +bt} False{}:
          sbc.arm(pp, at, bt, True{}, True{}, False{}, True{}, False{}, {==}, hh,
            xx => sbc_nat(pp, at, bt, False{}, xx))
        case WCon{True{}, +at} WCon{True{}, +bt} True{}:
          sbc.arm(pp, at, bt, True{}, True{}, True{}, False{}, True{}, {==}, hh,
            xx => sbc_nat(pp, at, bt, True{}, xx))

# a minus zero is a
law sub_zero:
  for aa: Nat
  {Nat.sub(aa, 0n) == aa : Nat}

# the proof of sub_zero
def sub_zero(aa):
  match aa:
    case 0n:
      {==}
    case 1n+_pp:
      {==}

# a - b is r when r + b = a
law sub_of_add:
  for +rn: Nat
  for bn: Nat
  for +an: Nat
  for ee: {Nat.add(rn, bn) == an : Nat}
  {Nat.sub(an, bn) == rn : Nat}

# the proof of sub_of_add
def sub_of_add(rn, bn, an, ee):
  match bn:
    case 0n:
      Equal.trans(Nat, Nat.sub(an, 0n), Nat.sub(Nat.add(rn, 0n), 0n), rn,
        Equal.cong(Nat, Nat, xx => Nat.sub(xx, 0n), an, Nat.add(rn, 0n), Equal.sym(Nat, Nat.add(rn, 0n), an, ee)),
        Equal.trans(Nat, Nat.sub(Nat.add(rn, 0n), 0n), Nat.sub(rn, 0n), rn,
          Equal.cong(Nat, Nat, xx => Nat.sub(xx, 0n), Nat.add(rn, 0n), rn, add_zero(rn)), sub_zero(rn)))
    case 1n+(+pb):
      Equal.trans(Nat, Nat.sub(an, 1n+pb), Nat.sub(1n+Nat.add(rn, pb), 1n+pb), rn,
        Equal.cong(Nat, Nat, xx => Nat.sub(xx, 1n+pb), an, 1n+Nat.add(rn, pb),
          Equal.trans(Nat, an, Nat.add(rn, 1n+pb), 1n+Nat.add(rn, pb), Equal.sym(Nat, Nat.add(rn, 1n+pb), an, ee),
            add_succ(rn, pb))),
        sub_of_add(rn, pb, Nat.add(rn, pb), {==}))

# U32 sub, when b <= a, is Nat sub
law u32_sub_nat:
  for +au: U32
  for +bu: U32
  for hh: {Nat.is_le(U32.to_nat(bu), U32.to_nat(au)) == True{} : Bool}
  {U32.to_nat(U32.sub(au, bu)) == Nat.sub(U32.to_nat(au), U32.to_nat(bu)) : Nat}

# the proof of u32_sub_nat
def u32_sub_nat(au, bu, hh):
  match au bu:
    case U32{+xw} U32{+yw}:
      Equal.sym(Nat, Nat.sub(Word.to_nat(32n, xw), Word.to_nat(32n, yw)), Word.to_nat(32n, Word.sub(32n, xw, yw)),
        sub_of_add(Word.to_nat(32n, Word.sub(32n, xw, yw)), Word.to_nat(32n, yw), Word.to_nat(32n, xw),
          sbc_nat(32n, xw, yw, True{}, hh)))

# ---- min and sub ----

# min(a, b) is a when a <= b
law min_of_le:
  for aa: Nat
  for bb: Nat
  for hh: {Nat.is_le(aa, bb) == True{} : Bool}
  {Nat.min(aa, bb) == aa : Nat}

# the proof of min_of_le
def min_of_le(aa, bb, hh):
  match aa bb:
    case 0n _bb:
      {==}
    case 1n+_pa 0n:
      Empty.absurd({0n == 1n+_pa : Nat}, U32L.false_true(hh))
    case 1n+pa 1n+pb:
      Equal.cong(Nat, Nat, xx => 1n+xx, Nat.min(pa, pb), pa, min_of_le(pa, pb, hh))

# min(a, b) is b when a <= b is false
law min_of_gt:
  for aa: Nat
  for bb: Nat
  for hh: {Nat.is_le(aa, bb) == False{} : Bool}
  {Nat.min(aa, bb) == bb : Nat}

# the proof of min_of_gt
def min_of_gt(aa, bb, hh):
  match aa bb:
    case 0n _bb:
      Empty.absurd({0n == _bb : Nat}, U32L.false_true(Equal.trans(Bool, False{}, Nat.is_le(0n, _bb), True{},
        Equal.sym(Bool, Nat.is_le(0n, _bb), False{}, hh), le_zero(_bb))))
    case 1n+_pa 0n:
      {==}
    case 1n+pa 1n+pb:
      Equal.cong(Nat, Nat, xx => 1n+xx, Nat.min(pa, pb), pb, min_of_gt(pa, pb, hh))

# min(a, b) <= b
law min_le_r:
  for aa: Nat
  for bb: Nat
  {Nat.is_le(Nat.min(aa, bb), bb) == True{} : Bool}

# the proof of min_le_r
def min_le_r(aa, bb):
  match aa bb:
    case 0n _bb:
      le_zero(_bb)
    case 1n+_pa 0n:
      {==}
    case 1n+pa 1n+pb:
      min_le_r(pa, pb)

# n <= n + 1
law le_succ:
  for nn: Nat
  {Nat.is_le(nn, 1n+nn) == True{} : Bool}

# the proof of le_succ
def le_succ(nn):
  match nn:
    case 0n:
      {==}
    case 1n+pp:
      le_succ(pp)

# a - b <= a
law sub_le:
  for aa: Nat
  for bb: Nat
  {Nat.is_le(Nat.sub(aa, bb), aa) == True{} : Bool}

# the proof of sub_le
def sub_le(aa, bb):
  match aa bb:
    case 0n 0n:
      {==}
    case 0n 1n+_pb:
      {==}
    case 1n+pa 0n:
      le_refl(pa)
    case 1n+(+pa) 1n+(+pb):
      le_trans(Nat.sub(pa, pb), pa, 1n+pa, sub_le(pa, pb), le_succ(pa))

# b + (a - b) is a when b <= a
law add_sub:
  for bb: Nat
  for aa: Nat
  for hh: {Nat.is_le(bb, aa) == True{} : Bool}
  {Nat.add(bb, Nat.sub(aa, bb)) == aa : Nat}

# the proof of add_sub
def add_sub(bb, aa, hh):
  match bb aa:
    case 0n 0n:
      {==}
    case 0n 1n+_pa:
      {==}
    case 1n+_pb 0n:
      Empty.absurd({Nat.add(1n+_pb, Nat.sub(0n, 1n+_pb)) == 0n : Nat}, U32L.false_true(hh))
    case 1n+pb 1n+pa:
      Equal.cong(Nat, Nat, xx => 1n+xx, Nat.add(pb, Nat.sub(pa, pb)), pa, add_sub(pb, pa, hh))

# a - b is 0 when a <= b
law sub_zero_le:
  for aa: Nat
  for bb: Nat
  for hh: {Nat.is_le(aa, bb) == True{} : Bool}
  {Nat.sub(aa, bb) == 0n : Nat}

# the proof of sub_zero_le
def sub_zero_le(aa, bb, hh):
  match aa bb:
    case 0n 0n:
      {==}
    case 0n 1n+_pb:
      {==}
    case 1n+_pa 0n:
      Empty.absurd({Nat.sub(1n+_pa, 0n) == 0n : Nat}, U32L.false_true(hh))
    case 1n+pa 1n+pb:
      sub_zero_le(pa, pb, hh)

# 0 < a - b gives b < a
law sub_pos:
  for aa: Nat
  for bb: Nat
  for hh: {Nat.is_lt(0n, Nat.sub(aa, bb)) == True{} : Bool}
  {Nat.is_lt(bb, aa) == True{} : Bool}

# the proof of sub_pos
def sub_pos(aa, bb, hh):
  match aa bb:
    case 0n 0n:
      Empty.absurd({False{} == True{} : Bool}, U32L.false_true(hh))
    case 0n 1n+_pb:
      Empty.absurd({False{} == True{} : Bool}, U32L.false_true(hh))
    case 1n+_pa 0n:
      {==}
    case 1n+pa 1n+pb:
      sub_pos(pa, pb, hh)

# x + r <= w gives x <= w - r
law le_sub_of_add:
  for +xx: Nat
  for +rr: Nat
  for +ww: Nat
  for +hh: {Nat.is_le(Nat.add(xx, rr), ww) == True{} : Bool}
  {Nat.is_le(xx, Nat.sub(ww, rr)) == True{} : Bool}

# the proof of le_sub_of_add
def le_sub_of_add(xx, rr, ww, hh):
  +hr = {le_add_r(rr, xx, ww, le_rw_l(Nat.add(xx, rr), Nat.add(rr, xx), ww, add_comm(xx, rr), hh)) :
    {Nat.is_le(rr, ww) == True{} : Bool}}
  le_cancel(rr, xx, Nat.sub(ww, rr), le_rw_r(Nat.add(rr, xx), ww, Nat.add(rr, Nat.sub(ww, rr)),
    Equal.sym(Nat, Nat.add(rr, Nat.sub(ww, rr)), ww, add_sub(rr, ww, hr)),
    le_rw_l(Nat.add(xx, rr), Nat.add(rr, xx), ww, add_comm(xx, rr), hh)))

# a <= b and c <= d give a + c <= b + d
law le_add_both:
  for +aa: Nat
  for +bb: Nat
  for +cc: Nat
  for +dd: Nat
  for hab: {Nat.is_le(aa, bb) == True{} : Bool}
  for hcd: {Nat.is_le(cc, dd) == True{} : Bool}
  {Nat.is_le(Nat.add(aa, cc), Nat.add(bb, dd)) == True{} : Bool}

# the proof of le_add_both
def le_add_both(aa, bb, cc, dd, hab, hcd):
  le_trans(Nat.add(aa, cc), Nat.add(aa, dd), Nat.add(bb, dd), le_add_mono(aa, cc, dd, hcd),
    le_rw_l(Nat.add(dd, aa), Nat.add(aa, dd), Nat.add(bb, dd), add_comm(dd, aa),
      le_rw_r(Nat.add(dd, aa), Nat.add(dd, bb), Nat.add(bb, dd), add_comm(dd, bb), le_add_mono(dd, aa, bb, hab))))

# 0 < n says n is not 0
law pos_eq:
  for nn: Nat
  {Nat.is_lt(0n, nn) == Bool.not(Nat.is_eq(nn, 0n)) : Bool}

# the proof of pos_eq
def pos_eq(nn):
  match nn:
    case 0n:
      {==}
    case 1n+_pp:
      {==}

# ---- take, drop and append ----

# element k after dropping m is element m + k
law get_drop:
  for xs: List<&2, U32>
  for mm: Nat
  for -kk: Nat
  {List.get(&2, U32, List.drop(&2, U32, xs, mm), kk) == List.get(&2, U32, xs, Nat.add(mm, kk)) : Maybe<&2, U32>}

# the proof of get_drop
def get_drop(xs, mm, kk):
  match xs mm:
    case Nil{} _mm:
      {==}
    case _hd <> _tl 0n:
      {==}
    case _hd <> tl 1n+qq:
      get_drop(tl, qq, kk)

# m + k <= length + g gives k <= length after dropping m, + g
law drop_le:
  for xs: List<&2, U32>
  for mm: Nat
  for +kk: Nat
  for +gg: Nat
  for hh: {Nat.is_le(Nat.add(mm, kk), Nat.add(List.length(&2, U32, xs), gg)) == True{} : Bool}
  {Nat.is_le(kk, Nat.add(List.length(&2, U32, List.drop(&2, U32, xs, mm)), gg)) == True{} : Bool}

# the proof of drop_le
def drop_le(xs, mm, kk, gg, hh):
  match xs mm:
    case Nil{} 0n:
      hh
    case Nil{} 1n+(+qq):
      le_add_r(kk, 1n+qq, gg, le_rw_l(Nat.add(1n+qq, kk), Nat.add(kk, 1n+qq), gg, add_comm(1n+qq, kk), hh))
    case _hd <> _tl 0n:
      hh
    case _hd <> tl 1n+qq:
      drop_le(tl, qq, kk, gg, hh)

# the length of an append is the sum of the lengths
law len_append:
  for aa: List<&2, U32>
  for -bb: List<&2, U32>
  {List.length(&2, U32, List.append(&2, U32, aa, bb)) ==
    Nat.add(List.length(&2, U32, aa), List.length(&2, U32, bb)) : Nat}

# the proof of len_append
def len_append(aa, bb):
  match aa:
    case Nil{}:
      {==}
    case _hd <> tl:
      Equal.cong(Nat, Nat, xx => 1n+xx, List.length(&2, U32, List.append(&2, U32, tl, bb)),
        Nat.add(List.length(&2, U32, tl), List.length(&2, U32, bb)), len_append(tl, bb))

# taking n <= length elements takes n
law len_take:
  for xs: List<&2, U32>
  for nn: Nat
  for hh: {Nat.is_le(nn, List.length(&2, U32, xs)) == True{} : Bool}
  {List.length(&2, U32, List.take(&2, U32, xs, nn)) == nn : Nat}

# the proof of len_take
def len_take(xs, nn, hh):
  match xs nn:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+_qq:
      Empty.absurd({0n == 1n+_qq : Nat}, U32L.false_true(hh))
    case _hd <> _tl 0n:
      {==}
    case _hd <> tl 1n+qq:
      Equal.cong(Nat, Nat, xx => 1n+xx, List.length(&2, U32, List.take(&2, U32, tl, qq)), qq, len_take(tl, qq, hh))

# below n, the first n elements followed by anything read as the list
law get_append_take:
  for xs: List<&2, U32>
  for nn: Nat
  for kk: Nat
  for -rest: List<&2, U32>
  for hk: {Nat.is_lt(kk, nn) == True{} : Bool}
  for hl: {Nat.is_le(nn, List.length(&2, U32, xs)) == True{} : Bool}
  {List.get(&2, U32, List.append(&2, U32, List.take(&2, U32, xs, nn), rest), kk) == List.get(&2, U32, xs, kk) :
    Maybe<&2, U32>}

# the proof of get_append_take
def get_append_take(xs, nn, kk, rest, hk, hl):
  match xs nn kk:
    case _xs 0n _kk:
      Empty.absurd({List.get(&2, U32, List.append(&2, U32, List.take(&2, U32, _xs, 0n), rest), _kk) ==
        List.get(&2, U32, _xs, _kk) : Maybe<&2, U32>}, U32L.false_true(
        Equal.trans(Bool, False{}, Nat.is_lt(_kk, 0n), True{}, lt_zero_false(_kk), hk)))
    case Nil{} 1n+_qq _kk:
      Empty.absurd({List.get(&2, U32, List.append(&2, U32, List.take(&2, U32, Nil{}, 1n+_qq), rest), _kk) ==
        List.get(&2, U32, Nil{}, _kk) : Maybe<&2, U32>}, U32L.false_true(hl))
    case _hd <> _tl 1n+_qq 0n:
      {==}
    case _hd <> tl 1n+qq 1n+pk:
      get_append_take(tl, qq, pk, rest, hk, hl)

# past the first n elements (n <= length), the rest reads on
law get_append_skip:
  for xs: List<&2, U32>
  for nn: Nat
  for -kk: Nat
  for -rest: List<&2, U32>
  for hl: {Nat.is_le(nn, List.length(&2, U32, xs)) == True{} : Bool}
  {List.get(&2, U32, List.append(&2, U32, List.take(&2, U32, xs, nn), rest), Nat.add(nn, kk)) ==
    List.get(&2, U32, rest, kk) : Maybe<&2, U32>}

# the proof of get_append_skip
def get_append_skip(xs, nn, kk, rest, hl):
  match xs nn:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+_qq:
      Empty.absurd({List.get(&2, U32, List.append(&2, U32, List.take(&2, U32, Nil{}, 1n+_qq), rest),
        Nat.add(1n+_qq, kk)) == List.get(&2, U32, rest, kk) : Maybe<&2, U32>}, U32L.false_true(hl))
    case _hd <> _tl 0n:
      {==}
    case _hd <> tl 1n+qq:
      get_append_skip(tl, qq, kk, rest, hl)

# ---- small facts crop uses ----

# a < b false gives b <= a
law not_lt_le:
  for aa: Nat
  for bb: Nat
  for hh: {Nat.is_lt(aa, bb) == False{} : Bool}
  {Nat.is_le(bb, aa) == True{} : Bool}

# the proof of not_lt_le
def not_lt_le(aa, bb, hh):
  match aa bb:
    case _aa 0n:
      le_zero(_aa)
    case 0n 1n+_pb:
      Empty.absurd({Nat.is_le(1n+_pb, 0n) == True{} : Bool}, U32L.false_true(Equal.sym(Bool, True{}, False{}, hh)))
    case 1n+pa 1n+pb:
      not_lt_le(pa, pb, hh)

# min(a, 0) is 0
law min_zero_r:
  for aa: Nat
  {Nat.min(aa, 0n) == 0n : Nat}

# the proof of min_zero_r
def min_zero_r(aa):
  match aa:
    case 0n:
      {==}
    case 1n+_pp:
      {==}

# and with false on the right is false
law and_false_r:
  for bb: Bool
  {Bool.and(bb, False{}) == False{} : Bool}

# the proof of and_false_r
def and_false_r(bb):
  match bb:
    case False{}:
      {==}
    case True{}:
      {==}

# (a + b) + c regrouped as (a + c) + b
law add_right_swap:
  for +aa: Nat
  for +bb: Nat
  for +cc: Nat
  {Nat.add(Nat.add(aa, bb), cc) == Nat.add(Nat.add(aa, cc), bb) : Nat}

# the proof of add_right_swap
def add_right_swap(aa, bb, cc):
  Equal.trans(Nat, Nat.add(Nat.add(aa, bb), cc), Nat.add(aa, Nat.add(bb, cc)), Nat.add(Nat.add(aa, cc), bb),
    add_assoc(aa, bb, cc),
    Equal.trans(Nat, Nat.add(aa, Nat.add(bb, cc)), Nat.add(aa, Nat.add(cc, bb)), Nat.add(Nat.add(aa, cc), bb),
      Equal.cong(Nat, Nat, xx => Nat.add(aa, xx), Nat.add(bb, cc), Nat.add(cc, bb), add_comm(bb, cc)),
      Equal.sym(Nat, Nat.add(Nat.add(aa, cc), bb), Nat.add(aa, Nat.add(cc, bb)), add_assoc(aa, cc, bb))))

# at most z, the right summand alone is at most z
law le_add_l:
  for +xx: Nat
  for +yy: Nat
  for +zz: Nat
  for hh: {Nat.is_le(Nat.add(xx, yy), zz) == True{} : Bool}
  {Nat.is_le(yy, zz) == True{} : Bool}

# the proof of le_add_l
def le_add_l(xx, yy, zz, hh):
  le_add_r(yy, xx, zz, le_rw_l(Nat.add(xx, yy), Nat.add(yy, xx), zz, add_comm(xx, yy), hh))

# ---- more on append, take and drop ----

# below the first list's length, an append reads as the first list
law get_append_lt:
  for aa: List<&2, U32>
  for kk: Nat
  for -rest: List<&2, U32>
  for hk: {Nat.is_lt(kk, List.length(&2, U32, aa)) == True{} : Bool}
  {List.get(&2, U32, List.append(&2, U32, aa, rest), kk) == List.get(&2, U32, aa, kk) : Maybe<&2, U32>}

# the proof of get_append_lt
def get_append_lt(aa, kk, rest, hk):
  match aa kk:
    case Nil{} _kk:
      Empty.absurd({List.get(&2, U32, rest, _kk) == None{} : Maybe<&2, U32>}, U32L.false_true(
        Equal.trans(Bool, False{}, Nat.is_lt(_kk, 0n), True{}, lt_zero_false(_kk), hk)))
    case _hd <> _tl 0n:
      {==}
    case _hd <> tl 1n+qq:
      get_append_lt(tl, qq, rest, hk)

# past the first list's length, an append reads as the second list
law get_append_len:
  for aa: List<&2, U32>
  for -kk: Nat
  for -rest: List<&2, U32>
  {List.get(&2, U32, List.append(&2, U32, aa, rest), Nat.add(List.length(&2, U32, aa), kk)) ==
    List.get(&2, U32, rest, kk) : Maybe<&2, U32>}

# the proof of get_append_len
def get_append_len(aa, kk, rest):
  match aa:
    case Nil{}:
      {==}
    case _hd <> tl:
      get_append_len(tl, kk, rest)

# below n, the first n elements read as the list
law get_take:
  for xs: List<&2, U32>
  for nn: Nat
  for kk: Nat
  for hk: {Nat.is_lt(kk, nn) == True{} : Bool}
  {List.get(&2, U32, List.take(&2, U32, xs, nn), kk) == List.get(&2, U32, xs, kk) : Maybe<&2, U32>}

# the proof of get_take
def get_take(xs, nn, kk, hk):
  match xs nn kk:
    case Nil{} _nn _kk:
      {==}
    case _hd <> _tl 0n _kk:
      Empty.absurd({None{} == List.get(&2, U32, _hd <> _tl, _kk) : Maybe<&2, U32>}, U32L.false_true(
        Equal.trans(Bool, False{}, Nat.is_lt(_kk, 0n), True{}, lt_zero_false(_kk), hk)))
    case _hd <> _tl 1n+_qq 0n:
      {==}
    case _hd <> tl 1n+qq 1n+pk:
      get_take(tl, qq, pk, hk)

# dropping from the empty list leaves it empty
law drop_nil:
  for nn: Nat
  {List.drop(&2, U32, Nil{}, nn) == Nil{} : List<&2, U32>}

# the proof of drop_nil
def drop_nil(_nn):
  {==}

# dropping a then b drops a + b
law drop_drop:
  for xs: List<&2, U32>
  for aa: Nat
  for bb: Nat
  {List.drop(&2, U32, List.drop(&2, U32, xs, aa), bb) == List.drop(&2, U32, xs, Nat.add(aa, bb)) : List<&2, U32>}

# the proof of drop_drop
def drop_drop(xs, aa, bb):
  match xs aa:
    case Nil{} _aa:
      drop_nil(bb)
    case _hd <> _tl 0n:
      {==}
    case _hd <> tl 1n+qq:
      drop_drop(tl, qq, bb)

# dropping nothing is the list
law drop_zero:
  for xs: List<&2, U32>
  {List.drop(&2, U32, xs, 0n) == xs : List<&2, U32>}

# the proof of drop_zero
def drop_zero(xs):
  match xs:
    case Nil{}:
      {==}
    case _hd <> _tl:
      {==}

# a + b - a is b
law sub_add_cancel:
  for aa: Nat
  for +bb: Nat
  {Nat.sub(Nat.add(aa, bb), aa) == bb : Nat}

# the proof of sub_add_cancel
def sub_add_cancel(aa, bb):
  match aa:
    case 0n:
      sub_zero(bb)
    case 1n+pp:
      sub_add_cancel(pp, bb)

# m + k <= length gives k <= length after dropping m
law drop_le0:
  for +xs: List<&2, U32>
  for +mm: Nat
  for +kk: Nat
  for hh: {Nat.is_le(Nat.add(mm, kk), List.length(&2, U32, xs)) == True{} : Bool}
  {Nat.is_le(kk, List.length(&2, U32, List.drop(&2, U32, xs, mm))) == True{} : Bool}

# the proof of drop_le0
def drop_le0(xs, mm, kk, hh):
  +ln = List.length(&2, U32, List.drop(&2, U32, xs, mm))
  le_rw_r(kk, Nat.add(ln, 0n), ln, add_zero(ln), drop_le(xs, mm, kk, 0n,
    le_rw_r(Nat.add(mm, kk), List.length(&2, U32, xs), Nat.add(List.length(&2, U32, xs), 0n),
      Equal.sym(Nat, Nat.add(List.length(&2, U32, xs), 0n), List.length(&2, U32, xs),
        add_zero(List.length(&2, U32, xs))), hh)))

# ---- more order facts ----

# min(a, b) <= a
law min_le_l:
  for aa: Nat
  for bb: Nat
  {Nat.is_le(Nat.min(aa, bb), aa) == True{} : Bool}

# the proof of min_le_l
def min_le_l(aa, bb):
  match aa bb:
    case 0n _bb:
      {==}
    case 1n+pa 0n:
      le_zero(1n+pa)
    case 1n+pa 1n+pb:
      min_le_l(pa, pb)

# below both, below their min
law lt_min:
  for xx: Nat
  for aa: Nat
  for bb: Nat
  for ha: {Nat.is_lt(xx, aa) == True{} : Bool}
  for hb: {Nat.is_lt(xx, bb) == True{} : Bool}
  {Nat.is_lt(xx, Nat.min(aa, bb)) == True{} : Bool}

# the proof of lt_min
def lt_min(xx, aa, bb, ha, hb):
  match xx aa bb:
    case _xx 0n _bb:
      Empty.absurd({Nat.is_lt(_xx, Nat.min(0n, _bb)) == True{} : Bool}, U32L.false_true(
        Equal.trans(Bool, False{}, Nat.is_lt(_xx, 0n), True{}, lt_zero_false(_xx), ha)))
    case _xx 1n+_pa 0n:
      Empty.absurd({Nat.is_lt(_xx, 0n) == True{} : Bool}, U32L.false_true(
        Equal.trans(Bool, False{}, Nat.is_lt(_xx, 0n), True{}, lt_zero_false(_xx), hb)))
    case 0n 1n+_pa 1n+_pb:
      {==}
    case 1n+px 1n+pa 1n+pb:
      lt_min(px, pa, pb, ha, hb)

# min(a, b) < b gives min(a, b) = a
law min_lt_r:
  for aa: Nat
  for bb: Nat
  for hh: {Nat.is_lt(Nat.min(aa, bb), bb) == True{} : Bool}
  {Nat.min(aa, bb) == aa : Nat}

# the proof of min_lt_r
def min_lt_r(aa, bb, hh):
  match aa bb:
    case 0n _bb:
      {==}
    case 1n+_pa 0n:
      Empty.absurd({0n == 1n+_pa : Nat}, U32L.false_true(hh))
    case 1n+pa 1n+pb:
      Equal.cong(Nat, Nat, xx => 1n+xx, Nat.min(pa, pb), pa, min_lt_r(pa, pb, hh))

# cancel the same number added on the left of both sides of <
law lt_cancel:
  for mm: Nat
  for -xx: Nat
  for -yy: Nat
  for hh: {Nat.is_lt(Nat.add(mm, xx), Nat.add(mm, yy)) == True{} : Bool}
  {Nat.is_lt(xx, yy) == True{} : Bool}

# the proof of lt_cancel
def lt_cancel(mm, xx, yy, hh):
  match mm:
    case 0n:
      hh
    case 1n+pp:
      lt_cancel(pp, xx, yy, hh)

# something below b makes b positive
law lt_pos:
  for aa: Nat
  for bb: Nat
  for hh: {Nat.is_lt(aa, bb) == True{} : Bool}
  {Nat.is_lt(0n, bb) == True{} : Bool}

# the proof of lt_pos
def lt_pos(aa, bb, hh):
  match bb:
    case 0n:
      Empty.absurd({False{} == True{} : Bool}, U32L.false_true(
        Equal.trans(Bool, False{}, Nat.is_lt(aa, 0n), True{}, lt_zero_false(aa), hh)))
    case 1n+_pb:
      {==}

# what dropping m <= length leaves, and m, make up the length
law len_drop_add:
  for xs: List<&2, U32>
  for mm: Nat
  for hh: {Nat.is_le(mm, List.length(&2, U32, xs)) == True{} : Bool}
  {Nat.add(mm, List.length(&2, U32, List.drop(&2, U32, xs, mm))) == List.length(&2, U32, xs) : Nat}

# the proof of len_drop_add
def len_drop_add(xs, mm, hh):
  match xs mm:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+_qq:
      Empty.absurd({Nat.add(1n+_qq, 0n) == 0n : Nat}, U32L.false_true(hh))
    case _hd <> _tl 0n:
      {==}
    case _hd <> tl 1n+qq:
      Equal.cong(Nat, Nat, xx => 1n+xx, Nat.add(qq, List.length(&2, U32, List.drop(&2, U32, tl, qq))),
        List.length(&2, U32, tl), len_drop_add(tl, qq, hh))

# i - x below c, when x <= i < x + c
law sub_lt:
  for +xx: Nat
  for +ii: Nat
  for +cc: Nat
  for h_le: {Nat.is_le(xx, ii) == True{} : Bool}
  for h_lt: {Nat.is_lt(ii, Nat.add(xx, cc)) == True{} : Bool}
  {Nat.is_lt(Nat.sub(ii, xx), cc) == True{} : Bool}

# the proof of sub_lt
def sub_lt(xx, ii, cc, h_le, h_lt):
  lt_cancel(xx, Nat.sub(ii, xx), cc, lt_rw_l(ii, Nat.add(xx, Nat.sub(ii, xx)), Nat.add(xx, cc),
    Equal.sym(Nat, Nat.add(xx, Nat.sub(ii, xx)), ii, add_sub(xx, ii, h_le)), h_lt))
