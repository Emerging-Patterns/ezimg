# Word addition and order read as Nat
import Base
import ./BasicFacts.bend as M1

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
      M1.le_zero(_zz)
    case 1n+_pp 0n:
      Empty.absurd({False{} == True{} : Bool}, M1.false_true(hh))
    case 1n+pp 1n+qq:
      le_add_r(pp, yy, qq, hh)

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
      M1.le_zero(Nat.mul(_bb, cc))
    case 1n+_pp 0n:
      Empty.absurd({Nat.is_le(Nat.mul(1n+_pp, cc), 0n) == True{} : Bool}, M1.false_true(hh))
    case 1n+pp 1n+qq:
      M1.le_add_mono(cc, Nat.mul(pp, cc), Nat.mul(qq, cc), le_mul_mono(pp, qq, cc, hh))

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
        Nat.cmp(Word.to_nat(32n, xw), Word.to_nat(32n, yw)), M1.ras.word_cmp_nat(32n, xw, yw))

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
    Nat.add(Nat.add(aa, cc), Nat.add(bb, dd)), M1.ras.add_assoc(aa, bb, Nat.add(cc, dd)),
    Equal.trans(Nat, Nat.add(aa, Nat.add(bb, Nat.add(cc, dd))), Nat.add(aa, Nat.add(cc, Nat.add(bb, dd))),
      Nat.add(Nat.add(aa, cc), Nat.add(bb, dd)),
      Equal.cong(Nat, Nat, xx => Nat.add(aa, xx), Nat.add(bb, Nat.add(cc, dd)), Nat.add(cc, Nat.add(bb, dd)),
        M1.add_swap(bb, cc, dd)),
      Equal.sym(Nat, Nat.add(Nat.add(aa, cc), Nat.add(bb, dd)), Nat.add(aa, Nat.add(cc, Nat.add(bb, dd))),
        M1.ras.add_assoc(aa, cc, Nat.add(bb, dd)))))

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
        Nat.add(c0, Nat.add(Nat.add(a0, b0), Nat.add(da, db))), M1.ras.add_assoc(c0, Nat.add(a0, b0), Nat.add(da, db))),
      Equal.trans(Nat, Nat.add(Nat.add(c0, Nat.add(a0, b0)), Nat.add(da, db)),
        Nat.add(Nat.add(s0, dk), Nat.add(da, db)),
        Nat.add(s0, Nat.double(Nat.add(k0, Nat.add(na, nb)))),
        Equal.cong(Nat, Nat, xx => Nat.add(xx, Nat.add(da, db)), Nat.add(c0, Nat.add(a0, b0)),
          Nat.add(s0, dk), ee),
        Equal.trans(Nat, Nat.add(Nat.add(s0, dk), Nat.add(da, db)), Nat.add(s0, Nat.add(dk, Nat.add(da, db))),
          Nat.add(s0, Nat.double(Nat.add(k0, Nat.add(na, nb)))), M1.ras.add_assoc(s0, dk, Nat.add(da, db)),
          Equal.cong(Nat, Nat, xx => Nat.add(s0, xx), Nat.add(dk, Nat.add(da, db)),
            Nat.double(Nat.add(k0, Nat.add(na, nb))),
            Equal.trans(Nat, Nat.add(dk, Nat.add(da, db)), Nat.add(dk, Nat.double(Nat.add(na, nb))),
              Nat.double(Nat.add(k0, Nat.add(na, nb))),
              Equal.cong(Nat, Nat, xx => Nat.add(dk, xx), Nat.add(da, db), Nat.double(Nat.add(na, nb)),
                Equal.sym(Nat, Nat.double(Nat.add(na, nb)), Nat.add(da, db), M1.double_dist(na, nb))),
              Equal.sym(Nat, Nat.double(Nat.add(k0, Nat.add(na, nb))), Nat.add(dk, Nat.double(Nat.add(na, nb))),
                M1.double_dist(k0, Nat.add(na, nb)))))))))

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
  for e_bits: {Nat.add(M1.bit(cc), Nat.add(M1.bit(ab), M1.bit(bb))) == Nat.add(M1.bit(ss),
      Nat.double(M1.bit(kk))) : Nat}
  for hh: {Nat.is_lt(Nat.add(M1.bit(cc), Nat.add(Word.to_nat(1n+pp, WCon{ab, at}), Word.to_nat(1n+pp, WCon{bb, bt}))),
    Nat.pow(2n, 1n+pp)) == True{} : Bool}
  for ih: {Nat.is_lt(Nat.add(M1.bit(kk), Nat.add(Word.to_nat(pp, at), Word.to_nat(pp, bt))), Nat.pow(2n,
      pp)) == True{} :
    Bool} -> {Word.to_nat(pp, Word.adc(pp, at, bt, False{}, kk)) ==
    Nat.add(M1.bit(kk), Nat.add(Word.to_nat(pp, at), Word.to_nat(pp, bt))) : Nat}
  {Word.to_nat(1n+pp, WCon{ss, Word.adc(pp, at, bt, False{}, kk)}) ==
    Nat.add(M1.bit(cc), Nat.add(Word.to_nat(1n+pp, WCon{ab, at}), Word.to_nat(1n+pp, WCon{bb, bt}))) : Nat}

# the proof of adc.arm
def adc.arm(pp, at, bt, ab, bb, cc, ss, kk, e_bits, hh, ih):
  +na = Word.to_nat(pp, at)
  +nb = Word.to_nat(pp, bt)
  +mm = Nat.add(M1.bit(kk), Nat.add(na, nb))
  +wa = Word.to_nat(1n+pp, WCon{ab, at})
  +wb = Word.to_nat(1n+pp, WCon{bb, bt})
  +xa = Nat.add(M1.bit(ab), Nat.double(na))
  +xb = Nat.add(M1.bit(bb), Nat.double(nb))
  +e_in = {Equal.trans(Nat, Nat.add(M1.bit(cc), Nat.add(wa, wb)), Nat.add(M1.bit(cc), Nat.add(xa, wb)),
    Nat.add(M1.bit(cc), Nat.add(xa, xb)),
    Equal.cong(Nat, Nat, xx => Nat.add(M1.bit(cc), Nat.add(xx, wb)), wa, xa, M1.to_nat_con(pp, ab, at)),
    Equal.cong(Nat, Nat, xx => Nat.add(M1.bit(cc), Nat.add(xa, xx)), wb, xb, M1.to_nat_con(pp, bb, bt))) :
    {Nat.add(M1.bit(cc), Nat.add(wa, wb)) == Nat.add(M1.bit(cc), Nat.add(xa, xb)) : Nat}}
  +e_all = {Equal.trans(Nat, Nat.add(M1.bit(cc), Nat.add(wa, wb)), Nat.add(M1.bit(cc), Nat.add(xa, xb)),
    Nat.add(M1.bit(ss), Nat.double(mm)), e_in, sum_regroup(M1.bit(cc), M1.bit(ab), M1.bit(bb), M1.bit(ss), M1.bit(kk),
        na, nb, e_bits)) :
    {Nat.add(M1.bit(cc), Nat.add(wa, wb)) == Nat.add(M1.bit(ss), Nat.double(mm)) : Nat}}
  +h2 = {M1.lt_rw_r(Nat.add(M1.bit(ss), Nat.double(mm)), Nat.pow(2n, 1n+pp), Nat.double(Nat.pow(2n, pp)),
      M1.pow2_succ(pp),
    M1.lt_rw_l(Nat.add(M1.bit(cc), Nat.add(wa, wb)), Nat.add(M1.bit(ss), Nat.double(mm)), Nat.pow(2n, 1n+pp), e_all,
        hh)) :
    {Nat.is_lt(Nat.add(M1.bit(ss), Nat.double(mm)), Nat.double(Nat.pow(2n, pp))) == True{} : Bool}}
  +er = {ih(M1.lt_half(ss, mm, Nat.pow(2n, pp), h2)) : {Word.to_nat(pp, Word.adc(pp, at, bt, False{}, kk)) == mm : Nat}}
  Equal.trans(Nat, Word.to_nat(1n+pp, WCon{ss, Word.adc(pp, at, bt, False{}, kk)}),
    Nat.add(M1.bit(ss), Nat.double(Word.to_nat(pp, Word.adc(pp, at, bt, False{}, kk)))),
    Nat.add(M1.bit(cc), Nat.add(wa, wb)),
    M1.to_nat_con(pp, ss, Word.adc(pp, at, bt, False{}, kk)),
    Equal.trans(Nat, Nat.add(M1.bit(ss), Nat.double(Word.to_nat(pp, Word.adc(pp, at, bt, False{}, kk)))),
      Nat.add(M1.bit(ss), Nat.double(mm)), Nat.add(M1.bit(cc), Nat.add(wa, wb)),
      Equal.cong(Nat, Nat, xx => Nat.add(M1.bit(ss), Nat.double(xx)), Word.to_nat(pp, Word.adc(pp, at, bt, False{},
          kk)),
        mm, er),
      Equal.sym(Nat, Nat.add(M1.bit(cc), Nat.add(wa, wb)), Nat.add(M1.bit(ss), Nat.double(mm)), e_all)))

# the adder with carry in c, when the sum is below 2^n, is the sum
law adc_nat:
  for nn: Nat
  for aw: Word(nn)
  for bw: Word(nn)
  for cc: Bool
  for hh: {Nat.is_lt(Nat.add(M1.bit(cc), Nat.add(Word.to_nat(nn, aw), Word.to_nat(nn, bw))), Nat.pow(2n, nn)) ==
    True{} : Bool}
  {Word.to_nat(nn, Word.adc(nn, aw, bw, False{}, cc)) ==
    Nat.add(M1.bit(cc), Nat.add(Word.to_nat(nn, aw), Word.to_nat(nn, bw))) : Nat}

# the proof of adc_nat
def adc_nat(nn, aw, bw, cc, hh):
  match nn:
    case 0n:
      match aw bw cc:
        case WNil{} WNil{} False{}:
          {==}
        case WNil{} WNil{} True{}:
          Empty.absurd({0n == 1n : Nat}, M1.false_true(hh))
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
      Empty.absurd({Cmp.is_lt(Word.cmp.fin(cc, False{}, EQ{})) == True{} : Bool}, M1.false_true(hh))
    case GT{}:
      Empty.absurd({False{} == True{} : Bool}, M1.false_true(hh))

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
          +xn = Nat.add(M1.bit(bb), Nat.double(tn))
          +h1 = {Equal.trans(Bool, Nat.is_lt(xn, Nat.double(top)),
            Cmp.is_lt(Word.cmp.fin(bb, False{}, Nat.cmp(tn, top))), True{},
            Equal.cong(Cmp, Bool, cc => Cmp.is_lt(cc), Nat.cmp(xn, Nat.double(top)),
              Word.cmp.fin(bb, False{}, Nat.cmp(tn, top)), M1.cmp_dbl(tn, top, bb, False{})),
            fin_lt_back(bb, Nat.cmp(tn, top), word_lt_pow(pp, tt))) :
            {Nat.is_lt(xn, Nat.double(top)) == True{} : Bool}}
          M1.lt_rw_l(xn, Word.to_nat(1n+pp, WCon{bb, tt}), Nat.pow(2n, 1n+pp),
            Equal.sym(Nat, Word.to_nat(1n+pp, WCon{bb, tt}), xn, M1.to_nat_con(pp, bb, tt)),
            M1.lt_rw_r(xn, Nat.double(top), Nat.pow(2n, 1n+pp), Equal.sym(Nat, Nat.pow(2n, 1n+pp), Nat.double(top),
              M1.pow2_succ(pp)), h1))

# the adder, when the sum is at most some n-bit word's value, is the sum
law adc_below:
  for +nn: Nat
  for +aw: Word(nn)
  for +bw: Word(nn)
  for +cc: Bool
  for +tw: Word(nn)
  for hh: {Nat.is_le(Nat.add(M1.bit(cc), Nat.add(Word.to_nat(nn, aw), Word.to_nat(nn, bw))), Word.to_nat(nn, tw)) ==
    True{} : Bool}
  {Word.to_nat(nn, Word.adc(nn, aw, bw, False{}, cc)) ==
    Nat.add(M1.bit(cc), Nat.add(Word.to_nat(nn, aw), Word.to_nat(nn, bw))) : Nat}

# the proof of adc_below
def adc_below(nn, aw, bw, cc, tw, hh):
  adc_nat(nn, aw, bw, cc, M1.le_lt_trans(Nat.add(M1.bit(cc), Nat.add(Word.to_nat(nn, aw), Word.to_nat(nn, bw))),
    Word.to_nat(nn, tw), Nat.pow(2n, nn), hh, word_lt_pow(nn, tw)))

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
