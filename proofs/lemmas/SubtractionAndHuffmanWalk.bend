# Word subtraction and order read as Nat, and the Huffman walk over bits
import Base
import ../../src/jpeg.bend as Jpeg
import ./BasicFacts.bend as M1
import ./WordAddition.bend as M2

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
      M1.le_zero(Nat.add(_yy, zz))
    case 1n+_pp 0n:
      Empty.absurd({Nat.is_le(1n+_pp, zz) == True{} : Bool}, M1.false_true(hh))
    case 1n+pp 1n+qq:
      le_add_more(pp, qq, zz, hh)

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
        Nat.cmp(Word.to_nat(32n, xw), Word.to_nat(32n, yw)), M1.ras.word_cmp_nat(32n, xw, yw))

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
      Empty.absurd({False{} == True{} : Bool}, M1.false_true(hh))
    case True{} LT{}:
      {==}
    case True{} EQ{}:
      {==}
    case True{} GT{}:
      Empty.absurd({False{} == True{} : Bool}, M1.false_true(hh))

# 2x <= s + 2y gives x <= y
law le_half:
  for +ss: Bool
  for +xx: Nat
  for +yy: Nat
  for hh: {Nat.is_le(Nat.double(xx), Nat.add(M1.bit(ss), Nat.double(yy))) == True{} : Bool}
  {Nat.is_le(xx, yy) == True{} : Bool}

# the proof of le_half
def le_half(ss, xx, yy, hh):
  fin_le(ss, Nat.cmp(xx, yy), Equal.trans(Bool, Cmp.is_le(Word.cmp.fin(False{}, ss, Nat.cmp(xx, yy))),
    Nat.is_le(Nat.double(xx), Nat.add(M1.bit(ss), Nat.double(yy))), True{},
    Equal.cong(Cmp, Bool, tt => Cmp.is_le(tt), Word.cmp.fin(False{}, ss, Nat.cmp(xx, yy)),
      Nat.cmp(Nat.double(xx), Nat.add(M1.bit(ss), Nat.double(yy))),
      Equal.sym(Cmp, Nat.cmp(Nat.double(xx), Nat.add(M1.bit(ss), Nat.double(yy))),
        Word.cmp.fin(False{}, ss, Nat.cmp(xx, yy)), M1.cmp_dbl(xx, yy, False{}, ss))), hh))

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
    Equal.sym(Nat, Nat.add(Nat.add(c0, b0), db), Nat.add(c0, Nat.add(b0, db)), M1.ras.add_assoc(c0, b0, db)), {==}) :
    {Nat.add(c0, Nat.add(b0, db)) == Nat.add(Nat.add(c0, b0), db) : Nat}}
  +e2 = {M2.add4(s0, dr, Nat.add(c0, b0), db) :
    {Nat.add(Nat.add(s0, dr), Nat.add(Nat.add(c0, b0), db)) == Nat.add(Nat.add(s0, Nat.add(c0, b0)), Nat.add(dr, db)) :
      Nat}}
  +e3 = {Equal.cong(Nat, Nat, xx => Nat.add(xx, Nat.add(dr, db)), Nat.add(s0, Nat.add(c0, b0)),
    Nat.add(a0, Nat.double(k0)), ee) :
    {Nat.add(Nat.add(s0, Nat.add(c0, b0)), Nat.add(dr, db)) == Nat.add(Nat.add(a0, Nat.double(k0)), Nat.add(dr, db)) :
      Nat}}
  +e4 = {M1.ras.add_assoc(a0, Nat.double(k0), Nat.add(dr, db)) :
    {Nat.add(Nat.add(a0, Nat.double(k0)), Nat.add(dr, db)) == Nat.add(a0, Nat.add(Nat.double(k0), Nat.add(dr, db))) :
      Nat}}
  +e5 = {Equal.trans(Nat, Nat.add(Nat.double(k0), Nat.add(dr, db)), Nat.add(dr, Nat.add(Nat.double(k0), db)),
    Nat.double(na), M1.add_swap(Nat.double(k0), dr, db),
    Equal.trans(Nat, Nat.add(dr, Nat.add(Nat.double(k0), db)), Nat.add(dr, Nat.double(Nat.add(k0, nb))),
      Nat.double(na),
      Equal.cong(Nat, Nat, xx => Nat.add(dr, xx), Nat.add(Nat.double(k0), db), Nat.double(Nat.add(k0, nb)),
        Equal.sym(Nat, Nat.double(Nat.add(k0, nb)), Nat.add(Nat.double(k0), db), M1.double_dist(k0, nb))),
      Equal.trans(Nat, Nat.add(dr, Nat.double(Nat.add(k0, nb))), Nat.double(Nat.add(rn, Nat.add(k0, nb))),
        Nat.double(na), Equal.sym(Nat, Nat.double(Nat.add(rn, Nat.add(k0, nb))),
          Nat.add(dr, Nat.double(Nat.add(k0, nb))), M1.double_dist(rn, Nat.add(k0, nb))),
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
  for ee: {Nat.add(M1.bit(ss), Nat.add(c0, b0)) == Nat.add(a0, Nat.double(k0)) : Nat}
  for hh: {Nat.is_le(Nat.add(c0, Nat.add(b0, Nat.double(nb))), Nat.add(a0, Nat.double(na))) == True{} : Bool}
  {Nat.is_le(Nat.add(k0, nb), na) == True{} : Bool}

# the proof of diff_half
def diff_half(ss, c0, b0, a0, k0, nb, na, ee, hh):
  +s0 = M1.bit(ss)
  +db = Nat.double(nb)
  +dn = Nat.double(na)
  +h1 = {M1.le_add_mono(s0, Nat.add(c0, Nat.add(b0, db)), Nat.add(a0, dn), hh) :
    {Nat.is_le(Nat.add(s0, Nat.add(c0, Nat.add(b0, db))), Nat.add(s0, Nat.add(a0, dn))) == True{} : Bool}}
  +el = {Equal.trans(Nat, Nat.add(s0, Nat.add(c0, Nat.add(b0, db))), Nat.add(s0, Nat.add(Nat.add(c0, b0), db)),
    Nat.add(a0, Nat.add(Nat.double(k0), db)),
    Equal.cong(Nat, Nat, xx => Nat.add(s0, xx), Nat.add(c0, Nat.add(b0, db)), Nat.add(Nat.add(c0, b0), db),
      Equal.sym(Nat, Nat.add(Nat.add(c0, b0), db), Nat.add(c0, Nat.add(b0, db)), M1.ras.add_assoc(c0, b0, db))),
    Equal.trans(Nat, Nat.add(s0, Nat.add(Nat.add(c0, b0), db)), Nat.add(Nat.add(s0, Nat.add(c0, b0)), db),
      Nat.add(a0, Nat.add(Nat.double(k0), db)),
      Equal.sym(Nat, Nat.add(Nat.add(s0, Nat.add(c0, b0)), db), Nat.add(s0, Nat.add(Nat.add(c0, b0), db)),
        M1.ras.add_assoc(s0, Nat.add(c0, b0), db)),
      Equal.trans(Nat, Nat.add(Nat.add(s0, Nat.add(c0, b0)), db), Nat.add(Nat.add(a0, Nat.double(k0)), db),
        Nat.add(a0, Nat.add(Nat.double(k0), db)),
        Equal.cong(Nat, Nat, xx => Nat.add(xx, db), Nat.add(s0, Nat.add(c0, b0)), Nat.add(a0, Nat.double(k0)), ee),
        M1.ras.add_assoc(a0, Nat.double(k0), db)))) :
    {Nat.add(s0, Nat.add(c0, Nat.add(b0, db))) == Nat.add(a0, Nat.add(Nat.double(k0), db)) : Nat}}
  +h2 = {M1.le_rw_l(Nat.add(s0, Nat.add(c0, Nat.add(b0, db))), Nat.add(a0, Nat.add(Nat.double(k0), db)),
    Nat.add(s0, Nat.add(a0, dn)), el, h1) :
    {Nat.is_le(Nat.add(a0, Nat.add(Nat.double(k0), db)), Nat.add(s0, Nat.add(a0, dn))) == True{} : Bool}}
  +h3 = {M1.le_rw_r(Nat.add(a0, Nat.add(Nat.double(k0), db)), Nat.add(s0, Nat.add(a0, dn)), Nat.add(a0, Nat.add(s0,
      dn)),
    M1.add_swap(s0, a0, dn), h2) :
    {Nat.is_le(Nat.add(a0, Nat.add(Nat.double(k0), db)), Nat.add(a0, Nat.add(s0, dn))) == True{} : Bool}}
  +h4 = {le_cancel(a0, Nat.add(Nat.double(k0), db), Nat.add(s0, dn), h3) :
    {Nat.is_le(Nat.add(Nat.double(k0), db), Nat.add(s0, dn)) == True{} : Bool}}
  le_half(ss, Nat.add(k0, nb), na, M1.le_rw_l(Nat.add(Nat.double(k0), db), Nat.double(Nat.add(k0, nb)), Nat.add(s0, dn),
    Equal.sym(Nat, Nat.double(Nat.add(k0, nb)), Nat.add(Nat.double(k0), db), M1.double_dist(k0, nb)), h4))

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
  for +e_bits: {Nat.add(M1.bit(ss), Nat.add(M1.bit(Bool.not(cc)), M1.bit(bb))) == Nat.add(M1.bit(ab),
    Nat.double(M1.bit(Bool.not(kk)))) :
    Nat}
  for hh: {Nat.is_le(Nat.add(M1.bit(Bool.not(cc)), Word.to_nat(1n+pp, WCon{bb, bt})), Word.to_nat(1n+pp, WCon{ab,
      at})) ==
    True{} : Bool}
  for ih: {Nat.is_le(Nat.add(M1.bit(Bool.not(kk)), Word.to_nat(pp, bt)), Word.to_nat(pp, at)) == True{} : Bool} ->
    {Nat.add(Word.to_nat(pp, Word.adc(pp, at, bt, True{}, kk)), Nat.add(M1.bit(Bool.not(kk)), Word.to_nat(pp, bt))) ==
      Word.to_nat(pp, at) : Nat}
  {Nat.add(Word.to_nat(1n+pp, WCon{ss, Word.adc(pp, at, bt, True{}, kk)}),
    Nat.add(M1.bit(Bool.not(cc)), Word.to_nat(1n+pp, WCon{bb, bt}))) == Word.to_nat(1n+pp, WCon{ab, at}) : Nat}

# the proof of sbc.arm
def sbc.arm(pp, at, bt, ab, bb, cc, ss, kk, e_bits, hh, ih):
  +na = Word.to_nat(pp, at)
  +nb = Word.to_nat(pp, bt)
  +c0 = M1.bit(Bool.not(cc))
  +k0 = M1.bit(Bool.not(kk))
  +xa = Nat.add(M1.bit(ab), Nat.double(na))
  +xb = Nat.add(M1.bit(bb), Nat.double(nb))
  +wa = Word.to_nat(1n+pp, WCon{ab, at})
  +wb = Word.to_nat(1n+pp, WCon{bb, bt})
  +rw = Word.adc(pp, at, bt, True{}, kk)
  +rn = Word.to_nat(pp, rw)
  +ea = {M1.to_nat_con(pp, ab, at) : {wa == xa : Nat}}
  +eb = {M1.to_nat_con(pp, bb, bt) : {wb == xb : Nat}}
  +h1 = {M1.le_rw_r(Nat.add(c0, xb), wa, xa, ea, M1.le_rw_l(Nat.add(c0, wb), Nat.add(c0, xb), wa,
    Equal.cong(Nat, Nat, xx => Nat.add(c0, xx), wb, xb, eb), hh)) :
    {Nat.is_le(Nat.add(c0, xb), xa) == True{} : Bool}}
  +er = {ih(diff_half(ss, c0, M1.bit(bb), M1.bit(ab), k0, nb, na, e_bits, h1)) :
    {Nat.add(rn, Nat.add(k0, nb)) == na : Nat}}
  +eg = {diff_regroup(M1.bit(ss), c0, M1.bit(bb), M1.bit(ab), k0, rn, nb, na, e_bits, er) :
    {Nat.add(Nat.add(M1.bit(ss), Nat.double(rn)), Nat.add(c0, xb)) == xa : Nat}}
  Equal.trans(Nat, Nat.add(Word.to_nat(1n+pp, WCon{ss, rw}), Nat.add(c0, wb)),
    Nat.add(Nat.add(M1.bit(ss), Nat.double(rn)), Nat.add(c0, wb)), wa,
    Equal.cong(Nat, Nat, xx => Nat.add(xx, Nat.add(c0, wb)), Word.to_nat(1n+pp, WCon{ss, rw}),
      Nat.add(M1.bit(ss), Nat.double(rn)), M1.to_nat_con(pp, ss, rw)),
    Equal.trans(Nat, Nat.add(Nat.add(M1.bit(ss), Nat.double(rn)), Nat.add(c0, wb)),
      Nat.add(Nat.add(M1.bit(ss), Nat.double(rn)), Nat.add(c0, xb)), wa,
      Equal.cong(Nat, Nat, xx => Nat.add(Nat.add(M1.bit(ss), Nat.double(rn)), Nat.add(c0, xx)), wb, xb, eb),
      Equal.trans(Nat, Nat.add(Nat.add(M1.bit(ss), Nat.double(rn)), Nat.add(c0, xb)), xa, wa, eg,
        Equal.sym(Nat, wa, xa, ea))))

# the subtractor with carry in c: when b + (1 - c) <= a, the difference r
# gives r + (1 - c) + b = a
law sbc_nat:
  for nn: Nat
  for aw: Word(nn)
  for bw: Word(nn)
  for cc: Bool
  for hh: {Nat.is_le(Nat.add(M1.bit(Bool.not(cc)), Word.to_nat(nn, bw)), Word.to_nat(nn, aw)) == True{} : Bool}
  {Nat.add(Word.to_nat(nn, Word.adc(nn, aw, bw, True{}, cc)), Nat.add(M1.bit(Bool.not(cc)), Word.to_nat(nn, bw))) ==
    Word.to_nat(nn, aw) : Nat}

# the proof of sbc_nat
def sbc_nat(nn, aw, bw, cc, hh):
  match nn:
    case 0n:
      match aw bw cc:
        case WNil{} WNil{} True{}:
          {==}
        case WNil{} WNil{} False{}:
          Empty.absurd({1n == 0n : Nat}, M1.false_true(hh))
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
          Equal.cong(Nat, Nat, xx => Nat.sub(xx, 0n), Nat.add(rn, 0n), rn, M1.ras.add_zero(rn)), sub_zero(rn)))
    case 1n+(+pb):
      Equal.trans(Nat, Nat.sub(an, 1n+pb), Nat.sub(1n+Nat.add(rn, pb), 1n+pb), rn,
        Equal.cong(Nat, Nat, xx => Nat.sub(xx, 1n+pb), an, 1n+Nat.add(rn, pb),
          Equal.trans(Nat, an, Nat.add(rn, 1n+pb), 1n+Nat.add(rn, pb), Equal.sym(Nat, Nat.add(rn, 1n+pb), an, ee),
            M1.ras.add_succ(rn, pb))),
        sub_of_add(rn, pb, Nat.add(rn, pb), {==}))

# U32 sub, when b <= a, is Nat sub
law ras.u32_sub_nat:
  for +au: U32
  for +bu: U32
  for hh: {Nat.is_le(U32.to_nat(bu), U32.to_nat(au)) == True{} : Bool}
  {U32.to_nat(U32.sub(au, bu)) == Nat.sub(U32.to_nat(au), U32.to_nat(bu)) : Nat}

# the proof of ras.u32_sub_nat
def ras.u32_sub_nat(au, bu, hh):
  match au bu:
    case U32{+xw} U32{+yw}:
      Equal.sym(Nat, Nat.sub(Word.to_nat(32n, xw), Word.to_nat(32n, yw)), Word.to_nat(32n, Word.sub(32n, xw, yw)),
        sub_of_add(Word.to_nat(32n, Word.sub(32n, xw, yw)), Word.to_nat(32n, yw), Word.to_nat(32n, xw),
          sbc_nat(32n, xw, yw, True{}, hh)))

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
      Empty.absurd({Nat.add(1n+_pb, Nat.sub(0n, 1n+_pb)) == 0n : Nat}, M1.false_true(hh))
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
      Empty.absurd({Nat.sub(1n+_pa, 0n) == 0n : Nat}, M1.false_true(hh))
    case 1n+pa 1n+pb:
      sub_zero_le(pa, pb, hh)

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

# at most z, the right summand alone is at most z
law le_add_l:
  for +xx: Nat
  for +yy: Nat
  for +zz: Nat
  for hh: {Nat.is_le(Nat.add(xx, yy), zz) == True{} : Bool}
  {Nat.is_le(yy, zz) == True{} : Bool}

# the proof of le_add_l
def le_add_l(xx, yy, zz, hh):
  M2.le_add_r(yy, xx, zz, M1.le_rw_l(Nat.add(xx, yy), Nat.add(yy, xx), zz, M1.ras.add_comm(xx, yy), hh))

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
  lt_cancel(xx, Nat.sub(ii, xx), cc, M1.lt_rw_l(ii, Nat.add(xx, Nat.sub(ii, xx)), Nat.add(xx, cc),
    Equal.sym(Nat, Nat.add(xx, Nat.sub(ii, xx)), ii, add_sub(xx, ii, h_le)), h_lt))

# a U32 above some successor's predecessor is not zero, once is_zero's answer is named
def pos.at(
  zz: Bool,
  +uu: U32,
  +kk: Nat,
  +ez: {U32.is_zero(uu) == zz : Bool},
  +hh: {Nat.is_le(1n+kk, U32.to_nat(uu)) == True{} : Bool}
) -> {U32.is_zero(uu) == False{} : Bool}:
  match zz:
    case False{}:
      ez
    case True{}:
      +e0 = {M1.zero.val(uu, Equal.sym(Bool, U32.is_zero(uu), True{}, ez)) : {U32.to_nat(uu) == 0n : Nat}}
      Empty.absurd({U32.is_zero(uu) == False{} : Bool}, M1.false_true(Equal.trans(Bool, False{},
        Nat.is_le(1n+kk, U32.to_nat(uu)), True{}, Equal.sym(Bool, Nat.is_le(1n+kk, U32.to_nat(uu)), False{},
        Equal.cong(Nat, Bool, xx => Nat.is_le(1n+kk, xx), U32.to_nat(uu), 0n, e0)), hh)))

# a U32 at least a successor is not zero
def pos(
  +uu: U32,
  +kk: Nat,
  hh: {Nat.is_le(1n+kk, U32.to_nat(uu)) == True{} : Bool}
) -> {U32.is_zero(uu) == False{} : Bool}:
  pos.at(U32.is_zero(uu), uu, kk, {==}, hh)

# ---- E. adding without a carry out, and the block count ----

# the adder's carry out of the top bit
def cy(nn: Nat, aw: Word(nn), bw: Word(nn), cc: Bool) -> Bool:
  match nn:
    case 0n:
      cc
    case 1n+pp:
      match aw bw cc:
        case WCon{False{}, at} WCon{False{}, bt} False{}:
          cy(pp, at, bt, False{})
        case WCon{False{}, at} WCon{False{}, bt} True{}:
          cy(pp, at, bt, False{})
        case WCon{False{}, at} WCon{True{}, bt} False{}:
          cy(pp, at, bt, False{})
        case WCon{False{}, at} WCon{True{}, bt} True{}:
          cy(pp, at, bt, True{})
        case WCon{True{}, at} WCon{False{}, bt} False{}:
          cy(pp, at, bt, False{})
        case WCon{True{}, at} WCon{False{}, bt} True{}:
          cy(pp, at, bt, True{})
        case WCon{True{}, at} WCon{True{}, bt} False{}:
          cy(pp, at, bt, True{})
        case WCon{True{}, at} WCon{True{}, bt} True{}:
          cy(pp, at, bt, True{})

# the room bs has in its open block: none at a block's start
def rm(zblock: Bool, +need: U32) -> U32:
  match zblock:
    case True{}:
      0
    case False{}:
      need

# a word shifted up one place with bb in the low bit, the top bit dropped
def vstep(xx: U32, bb: Bool) -> U32:
  match xx:
    case U32{ww}:
      match ww:
        case WCon{w0, wt}:
          U32{WCon{bb, Word.shl.put(31n, w0, wt)}}

# nothing is below zero
def lt0(xx: Nat) -> {False{} == Nat.is_lt(xx, 0n) : Bool}:
  match xx:
    case 0n:
      {==}
    case 1n+_pp:
      {==}

# a Huffman walk over bits: the symbol found and the bits it took, or none
type HW is Data:
  HWHit{sym: U32, used: Nat}
  HWMiss{}

# the table's answer for one more code bit, before the walk over the bits after it
def hw.pick(look: Maybe<&2, U32>, rest: HW) -> HW:
  match look:
    case Some{+ss}:
      match rest:
        case _r:
          HWHit{ss, 1n}
    case None{}:
      match rest:
        case HWHit{+ss, +nn}:
          HWHit{ss, 1n+nn}
        case HWMiss{}:
          HWMiss{}

# the decoder's Huffman lookup over a list of bits, code and len so far: each bit extends the code, the
# table asked at each length
def hw(bs: List<&2, Bool>, +tab: Jpeg.Huff, +code: U32, +len: U32) -> HW:
  match bs:
    case Nil{}:
      HWMiss{}
    case +bb <> rest:
      match tab:
        case Jpeg.Huff{+cs, +ls, +ys}:
          hw.pick(Jpeg.decode.look(cs, ls, ys, vstep(code, bb), (len + 1 : U32)), hw(rest, Jpeg.Huff{cs, ls, ys},
            vstep(code, bb), (len + 1 : U32)))

# the index after j ZRLs
def kz(jj: Nat, +kk: U32) -> U32:
  match jj:
    case 0n:
      kk
    case 1n+ +pp:
      kz(pp, (kk + 16 : U32))
