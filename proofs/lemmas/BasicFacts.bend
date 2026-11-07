# Bool, Nat, Word and list facts most proofs use, with the plane tree and
# Huffman table groups
import Base
import ../../src/crc.bend as Crc
import ../../src/png.bend as Png
import ../../src/jpeg.bend as Jpeg
import ../../src/jpeg_enc.bend as Jenc
import ../../laws/JpegPlacesComponentSamples.bend as L1
import ../../laws/JpegRoundTripKeepsSize.bend as L2
import ../../laws/PngAncillaryChunksIgnored.bend as L3
import ../../laws/defs/PngSpecification.bend as D1

# the type False names: Unit for False, Empty for True
def false_ty(bb: Bool) -> Type:
  match bb:
    case False{}:
      Unit
    case True{}:
      Empty

# False is never True
law false_true:
  for ee: {False{} == True{} : Bool}
  Empty

# the proof of false_true
def false_true(ee):
  %ee : false_ty(_)
  Unit{}

# both sides of a true and: the left
law and_left:
  for aa: Bool
  for -bb: Bool
  for h_and: {Bool.and(aa, bb) == True{} : Bool}
  {aa == True{} : Bool}

# the proof of and_left
def and_left(aa, _bb, h_and):
  match aa:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, false_true(h_and))

# both sides of a true and: the right
law and_right:
  for aa: Bool
  for -bb: Bool
  for h_and: {Bool.and(aa, bb) == True{} : Bool}
  {bb == True{} : Bool}

# the proof of and_right
def and_right(aa, _bb, h_and):
  match aa:
    case True{}:
      h_and
    case False{}:
      Empty.absurd({_bb == True{} : Bool}, false_true(h_and))

# a bit compares equal to itself
law fin_self:
  for bb: Bool
  {Word.cmp.fin(bb, bb, EQ{}) == EQ{} : Cmp}

# the proof of fin_self
def fin_self(bb):
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# words compare equal to themselves
law weq_refl:
  for nn: Nat
  for +ww: Word(nn)
  {Word.cmp(nn, ww, ww) == EQ{} : Cmp}

# the proof of weq_refl
def weq_refl(nn, ww):
  match nn:
    case 0n:
      {==}
    case 1n+pp:
      match ww:
        case WCon{bb, tt}:
          ih = Equal.sym(Cmp, Word.cmp(pp, tt, tt), EQ{}, weq_refl(pp, tt))
          %ih : {Word.cmp.fin(bb, bb, _) == EQ{} : Cmp}
          fin_self(bb)

# a U32 is_eq itself
law u32_eq_refl:
  for +uu: U32
  {U32.is_eq(uu, uu) == True{} : Bool}

# the proof of u32_eq_refl
def u32_eq_refl(uu):
  match uu:
    case U32{ww}:
      rf = Equal.sym(Cmp, Word.cmp(32n, ww, ww), EQ{}, weq_refl(32n, ww))
      %rf : {Cmp.is_eq(_) == True{} : Bool}
      {==}

# words that compare equal, bit by bit past the first: the rest equal, the
# first bits the same
law weq.arm:
  for -pp: Nat
  for -at: Word(pp)
  for -bt: Word(pp)
  for cc: Cmp
  for ec: {Word.cmp(pp, at, bt) == cc : Cmp}
  for ih: {Cmp.is_eq(Word.cmp(pp, at, bt)) == True{} : Bool} -> {at == bt : Word(pp)}
  for ab: Bool
  for bb: Bool
  for ee: {Cmp.is_eq(Word.cmp.fin(ab, bb, cc)) == True{} : Bool}
  {WCon{ab, at} == WCon{bb, bt} : Word.Con<pp>}

# the proof of weq.arm
def weq.arm(pp, at, bt, cc, ec, ih, ab, bb, ee):
  match cc:
    case LT{}:
      Empty.absurd({WCon{ab, at} == WCon{bb, bt} : Word.Con<pp>}, false_true(ee))
    case GT{}:
      Empty.absurd({WCon{ab, at} == WCon{bb, bt} : Word.Con<pp>}, false_true(ee))
    case EQ{}:
      match ab bb:
        case False{} False{}:
          Equal.cong(Word(pp), Word.Con<pp>, ww => WCon{False{}, ww}, at, bt,
            ih(Equal.cong(Cmp, Bool, xx => Cmp.is_eq(xx), Word.cmp(pp, at, bt), EQ{}, ec)))
        case True{} True{}:
          Equal.cong(Word(pp), Word.Con<pp>, ww => WCon{True{}, ww}, at, bt,
            ih(Equal.cong(Cmp, Bool, xx => Cmp.is_eq(xx), Word.cmp(pp, at, bt), EQ{}, ec)))
        case False{} True{}:
          Empty.absurd({WCon{False{}, at} == WCon{True{}, bt} : Word.Con<pp>}, false_true(ee))
        case True{} False{}:
          Empty.absurd({WCon{True{}, at} == WCon{False{}, bt} : Word.Con<pp>}, false_true(ee))

# words that compare equal are equal
law weq:
  for nn: Nat
  for aw: Word(nn)
  for bw: Word(nn)
  for ee: {Cmp.is_eq(Word.cmp(nn, aw, bw)) == True{} : Bool}
  {aw == bw : Word(nn)}

# the proof of weq
def weq(nn, aw, bw, ee):
  match nn:
    case 0n:
      match aw bw:
        case WNil{} WNil{}:
          {==}
    case 1n+(+pp):
      match aw bw:
        case WCon{ab, +at} WCon{bb, +bt}:
          weq.arm(pp, at, bt, Word.cmp(pp, at, bt), {==}, xx => weq(pp, at, bt, xx), ab, bb, ee)

# U32s that is_eq are equal
law ueq:
  for au: U32
  for bu: U32
  for ee: {U32.is_eq(au, bu) == True{} : Bool}
  {au == bu : U32}

# the proof of ueq
def ueq(au, bu, ee):
  match au bu:
    case U32{xw} U32{yw}:
      Equal.cong(Word(32n), U32, ww => U32{ww}, xw, yw, weq(32n, xw, yw, ee))

# ---- U32 and Nat: a count read as a U32 ----

# the type 0n names: Unit for 0n, Empty for a successor
def zero_ty(nn: Nat) -> Type:
  match nn:
    case 0n:
      Unit
    case 1n+_pp:
      Empty

# 0n is no successor
law zero_succ:
  for -kk: Nat
  for ee: {0n == 1n+kk : Nat}
  Empty

# the proof of zero_succ
def zero_succ(_kk, ee):
  %ee : zero_ty(_)
  Unit{}

# one less, with 0n below 1n
def nat_pred(nn: Nat) -> Nat:
  match nn:
    case 0n:
      0n
    case 1n+pp:
      pp

# successors that are equal come from equal numbers
law succ_inj:
  for +aa: Nat
  for +bb: Nat
  for ee: {1n+aa == 1n+bb : Nat}
  {aa == bb : Nat}

# the proof of succ_inj
def succ_inj(aa, bb, ee):
  Equal.cong(Nat, Nat, nn => nat_pred(nn), 1n+aa, 1n+bb, ee)

# Unit for True, Empty for False: tells them apart
def true_ty(bb: Bool) -> Type:
  match bb:
    case False{}:
      Empty
    case True{}:
      Unit

# True is never False
law true_false:
  for ee: {True{} == False{} : Bool}
  Empty

# the proof of true_false
def true_false(ee):
  %ee : true_ty(_)
  Unit{}

# one bit of adc_zero_carry, the rest given. From ezjson
law adc_zero_carry.at:
  for +qq: Nat
  for ab: Bool
  for -at: Word(qq)
  for ih: {Word.adc(qq, at, Word.zero(qq), True{}, True{}) == at : Word(qq)}
  {Word.adc.con(qq, at, Word.zero(qq), True{}, Bool.full_add(ab, True{}, True{})) == WCon{ab, at} : Word.Con<qq>}

# the proof of adc_zero_carry.at
def adc_zero_carry.at(qq, ab, at, ih):
  match ab:
    case True{}:
      Equal.cong(Word(qq), Word.Con<qq>, ww => WCon{True{}, ww},
        Word.adc(qq, at, Word.zero(qq), True{}, True{}), at, ih)
    case False{}:
      Equal.cong(Word(qq), Word.Con<qq>, ww => WCon{False{}, ww},
        Word.adc(qq, at, Word.zero(qq), True{}, True{}), at, ih)

# subtracting zero with the carry in adds nothing: a - 0 - 1 + 1 is a. From ezjson
law adc_zero_carry:
  for +pp: Nat
  for +aw: Word(pp)
  {Word.adc(pp, aw, Word.zero(pp), True{}, True{}) == aw : Word(pp)}

# the proof of adc_zero_carry
def adc_zero_carry(pp, aw):
  match pp:
    case 0n:
      match aw:
        case WNil{}:
          {==}
    case 1n+(+qq):
      match aw:
        case WCon{ab, +at}:
          adc_zero_carry.at(qq, ab, at, adc_zero_carry(qq, at))

# a word whose first bit is clear and that is not zero: the rest is not zero. From ezjson
law fin_ff:
  for cc: Cmp
  for h_nz: {Cmp.is_eq(Word.cmp.fin(False{}, False{}, cc)) == False{} : Bool}
  {Cmp.is_eq(cc) == False{} : Bool}

# the proof of fin_ff
def fin_ff(cc, h_nz):
  match cc:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({Cmp.is_eq(EQ{}) == False{} : Bool}, true_false(h_nz))
    case GT{}:
      {==}

# subtracting zero with no carry in takes one: a - 0 - 1, one less than a
# when a is not zero. From ezjson
law adc_zero_borrow:
  for +pp: Nat
  for +aw: Word(pp)
  for h_nz: {Cmp.is_eq(Word.cmp(pp, aw, Word.zero(pp))) == False{} : Bool}
  {1n+Word.to_nat(pp, Word.adc(pp, aw, Word.zero(pp), True{}, False{})) == Word.to_nat(pp, aw) : Nat}

# the proof of adc_zero_borrow
def adc_zero_borrow(pp, aw, h_nz):
  match pp:
    case 0n:
      match aw:
        case WNil{}:
          Empty.absurd({1n == 0n : Nat}, true_false(h_nz))
    case 1n+(+qq):
      match aw:
        case WCon{True{}, +at}:
          lc = Equal.sym(Word(qq), Word.adc(qq, at, Word.zero(qq), True{}, True{}), at, adc_zero_carry(qq, at))
          %lc : {1n+Nat.double(Word.to_nat(qq, _)) == 1n+Nat.double(Word.to_nat(qq, at)) : Nat}
          {==}
        case WCon{False{}, +at}:
          ih = adc_zero_borrow(qq, at, fin_ff(Word.cmp(qq, at, Word.zero(qq)), h_nz))
          %ih : {2n+Nat.double(Word.to_nat(qq, Word.adc(qq, at, Word.zero(qq), True{}, False{})))
            == Nat.double(_) : Nat}
          {==}

# one less than a nonzero U32, as a Nat. From ezjson
law u32_dec:
  for +uu: U32
  for h_nz: {U32.is_zero(uu) == False{} : Bool}
  {U32.to_nat(uu) == 1n+U32.to_nat(U32.sub(uu, 1)) : Nat}

# the proof of u32_dec
def u32_dec(uu, h_nz):
  match uu:
    case U32{WCon{True{}, +at}}:
      lc = Equal.sym(Word(31n), Word.adc(31n, at, Word.zero(31n), True{}, True{}), at, adc_zero_carry(31n, at))
      %lc : {1n+Nat.double(Word.to_nat(31n, at)) == 1n+Nat.double(Word.to_nat(31n, _)) : Nat}
      {==}
    case U32{WCon{False{}, +at}}:
      ih = adc_zero_borrow(31n, at, fin_ff(Word.cmp(31n, at, Word.zero(31n)), h_nz))
      %ih : {Nat.double(_)
        == 2n+Nat.double(Word.to_nat(31n, Word.adc(31n, at, Word.zero(31n), True{}, False{}))) : Nat}
      {==}

# a U32 worth a successor is not 0, once is_zero's answer is named
law u32_nonzero.at:
  for +uu: U32
  for -kk: Nat
  for bz: Bool
  for +ez: {U32.is_zero(uu) == bz : Bool}
  for hn: {U32.to_nat(uu) == 1n+kk : Nat}
  {U32.is_zero(uu) == False{} : Bool}

# the proof of u32_nonzero.at
def u32_nonzero.at(uu, kk, bz, ez, hn):
  match bz:
    case False{}:
      ez
    case True{}:
      +e0 = {ueq(uu, 0, ez) : {uu == 0 : U32}}
      Empty.absurd({U32.is_zero(uu) == False{} : Bool}, zero_succ(kk, Equal.trans(Nat, 0n, U32.to_nat(uu), 1n+kk,
        Equal.cong(U32, Nat, xu => U32.to_nat(xu), 0, uu, Equal.sym(U32, uu, 0, e0)), hn)))

# a U32 worth a successor is not 0
law u32_nonzero:
  for +uu: U32
  for -kk: Nat
  for hn: {U32.to_nat(uu) == 1n+kk : Nat}
  {U32.is_zero(uu) == False{} : Bool}

# the proof of u32_nonzero
def u32_nonzero(uu, kk, hn):
  u32_nonzero.at(uu, kk, U32.is_zero(uu), {==}, hn)

# one less than a U32 worth 1n+k is worth k
law u32_pred:
  for +uu: U32
  for +kk: Nat
  for +hn: {U32.to_nat(uu) == 1n+kk : Nat}
  {U32.to_nat(U32.sub(uu, 1)) == kk : Nat}

# the proof of u32_pred
def u32_pred(uu, kk, hn):
  succ_inj(U32.to_nat(U32.sub(uu, 1)), kk, Equal.trans(Nat, 1n+U32.to_nat(U32.sub(uu, 1)), U32.to_nat(uu), 1n+kk,
    Equal.sym(Nat, U32.to_nat(uu), 1n+U32.to_nat(U32.sub(uu, 1)), u32_dec(uu, u32_nonzero(uu, kk, hn))), hn))

# the Cmp LT names: Empty for LT, Unit otherwise
def lt_ty(cc: Cmp) -> Type:
  match cc:
    case LT{}:
      Empty
    case EQ{}:
      Unit
    case GT{}:
      Unit

# what a count runs down to over `xs`
def cd(xs: List<&2, U32>, +nn: U32) -> U32:
  match xs:
    case Nil{}:
      nn
    case _hd <> tl:
      cd(tl, (nn - 1 : U32))

# adding the carry then taking it back, from the lowest bit up, is nothing
law adc_inc_dec:
  for +qq: Nat
  for +aw: Word(qq)
  for cc: Bool
  {Word.adc(qq, Word.adc(qq, aw, Word.zero(qq), False{}, cc), Word.zero(qq), True{}, Bool.not(cc)) == aw : Word(qq)}

# the proof of adc_inc_dec
def adc_inc_dec(qq, aw, cc):
  match qq:
    case 0n:
      match aw:
        case WNil{}:
          {==}
    case 1n+(+pp):
      match aw cc:
        case WCon{False{}, +at} False{}:
          Equal.cong(Word(pp), Word.Con<pp>, ww => WCon{False{}, ww},
            Word.adc(pp, Word.adc(pp, at, Word.zero(pp), False{}, False{}), Word.zero(pp), True{}, True{}), at,
            adc_inc_dec(pp, at, False{}))
        case WCon{True{}, +at} False{}:
          Equal.cong(Word(pp), Word.Con<pp>, ww => WCon{True{}, ww},
            Word.adc(pp, Word.adc(pp, at, Word.zero(pp), False{}, False{}), Word.zero(pp), True{}, True{}), at,
            adc_inc_dec(pp, at, False{}))
        case WCon{False{}, +at} True{}:
          Equal.cong(Word(pp), Word.Con<pp>, ww => WCon{False{}, ww},
            Word.adc(pp, Word.adc(pp, at, Word.zero(pp), False{}, False{}), Word.zero(pp), True{}, True{}), at,
            adc_inc_dec(pp, at, False{}))
        case WCon{True{}, +at} True{}:
          Equal.cong(Word(pp), Word.Con<pp>, ww => WCon{True{}, ww},
            Word.adc(pp, Word.adc(pp, at, Word.zero(pp), False{}, True{}), Word.zero(pp), True{}, False{}), at,
            adc_inc_dec(pp, at, True{}))

# one more then one less is the same U32
law u32_dec_inc:
  for +uu: U32
  {U32.sub(U32.add(uu, 1), 1) == uu : U32}

# the proof of u32_dec_inc
def u32_dec_inc(uu):
  match uu:
    case U32{WCon{False{}, +at}}:
      Equal.cong(Word(31n), U32, ww => U32{WCon{False{}, ww}},
        Word.adc(31n, Word.adc(31n, at, Word.zero(31n), False{}, False{}), Word.zero(31n), True{}, True{}), at,
        adc_inc_dec(31n, at, False{}))
    case U32{WCon{True{}, +at}}:
      Equal.cong(Word(31n), U32, ww => U32{WCon{True{}, ww}},
        Word.adc(31n, Word.adc(31n, at, Word.zero(31n), False{}, True{}), Word.zero(31n), True{}, False{}), at,
        adc_inc_dec(31n, at, True{}))

# adding one more on the right
law nat_add_succ:
  for +aa: Nat
  for +bb: Nat
  {Nat.add(aa, 1n+bb) == 1n+Nat.add(aa, bb) : Nat}

# the proof of nat_add_succ
def nat_add_succ(aa, bb):
  match aa:
    case 0n:
      {==}
    case 1n+(+pp):
      Equal.cong(Nat, Nat, xx => 1n+xx, Nat.add(pp, 1n+bb), 1n+Nat.add(pp, bb), nat_add_succ(pp, bb))

# a bit as a Nat
def bit_nat(bb: Bool) -> Nat:
  match bb:
    case False{}:
      0n
    case True{}:
      1n

# comparing a bit and twice a Nat: the rest decides, the bit breaks a tie
law nat_cmp_bits:
  for +aa: Nat
  for +bb: Nat
  for xx: Bool
  for yy: Bool
  {Nat.cmp(Nat.add(bit_nat(xx), Nat.double(aa)), Nat.add(bit_nat(yy), Nat.double(bb))) ==
    Word.cmp.fin(xx, yy, Nat.cmp(aa, bb)) : Cmp}

# the proof of nat_cmp_bits
def nat_cmp_bits(aa, bb, xx, yy):
  match aa bb:
    case 0n 0n:
      match xx yy:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}
    case 1n+(+ap) 0n:
      match xx yy:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}
    case 0n 1n+(+bp):
      match xx yy:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}
    case 1n+(+ap) 1n+(+bp):
      match xx yy:
        case False{} False{}:
          nat_cmp_bits(ap, bp, False{}, False{})
        case False{} True{}:
          nat_cmp_bits(ap, bp, False{}, True{})
        case True{} False{}:
          nat_cmp_bits(ap, bp, True{}, False{})
        case True{} True{}:
          nat_cmp_bits(ap, bp, True{}, True{})

# words compare as the Nats they are
law w_cmp:
  for +nn: Nat
  for aa: Word(nn)
  for bb: Word(nn)
  {Word.cmp(nn, aa, bb) == Nat.cmp(Word.to_nat(nn, aa), Word.to_nat(nn, bb)) : Cmp}

# the proof of w_cmp
def w_cmp(nn, aa, bb):
  match nn:
    case 0n:
      match aa bb:
        case WNil{} WNil{}:
          {==}
    case 1n+(+pp):
      match aa bb:
        case WCon{False{}, +at} WCon{False{}, +bt}:
          Equal.trans(Cmp, Word.cmp.fin(False{}, False{}, Word.cmp(pp, at, bt)), Word.cmp.fin(False{}, False{},
            Nat.cmp(Word.to_nat(pp, at), Word.to_nat(pp, bt))),
            Nat.cmp(Nat.add(bit_nat(False{}), Nat.double(Word.to_nat(pp, at))), Nat.add(bit_nat(False{}),
              Nat.double(Word.to_nat(pp, bt)))),
            Equal.cong(Cmp, Cmp, zz => Word.cmp.fin(False{}, False{}, zz), Word.cmp(pp, at, bt),
              Nat.cmp(Word.to_nat(pp, at), Word.to_nat(pp, bt)),
              w_cmp(pp, at, bt)),
            Equal.sym(Cmp, Nat.cmp(Nat.add(bit_nat(False{}), Nat.double(Word.to_nat(pp, at))),
              Nat.add(bit_nat(False{}), Nat.double(Word.to_nat(pp, bt)))),
              Word.cmp.fin(False{}, False{}, Nat.cmp(Word.to_nat(pp, at), Word.to_nat(pp, bt))),
                nat_cmp_bits(Word.to_nat(pp, at), Word.to_nat(pp, bt), False{}, False{})))
        case WCon{False{}, +at} WCon{True{}, +bt}:
          Equal.trans(Cmp, Word.cmp.fin(False{}, True{}, Word.cmp(pp, at, bt)), Word.cmp.fin(False{}, True{},
            Nat.cmp(Word.to_nat(pp, at), Word.to_nat(pp, bt))),
            Nat.cmp(Nat.add(bit_nat(False{}), Nat.double(Word.to_nat(pp, at))), Nat.add(bit_nat(True{}),
              Nat.double(Word.to_nat(pp, bt)))),
            Equal.cong(Cmp, Cmp, zz => Word.cmp.fin(False{}, True{}, zz), Word.cmp(pp, at, bt), Nat.cmp(Word.to_nat(pp,
              at), Word.to_nat(pp, bt)),
              w_cmp(pp, at, bt)),
            Equal.sym(Cmp, Nat.cmp(Nat.add(bit_nat(False{}), Nat.double(Word.to_nat(pp, at))), Nat.add(bit_nat(True{}),
              Nat.double(Word.to_nat(pp, bt)))),
              Word.cmp.fin(False{}, True{}, Nat.cmp(Word.to_nat(pp, at), Word.to_nat(pp, bt))),
                nat_cmp_bits(Word.to_nat(pp, at), Word.to_nat(pp, bt), False{}, True{})))
        case WCon{True{}, +at} WCon{False{}, +bt}:
          Equal.trans(Cmp, Word.cmp.fin(True{}, False{}, Word.cmp(pp, at, bt)), Word.cmp.fin(True{}, False{},
            Nat.cmp(Word.to_nat(pp, at), Word.to_nat(pp, bt))),
            Nat.cmp(Nat.add(bit_nat(True{}), Nat.double(Word.to_nat(pp, at))), Nat.add(bit_nat(False{}),
              Nat.double(Word.to_nat(pp, bt)))),
            Equal.cong(Cmp, Cmp, zz => Word.cmp.fin(True{}, False{}, zz), Word.cmp(pp, at, bt), Nat.cmp(Word.to_nat(pp,
              at), Word.to_nat(pp, bt)),
              w_cmp(pp, at, bt)),
            Equal.sym(Cmp, Nat.cmp(Nat.add(bit_nat(True{}), Nat.double(Word.to_nat(pp, at))), Nat.add(bit_nat(False{}),
              Nat.double(Word.to_nat(pp, bt)))),
              Word.cmp.fin(True{}, False{}, Nat.cmp(Word.to_nat(pp, at), Word.to_nat(pp, bt))),
                nat_cmp_bits(Word.to_nat(pp, at), Word.to_nat(pp, bt), True{}, False{})))
        case WCon{True{}, +at} WCon{True{}, +bt}:
          Equal.trans(Cmp, Word.cmp.fin(True{}, True{}, Word.cmp(pp, at, bt)), Word.cmp.fin(True{}, True{},
            Nat.cmp(Word.to_nat(pp, at), Word.to_nat(pp, bt))),
            Nat.cmp(Nat.add(bit_nat(True{}), Nat.double(Word.to_nat(pp, at))), Nat.add(bit_nat(True{}),
              Nat.double(Word.to_nat(pp, bt)))),
            Equal.cong(Cmp, Cmp, zz => Word.cmp.fin(True{}, True{}, zz), Word.cmp(pp, at, bt), Nat.cmp(Word.to_nat(pp,
              at), Word.to_nat(pp, bt)),
              w_cmp(pp, at, bt)),
            Equal.sym(Cmp, Nat.cmp(Nat.add(bit_nat(True{}), Nat.double(Word.to_nat(pp, at))), Nat.add(bit_nat(True{}),
              Nat.double(Word.to_nat(pp, bt)))),
              Word.cmp.fin(True{}, True{}, Nat.cmp(Word.to_nat(pp, at), Word.to_nat(pp, bt))),
                nat_cmp_bits(Word.to_nat(pp, at), Word.to_nat(pp, bt), True{}, True{})))

# U32s compare as the Nats they are
law u_cmp:
  for aa: U32
  for bb: U32
  {U32.cmp(aa, bb) == Nat.cmp(U32.to_nat(aa), U32.to_nat(bb)) : Cmp}

# the proof of u_cmp
def u_cmp(aa, bb):
  match aa bb:
    case U32{xw} U32{yw}:
      w_cmp(32n, xw, yw)

# adding 0 on the right
def nat_add_zero(+aa: Nat) -> {Nat.add(aa, 0n) == aa : Nat}:
  match aa:
    case 0n:
      {==}
    case 1n+(+pp):
      Equal.cong(Nat, Nat, xx => 1n+xx, Nat.add(pp, 0n), pp, nat_add_zero(pp))

# one less, or zero
def pred(nn: Nat) -> Nat:
  match nn:
    case 0n:
      0n
    case 1n+pp:
      pp

# a sum with a successor on the right is at most n: its left addend is below n
def nlt_add(
  +aa: Nat,
  +bb: Nat,
  +nn: Nat,
  h_le: {Nat.is_le(Nat.add(aa, 1n+bb), nn) == True{} : Bool}
) -> {Nat.is_lt(aa, nn) == True{} : Bool}:
  match aa nn:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, false_true(h_le))
    case 0n 1n+_np:
      {==}
    case 1n+_ap 0n:
      Empty.absurd({Nat.is_lt(aa, 0n) == True{} : Bool}, false_true(h_le))
    case 1n+(+ap) 1n+(+np):
      nlt_add(ap, bb, np, h_le)

# the word of all ones
def ones(nn: Nat) -> Word(nn):
  match nn:
    case 0n:
      WNil{}
    case 1n+pp:
      WCon{True{}, ones(pp)}

# one bit of ones_nlt: the rest given, as cc
def ones_nlt.at(
  cc: Cmp,
  bb: Bool,
  ih: {cc == LT{} : Cmp} -> Empty,
  ee: {Word.cmp.fin(True{}, bb, cc) == LT{} : Cmp}
) -> Empty:
  match cc:
    case LT{}:
      ih({==})
    case GT{}:
      %ee : lt_ty(_)
      Unit{}
    case EQ{}:
      match bb:
        case False{}:
          %ee : lt_ty(_)
          Unit{}
        case True{}:
          %ee : lt_ty(_)
          Unit{}

# no word is above all ones
def ones_nlt(nn: Nat, ww: Word(nn), ee: {Word.cmp(nn, ones(nn), ww) == LT{} : Cmp}) -> Empty:
  match nn:
    case 0n:
      match ww:
        case WNil{}:
          %ee : lt_ty(_)
          Unit{}
    case 1n+(+pp):
      match ww:
        case WCon{bb, +tt}:
          ones_nlt.at(Word.cmp(pp, ones(pp), tt), bb, xx => ones_nlt(pp, tt, xx), ee)

# the top U32, compared with a word, once the comparison is named cc
def top_nlt.at(
  cc: Cmp,
  ww: Word(32n),
  ec: {Word.cmp(32n, ones(32n), ww) == cc : Cmp}
) -> {Cmp.is_lt(cc) == False{} : Bool}:
  match cc:
    case LT{}:
      Empty.absurd({True{} == False{} : Bool}, ones_nlt(32n, ww, ec))
    case EQ{}:
      {==}
    case GT{}:
      {==}

# the top U32, 0 - 1, is below nothing
def top_nlt(+cap: U32) -> {U32.is_lt(U32.sub(0, 1), cap) == False{} : Bool}:
  match cap:
    case U32{+ww}:
      top_nlt.at(Word.cmp(32n, ones(32n), ww), ww, {==})

# a U32 below cap plus one, as a Nat, once whether the sum is zero is named zz
def inc_nat.at(
  +aa: U32,
  +cap: U32,
  zz: Bool,
  ez: {U32.is_zero(U32.add(aa, 1)) == zz : Bool},
  h_lt: {U32.is_lt(aa, cap) == True{} : Bool}
) -> {U32.to_nat(U32.add(aa, 1)) == 1n+U32.to_nat(aa) : Nat}:
  match zz:
    case False{}:
      Equal.trans(Nat, U32.to_nat(U32.add(aa, 1)), 1n+U32.to_nat(U32.sub(U32.add(aa, 1), 1)), 1n+U32.to_nat(aa),
        u32_dec(U32.add(aa, 1), ez),
        Equal.cong(U32, Nat, uu => 1n+U32.to_nat(uu), U32.sub(U32.add(aa, 1), 1), aa, u32_dec_inc(aa)))
    case True{}:
      e0 = ueq(U32.add(aa, 1), 0, ez)
      back = Equal.sym(U32, U32.sub(U32.add(aa, 1), 1), aa, u32_dec_inc(aa))
      down = Equal.cong(U32, U32, xx => U32.sub(xx, 1), U32.add(aa, 1), 0, e0)
      at_top = Equal.trans(U32, aa, U32.sub(U32.add(aa, 1), 1), U32.sub(0, 1), back, down)
      top = Equal.cong(U32, Bool, xx => U32.is_lt(xx, cap), aa, U32.sub(0, 1), at_top)
      Empty.absurd({U32.to_nat(U32.add(aa, 1)) == 1n+U32.to_nat(aa) : Nat}, true_false(Equal.trans(Bool, True{},
        U32.is_lt(U32.sub(0, 1), cap), False{},
        Equal.trans(Bool, True{}, U32.is_lt(aa, cap), U32.is_lt(U32.sub(0, 1), cap), Equal.sym(Bool,
          U32.is_lt(aa, cap), True{}, h_lt), top), top_nlt(cap))))

# a U32 below cap plus one, as a Nat
def inc_nat(
  +aa: U32,
  +cap: U32,
  h_lt: {U32.is_lt(aa, cap) == True{} : Bool}
) -> {U32.to_nat(U32.add(aa, 1)) == 1n+U32.to_nat(aa) : Nat}:
  inc_nat.at(aa, cap, U32.is_zero(U32.add(aa, 1)), {==}, h_lt)

# a U32 is below cap when its Nat is
def u_lt(
  +aa: U32,
  +cap: U32,
  h_lt: {Nat.is_lt(U32.to_nat(aa), U32.to_nat(cap)) == True{} : Bool}
) -> {U32.is_lt(aa, cap) == True{} : Bool}:
  Equal.trans(Bool, U32.is_lt(aa, cap), Nat.is_lt(U32.to_nat(aa), U32.to_nat(cap)), True{},
    Equal.cong(Cmp, Bool, cc => Cmp.is_lt(cc), U32.cmp(aa, cap), Nat.cmp(U32.to_nat(aa), U32.to_nat(cap)),
      u_cmp(aa, cap)), h_lt)

# counting xs up from aa, as a Nat, when the sum stays within cap
def up(
  +xs: List<&2, U32>,
  +aa: U32,
  +cap: U32,
  +h_le: {Nat.is_le(Nat.add(U32.to_nat(aa), List.length(&2, U32, xs)), U32.to_nat(cap)) == True{} : Bool}
) -> {U32.to_nat(Png.enc.len(xs, aa)) == Nat.add(U32.to_nat(aa), List.length(&2, U32, xs)) : Nat}:
  match xs:
    case Nil{}:
      Equal.sym(Nat, Nat.add(U32.to_nat(aa), 0n), U32.to_nat(aa), nat_add_zero(U32.to_nat(aa)))
    case _hd <> +tl:
      +xx = U32.to_nat(aa)
      +nt = List.length(&2, U32, tl)
      +a1 = U32.add(aa, 1)
      +inc = inc_nat(aa, cap, u_lt(aa, cap, nlt_add(xx, nt, U32.to_nat(cap), h_le)))
      +sw = Equal.trans(Nat, Nat.add(xx, 1n+nt), 1n+Nat.add(xx, nt), Nat.add(U32.to_nat(a1), nt), nat_add_succ(xx, nt),
        Equal.cong(Nat, Nat, yy => Nat.add(yy, nt), 1n+xx, U32.to_nat(a1), Equal.sym(Nat, U32.to_nat(a1), 1n+xx, inc)))
      +h2 = Equal.trans(Bool, Nat.is_le(Nat.add(U32.to_nat(a1), nt), U32.to_nat(cap)), Nat.is_le(Nat.add(xx, 1n+nt),
        U32.to_nat(cap)), True{}, Equal.cong(Nat, Bool, yy => Nat.is_le(yy, U32.to_nat(cap)), Nat.add(U32.to_nat(a1),
        nt), Nat.add(xx, 1n+nt), Equal.sym(Nat, Nat.add(xx, 1n+nt), Nat.add(U32.to_nat(a1), nt), sw)), h_le)
      Equal.trans(Nat, U32.to_nat(Png.enc.len(tl, a1)), Nat.add(U32.to_nat(a1), nt), Nat.add(xx, 1n+nt),
        up(tl, a1, cap, h2), Equal.sym(Nat, Nat.add(xx, 1n+nt), Nat.add(U32.to_nat(a1), nt), sw))

# reversing onto acc, then reversing that onto ys: acc reversed onto xs then ys
def revrev(
  +xs: List<&2, U32>,
  +acc: List<&2, U32>,
  +ys: List<&2, U32>
) -> {List.reverse.go(&2, U32, List.reverse.go(&2, U32, xs, acc), ys) == List.reverse.go(&2, U32, acc, List.append(&2,
  U32, xs, ys)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case +hd <> +tl:
      revrev(tl, hd <> acc, ys)

# a list reversed, reversed onto out: the list, then out
def rr(
  +xs: List<&2, U32>,
  +out: List<&2, U32>
) -> {List.reverse.go(&2, U32, List.reverse(&2, U32, xs), out) == List.append(&2, U32, xs, out) : List<&2, U32>}:
  revrev(xs, [], out)

# appending nothing
def app_nil(+xs: List<&2, U32>) -> {List.append(&2, U32, xs, []) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case +hd <> +tl:
      Equal.cong(List<&2, U32>, List<&2, U32>, ll => hd <> ll, List.append(&2, U32, tl, []), tl, app_nil(tl))

# append associates
def app_assoc(
  +aa: List<&2, U32>,
  +bb: List<&2, U32>,
  +cc: List<&2, U32>
) -> {List.append(&2, U32, List.append(&2, U32, aa, bb), cc) == List.append(&2, U32, aa, List.append(&2, U32, bb, cc)) :
  List<&2, U32>}:
  match aa:
    case Nil{}:
      {==}
    case +hd <> +tl:
      Equal.cong(List<&2, U32>, List<&2, U32>, ll => hd <> ll, List.append(&2, U32, List.append(&2, U32, tl, bb), cc),
        List.append(&2, U32, tl, List.append(&2, U32, bb, cc)), app_assoc(tl, bb, cc))

# a list reversed onto out is as long as both
def len_revgo(
  +xs: List<&2, U32>,
  +out: List<&2, U32>
) -> {List.length(&2, U32, List.reverse.go(&2, U32, xs, out)) == Nat.add(List.length(&2, U32, xs), List.length(&2, U32,
  out)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +hd <> +tl:
      Equal.trans(Nat, List.length(&2, U32, List.reverse.go(&2, U32, tl, hd <> out)), Nat.add(List.length(&2, U32, tl),
        1n+List.length(&2, U32, out)), 1n+Nat.add(List.length(&2, U32, tl), List.length(&2, U32, out)),
        len_revgo(tl, hd <> out), nat_add_succ(List.length(&2, U32, tl), List.length(&2, U32, out)))

# a list reversed is as long
def len_rev(
  +xs: List<&2, U32>
) -> {List.length(&2, U32, List.reverse(&2, U32, xs)) == List.length(&2, U32, xs) : Nat}:
  Equal.trans(Nat, List.length(&2, U32, List.reverse(&2, U32, xs)), Nat.add(List.length(&2, U32, xs), 0n),
    List.length(&2, U32, xs), len_revgo(xs, []), nat_add_zero(List.length(&2, U32, xs)))

# a list reversed onto nothing, reversed again, is the list
def inf.rev_rev(+xs: List<&2, U32>) -> {List.reverse(&2, U32, List.reverse.go(&2, U32, xs, [])) == xs : List<&2, U32>}:
  Equal.trans(List<&2, U32>, List.reverse(&2, U32, List.reverse.go(&2, U32, xs, [])), List.append(&2, U32, xs, []),
    xs, revrev(xs, [], []), app_nil(xs))

# reversing onto acc, then reversing that onto ys, puts acc back in front of xs ++ ys
law rev_rev.go:
  for +xs: List<&2, U32>
  for +acc: List<&2, U32>
  for +ys: List<&2, U32>
  {List.reverse.go(&2, U32, List.reverse.go(&2, U32, xs, acc), ys)
    == List.reverse.go(&2, U32, acc, List.append(&2, U32, xs, ys)) : List<&2, U32>}

# the proof of rev_rev.go
def rev_rev.go(xs, acc, ys):
  match xs:
    case Nil{}:
      {==}
    case +hd <> +tl:
      rev_rev.go(tl, hd <> acc, ys)

# appending nothing
law flt.app_nil:
  for +xs: List<&2, U32>
  {List.append(&2, U32, xs, Nil{}) == xs : List<&2, U32>}

# the proof of flt.app_nil
def flt.app_nil(xs):
  match xs:
    case Nil{}:
      {==}
    case +hd <> +tl:
      Equal.cong(List<&2, U32>, List<&2, U32>, ll => {hd <> ll : List<&2, U32>}, List.append(&2, U32, tl, Nil{}), tl,
        flt.app_nil(tl))

# reversing twice gives the list back
law flt.rev_rev:
  for +xs: List<&2, U32>
  {List.reverse(&2, U32, List.reverse.go(&2, U32, xs, Nil{})) == xs : List<&2, U32>}

# the proof of flt.rev_rev
def flt.rev_rev(xs):
  Equal.trans(List<&2, U32>, List.reverse(&2, U32, List.reverse.go(&2, U32, xs, Nil{})),
    List.append(&2, U32, xs, Nil{}), xs, rev_rev.go(xs, Nil{}, Nil{}), flt.app_nil(xs))

# the 1 a subtraction takes away when no carry comes in
def nb(cc: Bool) -> Nat:
  match cc:
    case True{}:
      0n
    case False{}:
      1n

# the type True names here: Unit for True, Empty for False
def pdec.true_ty(bb: Bool) -> Type:
  match bb:
    case True{}:
      Unit
    case False{}:
      Empty

# True is never False
law pdec.true_false:
  for ee: {True{} == False{} : Bool}
  Empty

# the proof of pdec.true_false
def pdec.true_false(ee):
  %ee : pdec.true_ty(_)
  Unit{}

# ---- Nat arithmetic ----

# a plus zero is a
law ras.add_zero:
  for aa: Nat
  {Nat.add(aa, 0n) == aa : Nat}

# the proof of ras.add_zero
def ras.add_zero(aa):
  match aa:
    case 0n:
      {==}
    case 1n+pp:
      Equal.cong(Nat, Nat, xx => 1n+xx, Nat.add(pp, 0n), pp, ras.add_zero(pp))

# a plus one more than b is one more than a plus b
law ras.add_succ:
  for aa: Nat
  for -bb: Nat
  {Nat.add(aa, 1n+bb) == 1n+Nat.add(aa, bb) : Nat}

# the proof of ras.add_succ
def ras.add_succ(aa, bb):
  match aa:
    case 0n:
      {==}
    case 1n+pp:
      Equal.cong(Nat, Nat, xx => 1n+xx, Nat.add(pp, 1n+bb), 1n+Nat.add(pp, bb), ras.add_succ(pp, bb))

# addition commutes
law ras.add_comm:
  for aa: Nat
  for +bb: Nat
  {Nat.add(aa, bb) == Nat.add(bb, aa) : Nat}

# the proof of ras.add_comm
def ras.add_comm(aa, bb):
  match aa:
    case 0n:
      Equal.sym(Nat, Nat.add(bb, 0n), bb, ras.add_zero(bb))
    case 1n+pp:
      Equal.trans(Nat, 1n+Nat.add(pp, bb), 1n+Nat.add(bb, pp), Nat.add(bb, 1n+pp),
        Equal.cong(Nat, Nat, xx => 1n+xx, Nat.add(pp, bb), Nat.add(bb, pp), ras.add_comm(pp, bb)),
        Equal.sym(Nat, Nat.add(bb, 1n+pp), 1n+Nat.add(bb, pp), ras.add_succ(bb, pp)))

# addition associates
law ras.add_assoc:
  for aa: Nat
  for -bb: Nat
  for -cc: Nat
  {Nat.add(Nat.add(aa, bb), cc) == Nat.add(aa, Nat.add(bb, cc)) : Nat}

# the proof of ras.add_assoc
def ras.add_assoc(aa, bb, cc):
  match aa:
    case 0n:
      {==}
    case 1n+pp:
      Equal.cong(Nat, Nat, xx => 1n+xx, Nat.add(Nat.add(pp, bb), cc), Nat.add(pp, Nat.add(bb, cc)),
        ras.add_assoc(pp, bb, cc))

# the first two of three summands swap
law add_swap:
  for +aa: Nat
  for +bb: Nat
  for +cc: Nat
  {Nat.add(aa, Nat.add(bb, cc)) == Nat.add(bb, Nat.add(aa, cc)) : Nat}

# the proof of add_swap
def add_swap(aa, bb, cc):
  Equal.trans(Nat, Nat.add(aa, Nat.add(bb, cc)), Nat.add(Nat.add(aa, bb), cc), Nat.add(bb, Nat.add(aa, cc)),
    Equal.sym(Nat, Nat.add(Nat.add(aa, bb), cc), Nat.add(aa, Nat.add(bb, cc)), ras.add_assoc(aa, bb, cc)),
    Equal.trans(Nat, Nat.add(Nat.add(aa, bb), cc), Nat.add(Nat.add(bb, aa), cc), Nat.add(bb, Nat.add(aa, cc)),
      Equal.cong(Nat, Nat, xx => Nat.add(xx, cc), Nat.add(aa, bb), Nat.add(bb, aa), ras.add_comm(aa, bb)),
      ras.add_assoc(bb, aa, cc)))

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
          Equal.cong(Nat, Nat, xx => 1n+xx, Nat.add(pp, 1n+pp), 1n+Nat.add(pp, pp), ras.add_succ(pp, pp))))

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
          Nat.add(cc, Nat.add(Nat.mul(pp, cc), Nat.mul(bb, cc))), ras.add_assoc(cc, Nat.mul(pp, cc), Nat.mul(bb, cc))))

# two to one more than p is the double of two to p
law pow2_succ:
  for +pp: Nat
  {Nat.pow(2n, 1n+pp) == Nat.double(Nat.pow(2n, pp)) : Nat}

# the proof of pow2_succ
def pow2_succ(pp):
  Equal.trans(Nat, Nat.add(Nat.pow(2n, pp), Nat.add(Nat.pow(2n, pp), 0n)),
    Nat.add(Nat.pow(2n, pp), Nat.pow(2n, pp)), Nat.double(Nat.pow(2n, pp)),
    Equal.cong(Nat, Nat, xx => Nat.add(Nat.pow(2n, pp), xx), Nat.add(Nat.pow(2n, pp), 0n), Nat.pow(2n, pp),
      ras.add_zero(Nat.pow(2n, pp))),
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
      Empty.absurd({Nat.is_lt(_xx, _zz) == True{} : Bool}, false_true(
        Equal.trans(Bool, False{}, Nat.is_lt(_xx, 0n), True{}, lt_zero_false(_xx), hxy)))
    case _xx 1n+_qq 0n:
      Empty.absurd({Nat.is_lt(_xx, 0n) == True{} : Bool}, false_true(hyz))
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
      Empty.absurd({Nat.is_le(1n+_pp, _zz) == True{} : Bool}, false_true(hxy))
    case 1n+_pp 1n+_qq 0n:
      Empty.absurd({False{} == True{} : Bool}, false_true(hyz))
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
      Empty.absurd({Nat.is_lt(_xx, 0n) == True{} : Bool}, false_true(
        Equal.trans(Bool, False{}, Nat.is_lt(_yy, 0n), True{}, lt_zero_false(_yy), hyz)))
    case 0n _yy 1n+_rr:
      {==}
    case 1n+_pp 0n 1n+_rr:
      Empty.absurd({Nat.is_lt(1n+_pp, 1n+_rr) == True{} : Bool}, false_true(hxy))
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
      Empty.absurd({False{} == True{} : Bool}, false_true(hh))
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
law ras.word_cmp_nat:
  for nn: Nat
  for aw: Word(nn)
  for bw: Word(nn)
  {Word.cmp(nn, aw, bw) == Nat.cmp(Word.to_nat(nn, aw), Word.to_nat(nn, bw)) : Cmp}

# the proof of ras.word_cmp_nat
def ras.word_cmp_nat(nn, aw, bw):
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
              ras.word_cmp_nat(pp, at, bt)),
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
        Nat.cmp(Word.to_nat(32n, xw), Word.to_nat(32n, yw)), ras.word_cmp_nat(32n, xw, yw))

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
      Empty.absurd({False{} == True{} : Bool}, false_true(hh))
    case False{} GT{}:
      Empty.absurd({False{} == True{} : Bool}, false_true(hh))
    case True{} LT{}:
      {==}
    case True{} EQ{}:
      Empty.absurd({False{} == True{} : Bool}, false_true(hh))
    case True{} GT{}:
      Empty.absurd({False{} == True{} : Bool}, false_true(hh))

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
      Empty.absurd({0n == 1n : Nat}, false_true(hh))

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
law ras.nat_eq_true:
  for aa: Nat
  for bb: Nat
  for hh: {Nat.is_eq(aa, bb) == True{} : Bool}
  {aa == bb : Nat}

# the proof of ras.nat_eq_true
def ras.nat_eq_true(aa, bb, hh):
  match aa bb:
    case 0n 0n:
      {==}
    case 0n 1n+_qq:
      Empty.absurd({0n == 1n+_qq : Nat}, false_true(hh))
    case 1n+_pp 0n:
      Empty.absurd({1n+_pp == 0n : Nat}, false_true(hh))
    case 1n+pp 1n+qq:
      Equal.cong(Nat, Nat, xx => 1n+xx, pp, qq, ras.nat_eq_true(pp, qq, hh))

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
    le_rw_l(Nat.add(dd, aa), Nat.add(aa, dd), Nat.add(bb, dd), ras.add_comm(dd, aa),
      le_rw_r(Nat.add(dd, aa), Nat.add(dd, bb), Nat.add(bb, dd), ras.add_comm(dd, bb), le_add_mono(dd, aa, bb, hab))))

# True is never False
def jst.true_false(ee: {True{} == False{} : Bool}) -> Empty:
  false_true(Equal.sym(Bool, True{}, False{}, ee))

# a comparison that is greater is not equal
def gt_ne(cc: Cmp, hh: {Cmp.is_gt(cc) == True{} : Bool}) -> {Cmp.is_eq(cc) == False{} : Bool}:
  match cc:
    case LT{}:
      Empty.absurd({False{} == False{} : Bool}, false_true(hh))
    case EQ{}:
      Empty.absurd({True{} == False{} : Bool}, false_true(hh))
    case GT{}:
      {==}

# a comparison that is at most is not greater
def le_ngt(cc: Cmp, hh: {Cmp.is_le(cc) == True{} : Bool}) -> {Cmp.is_gt(cc) == False{} : Bool}:
  match cc:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({True{} == False{} : Bool}, false_true(hh))

# the encoder's size test is false when no side is zero and none passes 65535
def bad_no(
  zw: Bool,
  zh: Bool,
  bw: Bool,
  bh: Bool,
  ew: {zw == False{} : Bool},
  eh: {zh == False{} : Bool},
  gw: {bw == False{} : Bool},
  gh: {bh == False{} : Bool}
) -> {Jenc.encode.bad.w(zw, zh, bw, bh) == False{} : Bool}:
  match zw zh bw bh:
    case False{} False{} False{} False{}:
      {==}
    case True{} _zh _bw _bh:
      Empty.absurd({True{} == False{} : Bool}, jst.true_false(ew))
    case False{} True{} _bw _bh:
      Empty.absurd({True{} == False{} : Bool}, jst.true_false(eh))
    case False{} False{} True{} _bh:
      Empty.absurd({True{} == False{} : Bool}, jst.true_false(gw))
    case False{} False{} False{} True{}:
      Empty.absurd({True{} == False{} : Bool}, jst.true_false(gh))

# ---- the marker walk (laws/JpegRefusesNonBaselineFrames.bend) ----

# the phases the walk may be in between two segments: seeking a marker, inside a scan, or stopped
def ph.ok(ph: Jpeg.Phase) -> Bool:
  match ph:
    case Jpeg.Seek{}:
      True{}
    case Jpeg.Ent{}:
      True{}
    case Jpeg.Stop{}:
      True{}
    case Jpeg.Mark{}:
      False{}
    case Jpeg.LenHi{_mark}:
      False{}
    case Jpeg.LenLo{_mark, _hi}:
      False{}
    case Jpeg.Pay{_mark, _left, _acc}:
      False{}
    case Jpeg.EntFF{}:
      False{}
    case Jpeg.Rest{_mark, _acc}:
      False{}

# a walk state between two segments that has read no frame header: kind is still 0
def inv(st: Jpeg.St) -> Bool:
  match st:
    case Jpeg.St{ph, _fr, _sc, _tb, _en, _ri, kind, _bad}:
      Bool.and(ph.ok(ph), U32.is_eq(kind, 0))

# ---- A. four bytes of a U32, put back together ----

# a U32 from its 32 bits, low bit first
def w32(
  b0: Bool,
  b1: Bool,
  b2: Bool,
  b3: Bool,
  b4: Bool,
  b5: Bool,
  b6: Bool,
  b7: Bool,
  b8: Bool,
  b9: Bool,
  b10: Bool,
  b11: Bool,
  b12: Bool,
  b13: Bool,
  b14: Bool,
  b15: Bool,
  b16: Bool,
  b17: Bool,
  b18: Bool,
  b19: Bool,
  b20: Bool,
  b21: Bool,
  b22: Bool,
  b23: Bool,
  b24: Bool,
  b25: Bool,
  b26: Bool,
  b27: Bool,
  b28: Bool,
  b29: Bool,
  b30: Bool,
  b31: Bool
) -> U32:
  U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11,
    WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22,
    WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31,
    WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

# ---- C. the walker's state, chunk by chunk ----

# the state after IHDR, PLTE when there is one, and tRNS when there is one,
# with idat the IDAT data so far, newest first, and sid whether an IDAT came
def st(
  +ww: U32,
  +hh: U32,
  +cc: U32,
  +plte: Maybe<&2, List<&2, U32>>,
  +trns: Maybe<&2, List<&2, U32>>,
  idat: List<&2, U32>,
  sid: Bool
) -> Png.Pg:
  Png.Pg{ww, hh, 8, cc, 0, 0, 0, idat, D1.spec.or.nil(plte), D1.spec.or.nil(trns), True{},
    Maybe.is_some(&2, List<&2, U32>, plte), sid, False{}, Maybe.is_some(&2, List<&2, U32>, trns), False{}}

# a colour type other than 3, or a PLTE: what IDAT and IEND ask of the state
def need(+cc: U32, +plte: Maybe<&2, List<&2, U32>>) -> Bool:
  Bool.or(Bool.not(U32.is_eq(cc, 3)), Maybe.is_some(&2, List<&2, U32>, plte))

# the channel bytes enc.push writes for a sample, in order: red, green, blue,
# and alpha when the picture is not opaque
def chans(op: Bool, +cc: U32) -> List<&2, U32>:
  match op:
    case True{}:
      [Png.enc.r(cc), Png.enc.g(cc), Png.enc.b(cc)]
    case False{}:
      [Png.enc.r(cc), Png.enc.g(cc), Png.enc.b(cc), Png.enc.a(cc)]

# the bytes enc.raw writes, in order, from row position left: a filter byte 0
# where a row starts, then each sample's channels
def sc(px: List<&2, U32>, left: Nat, +ww: Nat, +op: Bool) -> List<&2, U32>:
  match px left:
    case Nil{} _left:
      []
    case +cc <> tl 0n:
      0 <> List.append(&2, U32, chans(op, cc), sc(tl, Png.enc.pred(ww), ww, op))
    case +cc <> tl 1n+pp:
      List.append(&2, U32, chans(op, cc), sc(tl, pp, ww, op))

# ---- F. the scanlines as rows, and each byte a byte ----

# every byte is its own low byte: masking it with 255 leaves it
def masked(xs: List<&2, U32>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case +xx <> tl:
      {U32.and(255, xx) == xx : U32} & masked(tl)

# the first k samples
def tk(kk: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match kk xs:
    case 0n _xs:
      []
    case 1n+_pp Nil{}:
      []
    case 1n+pp +hd <> tl:
      hd <> tk(pp, tl)

# the samples after the first k
def dr(kk: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match kk xs:
    case 0n xs:
      xs
    case 1n+_pp Nil{}:
      []
    case 1n+pp _hd <> tl:
      dr(pp, tl)

# xs is qq then rr, of lengths k and m
def split.of(+kk: Nat, +mm: Nat, +xs: List<&2, U32>, +qq: List<&2, U32>, +rr: List<&2, U32>) -> Type:
  {xs == List.append(&2, U32, qq, rr) : List<&2, U32>} & {List.length(&2, U32, qq) == kk : Nat} &
    {List.length(&2, U32, rr) == mm : Nat}

# what split proves: xs is its first k and the rest, of those lengths
def split.ty(+kk: Nat, +mm: Nat, +xs: List<&2, U32>) -> Type:
  split.of(kk, mm, xs, tk(kk, xs), dr(kk, xs))

# one more sample in front: the split one further
def prt.split.up(
  +pp: Nat,
  +mm: Nat,
  +hd: U32,
  +tl: List<&2, U32>,
  sp: split.ty(pp, mm, tl)
) -> split.ty(1n+pp, mm, hd <> tl):
  (e1, (e2, e3)) = sp
  +qq = tk(pp, tl)
  +rr = dr(pp, tl)
  (Equal.cong(List<&2, U32>, List<&2, U32>, ys => hd <> ys, tl, List.append(&2, U32, qq, rr), e1),
    (Equal.cong(Nat, Nat, nn => 1n+nn, List.length(&2, U32, qq), pp, e2), e3))

# a list of k + m samples splits into k and m
def split(
  kk: Nat,
  +mm: Nat,
  +xs: List<&2, U32>,
  hl: {List.length(&2, U32, xs) == Nat.add(kk, mm) : Nat}
) -> split.ty(kk, mm, xs):
  match kk xs:
    case 0n _xs:
      ({==}, ({==}, hl))
    case 1n+pp Nil{}:
      Empty.absurd(split.ty(1n+pp, mm, []), zero_succ(Nat.add(pp, mm), hl))
    case 1n+(+pp) +hd <> +tl:
      prt.split.up(pp, mm, hd, tl, split(pp, mm, tl, succ_inj(List.length(&2, U32, tl), Nat.add(pp, mm), hl)))

# rows as scanlines: a filter byte 0 before each
def scan(rows: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match rows:
    case Nil{}:
      []
    case +row <> tl:
      0 <> List.append(&2, U32, row, scan(tl))

# ---- G. the samples back, and the counts in range ----

# Base's List.all steps through List.all.if, which is Bool.and of its hit and the rest
def all.if.and(hit: Bool, rest: Bool) -> {List.all.if(_u => rest, hit) == Bool.and(hit, rest) : Bool}:
  match hit:
    case False{}:
      {==}
    case True{}:
      {==}

# ---- the SOF0 refusals (laws/JpegPlacesComponentSamples.bend) ----

# the state a refused frame header leaves the walk in (the same state as w8.stop)
def stop(+sc: Jpeg.Scan, +tb: Jpeg.Tabs, +en: List<&2, U32>, +ri: U32, +kd: U32) -> Jpeg.St:
  Jpeg.St{Jpeg.Stop{}, Jpeg.decode.frame0(), sc, tb, en, ri, kd, 1}

# ---- the MCU walk over the frame (laws/JpegPlacesComponentSamples.bend) ----

# the walk's next position, the restart count dropped
def nxt(+ctrl: Jpeg.Ctrl, +fr: Jpeg.Frame, +sc: Jpeg.Scan, +ri: U32) -> Jpeg.Ctrl:
  L1.jpg.pos(Jpeg.decode.adv.ctrl(Jpeg.decode.adv(ctrl, fr, sc, ri)))

# the positions of the next left blocks, the restart count dropped at every step
def tr(left: Nat, +ctrl: Jpeg.Ctrl, +fr: Jpeg.Frame, +sc: Jpeg.Scan, +ri: U32) -> List<&2, Jpeg.Ctrl>:
  match left:
    case 0n:
      []
    case 1n+pp:
      L1.jpg.pos(ctrl) <> tr(pp, nxt(ctrl, fr, sc, ri), fr, sc, ri)

# ---- A. U32 and Nat facts ----

# U32s of the same value are the same U32
def u32.same(+uu: U32, +vv: U32, en: {U32.to_nat(uu) == U32.to_nat(vv) : Nat}) -> {uu == vv : U32}:
  ueq(uu, vv, Equal.trans(Bool, U32.is_eq(uu, vv), Nat.is_eq(U32.to_nat(vv), U32.to_nat(vv)), True{},
    Equal.trans(Bool, U32.is_eq(uu, vv), Nat.is_eq(U32.to_nat(uu), U32.to_nat(vv)), Nat.is_eq(U32.to_nat(vv),
      U32.to_nat(vv)), u32_eq(uu, vv), Equal.cong(Nat, Bool, kk => Nat.is_eq(kk, U32.to_nat(vv)), U32.to_nat(uu),
      U32.to_nat(vv), en)),
    nat_eq_refl(U32.to_nat(vv))))

# a U32 is_zero calls zero is worth 0
def zero.val(+uu: U32, ez: {True{} == U32.is_zero(uu) : Bool}) -> {U32.to_nat(uu) == 0n : Nat}:
  Equal.cong(U32, Nat, xx => U32.to_nat(xx), uu, 0, ueq(uu, 0, Equal.sym(Bool, True{}, U32.is_zero(uu), ez)))

# a U32 is_eq calls 1 is worth 1
def one.val(+uu: U32, e1: {True{} == U32.is_eq(uu, 1) : Bool}) -> {U32.to_nat(uu) == 1n : Nat}:
  Equal.cong(U32, Nat, xx => U32.to_nat(xx), uu, 1, ueq(uu, 1, Equal.sym(Bool, True{}, U32.is_eq(uu, 1), e1)))

# a U32 neither 0 nor 1 less one is not zero, once is_zero's answer is named
def two.at(
  zz: Bool,
  +uu: U32,
  +ez: {U32.is_zero((uu - 1 : U32)) == zz : Bool},
  +hz: {False{} == U32.is_zero(uu) : Bool},
  +h1: {False{} == U32.is_eq(uu, 1) : Bool}
) -> {U32.is_zero((uu - 1 : U32)) == False{} : Bool}:
  match zz:
    case False{}:
      ez
    case True{}:
      +e0 = {zero.val((uu - 1 : U32), Equal.sym(Bool, U32.is_zero((uu - 1 : U32)), True{}, ez)) :
        {U32.to_nat((uu - 1 : U32)) == 0n : Nat}}
      +e1 = {Equal.trans(Nat, U32.to_nat(uu), 1n+U32.to_nat((uu - 1 : U32)), 1n, u32_dec(uu, Equal.sym(Bool,
        False{}, U32.is_zero(uu), hz)), Equal.cong(Nat, Nat, kk => 1n+kk, U32.to_nat((uu - 1 : U32)), 0n, e0)) :
        {U32.to_nat(uu) == 1n : Nat}}
      Empty.absurd({U32.is_zero((uu - 1 : U32)) == False{} : Bool}, false_true(Equal.trans(Bool, False{},
        U32.is_eq(uu, 1), True{}, h1, Equal.trans(Bool, U32.is_eq(uu, 1), Nat.is_eq(U32.to_nat(uu), 1n), True{},
        u32_eq(uu, 1), Equal.cong(Nat, Bool, kk => Nat.is_eq(kk, 1n), U32.to_nat(uu), 1n, e1)))))

# a U32 neither 0 nor 1, less one, is not zero
def two(
  +uu: U32,
  +hz: {False{} == U32.is_zero(uu) : Bool},
  +h1: {False{} == U32.is_eq(uu, 1) : Bool}
) -> {U32.is_zero((uu - 1 : U32)) == False{} : Bool}:
  two.at(U32.is_zero((uu - 1 : U32)), uu, {==}, hz, h1)

# one more on the left of a sum, one less on the right: the same sum
def shift(
  +aa: Nat,
  +uu: U32,
  +vv: U32,
  +nn: Nat,
  +ev: {U32.to_nat(uu) == 1n+U32.to_nat(vv) : Nat},
  +ee: {Nat.add(aa, U32.to_nat(uu)) == nn : Nat}
) -> {Nat.add(1n+aa, U32.to_nat(vv)) == nn : Nat}:
  Equal.trans(Nat, 1n+Nat.add(aa, U32.to_nat(vv)), Nat.add(aa, U32.to_nat(uu)), nn,
    Equal.trans(Nat, 1n+Nat.add(aa, U32.to_nat(vv)), Nat.add(aa, 1n+U32.to_nat(vv)), Nat.add(aa, U32.to_nat(uu)),
      Equal.sym(Nat, Nat.add(aa, 1n+U32.to_nat(vv)), 1n+Nat.add(aa, U32.to_nat(vv)), ras.add_succ(aa,
        U32.to_nat(vv))),
      Equal.cong(Nat, Nat, kk => Nat.add(aa, kk), 1n+U32.to_nat(vv), U32.to_nat(uu), Equal.sym(Nat, U32.to_nat(uu),
        1n+U32.to_nat(vv), ev))),
    ee)

# the bytes enc.pour writes, in order: its walk without the CRC
def bs(
  xs: List<&2, U32>,
  znew: Bool,
  zlast: Bool,
  +room: U32,
  +left: U32,
  +len: U32,
  +bf: U32
) -> List<&2, U32>:
  match xs znew zlast:
    case Nil{} _z _last:
      []
    case +h <> +t False{} False{}:
      +room2 = (room - 1 : U32)
      h <> bs(t, False{}, U32.is_eq(room2, 1), room2, (left - 1 : U32), len, bf)
    case +h <> +t False{} True{}:
      +left2 = (left - 1 : U32)
      h <> bs(t, True{}, False{}, 0, left2, Png.enc.cap(left2), Png.enc.bf(left2))
    case +h <> t True{} _last:
      +nlen = (len .^. 65535 : U32)
      +left2 = (left - 1 : U32)
      +room2 = (len - 1 : U32)
      bf <> Png.enc.byte(len) <> Png.enc.hi(len) <> Png.enc.byte(nlen) <> Png.enc.hi(nlen) <> h <> bs(t,
        U32.is_zero(room2), U32.is_eq(room2, 1), room2, left2, Png.enc.cap(left2), Png.enc.bf(left2))

# at a block boundary the walk carries the next block's length and BFINAL
def at.edge(+rp: U32, +left: U32, +plen: U32, +pbf: U32) -> Type:
  {U32.is_zero(rp) == True{} : Bool} -> {plen == Png.enc.cap(left) : U32} & {pbf == Png.enc.bf(left) : U32}

# a room that is not zero leaves at.edge nothing to ask
def edge.no(
  +rp: U32,
  +left: U32,
  +plen: U32,
  +pbf: U32,
  +nz: {U32.is_zero(rp) == False{} : Bool}
) -> at.edge(rp, left, plen, pbf):
  ez => Empty.absurd({plen == Png.enc.cap(left) : U32} & {pbf == Png.enc.bf(left) : U32},
    false_true(Equal.trans(Bool, False{}, U32.is_zero(rp), True{}, Equal.sym(Bool, U32.is_zero(rp), False{}, nz),
    ez)))

# k blocks of m bytes hold x bytes with the last block not empty: k is ceil(x / m)
def kok(+xn: Nat, kk: Nat, +mn: Nat) -> Type:
  match kk:
    case 0n:
      {xn == 0n : Nat}
    case 1n+(+kp):
      {Nat.is_lt(Nat.mul(kp, mn), xn) == True{} : Bool} & {Nat.is_le(xn, Nat.mul(1n+kp, mn)) == True{} : Bool}

# n's quotient by m times m, plus the remainder
def dq(+nn: U32, +mx: U32) -> Nat:
  Nat.add(Nat.mul(U32.to_nat(U32.div(nn, mx)), U32.to_nat(mx)), U32.to_nat(U32.mod(nn, mx)))

# ---- G. the wide file, laid out as spec.png ----

# the CRC register and the accumulator after a run of bytes
def fr(+xs: List<&2, U32>, +cc: U32, +acc: List<&2, U32>) -> U32 & List<&2, U32>:
  (Crc.crc.fold(xs, cc), List.reverse.go(&2, U32, xs, acc))

# the zlib stream of stored blocks bb and an Adler-32 sum
def zb(+bb: List<&2, U32>, +sum: U32) -> List<&2, U32>:
  Png.enc.cat([120, 1], Png.enc.cat(bb, Png.enc.be(sum)))

# the IDAT type, the zlib header and the stored blocks
def t0(+bb: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, Png.enc.be(Png.tag.idat()), List.append(&2, U32, [120, 1], bb))

# the file after the IDAT type as the encoder writes it, from t0 on
def gg(+xs: List<&2, U32>, +uu: U32, +ie: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, Png.enc.be(uu), List.append(&2, U32, xs, List.append(&2, U32, Png.enc.be((Crc.crc.fold(xs,
    4294967295) .^. 4294967295 : U32)), ie)))

# ---- H. enc.rgb.go against bs ----

# Adler-32 as enc.rgb.go adds it up, then packed
def afold(xs: List<&2, U32>, +aa: U32, +bb: U32) -> U32:
  match xs:
    case Nil{}:
      ((bb << 16n : U32) .|. aa : U32)
    case +x <> t:
      +a2 = Png.enc.add(aa, x)
      +b2 = Png.enc.add(bb, a2)
      afold(t, a2, b2)

# the walk's hypothesis for the bytes after xb
def step.ty(
  -xb: U32,
  -rr: List<&2, U32>,
  -need: U32,
  -pl: U32,
  -cc: U32,
  -acc: List<&2, U32>,
  -aa: U32,
  -bb: U32,
  -gg: (U32 & List<&2, U32>) & U32
) -> Type:
  @xx: U32 -> @yy: U32 -> at.edge((need - 1 : U32), (pl - 1 : U32), xx, yy) -> {gg == (fr(bs(rr, U32.is_zero((need -
    1 : U32)), U32.is_eq((need - 1 : U32), 1), (need - 1 : U32), (pl - 1 : U32), xx, yy), Crc.crc.byte(cc, xb),
    xb <> acc), afold(rr, Png.enc.add(aa, xb), Png.enc.add(bb, Png.enc.add(aa, xb)))) : (U32 & List<&2, U32>) & U32}

# one raw byte: bs writes it, and the block goes on or closes
def step(
  z1: Bool,
  +xb: U32,
  +rr: List<&2, U32>,
  +need: U32,
  +pl: U32,
  +plen: U32,
  +pbf: U32,
  +cc: U32,
  +acc: List<&2, U32>,
  +aa: U32,
  +bb: U32,
  -gg: (U32 & List<&2, U32>) & U32,
  +ez1: {U32.is_eq(need, 1) == z1 : Bool},
  +nz: {U32.is_zero(need) == False{} : Bool},
  ih: step.ty(xb, rr, need, pl, cc, acc, aa, bb, gg)
) -> {gg == (fr(bs(xb <> rr, False{}, U32.is_eq(need, 1), need, pl, plen, pbf), cc, acc), afold(xb <> rr, aa,
  bb)) : (U32 & List<&2, U32>) & U32}:
  match z1:
    case True{}:
      +n1 = (need - 1 : U32)
      +p1 = (pl - 1 : U32)
      +c1 = Crc.crc.byte(cc, xb)
      +a2 = Png.enc.add(aa, xb)
      +b2 = Png.enc.add(bb, a2)
      +e1 = {one.val(need, Equal.sym(Bool, U32.is_eq(need, 1), True{}, ez1)) : {U32.to_nat(need) == 1n : Nat}}
      +e0 = {u32.same(n1, 0, u32_pred(need, 0n, e1)) : {n1 == 0 : U32}}
      %Equal.sym(Bool, U32.is_eq(need, 1), True{}, ez1) : {gg == (fr(bs(xb <> rr, False{}, _, need, pl, plen, pbf), cc,
        acc), afold(xb <> rr, aa, bb)) : (U32 & List<&2, U32>) & U32}
      Equal.trans((U32 & List<&2, U32>) & U32, gg, (fr(bs(rr, U32.is_zero(n1), U32.is_eq(n1, 1), n1, p1,
        Png.enc.cap(p1), Png.enc.bf(p1)), c1, xb <> acc), afold(rr, a2, b2)), (fr(bs(rr, True{}, False{}, 0, p1,
        Png.enc.cap(p1), Png.enc.bf(p1)), c1, xb <> acc), afold(rr, a2, b2)),
        ih(Png.enc.cap(p1), Png.enc.bf(p1), _ez => ({==}, {==})),
        Equal.cong(U32, (U32 & List<&2, U32>) & U32, uu => (fr(bs(rr, U32.is_zero(uu), U32.is_eq(uu, 1), uu, p1,
          Png.enc.cap(p1), Png.enc.bf(p1)), c1, xb <> acc), afold(rr, a2, b2)), n1, 0, e0))
    case False{}:
      +n1 = (need - 1 : U32)
      +p1 = (pl - 1 : U32)
      +c1 = Crc.crc.byte(cc, xb)
      +a2 = Png.enc.add(aa, xb)
      +b2 = Png.enc.add(bb, a2)
      +nz1 = {two(need, Equal.sym(Bool, U32.is_zero(need), False{}, nz), Equal.sym(Bool, U32.is_eq(need, 1), False{},
        ez1)) : {U32.is_zero(n1) == False{} : Bool}}
      %Equal.sym(Bool, U32.is_eq(need, 1), False{}, ez1) : {gg == (fr(bs(xb <> rr, False{}, _, need, pl, plen, pbf), cc,
        acc), afold(xb <> rr, aa, bb)) : (U32 & List<&2, U32>) & U32}
      Equal.trans((U32 & List<&2, U32>) & U32, gg, (fr(bs(rr, U32.is_zero(n1), U32.is_eq(n1, 1), n1, p1, plen, pbf), c1,
        xb <> acc), afold(rr, a2, b2)), (fr(bs(rr, False{}, U32.is_eq(n1, 1), n1, p1, plen, pbf), c1, xb <> acc),
        afold(rr, a2, b2)),
        ih(plen, pbf, edge.no(n1, p1, plen, pbf, nz1)),
        Equal.cong(Bool, (U32 & List<&2, U32>) & U32, zb => (fr(bs(rr, zb, U32.is_eq(n1, 1), n1, p1, plen, pbf), c1,
          xb <> acc), afold(rr, a2, b2)), U32.is_zero(n1), False{}, nz1))

# the IDAT run's end after ancillary chunks: closed once one follows an IDAT
def dn(cs: List<&2, L3.Anc>, +sid: Bool, done: Bool) -> Bool:
  match cs:
    case Nil{}:
      done
    case _ac <> tl:
      dn(tl, sid, Bool.or(sid, done))

# ---- L. the sizes from 8 w h, and the wide encodings as the one-block layout ----

# p a is at most p b when a is at most b
def ml.le(
  pp: Nat,
  +aa: Nat,
  +bb: Nat,
  +hh: {Nat.is_le(aa, bb) == True{} : Bool}
) -> {Nat.is_le(Nat.mul(pp, aa), Nat.mul(pp, bb)) == True{} : Bool}:
  match pp:
    case 0n:
      {==}
    case 1n+(+qq):
      le_add_both(aa, bb, Nat.mul(qq, aa), Nat.mul(qq, bb), hh, ml.le(qq, aa, bb, hh))

# 5 x below 5 y: x below y
def lt.c5(
  xx: Nat,
  yy: Nat,
  +hh: {Nat.is_lt(Nat.mul(xx, 5n), Nat.mul(yy, 5n)) == True{} : Bool}
) -> {Nat.is_lt(xx, yy) == True{} : Bool}:
  match xx yy:
    case 0n 0n:
      hh
    case 0n 1n+_yp:
      {==}
    case 1n+_xp 0n:
      hh
    case 1n+xp 1n+yp:
      lt.c5(xp, yp, hh)

# (5 p) 5 is 25 p
def m25(pp: Nat) -> {Nat.mul(Nat.mul(pp, 5n), 5n) == Nat.mul(pp, 25n) : Nat}:
  match pp:
    case 0n:
      {==}
    case 1n+(+qq):
      Equal.cong(Nat, Nat, xx => Nat.add(25n, xx), Nat.mul(Nat.mul(qq, 5n), 5n), Nat.mul(qq, 25n), m25(qq))

# 11 + y is at most 3 a when y is at most a and 6 is too
def eleven(
  +yy: Nat,
  +aa: Nat,
  +hy: {Nat.is_le(yy, aa) == True{} : Bool},
  +h6: {Nat.is_le(6n, aa) == True{} : Bool}
) -> {Nat.is_le(11n+yy, Nat.mul(3n, aa)) == True{} : Bool}:
  +a0 = Nat.add(aa, 0n)
  +h6z = {le_rw_r(6n, aa, a0, Equal.sym(Nat, a0, aa, ras.add_zero(aa)), h6) : {Nat.is_le(6n, a0) == True{} : Bool}}
  +h11 = {le_trans(11n, 12n, Nat.add(aa, a0), {==}, le_add_both(6n, aa, 6n, a0, h6, h6z)) : {Nat.is_le(11n,
    Nat.add(aa, a0)) == True{} : Bool}}
  le_rw_l(Nat.add(yy, 11n), 11n+yy, Nat.mul(3n, aa), ras.add_comm(yy, 11n), le_add_both(yy, aa, 11n, Nat.add(aa, a0),
    hy, h11))

# the stored blocks' bytes fit in 8 a: n + 5 k + 6 is at most 8 a when n is at most 5 a, k blocks of m bytes hold
# the n bytes, m is at least 25 and n is above m
def kb(
  kk: Nat,
  +xn: Nat,
  +mn: Nat,
  +aa: Nat,
  hk: kok(xn, kk, mn),
  +h5: {Nat.is_le(xn, Nat.mul(aa, 5n)) == True{} : Bool},
  +hm: {Nat.is_le(25n, mn) == True{} : Bool},
  +hb: {Nat.is_lt(mn, xn) == True{} : Bool}
) -> {Nat.is_le(Nat.add(Nat.add(xn, Nat.mul(kk, 5n)), 6n), Nat.mul(8n, aa)) == True{} : Bool}:
  match kk:
    case 0n:
      Empty.absurd({Nat.is_le(Nat.add(Nat.add(xn, 0n), 6n), Nat.mul(8n, aa)) == True{} : Bool},
        false_true(Equal.trans(Bool, False{}, Nat.is_lt(mn, 0n), True{}, lt_zero_false(mn), lt_rw_r(mn, xn, 0n,
        hk, hb))))
    case 1n+(+kp):
      (hl, _hr) = hk
      +yy = Nat.mul(kp, 5n)
      +x5 = Nat.mul(aa, 5n)
      +y25 = {le_rw_l(Nat.mul(kp, 25n), Nat.mul(yy, 5n), Nat.mul(kp, mn), Equal.sym(Nat, Nat.mul(yy, 5n),
        Nat.mul(kp, 25n), m25(kp)), ml.le(kp, 25n, mn, hm)) : {Nat.is_le(Nat.mul(yy, 5n), Nat.mul(kp, mn)) == True{} :
        Bool}}
      +ya = {lt.c5(yy, aa, le_lt_trans(Nat.mul(yy, 5n), Nat.mul(kp, mn), x5, y25, lt_le_trans(Nat.mul(kp, mn), xn,
        x5, hl, h5))) : {Nat.is_lt(yy, aa) == True{} : Bool}}
      +a5 = {lt.c5(5n, aa, le_lt_trans(25n, mn, x5, hm, lt_le_trans(mn, xn, x5, hb, h5))) : {Nat.is_lt(5n, aa) ==
        True{} : Bool}}
      +h6 = {Equal.trans(Bool, Nat.is_le(6n, aa), Nat.is_lt(5n, aa), True{}, Equal.sym(Bool, Nat.is_lt(5n, aa),
        Nat.is_le(6n, aa), lt_le_succ(5n, aa)), a5) : {Nat.is_le(6n, aa) == True{} : Bool}}
      +h5c = {le_rw_r(xn, x5, Nat.mul(5n, aa), mul_comm(aa, 5n), h5) : {Nat.is_le(xn, Nat.mul(5n, aa)) == True{} :
        Bool}}
      +lhs = Nat.add(Nat.add(xn, 5n+yy), 6n)
      +e1 = {Equal.trans(Nat, lhs, Nat.add(xn, 5n+Nat.add(yy, 6n)), Nat.add(xn, 11n+yy), ras.add_assoc(xn, 5n+yy, 6n),
        Equal.cong(Nat, Nat, zz => Nat.add(xn, Nat.add(5n, zz)), Nat.add(yy, 6n), Nat.add(6n, yy), ras.add_comm(yy,
        6n))) : {lhs == Nat.add(xn, 11n+yy) : Nat}}
      le_rw_r(lhs, Nat.add(Nat.mul(5n, aa), Nat.mul(3n, aa)), Nat.mul(8n, aa), Equal.sym(Nat, Nat.mul(Nat.add(5n, 3n),
        aa), Nat.add(Nat.mul(5n, aa), Nat.mul(3n, aa)), mul_add(5n, 3n, aa)),
        le_rw_l(Nat.add(xn, 11n+yy), lhs, Nat.add(Nat.mul(5n, aa), Nat.mul(3n, aa)), Equal.sym(Nat, lhs,
        Nat.add(xn, 11n+yy), e1), le_add_both(xn, Nat.mul(5n, aa), 11n+yy, Nat.mul(3n, aa), h5c, eleven(yy, aa,
        lt_le(yy, aa, ya), h6))))

# False is never True
def huf.false_true(ee: {False{} == True{} : Bool}) -> Empty:
  %ee : false_ty(_)
  Unit{}

# the first answer of a true also
def also_l(ok: Bool, -rest: Bool, hh: {L2.jpg.also(ok, rest) == True{} : Bool}) -> {ok == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, huf.false_true(hh))

# the second answer of a true also
def also_r(ok: Bool, -rest: Bool, hh: {L2.jpg.also(ok, rest) == True{} : Bool}) -> {rest == True{} : Bool}:
  match ok:
    case True{}:
      hh
    case False{}:
      Empty.absurd({rest == True{} : Bool}, huf.false_true(hh))

# one group of a table: a length, and its codes and symbols in order
type HG is Data:
  HG{len: U32, cs: List<&2, U32>, ys: List<&2, U32>}

# the groups' lengths, one per code
def gl(gs: List<&2, HG>) -> List<&2, U32>:
  match gs:
    case Nil{}:
      []
    case HG{+ln, cs, _y} <> rest:
      List.append(&2, U32, List.replicate(U32, List.length(&2, U32, cs), ln), gl(rest))

# ---- a plane as data ----

# an array's tree as data, so a proof may use it more than once
type Tr is Data:
  TLeaf{value: U32}
  TNode{lo: Tr, hi: Tr}

# the array a tree stands for
def arr(tt: Tr) -> Array<U32>:
  match tt:
    case TLeaf{xx}:
      ALeaf{xx}
    case TNode{lo, hi}:
      ANode{arr(lo), arr(hi)}

# an array and a tree it is the array of
def Of(-aa: Array<U32>) -> Type:
  &tt: Tr -> {aa == arr(tt) : Array<U32>}

# a node's tree from its halves' trees
def of.node(-xs: Array<U32>, -ys: Array<U32>, ox: Of(xs), oy: Of(ys)) -> Of(ANode{xs, ys}):
  (tx, ex) = ox
  (ty, ey) = oy
  sx = Equal.sym(Array<U32>, xs, arr(tx), ex)
  sy = Equal.sym(Array<U32>, ys, arr(ty), ey)
  %sx : Of(ANode{_, ys})
  %sy : Of(ANode{arr(tx), _})
  (TNode{tx, ty}, {==})

# every array is the array of a tree
def of(aa: Array<U32>) -> Of(aa):
  match aa:
    case ALeaf{+xx}:
      (TLeaf{xx}, {==})
    case ANode{xs, ys}:
      of.node(xs, ys, of(xs), of(ys))

# the size Array.size reads: the leftmost path, doubled at each node
def size(tt: Tr) -> U32:
  match tt:
    case TLeaf{_xx}:
      1
    case TNode{lo, _hi}:
      U32.shl(size(lo))

# the value Array.get.go finds, the tree walked as it walks the array
def get(tt: Tr, +nn: U32, +ii: U32) -> U32:
  match tt:
    case TLeaf{xx}:
      xx
    case TNode{lo, hi}:
      +hh = U32.shr(nn)
      +gl = get(lo, hh, ii)
      +gh = get(hi, hh, U32.sub(ii, hh))
      Bool.pick(U32, U32.is_lt(ii, hh), gl, gh)

# the node a write leaves: the low half written, or the high half
def put.if(zz: Bool, +lo: Tr, +hi: Tr, +pl: Tr, +ph: Tr) -> Tr:
  match zz:
    case True{}:
      TNode{pl, hi}
    case False{}:
      TNode{lo, ph}

# the tree Array.swap.go leaves, walked as it walks the array
def put(+tt: Tr, +nn: U32, +ii: U32, +vv: U32) -> Tr:
  match tt:
    case TLeaf{_xx}:
      TLeaf{vv}
    case TNode{lo, hi}:
      +hh = U32.shr(nn)
      put.if(U32.is_lt(ii, hh), lo, hi, put(lo, hh, ii, vv), put(hi, hh, U32.sub(ii, hh), vv))

# the index Array.get and Array.set walk to: the index masked by the size less one
def mask(+ii: U32, +nn: U32) -> U32:
  U32.and(ii, U32.sub(nn, 1))

# the tree Array.set leaves: put at the masked index
def set(+tt: Tr, +ii: U32, +vv: U32) -> Tr:
  put(tt, size(tt), mask(ii, size(tt)), vv)

# both walks go the same way: on to the next level, or they part
def same.if(zi: Bool, zj: Bool, next: Bool) -> Bool:
  match zi zj:
    case True{} True{}:
      next
    case False{} False{}:
      next
    case True{} False{}:
      False{}
    case False{} True{}:
      False{}

# whether the walks of two indices down a perfect tree of 2^d leaves, the root's size nn, end at one leaf
def same(dd: Nat, +nn: U32, +ii: U32, +jj: U32) -> Bool:
  match dd:
    case 0n:
      True{}
    case 1n+ee:
      +hh = U32.shr(nn)
      same.if(U32.is_lt(ii, hh), U32.is_lt(jj, hh), same(ee, hh, Bool.pick(U32, U32.is_lt(ii, hh), ii, U32.sub(ii,
        hh)), Bool.pick(U32, U32.is_lt(jj, hh), jj, U32.sub(jj, hh))))

# the value a read finds after a write: the written value when both walks end at one leaf, else the old one
def after(+ok: Bool, +vv: U32, +old: U32) -> U32:
  Bool.pick(U32, ok, vv, old)

# ---- powers of two ----

# the double of a number above zero is above one
def dbl_pos(+xx: Nat, hh: {Nat.is_lt(0n, xx) == True{} : Bool}) -> {Nat.is_lt(1n, Nat.double(xx)) == True{} : Bool}:
  match xx:
    case 0n:
      Empty.absurd({Nat.is_lt(1n, 0n) == True{} : Bool}, false_true(hh))
    case 1n+_pp:
      {==}

# doubling keeps an order
def dbl_lt(
  +xx: Nat,
  +yy: Nat,
  hh: {Nat.is_lt(xx, yy) == True{} : Bool}
) -> {Nat.is_lt(Nat.double(xx), Nat.double(yy)) == True{} : Bool}:
  match xx yy:
    case _xx 0n:
      Empty.absurd({Nat.is_lt(Nat.double(xx), 0n) == True{} : Bool}, false_true(Equal.trans(Bool, False{},
        Nat.is_lt(xx, 0n), True{}, lt_zero_false(xx), hh)))
    case 0n 1n+_qq:
      {==}
    case 1n+pp 1n+qq:
      dbl_lt(pp, qq, hh)

# two to any power is above zero
def pow_pos(+pp: Nat) -> {Nat.is_lt(0n, Nat.pow(2n, pp)) == True{} : Bool}:
  match pp:
    case 0n:
      {==}
    case 1n+qq:
      lt_rw_r(0n, Nat.double(Nat.pow(2n, qq)), Nat.pow(2n, 1n+qq), Equal.sym(Nat, Nat.pow(2n, 1n+qq),
        Nat.double(Nat.pow(2n, qq)), pow2_succ(qq)), lt_le_trans(0n, 1n, Nat.double(Nat.pow(2n, qq)), {==},
        lt_le(1n, Nat.double(Nat.pow(2n, qq)), dbl_pos(Nat.pow(2n, qq), pow_pos(qq)))))

# ---- U32 halving ----

# padding a zero on top keeps a word's number
def pad_nat(+pp: Nat, +tt: Word(pp)) -> {Word.to_nat(1n+pp, Word.shr.pad(pp, tt)) == Word.to_nat(pp, tt) : Nat}:
  match pp:
    case 0n:
      match tt:
        case WNil{}:
          {==}
    case 1n+qq:
      match tt:
        case WCon{+bb, +rest}:
          match bb:
            case False{}:
              Equal.cong(Nat, Nat, nn => Nat.double(nn), Word.to_nat(1n+qq, Word.shr.pad(qq, rest)), Word.to_nat(qq,
                rest), pad_nat(qq, rest))
            case True{}:
              Equal.cong(Nat, Nat, nn => 1n+Nat.double(nn), Word.to_nat(1n+qq, Word.shr.pad(qq, rest)),
                Word.to_nat(qq, rest), pad_nat(qq, rest))

# ---- Array.get after Array.set, on the tree ----

# the value Array.get finds in a tree's array
def at(+tt: Tr, +jj: U32) -> U32:
  get(tt, size(tt), mask(jj, size(tt)))

# ---- the plane's depth ----

# a U32's lowest bit
def lowb(uu: U32) -> Bool:
  match uu:
    case U32{ww}:
      match ww:
        case WCon{bb, _tt}:
          bb

# a U32 is its lowest bit plus twice its shr
def shr_split(+uu: U32) -> {U32.to_nat(uu) == Nat.add(bit(lowb(uu)), Nat.double(U32.to_nat(U32.shr(uu)))) : Nat}:
  match uu:
    case U32{+ww}:
      match ww:
        case WCon{+bb, +tt}:
          Equal.trans(Nat, Word.to_nat(32n, WCon{bb, tt}), Nat.add(bit(bb), Nat.double(Word.to_nat(31n, tt))),
            Nat.add(bit(bb), Nat.double(Word.to_nat(32n, Word.shr.pad(31n, tt)))), to_nat_con(31n, bb, tt),
            Equal.cong(Nat, Nat, nn => Nat.add(bit(bb), Nat.double(nn)), Word.to_nat(31n, tt), Word.to_nat(32n,
            Word.shr.pad(31n, tt)), Equal.sym(Nat, Word.to_nat(32n, Word.shr.pad(31n, tt)), Word.to_nat(31n, tt),
            pad_nat(31n, tt))))

# doubling keeps an order, at most
def dbl_le(
  +xx: Nat,
  +yy: Nat,
  +hh: {Nat.is_le(xx, yy) == True{} : Bool}
) -> {Nat.is_le(Nat.double(xx), Nat.double(yy)) == True{} : Bool}:
  match xx yy:
    case 0n _yy:
      le_zero(Nat.double(yy))
    case 1n+_pp 0n:
      Empty.absurd({Nat.is_le(Nat.double(xx), 0n) == True{} : Bool}, false_true(hh))
    case 1n+pp 1n+qq:
      dbl_le(pp, qq, hh)

# two to a power at most another is at most two to it
def pow_le(
  +aa: Nat,
  +bb: Nat,
  +hh: {Nat.is_le(aa, bb) == True{} : Bool}
) -> {Nat.is_le(Nat.pow(2n, aa), Nat.pow(2n, bb)) == True{} : Bool}:
  match aa bb:
    case 0n _bb:
      Equal.trans(Bool, Nat.is_le(1n, Nat.pow(2n, bb)), Nat.is_lt(0n, Nat.pow(2n, bb)), True{}, Equal.sym(Bool,
        Nat.is_lt(0n, Nat.pow(2n, bb)), Nat.is_le(1n, Nat.pow(2n, bb)), lt_le_succ(0n, Nat.pow(2n, bb))), pow_pos(bb))
    case 1n+_pp 0n:
      Empty.absurd({Nat.is_le(Nat.pow(2n, aa), 1n) == True{} : Bool}, false_true(hh))
    case 1n+pp 1n+qq:
      le_rw_l(Nat.double(Nat.pow(2n, pp)), Nat.pow(2n, 1n+pp), Nat.pow(2n, 1n+qq), Equal.sym(Nat, Nat.pow(2n, 1n+pp),
        Nat.double(Nat.pow(2n, pp)), pow2_succ(pp)), le_rw_r(Nat.double(Nat.pow(2n, pp)), Nat.double(Nat.pow(2n,
        qq)), Nat.pow(2n, 1n+qq), Equal.sym(Nat, Nat.pow(2n, 1n+qq), Nat.double(Nat.pow(2n, qq)), pow2_succ(qq)),
        dbl_le(Nat.pow(2n, pp), Nat.pow(2n, qq), pow_le(pp, qq, hh))))

# shifting a word left doubles it, when it is below 2^e and e is at most p
def shl_ok(
  +pp: Nat,
  +ww: Word(1n+pp),
  +ee: Nat,
  +h1: {Nat.is_lt(Word.to_nat(1n+pp, ww), Nat.pow(2n, ee)) == True{} : Bool},
  +h2: {Nat.is_le(ee, pp) == True{} : Bool}
) -> {Word.to_nat(1n+pp, Word.shl(1n+pp, ww)) == Nat.double(Word.to_nat(1n+pp, ww)) : Nat}:
  match ww:
    case WCon{+bb, +tt}:
      +xn = Nat.add(bit(bb), Nat.double(Word.to_nat(pp, tt)))
      +hx = {lt_le_trans(xn, Nat.pow(2n, ee), Nat.pow(2n, pp), lt_rw_l(Word.to_nat(1n+pp, WCon{bb, tt}), xn,
        Nat.pow(2n, ee), to_nat_con(pp, bb, tt), h1), pow_le(ee, pp, h2)) : {Nat.is_lt(xn, Nat.pow(2n,
        pp)) == True{} :
        Bool}}
      Equal.trans(Nat, Nat.double(Word.to_nat(pp, Word.shl.put(pp, bb, tt))), Nat.double(xn),
        Nat.double(Word.to_nat(1n+pp, WCon{bb, tt})), Equal.cong(Nat, Nat, nn => Nat.double(nn), Word.to_nat(pp,
        Word.shl.put(pp, bb, tt)), xn, shl_put_nat(pp, bb, tt, hx)), Equal.cong(Nat, Nat, nn => Nat.double(nn), xn,
        Word.to_nat(1n+pp, WCon{bb, tt}), Equal.sym(Nat, Word.to_nat(1n+pp, WCon{bb, tt}), xn, to_nat_con(pp, bb,
        tt))))

# U32 shl doubles a number below 2^e, e at most 31
def shl_u(
  +uu: U32,
  +ee: Nat,
  +h1: {Nat.is_lt(U32.to_nat(uu), Nat.pow(2n, ee)) == True{} : Bool},
  +h2: {Nat.is_le(ee, 31n) == True{} : Bool}
) -> {U32.to_nat(U32.shl(uu)) == Nat.double(U32.to_nat(uu)) : Nat}:
  match uu:
    case U32{+ww}:
      shl_ok(31n, ww, ee, h1, h2)

# a number above zero is below its double
def lt_dbl(+xx: Nat, +hh: {Nat.is_lt(0n, xx) == True{} : Bool}) -> {Nat.is_lt(xx, Nat.double(xx)) == True{} : Bool}:
  lt_rw_l(Nat.add(xx, 0n), xx, Nat.double(xx), ras.add_zero(xx), lt_rw_r(Nat.add(xx, 0n), Nat.add(xx, xx),
    Nat.double(xx), Equal.sym(Nat, Nat.double(xx), Nat.add(xx, xx), double_add(xx)), lt_add_mono(xx, 0n, xx, hh)))

# one more than twice a number below yy is below twice yy
def lt_bd1(
  +xx: Nat,
  +yy: Nat,
  +hh: {Nat.is_lt(xx, yy) == True{} : Bool}
) -> {Nat.is_lt(1n+Nat.double(xx), Nat.double(yy)) == True{} : Bool}:
  match xx yy:
    case _xx 0n:
      Empty.absurd({Nat.is_lt(1n+Nat.double(xx), 0n) == True{} : Bool}, false_true(Equal.trans(Bool, False{},
        Nat.is_lt(xx, 0n), True{}, lt_zero_false(xx), hh)))
    case 0n 1n+_qq:
      {==}
    case 1n+pp 1n+qq:
      lt_bd1(pp, qq, hh)

# the bit a U32 shr drops, plus twice a number below yy, is below twice yy
def lt_bd(
  +cc: Bool,
  +xx: Nat,
  +yy: Nat,
  +hh: {Nat.is_lt(xx, yy) == True{} : Bool}
) -> {Nat.is_lt(Nat.add(bit(cc), Nat.double(xx)), Nat.double(yy)) == True{} : Bool}:
  match cc:
    case False{}:
      dbl_lt(xx, yy, hh)
    case True{}:
      lt_bd1(xx, yy, hh)

# a U32 shifted right s times below 2^c: the U32 is below 2^(s + c)
def shrn_up(
  +ss: Nat,
  +uu: U32,
  +cc: Nat,
  +hh: {Nat.is_lt(U32.to_nat(U32.shrn(uu, ss)), Nat.pow(2n, cc)) == True{} : Bool}
) -> {Nat.is_lt(U32.to_nat(uu), Nat.pow(2n, Nat.add(ss, cc))) == True{} : Bool}:
  match ss:
    case 0n:
      hh
    case 1n+qq:
      +vv = U32.shrn(uu, qq)
      +sv = Nat.add(bit(lowb(vv)), Nat.double(U32.to_nat(U32.shr(vv))))
      +h1 = {lt_rw_l(sv, U32.to_nat(vv), Nat.pow(2n, 1n+cc), Equal.sym(Nat, U32.to_nat(vv), sv, shr_split(vv)),
        lt_rw_r(sv, Nat.double(Nat.pow(2n, cc)), Nat.pow(2n, 1n+cc), Equal.sym(Nat, Nat.pow(2n, 1n+cc),
        Nat.double(Nat.pow(2n, cc)), pow2_succ(cc)), lt_bd(lowb(vv), U32.to_nat(U32.shr(vv)), Nat.pow(2n, cc),
        hh))) : {Nat.is_lt(U32.to_nat(vv), Nat.pow(2n, 1n+cc)) == True{} : Bool}}
      lt_rw_r(U32.to_nat(uu), Nat.pow(2n, Nat.add(qq, 1n+cc)), Nat.pow(2n, 1n+Nat.add(qq, cc)), Equal.cong(Nat, Nat,
        xx => Nat.pow(2n, xx), Nat.add(qq, 1n+cc), 1n+Nat.add(qq, cc), ras.add_succ(qq, cc)), shrn_up(qq, uu, 1n+cc,
            h1))

# a U32 below 2^(s + c), shifted right s times, is below 2^c
def shrn_dn(
  +ss: Nat,
  +uu: U32,
  +cc: Nat,
  +hh: {Nat.is_lt(U32.to_nat(uu), Nat.pow(2n, Nat.add(ss, cc))) == True{} : Bool}
) -> {Nat.is_lt(U32.to_nat(U32.shrn(uu, ss)), Nat.pow(2n, cc)) == True{} : Bool}:
  match ss:
    case 0n:
      hh
    case 1n+qq:
      +vv = U32.shrn(uu, qq)
      +sv = Nat.add(bit(lowb(vv)), Nat.double(U32.to_nat(U32.shr(vv))))
      +h0 = {lt_rw_r(U32.to_nat(uu), Nat.pow(2n, 1n+Nat.add(qq, cc)), Nat.pow(2n, Nat.add(qq, 1n+cc)), Equal.cong(Nat,
        Nat, xx => Nat.pow(2n, xx), 1n+Nat.add(qq, cc), Nat.add(qq, 1n+cc), Equal.sym(Nat, Nat.add(qq, 1n+cc),
        1n+Nat.add(qq, cc), ras.add_succ(qq, cc))), hh) : {Nat.is_lt(U32.to_nat(uu), Nat.pow(2n, Nat.add(qq, 1n+cc))) ==
        True{} : Bool}}
      +h1 = {shrn_dn(qq, uu, 1n+cc, h0) : {Nat.is_lt(U32.to_nat(vv), Nat.pow(2n, 1n+cc)) == True{} : Bool}}
      lt_half(lowb(vv), U32.to_nat(U32.shr(vv)), Nat.pow(2n, cc), lt_rw_r(sv, Nat.pow(2n, 1n+cc),
        Nat.double(Nat.pow(2n, cc)), pow2_succ(cc), lt_rw_l(U32.to_nat(vv), sv, Nat.pow(2n, 1n+cc), shr_split(vv),
        h1)))

# a Bool whose not is false is true
def not_false(+bb: Bool, +hh: {Bool.not(bb) == False{} : Bool}) -> {bb == True{} : Bool}:
  match bb:
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, false_true(Equal.sym(Bool, True{}, False{}, hh)))
    case True{}:
      {==}

# a U32 equal to zero is below one
def eq_zero(+xx: U32, +hh: {U32.is_ne(xx, 0) == False{} : Bool}) -> {Nat.is_lt(U32.to_nat(xx), 1n) == True{} : Bool}:
  +he = {Equal.trans(Bool, Bool.not(Nat.is_eq(U32.to_nat(xx), 0n)), Bool.not(U32.is_eq(xx, 0)), False{},
    Equal.cong(Bool, Bool, bb => Bool.not(bb), Nat.is_eq(U32.to_nat(xx), 0n), U32.is_eq(xx, 0), Equal.sym(Bool,
    U32.is_eq(xx, 0), Nat.is_eq(U32.to_nat(xx), 0n), u32_eq(xx, 0))), hh) : {Bool.not(Nat.is_eq(U32.to_nat(xx), 0n))
    == False{} : Bool}}
  lt_rw_l(0n, U32.to_nat(xx), 1n, Equal.sym(Nat, U32.to_nat(xx), 0n, ras.nat_eq_true(U32.to_nat(xx), 0n, not_false(
    Nat.is_eq(U32.to_nat(xx), 0n), he))), {==})

# the log2 walk's step width at step p
def sw(+pp: Nat) -> Nat:
  U32.to_nat(U32.shln(1, pp))

# a number times one
def mul_one(+ss: Nat) -> {Nat.mul(ss, 1n) == ss : Nat}:
  Equal.trans(Nat, Nat.mul(ss, 1n), Nat.mul(1n, ss), ss, mul_comm(ss, 1n), ras.add_zero(ss))

# the width the log2 walk's step shifts by: the step width when the shifted number is not zero, else none
def mul_pick(+ss: Nat, zz: Bool) -> {Nat.mul(ss, U32.to_nat(Bool.to_u32(zz))) == Bool.pick(Nat, zz, ss, 0n) : Nat}:
  match zz:
    case True{}:
      mul_one(ss)
    case False{}:
      mul_zero(ss)

# the shift the log2 walk's step takes
def sp(+pp: Nat, +nn: U32) -> Nat:
  Bool.pick(Nat, U32.is_ne(U32.shrn(nn, sw(pp)), 0), sw(pp), 0n)

# a step of the log2 walk: shift by the step width, and count it, when the shifted number is not zero
def go_z(
  +pp: Nat,
  +nn: U32,
  +bb: Nat
) -> {U32.log2.go(1n+pp, nn, bb) == U32.log2.go(pp, U32.shrn(nn, sp(pp, nn)), Nat.add(bb, sp(pp, nn))) : Nat}:
  Equal.cong(Nat, Nat, xx => U32.log2.go(pp, U32.shrn(nn, xx), Nat.add(bb, xx)), Nat.mul(sw(pp),
    U32.to_nat(Bool.to_u32(U32.is_ne(U32.shrn(nn, sw(pp)), 0)))), sp(pp, nn), mul_pick(sw(pp),
    U32.is_ne(U32.shrn(nn, sw(pp)), 0)))

# the log2 walk adds its count to the count it starts from
def go_add(+kk: Nat, +nn: U32, +bb: Nat) -> {U32.log2.go(kk, nn, bb) == Nat.add(bb, U32.log2.go(kk, nn, 0n)) : Nat}:
  match kk:
    case 0n:
      Equal.sym(Nat, Nat.add(bb, 0n), bb, ras.add_zero(bb))
    case 1n+pp:
      +tt = sp(pp, nn)
      +n1 = U32.shrn(nn, tt)
      +g0 = U32.log2.go(pp, n1, 0n)
      +e1 = {Equal.trans(Nat, U32.log2.go(1n+pp, nn, bb), U32.log2.go(pp, n1, Nat.add(bb, tt)), Nat.add(Nat.add(bb, tt),
        g0), go_z(pp, nn, bb), go_add(pp, n1, Nat.add(bb, tt))) : {U32.log2.go(1n+pp, nn, bb) == Nat.add(Nat.add(bb,
        tt), g0) : Nat}}
      +e2 = {Equal.trans(Nat, U32.log2.go(1n+pp, nn, 0n), U32.log2.go(pp, n1, tt), Nat.add(tt, g0), go_z(pp, nn, 0n),
        go_add(pp, n1, tt)) : {U32.log2.go(1n+pp, nn, 0n) == Nat.add(tt, g0) : Nat}}
      +g1 = U32.log2.go(1n+pp, nn, 0n)
      Equal.trans(Nat, U32.log2.go(1n+pp, nn, bb), Nat.add(Nat.add(bb, tt), g0), Nat.add(bb, g1), e1, Equal.trans(Nat,
        Nat.add(Nat.add(bb, tt), g0), Nat.add(bb, Nat.add(tt, g0)), Nat.add(bb, g1), ras.add_assoc(bb, tt, g0),
        Equal.cong(Nat, Nat, xx => Nat.add(bb, xx), Nat.add(tt, g0), g1, Equal.sym(Nat, g1, Nat.add(tt, g0), e2))))

# the step width at step p is 2^p, p at most 31
def sw_pow(+pp: Nat, +hp: {Nat.is_le(pp, 31n) == True{} : Bool}) -> {sw(pp) == Nat.pow(2n, pp) : Nat}:
  match pp:
    case 0n:
      {==}
    case 1n+qq:
      +ih = {sw_pow(qq, le_trans(qq, 30n, 31n, hp, {==})) : {sw(qq) == Nat.pow(2n, qq) : Nat}}
      +pw = Nat.pow(2n, qq)
      +h1 = {lt_rw_l(pw, sw(qq), Nat.pow(2n, 1n+qq), Equal.sym(Nat, sw(qq), pw, ih), lt_rw_r(pw, Nat.double(pw),
        Nat.pow(2n, 1n+qq), Equal.sym(Nat, Nat.pow(2n, 1n+qq), Nat.double(pw), pow2_succ(qq)), lt_dbl(pw,
        pow_pos(qq)))) : {Nat.is_lt(sw(qq), Nat.pow(2n, 1n+qq)) == True{} : Bool}}
      Equal.trans(Nat, U32.to_nat(U32.shl(U32.shln(1, qq))), Nat.double(sw(qq)), Nat.pow(2n, 1n+qq), shl_u(U32.shln(1,
        qq), 1n+qq, h1, hp), Equal.trans(Nat, Nat.double(sw(qq)), Nat.double(pw), Nat.pow(2n, 1n+qq), Equal.cong(Nat,
        Nat, xx => Nat.double(xx), sw(qq), pw, ih), Equal.sym(Nat, Nat.pow(2n, 1n+qq), Nat.double(pw),
        pow2_succ(qq))))

# the bound the log2 walk's next step needs, for the lower bound: below 2^(the step width) after the shift
def lo_hyp(
  zz: Bool,
  +pp: Nat,
  +ee: Nat,
  +nn: U32,
  +ez: {U32.is_ne(U32.shrn(nn, sw(pp)), 0) == zz : Bool},
  +hp: {Nat.is_le(pp, 31n) == True{} : Bool},
  +he: {Nat.is_le(ee, Nat.pow(2n, 1n+pp)) == True{} : Bool},
  +hn: {Nat.is_lt(U32.to_nat(nn), Nat.pow(2n, ee)) == True{} : Bool}
) -> {Nat.is_lt(U32.to_nat(U32.shrn(nn, Bool.pick(Nat, zz, sw(pp), 0n))), Nat.pow(2n, sw(pp))) == True{} : Bool}:
  match zz:
    case False{}:
      +ss = sw(pp)
      lt_rw_r(U32.to_nat(nn), Nat.pow(2n, Nat.add(ss, 0n)), Nat.pow(2n, ss), Equal.cong(Nat, Nat, xx => Nat.pow(2n,
        xx), Nat.add(ss, 0n), ss, ras.add_zero(ss)), shrn_up(ss, nn, 0n, eq_zero(U32.shrn(nn, ss), ez)))
    case True{}:
      +ss = sw(pp)
      +es = {Equal.trans(Nat, Nat.pow(2n, 1n+pp), Nat.double(ss), Nat.add(ss, ss), Equal.trans(Nat, Nat.pow(2n, 1n+pp),
        Nat.double(Nat.pow(2n, pp)), Nat.double(ss), pow2_succ(pp), Equal.cong(Nat, Nat, xx => Nat.double(xx),
        Nat.pow(2n, pp), ss, Equal.sym(Nat, ss, Nat.pow(2n, pp), sw_pow(pp, hp)))), double_add(ss)) :
        {Nat.pow(2n, 1n+pp) == Nat.add(ss, ss) : Nat}}
      shrn_dn(ss, nn, ss, lt_le_trans(U32.to_nat(nn), Nat.pow(2n, ee), Nat.pow(2n, Nat.add(ss, ss)), hn, pow_le(ee,
        Nat.add(ss, ss), le_rw_r(ee, Nat.pow(2n, 1n+pp), Nat.add(ss, ss), es, he))))

# the number the log2 walk's step leaves, zz saying whether it shifts
def nx(zz: Bool, +pp: Nat, +nn: U32) -> U32:
  U32.shrn(nn, Bool.pick(Nat, zz, sw(pp), 0n))

# the bound after the log2 walk's step gives the bound before it
def lo_fin(
  zz: Bool,
  +pp: Nat,
  +nn: U32,
  +ih: {Nat.is_lt(U32.to_nat(nx(zz, pp, nn)), Nat.pow(2n, 1n+U32.log2.go(pp, nx(zz, pp, nn), 0n))) == True{} : Bool}
) -> {Nat.is_lt(U32.to_nat(nn), Nat.pow(2n, 1n+Nat.add(Bool.pick(Nat, zz, sw(pp), 0n), U32.log2.go(pp, nx(zz, pp,
  nn), 0n)))) == True{} : Bool}:
  match zz:
    case False{}:
      ih
    case True{}:
      +ss = sw(pp)
      +gg = U32.log2.go(pp, U32.shrn(nn, ss), 0n)
      lt_rw_r(U32.to_nat(nn), Nat.pow(2n, Nat.add(ss, 1n+gg)), Nat.pow(2n, 1n+Nat.add(ss, gg)), Equal.cong(Nat, Nat,
        xx => Nat.pow(2n, xx), Nat.add(ss, 1n+gg), 1n+Nat.add(ss, gg), ras.add_succ(ss, gg)), shrn_up(ss, nn, 1n+gg,
            ih))

# a number below 2^e, e at most 2^k, is below 2^(1 + the count of k steps of the log2 walk), k at most 5
def lo(
  +kk: Nat,
  +ee: Nat,
  +nn: U32,
  +hk: {Nat.is_le(kk, 5n) == True{} : Bool},
  +he: {Nat.is_le(ee, Nat.pow(2n, kk)) == True{} : Bool},
  +hn: {Nat.is_lt(U32.to_nat(nn), Nat.pow(2n, ee)) == True{} : Bool}
) -> {Nat.is_lt(U32.to_nat(nn), Nat.pow(2n, 1n+U32.log2.go(kk, nn, 0n))) == True{} : Bool}:
  match kk:
    case 0n:
      lt_le_trans(U32.to_nat(nn), Nat.pow(2n, ee), Nat.pow(2n, 1n), hn, pow_le(ee, 1n, he))
    case 1n+pp:
      +zz = U32.is_ne(U32.shrn(nn, sw(pp)), 0)
      +tt = sp(pp, nn)
      +n1 = U32.shrn(nn, tt)
      +g0 = U32.log2.go(pp, n1, 0n)
      +hp = {le_trans(pp, 4n, 31n, hk, {==}) : {Nat.is_le(pp, 31n) == True{} : Bool}}
      +ih = {lo(pp, sw(pp), n1, le_trans(pp, 4n, 5n, hk, {==}), le_rw_r(sw(pp), sw(pp), Nat.pow(2n, pp), sw_pow(pp,
        hp), le_refl(sw(pp))), lo_hyp(zz, pp, ee, nn, {==}, hp, he, hn)) : {Nat.is_lt(U32.to_nat(n1), Nat.pow(2n,
        1n+g0)) == True{} : Bool}}
      +eg = {Equal.trans(Nat, U32.log2.go(1n+pp, nn, 0n), U32.log2.go(pp, n1, tt), Nat.add(tt, g0), go_z(pp, nn, 0n),
        go_add(pp, n1, tt)) : {U32.log2.go(1n+pp, nn, 0n) == Nat.add(tt, g0) : Nat}}
      lt_rw_r(U32.to_nat(nn), Nat.pow(2n, 1n+Nat.add(tt, g0)), Nat.pow(2n, 1n+U32.log2.go(1n+pp, nn, 0n)),
        Equal.cong(Nat, Nat, xx => Nat.pow(2n, 1n+xx), Nat.add(tt, g0), U32.log2.go(1n+pp, nn, 0n), Equal.sym(Nat,
        U32.log2.go(1n+pp, nn, 0n), Nat.add(tt, g0), eg)), lo_fin(zz, pp, nn, ih))

# ---- a new plane ----

# the tree of 2^d leaves, every one v
def full(+dd: Nat, +vv: U32) -> Tr:
  match dd:
    case 0n:
      TLeaf{vv}
    case 1n+ee:
      TNode{full(ee, vv), full(ee, vv)}

# the AC symbol of run nibble qq and size cc
def acsym(+qq: U32, +cc: U32) -> U32:
  U32.or(cc, U32.shln(qq, 4n))

# the facts the decoder needs of the AC symbol of nibble qq and size cc: in the table, not EOB or ZRL, its size and
# its run read back
def symok(+qq: U32, +cc: U32) -> Bool:
  +sy = acsym(qq, cc)
  Bool.and(L2.jpg.memb(sy, Jenc.encode.acsyms()), Bool.and(Bool.not(U32.is_eq(sy, 0)), Bool.and(Bool.not(U32.is_eq(sy,
    240)), Bool.and(U32.is_eq(U32.and(15, sy), cc), U32.is_eq(U32.shrn(sy, 4n), qq)))))

# the facts for nibble qq and every size of a list
def allc(+qq: U32, cs: List<&2, U32>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case +cc <> rest:
      L2.jpg.also(symok(qq, cc), allc(qq, rest))

# the rest of the sizes, as a size's membership step needs it
def IncIh(+_qq: U32, +_cc: U32, -rest: List<&2, U32>) -> Type:
  @hr: {L2.jpg.memb(_cc, rest) == True{} : Bool} -> @ha: {allc(_qq, rest) == True{} : Bool} -> {symok(_qq,
    _cc) == True{} :
    Bool}

# a size of the list, by whether it is the list's first
def inc.b(
  eq: Bool,
  +qq: U32,
  +cc: U32,
  +xx: U32,
  +rest: List<&2, U32>,
  he: {U32.is_eq(cc, xx) == eq : Bool},
  hin: {L2.jpg.eith(eq, L2.jpg.memb(cc, rest)) == True{} : Bool},
  hall: {L2.jpg.also(symok(qq, xx), allc(qq, rest)) == True{} : Bool},
  ih: IncIh(qq, cc, rest)
) -> {symok(qq, cc) == True{} : Bool}:
  match eq:
    case True{}:
      es = Equal.sym(U32, cc, xx, ueq(cc, xx, he))
      %es : {symok(qq, _) == True{} : Bool}
      also_l(symok(qq, xx), allc(qq, rest), hall)
    case False{}:
      ih(hin, also_r(symok(qq, xx), allc(qq, rest), hall))

# a size of a list whose sizes all have the facts has them
def inc(
  cs: List<&2, U32>,
  +qq: U32,
  +cc: U32,
  hin: {L2.jpg.memb(cc, cs) == True{} : Bool},
  hall: {allc(qq, cs) == True{} : Bool}
) -> {symok(qq, cc) == True{} : Bool}:
  match cs:
    case Nil{}:
      Empty.absurd({symok(qq, cc) == True{} : Bool}, huf.false_true(hin))
    case +xx <> +rest:
      inc.b(U32.is_eq(cc, xx), qq, cc, xx, rest, {==}, hin, hall, hr => ha => inc(rest, qq, cc, hr, ha))

# sixteen times a number
def sixteen(nn: Nat) -> Nat:
  Nat.double(Nat.double(Nat.double(Nat.double(nn))))

# a word shifted down keeps its number: the new top bit is clear
def jenc.pad_nat(nn: Nat, ww: Word(nn)) -> {Word.to_nat(1n+nn, Word.shr.pad(nn, ww)) == Word.to_nat(nn, ww) : Nat}:
  match nn:
    case 0n:
      {==}
    case 1n+ +pp:
      match ww:
        case WCon{False{}, tt}:
          Equal.cong(Nat, Nat, xx => Nat.double(xx), Word.to_nat(1n+pp, Word.shr.pad(pp, tt)), Word.to_nat(pp, tt),
            jenc.pad_nat(pp, tt))
        case WCon{True{}, tt}:
          Equal.cong(Nat, Nat, xx => 1n+Nat.double(xx), Word.to_nat(1n+pp, Word.shr.pad(pp, tt)), Word.to_nat(pp, tt),
            jenc.pad_nat(pp, tt))

# one more low bit on two words whose numbers differ by cc: they differ by twice cc
def nstep(
  bb: Bool,
  +pp: Nat,
  +tt: Word(pp),
  +uu: Word(pp),
  +cc: Nat,
  ee: {Word.to_nat(pp, tt) == Nat.add(Word.to_nat(pp, uu), cc) : Nat}
) -> {Word.to_nat(1n+pp, WCon{bb, tt}) == Nat.add(Word.to_nat(1n+pp, WCon{bb, uu}), Nat.double(cc)) : Nat}:
  match bb:
    case False{}:
      +un = Word.to_nat(pp, uu)
      Equal.trans(Nat, Nat.double(Word.to_nat(pp, tt)), Nat.double(Nat.add(un, cc)), Nat.add(Nat.double(un),
        Nat.double(cc)), Equal.cong(Nat, Nat, xx => Nat.double(xx), Word.to_nat(pp, tt), Nat.add(un, cc), ee),
        double_dist(un, cc))
    case True{}:
      +un = Word.to_nat(pp, uu)
      Equal.trans(Nat, 1n+Nat.double(Word.to_nat(pp, tt)), 1n+Nat.double(Nat.add(un, cc)), 1n+Nat.add(Nat.double(un),
        Nat.double(cc)), Equal.cong(Nat, Nat, xx => 1n+Nat.double(xx), Word.to_nat(pp, tt), Nat.add(un, cc), ee),
        Equal.cong(Nat, Nat, xx => 1n+xx, Nat.double(Nat.add(un, cc)), Nat.add(Nat.double(un), Nat.double(cc)),
        double_dist(un, cc)))

# zero and a word is zero
def and_zero_l(nn: Nat, ww: Word(nn)) -> {Word.and(nn, Word.zero(nn), ww) == Word.zero(nn) : Word(nn)}:
  match nn:
    case 0n:
      match ww:
        case WNil{}:
          {==}
    case 1n+ +pp:
      match ww:
        case WCon{_b, tt}:
          Equal.cong(Word(pp), Word.Con<pp>, xx => WCon{False{}, xx}, Word.and(pp, Word.zero(pp), tt), Word.zero(pp),
            and_zero_l(pp, tt))

# a U32 is its low four bits and sixteen times the rest
def n1(
  xx: U32
) -> {U32.to_nat(xx) == Nat.add(U32.to_nat(U32.and(15, xx)), sixteen(U32.to_nat(U32.shrn(xx, 4n)))) : Nat}:
  match xx:
    case U32{WCon{+b0, WCon{+b1, WCon{+b2, WCon{+b3, +tt}}}}}:
      +hn = Word.to_nat(28n, tt)
      +zz = Word.zero(28n)
      +e0 = {{==} : {Word.to_nat(28n, tt) == Nat.add(Word.to_nat(28n, zz), hn) : Nat}}
      +e1 = {nstep(b3, 28n, tt, zz, hn, e0) : {Word.to_nat(29n, WCon{b3, tt}) == Nat.add(Word.to_nat(29n, WCon{b3, zz}),
        Nat.double(hn)) : Nat}}
      +e2 = {nstep(b2, 29n, WCon{b3, tt}, WCon{b3, zz}, Nat.double(hn), e1) : {Word.to_nat(30n, WCon{b2, WCon{b3, tt}})
        == Nat.add(Word.to_nat(30n, WCon{b2, WCon{b3, zz}}), Nat.double(Nat.double(hn))) : Nat}}
      +e3 = {nstep(b1, 30n, WCon{b2, WCon{b3, tt}}, WCon{b2, WCon{b3, zz}}, Nat.double(Nat.double(hn)), e2) :
        {Word.to_nat(31n, WCon{b1, WCon{b2, WCon{b3, tt}}}) == Nat.add(Word.to_nat(31n, WCon{b1, WCon{b2, WCon{b3,
        zz}}}), Nat.double(Nat.double(Nat.double(hn)))) : Nat}}
      +e4 = {nstep(b0, 31n, WCon{b1, WCon{b2, WCon{b3, tt}}}, WCon{b1, WCon{b2, WCon{b3, zz}}}, Nat.double(Nat.double(
        Nat.double(hn))), e3) : {Word.to_nat(32n, WCon{b0, WCon{b1, WCon{b2, WCon{b3,
          tt}}}}) == Nat.add(Word.to_nat(32n,
        WCon{b0, WCon{b1, WCon{b2, WCon{b3, zz}}}}), sixteen(hn)) : Nat}}
      ea = Equal.sym(Word(28n), Word.and(28n, Word.zero(28n), tt), zz, and_zero_l(28n, tt))
      %ea : {Word.to_nat(32n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, tt}}}}) == Nat.add(Word.to_nat(32n, WCon{b0, WCon{b1,
        WCon{b2, WCon{b3, _}}}}), sixteen(U32.to_nat(U32.shrn(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, tt}}}}}, 4n))))
        : Nat}
      +p1 = Word.shr.pad(28n, tt)
      +p2 = Word.shr.pad(29n, p1)
      +p3 = Word.shr.pad(30n, p2)
      ep = Equal.sym(Nat, Word.to_nat(32n, Word.shr.pad(31n, p3)), hn, Equal.trans(Nat, Word.to_nat(32n,
        Word.shr.pad(31n, p3)), Word.to_nat(31n, p3), hn, jenc.pad_nat(31n, p3), Equal.trans(Nat, Word.to_nat(31n, p3),
        Word.to_nat(30n, p2), hn, jenc.pad_nat(30n, p2), Equal.trans(Nat, Word.to_nat(30n, p2), Word.to_nat(29n, p1),
            hn,
        jenc.pad_nat(29n, p1), jenc.pad_nat(28n, tt)))))
      %ep : {Word.to_nat(32n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, tt}}}}) == Nat.add(Word.to_nat(32n, WCon{b0, WCon{b1,
        WCon{b2, WCon{b3, zz}}}}), sixteen(_)) : Nat}
      e4

# eight times a number
def eight(nn: Nat) -> Nat:
  Nat.double(Nat.double(Nat.double(nn)))

# half a number, rounded down
def half(nn: Nat) -> Nat:
  match nn:
    case 0n:
      0n
    case 1n+0n:
      0n
    case 1n+1n+pp:
      1n+half(pp)

# whether a number is odd
def odd(nn: Nat) -> Bool:
  match nn:
    case 0n:
      False{}
    case 1n+0n:
      True{}
    case 1n+1n+pp:
      odd(pp)

# a number below 1 is 0
def lt1(xx: Nat, hh: {Nat.is_lt(xx, 1n) == True{} : Bool}) -> {0n == xx : Nat}:
  match xx:
    case 0n:
      {==}
    case 1n+_p:
      Empty.absurd({0n == 1n+_p : Nat}, huf.false_true(Equal.trans(Bool, False{}, Nat.is_lt(_p, 0n), True{},
        lt_zero_false(_p), hh)))

# samples built onto an accumulator: the accumulator reversed, then the list, or none
def onto(acc: List<&2, U32>, mm: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match mm:
    case None{}:
      None{}
    case Some{ll}:
      Some{List.reverse.go(&2, U32, acc, ll)}

# the alpha byte with the mask first is the top byte shifted down: the 32
# bits taken apart, both sides are the same word
def alpha.mask(cc: U32) -> {Png.enc.a(cc) == U32.shrn(cc, 24n) : U32}:
  match cc:
    case U32{w0}:
      match w0:
        case WCon{_b0, WCon{_b1, WCon{_b2, WCon{_b3, w4}}}}:
          match w4:
            case WCon{_b4, WCon{_b5, WCon{_b6, WCon{_b7, w8}}}}:
              match w8:
                case WCon{_b8, WCon{_b9, WCon{_b10, WCon{_b11, w12}}}}:
                  match w12:
                    case WCon{_b12, WCon{_b13, WCon{_b14, WCon{_b15, w16}}}}:
                      match w16:
                        case WCon{_b16, WCon{_b17, WCon{_b18, WCon{_b19, w20}}}}:
                          match w20:
                            case WCon{_b20, WCon{_b21, WCon{_b22, WCon{_b23, w24}}}}:
                              match w24:
                                case WCon{_b24, WCon{_b25, WCon{_b26, WCon{_b27, w28}}}}:
                                  match w28:
                                    case WCon{_b28, WCon{_b29, WCon{_b30, WCon{_b31, w32}}}}:
                                      match w32:
                                        case WNil{}:
                                          {==}

# enc.opaque with the flag z is z and every sample opaque
def opaque.all(
  px: List<&2, U32>,
  zz: Bool
) -> {Png.enc.opaque(px, zz) == Bool.and(zz, D1.all_opaque(px)) : Bool}:
  match px zz:
    case Nil{} False{}:
      {==}
    case Nil{} True{}:
      {==}
    case _cc <> _tl False{}:
      {==}
    case +cc <> +tl True{}:
      +ea = Equal.cong(U32, Bool, uu => U32.is_eq(uu, 255), Png.enc.a(cc), U32.shrn(cc, 24n), alpha.mask(cc))
      Equal.trans(Bool, Png.enc.opaque(tl, U32.is_eq(Png.enc.a(cc), 255)),
        Bool.and(D1.opaque(cc), D1.all_opaque(tl)), D1.all_opaque(cc <> tl),
        Equal.trans(Bool, Png.enc.opaque(tl, U32.is_eq(Png.enc.a(cc), 255)),
          Bool.and(U32.is_eq(Png.enc.a(cc), 255), D1.all_opaque(tl)),
          Bool.and(D1.opaque(cc), D1.all_opaque(tl)),
          opaque.all(tl, U32.is_eq(Png.enc.a(cc), 255)),
          Equal.cong(Bool, Bool, bb => Bool.and(bb, D1.all_opaque(tl)), U32.is_eq(Png.enc.a(cc), 255),
            D1.opaque(cc), ea)),
        Equal.sym(Bool, D1.all_opaque(cc <> tl), Bool.and(D1.opaque(cc), D1.all_opaque(tl)),
          all.if.and(D1.opaque(cc), D1.all_opaque(tl))))

# the state a refused frame header leaves the walk in
def w8.stop(+sc: Jpeg.Scan, +tb: Jpeg.Tabs, +en: List<&2, U32>, +ri: U32, +kd: U32) -> Jpeg.St:
  Jpeg.St{Jpeg.Stop{}, Jpeg.decode.frame0(), sc, tb, en, ri, kd, 1}
