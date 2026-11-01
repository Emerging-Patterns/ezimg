# Word multiplication read as Nat, and the row-major index y * w + x
import Base
import ./BasicFacts.bend as M1
import ./WordAddition.bend as M2

# a double times b is the double of a times b
law mul_double:
  for +aa: Nat
  for +bb: Nat
  {Nat.mul(Nat.double(aa), bb) == Nat.double(Nat.mul(aa, bb)) : Nat}

# the proof of mul_double
def mul_double(aa, bb):
  Equal.trans(Nat, Nat.mul(Nat.double(aa), bb), Nat.mul(Nat.add(aa, aa), bb), Nat.double(Nat.mul(aa, bb)),
    Equal.cong(Nat, Nat, xx => Nat.mul(xx, bb), Nat.double(aa), Nat.add(aa, aa), M1.double_add(aa)),
    Equal.trans(Nat, Nat.mul(Nat.add(aa, aa), bb), Nat.add(Nat.mul(aa, bb), Nat.mul(aa, bb)),
      Nat.double(Nat.mul(aa, bb)), M1.mul_add(aa, aa, bb),
      Equal.sym(Nat, Nat.double(Nat.mul(aa, bb)), Nat.add(Nat.mul(aa, bb), Nat.mul(aa, bb)),
        M1.double_add(Nat.mul(aa, bb)))))

# a times the double of b is the double of a times b
law mul_double_r:
  for +aa: Nat
  for +bb: Nat
  {Nat.mul(aa, Nat.double(bb)) == Nat.double(Nat.mul(aa, bb)) : Nat}

# the proof of mul_double_r
def mul_double_r(aa, bb):
  Equal.trans(Nat, Nat.mul(aa, Nat.double(bb)), Nat.mul(Nat.double(bb), aa), Nat.double(Nat.mul(aa, bb)),
    M1.mul_comm(aa, Nat.double(bb)),
    Equal.trans(Nat, Nat.mul(Nat.double(bb), aa), Nat.double(Nat.mul(bb, aa)), Nat.double(Nat.mul(aa, bb)),
      mul_double(bb, aa),
      Equal.cong(Nat, Nat, xx => Nat.double(xx), Nat.mul(bb, aa), Nat.mul(aa, bb), M1.mul_comm(bb, aa))))

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
      Empty.absurd({False{} == True{} : Bool}, M1.false_true(
        Equal.trans(Bool, False{}, Nat.is_lt(yy, 0n), True{}, M1.lt_zero_false(yy), hh)))
    case 0n 1n+_qq:
      {==}
    case 1n+_pp 0n:
      Empty.absurd({False{} == True{} : Bool}, M1.false_true(hh))
    case 1n+pp 1n+qq:
      lt_add_r(pp, yy, qq, hh)

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
    Equal.cong(Nat, Bool, nn => Nat.is_lt(nn, zz), Nat.add(yy, xx), Nat.add(xx, yy), M1.ras.add_comm(yy, xx)), hh))

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
          +xn = Nat.add(M1.bit(bb), Nat.double(Word.to_nat(pp, tt)))
          +h1 = {M1.lt_half(False{}, wn, Nat.pow(2n, pp), M1.lt_rw_r(Nat.double(wn), Nat.pow(2n, 1n+pp),
            Nat.double(Nat.pow(2n, pp)), M1.pow2_succ(pp), hh)) : {Nat.is_lt(wn, Nat.pow(2n, pp)) == True{} : Bool}}
          Equal.cong(Nat, Nat, xx => Nat.double(xx), Word.to_nat(pp, Word.shl.put(pp, bb, tt)), wn,
            Equal.trans(Nat, Word.to_nat(pp, Word.shl.put(pp, bb, tt)), xn, wn,
              M1.shl_put_nat(pp, bb, tt, M1.lt_rw_l(wn, xn, Nat.pow(2n, pp), M1.to_nat_con(pp, bb, tt), h1)),
              Equal.sym(Nat, wn, xn, M1.to_nat_con(pp, bb, tt))))

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
      +h2 = {lt_add_r(Nat.add(bn, bn), rr, top, M1.lt_rw_l(Nat.add(bn, Nat.add(bn, rr)), Nat.add(Nat.add(bn, bn), rr),
          top,
        Equal.sym(Nat, Nat.add(Nat.add(bn, bn), rr), Nat.add(bn, Nat.add(bn, rr)), M1.ras.add_assoc(bn, bn, rr)), h1)) :
        {Nat.is_lt(Nat.add(bn, bn), top) == True{} : Bool}}
      +es = {hs(M1.lt_rw_l(Nat.add(bn, bn), Nat.double(bn), top, Equal.sym(Nat, Nat.double(bn), Nat.add(bn, bn),
        M1.double_add(bn)), h2)) : {sn == Nat.double(bn) : Nat}}
      +em = {Equal.trans(Nat, Nat.mul(1n+pa, sn), Nat.mul(1n+pa, Nat.double(bn)), Nat.mul(Nat.double(1n+pa), bn),
        Equal.cong(Nat, Nat, xx => Nat.mul(1n+pa, xx), sn, Nat.double(bn), es),
        Equal.trans(Nat, Nat.mul(1n+pa, Nat.double(bn)), Nat.double(Nat.mul(1n+pa, bn)), Nat.mul(Nat.double(1n+pa), bn),
          mul_double_r(1n+pa, bn),
          Equal.sym(Nat, Nat.mul(Nat.double(1n+pa), bn), Nat.double(Nat.mul(1n+pa, bn)), mul_double(1n+pa, bn)))) :
        {Nat.mul(1n+pa, sn) == Nat.mul(Nat.double(1n+pa), bn) : Nat}}
      +ea = {Equal.cong(Nat, Nat, xx => Nat.add(acn, xx), Nat.mul(1n+pa, sn), Nat.mul(Nat.double(1n+pa), bn), em) :
        {Nat.add(acn, Nat.mul(1n+pa, sn)) == Nat.add(acn, Nat.mul(Nat.double(1n+pa), bn)) : Nat}}
      Equal.trans(Nat, rn, Nat.add(acn, Nat.mul(1n+pa, sn)), Nat.add(acn, Nat.mul(Nat.double(1n+pa), bn)),
        ih(M1.lt_rw_l(Nat.add(acn, Nat.mul(Nat.double(1n+pa), bn)), Nat.add(acn, Nat.mul(1n+pa, sn)), top,
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
          Equal.sym(Nat, Nat.add(Word.to_nat(nn, acc), 0n), Word.to_nat(nn, acc), M1.ras.add_zero(Word.to_nat(nn, acc)))
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
          +ex = {M1.ras.add_assoc(an, bn, rr) : {Nat.add(Nat.add(an, bn), rr) == Nat.add(an, Nat.add(bn, rr)) : Nat}}
          +h1 = {M1.lt_rw_l(Nat.add(an, Nat.add(bn, rr)), Nat.add(Nat.add(an, bn), rr), top,
            Equal.sym(Nat, Nat.add(Nat.add(an, bn), rr), Nat.add(an, Nat.add(bn, rr)), ex), hh) :
            {Nat.is_lt(Nat.add(Nat.add(an, bn), rr), top) == True{} : Bool}}
          +ea = {M2.adc_nat(nn, acc, bw, False{}, lt_add_r(Nat.add(an, bn), rr, top, h1)) :
            {Word.to_nat(nn, ac2) == Nat.add(an, bn) : Nat}}
          +h2 = {M1.lt_rw_l(Nat.add(Nat.add(an, bn), rr), Nat.add(Word.to_nat(nn, ac2), rr), top,
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
  +h0 = {M1.le_lt_trans(pr, Word.to_nat(nn, tw), top, hh, M2.word_lt_pow(nn, tw)) :
    {Nat.is_lt(pr, top) == True{} : Bool}}
  +h1 = {M1.lt_rw_l(pr, Nat.add(zn, pr), top,
    Equal.cong(Nat, Nat, xx => Nat.add(xx, pr), 0n, zn, Equal.sym(Nat, zn, 0n, ez)), h0) :
    {Nat.is_lt(Nat.add(zn, pr), top) == True{} : Bool}}
  Equal.trans(Nat, Word.to_nat(nn, Word.mul.go(nn, nn, aw, bw, Word.zero(nn))), Nat.add(zn, pr), pr,
    mulgo_nat(nn, nn, aw, bw, Word.zero(nn), h1),
    Equal.cong(Nat, Nat, xx => Nat.add(xx, pr), zn, 0n, ez))

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
  +h1 = {M1.lt_add_mono(yw, xn, wn, hx) : {Nat.is_lt(Nat.add(yw, xn), Nat.add(yw, wn)) == True{} : Bool}}
  +h2 = {M2.le_mul_mono(1n+yn, hn, wn, Equal.trans(Bool, Nat.is_le(1n+yn, hn), Nat.is_lt(yn, hn), True{},
    Equal.sym(Bool, Nat.is_lt(yn, hn), Nat.is_le(1n+yn, hn), M1.lt_le_succ(yn, hn)), hy)) :
    {Nat.is_le(Nat.add(wn, yw), Nat.mul(hn, wn)) == True{} : Bool}}
  +h3 = {M1.le_rw_l(Nat.add(wn, yw), Nat.add(yw, wn), Nat.mul(hn, wn), M1.ras.add_comm(wn, yw), h2) :
    {Nat.is_le(Nat.add(yw, wn), Nat.mul(hn, wn)) == True{} : Bool}}
  M1.lt_rw_r(Nat.add(yw, xn), Nat.mul(hn, wn), Nat.mul(wn, hn), M1.mul_comm(hn, wn),
    M1.lt_le_trans(Nat.add(yw, xn), Nat.add(yw, wn), Nat.mul(hn, wn), h1, h3))

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
  +h1 = {M1.le_rw_r(Nat.add(yw, xn), Nat.mul(wn, U32.to_nat(hh)), U32.to_nat(area),
    Equal.sym(Nat, U32.to_nat(area), Nat.mul(wn, U32.to_nat(hh)), h_area),
    M1.lt_le(Nat.add(yw, xn), Nat.mul(wn, U32.to_nat(hh)), index_lt(xn, yn, wn, U32.to_nat(hh), hx, hy))) :
    {Nat.is_le(Nat.add(yw, xn), U32.to_nat(area)) == True{} : Bool}}
  +em = {u32_mul_below(yy, ww, area, M2.le_add_r(yw, xn, U32.to_nat(area), h1)) :
    {U32.to_nat(U32.mul(yy, ww)) == yw : Nat}}
  +h2 = {M1.le_rw_l(Nat.add(yw, xn), Nat.add(U32.to_nat(U32.mul(yy, ww)), xn), U32.to_nat(area),
    Equal.cong(Nat, Nat, nn => Nat.add(nn, xn), yw, U32.to_nat(U32.mul(yy, ww)),
      Equal.sym(Nat, U32.to_nat(U32.mul(yy, ww)), yw, em)), h1) :
    {Nat.is_le(Nat.add(U32.to_nat(U32.mul(yy, ww)), xn), U32.to_nat(area)) == True{} : Bool}}
  Equal.trans(Nat, U32.to_nat(U32.add(U32.mul(yy, ww), xx)), Nat.add(U32.to_nat(U32.mul(yy, ww)), xn),
    Nat.add(yw, xn), M2.u32_add_below(U32.mul(yy, ww), xx, area, h2),
    Equal.cong(Nat, Nat, nn => Nat.add(nn, xn), U32.to_nat(U32.mul(yy, ww)), yw, em))

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
      M1.le_zero(_aa)
    case 0n 1n+_pb:
      Empty.absurd({Nat.is_le(1n+_pb, 0n) == True{} : Bool}, M1.false_true(Equal.sym(Bool, True{}, False{}, hh)))
    case 1n+pa 1n+pb:
      not_lt_le(pa, pb, hh)

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
      Empty.absurd({False{} == True{} : Bool}, M1.false_true(
        Equal.trans(Bool, False{}, Nat.is_lt(aa, 0n), True{}, M1.lt_zero_false(aa), hh)))
    case 1n+_pb:
      {==}

# x < w as U32 when x < w as Nat
def ras.lt(
  +aa: U32,
  +bb: U32,
  hh: {Nat.is_lt(U32.to_nat(aa), U32.to_nat(bb)) == True{} : Bool}
) -> {U32.is_lt(aa, bb) == True{} : Bool}:
  Equal.trans(Bool, U32.is_lt(aa, bb), Nat.is_lt(U32.to_nat(aa), U32.to_nat(bb)), True{}, M2.u32_lt(aa, bb), hh)
