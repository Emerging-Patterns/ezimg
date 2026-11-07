# PNG filter reconstruction: the code's bytes against the specification's
import Base
import ../../src/png.bend as Png
import ../../laws/UnfilterUndoesFilter.bend as L1
import ./BasicFacts.bend as M1

# k ones then zeros: the low k bits of an n-bit word
def lo.mask(nn: Nat, kk: Nat) -> Word(nn):
  match nn:
    case 0n:
      WNil{}
    case 1n+pp:
      match kk:
        case 0n:
          WCon{False{}, lo.mask(pp, 0n)}
        case 1n+qq:
          WCon{True{}, lo.mask(pp, qq)}

# a word masked with no bits is zero
law and_none:
  for nn: Nat
  for ww: Word(nn)
  {Word.and(nn, lo.mask(nn, 0n), ww) == lo.mask(nn, 0n) : Word(nn)}

# the proof of and_none
def and_none(nn, ww):
  match nn:
    case 0n:
      match ww:
        case WNil{}:
          {==}
    case 1n+pp:
      match ww:
        case WCon{_bb, tt}:
          Equal.cong(Word(pp), Word.Con<pp>, vv => WCon{False{}, vv}, Word.and(pp, lo.mask(pp, 0n), tt),
            lo.mask(pp, 0n), and_none(pp, tt))

# the low k bits of a - b (carry c in), masked, plus b (carry not c in) are
# the low k bits of a: the carries of the two sums are opposite at every bit
def sal.ty(+nn: Nat, +kk: Nat, +aw: Word(nn), +bw: Word(nn), +cc: Bool) -> Type:
  {Word.and(nn, lo.mask(nn, kk),
    Word.adc(nn, Word.and(nn, lo.mask(nn, kk), Word.adc(nn, aw, bw, True{}, cc)), bw, False{}, Bool.not(cc)))
    == Word.and(nn, lo.mask(nn, kk), aw) : Word(nn)}

# one bit of sub_add_low: the bit agrees, the rest by the hypothesis
law sal.arm:
  for +pp: Nat
  for +qq: Nat
  for +at: Word(pp)
  for +bt: Word(pp)
  for bit: Bool
  for +kk: Bool
  for ih: sal.ty(pp, qq, at, bt, kk)
  {WCon{bit, Word.and(pp, lo.mask(pp, qq),
    Word.adc(pp, Word.and(pp, lo.mask(pp, qq), Word.adc(pp, at, bt, True{}, kk)), bt, False{}, Bool.not(kk)))}
    == WCon{bit, Word.and(pp, lo.mask(pp, qq), at)} : Word.Con<pp>}

# the proof of sal.arm
def sal.arm(pp, qq, at, bt, bit, kk, ih):
  Equal.cong(Word(pp), Word.Con<pp>, vv => WCon{bit, vv},
    Word.and(pp, lo.mask(pp, qq),
      Word.adc(pp, Word.and(pp, lo.mask(pp, qq), Word.adc(pp, at, bt, True{}, kk)), bt, False{}, Bool.not(kk))),
    Word.and(pp, lo.mask(pp, qq), at), ih)

# the low k bits of a - b plus b are the low k bits of a
law sub_add_low:
  for +nn: Nat
  for +kk: Nat
  for +aw: Word(nn)
  for +bw: Word(nn)
  for +cc: Bool
  sal.ty(nn, kk, aw, bw, cc)

# the proof of sub_add_low
def sub_add_low(nn, kk, aw, bw, cc):
  match nn:
    case 0n:
      {==}
    case 1n+(+pp):
      match kk:
        case 0n:
          Equal.trans(Word(1n+pp),
            Word.and(1n+pp, lo.mask(1n+pp, 0n),
              Word.adc(1n+pp, Word.and(1n+pp, lo.mask(1n+pp, 0n), Word.adc(1n+pp, aw, bw, True{}, cc)), bw, False{},
                Bool.not(cc))),
            lo.mask(1n+pp, 0n), Word.and(1n+pp, lo.mask(1n+pp, 0n), aw),
            and_none(1n+pp, Word.adc(1n+pp, Word.and(1n+pp, lo.mask(1n+pp, 0n), Word.adc(1n+pp, aw, bw, True{}, cc)),
              bw, False{}, Bool.not(cc))),
            Equal.sym(Word(1n+pp), Word.and(1n+pp, lo.mask(1n+pp, 0n), aw), lo.mask(1n+pp, 0n), and_none(1n+pp, aw)))
        case 1n+(+qq):
          match aw bw cc:
            case WCon{False{}, +at} WCon{False{}, +bt} False{}:
              sal.arm(pp, qq, at, bt, False{}, False{}, sub_add_low(pp, qq, at, bt, False{}))
            case WCon{False{}, +at} WCon{False{}, +bt} True{}:
              sal.arm(pp, qq, at, bt, False{}, True{}, sub_add_low(pp, qq, at, bt, True{}))
            case WCon{False{}, +at} WCon{True{}, +bt} False{}:
              sal.arm(pp, qq, at, bt, False{}, False{}, sub_add_low(pp, qq, at, bt, False{}))
            case WCon{False{}, +at} WCon{True{}, +bt} True{}:
              sal.arm(pp, qq, at, bt, False{}, False{}, sub_add_low(pp, qq, at, bt, False{}))
            case WCon{True{}, +at} WCon{False{}, +bt} False{}:
              sal.arm(pp, qq, at, bt, True{}, True{}, sub_add_low(pp, qq, at, bt, True{}))
            case WCon{True{}, +at} WCon{False{}, +bt} True{}:
              sal.arm(pp, qq, at, bt, True{}, True{}, sub_add_low(pp, qq, at, bt, True{}))
            case WCon{True{}, +at} WCon{True{}, +bt} False{}:
              sal.arm(pp, qq, at, bt, True{}, False{}, sub_add_low(pp, qq, at, bt, False{}))
            case WCon{True{}, +at} WCon{True{}, +bt} True{}:
              sal.arm(pp, qq, at, bt, True{}, True{}, sub_add_low(pp, qq, at, bt, True{}))

# a byte's reconstruction: the low 8 bits of (x - p) mod 256, plus p, are
# the low 8 bits of x
law byte_back:
  for +xx: U32
  for +pp: U32
  {U32.and(255, U32.add(U32.and(255, U32.sub(xx, pp)), pp)) == U32.and(255, xx) : U32}

# the proof of byte_back
def byte_back(xx, pp):
  match xx pp:
    case U32{+xw} U32{+pw}:
      Equal.cong(Word(32n), U32, ww => U32{ww},
        Word.and(32n, lo.mask(32n, 8n),
          Word.adc(32n, Word.and(32n, lo.mask(32n, 8n), Word.adc(32n, xw, pw, True{}, True{})), pw, False{}, False{})),
        Word.and(32n, lo.mask(32n, 8n), xw), sub_add_low(32n, 8n, xw, pw, True{}))

# 2 to the k as an n-bit word: k zeros, a one, then zeros
def lo.pow(nn: Nat, kk: Nat) -> Word(nn):
  match nn:
    case 0n:
      WNil{}
    case 1n+pp:
      match kk:
        case 0n:
          WCon{True{}, lo.mask(pp, 0n)}
        case 1n+qq:
          WCon{False{}, lo.pow(pp, qq)}

# True is never False
law flt.true_false:
  for ee: {True{} == False{} : Bool}
  Empty

# the proof of flt.true_false
def flt.true_false(ee):
  M1.false_true(Equal.sym(Bool, True{}, False{}, ee))

# one bit of never_below: a comparison not below stays not below
law nb.arm:
  for +cc: Cmp
  for +bb: Bool
  for ih: {Cmp.is_lt(cc) == False{} : Bool}
  {Cmp.is_lt(Word.cmp.fin(bb, False{}, cc)) == False{} : Bool}

# the proof of nb.arm
def nb.arm(cc, bb, ih):
  match cc:
    case LT{}:
      Empty.absurd({Cmp.is_lt(Word.cmp.fin(bb, False{}, LT{})) == False{} : Bool}, flt.true_false(ih))
    case EQ{}:
      match bb:
        case False{}:
          {==}
        case True{}:
          {==}
    case GT{}:
      {==}

# no word is below zero
law never_below:
  for +nn: Nat
  for +ww: Word(nn)
  {Cmp.is_lt(Word.cmp(nn, ww, lo.mask(nn, 0n))) == False{} : Bool}

# the proof of never_below
def never_below(nn, ww):
  match nn:
    case 0n:
      {==}
    case 1n+(+pp):
      match ww:
        case WCon{bb, +tt}:
          nb.arm(Word.cmp(pp, tt, lo.mask(pp, 0n)), bb, never_below(pp, tt))

# below with a clear bit on the right: the rest is below
law lt_strip:
  for +cc: Cmp
  for +bb: Bool
  for hh: {Cmp.is_lt(Word.cmp.fin(bb, False{}, cc)) == True{} : Bool}
  {Cmp.is_lt(cc) == True{} : Bool}

# the proof of lt_strip
def lt_strip(cc, bb, hh):
  match cc:
    case LT{}:
      {==}
    case EQ{}:
      match bb:
        case False{}:
          Empty.absurd({Cmp.is_lt(EQ{}) == True{} : Bool}, M1.false_true(hh))
        case True{}:
          Empty.absurd({Cmp.is_lt(EQ{}) == True{} : Bool}, M1.false_true(hh))
    case GT{}:
      Empty.absurd({Cmp.is_lt(GT{}) == True{} : Bool}, M1.false_true(hh))

# below_top when the rest compares equal to zero
law below_eq:
  for +pp: Nat
  for +bb: Bool
  for +tt: Word(pp)
  for ec: {Word.cmp(pp, tt, lo.mask(pp, 0n)) == EQ{} : Cmp}
  for hh: {Cmp.is_lt(Word.cmp.fin(bb, True{}, EQ{})) == True{} : Bool}
  {WCon{False{}, Word.and(pp, lo.mask(pp, 0n), tt)} == WCon{bb, tt} : Word.Con<pp>}

# the proof of below_eq
def below_eq(pp, bb, tt, ec, hh):
  match bb:
    case True{}:
      Empty.absurd({WCon{False{}, Word.and(pp, lo.mask(pp, 0n), tt)} == WCon{True{}, tt} : Word.Con<pp>},
        M1.false_true(hh))
    case False{}:
      Equal.cong(Word(pp), Word.Con<pp>, vv => WCon{False{}, vv}, Word.and(pp, lo.mask(pp, 0n), tt), tt,
          Equal.trans(Word(pp), Word.and(pp, lo.mask(pp, 0n), tt), lo.mask(pp, 0n), tt, and_none(pp, tt),
            Equal.sym(Word(pp), tt, lo.mask(pp, 0n),
              M1.weq(pp, tt, lo.mask(pp, 0n), Equal.cong(Cmp, Bool, xx => Cmp.is_eq(xx),
                Word.cmp(pp, tt, lo.mask(pp, 0n)), EQ{}, ec)))))

# below 2^0 past a prefix: the bit is clear and the rest is zero
law below_top:
  for +pp: Nat
  for +bb: Bool
  for +cc: Cmp
  for +tt: Word(pp)
  for ec: {Word.cmp(pp, tt, lo.mask(pp, 0n)) == cc : Cmp}
  for hh: {Cmp.is_lt(Word.cmp.fin(bb, True{}, cc)) == True{} : Bool}
  {WCon{False{}, Word.and(pp, lo.mask(pp, 0n), tt)} == WCon{bb, tt} : Word.Con<pp>}

# the proof of below_top
def below_top(pp, bb, cc, tt, ec, hh):
  match cc:
    case LT{}:
      Empty.absurd({WCon{False{}, Word.and(pp, lo.mask(pp, 0n), tt)} == WCon{bb, tt} : Word.Con<pp>},
        flt.true_false(Equal.trans(Bool, True{}, Cmp.is_lt(Word.cmp(pp, tt, lo.mask(pp, 0n))), False{},
          Equal.cong(Cmp, Bool, xx => Cmp.is_lt(xx), LT{}, Word.cmp(pp, tt, lo.mask(pp, 0n)),
            Equal.sym(Cmp, Word.cmp(pp, tt, lo.mask(pp, 0n)), LT{}, ec)),
          never_below(pp, tt))))
    case GT{}:
      Empty.absurd({WCon{False{}, Word.and(pp, lo.mask(pp, 0n), tt)} == WCon{bb, tt} : Word.Con<pp>},
        M1.false_true(hh))
    case EQ{}:
      below_eq(pp, bb, tt, ec, hh)

# a word below 2^k keeps its value under the low-k-bits mask
law below_low:
  for +nn: Nat
  for +kk: Nat
  for +ww: Word(nn)
  for hh: {Cmp.is_lt(Word.cmp(nn, ww, lo.pow(nn, kk))) == True{} : Bool}
  {Word.and(nn, lo.mask(nn, kk), ww) == ww : Word(nn)}

# the proof of below_low
def below_low(nn, kk, ww, hh):
  match nn:
    case 0n:
      match ww:
        case WNil{}:
          {==}
    case 1n+(+pp):
      match kk:
        case 0n:
          match ww:
            case WCon{bb, +tt}:
              below_top(pp, bb, Word.cmp(pp, tt, lo.mask(pp, 0n)), tt, {==}, hh)
        case 1n+(+qq):
          match ww:
            case WCon{bb, +tt}:
              Equal.cong(Word(pp), Word.Con<pp>, vv => WCon{bb, vv}, Word.and(pp, lo.mask(pp, qq), tt), tt,
                below_low(pp, qq, tt, lt_strip(Word.cmp(pp, tt, lo.pow(pp, qq)), bb, hh)))

# a U32 below 256 is its own low byte
law byte_low:
  for +xx: U32
  for hh: {U32.is_lt(xx, 256) == True{} : Bool}
  {U32.and(255, xx) == xx : U32}

# the proof of byte_low
def byte_low(xx, hh):
  match xx:
    case U32{+xw}:
      Equal.cong(Word(32n), U32, ww => U32{ww}, Word.and(32n, lo.mask(32n, 8n), xw), xw,
        below_low(32n, 8n, xw, hh))

# a word whose first bit is clear and that is not zero: the rest is not zero (after ezjson)
law flt.fin_ff:
  for cc: Cmp
  for h_nz: {Cmp.is_eq(Word.cmp.fin(False{}, False{}, cc)) == False{} : Bool}
  {Cmp.is_eq(cc) == False{} : Bool}

# the proof of flt.fin_ff
def flt.fin_ff(cc, h_nz):
  match cc:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({Cmp.is_eq(EQ{}) == False{} : Bool}, flt.true_false(h_nz))
    case GT{}:
      {==}

# subtracting zero with no carry in takes one: a - 0 - 1, one less than a
# when a is not zero (after ezjson)
law flt.adc_zero_borrow:
  for +pp: Nat
  for +aw: Word(pp)
  for h_nz: {Cmp.is_eq(Word.cmp(pp, aw, Word.zero(pp))) == False{} : Bool}
  {1n+Word.to_nat(pp, Word.adc(pp, aw, Word.zero(pp), True{}, False{})) == Word.to_nat(pp, aw) : Nat}

# the proof of flt.adc_zero_borrow
def flt.adc_zero_borrow(pp, aw, h_nz):
  match pp:
    case 0n:
      match aw:
        case WNil{}:
          Empty.absurd({1n == 0n : Nat}, flt.true_false(h_nz))
    case 1n+(+qq):
      match aw:
        case WCon{True{}, +at}:
          lc = Equal.sym(Word(qq), Word.adc(qq, at, Word.zero(qq), True{}, True{}), at, M1.adc_zero_carry(qq, at))
          %lc : {1n+Nat.double(Word.to_nat(qq, _)) == 1n+Nat.double(Word.to_nat(qq, at)) : Nat}
          {==}
        case WCon{False{}, +at}:
          ih = flt.adc_zero_borrow(qq, at, flt.fin_ff(Word.cmp(qq, at, Word.zero(qq)), h_nz))
          %ih : {2n+Nat.double(Word.to_nat(qq, Word.adc(qq, at, Word.zero(qq), True{}, False{})))
            == Nat.double(_) : Nat}
          {==}

# one less than a nonzero U32, as a Nat (after ezjson)
law flt.u32_dec:
  for +uu: U32
  for h_nz: {U32.is_zero(uu) == False{} : Bool}
  {U32.to_nat(uu) == 1n+U32.to_nat(U32.sub(uu, 1)) : Nat}

# the proof of flt.u32_dec
def flt.u32_dec(uu, h_nz):
  match uu:
    case U32{WCon{True{}, +at}}:
      lc = Equal.sym(Word(31n), Word.adc(31n, at, Word.zero(31n), True{}, True{}), at, M1.adc_zero_carry(31n, at))
      %lc : {1n+Nat.double(Word.to_nat(31n, at)) == 1n+Nat.double(Word.to_nat(31n, _)) : Nat}
      {==}
    case U32{WCon{False{}, +at}}:
      ih = flt.adc_zero_borrow(31n, at, flt.fin_ff(Word.cmp(31n, at, Word.zero(31n)), h_nz))
      %ih : {Nat.double(_)
        == 2n+Nat.double(Word.to_nat(31n, Word.adc(31n, at, Word.zero(31n), True{}, False{}))) : Nat}
      {==}

# a zero U32 is 0 as a Nat
law u32_zero_nat:
  for +uu: U32
  for h_z: {U32.is_zero(uu) == True{} : Bool}
  {U32.to_nat(uu) == 0n : Nat}

# the proof of u32_zero_nat
def u32_zero_nat(uu, h_z):
  Equal.cong(U32, Nat, vv => U32.to_nat(vv), uu, 0, M1.ueq(uu, 0, h_z))

# a comparison that is greater is not equal
law gt_ne.at:
  for cc: Cmp
  for h_gt: {Cmp.is_gt(cc) == True{} : Bool}
  {Cmp.is_eq(cc) == False{} : Bool}

# the proof of gt_ne.at
def gt_ne.at(cc, h_gt):
  match cc:
    case LT{}:
      Empty.absurd({Cmp.is_eq(LT{}) == False{} : Bool}, M1.false_true(h_gt))
    case EQ{}:
      Empty.absurd({Cmp.is_eq(EQ{}) == False{} : Bool}, M1.false_true(h_gt))
    case GT{}:
      {==}

# a U32 greater than 0 is not zero
law gt_nonzero:
  for +uu: U32
  for h_gt: {U32.is_gt(uu, 0) == True{} : Bool}
  {U32.is_zero(uu) == False{} : Bool}

# the proof of gt_nonzero
def gt_nonzero(uu, h_gt):
  gt_ne.at(U32.cmp(uu, 0), h_gt)

# 0 is never one more than a Nat
law flt.zero_succ:
  for +nn: Nat
  for ee: {0n == 1n+nn : Nat}
  Empty

# the proof of flt.zero_succ
def flt.zero_succ(_nn, ee):
  %ee : M1.zero_ty(_)
  Unit{}

# uf.nth counting a U32 down is flt.at counting its Nat down, once whether
# the count is zero is named
law nth_at.go:
  for +xs: List<&2, U32>
  for zz: Bool
  for +kk: U32
  for ez: {U32.is_zero(kk) == zz : Bool}
  {Png.uf.nth(xs, zz, kk) == L1.flt.at(xs, U32.to_nat(kk)) : U32}

# the proof of nth_at.go
def nth_at.go(xs, zz, kk, ez):
  match xs zz:
    case Nil{} _zz:
      {==}
    case +hd <> +tl True{}:
      Equal.sym(U32, L1.flt.at(hd <> tl, U32.to_nat(kk)), hd,
        Equal.cong(Nat, U32, nn => L1.flt.at(hd <> tl, nn), U32.to_nat(kk), 0n, u32_zero_nat(kk, ez)))
    case +hd <> +tl False{}:
      Equal.trans(U32, Png.uf.nth(tl, U32.is_zero(U32.sub(kk, 1)), U32.sub(kk, 1)),
        L1.flt.at(tl, U32.to_nat(U32.sub(kk, 1))), L1.flt.at(hd <> tl, U32.to_nat(kk)),
        nth_at.go(tl, U32.is_zero(U32.sub(kk, 1)), U32.sub(kk, 1), {==}),
        Equal.cong(Nat, U32, nn => L1.flt.at(hd <> tl, nn), 1n+U32.to_nat(U32.sub(kk, 1)), U32.to_nat(kk),
          Equal.sym(Nat, U32.to_nat(kk), 1n+U32.to_nat(U32.sub(kk, 1)), flt.u32_dec(kk, ez))))

# the code's byte bpp back is the specification's
law back_at:
  for +xs: List<&2, U32>
  for +bpp: U32
  {Png.uf.back(xs, bpp) == L1.flt.at(xs, U32.to_nat(U32.sub(bpp, 1))) : U32}

# the proof of back_at
def back_at(xs, bpp):
  nth_at.go(xs, U32.is_zero(U32.sub(bpp, 1)), U32.sub(bpp, 1), {==})

# the code's |x - y| is the specification's, once which is larger is named
law dist_abs.at:
  for ge: Bool
  for +xx: U32
  for +yy: U32
  {Png.uf.abs.at(U32.sub(xx, yy), U32.sub(yy, xx), ge) == L1.flt.dist.at(ge, xx, yy) : U32}

# the proof of dist_abs.at
def dist_abs.at(ge, _xx, _yy):
  match ge:
    case True{}:
      {==}
    case False{}:
      {==}

# the code's |x - y| is the specification's
law dist_abs:
  for +xx: U32
  for +yy: U32
  {Png.uf.abs(xx, yy) == L1.flt.dist(xx, yy) : U32}

# the proof of dist_abs
def dist_abs(xx, yy):
  dist_abs.at(U32.is_ge(xx, yy), xx, yy)

# the code's Paeth choice is the specification's, in the same order
law near_at:
  for z1: Bool
  for z2: Bool
  for z3: Bool
  for +aa: U32
  for +bb: U32
  for +cc: U32
  {Png.uf.paeth.at(Bool.and(z1, z2), z3, aa, bb, cc) == L1.flt.paeth.near(z1, z2, z3, aa, bb, cc) : U32}

# the proof of near_at
def near_at(z1, z2, z3, _aa, _bb, _cc):
  match z1 z2 z3:
    case True{} True{} _z3:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} _z2 True{}:
      {==}
    case False{} _z2 False{}:
      {==}

# the specification's Paeth choice over three distances
def near.of(+pa: U32, +pb: U32, +pc: U32, +aa: U32, +bb: U32, +cc: U32) -> U32:
  L1.flt.paeth.near(U32.is_le(pa, pb), U32.is_le(pa, pc), U32.is_le(pb, pc), aa, bb, cc)

# the code's PaethPredictor is the specification's
law paeth_eq:
  for +aa: U32
  for +bb: U32
  for +cc: U32
  {Png.uf.paeth(aa, bb, cc) == L1.flt.paeth(aa, bb, cc) : U32}

# the proof of paeth_eq
def paeth_eq(aa, bb, cc):
  +d1 = Png.uf.abs(bb, cc)
  +d2 = Png.uf.abs(aa, cc)
  +d3 = Png.uf.abs(U32.add(aa, bb), U32.shl(cc))
  +e1 = dist_abs(bb, cc)
  +e2 = dist_abs(aa, cc)
  +e3 = dist_abs(U32.add(aa, bb), U32.shl(cc))
  Equal.trans(U32, Png.uf.paeth(aa, bb, cc), near.of(d1, d2, d3, aa, bb, cc), L1.flt.paeth(aa, bb, cc),
    near_at(U32.is_le(d1, d2), U32.is_le(d1, d3), U32.is_le(d2, d3), aa, bb, cc),
    Equal.trans(U32, near.of(d1, d2, d3, aa, bb, cc), near.of(L1.flt.dist(bb, cc), d2, d3, aa, bb, cc),
      L1.flt.paeth(aa, bb, cc),
      Equal.cong(U32, U32, vv => near.of(vv, d2, d3, aa, bb, cc), d1, L1.flt.dist(bb, cc), e1),
      Equal.trans(U32, near.of(L1.flt.dist(bb, cc), d2, d3, aa, bb, cc),
        near.of(L1.flt.dist(bb, cc), L1.flt.dist(aa, cc), d3, aa, bb, cc), L1.flt.paeth(aa, bb, cc),
        Equal.cong(U32, U32, vv => near.of(L1.flt.dist(bb, cc), vv, d3, aa, bb, cc), d2, L1.flt.dist(aa, cc), e2),
        Equal.cong(U32, U32, vv => near.of(L1.flt.dist(bb, cc), L1.flt.dist(aa, cc), vv, aa, bb, cc), d3,
          L1.flt.dist(U32.add(aa, bb), U32.shl(cc)), e3))))

# the code's predictor for each filter type is the specification's
law pred_eq:
  for +ft: L1.Ft
  for +aa: U32
  for +bb: U32
  for +cc: U32
  {Png.uf.pred(L1.ft.code(ft), aa, bb, cc) == L1.flt.pred(ft, aa, bb, cc) : U32}

# the proof of pred_eq
def pred_eq(ft, aa, bb, cc):
  match ft:
    case L1.FNone{}:
      {==}
    case L1.FSub{}:
      {==}
    case L1.FUp{}:
      {==}
    case L1.FAvg{}:
      {==}
    case L1.FPaeth{}:
      paeth_eq(aa, bb, cc)

# the code's byte above is the specification's
law bb_up:
  for +prest: List<&2, U32>
  {Png.uf.bb(prest) == L1.flt.up(prest) : U32}

# the proof of bb_up
def bb_up(prest):
  match prest:
    case Nil{}:
      {==}
    case _hd <> _tl:
      {==}

# the specification's predictor at a byte, from the row so far and the previous row
def pred.at(+ft: L1.Ft, +bpp: U32, +prest: List<&2, U32>, +phist: List<&2, U32>, +cur: List<&2, U32>) -> U32:
  L1.flt.pred(ft, L1.flt.at(cur, U32.to_nat(U32.sub(bpp, 1))), L1.flt.up(prest),
    L1.flt.at(phist, U32.to_nat(U32.sub(bpp, 1))))

# the code's predictor at a byte is the specification's
law pred_at:
  for +ft: L1.Ft
  for +bpp: U32
  for +prest: List<&2, U32>
  for +phist: List<&2, U32>
  for +cur: List<&2, U32>
  {Png.uf.pred(L1.ft.code(ft), Png.uf.back(cur, bpp), Png.uf.bb(prest), Png.uf.back(phist, bpp))
    == pred.at(ft, bpp, prest, phist, cur) : U32}

# the proof of pred_at
def pred_at(ft, bpp, prest, phist, cur):
  +ka = L1.flt.at(cur, U32.to_nat(U32.sub(bpp, 1)))
  +kb = L1.flt.up(prest)
  +kc = L1.flt.at(phist, U32.to_nat(U32.sub(bpp, 1)))
  +cd = L1.ft.code(ft)
  Equal.trans(U32, Png.uf.pred(cd, Png.uf.back(cur, bpp), Png.uf.bb(prest), Png.uf.back(phist, bpp)),
    Png.uf.pred(cd, ka, Png.uf.bb(prest), Png.uf.back(phist, bpp)), pred.at(ft, bpp, prest, phist, cur),
    Equal.cong(U32, U32, vv => Png.uf.pred(cd, vv, Png.uf.bb(prest), Png.uf.back(phist, bpp)),
      Png.uf.back(cur, bpp), ka, back_at(cur, bpp)),
    Equal.trans(U32, Png.uf.pred(cd, ka, Png.uf.bb(prest), Png.uf.back(phist, bpp)),
      Png.uf.pred(cd, ka, kb, Png.uf.back(phist, bpp)), pred.at(ft, bpp, prest, phist, cur),
      Equal.cong(U32, U32, vv => Png.uf.pred(cd, ka, vv, Png.uf.back(phist, bpp)), Png.uf.bb(prest), kb,
        bb_up(prest)),
      Equal.trans(U32, Png.uf.pred(cd, ka, kb, Png.uf.back(phist, bpp)), Png.uf.pred(cd, ka, kb, kc),
        pred.at(ft, bpp, prest, phist, cur),
        Equal.cong(U32, U32, vv => Png.uf.pred(cd, ka, kb, vv), Png.uf.back(phist, bpp), kc, back_at(phist, bpp)),
        pred_eq(ft, ka, kb, kc))))

# the code reconstructs each byte the specification's filter wrote: for a
# byte below 256, uf.recon of its filtered byte is the byte
law recon_eq:
  for +ft: L1.Ft
  for +bpp: U32
  for +xx: U32
  for +prest: List<&2, U32>
  for +phist: List<&2, U32>
  for +cur: List<&2, U32>
  for h_byte: {U32.is_lt(xx, 256) == True{} : Bool}
  {Png.uf.recon(U32.and(255, U32.sub(xx, pred.at(ft, bpp, prest, phist, cur))), L1.ft.code(ft), bpp, prest, phist,
    cur) == xx : U32}

# the proof of recon_eq
def recon_eq(ft, bpp, xx, prest, phist, cur, h_byte):
  +pl = pred.at(ft, bpp, prest, phist, cur)
  +fb = U32.and(255, U32.sub(xx, pl))
  Equal.trans(U32, Png.uf.recon(fb, L1.ft.code(ft), bpp, prest, phist, cur), Png.uf.add(fb, pl), xx,
    Equal.cong(U32, U32, vv => Png.uf.add(fb, vv),
      Png.uf.pred(L1.ft.code(ft), Png.uf.back(cur, bpp), Png.uf.bb(prest), Png.uf.back(phist, bpp)), pl,
      pred_at(ft, bpp, prest, phist, cur)),
    Equal.trans(U32, Png.uf.add(fb, pl), U32.and(255, xx), xx, byte_back(xx, pl), byte_low(xx, h_byte)))

# the code's rest of the previous row is the specification's
law drop_next:
  for +prest: List<&2, U32>
  {Png.uf.drop(prest) == L1.flt.next(prest) : List<&2, U32>}

# the proof of drop_next
def drop_next(prest):
  match prest:
    case Nil{}:
      {==}
    case _hd <> _tl:
      {==}

# a true answer from flt.bytes started from a true answer
law bytes_acc:
  for +row: List<&2, U32>
  for +nn: Nat
  for +ok: Bool
  for hh: {L1.flt.bytes(row, nn, ok) == True{} : Bool}
  {ok == True{} : Bool}

# the proof of bytes_acc
def bytes_acc(row, nn, ok, hh):
  match row nn:
    case Nil{} 0n:
      hh
    case Nil{} 1n+_pp:
      Empty.absurd({ok == True{} : Bool}, M1.false_true(hh))
    case _xx <> _rest 0n:
      Empty.absurd({ok == True{} : Bool}, M1.false_true(hh))
    case +xx <> +rest 1n+(+pp):
      M1.and_left(ok, U32.is_lt(xx, 256), bytes_acc(rest, pp, Bool.and(ok, U32.is_lt(xx, 256)), hh))

# unfilter in a row's body: the state uf.go carries there
def row.code(
  +xs: List<&2, U32>,
  +zz: Bool,
  +bpp: U32,
  +stride: U32,
  +nr: Nat,
  +prest: List<&2, U32>,
  +phist: List<&2, U32>,
  +cur: List<&2, U32>,
  +all: List<&2, U32>,
  +left: U32,
  +ft: L1.Ft
) -> Maybe<&2, List<&2, U32>>:
  Png.uf.go(xs, Png.UBody{}, zz, bpp, stride, nr, prest, phist, cur, all, left, L1.ft.code(ft))

# unfilter at the next filter byte, once the row `row` is read after `cur` and `all`
def row.done(
  +tail: List<&2, U32>,
  +bpp: U32,
  +stride: U32,
  +nr: Nat,
  +cur: List<&2, U32>,
  +all: List<&2, U32>,
  +row: List<&2, U32>
) -> Maybe<&2, List<&2, U32>>:
  Png.uf.go(tail, Png.UFilt{}, False{}, bpp, stride, nr, List.reverse(&2, U32, List.reverse.go(&2, U32, row, cur)), [],
    [], List.reverse.go(&2, U32, row, all), 0, 0)

# row.code one byte on: vv the byte just read, pn and pb the previous row's rest and byte above
def row.mid(
  +xs: List<&2, U32>,
  +zz: Bool,
  +bpp: U32,
  +stride: U32,
  +nr: Nat,
  +pn: List<&2, U32>,
  +pb: U32,
  +phist: List<&2, U32>,
  +vv: U32,
  +cur: List<&2, U32>,
  +all: List<&2, U32>,
  +nl: U32,
  +ft: L1.Ft
) -> Maybe<&2, List<&2, U32>>:
  row.code(xs, zz, bpp, stride, nr, pn, pb <> phist, vv <> cur, vv <> all, nl, ft)

# what row_go proves
def row.ty(
  +rr: List<&2, U32>,
  +xx: U32,
  +ft: L1.Ft,
  +bpp: U32,
  +stride: U32,
  +nr: Nat,
  +prest: List<&2, U32>,
  +phist: List<&2, U32>,
  +cur: List<&2, U32>,
  +all: List<&2, U32>,
  +left: U32,
  +zz: Bool,
  +tail: List<&2, U32>
) -> Type:
  {row.code(List.append(&2, U32, L1.flt.row(xx <> rr, ft, bpp, prest, cur, phist), tail), zz, bpp, stride, nr, prest,
    phist, cur, all, left, ft) == row.done(tail, bpp, stride, nr, cur, all, xx <> rr) : Maybe<&2, List<&2, U32>>}

# unfilter reads one filtered row back: from byte xx with rr after it and
# `left` counting rr, it reaches the next filter byte with the row read
law row_go:
  for +rr: List<&2, U32>
  for +xx: U32
  for +ft: L1.Ft
  for +bpp: U32
  for +stride: U32
  for +nr: Nat
  for +prest: List<&2, U32>
  for +phist: List<&2, U32>
  for +cur: List<&2, U32>
  for +all: List<&2, U32>
  for +left: U32
  for zz: Bool
  for ez: {U32.is_zero(left) == zz : Bool}
  for +ok: Bool
  for h_row: {L1.flt.bytes(xx <> rr, 1n+U32.to_nat(left), ok) == True{} : Bool}
  for +tail: List<&2, U32>
  row.ty(rr, xx, ft, bpp, stride, nr, prest, phist, cur, all, left, zz, tail)

# the proof of row_go
def row_go(rr, xx, ft, bpp, stride, nr, prest, phist, cur, all, left, zz, ez, ok, h_row, tail):
  match rr zz:
    case Nil{} True{}:
      +e0 = u32_zero_nat(left, ez)
      +h0 = Equal.trans(Bool, L1.flt.bytes(xx <> Nil{}, 1n, ok), L1.flt.bytes(xx <> Nil{}, 1n+U32.to_nat(left), ok),
        True{},
        Equal.sym(Bool, L1.flt.bytes(xx <> Nil{}, 1n+U32.to_nat(left), ok), L1.flt.bytes(xx <> Nil{}, 1n, ok),
          Equal.cong(Nat, Bool, nn => L1.flt.bytes(xx <> Nil{}, 1n+nn, ok), U32.to_nat(left), 0n, e0)),
        h_row)
      Equal.cong(U32, Maybe<&2, List<&2, U32>>,
        vv => Png.uf.go(tail, Png.UFilt{}, False{}, bpp, stride, nr, List.reverse(&2, U32, vv <> cur), [], [],
          vv <> all, 0, 0),
        Png.uf.recon(U32.and(255, U32.sub(xx, pred.at(ft, bpp, prest, phist, cur))), L1.ft.code(ft), bpp, prest,
          phist, cur), xx,
        recon_eq(ft, bpp, xx, prest, phist, cur, M1.and_right(ok, U32.is_lt(xx, 256), h0)))
    case Nil{} False{}:
      +en = flt.u32_dec(left, ez)
      Empty.absurd(row.ty(Nil{}, xx, ft, bpp, stride, nr, prest, phist, cur, all, left, False{}, tail),
        M1.false_true(Equal.trans(Bool, False{}, L1.flt.bytes(xx <> Nil{}, 1n+U32.to_nat(left), ok), True{},
          Equal.sym(Bool, L1.flt.bytes(xx <> Nil{}, 1n+U32.to_nat(left), ok), False{},
            Equal.cong(Nat, Bool, nn => L1.flt.bytes(xx <> Nil{}, 1n+nn, ok), U32.to_nat(left),
              1n+U32.to_nat(U32.sub(left, 1)), en)),
          h_row)))
    case +yy <> +rest True{}:
      +e0 = u32_zero_nat(left, ez)
      Empty.absurd(row.ty(yy <> rest, xx, ft, bpp, stride, nr, prest, phist, cur, all, left, True{}, tail),
        M1.false_true(Equal.trans(Bool, False{}, L1.flt.bytes(xx <> yy <> rest, 1n+U32.to_nat(left), ok), True{},
          Equal.sym(Bool, L1.flt.bytes(xx <> yy <> rest, 1n+U32.to_nat(left), ok), False{},
            Equal.cong(Nat, Bool, nn => L1.flt.bytes(xx <> yy <> rest, 1n+nn, ok), U32.to_nat(left), 0n, e0)),
          h_row)))
    case +yy <> +rest False{}:
      +nl = U32.sub(left, 1)
      +en = flt.u32_dec(left, ez)
      +ok2 = Bool.and(ok, U32.is_lt(xx, 256))
      +h1 = Equal.trans(Bool, L1.flt.bytes(yy <> rest, 1n+U32.to_nat(nl), ok2),
        L1.flt.bytes(xx <> yy <> rest, 1n+U32.to_nat(left), ok), True{},
        Equal.sym(Bool, L1.flt.bytes(xx <> yy <> rest, 1n+U32.to_nat(left), ok),
          L1.flt.bytes(yy <> rest, 1n+U32.to_nat(nl), ok2),
          Equal.cong(Nat, Bool, nn => L1.flt.bytes(xx <> yy <> rest, 1n+nn, ok), U32.to_nat(left),
            1n+U32.to_nat(nl), en)),
        h_row)
      +h_lt = M1.and_right(ok, U32.is_lt(xx, 256), bytes_acc(yy <> rest, 1n+U32.to_nat(nl), ok2, h1))
      +xs = List.append(&2, U32, L1.flt.row(yy <> rest, ft, bpp, L1.flt.next(prest), xx <> cur,
        L1.flt.up(prest) <> phist), tail)
      +zn = U32.is_zero(nl)
      +yv = Png.uf.recon(U32.and(255, U32.sub(xx, pred.at(ft, bpp, prest, phist, cur))), L1.ft.code(ft), bpp, prest,
        phist, cur)
      Equal.trans(Maybe<&2, List<&2, U32>>,
        row.mid(xs, zn, bpp, stride, nr, Png.uf.drop(prest), Png.uf.bb(prest), phist, yv, cur, all, nl, ft),
        row.mid(xs, zn, bpp, stride, nr, Png.uf.drop(prest), Png.uf.bb(prest), phist, xx, cur, all, nl, ft),
        row.done(tail, bpp, stride, nr, cur, all, xx <> yy <> rest),
        Equal.cong(U32, Maybe<&2, List<&2, U32>>,
          vv => row.mid(xs, zn, bpp, stride, nr, Png.uf.drop(prest), Png.uf.bb(prest), phist, vv, cur, all, nl, ft),
          yv, xx, recon_eq(ft, bpp, xx, prest, phist, cur, h_lt)),
        Equal.trans(Maybe<&2, List<&2, U32>>,
          row.mid(xs, zn, bpp, stride, nr, Png.uf.drop(prest), Png.uf.bb(prest), phist, xx, cur, all, nl, ft),
          row.mid(xs, zn, bpp, stride, nr, L1.flt.next(prest), Png.uf.bb(prest), phist, xx, cur, all, nl, ft),
          row.done(tail, bpp, stride, nr, cur, all, xx <> yy <> rest),
          Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>,
            ll => row.mid(xs, zn, bpp, stride, nr, ll, Png.uf.bb(prest), phist, xx, cur, all, nl, ft),
            Png.uf.drop(prest), L1.flt.next(prest), drop_next(prest)),
          Equal.trans(Maybe<&2, List<&2, U32>>,
            row.mid(xs, zn, bpp, stride, nr, L1.flt.next(prest), Png.uf.bb(prest), phist, xx, cur, all, nl, ft),
            row.mid(xs, zn, bpp, stride, nr, L1.flt.next(prest), L1.flt.up(prest), phist, xx, cur, all, nl, ft),
            row.done(tail, bpp, stride, nr, cur, all, xx <> yy <> rest),
            Equal.cong(U32, Maybe<&2, List<&2, U32>>,
              vv => row.mid(xs, zn, bpp, stride, nr, L1.flt.next(prest), vv, phist, xx, cur, all, nl, ft),
              Png.uf.bb(prest), L1.flt.up(prest), bb_up(prest)),
            row_go(rest, yy, ft, bpp, stride, nr, L1.flt.next(prest), L1.flt.up(prest) <> phist, xx <> cur,
              xx <> all, nl, zn, {==}, ok2, h1, tail))))

# reversing xs ++ ys onto acc reverses xs, then ys
law rev_app:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +acc: List<&2, U32>
  {List.reverse.go(&2, U32, List.append(&2, U32, xs, ys), acc)
    == List.reverse.go(&2, U32, ys, List.reverse.go(&2, U32, xs, acc)) : List<&2, U32>}

# the proof of rev_app
def rev_app(xs, ys, acc):
  match xs:
    case Nil{}:
      {==}
    case +hd <> +tl:
      rev_app(tl, ys, hd <> acc)

# a true answer from flt.fit started from a true answer
law fit_acc:
  for +rows: List<&2, List<&2, U32>>
  for +nn: Nat
  for +ok: Bool
  for hh: {L1.flt.fit(rows, nn, ok) == True{} : Bool}
  {ok == True{} : Bool}

# the proof of fit_acc
def fit_acc(rows, nn, ok, hh):
  match rows:
    case Nil{}:
      hh
    case +row <> +rest:
      M1.and_left(ok, L1.flt.bytes(row, nn, True{}),
        fit_acc(rest, nn, Bool.and(ok, L1.flt.bytes(row, nn, True{})), hh))

# a filter type byte opens a row body
law phase_ok:
  for +ft: L1.Ft
  {Png.uf.phase(U32.is_le(L1.ft.code(ft), 4)) == Png.UBody{} : Png.Uf}

# the proof of phase_ok
def phase_ok(ft):
  match ft:
    case L1.FNone{}:
      {==}
    case L1.FSub{}:
      {==}
    case L1.FUp{}:
      {==}
    case L1.FAvg{}:
      {==}
    case L1.FPaeth{}:
      {==}

# one less, for Nats
def nat.dec(nn: Nat) -> Nat:
  match nn:
    case 0n:
      0n
    case 1n+pp:
      pp

# unfilter at a filter byte, in phase ph
def rows.ph(
  ph: Png.Uf,
  +xs: List<&2, U32>,
  +zz: Bool,
  +bpp: U32,
  +stride: U32,
  +nr: Nat,
  +prev: List<&2, U32>,
  +all: List<&2, U32>,
  +left: U32,
  +cd: U32
) -> Maybe<&2, List<&2, U32>>:
  Png.uf.go(xs, ph, zz, bpp, stride, nr, prev, [], [], all, left, cd)

# unfilter at a filter byte, with prev the row above
def rows.at(
  +xs: List<&2, U32>,
  +bpp: U32,
  +stride: U32,
  +nr: Nat,
  +prev: List<&2, U32>,
  +all: List<&2, U32>
) -> Maybe<&2, List<&2, U32>>:
  Png.uf.go(xs, Png.UFilt{}, False{}, bpp, stride, nr, prev, [], [], all, 0, 0)

# what rows_go proves
def rows.ty(
  +rows: List<&2, L1.Row>,
  +nr: Nat,
  +bpp: U32,
  +stride: U32,
  +prev: List<&2, U32>,
  +all: List<&2, U32>
) -> Type:
  {rows.at(L1.flt.rows(rows, bpp, prev), bpp, stride, nr, prev, all)
    == Some{List.reverse(&2, U32, List.reverse.go(&2, U32, List.concat(&2, U32, L1.flt.data(rows)), all))}
    : Maybe<&2, List<&2, U32>>}

# one row of rows_go, the rows after it given by the hypothesis ih
law rows.step:
  for +row: List<&2, U32>
  for +rest: List<&2, L1.Row>
  for +nr: Nat
  for +ft: L1.Ft
  for +bpp: U32
  for +stride: U32
  for en: {U32.is_zero(stride) == False{} : Bool}
  for h_row: {L1.flt.bytes(row, U32.to_nat(stride), True{}) == True{} : Bool}
  for +prev: List<&2, U32>
  for +all: List<&2, U32>
  for ih: rows.ty(rest, nr, bpp, stride, row, List.reverse.go(&2, U32, row, all))
  rows.ty(L1.Row{ft, row} <> rest, 1n+nr, bpp, stride, prev, all)

# the proof of rows.step
def rows.step(row, rest, nr, ft, bpp, stride, en, h_row, prev, all, ih):
  match row:
    case Nil{}:
      +es = flt.u32_dec(stride, en)
      Empty.absurd(rows.ty(L1.Row{ft, Nil{}} <> rest, 1n+nr, bpp, stride, prev, all),
        M1.false_true(Equal.trans(Bool, False{}, L1.flt.bytes(Nil{}, U32.to_nat(stride), True{}), True{},
          Equal.sym(Bool, L1.flt.bytes(Nil{}, U32.to_nat(stride), True{}), False{},
            Equal.cong(Nat, Bool, nn => L1.flt.bytes(Nil{}, nn, True{}), U32.to_nat(stride),
              1n+U32.to_nat(U32.sub(stride, 1)), es)),
          h_row)))
    case +xx <> +rr:
      +es = flt.u32_dec(stride, en)
      +sl = U32.sub(stride, 1)
      +h1 = Equal.trans(Bool, L1.flt.bytes(xx <> rr, 1n+U32.to_nat(sl), True{}),
        L1.flt.bytes(xx <> rr, U32.to_nat(stride), True{}), True{},
        Equal.sym(Bool, L1.flt.bytes(xx <> rr, U32.to_nat(stride), True{}),
          L1.flt.bytes(xx <> rr, 1n+U32.to_nat(sl), True{}),
          Equal.cong(Nat, Bool, nn => L1.flt.bytes(xx <> rr, nn, True{}), U32.to_nat(stride), 1n+U32.to_nat(sl),
            es)),
        h_row)
      +tail = L1.flt.rows(rest, bpp, xx <> rr)
      +xs = List.append(&2, U32, L1.flt.row(xx <> rr, ft, bpp, prev, [], []), tail)
      +zz = U32.is_zero(sl)
      +cd = L1.ft.code(ft)
      +acc = List.reverse.go(&2, U32, xx <> rr, all)
      +data = L1.flt.data(rest)
      +goal = {Some{List.reverse(&2, U32, List.reverse.go(&2, U32, List.concat(&2, U32, (xx <> rr) <> data), all))}
        : Maybe<&2, List<&2, U32>>}
      Equal.trans(Maybe<&2, List<&2, U32>>,
        rows.ph(Png.uf.phase(U32.is_le(cd, 4)), xs, zz, bpp, stride, nr, prev, all, sl, cd),
        rows.ph(Png.UBody{}, xs, zz, bpp, stride, nr, prev, all, sl, cd), goal,
        Equal.cong(Png.Uf, Maybe<&2, List<&2, U32>>, ph => rows.ph(ph, xs, zz, bpp, stride, nr, prev, all, sl, cd),
          Png.uf.phase(U32.is_le(cd, 4)), Png.UBody{}, phase_ok(ft)),
        Equal.trans(Maybe<&2, List<&2, U32>>,
          rows.ph(Png.UBody{}, xs, zz, bpp, stride, nr, prev, all, sl, cd),
          rows.at(tail, bpp, stride, nr, List.reverse(&2, U32, List.reverse.go(&2, U32, xx <> rr, [])), acc), goal,
          row_go(rr, xx, ft, bpp, stride, nr, prev, [], [], all, sl, zz, {==}, True{}, h1, tail),
          Equal.trans(Maybe<&2, List<&2, U32>>,
            rows.at(tail, bpp, stride, nr, List.reverse(&2, U32, List.reverse.go(&2, U32, xx <> rr, [])), acc),
            rows.at(tail, bpp, stride, nr, xx <> rr, acc), goal,
            Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, ll => rows.at(tail, bpp, stride, nr, ll, acc),
              List.reverse(&2, U32, List.reverse.go(&2, U32, xx <> rr, [])), xx <> rr, M1.flt.rev_rev(xx <> rr)),
            Equal.trans(Maybe<&2, List<&2, U32>>, rows.at(tail, bpp, stride, nr, xx <> rr, acc),
              Some{List.reverse(&2, U32, List.reverse.go(&2, U32, List.concat(&2, U32, data), acc))}, goal, ih,
              Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, ll => Some{List.reverse(&2, U32, ll)},
                List.reverse.go(&2, U32, List.concat(&2, U32, data), acc),
                List.reverse.go(&2, U32, List.concat(&2, U32, (xx <> rr) <> data), all),
                Equal.sym(List<&2, U32>, List.reverse.go(&2, U32, List.concat(&2, U32, (xx <> rr) <> data), all),
                  List.reverse.go(&2, U32, List.concat(&2, U32, data), acc),
                  rev_app(xx <> rr, List.concat(&2, U32, data), all)))))))

# unfilter reads every filtered row back: nr rows, each stride bytes below 256
law rows_go:
  for +rows: List<&2, L1.Row>
  for +nr: Nat
  for h_n: {List.length(&2, L1.Row, rows) == nr : Nat}
  for +bpp: U32
  for +stride: U32
  for +en: {U32.is_zero(stride) == False{} : Bool}
  for +ok: Bool
  for +h_fit: {L1.flt.fit(L1.flt.data(rows), U32.to_nat(stride), ok) == True{} : Bool}
  for +prev: List<&2, U32>
  for +all: List<&2, U32>
  rows.ty(rows, nr, bpp, stride, prev, all)

# the proof of rows_go
def rows_go(rows, nr, h_n, bpp, stride, en, ok, h_fit, prev, all):
  match rows nr:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+(+pp):
      Empty.absurd(rows.ty(Nil{}, 1n+pp, bpp, stride, prev, all), flt.zero_succ(pp, h_n))
    case +rw <> +rest 0n:
      Empty.absurd(rows.ty(rw <> rest, 0n, bpp, stride, prev, all),
        flt.zero_succ(List.length(&2, L1.Row, rest),
          Equal.sym(Nat, 1n+List.length(&2, L1.Row, rest), 0n, h_n)))
    case L1.Row{+ft, +row} <> +rest 1n+(+pp):
      +ok2 = Bool.and(ok, L1.flt.bytes(row, U32.to_nat(stride), True{}))
      rows.step(row, rest, pp, ft, bpp, stride, en,
        M1.and_right(ok, L1.flt.bytes(row, U32.to_nat(stride), True{}),
          fit_acc(L1.flt.data(rest), U32.to_nat(stride), ok2, h_fit)),
        prev, all,
        rows_go(rest, pp, Equal.cong(Nat, Nat, nn => nat.dec(nn), 1n+List.length(&2, L1.Row, rest), 1n+pp, h_n),
          bpp, stride, en, ok2, h_fit, row, List.reverse.go(&2, U32, row, all)))

# a U32 whose Nat is a successor is not zero, once is_zero's answer is named
law nz.of:
  for zz: Bool
  for +ss: U32
  for ez: {U32.is_zero(ss) == zz : Bool}
  for +kk: Nat
  for hh: {U32.to_nat(ss) == 1n+kk : Nat}
  {U32.is_zero(ss) == False{} : Bool}

# the proof of nz.of
def nz.of(zz, ss, ez, kk, hh):
  match zz:
    case False{}:
      ez
    case True{}:
      Empty.absurd({U32.is_zero(ss) == False{} : Bool},
        flt.zero_succ(kk, Equal.trans(Nat, 0n, U32.to_nat(ss), 1n+kk,
          Equal.sym(Nat, U32.to_nat(ss), 0n, u32_zero_nat(ss, ez)), hh)))

# a width and a bpp above 0 whose product fits give a nonzero stride
law stride_nz:
  for +ww: U32
  for +bpp: U32
  for h_ww: {U32.is_gt(ww, 0) == True{} : Bool}
  for h_bpp: {U32.is_gt(bpp, 0) == True{} : Bool}
  for h_wrap: {U32.to_nat(U32.mul(ww, bpp)) == Nat.mul(U32.to_nat(ww), U32.to_nat(bpp)) : Nat}
  {U32.is_zero(U32.mul(ww, bpp)) == False{} : Bool}

# the proof of stride_nz
def stride_nz(ww, bpp, h_ww, h_bpp, h_wrap):
  +na = U32.to_nat(U32.sub(ww, 1))
  +nb = U32.to_nat(U32.sub(bpp, 1))
  +ew = flt.u32_dec(ww, gt_nonzero(ww, h_ww))
  +eb = flt.u32_dec(bpp, gt_nonzero(bpp, h_bpp))
  nz.of(U32.is_zero(U32.mul(ww, bpp)), U32.mul(ww, bpp), {==}, Nat.add(nb, Nat.mul(na, 1n+nb)),
    Equal.trans(Nat, U32.to_nat(U32.mul(ww, bpp)), Nat.mul(U32.to_nat(ww), U32.to_nat(bpp)), Nat.mul(1n+na, 1n+nb),
      h_wrap,
      Equal.trans(Nat, Nat.mul(U32.to_nat(ww), U32.to_nat(bpp)), Nat.mul(1n+na, U32.to_nat(bpp)), Nat.mul(1n+na, 1n+nb),
        Equal.cong(Nat, Nat, nn => Nat.mul(nn, U32.to_nat(bpp)), U32.to_nat(ww), 1n+na, ew),
        Equal.cong(Nat, Nat, nn => Nat.mul(1n+na, nn), U32.to_nat(bpp), 1n+nb, eb))))

# unfilter past its size check, once the check's answer is named
law top.go:
  for zz: Bool
  for ez: {zz == True{} : Bool}
  for +ww: U32
  for +hh: U32
  for +bpp: U32
  for +rows: List<&2, L1.Row>
  for main: rows.ty(rows, U32.to_nat(hh), bpp, U32.mul(ww, bpp), [], [])
  {Png.uf.start(zz, L1.flt.rows(rows, bpp, []), ww, hh, bpp) == Some{List.concat(&2, U32, L1.flt.data(rows))}
    : Maybe<&2, List<&2, U32>>}

# the proof of top.go
def top.go(zz, ez, ww, hh, bpp, rows, main):
  match zz:
    case False{}:
      Empty.absurd({Png.uf.start(False{}, L1.flt.rows(rows, bpp, []), ww, hh, bpp) == Some{List.concat(&2, U32,
        L1.flt.data(rows))} : Maybe<&2, List<&2, U32>>}, M1.false_true(ez))
    case True{}:
      Equal.trans(Maybe<&2, List<&2, U32>>,
        rows.at(L1.flt.rows(rows, bpp, []), bpp, U32.mul(ww, bpp), U32.to_nat(hh), [], []),
        Some{List.reverse(&2, U32, List.reverse.go(&2, U32, List.concat(&2, U32, L1.flt.data(rows)), []))},
        Some{List.concat(&2, U32, L1.flt.data(rows))}, main,
        Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, ll => Some{ll},
          List.reverse(&2, U32, List.reverse.go(&2, U32, List.concat(&2, U32, L1.flt.data(rows)), [])),
          List.concat(&2, U32, L1.flt.data(rows)), M1.flt.rev_rev(List.concat(&2, U32, L1.flt.data(rows)))))

# unfilter.rows past its size check, once the check's answer is named
law top.rows:
  for zz: Bool
  for ez: {zz == True{} : Bool}
  for +stride: U32
  for +hh: U32
  for +bpp: U32
  for +rows: List<&2, L1.Row>
  for main: rows.ty(rows, U32.to_nat(hh), bpp, stride, [], [])
  {Png.uf.rows.at(zz, L1.flt.rows(rows, bpp, []), stride, hh, bpp) == Some{List.concat(&2, U32, L1.flt.data(rows))}
    : Maybe<&2, List<&2, U32>>}

# the proof of top.rows
def top.rows(zz, ez, stride, hh, bpp, rows, main):
  match zz:
    case False{}:
      Empty.absurd({Png.uf.rows.at(False{}, L1.flt.rows(rows, bpp, []), stride, hh, bpp) == Some{List.concat(&2, U32,
        L1.flt.data(rows))} : Maybe<&2, List<&2, U32>>}, M1.false_true(ez))
    case True{}:
      Equal.trans(Maybe<&2, List<&2, U32>>,
        rows.at(L1.flt.rows(rows, bpp, []), bpp, stride, U32.to_nat(hh), [], []),
        Some{List.reverse(&2, U32, List.reverse.go(&2, U32, List.concat(&2, U32, L1.flt.data(rows)), []))},
        Some{List.concat(&2, U32, L1.flt.data(rows))}, main,
        Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, ll => Some{ll},
          List.reverse(&2, U32, List.reverse.go(&2, U32, List.concat(&2, U32, L1.flt.data(rows)), [])),
          List.concat(&2, U32, L1.flt.data(rows)), M1.flt.rev_rev(List.concat(&2, U32, L1.flt.data(rows)))))

# the raw bytes enc.rgb.go's cursor has still to write, for a picture of
# rows wn samples wide: a filter byte first at a row's start, red while the
# sample is still in px, then green and blue of col
def cur(filt: Bool, zred: Bool, zgrn: Bool, px: List<&2, U32>, +col: U32, +row: U32, +wn: Nat) -> List<&2, U32>:
  match filt:
    case True{}:
      M1.sc(px, 0n, wn, True{})
    case False{}:
      match zred:
        case True{}:
          M1.sc(px, U32.to_nat(row), wn, True{})
        case False{}:
          match zgrn:
            case True{}:
              Png.enc.g(col) <> Png.enc.b(col) <> M1.sc(px, Png.enc.pred(U32.to_nat(row)), wn, True{})
            case False{}:
              Png.enc.b(col) <> M1.sc(px, Png.enc.pred(U32.to_nat(row)), wn, True{})

# rows_go from the law's hypotheses: the stride is not zero, and the fit is
# stated at the stride
def L1.unfilter_filter(ww, hh, bpp, rows, h_dims, h_wrap, h_rows, h_fit):
  +d_ww = M1.and_left(U32.is_gt(ww, 0), Bool.and(U32.is_gt(hh, 0), Bool.and(U32.is_gt(bpp, 0), U32.is_le(bpp, 4))),
    h_dims)
  +d_rest = M1.and_right(U32.is_gt(ww, 0), Bool.and(U32.is_gt(hh, 0), Bool.and(U32.is_gt(bpp, 0), U32.is_le(bpp, 4))),
    h_dims)
  +d_bpp = M1.and_left(U32.is_gt(bpp, 0), U32.is_le(bpp, 4),
    M1.and_right(U32.is_gt(hh, 0), Bool.and(U32.is_gt(bpp, 0), U32.is_le(bpp, 4)), d_rest))
  +en = stride_nz(ww, bpp, d_ww, d_bpp, h_wrap)
  +fit = Equal.trans(Bool, L1.flt.fit(L1.flt.data(rows), U32.to_nat(U32.mul(ww, bpp)), True{}),
    L1.flt.fit(L1.flt.data(rows), Nat.mul(U32.to_nat(ww), U32.to_nat(bpp)), True{}), True{},
    Equal.cong(Nat, Bool, nn => L1.flt.fit(L1.flt.data(rows), nn, True{}), U32.to_nat(U32.mul(ww, bpp)),
      Nat.mul(U32.to_nat(ww), U32.to_nat(bpp)), h_wrap),
    h_fit)
  top.go(Png.uf.ok(ww, hh, bpp), h_dims, ww, hh, bpp, rows,
    rows_go(rows, U32.to_nat(hh), h_rows, bpp, U32.mul(ww, bpp), en, True{}, fit, [], []))

def L1.unfilter_rows_filter(stride, hh, bpp, rows, h_dims, h_rows, h_fit):
  +en = gt_nonzero(stride, M1.and_left(U32.is_gt(stride, 0), Bool.and(U32.is_gt(hh, 0), Bool.and(U32.is_gt(bpp, 0),
    U32.is_le(bpp, 8))), h_dims))
  top.rows(L1.flt.dims.rows(stride, hh, bpp), h_dims, stride, hh, bpp, rows,
    rows_go(rows, U32.to_nat(hh), h_rows, bpp, stride, en, True{}, h_fit, [], []))
