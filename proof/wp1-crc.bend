# proof/wp1-crc: lemmas for IMG-PNG-5. Each is a law proved here, or a def
# whose type is the fact it proves; PROOF.bend imports this file, so the gate
# checks it.
import Base
import ../LAWS.bend as Laws
import ../src/crc.bend as Crc
import ../src/png.bend as Png
import ./u32.bend as U32L

# ---- the CRC-32 against the bitwise reference ----

# crc.bit is handed the low bit of the register it is about to shift: given
# that, its nn steps are the reference's nn bit steps
law bit_ref:
  for nn: Nat
  for odd: Bool
  for +cc: U32
  for +eo: {U32.is_eq((cc .&. 1 : U32), 1) == odd : Bool}
  {Crc.crc.bit(nn, odd, cc) == Laws.crc.ref.bits(nn, cc) : U32}

# the proof of bit_ref
def bit_ref(nn, odd, cc, eo):
  match nn odd cc:
    case 0n _odd _cc:
      {==}
    case 1n+pp True{} U32{+ww}:
      +cc = {U32{ww} : U32}
      +n1 = ((cc >> 1n : U32) .^. Crc.crc.poly() : U32)
      Equal.trans(U32, Crc.crc.bit(pp, U32.is_eq((n1 .&. 1 : U32), 1), n1), Laws.crc.ref.bits(pp, n1),
        Laws.crc.ref.bits(pp, Laws.crc.ref.step(cc)),
        bit_ref(pp, U32.is_eq((n1 .&. 1 : U32), 1), n1, {==}),
        Equal.cong(Bool, U32, bb => Laws.crc.ref.bits(pp, Laws.crc.ref.shift(bb, cc)), True{},
          U32.is_eq((cc .&. 1 : U32), 1), Equal.sym(Bool, U32.is_eq((cc .&. 1 : U32), 1), True{}, eo)))
    case 1n+pp False{} U32{+ww}:
      +cc = {U32{ww} : U32}
      +n0 = (cc >> 1n : U32)
      Equal.trans(U32, Crc.crc.bit(pp, U32.is_eq((n0 .&. 1 : U32), 1), n0), Laws.crc.ref.bits(pp, n0),
        Laws.crc.ref.bits(pp, Laws.crc.ref.step(cc)),
        bit_ref(pp, U32.is_eq((n0 .&. 1 : U32), 1), n0, {==}),
        Equal.cong(Bool, U32, bb => Laws.crc.ref.bits(pp, Laws.crc.ref.shift(bb, cc)), False{},
          U32.is_eq((cc .&. 1 : U32), 1), Equal.sym(Bool, U32.is_eq((cc .&. 1 : U32), 1), False{}, eo)))

# folding the bytes: the code's register is the reference's, byte by byte
law fold_ref:
  for xs: List<&2, U32>
  for +cc: U32
  {Crc.crc.fold(xs, cc) == Laws.crc.ref.fold(xs, cc) : U32}

# the proof of fold_ref
def fold_ref(xs, cc):
  match xs:
    case Nil{}:
      {==}
    case +bb <> tl:
      +xx = (cc .^. bb : U32)
      Equal.trans(U32, Crc.crc.fold(tl, Crc.crc.byte(cc, bb)), Laws.crc.ref.fold(tl, Crc.crc.byte(cc, bb)),
        Laws.crc.ref.fold(tl, Laws.crc.ref.byte(cc, bb)),
        fold_ref(tl, Crc.crc.byte(cc, bb)),
        Equal.cong(U32, U32, rr => Laws.crc.ref.fold(tl, rr), Crc.crc.byte(cc, bb), Laws.crc.ref.byte(cc, bb),
          bit_ref(8n, U32.is_eq((xx .&. 1 : U32), 1), xx, {==})))

# the CRC-32 is the reference's, the preset and the final xor alike
law crc32_ref:
  for xs: List<&2, U32>
  {Crc.crc32(xs) == Laws.crc.ref(xs) : U32}

# the proof of crc32_ref
def crc32_ref(xs):
  Equal.cong(U32, U32, cc => (cc .^. 4294967295 : U32), Crc.crc.fold(xs, 4294967295),
    Laws.crc.ref.fold(xs, 4294967295), fold_ref(xs, 4294967295))

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

# a double that is 0n is the double of 0n
law double_zero:
  for +nn: Nat
  for ee: {Nat.double(nn) == 0n : Nat}
  {nn == 0n : Nat}

# the proof of double_zero
def double_zero(nn, ee):
  match nn:
    case 0n:
      {==}
    case 1n+pp:
      Empty.absurd({1n+pp == 0n : Nat}, zero_succ(1n+Nat.double(pp), Equal.sym(Nat, 2n+Nat.double(pp), 0n, ee)))

# no double is 1n
law double_one:
  for +nn: Nat
  for ee: {Nat.double(nn) == 1n : Nat}
  Empty

# the proof of double_one
def double_one(nn, ee):
  match nn:
    case 0n:
      zero_succ(0n, ee)
    case 1n+pp:
      zero_succ(Nat.double(pp), Equal.sym(Nat, 1n+Nat.double(pp), 0n, succ_inj(1n+Nat.double(pp), 0n, ee)))

# a word worth 0n is the zero word
law word_zero:
  for nn: Nat
  for ww: Word(nn)
  for ee: {Word.to_nat(nn, ww) == 0n : Nat}
  {ww == Word.zero(nn) : Word(nn)}

# the proof of word_zero
def word_zero(nn, ww, ee):
  match nn:
    case 0n:
      match ww:
        case WNil{}:
          {==}
    case 1n+(+pp):
      match ww:
        case WCon{False{}, +tt}:
          Equal.cong(Word(pp), Word.Con<pp>, xw => WCon{False{}, xw}, tt, Word.zero(pp),
            word_zero(pp, tt, double_zero(Word.to_nat(pp, tt), ee)))
        case WCon{True{}, +tt}:
          Empty.absurd({WCon{True{}, tt} == WCon{False{}, Word.zero(pp)} : Word.Con<pp>},
            zero_succ(Nat.double(Word.to_nat(pp, tt)), Equal.sym(Nat, 1n+Nat.double(Word.to_nat(pp, tt)), 0n, ee)))

# a U32 worth 0n is 0
law u32_zero:
  for uu: U32
  for ee: {U32.to_nat(uu) == 0n : Nat}
  {uu == 0 : U32}

# the proof of u32_zero
def u32_zero(uu, ee):
  match uu:
    case U32{ww}:
      Equal.cong(Word(32n), U32, xw => U32{xw}, ww, Word.zero(32n), word_zero(32n, ww, ee))

# a U32 worth 1n is 1
law u32_one:
  for uu: U32
  for ee: {U32.to_nat(uu) == 1n : Nat}
  {uu == 1 : U32}

# the proof of u32_one
def u32_one(uu, ee):
  match uu:
    case U32{WCon{False{}, +tt}}:
      Empty.absurd({U32{WCon{False{}, tt}} == 1 : U32}, double_one(Word.to_nat(31n, tt), ee))
    case U32{WCon{True{}, +tt}}:
      Equal.cong(Word(31n), U32, xw => U32{WCon{True{}, xw}}, tt, Word.zero(31n),
        word_zero(31n, tt, double_zero(Word.to_nat(31n, tt), succ_inj(Nat.double(Word.to_nat(31n, tt)), 0n, ee))))

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
      +e0 = {U32L.ueq(uu, 0, ez) : {uu == 0 : U32}}
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

# ---- lists ----

# appending nothing
law append_nil:
  for xs: List<&2, U32>
  {List.append(&2, U32, xs, []) == xs : List<&2, U32>}

# the proof of append_nil
def append_nil(xs):
  match xs:
    case Nil{}:
      {==}
    case +hd <> tl:
      Equal.cong(List<&2, U32>, List<&2, U32>, ll => {hd <> ll : List<&2, U32>}, List.append(&2, U32, tl, []), tl,
        append_nil(tl))

# reversing a reversal onto acc: acc read back, then xs in order
law rev_rev:
  for xs: List<&2, U32>
  for +acc: List<&2, U32>
  for +ys: List<&2, U32>
  {List.reverse.go(&2, U32, List.reverse.go(&2, U32, xs, acc), ys)
    == List.reverse.go(&2, U32, acc, List.append(&2, U32, xs, ys)) : List<&2, U32>}

# the proof of rev_rev
def rev_rev(xs, acc, ys):
  match xs:
    case Nil{}:
      {==}
    case +hd <> tl:
      rev_rev(tl, hd <> acc, ys)

# ---- the chunk walker, Png.png.go ----

# the walker at a chunk's four CRC bytes, with rest after them
def at_crc(
  +s0: U32,
  +s1: U32,
  +s2: U32,
  +s3: U32,
  rest: List<&2, U32>,
  +typ: U32,
  crc: List<&2, U32>,
  data: List<&2, U32>,
  pg: Png.Pg
) -> Maybe<&2, Png.Pic>:
  Png.png.go(s0 <> s1 <> s2 <> s3 <> rest, Png.ZCrc{}, False{}, 0, typ, crc, data, pg)

# the last data byte: the count is 1, so the walker goes on to the CRC
law walk_last:
  for zl: Bool
  for +xx: U32
  for +ll: U32
  for +ez: {U32.is_eq(ll, 1) == zl : Bool}
  for +hn: {U32.to_nat(ll) == 1n : Nat}
  for +s0: U32
  for +s1: U32
  for +s2: U32
  for +s3: U32
  for +rest: List<&2, U32>
  for +typ: U32
  for +cacc: List<&2, U32>
  for +dacc: List<&2, U32>
  for +pg: Png.Pg
  {Png.png.go(xx <> s0 <> s1 <> s2 <> s3 <> rest, Png.ZDat{}, zl, ll, typ, cacc, dacc, pg)
    == at_crc(s0, s1, s2, s3, rest, typ, xx <> cacc, xx <> dacc, pg) : Maybe<&2, Png.Pic>}

# the proof of walk_last
def walk_last(zl, xx, ll, ez, hn, s0, s1, s2, s3, rest, typ, cacc, dacc, pg):
  match zl:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Png.png.go(xx <> s0 <> s1 <> s2 <> s3 <> rest, Png.ZDat{}, False{}, ll, typ, cacc, dacc, pg)
        == at_crc(s0, s1, s2, s3, rest, typ, xx <> cacc, xx <> dacc, pg) : Maybe<&2, Png.Pic>},
        true_false(Equal.trans(Bool, True{}, U32.is_eq(ll, 1), False{},
          Equal.cong(U32, Bool, xu => U32.is_eq(xu, 1), 1, ll, Equal.sym(U32, ll, 1, u32_one(ll, hn))), ez)))

# a data byte before the last: the count is 2 or more, so the walker counts
# down by one and reads the next byte as data
law walk_step:
  for zl: Bool
  for +t2: List<&2, U32>
  for +xx: U32
  for +yy: U32
  for +ll: U32
  for +ez: {U32.is_eq(ll, 1) == zl : Bool}
  for +hn: {U32.to_nat(ll) == 2n+List.length(&2, U32, t2) : Nat}
  for +s0: U32
  for +s1: U32
  for +s2: U32
  for +s3: U32
  for +rest: List<&2, U32>
  for +typ: U32
  for +cacc: List<&2, U32>
  for +dacc: List<&2, U32>
  for +pg: Png.Pg
  {Png.png.go(xx <> yy <> List.append(&2, U32, t2, s0 <> s1 <> s2 <> s3 <> rest), Png.ZDat{}, zl, ll, typ, cacc,
    dacc, pg) == Png.png.go(yy <> List.append(&2, U32, t2, s0 <> s1 <> s2 <> s3 <> rest), Png.ZDat{},
    U32.is_eq(U32.sub(ll, 1), 1), U32.sub(ll, 1), typ, xx <> cacc, xx <> dacc, pg) : Maybe<&2, Png.Pic>}

# the proof of walk_step
def walk_step(zl, t2, xx, yy, ll, ez, hn, s0, s1, s2, s3, rest, typ, cacc, dacc, pg):
  match zl:
    case True{}:
      +e1 = {U32L.ueq(ll, 1, ez) : {ll == 1 : U32}}
      Empty.absurd({Png.png.go(xx <> yy <> List.append(&2, U32, t2, s0 <> s1 <> s2 <> s3 <> rest), Png.ZDat{}, True{},
        ll, typ, cacc, dacc, pg) == Png.png.go(yy <> List.append(&2, U32, t2, s0 <> s1 <> s2 <> s3 <> rest),
        Png.ZDat{}, U32.is_eq(U32.sub(ll, 1), 1), U32.sub(ll, 1), typ, xx <> cacc, xx <> dacc, pg)
        : Maybe<&2, Png.Pic>}, zero_succ(List.length(&2, U32, t2), succ_inj(0n, 1n+List.length(&2, U32, t2),
        Equal.trans(Nat, 1n, U32.to_nat(ll), 2n+List.length(&2, U32, t2),
          Equal.cong(U32, Nat, xu => U32.to_nat(xu), 1, ll, Equal.sym(U32, ll, 1, e1)), hn))))
    case False{}:
      match t2:
        case Nil{}:
          {==}
        case _zz <> Nil{}:
          {==}
        case _zz <> _ww <> _t4:
          {==}

# the data bytes from the first: a count of one more than the bytes after xx
# walks every byte and stops at the CRC, each byte pushed onto both lists
law walk_dat:
  for tt: List<&2, U32>
  for +xx: U32
  for +ll: U32
  for +hn: {U32.to_nat(ll) == 1n+List.length(&2, U32, tt) : Nat}
  for +s0: U32
  for +s1: U32
  for +s2: U32
  for +s3: U32
  for +rest: List<&2, U32>
  for +typ: U32
  for +cacc: List<&2, U32>
  for +dacc: List<&2, U32>
  for +pg: Png.Pg
  {Png.png.go(xx <> List.append(&2, U32, tt, s0 <> s1 <> s2 <> s3 <> rest), Png.ZDat{}, U32.is_eq(ll, 1), ll, typ,
    cacc, dacc, pg) == at_crc(s0, s1, s2, s3, rest, typ, List.reverse.go(&2, U32, tt, xx <> cacc),
    List.reverse.go(&2, U32, tt, xx <> dacc), pg) : Maybe<&2, Png.Pic>}

# the proof of walk_dat
def walk_dat(tt, xx, ll, hn, s0, s1, s2, s3, rest, typ, cacc, dacc, pg):
  match tt:
    case Nil{}:
      walk_last(U32.is_eq(ll, 1), xx, ll, {==}, hn, s0, s1, s2, s3, rest, typ, cacc, dacc, pg)
    case +yy <> +t2:
      Equal.trans(Maybe<&2, Png.Pic>,
        Png.png.go(xx <> yy <> List.append(&2, U32, t2, s0 <> s1 <> s2 <> s3 <> rest), Png.ZDat{}, U32.is_eq(ll, 1),
          ll, typ, cacc, dacc, pg),
        Png.png.go(yy <> List.append(&2, U32, t2, s0 <> s1 <> s2 <> s3 <> rest), Png.ZDat{},
          U32.is_eq(U32.sub(ll, 1), 1), U32.sub(ll, 1), typ, xx <> cacc, xx <> dacc, pg),
        at_crc(s0, s1, s2, s3, rest, typ, List.reverse.go(&2, U32, t2, yy <> xx <> cacc),
          List.reverse.go(&2, U32, t2, yy <> xx <> dacc), pg),
        walk_step(U32.is_eq(ll, 1), t2, xx, yy, ll, {==}, hn, s0, s1, s2, s3, rest, typ, cacc, dacc, pg),
        walk_dat(t2, yy, U32.sub(ll, 1), u32_pred(ll, 1n+List.length(&2, U32, t2), hn), s0, s1, s2, s3, rest, typ,
          xx <> cacc, xx <> dacc, pg))

# a chunk's data from the state the type bytes leave: a count equal to the
# number of data bytes walks them all and stops at the CRC
law walk_data:
  for +data: List<&2, U32>
  for +ll: U32
  for +hn: {U32.to_nat(ll) == List.length(&2, U32, data) : Nat}
  for +s0: U32
  for +s1: U32
  for +s2: U32
  for +s3: U32
  for +rest: List<&2, U32>
  for +typ: U32
  for +cacc: List<&2, U32>
  for +dacc: List<&2, U32>
  for +pg: Png.Pg
  {Png.png.go(List.append(&2, U32, data, s0 <> s1 <> s2 <> s3 <> rest), Png.png.zp(U32.is_zero(ll)),
    U32.is_eq(ll, 1), ll, typ, cacc, dacc, pg) == at_crc(s0, s1, s2, s3, rest, typ,
    List.reverse.go(&2, U32, data, cacc), List.reverse.go(&2, U32, data, dacc), pg) : Maybe<&2, Png.Pic>}

# the proof of walk_data
def walk_data(data, ll, hn, s0, s1, s2, s3, rest, typ, cacc, dacc, pg):
  match data:
    case Nil{}:
      Equal.cong(U32, Maybe<&2, Png.Pic>, xu => Png.png.go(s0 <> s1 <> s2 <> s3 <> rest, Png.png.zp(U32.is_zero(xu)),
        U32.is_eq(xu, 1), xu, typ, cacc, dacc, pg), ll, 0, u32_zero(ll, hn))
    case +xx <> +tt:
      Equal.trans(Maybe<&2, Png.Pic>,
        Png.png.go(xx <> List.append(&2, U32, tt, s0 <> s1 <> s2 <> s3 <> rest), Png.png.zp(U32.is_zero(ll)),
          U32.is_eq(ll, 1), ll, typ, cacc, dacc, pg),
        Png.png.go(xx <> List.append(&2, U32, tt, s0 <> s1 <> s2 <> s3 <> rest), Png.ZDat{}, U32.is_eq(ll, 1), ll,
          typ, cacc, dacc, pg),
        at_crc(s0, s1, s2, s3, rest, typ, List.reverse.go(&2, U32, tt, xx <> cacc),
          List.reverse.go(&2, U32, tt, xx <> dacc), pg),
        Equal.cong(Bool, Maybe<&2, Png.Pic>,
          bb => Png.png.go(xx <> List.append(&2, U32, tt, s0 <> s1 <> s2 <> s3 <> rest), Png.png.zp(bb),
            U32.is_eq(ll, 1), ll, typ, cacc, dacc, pg), U32.is_zero(ll), False{},
          u32_nonzero(ll, List.length(&2, U32, tt), hn)),
        walk_dat(tt, xx, ll, hn, s0, s1, s2, s3, rest, typ, cacc, dacc, pg))

# a whole chunk from its length bytes: when the length field counts the data
# bytes, the walker reaches the CRC with the type and data behind it
law walk_chunk:
  for +l0: U32
  for +l1: U32
  for +l2: U32
  for +l3: U32
  for +t0: U32
  for +t1: U32
  for +t2: U32
  for +t3: U32
  for +data: List<&2, U32>
  for +s0: U32
  for +s1: U32
  for +s2: U32
  for +s3: U32
  for +rest: List<&2, U32>
  for +pg: Png.Pg
  for +hn: {U32.to_nat(Png.be.u32(l0, l1, l2, l3)) == List.length(&2, U32, data) : Nat}
  {Png.png.go(l0 <> l1 <> l2 <> l3 <> t0 <> t1 <> t2 <> t3 <> List.append(&2, U32, data, s0 <> s1 <> s2 <> s3 <> rest),
    Png.ZLen{}, False{}, 0, 0, [], [], pg) == at_crc(s0, s1, s2, s3, rest, Png.be.u32(t0, t1, t2, t3),
    List.reverse.go(&2, U32, data, [t3, t2, t1, t0]), List.reverse.go(&2, U32, data, []), pg) : Maybe<&2, Png.Pic>}

# the proof of walk_chunk
def walk_chunk(l0, l1, l2, l3, t0, t1, t2, t3, data, s0, s1, s2, s3, rest, pg, hn):
  walk_data(data, Png.be.u32(l0, l1, l2, l3), hn, s0, s1, s2, s3, rest, Png.be.u32(t0, t1, t2, t3), [t3, t2, t1, t0],
    [], pg)

# the bytes the walker's CRC covers, read back in order: type, then data
law crc_bytes:
  for +data: List<&2, U32>
  for +t0: U32
  for +t1: U32
  for +t2: U32
  for +t3: U32
  {List.reverse(&2, U32, List.reverse.go(&2, U32, data, [t3, t2, t1, t0]))
    == t0 <> t1 <> t2 <> t3 <> data : List<&2, U32>}

# the proof of crc_bytes
def crc_bytes(data, t0, t1, t2, t3):
  Equal.trans(List<&2, U32>, List.reverse(&2, U32, List.reverse.go(&2, U32, data, [t3, t2, t1, t0])),
    t0 <> t1 <> t2 <> t3 <> List.append(&2, U32, data, []), t0 <> t1 <> t2 <> t3 <> data,
    rev_rev(data, [t3, t2, t1, t0], []),
    Equal.cong(List<&2, U32>, List<&2, U32>, ll => {t0 <> t1 <> t2 <> t3 <> ll : List<&2, U32>},
      List.append(&2, U32, data, []), data, append_nil(data)))

# a judged chunk: a stored CRC unequal to the computed one is refused
law judge_bad:
  for zz: Bool
  for +got: U32
  for +want: U32
  for +ee: {U32.is_eq(got, want) == zz : Bool}
  for h_ne: {got == want : U32} -> Empty
  for +typ: U32
  for +data: List<&2, U32>
  for +pg: Png.Pg
  for +em: Bool
  for +rest: List<&2, U32>
  {Png.png.crc(Png.png.judge.at(zz, typ, data, pg), em, Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [],
    Png.png.pgof(Png.png.judge.at(zz, typ, data, pg)))) == None{} : Maybe<&2, Png.Pic>}

# the proof of judge_bad
def judge_bad(zz, got, want, ee, h_ne, typ, data, pg, em, rest):
  match zz:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({Png.png.crc(Png.png.judge.at(True{}, typ, data, pg), em, Png.png.go(rest, Png.ZLen{}, False{}, 0,
        0, [], [], Png.png.pgof(Png.png.judge.at(True{}, typ, data, pg)))) == None{} : Maybe<&2, Png.Pic>},
        h_ne(U32L.ueq(got, want, ee)))

# a chunk whose stored CRC differs from the CRC-32 of its type and data:
# once the walker reaches its CRC bytes, the decode is none
law crc_bad:
  for +data: List<&2, U32>
  for +t0: U32
  for +t1: U32
  for +t2: U32
  for +t3: U32
  for +s0: U32
  for +s1: U32
  for +s2: U32
  for +s3: U32
  for +rest: List<&2, U32>
  for +pg: Png.Pg
  for h_ne: {Png.be.u32(s0, s1, s2, s3) == Crc.crc32(t0 <> t1 <> t2 <> t3 <> data) : U32} -> Empty
  {at_crc(s0, s1, s2, s3, rest, Png.be.u32(t0, t1, t2, t3), List.reverse.go(&2, U32, data, [t3, t2, t1, t0]),
    List.reverse.go(&2, U32, data, []), pg) == None{} : Maybe<&2, Png.Pic>}

# the proof of crc_bad
def crc_bad(data, t0, t1, t2, t3, s0, s1, s2, s3, rest, pg, h_ne):
  +got = Png.be.u32(s0, s1, s2, s3)
  +want = Crc.crc32(List.reverse(&2, U32, List.reverse.go(&2, U32, data, [t3, t2, t1, t0])))
  judge_bad(U32.is_eq(got, want), got, want, {==},
    ee => h_ne(Equal.trans(U32, got, want, Crc.crc32(t0 <> t1 <> t2 <> t3 <> data), ee,
      Equal.cong(List<&2, U32>, U32, xs => Crc.crc32(xs),
        List.reverse(&2, U32, List.reverse.go(&2, U32, data, [t3, t2, t1, t0])), t0 <> t1 <> t2 <> t3 <> data,
        crc_bytes(data, t0, t1, t2, t3)))),
    Png.be.u32(t0, t1, t2, t3), List.reverse.go(&2, U32, data, []), pg, List.is_empty(&2, U32, rest), rest)

# a judged chunk with more bytes after it: whatever the judgement, the decode
# is none when the walk over the rest is none
law judge_more:
  for em: Bool
  for +he: {em == False{} : Bool}
  for nx: Png.Nx
  for +rest: List<&2, U32>
  for ih: {Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], Png.png.pgof(nx)) == None{} : Maybe<&2, Png.Pic>}
  {Png.png.crc(nx, em, Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], Png.png.pgof(nx)))
    == None{} : Maybe<&2, Png.Pic>}

# the proof of judge_more
def judge_more(em, he, nx, rest, ih):
  match em:
    case True{}:
      Empty.absurd({Png.png.crc(nx, True{}, Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], Png.png.pgof(nx)))
        == None{} : Maybe<&2, Png.Pic>}, true_false(he))
    case False{}:
      match nx:
        case Png.NBad{}:
          {==}
        case Png.NEnd{_pg}:
          {==}
        case Png.NMore{_pg}:
          ih

# ---- chunks as the laws lay them out ----

# a chunk's bytes are never empty
law chunk_full:
  for ck: Laws.Chunk
  for rest: List<&2, U32>
  {List.is_empty(&2, U32, Laws.chunk.onto(ck, rest)) == False{} : Bool}

# the proof of chunk_full
def chunk_full(ck, _rest):
  match ck:
    case Laws.Chunk{_l0, _l1, _l2, _l3, _t0, _t1, _t2, _t3, _data, _s0, _s1, _s2, _s3}:
      {==}

# chunks before a chunk are never empty
law chunks_full:
  for cs: List<&2, Laws.Chunk>
  for ck: Laws.Chunk
  for rest: List<&2, U32>
  {List.is_empty(&2, U32, Laws.chunks.onto(cs, Laws.chunk.onto(ck, rest))) == False{} : Bool}

# the proof of chunks_full
def chunks_full(cs, ck, rest):
  match cs:
    case Nil{}:
      chunk_full(ck, rest)
    case hd <> tl:
      chunk_full(hd, Laws.chunks.onto(tl, Laws.chunk.onto(ck, rest)))


# a chunk walked to its CRC and refused, the CRC it should store named sum
law walk_bad.at:
  for +l0: U32
  for +l1: U32
  for +l2: U32
  for +l3: U32
  for +t0: U32
  for +t1: U32
  for +t2: U32
  for +t3: U32
  for +data: List<&2, U32>
  for +s0: U32
  for +s1: U32
  for +s2: U32
  for +s3: U32
  for +rest: List<&2, U32>
  for +pg: Png.Pg
  for +hn: {U32.to_nat(Png.be.u32(l0, l1, l2, l3)) == List.length(&2, U32, data) : Nat}
  for +sum: U32
  for +es: {Crc.crc32(t0 <> t1 <> t2 <> t3 <> data) == sum : U32}
  for h_ne: {Png.be.u32(s0, s1, s2, s3) == sum : U32} -> Empty
  {Png.png.go(l0 <> l1 <> l2 <> l3 <> t0 <> t1 <> t2 <> t3 <> List.append(&2, U32, data, s0 <> s1 <> s2 <> s3 <> rest),
    Png.ZLen{}, False{}, 0, 0, [], [], pg) == None{} : Maybe<&2, Png.Pic>}

# the proof of walk_bad.at
def walk_bad.at(l0, l1, l2, l3, t0, t1, t2, t3, data, s0, s1, s2, s3, rest, pg, hn, sum, es, h_ne):
  Equal.trans(Maybe<&2, Png.Pic>,
    Png.png.go(l0 <> l1 <> l2 <> l3 <> t0 <> t1 <> t2 <> t3 <> List.append(&2, U32, data, s0 <> s1 <> s2 <> s3 <> rest),
      Png.ZLen{}, False{}, 0, 0, [], [], pg),
    at_crc(s0, s1, s2, s3, rest, Png.be.u32(t0, t1, t2, t3), List.reverse.go(&2, U32, data, [t3, t2, t1, t0]),
      List.reverse.go(&2, U32, data, []), pg),
    None{},
    walk_chunk(l0, l1, l2, l3, t0, t1, t2, t3, data, s0, s1, s2, s3, rest, pg, hn),
    crc_bad(data, t0, t1, t2, t3, s0, s1, s2, s3, rest, pg,
      ee => h_ne(Equal.trans(U32, Png.be.u32(s0, s1, s2, s3), Crc.crc32(t0 <> t1 <> t2 <> t3 <> data), sum, ee, es))))

# the bad chunk itself: walked to its CRC and refused
law walk_bad:
  for +bad: Laws.Chunk
  for +rest: List<&2, U32>
  for +pg: Png.Pg
  for h_bad: Laws.chunk.framed(bad)
  for h_crc: {Laws.chunk.stored(bad) == Laws.chunk.sum(bad) : U32} -> Empty
  {Png.png.go(Laws.chunk.onto(bad, rest), Png.ZLen{}, False{}, 0, 0, [], [], pg) == None{} : Maybe<&2, Png.Pic>}

# the proof of walk_bad
def walk_bad(bad, rest, pg, h_bad, h_crc):
  match bad:
    case Laws.Chunk{+l0, +l1, +l2, +l3, +t0, +t1, +t2, +t3, +data, +s0, +s1, +s2, +s3}:
      walk_bad.at(l0, l1, l2, l3, t0, t1, t2, t3, data, s0, s1, s2, s3, rest, pg, h_bad,
        Laws.chunk.sum(Laws.Chunk{l0, l1, l2, l3, t0, t1, t2, t3, data, s0, s1, s2, s3}),
        crc32_ref(t0 <> t1 <> t2 <> t3 <> data), h_crc)

# a chunk before the bad one: walked to its CRC and judged; whatever the
# judgement, more bytes follow, so the decode is none when the walk over them is
law walk_pass:
  for +ck: Laws.Chunk
  for +rest: List<&2, U32>
  for +pg: Png.Pg
  for h_ck: Laws.chunk.framed(ck)
  for +full: {List.is_empty(&2, U32, rest) == False{} : Bool}
  for ih: @pp: Png.Pg -> {Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], pp) == None{} : Maybe<&2, Png.Pic>}
  {Png.png.go(Laws.chunk.onto(ck, rest), Png.ZLen{}, False{}, 0, 0, [], [], pg) == None{} : Maybe<&2, Png.Pic>}

# the proof of walk_pass
def walk_pass(ck, rest, pg, h_ck, full, ih):
  match ck:
    case Laws.Chunk{+l0, +l1, +l2, +l3, +t0, +t1, +t2, +t3, +data, +s0, +s1, +s2, +s3}:
      +nx = {Png.png.judge(Png.be.u32(s0, s1, s2, s3), List.reverse.go(&2, U32, data, [t3, t2, t1, t0]),
        Png.be.u32(t0, t1, t2, t3), List.reverse.go(&2, U32, data, []), pg) : Png.Nx}
      Equal.trans(Maybe<&2, Png.Pic>,
        Png.png.go(Laws.chunk.onto(Laws.Chunk{l0, l1, l2, l3, t0, t1, t2, t3, data, s0, s1, s2, s3}, rest),
          Png.ZLen{}, False{}, 0, 0, [], [], pg),
        at_crc(s0, s1, s2, s3, rest, Png.be.u32(t0, t1, t2, t3), List.reverse.go(&2, U32, data, [t3, t2, t1, t0]),
          List.reverse.go(&2, U32, data, []), pg),
        None{},
        walk_chunk(l0, l1, l2, l3, t0, t1, t2, t3, data, s0, s1, s2, s3, rest, pg, h_ck),
        judge_more(List.is_empty(&2, U32, rest), full, nx, rest, ih(Png.png.pgof(nx))))

# every chunk before the bad one: walked to its CRC, and then either refused,
# ended with bytes still to come, or on to the next chunk
law walk_all:
  for +pre: List<&2, Laws.Chunk>
  for +bad: Laws.Chunk
  for +rest: List<&2, U32>
  for +pg: Png.Pg
  for h_pre: Laws.chunks.framed(pre)
  for h_bad: Laws.chunk.framed(bad)
  for h_crc: {Laws.chunk.stored(bad) == Laws.chunk.sum(bad) : U32} -> Empty
  {Png.png.go(Laws.chunks.onto(pre, Laws.chunk.onto(bad, rest)), Png.ZLen{}, False{}, 0, 0, [], [], pg)
    == None{} : Maybe<&2, Png.Pic>}

# the proof of walk_all
def walk_all(pre, bad, rest, pg, h_pre, h_bad, h_crc):
  match pre:
    case Nil{}:
      walk_bad(bad, rest, pg, h_bad, h_crc)
    case +ck <> +tl:
      (h_ck, h_tl) = h_pre
      walk_pass(ck, Laws.chunks.onto(tl, Laws.chunk.onto(bad, rest)), pg, h_ck, chunks_full(tl, bad, rest),
        pp => walk_all(tl, bad, rest, pp, h_tl, h_bad, h_crc))
