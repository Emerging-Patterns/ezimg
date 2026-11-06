# the CRC-32 against the bitwise reference, and the bytes the chunk CRC covers
import Base
import ../../src/crc.bend as Crc
import ../../src/png.bend as Png
import ../../laws/defs/PngSpecification.bend as D1
import ./BasicFacts.bend as M1

# ---- the CRC-32 against the bitwise reference ----

# crc.bit is handed the low bit of the register it is about to shift: given
# that, its nn steps are the reference's nn bit steps
law bit_ref:
  for nn: Nat
  for odd: Bool
  for +cc: U32
  for +eo: {U32.is_eq((cc .&. 1 : U32), 1) == odd : Bool}
  {Crc.crc.bit(nn, odd, cc) == D1.crc.ref.bits(nn, cc) : U32}

# the proof of bit_ref
def bit_ref(nn, odd, cc, eo):
  match nn odd cc:
    case 0n _odd _cc:
      {==}
    case 1n+pp True{} U32{+ww}:
      +cc = {U32{ww} : U32}
      +n1 = ((cc >> 1n : U32) .^. Crc.crc.poly() : U32)
      Equal.trans(U32, Crc.crc.bit(pp, U32.is_eq((n1 .&. 1 : U32), 1), n1), D1.crc.ref.bits(pp, n1),
        D1.crc.ref.bits(pp, D1.crc.ref.step(cc)),
        bit_ref(pp, U32.is_eq((n1 .&. 1 : U32), 1), n1, {==}),
        Equal.cong(Bool, U32, bb => D1.crc.ref.bits(pp, D1.crc.ref.shift(bb, cc)), True{},
          U32.is_eq((cc .&. 1 : U32), 1), Equal.sym(Bool, U32.is_eq((cc .&. 1 : U32), 1), True{}, eo)))
    case 1n+pp False{} U32{+ww}:
      +cc = {U32{ww} : U32}
      +n0 = (cc >> 1n : U32)
      Equal.trans(U32, Crc.crc.bit(pp, U32.is_eq((n0 .&. 1 : U32), 1), n0), D1.crc.ref.bits(pp, n0),
        D1.crc.ref.bits(pp, D1.crc.ref.step(cc)),
        bit_ref(pp, U32.is_eq((n0 .&. 1 : U32), 1), n0, {==}),
        Equal.cong(Bool, U32, bb => D1.crc.ref.bits(pp, D1.crc.ref.shift(bb, cc)), False{},
          U32.is_eq((cc .&. 1 : U32), 1), Equal.sym(Bool, U32.is_eq((cc .&. 1 : U32), 1), False{}, eo)))

# folding the bytes: the code's register is the reference's, byte by byte
law fold_ref:
  for xs: List<&2, U32>
  for +cc: U32
  {Crc.crc.fold(xs, cc) == D1.crc.ref.fold(xs, cc) : U32}

# the proof of fold_ref
def fold_ref(xs, cc):
  match xs:
    case Nil{}:
      {==}
    case +bb <> tl:
      +xx = (cc .^. bb : U32)
      Equal.trans(U32, Crc.crc.fold(tl, Crc.crc.byte(cc, bb)), D1.crc.ref.fold(tl, Crc.crc.byte(cc, bb)),
        D1.crc.ref.fold(tl, D1.crc.ref.byte(cc, bb)),
        fold_ref(tl, Crc.crc.byte(cc, bb)),
        Equal.cong(U32, U32, rr => D1.crc.ref.fold(tl, rr), Crc.crc.byte(cc, bb), D1.crc.ref.byte(cc, bb),
          bit_ref(8n, U32.is_eq((xx .&. 1 : U32), 1), xx, {==})))

# the CRC-32 is the reference's, the preset and the final xor alike
law crc32_ref:
  for xs: List<&2, U32>
  {Crc.crc32(xs) == D1.crc.ref(xs) : U32}

# the proof of crc32_ref
def crc32_ref(xs):
  Equal.cong(U32, U32, cc => (cc .^. 4294967295 : U32), Crc.crc.fold(xs, 4294967295),
    D1.crc.ref.fold(xs, 4294967295), fold_ref(xs, 4294967295))

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
      Empty.absurd({1n+pp == 0n : Nat}, M1.zero_succ(1n+Nat.double(pp), Equal.sym(Nat, 2n+Nat.double(pp), 0n, ee)))

# no double is 1n
law double_one:
  for +nn: Nat
  for ee: {Nat.double(nn) == 1n : Nat}
  Empty

# the proof of double_one
def double_one(nn, ee):
  match nn:
    case 0n:
      M1.zero_succ(0n, ee)
    case 1n+pp:
      M1.zero_succ(Nat.double(pp), Equal.sym(Nat, 1n+Nat.double(pp), 0n, M1.succ_inj(1n+Nat.double(pp), 0n, ee)))

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
            M1.zero_succ(Nat.double(Word.to_nat(pp, tt)), Equal.sym(Nat, 1n+Nat.double(Word.to_nat(pp, tt)), 0n, ee)))

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
        word_zero(31n, tt, double_zero(Word.to_nat(31n, tt), M1.succ_inj(Nat.double(Word.to_nat(31n, tt)), 0n, ee))))

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
        M1.true_false(Equal.trans(Bool, True{}, U32.is_eq(ll, 1), False{},
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
      +e1 = {M1.ueq(ll, 1, ez) : {ll == 1 : U32}}
      Empty.absurd({Png.png.go(xx <> yy <> List.append(&2, U32, t2, s0 <> s1 <> s2 <> s3 <> rest), Png.ZDat{}, True{},
        ll, typ, cacc, dacc, pg) == Png.png.go(yy <> List.append(&2, U32, t2, s0 <> s1 <> s2 <> s3 <> rest),
        Png.ZDat{}, U32.is_eq(U32.sub(ll, 1), 1), U32.sub(ll, 1), typ, xx <> cacc, xx <> dacc, pg)
        : Maybe<&2, Png.Pic>}, M1.zero_succ(List.length(&2, U32, t2), M1.succ_inj(0n, 1n+List.length(&2, U32, t2),
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
        walk_dat(t2, yy, U32.sub(ll, 1), M1.u32_pred(ll, 1n+List.length(&2, U32, t2), hn), s0, s1, s2, s3, rest, typ,
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
          M1.u32_nonzero(ll, List.length(&2, U32, tt), hn)),
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
  for +hs: {Png.png.short(Png.be.u32(l0, l1, l2, l3)) == True{} : Bool}
  {Png.png.go(l0 <> l1 <> l2 <> l3 <> t0 <> t1 <> t2 <> t3 <> List.append(&2, U32, data, s0 <> s1 <> s2 <> s3 <> rest),
    Png.ZLen{}, False{}, 0, 0, [], [], pg) == at_crc(s0, s1, s2, s3, rest, Png.be.u32(t0, t1, t2, t3),
    List.reverse.go(&2, U32, data, [t3, t2, t1, t0]), List.reverse.go(&2, U32, data, []), pg) : Maybe<&2, Png.Pic>}

# the proof of walk_chunk: the length is below 2^31, so the walker reads the type
def walk_chunk(l0, l1, l2, l3, t0, t1, t2, t3, data, s0, s1, s2, s3, rest, pg, hn, hs):
  +ln = Png.be.u32(l0, l1, l2, l3)
  +body = {t0 <> t1 <> t2 <> t3 <> List.append(&2, U32, data, s0 <> s1 <> s2 <> s3 <> rest) : List<&2, U32>}
  Equal.trans(Maybe<&2, Png.Pic>,
    Png.png.go(l0 <> l1 <> l2 <> l3 <> body, Png.ZLen{}, False{}, 0, 0, [], [], pg),
    Png.png.go(body, Png.ZTyp{}, False{}, ln, 0, [], [], pg),
    at_crc(s0, s1, s2, s3, rest, Png.be.u32(t0, t1, t2, t3), List.reverse.go(&2, U32, data, [t3, t2, t1, t0]),
      List.reverse.go(&2, U32, data, []), pg),
    Equal.cong(Bool, Maybe<&2, Png.Pic>, zz => Png.png.len.ok(zz, _u => Png.png.go(body, Png.ZTyp{}, False{}, ln, 0, [],
      [], pg)), Png.png.short(ln), True{}, hs),
    walk_data(data, ln, hn, s0, s1, s2, s3, rest, Png.be.u32(t0, t1, t2, t3), [t3, t2, t1, t0], [], pg))

# a length field of 2^31 or more: the walker refuses the input there
law walk_long:
  for +l0: U32
  for +l1: U32
  for +l2: U32
  for +l3: U32
  for +rest: List<&2, U32>
  for +pg: Png.Pg
  for hs: {Png.png.short(Png.be.u32(l0, l1, l2, l3)) == False{} : Bool}
  {Png.png.go(l0 <> l1 <> l2 <> l3 <> rest, Png.ZLen{}, False{}, 0, 0, [], [], pg) == None{} : Maybe<&2, Png.Pic>}

# the proof of walk_long
def walk_long(l0, l1, l2, l3, rest, pg, hs):
  +ln = Png.be.u32(l0, l1, l2, l3)
  Equal.cong(Bool, Maybe<&2, Png.Pic>, zz => Png.png.len.ok(zz, _u => Png.png.go(rest, Png.ZTyp{}, False{}, ln, 0, [],
    [], pg)), Png.png.short(ln), False{}, hs)

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
