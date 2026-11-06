# proofs of laws/PngRoundTrips.bend
import Base
import ../main.bend as Img
import ../src/crc.bend as Crc
import ../src/inflate.bend as Inf
import ../src/png.bend as Png
import ../laws/InflateReadsStoredBlocks.bend as L1
import ../laws/PngRefusesBadRasters.bend as L2
import ../laws/PngRoundTrips.bend as Laws
import ../laws/PngSamplesFollowColourType.bend as L3
import ../laws/UnfilterUndoesFilter.bend as L4
import ../laws/defs/PngSpecification.bend as D1
import ../laws/defs/SizeBounds.bend as D2
import ./lemmas/BasicFacts.bend as M1
import ./lemmas/CrcReference.bend as M2
import ./lemmas/FilterReconstruction.bend as M3
import ./lemmas/PngChunkWalker.bend as M4
import ./lemmas/PngEncoderArithmetic.bend as M5
import ./lemmas/PngImageWalk.bend as M6
import ./lemmas/RowMajorIndex.bend as M7
import ./lemmas/StoredBlockEncoder.bend as M8
import ./lemmas/StoredBlockReader.bend as M9
import ./lemmas/SubtractionAndHuffmanWalk.bend as M10
import ./lemmas/WordAddition.bend as M11
import ./lemmas/ZlibStoredStream.bend as M12

# a + b - a is b
law sub_add_cancel:
  for aa: Nat
  for +bb: Nat
  {Nat.sub(Nat.add(aa, bb), aa) == bb : Nat}

# the proof of sub_add_cancel
def sub_add_cancel(aa, bb):
  match aa:
    case 0n:
      M10.sub_zero(bb)
    case 1n+pp:
      sub_add_cancel(pp, bb)

# ---- D. the encoder's file, laid out as spec.png ----

# adding zero with no carry in leaves a word
def adc.zero(pp: Nat, tt: Word(pp)) -> {Word.adc(pp, tt, Word.zero(pp), False{}, False{}) == tt : Word(pp)}:
  match pp:
    case 0n:
      match tt:
        case WNil{}:
          {==}
    case 1n+(+qq):
      match tt:
        case WCon{False{}, rest}:
          Equal.cong(Word(qq), Word.Con<qq>, ww => WCon{False{}, ww}, Word.adc(qq, rest, Word.zero(qq), False{},
            False{}), rest, adc.zero(qq, rest))
        case WCon{True{}, rest}:
          Equal.cong(Word(qq), Word.Con<qq>, ww => WCon{True{}, ww}, Word.adc(qq, rest, Word.zero(qq), False{},
            False{}),
            rest, adc.zero(qq, rest))

# adding zero with a carry in is the increment
def adc.carry(
  pp: Nat,
  tt: Word(pp)
) -> {Word.adc(pp, tt, Word.zero(pp), False{}, True{}) == Word.inc(pp, tt) : Word(pp)}:
  match pp:
    case 0n:
      match tt:
        case WNil{}:
          {==}
    case 1n+(+qq):
      match tt:
        case WCon{False{}, rest}:
          Equal.cong(Word(qq), Word.Con<qq>, ww => WCon{True{}, ww}, Word.adc(qq, rest, Word.zero(qq), False{},
            False{}), rest, adc.zero(qq, rest))
        case WCon{True{}, rest}:
          Equal.cong(Word(qq), Word.Con<qq>, ww => WCon{False{}, ww}, Word.adc(qq, rest, Word.zero(qq), False{},
            True{}),
            Word.inc(qq, rest), adc.carry(qq, rest))

# adding one is the increment
def add.one(uu: U32) -> {U32.add(uu, 1) == U32.inc(uu) : U32}:
  match uu:
    case U32{WCon{False{}, rest}}:
      Equal.cong(Word(31n), U32, ww => U32{WCon{True{}, ww}}, Word.adc(31n, rest, Word.zero(31n), False{}, False{}),
        rest, adc.zero(31n, rest))
    case U32{WCon{True{}, rest}}:
      Equal.cong(Word(31n), U32, ww => U32{WCon{False{}, ww}}, Word.adc(31n, rest, Word.zero(31n), False{}, True{}),
        Word.inc(31n, rest), adc.carry(31n, rest))

# counting a list in a word from k ends at k plus its length, taken in a word
def len.from(
  +xs: List<&2, U32>,
  +kk: Nat
) -> {Png.enc.len(xs, U32.from_nat(kk)) == U32.from_nat(Nat.add(kk, List.length(&2, U32, xs))) : U32}:
  match xs:
    case Nil{}:
      Equal.cong(Nat, U32, nn => U32.from_nat(nn), kk, Nat.add(kk, 0n), Equal.sym(Nat, Nat.add(kk, 0n), kk,
        M1.nat_add_zero(kk)))
    case _hd <> +tl:
      +lt = List.length(&2, U32, tl)
      Equal.trans(U32, Png.enc.len(tl, U32.add(U32.from_nat(kk), 1)), Png.enc.len(tl, U32.from_nat(1n+kk)),
        U32.from_nat(Nat.add(kk, 1n+lt)),
        Equal.cong(U32, U32, uu => Png.enc.len(tl, uu), U32.add(U32.from_nat(kk), 1), U32.from_nat(1n+kk),
          add.one(U32.from_nat(kk))),
        Equal.trans(U32, Png.enc.len(tl, U32.from_nat(1n+kk)), U32.from_nat(1n+Nat.add(kk, lt)),
          U32.from_nat(Nat.add(kk, 1n+lt)), len.from(tl, 1n+kk),
          Equal.cong(Nat, U32, nn => U32.from_nat(nn), 1n+Nat.add(kk, lt), Nat.add(kk, 1n+lt), Equal.sym(Nat,
            Nat.add(kk, 1n+lt), 1n+Nat.add(kk, lt), M1.nat_add_succ(kk, lt)))))

# the encoder's count of a list is its length, taken in a word
def len.word(+xs: List<&2, U32>) -> {Png.enc.len(xs, 0) == U32.from_nat(List.length(&2, U32, xs)) : U32}:
  len.from(xs, 0n)

# a chunk's bytes: length, type, data, CRC, then rest
def chunk.form(
  +nn: U32,
  +tb: List<&2, U32>,
  +data: List<&2, U32>,
  +crc: U32,
  +rest: List<&2, U32>
) -> List<&2, U32>:
  List.append(&2, U32, Png.enc.be(nn), List.append(&2, U32, tb, List.append(&2, U32, data, List.append(&2, U32,
    Png.enc.be(crc), rest))))

# the chunk enc.chunk writes, then rest, is spec.chunk's
def chunk.same(
  +tag: U32,
  +data: List<&2, U32>,
  +rest: List<&2, U32>
) -> {List.append(&2, U32, Png.enc.chunk(tag, data), rest) == D1.spec.chunk(Png.enc.be(tag), data, rest) :
  List<&2, U32>}:
  +tb = Png.enc.be(tag)
  +body = Png.enc.cat(tb, data)
  +crc = Crc.crc32(body)
  +ee = Png.enc.be(crc)
  +n0 = Png.enc.len(data, 0)
  Equal.trans(List<&2, U32>, List.append(&2, U32, Png.enc.chunk(tag, data), rest),
    chunk.form(n0, tb, data, crc, rest),
    D1.spec.chunk(tb, data, rest),
    Equal.trans(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, Png.enc.be(n0), Png.enc.cat(body, ee)), rest),
      List.append(&2, U32, List.append(&2, U32, Png.enc.be(n0), List.append(&2, U32, body, ee)), rest),
      chunk.form(n0, tb, data, crc, rest),
      Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.append(&2, U32, List.append(&2, U32, Png.enc.be(n0), ys),
        rest), Png.enc.cat(body, ee), List.append(&2, U32, body, ee), M8.cat_app(body, ee)),
      Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.append(&2, U32, Png.enc.be(n0), List.append(&2, U32, tb,
        ys)), List.append(&2, U32, List.append(&2, U32, data, ee), rest), List.append(&2, U32, data, List.append(&2,
        U32, ee, rest)), M1.app_assoc(data, ee, rest))),
    Equal.trans(List<&2, U32>, chunk.form(n0, tb, data, crc, rest),
      chunk.form(U32.from_nat(List.length(&2, U32, data)), tb, data, crc, rest),
      D1.spec.chunk(tb, data, rest),
      Equal.cong(U32, List<&2, U32>, uu => chunk.form(uu, tb, data, crc, rest), n0, U32.from_nat(List.length(&2, U32,
        data)), len.word(data)),
      Equal.cong(U32, List<&2, U32>, uu => chunk.form(U32.from_nat(List.length(&2, U32, data)), tb, data, uu, rest),
        crc, D1.crc.ref(List.append(&2, U32, tb, data)), M2.crc32_ref(List.append(&2, U32, tb, data)))))

# the file enc.seal.one lays out, for any IHDR data and zlib stream: the
# signature, IHDR, one IDAT and IEND, as spec.chunk lays them out. The data
# stays a variable here, so the checker never compares the IHDR CRC term
def seal.gen(
  +ihd: List<&2, U32>,
  +zz: List<&2, U32>
) -> {Png.enc.cat(Png.enc.sig(), Png.enc.cat(Png.enc.chunk(Png.tag.ihdr(), ihd),
  Png.enc.cat(Png.enc.chunk(Png.tag.idat(),
  zz), Png.enc.chunk(Png.tag.iend(), [])))) == List.append(&2, U32, Img.png_sig(), D1.spec.chunk([73, 72, 68, 82],
  ihd, D1.spec.chunk([73, 68, 65, 84], zz, D1.spec.chunk([73, 69, 78, 68], [], [])))) : List<&2, U32>}:
  +ih = Png.enc.chunk(Png.tag.ihdr(), ihd)
  +id = Png.enc.chunk(Png.tag.idat(), zz)
  +ie = Png.enc.chunk(Png.tag.iend(), [])
  +sig = Img.png_sig()
  +t_ih = Png.enc.be(Png.tag.ihdr())
  +t_id = Png.enc.be(Png.tag.idat())
  Equal.trans(List<&2, U32>, Png.enc.cat(Png.enc.sig(), Png.enc.cat(ih, Png.enc.cat(id, ie))),
    List.append(&2, U32, sig, List.append(&2, U32, ih, List.append(&2, U32, id, ie))),
    List.append(&2, U32, sig, D1.spec.chunk(t_ih, ihd, D1.spec.chunk(t_id, zz, ie))),
    Equal.trans(List<&2, U32>, Png.enc.cat(Png.enc.sig(), Png.enc.cat(ih, Png.enc.cat(id, ie))),
      List.append(&2, U32, sig, List.append(&2, U32, ih, Png.enc.cat(id, ie))),
      List.append(&2, U32, sig, List.append(&2, U32, ih, List.append(&2, U32, id, ie))),
      Equal.cong(List<&2, U32>, List<&2, U32>, ys => Png.enc.cat(Png.enc.sig(), ys), Png.enc.cat(ih, Png.enc.cat(id,
        ie)), List.append(&2, U32, ih, Png.enc.cat(id, ie)), M8.cat_app(ih, Png.enc.cat(id, ie))),
      Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.append(&2, U32, sig, List.append(&2, U32, ih, ys)),
        Png.enc.cat(id, ie), List.append(&2, U32, id, ie), M8.cat_app(id, ie))),
    Equal.trans(List<&2, U32>, List.append(&2, U32, sig, List.append(&2, U32, ih, List.append(&2, U32, id, ie))),
      List.append(&2, U32, sig, D1.spec.chunk(t_ih, ihd, List.append(&2, U32, id, ie))),
      List.append(&2, U32, sig, D1.spec.chunk(t_ih, ihd, D1.spec.chunk(t_id, zz, ie))),
      Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.append(&2, U32, sig, ys), List.append(&2, U32, ih,
        List.append(&2, U32, id, ie)), D1.spec.chunk(t_ih, ihd, List.append(&2, U32, id, ie)),
        chunk.same(Png.tag.ihdr(), ihd, List.append(&2, U32, id, ie))),
      Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.append(&2, U32, sig, D1.spec.chunk(t_ih, ihd, ys)),
        List.append(&2, U32, id, ie), D1.spec.chunk(t_id, zz, ie), chunk.same(Png.tag.idat(), zz, ie))))

# the file enc.seal.one writes is spec.png's, with no PLTE or tRNS and one IDAT
def seal.one.same(
  +ww: U32,
  +hh: U32,
  +op: Bool,
  +raw: List<&2, U32>,
  +nn: U32
) -> {Png.enc.seal.one(ww, hh, op, raw, nn) == D1.spec.png(ww, hh, Png.enc.ct(op), None{}, None{},
  [Png.enc.zlib(raw, nn)]) : List<&2, U32>}:
  seal.gen(Png.enc.ihdr(ww, hh, Png.enc.ct(op)), Png.enc.zlib(raw, nn))

# ---- E. the scanlines enc.raw writes, and their count ----

# adding a word to zero leaves the word
def adc.zl(pp: Nat, tt: Word(pp)) -> {Word.adc(pp, Word.zero(pp), tt, False{}, False{}) == tt : Word(pp)}:
  match pp:
    case 0n:
      match tt:
        case WNil{}:
          {==}
    case 1n+(+qq):
      match tt:
        case WCon{False{}, rest}:
          Equal.cong(Word(qq), Word.Con<qq>, ww => WCon{False{}, ww}, Word.adc(qq, Word.zero(qq), rest, False{},
            False{}), rest, adc.zl(qq, rest))
        case WCon{True{}, rest}:
          Equal.cong(Word(qq), Word.Con<qq>, ww => WCon{True{}, ww}, Word.adc(qq, Word.zero(qq), rest, False{},
            False{}),
            rest, adc.zl(qq, rest))

# an incremented word added in is a carry in
def adc.inc(
  pp: Nat,
  +xx: Word(pp),
  +yy: Word(pp)
) -> {Word.adc(pp, Word.inc(pp, xx), yy, False{}, False{}) == Word.adc(pp, xx, yy, False{}, True{}) : Word(pp)}:
  match pp:
    case 0n:
      match xx yy:
        case WNil{} WNil{}:
          {==}
    case 1n+(+qq):
      match xx yy:
        case WCon{False{}, _xt} WCon{False{}, _yt}:
          {==}
        case WCon{False{}, _xt} WCon{True{}, _yt}:
          {==}
        case WCon{True{}, +xt} WCon{False{}, +yt}:
          Equal.cong(Word(qq), Word.Con<qq>, ww => WCon{False{}, ww}, Word.adc(qq, Word.inc(qq, xt), yt, False{},
            False{}), Word.adc(qq, xt, yt, False{}, True{}), adc.inc(qq, xt, yt))
        case WCon{True{}, +xt} WCon{True{}, +yt}:
          Equal.cong(Word(qq), Word.Con<qq>, ww => WCon{True{}, ww}, Word.adc(qq, Word.inc(qq, xt), yt, False{},
            False{}), Word.adc(qq, xt, yt, False{}, True{}), adc.inc(qq, xt, yt))

# a carry in is an increment of the sum
def adc.cin(
  pp: Nat,
  +xx: Word(pp),
  +yy: Word(pp)
) -> {Word.adc(pp, xx, yy, False{}, True{}) == Word.inc(pp, Word.adc(pp, xx, yy, False{}, False{})) : Word(pp)}:
  match pp:
    case 0n:
      match xx yy:
        case WNil{} WNil{}:
          {==}
    case 1n+(+qq):
      match xx yy:
        case WCon{False{}, _xt} WCon{False{}, _yt}:
          {==}
        case WCon{False{}, +xt} WCon{True{}, +yt}:
          Equal.cong(Word(qq), Word.Con<qq>, ww => WCon{False{}, ww}, Word.adc(qq, xt, yt, False{}, True{}),
            Word.inc(qq, Word.adc(qq, xt, yt, False{}, False{})), adc.cin(qq, xt, yt))
        case WCon{True{}, +xt} WCon{False{}, +yt}:
          Equal.cong(Word(qq), Word.Con<qq>, ww => WCon{False{}, ww}, Word.adc(qq, xt, yt, False{}, True{}),
            Word.inc(qq, Word.adc(qq, xt, yt, False{}, False{})), adc.cin(qq, xt, yt))
        case WCon{True{}, _xt} WCon{True{}, _yt}:
          {==}

# zero plus a U32 is the U32
def add.zl(uu: U32) -> {U32.add(0, uu) == uu : U32}:
  match uu:
    case U32{ww}:
      Equal.cong(Word(32n), U32, xx => U32{xx}, Word.adc(32n, Word.zero(32n), ww, False{}, False{}), ww, adc.zl(32n,
        ww))

# an incremented U32 added in: the sum incremented
def add.inc(+xx: U32, +yy: U32) -> {U32.add(U32.inc(xx), yy) == U32.inc(U32.add(xx, yy)) : U32}:
  match xx yy:
    case U32{+xw} U32{+yw}:
      Equal.cong(Word(32n), U32, ww => U32{ww}, Word.adc(32n, Word.inc(32n, xw), yw, False{}, False{}),
        Word.inc(32n, Word.adc(32n, xw, yw, False{}, False{})), Equal.trans(Word(32n), Word.adc(32n, Word.inc(32n, xw),
        yw, False{}, False{}), Word.adc(32n, xw, yw, False{}, True{}), Word.inc(32n, Word.adc(32n, xw, yw, False{},
        False{})), adc.inc(32n, xw, yw), adc.cin(32n, xw, yw)))

# two naturals taken in words and added: their sum taken in a word
def add.nat(aa: Nat, +bb: Nat) -> {U32.add(U32.from_nat(aa), U32.from_nat(bb)) == U32.from_nat(Nat.add(aa, bb)) : U32}:
  match aa:
    case 0n:
      add.zl(U32.from_nat(bb))
    case 1n+(+pp):
      Equal.trans(U32, U32.add(U32.inc(U32.from_nat(pp)), U32.from_nat(bb)), U32.inc(U32.add(U32.from_nat(pp),
        U32.from_nat(bb))), U32.inc(U32.from_nat(Nat.add(pp, bb))), add.inc(U32.from_nat(pp), U32.from_nat(bb)),
        Equal.cong(U32, U32, uu => U32.inc(uu), U32.add(U32.from_nat(pp), U32.from_nat(bb)), U32.from_nat(Nat.add(pp,
        bb)), add.nat(pp, bb)))

# enc.nch in a word is nchn
def nch.nat(op: Bool) -> {Png.enc.nch(op) == U32.from_nat(Laws.spec.nch(op)) : U32}:
  match op:
    case True{}:
      {==}
    case False{}:
      {==}

# a sample's channels, then more bytes: nchn more bytes
def len.chans(
  op: Bool,
  +cc: U32,
  +rest: List<&2, U32>
) -> {List.length(&2, U32, List.append(&2, U32, M1.chans(op, cc), rest)) == Nat.add(Laws.spec.nch(op), List.length(&2,
  U32, rest)) : Nat}:
  match op:
    case True{}:
      {==}
    case False{}:
      {==}

# enc.push is the channels reversed onto the accumulator
def push.rev(
  op: Bool,
  +cc: U32,
  +acc: List<&2, U32>
) -> {Png.enc.push(op, cc, acc) == List.reverse.go(&2, U32, M1.chans(op, cc), acc) : List<&2, U32>}:
  match op:
    case True{}:
      {==}
    case False{}:
      {==}

# the count enc.raw carries, from row position left
def prt.cnt(px: List<&2, U32>, left: Nat, +ww: Nat, +op: Bool, +nn: U32) -> U32:
  match px left:
    case Nil{} _left:
      nn
    case _cc <> tl 0n:
      prt.cnt(tl, Png.enc.pred(ww), ww, op, ((nn + 1 : U32) + Png.enc.nch(op) : U32))
    case _cc <> tl 1n+pp:
      prt.cnt(tl, pp, ww, op, (nn + Png.enc.nch(op) : U32))

# one sample's channels pushed: the bytes so far reversed onto them
def push.step(
  +op: Bool,
  +cc: U32,
  +rest: List<&2, U32>,
  +acc: List<&2, U32>
) -> {List.reverse.go(&2, U32, rest, Png.enc.push(op, cc, acc)) == List.reverse.go(&2, U32, List.append(&2, U32,
  M1.chans(op, cc), rest), acc) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, List.reverse.go(&2, U32, rest, Png.enc.push(op, cc, acc)), List.reverse.go(&2, U32, rest,
    List.reverse.go(&2, U32, M1.chans(op, cc), acc)), List.reverse.go(&2, U32, List.append(&2, U32, M1.chans(op, cc),
        rest),
    acc), Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.reverse.go(&2, U32, rest, ys), Png.enc.push(op, cc, acc),
    List.reverse.go(&2, U32, M1.chans(op, cc), acc), push.rev(op, cc, acc)), Equal.sym(List<&2, U32>,
        List.reverse.go(&2,
    U32, List.append(&2, U32, M1.chans(op, cc), rest), acc), List.reverse.go(&2, U32, rest, List.reverse.go(&2, U32,
    M1.chans(op, cc), acc)), M4.revgo_app(M1.chans(op, cc), rest, acc)))

# enc.raw: its bytes are sc's, after the accumulator, and its count is prt.cnt's
def raw.eq(
  +px: List<&2, U32>,
  left: Nat,
  +ww: Nat,
  +op: Bool,
  +acc: List<&2, U32>,
  +nn: U32
) -> {Png.enc.raw(px, left, ww, op, acc, nn) == (List.reverse(&2, U32, List.reverse.go(&2, U32, M1.sc(px, left, ww, op),
  acc)), prt.cnt(px, left, ww, op, nn)) : List<&2, U32> & U32}:
  match px left:
    case Nil{} _left:
      {==}
    case +cc <> +tl 0n:
      +a1 = Png.enc.push(op, cc, 0 <> acc)
      +n2 = ((nn + 1 : U32) + Png.enc.nch(op) : U32)
      +pw = Png.enc.pred(ww)
      +rest = M1.sc(tl, pw, ww, op)
      +ct = prt.cnt(tl, pw, ww, op, n2)
      Equal.trans(List<&2, U32> & U32, Png.enc.raw(tl, pw, ww, op, a1, n2),
        (List.reverse(&2, U32, List.reverse.go(&2, U32, rest, a1)), ct),
        (List.reverse(&2, U32, List.reverse.go(&2, U32, List.append(&2, U32, M1.chans(op, cc), rest), 0 <> acc)), ct),
        raw.eq(tl, pw, ww, op, a1, n2),
        Equal.cong(List<&2, U32>, List<&2, U32> & U32, xs => (List.reverse(&2, U32, xs), ct),
          List.reverse.go(&2, U32, rest, a1), List.reverse.go(&2, U32, List.append(&2, U32, M1.chans(op, cc), rest),
          0 <> acc), push.step(op, cc, rest, 0 <> acc)))
    case +cc <> +tl 1n+(+pp):
      +a1 = Png.enc.push(op, cc, acc)
      +n2 = (nn + Png.enc.nch(op) : U32)
      +rest = M1.sc(tl, pp, ww, op)
      +ct = prt.cnt(tl, pp, ww, op, n2)
      Equal.trans(List<&2, U32> & U32, Png.enc.raw(tl, pp, ww, op, a1, n2),
        (List.reverse(&2, U32, List.reverse.go(&2, U32, rest, a1)), ct),
        (List.reverse(&2, U32, List.reverse.go(&2, U32, List.append(&2, U32, M1.chans(op, cc), rest), acc)), ct),
        raw.eq(tl, pp, ww, op, a1, n2),
        Equal.cong(List<&2, U32>, List<&2, U32> & U32, xs => (List.reverse(&2, U32, xs), ct),
          List.reverse.go(&2, U32, rest, a1), List.reverse.go(&2, U32, List.append(&2, U32, M1.chans(op, cc), rest),
              acc),
          push.step(op, cc, rest, acc)))

# a count from k plus n, taken in a word, is k + n taken in a word
def cnt.add(
  +kk: Nat,
  +nn: Nat,
  +uu: U32,
  eu: {uu == U32.from_nat(nn) : U32}
) -> {U32.add(U32.from_nat(kk), uu) == U32.from_nat(Nat.add(kk, nn)) : U32}:
  Equal.trans(U32, U32.add(U32.from_nat(kk), uu), U32.add(U32.from_nat(kk), U32.from_nat(nn)),
    U32.from_nat(Nat.add(kk, nn)), Equal.cong(U32, U32, xx => U32.add(U32.from_nat(kk), xx), uu, U32.from_nat(nn), eu),
    add.nat(kk, nn))

# prt.cnt from k taken in a word ends at k plus the bytes sc writes, taken in a word
def cnt.word(
  +px: List<&2, U32>,
  left: Nat,
  +ww: Nat,
  +op: Bool,
  +kk: Nat
) -> {prt.cnt(px, left, ww, op, U32.from_nat(kk)) == U32.from_nat(Nat.add(kk, List.length(&2, U32, M1.sc(px, left, ww,
    op)))) :
  U32}:
  match px left:
    case Nil{} _left:
      Equal.cong(Nat, U32, nn => U32.from_nat(nn), kk, Nat.add(kk, 0n), Equal.sym(Nat, Nat.add(kk, 0n), kk,
        M1.nat_add_zero(kk)))
    case +cc <> +tl 0n:
      +pw = Png.enc.pred(ww)
      +rest = M1.sc(tl, pw, ww, op)
      +ll = List.length(&2, U32, rest)
      +k0 = Nat.add(kk, 1n)
      +k1 = Nat.add(k0, Laws.spec.nch(op))
      +u0 = U32.add(U32.from_nat(kk), 1)
      +e_n = {Equal.trans(U32, U32.add(u0, Png.enc.nch(op)), U32.add(U32.from_nat(k0), Png.enc.nch(op)),
        U32.from_nat(k1), Equal.cong(U32, U32, uu => U32.add(uu, Png.enc.nch(op)), u0, U32.from_nat(k0),
        add.nat(kk, 1n)), cnt.add(k0, Laws.spec.nch(op), Png.enc.nch(op), nch.nat(op))) :
        {U32.add(u0, Png.enc.nch(op)) == U32.from_nat(k1) : U32}}
      +e_k = {Equal.trans(Nat, Nat.add(k1, ll), Nat.add(k0, Nat.add(Laws.spec.nch(op), ll)), Nat.add(kk,
        1n+Nat.add(Laws.spec.nch(op), ll)), M1.ras.add_assoc(k0, Laws.spec.nch(op), ll), M1.ras.add_assoc(kk, 1n,
        Nat.add(Laws.spec.nch(op), ll))) : {Nat.add(k1, ll) == Nat.add(kk, 1n+Nat.add(Laws.spec.nch(op), ll)) : Nat}}
      +lc = List.length(&2, U32, List.append(&2, U32, M1.chans(op, cc), rest))
      +e_l = {Equal.cong(Nat, Nat, nn => Nat.add(kk, 1n+nn), Nat.add(Laws.spec.nch(op), ll), lc, Equal.sym(Nat, lc,
        Nat.add(Laws.spec.nch(op), ll), len.chans(op, cc, rest))) : {Nat.add(kk, 1n+Nat.add(Laws.spec.nch(op),
        ll)) == Nat.add(kk, 1n+lc) : Nat}}
      Equal.trans(U32, prt.cnt(tl, pw, ww, op, U32.add(u0, Png.enc.nch(op))), prt.cnt(tl, pw, ww, op, U32.from_nat(k1)),
        U32.from_nat(Nat.add(kk, 1n+lc)),
        Equal.cong(U32, U32, uu => prt.cnt(tl, pw, ww, op, uu), U32.add(u0, Png.enc.nch(op)), U32.from_nat(k1), e_n),
        Equal.trans(U32, prt.cnt(tl, pw, ww, op, U32.from_nat(k1)), U32.from_nat(Nat.add(k1, ll)),
          U32.from_nat(Nat.add(kk, 1n+lc)), cnt.word(tl, pw, ww, op, k1),
          Equal.cong(Nat, U32, nn => U32.from_nat(nn), Nat.add(k1, ll), Nat.add(kk, 1n+lc), Equal.trans(Nat,
            Nat.add(k1, ll), Nat.add(kk, 1n+Nat.add(Laws.spec.nch(op), ll)), Nat.add(kk, 1n+lc), e_k, e_l))))
    case +cc <> +tl 1n+(+pp):
      +rest = M1.sc(tl, pp, ww, op)
      +ll = List.length(&2, U32, rest)
      +k1 = Nat.add(kk, Laws.spec.nch(op))
      +lc = List.length(&2, U32, List.append(&2, U32, M1.chans(op, cc), rest))
      +e_l = {Equal.cong(Nat, Nat, nn => Nat.add(kk, nn), Nat.add(Laws.spec.nch(op), ll), lc, Equal.sym(Nat, lc,
        Nat.add(Laws.spec.nch(op), ll), len.chans(op, cc, rest))) : {Nat.add(kk, Nat.add(Laws.spec.nch(op),
          ll)) == Nat.add(kk, lc) :
        Nat}}
      Equal.trans(U32, prt.cnt(tl, pp, ww, op, U32.add(U32.from_nat(kk), Png.enc.nch(op))), prt.cnt(tl, pp, ww, op,
        U32.from_nat(k1)), U32.from_nat(Nat.add(kk, lc)),
        Equal.cong(U32, U32, uu => prt.cnt(tl, pp, ww, op, uu), U32.add(U32.from_nat(kk), Png.enc.nch(op)),
          U32.from_nat(k1), cnt.add(kk, Laws.spec.nch(op), Png.enc.nch(op), nch.nat(op))),
        Equal.trans(U32, prt.cnt(tl, pp, ww, op, U32.from_nat(k1)), U32.from_nat(Nat.add(k1, ll)),
          U32.from_nat(Nat.add(kk, lc)), cnt.word(tl, pp, ww, op, k1),
          Equal.cong(Nat, U32, nn => U32.from_nat(nn), Nat.add(k1, ll), Nat.add(kk, lc), Equal.trans(Nat, Nat.add(k1,
            ll), Nat.add(kk, Nat.add(Laws.spec.nch(op), ll)), Nat.add(kk, lc), M1.ras.add_assoc(kk, Laws.spec.nch(op),
                ll),
            e_l))))

# one more bit against a set bit keeps at most
def lestep(
  cc: Cmp,
  bit: Bool,
  hh: {Cmp.is_le(cc) == True{} : Bool}
) -> {Cmp.is_le(Word.cmp.fin(bit, True{}, cc)) == True{} : Bool}:
  match cc bit:
    case LT{} _bit:
      {==}
    case EQ{} True{}:
      {==}
    case EQ{} False{}:
      {==}
    case GT{} _bit:
      Empty.absurd({False{} == True{} : Bool}, M1.false_true(hh))

# eight low bits against 255's, the rest equal: at most
def le8(
  +b0: Bool,
  +b1: Bool,
  +b2: Bool,
  +b3: Bool,
  +b4: Bool,
  +b5: Bool,
  +b6: Bool,
  +b7: Bool
) -> {Cmp.is_le(M9.le8.cmp(b0, b1, b2, b3, b4, b5, b6, b7, EQ{})) == True{} : Bool}:
  +c7 = Word.cmp.fin(b7, True{}, EQ{})
  +c6 = Word.cmp.fin(b6, True{}, c7)
  +c5 = Word.cmp.fin(b5, True{}, c6)
  +c4 = Word.cmp.fin(b4, True{}, c5)
  +c3 = Word.cmp.fin(b3, True{}, c4)
  +c2 = Word.cmp.fin(b2, True{}, c3)
  +c1 = Word.cmp.fin(b1, True{}, c2)
  lestep(c1, b0, lestep(c2, b1, lestep(c3, b2, lestep(c4, b3, lestep(c5, b4, lestep(c6, b5, lestep(c7, b6,
    lestep(EQ{}, b7, {==}))))))))

# a channel masked again is itself: the mask is first in both
def mask.red(cc: U32) -> {U32.and(255, Png.enc.r(cc)) == Png.enc.r(cc) : U32}:
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

# the same for green
def mask.grn(cc: U32) -> {U32.and(255, Png.enc.g(cc)) == Png.enc.g(cc) : U32}:
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

# the same for blue
def mask.blu(cc: U32) -> {U32.and(255, Png.enc.b(cc)) == Png.enc.b(cc) : U32}:
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

# the same for alpha
def mask.alp(cc: U32) -> {U32.and(255, Png.enc.a(cc)) == Png.enc.a(cc) : U32}:
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

# the alpha byte is the top byte shifted down
def alpha.top(cc: U32) -> {Png.enc.a(cc) == U32.shrn(cc, 24n) : U32}:
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

# a masked byte is below 256
def lt256(xx: U32) -> {U32.is_lt(U32.and(255, xx), 256) == True{} : Bool}:
  match xx:
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

# a masked byte is at most 255: its low eight bits against 255's
def le255(xx: U32) -> {U32.is_le(U32.and(255, xx), 255) == True{} : Bool}:
  match xx:
    case U32{w0}:
      match w0:
        case WCon{+b0, WCon{+b1, WCon{+b2, WCon{+b3, w4}}}}:
          match w4:
            case WCon{+b4, WCon{+b5, WCon{+b6, WCon{+b7, w8}}}}:
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
                                          le8(b0, b1, b2, b3, b4, b5, b6, b7)

# masked lists appended are masked
def masked.app(
  +aa: List<&2, U32>,
  +bb: List<&2, U32>,
  ha: M1.masked(aa),
  hb: M1.masked(bb)
) -> M1.masked(List.append(&2, U32, aa, bb)):
  match aa:
    case Nil{}:
      hb
    case +xx <> +tl:
      (ex, ht) = ha
      (ex, masked.app(tl, bb, ht, hb))

# a sample's channels are masked
def masked.chans(op: Bool, +cc: U32) -> M1.masked(M1.chans(op, cc)):
  match op:
    case True{}:
      (mask.red(cc), (mask.grn(cc), (mask.blu(cc), Unit{})))
    case False{}:
      (mask.red(cc), (mask.grn(cc), (mask.blu(cc), (mask.alp(cc), Unit{}))))

# the channels of samples, in order
def chans.all(+op: Bool, px: List<&2, U32>) -> List<&2, U32>:
  match px:
    case Nil{}:
      []
    case +cc <> tl:
      List.append(&2, U32, M1.chans(op, cc), chans.all(op, tl))

# every channel is masked
def masked.all(+op: Bool, +px: List<&2, U32>) -> M1.masked(chans.all(op, px)):
  match px:
    case Nil{}:
      Unit{}
    case +cc <> +tl:
      masked.app(M1.chans(op, cc), chans.all(op, tl), masked.chans(op, cc), masked.all(op, tl))

# the channels of samples appended: the channels of each, appended
def chans.app(
  +op: Bool,
  +aa: List<&2, U32>,
  +bb: List<&2, U32>
) -> {chans.all(op, List.append(&2, U32, aa, bb)) == List.append(&2, U32, chans.all(op, aa), chans.all(op, bb)) :
  List<&2, U32>}:
  match aa:
    case Nil{}:
      {==}
    case +cc <> +tl:
      Equal.trans(List<&2, U32>, List.append(&2, U32, M1.chans(op, cc), chans.all(op, List.append(&2, U32, tl, bb))),
        List.append(&2, U32, M1.chans(op, cc), List.append(&2, U32, chans.all(op, tl), chans.all(op, bb))),
        List.append(&2, U32, List.append(&2, U32, M1.chans(op, cc), chans.all(op, tl)), chans.all(op, bb)),
        Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.append(&2, U32, M1.chans(op, cc), ys), chans.all(op,
          List.append(&2, U32, tl, bb)), List.append(&2, U32, chans.all(op, tl), chans.all(op, bb)), chans.app(op, tl,
          bb)),
        Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, M1.chans(op, cc), chans.all(op, tl)),
          chans.all(op, bb)), List.append(&2, U32, M1.chans(op, cc), List.append(&2, U32, chans.all(op, tl),
              chans.all(op,
          bb))), M1.app_assoc(M1.chans(op, cc), chans.all(op, tl), chans.all(op, bb))))

# the channels of k samples: k times nchn bytes
def len.chans.all(
  +op: Bool,
  +px: List<&2, U32>
) -> {List.length(&2, U32, chans.all(op, px)) == Nat.mul(List.length(&2, U32, px), Laws.spec.nch(op)) : Nat}:
  match px:
    case Nil{}:
      {==}
    case +cc <> +tl:
      Equal.trans(Nat, List.length(&2, U32, List.append(&2, U32, M1.chans(op, cc), chans.all(op, tl))),
        Nat.add(Laws.spec.nch(op),
        List.length(&2, U32, chans.all(op, tl))), Nat.add(Laws.spec.nch(op), Nat.mul(List.length(&2, U32, tl),
        Laws.spec.nch(op))),
        len.chans(op, cc, chans.all(op, tl)), Equal.cong(Nat, Nat, nn => Nat.add(Laws.spec.nch(op), nn),
        List.length(&2, U32,
        chans.all(op, tl)), Nat.mul(List.length(&2, U32, tl), Laws.spec.nch(op)), len.chans.all(op, tl)))

# the rows of h rows of w samples: each row the channels of its samples
def rows.of(hn: Nat, +ww: Nat, +op: Bool, +px: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match hn:
    case 0n:
      []
    case 1n+hp:
      chans.all(op, M1.tk(ww, px)) <> rows.of(hp, ww, op, M1.dr(ww, px))

# inside a row: k samples with k positions left, then the next row
def sc.part(
  +qq: List<&2, U32>,
  kk: Nat,
  +rest: List<&2, U32>,
  +ww: Nat,
  +op: Bool,
  hq: {List.length(&2, U32, qq) == kk : Nat}
) -> {M1.sc(List.append(&2, U32, qq, rest), kk, ww, op) == List.append(&2, U32, chans.all(op, qq), M1.sc(rest, 0n, ww,
    op)) :
  List<&2, U32>}:
  match qq kk:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+pp:
      Empty.absurd({M1.sc(rest, 1n+pp, ww, op) == M1.sc(rest, 0n, ww, op) : List<&2, U32>}, M1.zero_succ(pp, hq))
    case +cc <> +tl 0n:
      Empty.absurd({M1.sc(cc <> List.append(&2, U32, tl, rest), 0n, ww, op) == List.append(&2, U32, chans.all(op,
        cc <> tl), M1.sc(rest, 0n, ww, op)) : List<&2, U32>}, M1.zero_succ(List.length(&2, U32, tl), Equal.sym(Nat,
        1n+List.length(&2, U32, tl), 0n, hq)))
    case +cc <> +tl 1n+(+pp):
      +ch = M1.chans(op, cc)
      +ct = chans.all(op, tl)
      +sr = M1.sc(rest, 0n, ww, op)
      Equal.trans(List<&2, U32>, List.append(&2, U32, ch, M1.sc(List.append(&2, U32, tl, rest), pp, ww, op)),
        List.append(&2, U32, ch, List.append(&2, U32, ct, sr)), List.append(&2, U32, List.append(&2, U32, ch, ct), sr),
        Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.append(&2, U32, ch, ys), M1.sc(List.append(&2, U32, tl,
            rest),
          pp, ww, op), List.append(&2, U32, ct, sr), sc.part(tl, pp, rest, ww, op, M1.succ_inj(List.length(&2, U32,
          tl), pp, hq))),
        Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, ch, ct), sr), List.append(&2, U32, ch,
          List.append(&2, U32, ct, sr)), M1.app_assoc(ch, ct, sr)))

# a whole row of 1 + w' samples, then the rest: a filter byte and the row's channels
def sc.row(
  +qq: List<&2, U32>,
  +rest: List<&2, U32>,
  +wp: Nat,
  +op: Bool,
  hq: {List.length(&2, U32, qq) == 1n+wp : Nat}
) -> {M1.sc(List.append(&2, U32, qq, rest), 0n, 1n+wp, op) == 0 <> List.append(&2, U32, chans.all(op, qq), M1.sc(rest,
    0n,
  1n+wp, op)) : List<&2, U32>}:
  match qq:
    case Nil{}:
      Empty.absurd({M1.sc(rest, 0n, 1n+wp, op) == 0 <> List.append(&2, U32, [], M1.sc(rest, 0n, 1n+wp, op)) : List<&2,
          U32>},
        M1.zero_succ(wp, hq))
    case +cc <> +tl:
      +ch = M1.chans(op, cc)
      +ct = chans.all(op, tl)
      +sr = M1.sc(rest, 0n, 1n+wp, op)
      Equal.cong(List<&2, U32>, List<&2, U32>, ys => 0 <> ys, List.append(&2, U32, ch, M1.sc(List.append(&2, U32, tl,
        rest), wp, 1n+wp, op)), List.append(&2, U32, List.append(&2, U32, ch, ct), sr), Equal.trans(List<&2, U32>,
        List.append(&2, U32, ch, M1.sc(List.append(&2, U32, tl, rest), wp, 1n+wp, op)), List.append(&2, U32, ch,
        List.append(&2, U32, ct, sr)), List.append(&2, U32, List.append(&2, U32, ch, ct), sr),
        Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.append(&2, U32, ch, ys), M1.sc(List.append(&2, U32, tl,
            rest),
          wp, 1n+wp, op), List.append(&2, U32, ct, sr), sc.part(tl, wp, rest, 1n+wp, op, M1.succ_inj(List.length(&2,
          U32, tl), wp, hq))),
        Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, ch, ct), sr), List.append(&2, U32, ch,
          List.append(&2, U32, ct, sr)), M1.app_assoc(ch, ct, sr))))

# h rows of 1 + w' samples, as the bytes of their rows: what sc.rows proves
def sc.rows.ty(+hn: Nat, +wp: Nat, +op: Bool, +px: List<&2, U32>) -> Type:
  {M1.sc(px, 0n, 1n+wp, op) == M1.scan(rows.of(hn, 1n+wp, op, px)) : List<&2, U32>}

# a row split off the front, then the rest by induction
def sc.rows.at(
  +hp: Nat,
  +wp: Nat,
  +op: Bool,
  +px: List<&2, U32>,
  sp: M1.split.ty(1n+wp, Nat.mul(hp, 1n+wp), px),
  ih: @xs: List<&2, U32> -> {List.length(&2, U32, xs) == Nat.mul(hp, 1n+wp) : Nat} -> sc.rows.ty(hp, wp, op, xs)
) -> sc.rows.ty(1n+hp, wp, op, px):
  (e1, (e2, e3)) = sp
  +ww = {1n+wp : Nat}
  +qq = M1.tk(ww, px)
  +rr = M1.dr(ww, px)
  Equal.trans(List<&2, U32>, M1.sc(px, 0n, ww, op), M1.sc(List.append(&2, U32, qq, rr), 0n, ww, op),
    M1.scan(rows.of(1n+hp, ww, op, px)),
    Equal.cong(List<&2, U32>, List<&2, U32>, xs => M1.sc(xs, 0n, ww, op), px, List.append(&2, U32, qq, rr), e1),
    Equal.trans(List<&2, U32>, M1.sc(List.append(&2, U32, qq, rr), 0n, ww, op), 0 <> List.append(&2, U32,
      chans.all(op, qq), M1.sc(rr, 0n, ww, op)), M1.scan(rows.of(1n+hp, ww, op, px)), sc.row(qq, rr, wp, op, e2),
      Equal.cong(List<&2, U32>, List<&2, U32>, ys => 0 <> List.append(&2, U32, chans.all(op, qq), ys), M1.sc(rr, 0n,
        ww, op), M1.scan(rows.of(hp, ww, op, rr)), ih(rr, e3))))

# h rows of 1 + w' samples: the bytes enc.raw writes are the rows as scanlines
def sc.rows(
  hn: Nat,
  +wp: Nat,
  +op: Bool,
  +px: List<&2, U32>,
  hl: {List.length(&2, U32, px) == Nat.mul(hn, 1n+wp) : Nat}
) -> sc.rows.ty(hn, wp, op, px):
  match hn:
    case 0n:
      match px:
        case Nil{}:
          {==}
        case +cc <> +tl:
          Empty.absurd({M1.sc(cc <> tl, 0n, 1n+wp, op) == [] : List<&2, U32>}, M1.zero_succ(List.length(&2, U32, tl),
            Equal.sym(Nat, 1n+List.length(&2, U32, tl), 0n, hl)))
    case 1n+(+hp):
      sc.rows.at(hp, wp, op, px, M1.split(1n+wp, Nat.mul(hp, 1n+wp), px, hl), xs => ex => sc.rows(hp, wp, op, xs, ex))

# the rows of h rows of w samples, concatenated: what rows.cat proves
def rows.cat.ty(+hn: Nat, +ww: Nat, +op: Bool, +px: List<&2, U32>) -> Type:
  {List.concat(&2, U32, rows.of(hn, ww, op, px)) == chans.all(op, px) : List<&2, U32>}

# a row split off the front, then the rest by induction
def rows.cat.at(
  +hp: Nat,
  +ww: Nat,
  +op: Bool,
  +px: List<&2, U32>,
  sp: M1.split.ty(ww, Nat.mul(hp, ww), px),
  ih: @xs: List<&2, U32> -> {List.length(&2, U32, xs) == Nat.mul(hp, ww) : Nat} -> rows.cat.ty(hp, ww, op, xs)
) -> rows.cat.ty(1n+hp, ww, op, px):
  (e1, (_e2, e3)) = sp
  +qq = M1.tk(ww, px)
  +rr = M1.dr(ww, px)
  Equal.trans(List<&2, U32>, List.append(&2, U32, chans.all(op, qq), List.concat(&2, U32, rows.of(hp, ww, op, rr))),
    List.append(&2, U32, chans.all(op, qq), chans.all(op, rr)), chans.all(op, px),
    Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.append(&2, U32, chans.all(op, qq), ys), List.concat(&2, U32,
      rows.of(hp, ww, op, rr)), chans.all(op, rr), ih(rr, e3)),
    Equal.trans(List<&2, U32>, List.append(&2, U32, chans.all(op, qq), chans.all(op, rr)), chans.all(op,
      List.append(&2, U32, qq, rr)), chans.all(op, px), Equal.sym(List<&2, U32>, chans.all(op, List.append(&2, U32,
      qq, rr)), List.append(&2, U32, chans.all(op, qq), chans.all(op, rr)), chans.app(op, qq, rr)),
      Equal.cong(List<&2, U32>, List<&2, U32>, xs => chans.all(op, xs), List.append(&2, U32, qq, rr), px,
        Equal.sym(List<&2, U32>, px, List.append(&2, U32, qq, rr), e1))))

# the rows, concatenated, are the channels of every sample
def rows.cat(
  hn: Nat,
  +ww: Nat,
  +op: Bool,
  +px: List<&2, U32>,
  hl: {List.length(&2, U32, px) == Nat.mul(hn, ww) : Nat}
) -> rows.cat.ty(hn, ww, op, px):
  match hn:
    case 0n:
      match px:
        case Nil{}:
          {==}
        case +cc <> +tl:
          Empty.absurd({[] == chans.all(op, cc <> tl) : List<&2, U32>}, M1.zero_succ(List.length(&2, U32, tl),
            Equal.sym(Nat, 1n+List.length(&2, U32, tl), 0n, hl)))
    case 1n+(+hp):
      rows.cat.at(hp, ww, op, px, M1.split(ww, Nat.mul(hp, ww), px, hl), xs => ex => rows.cat(hp, ww, op, xs, ex))

# h rows
def rows.len(
  hn: Nat,
  +ww: Nat,
  +op: Bool,
  +px: List<&2, U32>
) -> {List.length(&2, List<&2, U32>, rows.of(hn, ww, op, px)) == hn : Nat}:
  match hn:
    case 0n:
      {==}
    case 1n+(+hp):
      Equal.cong(Nat, Nat, nn => 1n+nn, List.length(&2, List<&2, U32>, rows.of(hp, ww, op, M1.dr(ww, px))), hp,
        rows.len(hp, ww, op, M1.dr(ww, px)))

# every row's bytes masked
def masked.rows(rows: List<&2, List<&2, U32>>) -> Type:
  match rows:
    case Nil{}:
      Unit
    case +row <> tl:
      M1.masked(row) & masked.rows(tl)

# the rows of samples are masked
def masked.rows.of(hn: Nat, +ww: Nat, +op: Bool, +px: List<&2, U32>) -> masked.rows(rows.of(hn, ww, op, px)):
  match hn:
    case 0n:
      Unit{}
    case 1n+(+hp):
      (masked.all(op, M1.tk(ww, px)), masked.rows.of(hp, ww, op, M1.dr(ww, px)))

# subtracting zero leaves a U32
def sub.zero(+xx: U32) -> {U32.sub(xx, 0) == xx : U32}:
  match xx:
    case U32{+ww}:
      Equal.cong(Word(32n), U32, vv => U32{vv}, Word.adc(32n, ww, Word.zero(32n), True{}, True{}), ww,
        M1.adc_zero_carry(32n, ww))

# filter None leaves a row of masked bytes as it is
def frow(
  +row: List<&2, U32>,
  +bpp: U32,
  +prev: List<&2, U32>,
  +hist: List<&2, U32>,
  +phist: List<&2, U32>,
  hm: M1.masked(row)
) -> {L4.flt.row(row, L4.FNone{}, bpp, prev, hist, phist) == row : List<&2, U32>}:
  match row:
    case Nil{}:
      {==}
    case +xx <> +tl:
      (ex, ht) = hm
      +bb = L4.flt.up(prev)
      Equal.trans(List<&2, U32>, U32.and(255, U32.sub(xx, 0)) <> L4.flt.row(tl, L4.FNone{}, bpp,
        L4.flt.next(prev),
        xx <> hist, bb <> phist), xx <> L4.flt.row(tl, L4.FNone{}, bpp, L4.flt.next(prev), xx <> hist,
        bb <> phist), xx <> tl,
        Equal.cong(U32, List<&2, U32>, uu => uu <> L4.flt.row(tl, L4.FNone{}, bpp, L4.flt.next(prev), xx <> hist,
          bb <> phist), U32.and(255, U32.sub(xx, 0)), xx, Equal.trans(U32, U32.and(255, U32.sub(xx, 0)), U32.and(255,
          xx), xx, Equal.cong(U32, U32, uu => U32.and(255, uu), U32.sub(xx, 0), xx, sub.zero(xx)), ex)),
        Equal.cong(List<&2, U32>, List<&2, U32>, ys => xx <> ys, L4.flt.row(tl, L4.FNone{}, bpp,
          L4.flt.next(prev), xx <> hist, bb <> phist), tl, frow(tl, bpp, L4.flt.next(prev), xx <> hist,
          bb <> phist, ht)))

# filter None over masked rows: the scanlines
def frows(
  +rows: List<&2, List<&2, U32>>,
  +bpp: U32,
  +prev: List<&2, U32>,
  hm: masked.rows(rows)
) -> {L4.flt.rows(rows, L4.FNone{}, bpp, prev) == M1.scan(rows) : List<&2, U32>}:
  match rows:
    case Nil{}:
      {==}
    case +row <> +tl:
      (hr, ht) = hm
      Equal.trans(List<&2, U32>, 0 <> List.append(&2, U32, L4.flt.row(row, L4.FNone{}, bpp, prev, [], []),
        L4.flt.rows(tl, L4.FNone{}, bpp, row)), 0 <> List.append(&2, U32, row, L4.flt.rows(tl, L4.FNone{}, bpp,
        row)), 0 <> List.append(&2, U32, row, M1.scan(tl)),
        Equal.cong(List<&2, U32>, List<&2, U32>, ys => 0 <> List.append(&2, U32, ys, L4.flt.rows(tl, L4.FNone{},
          bpp, row)), L4.flt.row(row, L4.FNone{}, bpp, prev, [], []), row, frow(row, bpp, prev, [], [], hr)),
        Equal.cong(List<&2, U32>, List<&2, U32>, ys => 0 <> List.append(&2, U32, row, ys), L4.flt.rows(tl,
          L4.FNone{}, bpp, row), M1.scan(tl), frows(tl, bpp, row, ht)))

# a masked byte is below 256
def byte.lt(+xx: U32, ex: {U32.and(255, xx) == xx : U32}) -> {U32.is_lt(xx, 256) == True{} : Bool}:
  Equal.trans(Bool, U32.is_lt(xx, 256), U32.is_lt(U32.and(255, xx), 256), True{}, Equal.cong(U32, Bool, uu =>
    U32.is_lt(uu, 256), xx, U32.and(255, xx), Equal.sym(U32, U32.and(255, xx), xx, ex)), lt256(xx))

# a masked byte is at most 255
def byte.le(+xx: U32, ex: {U32.and(255, xx) == xx : U32}) -> {U32.is_le(xx, 255) == True{} : Bool}:
  Equal.trans(Bool, U32.is_le(xx, 255), U32.is_le(U32.and(255, xx), 255), True{}, Equal.cong(U32, Bool, uu =>
    U32.is_le(uu, 255), xx, U32.and(255, xx), Equal.sym(U32, U32.and(255, xx), xx, ex)), le255(xx))

# a masked row of n bytes: flt.bytes takes it
def fbytes(
  +xs: List<&2, U32>,
  nn: Nat,
  hm: M1.masked(xs),
  hl: {List.length(&2, U32, xs) == nn : Nat}
) -> {L4.flt.bytes(xs, nn, True{}) == True{} : Bool}:
  match xs nn:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+pp:
      Empty.absurd({False{} == True{} : Bool}, M1.zero_succ(pp, hl))
    case +xx <> +tl 0n:
      Empty.absurd({False{} == True{} : Bool}, M1.zero_succ(List.length(&2, U32, tl), Equal.sym(Nat,
        1n+List.length(&2, U32, tl), 0n, hl)))
    case +xx <> +tl 1n+(+pp):
      (ex, ht) = hm
      Equal.trans(Bool, L4.flt.bytes(tl, pp, U32.is_lt(xx, 256)), L4.flt.bytes(tl, pp, True{}), True{},
        Equal.cong(Bool, Bool, bb => L4.flt.bytes(tl, pp, bb), U32.is_lt(xx, 256), True{}, byte.lt(xx, ex)),
        fbytes(tl, pp, ht, M1.succ_inj(List.length(&2, U32, tl), pp, hl)))

# the rows of h rows of w samples fit: what fit.rows proves
def fit.rows.ty(+hn: Nat, +ww: Nat, +op: Bool, +px: List<&2, U32>) -> Type:
  {L4.flt.fit(rows.of(hn, ww, op, px), Nat.mul(ww, Laws.spec.nch(op)), True{}) == True{} : Bool}

# a row split off the front fits, then the rest by induction
def fit.rows.at(
  +hp: Nat,
  +ww: Nat,
  +op: Bool,
  +px: List<&2, U32>,
  sp: M1.split.ty(ww, Nat.mul(hp, ww), px),
  ih: @xs: List<&2, U32> -> {List.length(&2, U32, xs) == Nat.mul(hp, ww) : Nat} -> fit.rows.ty(hp, ww, op, xs)
) -> fit.rows.ty(1n+hp, ww, op, px):
  (_e1, (e2, e3)) = sp
  +qq = M1.tk(ww, px)
  +row = chans.all(op, qq)
  +nb = Nat.mul(ww, Laws.spec.nch(op))
  +e_len = {Equal.trans(Nat, List.length(&2, U32, row), Nat.mul(List.length(&2, U32, qq), Laws.spec.nch(op)), nb,
    len.chans.all(op, qq), Equal.cong(Nat, Nat, nn => Nat.mul(nn, Laws.spec.nch(op)), List.length(&2, U32, qq), ww,
    e2)) : {List.length(&2, U32, row) == nb : Nat}}
  Equal.trans(Bool, L4.flt.fit(rows.of(hp, ww, op, M1.dr(ww, px)), nb, L4.flt.bytes(row, nb, True{})),
    L4.flt.fit(rows.of(hp, ww, op, M1.dr(ww, px)), nb, True{}), True{},
    Equal.cong(Bool, Bool, bb => L4.flt.fit(rows.of(hp, ww, op, M1.dr(ww, px)), nb, bb), L4.flt.bytes(row, nb,
      True{}), True{}, fbytes(row, nb, masked.all(op, qq), e_len)),
    ih(M1.dr(ww, px), e3))

# the rows of samples fit: each w times nchn masked bytes
def fit.rows(
  hn: Nat,
  +ww: Nat,
  +op: Bool,
  +px: List<&2, U32>,
  hl: {List.length(&2, U32, px) == Nat.mul(hn, ww) : Nat}
) -> fit.rows.ty(hn, ww, op, px):
  match hn:
    case 0n:
      {==}
    case 1n+(+hp):
      fit.rows.at(hp, ww, op, px, M1.split(ww, Nat.mul(hp, ww), px, hl), xs => ex => fit.rows(hp, ww, op, xs, ex))

# masked bytes, then bytes: bytes
def bytes.app(
  +xs: List<&2, U32>,
  +rest: List<&2, U32>,
  hm: M1.masked(xs),
  hr: {D1.bytes.go(rest, True{}) == True{} : Bool}
) -> {D1.bytes.go(List.append(&2, U32, xs, rest), True{}) == True{} : Bool}:
  match xs:
    case Nil{}:
      hr
    case +xx <> +tl:
      (ex, ht) = hm
      Equal.trans(Bool, D1.bytes.go(List.append(&2, U32, tl, rest), U32.is_le(xx, 255)), D1.bytes.go(List.append(&2,
        U32, tl, rest), True{}), True{}, Equal.cong(Bool, Bool, bb => D1.bytes.go(List.append(&2, U32, tl, rest), bb),
        U32.is_le(xx, 255), True{}, byte.le(xx, ex)), bytes.app(tl, rest, ht, hr))

# masked rows as scanlines are bytes
def bytes.scan(
  +rows: List<&2, List<&2, U32>>,
  hm: masked.rows(rows)
) -> {D1.bytes.go(M1.scan(rows), True{}) == True{} : Bool}:
  match rows:
    case Nil{}:
      {==}
    case +row <> +tl:
      (hr, ht) = hm
      bytes.app(row, M1.scan(tl), hr, bytes.scan(tl, ht))

# opaque samples: their red, green and blue, packed with alpha 255, are the samples
def rgb.back(
  +px: List<&2, U32>,
  +hop: {D1.all_opaque(px) == True{} : Bool}
) -> {L3.spec.rgb(chans.all(True{}, px)) == Some{px} : Maybe<&2, List<&2, U32>>}:
  match px:
    case Nil{}:
      {==}
    case +cc <> +tl:
      +hand = {Equal.trans(Bool, Bool.and(D1.opaque(cc), D1.all_opaque(tl)),
        List.all.if(_u => D1.all_opaque(tl), D1.opaque(cc)), True{},
        Equal.sym(Bool, List.all.if(_u => D1.all_opaque(tl), D1.opaque(cc)),
          Bool.and(D1.opaque(cc), D1.all_opaque(tl)), M1.all.if.and(D1.opaque(cc), D1.all_opaque(tl))),
        hop) : {Bool.and(D1.opaque(cc), D1.all_opaque(tl)) == True{} : Bool}}
      +ho = M1.and_left(D1.opaque(cc), D1.all_opaque(tl), hand)
      +ht = M1.and_right(D1.opaque(cc), D1.all_opaque(tl), hand)
      +e_sh = M1.ueq(U32.shrn(cc, 24n), 255, ho)
      +pk = L3.spec.argb(255, Png.enc.r(cc), Png.enc.g(cc), Png.enc.b(cc))
      +e_a = {Equal.trans(U32, Png.enc.a(cc), U32.shrn(cc, 24n), 255, alpha.top(cc), e_sh) : {Png.enc.a(cc) == 255 :
        U32}}
      +e_c = {Equal.trans(U32, pk, L3.spec.argb(Png.enc.a(cc), Png.enc.r(cc), Png.enc.g(cc), Png.enc.b(cc)), cc,
        Equal.cong(U32, U32, aa => L3.spec.argb(aa, Png.enc.r(cc), Png.enc.g(cc), Png.enc.b(cc)), 255, Png.enc.a(cc),
        Equal.sym(U32, Png.enc.a(cc), 255, e_a)), M4.prt.be.back(cc)) : {pk == cc : U32}}
      Equal.trans(Maybe<&2, List<&2, U32>>, L3.spec.cons(pk, L3.spec.rgb(chans.all(True{}, tl))),
        L3.spec.cons(pk, Some{tl}), Some{cc <> tl},
        Equal.cong(Maybe<&2, List<&2, U32>>, Maybe<&2, List<&2, U32>>, mm => L3.spec.cons(pk, mm),
          L3.spec.rgb(chans.all(True{}, tl)), Some{tl}, rgb.back(tl, ht)),
        Equal.cong(U32, Maybe<&2, List<&2, U32>>, uu => Some{uu <> tl}, pk, cc, e_c))

# any samples: their red, green, blue and alpha, packed, are the samples
def rgba.back(+px: List<&2, U32>) -> {L3.spec.rgba(chans.all(False{}, px)) == Some{px} : Maybe<&2, List<&2, U32>>}:
  match px:
    case Nil{}:
      {==}
    case +cc <> +tl:
      +pk = L3.spec.argb(Png.enc.a(cc), Png.enc.r(cc), Png.enc.g(cc), Png.enc.b(cc))
      Equal.trans(Maybe<&2, List<&2, U32>>, L3.spec.cons(pk, L3.spec.rgba(chans.all(False{}, tl))),
        L3.spec.cons(pk, Some{tl}), Some{cc <> tl},
        Equal.cong(Maybe<&2, List<&2, U32>>, Maybe<&2, List<&2, U32>>, mm => L3.spec.cons(pk, mm),
          L3.spec.rgba(chans.all(False{}, tl)), Some{tl}, rgba.back(tl)),
        Equal.cong(U32, Maybe<&2, List<&2, U32>>, uu => Some{uu <> tl}, pk, cc, M4.prt.be.back(cc)))

# a number is at most its successor
def le.succ(xx: Nat) -> {Nat.is_le(xx, 1n+xx) == True{} : Bool}:
  match xx:
    case 0n:
      {==}
    case 1n+pp:
      le.succ(pp)

# adding one on the right
def add.one.nat(+xx: Nat) -> {Nat.add(xx, 1n) == 1n+xx : Nat}:
  Equal.trans(Nat, Nat.add(xx, 1n), 1n+Nat.add(xx, 0n), 1n+xx, M1.nat_add_succ(xx, 0n), Equal.cong(Nat, Nat, nn =>
    1n+nn, Nat.add(xx, 0n), xx, M1.nat_add_zero(xx)))

# at most is not above
def le.not.gt(cc: Cmp, hh: {Cmp.is_le(cc) == True{} : Bool}) -> {Cmp.is_gt(cc) == False{} : Bool}:
  match cc:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({True{} == False{} : Bool}, M1.false_true(hh))

# a natural at most a word's value, taken in a word, keeps its value
def nat.fits(
  kk: Nat,
  +cap: U32,
  +hh: {Nat.is_le(kk, U32.to_nat(cap)) == True{} : Bool}
) -> {U32.to_nat(U32.from_nat(kk)) == kk : Nat}:
  match kk:
    case 0n:
      {==}
    case 1n+(+pp):
      +cn = U32.to_nat(cap)
      +up = U32.from_nat(pp)
      +hp = M1.le_trans(pp, 1n+pp, cn, le.succ(pp), hh)
      +ih = nat.fits(pp, cap, hp)
      +h_lt = {Equal.trans(Bool, Nat.is_lt(U32.to_nat(up), cn), Nat.is_lt(pp, cn), True{}, Equal.cong(Nat, Bool, nn =>
        Nat.is_lt(nn, cn), U32.to_nat(up), pp, ih), Equal.trans(Bool, Nat.is_lt(pp, cn), Nat.is_le(1n+pp, cn), True{},
        M1.lt_le_succ(pp, cn), hh)) : {Nat.is_lt(U32.to_nat(up), cn) == True{} : Bool}}
      Equal.trans(Nat, U32.to_nat(U32.inc(up)), U32.to_nat(U32.add(up, 1)), 1n+pp,
        Equal.cong(U32, Nat, uu => U32.to_nat(uu), U32.inc(up), U32.add(up, 1), Equal.sym(U32, U32.add(up, 1),
          U32.inc(up), add.one(up))),
        Equal.trans(Nat, U32.to_nat(U32.add(up, 1)), 1n+U32.to_nat(up), 1n+pp, M1.inc_nat(up, cap, M1.u_lt(up, cap,
          h_lt)), Equal.cong(Nat, Nat, nn => 1n+nn, U32.to_nat(up), pp, ih)))

# a U32 whose value is at most cap's is not above cap
def gt.no(
  +uu: U32,
  +cap: U32,
  +nn: Nat,
  en: {U32.to_nat(uu) == nn : Nat},
  hh: {Nat.is_le(nn, U32.to_nat(cap)) == True{} : Bool}
) -> {U32.is_gt(uu, cap) == False{} : Bool}:
  +cn = U32.to_nat(cap)
  Equal.trans(Bool, U32.is_gt(uu, cap), Cmp.is_gt(Nat.cmp(nn, cn)), False{},
    Equal.trans(Bool, U32.is_gt(uu, cap), Cmp.is_gt(Nat.cmp(U32.to_nat(uu), cn)), Cmp.is_gt(Nat.cmp(nn, cn)),
      Equal.cong(Cmp, Bool, cc => Cmp.is_gt(cc), U32.cmp(uu, cap), Nat.cmp(U32.to_nat(uu), cn), M1.u_cmp(uu, cap)),
      Equal.cong(Nat, Bool, kk => Cmp.is_gt(Nat.cmp(kk, cn)), U32.to_nat(uu), nn, en)),
    le.not.gt(Nat.cmp(nn, cn), hh))

# a U32 whose value is at most cap's is at most cap
def le.yes(
  +uu: U32,
  +cap: U32,
  +nn: Nat,
  en: {U32.to_nat(uu) == nn : Nat},
  hh: {Nat.is_le(nn, U32.to_nat(cap)) == True{} : Bool}
) -> {U32.is_le(uu, cap) == True{} : Bool}:
  +cn = U32.to_nat(cap)
  Equal.trans(Bool, U32.is_le(uu, cap), Nat.is_le(nn, cn), True{},
    Equal.trans(Bool, U32.is_le(uu, cap), Nat.is_le(U32.to_nat(uu), cn), Nat.is_le(nn, cn), M8.u_le(uu, cap),
      Equal.cong(Nat, Bool, kk => Nat.is_le(kk, cn), U32.to_nat(uu), nn, en)), hh)

# a U32 above 0: its value is a successor
def gt.pos(+uu: U32, +pp: Nat, en: {U32.to_nat(uu) == 1n+pp : Nat}) -> {U32.is_gt(uu, 0) == True{} : Bool}:
  Equal.trans(Bool, U32.is_gt(uu, 0), Cmp.is_gt(Nat.cmp(1n+pp, 0n)), True{}, Equal.trans(Bool, U32.is_gt(uu, 0),
    Cmp.is_gt(Nat.cmp(U32.to_nat(uu), 0n)), Cmp.is_gt(Nat.cmp(1n+pp, 0n)), Equal.cong(Cmp, Bool, cc => Cmp.is_gt(cc),
    U32.cmp(uu, 0), Nat.cmp(U32.to_nat(uu), 0n), M1.u_cmp(uu, 0)), Equal.cong(Nat, Bool, kk => Cmp.is_gt(Nat.cmp(kk,
    0n)), U32.to_nat(uu), 1n+pp, en)), {==})

# the length of an append
def len.app(
  +aa: List<&2, U32>,
  +bb: List<&2, U32>
) -> {List.length(&2, U32, List.append(&2, U32, aa, bb)) == Nat.add(List.length(&2, U32, aa), List.length(&2, U32, bb))
  : Nat}:
  match aa:
    case Nil{}:
      {==}
    case _hd <> +tl:
      Equal.cong(Nat, Nat, nn => 1n+nn, List.length(&2, U32, List.append(&2, U32, tl, bb)), Nat.add(List.length(&2, U32,
        tl), List.length(&2, U32, bb)), len.app(tl, bb))

# the scanlines of h rows of w samples: h times a filter byte and w samples' channels
def len.scan.ty(+hn: Nat, +ww: Nat, +op: Bool, +px: List<&2, U32>) -> Type:
  {List.length(&2, U32, M1.scan(rows.of(hn, ww, op, px))) == Nat.mul(hn, 1n+Nat.mul(ww, Laws.spec.nch(op))) : Nat}

# a row split off the front, then the rest by induction
def len.scan.at(
  +hp: Nat,
  +ww: Nat,
  +op: Bool,
  +px: List<&2, U32>,
  sp: M1.split.ty(ww, Nat.mul(hp, ww), px),
  ih: @xs: List<&2, U32> -> {List.length(&2, U32, xs) == Nat.mul(hp, ww) : Nat} -> len.scan.ty(hp, ww, op, xs)
) -> len.scan.ty(1n+hp, ww, op, px):
  (_e1, (e2, e3)) = sp
  +qq = M1.tk(ww, px)
  +rr = M1.dr(ww, px)
  +row = chans.all(op, qq)
  +tl = M1.scan(rows.of(hp, ww, op, rr))
  +nb = Nat.mul(ww, Laws.spec.nch(op))
  +e_row = {Equal.trans(Nat, List.length(&2, U32, row), Nat.mul(List.length(&2, U32, qq), Laws.spec.nch(op)), nb,
    len.chans.all(op, qq), Equal.cong(Nat, Nat, nn => Nat.mul(nn, Laws.spec.nch(op)), List.length(&2, U32, qq), ww,
    e2)) : {List.length(&2, U32, row) == nb : Nat}}
  Equal.cong(Nat, Nat, nn => 1n+nn, List.length(&2, U32, List.append(&2, U32, row, tl)), Nat.add(nb, Nat.mul(hp,
    1n+nb)), Equal.trans(Nat, List.length(&2, U32, List.append(&2, U32, row, tl)), Nat.add(List.length(&2, U32, row),
    List.length(&2, U32, tl)), Nat.add(nb, Nat.mul(hp, 1n+nb)), len.app(row, tl), Equal.trans(Nat,
    Nat.add(List.length(&2, U32, row), List.length(&2, U32, tl)), Nat.add(nb, List.length(&2, U32, tl)), Nat.add(nb,
    Nat.mul(hp, 1n+nb)), Equal.cong(Nat, Nat, nn => Nat.add(nn, List.length(&2, U32, tl)), List.length(&2, U32, row),
    nb, e_row), Equal.cong(Nat, Nat, nn => Nat.add(nb, nn), List.length(&2, U32, tl), Nat.mul(hp, 1n+nb), ih(rr,
    e3)))))

# the scanlines' length
def len.scan(
  hn: Nat,
  +ww: Nat,
  +op: Bool,
  +px: List<&2, U32>,
  hl: {List.length(&2, U32, px) == Nat.mul(hn, ww) : Nat}
) -> len.scan.ty(hn, ww, op, px):
  match hn:
    case 0n:
      {==}
    case 1n+(+hp):
      len.scan.at(hp, ww, op, px, M1.split(ww, Nat.mul(hp, ww), px, hl), xs => ex => len.scan(hp, ww, op, xs, ex))

# ---- H. the one-block encoding's numbers ----

# enc.nch's value
def nch.val(op: Bool) -> {U32.to_nat(Png.enc.nch(op)) == Laws.spec.nch(op) : Nat}:
  match op:
    case True{}:
      {==}
    case False{}:
      {==}

# the decoder's bytes per pixel for the encoder's colour type: the channels
def bpp.eq(op: Bool) -> {Png.png.bpp(Png.enc.ct(op)) == Png.enc.nch(op) : U32}:
  match op:
    case True{}:
      {==}
    case False{}:
      {==}

# the zlib stream enc.zlib writes before the check that the block fits is taken
def zlib.at(zz: Bool, +raw: List<&2, U32>, +nn: U32) -> List<&2, U32>:
  Png.enc.cat([120, 1], Png.enc.cat(Png.enc.blocks.fit(zz, 65535, nn, raw), Png.enc.be(Inf.adler.of(raw))))

# one stored block: the zlib header, the block header, the bytes, and Adler-32
def zlib.len(
  +raw: List<&2, U32>,
  +nn: U32,
  hle: {U32.is_le(nn, 65535) == True{} : Bool}
) -> {List.length(&2, U32, Png.enc.zlib(raw, nn)) == 11n+List.length(&2, U32, raw) : Nat}:
  +hd = {Png.enc.head(True{}, nn, (nn .^. 65535 : U32)) : List<&2, U32>}
  +ad = Png.enc.be(Inf.adler.of(raw))
  +ln = List.length(&2, U32, raw)
  Equal.trans(Nat, List.length(&2, U32, zlib.at(U32.is_le(nn, 65535), raw, nn)), List.length(&2, U32, zlib.at(True{},
    raw, nn)), 11n+ln,
    Equal.cong(Bool, Nat, zz => List.length(&2, U32, zlib.at(zz, raw, nn)), U32.is_le(nn, 65535), True{}, hle),
    Equal.trans(Nat, List.length(&2, U32, zlib.at(True{}, raw, nn)), 7n+List.length(&2, U32, List.append(&2, U32, raw,
      ad)), 11n+ln,
      Equal.cong(List<&2, U32>, Nat, xs => 2n+List.length(&2, U32, xs), Png.enc.cat(List.append(&2, U32, hd, raw), ad),
        List.append(&2, U32, List.append(&2, U32, hd, raw), ad), M8.cat_app(List.append(&2, U32, hd, raw), ad)),
      Equal.trans(Nat, 7n+List.length(&2, U32, List.append(&2, U32, raw, ad)), 7n+Nat.add(ln, 4n), 11n+ln,
        Equal.cong(Nat, Nat, kk => 7n+kk, List.length(&2, U32, List.append(&2, U32, raw, ad)), Nat.add(ln, 4n),
          len.app(raw, ad)),
        Equal.cong(Nat, Nat, kk => 7n+kk, Nat.add(ln, 4n), Nat.add(4n, ln), M1.ras.add_comm(ln, 4n)))))

# a list of 11 bytes more than a count at most cap's fits in a U32 count,
# when 11 more than cap is at most cap2
def fits.small(
  +xs: List<&2, U32>,
  +nn: Nat,
  +cap: U32,
  +cap2: U32,
  el: {List.length(&2, U32, xs) == 11n+nn : Nat},
  hh: {Nat.is_le(nn, U32.to_nat(cap)) == True{} : Bool},
  hc: {Nat.is_le(11n+U32.to_nat(cap), U32.to_nat(cap2)) == True{} : Bool}
) -> D1.spec.fits(xs):
  +ll = List.length(&2, U32, xs)
  +cn = U32.to_nat(cap)
  +c2 = U32.to_nat(cap2)
  +h1 = {M1.le_add_mono(11n, nn, cn, hh) : {Nat.is_le(Nat.add(11n, nn), Nat.add(11n, cn)) == True{} : Bool}}
  +h2 = {M1.le_trans(Nat.add(11n, nn), Nat.add(11n, cn), c2, h1, hc) : {Nat.is_le(Nat.add(11n, nn), c2) == True{} :
    Bool}}
  +h3 = {M1.le_rw_l(Nat.add(11n, nn), ll, c2, Equal.sym(Nat, ll, 11n+nn, el), h2) : {Nat.is_le(ll, c2) == True{} :
    Bool}}
  nat.fits(ll, cap2, h3)

# a U32 worth 0 is zero
def zero.is(+uu: U32, e0: {U32.to_nat(uu) == 0n : Nat}) -> {U32.is_zero(uu) == True{} : Bool}:
  Equal.trans(Bool, U32.is_zero(uu), Nat.is_eq(U32.to_nat(uu), 0n), True{}, M1.u32_eq(uu, 0),
    Equal.cong(Nat, Bool, kk => Nat.is_eq(kk, 0n), U32.to_nat(uu), 0n, e0))

# not at most is above
def nle.lt(aa: Nat, bb: Nat, hh: {Nat.is_le(aa, bb) == False{} : Bool}) -> {Nat.is_lt(bb, aa) == True{} : Bool}:
  match aa bb:
    case 0n bb0:
      Empty.absurd({Nat.is_lt(bb0, 0n) == True{} : Bool}, M1.false_true(Equal.trans(Bool, False{}, Nat.is_le(0n, bb0),
        True{}, Equal.sym(Bool, Nat.is_le(0n, bb0), False{}, hh), M1.le_zero(bb0))))
    case 1n+_ap 0n:
      {==}
    case 1n+ap 1n+bp:
      nle.lt(ap, bp, hh)

# a list at most cap's value long is counted in a U32 to its length
def len.of(
  +xs: List<&2, U32>,
  +cap: U32,
  +hh: {Nat.is_le(List.length(&2, U32, xs), U32.to_nat(cap)) == True{} : Bool}
) -> {U32.to_nat(Png.enc.len(xs, 0)) == List.length(&2, U32, xs) : Nat}:
  Equal.trans(Nat, U32.to_nat(Png.enc.len(xs, 0)), U32.to_nat(U32.from_nat(List.length(&2, U32, xs))),
    List.length(&2, U32, xs), Equal.cong(U32, Nat, uu => U32.to_nat(uu), Png.enc.len(xs, 0),
    U32.from_nat(List.length(&2, U32, xs)), len.word(xs)), nat.fits(List.length(&2, U32, xs), cap, hh))

# ---- B. enc.crc.list, and the bytes enc.pour writes ----

# enc.crc.list is the CRC fold and the bytes reversed onto the accumulator
def crcl(
  xs: List<&2, U32>,
  +cc: U32,
  +acc: List<&2, U32>
) -> {Png.enc.crc.list(xs, cc, acc) == (Crc.crc.fold(xs, cc), List.reverse.go(&2, U32, xs, acc)) : U32 & List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case +hd <> tl:
      crcl(tl, Crc.crc.byte(cc, hd), hd <> acc)

# enc.pour is enc.crc.list over bs
def pour.bs(
  xs: List<&2, U32>,
  znew: Bool,
  zlast: Bool,
  +room: U32,
  +left: U32,
  +len: U32,
  +bf: U32,
  +cc: U32,
  +acc: List<&2, U32>
) -> {Png.enc.pour(xs, znew, zlast, room, left, len, bf, cc, acc) == Png.enc.crc.list(M1.bs(xs, znew, zlast, room, left,
  len, bf), cc, acc) : U32 & List<&2, U32>}:
  match xs znew zlast:
    case Nil{} _z _last:
      {==}
    case +h <> +t False{} False{}:
      pour.bs(t, False{}, U32.is_eq((room - 1 : U32), 1), (room - 1 : U32), (left - 1 : U32), len, bf,
        Crc.crc.byte(cc, h), h <> acc)
    case +h <> +t False{} True{}:
      +left2 = (left - 1 : U32)
      pour.bs(t, True{}, False{}, 0, left2, Png.enc.cap(left2), Png.enc.bf(left2), Crc.crc.byte(cc, h), h <> acc)
    case +h <> t True{} _last:
      +nlen = (len .^. 65535 : U32)
      +b1 = Png.enc.byte(len)
      +b2 = Png.enc.hi(len)
      +b3 = Png.enc.byte(nlen)
      +b4 = Png.enc.hi(nlen)
      +c1 = Crc.crc.byte(cc, bf)
      +c2 = Crc.crc.byte(c1, b1)
      +c3 = Crc.crc.byte(c2, b2)
      +c4 = Crc.crc.byte(c3, b3)
      +c5 = Crc.crc.byte(c4, b4)
      +left2 = (left - 1 : U32)
      +room2 = (len - 1 : U32)
      pour.bs(t, U32.is_zero(room2), U32.is_eq(room2, 1), room2, left2, Png.enc.cap(left2), Png.enc.bf(left2),
        Crc.crc.byte(c5, h), h <> b4 <> b3 <> b2 <> b1 <> bf <> acc)

# ---- C. bs against enc.feed, byte by byte ----

# The block size, 65535, is named mx here and its value is U32.to_nat(mx): a
# closed Nat as large as 65535 in a type is expanded in unary and overflows
# the checker's stack. Each lemma takes mx with {mx == 65535 : U32}.

# where the open block stands against the nx bytes still to come: a final
# block holds them all, rp their count; any other block is full, its room the
# feed's, and more bytes follow it
def fin.ok(fin: Bool, +rp: U32, +rf: U32, +nx: Nat) -> Type:
  match fin:
    case True{}:
      {U32.to_nat(rp) == nx : Nat}
    case False{}:
      {U32.to_nat(rp) == U32.to_nat(rf) : Nat} & {Nat.is_lt(U32.to_nat(rp), nx) == True{} : Bool}

# what sim proves: the open block's header, the block so far, then the rest
# of bs are enc.feed's blocks of mx bytes
def sim.ty(
  +xs: List<&2, U32>,
  +znew: Bool,
  +zlast: Bool,
  +zf: Bool,
  +fin: Bool,
  +acc: List<&2, U32>,
  +rf: U32,
  +rp: U32,
  +left: U32,
  +plen: U32,
  +pbf: U32,
  +ll: U32,
  +mx: U32
) -> Type:
  {List.append(&2, U32, Png.enc.head(fin, ll, (ll .^. 65535 : U32)), List.reverse.go(&2, U32, acc, M1.bs(xs, znew,
      zlast,
    rp, left, plen, pbf))) == Png.enc.feed(xs, zf, rf, mx, acc) : List<&2, U32>}

# one byte less on both sides of fin.ok
def fo.dec(
  fin: Bool,
  +rp: U32,
  +rf: U32,
  +rp2: U32,
  +rf2: U32,
  +nt: Nat,
  +ep: {U32.to_nat(rp) == 1n+U32.to_nat(rp2) : Nat},
  +ef: {U32.to_nat(rf) == 1n+U32.to_nat(rf2) : Nat},
  hf: fin.ok(fin, rp, rf, 1n+nt)
) -> fin.ok(fin, rp2, rf2, nt):
  match fin:
    case True{}:
      M1.succ_inj(U32.to_nat(rp2), nt, Equal.trans(Nat, 1n+U32.to_nat(rp2), U32.to_nat(rp), 1n+nt, Equal.sym(Nat,
        U32.to_nat(rp), 1n+U32.to_nat(rp2), ep), hf))
    case False{}:
      (e_rr, h_lt) = hf
      +e2 = {M1.succ_inj(U32.to_nat(rp2), U32.to_nat(rf2), Equal.trans(Nat, 1n+U32.to_nat(rp2), U32.to_nat(rp),
        1n+U32.to_nat(rf2), Equal.sym(Nat, U32.to_nat(rp), 1n+U32.to_nat(rp2), ep), Equal.trans(Nat, U32.to_nat(rp),
        U32.to_nat(rf), 1n+U32.to_nat(rf2), e_rr, ef))) : {U32.to_nat(rp2) == U32.to_nat(rf2) : Nat}}
      +l2 = {Equal.trans(Bool, Nat.is_lt(1n+U32.to_nat(rp2), 1n+nt), Nat.is_lt(U32.to_nat(rp), 1n+nt), True{},
        Equal.cong(Nat, Bool, kk => Nat.is_lt(kk, 1n+nt), 1n+U32.to_nat(rp2), U32.to_nat(rp), Equal.sym(Nat,
        U32.to_nat(rp), 1n+U32.to_nat(rp2), ep)), h_lt) : {Nat.is_lt(U32.to_nat(rp2), nt) == True{} : Bool}}
      (e2, l2)

# enc.cap.at with the block size named
def capm(zz: Bool, +left: U32, +mx: U32) -> U32:
  match zz:
    case True{}:
      left
    case False{}:
      mx

# enc.cap.at is capm at 65535
def cap.m(
  zz: Bool,
  +left: U32,
  +mx: U32,
  +emx: {mx == 65535 : U32}
) -> {Png.enc.cap.at(zz, left) == capm(zz, left, mx) : U32}:
  match zz:
    case True{}:
      {==}
    case False{}:
      Equal.sym(U32, mx, 65535, emx)

# the block size is not zero
def mx.nz(+mx: U32, +emx: {mx == 65535 : U32}) -> {U32.is_zero(mx) == False{} : Bool}:
  Equal.cong(U32, Bool, uu => U32.is_zero(uu), mx, 65535, emx)

# at most 65535 is at most the block size
def le.mx(+left: U32, +mx: U32, +emx: {mx == 65535 : U32}) -> {U32.is_le(left, mx) == U32.is_le(left, 65535) : Bool}:
  Equal.cong(U32, Bool, uu => U32.is_le(left, uu), mx, 65535, emx)

# a new block's length is not zero when bytes are left
def cap.nz(
  zz: Bool,
  +left: U32,
  +mx: U32,
  +kk: Nat,
  +nzm: {U32.is_zero(mx) == False{} : Bool},
  +hn: {U32.to_nat(left) == 1n+kk : Nat}
) -> {U32.is_zero(capm(zz, left, mx)) == False{} : Bool}:
  match zz:
    case True{}:
      M1.u32_nonzero(left, kk, hn)
    case False{}:
      nzm

# a new block's room after its first byte is within the feed's
def cap.le(
  zz: Bool,
  +left: U32,
  +mx: U32,
  +kk: Nat,
  +nzm: {U32.is_zero(mx) == False{} : Bool},
  +ez: {U32.is_le(left, mx) == zz : Bool},
  +hn: {U32.to_nat(left) == 1n+kk : Nat}
) -> {Nat.is_le(U32.to_nat((capm(zz, left, mx) - 1 : U32)), U32.to_nat((mx - 1 : U32))) == True{} : Bool}:
  match zz:
    case True{}:
      +l1 = (left - 1 : U32)
      +m1 = (mx - 1 : U32)
      +e_l = {M1.u32_dec(left, M1.u32_nonzero(left, kk, hn)) : {U32.to_nat(left) == 1n+U32.to_nat(l1) : Nat}}
      +e_m = {M1.u32_dec(mx, nzm) : {U32.to_nat(mx) == 1n+U32.to_nat(m1) : Nat}}
      +h0 = {Equal.trans(Bool, Nat.is_le(U32.to_nat(left), U32.to_nat(mx)), U32.is_le(left, mx), True{},
        Equal.sym(Bool, U32.is_le(left, mx), Nat.is_le(U32.to_nat(left), U32.to_nat(mx)), M10.u32_le(left, mx)), ez) :
        {Nat.is_le(U32.to_nat(left), U32.to_nat(mx)) == True{} : Bool}}
      M1.le_rw_r(1n+U32.to_nat(l1), U32.to_nat(mx), 1n+U32.to_nat(m1), e_m, M1.le_rw_l(U32.to_nat(left),
        1n+U32.to_nat(l1), U32.to_nat(mx), e_l, h0))
    case False{}:
      M1.le_refl(U32.to_nat((mx - 1 : U32)))

# where a new block stands: final when the bytes left fit, else full
def cap.fo(
  zz: Bool,
  +left: U32,
  +mx: U32,
  +kk: Nat,
  +nzm: {U32.is_zero(mx) == False{} : Bool},
  +ez: {U32.is_le(left, mx) == zz : Bool},
  +hn: {U32.to_nat(left) == 1n+kk : Nat}
) -> fin.ok(zz, (capm(zz, left, mx) - 1 : U32), (mx - 1 : U32), kk):
  match zz:
    case True{}:
      M1.u32_pred(left, kk, hn)
    case False{}:
      +m1 = (mx - 1 : U32)
      +e_m = {M1.u32_dec(mx, nzm) : {U32.to_nat(mx) == 1n+U32.to_nat(m1) : Nat}}
      +h0 = {Equal.trans(Bool, Nat.is_le(1n+kk, 1n+U32.to_nat(m1)), U32.is_le(left, mx), False{},
        Equal.sym(Bool, U32.is_le(left, mx), Nat.is_le(1n+kk, 1n+U32.to_nat(m1)), Equal.trans(Bool,
          U32.is_le(left, mx), Nat.is_le(U32.to_nat(left), U32.to_nat(mx)), Nat.is_le(1n+kk, 1n+U32.to_nat(m1)),
          M10.u32_le(left, mx), Equal.trans(Bool, Nat.is_le(U32.to_nat(left), U32.to_nat(mx)), Nat.is_le(1n+kk,
          U32.to_nat(mx)), Nat.is_le(1n+kk, 1n+U32.to_nat(m1)), Equal.cong(Nat, Bool, xx => Nat.is_le(xx,
          U32.to_nat(mx)), U32.to_nat(left), 1n+kk, hn), Equal.cong(Nat, Bool, xx => Nat.is_le(1n+kk, xx),
          U32.to_nat(mx), 1n+U32.to_nat(m1), e_m)))), ez) : {Nat.is_le(kk, U32.to_nat(m1)) == False{} : Bool}}
      ({==}, nle.lt(kk, U32.to_nat(m1), h0))

# fin.ok of enc.cap.at's room from capm's
def fo.cm(
  +zz: Bool,
  +left: U32,
  +mx: U32,
  +nt: Nat,
  +emx: {mx == 65535 : U32},
  hh: fin.ok(zz, (capm(zz, left, mx) - 1 : U32), (mx - 1 : U32), nt)
) -> fin.ok(zz, (Png.enc.cap.at(zz, left) - 1 : U32), (mx - 1 : U32), nt):
  %Equal.sym(U32, Png.enc.cap.at(zz, left), capm(zz, left, mx), cap.m(zz, left, mx, emx)) : fin.ok(zz, (_ - 1 : U32),
    (mx - 1 : U32), nt)
  hh

# the header bs writes at a new block is enc.head's for the block's BFINAL
def pfin.hdr(
  zz: Bool,
  +left: U32,
  +rest: List<&2, U32>
) -> {Png.enc.bf.at(zz) <> Png.enc.byte(Png.enc.cap.at(zz, left)) <> Png.enc.hi(Png.enc.cap.at(zz,
  left)) <> Png.enc.byte((Png.enc.cap.at(zz, left) .^. 65535 : U32)) <> Png.enc.hi((Png.enc.cap.at(zz,
  left) .^. 65535 : U32)) <> rest == List.append(&2, U32, Png.enc.head(zz, Png.enc.cap.at(zz, left),
  (Png.enc.cap.at(zz, left) .^. 65535 : U32)), rest) : List<&2, U32>}:
  match zz:
    case True{}:
      {==}
    case False{}:
      {==}

# the open block, reversed, is counted to its header's length when it ends
def len.blk(
  +acc: List<&2, U32>,
  +rf: U32,
  +ll: U32,
  +mx: U32,
  +ha: {Nat.add(List.length(&2, U32, acc), U32.to_nat(rf)) == U32.to_nat(mx) : Nat},
  +hl: {U32.to_nat(ll) == List.length(&2, U32, acc) : Nat}
) -> {Png.enc.len(List.reverse(&2, U32, acc), 0) == ll : U32}:
  +ra = List.reverse(&2, U32, acc)
  +na = List.length(&2, U32, acc)
  +e_r = {M1.len_rev(acc) : {List.length(&2, U32, ra) == na : Nat}}
  +h_b = {Equal.trans(Bool, Nat.is_le(na, U32.to_nat(mx)), Nat.is_le(na, Nat.add(na, U32.to_nat(rf))), True{},
    Equal.cong(Nat, Bool, kk => Nat.is_le(na, kk), U32.to_nat(mx), Nat.add(na, U32.to_nat(rf)), Equal.sym(Nat,
    Nat.add(na, U32.to_nat(rf)), U32.to_nat(mx), ha)), M8.nle_add(na, U32.to_nat(rf))) : {Nat.is_le(na,
    U32.to_nat(mx)) == True{} : Bool}}
  +h_r = {M1.le_rw_l(na, List.length(&2, U32, ra), U32.to_nat(mx), Equal.sym(Nat, List.length(&2, U32, ra), na, e_r),
    h_b) : {Nat.is_le(List.length(&2, U32, ra), U32.to_nat(mx)) == True{} : Bool}}
  M1.u32.same(Png.enc.len(ra, 0), ll, Equal.trans(Nat, U32.to_nat(Png.enc.len(ra, 0)), na, U32.to_nat(ll),
      Equal.trans(Nat,
    U32.to_nat(Png.enc.len(ra, 0)), List.length(&2, U32, ra), na, len.of(ra, mx, h_r), e_r), Equal.sym(Nat,
    U32.to_nat(ll), na, hl)))

# no bytes left: the open block is enc.feed's final block
def sim.nil(
  fin: Bool,
  +acc: List<&2, U32>,
  +rf: U32,
  +rp: U32,
  +ll: U32,
  +mx: U32,
  +ha: {Nat.add(List.length(&2, U32, acc), U32.to_nat(rf)) == U32.to_nat(mx) : Nat},
  +hl: {U32.to_nat(ll) == Nat.add(List.length(&2, U32, acc), U32.to_nat(rp)) : Nat},
  hf: fin.ok(fin, rp, rf, 0n)
) -> {List.append(&2, U32, Png.enc.head(fin, ll, (ll .^. 65535 : U32)), List.reverse(&2, U32, acc)) ==
  Png.enc.stored(True{}, List.reverse(&2, U32, acc)) : List<&2, U32>}:
  match fin:
    case False{}:
      (_e_rr, h_lt) = hf
      Empty.absurd({List.append(&2, U32, Png.enc.head(False{}, ll, (ll .^. 65535 : U32)), List.reverse(&2, U32, acc)) ==
        Png.enc.stored(True{}, List.reverse(&2, U32, acc)) : List<&2, U32>}, M1.false_true(Equal.trans(Bool,
        False{}, Nat.is_lt(U32.to_nat(rp), 0n), True{}, M1.lt_zero_false(U32.to_nat(rp)), h_lt)))
    case True{}:
      +e_rp = {hf : {U32.to_nat(rp) == 0n : Nat}}
      +ra = List.reverse(&2, U32, acc)
      +na = List.length(&2, U32, acc)
      +hd = Png.enc.head(True{}, ll, (ll .^. 65535 : U32))
      +hl0 = {Equal.trans(Nat, U32.to_nat(ll), Nat.add(na, 0n), na, Equal.trans(Nat, U32.to_nat(ll), Nat.add(na,
        U32.to_nat(rp)), Nat.add(na, 0n), hl, Equal.cong(Nat, Nat, kk => Nat.add(na, kk), U32.to_nat(rp), 0n, e_rp)),
        M1.ras.add_zero(na)) : {U32.to_nat(ll) == na : Nat}}
      +e_len = {len.blk(acc, rf, ll, mx, ha, hl0) : {Png.enc.len(ra, 0) == ll : U32}}
      Equal.trans(List<&2, U32>, List.append(&2, U32, hd, ra), Png.enc.cat(hd, ra), Png.enc.stored(True{}, ra),
        Equal.sym(List<&2, U32>, Png.enc.cat(hd, ra), List.append(&2, U32, hd, ra), M8.cat_app(hd, ra)),
        Equal.cong(U32, List<&2, U32>, uu => Png.enc.cat(Png.enc.head(True{}, uu, (uu .^. 65535 : U32)), ra), ll,
          Png.enc.len(ra, 0), Equal.sym(U32, Png.enc.len(ra, 0), ll, e_len)))

# a new block's bytes as bs writes them for length u and BFINAL v: the
# header, the first byte, then the rest of the walk
def open.bs(
  +hd: U32,
  +tl: List<&2, U32>,
  +l2: U32,
  +uu: U32,
  +vv: U32
) -> List<&2, U32>:
  +nlen = (uu .^. 65535 : U32)
  +room2 = (uu - 1 : U32)
  vv <> Png.enc.byte(uu) <> Png.enc.hi(uu) <> Png.enc.byte(nlen) <> Png.enc.hi(nlen) <> hd <> M1.bs(tl,
      U32.is_zero(room2),
    U32.is_eq(room2, 1), room2, l2, Png.enc.cap(l2), Png.enc.bf(l2))

# a new block's header for left bytes, as enc.feed opens it
def hd1(+left: U32) -> List<&2, U32>:
  Png.enc.head(U32.is_le(left, 65535), Png.enc.cap(left), (Png.enc.cap(left) .^. 65535 : U32))

# bs after a new block's first byte, for left bytes
def bs1(+tl: List<&2, U32>, +left: U32) -> List<&2, U32>:
  +room = (Png.enc.cap(left) - 1 : U32)
  M1.bs(tl, U32.is_zero(room), U32.is_eq(room, 1), room, (left - 1 : U32), Png.enc.cap((left - 1 : U32)),
    Png.enc.bf((left - 1 : U32)))

# enc.feed after a new block's first byte hd
def fd1(+tl: List<&2, U32>, +mx: U32, +hd: U32) -> List<&2, U32>:
  Png.enc.feed(tl, U32.is_zero((mx - 1 : U32)), (mx - 1 : U32), mx, [hd])

# a new block from left bytes, hd then tl: bs's bytes are enc.feed's from a
# block holding hd alone
def open.feed(
  +hd: U32,
  +tl: List<&2, U32>,
  +left: U32,
  +mx: U32,
  +ih: {List.append(&2, U32, hd1(left), hd <> bs1(tl, left)) == fd1(tl, mx, hd) : List<&2, U32>}
) -> {open.bs(hd, tl, (left - 1 : U32), Png.enc.cap(left), Png.enc.bf(left)) == Png.enc.feed(tl,
  U32.is_zero((mx - 1 : U32)), (mx - 1 : U32), mx, [hd]) : List<&2, U32>}:
  +zz = U32.is_le(left, 65535)
  +cp = Png.enc.cap(left)
  +l2 = (left - 1 : U32)
  +q = M1.bs(tl, U32.is_zero((cp - 1 : U32)), U32.is_eq((cp - 1 : U32), 1), (cp - 1 : U32), l2, Png.enc.cap(l2),
    Png.enc.bf(l2))
  Equal.trans(List<&2, U32>, open.bs(hd, tl, l2, cp, Png.enc.bf(left)), List.append(&2, U32, Png.enc.head(zz, cp,
    (cp .^.
    65535 : U32)), hd <> q), Png.enc.feed(tl, U32.is_zero((mx - 1 : U32)), (mx - 1 : U32), mx, [hd]),
    pfin.hdr(zz, left, hd <> q), ih)

# the simulation's hypothesis for the rest of a block opened by hd
def open.ih.ty(+hd: U32, +tl: List<&2, U32>, +left: U32, +mx: U32) -> Type:
  @zn: Bool -> @zl: Bool -> @zf: Bool -> @fin: Bool -> @rf: U32 -> @rp: U32 -> @plen: U32 -> @pbf: U32 ->
    @ll: U32 -> {zn == U32.is_zero(rp) : Bool} -> {zl == U32.is_eq(rp, 1) : Bool} -> {zf == U32.is_zero(rf) : Bool} ->
    {Nat.add(1n, U32.to_nat(rf)) == U32.to_nat(mx) : Nat} -> {U32.to_nat(ll) == Nat.add(1n, U32.to_nat(rp)) : Nat}
    -> {Nat.is_le(U32.to_nat(rp), U32.to_nat(rf)) == True{} : Bool} -> {U32.to_nat((left - 1 : U32)) ==
    List.length(&2, U32, tl) : Nat} -> fin.ok(fin, rp, rf, List.length(&2, U32, tl)) -> M1.at.edge(rp, (left - 1 : U32),
    plen, pbf) -> sim.ty(tl, zn, zl, zf, fin, [hd], rf, rp, (left - 1 : U32), plen, pbf, ll, mx)

# the facts a new block's walk starts from, for sim: the feed holds hd, with
# mx - 1 bytes of room; bs has cap(left) - 1 left in the block
def open.ih(
  +hd: U32,
  +tl: List<&2, U32>,
  +left: U32,
  +mx: U32,
  +emx: {mx == 65535 : U32},
  +hn: {U32.to_nat(left) == 1n+List.length(&2, U32, tl) : Nat},
  sim_t: open.ih.ty(hd, tl, left, mx)
) -> {open.bs(hd, tl, (left - 1 : U32), Png.enc.cap(left), Png.enc.bf(left)) == Png.enc.feed(tl,
  U32.is_zero((mx - 1 : U32)), (mx - 1 : U32), mx, [hd]) : List<&2, U32>}:
  +nt = List.length(&2, U32, tl)
  +zz = U32.is_le(left, 65535)
  +cp = Png.enc.cap(left)
  +cm = capm(zz, left, mx)
  +c1 = (cp - 1 : U32)
  +m1 = (mx - 1 : U32)
  +l2 = (left - 1 : U32)
  +nzm = {mx.nz(mx, emx) : {U32.is_zero(mx) == False{} : Bool}}
  +e_cm = {cap.m(zz, left, mx, emx) : {cp == cm : U32}}
  +ezm = {le.mx(left, mx, emx) : {U32.is_le(left, mx) == zz : Bool}}
  +nz_cp = {Equal.trans(Bool, U32.is_zero(cp), U32.is_zero(cm), False{}, Equal.cong(U32, Bool, uu => U32.is_zero(uu),
    cp, cm, e_cm), cap.nz(zz, left, mx, nt, nzm, hn)) : {U32.is_zero(cp) == False{} : Bool}}
  +ha2 = {Equal.sym(Nat, U32.to_nat(mx), 1n+U32.to_nat(m1), M1.u32_dec(mx, nzm)) : {Nat.add(1n, U32.to_nat(m1)) ==
    U32.to_nat(mx) : Nat}}
  +hl2 = {M1.u32_dec(cp, nz_cp) : {U32.to_nat(cp) == Nat.add(1n, U32.to_nat(c1)) : Nat}}
  +hle2 = {Equal.trans(Bool, Nat.is_le(U32.to_nat(c1), U32.to_nat(m1)), Nat.is_le(U32.to_nat((cm - 1 : U32)),
    U32.to_nat(m1)), True{}, Equal.cong(U32, Bool, uu => Nat.is_le(U32.to_nat((uu - 1 : U32)), U32.to_nat(m1)), cp, cm,
    e_cm), cap.le(zz, left, mx, nt, nzm, ezm, hn)) : {Nat.is_le(U32.to_nat(c1), U32.to_nat(m1)) == True{} : Bool}}
  +hn2 = {M1.u32_pred(left, nt, hn) : {U32.to_nat(l2) == nt : Nat}}
  hf2 = {fo.cm(zz, left, mx, nt, emx, cap.fo(zz, left, mx, nt, nzm, ezm, hn)) : fin.ok(zz, c1, m1, nt)}
  open.feed(hd, tl, left, mx, sim_t(U32.is_zero(c1), U32.is_eq(c1, 1), U32.is_zero(m1), zz, m1, c1, Png.enc.cap(l2),
    Png.enc.bf(l2), cp, {==}, {==}, {==}, ha2, hl2, hle2, hn2, hf2, _ez => ({==}, {==})))

# a block boundary with bytes left: the full block closes and a new one opens
def sim.edge(
  fin: Bool,
  +hd: U32,
  +tl: List<&2, U32>,
  +acc: List<&2, U32>,
  +rf: U32,
  +rp: U32,
  +left: U32,
  +plen: U32,
  +pbf: U32,
  +ll: U32,
  +mx: U32,
  +zf: Bool,
  +hzf: {zf == U32.is_zero(rf) : Bool},
  +ha: {Nat.add(List.length(&2, U32, acc), U32.to_nat(rf)) == U32.to_nat(mx) : Nat},
  +hl: {U32.to_nat(ll) == Nat.add(List.length(&2, U32, acc), U32.to_nat(rp)) : Nat},
  +e0: {U32.to_nat(rp) == 0n : Nat},
  +e_ob: {open.bs(hd, tl, (left - 1 : U32), Png.enc.cap(left), Png.enc.bf(left)) == fd1(tl, mx, hd) : List<&2, U32>},
  hf: fin.ok(fin, rp, rf, 1n+List.length(&2, U32, tl)),
  pe: {plen == Png.enc.cap(left) : U32} & {pbf == Png.enc.bf(left) : U32}
) -> {List.append(&2, U32, Png.enc.head(fin, ll, (ll .^. 65535 : U32)), List.reverse.go(&2, U32, acc, open.bs(hd, tl,
  (left - 1 : U32), plen, pbf))) == Png.enc.feed(hd <> tl, zf, rf, mx, acc) : List<&2, U32>}:
  match fin:
    case True{}:
      Empty.absurd({List.append(&2, U32, Png.enc.head(True{}, ll, (ll .^. 65535 : U32)), List.reverse.go(&2, U32, acc,
        open.bs(hd, tl, (left - 1 : U32), plen, pbf))) == Png.enc.feed(hd <> tl, zf, rf, mx, acc) : List<&2, U32>},
        M1.zero_succ(List.length(&2, U32, tl), Equal.trans(Nat, 0n, U32.to_nat(rp), 1n+List.length(&2, U32, tl),
        Equal.sym(Nat, U32.to_nat(rp), 0n, e0), hf)))
    case False{}:
      (e_rr, _h_lt) = hf
      (e_plen, e_pbf) = pe
      +na = List.length(&2, U32, acc)
      +ra = List.reverse(&2, U32, acc)
      +l2 = (left - 1 : U32)
      +cp = Png.enc.cap(left)
      +e_rf0 = {Equal.trans(Nat, U32.to_nat(rf), U32.to_nat(rp), 0n, Equal.sym(Nat, U32.to_nat(rp), U32.to_nat(rf),
        e_rr), e0) : {U32.to_nat(rf) == 0n : Nat}}
      +e_zf = {Equal.trans(Bool, zf, U32.is_zero(rf), True{}, hzf, zero.is(rf, e_rf0)) : {zf == True{} : Bool}}
      +ff = Png.enc.feed(tl, U32.is_zero((mx - 1 : U32)), (mx - 1 : U32), mx, [hd])
      +hd0 = Png.enc.head(False{}, ll, (ll .^. 65535 : U32))
      +hl0 = {Equal.trans(Nat, U32.to_nat(ll), Nat.add(na, 0n), na, Equal.trans(Nat, U32.to_nat(ll), Nat.add(na,
        U32.to_nat(rp)), Nat.add(na, 0n), hl, Equal.cong(Nat, Nat, kk => Nat.add(na, kk), U32.to_nat(rp), 0n, e0)),
        M1.ras.add_zero(na)) : {U32.to_nat(ll) == na : Nat}}
      +e_len = {len.blk(acc, rf, ll, mx, ha, hl0) : {Png.enc.len(ra, 0) == ll : U32}}
      +e_bs = {Equal.trans(List<&2, U32>, open.bs(hd, tl, l2, plen, pbf), open.bs(hd, tl, l2, cp, Png.enc.bf(left)), ff,
        Equal.trans(List<&2, U32>, open.bs(hd, tl, l2, plen, pbf), open.bs(hd, tl, l2, cp, pbf), open.bs(hd, tl, l2, cp,
          Png.enc.bf(left)), Equal.cong(U32, List<&2, U32>, uu => open.bs(hd, tl, l2, uu, pbf), plen, cp, e_plen),
          Equal.cong(U32, List<&2, U32>, uu => open.bs(hd, tl, l2, cp, uu), pbf, Png.enc.bf(left), e_pbf)),
        e_ob) : {open.bs(hd, tl, l2, plen, pbf) == ff : List<&2, U32>}}
      Equal.trans(List<&2, U32>, List.append(&2, U32, hd0, List.reverse.go(&2, U32, acc, open.bs(hd, tl, l2, plen,
        pbf))),
        List.append(&2, U32, List.append(&2, U32, hd0, ra), ff), Png.enc.feed(hd <> tl, zf, rf, mx, acc),
        Equal.trans(List<&2, U32>, List.append(&2, U32, hd0, List.reverse.go(&2, U32, acc, open.bs(hd, tl, l2, plen,
          pbf))), List.append(&2, U32, hd0, List.append(&2, U32, ra, ff)), List.append(&2, U32, List.append(&2, U32,
          hd0, ra), ff),
          Equal.trans(List<&2, U32>, List.append(&2, U32, hd0, List.reverse.go(&2, U32, acc, open.bs(hd, tl, l2, plen,
            pbf))), List.append(&2, U32, hd0, List.reverse.go(&2, U32, acc, ff)), List.append(&2, U32, hd0,
            List.append(&2, U32, ra, ff)),
            Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.append(&2, U32, hd0, List.reverse.go(&2, U32, acc,
              ys)), open.bs(hd, tl, l2, plen, pbf), ff, e_bs),
            Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.append(&2, U32, hd0, ys), List.reverse.go(&2, U32, acc,
              ff), List.append(&2, U32, ra, ff), M4.revgo_acc(acc, [], ff))),
          Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, hd0, ra), ff), List.append(&2, U32, hd0,
            List.append(&2, U32, ra, ff)), M1.app_assoc(hd0, ra, ff))),
        Equal.trans(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, hd0, ra), ff), Png.enc.feed(hd <> tl,
          True{},
          rf, mx, acc), Png.enc.feed(hd <> tl, zf, rf, mx, acc),
          Equal.trans(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, hd0, ra), ff), List.append(&2, U32,
            Png.enc.cat(hd0, ra), ff), Png.enc.feed(hd <> tl, True{}, rf, mx, acc),
            Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.append(&2, U32, ys, ff), List.append(&2, U32, hd0, ra),
              Png.enc.cat(hd0, ra), Equal.sym(List<&2, U32>, Png.enc.cat(hd0, ra), List.append(&2, U32, hd0, ra),
              M8.cat_app(hd0, ra))),
            Equal.trans(List<&2, U32>, List.append(&2, U32, Png.enc.cat(hd0, ra), ff), Png.enc.cat(Png.enc.cat(hd0,
              ra), ff), Png.enc.feed(hd <> tl, True{}, rf, mx, acc),
              Equal.sym(List<&2, U32>, Png.enc.cat(Png.enc.cat(hd0, ra), ff), List.append(&2, U32, Png.enc.cat(hd0,
                ra), ff), M8.cat_app(Png.enc.cat(hd0, ra), ff)),
              Equal.cong(U32, List<&2, U32>, uu => Png.enc.cat(Png.enc.cat(Png.enc.head(False{}, uu, (uu .^. 65535 :
                U32)), ra), ff), ll, Png.enc.len(ra, 0), Equal.sym(U32, Png.enc.len(ra, 0), ll, e_len)))),
          Equal.cong(Bool, List<&2, U32>, zb => Png.enc.feed(hd <> tl, zb, rf, mx, acc), True{}, zf, Equal.sym(Bool,
            zf, True{}, e_zf))))

# bs against enc.feed: the open block (acc, newest first, with rf bytes of
# room in the feed) under a header of length ll and BFINAL fin, then bs from
# rp bytes left in the block, are enc.feed's blocks
def sim(
  xs: List<&2, U32>,
  znew: Bool,
  zlast: Bool,
  +zf: Bool,
  +fin: Bool,
  +acc: List<&2, U32>,
  +rf: U32,
  +rp: U32,
  +left: U32,
  +plen: U32,
  +pbf: U32,
  +ll: U32,
  +mx: U32,
  +emx: {mx == 65535 : U32},
  +hzn: {znew == U32.is_zero(rp) : Bool},
  +hzl: {zlast == U32.is_eq(rp, 1) : Bool},
  +hzf: {zf == U32.is_zero(rf) : Bool},
  +ha: {Nat.add(List.length(&2, U32, acc), U32.to_nat(rf)) == U32.to_nat(mx) : Nat},
  +hl: {U32.to_nat(ll) == Nat.add(List.length(&2, U32, acc), U32.to_nat(rp)) : Nat},
  +hle: {Nat.is_le(U32.to_nat(rp), U32.to_nat(rf)) == True{} : Bool},
  +hn: {U32.to_nat(left) == List.length(&2, U32, xs) : Nat},
  hf: fin.ok(fin, rp, rf, List.length(&2, U32, xs)),
  hb: M1.at.edge(rp, left, plen, pbf)
) -> sim.ty(xs, znew, zlast, zf, fin, acc, rf, rp, left, plen, pbf, ll, mx):
  match xs znew zlast:
    case Nil{} _zn _zl:
      sim.nil(fin, acc, rf, rp, ll, mx, ha, hl, hf)
    case +h <> +t False{} False{}:
      +rp2 = (rp - 1 : U32)
      +rf2 = (rf - 1 : U32)
      +l2 = (left - 1 : U32)
      +nt = List.length(&2, U32, t)
      +na = List.length(&2, U32, acc)
      +nz_rp = {Equal.sym(Bool, False{}, U32.is_zero(rp), hzn) : {U32.is_zero(rp) == False{} : Bool}}
      +e_rp = {M1.u32_dec(rp, nz_rp) : {U32.to_nat(rp) == 1n+U32.to_nat(rp2) : Nat}}
      +nz_rp2 = {M1.two(rp, hzn, hzl) : {U32.is_zero(rp2) == False{} : Bool}}
      +h_rf = {M1.le_rw_l(U32.to_nat(rp), 1n+U32.to_nat(rp2), U32.to_nat(rf), e_rp, hle) :
        {Nat.is_le(1n+U32.to_nat(rp2), U32.to_nat(rf)) == True{} : Bool}}
      +nz_rf = {M10.pos(rf, U32.to_nat(rp2), h_rf) : {U32.is_zero(rf) == False{} : Bool}}
      +e_rf = {M1.u32_dec(rf, nz_rf) : {U32.to_nat(rf) == 1n+U32.to_nat(rf2) : Nat}}
      +e_zf = {Equal.trans(Bool, zf, U32.is_zero(rf), False{}, hzf, nz_rf) : {zf == False{} : Bool}}
      +ha2 = {M1.shift(na, rf, rf2, U32.to_nat(mx), e_rf, ha) : {Nat.add(1n+na,
          U32.to_nat(rf2)) == U32.to_nat(mx) : Nat}}
      +hl2 = {Equal.sym(Nat, Nat.add(1n+na, U32.to_nat(rp2)), U32.to_nat(ll), M1.shift(na, rp, rp2, U32.to_nat(ll),
          e_rp,
        Equal.sym(Nat, U32.to_nat(ll), Nat.add(na, U32.to_nat(rp)), hl))) : {U32.to_nat(ll) == Nat.add(1n+na,
        U32.to_nat(rp2)) : Nat}}
      +hle2 = {M1.le_rw_r(1n+U32.to_nat(rp2), U32.to_nat(rf), 1n+U32.to_nat(rf2), e_rf, h_rf) :
        {Nat.is_le(U32.to_nat(rp2), U32.to_nat(rf2)) == True{} : Bool}}
      +hn2 = {M1.u32_pred(left, nt, hn) : {U32.to_nat(l2) == nt : Nat}}
      hf2 = {fo.dec(fin, rp, rf, rp2, rf2, nt, e_rp, e_rf, hf) : fin.ok(fin, rp2, rf2, nt)}
      Equal.trans(List<&2, U32>, List.append(&2, U32, Png.enc.head(fin, ll, (ll .^. 65535 : U32)), List.reverse.go(&2,
        U32, acc, M1.bs(h <> t, False{}, False{}, rp, left, plen, pbf))), Png.enc.feed(h <> t, False{}, rf, mx, acc),
        Png.enc.feed(h <> t, zf, rf, mx, acc),
        sim(t, False{}, U32.is_eq(rp2, 1), U32.is_zero(rf2), fin, h <> acc, rf2, rp2, l2, plen, pbf, ll, mx, emx,
          Equal.sym(Bool, U32.is_zero(rp2), False{}, nz_rp2), {==}, {==}, ha2, hl2, hle2, hn2, hf2, M1.edge.no(rp2, l2,
          plen, pbf, nz_rp2)),
        Equal.cong(Bool, List<&2, U32>, zb => Png.enc.feed(h <> t, zb, rf, mx, acc), False{}, zf, Equal.sym(Bool, zf,
          False{}, e_zf)))
    case +h <> +t False{} True{}:
      +rf2 = (rf - 1 : U32)
      +l2 = (left - 1 : U32)
      +nt = List.length(&2, U32, t)
      +na = List.length(&2, U32, acc)
      +e_rp = {M1.one.val(rp, hzl) : {U32.to_nat(rp) == 1n+U32.to_nat(0) : Nat}}
      +h_rf = {M1.le_rw_l(U32.to_nat(rp), 1n, U32.to_nat(rf), e_rp, hle) : {Nat.is_le(1n, U32.to_nat(rf)) == True{} :
        Bool}}
      +nz_rf = {M10.pos(rf, 0n, h_rf) : {U32.is_zero(rf) == False{} : Bool}}
      +e_rf = {M1.u32_dec(rf, nz_rf) : {U32.to_nat(rf) == 1n+U32.to_nat(rf2) : Nat}}
      +e_zf = {Equal.trans(Bool, zf, U32.is_zero(rf), False{}, hzf, nz_rf) : {zf == False{} : Bool}}
      +ha2 = {M1.shift(na, rf, rf2, U32.to_nat(mx), e_rf, ha) : {Nat.add(1n+na,
          U32.to_nat(rf2)) == U32.to_nat(mx) : Nat}}
      +hl2 = {Equal.sym(Nat, Nat.add(1n+na, U32.to_nat(0)), U32.to_nat(ll), M1.shift(na, rp, 0, U32.to_nat(ll), e_rp,
        Equal.sym(Nat, U32.to_nat(ll), Nat.add(na, U32.to_nat(rp)), hl))) : {U32.to_nat(ll) == Nat.add(1n+na,
        U32.to_nat(0)) : Nat}}
      +hle2 = {M1.le_zero(U32.to_nat(rf2)) : {Nat.is_le(U32.to_nat(0), U32.to_nat(rf2)) == True{} : Bool}}
      +hn2 = {M1.u32_pred(left, nt, hn) : {U32.to_nat(l2) == nt : Nat}}
      hf2 = {fo.dec(fin, rp, rf, 0, rf2, nt, e_rp, e_rf, hf) : fin.ok(fin, 0, rf2, nt)}
      Equal.trans(List<&2, U32>, List.append(&2, U32, Png.enc.head(fin, ll, (ll .^. 65535 : U32)), List.reverse.go(&2,
        U32, acc, M1.bs(h <> t, False{}, True{}, rp, left, plen, pbf))), Png.enc.feed(h <> t, False{}, rf, mx, acc),
        Png.enc.feed(h <> t, zf, rf, mx, acc),
        sim(t, True{}, False{}, U32.is_zero(rf2), fin, h <> acc, rf2, 0, l2, Png.enc.cap(l2), Png.enc.bf(l2), ll, mx,
          emx, {==}, {==}, {==}, ha2, hl2, hle2, hn2, hf2, _ez => ({==}, {==})),
        Equal.cong(Bool, List<&2, U32>, zb => Png.enc.feed(h <> t, zb, rf, mx, acc), False{}, zf, Equal.sym(Bool, zf,
          False{}, e_zf)))
    case +h <> +t True{} _zl:
      +l2 = (left - 1 : U32)
      +ez = {Equal.sym(Bool, True{}, U32.is_zero(rp), hzn) : {U32.is_zero(rp) == True{} : Bool}}
      +e0 = {M1.zero.val(rp, hzn) : {U32.to_nat(rp) == 0n : Nat}}
      +e_ob = {open.ih(h, t, left, mx, emx, hn, zn => zl => zb => fb => rf3 => rp3 => pl3 => pb3 => ll3 => a1 => a2 =>
        a3 => a4 => a5 => a6 => a7 => a8 => a9 => sim(t, zn, zl, zb, fb, [h], rf3, rp3, l2, pl3, pb3, ll3, mx, emx,
        a1, a2, a3, a4, a5, a6, a7, a8, a9)) : {open.bs(h, t, l2, Png.enc.cap(left), Png.enc.bf(left)) ==
        Png.enc.feed(t, U32.is_zero((mx - 1 : U32)), (mx - 1 : U32), mx, [h]) : List<&2, U32>}}
      sim.edge(fin, h, t, acc, rf, rp, left, plen, pbf, ll, mx, zf, hzf, ha, hl, e0, e_ob, hf, hb(ez))

# the first block: bs from the start writes enc.feed's blocks for every
# non-empty list of left bytes
def sim.start(
  +hd: U32,
  +tl: List<&2, U32>,
  +left: U32,
  +mx: U32,
  +emx: {mx == 65535 : U32},
  +hn: {U32.to_nat(left) == 1n+List.length(&2, U32, tl) : Nat}
) -> {M1.bs(hd <> tl, True{}, False{}, 0, left, Png.enc.cap(left), Png.enc.bf(left)) == Png.enc.feed(hd <> tl, False{},
  mx, mx, []) : List<&2, U32>}:
  +l2 = (left - 1 : U32)
  open.ih(hd, tl, left, mx, emx, hn, zn => zl => zb => fb => rf3 => rp3 => pl3 => pb3 => ll3 => a1 => a2 => a3 => a4 =>
    a5 => a6 => a7 => a8 => a9 => sim(tl, zn, zl, zb, fb, [hd], rf3, rp3, l2, pl3, pb3, ll3, mx, emx, a1, a2, a3, a4,
      a5,
    a6, a7, a8, a9))

# enc.blocks at 65535 for a list longer than one block is bs from the start
def sim.blocks(
  xs: List<&2, U32>,
  +mx: U32,
  +emx: {mx == 65535 : U32},
  +hn: {U32.to_nat(Png.enc.len(xs, 0)) == List.length(&2, U32, xs) : Nat},
  +hbig: {U32.is_le(Png.enc.len(xs, 0), 65535) == False{} : Bool}
) -> {Png.enc.blocks(65535, xs) == M1.bs(xs, True{}, False{}, 0, Png.enc.len(xs, 0), Png.enc.cap(Png.enc.len(xs, 0)),
  Png.enc.bf(Png.enc.len(xs, 0))) : List<&2, U32>}:
  match xs:
    case Nil{}:
      Empty.absurd({Png.enc.blocks(65535, []) == M1.bs([], True{}, False{}, 0, 0, Png.enc.cap(0), Png.enc.bf(0)) :
        List<&2, U32>}, M1.false_true(Equal.sym(Bool, True{}, False{}, hbig)))
    case +h <> +t:
      +nn = Png.enc.len(h <> t, 0)
      +bb = M1.bs(h <> t, True{}, False{}, 0, nn, Png.enc.cap(nn), Png.enc.bf(nn))
      Equal.trans(List<&2, U32>, Png.enc.blocks(65535, h <> t), Png.enc.blocks.fit(False{}, 65535, nn, h <> t), bb,
        Equal.cong(Bool, List<&2, U32>, zb => Png.enc.blocks.fit(zb, 65535, nn, h <> t), U32.is_le(nn, 65535), False{},
          hbig),
        Equal.trans(List<&2, U32>, Png.enc.feed(h <> t, False{}, 65535, 65535, []), Png.enc.feed(h <> t, False{}, mx,
          mx,
          []), bb, Equal.cong(U32, List<&2, U32>, uu => Png.enc.feed(h <> t, False{}, uu, uu, []), 65535, mx,
          Equal.sym(U32, mx, 65535, emx)), Equal.sym(List<&2, U32>, bb, Png.enc.feed(h <> t, False{}, mx, mx, []),
          sim.start(h, t, nn, mx, emx, hn))))

# ---- D. U32.div and U32.mod ----

# a word shifted left with c coming in: nothing falls out, and it is c + 2 w
def sho.ok(nn: Nat, +cc: Bool, +ww: Word(nn), pp: Bool & Word(nn)) -> Type:
  match pp:
    case (tt, ss):
      {tt == False{} : Bool} & {Word.to_nat(nn, ss) == Nat.add(M1.bit(cc), Nat.double(Word.to_nat(nn, ww))) : Nat}

# one step of so: the lower bits shifted, then this bit in front
def sho.step(
  +pp: Nat,
  +cc: Bool,
  +bb: Bool,
  +tt: Word(pp),
  yy: Bool & Word(pp),
  ih: sho.ok(pp, bb, tt, yy)
) -> sho.ok(1n+pp, cc, WCon{bb, tt}, Word.shl.out.con(pp, cc, yy)):
  match yy:
    case (hi, +t2):
      (e_hi, e_t2) = ih
      +vt = Word.to_nat(pp, tt)
      (e_hi, Equal.trans(Nat, Word.to_nat(1n+pp, WCon{cc, t2}), Nat.add(M1.bit(cc), Nat.double(Word.to_nat(pp, t2))),
        Nat.add(M1.bit(cc), Nat.double(Word.to_nat(1n+pp, WCon{bb, tt}))), M1.to_nat_con(pp, cc, t2),
        Equal.cong(Nat, Nat, kk => Nat.add(M1.bit(cc), Nat.double(kk)), Word.to_nat(pp, t2), Word.to_nat(1n+pp,
          WCon{bb, tt}), Equal.trans(Nat, Word.to_nat(pp, t2), Nat.add(M1.bit(bb), Nat.double(vt)), Word.to_nat(1n+pp,
          WCon{bb, tt}), e_t2, Equal.sym(Nat, Word.to_nat(1n+pp, WCon{bb, tt}), Nat.add(M1.bit(bb), Nat.double(vt)),
          M1.to_nat_con(pp, bb, tt))))))

# shifting a word left with c coming in, when c + 2 w is at most a word's value
def sho(
  nn: Nat,
  +cc: Bool,
  +ww: Word(nn),
  +tw: Word(nn),
  +hh: {Nat.is_le(Nat.add(M1.bit(cc), Nat.double(Word.to_nat(nn, ww))), Word.to_nat(nn, tw)) == True{} : Bool}
) -> sho.ok(nn, cc, ww, Word.shl.out(nn, cc, ww)):
  match nn:
    case 0n:
      match cc ww tw:
        case False{} WNil{} WNil{}:
          ({==}, {==})
        case True{} WNil{} WNil{}:
          Empty.absurd(sho.ok(0n, True{}, WNil{}, (True{}, WNil{})), M1.false_true(hh))
    case 1n+(+pp):
      match ww tw:
        case WCon{+bb, +tt} WCon{+sb, +st}:
          +vt = Word.to_nat(pp, tt)
          +vs = Word.to_nat(pp, st)
          +wb = Word.to_nat(1n+pp, WCon{bb, tt})
          +ws = Word.to_nat(1n+pp, WCon{sb, st})
          +xb = Nat.add(M1.bit(bb), Nat.double(vt))
          +xs = Nat.add(M1.bit(sb), Nat.double(vs))
          +h0 = {M10.le_add_l(M1.bit(cc), Nat.double(wb), ws, hh) : {Nat.is_le(Nat.double(wb), ws) == True{} : Bool}}
          +h1 = {M1.le_rw_r(Nat.double(xb), ws, xs, M1.to_nat_con(pp, sb, st), M1.le_rw_l(Nat.double(wb),
              Nat.double(xb),
            ws, Equal.cong(Nat, Nat, kk => Nat.double(kk), wb, xb, M1.to_nat_con(pp, bb, tt)), h0)) :
            {Nat.is_le(Nat.double(xb), xs) == True{} : Bool}}
          +h2 = {M10.le_half(sb, xb, vs, h1) : {Nat.is_le(xb, vs) == True{} : Bool}}
          sho.step(pp, cc, bb, tt, Word.shl.out(pp, bb, tt), sho(pp, bb, tt, st, h2))

# at least in Cmp is at most the other way
def ge.le(
  aa: Nat,
  bb: Nat,
  +hh: {Cmp.is_ge(Nat.cmp(aa, bb)) == True{} : Bool}
) -> {Nat.is_le(bb, aa) == True{} : Bool}:
  match aa bb:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({Nat.is_le(1n+bp, 0n) == True{} : Bool}, M1.false_true(hh))
    case 1n+_ap 0n:
      {==}
    case 1n+ap 1n+bp:
      ge.le(ap, bp, hh)

# not at least in Cmp is below
def nge.lt(
  aa: Nat,
  bb: Nat,
  +hh: {Cmp.is_ge(Nat.cmp(aa, bb)) == False{} : Bool}
) -> {Nat.is_lt(aa, bb) == True{} : Bool}:
  match aa bb:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, M1.false_true(Equal.sym(Bool, True{}, False{}, hh)))
    case 0n 1n+_bp:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.is_lt(1n+ap, 0n) == True{} : Bool}, M1.false_true(Equal.sym(Bool, True{}, False{}, hh)))
    case 1n+ap 1n+bp:
      nge.lt(ap, bp, hh)

# U32.is_ge is Nat's
def u.ge(+uu: U32, +vv: U32) -> {U32.is_ge(uu, vv) == Cmp.is_ge(Nat.cmp(U32.to_nat(uu), U32.to_nat(vv))) : Bool}:
  Equal.cong(Cmp, Bool, cc => Cmp.is_ge(cc), U32.cmp(uu, vv), Nat.cmp(U32.to_nat(uu), U32.to_nat(vv)), M1.u_cmp(uu,
    vv))

# a bit plus x is below y when 2 plus x is at most y
def bit.lt(
  aa: Bool,
  +xx: Nat,
  +yy: Nat,
  +hh: {Nat.is_le(2n+xx, yy) == True{} : Bool}
) -> {Nat.is_lt(Nat.add(M1.bit(aa), xx), yy) == True{} : Bool}:
  match aa:
    case False{}:
      Equal.trans(Bool, Nat.is_lt(xx, yy), Nat.is_le(1n+xx, yy), True{}, M1.lt_le_succ(xx, yy), M1.le_trans(1n+xx,
          2n+xx,
        yy, M10.le_succ(1n+xx), hh))
    case True{}:
      Equal.trans(Bool, Nat.is_lt(1n+xx, yy), Nat.is_le(2n+xx, yy), True{}, M1.lt_le_succ(1n+xx, yy), hh)

# 2 r and a bit is below 2 b when r is below b
def dbl.lt(
  +aa: Bool,
  +rn: Nat,
  +bn: Nat,
  +hh: {Nat.is_lt(rn, bn) == True{} : Bool}
) -> {Nat.is_lt(Nat.add(M1.bit(aa), Nat.double(rn)), Nat.add(bn, bn)) == True{} : Bool}:
  +h1 = {Equal.trans(Bool, Nat.is_le(1n+rn, bn), Nat.is_lt(rn, bn), True{}, Equal.sym(Bool, Nat.is_lt(rn, bn),
    Nat.is_le(1n+rn, bn), M1.lt_le_succ(rn, bn)), hh) : {Nat.is_le(1n+rn, bn) == True{} : Bool}}
  +h2 = {M1.le_add_both(1n+rn, bn, 1n+rn, bn, h1, h1) : {Nat.is_le(Nat.add(1n+rn, 1n+rn), Nat.add(bn, bn)) == True{} :
    Bool}}
  +h3 = {Equal.trans(Nat, 2n+Nat.double(rn), 2n+Nat.add(rn, rn), Nat.add(1n+rn, 1n+rn), Equal.cong(Nat, Nat, kk =>
    2n+kk, Nat.double(rn), Nat.add(rn, rn), M1.double_add(rn)), Equal.cong(Nat, Nat, kk => 1n+kk, 1n+Nat.add(rn, rn),
    Nat.add(rn, 1n+rn), Equal.sym(Nat, Nat.add(rn, 1n+rn), 1n+Nat.add(rn, rn), M1.ras.add_succ(rn, rn)))) :
    {2n+Nat.double(rn) == Nat.add(1n+rn, 1n+rn) : Nat}}
  +h4 = {M1.le_rw_l(Nat.add(1n+rn, 1n+rn), 2n+Nat.double(rn), Nat.add(bn, bn), Equal.sym(Nat, 2n+Nat.double(rn),
    Nat.add(1n+rn, 1n+rn), h3), h2) : {Nat.is_le(2n+Nat.double(rn), Nat.add(bn, bn)) == True{} : Bool}}
  bit.lt(aa, Nat.double(rn), Nat.add(bn, bn), h4)

# a + 2 (q b + r) is 2 q b + (a + 2 r)
def alg.lhs(
  +an: Nat,
  +qb: Nat,
  +rn: Nat
) -> {Nat.add(an, Nat.double(Nat.add(qb, rn))) == Nat.add(Nat.double(qb), Nat.add(an, Nat.double(rn))) : Nat}:
  Equal.trans(Nat, Nat.add(an, Nat.double(Nat.add(qb, rn))), Nat.add(an, Nat.add(Nat.double(qb), Nat.double(rn))),
    Nat.add(Nat.double(qb), Nat.add(an, Nat.double(rn))), Equal.cong(Nat, Nat, kk => Nat.add(an, kk),
    Nat.double(Nat.add(qb, rn)), Nat.add(Nat.double(qb), Nat.double(rn)), M1.double_dist(qb, rn)), M1.add_swap(an,
    Nat.double(qb), Nat.double(rn)))

# what U32.divmod.go gives: the word is q * b + r, with r below b
def dm.ok(mm: Nat, +aw: Word(mm), +bu: U32, qr: Word(mm) & U32) -> Type:
  match qr:
    case (+qw, +ru):
      {Word.to_nat(mm, aw) == Nat.add(Nat.mul(Word.to_nat(mm, qw), U32.to_nat(bu)), U32.to_nat(ru)) : Nat} &
        {Nat.is_lt(U32.to_nat(ru), U32.to_nat(bu)) == True{} : Bool}

# the step where the new bit makes the remainder reach b: q gets a 1 and b comes off
def dm.sub(
  +pp: Nat,
  +a0: Bool,
  +hi: Word(pp),
  +bu: U32,
  +qw: Word(pp),
  +rn: Nat,
  +su: U32,
  +e1: {Word.to_nat(pp, hi) == Nat.add(Nat.mul(Word.to_nat(pp, qw), U32.to_nat(bu)), rn) : Nat},
  +es: {U32.to_nat(su) == Nat.add(M1.bit(a0), Nat.double(rn)) : Nat},
  +hge: {Nat.is_le(U32.to_nat(bu), U32.to_nat(su)) == True{} : Bool},
  +hlt: {Nat.is_lt(U32.to_nat(su), Nat.add(U32.to_nat(bu), U32.to_nat(bu))) == True{} : Bool}
) -> dm.ok(1n+pp, WCon{a0, hi}, bu, (WCon{True{}, qw}, U32.sub(su, bu))):
  +bn = U32.to_nat(bu)
  +sn = U32.to_nat(su)
  +qn = Word.to_nat(pp, qw)
  +qb = Nat.mul(qn, bn)
  +an = M1.bit(a0)
  +dd = Nat.mul(Nat.double(qn), bn)
  +e_sub = {M10.ras.u32_sub_nat(su, bu, hge) : {U32.to_nat(U32.sub(su, bu)) == Nat.sub(sn, bn) : Nat}}
  +e_l = {Equal.trans(Nat, Word.to_nat(1n+pp, WCon{a0, hi}), Nat.add(an, Nat.double(Nat.add(qb, rn))),
    Nat.add(Nat.double(qb), Nat.add(an, Nat.double(rn))), Equal.trans(Nat, Word.to_nat(1n+pp, WCon{a0, hi}),
    Nat.add(an, Nat.double(Word.to_nat(pp, hi))), Nat.add(an, Nat.double(Nat.add(qb, rn))), M1.to_nat_con(pp, a0, hi),
    Equal.cong(Nat, Nat, kk => Nat.add(an, Nat.double(kk)), Word.to_nat(pp, hi), Nat.add(qb, rn), e1)), alg.lhs(an, qb,
    rn)) : {Word.to_nat(1n+pp, WCon{a0, hi}) == Nat.add(Nat.double(qb), Nat.add(an, Nat.double(rn))) : Nat}}
  +e_r = {Equal.trans(Nat, Nat.add(Nat.add(bn, dd), Nat.sub(sn, bn)), Nat.add(dd, sn), Nat.add(Nat.double(qb),
    Nat.add(an, Nat.double(rn))),
    Equal.trans(Nat, Nat.add(Nat.add(bn, dd), Nat.sub(sn, bn)), Nat.add(dd, Nat.add(bn, Nat.sub(sn, bn))), Nat.add(dd,
      sn),
      Equal.trans(Nat, Nat.add(Nat.add(bn, dd), Nat.sub(sn, bn)), Nat.add(bn, Nat.add(dd, Nat.sub(sn, bn))),
        Nat.add(dd, Nat.add(bn, Nat.sub(sn, bn))), M1.ras.add_assoc(bn, dd, Nat.sub(sn, bn)), M1.add_swap(bn, dd,
        Nat.sub(sn, bn))),
      Equal.cong(Nat, Nat, kk => Nat.add(dd, kk), Nat.add(bn, Nat.sub(sn, bn)), sn, M10.add_sub(bn, sn, hge))),
    Equal.trans(Nat, Nat.add(dd, sn), Nat.add(Nat.double(qb), sn), Nat.add(Nat.double(qb), Nat.add(an,
      Nat.double(rn))), Equal.cong(Nat, Nat, kk => Nat.add(kk, sn), dd, Nat.double(qb), M7.mul_double(qn, bn)),
      Equal.cong(Nat, Nat, kk => Nat.add(Nat.double(qb), kk), sn, Nat.add(an, Nat.double(rn)), es))) :
    {Nat.add(Nat.add(bn, dd), Nat.sub(sn, bn)) == Nat.add(Nat.double(qb), Nat.add(an, Nat.double(rn))) : Nat}}
  +e_all = {Equal.trans(Nat, Word.to_nat(1n+pp, WCon{a0, hi}), Nat.add(Nat.double(qb), Nat.add(an, Nat.double(rn))),
    Nat.add(Nat.add(bn, dd), U32.to_nat(U32.sub(su, bu))), e_l, Equal.trans(Nat, Nat.add(Nat.double(qb), Nat.add(an,
    Nat.double(rn))), Nat.add(Nat.add(bn, dd), Nat.sub(sn, bn)), Nat.add(Nat.add(bn, dd), U32.to_nat(U32.sub(su, bu))),
    Equal.sym(Nat, Nat.add(Nat.add(bn, dd), Nat.sub(sn, bn)), Nat.add(Nat.double(qb), Nat.add(an, Nat.double(rn))),
    e_r), Equal.cong(Nat, Nat, kk => Nat.add(Nat.add(bn, dd), kk), Nat.sub(sn, bn), U32.to_nat(U32.sub(su, bu)),
    Equal.sym(Nat, U32.to_nat(U32.sub(su, bu)), Nat.sub(sn, bn), e_sub)))) : {Word.to_nat(1n+pp, WCon{a0, hi}) ==
    Nat.add(Nat.add(bn, dd), U32.to_nat(U32.sub(su, bu))) : Nat}}
  +l_sub = {M1.lt_rw_l(Nat.sub(sn, bn), U32.to_nat(U32.sub(su, bu)), bn, Equal.sym(Nat, U32.to_nat(U32.sub(su, bu)),
    Nat.sub(sn, bn), e_sub), M10.sub_lt(bn, sn, bn, hge, hlt)) : {Nat.is_lt(U32.to_nat(U32.sub(su, bu)), bn) == True{} :
    Bool}}
  (e_all, l_sub)

# the step where the remainder stays below b: q gets a 0
def dm.keep(
  +pp: Nat,
  +a0: Bool,
  +hi: Word(pp),
  +bu: U32,
  +qw: Word(pp),
  +rn: Nat,
  +su: U32,
  +e1: {Word.to_nat(pp, hi) == Nat.add(Nat.mul(Word.to_nat(pp, qw), U32.to_nat(bu)), rn) : Nat},
  +es: {U32.to_nat(su) == Nat.add(M1.bit(a0), Nat.double(rn)) : Nat},
  +hlt: {Nat.is_lt(U32.to_nat(su), U32.to_nat(bu)) == True{} : Bool}
) -> dm.ok(1n+pp, WCon{a0, hi}, bu, (WCon{False{}, qw}, su)):
  +bn = U32.to_nat(bu)
  +qn = Word.to_nat(pp, qw)
  +qb = Nat.mul(qn, bn)
  +an = M1.bit(a0)
  +e_all = {Equal.trans(Nat, Word.to_nat(1n+pp, WCon{a0, hi}), Nat.add(Nat.double(qb), Nat.add(an, Nat.double(rn))),
    Nat.add(Nat.mul(Nat.double(qn), bn), U32.to_nat(su)), Equal.trans(Nat, Word.to_nat(1n+pp, WCon{a0, hi}),
    Nat.add(an, Nat.double(Nat.add(qb, rn))), Nat.add(Nat.double(qb), Nat.add(an, Nat.double(rn))), Equal.trans(Nat,
    Word.to_nat(1n+pp, WCon{a0, hi}), Nat.add(an, Nat.double(Word.to_nat(pp, hi))), Nat.add(an, Nat.double(Nat.add(qb,
    rn))), M1.to_nat_con(pp, a0, hi), Equal.cong(Nat, Nat, kk => Nat.add(an, Nat.double(kk)), Word.to_nat(pp, hi),
    Nat.add(qb, rn), e1)), alg.lhs(an, qb, rn)), Equal.trans(Nat, Nat.add(Nat.double(qb), Nat.add(an, Nat.double(rn))),
    Nat.add(Nat.mul(Nat.double(qn), bn), Nat.add(an, Nat.double(rn))), Nat.add(Nat.mul(Nat.double(qn), bn),
    U32.to_nat(su)), Equal.cong(Nat, Nat, kk => Nat.add(kk, Nat.add(an, Nat.double(rn))), Nat.double(qb),
    Nat.mul(Nat.double(qn), bn), Equal.sym(Nat, Nat.mul(Nat.double(qn), bn), Nat.double(qb), M7.mul_double(qn, bn))),
    Equal.cong(Nat, Nat, kk => Nat.add(Nat.mul(Nat.double(qn), bn), kk), Nat.add(an, Nat.double(rn)), U32.to_nat(su),
    Equal.sym(Nat, U32.to_nat(su), Nat.add(an, Nat.double(rn)), es)))) : {Word.to_nat(1n+pp, WCon{a0, hi}) ==
    Nat.add(Nat.mul(Nat.double(qn), bn), U32.to_nat(su)) : Nat}}
  (e_all, hlt)

# divmod.go.fin, as it picks on whether the shifted remainder reached b
def dm.fin(
  +pp: Nat,
  +a0: Bool,
  +hi: Word(pp),
  +bu: U32,
  +qw: Word(pp),
  +rn: Nat,
  +su: U32,
  zg: Bool,
  +eg: {U32.is_ge(su, bu) == zg : Bool},
  +e1: {Word.to_nat(pp, hi) == Nat.add(Nat.mul(Word.to_nat(pp, qw), U32.to_nat(bu)), rn) : Nat},
  +es: {U32.to_nat(su) == Nat.add(M1.bit(a0), Nat.double(rn)) : Nat},
  +hlt: {Nat.is_lt(U32.to_nat(su), Nat.add(U32.to_nat(bu), U32.to_nat(bu))) == True{} : Bool}
) -> dm.ok(1n+pp, WCon{a0, hi}, bu, U32.divmod.go.fin(pp, qw, su, bu, zg)):
  match zg:
    case True{}:
      +hg = {Equal.trans(Bool, Cmp.is_ge(Nat.cmp(U32.to_nat(su), U32.to_nat(bu))), U32.is_ge(su, bu), True{},
        Equal.sym(Bool, U32.is_ge(su, bu), Cmp.is_ge(Nat.cmp(U32.to_nat(su), U32.to_nat(bu))), u.ge(su, bu)), eg) :
        {Cmp.is_ge(Nat.cmp(U32.to_nat(su), U32.to_nat(bu))) == True{} : Bool}}
      dm.sub(pp, a0, hi, bu, qw, rn, su, e1, es, ge.le(U32.to_nat(su), U32.to_nat(bu), hg), hlt)
    case False{}:
      +hg = {Equal.trans(Bool, Cmp.is_ge(Nat.cmp(U32.to_nat(su), U32.to_nat(bu))), U32.is_ge(su, bu), False{},
        Equal.sym(Bool, U32.is_ge(su, bu), Cmp.is_ge(Nat.cmp(U32.to_nat(su), U32.to_nat(bu))), u.ge(su, bu)), eg) :
        {Cmp.is_ge(Nat.cmp(U32.to_nat(su), U32.to_nat(bu))) == False{} : Bool}}
      dm.keep(pp, a0, hi, bu, qw, rn, su, e1, es, nge.lt(U32.to_nat(su), U32.to_nat(bu), hg))

# divmod.go.shl: the remainder shifted with the new bit, nothing falling out
def dm.shl(
  +pp: Nat,
  +a0: Bool,
  +hi: Word(pp),
  +bu: U32,
  +qw: Word(pp),
  +rw: Word(32n),
  yy: Bool & Word(32n),
  hy: sho.ok(32n, a0, rw, yy),
  +e1: {Word.to_nat(pp, hi) == Nat.add(Nat.mul(Word.to_nat(pp, qw), U32.to_nat(bu)), Word.to_nat(32n, rw)) : Nat},
  +lt1: {Nat.is_lt(Word.to_nat(32n, rw), U32.to_nat(bu)) == True{} : Bool}
) -> dm.ok(1n+pp, WCon{a0, hi}, bu, U32.divmod.go.shl(pp, qw, bu, yy)):
  match yy:
    case (tt, +ss):
      (e_t, +e_s) = hy
      +rn = Word.to_nat(32n, rw)
      +hlt = {M1.lt_rw_l(Nat.add(M1.bit(a0), Nat.double(rn)), U32.to_nat(U32{ss}), Nat.add(U32.to_nat(bu),
        U32.to_nat(bu)), Equal.sym(Nat, Word.to_nat(32n, ss), Nat.add(M1.bit(a0), Nat.double(rn)), e_s), dbl.lt(a0, rn,
        U32.to_nat(bu), lt1)) : {Nat.is_lt(U32.to_nat(U32{ss}), Nat.add(U32.to_nat(bu), U32.to_nat(bu))) == True{} :
        Bool}}
      %Equal.sym(Bool, tt, False{}, e_t) : dm.ok(1n+pp, WCon{a0, hi}, bu, U32.divmod.go.fin(pp, qw, U32{ss}, bu,
        Bool.or(_, U32.is_ge(U32{ss}, bu))))
      dm.fin(pp, a0, hi, bu, qw, rn, U32{ss}, U32.is_ge(U32{ss}, bu), {==}, e1, e_s, hlt)

# divmod.go.rec with the remainder and the bound taken apart into words
def dm.rec2(
  +pp: Nat,
  +a0: Bool,
  +hi: Word(pp),
  +bu: U32,
  +qw: Word(pp),
  ru: U32,
  tu: U32,
  +e1: {Word.to_nat(pp, hi) == Nat.add(Nat.mul(Word.to_nat(pp, qw), U32.to_nat(bu)), U32.to_nat(ru)) : Nat},
  +lt1: {Nat.is_lt(U32.to_nat(ru), U32.to_nat(bu)) == True{} : Bool},
  +hb2: {Nat.is_le(Nat.add(U32.to_nat(bu), U32.to_nat(bu)), U32.to_nat(tu)) == True{} : Bool}
) -> dm.ok(1n+pp, WCon{a0, hi}, bu, U32.divmod.go.rec(pp, a0, bu, (qw, ru))):
  match ru tu:
    case U32{+rw} U32{+tw}:
      +rn = Word.to_nat(32n, rw)
      +bb = Nat.add(U32.to_nat(bu), U32.to_nat(bu))
      +hbd = {M1.le_trans(Nat.add(M1.bit(a0), Nat.double(rn)), bb, Word.to_nat(32n, tw), M1.lt_le(Nat.add(M1.bit(a0),
        Nat.double(rn)), bb, dbl.lt(a0, rn, U32.to_nat(bu), lt1)), hb2) : {Nat.is_le(Nat.add(M1.bit(a0),
        Nat.double(rn)), Word.to_nat(32n, tw)) == True{} : Bool}}
      dm.shl(pp, a0, hi, bu, qw, rw, Word.shl.out(32n, a0, rw), sho(32n, a0, rw, tw, hbd), e1, lt1)

# divmod.go.rec: the bits above, divided, then this bit shifted in
def dm.rec(
  +pp: Nat,
  +a0: Bool,
  +hi: Word(pp),
  +bu: U32,
  +tu: U32,
  xx: Word(pp) & U32,
  ih: dm.ok(pp, hi, bu, xx),
  +hb2: {Nat.is_le(Nat.add(U32.to_nat(bu), U32.to_nat(bu)), U32.to_nat(tu)) == True{} : Bool}
) -> dm.ok(1n+pp, WCon{a0, hi}, bu, U32.divmod.go.rec(pp, a0, bu, xx)):
  match xx:
    case (+qw, +ru):
      (e1, lt1) = ih
      dm.rec2(pp, a0, hi, bu, qw, ru, tu, e1, lt1, hb2)

# U32.divmod.go by a b above 0 with 2 b some U32's value: the word is q b + r, r below b
def dm(
  mm: Nat,
  aw: Word(mm),
  +bu: U32,
  +tu: U32,
  +hb0: {Nat.is_lt(0n, U32.to_nat(bu)) == True{} : Bool},
  +hb2: {Nat.is_le(Nat.add(U32.to_nat(bu), U32.to_nat(bu)), U32.to_nat(tu)) == True{} : Bool}
) -> dm.ok(mm, aw, bu, U32.divmod.go(mm, aw, bu)):
  match mm aw:
    case 0n WNil{}:
      ({==}, hb0)
    case 1n+(+pp) WCon{+a0, +hi}:
      dm.rec(pp, a0, hi, bu, tu, U32.divmod.go(pp, hi, bu), dm(pp, hi, bu, tu, hb0, hb2), hb2)

# what U32.div and U32.mod give
def dvm.ty(+nu: U32, +bu: U32) -> Type:
  {U32.to_nat(nu) == Nat.add(Nat.mul(U32.to_nat(U32.div(nu, bu)), U32.to_nat(bu)), U32.to_nat(U32.mod(nu, bu))) : Nat}
    & {Nat.is_lt(U32.to_nat(U32.mod(nu, bu)), U32.to_nat(bu)) == True{} : Bool}

# the quotient and remainder divmod.go leaves, read by div.fin and mod.fin
def dvm.pair(
  +aw: Word(32n),
  +bu: U32,
  xx: Word(32n) & U32,
  hh: dm.ok(32n, aw, bu, xx)
) -> {Word.to_nat(32n, aw) == Nat.add(Nat.mul(U32.to_nat(U32.div.fin(xx)), U32.to_nat(bu)),
  U32.to_nat(U32.mod.fin(xx))) : Nat} & {Nat.is_lt(U32.to_nat(U32.mod.fin(xx)), U32.to_nat(bu)) == True{} : Bool}:
  match xx:
    case (+qw, +ru):
      hh

# U32.div and U32.mod by a nonzero b, once is_zero's answer is named
def dvm.at(
  zz: Bool,
  +aw: Word(32n),
  +bu: U32,
  +tu: U32,
  +ez: {U32.is_zero(bu) == zz : Bool},
  +hb0: {Nat.is_lt(0n, U32.to_nat(bu)) == True{} : Bool},
  +hb2: {Nat.is_le(Nat.add(U32.to_nat(bu), U32.to_nat(bu)), U32.to_nat(tu)) == True{} : Bool}
) -> {Word.to_nat(32n, aw) == Nat.add(Nat.mul(U32.to_nat(U32.div.if(aw, bu, zz)), U32.to_nat(bu)),
  U32.to_nat(U32.mod.if(aw, bu, zz))) : Nat} & {Nat.is_lt(U32.to_nat(U32.mod.if(aw, bu, zz)), U32.to_nat(bu)) ==
  True{} : Bool}:
  match zz:
    case False{}:
      dvm.pair(aw, bu, U32.divmod.go(32n, aw, bu), dm(32n, aw, bu, tu, hb0, hb2))
    case True{}:
      +e0 = {M1.zero.val(bu, Equal.sym(Bool, U32.is_zero(bu), True{}, ez)) : {U32.to_nat(bu) == 0n : Nat}}
      Empty.absurd({Word.to_nat(32n, aw) == Nat.add(Nat.mul(U32.to_nat(U32.div.if(aw, bu, True{})), U32.to_nat(bu)),
        U32.to_nat(U32.mod.if(aw, bu, True{}))) : Nat} & {Nat.is_lt(U32.to_nat(U32.mod.if(aw, bu, True{})),
        U32.to_nat(bu)) == True{} : Bool}, M1.false_true(Equal.trans(Bool, False{}, Nat.is_lt(0n, U32.to_nat(bu)),
        True{}, Equal.cong(Nat, Bool, kk => Nat.is_lt(0n, kk), 0n, U32.to_nat(bu), Equal.sym(Nat, U32.to_nat(bu), 0n,
        e0)), hb0)))

# U32.div and U32.mod: n is q b + r with r below b, for b above 0 whose double
# is some U32's value
def dvm(
  nu: U32,
  +bu: U32,
  +tu: U32,
  +hb0: {Nat.is_lt(0n, U32.to_nat(bu)) == True{} : Bool},
  +hb2: {Nat.is_le(Nat.add(U32.to_nat(bu), U32.to_nat(bu)), U32.to_nat(tu)) == True{} : Bool}
) -> dvm.ty(nu, bu):
  match nu bu:
    case U32{+aw} U32{+bw}:
      dvm.at(U32.is_zero(U32{bw}), aw, U32{bw}, tu, {==}, hb0, hb2)

# two words' values added
def wsum(+pp: Nat, +at: Word(pp), +bt: Word(pp)) -> Nat:
  Nat.add(Word.to_nat(pp, at), Word.to_nat(pp, bt))

# one bit of cfa: this bit's sum and carry, then the bits above
def cfa.arm(
  +pp: Nat,
  +at: Word(pp),
  +bt: Word(pp),
  +ab: Bool,
  +bb: Bool,
  +cc: Bool,
  +ss: Bool,
  +kk: Bool,
  +e_bits: {Nat.add(M1.bit(cc), Nat.add(M1.bit(ab), M1.bit(bb))) == Nat.add(M1.bit(ss), Nat.double(M1.bit(kk))) : Nat},
  +er: {Word.to_nat(pp, Word.adc(pp, at, bt, False{}, kk)) == Nat.add(M1.bit(kk), wsum(pp, at, bt)) : Nat}
) -> {Word.to_nat(1n+pp, WCon{ss, Word.adc(pp, at, bt, False{}, kk)}) == Nat.add(M1.bit(cc), Nat.add(Word.to_nat(1n+pp,
  WCon{ab, at}), Word.to_nat(1n+pp, WCon{bb, bt}))) : Nat}:
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
    Nat.add(M1.bit(ss), Nat.double(mm)), e_in, M11.sum_regroup(M1.bit(cc), M1.bit(ab), M1.bit(bb), M1.bit(ss),
        M1.bit(kk), na,
    nb, e_bits)) : {Nat.add(M1.bit(cc), Nat.add(wa, wb)) == Nat.add(M1.bit(ss), Nat.double(mm)) : Nat}}
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

# the adder with no carry out is the sum
def cfa(
  nn: Nat,
  aw: Word(nn),
  bw: Word(nn),
  cc: Bool,
  +hh: {M10.cy(nn, aw, bw, cc) == False{} : Bool}
) -> {Word.to_nat(nn, Word.adc(nn, aw, bw, False{}, cc)) == Nat.add(M1.bit(cc), Nat.add(Word.to_nat(nn, aw),
  Word.to_nat(nn, bw))) : Nat}:
  match nn:
    case 0n:
      match aw bw cc:
        case WNil{} WNil{} False{}:
          {==}
        case WNil{} WNil{} True{}:
          Empty.absurd({0n == 1n : Nat}, M1.false_true(Equal.sym(Bool, True{}, False{}, hh)))
    case 1n+(+pp):
      match aw bw cc:
        case WCon{False{}, +at} WCon{False{}, +bt} False{}:
          cfa.arm(pp, at, bt, False{}, False{}, False{}, False{}, False{}, {==}, cfa(pp, at, bt, False{}, hh))
        case WCon{False{}, +at} WCon{False{}, +bt} True{}:
          cfa.arm(pp, at, bt, False{}, False{}, True{}, True{}, False{}, {==}, cfa(pp, at, bt, False{}, hh))
        case WCon{False{}, +at} WCon{True{}, +bt} False{}:
          cfa.arm(pp, at, bt, False{}, True{}, False{}, True{}, False{}, {==}, cfa(pp, at, bt, False{}, hh))
        case WCon{False{}, +at} WCon{True{}, +bt} True{}:
          cfa.arm(pp, at, bt, False{}, True{}, True{}, False{}, True{}, {==}, cfa(pp, at, bt, True{}, hh))
        case WCon{True{}, +at} WCon{False{}, +bt} False{}:
          cfa.arm(pp, at, bt, True{}, False{}, False{}, True{}, False{}, {==}, cfa(pp, at, bt, False{}, hh))
        case WCon{True{}, +at} WCon{False{}, +bt} True{}:
          cfa.arm(pp, at, bt, True{}, False{}, True{}, False{}, True{}, {==}, cfa(pp, at, bt, True{}, hh))
        case WCon{True{}, +at} WCon{True{}, +bt} False{}:
          cfa.arm(pp, at, bt, True{}, True{}, False{}, False{}, True{}, {==}, cfa(pp, at, bt, True{}, hh))
        case WCon{True{}, +at} WCon{True{}, +bt} True{}:
          cfa.arm(pp, at, bt, True{}, True{}, True{}, True{}, True{}, {==}, cfa(pp, at, bt, True{}, hh))

# the carry out of a U32 add
def cy32(uu: U32, vv: U32) -> Bool:
  match uu vv:
    case U32{xw} U32{yw}:
      M10.cy(32n, xw, yw, False{})

# a U32 add with no carry out is the sum
def add.cf(
  uu: U32,
  vv: U32,
  +hh: {cy32(uu, vv) == False{} : Bool}
) -> {U32.to_nat(U32.add(uu, vv)) == Nat.add(U32.to_nat(uu), U32.to_nat(vv)) : Nat}:
  match uu vv:
    case U32{+xw} U32{+yw}:
      cfa(32n, xw, yw, False{}, hh)

# the block size doubled is a U32's value
def mx.dbl(
  +mx: U32,
  +emx: {mx == 65535 : U32}
) -> {U32.to_nat(U32.add(mx, mx)) == Nat.add(U32.to_nat(mx), U32.to_nat(mx)) : Nat}:
  add.cf(mx, mx, Equal.cong(U32, Bool, uu => cy32(uu, uu), mx, 65535, emx))

# the block size is at least 2
def mx.two(
  +mx: U32,
  +emx: {mx == 65535 : U32}
) -> {U32.to_nat(mx) == 2n+U32.to_nat(((mx - 1 : U32) - 1 : U32)) : Nat}:
  +m1 = (mx - 1 : U32)
  +nz1 = {Equal.cong(U32, Bool, uu => U32.is_zero((uu - 1 : U32)), mx, 65535, emx) : {U32.is_zero(m1) == False{} :
    Bool}}
  Equal.trans(Nat, U32.to_nat(mx), 1n+U32.to_nat(m1), 2n+U32.to_nat((m1 - 1 : U32)), M1.u32_dec(mx, mx.nz(mx, emx)),
    Equal.cong(Nat, Nat, kk => 1n+kk, U32.to_nat(m1), 1n+U32.to_nat((m1 - 1 : U32)), M1.u32_dec(m1, nz1)))

# x below x + y when y is above 0
def pfin.lt.more(
  +xx: Nat,
  +yy: Nat,
  +hh: {Nat.is_lt(0n, yy) == True{} : Bool}
) -> {Nat.is_lt(xx, Nat.add(xx, yy)) == True{} : Bool}:
  M1.lt_rw_l(Nat.add(xx, 0n), xx, Nat.add(xx, yy), M1.ras.add_zero(xx), M1.lt_add_mono(xx, 0n, yy, hh))

# q blocks exactly: ceil(q m / m) is q
def nb.exact(
  qn: Nat,
  +mn: Nat,
  +xn: Nat,
  +ee: {xn == Nat.mul(qn, mn) : Nat},
  +hm: {Nat.is_lt(0n, mn) == True{} : Bool}
) -> M1.kok(xn, qn, mn):
  match qn:
    case 0n:
      ee
    case 1n+(+kp):
      +km = Nat.mul(kp, mn)
      +e2 = {Equal.trans(Nat, xn, Nat.add(mn, km), Nat.add(km, mn), ee, M1.ras.add_comm(mn, km)) : {xn == Nat.add(km,
          mn) :
        Nat}}
      (M1.lt_rw_r(km, Nat.add(km, mn), xn, Equal.sym(Nat, xn, Nat.add(km, mn), e2), pfin.lt.more(km, mn, hm)),
        M1.le_rw_l(Nat.mul(1n+kp, mn), xn, Nat.mul(1n+kp, mn), Equal.sym(Nat, xn, Nat.mul(1n+kp, mn), ee),
        M1.le_refl(Nat.mul(1n+kp, mn))))

# q blocks and a remainder r from 1 to m - 1: ceil is q + 1
def nb.rem(
  +qn: Nat,
  +mn: Nat,
  +xn: Nat,
  +rn: Nat,
  +ee: {xn == Nat.add(Nat.mul(qn, mn), rn) : Nat},
  +h1: {Nat.is_lt(0n, rn) == True{} : Bool},
  +hr: {Nat.is_lt(rn, mn) == True{} : Bool}
) -> M1.kok(xn, 1n+qn, mn):
  +qm = Nat.mul(qn, mn)
  (M1.lt_rw_r(qm, Nat.add(qm, rn), xn, Equal.sym(Nat, xn, Nat.add(qm, rn), ee), pfin.lt.more(qm, rn, h1)),
    M1.le_rw_l(Nat.add(qm, rn), xn, Nat.mul(1n+qn, mn), Equal.sym(Nat, xn, Nat.add(qm, rn), ee), M1.le_rw_r(Nat.add(qm,
    rn), Nat.add(qm, mn), Nat.mul(1n+qn, mn), M1.ras.add_comm(qm, mn), M1.le_add_mono(qm, rn, mn, M1.lt_le(rn, mn,
        hr)))))

# x at most x times m for m above 0
def le.mul(
  +xx: Nat,
  +mn: Nat,
  +hm: {Nat.is_lt(0n, mn) == True{} : Bool}
) -> {Nat.is_le(xx, Nat.mul(xx, mn)) == True{} : Bool}:
  +h1 = {Equal.trans(Bool, Nat.is_le(1n, mn), Nat.is_lt(0n, mn), True{}, Equal.sym(Bool, Nat.is_lt(0n, mn),
    Nat.is_le(1n, mn), M1.lt_le_succ(0n, mn)), hm) : {Nat.is_le(1n, mn) == True{} : Bool}}
  M1.le_rw_l(Nat.mul(1n, xx), xx, Nat.mul(xx, mn), M1.ras.add_zero(xx), M1.le_rw_r(Nat.mul(1n, xx), Nat.mul(mn, xx),
    Nat.mul(xx, mn), M1.mul_comm(mn, xx), M11.le_mul_mono(1n, mn, xx, h1)))

# enc.nblk with the block size named
def nblk.m(+nn: U32, +mx: U32) -> U32:
  Png.enc.nblk.at(U32.is_zero(U32.mod(nn, mx)), U32.div(nn, mx))

# enc.nblk is nblk.m at 65535
def nblk.eq(+nn: U32, +mx: U32, +emx: {mx == 65535 : U32}) -> {Png.enc.nblk(nn) == nblk.m(nn, mx) : U32}:
  Equal.cong(U32, U32, uu => Png.enc.nblk.at(U32.is_zero(U32.mod(nn, uu)), U32.div(nn, uu)), 65535, mx, Equal.sym(U32,
    mx, 65535, emx))

# nblk.m, once whether the remainder is zero is named
def nb.at(
  zz: Bool,
  +nn: U32,
  +mx: U32,
  +ez: {U32.is_zero(U32.mod(nn, mx)) == zz : Bool},
  +e_n: {U32.to_nat(nn) == M1.dq(nn, mx) : Nat},
  +l_r: {Nat.is_lt(U32.to_nat(U32.mod(nn, mx)), U32.to_nat(mx)) == True{} : Bool},
  +hm: {Nat.is_lt(0n, U32.to_nat(mx)) == True{} : Bool}
) -> M1.kok(U32.to_nat(nn), U32.to_nat(Png.enc.nblk.at(zz, U32.div(nn, mx))), U32.to_nat(mx)):
  match zz:
    case True{}:
      +qu = U32.div(nn, mx)
      +ru = U32.mod(nn, mx)
      +qn = U32.to_nat(qu)
      +mn = U32.to_nat(mx)
      +xn = U32.to_nat(nn)
      +e0 = {M1.zero.val(ru, Equal.sym(Bool, U32.is_zero(ru), True{}, ez)) : {U32.to_nat(ru) == 0n : Nat}}
      nb.exact(qn, mn, xn, Equal.trans(Nat, xn, Nat.add(Nat.mul(qn, mn), 0n), Nat.mul(qn, mn), Equal.trans(Nat, xn,
        Nat.add(Nat.mul(qn, mn), U32.to_nat(ru)), Nat.add(Nat.mul(qn, mn), 0n), e_n, Equal.cong(Nat, Nat, kk =>
        Nat.add(Nat.mul(qn, mn), kk), U32.to_nat(ru), 0n, e0)), M1.ras.add_zero(Nat.mul(qn, mn))), hm)
    case False{}:
      +qu = U32.div(nn, mx)
      +ru = U32.mod(nn, mx)
      +qn = U32.to_nat(qu)
      +mn = U32.to_nat(mx)
      +xn = U32.to_nat(nn)
      +h1 = {Equal.trans(Bool, Nat.is_lt(0n, U32.to_nat(ru)), Bool.not(Nat.is_eq(U32.to_nat(ru), 0n)), True{},
        M10.pos_eq(U32.to_nat(ru)), Equal.cong(Bool, Bool, bb => Bool.not(bb), Nat.is_eq(U32.to_nat(ru), 0n), False{},
        Equal.trans(Bool, Nat.is_eq(U32.to_nat(ru), 0n), U32.is_zero(ru), False{}, Equal.sym(Bool, U32.is_zero(ru),
        Nat.is_eq(U32.to_nat(ru), U32.to_nat(0)), M1.u32_eq(ru, 0)), ez))) : {Nat.is_lt(0n, U32.to_nat(ru)) == True{} :
        Bool}}
      +h_q1 = {M1.le_rw_r(Nat.add(qn, 1n), Nat.add(Nat.mul(qn, mn), U32.to_nat(ru)), xn, Equal.sym(Nat, xn,
        Nat.add(Nat.mul(qn, mn), U32.to_nat(ru)), e_n), M1.le_add_both(qn, Nat.mul(qn, mn), 1n, U32.to_nat(ru),
        le.mul(qn, mn, hm), Equal.trans(Bool, Nat.is_le(1n, U32.to_nat(ru)), Nat.is_lt(0n, U32.to_nat(ru)), True{},
        Equal.sym(Bool, Nat.is_lt(0n, U32.to_nat(ru)), Nat.is_le(1n, U32.to_nat(ru)), M1.lt_le_succ(0n,
        U32.to_nat(ru))), h1))) : {Nat.is_le(Nat.add(qn, 1n), xn) == True{} : Bool}}
      +e_q1 = {Equal.trans(Nat, U32.to_nat((qu + 1 : U32)), Nat.add(qn, 1n), 1n+qn, M11.u32_add_below(qu, 1, nn, h_q1),
        add.one.nat(qn)) : {U32.to_nat((qu + 1 : U32)) == 1n+qn : Nat}}
      %Equal.sym(Nat, U32.to_nat((qu + 1 : U32)), 1n+qn, e_q1) : M1.kok(xn, _, mn)
      nb.rem(qn, mn, xn, U32.to_nat(ru), e_n, h1, l_r)

# the pair U32.div and U32.mod give, taken apart
def nb.go(
  +nn: U32,
  +mx: U32,
  pr: dvm.ty(nn, mx),
  +hm: {Nat.is_lt(0n, U32.to_nat(mx)) == True{} : Bool}
) -> M1.kok(U32.to_nat(nn), U32.to_nat(nblk.m(nn, mx)), U32.to_nat(mx)):
  (+e_n, +l_r) = pr
  nb.at(U32.is_zero(U32.mod(nn, mx)), nn, mx, {==}, e_n, l_r, hm)

# enc.nblk(n) blocks of 65535 bytes hold n bytes, the last one not empty
def nb.k(
  +nn: U32,
  +mx: U32,
  +emx: {mx == 65535 : U32}
) -> M1.kok(U32.to_nat(nn), U32.to_nat(Png.enc.nblk(nn)), U32.to_nat(mx)):
  +mn = U32.to_nat(mx)
  +hm = {Equal.trans(Bool, Nat.is_lt(0n, mn), Nat.is_lt(0n, 2n+U32.to_nat(((mx - 1 : U32) - 1 : U32))), True{},
    Equal.cong(Nat, Bool, kk => Nat.is_lt(0n, kk), mn, 2n+U32.to_nat(((mx - 1 : U32) - 1 : U32)), mx.two(mx, emx)),
    {==}) : {Nat.is_lt(0n, mn) == True{} : Bool}}
  +h2 = {M1.le_rw_r(Nat.add(mn, mn), Nat.add(mn, mn), U32.to_nat(U32.add(mx, mx)), Equal.sym(Nat,
    U32.to_nat(U32.add(mx, mx)), Nat.add(mn, mn), mx.dbl(mx, emx)), M1.le_refl(Nat.add(mn, mn))) :
    {Nat.is_le(Nat.add(mn, mn), U32.to_nat(U32.add(mx, mx))) == True{} : Bool}}
  %Equal.sym(U32, Png.enc.nblk(nn), nblk.m(nn, mx), nblk.eq(nn, mx, emx)) : M1.kok(U32.to_nat(nn), U32.to_nat(_), mn)
  nb.go(nn, mx, dvm(nn, mx, U32.add(mx, mx), hm, h2), hm)

# ---- F. how many bytes bs writes ----

# at most 0 is 0
def le.zero(xx: Nat, +hh: {Nat.is_le(xx, 0n) == True{} : Bool}) -> {xx == 0n : Nat}:
  match xx:
    case 0n:
      {==}
    case 1n+pp:
      Empty.absurd({1n+pp == 0n : Nat}, M1.false_true(hh))

# nothing is below itself
def pfin.lt.irr(mm: Nat, +hh: {Nat.is_lt(mm, mm) == True{} : Bool}) -> Empty:
  match mm:
    case 0n:
      M1.false_true(hh)
    case 1n+pp:
      pfin.lt.irr(pp, hh)

# m + x is not below m
def lt.self(+mm: Nat, +xx: Nat, +hh: {Nat.is_lt(Nat.add(mm, xx), mm) == True{} : Bool}) -> Empty:
  pfin.lt.irr(mm, M1.le_lt_trans(mm, Nat.add(mm, xx), mm, M8.nle_add(mm, xx), hh))

# a sum that is 0 has a right part 0
def add.zero.r(aa: Nat, +bb: Nat, +hh: {Nat.add(aa, bb) == 0n : Nat}) -> {bb == 0n : Nat}:
  match aa:
    case 0n:
      hh
    case 1n+pp:
      Empty.absurd({bb == 0n : Nat}, M1.zero_succ(Nat.add(pp, bb), Equal.sym(Nat, 1n+Nat.add(pp, bb), 0n, hh)))

# no bytes left, no blocks left
def kok.nil(kk: Nat, +mn: Nat, hk: M1.kok(0n, kk, mn)) -> {Nat.mul(kk, 5n) == 0n : Nat}:
  match kk:
    case 0n:
      {==}
    case 1n+(+kp):
      (h_lt, _h_le) = hk
      Empty.absurd({Nat.mul(1n+kp, 5n) == 0n : Nat}, M1.false_true(Equal.trans(Bool, False{}, Nat.is_lt(Nat.mul(kp,
        mn), 0n), True{}, M1.lt_zero_false(Nat.mul(kp, mn)), h_lt)))

# a new block's room after its first byte is at most the bytes after it
def ks.le(
  zz: Bool,
  +left: U32,
  +mx: U32,
  +nt: Nat,
  +nzm: {U32.is_zero(mx) == False{} : Bool},
  +ez: {U32.is_le(left, mx) == zz : Bool},
  +hn: {U32.to_nat(left) == 1n+nt : Nat}
) -> {Nat.is_le(U32.to_nat((capm(zz, left, mx) - 1 : U32)), nt) == True{} : Bool}:
  match zz:
    case True{}:
      M1.le_rw_l(nt, U32.to_nat((left - 1 : U32)), nt, Equal.sym(Nat, U32.to_nat((left - 1 : U32)), nt,
        M1.u32_pred(left, nt, hn)), M1.le_refl(nt))
    case False{}:
      +m1 = (mx - 1 : U32)
      +e_m = {M1.u32_dec(mx, nzm) : {U32.to_nat(mx) == 1n+U32.to_nat(m1) : Nat}}
      +h0 = {Equal.trans(Bool, Nat.is_le(1n+nt, 1n+U32.to_nat(m1)), U32.is_le(left, mx), False{},
        Equal.sym(Bool, U32.is_le(left, mx), Nat.is_le(1n+nt, 1n+U32.to_nat(m1)), Equal.trans(Bool,
          U32.is_le(left, mx), Nat.is_le(U32.to_nat(left), U32.to_nat(mx)), Nat.is_le(1n+nt, 1n+U32.to_nat(m1)),
          M10.u32_le(left, mx), Equal.trans(Bool, Nat.is_le(U32.to_nat(left), U32.to_nat(mx)), Nat.is_le(1n+nt,
          U32.to_nat(mx)), Nat.is_le(1n+nt, 1n+U32.to_nat(m1)), Equal.cong(Nat, Bool, xx => Nat.is_le(xx,
          U32.to_nat(mx)), U32.to_nat(left), 1n+nt, hn), Equal.cong(Nat, Bool, xx => Nat.is_le(1n+nt, xx),
          U32.to_nat(mx), 1n+U32.to_nat(m1), e_m)))), ez) : {Nat.is_le(nt, U32.to_nat(m1)) == False{} : Bool}}
      M1.lt_le(U32.to_nat(m1), nt, nle.lt(nt, U32.to_nat(m1), h0))

# the blocks after a new block: one fewer than before it
def ks.k(
  zz: Bool,
  kp: Nat,
  +left: U32,
  +mx: U32,
  +nt: Nat,
  +nzm: {U32.is_zero(mx) == False{} : Bool},
  +ez: {U32.is_le(left, mx) == zz : Bool},
  +hn: {U32.to_nat(left) == 1n+nt : Nat},
  +h_lt: {Nat.is_lt(Nat.mul(kp, U32.to_nat(mx)), 1n+nt) == True{} : Bool},
  +h_le: {Nat.is_le(1n+nt, Nat.add(U32.to_nat(mx), Nat.mul(kp, U32.to_nat(mx)))) == True{} : Bool}
) -> M1.kok(Nat.sub(nt, U32.to_nat((capm(zz, left, mx) - 1 : U32))), kp, U32.to_nat(mx)):
  match zz kp:
    case True{} 0n:
      +e_l = {M1.u32_pred(left, nt, hn) : {U32.to_nat((left - 1 : U32)) == nt : Nat}}
      Equal.trans(Nat, Nat.sub(nt, U32.to_nat((left - 1 : U32))), Nat.sub(nt, nt), 0n, Equal.cong(Nat, Nat, xx =>
        Nat.sub(nt, xx), U32.to_nat((left - 1 : U32)), nt, e_l), M10.sub_zero_le(nt, nt, M1.le_refl(nt)))
    case True{} 1n+(+k2):
      +mn = U32.to_nat(mx)
      +h0 = {Equal.trans(Bool, Nat.is_le(U32.to_nat(left), mn), U32.is_le(left, mx), True{}, Equal.sym(Bool,
        U32.is_le(left, mx), Nat.is_le(U32.to_nat(left), mn), M10.u32_le(left, mx)), ez) : {Nat.is_le(U32.to_nat(left),
        mn) == True{} : Bool}}
      +h1 = {M1.le_rw_l(U32.to_nat(left), 1n+nt, mn, hn, h0) : {Nat.is_le(1n+nt, mn) == True{} : Bool}}
      Empty.absurd(M1.kok(Nat.sub(nt, U32.to_nat((left - 1 : U32))), 1n+k2, mn), lt.self(mn, Nat.mul(k2, mn),
        M1.lt_le_trans(Nat.add(mn, Nat.mul(k2, mn)), 1n+nt, mn, h_lt, h1)))
    case False{} 0n:
      +mn = U32.to_nat(mx)
      +m1 = U32.to_nat((mx - 1 : U32))
      +xn = Nat.sub(nt, m1)
      +e_m = {M1.u32_dec(mx, nzm) : {mn == 1n+m1 : Nat}}
      +h_m = {ks.le(False{}, left, mx, nt, nzm, ez, hn) : {Nat.is_le(m1, nt) == True{} : Bool}}
      +e_x = {Equal.trans(Nat, 1n+nt, 1n+Nat.add(m1, xn), Nat.add(mn, xn), Equal.cong(Nat, Nat, kk => 1n+kk, nt,
        Nat.add(m1, xn), Equal.sym(Nat, Nat.add(m1, xn), nt, M10.add_sub(m1, nt, h_m))), Equal.cong(Nat, Nat, kk =>
        Nat.add(kk, xn), 1n+m1, mn, Equal.sym(Nat, mn, 1n+m1, e_m))) : {1n+nt == Nat.add(mn, xn) : Nat}}
      +h2 = {M1.le_rw_l(1n+nt, Nat.add(mn, xn), Nat.add(mn, 0n), e_x, h_le) : {Nat.is_le(Nat.add(mn, xn), Nat.add(mn,
        0n)) == True{} : Bool}}
      le.zero(xn, M10.le_cancel(mn, xn, 0n, h2))
    case False{} 1n+(+k2):
      +mn = U32.to_nat(mx)
      +m1 = U32.to_nat((mx - 1 : U32))
      +xn = Nat.sub(nt, m1)
      +km = Nat.mul(k2, mn)
      +e_m = {M1.u32_dec(mx, nzm) : {mn == 1n+m1 : Nat}}
      +h_m = {ks.le(False{}, left, mx, nt, nzm, ez, hn) : {Nat.is_le(m1, nt) == True{} : Bool}}
      +e_x = {Equal.trans(Nat, 1n+nt, 1n+Nat.add(m1, xn), Nat.add(mn, xn), Equal.cong(Nat, Nat, kk => 1n+kk, nt,
        Nat.add(m1, xn), Equal.sym(Nat, Nat.add(m1, xn), nt, M10.add_sub(m1, nt, h_m))), Equal.cong(Nat, Nat, kk =>
        Nat.add(kk, xn), 1n+m1, mn, Equal.sym(Nat, mn, 1n+m1, e_m))) : {1n+nt == Nat.add(mn, xn) : Nat}}
      (M10.lt_cancel(mn, km, xn, M1.lt_rw_r(Nat.add(mn, km), 1n+nt, Nat.add(mn, xn), e_x, h_lt)), M10.le_cancel(mn, xn,
        Nat.mul(1n+k2, mn), M1.le_rw_l(1n+nt, Nat.add(mn, xn), Nat.add(mn, Nat.mul(1n+k2, mn)), e_x, h_le)))

# what pfin.cnt proves: bs writes its bytes and 5 more for each block header
def cnt.ty(
  +xs: List<&2, U32>,
  +znew: Bool,
  +zlast: Bool,
  +rp: U32,
  +left: U32,
  +plen: U32,
  +pbf: U32,
  +kk: Nat
) -> Type:
  {List.length(&2, U32, M1.bs(xs, znew, zlast, rp, left, plen, pbf)) == Nat.add(List.length(&2, U32, xs), Nat.mul(kk,
    5n)) : Nat}

# bs after a block's first byte, with plen bytes in the block and l2 left after it
def bs2(+tl: List<&2, U32>, +plen: U32, +l2: U32) -> List<&2, U32>:
  M1.bs(tl, U32.is_zero((plen - 1 : U32)), U32.is_eq((plen - 1 : U32), 1), (plen - 1 : U32), l2, Png.enc.cap(l2),
    Png.enc.bf(l2))

# the header, the first byte and the rest of a new block: six more bytes
def cnt.open(
  +hd: U32,
  +tl: List<&2, U32>,
  +l2: U32,
  +plen: U32,
  +pbf: U32,
  +kp: Nat,
  +ih: {List.length(&2, U32, bs2(tl, plen, l2)) == Nat.add(List.length(&2, U32, tl), Nat.mul(kp, 5n)) : Nat}
) -> {List.length(&2, U32, open.bs(hd, tl, l2, plen, pbf)) == Nat.add(1n+List.length(&2, U32, tl), Nat.mul(1n+kp,
  5n)) : Nat}:
  +nt = List.length(&2, U32, tl)
  +k5 = Nat.mul(kp, 5n)
  Equal.trans(Nat, 6n+List.length(&2, U32, M1.bs(tl, U32.is_zero((plen - 1 : U32)), U32.is_eq((plen - 1 : U32), 1),
    (plen - 1 : U32), l2, Png.enc.cap(l2), Png.enc.bf(l2))), 6n+Nat.add(nt, k5), 1n+Nat.add(nt, 5n+k5),
    Equal.cong(Nat, Nat, xx => 6n+xx, List.length(&2, U32, M1.bs(tl, U32.is_zero((plen - 1 : U32)),
        U32.is_eq((plen - 1 :
    U32), 1), (plen - 1 : U32), l2, Png.enc.cap(l2), Png.enc.bf(l2))), Nat.add(nt, k5), ih),
    Equal.cong(Nat, Nat, xx => 1n+xx, 5n+Nat.add(nt, k5), Nat.add(nt, 5n+k5), Equal.sym(Nat, Nat.add(nt, 5n+k5),
    5n+Nat.add(nt, k5), M1.add_swap(nt, 5n, k5))))

# kok along an equation of the byte count
def kok.rw(+xa: Nat, +xb: Nat, +kk: Nat, +mn: Nat, +ee: {xa == xb : Nat}, hk: M1.kok(xa, kk, mn)) -> M1.kok(xb, kk, mn):
  %ee : M1.kok(_, kk, mn)
  hk

# the count's hypothesis for the rest of a block opened with plen bytes
def cnt.edge.ty(-tl: List<&2, U32>, -left: U32, -plen: U32, -kp: Nat, -mx: U32) -> Type:
  @xn: Nat -> {Nat.add(U32.to_nat((plen - 1 : U32)), xn) == List.length(&2, U32, tl) : Nat} -> M1.kok(xn, kp,
    U32.to_nat(mx)) -> cnt.ty(tl, U32.is_zero((plen - 1 : U32)), U32.is_eq((plen - 1 : U32), 1), (plen - 1 : U32),
    (left - 1 : U32), Png.enc.cap((left - 1 : U32)), Png.enc.bf((left - 1 : U32)), kp)

# a new block with kp + 1 blocks to go: the header and the first byte, then
# the rest of the walk, with kp blocks after this one
def cnt.edge(
  +hd: U32,
  +tl: List<&2, U32>,
  +left: U32,
  +plen: U32,
  +pbf: U32,
  +mx: U32,
  +emx: {mx == 65535 : U32},
  +kp: Nat,
  +hn: {U32.to_nat(left) == 1n+List.length(&2, U32, tl) : Nat},
  +h_lt: {Nat.is_lt(Nat.mul(kp, U32.to_nat(mx)), 1n+List.length(&2, U32, tl)) == True{} : Bool},
  +h_le: {Nat.is_le(1n+List.length(&2, U32, tl), Nat.mul(1n+kp, U32.to_nat(mx))) == True{} : Bool},
  pe: {plen == Png.enc.cap(left) : U32} & {pbf == Png.enc.bf(left) : U32},
  cnt_t: cnt.edge.ty(tl, left, plen, kp, mx)
) -> {List.length(&2, U32, open.bs(hd, tl, (left - 1 : U32), plen, pbf)) == Nat.add(1n+List.length(&2, U32, tl),
  Nat.mul(1n+kp, 5n)) : Nat}:
  (+e_plen, _e_pbf) = pe
  +nt = List.length(&2, U32, tl)
  +zz = U32.is_le(left, 65535)
  +cm = capm(zz, left, mx)
  +mn = U32.to_nat(mx)
  +c2 = U32.to_nat((plen - 1 : U32))
  +nzm = {mx.nz(mx, emx) : {U32.is_zero(mx) == False{} : Bool}}
  +ezm = {le.mx(left, mx, emx) : {U32.is_le(left, mx) == zz : Bool}}
  +e_c = {Equal.cong(U32, Nat, uu => U32.to_nat((uu - 1 : U32)), plen, cm, Equal.trans(U32, plen, Png.enc.cap(left), cm,
    e_plen, cap.m(zz, left, mx, emx))) : {c2 == U32.to_nat((cm - 1 : U32)) : Nat}}
  +h_c = {M1.le_rw_l(U32.to_nat((cm - 1 : U32)), c2, nt, Equal.sym(Nat, c2, U32.to_nat((cm - 1 : U32)), e_c), ks.le(zz,
    left, mx, nt, nzm, ezm, hn)) : {Nat.is_le(c2, nt) == True{} : Bool}}
  +x2 = Nat.sub(nt, c2)
  +hx2 = {M10.add_sub(c2, nt, h_c) : {Nat.add(c2, x2) == nt : Nat}}
  hk2 = kok.rw(Nat.sub(nt, U32.to_nat((cm - 1 : U32))), x2, kp, mn, Equal.cong(Nat, Nat, kk => Nat.sub(nt, kk),
    U32.to_nat((cm - 1 : U32)), c2, Equal.sym(Nat, c2, U32.to_nat((cm - 1 : U32)), e_c)), ks.k(zz, kp, left, mx, nt,
    nzm, ezm, hn, h_lt, h_le))
  cnt.open(hd, tl, (left - 1 : U32), plen, pbf, kp, cnt_t(x2, hx2, hk2))

# bs from a state: its bytes, and a header for each of the kk blocks it opens,
# xn the bytes after the open block (rp of them still in it)
def pfin.cnt(
  xs: List<&2, U32>,
  znew: Bool,
  zlast: Bool,
  +kk: Nat,
  +rp: U32,
  +left: U32,
  +plen: U32,
  +pbf: U32,
  +mx: U32,
  +xn: Nat,
  +emx: {mx == 65535 : U32},
  +hzn: {znew == U32.is_zero(rp) : Bool},
  +hzl: {zlast == U32.is_eq(rp, 1) : Bool},
  +hn: {U32.to_nat(left) == List.length(&2, U32, xs) : Nat},
  +hx: {Nat.add(U32.to_nat(rp), xn) == List.length(&2, U32, xs) : Nat},
  hk: M1.kok(xn, kk, U32.to_nat(mx)),
  hb: M1.at.edge(rp, left, plen, pbf)
) -> cnt.ty(xs, znew, zlast, rp, left, plen, pbf, kk):
  match xs znew zlast:
    case Nil{} _zn _zl:
      +e_x = {add.zero.r(U32.to_nat(rp), xn, hx) : {xn == 0n : Nat}}
      Equal.sym(Nat, Nat.mul(kk, 5n), 0n, kok.nil(kk, U32.to_nat(mx), kok.rw(xn, 0n, kk, U32.to_nat(mx), e_x, hk)))
    case +h <> +t False{} False{}:
      +rp2 = (rp - 1 : U32)
      +l2 = (left - 1 : U32)
      +nt = List.length(&2, U32, t)
      +nz_rp = {Equal.sym(Bool, False{}, U32.is_zero(rp), hzn) : {U32.is_zero(rp) == False{} : Bool}}
      +e_rp = {M1.u32_dec(rp, nz_rp) : {U32.to_nat(rp) == 1n+U32.to_nat(rp2) : Nat}}
      +nz_rp2 = {M1.two(rp, hzn, hzl) : {U32.is_zero(rp2) == False{} : Bool}}
      +hx2 = {M1.succ_inj(Nat.add(U32.to_nat(rp2), xn), nt, Equal.trans(Nat, 1n+Nat.add(U32.to_nat(rp2), xn),
        Nat.add(U32.to_nat(rp), xn), 1n+nt, Equal.cong(Nat, Nat, kk2 => Nat.add(kk2, xn), 1n+U32.to_nat(rp2),
        U32.to_nat(rp), Equal.sym(Nat, U32.to_nat(rp), 1n+U32.to_nat(rp2), e_rp)), hx)) : {Nat.add(U32.to_nat(rp2),
        xn) == nt : Nat}}
      +hn2 = {M1.u32_pred(left, nt, hn) : {U32.to_nat(l2) == nt : Nat}}
      Equal.cong(Nat, Nat, x2 => 1n+x2, List.length(&2, U32, M1.bs(t, False{}, U32.is_eq(rp2, 1), rp2, l2, plen, pbf)),
        Nat.add(nt, Nat.mul(kk, 5n)), pfin.cnt(t, False{}, U32.is_eq(rp2, 1), kk, rp2, l2, plen, pbf, mx, xn, emx,
        Equal.sym(Bool, U32.is_zero(rp2), False{}, nz_rp2), {==}, hn2, hx2, hk, M1.edge.no(rp2, l2, plen, pbf, nz_rp2)))
    case +h <> +t False{} True{}:
      +l2 = (left - 1 : U32)
      +nt = List.length(&2, U32, t)
      +e_rp = {M1.one.val(rp, hzl) : {U32.to_nat(rp) == 1n : Nat}}
      +hx2 = {M1.succ_inj(xn, nt, Equal.trans(Nat, 1n+xn, Nat.add(U32.to_nat(rp), xn), 1n+nt, Equal.cong(Nat, Nat,
        kk2 => Nat.add(kk2, xn), 1n, U32.to_nat(rp), Equal.sym(Nat, U32.to_nat(rp), 1n, e_rp)), hx)) :
        {Nat.add(U32.to_nat(0), xn) == nt : Nat}}
      +hn2 = {M1.u32_pred(left, nt, hn) : {U32.to_nat(l2) == nt : Nat}}
      Equal.cong(Nat, Nat, x2 => 1n+x2, List.length(&2, U32, M1.bs(t, True{}, False{}, 0, l2, Png.enc.cap(l2),
        Png.enc.bf(l2))), Nat.add(nt, Nat.mul(kk, 5n)), pfin.cnt(t, True{}, False{}, kk, 0, l2, Png.enc.cap(l2),
        Png.enc.bf(l2), mx, xn, emx, {==}, {==}, hn2, hx2, hk, _ez => ({==}, {==})))
    case +h <> +t True{} _zl:
      match kk:
        case 0n:
          +nt = List.length(&2, U32, t)
          +e0 = {M1.zero.val(rp, hzn) : {U32.to_nat(rp) == 0n : Nat}}
          +e_xn = {Equal.trans(Nat, xn, Nat.add(U32.to_nat(rp), xn), 1n+nt, Equal.cong(Nat, Nat, kk2 => Nat.add(kk2,
            xn),
            0n, U32.to_nat(rp), Equal.sym(Nat, U32.to_nat(rp), 0n, e0)), hx) : {xn == 1n+nt : Nat}}
          Empty.absurd(cnt.ty(h <> t, True{}, _zl, rp, left, plen, pbf, 0n), M1.zero_succ(nt, Equal.trans(Nat, 0n, xn,
            1n+nt, Equal.sym(Nat, xn, 0n, hk), e_xn)))
        case 1n+(+kp):
          (+h_lt, +h_le) = hk
          +nt = List.length(&2, U32, t)
          +l2 = (left - 1 : U32)
          +mn = U32.to_nat(mx)
          +e0 = {M1.zero.val(rp, hzn) : {U32.to_nat(rp) == 0n : Nat}}
          +e_xn = {Equal.trans(Nat, xn, Nat.add(U32.to_nat(rp), xn), 1n+nt, Equal.cong(Nat, Nat, kk2 => Nat.add(kk2,
            xn),
            0n, U32.to_nat(rp), Equal.sym(Nat, U32.to_nat(rp), 0n, e0)), hx) : {xn == 1n+nt : Nat}}
          +ez = {Equal.sym(Bool, True{}, U32.is_zero(rp), hzn) : {U32.is_zero(rp) == True{} : Bool}}
          +hn2 = {M1.u32_pred(left, nt, hn) : {U32.to_nat(l2) == nt : Nat}}
          cnt.edge(h, t, left, plen, pbf, mx, emx, kp, hn, M1.lt_rw_r(Nat.mul(kp, mn), xn, 1n+nt, e_xn, h_lt),
            M1.le_rw_l(xn, 1n+nt, Nat.mul(1n+kp, mn), e_xn, h_le), hb(ez), x2 => a1 => a2 => pfin.cnt(t,
                U32.is_zero((plen - 1
            : U32)), U32.is_eq((plen - 1 : U32), 1), kp, (plen - 1 : U32), l2, Png.enc.cap(l2), Png.enc.bf(l2), mx, x2,
            emx, {==}, {==}, hn2, a1, a2, _ez => ({==}, {==})))

# the blocks enc.blocks writes for more than one block: the bytes, and 5 for
# each of the enc.nblk block headers
def cnt.blocks(
  +xs: List<&2, U32>,
  +mx: U32,
  +emx: {mx == 65535 : U32},
  +hn: {U32.to_nat(Png.enc.len(xs, 0)) == List.length(&2, U32, xs) : Nat},
  +hbig: {U32.is_le(Png.enc.len(xs, 0), 65535) == False{} : Bool}
) -> {List.length(&2, U32, Png.enc.blocks(65535, xs)) == Nat.add(List.length(&2, U32, xs),
  Nat.mul(U32.to_nat(Png.enc.nblk(Png.enc.len(xs, 0))), 5n)) : Nat}:
  +nn = Png.enc.len(xs, 0)
  +kk = U32.to_nat(Png.enc.nblk(nn))
  +bb = M1.bs(xs, True{}, False{}, 0, nn, Png.enc.cap(nn), Png.enc.bf(nn))
  Equal.trans(Nat, List.length(&2, U32, Png.enc.blocks(65535, xs)), List.length(&2, U32, bb), Nat.add(List.length(&2,
    U32, xs), Nat.mul(kk, 5n)), Equal.cong(List<&2, U32>, Nat, ys => List.length(&2, U32, ys), Png.enc.blocks(65535,
    xs), bb, sim.blocks(xs, mx, emx, hn, hbig)), pfin.cnt(xs, True{}, False{}, kk, 0, nn, Png.enc.cap(nn),
        Png.enc.bf(nn),
      mx,
    List.length(&2, U32, xs), emx, {==}, {==}, hn, {==}, kok.rw(U32.to_nat(nn), List.length(&2, U32, xs), kk,
    U32.to_nat(mx), hn, nb.k(nn, mx, emx)), _ez => ({==}, {==})))

# folding a list then more is folding both
def fold.app(
  xs: List<&2, U32>,
  +ys: List<&2, U32>,
  +cc: U32
) -> {Crc.crc.fold(List.append(&2, U32, xs, ys), cc) == Crc.crc.fold(ys, Crc.crc.fold(xs, cc)) : U32}:
  match xs:
    case Nil{}:
      {==}
    case +hd <> tl:
      fold.app(tl, ys, Crc.crc.byte(cc, hd))

# a run, then more: one run over both
def fr.app(
  +xs: List<&2, U32>,
  +ys: List<&2, U32>,
  +cc: U32,
  +acc: List<&2, U32>
) -> {M1.fr(ys, Crc.crc.fold(xs, cc), List.reverse.go(&2, U32, xs, acc)) == M1.fr(List.append(&2, U32, xs, ys), cc,
  acc) : U32 & List<&2, U32>}:
  +f2 = Crc.crc.fold(ys, Crc.crc.fold(xs, cc))
  +fa = Crc.crc.fold(List.append(&2, U32, xs, ys), cc)
  +r2 = List.reverse.go(&2, U32, ys, List.reverse.go(&2, U32, xs, acc))
  +ra = List.reverse.go(&2, U32, List.append(&2, U32, xs, ys), acc)
  Equal.trans(U32 & List<&2, U32>, (f2, r2), (fa, r2), (fa, ra),
    Equal.cong(U32, U32 & List<&2, U32>, uu => (uu, r2), f2, fa, Equal.sym(U32, fa, f2, fold.app(xs, ys, cc))),
    Equal.cong(List<&2, U32>, U32 & List<&2, U32>, ll => (fa, ll), r2, ra, Equal.sym(List<&2, U32>, ra, r2,
      M4.revgo_app(xs, ys, acc))))

# three runs reversed onto nothing, reversed back: the runs in order
def rev3(
  +aa: List<&2, U32>,
  +bb: List<&2, U32>,
  +cc: List<&2, U32>
) -> {List.reverse(&2, U32, List.reverse.go(&2, U32, cc, List.reverse.go(&2, U32, bb, List.reverse.go(&2, U32, aa,
  [])))) == List.append(&2, U32, aa, List.append(&2, U32, bb, cc)) : List<&2, U32>}:
  +ab = List.append(&2, U32, aa, bb)
  +abc = List.append(&2, U32, ab, cc)
  Equal.trans(List<&2, U32>, List.reverse(&2, U32, List.reverse.go(&2, U32, cc, List.reverse.go(&2, U32, bb,
    List.reverse.go(&2, U32, aa, [])))), List.reverse(&2, U32, List.reverse.go(&2, U32, abc, [])),
    List.append(&2, U32, aa, List.append(&2, U32, bb, cc)),
    Equal.cong(List<&2, U32>, List<&2, U32>, ll => List.reverse(&2, U32, ll), List.reverse.go(&2, U32, cc,
      List.reverse.go(&2, U32, bb, List.reverse.go(&2, U32, aa, []))), List.reverse.go(&2, U32, abc, []),
      Equal.trans(List<&2, U32>, List.reverse.go(&2, U32, cc, List.reverse.go(&2, U32, bb, List.reverse.go(&2, U32,
        aa, []))), List.reverse.go(&2, U32, cc, List.reverse.go(&2, U32, ab, [])), List.reverse.go(&2, U32, abc, []),
        Equal.cong(List<&2, U32>, List<&2, U32>, ll => List.reverse.go(&2, U32, cc, ll), List.reverse.go(&2, U32, bb,
          List.reverse.go(&2, U32, aa, [])), List.reverse.go(&2, U32, ab, []), Equal.sym(List<&2, U32>,
          List.reverse.go(&2, U32, ab, []), List.reverse.go(&2, U32, bb, List.reverse.go(&2, U32, aa, [])),
          M4.revgo_app(aa, bb, []))),
        Equal.sym(List<&2, U32>, List.reverse.go(&2, U32, abc, []), List.reverse.go(&2, U32, cc, List.reverse.go(&2,
          U32, ab, [])), M4.revgo_app(ab, cc, [])))),
    Equal.trans(List<&2, U32>, List.reverse(&2, U32, List.reverse.go(&2, U32, abc, [])), abc, List.append(&2, U32, aa,
      List.append(&2, U32, bb, cc)), M1.inf.rev_rev(abc), M1.app_assoc(aa, bb, cc)))

# the end of the IDAT chunk as seal.crc writes it: the length, the type and
# data, the CRC-32 of them, then IEND, once the whole file is reversed
def tail.eq(
  +ll: U32,
  +tt: List<&2, U32>,
  +ie: List<&2, U32>
) -> {List.reverse(&2, U32, Png.enc.cat.go(ie, Png.enc.cat.go(Png.enc.be((Crc.crc.fold(tt,
  4294967295) .^. 4294967295 : U32)), List.reverse.go(&2, U32, tt, Png.enc.cat.go(Png.enc.be(ll), []))))) ==
  List.append(&2, U32, Png.enc.be(ll), List.append(&2, U32, tt, List.append(&2, U32, Png.enc.be((Crc.crc.fold(tt,
  4294967295) .^. 4294967295 : U32)), ie))) : List<&2, U32>}:
  +bl = Png.enc.be(ll)
  +ee = Png.enc.be((Crc.crc.fold(tt, 4294967295) .^. 4294967295 : U32))
  +a0 = List.reverse.go(&2, U32, bl, [])
  +a1 = List.reverse.go(&2, U32, tt, a0)
  +a2 = List.reverse.go(&2, U32, ee, a1)
  +lt = List.append(&2, U32, bl, tt)
  Equal.trans(List<&2, U32>, List.reverse(&2, U32, Png.enc.cat.go(ie, Png.enc.cat.go(ee, List.reverse.go(&2, U32, tt,
    Png.enc.cat.go(bl, []))))), List.reverse(&2, U32, List.reverse.go(&2, U32, ie, List.reverse.go(&2, U32, ee,
    List.reverse.go(&2, U32, lt, [])))), List.append(&2, U32, bl, List.append(&2, U32, tt, List.append(&2, U32, ee,
    ie))),
    Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.reverse(&2, U32, ys), Png.enc.cat.go(ie, Png.enc.cat.go(ee,
      List.reverse.go(&2, U32, tt, Png.enc.cat.go(bl, [])))), List.reverse.go(&2, U32, ie, List.reverse.go(&2, U32, ee,
      List.reverse.go(&2, U32, lt, []))),
      Equal.trans(List<&2, U32>, Png.enc.cat.go(ie, Png.enc.cat.go(ee, List.reverse.go(&2, U32, tt, Png.enc.cat.go(bl,
        [])))), Png.enc.cat.go(ie, Png.enc.cat.go(ee, a1)), List.reverse.go(&2, U32, ie, List.reverse.go(&2, U32, ee,
        List.reverse.go(&2, U32, lt, []))),
        Equal.cong(List<&2, U32>, List<&2, U32>, ys => Png.enc.cat.go(ie, Png.enc.cat.go(ee, List.reverse.go(&2, U32,
          tt, ys))), Png.enc.cat.go(bl, []), a0, M8.catgo_rev(bl, [])),
        Equal.trans(List<&2, U32>, Png.enc.cat.go(ie, Png.enc.cat.go(ee, a1)), Png.enc.cat.go(ie, a2),
          List.reverse.go(&2, U32, ie, List.reverse.go(&2, U32, ee, List.reverse.go(&2, U32, lt, []))),
          Equal.cong(List<&2, U32>, List<&2, U32>, ys => Png.enc.cat.go(ie, ys), Png.enc.cat.go(ee, a1), a2,
            M8.catgo_rev(ee, a1)),
          Equal.trans(List<&2, U32>, Png.enc.cat.go(ie, a2), List.reverse.go(&2, U32, ie, a2), List.reverse.go(&2, U32,
            ie, List.reverse.go(&2, U32, ee, List.reverse.go(&2, U32, lt, []))), M8.catgo_rev(ie, a2),
            Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.reverse.go(&2, U32, ie, List.reverse.go(&2, U32, ee,
              ys)), a1, List.reverse.go(&2, U32, lt, []), Equal.sym(List<&2, U32>, List.reverse.go(&2, U32, lt, []), a1,
              M4.revgo_app(bl, tt, []))))))),
    Equal.trans(List<&2, U32>, List.reverse(&2, U32, List.reverse.go(&2, U32, ie, List.reverse.go(&2, U32, ee,
      List.reverse.go(&2, U32, lt, [])))), List.append(&2, U32, lt, List.append(&2, U32, ee, ie)), List.append(&2, U32,
      bl, List.append(&2, U32, tt, List.append(&2, U32, ee, ie))), rev3(lt, ee, ie), M1.app_assoc(bl, tt,
      List.append(&2, U32, ee, ie))))

# the chunk's type and data as enc.chunk counts them are t0 then the sum
def body.eq(
  +bb: List<&2, U32>,
  +sum: U32
) -> {Png.enc.cat(Png.enc.be(Png.tag.idat()), M1.zb(bb, sum)) == List.append(&2, U32, M1.t0(bb),
    Png.enc.be(sum)) : List<&2,
  U32>}:
  +bi = Png.enc.be(Png.tag.idat())
  +bs2 = Png.enc.be(sum)
  +zz = List.append(&2, U32, [120, 1], List.append(&2, U32, bb, bs2))
  Equal.trans(List<&2, U32>, Png.enc.cat(bi, M1.zb(bb, sum)), List.append(&2, U32, bi, zz), List.append(&2, U32,
      M1.t0(bb),
    bs2),
    Equal.trans(List<&2, U32>, Png.enc.cat(bi, M1.zb(bb, sum)), List.append(&2, U32, bi, M1.zb(bb, sum)),
        List.append(&2,
      U32, bi, zz), M8.cat_app(bi, M1.zb(bb, sum)), Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.append(&2, U32,
      bi, ys), M1.zb(bb, sum), zz, Equal.trans(List<&2, U32>, M1.zb(bb, sum), List.append(&2, U32, [120, 1],
      Png.enc.cat(bb, bs2)), zz, M8.cat_app([120, 1], Png.enc.cat(bb, bs2)), Equal.cong(List<&2, U32>, List<&2, U32>,
      ys => List.append(&2, U32, [120, 1], ys), Png.enc.cat(bb, bs2), List.append(&2, U32, bb, bs2),
      M8.cat_app(bb, bs2))))),
    Equal.sym(List<&2, U32>, List.append(&2, U32, M1.t0(bb), bs2), List.append(&2, U32, bi, zz), Equal.trans(List<&2,
      U32>, List.append(&2, U32, M1.t0(bb), bs2), List.append(&2, U32, bi, List.append(&2, U32, List.append(&2, U32,
          [120,
      1], bb), bs2)), List.append(&2, U32, bi, zz), M1.app_assoc(bi, List.append(&2, U32, [120, 1], bb), bs2),
      Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.append(&2, U32, bi, ys), List.append(&2, U32,
      List.append(&2, U32, [120, 1], bb), bs2), zz, M1.app_assoc([120, 1], bb, bs2)))))

# enc.chunk of IDAT, then IEND, is gg of its type and data
def chunk.gg(
  +data: List<&2, U32>,
  +ie: List<&2, U32>
) -> {Png.enc.cat(Png.enc.chunk(Png.tag.idat(), data), ie) == M1.gg(Png.enc.cat(Png.enc.be(Png.tag.idat()), data),
  Png.enc.len(data, 0), ie) : List<&2, U32>}:
  +body = Png.enc.cat(Png.enc.be(Png.tag.idat()), data)
  +be_c = Png.enc.be(Crc.crc32(body))
  +be_n = Png.enc.be(Png.enc.len(data, 0))
  Equal.trans(List<&2, U32>, Png.enc.cat(Png.enc.cat(be_n, Png.enc.cat(body, be_c)), ie), List.append(&2, U32,
    List.append(&2, U32, be_n, List.append(&2, U32, body, be_c)), ie), M1.gg(body, Png.enc.len(data, 0), ie),
    Equal.trans(List<&2, U32>, Png.enc.cat(Png.enc.cat(be_n, Png.enc.cat(body, be_c)), ie), List.append(&2, U32,
      Png.enc.cat(be_n, Png.enc.cat(body, be_c)), ie), List.append(&2, U32, List.append(&2, U32, be_n, List.append(&2,
      U32, body, be_c)), ie), M8.cat_app(Png.enc.cat(be_n, Png.enc.cat(body, be_c)), ie), Equal.cong(List<&2, U32>,
      List<&2, U32>, ys => List.append(&2, U32, ys, ie), Png.enc.cat(be_n, Png.enc.cat(body, be_c)), List.append(&2,
      U32, be_n, List.append(&2, U32, body, be_c)), Equal.trans(List<&2, U32>, Png.enc.cat(be_n, Png.enc.cat(body,
      be_c)), List.append(&2, U32, be_n, Png.enc.cat(body, be_c)), List.append(&2, U32, be_n, List.append(&2, U32,
      body, be_c)), M8.cat_app(be_n, Png.enc.cat(body, be_c)), Equal.cong(List<&2, U32>, List<&2, U32>, ys =>
      List.append(&2, U32, be_n, ys), Png.enc.cat(body, be_c), List.append(&2, U32, body, be_c), M8.cat_app(body,
      be_c))))),
    Equal.trans(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, be_n, List.append(&2, U32, body, be_c)), ie),
      List.append(&2, U32, be_n, List.append(&2, U32, List.append(&2, U32, body, be_c), ie)), M1.gg(body,
      Png.enc.len(data, 0), ie), M1.app_assoc(be_n, List.append(&2, U32, body, be_c), ie), Equal.cong(List<&2, U32>,
      List<&2, U32>, ys => List.append(&2, U32, be_n, ys), List.append(&2, U32, List.append(&2, U32, body, be_c), ie),
      List.append(&2, U32, body, List.append(&2, U32, be_c, ie)), M1.app_assoc(body, be_c, ie))))

# the IDAT chunk from its CRC run: the run over the type, header and blocks,
# then the Adler-32 sum, the CRC, and IEND, is enc.chunk's IDAT then IEND
def tail.chunk(
  +bb: List<&2, U32>,
  +sum: U32,
  +ll: U32,
  +ie: List<&2, U32>,
  +hl: {ll == Png.enc.len(M1.zb(bb, sum), 0) : U32}
) -> {Png.enc.seal.adler(M1.fr(M1.t0(bb), 4294967295, Png.enc.cat.go(Png.enc.be(ll), [])), sum, ie) ==
  Png.enc.cat(Png.enc.chunk(Png.tag.idat(), M1.zb(bb, sum)), ie) : List<&2, U32>}:
  +aa = Png.enc.cat.go(Png.enc.be(ll), [])
  +bs2 = Png.enc.be(sum)
  +tt = List.append(&2, U32, M1.t0(bb), bs2)
  +c0 = Crc.crc.fold(M1.t0(bb), 4294967295)
  +r0 = List.reverse.go(&2, U32, M1.t0(bb), aa)
  +body = Png.enc.cat(Png.enc.be(Png.tag.idat()), M1.zb(bb, sum))
  Equal.trans(List<&2, U32>, Png.enc.seal.crc(Png.enc.crc.list(bs2, c0, r0), ie), M1.gg(tt, ll, ie),
    Png.enc.cat(Png.enc.chunk(Png.tag.idat(), M1.zb(bb, sum)), ie),
    Equal.trans(List<&2, U32>, Png.enc.seal.crc(Png.enc.crc.list(bs2, c0, r0), ie), Png.enc.seal.crc(M1.fr(tt,
      4294967295, aa), ie), M1.gg(tt, ll, ie),
      Equal.cong(U32 & List<&2, U32>, List<&2, U32>, pp => Png.enc.seal.crc(pp, ie), Png.enc.crc.list(bs2, c0, r0),
        M1.fr(tt, 4294967295, aa), Equal.trans(U32 & List<&2, U32>, Png.enc.crc.list(bs2, c0, r0), M1.fr(bs2, c0, r0),
        M1.fr(tt, 4294967295, aa), crcl(bs2, c0, r0), fr.app(M1.t0(bb), bs2, 4294967295, aa))),
      tail.eq(ll, tt, ie)),
    Equal.sym(List<&2, U32>, Png.enc.cat(Png.enc.chunk(Png.tag.idat(), M1.zb(bb, sum)), ie), M1.gg(tt, ll, ie),
      Equal.trans(List<&2, U32>, Png.enc.cat(Png.enc.chunk(Png.tag.idat(), M1.zb(bb, sum)), ie), M1.gg(body,
        Png.enc.len(M1.zb(bb, sum), 0), ie), M1.gg(tt, ll, ie), chunk.gg(M1.zb(bb, sum), ie),
        Equal.trans(List<&2, U32>, M1.gg(body, Png.enc.len(M1.zb(bb, sum), 0), ie), M1.gg(tt, Png.enc.len(M1.zb(bb,
            sum), 0), ie),
          M1.gg(tt, ll, ie), Equal.cong(List<&2, U32>, List<&2, U32>, xs => M1.gg(xs, Png.enc.len(M1.zb(bb, sum), 0),
              ie), body,
          tt, body.eq(bb, sum)), Equal.cong(U32, List<&2, U32>, uu => M1.gg(tt, uu, ie), Png.enc.len(M1.zb(bb, sum),
              0), ll,
          Equal.sym(U32, ll, Png.enc.len(M1.zb(bb, sum), 0), hl))))))

# seal.wide up to the Adler field: the CRC run over the IDAT type, the zlib
# header and bs's blocks
def wide.front(
  +raw: List<&2, U32>,
  +nn: U32,
  +sum: U32,
  +aa: List<&2, U32>,
  +ie: List<&2, U32>
) -> {Png.enc.seal.body(Png.enc.crc.list(Png.enc.be(Png.tag.idat()), 4294967295, aa), raw, nn, sum, ie) ==
  Png.enc.seal.adler(M1.fr(M1.t0(M1.bs(raw, True{}, False{}, 0, nn, Png.enc.cap(nn), Png.enc.bf(nn))), 4294967295, aa), sum,  # noqa: S002
  ie) : List<&2, U32>}:
  +bi = Png.enc.be(Png.tag.idat())
  +bb = M1.bs(raw, True{}, False{}, 0, nn, Png.enc.cap(nn), Png.enc.bf(nn))
  +c1 = Crc.crc.fold(bi, 4294967295)
  +a1 = List.reverse.go(&2, U32, bi, aa)
  +c2 = Crc.crc.fold([120, 1], c1)
  +a2 = List.reverse.go(&2, U32, [120, 1], a1)
  Equal.trans(List<&2, U32>, Png.enc.seal.body(Png.enc.crc.list(bi, 4294967295, aa), raw, nn, sum, ie),
    Png.enc.seal.body(M1.fr(bi, 4294967295, aa), raw, nn, sum, ie), Png.enc.seal.adler(M1.fr(M1.t0(bb), 4294967295,
        aa), sum,
    ie),
    Equal.cong(U32 & List<&2, U32>, List<&2, U32>, pp => Png.enc.seal.body(pp, raw, nn, sum, ie),
      Png.enc.crc.list(bi, 4294967295, aa), M1.fr(bi, 4294967295, aa), crcl(bi, 4294967295, aa)),
    Equal.trans(List<&2, U32>, Png.enc.seal.run(Png.enc.crc.list([120, 1], c1, a1), raw, nn, sum, ie),
      Png.enc.seal.run(M1.fr([120, 1], c1, a1), raw, nn, sum, ie), Png.enc.seal.adler(M1.fr(M1.t0(bb), 4294967295, aa),
          sum,
      ie),
      Equal.cong(U32 & List<&2, U32>, List<&2, U32>, pp => Png.enc.seal.run(pp, raw, nn, sum, ie),
        Png.enc.crc.list([120, 1], c1, a1), M1.fr([120, 1], c1, a1), crcl([120, 1], c1, a1)),
      Equal.cong(U32 & List<&2, U32>, List<&2, U32>, pp => Png.enc.seal.adler(pp, sum, ie), Png.enc.pour(raw, True{},
        False{}, 0, nn, Png.enc.cap(nn), Png.enc.bf(nn), c2, a2), M1.fr(M1.t0(bb), 4294967295, aa),
        Equal.trans(U32 & List<&2, U32>, Png.enc.pour(raw, True{}, False{}, 0, nn, Png.enc.cap(nn), Png.enc.bf(nn), c2,
          a2), Png.enc.crc.list(bb, c2, a2), M1.fr(M1.t0(bb), 4294967295, aa), pour.bs(raw, True{}, False{}, 0, nn,
          Png.enc.cap(nn), Png.enc.bf(nn), c2, a2),
          Equal.trans(U32 & List<&2, U32>, Png.enc.crc.list(bb, c2, a2), M1.fr(bb, c2, a2), M1.fr(M1.t0(bb),
              4294967295, aa),
            crcl(bb, c2, a2),
            Equal.trans(U32 & List<&2, U32>, M1.fr(bb, c2, a2), M1.fr(List.append(&2, U32, [120, 1], bb), c1, a1),
              M1.fr(M1.t0(bb), 4294967295, aa), fr.app([120, 1], bb, c1, a1), fr.app(bi, List.append(&2, U32, [120, 1],
              bb), 4294967295, aa)))))))

# seal.wide after the signature and IHDR: the IDAT chunk holding the zlib
# stream of stored blocks of 65535 bytes, then IEND, when its length field is
# right. The IHDR stays out of the statement: its CRC over a symbolic width
# and height costs the checker seconds each time a type holding it is read.
def wide.tail(
  +raw: List<&2, U32>,
  +mx: U32,
  +ie: List<&2, U32>,
  +emx: {mx == 65535 : U32},
  +hn: {U32.to_nat(Png.enc.len(raw, 0)) == List.length(&2, U32, raw) : Nat},
  +hbig: {U32.is_le(Png.enc.len(raw, 0), 65535) == False{} : Bool},
  +hl: {Png.enc.idat.ln(Png.enc.len(raw, 0)) == Png.enc.len(L1.zlib.stored(65535, raw), 0) : U32}
) -> {Png.enc.seal.body(Png.enc.crc.list(Png.enc.be(Png.tag.idat()), 4294967295,
  Png.enc.cat.go(Png.enc.be(Png.enc.idat.ln(Png.enc.len(raw, 0))), [])), raw, Png.enc.len(raw, 0), Inf.adler.of(raw),
  ie) == Png.enc.cat(Png.enc.chunk(Png.tag.idat(), L1.zlib.stored(65535, raw)), ie) : List<&2, U32>}:
  +nn = Png.enc.len(raw, 0)
  +sum = Inf.adler.of(raw)
  +ll = Png.enc.idat.ln(nn)
  +aa = Png.enc.cat.go(Png.enc.be(ll), [])
  +bb = M1.bs(raw, True{}, False{}, 0, nn, Png.enc.cap(nn), Png.enc.bf(nn))
  +bl = Png.enc.blocks(65535, raw)
  +e_b = {sim.blocks(raw, mx, emx, hn, hbig) : {bl == bb : List<&2, U32>}}
  +zz = L1.zlib.stored(65535, raw)
  +hl2 = {Equal.trans(U32, ll, Png.enc.len(zz, 0), Png.enc.len(M1.zb(bb, sum), 0), hl, Equal.cong(List<&2, U32>, U32,
      ys =>
    Png.enc.len(M1.zb(ys, sum), 0), bl, bb, e_b)) : {ll == Png.enc.len(M1.zb(bb, sum), 0) : U32}}
  Equal.trans(List<&2, U32>, Png.enc.seal.body(Png.enc.crc.list(Png.enc.be(Png.tag.idat()), 4294967295, aa), raw, nn,
    sum, ie), Png.enc.seal.adler(M1.fr(M1.t0(bb), 4294967295, aa), sum, ie), Png.enc.cat(Png.enc.chunk(Png.tag.idat(),
        zz),
    ie), wide.front(raw, nn, sum, aa, ie), Equal.trans(List<&2, U32>, Png.enc.seal.adler(M1.fr(M1.t0(bb), 4294967295,
        aa),
    sum, ie), Png.enc.cat(Png.enc.chunk(Png.tag.idat(), M1.zb(bb, sum)), ie), Png.enc.cat(Png.enc.chunk(Png.tag.idat(),
    zz), ie), tail.chunk(bb, sum, ll, ie, hl2), Equal.cong(List<&2, U32>, List<&2, U32>, ys =>
    Png.enc.cat(Png.enc.chunk(Png.tag.idat(), M1.zb(ys, sum)), ie), bb, bl, Equal.sym(List<&2, U32>, bl, bb, e_b))))

# 2 and x + 4 is x + 6
def add.six(+xx: Nat) -> {2n+Nat.add(xx, 4n) == Nat.add(xx, 6n) : Nat}:
  Equal.sym(Nat, Nat.add(xx, 6n), 2n+Nat.add(xx, 4n), Equal.trans(Nat, Nat.add(xx, 6n), 1n+Nat.add(xx, 5n),
    2n+Nat.add(xx, 4n), M1.ras.add_succ(xx, 5n), Equal.cong(Nat, Nat, kk => 1n+kk, Nat.add(xx, 5n), 1n+Nat.add(xx, 4n),
    M1.ras.add_succ(xx, 4n))))

# the zlib stream of stored blocks of 65535 bytes: 6 bytes, the list, and 5
# for each of enc.nblk's block headers
def pfin.zlib.len(
  +raw: List<&2, U32>,
  +mx: U32,
  +emx: {mx == 65535 : U32},
  +hn: {U32.to_nat(Png.enc.len(raw, 0)) == List.length(&2, U32, raw) : Nat},
  +hbig: {U32.is_le(Png.enc.len(raw, 0), 65535) == False{} : Bool}
) -> {List.length(&2, U32, L1.zlib.stored(65535, raw)) == Nat.add(Nat.add(List.length(&2, U32, raw),
  Nat.mul(U32.to_nat(Png.enc.nblk(Png.enc.len(raw, 0))), 5n)), 6n) : Nat}:
  +bl = Png.enc.blocks(65535, raw)
  +be_s = Png.enc.be(Inf.adler.of(raw))
  +xx = Nat.add(List.length(&2, U32, raw), Nat.mul(U32.to_nat(Png.enc.nblk(Png.enc.len(raw, 0))), 5n))
  +ap = List.append(&2, U32, [120, 1], List.append(&2, U32, bl, be_s))
  Equal.trans(Nat, List.length(&2, U32, L1.zlib.stored(65535, raw)), List.length(&2, U32, ap), Nat.add(xx, 6n),
    Equal.cong(List<&2, U32>, Nat, ys => List.length(&2, U32, ys), L1.zlib.stored(65535, raw), ap,
      Equal.trans(List<&2,
    U32>, L1.zlib.stored(65535, raw), List.append(&2, U32, [120, 1], Png.enc.cat(bl, be_s)), ap, M8.cat_app([120, 1],
    Png.enc.cat(bl, be_s)), Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.append(&2, U32, [120, 1], ys),
    Png.enc.cat(bl, be_s), List.append(&2, U32, bl, be_s), M8.cat_app(bl, be_s)))),
    Equal.trans(Nat, List.length(&2, U32, ap), 2n+Nat.add(List.length(&2, U32, bl), 4n), Nat.add(xx, 6n),
      Equal.cong(Nat, Nat, kk => 2n+kk, List.length(&2, U32, List.append(&2, U32, bl, be_s)), Nat.add(List.length(&2,
      U32, bl), 4n), len.app(bl, be_s)),
      Equal.trans(Nat, 2n+Nat.add(List.length(&2, U32, bl), 4n), 2n+Nat.add(xx, 4n), Nat.add(xx, 6n), Equal.cong(Nat,
        Nat, kk => 2n+Nat.add(kk, 4n), List.length(&2, U32, bl), xx, cnt.blocks(raw, mx, emx, hn, hbig)),
        add.six(xx))))

# the IDAT data's length for n raw bytes in k blocks: n + 5 k + 6
def kzn(+nr: Nat, +nn: U32) -> Nat:
  Nat.add(Nat.add(nr, Nat.mul(U32.to_nat(Png.enc.nblk(nn)), 5n)), 6n)

# the IDAT data's length for the raw bytes xs
def kzs(+xs: List<&2, U32>) -> Nat:
  kzn(List.length(&2, U32, xs), Png.enc.len(xs, 0))

# the IDAT length the encoder writes is the zlib stream's, when the stream is
# at most some U32's value long
def idat.len(
  +raw: List<&2, U32>,
  +mx: U32,
  +tu: U32,
  +emx: {mx == 65535 : U32},
  +hn: {U32.to_nat(Png.enc.len(raw, 0)) == List.length(&2, U32, raw) : Nat},
  +hbig: {U32.is_le(Png.enc.len(raw, 0), 65535) == False{} : Bool},
  +h_tu: {Nat.is_le(kzs(raw), U32.to_nat(tu)) == True{} : Bool}
) -> {Png.enc.idat.ln(Png.enc.len(raw, 0)) == Png.enc.len(L1.zlib.stored(65535, raw), 0) : U32}:
  +nn = Png.enc.len(raw, 0)
  +kb = Png.enc.nblk(nn)
  +k5 = Nat.mul(U32.to_nat(kb), 5n)
  +n0 = List.length(&2, U32, raw)
  +xx = Nat.add(n0, k5)
  +tn = U32.to_nat(tu)
  +h_x = {M11.le_add_r(xx, 6n, tn, h_tu) : {Nat.is_le(xx, tn) == True{} : Bool}}
  +h_k = {M10.le_add_l(n0, k5, tn, h_x) : {Nat.is_le(k5, tn) == True{} : Bool}}
  +e_m = {M7.u32_mul_below(kb, 5, tu, h_k) : {U32.to_nat((kb * 5 : U32)) == k5 : Nat}}
  +h_a = {M1.le_rw_l(xx, Nat.add(U32.to_nat(nn), U32.to_nat((kb * 5 : U32))), tn, Equal.trans(Nat, xx,
    Nat.add(U32.to_nat(nn),
    k5), Nat.add(U32.to_nat(nn), U32.to_nat((kb * 5 : U32))), Equal.cong(Nat, Nat, kk => Nat.add(kk, k5), n0,
    U32.to_nat(nn), Equal.sym(Nat, U32.to_nat(nn), n0, hn)), Equal.cong(Nat, Nat, kk => Nat.add(U32.to_nat(nn), kk), k5,
    U32.to_nat((kb * 5 : U32)), Equal.sym(Nat, U32.to_nat((kb * 5 : U32)), k5, e_m))), h_x) :
    {Nat.is_le(Nat.add(U32.to_nat(nn), U32.to_nat((kb * 5 : U32))), tn) == True{} : Bool}}
  +e_a = {Equal.trans(Nat, U32.to_nat((nn + (kb * 5 : U32) : U32)), Nat.add(U32.to_nat(nn),
    U32.to_nat((kb * 5 : U32))), xx,
    M11.u32_add_below(nn, (kb * 5 : U32), tu, h_a), Equal.trans(Nat, Nat.add(U32.to_nat(nn),
        U32.to_nat((kb * 5 : U32))),
    Nat.add(n0, U32.to_nat((kb * 5 : U32))), xx, Equal.cong(Nat, Nat, kk => Nat.add(kk, U32.to_nat((kb * 5 : U32))),
    U32.to_nat(nn), n0, hn), Equal.cong(Nat, Nat, kk => Nat.add(n0, kk), U32.to_nat((kb * 5 : U32)), k5, e_m))) :
    {U32.to_nat((nn + (kb * 5 : U32) : U32)) == xx : Nat}}
  +s1 = (nn + (kb * 5 : U32) : U32)
  +h_6 = {M1.le_rw_l(Nat.add(xx, 6n), Nat.add(U32.to_nat(s1), 6n), tn, Equal.cong(Nat, Nat, kk => Nat.add(kk, 6n), xx,
    U32.to_nat(s1), Equal.sym(Nat, U32.to_nat(s1), xx, e_a)), h_tu) : {Nat.is_le(Nat.add(U32.to_nat(s1), U32.to_nat(6)),
    tn) == True{} : Bool}}
  +e_i = {Equal.trans(Nat, U32.to_nat((s1 + 6 : U32)), Nat.add(U32.to_nat(s1), 6n), Nat.add(xx, 6n),
    M11.u32_add_below(s1, 6, tu, h_6), Equal.cong(Nat, Nat, kk => Nat.add(kk, 6n), U32.to_nat(s1), xx, e_a)) :
    {U32.to_nat(Png.enc.idat.ln(nn)) == Nat.add(xx, 6n) : Nat}}
  +zz = L1.zlib.stored(65535, raw)
  +e_z = {pfin.zlib.len(raw, mx, emx, hn, hbig) : {List.length(&2, U32, zz) == Nat.add(xx, 6n) : Nat}}
  +e_zl = {len.of(zz, tu, M1.le_rw_l(Nat.add(xx, 6n), List.length(&2, U32, zz), tn, Equal.sym(Nat, List.length(&2, U32,
    zz), Nat.add(xx, 6n), e_z), h_tu)) : {U32.to_nat(Png.enc.len(zz, 0)) == List.length(&2, U32, zz) : Nat}}
  M1.u32.same(Png.enc.idat.ln(nn), Png.enc.len(zz, 0), Equal.trans(Nat, U32.to_nat(Png.enc.idat.ln(nn)), Nat.add(xx,
      6n),
    U32.to_nat(Png.enc.len(zz, 0)), e_i, Equal.sym(Nat, U32.to_nat(Png.enc.len(zz, 0)), Nat.add(xx, 6n),
      Equal.trans(Nat,
    U32.to_nat(Png.enc.len(zz, 0)), List.length(&2, U32, zz), Nat.add(xx, 6n), e_zl, e_z))))

# the facts enc.rgb.go's block state carries, nr the raw bytes still to come:
# at a block's start, left counts them; inside a block, need bytes are left
# in it, and left less len counts the bytes after it
def rg.hyp(
  zblock: Bool,
  +zdone: Bool,
  +zspan: Bool,
  +zneed: Bool,
  +nr: Nat,
  +left: U32,
  +len: U32,
  +need: U32,
  +pl: U32,
  +plen: U32,
  +pbf: U32
) -> Type:
  match zblock:
    case True{}:
      {zdone == U32.is_zero(left) : Bool} & {U32.to_nat(left) == nr : Nat}
    case False{}:
      {zdone == False{} : Bool} & ({zspan == True{} : Bool} & ({zneed == U32.is_zero(need) : Bool} &
        ({U32.to_nat(pl) == nr : Nat} & ({Nat.add(U32.to_nat(len), nr) == Nat.add(U32.to_nat(left), U32.to_nat(need)) :
        Nat} & M1.at.edge(need, pl, plen, pbf)))))

# what enc.rgb.go returns: the CRC run over bs's blocks, and Adler-32 of the raw bytes
def rg.val(
  zblock: Bool,
  +rr: List<&2, U32>,
  +cc: U32,
  +acc: List<&2, U32>,
  +aa: U32,
  +bb: U32,
  +left: U32,
  +need: U32,
  +pl: U32,
  +plen: U32,
  +pbf: U32
) -> (U32 & List<&2, U32>) & U32:
  match zblock:
    case True{}:
      (M1.fr(M1.bs(rr, True{}, False{}, 0, left, Png.enc.cap(left), Png.enc.bf(left)), cc, acc), M1.afold(rr, aa, bb))
    case False{}:
      (M1.fr(M1.bs(rr, U32.is_zero(need), U32.is_eq(need, 1), need, pl, plen, pbf), cc, acc), M1.afold(rr, aa, bb))

# no raw bytes left: enc.rgb.go's end is bs's
def nil.r(
  xs: List<&2, U32>,
  +z1: Bool,
  +z2: Bool,
  +r1: U32,
  +l1: U32,
  +n1: U32,
  +f1: U32,
  +cc: U32,
  +acc: List<&2, U32>,
  +aa: U32,
  +bb: U32,
  +hh: {List.length(&2, U32, xs) == 0n : Nat}
) -> {Png.enc.rgb.fin(cc, acc, aa, bb) == (M1.fr(M1.bs(xs, z1, z2, r1, l1, n1, f1), cc, acc), M1.afold(xs, aa,
  bb)) : (U32 & List<&2, U32>) & U32}:
  match xs:
    case Nil{}:
      {==}
    case _x <> t:
      Empty.absurd({Png.enc.rgb.fin(cc, acc, aa, bb) == (M1.fr(M1.bs(_x <> t, z1, z2, r1, l1, n1, f1), cc, acc),
        M1.afold(_x <> t,
        aa, bb)) : (U32 & List<&2, U32>) & U32}, M1.zero_succ(List.length(&2, U32, t), Equal.sym(Nat,
          1n+List.length(&2,
        U32, t), 0n, hh)))

# the walk's hypothesis for the bytes after xb, with the fuel and counts
def rg.byte.ty(
  -pp: Nat,
  -xb: U32,
  -r2: List<&2, U32>,
  -need: U32,
  -pl: U32,
  -cc: U32,
  -acc: List<&2, U32>,
  -aa: U32,
  -bb: U32,
  -left: U32,
  -len: U32,
  -kk: Nat,
  -xn: Nat,
  -gg: (U32 & List<&2, U32>) & U32
) -> Type:
  @xx: U32 -> @yy: U32 -> M1.at.edge((need - 1 : U32), (pl - 1 : U32), xx, yy) -> {Nat.add(U32.to_nat((need - 1 : U32)),
    xn) == List.length(&2, U32, r2) : Nat} -> {Nat.is_le(Nat.add(Nat.add(List.length(&2, U32, r2), 1n),
    Nat.double(kk)), 1n+pp) == True{} : Bool} -> {U32.to_nat((pl - 1 : U32)) == List.length(&2, U32, r2) : Nat} ->
    {Nat.add(U32.to_nat(len), List.length(&2, U32, r2)) == Nat.add(U32.to_nat(left), U32.to_nat((need - 1 : U32))) :
    Nat} -> {gg == (M1.fr(M1.bs(r2, U32.is_zero((need - 1 : U32)), U32.is_eq((need - 1 : U32), 1), (need - 1 : U32),
        (pl - 1 :
    U32), xx, yy), Crc.crc.byte(cc, xb), xb <> acc), M1.afold(r2, Png.enc.add(aa, xb), Png.enc.add(bb, Png.enc.add(aa,
    xb)))) : (U32 & List<&2, U32>) & U32}

# a raw byte in a block, from the rg state: the facts for the state after it,
# then step, then rg.val read with the byte in front
def rg.byte(
  +pp: Nat,
  +xb: U32,
  +rr: List<&2, U32>,
  +r2: List<&2, U32>,
  +need: U32,
  +pl: U32,
  +plen: U32,
  +pbf: U32,
  +cc: U32,
  +acc: List<&2, U32>,
  +aa: U32,
  +bb: U32,
  +left: U32,
  +len: U32,
  +kk: Nat,
  +xn: Nat,
  -gg: (U32 & List<&2, U32>) & U32,
  +e_r: {rr == xb <> r2 : List<&2, U32>},
  +e_zn: {False{} == U32.is_zero(need) : Bool},
  +hx: {Nat.add(U32.to_nat(need), xn) == List.length(&2, U32, rr) : Nat},
  +hw: {Nat.is_le(Nat.add(Nat.add(List.length(&2, U32, rr), 1n), Nat.double(kk)), 2n+pp) == True{} : Bool},
  +e_pl: {U32.to_nat(pl) == List.length(&2, U32, rr) : Nat},
  +e_ll: {Nat.add(U32.to_nat(len), List.length(&2, U32, rr)) == Nat.add(U32.to_nat(left), U32.to_nat(need)) : Nat},
  ih: rg.byte.ty(pp, xb, r2, need, pl, cc, acc, aa, bb, left, len, kk, xn, gg)
) -> {gg == rg.val(False{}, rr, cc, acc, aa, bb, left, need, pl, plen, pbf) : (U32 & List<&2, U32>) & U32}:
  +n1 = (need - 1 : U32)
  +nr = List.length(&2, U32, r2)
  +nz = {Equal.sym(Bool, False{}, U32.is_zero(need), e_zn) : {U32.is_zero(need) == False{} : Bool}}
  +e_n = {M1.u32_dec(need, nz) : {U32.to_nat(need) == 1n+U32.to_nat(n1) : Nat}}
  +e_len = {Equal.cong(List<&2, U32>, Nat, ys => List.length(&2, U32, ys), rr, xb <> r2, e_r) : {List.length(&2, U32,
    rr) == 1n+nr : Nat}}
  +hx2 = {M1.succ_inj(Nat.add(U32.to_nat(n1), xn), nr, Equal.trans(Nat, 1n+Nat.add(U32.to_nat(n1), xn),
    Nat.add(U32.to_nat(need), xn), 1n+nr, Equal.cong(Nat, Nat, kz => Nat.add(kz, xn), 1n+U32.to_nat(n1),
    U32.to_nat(need), Equal.sym(Nat, U32.to_nat(need), 1n+U32.to_nat(n1),
      e_n)), Equal.trans(Nat, Nat.add(U32.to_nat(need),
    xn), List.length(&2, U32, rr), 1n+nr, hx, e_len))) : {Nat.add(U32.to_nat(n1), xn) == nr : Nat}}
  +hw2 = {Equal.trans(Bool, Nat.is_le(Nat.add(Nat.add(1n+nr, 1n), Nat.double(kk)), 2n+pp), Nat.is_le(Nat.add(Nat.add(
    List.length(&2, U32, rr), 1n), Nat.double(kk)), 2n+pp), True{}, Equal.cong(Nat, Bool, kz =>
    Nat.is_le(Nat.add(Nat.add(kz, 1n), Nat.double(kk)), 2n+pp), 1n+nr, List.length(&2, U32, rr), Equal.sym(Nat,
    List.length(&2, U32, rr), 1n+nr, e_len)), hw) : {Nat.is_le(Nat.add(Nat.add(nr, 1n), Nat.double(kk)), 1n+pp) ==
    True{} : Bool}}
  +epl2 = {M1.u32_pred(pl, nr, Equal.trans(Nat, U32.to_nat(pl), List.length(&2, U32, rr), 1n+nr, e_pl, e_len)) :
    {U32.to_nat((pl - 1 : U32)) == nr : Nat}}
  +ell2 = {M1.succ_inj(Nat.add(U32.to_nat(len), nr), Nat.add(U32.to_nat(left), U32.to_nat(n1)), Equal.trans(Nat,
    1n+Nat.add(U32.to_nat(len), nr), Nat.add(U32.to_nat(len), 1n+nr), 1n+Nat.add(U32.to_nat(left), U32.to_nat(n1)),
    Equal.sym(Nat, Nat.add(U32.to_nat(len), 1n+nr), 1n+Nat.add(U32.to_nat(len), nr), M1.ras.add_succ(U32.to_nat(len),
        nr)),
    Equal.trans(Nat, Nat.add(U32.to_nat(len), 1n+nr), Nat.add(U32.to_nat(left), 1n+U32.to_nat(n1)),
    1n+Nat.add(U32.to_nat(left), U32.to_nat(n1)), Equal.trans(Nat, Nat.add(U32.to_nat(len), 1n+nr),
    Nat.add(U32.to_nat(len), List.length(&2, U32, rr)), Nat.add(U32.to_nat(left), 1n+U32.to_nat(n1)), Equal.cong(Nat,
      Nat,
    kz => Nat.add(U32.to_nat(len), kz), 1n+nr, List.length(&2, U32, rr), Equal.sym(Nat, List.length(&2, U32, rr), 1n+nr,
    e_len)), Equal.trans(Nat, Nat.add(U32.to_nat(len), List.length(&2, U32, rr)), Nat.add(U32.to_nat(left),
    U32.to_nat(need)), Nat.add(U32.to_nat(left), 1n+U32.to_nat(n1)), e_ll, Equal.cong(Nat, Nat, kz =>
    Nat.add(U32.to_nat(left), kz), U32.to_nat(need), 1n+U32.to_nat(n1), e_n))), M1.ras.add_succ(U32.to_nat(left),
    U32.to_nat(n1))))) : {Nat.add(U32.to_nat(len), nr) == Nat.add(U32.to_nat(left), U32.to_nat(n1)) : Nat}}
  Equal.trans((U32 & List<&2, U32>) & U32, gg, (M1.fr(M1.bs(xb <> r2, False{}, U32.is_eq(need, 1), need, pl, plen,
      pbf), cc,
    acc), M1.afold(xb <> r2, aa, bb)), rg.val(False{}, rr, cc, acc, aa, bb, left, need, pl, plen, pbf),
    M1.step(U32.is_eq(need, 1), xb, r2, need, pl, plen, pbf, cc, acc, aa, bb, gg, {==}, nz, xx => yy => ee => ih(xx, yy,
      ee, hx2, hw2, epl2, ell2)),
    Equal.sym((U32 & List<&2, U32>) & U32, rg.val(False{}, rr, cc, acc, aa, bb, left, need, pl, plen, pbf),
      (M1.fr(M1.bs(xb <> r2, False{}, U32.is_eq(need, 1), need, pl, plen, pbf), cc, acc), M1.afold(xb <> r2, aa, bb)),
      Equal.trans((U32 & List<&2, U32>) & U32, rg.val(False{}, rr, cc, acc, aa, bb, left, need, pl, plen, pbf),
        (M1.fr(M1.bs(rr, False{}, U32.is_eq(need, 1), need, pl, plen, pbf), cc, acc), M1.afold(rr, aa, bb)),
        (M1.fr(M1.bs(xb <> r2, False{}, U32.is_eq(need, 1), need, pl, plen, pbf), cc, acc), M1.afold(xb <> r2, aa, bb)),
        Equal.cong(Bool, (U32 & List<&2, U32>) & U32, zb => (M1.fr(M1.bs(rr, zb, U32.is_eq(need, 1), need, pl, plen,
            pbf),
          cc, acc), M1.afold(rr, aa, bb)), U32.is_zero(need), False{}, nz),
        Equal.cong(List<&2, U32>, (U32 & List<&2, U32>) & U32, ys => (M1.fr(M1.bs(ys, False{}, U32.is_eq(need, 1),
            need, pl,
          plen, pbf), cc, acc), M1.afold(ys, aa, bb)), rr, xb <> r2, e_r))))

# the five header bytes bs writes at a block's start from left bytes
def hd5(+left: U32) -> List<&2, U32>:
  +len = Png.enc.cap(left)
  +nlen = (len .^. 65535 : U32)
  [Png.enc.bf(left), Png.enc.byte(len), Png.enc.hi(len), Png.enc.byte(nlen), Png.enc.hi(nlen)]

# a new block, split as enc.rgb.go writes it: the header, then the bytes with
# the block's whole length in hand, once whether that length is 1 is named
def spl.at(
  z1: Bool,
  +hd: U32,
  +tl: List<&2, U32>,
  +left: U32,
  +ez1: {U32.is_eq(Png.enc.cap(left), 1) == z1 : Bool},
  +nzc: {U32.is_zero(Png.enc.cap(left)) == False{} : Bool}
) -> {open.bs(hd, tl, (left - 1 : U32), Png.enc.cap(left), Png.enc.bf(left)) == List.append(&2, U32, hd5(left),
  M1.bs(hd <> tl, False{}, U32.is_eq(Png.enc.cap(left), 1), Png.enc.cap(left), left, Png.enc.cap((left - 1 : U32)),
  Png.enc.bf((left - 1 : U32)))) : List<&2, U32>}:
  match z1:
    case True{}:
      +cp = Png.enc.cap(left)
      +l1 = (left - 1 : U32)
      +e1 = {M1.one.val(cp, Equal.sym(Bool, U32.is_eq(cp, 1), True{}, ez1)) : {U32.to_nat(cp) == 1n : Nat}}
      +e0 = {M1.u32.same((cp - 1 : U32), 0, M1.u32_pred(cp, 0n, e1)) : {(cp - 1 : U32) == 0 : U32}}
      %Equal.sym(Bool, U32.is_eq(cp, 1), True{}, ez1) : {open.bs(hd, tl, l1, cp, Png.enc.bf(left)) == List.append(&2,
        U32,
        hd5(left), M1.bs(hd <> tl, False{}, _, cp, left, Png.enc.cap(l1), Png.enc.bf(l1))) : List<&2, U32>}
      Equal.cong(U32, List<&2, U32>, uu => List.append(&2, U32, hd5(left), hd <> M1.bs(tl, U32.is_zero(uu),
          U32.is_eq(uu,
        1),
        uu, l1, Png.enc.cap(l1), Png.enc.bf(l1))), (cp - 1 : U32), 0, e0)
    case False{}:
      +cp = Png.enc.cap(left)
      +l1 = (left - 1 : U32)
      +nz1 = {M1.two(cp, Equal.sym(Bool, U32.is_zero(cp), False{}, nzc), Equal.sym(Bool, U32.is_eq(cp, 1), False{},
          ez1)) :
        {U32.is_zero((cp - 1 : U32)) == False{} : Bool}}
      %Equal.sym(Bool, U32.is_eq(cp, 1), False{}, ez1) : {open.bs(hd, tl, l1, cp, Png.enc.bf(left)) == List.append(&2,
        U32,
        hd5(left), M1.bs(hd <> tl, False{}, _, cp, left, Png.enc.cap(l1), Png.enc.bf(l1))) : List<&2, U32>}
      Equal.cong(Bool, List<&2, U32>, zb => List.append(&2, U32, hd5(left), hd <> M1.bs(tl, zb,
          U32.is_eq((cp - 1 : U32),
        1),
        (cp - 1 : U32), l1, Png.enc.cap(l1), Png.enc.bf(l1))), U32.is_zero((cp - 1 : U32)), False{}, nz1)

# a block's start with bytes left: the header, then the bytes with the block's
# whole length in hand
def spl(
  xs: List<&2, U32>,
  +left: U32,
  +hn: {U32.to_nat(left) == List.length(&2, U32, xs) : Nat},
  +nzl: {U32.is_zero(left) == False{} : Bool},
  +nzc: {U32.is_zero(Png.enc.cap(left)) == False{} : Bool}
) -> {M1.bs(xs, True{}, False{}, 0, left, Png.enc.cap(left), Png.enc.bf(left)) == List.append(&2, U32, hd5(left),
    M1.bs(xs,
  False{}, U32.is_eq(Png.enc.cap(left), 1), Png.enc.cap(left), left, Png.enc.cap((left - 1 : U32)),
  Png.enc.bf((left - 1 : U32)))) : List<&2, U32>}:
  match xs:
    case Nil{}:
      Empty.absurd({M1.bs([], True{}, False{}, 0, left, Png.enc.cap(left), Png.enc.bf(left)) == List.append(&2, U32,
        hd5(left), M1.bs([], False{}, U32.is_eq(Png.enc.cap(left), 1), Png.enc.cap(left), left, Png.enc.cap((left - 1 :
        U32)), Png.enc.bf((left - 1 : U32)))) : List<&2, U32>}, M1.false_true(Equal.trans(Bool, False{},
        U32.is_zero(left), True{}, Equal.sym(Bool, U32.is_zero(left), False{}, nzl), zero.is(left, hn))))
    case +h <> +t:
      spl.at(U32.is_eq(Png.enc.cap(left), 1), h, t, left, {==}, nzc)

# the pair at.edge gives, used to rewrite bs's length and BFINAL
def n0.pe(
  +rr: List<&2, U32>,
  +pl: U32,
  +plen: U32,
  +pbf: U32,
  pe: {plen == Png.enc.cap(pl) : U32} & {pbf == Png.enc.bf(pl) : U32}
) -> {M1.bs(rr, True{}, False{}, 0, pl, plen, pbf) == M1.bs(rr, True{}, False{}, 0, pl, Png.enc.cap(pl),
  Png.enc.bf(pl)) : List<&2, U32>}:
  (+e_l, +e_b) = pe
  Equal.trans(List<&2, U32>, M1.bs(rr, True{}, False{}, 0, pl, plen, pbf), M1.bs(rr, True{}, False{}, 0, pl,
      Png.enc.cap(pl),
    pbf), M1.bs(rr, True{}, False{}, 0, pl, Png.enc.cap(pl), Png.enc.bf(pl)), Equal.cong(U32, List<&2, U32>,
        uu => M1.bs(rr,
    True{}, False{}, 0, pl, uu, pbf), plen, Png.enc.cap(pl), e_l), Equal.cong(U32, List<&2, U32>, uu => M1.bs(rr,
        True{},
    False{}, 0, pl, Png.enc.cap(pl), uu), pbf, Png.enc.bf(pl), e_b))

# a block's end in enc.rgb.go's state is a block's start in bs's
def n0.bs(
  +rr: List<&2, U32>,
  +need: U32,
  +pl: U32,
  +plen: U32,
  +pbf: U32,
  +left2: U32,
  +ez: {True{} == U32.is_zero(need) : Bool},
  +e_pl: {U32.to_nat(pl) == List.length(&2, U32, rr) : Nat},
  +e_l2: {U32.to_nat(left2) == List.length(&2, U32, rr) : Nat},
  hb: M1.at.edge(need, pl, plen, pbf)
) -> {M1.bs(rr, U32.is_zero(need), U32.is_eq(need, 1), need, pl, plen, pbf) == M1.bs(rr, True{}, False{}, 0, left2,
  Png.enc.cap(left2), Png.enc.bf(left2)) : List<&2, U32>}:
  +e0 = {M1.u32.same(need, 0, M1.zero.val(need, ez)) : {need == 0 : U32}}
  +e_p = {M1.u32.same(pl, left2, Equal.trans(Nat, U32.to_nat(pl), List.length(&2, U32, rr), U32.to_nat(left2), e_pl,
    Equal.sym(Nat, U32.to_nat(left2), List.length(&2, U32, rr), e_l2))) : {pl == left2 : U32}}
  Equal.trans(List<&2, U32>, M1.bs(rr, U32.is_zero(need), U32.is_eq(need, 1), need, pl, plen, pbf), M1.bs(rr, True{},
      False{},
    0, pl, plen, pbf), M1.bs(rr, True{}, False{}, 0, left2, Png.enc.cap(left2), Png.enc.bf(left2)),
    Equal.cong(U32, List<&2, U32>, uu => M1.bs(rr, U32.is_zero(uu), U32.is_eq(uu, 1), uu, pl, plen, pbf), need, 0, e0),
    Equal.trans(List<&2, U32>, M1.bs(rr, True{}, False{}, 0, pl, plen, pbf), M1.bs(rr, True{}, False{}, 0, pl,
      Png.enc.cap(pl),
      Png.enc.bf(pl)), M1.bs(rr, True{}, False{}, 0, left2, Png.enc.cap(left2), Png.enc.bf(left2)), n0.pe(rr, pl, plen,
        pbf,
      hb(Equal.sym(Bool, True{}, U32.is_zero(need), ez))), Equal.cong(U32, List<&2, U32>, uu => M1.bs(rr, True{},
          False{},
      0, uu, Png.enc.cap(uu), Png.enc.bf(uu)), pl, left2, e_p)))

# out of fuel at a block's start: no raw bytes are left
def z0.m1(
  kk: Nat,
  +xn: Nat,
  +nr: Nat,
  +mn: Nat,
  +hx: {xn == nr : Nat},
  hk: M1.kok(xn, kk, mn),
  +hw: {Nat.is_le(Nat.add(Nat.add(nr, 0n), Nat.double(kk)), 1n) == True{} : Bool}
) -> {nr == 0n : Nat}:
  match kk:
    case 0n:
      Equal.trans(Nat, nr, xn, 0n, Equal.sym(Nat, xn, nr, hx), hk)
    case 1n+kp:
      Empty.absurd({nr == 0n : Nat}, M1.false_true(M10.le_add_l(Nat.add(nr, 0n), 2n+Nat.double(kp), 1n, hw)))

# out of fuel inside a block: no raw bytes are left
def z0.s2(+nr: Nat, +dk: Nat, +hw: {Nat.is_le(Nat.add(Nat.add(nr, 1n), dk), 1n) == True{} : Bool}) -> {nr == 0n : Nat}:
  +h1 = {M11.le_add_r(Nat.add(nr, 1n), dk, 1n, hw) : {Nat.is_le(Nat.add(nr, 1n), 1n) == True{} : Bool}}
  +h2 = {M1.le_rw_l(Nat.add(nr, 1n), 1n+Nat.add(nr, 0n), 1n, M1.ras.add_succ(nr, 0n), h1) : {Nat.is_le(Nat.add(nr, 0n),
      0n) ==
    True{} : Bool}}
  Equal.trans(Nat, nr, Nat.add(nr, 0n), 0n, Equal.sym(Nat, Nat.add(nr, 0n), nr, M1.ras.add_zero(nr)),
      le.zero(Nat.add(nr,
    0n),
    h2))

# the fuel after a block header: one step fewer, one block fewer, one more to close it
def hw.head(
  +nr: Nat,
  +dk: Nat,
  +pp: Nat,
  +hw: {Nat.is_le(Nat.add(Nat.add(nr, 0n), 2n+dk), 2n+pp) == True{} : Bool}
) -> {Nat.is_le(Nat.add(Nat.add(nr, 1n), dk), 1n+pp) == True{} : Bool}:
  +ee = {Equal.trans(Nat, Nat.add(Nat.add(nr, 0n), 2n+dk), Nat.add(nr, 2n+dk), 1n+Nat.add(Nat.add(nr, 1n), dk),
    Equal.cong(Nat, Nat, kz => Nat.add(kz, 2n+dk), Nat.add(nr, 0n), nr, M1.ras.add_zero(nr)), Equal.trans(Nat,
        Nat.add(nr,
    2n+dk), 1n+Nat.add(nr, 1n+dk), 1n+Nat.add(Nat.add(nr, 1n), dk), M1.ras.add_succ(nr, 1n+dk), Equal.cong(Nat, Nat,
        kz =>
    1n+kz, Nat.add(nr, 1n+dk), Nat.add(Nat.add(nr, 1n), dk), Equal.sym(Nat, Nat.add(Nat.add(nr, 1n), dk), Nat.add(nr,
    1n+dk), M1.ras.add_assoc(nr, 1n, dk))))) : {Nat.add(Nat.add(nr, 0n), 2n+dk) == 1n+Nat.add(Nat.add(nr, 1n),
        dk) : Nat}}
  M1.le_rw_l(Nat.add(Nat.add(nr, 0n), 2n+dk), 1n+Nat.add(Nat.add(nr, 1n), dk), 2n+pp, ee, hw)

# the fuel at a block's end: the step that closes it
def hw.end(
  +nr: Nat,
  +dk: Nat,
  +pp: Nat,
  +hw: {Nat.is_le(Nat.add(Nat.add(nr, 1n), dk), 2n+pp) == True{} : Bool}
) -> {Nat.is_le(Nat.add(Nat.add(nr, 0n), dk), 1n+pp) == True{} : Bool}:
  M1.le_rw_l(Nat.add(Nat.add(nr, 1n), dk), 1n+Nat.add(Nat.add(nr, 0n), dk), 2n+pp, Equal.cong(Nat, Nat,
      kz => Nat.add(kz,
    dk), Nat.add(nr, 1n), 1n+Nat.add(nr, 0n), M1.ras.add_succ(nr, 0n)), hw)

# a sum that is 0 has a left part 0
def add.zero.l(aa: Nat, +bb: Nat, +hh: {Nat.add(aa, bb) == 0n : Nat}) -> {aa == 0n : Nat}:
  match aa:
    case 0n:
      {==}
    case 1n+pp:
      Empty.absurd({1n+pp == 0n : Nat}, M1.zero_succ(Nat.add(pp, bb), Equal.sym(Nat, 1n+Nat.add(pp, bb), 0n, hh)))

# a byte is due in the block, so the raw bytes are not gone
def need.nil(
  +need: U32,
  +xn: Nat,
  +e_zn: {False{} == U32.is_zero(need) : Bool},
  +hx: {Nat.add(U32.to_nat(need), xn) == 0n : Nat}
) -> Empty:
  M1.false_true(Equal.trans(Bool, False{}, U32.is_zero(need), True{}, e_zn, zero.is(need, add.zero.l(U32.to_nat(need),
    xn, hx))))

# the filter byte: 0, then the row's samples
def cur.filt(
  +sv: U32,
  +tl: List<&2, U32>,
  +row: U32,
  +wp: Nat,
  +er: {U32.to_nat(row) == 1n+wp : Nat}
) -> {M1.sc(sv <> tl, 0n, 1n+wp, True{}) == 0 <> M1.sc(sv <> tl, U32.to_nat(row), 1n+wp, True{}) : List<&2, U32>}:
  Equal.cong(Nat, List<&2, U32>, kz => 0 <> M1.sc(sv <> tl, kz, 1n+wp, True{}), 1n+wp, U32.to_nat(row), Equal.sym(Nat,
    U32.to_nat(row), 1n+wp, er))

# a red byte: the sample's red, then its green and blue and the rest of the row
def cur.red(
  +sv: U32,
  +tl: List<&2, U32>,
  +row: U32,
  +wn: Nat,
  +hrow: {U32.is_zero(row) == False{} : Bool}
) -> {M1.sc(sv <> tl, U32.to_nat(row), wn, True{}) == Png.enc.r(sv) <> Png.enc.g(sv) <> Png.enc.b(sv) <> M1.sc(tl,
  Png.enc.pred(U32.to_nat(row)), wn, True{}) : List<&2, U32>}:
  +r1 = U32.to_nat((row - 1 : U32))
  +er = {M1.u32_dec(row, hrow) : {U32.to_nat(row) == 1n+r1 : Nat}}
  Equal.trans(List<&2, U32>, M1.sc(sv <> tl, U32.to_nat(row), wn, True{}), M1.sc(sv <> tl, 1n+r1, wn, True{}),
    Png.enc.r(sv)
    <> Png.enc.g(sv) <> Png.enc.b(sv) <> M1.sc(tl, Png.enc.pred(U32.to_nat(row)), wn, True{}),
    Equal.cong(Nat, List<&2, U32>, kz => M1.sc(sv <> tl, kz, wn, True{}), U32.to_nat(row), 1n+r1, er),
    Equal.cong(Nat, List<&2, U32>, kz => Png.enc.r(sv) <> Png.enc.g(sv) <> Png.enc.b(sv) <> M1.sc(tl, Png.enc.pred(kz),
      wn,
      True{}), 1n+r1, U32.to_nat(row), Equal.sym(Nat, U32.to_nat(row), 1n+r1, er)))

# a row's last blue byte: the next row starts with its filter byte
def cur.last(
  +col: U32,
  +px: List<&2, U32>,
  +row: U32,
  +wn: Nat,
  +e1: {True{} == U32.is_eq(row, 1) : Bool}
) -> {Png.enc.b(col) <> M1.sc(px, Png.enc.pred(U32.to_nat(row)), wn, True{}) == Png.enc.b(col) <> M1.sc(px, 0n, wn,
  True{}) : List<&2, U32>}:
  Equal.cong(Nat, List<&2, U32>, kz => Png.enc.b(col) <> M1.sc(px, Png.enc.pred(kz), wn, True{}), U32.to_nat(row), 1n,
    M1.one.val(row, e1))

# a blue byte inside a row: the next sample's red comes next
def cur.blue(
  +col: U32,
  +px: List<&2, U32>,
  +row: U32,
  +wn: Nat,
  +hrow: {U32.is_zero(row) == False{} : Bool}
) -> {Png.enc.b(col) <> M1.sc(px, Png.enc.pred(U32.to_nat(row)), wn, True{}) == Png.enc.b(col) <> M1.sc(px,
  U32.to_nat((row - 1 : U32)), wn, True{}) : List<&2, U32>}:
  Equal.cong(Nat, List<&2, U32>, kz => Png.enc.b(col) <> M1.sc(px, Png.enc.pred(kz), wn, True{}), U32.to_nat(row),
    1n+U32.to_nat((row - 1 : U32)), M1.u32_dec(row, hrow))

# at a filter byte or a blue channel, the next is not a red or green one, and zlast says the row's last pixel
def rg.hbl(filt: Bool, zred: Bool, zgrn: Bool, zlast: Bool, +row: U32) -> Type:
  {filt == False{} : Bool} -> {zred == False{} : Bool} -> {zgrn == False{} : Bool} -> {zlast == U32.is_eq(row, 1) :
    Bool}

# how many bytes are left from the cursor
def curl(filt: Bool, zred: Bool, zgrn: Bool, px: List<&2, U32>, +col: U32, +row: U32, +wp: Nat) -> Nat:
  List.length(&2, U32, M3.cur(filt, zred, zgrn, px, col, row, 1n+wp))

# the steps the walk takes from the cursor: the bytes, one more when a block is open, and two per block
def rgw(
  filt: Bool,
  zred: Bool,
  zgrn: Bool,
  px: List<&2, U32>,
  +col: U32,
  +row: U32,
  +wp: Nat,
  zblock: Bool,
  +kk: Nat
) -> Nat:
  Nat.add(Nat.add(curl(filt, zred, zgrn, px, col, row, wp), M1.bit(Bool.not(zblock))), Nat.double(kk))

# enc.rgb.go writes bs's blocks of the raw bytes its cursor walks, with their
# CRC run, and the Adler-32 of those bytes, while its fuel covers a step per
# raw byte and two per block (the header, and the step that closes it)
def rg(
  fuel: Nat,
  +zblock: Bool,
  +zdone: Bool,
  +zspan: Bool,
  +zneed: Bool,
  +filt: Bool,
  +zred: Bool,
  +zgrn: Bool,
  +zlast: Bool,
  +px: List<&2, U32>,
  +col: U32,
  +row: U32,
  +ww: U32,
  +need: U32,
  +cc: U32,
  +acc: List<&2, U32>,
  +aa: U32,
  +bb: U32,
  +left: U32,
  +len: U32,
  +pl: U32,
  +plen: U32,
  +pbf: U32,
  +kk: Nat,
  +xn: Nat,
  +wp: Nat,
  +mx: U32,
  +emx: {mx == 65535 : U32},
  +ew: {U32.to_nat(ww) == 1n+wp : Nat},
  +hrow: {U32.is_zero(row) == False{} : Bool},
  hfw: {filt == True{} : Bool} -> {row == ww : U32},
  hbl: rg.hbl(filt, zred, zgrn, zlast, row),
  +hx: {Nat.add(U32.to_nat(M10.rm(zblock, need)), xn) == curl(filt, zred, zgrn, px, col, row, wp) : Nat},
  hk: M1.kok(xn, kk, U32.to_nat(mx)),
  +hw: {Nat.is_le(rgw(filt, zred, zgrn, px, col, row, wp, zblock, kk), 1n+fuel) == True{} : Bool},
  hb: rg.hyp(zblock, zdone, zspan, zneed, curl(filt, zred, zgrn, px, col, row, wp), left, len, need, pl, plen, pbf)
) -> {Png.enc.rgb.go(fuel, zblock, zdone, zspan, zneed, filt, zred, zgrn, zlast, px, col, row, ww, need, cc, acc, aa,
  bb, left, len) == rg.val(zblock, M3.cur(filt, zred, zgrn, px, col, row, 1n+wp), cc, acc, aa, bb, left, need, pl, plen,
  pbf) : (U32 & List<&2, U32>) & U32}:
  match fuel:
    case 0n:
      match zblock:
        case True{}:
          +rr = M3.cur(filt, zred, zgrn, px, col, row, 1n+wp)
          nil.r(rr, True{}, False{}, 0, left, Png.enc.cap(left), Png.enc.bf(left), cc, acc, aa, bb, z0.m1(kk, xn,
            List.length(&2, U32, rr), U32.to_nat(mx), hx, hk, hw))
        case False{}:
          +rr = M3.cur(filt, zred, zgrn, px, col, row, 1n+wp)
          nil.r(rr, U32.is_zero(need), U32.is_eq(need, 1), need, pl, plen, pbf, cc, acc, aa, bb,
            z0.s2(List.length(&2, U32, rr), Nat.double(kk), hw))
    case 1n+(+pp):
      match zblock:
        case True{}:
          match zdone:
            case True{}:
              (e_zd, e_l) = hb
              +rr = M3.cur(filt, zred, zgrn, px, col, row, 1n+wp)
              nil.r(rr, True{}, False{}, 0, left, Png.enc.cap(left), Png.enc.bf(left), cc, acc, aa, bb,
                Equal.trans(Nat, List.length(&2, U32, rr), U32.to_nat(left), 0n, Equal.sym(Nat, U32.to_nat(left),
                List.length(&2, U32, rr), e_l), M1.zero.val(left, e_zd)))
            case False{}:
              match kk:
                case 0n:
                  (e_zd, e_l) = hb
                  +rr = M3.cur(filt, zred, zgrn, px, col, row, 1n+wp)
                  +e_r0 = {Equal.trans(Nat, U32.to_nat(left), List.length(&2, U32, rr), 0n, e_l, Equal.trans(Nat,
                    List.length(&2, U32, rr), xn, 0n, Equal.sym(Nat, xn, List.length(&2, U32, rr), hx), hk)) :
                    {U32.to_nat(left) == 0n : Nat}}
                  Empty.absurd({Png.enc.rgb.go(1n+pp, True{}, False{}, zspan, zneed, filt, zred, zgrn, zlast, px, col,
                    row, ww, need, cc, acc, aa, bb, left, len) == rg.val(True{}, rr, cc, acc, aa, bb, left, need, pl,
                    plen, pbf) : (U32 & List<&2, U32>) & U32}, M1.false_true(Equal.trans(Bool, False{},
                    U32.is_zero(left), True{}, e_zd, zero.is(left, e_r0))))
                case 1n+(+kp):
                  match hk hb:
                    case Tuple{h_lt, h_le} Tuple{e_zd, +e_l}:
                      +rr = M3.cur(filt, zred, zgrn, px, col, row, 1n+wp)
                      +nr = List.length(&2, U32, rr)
                      +mn = U32.to_nat(mx)
                      +l1 = (left - 1 : U32)
                      +nt = U32.to_nat(l1)
                      +nzl = {Equal.sym(Bool, False{}, U32.is_zero(left), e_zd) : {U32.is_zero(left) == False{} : Bool}}
                      +e_lt = {M1.u32_dec(left, nzl) : {U32.to_nat(left) == 1n+nt : Nat}}
                      +e_R = {Equal.trans(Nat, nr, U32.to_nat(left), 1n+nt, Equal.sym(Nat, U32.to_nat(left), nr, e_l),
                        e_lt) : {nr == 1n+nt : Nat}}
                      +zz = U32.is_le(left, 65535)
                      +cp = Png.enc.cap(left)
                      +cm = capm(zz, left, mx)
                      +c1 = (cp - 1 : U32)
                      +nzm = {mx.nz(mx, emx) : {U32.is_zero(mx) == False{} : Bool}}
                      +ezm = {le.mx(left, mx, emx) : {U32.is_le(left, mx) == zz : Bool}}
                      +e_cm = {cap.m(zz, left, mx, emx) : {cp == cm : U32}}
                      +nz_cp = {Equal.trans(Bool, U32.is_zero(cp), U32.is_zero(cm), False{}, Equal.cong(U32, Bool, uu =>
                        U32.is_zero(uu), cp, cm, e_cm), cap.nz(zz, left, mx, nt, nzm, e_lt)) : {U32.is_zero(cp) ==
                        False{} : Bool}}
                      +e_cp = {M1.u32_dec(cp, nz_cp) : {U32.to_nat(cp) == 1n+U32.to_nat(c1) : Nat}}
                      +e_c = {Equal.cong(U32, Nat, uu => U32.to_nat((uu - 1 : U32)), cp, cm, e_cm) : {U32.to_nat(c1) ==
                        U32.to_nat((cm - 1 : U32)) : Nat}}
                      +h_c = {M1.le_rw_l(U32.to_nat((cm - 1 : U32)), U32.to_nat(c1), nt, Equal.sym(Nat, U32.to_nat(c1),
                        U32.to_nat((cm - 1 : U32)), e_c), ks.le(zz, left, mx, nt, nzm, ezm, e_lt)) :
                        {Nat.is_le(U32.to_nat(c1), nt) == True{} : Bool}}
                      +x2 = Nat.sub(nt, U32.to_nat(c1))
                      +hx2 = {Equal.trans(Nat, Nat.add(U32.to_nat(cp), x2), 1n+Nat.add(U32.to_nat(c1), x2), nr,
                        Equal.cong(Nat, Nat, kz => Nat.add(kz, x2), U32.to_nat(cp), 1n+U32.to_nat(c1), e_cp),
                        Equal.trans(Nat, 1n+Nat.add(U32.to_nat(c1), x2), 1n+nt, nr, Equal.cong(Nat, Nat, kz => 1n+kz,
                        Nat.add(U32.to_nat(c1), x2), nt, M10.add_sub(U32.to_nat(c1), nt, h_c)), Equal.sym(Nat, nr,
                            1n+nt,
                        e_R))) : {Nat.add(U32.to_nat(cp), x2) == nr : Nat}}
                      +h_lt2 = {M1.lt_rw_r(Nat.mul(kp, mn), xn, 1n+nt, Equal.trans(Nat, xn, nr, 1n+nt, hx, e_R), h_lt) :
                        {Nat.is_lt(Nat.mul(kp, mn), 1n+nt) == True{} : Bool}}
                      +h_le2 = {M1.le_rw_l(xn, 1n+nt, Nat.add(mn, Nat.mul(kp, mn)), Equal.trans(Nat, xn, nr, 1n+nt, hx,
                        e_R),
                        h_le) : {Nat.is_le(1n+nt, Nat.add(mn, Nat.mul(kp, mn))) == True{} : Bool}}
                      hk2 = kok.rw(Nat.sub(nt, U32.to_nat((cm - 1 : U32))), x2, kp, mn, Equal.cong(Nat, Nat, kz =>
                        Nat.sub(nt, kz), U32.to_nat((cm - 1 : U32)), U32.to_nat(c1), Equal.sym(Nat, U32.to_nat(c1),
                        U32.to_nat((cm - 1 : U32)), e_c)), ks.k(zz, kp, left, mx, nt, nzm, ezm, e_lt, h_lt2, h_le2))
                      +hw2 = {hw.head(nr, Nat.double(kp), pp, hw) : {Nat.is_le(Nat.add(Nat.add(nr, 1n), Nat.double(kp)),
                        1n+pp) == True{} : Bool}}
                      +ell2 = {Equal.trans(Nat, Nat.add(U32.to_nat(cp), nr), Nat.add(nr, U32.to_nat(cp)),
                        Nat.add(U32.to_nat(left), U32.to_nat(cp)), M1.ras.add_comm(U32.to_nat(cp), nr), Equal.cong(Nat,
                            Nat,
                        kz => Nat.add(kz, U32.to_nat(cp)), nr, U32.to_nat(left), Equal.sym(Nat, U32.to_nat(left), nr,
                        e_l))) : {Nat.add(U32.to_nat(cp), nr) == Nat.add(U32.to_nat(left), U32.to_nat(cp)) : Nat}}
                      +bf = Png.enc.bf(left)
                      +nlen = (cp .^. 65535 : U32)
                      +b1 = Png.enc.byte(cp)
                      +b2 = Png.enc.hi(cp)
                      +b3 = Png.enc.byte(nlen)
                      +b4 = Png.enc.hi(nlen)
                      +c5 = Crc.crc.byte(Crc.crc.byte(Crc.crc.byte(Crc.crc.byte(Crc.crc.byte(cc, bf), b1), b2), b3), b4)
                      +a4 = {b4 <> b3 <> b2 <> b1 <> bf <> acc : List<&2, U32>}
                      +bb2 = M1.bs(rr, False{}, U32.is_eq(cp, 1), cp, left, Png.enc.cap(l1), Png.enc.bf(l1))
                      +ih = {rg(pp, False{}, False{}, True{}, False{}, filt, zred, zgrn, zlast, px, col, row, ww, cp,
                        c5, a4,
                        aa, bb, left, cp, left, Png.enc.cap(l1), Png.enc.bf(l1), kp, x2, wp, mx, emx, ew, hrow, hfw,
                          hbl,
                        hx2, hk2, hw2, ({==}, ({==}, (Equal.sym(Bool, U32.is_zero(cp), False{}, nz_cp), (e_l, (ell2,
                        M1.edge.no(cp, left, Png.enc.cap(l1), Png.enc.bf(l1), nz_cp))))))) : {Png.enc.rgb.go(pp,
                            False{},
                        False{}, True{}, False{}, filt, zred, zgrn, zlast, px, col, row, ww, cp, c5, a4, aa, bb, left,
                          cp)
                        == (M1.fr(M1.bs(rr, U32.is_zero(cp), U32.is_eq(cp, 1), cp, left, Png.enc.cap(l1),
                            Png.enc.bf(l1)), c5,
                        a4), M1.afold(rr, aa, bb)) : (U32 & List<&2, U32>) & U32}}
                      Equal.trans((U32 & List<&2, U32>) & U32, Png.enc.rgb.go(pp, False{}, False{}, True{}, False{},
                        filt,
                        zred, zgrn, zlast, px, col, row, ww, cp, c5, a4, aa, bb, left, cp), (M1.fr(bb2, c5, a4),
                            M1.afold(rr,
                          aa,
                        bb)), rg.val(True{}, rr, cc, acc, aa, bb, left, need, pl, plen, pbf),
                        Equal.trans((U32 & List<&2, U32>) & U32, Png.enc.rgb.go(pp, False{}, False{}, True{}, False{},
                          filt,
                          zred, zgrn, zlast, px, col, row, ww, cp, c5, a4, aa, bb, left, cp), (M1.fr(M1.bs(rr,
                            U32.is_zero(cp),
                          U32.is_eq(cp, 1), cp, left, Png.enc.cap(l1), Png.enc.bf(l1)), c5, a4), M1.afold(rr, aa, bb)),
                          (M1.fr(bb2, c5, a4), M1.afold(rr, aa, bb)), ih, Equal.cong(Bool, (U32 & List<&2, U32>) & U32,
                              zb =>
                          (M1.fr(M1.bs(rr, zb, U32.is_eq(cp, 1), cp, left, Png.enc.cap(l1), Png.enc.bf(l1)), c5, a4),
                            M1.afold(rr,
                          aa, bb)), U32.is_zero(cp), False{}, nz_cp)),
                        Equal.sym((U32 & List<&2, U32>) & U32, rg.val(True{}, rr, cc, acc, aa, bb, left, need, pl, plen,
                          pbf), (M1.fr(bb2, c5, a4), M1.afold(rr, aa, bb)), Equal.trans((U32 & List<&2, U32>) & U32,
                          rg.val(True{}, rr, cc, acc, aa, bb, left, need, pl, plen, pbf), (M1.fr(List.append(&2, U32,
                          hd5(left), bb2), cc, acc), M1.afold(rr, aa, bb)), (M1.fr(bb2, c5, a4), M1.afold(rr, aa, bb)),
                          Equal.cong(List<&2, U32>, (U32 & List<&2, U32>) & U32, ys => (M1.fr(ys, cc, acc),
                              M1.afold(rr, aa,
                            bb)),
                          M1.bs(rr, True{}, False{}, 0, left, cp, bf), List.append(&2, U32, hd5(left), bb2), spl(rr,
                              left,
                          e_l, nzl, nz_cp)), Equal.cong(U32 & List<&2, U32>, (U32 & List<&2, U32>) & U32, qq => (qq,
                          M1.afold(rr, aa, bb)), M1.fr(List.append(&2, U32, hd5(left), bb2), cc, acc), M1.fr(bb2, c5,
                              a4),
                          Equal.sym(U32 & List<&2, U32>, M1.fr(bb2, c5, a4), M1.fr(List.append(&2, U32, hd5(left),
                              bb2), cc,
                          acc), fr.app(hd5(left), bb2, cc, acc))))))
        case False{}:
          match zdone:
            case True{}:
              (e_d, _rest) = hb
              Empty.absurd({Png.enc.rgb.go(1n+pp, False{}, True{}, zspan, zneed, filt, zred, zgrn, zlast, px, col, row,
                ww, need, cc, acc, aa, bb, left, len) == rg.val(False{}, M3.cur(filt, zred, zgrn, px, col, row, 1n+wp),
                    cc,
                acc, aa, bb, left, need, pl, plen, pbf) : (U32 & List<&2, U32>) & U32}, M1.false_true(Equal.sym(Bool,
                True{}, False{}, e_d)))
            case False{}:
              match zspan:
                case False{}:
                  (_e_d, (e_s, _rest)) = hb
                  Empty.absurd({Png.enc.rgb.go(1n+pp, False{}, False{}, False{}, zneed, filt, zred, zgrn, zlast, px,
                    col, row, ww, need, cc, acc, aa, bb, left, len) == rg.val(False{}, M3.cur(filt, zred, zgrn, px, col,
                    row, 1n+wp), cc, acc, aa, bb, left, need, pl, plen, pbf) : (U32 & List<&2, U32>) & U32},
                    M1.false_true(e_s))
                case True{}:
                  match zneed:
                    case True{}:
                      (_e_d, (_e_s, (+e_zn, (+e_pl, (+e_ll, hbe))))) = hb
                      +rr = M3.cur(filt, zred, zgrn, px, col, row, 1n+wp)
                      +nr = List.length(&2, U32, rr)
                      +l2 = (left - len : U32)
                      +e_n0 = {M1.zero.val(need, e_zn) : {U32.to_nat(need) == 0n : Nat}}
                      +e_lf = {Equal.trans(Nat, U32.to_nat(left), Nat.add(U32.to_nat(left), 0n),
                        Nat.add(U32.to_nat(len),
                        nr), Equal.sym(Nat, Nat.add(U32.to_nat(left), 0n), U32.to_nat(left),
                        M1.ras.add_zero(U32.to_nat(left))), Equal.trans(Nat, Nat.add(U32.to_nat(left), 0n),
                        Nat.add(U32.to_nat(left), U32.to_nat(need)), Nat.add(U32.to_nat(len), nr), Equal.cong(Nat, Nat,
                        kz => Nat.add(U32.to_nat(left), kz), 0n, U32.to_nat(need), Equal.sym(Nat, U32.to_nat(need), 0n,
                        e_n0)), Equal.sym(Nat, Nat.add(U32.to_nat(len), nr), Nat.add(U32.to_nat(left),
                        U32.to_nat(need)), e_ll))) : {U32.to_nat(left) == Nat.add(U32.to_nat(len), nr) : Nat}}
                      +h_ll = {M1.le_rw_r(U32.to_nat(len), Nat.add(U32.to_nat(len), nr), U32.to_nat(left),
                          Equal.sym(Nat,
                        U32.to_nat(left), Nat.add(U32.to_nat(len), nr), e_lf), M8.nle_add(U32.to_nat(len), nr)) :
                        {Nat.is_le(U32.to_nat(len), U32.to_nat(left)) == True{} : Bool}}
                      +e_l2 = {Equal.trans(Nat, U32.to_nat(l2), Nat.sub(U32.to_nat(left), U32.to_nat(len)), nr,
                        M10.ras.u32_sub_nat(left, len, h_ll), Equal.trans(Nat, Nat.sub(U32.to_nat(left),
                            U32.to_nat(len)),
                        Nat.sub(Nat.add(U32.to_nat(len), nr), U32.to_nat(len)), nr, Equal.cong(Nat, Nat, kz =>
                        Nat.sub(kz, U32.to_nat(len)), U32.to_nat(left), Nat.add(U32.to_nat(len), nr), e_lf),
                        sub_add_cancel(U32.to_nat(len), nr))) : {U32.to_nat(l2) == nr : Nat}}
                      +hx2 = {Equal.trans(Nat, xn, Nat.add(U32.to_nat(need), xn), nr, Equal.cong(Nat, Nat, kz =>
                        Nat.add(kz, xn), 0n, U32.to_nat(need), Equal.sym(Nat, U32.to_nat(need), 0n, e_n0)), hx) :
                        {Nat.add(U32.to_nat(0), xn) == nr : Nat}}
                      +ih = {rg(pp, True{}, U32.is_zero(l2), False{}, False{}, filt, zred, zgrn, zlast, px, col, row,
                        ww,
                        need, cc, acc, aa, bb, l2, len, pl, plen, pbf, kk, xn, wp, mx, emx, ew, hrow, hfw, hbl, hx2, hk,
                        hw.end(nr, Nat.double(kk), pp, hw), ({==}, e_l2)) : {Png.enc.rgb.go(pp, True{},
                        U32.is_zero(l2), False{}, False{}, filt, zred, zgrn, zlast, px, col, row, ww, need, cc, acc, aa,
                        bb, l2, len) == (M1.fr(M1.bs(rr, True{}, False{}, 0, l2, Png.enc.cap(l2), Png.enc.bf(l2)), cc,
                            acc),
                        M1.afold(rr, aa, bb)) : (U32 & List<&2, U32>) & U32}}
                      Equal.trans((U32 & List<&2, U32>) & U32, Png.enc.rgb.go(pp, True{}, U32.is_zero(l2), False{},
                        False{}, filt, zred, zgrn, zlast, px, col, row, ww, need, cc, acc, aa, bb, l2, len),
                        (M1.fr(M1.bs(rr, True{}, False{}, 0, l2, Png.enc.cap(l2), Png.enc.bf(l2)), cc, acc),
                            M1.afold(rr, aa,
                        bb)), rg.val(False{}, rr, cc, acc, aa, bb, left, need, pl, plen, pbf), ih,
                        Equal.cong(List<&2, U32>, (U32 & List<&2, U32>) & U32, ys => (M1.fr(ys, cc, acc), M1.afold(rr,
                            aa,
                        bb)), M1.bs(rr, True{}, False{}, 0, l2, Png.enc.cap(l2), Png.enc.bf(l2)), M1.bs(rr,
                        U32.is_zero(need), U32.is_eq(need, 1), need, pl, plen, pbf), Equal.sym(List<&2, U32>, M1.bs(rr,
                        U32.is_zero(need), U32.is_eq(need, 1), need, pl, plen, pbf), M1.bs(rr, True{}, False{}, 0, l2,
                        Png.enc.cap(l2), Png.enc.bf(l2)), n0.bs(rr, need, pl, plen, pbf, l2, e_zn, e_pl, e_l2, hbe))))
                      case False{}:
                        match filt:
                          case True{}:
                            match px:
                              case Nil{}:
                                (_e_d, (_e_s, (e_zn, _rest))) = hb
                                Empty.absurd({Png.enc.rgb.go(1n+pp, False{}, False{}, True{}, False{}, True{}, zred,
                                  zgrn, zlast, [], col, row, ww, need, cc, acc, aa, bb, left, len) == rg.val(False{},
                                    M3.cur(True{}, zred, zgrn, [], col, row, 1n+wp), cc, acc, aa, bb, left, need, pl,
                                    plen, pbf) : (U32 & List<&2, U32>) & U32}, need.nil(need, xn, e_zn, hx))
                              case +s <> +t:
                                (_e_d, (_e_s, (+e_zn, (+e_pl, (+e_ll, _hbe))))) = hb
                                +r2 = M3.cur(False{}, True{}, False{}, s <> t, col, row, 1n+wp)
                                +e_R = {cur.filt(s, t, row, wp, Equal.trans(Nat, U32.to_nat(row), U32.to_nat(ww),
                                  1n+wp, Equal.cong(U32, Nat, uu => U32.to_nat(uu), row, ww,
                                  hfw({==})), ew)) : {M3.cur(True{}, zred, zgrn, s <> t, col, row, 1n+wp) ==
                                    0 <> r2 : List<&2, U32>}}
                                rg.byte(pp, 0, M3.cur(True{}, zred, zgrn, s <> t, col, row, 1n+wp), r2, need, pl, plen,
                                  pbf, cc, acc, aa, bb, left, len, kk, xn, Png.enc.rgb.go(pp, False{}, False{}, True{},
                                  U32.is_zero((need - 1 : U32)), False{}, True{}, False{}, False{}, s <> t, col, row,
                                    ww, (need - 1 : U32), Crc.crc.byte(cc, 0), 0 <> acc, Png.enc.add(aa, 0),
                                    Png.enc.add(bb, Png.enc.add(aa, 0)), left, len), e_R, e_zn, hx, hw, e_pl, e_ll,
                                    xx => yy => h1 => h2 => h3 => h4 => h5 => rg(pp, False{}, False{}, True{},
                                    U32.is_zero((need - 1 : U32)), False{}, True{}, False{}, False{}, s <> t, col, row,
                                    ww, (need - 1 : U32), Crc.crc.byte(cc, 0), 0 <> acc, Png.enc.add(aa, 0),
                                    Png.enc.add(bb, Png.enc.add(aa, 0)), left, len, (pl - 1 : U32), xx, yy, kk, xn, wp,
                                    mx, emx, ew, hrow, ef => Empty.absurd({row == ww : U32}, M1.false_true(ef)),
                                    _e1 => e2 => _e3 => Empty.absurd({False{} == U32.is_eq(row, 1) : Bool},
                                    M1.false_true(Equal.sym(Bool, True{}, False{}, e2))), h2, hk, h3, ({==}, ({==},
                                    ({==}, (h4, (h5, h1)))))))
                          case False{}:
                            match zred:
                              case True{}:
                                match zgrn:
                                  case _gn:
                                    match zlast:
                                      case _ls:
                                        match px:
                                          case Nil{}:
                                            (_e_d, (_e_s, (e_zn, _rest))) = hb
                                            Empty.absurd({Png.enc.rgb.go(1n+pp, False{}, False{}, True{}, False{},
                                              False{}, True{}, _gn, _ls, [], col, row, ww, need, cc, acc, aa, bb, left,
                                                len) == rg.val(False{}, M3.cur(False{}, True{}, _gn, [], col, row,
                                                    1n+wp),
                                                cc, acc, aa, bb, left, need, pl, plen, pbf) : (U32 & List<&2,
                                                U32>) & U32}, need.nil(need, xn, e_zn, hx))
                                          case +s <> +t:
                                            (_e_d, (_e_s, (+e_zn, (+e_pl, (+e_ll, _hbe))))) = hb
                                            +r2 = M3.cur(False{}, False{}, True{}, t, s, row, 1n+wp)
                                            +e_R = {cur.red(s, t, row, 1n+wp, hrow) : {M3.cur(False{}, True{}, _gn,
                                              s <> t, col, row, 1n+wp) == Png.enc.r(s) <> r2 : List<&2, U32>}}
                                            rg.byte(pp, Png.enc.r(s), M3.cur(False{}, True{}, _gn, s <> t, col, row,
                                              1n+wp), r2, need, pl, plen, pbf, cc, acc, aa, bb, left, len, kk, xn,
                                                Png.enc.rgb.go(pp, False{}, False{}, True{},
                                                U32.is_zero((need - 1 : U32)), False{}, False{}, True{}, False{}, t, s,
                                                row, ww, (need - 1 : U32), Crc.crc.byte(cc, Png.enc.r(s)),
                                                Png.enc.r(s) <> acc, Png.enc.add(aa, Png.enc.r(s)), Png.enc.add(bb,
                                                Png.enc.add(aa, Png.enc.r(s))), left, len), e_R, e_zn, hx, hw, e_pl,
                                                e_ll, xx => yy => h1 => h2 => h3 => h4 => h5 => rg(pp, False{},
                                                False{}, True{}, U32.is_zero((need - 1 : U32)), False{}, False{},
                                                True{}, False{}, t, s, row, ww, (need - 1 : U32), Crc.crc.byte(cc,
                                                Png.enc.r(s)), Png.enc.r(s) <> acc, Png.enc.add(aa, Png.enc.r(s)),
                                                Png.enc.add(bb, Png.enc.add(aa, Png.enc.r(s))), left, len,
                                                (pl - 1 : U32), xx, yy, kk, xn, wp, mx, emx, ew, hrow,
                                                ef => Empty.absurd({row == ww : U32}, M1.false_true(ef)),
                                                _e1 => _e2 => e3 => Empty.absurd({False{} == U32.is_eq(row, 1) : Bool},
                                                M1.false_true(Equal.sym(Bool, True{}, False{}, e3))), h2, hk, h3,
                                                ({==}, ({==}, ({==}, (h4, (h5, h1)))))))
                              case False{}:
                                match zgrn:
                                  case True{}:
                                    (_e_d, (_e_s, (+e_zn, (+e_pl, (+e_ll, _hbe))))) = hb
                                    +r2 = M3.cur(False{}, False{}, False{}, px, col, row, 1n+wp)
                                    +e_R = {{==} : {M3.cur(False{}, False{}, True{}, px, col, row,
                                      1n+wp) == Png.enc.g(col) <> r2 : List<&2, U32>}}
                                    rg.byte(pp, Png.enc.g(col), M3.cur(False{}, False{}, True{}, px, col, row, 1n+wp),
                                        r2,
                                      need, pl, plen, pbf, cc, acc, aa, bb, left, len, kk, xn, Png.enc.rgb.go(pp,
                                      False{}, False{}, True{}, U32.is_zero((need - 1 : U32)), False{}, False{},
                                        False{}, U32.is_eq(row, 1), px, col, row, ww, (need - 1 : U32),
                                        Crc.crc.byte(cc, Png.enc.g(col)), Png.enc.g(col) <> acc, Png.enc.add(aa,
                                        Png.enc.g(col)), Png.enc.add(bb, Png.enc.add(aa, Png.enc.g(col))), left, len),
                                        e_R, e_zn, hx, hw, e_pl, e_ll, xx => yy => h1 => h2 => h3 => h4 => h5 => rg(pp,
                                        False{}, False{}, True{}, U32.is_zero((need - 1 : U32)), False{}, False{},
                                        False{}, U32.is_eq(row, 1), px, col, row, ww, (need - 1 : U32),
                                        Crc.crc.byte(cc, Png.enc.g(col)), Png.enc.g(col) <> acc, Png.enc.add(aa,
                                        Png.enc.g(col)), Png.enc.add(bb, Png.enc.add(aa, Png.enc.g(col))), left, len,
                                        (pl - 1 : U32), xx, yy, kk, xn, wp, mx, emx, ew, hrow,
                                        ef => Empty.absurd({row == ww : U32}, M1.false_true(ef)),
                                        _e1 => _e2 => _e3 => {==}, h2, hk, h3, ({==}, ({==}, ({==}, (h4, (h5, h1)))))))
                                  case False{}:
                                    match zlast:
                                      case True{}:
                                        (_e_d, (_e_s, (+e_zn, (+e_pl, (+e_ll, _hbe))))) = hb
                                        +r2 = M3.cur(True{}, True{}, False{}, px, col, ww, 1n+wp)
                                        +e_R = {cur.last(col, px, row, 1n+wp, hbl({==}, {==}, {==})) : {M3.cur(False{},
                                          False{}, False{}, px, col, row, 1n+wp) == Png.enc.b(col) <> r2 : List<&2,
                                            U32>}}
                                        rg.byte(pp, Png.enc.b(col), M3.cur(False{}, False{}, False{}, px, col, row,
                                          1n+wp), r2, need, pl, plen, pbf, cc, acc, aa, bb, left, len, kk, xn,
                                            Png.enc.rgb.go(pp, False{}, False{}, True{}, U32.is_zero((need - 1 : U32)),
                                            True{}, True{}, False{}, False{}, px, col, ww, ww, (need - 1 : U32),
                                            Crc.crc.byte(cc, Png.enc.b(col)), Png.enc.b(col) <> acc, Png.enc.add(aa,
                                            Png.enc.b(col)), Png.enc.add(bb, Png.enc.add(aa, Png.enc.b(col))), left,
                                            len), e_R, e_zn, hx, hw, e_pl, e_ll,
                                            xx => yy => h1 => h2 => h3 => h4 => h5 => rg(pp, False{}, False{}, True{},
                                            U32.is_zero((need - 1 : U32)), True{}, True{}, False{}, False{}, px, col,
                                            ww, ww, (need - 1 : U32), Crc.crc.byte(cc, Png.enc.b(col)),
                                            Png.enc.b(col) <> acc, Png.enc.add(aa, Png.enc.b(col)), Png.enc.add(bb,
                                            Png.enc.add(aa, Png.enc.b(col))), left, len, (pl - 1 : U32), xx, yy, kk,
                                            xn, wp, mx, emx, ew, M1.u32_nonzero(ww, wp, ew), _ef => {==},
                                            ef => Empty.absurd({True{} == False{} : Bool} -> {False{} ==
                                            False{} : Bool} -> {False{} == U32.is_eq(ww, 1) : Bool},
                                            M1.false_true(Equal.sym(Bool, True{}, False{}, ef))), h2, hk, h3, ({==},
                                            ({==}, ({==}, (h4, (h5, h1)))))))
                                      case False{}:
                                        (_e_d, (_e_s, (+e_zn, (+e_pl, (+e_ll, _hbe))))) = hb
                                        +r2 = M3.cur(False{}, True{}, False{}, px, col, (row - 1 : U32), 1n+wp)
                                        +e_R = {cur.blue(col, px, row, 1n+wp, hrow) : {M3.cur(False{}, False{}, False{},
                                          px, col, row, 1n+wp) == Png.enc.b(col) <> r2 : List<&2, U32>}}
                                        rg.byte(pp, Png.enc.b(col), M3.cur(False{}, False{}, False{}, px, col, row,
                                          1n+wp), r2, need, pl, plen, pbf, cc, acc, aa, bb, left, len, kk, xn,
                                            Png.enc.rgb.go(pp, False{}, False{}, True{}, U32.is_zero((need - 1 : U32)),
                                            False{}, True{}, False{}, False{}, px, col, (row - 1 : U32), ww,
                                            (need - 1 : U32), Crc.crc.byte(cc, Png.enc.b(col)), Png.enc.b(col) <> acc,
                                            Png.enc.add(aa, Png.enc.b(col)), Png.enc.add(bb, Png.enc.add(aa,
                                            Png.enc.b(col))), left, len), e_R, e_zn, hx, hw, e_pl, e_ll,
                                            xx => yy => h1 => h2 => h3 => h4 => h5 => rg(pp, False{}, False{}, True{},
                                            U32.is_zero((need - 1 : U32)), False{}, True{}, False{}, False{}, px, col,
                                            (row - 1 : U32), ww, (need - 1 : U32), Crc.crc.byte(cc, Png.enc.b(col)),
                                            Png.enc.b(col) <> acc, Png.enc.add(aa, Png.enc.b(col)), Png.enc.add(bb,
                                            Png.enc.add(aa, Png.enc.b(col))), left, len, (pl - 1 : U32), xx, yy, kk,
                                            xn, wp, mx, emx, ew, M1.two(row, Equal.sym(Bool, U32.is_zero(row), False{},
                                            hrow), hbl({==}, {==}, {==})), ef => Empty.absurd({(row - 1 : U32) ==
                                            ww : U32}, M1.false_true(ef)),
                                            _e1 => e2 => _e3 => Empty.absurd({False{} == U32.is_eq((row - 1 : U32),
                                            1) : Bool}, M1.false_true(Equal.sym(Bool, True{}, False{}, e2))), h2, hk,
                                            h3, ({==}, ({==}, ({==}, (h4, (h5, h1)))))))

# ---- I. Adler-32 as enc.rgb.go adds it is Inf.adler.of ----

# The Adler modulus, 65521, is named pm below, for the same reason as mx.

# enc.add.at with the modulus named
def addm(zz: Bool, +tt: U32, +pm: U32) -> U32:
  match zz:
    case True{}:
      (tt - pm : U32)
    case False{}:
      tt

# enc.add.at is addm at 65521
def addm.eq(
  zz: Bool,
  +tt: U32,
  +pm: U32,
  +epm: {pm == 65521 : U32}
) -> {Png.enc.add.at(zz, tt) == addm(zz, tt, pm) : U32}:
  match zz:
    case True{}:
      Equal.cong(U32, U32, uu => (tt - uu : U32), 65521, pm, Equal.sym(U32, pm, 65521, epm))
    case False{}:
      {==}

# at most and below cannot both hold the other way round
def le.lt.no(
  +aa: Nat,
  +bb: Nat,
  +h1: {Nat.is_le(aa, bb) == True{} : Bool},
  +h2: {Nat.is_lt(bb, aa) == True{} : Bool}
) -> Empty:
  pfin.lt.irr(aa, M1.le_lt_trans(aa, bb, aa, h1, h2))

# t below 2 m is t mod m after one subtraction of m, or none: which one is t >= m's answer
def md.at(
  zz: Bool,
  qn: Nat,
  +tt: U32,
  +pm: U32,
  +ez: {U32.is_ge(tt, pm) == zz : Bool},
  +e_t: {U32.to_nat(tt) == Nat.add(Nat.mul(qn, U32.to_nat(pm)), U32.to_nat(U32.mod(tt, pm))) : Nat},
  +l_r: {Nat.is_lt(U32.to_nat(U32.mod(tt, pm)), U32.to_nat(pm)) == True{} : Bool},
  +ht: {Nat.is_lt(U32.to_nat(tt), Nat.add(U32.to_nat(pm), U32.to_nat(pm))) == True{} : Bool}
) -> {addm(zz, tt, pm) == U32.mod(tt, pm) : U32}:
  match zz qn:
    case True{} 0n:
      +mn = U32.to_nat(pm)
      +rn = U32.to_nat(U32.mod(tt, pm))
      +hg = {ge.le(U32.to_nat(tt), mn, Equal.trans(Bool, Cmp.is_ge(Nat.cmp(U32.to_nat(tt), mn)), U32.is_ge(tt, pm),
        True{}, Equal.sym(Bool, U32.is_ge(tt, pm), Cmp.is_ge(Nat.cmp(U32.to_nat(tt), mn)), u.ge(tt, pm)), ez)) :
        {Nat.is_le(mn, U32.to_nat(tt)) == True{} : Bool}}
      Empty.absurd({(tt - pm : U32) == U32.mod(tt, pm) : U32}, le.lt.no(mn, rn, M1.le_rw_r(mn, U32.to_nat(tt), rn, e_t,
        hg), l_r))
    case True{} 1n+qp:
      match qp:
        case 0n:
          +mn = U32.to_nat(pm)
          +rn = U32.to_nat(U32.mod(tt, pm))
          +hg = {ge.le(U32.to_nat(tt), mn, Equal.trans(Bool, Cmp.is_ge(Nat.cmp(U32.to_nat(tt), mn)), U32.is_ge(tt, pm),
            True{}, Equal.sym(Bool, U32.is_ge(tt, pm), Cmp.is_ge(Nat.cmp(U32.to_nat(tt), mn)), u.ge(tt, pm)), ez)) :
            {Nat.is_le(mn, U32.to_nat(tt)) == True{} : Bool}}
          +e_t2 = {Equal.trans(Nat, U32.to_nat(tt), Nat.add(Nat.add(mn, 0n), rn), Nat.add(mn, rn), e_t, Equal.cong(Nat,
            Nat, kz => Nat.add(kz, rn), Nat.add(mn, 0n), mn, M1.ras.add_zero(mn))) : {U32.to_nat(tt) == Nat.add(mn,
                rn) :
            Nat}}
          M1.u32.same((tt - pm : U32), U32.mod(tt, pm), Equal.trans(Nat, U32.to_nat((tt - pm : U32)),
            Nat.sub(U32.to_nat(tt),
            mn), rn, M10.ras.u32_sub_nat(tt, pm, hg), Equal.trans(Nat, Nat.sub(U32.to_nat(tt), mn), Nat.sub(Nat.add(mn,
                rn),
            mn), rn, Equal.cong(Nat, Nat, kz => Nat.sub(kz, mn), U32.to_nat(tt), Nat.add(mn, rn), e_t2),
            sub_add_cancel(mn, rn))))
        case 1n+(+qq):
          +mn = U32.to_nat(pm)
          +rn = U32.to_nat(U32.mod(tt, pm))
          +yy = Nat.add(mn, Nat.mul(qq, mn))
          +h1 = {M1.le_add_mono(mn, mn, yy, M8.nle_add(mn, Nat.mul(qq, mn))) : {Nat.is_le(Nat.add(mn, mn), Nat.add(mn,
            yy)) == True{} : Bool}}
          +h2 = {M1.le_rw_r(Nat.add(mn, mn), Nat.add(Nat.add(mn, yy), rn), U32.to_nat(tt), Equal.sym(Nat,
              U32.to_nat(tt),
            Nat.add(Nat.add(mn, yy), rn), e_t), M1.le_trans(Nat.add(mn, mn), Nat.add(mn, yy), Nat.add(Nat.add(mn, yy),
            rn), h1, M8.nle_add(Nat.add(mn, yy), rn))) : {Nat.is_le(Nat.add(mn, mn), U32.to_nat(tt)) == True{} : Bool}}
          Empty.absurd({(tt - pm : U32) == U32.mod(tt, pm) : U32}, le.lt.no(Nat.add(mn, mn), U32.to_nat(tt), h2, ht))
    case False{} 0n:
      M1.u32.same(tt, U32.mod(tt, pm), e_t)
    case False{} 1n+(+qp):
      +mn = U32.to_nat(pm)
      +rn = U32.to_nat(U32.mod(tt, pm))
      +yy = Nat.add(mn, Nat.mul(qp, mn))
      +hl = {nge.lt(U32.to_nat(tt), mn, Equal.trans(Bool, Cmp.is_ge(Nat.cmp(U32.to_nat(tt), mn)), U32.is_ge(tt, pm),
        False{}, Equal.sym(Bool, U32.is_ge(tt, pm), Cmp.is_ge(Nat.cmp(U32.to_nat(tt), mn)), u.ge(tt, pm)), ez)) :
        {Nat.is_lt(U32.to_nat(tt), mn) == True{} : Bool}}
      +h2 = {M1.le_rw_r(mn, Nat.add(yy, rn), U32.to_nat(tt), Equal.sym(Nat, U32.to_nat(tt), Nat.add(yy, rn), e_t),
        M1.le_trans(mn, yy, Nat.add(yy, rn), M8.nle_add(mn, Nat.mul(qp, mn)), M8.nle_add(yy, rn))) : {Nat.is_le(mn,
        U32.to_nat(tt)) == True{} : Bool}}
      Empty.absurd({tt == U32.mod(tt, pm) : U32}, le.lt.no(mn, U32.to_nat(tt), h2, hl))

# the modulus doubled is a U32's value
def pm.dbl(
  +pm: U32,
  +epm: {pm == 65521 : U32}
) -> {U32.to_nat(U32.add(pm, pm)) == Nat.add(U32.to_nat(pm), U32.to_nat(pm)) : Nat}:
  add.cf(pm, pm, Equal.cong(U32, Bool, uu => cy32(uu, uu), pm, 65521, epm))

# U32.mod by the modulus: a quotient and a remainder below it
def pm.dvm(+tt: U32, +pm: U32, +epm: {pm == 65521 : U32}) -> dvm.ty(tt, pm):
  +mn = U32.to_nat(pm)
  +hm = {Equal.trans(Bool, Nat.is_lt(0n, mn), U32.is_lt(0, pm), True{}, Equal.sym(Bool, U32.is_lt(0, pm), Nat.is_lt(0n,
    mn), M11.u32_lt(0, pm)), Equal.cong(U32, Bool, uu => U32.is_lt(0, uu), pm, 65521, epm)) : {Nat.is_lt(0n, mn) ==
      True{} :
    Bool}}
  +h2 = {M1.le_rw_r(Nat.add(mn, mn), Nat.add(mn, mn), U32.to_nat(U32.add(pm, pm)), Equal.sym(Nat,
    U32.to_nat(U32.add(pm, pm)), Nat.add(mn, mn), pm.dbl(pm, epm)), M1.le_refl(Nat.add(mn, mn))) :
    {Nat.is_le(Nat.add(mn, mn), U32.to_nat(U32.add(pm, pm))) == True{} : Bool}}
  dvm(tt, pm, U32.add(pm, pm), hm, h2)

# the pair pm.dvm gives, taken apart, for one subtraction
def md.go(
  +tt: U32,
  +pm: U32,
  pr: dvm.ty(tt, pm),
  +ht: {Nat.is_lt(U32.to_nat(tt), Nat.add(U32.to_nat(pm), U32.to_nat(pm))) == True{} : Bool}
) -> {addm(U32.is_ge(tt, pm), tt, pm) == U32.mod(tt, pm) : U32}:
  (+e_t, +l_r) = pr
  md.at(U32.is_ge(tt, pm), U32.to_nat(U32.div(tt, pm)), tt, pm, {==}, e_t, l_r, ht)

# enc.add.at of a sum below twice the modulus is the sum mod 65521
def mod.once(
  +tt: U32,
  +pm: U32,
  +epm: {pm == 65521 : U32},
  +ht: {Nat.is_lt(U32.to_nat(tt), Nat.add(U32.to_nat(pm), U32.to_nat(pm))) == True{} : Bool}
) -> {Png.enc.add.at(U32.is_ge(tt, 65521), tt) == (tt % 65521 : U32) : U32}:
  +e65 = {Equal.sym(U32, pm, 65521, epm) : {65521 == pm : U32}}
  Equal.trans(U32, Png.enc.add.at(U32.is_ge(tt, 65521), tt), addm(U32.is_ge(tt, pm), tt, pm), (tt % 65521 : U32),
    Equal.trans(U32, Png.enc.add.at(U32.is_ge(tt, 65521), tt), Png.enc.add.at(U32.is_ge(tt, pm), tt), addm(U32.is_ge(tt,
      pm), tt, pm), Equal.cong(U32, U32, uu => Png.enc.add.at(U32.is_ge(tt, uu), tt), 65521, pm, e65),
      addm.eq(U32.is_ge(tt, pm), tt, pm, epm)),
    Equal.trans(U32, addm(U32.is_ge(tt, pm), tt, pm), U32.mod(tt, pm), (tt % 65521 : U32), md.go(tt, pm, pm.dvm(tt, pm,
      epm), ht), Equal.cong(U32, U32, uu => U32.mod(tt, uu), pm, 65521, epm)))

# the remainder pm.dvm gives, read as mod 65521
def mod.lt.go(
  +tt: U32,
  +pm: U32,
  +epm: {pm == 65521 : U32},
  pr: dvm.ty(tt, pm)
) -> {Nat.is_lt(U32.to_nat((tt % 65521 : U32)), U32.to_nat(pm)) == True{} : Bool}:
  (_e_t, +l_r) = pr
  M1.lt_rw_l(U32.to_nat(U32.mod(tt, pm)), U32.to_nat((tt % 65521 : U32)), U32.to_nat(pm), Equal.cong(U32, Nat, uu =>
    U32.to_nat(U32.mod(tt, uu)), pm, 65521, epm), l_r)

# U32.mod by 65521 is below it
def mod.lt(
  +tt: U32,
  +pm: U32,
  +epm: {pm == 65521 : U32}
) -> {Nat.is_lt(U32.to_nat((tt % 65521 : U32)), U32.to_nat(pm)) == True{} : Bool}:
  mod.lt.go(tt, pm, epm, pm.dvm(tt, pm, epm))

# one Adler-32 add of values below the modulus is the add mod 65521
def add.mod(
  +ss: U32,
  +xx: U32,
  +pm: U32,
  +epm: {pm == 65521 : U32},
  +hs: {Nat.is_lt(U32.to_nat(ss), U32.to_nat(pm)) == True{} : Bool},
  +hx: {Nat.is_lt(U32.to_nat(xx), U32.to_nat(pm)) == True{} : Bool}
) -> {Png.enc.add(ss, xx) == ((ss + xx : U32) % 65521 : U32) : U32}:
  +mn = U32.to_nat(pm)
  +sn = U32.to_nat(ss)
  +xn = U32.to_nat(xx)
  +h1 = {Equal.trans(Bool, Nat.is_le(1n+sn, mn), Nat.is_lt(sn, mn), True{}, Equal.sym(Bool, Nat.is_lt(sn, mn),
    Nat.is_le(1n+sn, mn), M1.lt_le_succ(sn, mn)), hs) : {Nat.is_le(1n+sn, mn) == True{} : Bool}}
  +h2 = {M1.le_add_both(1n+sn, mn, xn, mn, h1, M1.lt_le(xn, mn, hx)) : {Nat.is_le(1n+Nat.add(sn, xn), Nat.add(mn,
      mn)) ==
    True{} : Bool}}
  +h3 = {Equal.trans(Bool, Nat.is_lt(Nat.add(sn, xn), Nat.add(mn, mn)), Nat.is_le(1n+Nat.add(sn, xn), Nat.add(mn, mn)),
    True{}, M1.lt_le_succ(Nat.add(sn, xn), Nat.add(mn, mn)), h2) : {Nat.is_lt(Nat.add(sn, xn), Nat.add(mn, mn)) ==
    True{} : Bool}}
  +e_s = {M11.u32_add_below(ss, xx, U32.add(pm, pm), M1.le_rw_r(Nat.add(sn, xn), Nat.add(mn, mn), U32.to_nat(U32.add(pm,
    pm)), Equal.sym(Nat, U32.to_nat(U32.add(pm, pm)), Nat.add(mn, mn), pm.dbl(pm, epm)), M1.lt_le(Nat.add(sn, xn),
    Nat.add(mn, mn), h3))) : {U32.to_nat((ss + xx : U32)) == Nat.add(sn, xn) : Nat}}
  mod.once((ss + xx : U32), pm, epm, M1.lt_rw_l(Nat.add(sn, xn), U32.to_nat((ss + xx : U32)), Nat.add(mn, mn),
    Equal.sym(Nat, U32.to_nat((ss + xx : U32)), Nat.add(sn, xn), e_s), h3))

# a byte is below the modulus
def byte.pm(
  +xx: U32,
  +pm: U32,
  +epm: {pm == 65521 : U32},
  +hh: {U32.is_le(xx, 255) == True{} : Bool}
) -> {Nat.is_lt(U32.to_nat(xx), U32.to_nat(pm)) == True{} : Bool}:
  M1.le_lt_trans(U32.to_nat(xx), U32.to_nat(255), U32.to_nat(pm), Equal.trans(Bool, Nat.is_le(U32.to_nat(xx),
    U32.to_nat(255)), U32.is_le(xx, 255), True{}, Equal.sym(Bool, U32.is_le(xx, 255), Nat.is_le(U32.to_nat(xx),
    U32.to_nat(255)), M10.u32_le(xx, 255)), hh), Equal.trans(Bool, Nat.is_lt(U32.to_nat(255), U32.to_nat(pm)),
    U32.is_lt(255, pm), True{}, Equal.sym(Bool, U32.is_lt(255, pm), Nat.is_lt(U32.to_nat(255), U32.to_nat(pm)),
    M11.u32_lt(255, pm)), Equal.cong(U32, Bool, uu => U32.is_lt(255, uu), pm, 65521, epm)))

# afold of bytes is Inf.adler's fold, from sums below the modulus
def ad.eq(
  xs: List<&2, U32>,
  +aa: U32,
  +bb: U32,
  +pm: U32,
  +epm: {pm == 65521 : U32},
  +hby: {D1.bytes.go(xs, True{}) == True{} : Bool},
  +ha: {Nat.is_lt(U32.to_nat(aa), U32.to_nat(pm)) == True{} : Bool},
  +hb: {Nat.is_lt(U32.to_nat(bb), U32.to_nat(pm)) == True{} : Bool}
) -> {M1.afold(xs, aa, bb) == Inf.adler.fin(Inf.adler.go(xs, aa, bb)) : U32}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      +a2 = ((aa + x : U32) % 65521 : U32)
      +b2 = ((bb + a2 : U32) % 65521 : U32)
      +hxb = {M9.bytes.ok(t, U32.is_le(x, 255), hby) : {U32.is_le(x, 255) == True{} : Bool}}
      +e_a = {add.mod(aa, x, pm, epm, ha, byte.pm(x, pm, epm, hxb)) : {Png.enc.add(aa, x) == a2 : U32}}
      +l_a = {mod.lt((aa + x : U32), pm, epm) : {Nat.is_lt(U32.to_nat(a2), U32.to_nat(pm)) == True{} : Bool}}
      +e_b = {Equal.trans(U32, Png.enc.add(bb, Png.enc.add(aa, x)), Png.enc.add(bb, a2), b2, Equal.cong(U32, U32, uu =>
        Png.enc.add(bb, uu), Png.enc.add(aa, x), a2, e_a), add.mod(bb, a2, pm, epm, hb, l_a)) : {Png.enc.add(bb,
        Png.enc.add(aa, x)) == b2 : U32}}
      +l_b = {mod.lt((bb + a2 : U32), pm, epm) : {Nat.is_lt(U32.to_nat(b2), U32.to_nat(pm)) == True{} : Bool}}
      Equal.trans(U32, M1.afold(t, Png.enc.add(aa, x), Png.enc.add(bb, Png.enc.add(aa, x))), M1.afold(t, a2, b2),
        Inf.adler.fin(Inf.adler.go(t, a2, b2)),
        Equal.trans(U32, M1.afold(t, Png.enc.add(aa, x), Png.enc.add(bb, Png.enc.add(aa, x))), M1.afold(t, a2,
          Png.enc.add(bb, Png.enc.add(aa, x))), M1.afold(t, a2, b2), Equal.cong(U32, U32, uu => M1.afold(t, uu,
            Png.enc.add(bb,
          Png.enc.add(aa, x))), Png.enc.add(aa, x), a2, e_a), Equal.cong(U32, U32, uu => M1.afold(t, a2, uu),
          Png.enc.add(bb, Png.enc.add(aa, x)), b2, e_b)),
        ad.eq(t, a2, b2, pm, epm, M9.bytes.tail(t, U32.is_le(x, 255), hby), l_a, l_b))

# enc.rgb.go's Adler-32 of bytes is Inf.adler.of
def afold.adler(
  +xs: List<&2, U32>,
  +pm: U32,
  +epm: {pm == 65521 : U32},
  +hby: {D1.bytes(xs) == True{} : Bool}
) -> {M1.afold(xs, 1, 0) == Inf.adler.of(xs) : U32}:
  +lt1 = {Equal.trans(Bool, Nat.is_lt(U32.to_nat(1), U32.to_nat(pm)), U32.is_lt(1, pm), True{}, Equal.sym(Bool,
    U32.is_lt(1, pm), Nat.is_lt(U32.to_nat(1), U32.to_nat(pm)), M11.u32_lt(1, pm)), Equal.cong(U32, Bool, uu =>
    U32.is_lt(1, uu), pm, 65521, epm)) : {Nat.is_lt(U32.to_nat(1), U32.to_nat(pm)) == True{} : Bool}}
  +lt0 = {Equal.trans(Bool, Nat.is_lt(U32.to_nat(0), U32.to_nat(pm)), U32.is_lt(0, pm), True{}, Equal.sym(Bool,
    U32.is_lt(0, pm), Nat.is_lt(U32.to_nat(0), U32.to_nat(pm)), M11.u32_lt(0, pm)), Equal.cong(U32, Bool, uu =>
    U32.is_lt(0, uu), pm, 65521, epm)) : {Nat.is_lt(U32.to_nat(0), U32.to_nat(pm)) == True{} : Bool}}
  ad.eq(xs, 1, 0, pm, epm, hby, lt1, lt0)

# ---- J. enc.wide.rgb after the signature and IHDR ----

# twice k, as a product
def mul2(kk: Nat) -> {Nat.mul(kk, 2n) == Nat.double(kk) : Nat}:
  match kk:
    case 0n:
      {==}
    case 1n+kp:
      Equal.cong(Nat, Nat, xx => 2n+xx, Nat.mul(kp, 2n), Nat.double(kp), mul2(kp))

# a count above 65535 is not zero, once is_zero's answer is named
def big.nz.at(
  zz: Bool,
  +nn: U32,
  +ez: {U32.is_zero(nn) == zz : Bool},
  +hbig: {U32.is_le(nn, 65535) == False{} : Bool}
) -> {U32.is_zero(nn) == False{} : Bool}:
  match zz:
    case False{}:
      ez
    case True{}:
      +e0 = {M1.ueq(nn, 0, ez) : {nn == 0 : U32}}
      Empty.absurd({U32.is_zero(nn) == False{} : Bool}, M1.false_true(Equal.trans(Bool, False{}, U32.is_le(nn, 65535),
        True{}, Equal.sym(Bool, U32.is_le(nn, 65535), False{}, hbig), Equal.cong(U32, Bool, uu => U32.is_le(uu, 65535),
        nn, 0, e0))))

# the fuel enc.wide.rgb.z gives enc.rgb.go: a step per raw byte and two per
# block, less one
def rgb.fuel(
  +nn: U32,
  +tu: U32,
  +nr: Nat,
  +hn: {U32.to_nat(nn) == nr : Nat},
  +nz: {U32.is_zero(nn) == False{} : Bool},
  +h_tu: {Nat.is_le(kzn(nr, nn), U32.to_nat(tu)) == True{} : Bool}
) -> {Nat.is_le(Nat.add(Nat.add(nr, 0n), Nat.double(U32.to_nat(Png.enc.nblk(nn)))),
  1n+U32.to_nat(((nn + (Png.enc.nblk(nn) * 2 : U32) : U32) - 1 : U32))) == True{} : Bool}:
  +kb = Png.enc.nblk(nn)
  +kn = U32.to_nat(kb)
  +k2 = Nat.mul(kn, 2n)
  +tn = U32.to_nat(tu)
  +s1 = (nn + (kb * 2 : U32) : U32)
  +h5 = {M11.le_add_r(Nat.add(nr, Nat.mul(kn, 5n)), 6n, tn, h_tu) : {Nat.is_le(Nat.add(nr, Nat.mul(kn, 5n)),
    tn) == True{} :
    Bool}}
  +h25 = {M1.le_rw_r(k2, Nat.mul(5n, kn), Nat.mul(kn, 5n), M1.mul_comm(5n, kn), M1.le_rw_l(Nat.mul(2n, kn), k2,
    Nat.mul(5n, kn), M1.mul_comm(2n, kn), M11.le_mul_mono(2n, 5n, kn, {==}))) : {Nat.is_le(k2, Nat.mul(kn,
        5n)) == True{} :
    Bool}}
  +h2 = {M1.le_trans(Nat.add(nr, k2), Nat.add(nr, Nat.mul(kn, 5n)), tn, M1.le_add_mono(nr, k2, Nat.mul(kn, 5n), h25),
    h5) :
    {Nat.is_le(Nat.add(nr, k2), tn) == True{} : Bool}}
  +e_m = {M7.u32_mul_below(kb, 2, tu, M10.le_add_l(nr, k2, tn, h2)) : {U32.to_nat((kb * 2 : U32)) == k2 : Nat}}
  +e_s = {Equal.trans(Nat, U32.to_nat(s1), Nat.add(U32.to_nat(nn), U32.to_nat((kb * 2 : U32))), Nat.add(nr, k2),
    M11.u32_add_below(nn, (kb * 2 : U32), tu, M1.le_rw_l(Nat.add(nr, k2), Nat.add(U32.to_nat(nn), U32.to_nat((kb * 2 :
    U32))), tn, Equal.trans(Nat, Nat.add(nr, k2), Nat.add(U32.to_nat(nn), k2), Nat.add(U32.to_nat(nn), U32.to_nat((kb *
    2 : U32))), Equal.cong(Nat, Nat, xx => Nat.add(xx, k2), nr, U32.to_nat(nn), Equal.sym(Nat, U32.to_nat(nn), nr, hn)),
    Equal.cong(Nat, Nat, xx => Nat.add(U32.to_nat(nn), xx), k2, U32.to_nat((kb * 2 : U32)), Equal.sym(Nat,
    U32.to_nat((kb * 2 : U32)), k2, e_m))), h2)), Equal.trans(Nat, Nat.add(U32.to_nat(nn), U32.to_nat((kb * 2 : U32))),
    Nat.add(nr, U32.to_nat((kb * 2 : U32))), Nat.add(nr, k2), Equal.cong(Nat, Nat, xx => Nat.add(xx,
      U32.to_nat((kb * 2 :
    U32))), U32.to_nat(nn), nr, hn), Equal.cong(Nat, Nat, xx => Nat.add(nr, xx), U32.to_nat((kb * 2 : U32)), k2,
      e_m))) :
    {U32.to_nat(s1) == Nat.add(nr, k2) : Nat}}
  +e_n = {Equal.trans(Nat, U32.to_nat(nn), 1n+U32.to_nat((nn - 1 : U32)), 1n+U32.to_nat((nn - 1 : U32)), M1.u32_dec(nn,
    nz), {==}) : {U32.to_nat(nn) == 1n+U32.to_nat((nn - 1 : U32)) : Nat}}
  +nz1 = {M1.u32_nonzero(s1, Nat.add(U32.to_nat((nn - 1 : U32)), k2), Equal.trans(Nat, U32.to_nat(s1), Nat.add(nr, k2),
    1n+Nat.add(U32.to_nat((nn - 1 : U32)), k2), e_s, Equal.cong(Nat, Nat, xx => Nat.add(xx, k2), nr, 1n+U32.to_nat((nn -
    1 : U32)), Equal.trans(Nat, nr, U32.to_nat(nn), 1n+U32.to_nat((nn - 1 : U32)), Equal.sym(Nat, U32.to_nat(nn), nr,
      hn),
    e_n)))) : {U32.is_zero(s1) == False{} : Bool}}
  +e_st = {Equal.sym(Nat, U32.to_nat(s1), 1n+U32.to_nat((s1 - 1 : U32)), M1.u32_dec(s1, nz1)) : {1n+U32.to_nat((s1 - 1
    : U32)) == U32.to_nat(s1) : Nat}}
  +e_l = {Equal.trans(Nat, Nat.add(Nat.add(nr, 0n), Nat.double(kn)), Nat.add(nr, Nat.double(kn)), Nat.add(nr, k2),
    Equal.cong(Nat, Nat, xx => Nat.add(xx, Nat.double(kn)), Nat.add(nr, 0n), nr, M1.ras.add_zero(nr)), Equal.cong(Nat,
        Nat,
    xx => Nat.add(nr, xx), Nat.double(kn), k2, Equal.sym(Nat, k2, Nat.double(kn), mul2(kn)))) :
    {Nat.add(Nat.add(nr, 0n), Nat.double(kn)) == Nat.add(nr, k2) : Nat}}
  M1.le_rw_r(Nat.add(Nat.add(nr, 0n), Nat.double(kn)), Nat.add(nr, k2), 1n+U32.to_nat((s1 - 1 : U32)), Equal.trans(Nat,
    Nat.add(nr, k2), U32.to_nat(s1), 1n+U32.to_nat((s1 - 1 : U32)), Equal.sym(Nat, U32.to_nat(s1), Nat.add(nr, k2),
      e_s),
    Equal.sym(Nat, 1n+U32.to_nat((s1 - 1 : U32)), U32.to_nat(s1), e_st)), M1.le_rw_l(Nat.add(nr, k2),
    Nat.add(Nat.add(nr, 0n), Nat.double(kn)), Nat.add(nr, k2), Equal.sym(Nat, Nat.add(Nat.add(nr, 0n), Nat.double(kn)),
    Nat.add(nr, k2), e_l), M1.le_refl(Nat.add(nr, k2))))

# the scanlines of a picture 1 + w' wide
def sco(+px: List<&2, U32>, +wp: Nat, +op: Bool) -> List<&2, U32>:
  M1.sc(px, 0n, 1n+wp, op)

# the IDAT data length the encoder writes for the raw bytes xs
def ilen(+xs: List<&2, U32>) -> U32:
  Png.enc.idat.ln(Png.enc.len(xs, 0))

# the zlib stream of xs in stored blocks of 65535 bytes
def zst(+xs: List<&2, U32>) -> List<&2, U32>:
  L1.zlib.stored(65535, xs)

# enc.wide.rgb after the signature and IHDR: the IDAT chunk holding the zlib
# stream of the scanlines in stored blocks of 65535 bytes, then IEND
def rgb.tail(
  +px: List<&2, U32>,
  +ww: U32,
  +wp: Nat,
  +mx: U32,
  +pm: U32,
  +tu: U32,
  +ie: List<&2, U32>,
  +emx: {mx == 65535 : U32},
  +epm: {pm == 65521 : U32},
  +ew: {U32.to_nat(ww) == 1n+wp : Nat},
  +hn: {U32.to_nat(Png.enc.len(sco(px, wp, True{}), 0)) == List.length(&2, U32, sco(px, wp, True{})) : Nat},
  +hbig: {U32.is_le(Png.enc.len(sco(px, wp, True{}), 0), 65535) == False{} : Bool},
  +hby: {D1.bytes(sco(px, wp, True{})) == True{} : Bool},
  +hl: {ilen(sco(px, wp, True{})) == Png.enc.len(zst(sco(px, wp, True{})), 0) : U32},
  +h_tu: {Nat.is_le(kzs(sco(px, wp, True{})), U32.to_nat(tu)) == True{} : Bool}
) -> {Png.enc.wide.rgb.go(Png.enc.crc.list(Png.enc.be(Png.tag.idat()), 4294967295,
  Png.enc.cat.go(Png.enc.be(Png.enc.idat.ln(Png.enc.len(M1.sc(px, 0n, 1n+wp, True{}), 0))), [])), px, ww,
  Png.enc.len(M1.sc(px, 0n, 1n+wp, True{}), 0), ie) == Png.enc.cat(Png.enc.chunk(Png.tag.idat(),
  L1.zlib.stored(65535, M1.sc(px, 0n, 1n+wp, True{}))), ie) : List<&2, U32>}:
  +raw = M1.sc(px, 0n, 1n+wp, True{})
  +nr = List.length(&2, U32, raw)
  +nn = Png.enc.len(raw, 0)
  +kn = U32.to_nat(Png.enc.nblk(nn))
  +ll = Png.enc.idat.ln(nn)
  +aa = Png.enc.cat.go(Png.enc.be(ll), [])
  +bi = Png.enc.be(Png.tag.idat())
  +c1 = Crc.crc.fold(bi, 4294967295)
  +a1 = List.reverse.go(&2, U32, bi, aa)
  +c2 = Crc.crc.fold([120, 1], c1)
  +a2 = List.reverse.go(&2, U32, [120, 1], a1)
  +steps = ((nn + (Png.enc.nblk(nn) * 2 : U32) : U32) - 1 : U32)
  +sum = Inf.adler.of(raw)
  +bb = M1.bs(raw, True{}, False{}, 0, nn, Png.enc.cap(nn), Png.enc.bf(nn))
  +bl = Png.enc.blocks(65535, raw)
  +e_b = {sim.blocks(raw, mx, emx, hn, hbig) : {bl == bb : List<&2, U32>}}
  +zz = L1.zlib.stored(65535, raw)
  +hl2 = {Equal.trans(U32, ll, Png.enc.len(zz, 0), Png.enc.len(M1.zb(bb, sum), 0), hl, Equal.cong(List<&2, U32>, U32,
      ys =>
    Png.enc.len(M1.zb(ys, sum), 0), bl, bb, e_b)) : {ll == Png.enc.len(M1.zb(bb, sum), 0) : U32}}
  +nz = {big.nz.at(U32.is_zero(nn), nn, {==}, hbig) : {U32.is_zero(nn) == False{} : Bool}}
  -go = Png.enc.rgb.go(U32.to_nat(steps), True{}, False{}, False{}, False{}, True{}, True{}, False{}, False{}, px, 0,
    ww,
    ww, 0, c2, a2, 1, 0, nn, 0)
  +e_go = {rg(U32.to_nat(steps), True{}, False{}, False{}, False{}, True{}, True{}, False{}, False{}, px, 0, ww, ww, 0,
    c2,
    a2, 1, 0, nn, 0, nn, 0, 0, kn, nr, wp, mx, emx, ew, M1.u32_nonzero(ww, wp, ew), _ef => {==}, ef =>
    Empty.absurd({True{} == False{} : Bool} -> {False{} == False{} : Bool} -> {False{} == U32.is_eq(ww, 1) : Bool},
    M1.false_true(Equal.sym(Bool, True{}, False{}, ef))), {==}, kok.rw(U32.to_nat(nn), nr, kn, U32.to_nat(mx), hn,
    nb.k(nn, mx, emx)), rgb.fuel(nn, tu, nr, hn, nz, h_tu), (Equal.sym(Bool, U32.is_zero(nn), False{},
      nz), hn)) : {go ==
    (M1.fr(bb, c2, a2), M1.afold(raw, 1, 0)) : (U32 & List<&2, U32>) & U32}}
  +e_fr = {Equal.trans(U32 & List<&2, U32>, M1.fr(bb, c2, a2), M1.fr(List.append(&2, U32, [120, 1], bb), c1, a1),
      M1.fr(M1.t0(bb),
    4294967295, aa), fr.app([120, 1], bb, c1, a1), fr.app(bi, List.append(&2, U32, [120, 1], bb), 4294967295, aa)) :
    {M1.fr(bb, c2, a2) == M1.fr(M1.t0(bb), 4294967295, aa) : U32 & List<&2, U32>}}
  Equal.trans(List<&2, U32>, Png.enc.wide.rgb.go(Png.enc.crc.list(bi, 4294967295, aa), px, ww, nn, ie),
    Png.enc.wide.rgb.go(M1.fr(bi, 4294967295, aa), px, ww, nn, ie), Png.enc.cat(Png.enc.chunk(Png.tag.idat(), zz), ie),
    Equal.cong(U32 & List<&2, U32>, List<&2, U32>, pp => Png.enc.wide.rgb.go(pp, px, ww, nn, ie), Png.enc.crc.list(bi,
      4294967295, aa), M1.fr(bi, 4294967295, aa), crcl(bi, 4294967295, aa)),
    Equal.trans(List<&2, U32>, Png.enc.wide.rgb.z(Png.enc.crc.list([120, 1], c1, a1), px, ww, nn, ie),
      Png.enc.wide.rgb.z(M1.fr([120, 1], c1, a1), px, ww, nn, ie), Png.enc.cat(Png.enc.chunk(Png.tag.idat(), zz), ie),
      Equal.cong(U32 & List<&2, U32>, List<&2, U32>, pp => Png.enc.wide.rgb.z(pp, px, ww, nn, ie),
        Png.enc.crc.list([120, 1], c1, a1), M1.fr([120, 1], c1, a1), crcl([120, 1], c1, a1)),
      Equal.trans(List<&2, U32>, Png.enc.wide.rgb.out(go, ie), Png.enc.wide.rgb.out((M1.fr(bb, c2, a2), M1.afold(raw,
          1, 0)),
        ie), Png.enc.cat(Png.enc.chunk(Png.tag.idat(), zz), ie),
        Equal.cong((U32 & List<&2, U32>) & U32, List<&2, U32>, gg => Png.enc.wide.rgb.out(gg, ie), go, (M1.fr(bb, c2,
            a2),
          M1.afold(raw, 1, 0)), e_go),
        Equal.trans(List<&2, U32>, Png.enc.seal.adler(M1.fr(bb, c2, a2), M1.afold(raw, 1, 0), ie),
          Png.enc.seal.adler(M1.fr(M1.t0(bb), 4294967295, aa), sum, ie), Png.enc.cat(Png.enc.chunk(Png.tag.idat(), zz),
              ie),
          Equal.trans(List<&2, U32>, Png.enc.seal.adler(M1.fr(bb, c2, a2), M1.afold(raw, 1, 0), ie),
            Png.enc.seal.adler(M1.fr(bb, c2, a2), sum, ie), Png.enc.seal.adler(M1.fr(M1.t0(bb), 4294967295, aa), sum,
                ie),
            Equal.cong(U32, List<&2, U32>, uu => Png.enc.seal.adler(M1.fr(bb, c2, a2), uu, ie), M1.afold(raw, 1, 0),
                sum,
              afold.adler(raw, pm, epm, hby)),
            Equal.cong(U32 & List<&2, U32>, List<&2, U32>, pp => Png.enc.seal.adler(pp, sum, ie), M1.fr(bb, c2, a2),
              M1.fr(M1.t0(bb), 4294967295, aa), e_fr)),
          Equal.trans(List<&2, U32>, Png.enc.seal.adler(M1.fr(M1.t0(bb), 4294967295, aa), sum, ie),
            Png.enc.cat(Png.enc.chunk(Png.tag.idat(), M1.zb(bb, sum)), ie), Png.enc.cat(Png.enc.chunk(Png.tag.idat(),
                zz),
            ie), tail.chunk(bb, sum, ll, ie, hl2), Equal.cong(List<&2, U32>, List<&2, U32>, ys =>
            Png.enc.cat(Png.enc.chunk(Png.tag.idat(), M1.zb(ys, sum)), ie), bb, bl, Equal.sym(List<&2, U32>, bl, bb,
            e_b)))))))

# the encoder's channel count is at most 4
def nch4(op: Bool) -> {Nat.is_le(Laws.spec.nch(op), 4n) == True{} : Bool}:
  match op:
    case True{}:
      {==}
    case False{}:
      {==}

# one row: 1 + w k is at most 5 w, for w above 0 and k at most 4
def row5(
  +wp: Nat,
  +kk: Nat,
  +hk: {Nat.is_le(kk, 4n) == True{} : Bool}
) -> {Nat.is_le(1n+Nat.mul(1n+wp, kk), Nat.mul(1n+wp, 5n)) == True{} : Bool}:
  M1.le_add_both(1n+kk, 5n, Nat.mul(wp, kk), Nat.mul(wp, 5n), hk, M1.ml.le(wp, kk, 5n, M1.le_trans(kk, 4n, 5n, hk,
      {==})))

# the scanline bytes are at most 5 w h
def scan5(
  hn: Nat,
  +wp: Nat,
  +kk: Nat,
  +hk: {Nat.is_le(kk, 4n) == True{} : Bool}
) -> {Nat.is_le(Nat.mul(hn, 1n+Nat.mul(1n+wp, kk)), Nat.mul(Nat.mul(hn, 1n+wp), 5n)) == True{} : Bool}:
  match hn:
    case 0n:
      {==}
    case 1n+(+hp):
      +bb = {1n+Nat.mul(1n+wp, kk) : Nat}
      +wn = {1n+wp : Nat}
      M1.le_rw_r(Nat.add(bb, Nat.mul(hp, bb)), Nat.add(Nat.mul(wn, 5n), Nat.mul(Nat.mul(hp, wn), 5n)),
        Nat.mul(Nat.add(wn, Nat.mul(hp, wn)), 5n), Equal.sym(Nat, Nat.mul(Nat.add(wn, Nat.mul(hp, wn)), 5n),
        Nat.add(Nat.mul(wn, 5n), Nat.mul(Nat.mul(hp, wn), 5n)), M1.mul_add(wn, Nat.mul(hp, wn), 5n)),
        M1.le_add_both(bb, Nat.mul(wn, 5n), Nat.mul(hp, bb), Nat.mul(Nat.mul(hp, wn), 5n), row5(wp, kk, hk),
        scan5(hp, wp, kk, hk)))

# 5 a is at most 8 a
def five.eight(+aa: Nat) -> {Nat.is_le(Nat.mul(aa, 5n), Nat.mul(8n, aa)) == True{} : Bool}:
  M1.le_rw_r(Nat.mul(aa, 5n), Nat.add(Nat.mul(5n, aa), Nat.mul(3n, aa)), Nat.mul(8n, aa), Equal.sym(Nat,
    Nat.mul(Nat.add(5n, 3n), aa), Nat.add(Nat.mul(5n, aa), Nat.mul(3n, aa)), M1.mul_add(5n, 3n, aa)),
    M1.le_rw_l(Nat.mul(5n, aa), Nat.mul(aa, 5n), Nat.add(Nat.mul(5n, aa), Nat.mul(3n, aa)), M1.mul_comm(5n, aa),
    M10.le_add_more(Nat.mul(5n, aa), Nat.mul(5n, aa), Nat.mul(3n, aa), M1.le_refl(Nat.mul(5n, aa)))))

# the IDAT data of the wide encodings fits in t, a word whose value is 8 a, when the scanlines are at most 5 a bytes
def tu.ok(
  +raw: List<&2, U32>,
  +mx: U32,
  +tu: U32,
  +aa: Nat,
  +emx: {mx == 65535 : U32},
  +hn: {U32.to_nat(Png.enc.len(raw, 0)) == List.length(&2, U32, raw) : Nat},
  +hbig: {U32.is_le(Png.enc.len(raw, 0), 65535) == False{} : Bool},
  +h5: {Nat.is_le(List.length(&2, U32, raw), Nat.mul(aa, 5n)) == True{} : Bool},
  +et: {U32.to_nat(tu) == Nat.mul(8n, aa) : Nat}
) -> {Nat.is_le(Nat.add(Nat.add(List.length(&2, U32, raw), Nat.mul(U32.to_nat(Png.enc.nblk(Png.enc.len(raw, 0))), 5n)),
  6n), U32.to_nat(tu)) == True{} : Bool}:
  +ll = Png.enc.len(raw, 0)
  +xn = U32.to_nat(ll)
  +ln = List.length(&2, U32, raw)
  +mn = U32.to_nat(mx)
  +kn = U32.to_nat(Png.enc.nblk(ll))
  +hm = {Equal.trans(Bool, Nat.is_le(25n, mn), U32.is_le(25, mx), True{}, Equal.sym(Bool, U32.is_le(25, mx),
    Nat.is_le(25n, mn), M10.u32_le(25, mx)), Equal.cong(U32, Bool, uu => U32.is_le(25, uu), mx, 65535, emx)) :
    {Nat.is_le(25n, mn) == True{} : Bool}}
  +hle = {Equal.trans(Bool, Nat.is_le(xn, mn), U32.is_le(ll, mx), False{}, Equal.sym(Bool, U32.is_le(ll, mx),
    Nat.is_le(xn, mn), M10.u32_le(ll, mx)), Equal.trans(Bool, U32.is_le(ll, mx), U32.is_le(ll, 65535), False{},
    Equal.cong(U32, Bool, uu => U32.is_le(ll, uu), mx, 65535, emx), hbig)) : {Nat.is_le(xn, mn) == False{} : Bool}}
  +h5x = {M1.le_rw_l(ln, xn, Nat.mul(aa, 5n), Equal.sym(Nat, xn, ln, hn), h5) : {Nat.is_le(xn, Nat.mul(aa, 5n)) ==
    True{} : Bool}}
  +k1 = {M1.kb(kn, xn, mn, aa, nb.k(ll, mx, emx), h5x, hm, nle.lt(xn, mn, hle)) : {Nat.is_le(Nat.add(Nat.add(xn,
    Nat.mul(kn, 5n)), 6n), Nat.mul(8n, aa)) == True{} : Bool}}
  M1.le_rw_r(Nat.add(Nat.add(ln, Nat.mul(kn, 5n)), 6n), Nat.mul(8n, aa), U32.to_nat(tu), Equal.sym(Nat, U32.to_nat(tu),
    Nat.mul(8n, aa), et), M1.le_rw_l(Nat.add(Nat.add(xn, Nat.mul(kn, 5n)), 6n), Nat.add(Nat.add(ln, Nat.mul(kn, 5n)),
    6n), Nat.mul(8n, aa), Equal.cong(Nat, Nat, zz => Nat.add(Nat.add(zz, Nat.mul(kn, 5n)), 6n), xn, ln, hn), k1))

# w k, taken in a word, does not wrap when h (1 + w k) is at most a word's value
def nb.em(
  +ww: U32,
  +op: Bool,
  +wp: Nat,
  +hp: Nat,
  +cap: U32,
  +e_w: {U32.to_nat(ww) == 1n+wp : Nat},
  +h_n: {Nat.is_le(Nat.mul(1n+hp, 1n+Nat.mul(1n+wp, Laws.spec.nch(op))), U32.to_nat(cap)) == True{} : Bool}
) -> {U32.to_nat(U32.mul(ww, Png.enc.nch(op))) == Nat.mul(U32.to_nat(ww), U32.to_nat(Png.enc.nch(op))) : Nat}:
  +kk = Laws.spec.nch(op)
  +wk = Nat.mul(1n+wp, kk)
  +cn = U32.to_nat(cap)
  +nc = Png.enc.nch(op)
  +h_y = {M11.le_add_r(1n+wk, Nat.mul(hp, 1n+wk), cn, h_n) : {Nat.is_le(1n+wk, cn) == True{} : Bool}}
  +h_wk = {M1.le_trans(wk, 1n+wk, cn, le.succ(wk), h_y) : {Nat.is_le(wk, cn) == True{} : Bool}}
  +e_m1n = {Equal.trans(Nat, Nat.mul(U32.to_nat(ww), U32.to_nat(nc)), Nat.mul(1n+wp, U32.to_nat(nc)), wk,
    Equal.cong(Nat, Nat, xx => Nat.mul(xx, U32.to_nat(nc)), U32.to_nat(ww), 1n+wp, e_w), Equal.cong(Nat, Nat, xx =>
    Nat.mul(1n+wp, xx), U32.to_nat(nc), kk, nch.val(op))) : {Nat.mul(U32.to_nat(ww), U32.to_nat(nc)) == wk : Nat}}
  M7.u32_mul_below(ww, nc, cap, M1.le_rw_l(wk, Nat.mul(U32.to_nat(ww), U32.to_nat(nc)), cn, Equal.sym(Nat,
    Nat.mul(U32.to_nat(ww), U32.to_nat(nc)), wk, e_m1n), h_wk))

# the filtered byte count, taken in a word, is h (1 + w k) when that is at most a word's value
def nb.val(
  +ww: U32,
  +hh: U32,
  +op: Bool,
  +wp: Nat,
  +hp: Nat,
  +cap: U32,
  +e_w: {U32.to_nat(ww) == 1n+wp : Nat},
  +e_h: {U32.to_nat(hh) == 1n+hp : Nat},
  +h_n: {Nat.is_le(Nat.mul(1n+hp, 1n+Nat.mul(1n+wp, Laws.spec.nch(op))), U32.to_nat(cap)) == True{} : Bool}
) -> {U32.to_nat(Png.enc.nbytes(op, ww, hh)) == Nat.mul(1n+hp, 1n+Nat.mul(1n+wp, Laws.spec.nch(op))) : Nat}:
  +kk = Laws.spec.nch(op)
  +wk = Nat.mul(1n+wp, kk)
  +nn = Nat.mul(1n+hp, 1n+wk)
  +cn = U32.to_nat(cap)
  +nc = Png.enc.nch(op)
  +m1 = U32.mul(ww, nc)
  +h_y = {M11.le_add_r(1n+wk, Nat.mul(hp, 1n+wk), cn, h_n) : {Nat.is_le(1n+wk, cn) == True{} : Bool}}
  +e_m1n = {Equal.trans(Nat, Nat.mul(U32.to_nat(ww), U32.to_nat(nc)), Nat.mul(1n+wp, U32.to_nat(nc)), wk,
    Equal.cong(Nat, Nat, xx => Nat.mul(xx, U32.to_nat(nc)), U32.to_nat(ww), 1n+wp, e_w), Equal.cong(Nat, Nat, xx =>
    Nat.mul(1n+wp, xx), U32.to_nat(nc), kk, nch.val(op))) : {Nat.mul(U32.to_nat(ww), U32.to_nat(nc)) == wk : Nat}}
  +t1 = {Equal.trans(Nat, U32.to_nat(m1), Nat.mul(U32.to_nat(ww), U32.to_nat(nc)), wk, nb.em(ww, op, wp, hp, cap, e_w,
    h_n), e_m1n) : {U32.to_nat(m1) == wk : Nat}}
  +x1 = U32.add(m1, 1)
  +e_x = {Equal.trans(Nat, Nat.add(U32.to_nat(m1), 1n), Nat.add(wk, 1n), 1n+wk, Equal.cong(Nat, Nat, xx => Nat.add(xx,
    1n), U32.to_nat(m1), wk, t1), add.one.nat(wk)) : {Nat.add(U32.to_nat(m1), 1n) == 1n+wk : Nat}}
  +t2 = {Equal.trans(Nat, U32.to_nat(x1), Nat.add(U32.to_nat(m1), 1n), 1n+wk, M11.u32_add_below(m1, 1, cap,
    M1.le_rw_l(1n+wk, Nat.add(U32.to_nat(m1), 1n), cn, Equal.sym(Nat, Nat.add(U32.to_nat(m1), 1n), 1n+wk, e_x), h_y)),
    e_x) : {U32.to_nat(x1) == 1n+wk : Nat}}
  +e_3 = {Equal.trans(Nat, Nat.mul(U32.to_nat(hh), U32.to_nat(x1)), Nat.mul(1n+hp, U32.to_nat(x1)), nn, Equal.cong(Nat,
    Nat, xx => Nat.mul(xx, U32.to_nat(x1)), U32.to_nat(hh), 1n+hp, e_h), Equal.cong(Nat, Nat, xx => Nat.mul(1n+hp, xx),
    U32.to_nat(x1), 1n+wk, t2)) : {Nat.mul(U32.to_nat(hh), U32.to_nat(x1)) == nn : Nat}}
  Equal.trans(Nat, U32.to_nat(U32.mul(hh, x1)), Nat.mul(U32.to_nat(hh), U32.to_nat(x1)), nn, M7.u32_mul_below(hh, x1,
    cap, M1.le_rw_l(nn, Nat.mul(U32.to_nat(hh), U32.to_nat(x1)), cn, Equal.sym(Nat, Nat.mul(U32.to_nat(hh),
    U32.to_nat(x1)), nn, e_3), h_n)), e_3)

# not at most: above
def gt.nle(cc: Cmp, +hh: {Cmp.is_le(cc) == False{} : Bool}) -> {Cmp.is_gt(cc) == True{} : Bool}:
  match cc:
    case LT{}:
      Empty.absurd({Cmp.is_gt(LT{}) == True{} : Bool}, M1.false_true(Equal.sym(Bool, True{}, False{}, hh)))
    case EQ{}:
      Empty.absurd({Cmp.is_gt(EQ{}) == True{} : Bool}, M1.false_true(Equal.sym(Bool, True{}, False{}, hh)))
    case GT{}:
      {==}

# the raw scanline list and its count, as the encoder builds them: the scanlines and their length
def raw.pair(
  +px: List<&2, U32>,
  +ww: U32,
  +wp: Nat,
  +op: Bool,
  +e_w: {U32.to_nat(ww) == 1n+wp : Nat}
) -> {Png.enc.raw(px, 0n, U32.to_nat(ww), op, [], 0) == (M1.sc(px, 0n, 1n+wp, op), Png.enc.len(M1.sc(px, 0n, 1n+wp,
  op), 0)) : List<&2, U32> & U32}:
  +ss = M1.sc(px, 0n, 1n+wp, op)
  +ll = Png.enc.len(ss, 0)
  +r0 = List.reverse(&2, U32, List.reverse.go(&2, U32, ss, []))
  +m0 = prt.cnt(px, 0n, 1n+wp, op, 0)
  +ls = List.length(&2, U32, ss)
  +e_m0 = {Equal.trans(U32, m0, U32.from_nat(ls), ll, cnt.word(px, 0n, 1n+wp, op, 0n), Equal.sym(U32, ll,
    U32.from_nat(ls), len.word(ss))) : {m0 == ll : U32}}
  Equal.trans(List<&2, U32> & U32, Png.enc.raw(px, 0n, U32.to_nat(ww), op, [], 0), Png.enc.raw(px, 0n, 1n+wp, op, [],
    0), (ss, ll),
    Equal.cong(Nat, List<&2, U32> & U32, kn => Png.enc.raw(px, 0n, kn, op, [], 0), U32.to_nat(ww), 1n+wp, e_w),
    Equal.trans(List<&2, U32> & U32, Png.enc.raw(px, 0n, 1n+wp, op, [], 0), (r0, m0), (ss, ll), raw.eq(px, 0n,
      1n+wp, op, [], 0),
      Equal.trans(List<&2, U32> & U32, (r0, m0), (ss, m0), (ss, ll),
        Equal.cong(List<&2, U32>, List<&2, U32> & U32, xs => (xs, m0), r0, ss, M1.inf.rev_rev(ss)),
        Equal.cong(U32, List<&2, U32> & U32, uu => (ss, uu), m0, ll, e_m0))))

# colour type 6 past one stored block: the wide layout is the one-block layout around the stored blocks of 65535
# bytes. Both sides are stated stuck on a flag, since the IHDR's CRC over a symbolic width and height is slow to
# normalise; the flags are rewritten to True and False only for the step that unfolds the layouts
def core.f(
  +zt: Bool,
  +zf: Bool,
  +ww: U32,
  +hh: U32,
  +ss: List<&2, U32>,
  +et: {zt == True{} : Bool},
  +ef: {zf == False{} : Bool},
  +hn: {U32.to_nat(Png.enc.len(ss, 0)) == List.length(&2, U32, ss) : Nat},
  +hbig: {U32.is_le(Png.enc.len(ss, 0), 65535) == False{} : Bool},
  +hl: {Png.enc.idat.ln(Png.enc.len(ss, 0)) == Png.enc.len(L1.zlib.stored(65535, ss), 0) : U32}
) -> {Png.enc.seal.at(zt, ww, hh, False{}, ss, Png.enc.len(ss, 0)) == Png.enc.seal.at(zf, ww, hh, False{}, ss,
  Png.enc.len(ss, 0)) : List<&2, U32>}:
  %Equal.sym(Bool, zt, True{}, et) : {Png.enc.seal.at(_, ww, hh, False{}, ss, Png.enc.len(ss, 0)) == Png.enc.seal.at(zf,
    ww, hh, False{}, ss, Png.enc.len(ss, 0)) : List<&2, U32>}
  %Equal.sym(Bool, zf, False{}, ef) : {Png.enc.seal.at(True{}, ww, hh, False{}, ss, Png.enc.len(ss, 0)) ==
    Png.enc.seal.at(_, ww, hh, False{}, ss, Png.enc.len(ss, 0)) : List<&2, U32>}
  Equal.cong(List<&2, U32>, List<&2, U32>, tl => Png.enc.cat(Png.enc.sig(), Png.enc.cat(Png.enc.chunk(Png.tag.ihdr(),
    Png.enc.ihdr(ww, hh, Png.enc.ct(False{}))), tl)),
    Png.enc.seal.body(Png.enc.crc.list(Png.enc.be(Png.tag.idat()), 4294967295,
    Png.enc.cat.go(Png.enc.be(Png.enc.idat.ln(Png.enc.len(ss, 0))), [])), ss, Png.enc.len(ss, 0), Inf.adler.of(ss),
    Png.enc.chunk(Png.tag.iend(), [])),
    Png.enc.cat(Png.enc.chunk(Png.tag.idat(), L1.zlib.stored(65535, ss)), Png.enc.chunk(Png.tag.iend(), [])),
    wide.tail(ss, 65535, Png.enc.chunk(Png.tag.iend(), []), {==}, hn, hbig, hl))

# colour type 2 past one stored block, written from the samples: the one-block layout around the stored blocks of
# 65535 bytes, stated stuck on flags as core.f is
def core.t(
  +zo: Bool,
  +zf: Bool,
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  +wp: Nat,
  +tu: U32,
  +eo: {zo == True{} : Bool},
  +ef: {zf == False{} : Bool},
  +e_w: {U32.to_nat(ww) == 1n+wp : Nat},
  +hn: {U32.to_nat(Png.enc.len(sco(px, wp, True{}), 0)) == List.length(&2, U32, sco(px, wp, True{})) : Nat},
  +hbig: {U32.is_le(Png.enc.len(sco(px, wp, True{}), 0), 65535) == False{} : Bool},
  +hby: {D1.bytes(sco(px, wp, True{})) == True{} : Bool},
  +h_tu: {Nat.is_le(kzs(sco(px, wp, True{})), U32.to_nat(tu)) == True{} : Bool}
) -> {Png.enc.paint.wide(zo, ww, hh, px, Png.enc.len(M1.sc(px, 0n, 1n+wp, True{}), 0)) == Png.enc.seal.at(zf, ww, hh,
  zo, M1.sc(px, 0n, 1n+wp, True{}), Png.enc.len(M1.sc(px, 0n, 1n+wp, True{}), 0)) : List<&2, U32>}:
  +ss = M1.sc(px, 0n, 1n+wp, True{})
  +ll = Png.enc.len(ss, 0)
  +ie = Png.enc.chunk(Png.tag.iend(), [])
  +hl = idat.len(ss, 65535, tu, {==}, hn, hbig, h_tu)
  %Equal.sym(Bool, zo, True{}, eo) : {Png.enc.paint.wide(_, ww, hh, px, ll) == Png.enc.seal.at(zf, ww, hh, _, ss, ll) :
    List<&2, U32>}
  %Equal.sym(Bool, zf, False{}, ef) : {Png.enc.paint.wide(True{}, ww, hh, px, ll) == Png.enc.seal.at(_, ww, hh, True{},
    ss, ll) : List<&2, U32>}
  Equal.cong(List<&2, U32>, List<&2, U32>, tl => Png.enc.cat(Png.enc.sig(), Png.enc.cat(Png.enc.chunk(Png.tag.ihdr(),
    Png.enc.ihdr(ww, hh, Png.enc.ct(True{}))), tl)),
    Png.enc.wide.rgb.go(Png.enc.crc.list(Png.enc.be(Png.tag.idat()), 4294967295,
    Png.enc.cat.go(Png.enc.be(Png.enc.idat.ln(ll)), [])), px, ww, ll, ie),
    Png.enc.cat(Png.enc.chunk(Png.tag.idat(), L1.zlib.stored(65535, ss)), ie),
    rgb.tail(px, ww, wp, 65535, 65521, tu, ie, {==}, {==}, e_w, hn, hbig, hby, hl, h_tu))

# the wide encodings, colour type 2 from the samples and colour type 6 from the raw list, are the one-block layout
# around the stored blocks of 65535 bytes. The layout is stated stuck on zf, which is False, and on zo, which is op
def wide.op(
  op: Bool,
  +zo: Bool,
  +zf: Bool,
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  +wp: Nat,
  +nb: U32,
  +tu: U32,
  +eo: {zo == op : Bool},
  +ef: {zf == False{} : Bool},
  +e_w: {U32.to_nat(ww) == 1n+wp : Nat},
  +e_nb: {nb == Png.enc.len(M1.sc(px, 0n, 1n+wp, op), 0) : U32},
  +hn: {U32.to_nat(Png.enc.len(sco(px, wp, op), 0)) == List.length(&2, U32, sco(px, wp, op)) : Nat},
  +hbig: {U32.is_le(Png.enc.len(sco(px, wp, op), 0), 65535) == False{} : Bool},
  +hby: {D1.bytes(sco(px, wp, op)) == True{} : Bool},
  +h_tu: {Nat.is_le(kzs(sco(px, wp, op)), U32.to_nat(tu)) == True{} : Bool}
) -> {Png.enc.paint.wide(zo, ww, hh, px, nb) == Png.enc.seal.at(zf, ww, hh, zo, M1.sc(px, 0n, 1n+wp, op),
  Png.enc.len(M1.sc(px, 0n, 1n+wp, op), 0)) : List<&2, U32>}:
  match op:
    case True{}:
      +ss = M1.sc(px, 0n, 1n+wp, True{})
      +ll = Png.enc.len(ss, 0)
      Equal.trans(List<&2, U32>, Png.enc.paint.wide(zo, ww, hh, px, nb), Png.enc.paint.wide(zo, ww, hh, px, ll),
        Png.enc.seal.at(zf, ww, hh, zo, ss, ll),
        Equal.cong(U32, List<&2, U32>, uu => Png.enc.paint.wide(zo, ww, hh, px, uu), nb, ll, e_nb),
        core.t(zo, zf, ww, hh, px, wp, tu, eo, ef, e_w, hn, hbig, hby, h_tu))
    case False{}:
      +ss = M1.sc(px, 0n, 1n+wp, False{})
      +ll = Png.enc.len(ss, 0)
      +hl = idat.len(ss, 65535, tu, {==}, hn, hbig, h_tu)
      +hg = {gt.nle(U32.cmp(ll, 65535), hbig) : {U32.is_gt(ll, 65535) == True{} : Bool}}
      %Equal.sym(Bool, zo, False{}, eo) : {Png.enc.paint.wide(_, ww, hh, px, nb) == Png.enc.seal.at(zf, ww, hh, _, ss,
        ll) : List<&2, U32>}
      Equal.trans(List<&2, U32>, Png.enc.paint.wide(False{}, ww, hh, px, nb), Png.enc.seal(ww, hh, False{}, (ss, ll)),
        Png.enc.seal.at(zf, ww, hh, False{}, ss, ll),
        Equal.cong(List<&2, U32> & U32, List<&2, U32>, pr => Png.enc.seal(ww, hh, False{}, pr), Png.enc.raw(px, 0n,
          U32.to_nat(ww), False{}, [], 0), (ss, ll), raw.pair(px, ww, wp, False{}, e_w)),
        core.f(U32.is_gt(ll, 65535), zf, ww, hh, ss, hg, ef, hn, hbig, hl))

# whether every sample is opaque, as the encoder asks
def opq(+px: List<&2, U32>) -> Bool:
  Png.enc.opaque(px, True{})

# the scanline byte count h (1 + w k), for 1 + h' rows of 1 + w' pixels of the encoder's channels
def snn(+hp: Nat, +wp: Nat, op: Bool) -> Nat:
  Nat.mul(1n+hp, 1n+Nat.mul(1n+wp, Laws.spec.nch(op)))

# a picture past one stored block: its encoding is the one-block layout around the stored blocks of 65535 bytes,
# the layout stated stuck on zf, which is False
def wide.rt(
  +zf: Bool,
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  +wp: Nat,
  +tu: U32,
  +ef: {zf == False{} : Bool},
  e_good: {Png.enc.good(ww, hh, px) == True{} : Bool},
  +e_w: {U32.to_nat(ww) == 1n+wp : Nat},
  +e_nb: {Png.enc.nbytes(opq(px), ww, hh) == Png.enc.len(sco(px, wp, opq(px)), 0) : U32},
  +hn: {U32.to_nat(Png.enc.len(sco(px, wp, opq(px)), 0)) == List.length(&2, U32, sco(px, wp, opq(px))) : Nat},
  +hbig: {U32.is_le(Png.enc.len(sco(px, wp, opq(px)), 0), 65535) == False{} : Bool},
  +hby: {D1.bytes(sco(px, wp, opq(px))) == True{} : Bool},
  +h_tu: {Nat.is_le(kzs(sco(px, wp, opq(px))), U32.to_nat(tu)) == True{} : Bool}
) -> {Png.enc.open(Png.enc.good(ww, hh, px), ww, hh, px) == Some{Png.enc.seal.at(zf, ww, hh, Png.enc.opaque(px,
  True{}), M1.sc(px, 0n, 1n+wp, Png.enc.opaque(px, True{})), Png.enc.len(M1.sc(px, 0n, 1n+wp, Png.enc.opaque(px,
  True{})), 0))} : Maybe<&2, List<&2, U32>>}:
  +op = Png.enc.opaque(px, True{})
  +nb = Png.enc.nbytes(op, ww, hh)
  +ss = M1.sc(px, 0n, 1n+wp, op)
  +ll = Png.enc.len(ss, 0)
  +so = Png.enc.seal.at(zf, ww, hh, op, ss, ll)
  +hg = {Equal.trans(Bool, U32.is_gt(nb, 65535), U32.is_gt(ll, 65535), True{}, Equal.cong(U32, Bool, uu =>
    U32.is_gt(uu, 65535), nb, ll, e_nb), gt.nle(U32.cmp(ll, 65535), hbig)) : {U32.is_gt(nb, 65535) == True{} : Bool}}
  Equal.trans(Maybe<&2, List<&2, U32>>, Png.enc.open(Png.enc.good(ww, hh, px), ww, hh, px), Png.enc.open(True{}, ww,
    hh, px), Some{so},
    Equal.cong(Bool, Maybe<&2, List<&2, U32>>, zb => Png.enc.open(zb, ww, hh, px), Png.enc.good(ww, hh, px), True{},
      e_good),
    Equal.trans(Maybe<&2, List<&2, U32>>, Png.enc.open(True{}, ww, hh, px), Some{Png.enc.paint.at(True{}, ww, hh, op,
      px, nb)}, Some{so},
      Equal.cong(Bool, Maybe<&2, List<&2, U32>>, zb => Some{Png.enc.paint.at(zb, ww, hh, op, px, nb)}, U32.is_gt(nb,
        65535), True{}, hg),
      Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, xs => Some{xs}, Png.enc.paint.wide(op, ww, hh, px, nb), so,
        wide.op(op, op, zf, ww, hh, px, wp, nb, tu, {==}, ef, e_w, e_nb, hn, hbig, hby, h_tu))))

# laws/PngRoundTrips.bend for one stored block. The guard enc.good passed, since png_encodes says the encoding is some
def rt.good.at(
  zz: Bool,
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  hs: {Maybe.is_some(&2, List<&2, U32>, Png.enc.open(zz, ww, hh, px)) == True{} : Bool}
) -> {zz == True{} : Bool}:
  match zz:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, M1.false_true(hs))

# the colour type the encoder writes is one the decoder reads
def rt.col(op: Bool) -> {D1.spec.colour.ok(Png.enc.ct(op)) == True{} : Bool}:
  match op:
    case True{}:
      {==}
    case False{}:
      {==}

# the encoder's colour types need no PLTE
def rt.plte(op: Bool) -> {D1.spec.plte.ok(Png.enc.ct(op), None{}) == True{} : Bool}:
  match op:
    case True{}:
      {==}
    case False{}:
      {==}

# the bytes per pixel are 1 to 4
def rt.bpp(
  op: Bool
) -> {Bool.and(U32.is_gt(Png.png.bpp(Png.enc.ct(op)), 0), U32.is_le(Png.png.bpp(Png.enc.ct(op)), 4)) == True{} : Bool}:
  match op:
    case True{}:
      {==}
    case False{}:
      {==}

# the sizes unfilter reads
def rt.dims(
  +ww: U32,
  +hh: U32,
  +op: Bool,
  h_ww: {U32.is_gt(ww, 0) == True{} : Bool},
  h_hh: {U32.is_gt(hh, 0) == True{} : Bool}
) -> {L4.flt.dims(ww, hh, Png.png.bpp(Png.enc.ct(op))) == True{} : Bool}:
  +bp = Png.png.bpp(Png.enc.ct(op))
  %Equal.sym(Bool, U32.is_gt(ww, 0), True{}, h_ww) : {Bool.and(_, Bool.and(U32.is_gt(hh, 0), Bool.and(U32.is_gt(bp, 0),
    U32.is_le(bp, 4)))) == True{} : Bool}
  %Equal.sym(Bool, U32.is_gt(hh, 0), True{}, h_hh) : {Bool.and(True{}, Bool.and(_, Bool.and(U32.is_gt(bp, 0),
    U32.is_le(bp, 4)))) == True{} : Bool}
  rt.bpp(op)

# the row width in bytes does not wrap: bpp is the channel count
def rt.wrap(
  +ww: U32,
  +op: Bool,
  e_m: {U32.to_nat(U32.mul(ww, Png.enc.nch(op))) == Nat.mul(U32.to_nat(ww), U32.to_nat(Png.enc.nch(op))) : Nat}
) -> {U32.to_nat(U32.mul(ww, Png.png.bpp(Png.enc.ct(op)))) == Nat.mul(U32.to_nat(ww), U32.to_nat(Png.png.bpp(
  Png.enc.ct(op)))) : Nat}:
  %Equal.sym(U32, Png.png.bpp(Png.enc.ct(op)), Png.enc.nch(op), bpp.eq(op)) : {U32.to_nat(U32.mul(ww, _)) ==
    Nat.mul(U32.to_nat(ww), U32.to_nat(_)) : Nat}
  e_m

# the samples px.of packs from the channels are the raster's
def rt.pix(
  op: Bool,
  +px: List<&2, U32>,
  hao: {D1.all_opaque(px) == op : Bool}
) -> {Png.px.of(Png.enc.ct(op), chans.all(op, px), [], []) == Some{px} : Maybe<&2, List<&2, U32>>}:
  match op:
    case True{}:
      Equal.trans(Maybe<&2, List<&2, U32>>, Png.px.of(2, chans.all(True{}, px), [], []),
        L3.spec.rgb(chans.all(True{}, px)), Some{px}, L3.png_px_rgb(chans.all(True{}, px), []),
        rgb.back(px, hao))
    case False{}:
      Equal.trans(Maybe<&2, List<&2, U32>>, Png.px.of(6, chans.all(False{}, px), [], []),
        L3.spec.rgba(chans.all(False{}, px)), Some{px}, L3.png_px_rgba(chans.all(False{}, px), []),
        rgba.back(px))

# a true sample-count check keeps the raster
def rt.keep.at(
  ok: Bool,
  eo: {ok == True{} : Bool},
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>
) -> {D1.spec.raster.keep(ok, ww, hh, px) == Some{Img.raster(ww, hh, px)} : Maybe<&2, Img.Raster>}:
  match ok:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({D1.spec.raster.keep(False{}, ww, hh, px) == Some{Img.raster(ww, hh, px)}
        : Maybe<&2, Img.Raster>}, M1.false_true(eo))

# the round trip's raster has h * w samples, so spec.raster keeps it
def rt.keep(
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  +wp: Nat,
  +hp: Nat,
  +e_w: {U32.to_nat(ww) == 1n+wp : Nat},
  +e_h: {U32.to_nat(hh) == 1n+hp : Nat},
  +hl: {List.length(&2, U32, px) == Nat.mul(1n+hp, 1n+wp) : Nat}
) -> {D1.spec.raster(Some{px}, ww, hh) == Some{Img.raster(ww, hh, px)} : Maybe<&2, Img.Raster>}:
  +area = Nat.mul(U32.to_nat(hh), U32.to_nat(ww))
  +nb = Nat.mul(1n+hp, 1n+wp)
  +e_a = {Equal.trans(Nat, area, Nat.mul(1n+hp, U32.to_nat(ww)), nb,
    Equal.cong(Nat, Nat, kk => Nat.mul(kk, U32.to_nat(ww)), U32.to_nat(hh), 1n+hp, e_h),
    Equal.cong(Nat, Nat, kk => Nat.mul(1n+hp, kk), U32.to_nat(ww), 1n+wp, e_w)) : {area == nb : Nat}}
  +e_ok = {Equal.trans(Bool, Nat.is_eq(List.length(&2, U32, px), area), Nat.is_eq(nb, area), True{},
    Equal.cong(Nat, Bool, kk => Nat.is_eq(kk, area), List.length(&2, U32, px), nb, hl),
    Equal.trans(Bool, Nat.is_eq(nb, area), Nat.is_eq(nb, nb), True{},
      Equal.cong(Nat, Bool, kk => Nat.is_eq(nb, kk), area, nb, e_a), M1.nat_eq_refl(nb)))
    : {Nat.is_eq(List.length(&2, U32, px), area) == True{} : Bool}}
  rt.keep.at(Nat.is_eq(List.length(&2, U32, px), area), e_ok, ww, hh, px)

# the pixel stage: the scanlines unfilter to the rows, and the rows pack to the samples
def rt.px(
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  +op: Bool,
  +wp: Nat,
  +hp: Nat,
  hao: {D1.all_opaque(px) == op : Bool},
  +e_w: {U32.to_nat(ww) == 1n+wp : Nat},
  +e_h: {U32.to_nat(hh) == 1n+hp : Nat},
  +hl: {List.length(&2, U32, px) == Nat.mul(1n+hp, 1n+wp) : Nat},
  e_m: {U32.to_nat(U32.mul(ww, Png.enc.nch(op))) == Nat.mul(U32.to_nat(ww), U32.to_nat(Png.enc.nch(op))) : Nat}
) -> {D1.spec.decoded(Some{M1.sc(px, 0n, 1n+wp, op)}, ww, hh, Png.enc.ct(op), [], []) == Some{Img.raster(ww, hh,
  px)} : Maybe<&2, Img.Raster>}:
  +ww1 = {1n+wp : Nat}
  +hh1 = {1n+hp : Nat}
  +ct = Png.enc.ct(op)
  +bp = Png.png.bpp(ct)
  +rows = rows.of(hh1, ww1, op, px)
  +ss = M1.sc(px, 0n, ww1, op)
  +fr = L4.flt.rows(rows, L4.FNone{}, bp, [])
  +e_s = {Equal.trans(List<&2, U32>, ss, M1.scan(rows), fr, sc.rows(hh1, wp, op, px, hl), Equal.sym(List<&2, U32>,
    fr, M1.scan(rows), frows(rows, bp, [], masked.rows.of(hh1, ww1, op, px)))) : {ss == fr : List<&2, U32>}}
  +h_ww = gt.pos(ww, wp, e_w)
  +h_hh = gt.pos(hh, hp, e_h)
  +h_rows = {Equal.trans(Nat, List.length(&2, List<&2, U32>, rows), hh1, U32.to_nat(hh), rows.len(hh1, ww1, op, px),
    Equal.sym(Nat, U32.to_nat(hh), hh1, e_h)) : {List.length(&2, List<&2, U32>, rows) == U32.to_nat(hh) : Nat}}
  +e_nb = {Equal.trans(Nat, Nat.mul(U32.to_nat(ww), U32.to_nat(bp)), Nat.mul(ww1, U32.to_nat(bp)), Nat.mul(ww1,
    Laws.spec.nch(op)), Equal.cong(Nat, Nat, kk => Nat.mul(kk, U32.to_nat(bp)), U32.to_nat(ww), ww1, e_w),
    Equal.trans(Nat, Nat.mul(ww1, U32.to_nat(bp)), Nat.mul(ww1, U32.to_nat(Png.enc.nch(op))), Nat.mul(ww1,
    Laws.spec.nch(op)), Equal.cong(U32, Nat, uu => Nat.mul(ww1, U32.to_nat(uu)), bp, Png.enc.nch(op), bpp.eq(op)),
    Equal.cong(Nat, Nat, kk => Nat.mul(ww1, kk), U32.to_nat(Png.enc.nch(op)), Laws.spec.nch(op), nch.val(op)))) :
    {Nat.mul(U32.to_nat(ww), U32.to_nat(bp)) == Nat.mul(ww1, Laws.spec.nch(op)) : Nat}}
  +h_fit = {Equal.trans(Bool, L4.flt.fit(rows, Nat.mul(U32.to_nat(ww), U32.to_nat(bp)), True{}),
    L4.flt.fit(rows, Nat.mul(ww1, Laws.spec.nch(op)), True{}), True{}, Equal.cong(Nat, Bool, kk => L4.flt.fit(rows,
    kk, True{}), Nat.mul(U32.to_nat(ww), U32.to_nat(bp)), Nat.mul(ww1, Laws.spec.nch(op)), e_nb), fit.rows(hh1, ww1,
    op, px, hl)) : {L4.flt.fit(rows, Nat.mul(U32.to_nat(ww), U32.to_nat(bp)), True{}) == True{} : Bool}}
  +e_un = {L4.unfilter_filter(L4.FNone{}, ww, hh, bp, rows, rt.dims(ww, hh, op, h_ww, h_hh), rt.wrap(ww, op, e_m),
    h_rows, h_fit) : {Png.unfilter(fr, ww, hh, bp) == Some{List.concat(&2, U32, rows)} : Maybe<&2, List<&2, U32>>}}
  +e_cat = {rows.cat(hh1, ww1, op, px, hl) : {List.concat(&2, U32, rows) == chans.all(op, px) : List<&2, U32>}}
  Equal.trans(Maybe<&2, Img.Raster>,
    D1.spec.raster(D1.spec.px.then(Png.unfilter(ss, ww, hh, bp), ct, [], []), ww, hh),
    D1.spec.raster(D1.spec.px.then(Some{chans.all(op, px)}, ct, [], []), ww, hh),
    Some{Img.raster(ww, hh, px)},
    Equal.cong(Maybe<&2, List<&2, U32>>, Maybe<&2, Img.Raster>, mm => D1.spec.raster(D1.spec.px.then(mm, ct, [],
      []), ww, hh), Png.unfilter(ss, ww, hh, bp), Some{chans.all(op, px)},
      Equal.trans(Maybe<&2, List<&2, U32>>, Png.unfilter(ss, ww, hh, bp), Png.unfilter(fr, ww, hh, bp),
        Some{chans.all(op, px)},
        Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, xs => Png.unfilter(xs, ww, hh, bp), ss, fr, e_s),
        Equal.trans(Maybe<&2, List<&2, U32>>, Png.unfilter(fr, ww, hh, bp), Some{List.concat(&2, U32, rows)},
          Some{chans.all(op, px)}, e_un, Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, xs => Some{xs},
          List.concat(&2, U32, rows), chans.all(op, px), e_cat)))),
    Equal.trans(Maybe<&2, Img.Raster>, D1.spec.raster(Png.px.of(ct, chans.all(op, px), [], []), ww, hh),
      D1.spec.raster(Some{px}, ww, hh), Some{Img.raster(ww, hh, px)},
      Equal.cong(Maybe<&2, List<&2, U32>>, Maybe<&2, Img.Raster>, mm => D1.spec.raster(mm, ww, hh),
        Png.px.of(ct, chans.all(op, px), [], []), Some{px}, rt.pix(op, px, hao)),
      rt.keep(ww, hh, px, wp, hp, e_w, e_h, hl)))

# the pixel stage after the layout: the one-block layout around any zlib stream of the scanlines that inflates to
# them decodes to the raster. The layout is stated stuck on zb, which is False
def rt.tail(
  +zb: Bool,
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  +op: Bool,
  +wp: Nat,
  +hp: Nat,
  +ez: {zb == False{} : Bool},
  hao: {D1.all_opaque(px) == op : Bool},
  +e_w: {U32.to_nat(ww) == 1n+wp : Nat},
  +e_h: {U32.to_nat(hh) == 1n+hp : Nat},
  +hl: {List.length(&2, U32, px) == Nat.mul(1n+hp, 1n+wp) : Nat},
  e_m: {U32.to_nat(U32.mul(ww, Png.enc.nch(op))) == Nat.mul(U32.to_nat(ww), U32.to_nat(Png.enc.nch(op))) : Nat},
  h_fz: D1.spec.fits(Png.enc.zlib(M1.sc(px, 0n, 1n+wp, op), Png.enc.len(M1.sc(px, 0n, 1n+wp, op), 0))),
  +h_nl: {U32.to_nat(Png.enc.len(M1.sc(px, 0n, 1n+wp, op), 0)) == List.length(&2, U32, M1.sc(px, 0n, 1n+wp, op)) : Nat}
) -> {Img.decode_png(Png.enc.seal.at(zb, ww, hh, op, M1.sc(px, 0n, 1n+wp, op), Png.enc.len(M1.sc(px, 0n, 1n+wp, op),
  0))) == Some{Img.raster(ww, hh, px)} : Maybe<&2, Img.Raster>}:
  +ww1 = {1n+wp : Nat}
  +hh1 = {1n+hp : Nat}
  +ss = M1.sc(px, 0n, ww1, op)
  +rows = rows.of(hh1, ww1, op, px)
  +ll = Png.enc.len(ss, 0)
  +zz = Png.enc.zlib(ss, ll)
  +e_s = {sc.rows(hh1, wp, op, px, hl) : {ss == M1.scan(rows) : List<&2, U32>}}
  +h_by = {Equal.trans(Bool, D1.bytes(ss), D1.bytes.go(M1.scan(rows), True{}), True{}, Equal.cong(List<&2, U32>,
    Bool, xs => D1.bytes.go(xs, True{}), ss, M1.scan(rows), e_s), bytes.scan(rows, masked.rows.of(hh1, ww1, op,
    px))) : {D1.bytes(ss) == True{} : Bool}}
  +e_inf = {L1.inflate_enc_zlib(ss, h_by, h_nl) : {Inf.inflate(zz) == Some{ss} : Maybe<&2, List<&2, U32>>}}
  +ct = Png.enc.ct(op)
  +h_ww = gt.pos(ww, wp, e_w)
  +h_hh = gt.pos(hh, hp, e_h)
  +a6 = Img.decode_png(Png.enc.seal.at(zb, ww, hh, op, ss, ll))
  +a8 = Img.decode_png(D1.spec.png(ww, hh, ct, None{}, None{}, [zz]))
  +a9 = D1.spec.decoded(Inf.inflate(List.concat(&2, U32, [zz])), ww, hh, ct, [], [])
  +a10 = D1.spec.decoded(Some{ss}, ww, hh, ct, [], [])
  Equal.trans(Maybe<&2, Img.Raster>, a6, a8, Some{Img.raster(ww, hh, px)},
    Equal.trans(Maybe<&2, Img.Raster>, a6, Img.decode_png(Png.enc.seal.one(ww, hh, op, ss, ll)), a8,
      Equal.cong(Bool, Maybe<&2, Img.Raster>, zc => Img.decode_png(Png.enc.seal.at(zc, ww, hh, op, ss, ll)),
        zb, False{}, ez),
      Equal.cong(List<&2, U32>, Maybe<&2, Img.Raster>, xs => Img.decode_png(xs), Png.enc.seal.one(ww, hh, op, ss,
        ll), D1.spec.png(ww, hh, ct, None{}, None{}, [zz]), seal.one.same(ww, hh, op, ss, ll))),
    Equal.trans(Maybe<&2, Img.Raster>, a8, a9, Some{Img.raster(ww, hh, px)},
      L3.png_walk(ww, hh, ct, None{}, None{}, [zz], h_ww, h_hh, rt.col(op), rt.plte(op), {==}, Unit{}, Unit{},
        (h_fz, Unit{})),
      Equal.trans(Maybe<&2, Img.Raster>, a9, D1.spec.decoded(Inf.inflate(zz), ww, hh, ct, [], []),
        Some{Img.raster(ww, hh, px)},
        Equal.cong(List<&2, U32>, Maybe<&2, Img.Raster>, xs => D1.spec.decoded(Inf.inflate(xs), ww, hh, ct, [],
          []), List.append(&2, U32, zz, []), zz, M1.app_nil(zz)),
        Equal.trans(Maybe<&2, Img.Raster>, D1.spec.decoded(Inf.inflate(zz), ww, hh, ct, [], []), a10,
          Some{Img.raster(ww, hh, px)},
          Equal.cong(Maybe<&2, List<&2, U32>>, Maybe<&2, Img.Raster>, mm => D1.spec.decoded(mm, ww, hh, ct, [],
            []), Inf.inflate(zz), Some{ss}, e_inf),
          rt.px(ww, hh, px, op, wp, hp, hao, e_w, e_h, hl, e_m)))))

# the one-block round trip, with the width and height 1 + w' and 1 + h', and
# op whether every sample is opaque
def rt.go(
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  +nb: U32,
  +op: Bool,
  +wp: Nat,
  +hp: Nat,
  e_op: {Png.enc.opaque(px, True{}) == op : Bool},
  hao: {D1.all_opaque(px) == op : Bool},
  e_good: {Png.enc.good(ww, hh, px) == True{} : Bool},
  +e_w: {U32.to_nat(ww) == 1n+wp : Nat},
  +e_h: {U32.to_nat(hh) == 1n+hp : Nat},
  +hl: {List.length(&2, U32, px) == Nat.mul(1n+hp, 1n+wp) : Nat},
  h_nb: {U32.to_nat(nb) == Nat.mul(1n+hp, 1n+Nat.mul(1n+wp, Laws.spec.nch(op))) : Nat},
  h_one: {U32.is_le(nb, 65535) == True{} : Bool},
  +cap: U32,
  +cap2: U32,
  +ec: {cap == 65535 : U32},
  hc: {Nat.is_le(11n+U32.to_nat(cap), U32.to_nat(cap2)) == True{} : Bool}
) -> {Laws.spec.png.back(Img.encode_png(Img.raster(ww, hh, px))) == Some{Img.raster(ww, hh, px)} :
  Maybe<&2, Img.Raster>}:
  +ww1 = {1n+wp : Nat}
  +hh1 = {1n+hp : Nat}
  +kk = Laws.spec.nch(op)
  +wk = Nat.mul(ww1, kk)
  +nn = Nat.mul(hh1, 1n+wk)
  +cn = U32.to_nat(cap)
  +h_oc = {Equal.trans(Bool, U32.is_le(nb, cap), U32.is_le(nb, 65535), True{}, Equal.cong(U32, Bool, cu => U32.is_le(nb,
    cu), cap, 65535, ec), h_one) : {U32.is_le(nb, cap) == True{} : Bool}}
  +h_n = {Equal.trans(Bool, Nat.is_le(nn, cn), Nat.is_le(U32.to_nat(nb), cn), True{}, Equal.cong(Nat, Bool, xx =>
    Nat.is_le(xx, cn), nn, U32.to_nat(nb), Equal.sym(Nat, U32.to_nat(nb), nn, h_nb)), Equal.trans(Bool,
    Nat.is_le(U32.to_nat(nb), cn), U32.is_le(nb, cap), True{}, Equal.sym(Bool, U32.is_le(nb, cap),
    Nat.is_le(U32.to_nat(nb), cn), M8.u_le(nb, cap)), h_oc)) : {Nat.is_le(nn, cn) == True{} : Bool}}
  +h_y = {M11.le_add_r(1n+wk, Nat.mul(hp, 1n+wk), cn, h_n) : {Nat.is_le(1n+wk, cn) == True{} : Bool}}
  +h_wk = {M1.le_trans(wk, 1n+wk, cn, le.succ(wk), h_y) : {Nat.is_le(wk, cn) == True{} : Bool}}
  +nc = Png.enc.nch(op)
  +m1 = U32.mul(ww, nc)
  +e_m1n = {Equal.trans(Nat, Nat.mul(U32.to_nat(ww), U32.to_nat(nc)), Nat.mul(ww1, U32.to_nat(nc)), wk,
    Equal.cong(Nat, Nat, xx => Nat.mul(xx, U32.to_nat(nc)), U32.to_nat(ww), ww1, e_w), Equal.cong(Nat, Nat, xx =>
    Nat.mul(ww1, xx), U32.to_nat(nc), kk, nch.val(op))) : {Nat.mul(U32.to_nat(ww), U32.to_nat(nc)) == wk : Nat}}
  +e_m = {M7.u32_mul_below(ww, nc, cap, M1.le_rw_l(wk, Nat.mul(U32.to_nat(ww), U32.to_nat(nc)), cn, Equal.sym(Nat,
    Nat.mul(U32.to_nat(ww), U32.to_nat(nc)), wk, e_m1n), h_wk)) : {U32.to_nat(m1) == Nat.mul(U32.to_nat(ww),
    U32.to_nat(nc)) : Nat}}
  +t1 = {Equal.trans(Nat, U32.to_nat(m1), Nat.mul(U32.to_nat(ww), U32.to_nat(nc)), wk, e_m, e_m1n) : {U32.to_nat(m1) ==
    wk : Nat}}
  +x1 = U32.add(m1, 1)
  +e_x = {Equal.trans(Nat, Nat.add(U32.to_nat(m1), 1n), Nat.add(wk, 1n), 1n+wk, Equal.cong(Nat, Nat, xx => Nat.add(xx,
    1n), U32.to_nat(m1), wk, t1), add.one.nat(wk)) : {Nat.add(U32.to_nat(m1), 1n) == 1n+wk : Nat}}
  +t2 = {Equal.trans(Nat, U32.to_nat(x1), Nat.add(U32.to_nat(m1), 1n), 1n+wk, M11.u32_add_below(m1, 1, cap,
    M1.le_rw_l(1n+wk, Nat.add(U32.to_nat(m1), 1n), cn, Equal.sym(Nat, Nat.add(U32.to_nat(m1), 1n), 1n+wk, e_x), h_y)),
    e_x) : {U32.to_nat(x1) == 1n+wk : Nat}}
  +n_b = U32.mul(hh, x1)
  +e_3 = {Equal.trans(Nat, Nat.mul(U32.to_nat(hh), U32.to_nat(x1)), Nat.mul(hh1, U32.to_nat(x1)), nn, Equal.cong(Nat,
    Nat, xx => Nat.mul(xx, U32.to_nat(x1)), U32.to_nat(hh), hh1, e_h), Equal.cong(Nat, Nat, xx => Nat.mul(hh1, xx),
    U32.to_nat(x1), 1n+wk, t2)) : {Nat.mul(U32.to_nat(hh), U32.to_nat(x1)) == nn : Nat}}
  +t3 = {Equal.trans(Nat, U32.to_nat(n_b), Nat.mul(U32.to_nat(hh), U32.to_nat(x1)), nn, M7.u32_mul_below(hh, x1, cap,
    M1.le_rw_l(nn, Nat.mul(U32.to_nat(hh), U32.to_nat(x1)), cn, Equal.sym(Nat, Nat.mul(U32.to_nat(hh), U32.to_nat(x1)),
    nn, e_3), h_n)), e_3) : {U32.to_nat(n_b) == nn : Nat}}
  +ss = M1.sc(px, 0n, ww1, op)
  +rows = rows.of(hh1, ww1, op, px)
  +ls = List.length(&2, U32, ss)
  +e_s = {sc.rows(hh1, wp, op, px, hl) : {ss == M1.scan(rows) : List<&2, U32>}}
  +e_ls = {Equal.trans(Nat, ls, List.length(&2, U32, M1.scan(rows)), nn, Equal.cong(List<&2, U32>, Nat, xs =>
    List.length(&2, U32, xs), ss, M1.scan(rows), e_s), len.scan(hh1, ww1, op, px, hl)) : {ls == nn : Nat}}
  +h_ls = {M1.le_rw_l(nn, ls, cn, Equal.sym(Nat, ls, nn, e_ls), h_n) : {Nat.is_le(ls, cn) == True{} : Bool}}
  +ll = Png.enc.len(ss, 0)
  +t_l = {Equal.trans(Nat, U32.to_nat(ll), U32.to_nat(U32.from_nat(ls)), nn, Equal.cong(U32, Nat, uu => U32.to_nat(uu),
    ll, U32.from_nat(ls), len.word(ss)), Equal.trans(Nat, U32.to_nat(U32.from_nat(ls)), ls, nn, nat.fits(ls,
    cap, h_ls), e_ls)) : {U32.to_nat(ll) == nn : Nat}}
  +r0 = List.reverse(&2, U32, List.reverse.go(&2, U32, ss, []))
  +m0 = prt.cnt(px, 0n, ww1, op, 0)
  +e_m0 = {Equal.trans(U32, m0, U32.from_nat(ls), ll, cnt.word(px, 0n, ww1, op, 0n), Equal.sym(U32, ll,
    U32.from_nat(ls), len.word(ss))) : {m0 == ll : U32}}
  +zz = Png.enc.zlib(ss, ll)
  +le_l = {Equal.trans(Bool, U32.is_le(ll, 65535), U32.is_le(ll, cap), True{}, Equal.cong(U32, Bool, cu => U32.is_le(ll,
    cu), 65535, cap, Equal.sym(U32, cap, 65535, ec)), le.yes(ll, cap, nn, t_l, h_n)) : {U32.is_le(ll,
    65535) == True{} : Bool}}
  +f_nb = {Equal.trans(Bool, U32.is_gt(n_b, 65535), U32.is_gt(n_b, cap), False{}, Equal.cong(U32, Bool, cu =>
    U32.is_gt(n_b, cu), 65535, cap, Equal.sym(U32, cap, 65535, ec)), gt.no(n_b, cap, nn, t3, h_n)) :
    {U32.is_gt(n_b, 65535) == False{} : Bool}}
  +f_ll = {Equal.trans(Bool, U32.is_gt(ll, 65535), U32.is_gt(ll, cap), False{}, Equal.cong(U32, Bool, cu =>
    U32.is_gt(ll, cu), 65535, cap, Equal.sym(U32, cap, 65535, ec)), gt.no(ll, cap, nn, t_l, h_n)) :
    {U32.is_gt(ll, 65535) == False{} : Bool}}
  h_fz = {fits.small(zz, ls, cap, cap2, zlib.len(ss, ll, le_l), h_ls, hc) :
    D1.spec.fits(zz)}
  +h_nl = {Equal.trans(Nat, U32.to_nat(ll), nn, ls, t_l, Equal.sym(Nat, ls, nn, e_ls)) : {U32.to_nat(ll) == ls : Nat}}
  +a2 = Img.decode_png(Png.enc.paint(ww, hh, op, px))
  +a4 = Img.decode_png(Png.enc.seal(ww, hh, op, Png.enc.raw(px, 0n, ww1, op, [], 0)))
  +a6 = Img.decode_png(Png.enc.seal.at(U32.is_gt(ll, 65535), ww, hh, op, ss, ll))
  Equal.trans(Maybe<&2, Img.Raster>, Laws.spec.png.back(Png.enc.open(Png.enc.good(ww, hh, px), ww, hh, px)), a2,
    Some{Img.raster(ww, hh, px)},
    Equal.trans(Maybe<&2, Img.Raster>, Laws.spec.png.back(Png.enc.open(Png.enc.good(ww, hh, px), ww, hh, px)),
      Laws.spec.png.back(Png.enc.open(True{}, ww, hh, px)), a2,
      Equal.cong(Bool, Maybe<&2, Img.Raster>, zb => Laws.spec.png.back(Png.enc.open(zb, ww, hh, px)), Png.enc.good(ww,
        hh, px), True{}, e_good),
      Equal.cong(Bool, Maybe<&2, Img.Raster>, ob => Img.decode_png(Png.enc.paint(ww, hh, ob, px)), Png.enc.opaque(px,
        True{}), op, e_op)),
    Equal.trans(Maybe<&2, Img.Raster>, a2, a4, Some{Img.raster(ww, hh, px)},
      Equal.trans(Maybe<&2, Img.Raster>, a2, Img.decode_png(Png.enc.paint.at(False{}, ww, hh, op, px, n_b)), a4,
        Equal.cong(Bool, Maybe<&2, Img.Raster>, zb => Img.decode_png(Png.enc.paint.at(zb, ww, hh, op, px, n_b)),
          U32.is_gt(n_b, 65535), False{}, f_nb),
        Equal.cong(Nat, Maybe<&2, Img.Raster>, kn => Img.decode_png(Png.enc.seal(ww, hh, op, Png.enc.raw(px, 0n, kn, op,
          [], 0))), U32.to_nat(ww), ww1, e_w)),
      Equal.trans(Maybe<&2, Img.Raster>, a4, a6, Some{Img.raster(ww, hh, px)},
        Equal.trans(Maybe<&2, Img.Raster>, a4, Img.decode_png(Png.enc.seal(ww, hh, op, (r0, m0))), a6,
          Equal.cong(List<&2, U32> & U32, Maybe<&2, Img.Raster>, pr => Img.decode_png(Png.enc.seal(ww, hh, op, pr)),
            Png.enc.raw(px, 0n, ww1, op, [], 0), (r0, m0), raw.eq(px, 0n, ww1, op, [], 0)),
          Equal.trans(Maybe<&2, Img.Raster>, Img.decode_png(Png.enc.seal(ww, hh, op, (r0, m0))),
            Img.decode_png(Png.enc.seal(ww, hh, op, (ss, m0))), a6,
            Equal.cong(List<&2, U32>, Maybe<&2, Img.Raster>, xs => Img.decode_png(Png.enc.seal(ww, hh, op, (xs, m0))),
              r0, ss, M1.inf.rev_rev(ss)),
            Equal.cong(U32, Maybe<&2, Img.Raster>, uu => Img.decode_png(Png.enc.seal(ww, hh, op, (ss, uu))), m0, ll,
              e_m0))),
        rt.tail(U32.is_gt(ll, 65535), ww, hh, px, op, wp, hp, f_ll, hao, e_w, e_h, hl, e_m, h_fz, h_nl))))

# the width and height as successors
def rt.pos(
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  +nb: U32,
  e_good: {Png.enc.good(ww, hh, px) == True{} : Bool},
  +hl: {List.length(&2, U32, px) == Nat.mul(U32.to_nat(hh), U32.to_nat(ww)) : Nat},
  h_nb: {U32.to_nat(nb) == Laws.spec.scan.len(ww, hh, D1.all_opaque(px)) : Nat},
  h_one: {U32.is_le(nb, 65535) == True{} : Bool},
  pw: &wp: Nat -> {U32.to_nat(ww) == 1n+wp : Nat},
  ph: &hp: Nat -> {U32.to_nat(hh) == 1n+hp : Nat}
) -> {Laws.spec.png.back(Img.encode_png(Img.raster(ww, hh, px))) == Some{Img.raster(ww, hh, px)} :
  Maybe<&2, Img.Raster>}:
  (+wp, e_w0) = pw
  (+hp, e_h0) = ph
  +e_w = {e_w0 : {U32.to_nat(ww) == 1n+wp : Nat}}
  +e_h = {e_h0 : {U32.to_nat(hh) == 1n+hp : Nat}}
  +op = D1.all_opaque(px)
  +kk = Laws.spec.nch(op)
  +e_l2 = {Equal.trans(Nat, List.length(&2, U32, px), Nat.mul(U32.to_nat(hh), U32.to_nat(ww)), Nat.mul(1n+hp, 1n+wp),
    hl, Equal.trans(Nat, Nat.mul(U32.to_nat(hh), U32.to_nat(ww)), Nat.mul(1n+hp, U32.to_nat(ww)), Nat.mul(1n+hp, 1n+wp),
    Equal.cong(Nat, Nat, xx => Nat.mul(xx, U32.to_nat(ww)), U32.to_nat(hh), 1n+hp, e_h), Equal.cong(Nat, Nat, xx =>
    Nat.mul(1n+hp, xx), U32.to_nat(ww), 1n+wp, e_w))) : {List.length(&2, U32, px) == Nat.mul(1n+hp, 1n+wp) : Nat}}
  +e_n2 = {Equal.trans(Nat, U32.to_nat(nb), Nat.mul(U32.to_nat(hh), 1n+Nat.mul(U32.to_nat(ww), kk)), Nat.mul(1n+hp,
    1n+Nat.mul(1n+wp, kk)), h_nb, Equal.trans(Nat, Nat.mul(U32.to_nat(hh), 1n+Nat.mul(U32.to_nat(ww), kk)),
    Nat.mul(1n+hp, 1n+Nat.mul(U32.to_nat(ww), kk)), Nat.mul(1n+hp, 1n+Nat.mul(1n+wp, kk)), Equal.cong(Nat, Nat, xx =>
    Nat.mul(xx, 1n+Nat.mul(U32.to_nat(ww), kk)), U32.to_nat(hh), 1n+hp, e_h), Equal.cong(Nat, Nat, xx => Nat.mul(1n+hp,
    1n+Nat.mul(xx, kk)), U32.to_nat(ww), 1n+wp, e_w))) : {U32.to_nat(nb) == Nat.mul(1n+hp, 1n+Nat.mul(1n+wp, kk)) :
    Nat}}
  rt.go(ww, hh, px, nb, op, wp, hp, M1.opaque.all(px, True{}), {==}, e_good, e_w, e_h, e_l2, e_n2, h_one, 65535, 65546,
    {==}, {==})

# laws/PngRoundTrips.bend for one stored block
def Laws.png_roundtrip_one(ww, hh, px, nb, h_ok, h_nb, h_one):
  +aa = Nat.mul(U32.to_nat(hh), U32.to_nat(ww))
  +ll = List.length(&2, U32, px)
  +nw = Bool.not(Nat.is_eq(U32.to_nat(ww), 0n))
  +nh = Bool.not(Nat.is_eq(U32.to_nat(hh), 0n))
  +ok = {h_ok : {D2.png_ok(ww, hh, px) == True{} : Bool}}
  +e_sides = {M1.and_left(Bool.and(nw, nh), Bool.and(D2.below(32n, aa), Nat.is_eq(ll, aa)), ok) :
    {Bool.and(nw, nh) == True{} : Bool}}
  +e_r = {M1.and_right(Bool.and(nw, nh), Bool.and(D2.below(32n, aa), Nat.is_eq(ll, aa)), ok) :
    {Bool.and(D2.below(32n, aa), Nat.is_eq(ll, aa)) == True{} : Bool}}
  +e_la = {M5.nat_eq_true(ll, aa, M1.and_right(D2.below(32n, aa), Nat.is_eq(ll, aa), e_r)) : {ll == aa : Nat}}
  +z_w = M5.not.true(Nat.is_eq(U32.to_nat(ww), 0n), M1.and_left(nw, nh, e_sides))
  +z_h = M5.not.true(Nat.is_eq(U32.to_nat(hh), 0n), M1.and_right(nw, nh, e_sides))
  +e_good = rt.good.at(Png.enc.good(ww, hh, px), ww, hh, px, L2.png_encodes(ww, hh, px, ok))
  rt.pos(ww, hh, px, nb, e_good, e_la, h_nb, h_one, M5.nat_pos(U32.to_nat(ww), z_w), M5.nat_pos(U32.to_nat(hh), z_h))

# laws/PngRoundTrips.bend when the scanlines fit one stored block: png_roundtrip_one, with the scanline count a word's
# value
def rt2.one(
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  +wp: Nat,
  +hp: Nat,
  h_ok: {D2.png_ok(ww, hh, px) == True{} : Bool},
  +hao: {D1.all_opaque(px) == Png.enc.opaque(px, True{}) : Bool},
  +e_w: {U32.to_nat(ww) == 1n+wp : Nat},
  +e_h: {U32.to_nat(hh) == 1n+hp : Nat},
  +t_nb: {U32.to_nat(Png.enc.nbytes(opq(px), ww, hh)) == snn(hp, wp, opq(px)) : Nat},
  h_one: {U32.is_le(Png.enc.nbytes(Png.enc.opaque(px, True{}), ww, hh), 65535) == True{} : Bool}
) -> {Laws.spec.png.back(Img.encode_png(Img.raster(ww, hh, px))) == Some{Img.raster(ww, hh, px)} : Maybe<&2,
  Img.Raster>}:
  +op = Png.enc.opaque(px, True{})
  +ao = D1.all_opaque(px)
  +nb = Png.enc.nbytes(op, ww, hh)
  +hn = U32.to_nat(hh)
  +wn = U32.to_nat(ww)
  +e_n = {Equal.trans(Nat, Nat.mul(1n+hp, 1n+Nat.mul(1n+wp, Laws.spec.nch(op))), Nat.mul(1n+hp, 1n+Nat.mul(1n+wp,
    Laws.spec.nch(ao))), Laws.spec.scan.len(ww, hh, ao),
    Equal.cong(Bool, Nat, oo => Nat.mul(1n+hp, 1n+Nat.mul(1n+wp, Laws.spec.nch(oo))), op, ao, Equal.sym(Bool, ao, op,
      hao)),
    Equal.trans(Nat, Nat.mul(1n+hp, 1n+Nat.mul(1n+wp, Laws.spec.nch(ao))), Nat.mul(hn, 1n+Nat.mul(1n+wp,
      Laws.spec.nch(ao))), Laws.spec.scan.len(ww, hh, ao),
      Equal.cong(Nat, Nat, xx => Nat.mul(xx, 1n+Nat.mul(1n+wp, Laws.spec.nch(ao))), 1n+hp, hn, Equal.sym(Nat, hn,
        1n+hp, e_h)),
      Equal.cong(Nat, Nat, xx => Nat.mul(hn, 1n+Nat.mul(xx, Laws.spec.nch(ao))), 1n+wp, wn, Equal.sym(Nat, wn, 1n+wp,
        e_w)))) : {Nat.mul(1n+hp, 1n+Nat.mul(1n+wp, Laws.spec.nch(op))) == Laws.spec.scan.len(ww, hh, ao) : Nat}}
  Laws.png_roundtrip_one(ww, hh, px, nb, h_ok, Equal.trans(Nat, U32.to_nat(nb), Nat.mul(1n+hp, 1n+Nat.mul(1n+wp,
    Laws.spec.nch(op))), Laws.spec.scan.len(ww, hh, ao), t_nb, e_n), h_one)

# laws/PngRoundTrips.bend past one stored block: the stored blocks of 65535 bytes, whose sizes fit a word by the bound
# 8 w h
def rt2.wide(
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  +a8: U32,
  +wp: Nat,
  +hp: Nat,
  e_good: {Png.enc.good(ww, hh, px) == True{} : Bool},
  +hao: {D1.all_opaque(px) == Png.enc.opaque(px, True{}) : Bool},
  +e_w: {U32.to_nat(ww) == 1n+wp : Nat},
  +e_h: {U32.to_nat(hh) == 1n+hp : Nat},
  +hl: {List.length(&2, U32, px) == Nat.mul(1n+hp, 1n+wp) : Nat},
  +t_nb: {U32.to_nat(Png.enc.nbytes(opq(px), ww, hh)) == snn(hp, wp, opq(px)) : Nat},
  +e_t: {U32.to_nat(a8) == Nat.mul(8n, Nat.mul(1n+hp, 1n+wp)) : Nat},
  +h5: {Nat.is_le(snn(hp, wp, opq(px)), Nat.mul(Nat.mul(1n+hp, 1n+wp), 5n)) == True{} : Bool},
  +h_n: {Nat.is_le(snn(hp, wp, opq(px)), U32.to_nat(a8)) == True{} : Bool},
  +hbn: {U32.is_le(Png.enc.nbytes(Png.enc.opaque(px, True{}), ww, hh), 65535) == False{} : Bool}
) -> {Laws.spec.png.back(Img.encode_png(Img.raster(ww, hh, px))) == Some{Img.raster(ww, hh, px)} : Maybe<&2,
  Img.Raster>}:
  +op = Png.enc.opaque(px, True{})
  +ww1 = {1n+wp : Nat}
  +hh1 = {1n+hp : Nat}
  +aa = Nat.mul(hh1, ww1)
  +nn = Nat.mul(hh1, 1n+Nat.mul(ww1, Laws.spec.nch(op)))
  +ss = M1.sc(px, 0n, ww1, op)
  +ll = Png.enc.len(ss, 0)
  +nb = Png.enc.nbytes(op, ww, hh)
  +ls = List.length(&2, U32, ss)
  +rows = rows.of(hh1, ww1, op, px)
  +e_s = {sc.rows(hh1, wp, op, px, hl) : {ss == M1.scan(rows) : List<&2, U32>}}
  +e_ls = {Equal.trans(Nat, ls, List.length(&2, U32, M1.scan(rows)), nn, Equal.cong(List<&2, U32>, Nat, xs =>
    List.length(&2, U32, xs), ss, M1.scan(rows), e_s), len.scan(hh1, ww1, op, px, hl)) : {ls == nn : Nat}}
  +hn = {len.of(ss, a8, M1.le_rw_l(nn, ls, U32.to_nat(a8), Equal.sym(Nat, ls, nn, e_ls), h_n)) :
    {U32.to_nat(ll) == ls : Nat}}
  +e_nbl = {M1.u32.same(nb, ll, Equal.trans(Nat, U32.to_nat(nb), nn, U32.to_nat(ll), t_nb, Equal.trans(Nat, nn, ls,
    U32.to_nat(ll), Equal.sym(Nat, ls, nn, e_ls), Equal.sym(Nat, U32.to_nat(ll), ls, hn)))) : {nb == ll : U32}}
  +hbig = {Equal.trans(Bool, U32.is_le(ll, 65535), U32.is_le(nb, 65535), False{}, Equal.cong(U32, Bool, uu =>
    U32.is_le(uu, 65535), ll, nb, Equal.sym(U32, nb, ll, e_nbl)), hbn) : {U32.is_le(ll, 65535) == False{} : Bool}}
  +h_tu = tu.ok(ss, 65535, a8, aa, {==}, hn, hbig, M1.le_rw_l(nn, ls, Nat.mul(aa, 5n), Equal.sym(Nat, ls, nn,
    e_ls), h5), e_t)
  +h_by = {Equal.trans(Bool, D1.bytes(ss), D1.bytes.go(M1.scan(rows), True{}), True{}, Equal.cong(List<&2, U32>,
    Bool, xs => D1.bytes.go(xs, True{}), ss, M1.scan(rows), e_s), bytes.scan(rows, masked.rows.of(hh1, ww1, op,
    px))) : {D1.bytes(ss) == True{} : Bool}}
  +zf = Nat.is_lt(ls, 0n)
  +ef = {Equal.sym(Bool, False{}, zf, M1.lt_zero_false(ls)) : {zf == False{} : Bool}}
  +kz = Nat.add(Nat.add(ls, Nat.mul(U32.to_nat(Png.enc.nblk(ll)), 5n)), 6n)
  h_fz = {nat.fits(List.length(&2, U32, Png.enc.zlib(ss, ll)), a8, M1.le_rw_l(kz, List.length(&2, U32,
    L1.zlib.stored(65535, ss)), U32.to_nat(a8), Equal.sym(Nat, List.length(&2, U32, L1.zlib.stored(65535, ss)), kz,
    pfin.zlib.len(ss, 65535, {==}, hn, hbig)), h_tu)) : D1.spec.fits(Png.enc.zlib(ss, ll))}
  Equal.trans(Maybe<&2, Img.Raster>, Laws.spec.png.back(Png.enc.open(Png.enc.good(ww, hh, px), ww, hh, px)),
    Laws.spec.png.back(Some{Png.enc.seal.at(zf, ww, hh, op, ss, ll)}), Some{Img.raster(ww, hh, px)},
    Equal.cong(Maybe<&2, List<&2, U32>>, Maybe<&2, Img.Raster>, mm => Laws.spec.png.back(mm),
      Png.enc.open(Png.enc.good(ww,
      hh, px), ww, hh, px), Some{Png.enc.seal.at(zf, ww, hh, op, ss, ll)}, wide.rt(zf, ww, hh, px, wp, a8, ef,
      e_good, e_w, e_nbl, hn, hbig, h_by, h_tu)),
    rt.tail(zf, ww, hh, px, op, wp, hp, ef, hao, e_w, e_h, hl, nb.em(ww, op, wp, hp, a8, e_w, h_n), h_fz, hn))

# laws/PngRoundTrips.bend: split on how the scanline count compares with 65535
def rt2.at(
  cc: Cmp,
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  +a8: U32,
  +wp: Nat,
  +hp: Nat,
  h_ok: {D2.png_ok(ww, hh, px) == True{} : Bool},
  e_good: {Png.enc.good(ww, hh, px) == True{} : Bool},
  +hao: {D1.all_opaque(px) == Png.enc.opaque(px, True{}) : Bool},
  +e_w: {U32.to_nat(ww) == 1n+wp : Nat},
  +e_h: {U32.to_nat(hh) == 1n+hp : Nat},
  +hl: {List.length(&2, U32, px) == Nat.mul(1n+hp, 1n+wp) : Nat},
  +t_nb: {U32.to_nat(Png.enc.nbytes(opq(px), ww, hh)) == snn(hp, wp, opq(px)) : Nat},
  +e_t: {U32.to_nat(a8) == Nat.mul(8n, Nat.mul(1n+hp, 1n+wp)) : Nat},
  +h5: {Nat.is_le(snn(hp, wp, opq(px)), Nat.mul(Nat.mul(1n+hp, 1n+wp), 5n)) == True{} : Bool},
  +h_n: {Nat.is_le(snn(hp, wp, opq(px)), U32.to_nat(a8)) == True{} : Bool},
  +ec: {U32.cmp(Png.enc.nbytes(Png.enc.opaque(px, True{}), ww, hh), 65535) == cc : Cmp}
) -> {Laws.spec.png.back(Img.encode_png(Img.raster(ww, hh, px))) == Some{Img.raster(ww, hh, px)} : Maybe<&2,
  Img.Raster>}:
  match cc:
    case LT{}:
      rt2.one(ww, hh, px, wp, hp, h_ok, hao, e_w, e_h, t_nb, Equal.cong(Cmp, Bool, xc => Cmp.is_le(xc),
        U32.cmp(Png.enc.nbytes(Png.enc.opaque(px, True{}), ww, hh), 65535), LT{}, ec))
    case EQ{}:
      rt2.one(ww, hh, px, wp, hp, h_ok, hao, e_w, e_h, t_nb, Equal.cong(Cmp, Bool, xc => Cmp.is_le(xc),
        U32.cmp(Png.enc.nbytes(Png.enc.opaque(px, True{}), ww, hh), 65535), EQ{}, ec))
    case GT{}:
      rt2.wide(ww, hh, px, a8, wp, hp, e_good, hao, e_w, e_h, hl, t_nb, e_t, h5, h_n, Equal.cong(Cmp, Bool, xc =>
        Cmp.is_le(xc), U32.cmp(Png.enc.nbytes(Png.enc.opaque(px, True{}), ww, hh), 65535), GT{}, ec))

# laws/PngRoundTrips.bend with the width and height as successors: the sizes from the bound 8 w h
def rt2.pos(
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  +a8: U32,
  h_ok: {D2.png_ok(ww, hh, px) == True{} : Bool},
  e_good: {Png.enc.good(ww, hh, px) == True{} : Bool},
  +hl: {List.length(&2, U32, px) == Nat.mul(U32.to_nat(hh), U32.to_nat(ww)) : Nat},
  +h_a8: {U32.to_nat(a8) == Nat.mul(8n, Nat.mul(U32.to_nat(hh), U32.to_nat(ww))) : Nat},
  pw: &wp: Nat -> {U32.to_nat(ww) == 1n+wp : Nat},
  ph: &hp: Nat -> {U32.to_nat(hh) == 1n+hp : Nat}
) -> {Laws.spec.png.back(Img.encode_png(Img.raster(ww, hh, px))) == Some{Img.raster(ww, hh, px)} : Maybe<&2,
  Img.Raster>}:
  (+wp, e_w0) = pw
  (+hp, e_h0) = ph
  +e_w = {e_w0 : {U32.to_nat(ww) == 1n+wp : Nat}}
  +e_h = {e_h0 : {U32.to_nat(hh) == 1n+hp : Nat}}
  +op = Png.enc.opaque(px, True{})
  +hn = U32.to_nat(hh)
  +wn = U32.to_nat(ww)
  +aa = Nat.mul(1n+hp, 1n+wp)
  +nn = Nat.mul(1n+hp, 1n+Nat.mul(1n+wp, Laws.spec.nch(op)))
  +hao = {Equal.sym(Bool, op, D1.all_opaque(px), M1.opaque.all(px, True{})) : {D1.all_opaque(px) == op : Bool}}
  +e_l2 = {Equal.trans(Nat, List.length(&2, U32, px), Nat.mul(hn, wn), aa, hl, Equal.trans(Nat, Nat.mul(hn, wn),
    Nat.mul(1n+hp, wn), aa, Equal.cong(Nat, Nat, xx => Nat.mul(xx, wn), hn, 1n+hp, e_h), Equal.cong(Nat, Nat, xx =>
    Nat.mul(1n+hp, xx), wn, 1n+wp, e_w))) : {List.length(&2, U32, px) == aa : Nat}}
  +e_t = {Equal.trans(Nat, U32.to_nat(a8), Nat.mul(8n, Nat.mul(hn, wn)), Nat.mul(8n, aa), h_a8, Equal.trans(Nat,
    Nat.mul(8n, Nat.mul(hn, wn)), Nat.mul(8n, Nat.mul(1n+hp, wn)), Nat.mul(8n, aa), Equal.cong(Nat, Nat, xx =>
    Nat.mul(8n, Nat.mul(xx, wn)), hn, 1n+hp, e_h), Equal.cong(Nat, Nat, xx => Nat.mul(8n, Nat.mul(1n+hp, xx)), wn,
    1n+wp, e_w))) : {U32.to_nat(a8) == Nat.mul(8n, aa) : Nat}}
  +h5 = {scan5(1n+hp, wp, Laws.spec.nch(op), nch4(op)) : {Nat.is_le(nn, Nat.mul(aa, 5n)) == True{} : Bool}}
  +h_n = {M1.le_rw_r(nn, Nat.mul(8n, aa), U32.to_nat(a8), Equal.sym(Nat, U32.to_nat(a8), Nat.mul(8n, aa), e_t),
    M1.le_trans(nn, Nat.mul(aa, 5n), Nat.mul(8n, aa), h5, five.eight(aa))) : {Nat.is_le(nn, U32.to_nat(a8)) ==
    True{} : Bool}}
  +t_nb = {nb.val(ww, hh, op, wp, hp, a8, e_w, e_h, h_n) : {U32.to_nat(Png.enc.nbytes(op, ww, hh)) == nn : Nat}}
  rt2.at(U32.cmp(Png.enc.nbytes(op, ww, hh), 65535), ww, hh, px, a8, wp, hp, h_ok, e_good, hao, e_w, e_h, e_l2, t_nb,
    e_t, h5, h_n, {==})

# laws/PngRoundTrips.bend: one stored block when the scanlines fit, the stored blocks of 65535 bytes otherwise
def Laws.png_roundtrip(ww, hh, px, a8, h_ok, h_a8):
  +aa = Nat.mul(U32.to_nat(hh), U32.to_nat(ww))
  +ll = List.length(&2, U32, px)
  +nw = Bool.not(Nat.is_eq(U32.to_nat(ww), 0n))
  +nh = Bool.not(Nat.is_eq(U32.to_nat(hh), 0n))
  +ok = {h_ok : {D2.png_ok(ww, hh, px) == True{} : Bool}}
  +e_sides = {M1.and_left(Bool.and(nw, nh), Bool.and(D2.below(32n, aa), Nat.is_eq(ll, aa)), ok) :
    {Bool.and(nw, nh) == True{} : Bool}}
  +e_r = {M1.and_right(Bool.and(nw, nh), Bool.and(D2.below(32n, aa), Nat.is_eq(ll, aa)), ok) :
    {Bool.and(D2.below(32n, aa), Nat.is_eq(ll, aa)) == True{} : Bool}}
  +e_la = {M5.nat_eq_true(ll, aa, M1.and_right(D2.below(32n, aa), Nat.is_eq(ll, aa), e_r)) : {ll == aa : Nat}}
  +z_w = M5.not.true(Nat.is_eq(U32.to_nat(ww), 0n), M1.and_left(nw, nh, e_sides))
  +z_h = M5.not.true(Nat.is_eq(U32.to_nat(hh), 0n), M1.and_right(nw, nh, e_sides))
  +e_good = rt.good.at(Png.enc.good(ww, hh, px), ww, hh, px, L2.png_encodes(ww, hh, px, ok))
  rt2.pos(ww, hh, px, a8, ok, e_good, e_la, h_a8, M5.nat_pos(U32.to_nat(ww), z_w), M5.nat_pos(U32.to_nat(hh), z_h))
