# For every raster `r` encode_jpeg writes (encode_jpeg.good: both sides from 1
# to 65535, at most 2^31 points, and w * h samples), and every quality,
# `decode_jpeg(encode_jpeg_q(r, q))` is some raster of `r`'s size with alpha
# 255, and so is `decode_jpeg(encode_jpeg(r))`.
import Base
import ../main.bend as Img
import ../src/jpeg.bend as Jpeg
import ../src/jpeg_enc.bend as Jenc
import ./defs/PngSpecification.bend as D1
import ./defs/PointInside.bend as D2

# a byte list in which every 255 is followed by a 0 (T.81 F.1.2.3), ff saying the byte before xs was a
# 255 and ok that every 255 so far was
def jpg.stuffed(xs: List<&2, U32>, ff: Bool, ok: Bool) -> Bool:
  match xs:
    case Nil{}:
      Bool.and(ok, Bool.not(ff))
    case +bb <> rest:
      match ff:
        case True{}:
          jpg.stuffed(rest, False{}, Bool.and(ok, U32.is_eq(bb, 0)))
        case False{}:
          jpg.stuffed(rest, U32.is_eq(bb, 255), ok)

# LAW: the entropy-coded bytes encode_jpeg writes, for every size, quality and samples, have every 255
# followed by a 0
law jpeg_enc_stuffed:
  for +ww: U32
  for +hh: U32
  for +qq: U32
  for px: List<&2, U32>
  {jpg.stuffed(Jenc.encode.arm(ww, hh, qq, px), False{}, True{}) == True{} : Bool}

# the tables the decoder holds after reading encode_jpeg's DQT and two DHT segments at quality qq: Annex K's
# tables K.1 and K.2 at that quality, in zigzag order, as quantisation tables 0 and 1, and the Annex K luminance
# and chrominance Huffman tables as tables 0 and 1 of each class
def jpg.enc.tabs(+qq: U32) -> Jpeg.Tabs:
  Jpeg.Tabs{Jenc.encode.qz(Jenc.encode.lumq(), qq), Jenc.encode.qz(Jenc.encode.chrq(), qq), [], [],
    Jpeg.decode.canon(272n, 0n, Jenc.encode.dccounts(), Jenc.encode.dcsyms(), 0, 0, [], [], []),
    Jpeg.decode.canon(272n, 0n, Jenc.encode.cdccounts(), Jenc.encode.dcsyms(), 0, 0, [], [], []), Jpeg.decode.huff0(),
    Jpeg.decode.huff0(), Jpeg.decode.canon(272n, 0n, Jenc.encode.accounts(), Jenc.encode.acsyms(), 0, 0, [], [], []),
    Jpeg.decode.canon(272n, 0n, Jenc.encode.caccounts(), Jenc.encode.cacsyms(), 0, 0, [], [], []),
    Jpeg.decode.huff0(), Jpeg.decode.huff0()}

# the frame encode_jpeg's SOF0 carries: its width and height, three components 1, 2 and 3, each sampled
# 1 by 1, Y with quantisation table 0, Cb and Cr with table 1
def jpg.enc.frame(+ww: U32, +hh: U32) -> Jpeg.Frame:
  Jpeg.Frame{ww, hh, 3, [1, 2, 3], [1, 1, 1], [1, 1, 1], [0, 1, 1], 1, 1}

# the scan encode_jpeg's SOS opens: components 1, 2 and 3, Y with Huffman tables 0, Cb and Cr with tables 1, all
# of 0 to 63
def jpg.enc.scan() -> Jpeg.Scan:
  Jpeg.Scan{3, [1, 2, 3], [0, 1, 1], [0, 1, 1], 0, 63, 0}

# LAW: the decoder's marker walk over encode_jpeg's header at any quality (SOI, APP0, DQT, SOF0, two DHT, SOS)
# reaches the entropy-coded data with the frame carrying the encoder's width and height, whatever they are, the
# encoder's scan and its tables at that quality, no restart interval, a baseline frame read and nothing refused
law jpeg_enc_header_walk:
  for +ww: U32
  for +hh: U32
  for +qq: U32
  {Jpeg.decode.walk(Jenc.encode.header(ww, hh, qq), Jpeg.decode.st0()) == Jpeg.St{Jpeg.Ent{}, jpg.enc.frame(ww, hh),
    jpg.enc.scan(), jpg.enc.tabs(qq), [], 0, 1, 0} : Jpeg.St}

# LAW: inside the entropy-coded data, the decoder's walk keeps every byte of stuffed data (the stuffed
# zeros too, which the bit reader drops) and stops at EOI, holding what it held
law jpeg_ent_walk:
  for xs: List<&2, U32>
  for h_stuffed: {jpg.stuffed(xs, False{}, True{}) == True{} : Bool}
  for +frame: Jpeg.Frame
  for +scan: Jpeg.Scan
  for +tabs: Jpeg.Tabs
  for +ent: List<&2, U32>
  for +ri: U32
  for +kind: U32
  for +bad: U32
  {Jpeg.decode.walk(List.append(&2, U32, xs, [255, 217]), Jpeg.St{Jpeg.Ent{}, frame, scan, tabs, ent, ri, kind, bad}) ==
    Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, List.reverse.go(&2, U32, xs, ent), ri, kind, bad} : Jpeg.St}

# decode_jpeg of encode_jpeg's bytes, when it wrote some
def jpg.back(mm: Maybe<&2, List<&2, U32>>) -> Maybe<&2, Img.Raster>:
  match mm:
    case None{}:
      None{}
    case Some{bytes}:
      Img.decode_jpeg(bytes)

# LAW: for every raster encode_jpeg writes and every quality, decode_jpeg of encode_jpeg_q's bytes is the decoder's
# scan decode of encode_jpeg_q's own entropy-coded bytes, in the frame of the raster's width and height, with the
# encoder's scan and its tables at that quality, as YCbCr (its JFIF APP0 says so): the marker walk, the unstuffing
# and the frame size are done
law jpeg_round_trip_scan:
  for +ww: U32
  for +hh: U32
  for +qq: U32
  for +px: List<&2, U32>
  for +h_good: {Img.encode_jpeg.good(ww, hh, px) == True{} : Bool}
  {jpg.back(Img.encode_jpeg_q(Img.Raster{ww, hh, px}, qq)) == Img.decode_jpeg.out(Jpeg.decode.run(jpg.enc.frame(ww,
    hh), jpg.enc.scan(), jpg.enc.tabs(qq), Jenc.encode.arm(ww, hh, qq, Img.colours(px)), 0, False{})) :
    Maybe<&2, Img.Raster>}

# a decoded raster, if any, has width ww and height hh
def jpg.sized(mm: Maybe<&2, Img.Raster>, +ww: U32, +hh: U32) -> Bool:
  match mm:
    case None{}:
      True{}
    case Some{Img.Raster{rw, rh, _px}}:
      Bool.and(U32.is_eq(rw, ww), U32.is_eq(rh, hh))

# LAW: the scan decode, whatever the bytes, tables, scan and colour coding, returns no picture or one of its
# frame's width and height
law jpeg_run_sized:
  for +ww: U32
  for +hh: U32
  for +nf: U32
  for +ids: List<&2, U32>
  for +hs: List<&2, U32>
  for +vs: List<&2, U32>
  for +tq: List<&2, U32>
  for +hmax: U32
  for +vmax: U32
  for +scan: Jpeg.Scan
  for +tabs: Jpeg.Tabs
  for +ent: List<&2, U32>
  for +ri: U32
  for +rgb: Bool
  {jpg.sized(Img.decode_jpeg.out(Jpeg.decode.run(Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, tabs, ent,
    ri, rgb)), ww, hh) == True{} : Bool}

# LAW: for every raster encode_jpeg writes and every quality, decode_jpeg of encode_jpeg_q's bytes is none or a
# raster of the raster's width and height; every sample of one has alpha 255 (jpeg_decode_opaque)
law jpeg_round_trip_sized:
  for +ww: U32
  for +hh: U32
  for +qq: U32
  for +px: List<&2, U32>
  for +h_good: {Img.encode_jpeg.good(ww, hh, px) == True{} : Bool}
  {jpg.sized(jpg.back(Img.encode_jpeg_q(Img.Raster{ww, hh, px}, qq)), ww, hh) == True{} : Bool}

# one byte as its eight bits, the lowest first
type JByte is Data:
  JByte{c0: Bool, c1: Bool, c2: Bool, c3: Bool, c4: Bool, c5: Bool, c6: Bool, c7: Bool}

# a byte's value: its eight bits over 24 zero bits
def jpg.byte(bb: JByte) -> U32:
  match bb:
    case JByte{c0, c1, c2, c3, c4, c5, c6, c7}:
      U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, Word.zero(24n)}}}}}}}}}

# the bytes' values, in order
def jpg.bytes(bs: List<&2, JByte>) -> List<&2, U32>:
  match bs:
    case Nil{}:
      []
    case bb <> rest:
      jpg.byte(bb) <> jpg.bytes(rest)

# the values the decoder's bit reader reads, eight bits at a time, left times: got is the reader and the
# value just read
def jpg.read8(left: Nat, got: Jpeg.Bits & U32) -> List<&2, U32>:
  match left:
    case 0n:
      []
    case 1n+pp:
      (bits, vv) = got
      vv <> jpg.read8(pp, Jpeg.decode.read.n(8, bits))

# LAW: stuffing and unstuffing are inverses: the decoder's bit reader, reading eight bits at a time from the
# encoder's stuffing of any bytes (encode.stuff.all, which puts a 0 after every 255), reads the bytes back,
# the stuffed zeros dropped, whatever the reader's ok flag
law jpeg_unstuff:
  for +bs: List<&2, JByte>
  for +ok: U32
  {jpg.read8(List.length(&2, JByte, bs), Jpeg.decode.read.n(8, Jpeg.Bits{0, ok, 0, Jenc.encode.stuff.all(
    List.reverse(&2, U32, jpg.bytes(bs)), [])})) == jpg.bytes(bs) : List<&2, U32>}

# a bit as 1 or 0
def jpg.bitu(bb: Bool) -> U32:
  match bb:
    case True{}:
      1
    case False{}:
      0

# a code's value: its bits, the first highest, shifted onto acc
def jpg.num(bs: List<&2, Bool>, acc: U32) -> U32:
  match bs:
    case Nil{}:
      acc
    case bb <> rest:
      jpg.num(rest, U32.or(U32.shl(acc), jpg.bitu(bb)))

# the encoder's bit writer given codes one after another, each code a list of bits, the first highest, written
# with encode.bits at its length and value
def jpg.write(cs: List<&2, List<&2, Bool>>, pp: Jenc.Put) -> Jenc.Put:
  match cs:
    case Nil{}:
      pp
    case +cc <> rest:
      jpg.write(rest, Jenc.encode.bits(pp, U32.from_nat(List.length(&2, Bool, cc)), jpg.num(cc, 0)))

# both answers: the first, then the second
def jpg.also(ok: Bool, rest: Bool) -> Bool:
  match ok:
    case True{}:
      rest
    case False{}:
      match rest:
        case _r:
          False{}

# every code has at most 16 bits
def jpg.codes16(cs: List<&2, List<&2, Bool>>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case cc <> rest:
      jpg.also(Nat.is_le(List.length(&2, Bool, cc), 16n), jpg.codes16(rest))

# the reader a read leaves
def jpg.got.bits(got: Jpeg.Bits & U32) -> Jpeg.Bits:
  match got:
    case (bits, _v):
      bits

# the value a read reads
def jpg.got.val(got: Jpeg.Bits & U32) -> U32:
  match got:
    case (_b, +vv):
      vv

# one more value before the values and the flag after it
def jpg.rcons(+vv: U32, got: List<&2, U32> & U32) -> List<&2, U32> & U32:
  match got:
    case (vs, +ok):
      (vv <> vs, ok)

# the reader's ok flag
def jpg.bits.ok(bits: Jpeg.Bits) -> U32:
  match bits:
    case Jpeg.Bits{_n, +ok, _b, _x}:
      ok

# the values the decoder's bit reader reads with decode.read.n, one code's length at a time, and its ok flag at
# the end
def jpg.reads(cs: List<&2, List<&2, Bool>>, +bits: Jpeg.Bits) -> List<&2, U32> & U32:
  match cs:
    case Nil{}:
      ([], jpg.bits.ok(bits))
    case +cc <> rest:
      +nn = U32.from_nat(List.length(&2, Bool, cc))
      jpg.rcons(jpg.got.val(Jpeg.decode.read.n(nn, bits)), jpg.reads(rest, jpg.got.bits(Jpeg.decode.read.n(nn,
        bits))))

# each code's value
def jpg.nums(cs: List<&2, List<&2, Bool>>) -> List<&2, U32>:
  match cs:
    case Nil{}:
      []
    case cc <> rest:
      jpg.num(cc, 0) <> jpg.nums(rest)

# LAW: the bit writer against the bit reader: codes of at most 16 bits each, any number of them, written one
# after another by the encoder's bit writer from an empty writer (so they cross byte boundaries at every
# offset) and padded and stuffed by encode.pad, are read back by the decoder's bit reader one code's length at a
# time, each code's value in order, the reader's ok flag still 1
law jpeg_bits_round_trip:
  for +cs: List<&2, List<&2, Bool>>
  for h_len: {jpg.codes16(cs) == True{} : Bool}
  {jpg.reads(cs, Jpeg.Bits{0, 1, 0, Jenc.encode.pad(jpg.write(cs, Jenc.encode.put0()))}) == (jpg.nums(cs), 1) :
    List<&2, U32> & U32}

# the reader after reading codes of these lengths, one at a time
def jpg.skip(cs: List<&2, List<&2, Bool>>, +bits: Jpeg.Bits) -> Jpeg.Bits:
  match cs:
    case Nil{}:
      bits
    case +cc <> rest:
      jpg.skip(rest, jpg.got.bits(Jpeg.decode.read.n(U32.from_nat(List.length(&2, Bool, cc)), bits)))

# the writer after the encoder writes a symbol's code from its book
def jpg.emit(got: Array<U32> & Jenc.Put) -> Jenc.Put:
  match got:
    case (_a, pp):
      pp

# the first answer, or else the second
def jpg.eith(aa: Bool, bb: Bool) -> Bool:
  match aa:
    case True{}:
      match bb:
        case _b:
          True{}
    case False{}:
      bb

# ss is one of xs
def jpg.memb(+ss: U32, xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case +xx <> rest:
      jpg.eith(U32.is_eq(ss, xx), jpg.memb(ss, rest))

# a Huffman lookup's symbol, the codes after it read back from its reader, and its ok flag
def jpg.hit(hit: Jpeg.Hit, post: List<&2, List<&2, Bool>>) -> U32 & (List<&2, U32> & U32) & U32:
  match hit:
    case Jpeg.Hit{+sym, bits, +ok}:
      (sym, jpg.reads(post, bits), ok)

# the entropy-coded bytes of codes pre, the encoder's code for symbol sy from a book, and codes post
def jpg.sym.bytes(
  +pre: List<&2, List<&2, Bool>>,
  book: Array<U32>,
  +sy: U32,
  +post: List<&2, List<&2, Bool>>
) -> List<&2, U32>:
  Jenc.encode.pad(jpg.write(post, jpg.emit(Jenc.encode.emit(Jenc.encode.sym(book, sy), jpg.write(pre,
    Jenc.encode.put0())))))

# the decoder's lookup in a table, after reading codes pre back from those bytes: the symbol, codes post read back,
# and the ok flag
def jpg.sym.back(
  +pre: List<&2, List<&2, Bool>>,
  book: Array<U32>,
  +tab: Jpeg.Huff,
  +sy: U32,
  +post: List<&2, List<&2, Bool>>
) -> U32 & (List<&2, U32> & U32) & U32:
  jpg.hit(Jpeg.decode.huff(16n, Jpeg.Ask{None{}, 0, 0, jpg.skip(pre, Jpeg.Bits{0, 1, 0, jpg.sym.bytes(pre, book, sy,
    post)})}, tab), post)

# the decoder's DC table a class's DHT counts build: Annex K's luminance table (K.3), or the chrominance table
# (K.4) when cls is set
def jpg.dctab(+cls: Bool) -> Jpeg.Huff:
  match cls:
    case False{}:
      Jpeg.decode.canon(272n, 0n, Jenc.encode.dccounts(), Jenc.encode.dcsyms(), 0, 0, [], [], [])
    case True{}:
      Jpeg.decode.canon(272n, 0n, Jenc.encode.cdccounts(), Jenc.encode.dcsyms(), 0, 0, [], [], [])

# the decoder's AC table a class's DHT counts and symbols build: K.5, or K.6 when cls is set
def jpg.actab(+cls: Bool) -> Jpeg.Huff:
  match cls:
    case False{}:
      Jpeg.decode.canon(272n, 0n, Jenc.encode.accounts(), Jenc.encode.acsyms(), 0, 0, [], [], [])
    case True{}:
      Jpeg.decode.canon(272n, 0n, Jenc.encode.caccounts(), Jenc.encode.cacsyms(), 0, 0, [], [], [])

# LAW: the Annex K DC tables, luminance and chrominance: for every DC symbol, the code the encoder's book for the
# class (encode.dcof) holds for it, written at any bit offset between any codes, is decoded by the decoder's
# Huffman lookup in the table decode.canon builds from the class's DHT counts (decode.look) to that symbol, the
# reader left exactly after the code, ok still 1
law jpeg_huff_dc:
  for +cls: Bool
  for +pre: List<&2, List<&2, Bool>>
  for h_pre: {jpg.codes16(pre) == True{} : Bool}
  for +sy: U32
  for h_sy: {jpg.memb(sy, Jenc.encode.dcsyms()) == True{} : Bool}
  for +post: List<&2, List<&2, Bool>>
  for h_post: {jpg.codes16(post) == True{} : Bool}
  {jpg.sym.back(pre, Jenc.encode.dcof(cls), jpg.dctab(cls), sy, post) == (sy, (jpg.nums(post), 1), 1) :
    U32 & (List<&2, U32> & U32) & U32}

# LAW: the Annex K AC tables, the same: every AC symbol's code from the encoder's book for the class decodes to the
# symbol at any bit offset, the reader left exactly after it. The luminance and chrominance tables hold the same
# 162 symbols, so both are asked of Annex K's luminance list
law jpeg_huff_ac:
  for +cls: Bool
  for +pre: List<&2, List<&2, Bool>>
  for h_pre: {jpg.codes16(pre) == True{} : Bool}
  for +sy: U32
  for h_sy: {jpg.memb(sy, Jenc.encode.acsyms()) == True{} : Bool}
  for +post: List<&2, List<&2, Bool>>
  for h_post: {jpg.codes16(post) == True{} : Bool}
  {jpg.sym.back(pre, Jenc.encode.acof(cls), jpg.actab(cls), sy, post) == (sy, (jpg.nums(post), 1), 1) :
    U32 & (List<&2, U32> & U32) & U32}

# a bit as a U32: bit 0 set to it, the rest clear
def jpg.ubit(bb: Bool) -> U32:
  U32{WCon{bb, Word.zero(31n)}}

# the low bit of a U32
def jpg.bit0(xx: U32) -> Bool:
  match xx:
    case U32{ww}:
      match ww:
        case WCon{b0, _t}:
          b0

# the bits the encoder's writer takes from a code of kk bits, top first: bit kk - 1 down to bit 0
def jpg.cb(kk: Nat, +code: U32) -> List<&2, Bool>:
  match kk:
    case 0n:
      []
    case 1n+ +pp:
      jpg.bit0(U32.shrn(code, pp)) <> jpg.cb(pp, code)

# the bits of a book word (encode.dcof, encode.acof): its length in the high half, its code in the low half
def jpg.cbw(+ww: U32) -> List<&2, Bool>:
  jpg.cb(U32.to_nat(U32.shrn(ww, 16n)), U32.and(ww, 65535))

# the encoder's bit writer (encode.bit) fed bits one at a time
def jpg.feed(bs: List<&2, Bool>, pp: Jenc.Put) -> Jenc.Put:
  match bs:
    case Nil{}:
      pp
    case bb <> rest:
      jpg.feed(rest, Jenc.encode.bit(pp, jpg.ubit(bb)))

# one AC token: a symbol and the magnitude bits after its code
type JTok is Data:
  JTok{sym: U32, ex: List<&2, Bool>}

# the code the encoder's AC book for a class (encode.acof: Annex K's luminance table, or chrominance when cls is set)
# holds for symbol sy, as its bits
def jpg.acode(+cls: Bool, +sy: U32) -> List<&2, Bool>:
  jpg.cbw(D2.jpg.val(Array.get(U32, Jenc.encode.acof(cls), sy)))

# the code the encoder's DC book for a class holds for symbol sy, as its bits
def jpg.dcode(+cls: Bool, +sy: U32) -> List<&2, Bool>:
  jpg.cbw(D2.jpg.val(Array.get(U32, Jenc.encode.dcof(cls), sy)))

# the bits of AC tokens: each symbol's code in a class's AC book, then its magnitude bits
def jpg.acbits(+cls: Bool, ts: List<&2, JTok>) -> List<&2, Bool>:
  match ts:
    case Nil{}:
      []
    case JTok{+sym, ex} <> rest:
      List.append(&2, Bool, jpg.acode(cls, sym), List.append(&2, Bool, ex, jpg.acbits(cls, rest)))

# the decoder's AC loop (decode.ac) as tokens follow it: the next index, the lookups left, and whether the block ended
type JAcSt is Data:
  JAcSt{kk: U32, left: Nat, fin: Bool}

# an empty list of bits
def jpg.isnil(xs: List<&2, Bool>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case _h <> _t:
      False{}

# the token's own check, by its kind: EOB with no bits, ZRL with no bits and room for 16 zeros, or a run and a
# nonzero size that stay inside the block, with as many magnitude bits as the size
def jpg.acok.k(eob: Bool, zrl: Bool, +sym: U32, ex: List<&2, Bool>, +kk: U32) -> Bool:
  match eob:
    case True{}:
      jpg.isnil(ex)
    case False{}:
      match zrl:
        case True{}:
          Bool.and(jpg.isnil(ex), Bool.or(U32.is_lt((kk + 16 : U32), 64), U32.is_eq((kk + 16 : U32), 64)))
        case False{}:
          Bool.and(Bool.not(U32.is_eq(U32.and(15, sym), 0)), Bool.and(Bool.not(U32.is_ge((kk + U32.shrn(sym, 4n) :
            U32), 64)), Nat.is_eq(List.length(&2, Bool, ex), U32.to_nat(U32.and(15, sym)))))

# the token is read in state st: the block has not ended, a lookup is left, the symbol is in the AC table
def jpg.acok(tt: JTok, st: JAcSt) -> Bool:
  match tt:
    case JTok{+sym, ex}:
      match st:
        case JAcSt{+kk, left, fin}:
          Bool.and(Bool.not(fin), Bool.and(Nat.is_lt(0n, left), Bool.and(jpg.memb(sym, Jenc.encode.acsyms()),
            jpg.acok.k(U32.is_eq(sym, 0), U32.is_eq(sym, 240), sym, ex, kk))))

# one less, and zero stays zero
def jpg.npred(nn: Nat) -> Nat:
  match nn:
    case 0n:
      0n
    case 1n+pp:
      pp

# the state after a token, by its kind
def jpg.acnx.k(eob: Bool, zrl: Bool, +sym: U32, +kk: U32, +left: Nat) -> JAcSt:
  match eob:
    case True{}:
      +_s = sym
      +_z = zrl
      JAcSt{kk, jpg.npred(left), True{}}
    case False{}:
      match zrl:
        case True{}:
          +_s = sym
          JAcSt{(kk + 16 : U32), jpg.npred(left), Bool.not(U32.is_lt((kk + 16 : U32), 64))}
        case False{}:
          +n2 = ((kk + U32.shrn(sym, 4n) : U32) + 1 : U32)
          JAcSt{n2, jpg.npred(left), U32.is_eq(n2, 64)}

# the state after a token
def jpg.acnx(tt: JTok, st: JAcSt) -> JAcSt:
  match tt:
    case JTok{+sym, _ex}:
      match st:
        case JAcSt{+kk, +left, _fin}:
          jpg.acnx.k(U32.is_eq(sym, 0), U32.is_eq(sym, 240), sym, kk, left)

# AC tokens the decoder's loop reads in full from state st, the block ending exactly at the last
def jpg.acwf(ts: List<&2, JTok>, +st: JAcSt) -> Bool:
  match ts:
    case Nil{}:
      match st:
        case JAcSt{_k, _l, fin}:
          fin
    case +tt <> rest:
      jpg.also(jpg.acok(tt, st), jpg.acwf(rest, jpg.acnx(tt, st)))

# one block's tokens: its class (luminance, or chrominance when cls is set), the DC symbol and its magnitude
# bits, then the AC tokens
type JBlkTok is Data:
  JBlkTok{cls: Bool, dcs: U32, dcx: List<&2, Bool>, acs: List<&2, JTok>}

# a block's bits: the DC symbol's code in its class's DC book, its magnitude bits, and the AC tokens' bits
def jpg.blkbits(bt: JBlkTok) -> List<&2, Bool>:
  match bt:
    case JBlkTok{+cls, +dcs, dcx, acs}:
      List.append(&2, Bool, jpg.dcode(cls, dcs), List.append(&2, Bool, dcx, jpg.acbits(cls, acs)))

# a block the decoder reads whole: a DC symbol of the DC table with as many magnitude bits as its size, and AC
# tokens read in full from index 1 with 63 lookups left, ending the block. Both classes' tables hold the same
# symbols
def jpg.blkwf(bt: JBlkTok) -> Bool:
  match bt:
    case JBlkTok{_c, +dcs, dcx, acs}:
      Bool.and(jpg.memb(dcs, Jenc.encode.dcsyms()), Bool.and(Nat.is_eq(List.length(&2, Bool, dcx), U32.to_nat(dcs)),
        jpg.acwf(acs, JAcSt{1, 63n, False{}})))

# the bits of blocks, one after another
def jpg.tbits(ts: List<&2, JBlkTok>) -> List<&2, Bool>:
  match ts:
    case Nil{}:
      []
    case tt <> rest:
      List.append(&2, Bool, jpg.blkbits(tt), jpg.tbits(rest))

# every block is one the decoder reads whole
def jpg.allwf(ts: List<&2, JBlkTok>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case tt <> rest:
      jpg.also(jpg.blkwf(tt), jpg.allwf(rest))

# a decode that returned a picture
def jpg.psome(mm: Maybe<&2, Jpeg.Pic>) -> Bool:
  match mm:
    case Some{_p}:
      True{}
    case None{}:
      False{}

# a bit as 0 or 1
def jpg.bitn(bb: Bool) -> U32:
  match bb:
    case True{}:
      1
    case False{}:
      0

# a block of class cls is one the decoder reads, at scan component cc, with the class's tables: its DC and AC
# Huffman tables and its frame component's quantisation table are table 1 for a chrominance block, else table 0
def jpg.clsok(+cls: Bool, +cc: U32, fr: Jpeg.Frame, sc: Jpeg.Scan) -> Bool:
  match fr:
    case Jpeg.Frame{_w, _h, _nf, +ids, _hs, _vs, +tq, _hm, _vm}:
      match sc:
        case Jpeg.Scan{_ns, +sids, +td, +ta, _ss, _se, _ah}:
          +kk = jpg.bitn(cls)
          Bool.and(U32.is_eq(Jpeg.decode.at(td, cc), kk), Bool.and(U32.is_eq(Jpeg.decode.at(ta, cc), kk),
            U32.is_eq(Jpeg.decode.at(tq, Jpeg.decode.index(ids, False{}, Jpeg.decode.at(sids, cc), 0)), kk)))

# the next of a component's data units while it has more, else the next component, else the first of the next MCU
def jpg.nxt.k(more: Bool, comp: Bool, +cc: U32, +bi: U32) -> U32 & U32:
  match more:
    case True{}:
      +_c = comp
      (cc, (bi + 1 : U32))
    case False{}:
      match comp:
        case True{}:
          +_b = bi
          ((cc + 1 : U32), 0)
        case False{}:
          +_u = (cc + bi : U32)
          (0, 0)

# the scan component and data unit of the block after data unit bi of scan component cc, in T.81's order
# (A.2.3): a component's hi * vi data units, then the next component's, then the next MCU's
def jpg.nxt(+cc: U32, +bi: U32, fr: Jpeg.Frame, sc: Jpeg.Scan) -> U32 & U32:
  match fr:
    case Jpeg.Frame{_w, _h, _nf, +ids, +hs, +vs, _tq, _hm, _vm}:
      match sc:
        case Jpeg.Scan{+ns, +sids, _td, _ta, _ss, _se, _ah}:
          +fi = Jpeg.decode.index(ids, False{}, Jpeg.decode.at(sids, cc), 0)
          jpg.nxt.k(U32.is_lt((bi + 1 : U32), (Jpeg.decode.at(hs, fi) * Jpeg.decode.at(vs, fi) : U32)),
            U32.is_lt((cc + 1 : U32), ns), cc, bi)

# blocks from the place nx on (a scan component and a data unit of it), each of the class the decoder's tables at
# its place hold
def jpg.tagok(ts: List<&2, JBlkTok>, nx: U32 & U32, +fr: Jpeg.Frame, +sc: Jpeg.Scan) -> Bool:
  match ts:
    case Nil{}:
      match nx:
        case (+cc, +bi):
          +_u = (cc + bi : U32)
          True{}
    case JBlkTok{+cls, _d, _x, _a} <> rest:
      match nx:
        case (+cc, +bi):
          jpg.also(jpg.clsok(cls, cc, fr, sc), jpg.tagok(rest, jpg.nxt(cc, bi, fr, sc), fr, sc))

# a scan's blocks in order, from its first (scan component 0, data unit 0), each of the class the decoder's
# tables at its place hold
def jpg.inorder(ts: List<&2, JBlkTok>, +fr: Jpeg.Frame, +sc: Jpeg.Scan) -> Bool:
  jpg.tagok(ts, (0, 0), fr, sc)

# LAW: the scan side of the JPEG round trip. Take blocks the decoder reads whole: each a DC symbol of an Annex K
# DC table with its magnitude bits, then AC tokens of an AC table (EOB, ZRL, or a run and a nonzero size with its
# magnitude bits) that fill or end the block, each block of the class (luminance or chrominance) whose tables the
# decoder holds at its place in the scan. Write as many of them as the encoder's frame has blocks, each symbol as
# the code the encoder's book for its class (encode.dcof, encode.acof) holds for it, with the encoder's bit writer
# (encode.bit, then encode.pad). decode.run, in the encoder's frame of sides 1 to 65535 and at most 2^31 points,
# scan and tables at any quality, decodes those bytes to a picture: each block takes at least two bits, so the
# bytes are enough for the blocks
law jpeg_scan_some:
  for +tt: JBlkTok
  for +rest: List<&2, JBlkTok>
  for +ww: U32
  for +hh: U32
  for +qq: U32
  for h_w: {U32.is_eq(ww, 0) == False{} : Bool}
  for h_h: {U32.is_eq(hh, 0) == False{} : Bool}
  for h_wl: {U32.is_le(ww, 65535) == True{} : Bool}
  for h_hl: {U32.is_le(hh, 65535) == True{} : Bool}
  for h_area: {U32.is_le((ww * hh : U32), 2147483648) == True{} : Bool}
  for h_wf: {jpg.allwf(tt <> rest) == True{} : Bool}
  for h_tag: {jpg.inorder(tt <> rest, jpg.enc.frame(ww, hh), jpg.enc.scan()) == True{} : Bool}
  for h_n: {U32.to_nat(Jpeg.decode.nblocks(ww, hh, [1, 1, 1], [1, 1, 1], 1, 1)) == 1n+List.length(&2, JBlkTok, rest) :
    Nat}
  {jpg.psome(Jpeg.decode.run(jpg.enc.frame(ww, hh), jpg.enc.scan(), jpg.enc.tabs(qq), Jenc.encode.pad(jpg.feed(
    jpg.tbits(tt <> rest), Jenc.encode.put0())), 0, False{})) == True{} : Bool}

# LAW: for every raster encode_jpeg writes and every quality, decode_jpeg of encode_jpeg_q's bytes is some raster.
# encode.arm writes, through the encoder's bit writer, three blocks per MCU, Y with the luminance books and Cb and
# Cr with the chrominance books, that the decoder reads whole (each DC clipped to T.81's 8-bit range, so its
# difference has at most 11 bits), and the MCU count times 3 is decode.nblocks of the encoder's frame with no U32
# wrap, so jpeg_scan_some applies. With jpeg_round_trip_sized (a raster of r's size) and jpeg_decode_opaque (alpha
# 255) this is laws/JpegRoundTripKeepsSize.bend
law jpeg_round_trip_some_q:
  for +ww: U32
  for +hh: U32
  for +qq: U32
  for +px: List<&2, U32>
  for +h_good: {Img.encode_jpeg.good(ww, hh, px) == True{} : Bool}
  {Maybe.is_some(&2, Img.Raster, jpg.back(Img.encode_jpeg_q(Img.Raster{ww, hh, px}, qq))) == True{} : Bool}

# LAW: for every raster encode_jpeg writes, decode_jpeg of encode_jpeg's bytes is some raster: encode_jpeg is
# encode_jpeg_q at quality 75
law jpeg_round_trip_some:
  for +ww: U32
  for +hh: U32
  for +px: List<&2, U32>
  for +h_good: {Img.encode_jpeg.good(ww, hh, px) == True{} : Bool}
  {Maybe.is_some(&2, Img.Raster, jpg.back(Img.encode_jpeg(Img.Raster{ww, hh, px}))) == True{} : Bool}

# a decode's samples, when it returned a raster, all have alpha 255
def jpg.opq(mm: Maybe<&2, Img.Raster>) -> Bool:
  match mm:
    case None{}:
      True{}
    case Some{img}:
      D1.all.opaque(Img.pixels(img), True{})

# a decode that is some raster of width w and height h, every sample of it with alpha 255
def jpg.round(+mm: Maybe<&2, Img.Raster>, +ww: U32, +hh: U32) -> Bool:
  Bool.and(Bool.and(Maybe.is_some(&2, Img.Raster, mm), jpg.sized(mm, ww, hh)), jpg.opq(mm))

# LAW: for every raster r encode_jpeg writes and every quality q, decode_jpeg(encode_jpeg_q(r, q)) is some raster
# of r's width and height, every sample of it with alpha 255: jpeg_round_trip_some_q, jpeg_round_trip_sized and
# jpeg_decode_opaque together. It needs no bound on the samples: sides of at most 65535 keep the MCU count's
# product, times 3, below 2^32
law jpeg_round_trip_q:
  for +ww: U32
  for +hh: U32
  for +qq: U32
  for +px: List<&2, U32>
  for +h_good: {Img.encode_jpeg.good(ww, hh, px) == True{} : Bool}
  {jpg.round(jpg.back(Img.encode_jpeg_q(Img.Raster{ww, hh, px}, qq)), ww, hh) == True{} : Bool}

# LAW: for every raster r encode_jpeg writes, decode_jpeg(encode_jpeg(r)) is some raster of r's width and height,
# every sample of it with alpha 255
law jpeg_round_trip:
  for +ww: U32
  for +hh: U32
  for +px: List<&2, U32>
  for +h_good: {Img.encode_jpeg.good(ww, hh, px) == True{} : Bool}
  {jpg.round(jpg.back(Img.encode_jpeg(Img.Raster{ww, hh, px})), ww, hh) == True{} : Bool}
