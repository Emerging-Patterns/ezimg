# src/inflate: zlib-wrapped DEFLATE for a PNG IDAT stream (compression
# method 0). Blocks are stored, fixed Huffman, or dynamic Huffman.
import Base

# where the bit reader is
type Ph is Data:
  PByte{}
  PAlign{}
  PSym{}
  PDone{}
  PFail{}

# which integer the bit reader is filling
type Md is Data:
  MCmf{}
  MFlg{}
  MBlk{}
  MLen{}
  MNlen{}
  MData{}
  MHlit{}
  MHdist{}
  MHclen{}
  MClen{}
  MXlen{}
  MXdist{}
  MAdler{}
  MRep{}

# which Huffman table a symbol is read from
type Wh is Data:
  WLit{}
  WDist{}
  WClen{}

# one inflate reader: phase, tables, and the bytes emitted newest-first
type St is Data:
  St{ph: Ph, md: Md, wh: Wh, +acc: U32, +got: U32, +need: U32, final: Bool, +left: U32, +dist: U32, out: List<&2, U32>,
    lit: List<&2, U32>, dts: List<&2, U32>, clen: List<&2, U32>, lens: List<&2, U32>, +nleft: U32, +prev: U32,
      +cmf: U32, +hacc: U32, +hlen: U32, +skew: U32, +hlit: U32, +hdist: U32, +run: U32, +sym: U32, +rep: U32}

# build a reader
def st.make(
  ph: Ph,
  md: Md,
  wh: Wh,
  +acc: U32,
  +got: U32,
  +need: U32,
  final: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +hacc: U32,
  +hlen: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  St{ph, md, wh, acc, got, need, final, left, dist, out, lit, dts, clen, lens, nleft, prev, cmf, hacc, hlen, skew, hlit,
    hdist, run, sym, rep}

# a reader that has failed
def st.fail() -> St:
  st.make(PFail{}, MCmf{}, WLit{}, 0, 0, 0, False{}, 0, 0, [], [], [], [], [], 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)

# the reader before the first byte
def st.empty() -> St:
  st.make(PByte{}, MCmf{}, WLit{}, 0, 0, 8, False{}, 0, 0, [], [], [], [], [], 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)

# pick a reader
def st.gate(zz: Bool, aa: St, bb: St) -> St:
  match zz:
    case True{}:
      aa
    case False{}:
      bb

# Huffman tables
# --------------

# sixteen zeros, or nineteen: a code-length histogram
def huff.zeros(nn: Nat) -> List<&2, U32>:
  match nn:
    case 0n:
      Nil{}
    case 1n+p:
      0 <> huff.zeros(p)

# the value at an index, or zero past the end
def huff.at.put(+hh: U32, +rest: U32, zz: Bool) -> U32:
  match zz:
    case True{}:
      hh
    case False{}:
      rest

# the value at an index
def huff.at(xs: List<&2, U32>, +ii: U32) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{+h, t}:
      huff.at.put(h, huff.at(t, (ii - 1 : U32)), U32.is_zero(ii))

# write an index. The Bool is "this is the slot".
def huff.set(xs: List<&2, U32>, zz: Bool, +ii: U32, +vv: U32) -> List<&2, U32>:
  match xs zz:
    case Nil{} _z:
      Nil{}
    case Con{_h, t} True{}:
      vv <> t
    case Con{+h, t} False{}:
      h <> huff.set(t, U32.is_zero((ii - 1 : U32)), (ii - 1 : U32), vv)

# count a nonzero length
def huff.bump(+acc: List<&2, U32>, +L: U32, zz: Bool) -> List<&2, U32>:
  match zz:
    case True{}:
      acc
    case False{}:
      huff.set(acc, U32.is_zero(L), L, (huff.at(acc, L) + 1 : U32))

# bl_count, index is the length. Zeros are not counted.
def huff.count(ls: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match ls:
    case Nil{}:
      acc
    case Con{+L, t}:
      huff.count(t, huff.bump(acc, L, U32.is_zero(L)))

# next_code, built newest-first
def huff.next(counts: List<&2, U32>, +code: U32, +prev: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match counts:
    case Nil{}:
      acc
    case Con{+cnt, rest}:
      +code2 = (((code + prev : U32) << 1n) : U32)
      huff.next(rest, code2, cnt, code2 <> acc)

# next_code[0] is zero, then one slot per length from 1
def huff.nexts(counts: List<&2, U32>) -> List<&2, U32>:
  match counts:
    case Nil{}:
      [0]
    case Con{+c0, rest}:
      0 <> List.reverse(&2, U32, huff.next(rest, 0, c0, []))

# pack length, canonical code, and symbol into one word
def huff.pack(+len: U32, +code: U32, +sym: U32) -> U32:
  ((((len << 16n : U32) .|. code : U32) << 9n : U32) .|. sym : U32)

# the symbol in a packed entry
def huff.sym(+ee: U32) -> U32:
  (ee .&. 511 : U32)

# the code in a packed entry
def huff.code(+ee: U32) -> U32:
  ((ee >> 9n : U32) .&. 65535 : U32)

# the length in a packed entry
def huff.len(+ee: U32) -> U32:
  ((ee >> 25n : U32) .&. 15 : U32)

# does this entry match the bits read so far?
def huff.hit(+ee: U32, +code: U32, +len: U32) -> Bool:
  Bool.and(U32.is_eq(huff.len(ee), len), U32.is_eq(huff.code(ee), code))

# keep the symbol when the entry matches
def huff.find.put(+sym: U32, rest: Maybe<&2, U32>, hit: Bool) -> Maybe<&2, U32>:
  match hit:
    case True{}:
      Some{sym}
    case False{}:
      rest

# the symbol whose canonical code is these bits
def huff.find(tab: List<&2, U32>, +code: U32, +len: U32) -> Maybe<&2, U32>:
  match tab:
    case Nil{}:
      None{}
    case +e <> t:
      huff.find.put(huff.sym(e), huff.find(t, code, len), huff.hit(e, code, len))

# cons a packed entry when the length is not zero
def huff.keep(acc: List<&2, U32>, +sym: U32, +len: U32, +code: U32, zz: Bool) -> List<&2, U32>:
  match zz:
    case True{}:
      acc
    case False{}:
      huff.pack(len, code, sym) <> acc

# advance next_code at this length when it was used
def huff.step(+nexts: List<&2, U32>, +len: U32, zz: Bool) -> List<&2, U32>:
  match zz:
    case True{}:
      nexts
    case False{}:
      huff.set(nexts, U32.is_zero(len), len, (huff.at(nexts, len) + 1 : U32))

# assign canonical codes in symbol order
def huff.assign(ls: List<&2, U32>, +sym: U32, +nexts: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match ls:
    case Nil{}:
      List.reverse(&2, U32, acc)
    case Con{+len, t}:
      huff.assign(t, (sym + 1 : U32), huff.step(nexts, len, U32.is_zero(len)), huff.keep(acc, sym, len, huff.at(nexts,
        len), U32.is_zero(len)))

# canonical Huffman table from a length per symbol
def huff.canon(+ls: List<&2, U32>) -> List<&2, U32>:
  huff.assign(ls, 0, huff.nexts(huff.count(ls, huff.zeros(16n))), [])

# fixed literal/length code length at a symbol
def lit.len2(cc: Bool) -> U32:
  match cc:
    case True{}:
      7
    case False{}:
      8

# fixed literal/length code length, past 143
def lit.len1(bb: Bool, cc: Bool) -> U32:
  match bb:
    case True{}:
      9
    case False{}:
      lit.len2(cc)

# fixed literal/length code length
def lit.len(+_s: U32, aa: Bool, bb: Bool, cc: Bool) -> U32:
  match aa:
    case True{}:
      8
    case False{}:
      lit.len1(bb, cc)

# lengths 0..i, oldest first once i runs down to zero
def lit.lens(ii: Nat, acc: List<&2, U32>) -> List<&2, U32>:
  match ii:
    case 0n:
      lit.len(0, True{}, True{}, True{}) <> acc
    case 1n++p:
      +s = U32.from_nat(1n+p)
      lit.lens(p, lit.len(s, U32.is_le(s, 143), U32.is_le(s, 255), U32.is_le(s, 279)) <> acc)

# the fixed literal/length table
def lit.fixed() -> List<&2, U32>:
  huff.canon(lit.lens(287n, []))

# thirty-two distance lengths of 5
def dist.lens(nn: Nat) -> List<&2, U32>:
  match nn:
    case 0n:
      Nil{}
    case 1n+p:
      5 <> dist.lens(p)

# the fixed distance table
def dist.fixed() -> List<&2, U32>:
  huff.canon(dist.lens(32n))

# length bases for symbols 257..285
def len.base() -> List<&2, U32>:
  [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258]

# extra bits for symbols 257..285
def len.extra() -> List<&2, U32>:
  [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0]

# distance bases
def dist.base() -> List<&2, U32>:
  [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145,
    8193, 12289, 16385, 24577]

# extra bits for distances
def dist.extra() -> List<&2, U32>:
  [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13]

# code-length symbol order
def clen.order() -> List<&2, U32>:
  [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]

# drop code-length values into the 19 symbol slots
def clen.place(order: List<&2, U32>, lens: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match order lens:
    case Nil{} _ls:
      acc
    case _od Nil{}:
      acc
    case Con{+i, ot} Con{+L, lt}:
      clen.place(ot, lt, huff.set(acc, U32.is_zero(i), i, L))

# repeat a length n times onto the front of the list
def lens.rep(kk: Nat, +vv: U32, lens: List<&2, U32>) -> List<&2, U32>:
  match kk:
    case 0n:
      lens
    case 1n+p:
      lens.rep(p, vv, vv <> lens)

# the two halves of a code-length list
type lens.Split is Data:
  lens.Split{lo: List<&2, U32>, hi: List<&2, U32>}

# split a list after n elements. The Bool is "n is zero".
def lens.split(xs: List<&2, U32>, zz: Bool, +nn: U32, acc: List<&2, U32>) -> Maybe<&2, lens.Split>:
  match xs zz:
    case rest True{}:
      Some{lens.Split{List.reverse(&2, U32, acc), rest}}
    case Nil{} False{}:
      None{}
    case Con{+h, t} False{}:
      lens.split(t, U32.is_zero((nn - 1 : U32)), (nn - 1 : U32), h <> acc)

# bits, Adler, and back-references
# --------------------------------

# eight bits of a byte, low bit at the head
def bits.push(ii: Nat, +bb: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match ii:
    case 0n:
      (1 .&. bb : U32) <> acc
    case 1n++p:
      bits.push(p, bb, ((1 .&. (bb >> (1n+p) : U32) : U32) <> acc))

# one bit list per byte
def bits.rows(xs: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+b, t}:
      bits.push(7n, b, []) <> bits.rows(t)

# the bit stream, low bit of each byte first
def bits.of(xs: List<&2, U32>) -> List<&2, U32>:
  List.concat(&2, U32, bits.rows(xs))

# Adler-32, one byte at a time
def adler.go(xs: List<&2, U32>, +aa: U32, +bb: U32) -> U32 & U32:
  match xs:
    case Nil{}:
      (bb, aa)
    case Con{+x, t}:
      +a2 = ((aa + x : U32) % 65521 : U32)
      +b2 = ((bb + a2 : U32) % 65521 : U32)
      adler.go(t, a2, b2)

# pack the two Adler sums
def adler.fin(pp: U32 & U32) -> U32:
  match pp:
    case (+b, +a):
      ((b << 16n : U32) .|. a : U32)

# Adler-32 of chronological bytes
def adler.of(xs: List<&2, U32>) -> U32:
  adler.fin(adler.go(xs, 1, 0))

# the byte `i` from the head
def copy.nth.put(+hh: U32, rest: Maybe<&2, U32>, zz: Bool) -> Maybe<&2, U32>:
  match zz:
    case True{}:
      Some{hh}
    case False{}:
      rest

# the byte `i` from the head, or none
def copy.nth(xs: List<&2, U32>, +ii: U32) -> Maybe<&2, U32>:
  match xs:
    case Nil{}:
      None{}
    case Con{+h, t}:
      copy.nth.put(h, copy.nth(t, (ii - 1 : U32)), U32.is_zero(ii))

# copy `n` bytes from `dist` back. `m` is the next byte, already read.
def copy.run(nn: Nat, mm: Maybe<&2, U32>, +dist: U32, +out: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match nn mm:
    case 0n _m:
      Some{out}
    case _n None{}:
      None{}
    case 1n+p Some{+b}:
      +out2 = {b <> out : List<&2, U32>}
      copy.run(p, copy.nth(out2, (dist - 1 : U32)), dist, out2)

# copy `len` bytes from `dist` back into a newest-first buffer
def copy.start(+len: U32, +dist: U32, +out: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  copy.run(U32.to_nat(len), copy.nth(out, (dist - 1 : U32)), dist, out)

# the reader, one bit at a time
# ------------------------------

# start the field `md` asks for, now that the stream is aligned
def rd.begin(
  md: Md,
  wh: Wh,
  final: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  match md:
    case MLen{}:
      st.make(PByte{}, MLen{}, wh, 0, 0, 16, final, left, dist, out, lit, dts, clen, lens, nleft, prev, cmf, 0, 0, skew,
        hlit, hdist, run, sym, rep)
    case MAdler{}:
      st.make(PByte{}, MAdler{}, wh, 0, 0, 8, final, 4, dist, out, lit, dts, clen, lens, nleft, prev, cmf, 0, 0, skew,
        hlit, hdist, 0, sym, rep)
    case _md:
      st.fail()

# a byte-aligned field starts, or a padding bit is still waiting
def rd.align(
  zz: Bool,
  md: Md,
  wh: Wh,
  final: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  match zz:
    case False{}:
      st.make(PAlign{}, md, wh, 0, 0, 0, final, left, dist, out, lit, dts, clen, lens, nleft, prev, cmf, 0, 0, skew,
        hlit, hdist, run, sym, rep)
    case True{}:
      rd.begin(md, wh, final, left, dist, out, lit, dts, clen, lens, nleft, prev, cmf, skew, hlit, hdist, run, sym, rep)

# skip bits up to the next byte, then read `md`
def rd.to_align(
  md: Md,
  wh: Wh,
  final: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  rd.align(U32.is_zero(skew), md, wh, final, left, dist, out, lit, dts, clen, lens, nleft, prev, cmf, skew, hlit, hdist,
    run, sym, rep)

# a fresh integer field of `need` bits
def rd.byte(
  md: Md,
  wh: Wh,
  +need: U32,
  final: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  st.make(PByte{}, md, wh, 0, 0, need, final, left, dist, out, lit, dts, clen, lens, nleft, prev, cmf, 0, 0, skew, hlit,
    hdist, run, sym, rep)

# the next block, or the Adler checksum when this was the last block
def rd.after(
  final: Bool,
  wh: Wh,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  match final:
    case True{}:
      rd.to_align(MAdler{}, wh, final, left, dist, out, lit, dts, clen, lens, nleft, prev, cmf, skew, hlit, hdist, run,
        sym, rep)
    case False{}:
      rd.byte(MBlk{}, wh, 3, final, left, dist, out, lit, dts, clen, lens, nleft, prev, cmf, skew, hlit, hdist, run,
        sym, rep)

# literal/length or distance symbols
def rd.sym(
  wh: Wh,
  final: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  st.make(PSym{}, MBlk{}, wh, 0, 0, 0, final, left, dist, out, lit, dts, clen, lens, nleft, prev, cmf, 0, 0, skew, hlit,
    hdist, run, sym, rep)

# the table a symbol is drawn from
def rd.tree(wh: Wh, +lit: List<&2, U32>, +dts: List<&2, U32>, +clen: List<&2, U32>) -> List<&2, U32>:
  match wh:
    case WLit{}:
      lit
    case WDist{}:
      dts
    case WClen{}:
      clen

# CMF: method 8, window at most 32K
def rd.cmf(
  +val: U32,
  wh: Wh,
  final: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  +ok = Bool.and(U32.is_eq((val .&. 15 : U32), 8), U32.is_le((val >> 4n : U32), 7))
  st.gate(ok, rd.byte(MFlg{}, wh, 8, final, left, dist, out, lit, dts, clen, lens, nleft, prev, val, skew, hlit, hdist,
    run, sym, rep), st.fail())

# FLG: the header check, and no preset dictionary
def rd.flg(
  +val: U32,
  wh: Wh,
  final: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  +sum = (((cmf << 8n : U32) + val : U32) % 31 : U32)
  +ok = Bool.and(U32.is_zero(sum), U32.is_zero((val .&. 32 : U32)))
  st.gate(ok, rd.byte(MBlk{}, wh, 3, final, left, dist, out, lit, dts, clen, lens, nleft, prev, cmf, skew, hlit, hdist,
    run, sym, rep), st.fail())

# dynamic header, or a reserved block type
def rd.blk.dyn(
  final: Bool,
  z2: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  match z2:
    case True{}:
      rd.byte(MHlit{}, WLit{}, 5, final, left, dist, out, [], [], clen, lens, nleft, prev, cmf, skew, hlit, hdist, run,
        sym, rep)
    case False{}:
      st.fail()

# fixed or dynamic Huffman
def rd.blk.huff(
  final: Bool,
  z1: Bool,
  z2: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  match z1:
    case True{}:
      rd.sym(WLit{}, final, left, dist, out, lit.fixed(), dist.fixed(), clen, lens, nleft, prev, cmf, skew, hlit, hdist,
        run, sym, rep)
    case False{}:
      rd.blk.dyn(final, z2, left, dist, out, clen, lens, nleft, prev, cmf, skew, hlit, hdist, run, sym, rep)

# dispatch on the block type
def rd.blk.go(
  final: Bool,
  z0: Bool,
  z1: Bool,
  z2: Bool,
  wh: Wh,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  match z0:
    case True{}:
      rd.to_align(MLen{}, wh, final, left, dist, out, lit, dts, clen, lens, nleft, prev, cmf, skew, hlit, hdist, run,
        sym, rep)
    case False{}:
      rd.blk.huff(final, z1, z2, left, dist, out, clen, lens, nleft, prev, cmf, skew, hlit, hdist, run, sym, rep)

# BFINAL is the low bit. BTYPE is the next two.
def rd.blk.at(
  +finb: U32,
  +bt: U32,
  wh: Wh,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  rd.blk.go(U32.is_eq(finb, 1), U32.is_eq(bt, 0), U32.is_eq(bt, 1), U32.is_eq(bt, 2), wh, left, dist, out, lit, dts,
    clen, lens, nleft, prev, cmf, skew, hlit, hdist, run, sym, rep)

# a stored block, a fixed block, or a dynamic block
def rd.blk(
  +val: U32,
  wh: Wh,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  rd.blk.at((val .&. 1 : U32),
    (val >> 1n : U32), wh, left, dist, out, lit, dts, clen, lens, nleft, prev, cmf, skew, hlit, hdist, run, sym, rep)

# stored LEN, then NLEN
def rd.len(
  +val: U32,
  wh: Wh,
  final: Bool,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  rd.byte(MNlen{}, wh, 16, final, val, dist, out, lit, dts, clen, lens, nleft, prev, cmf, skew, hlit, hdist, run, sym,
    rep)

# an empty stored block ends the block; otherwise the bytes follow
def rd.nlen.ok(
  zz: Bool,
  wh: Wh,
  final: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  match zz:
    case True{}:
      rd.after(final, wh, left, dist, out, lit, dts, clen, lens, nleft, prev, cmf, skew, hlit, hdist, run, sym, rep)
    case False{}:
      rd.byte(MData{}, wh, 8, final, left, dist, out, lit, dts, clen, lens, nleft, prev, cmf, skew, hlit, hdist, run,
        sym, rep)

# NLEN is the one's complement of LEN
def rd.nlen(
  +val: U32,
  wh: Wh,
  final: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  st.gate(U32.is_eq(val, (left .^. 65535 : U32)), rd.nlen.ok(U32.is_zero(left), wh, final, left, dist, out, lit, dts,
    clen, lens, nleft, prev, cmf, skew, hlit, hdist, run, sym, rep), st.fail())

# one stored byte, newest-first
def rd.data.z(
  zz: Bool,
  wh: Wh,
  final: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  match zz:
    case True{}:
      rd.after(
        final, wh, left, dist, out, lit, dts, clen, lens,
        nleft, prev, cmf, skew, hlit, hdist, run, sym, rep
      )
    case False{}:
      rd.byte(
        MData{}, wh, 8, final, left, dist, out, lit, dts, clen, lens,
        nleft, prev, cmf, skew, hlit, hdist, run, sym, rep
      )

# consume one stored byte
def rd.data(
  +val: U32,
  wh: Wh,
  final: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  +left2 = (left - 1 : U32)
  +out2 = {val <> out : List<&2, U32>}
  rd.data.z(
    U32.is_zero(left2), wh, final, left2, dist, out2, lit, dts, clen, lens,
    nleft, prev, cmf, skew, hlit, hdist, run, sym, rep
  )

# HLIT, then HDIST
def rd.hlit(
  +val: U32,
  wh: Wh,
  final: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  rd.byte(
    MHdist{}, wh, 5, final, left, dist, out, lit, dts, clen, lens,
    nleft, prev, cmf, skew, val, hdist, run, sym, rep
  )

# HDIST, then HCLEN
def rd.hdist(
  +val: U32,
  wh: Wh,
  final: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  rd.byte(
    MHclen{}, wh, 4, final, left, dist, out, lit, dts, clen, lens,
    nleft, prev, cmf, skew, hlit, val, run, sym, rep
  )

# HCLEN, then that many 3-bit code lengths
def rd.hclen(
  +val: U32,
  wh: Wh,
  final: Bool,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  rd.byte(
    MClen{}, wh, 3, final, (val + 4 : U32), dist, out, lit, dts, clen, [],
    nleft, prev, cmf, skew, hlit, hdist, run, sym, rep
  )

# code lengths are in. Build the code-length table and read the rest.
def rd.clen.z(
  zz: Bool,
  wh: Wh,
  final: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  +lens: List<&2, U32>,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  match zz:
    case False{}:
      rd.byte(
        MClen{}, wh, 3, final, left, dist, out, lit, dts, [], lens,
        0, prev, cmf, skew, hlit, hdist, run, sym, rep
      )
    case True{}:
      +placed = clen.place(clen.order(), List.reverse(&2, U32, lens), huff.zeros(19n))
      +nleft = ((hlit + 257 : U32) + (hdist + 1 : U32) : U32)
      rd.sym(
        WClen{}, final, left, 0, out, lit, dts, huff.canon(placed), [],
        nleft, 0, cmf, skew, hlit, hdist, run, sym, rep
      )

# one 3-bit code length
def rd.clen(
  +val: U32,
  wh: Wh,
  final: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  lens: List<&2, U32>,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  +left2 = (left - 1 : U32)
  +lens2 = {val <> lens : List<&2, U32>}
  rd.clen.z(
    U32.is_zero(left2), wh, final, left2, dist, out, lit, dts, lens2,
    prev, cmf, skew, hlit, hdist, run, sym, rep
  )

# literal/length symbols again, after a distance
def rd.back(
  _wh: Wh,
  final: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  rd.sym(WLit{}, final, left, dist, out, lit, dts, clen, lens, nleft, prev, cmf, skew, hlit, hdist, run, sym, rep)

# install the copied bytes, or fail
def rd.copied(
  mm: Maybe<&2, List<&2, U32>>,
  wh: Wh,
  final: Bool,
  +left: U32,
  +dist: U32,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  match mm:
    case None{}:
      st.fail()
    case Some{out2}:
      rd.back(
        wh, final, left, dist, out2, lit, dts, clen, lens,
        nleft, prev, cmf, skew, hlit, hdist, run, sym, rep
      )

# copy `left` bytes from `dist` back
def rd.docopy(
  wh: Wh,
  final: Bool,
  +left: U32,
  +dist: U32,
  +out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  rd.copied(
    copy.start(left, dist, out), wh, final, left, dist, lit, dts, clen, lens,
    nleft, prev, cmf, skew, hlit, hdist, run, sym, rep
  )

# extra distance bits are in `dist` as the base
def rd.xdist(
  +val: U32,
  wh: Wh,
  final: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  rd.docopy(
    wh, final, left, (dist + val : U32), out, lit, dts, clen, lens,
    nleft, prev, cmf, skew, hlit, hdist, run, sym, rep
  )

# no extra distance bits: the base is the distance
def rd.xdist0(
  zz: Bool,
  +extra: U32,
  +base: U32,
  wh: Wh,
  final: Bool,
  +left: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  match zz:
    case True{}:
      rd.docopy(
        wh, final, left, base, out, lit, dts, clen, lens,
        nleft, prev, cmf, skew, hlit, hdist, run, sym, rep
      )
    case False{}:
      rd.byte(
        MXdist{}, wh, extra, final, left, base, out, lit, dts, clen, lens,
        nleft, prev, cmf, skew, hlit, hdist, run, sym, rep
      )

# a distance symbol
def rd.distsym(
  +sy: U32,
  zz: Bool,
  wh: Wh,
  final: Bool,
  +left: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +rep: U32
) -> St:
  match zz:
    case False{}:
      st.fail()
    case True{}:
      rd.xdist0(
        U32.is_zero(huff.at(dist.extra(), sy)), huff.at(dist.extra(), sy),
        huff.at(dist.base(), sy), wh, final, left, out, lit, dts, clen, lens,
        nleft, prev, cmf, skew, hlit, hdist, run, sy, rep
      )

# extra length bits added to the base kept in `left`
def rd.xlen(
  +val: U32,
  _wh: Wh,
  final: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  rd.sym(
    WDist{}, final, (left + val : U32), dist, out, lit, dts, clen, lens,
    nleft, prev, cmf, skew, hlit, hdist, run, sym, rep
  )

# no extra length bits
def rd.xlen0(
  zz: Bool,
  +extra: U32,
  +base: U32,
  wh: Wh,
  final: Bool,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  match zz:
    case True{}:
      rd.sym(
        WDist{}, final, base, dist, out, lit, dts, clen, lens,
        nleft, prev, cmf, skew, hlit, hdist, run, sym, rep
      )
    case False{}:
      rd.byte(
        MXlen{}, wh, extra, final, base, dist, out, lit, dts, clen, lens,
        nleft, prev, cmf, skew, hlit, hdist, run, sym, rep
      )

# a length symbol, or the end of the block
def rd.lit.n(
  zz: Bool,
  +sy: U32,
  wh: Wh,
  final: Bool,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +rep: U32
) -> St:
  match zz:
    case False{}:
      st.fail()
    case True{}:
      +ix = (sy - 257 : U32)
      rd.xlen0(
        U32.is_zero(huff.at(len.extra(), ix)), huff.at(len.extra(), ix),
        huff.at(len.base(), ix), wh, final, dist, out, lit, dts, clen, lens,
        nleft, prev, cmf, skew, hlit, hdist, run, sy, rep
      )

# end of block, or a length code
def rd.lit.e(
  zend: Bool,
  zlen: Bool,
  +sy: U32,
  wh: Wh,
  final: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +rep: U32
) -> St:
  match zend:
    case True{}:
      rd.after(
        final, wh, left, dist, out, lit, dts, clen, lens,
        nleft, prev, cmf, skew, hlit, hdist, run, sy, rep
      )
    case False{}:
      rd.lit.n(
        zlen, sy, wh, final, dist, out, lit, dts, clen, lens,
        nleft, prev, cmf, skew, hlit, hdist, run, rep
      )

# a literal byte
def rd.lit(
  zlit: Bool,
  zend: Bool,
  zlen: Bool,
  +sy: U32,
  wh: Wh,
  final: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +rep: U32
) -> St:
  match zlit:
    case True{}:
      st.make(
        PSym{}, MBlk{}, WLit{}, 0, 0, 0, final, left, dist,
        {sy <> out : List<&2, U32>}, lit, dts, clen, lens, nleft, prev, cmf,
        0, 0, skew, hlit, hdist, run, sy, rep
      )
    case False{}:
      rd.lit.e(
        zend, zlen, sy, wh, final, left, dist, out, lit, dts, clen, lens,
        nleft, prev, cmf, skew, hlit, hdist, run, rep
      )

# both Huffman tables are built
def rd.finish.at(
  mm: Maybe<&2, lens.Split>,
  _wh: Wh,
  final: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  clen: List<&2, U32>,
  +_nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  match mm:
    case None{}:
      st.fail()
    case Some{lens.Split{lits, dists}}:
      rd.sym(
        WLit{}, final, left, dist, out, huff.canon(lits), huff.canon(dists),
        clen, [], 0, prev, cmf, skew, hlit, hdist, run, sym, rep
      )

# split the length list into literal and distance tables
def rd.finish(
  +lens: List<&2, U32>,
  wh: Wh,
  final: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  clen: List<&2, U32>,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  +chron = List.reverse(&2, U32, lens)
  +nlit = (hlit + 257 : U32)
  rd.finish.at(
    lens.split(chron, U32.is_zero(nlit), nlit, []), wh, final, left, dist,
    out, clen, 0, prev, cmf, skew, hlit, hdist, run, sym, rep
  )

# a code length was stored. `dist` is 1 once any length exists.
def rd.push(
  zz: Bool,
  +prev: U32,
  +nleft: U32,
  lens: List<&2, U32>,
  wh: Wh,
  final: Bool,
  +left: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  match zz:
    case True{}:
      rd.finish(
        lens, wh, final, left, 1, out, clen, prev, cmf, skew,
        hlit, hdist, run, sym, rep
      )
    case False{}:
      rd.sym(
        WClen{}, final, left, 1, out, lit, dts, clen, lens, nleft, prev,
        cmf, skew, hlit, hdist, run, sym, rep
      )

# code 16 needs a previous length
def rd.rep16(
  zz: Bool,
  wh: Wh,
  final: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +_rep: U32
) -> St:
  match zz:
    case True{}:
      st.fail()
    case False{}:
      rd.byte(
        MRep{}, wh, 2, final, left, dist, out, lit, dts, clen, lens,
        nleft, prev, cmf, skew, hlit, hdist, run, sym, 3
      )

# code 18, or an illegal code-length symbol
def rd.clen.t(
  z18: Bool,
  wh: Wh,
  final: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32
) -> St:
  match z18:
    case True{}:
      rd.byte(
        MRep{}, wh, 7, final, left, dist, out, lit, dts, clen, lens,
        nleft, 0, cmf, skew, hlit, hdist, run, sym, 11
      )
    case False{}:
      st.fail()

# codes 17 and 18 repeat zero
def rd.clen.s(
  z17: Bool,
  z18: Bool,
  wh: Wh,
  final: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +_prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32
) -> St:
  match z17:
    case True{}:
      rd.byte(
        MRep{}, wh, 3, final, left, dist, out, lit, dts, clen, lens,
        nleft, 0, cmf, skew, hlit, hdist, run, sym, 3
      )
    case False{}:
      rd.clen.t(
        z18, wh, final, left, dist, out, lit, dts, clen, lens,
        nleft, cmf, skew, hlit, hdist, run, sym
      )

# repeat codes 16, 17, and 18
def rd.clen.r(
  z16: Bool,
  z17: Bool,
  z18: Bool,
  wh: Wh,
  final: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32
) -> St:
  match z16:
    case True{}:
      rd.rep16(
        U32.is_zero(dist), wh, final, left, dist, out, lit, dts, clen, lens,
        nleft, prev, cmf, skew, hlit, hdist, run, sym, 3
      )
    case False{}:
      rd.clen.s(
        z17, z18, wh, final, left, dist, out, lit, dts, clen, lens,
        nleft, prev, cmf, skew, hlit, hdist, run, sym
      )

# one code-length symbol
def rd.clens(
  +sy: U32,
  z15: Bool,
  z16: Bool,
  z17: Bool,
  z18: Bool,
  wh: Wh,
  final: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +rep: U32
) -> St:
  match z15:
    case True{}:
      +n2 = (nleft - 1 : U32)
      rd.push(
        U32.is_zero(n2), sy, n2, {sy <> lens : List<&2, U32>}, wh, final,
        left, out, lit, dts, clen, cmf, skew, hlit, hdist, run, sy, rep
      )
    case False{}:
      rd.clen.r(
        z16, z17, z18, wh, final, left, dist, out, lit, dts, clen, lens,
        nleft, prev, cmf, skew, hlit, hdist, run, sy
      )

# the repeat is done, or it ran past the list
def rd.mrep.d(
  zz: Bool,
  +lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  wh: Wh,
  final: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  match zz:
    case True{}:
      rd.finish(
        lens, wh, final, left, dist, out, clen, prev, cmf, skew,
        hlit, hdist, run, sym, rep
      )
    case False{}:
      rd.sym(
        WClen{}, final, left, dist, out, lit, dts, clen, lens, nleft, prev,
        cmf, skew, hlit, hdist, run, sym, rep
      )

# reject a repeat that does not fit
def rd.mrep.z(
  zbad: Bool,
  +nn: U32,
  +prev: U32,
  +nleft: U32,
  lens: List<&2, U32>,
  wh: Wh,
  final: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  match zbad:
    case True{}:
      st.fail()
    case False{}:
      +n2 = (nleft - nn : U32)
      rd.mrep.d(
        U32.is_zero(n2), lens.rep(U32.to_nat(nn), prev, lens), n2, prev,
        wh, final, left, dist, out, lit, dts, clen, cmf, skew,
        hlit, hdist, run, sym, rep
      )

# extra bits of a repeat code
def rd.mrep(
  +val: U32,
  wh: Wh,
  final: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  +n = (rep + val : U32)
  rd.mrep.z(
    U32.is_gt(n, nleft), n, prev, nleft, lens, wh, final, left, dist, out,
    lit, dts, clen, cmf, skew, hlit, hdist, run, sym, rep
  )

# Adler matches the bytes
def rd.adler.eq(
  zz: Bool,
  +raw: List<&2, U32>,
  wh: Wh,
  final: Bool,
  +left: U32,
  +dist: U32,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  match zz:
    case True{}:
      st.make(
        PDone{}, MAdler{}, wh, 0, 0, 0, final, left, dist, raw, lit, dts,
        clen, lens, nleft, prev, cmf, 0, 0, skew, hlit, hdist, run, sym, rep
      )
    case False{}:
      st.fail()

# one more Adler byte, or the check
def rd.adler.z(
  zz: Bool,
  +run: U32,
  +left: U32,
  +out: List<&2, U32>,
  wh: Wh,
  final: Bool,
  +dist: U32,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +sym: U32,
  +rep: U32
) -> St:
  match zz:
    case False{}:
      st.make(
        PByte{}, MAdler{}, wh, 0, 0, 8, final, left, dist, out, lit, dts,
        clen, lens, nleft, prev, cmf, 0, 0, skew, hlit, hdist, run, sym, rep
      )
    case True{}:
      +raw = List.reverse(&2, U32, out)
      rd.adler.eq(
        U32.is_eq(adler.of(raw), run), raw, wh, final, left, dist, lit, dts,
        clen, lens, nleft, prev, cmf, skew, hlit, hdist, run, sym, rep
      )

# one big-endian Adler byte
def rd.adler(
  +val: U32,
  wh: Wh,
  final: Bool,
  +left: U32,
  +dist: U32,
  +out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  +run2 = ((255 .&. val : U32) .|. (run << 8n : U32) : U32)
  +left2 = (left - 1 : U32)
  rd.adler.z(
    U32.is_zero(left2), run2, left2, out, wh, final, dist, lit, dts, clen,
    lens, nleft, prev, cmf, skew, hlit, hdist, sym, rep
  )

# a finished integer field
def rd.field(
  md: Md,
  +val: U32,
  wh: Wh,
  final: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  match md:
    case MCmf{}:
      rd.cmf(
        val, wh, final, left, dist, out, lit, dts, clen, lens,
        nleft, prev, skew, hlit, hdist, run, sym, rep
      )
    case MFlg{}:
      rd.flg(
        val, wh, final, left, dist, out, lit, dts, clen, lens,
        nleft, prev, cmf, skew, hlit, hdist, run, sym, rep
      )
    case MBlk{}:
      rd.blk(
        val, wh, left, dist, out, lit, dts, clen, lens,
        nleft, prev, cmf, skew, hlit, hdist, run, sym, rep
      )
    case MLen{}:
      rd.len(
        val, wh, final, dist, out, lit, dts, clen, lens,
        nleft, prev, cmf, skew, hlit, hdist, run, sym, rep
      )
    case MNlen{}:
      rd.nlen(
        val, wh, final, left, dist, out, lit, dts, clen, lens,
        nleft, prev, cmf, skew, hlit, hdist, run, sym, rep
      )
    case MData{}:
      rd.data(
        val, wh, final, left, dist, out, lit, dts, clen, lens,
        nleft, prev, cmf, skew, hlit, hdist, run, sym, rep
      )
    case MHlit{}:
      rd.hlit(
        val, wh, final, left, dist, out, lit, dts, clen, lens,
        nleft, prev, cmf, skew, hdist, run, sym, rep
      )
    case MHdist{}:
      rd.hdist(
        val, wh, final, left, dist, out, lit, dts, clen, lens,
        nleft, prev, cmf, skew, hlit, run, sym, rep
      )
    case MHclen{}:
      rd.hclen(
        val, wh, final, dist, out, lit, dts, clen,
        nleft, prev, cmf, skew, hlit, hdist, run, sym, rep
      )
    case MClen{}:
      rd.clen(
        val, wh, final, left, dist, out, lit, dts, lens,
        prev, cmf, skew, hlit, hdist, run, sym, rep
      )
    case MXlen{}:
      rd.xlen(
        val, wh, final, left, dist, out, lit, dts, clen, lens,
        nleft, prev, cmf, skew, hlit, hdist, run, sym, rep
      )
    case MXdist{}:
      rd.xdist(
        val, wh, final, left, dist, out, lit, dts, clen, lens,
        nleft, prev, cmf, skew, hlit, hdist, run, sym, rep
      )
    case MAdler{}:
      rd.adler(
        val, wh, final, left, dist, out, lit, dts, clen, lens,
        nleft, prev, cmf, skew, hlit, hdist, run, sym, rep
      )
    case MRep{}:
      rd.mrep(
        val, wh, final, left, dist, out, lit, dts, clen, lens,
        nleft, prev, cmf, skew, hlit, hdist, run, sym, rep
      )

# keep a partial integer, or dispatch it
def rd.raw.at(
  zz: Bool,
  md: Md,
  wh: Wh,
  +acc: U32,
  +got: U32,
  +need: U32,
  final: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  match zz:
    case False{}:
      st.make(
        PByte{}, md, wh, acc, got, need, final, left, dist, out, lit, dts,
        clen, lens, nleft, prev, cmf, 0, 0, skew, hlit, hdist, run, sym, rep
      )
    case True{}:
      rd.field(
        md, acc, wh, final, left, dist, out, lit, dts, clen, lens,
        nleft, prev, cmf, skew, hlit, hdist, run, sym, rep
      )

# fold one bit into the integer being read
def rd.raw(
  md: Md,
  wh: Wh,
  +acc: U32,
  +got: U32,
  +need: U32,
  final: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32,
  +bit: U32
) -> St:
  +acc2 = ((bit << U32.to_nat(got) : U32) .|. acc : U32)
  +got2 = (got + 1 : U32)
  rd.raw.at(
    U32.is_eq(got2, need), md, wh, acc2, got2, need, final, left, dist, out,
    lit, dts, clen, lens, nleft, prev, cmf, skew, hlit, hdist, run, sym, rep
  )

# fifteen bits and no symbol is an error
def rd.miss(
  zz: Bool,
  +code: U32,
  +len: U32,
  wh: Wh,
  final: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  match zz:
    case True{}:
      st.fail()
    case False{}:
      st.make(
        PSym{}, MBlk{}, wh, 0, 0, 0, final, left, dist, out, lit, dts, clen,
        lens, nleft, prev, cmf, code, len, skew, hlit, hdist, run, sym, rep
      )

# dispatch a decoded symbol
def rd.symbol(
  +sy: U32,
  wh: Wh,
  final: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +rep: U32
) -> St:
  match wh:
    case WLit{}:
      rd.lit(
        U32.is_lt(sy, 256), U32.is_eq(sy, 256), U32.is_le(sy, 285), sy, wh,
        final, left, dist, out, lit, dts, clen, lens, nleft, prev, cmf, skew,
        hlit, hdist, run, rep
      )
    case WDist{}:
      rd.distsym(
        sy, U32.is_le(sy, 29), wh, final, left, out, lit, dts, clen, lens,
        nleft, prev, cmf, skew, hlit, hdist, run, rep
      )
    case WClen{}:
      rd.clens(
        sy, U32.is_le(sy, 15), U32.is_eq(sy, 16), U32.is_eq(sy, 17),
        U32.is_eq(sy, 18), wh, final, left, dist, out, lit, dts, clen, lens,
        nleft, prev, cmf, skew, hlit, hdist, run, rep
      )

# a symbol, or more bits
def rd.hbit.at(
  found: Maybe<&2, U32>,
  +code: U32,
  +len: U32,
  wh: Wh,
  final: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32
) -> St:
  match found:
    case None{}:
      rd.miss(
        U32.is_ge(len, 15), code, len, wh, final, left, dist, out, lit, dts,
        clen, lens, nleft, prev, cmf, skew, hlit, hdist, run, sym, rep
      )
    case Some{+sy}:
      rd.symbol(
        sy, wh, final, left, dist, out, lit, dts, clen, lens,
        nleft, prev, cmf, skew, hlit, hdist, run, rep
      )

# shift one Huffman bit in. The first bit is the high bit of the code.
def rd.hbit(
  +wh: Wh,
  final: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  +lit: List<&2, U32>,
  +dts: List<&2, U32>,
  +clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +hacc: U32,
  +hlen: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32,
  +bit: U32
) -> St:
  +code = ((hacc << 1n : U32) .|. bit : U32)
  +len = (hlen + 1 : U32)
  rd.hbit.at(
    huff.find(rd.tree(wh, lit, dts, clen), code, len), code, len, wh, final,
    left, dist, out, lit, dts, clen, lens, nleft, prev, cmf, skew,
    hlit, hdist, run, sym, rep
  )

# one bit of the phase the reader is in
def rd.on(
  ph: Ph,
  md: Md,
  wh: Wh,
  +acc: U32,
  +got: U32,
  +need: U32,
  final: Bool,
  +left: U32,
  +dist: U32,
  out: List<&2, U32>,
  lit: List<&2, U32>,
  dts: List<&2, U32>,
  clen: List<&2, U32>,
  lens: List<&2, U32>,
  +nleft: U32,
  +prev: U32,
  +cmf: U32,
  +hacc: U32,
  +hlen: U32,
  +skew: U32,
  +hlit: U32,
  +hdist: U32,
  +run: U32,
  +sym: U32,
  +rep: U32,
  +bit: U32
) -> St:
  match ph:
    case PFail{}:
      st.fail()
    case PDone{}:
      st.make(
        PDone{}, md, wh, acc, got, need, final, left, dist, out, lit, dts,
        clen, lens, nleft, prev, cmf, hacc, hlen, skew, hlit, hdist, run, sym, rep
      )
    case PAlign{}:
      rd.align(
        U32.is_zero(skew), md, wh, final, left, dist, out, lit, dts, clen,
        lens, nleft, prev, cmf, skew, hlit, hdist, run, sym, rep
      )
    case PByte{}:
      rd.raw(
        md, wh, acc, got, need, final, left, dist, out, lit, dts, clen, lens,
        nleft, prev, cmf, skew, hlit, hdist, run, sym, rep, bit
      )
    case PSym{}:
      rd.hbit(
        wh, final, left, dist, out, lit, dts, clen, lens, nleft, prev, cmf,
        hacc, hlen, skew, hlit, hdist, run, sym, rep, bit
      )

# advance one bit. The bit count mod 8 tracks byte alignment.
def rd.step(st: St, +bit: U32) -> St:
  match st:
    case St{
      ph, md, wh, +acc, +got, +need, final, +left, +dist, out, lit, dts,
      clen, lens, +nleft, +prev, +cmf, +hacc, +hlen, +skew, +hlit, +hdist,
      +run, +sym, +rep
    }:
      rd.on(
        ph, md, wh, acc, got, need, final, left, dist, out, lit, dts, clen,
        lens, nleft, prev, cmf, hacc, hlen, ((skew + 1 : U32) % 8 : U32),
        hlit, hdist, run, sym, rep, bit
      )

# walk the bit list until the reader finishes or the bits run out
def inflate.go(bits: List<&2, U32>, st: St) -> Maybe<&2, List<&2, U32>>:
  match bits st:
    case _bs St{
      PDone{}, _md, _wh, _a, _g, _n, _f, _l, _d, out, _i, _dt, _c, _ls,
      _nl, _pv, _cm, _ha, _hl, _sk, _h1, _h2, _rn, _sy, _rp
    }:
      Some{out}
    case _bs St{
      PFail{}, _md, _wh, _a, _g, _n, _f, _l, _d, _o, _i, _dt, _c, _ls,
      _nl, _pv, _cm, _ha, _hl, _sk, _h1, _h2, _rn, _sy, _rp
    }:
      None{}
    case Nil{} _st:
      None{}
    case Con{+b, t} st2:
      inflate.go(t, rd.step(st2, b))

# inflate a zlib wrapper around DEFLATE, as PNG compression method 0
def inflate(xs: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  inflate.go(bits.of(xs), st.empty())
