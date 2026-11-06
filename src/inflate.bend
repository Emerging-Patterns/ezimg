# src/inflate: zlib-wrapped DEFLATE for a PNG IDAT stream (compression
# method 0). Blocks are stored, fixed Huffman, or dynamic Huffman.
#
# Trusted, not proved: decode_png reads the fixed and dynamic Huffman
# DEFLATE streams other encoders (zlib, libpng) write. Only stored blocks are
# proved (laws/InflateReadsStoredBlocks.bend); a proof for dynamic Huffman
# needs a reference compressor. The Pillow check in bench/ exercises it,
# which is a test.
#
# The reader takes one bit at a time, eight per input byte. A Huffman code is
# read the canonical way (RFC 1951 3.2.2, as zlib's puff.c does): per length
# the reader keeps the code so far, the first code of that length and the
# index of that code among the symbols, so a symbol costs one step per bit and
# one walk of a 512-leaf tree. Back-references read a 32768-byte window kept
# as a tree by position, so a copy costs the same at any distance. Code
# lengths are checked as zlib's inflate checks them: no over-subscribed set,
# no incomplete set but a single code of length 1 or no code at all for the
# literal/length and distance codes, an end-of-block code, at most 286
# literal/length and 30 distance codes.
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

# a complete binary tree of U32 leaves, indexed from the root by the top bits
# of an index. TNone is a subtree of zeros, so an empty one is one cell.
type Tr is Data:
  TNone{}
  TLeaf{+val: U32}
  TNode{lo: Tr, hi: Tr}

# one Huffman table: how many codes have each length from 1 to 15, and the
# symbols in canonical order (by length, then by symbol) in a 512-leaf tree
type Hc is Data:
  Hc{cnt: List<&2, U32>, syms: Tr}

# the Huffman tables and the dynamic header being read: the code lengths so
# far (newest first), how many are still to come, the length a repeat code
# repeats and its base count, HLIT and HDIST
type Hs is Data:
  Hs{lit: Hc, dts: Hc, clen: Hc, lens: List<&2, U32>, +nleft: U32, +prev: U32, +rep: U32, +hlit: U32, +hdist: U32}

# what the fields and symbols read so far leave: BFINAL of this block; the
# stored bytes, Adler bytes or 3-bit code lengths left, or a match length;
# a distance base; the bytes emitted, newest first; the window of the last
# 32768 of them by position, and how many bytes it holds (mod 2^32); the
# stored bytes not yet copied into the window; CMF, then the Adler-32 read so
# far; the Huffman state
type Cx is Data:
  Cx{final: Bool, +left: U32, +dist: U32, out: List<&2, U32>, win: Tr, +wpos: U32, +pend: U32, +run: U32, hs: Hs}

# one inflate reader. Reading an integer (PByte): its bits so far, how many,
# and its width. Reading a Huffman code (PSym): the code so far, the first
# code of its length, the index of that first code among the symbols, and
# the counts of the lengths still to try. `skew` is the bit count mod 8.
type St is Data:
  St{ph: Ph, md: Md, wh: Wh, +acc: U32, +got: U32, +need: U32, cur: List<&2, U32>, +skew: U32, cx: Cx}

# an empty Huffman table
def hc.none() -> Hc:
  Hc{[], TNone{}}

# no Huffman tables yet
def hs.none() -> Hs:
  Hs{hc.none(), hc.none(), hc.none(), [], 0, 0, 0, 0, 0}

# nothing read yet
def cx.none() -> Cx:
  Cx{False{}, 0, 0, [], TNone{}, 0, 0, 0, hs.none()}

# a reader that has failed
def st.fail() -> St:
  St{PFail{}, MCmf{}, WLit{}, 0, 0, 0, [], 0, cx.none()}

# the reader before the first byte
def st.empty() -> St:
  St{PByte{}, MCmf{}, WLit{}, 0, 0, 8, [], 0, cx.none()}

# a fresh integer field of `need` bits
def st.byte(md: Md, +need: U32, +skew: U32, cx: Cx) -> St:
  St{PByte{}, md, WLit{}, 0, 0, need, [], skew, cx}

# trees
# -----

# whether the walk from here goes to the low half: the top bit of the index
def tr.lo(+ix: U32) -> Bool:
  U32.is_lt(ix, 2147483648)

# the leaf at the index whose top `dd` bits are the path; `zz` is tr.lo(ix)
def tr.get(dd: Nat, tt: Tr, zz: Bool, +ix: U32) -> U32:
  match dd tt zz:
    case _d TNone{} _z:
      0
    case _d TLeaf{+v} _z:
      v
    case 0n TNode{_l, _h} _z:
      0
    case 1n+p TNode{lo, _h} True{}:
      +i2 = (ix << 1n : U32)
      tr.get(p, lo, tr.lo(i2), i2)
    case 1n+p TNode{_l, hi} False{}:
      +i2 = (ix << 1n : U32)
      tr.get(p, hi, tr.lo(i2), i2)

# write the leaf at the index whose top `dd` bits are the path
def tr.set(dd: Nat, tt: Tr, zz: Bool, +ix: U32, +vv: U32) -> Tr:
  match dd tt zz:
    case 0n _t _z:
      TLeaf{vv}
    case 1n+p TNone{} True{}:
      +i2 = (ix << 1n : U32)
      TNode{tr.set(p, TNone{}, tr.lo(i2), i2, vv), TNone{}}
    case 1n+p TNone{} False{}:
      +i2 = (ix << 1n : U32)
      TNode{TNone{}, tr.set(p, TNone{}, tr.lo(i2), i2, vv)}
    case 1n+p TLeaf{_v} True{}:
      +i2 = (ix << 1n : U32)
      TNode{tr.set(p, TNone{}, tr.lo(i2), i2, vv), TNone{}}
    case 1n+p TLeaf{_v} False{}:
      +i2 = (ix << 1n : U32)
      TNode{TNone{}, tr.set(p, TNone{}, tr.lo(i2), i2, vv)}
    case 1n+p TNode{lo, hi} True{}:
      +i2 = (ix << 1n : U32)
      TNode{tr.set(p, lo, tr.lo(i2), i2, vv), hi}
    case 1n+p TNode{lo, hi} False{}:
      +i2 = (ix << 1n : U32)
      TNode{lo, tr.set(p, hi, tr.lo(i2), i2, vv)}

# one leaf per value
def tr.leaves(xs: List<&2, U32>) -> List<&2, Tr>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      TLeaf{h} <> tr.leaves(t)

# pair neighbouring trees into the next level up
def tr.pairs(xs: List<&2, Tr>) -> List<&2, Tr>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{aa, Nil{}}:
      [TNode{aa, TNone{}}]
    case Con{aa, Con{bb, t}}:
      TNode{aa, bb} <> tr.pairs(t)

# the one tree left at the top
def tr.top(xs: List<&2, Tr>) -> Tr:
  match xs:
    case Nil{}:
      TNone{}
    case Con{aa, _t}:
      aa

# a tree of depth `dd` whose leaves, in order, are these trees
def tr.up(dd: Nat, xs: List<&2, Tr>) -> Tr:
  match dd:
    case 0n:
      tr.top(xs)
    case 1n+p:
      tr.up(p, tr.pairs(xs))

# the byte at a position of the window: the low 15 bits pick the leaf
def win.get(win: Tr, +pos: U32) -> U32:
  +ix = (pos << 17n : U32)
  tr.get(15n, win, tr.lo(ix), ix)

# write the byte at a position of the window
def win.put(win: Tr, +pos: U32, +bb: U32) -> Tr:
  +ix = (pos << 17n : U32)
  tr.set(15n, win, tr.lo(ix), ix, bb)

# copy the newest `nn` bytes of a newest-first list into the window, the
# head at `pos` and each older one just before it
def win.sync(nn: Nat, xs: List<&2, U32>, win: Tr, +pos: U32) -> Tr:
  match nn xs:
    case 0n _x:
      win
    case _n Nil{}:
      win
    case 1n+p Con{+h, t}:
      win.sync(p, t, win.put(win, pos, h), (pos - 1 : U32))

# Huffman tables
# --------------

# zeros: a code-length list of zeros
def huff.zeros(nn: Nat) -> List<&2, U32>:
  match nn:
    case 0n:
      Nil{}
    case 1n+p:
      0 <> huff.zeros(p)

# the value at an index, or zero past the end. `zz` is whether `ii` is zero:
# the walk stops at that value
def tab.at(xs: List<&2, U32>, zz: Bool, +ii: U32) -> U32:
  match xs zz:
    case Nil{} _z:
      0
    case Con{+h, _t} True{}:
      h
    case Con{_h, t} False{}:
      tab.at(t, U32.is_zero((ii - 1 : U32)), (ii - 1 : U32))

# write an index. `zz` is "this is the slot".
def lens.set(xs: List<&2, U32>, zz: Bool, +ii: U32, +vv: U32) -> List<&2, U32>:
  match xs zz:
    case Nil{} _z:
      Nil{}
    case Con{_h, t} True{}:
      vv <> t
    case Con{+h, t} False{}:
      h <> lens.set(t, U32.is_zero((ii - 1 : U32)), (ii - 1 : U32), vv)

# code-length lists
# -----------------

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

# thirty-two distance lengths of 5
def dist.lens(nn: Nat) -> List<&2, U32>:
  match nn:
    case 0n:
      Nil{}
    case 1n+p:
      5 <> dist.lens(p)

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
      clen.place(ot, lt, lens.set(acc, U32.is_zero(i), i, L))

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

# one more when `zz`
def hc.inc(zz: Bool, +nn: U32) -> U32:
  match zz:
    case True{}:
      (nn + 1 : U32)
    case False{}:
      nn

# keep a code that has a length
def hc.nz.keep(zz: Bool, +ee: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match zz:
    case True{}:
      acc
    case False{}:
      ee <> acc

# the symbols whose length is not zero, each packed as `len << 16 | sym`,
# newest first: a sparse table is built from a short list
def hc.nz(ls: List<&2, U32>, +sym: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match ls:
    case Nil{}:
      acc
    case Con{+L, t}:
      hc.nz(t, (sym + 1 : U32), hc.nz.keep(U32.is_zero(L), ((L << 16n : U32) .|. sym : U32), acc))

# how many of the packed codes have length `ll`
def hc.num(ls: List<&2, U32>, +ll: U32, +nn: U32) -> U32:
  match ls:
    case Nil{}:
      nn
    case Con{+ee, t}:
      hc.num(t, ll, hc.inc(U32.is_eq((ee >> 16n : U32), ll), nn))

# bl_count for the lengths `ll` to `ll + kk - 1`, from the packed codes
def hc.cnts(kk: Nat, +ll: U32, +ls: List<&2, U32>) -> List<&2, U32>:
  match kk:
    case 0n:
      Nil{}
    case 1n+p:
      hc.num(ls, ll, 0) <> hc.cnts(p, (ll + 1 : U32), ls)

# keep the symbol when its length matches
def hc.keep(zz: Bool, +sym: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match zz:
    case True{}:
      sym <> acc
    case False{}:
      acc

# the symbols of the packed codes of length `ll`, in order, onto a newest-first list
def hc.pick(ls: List<&2, U32>, +ll: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match ls:
    case Nil{}:
      acc
    case Con{+ee, t}:
      hc.pick(t, ll, hc.keep(U32.is_eq((ee >> 16n : U32), ll), (ee .&. 65535 : U32), acc))

# the symbols of the packed codes (in symbol order), by length and then by symbol
def hc.sorted(kk: Nat, +ll: U32, +ls: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match kk:
    case 0n:
      List.reverse(&2, U32, acc)
    case 1n+p:
      hc.sorted(p, (ll + 1 : U32), ls, hc.pick(ls, ll, acc))

# the codes left unused once lengths 1 to 15 are counted (puff's `left`), or
# none when the lengths ask for more codes than there are. `zz` is "too many".
def hc.room(cs: List<&2, U32>, zz: Bool, +left: U32) -> Maybe<&2, U32>:
  match cs zz:
    case _c True{}:
      None{}
    case Nil{} False{}:
      Some{left}
    case Con{+c, t} False{}:
      +l2 = (left << 1n : U32)
      hc.room(t, U32.is_gt(c, l2), (l2 - c : U32))

# the sum of the counts
def hc.sum(cs: List<&2, U32>, +nn: U32) -> U32:
  match cs:
    case Nil{}:
      nn
    case Con{+c, t}:
      hc.sum(t, (nn + c : U32))

# the count of length 1
def hc.first(cs: List<&2, U32>) -> U32:
  match cs:
    case Nil{}:
      0
    case Con{+c, _t}:
      c

# zlib's inflate_table: refuse an over-subscribed set; refuse an incomplete
# one unless it has no code, or `single` allows one code of length 1
def hc.valid(rr: Maybe<&2, U32>, +total: U32, +one: U32, single: Bool) -> Bool:
  match rr:
    case None{}:
      False{}
    case Some{+left}:
      +lone = Bool.and(single, Bool.and(U32.is_eq(total, 1), U32.is_eq(one, 1)))
      Bool.or(U32.is_zero(left), Bool.or(U32.is_zero(total), lone))

# the table once its counts are checked
def hc.build.ok(zz: Bool, cs: List<&2, U32>, +ls: List<&2, U32>) -> Maybe<&2, Hc>:
  match zz:
    case True{}:
      Some{Hc{cs, tr.up(9n, tr.leaves(hc.sorted(15n, 1, ls, [])))}}
    case False{}:
      None{}

# the canonical Huffman table of a length per symbol, if the lengths are a
# set zlib accepts
def hc.build(ls: List<&2, U32>, single: Bool) -> Maybe<&2, Hc>:
  +nz = List.reverse(&2, U32, hc.nz(ls, 0, []))
  +cs = hc.cnts(15n, 1, nz)
  hc.build.ok(hc.valid(hc.room(cs, False{}, 1), hc.sum(cs, 0), hc.first(cs), single), cs, nz)

# `nn` symbols from `from` on, onto a list
def seq(nn: Nat, +from: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match nn:
    case 0n:
      acc
    case 1n+p:
      from <> seq(p, (from + 1 : U32), acc)

# the fixed literal/length table (RFC 1951 3.2.6): 256-279 have length 7,
# 0-143 and 280-287 length 8, 144-255 length 9
def lit.fixed() -> Hc:
  +syms = seq(24n, 256, seq(144n, 0, seq(8n, 280, seq(112n, 144, []))))
  Hc{[0, 0, 0, 0, 0, 0, 24, 152, 112, 0, 0, 0, 0, 0, 0], tr.up(9n, tr.leaves(syms))}

# the fixed distance table: thirty-two codes of length 5
def dist.fixed() -> Hc:
  Hc{[0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], tr.up(9n, tr.leaves(seq(32n, 0, [])))}

# the symbol at an index of a table's canonical order
def hc.sym(hc: Hc, +ix: U32) -> U32:
  match hc:
    case Hc{_c, syms}:
      +at = (ix << 23n : U32)
      tr.get(9n, syms, tr.lo(at), at)

# the counts of a table
def hc.cnt(hc: Hc) -> List<&2, U32>:
  match hc:
    case Hc{cnt, _s}:
      cnt

# the counts of the table `wh` names
def hs.cnt(wh: Wh, hs: Hs) -> List<&2, U32>:
  match wh hs:
    case WLit{} Hs{lit, _d, _c, _l, _n, _p, _r, _h1, _h2}:
      hc.cnt(lit)
    case WDist{} Hs{_i, dts, _c, _l, _n, _p, _r, _h1, _h2}:
      hc.cnt(dts)
    case WClen{} Hs{_i, _d, clen, _l, _n, _p, _r, _h1, _h2}:
      hc.cnt(clen)

# a symbol of the table `wh` names
def hs.sym(wh: Wh, hs: Hs, +ix: U32) -> U32:
  match wh hs:
    case WLit{} Hs{lit, _d, _c, _l, _n, _p, _r, _h1, _h2}:
      hc.sym(lit, ix)
    case WDist{} Hs{_i, dts, _c, _l, _n, _p, _r, _h1, _h2}:
      hc.sym(dts, ix)
    case WClen{} Hs{_i, _d, clen, _l, _n, _p, _r, _h1, _h2}:
      hc.sym(clen, ix)

# fixed literal/length and distance tables
def hs.fixed(hs: Hs) -> Hs:
  match hs:
    case Hs{_i, _d, clen, lens, +nleft, +prev, +rep, +hlit, +hdist}:
      Hs{lit.fixed(), dist.fixed(), clen, lens, nleft, prev, rep, hlit, hdist}

# HLIT
def hs.hlit(hs: Hs, +val: U32) -> Hs:
  match hs:
    case Hs{lit, dts, clen, lens, +nleft, +prev, +rep, _h1, +hdist}:
      Hs{lit, dts, clen, lens, nleft, prev, rep, val, hdist}

# HDIST
def hs.hdist(hs: Hs, +val: U32) -> Hs:
  match hs:
    case Hs{lit, dts, clen, lens, +nleft, +prev, +rep, +hlit, _h2}:
      Hs{lit, dts, clen, lens, nleft, prev, rep, hlit, val}

# no code lengths yet
def hs.clear(hs: Hs) -> Hs:
  match hs:
    case Hs{lit, dts, clen, _l, +nleft, +prev, +rep, +hlit, +hdist}:
      Hs{lit, dts, clen, [], nleft, prev, rep, hlit, hdist}

# one more code length, newest first
def hs.push(hs: Hs, +val: U32) -> Hs:
  match hs:
    case Hs{lit, dts, clen, lens, +nleft, +prev, +rep, +hlit, +hdist}:
      Hs{lit, dts, clen, {val <> lens : List<&2, U32>}, nleft, prev, rep, hlit, hdist}

# one more literal/length or distance code length, one fewer to come
def hs.store(hs: Hs, +val: U32) -> Hs:
  match hs:
    case Hs{lit, dts, clen, lens, +nleft, +prev, +rep, +hlit, +hdist}:
      Hs{lit, dts, clen, {val <> lens : List<&2, U32>}, (nleft - 1 : U32), prev, rep, hlit, hdist}

# the code-length table is built: HLIT + HDIST + 258 code lengths to come
def hs.clen(hs: Hs, ct: Hc) -> Hs:
  match hs:
    case Hs{lit, dts, _c, _l, _n, +prev, +rep, +hlit, +hdist}:
      Hs{lit, dts, ct, [], ((hlit + 257 : U32) + (hdist + 1 : U32) : U32), prev, rep, hlit, hdist}

# a repeat code: the length it repeats and its base count
def hs.rep(hs: Hs, +prev: U32, +rep: U32) -> Hs:
  match hs:
    case Hs{lit, dts, clen, lens, +nleft, _p, _r, +hlit, +hdist}:
      Hs{lit, dts, clen, lens, nleft, prev, rep, hlit, hdist}

# a repeat of `nn` lengths
def hs.fill(hs: Hs, +nn: U32) -> Hs:
  match hs:
    case Hs{lit, dts, clen, lens, +nleft, +prev, +rep, +hlit, +hdist}:
      Hs{lit, dts, clen, lens.rep(U32.to_nat(nn), prev, lens), (nleft - nn : U32), prev, rep, hlit, hdist}

# both tables of a dynamic block
def hs.tables(hs: Hs, lt: Hc, dt: Hc) -> Hs:
  match hs:
    case Hs{_i, _d, clen, _l, +nleft, +prev, +rep, +hlit, +hdist}:
      Hs{lt, dt, clen, [], nleft, prev, rep, hlit, hdist}

# the code lengths so far
def hs.lens(hs: Hs) -> List<&2, U32>:
  match hs:
    case Hs{_i, _d, _c, lens, _n, _p, _r, _h1, _h2}:
      lens

# the code lengths still to come
def hs.nleft(hs: Hs) -> U32:
  match hs:
    case Hs{_i, _d, _c, _l, +nleft, _p, _r, _h1, _h2}:
      nleft

# the base count of the repeat code being read
def hs.rep.of(hs: Hs) -> U32:
  match hs:
    case Hs{_i, _d, _c, _l, _n, _p, +rep, _h1, _h2}:
      rep

# HLIT
def hs.hlit.of(hs: Hs) -> U32:
  match hs:
    case Hs{_i, _d, _c, _l, _n, _p, _r, +hlit, _h2}:
      hlit

# Adler-32
# --------

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

# the reader's context
# --------------------

# BFINAL
def cx.final(cx: Cx) -> Bool:
  match cx:
    case Cx{final, _l, _d, _o, _w, _wp, _p, _r, _h}:
      final

# `left`
def cx.left(cx: Cx) -> U32:
  match cx:
    case Cx{_f, +left, _d, _o, _w, _wp, _p, _r, _h}:
      left

# the distance base
def cx.dist(cx: Cx) -> U32:
  match cx:
    case Cx{_f, _l, +dist, _o, _w, _wp, _p, _r, _h}:
      dist

# the bytes the window holds
def cx.wpos(cx: Cx) -> U32:
  match cx:
    case Cx{_f, _l, _d, _o, _w, +wpos, _p, _r, _h}:
      wpos

# the Huffman state
def cx.hs(cx: Cx) -> Hs:
  match cx:
    case Cx{_f, _l, _d, _o, _w, _wp, _p, _r, hs}:
      hs

# another Huffman state
def cx.with(cx: Cx, hs: Hs) -> Cx:
  match cx:
    case Cx{final, +left, +dist, out, win, +wpos, +pend, +run, _h}:
      Cx{final, left, dist, out, win, wpos, pend, run, hs}

# another `left`
def cx.set.left(cx: Cx, +val: U32) -> Cx:
  match cx:
    case Cx{final, _l, +dist, out, win, +wpos, +pend, +run, hs}:
      Cx{final, val, dist, out, win, wpos, pend, run, hs}

# another distance base
def cx.set.dist(cx: Cx, +val: U32) -> Cx:
  match cx:
    case Cx{final, +left, _d, out, win, +wpos, +pend, +run, hs}:
      Cx{final, left, val, out, win, wpos, pend, run, hs}

# the counts of the table `wh` names
def cx.cnt(wh: Wh, cx: Cx) -> List<&2, U32>:
  match cx:
    case Cx{_f, _l, _d, _o, _w, _wp, _p, _r, hs}:
      hs.cnt(wh, hs)

# a symbol of the table `wh` names
def cx.sym(wh: Wh, cx: Cx, +ix: U32) -> U32:
  match cx:
    case Cx{_f, _l, _d, _o, _w, _wp, _p, _r, hs}:
      hs.sym(wh, hs, ix)

# emit one byte: onto the output and into the window
def cx.emit(cx: Cx, +bb: U32) -> Cx:
  match cx:
    case Cx{final, +left, +dist, out, win, +wpos, +pend, +run, hs}:
      Cx{final, left, dist, {bb <> out : List<&2, U32>}, win.put(win, wpos, bb), (wpos + 1 : U32), pend, run, hs}

# copy one byte from `dd` back
def cx.copy1(cx: Cx, +dd: U32) -> Cx:
  match cx:
    case Cx{final, +left, +dist, out, +win, +wpos, +pend, +run, hs}:
      +bb = win.get(win, (wpos - dd : U32))
      Cx{final, left, dist, {bb <> out : List<&2, U32>}, win.put(win, wpos, bb), (wpos + 1 : U32), pend, run, hs}

# copy `nn` bytes from `dd` back
def copy.run(nn: Nat, +dd: U32, cx: Cx) -> Cx:
  match nn:
    case 0n:
      cx
    case 1n+p:
      copy.run(p, dd, cx.copy1(cx, dd))

# the most stored bytes the window can take
def win.cap(zz: Bool, +pend: U32) -> U32:
  match zz:
    case True{}:
      pend
    case False{}:
      32768

# a Huffman block starts: the stored bytes since the last one go into the window
def cx.sync(cx: Cx) -> Cx:
  match cx:
    case Cx{final, +left, +dist, +out, win, +wpos, +pend, +run, hs}:
      +nn = U32.to_nat(win.cap(U32.is_lt(pend, 32768), pend))
      +w2 = win.sync(nn, out, win, ((wpos + pend : U32) - 1 : U32))
      Cx{final, left, dist, out, w2, (wpos + pend : U32), 0, run, hs}

# the fixed tables
def cx.fixed(cx: Cx) -> Cx:
  match cx:
    case Cx{final, +left, +dist, out, win, +wpos, +pend, +run, hs}:
      Cx{final, left, dist, out, win, wpos, pend, run, hs.fixed(hs)}

# the reader, one bit at a time
# ------------------------------

# a Huffman code starts in the table `wh`
def st.sym(+wh: Wh, +skew: U32, +cx: Cx) -> St:
  St{PSym{}, MBlk{}, wh, 0, 0, 0, cx.cnt(wh, cx), skew, cx}

# start the field `md` asks for, now that the stream is aligned
def rd.begin(md: Md, +skew: U32, cx: Cx) -> St:
  match md cx:
    case MLen{} c2:
      st.byte(MLen{}, 16, skew, c2)
    case MAdler{} Cx{final, _l, +dist, out, win, +wpos, +pend, _r, hs}:
      st.byte(MAdler{}, 8, skew, Cx{final, 4, dist, out, win, wpos, pend, 0, hs})
    case _md _cx:
      st.fail()

# a byte-aligned field starts, or a padding bit is still waiting
def rd.align(zz: Bool, md: Md, +skew: U32, cx: Cx) -> St:
  match zz:
    case False{}:
      St{PAlign{}, md, WLit{}, 0, 0, 0, [], skew, cx}
    case True{}:
      rd.begin(md, skew, cx)

# skip bits up to the next byte, then read `md`
def rd.to_align(md: Md, +skew: U32, cx: Cx) -> St:
  rd.align(U32.is_zero(skew), md, skew, cx)

# the next block, or the Adler checksum when this was the last block
def rd.after.at(zz: Bool, +skew: U32, cx: Cx) -> St:
  match zz:
    case True{}:
      rd.to_align(MAdler{}, skew, cx)
    case False{}:
      st.byte(MBlk{}, 3, skew, cx)

# a block has ended
def rd.after(+skew: U32, +cx: Cx) -> St:
  rd.after.at(cx.final(cx), skew, cx)

# CMF checked: keep it in `run` for FLG
def rd.cmf.ok(zz: Bool, +val: U32, +skew: U32, cx: Cx) -> St:
  match zz cx:
    case True{} Cx{final, +left, +dist, out, win, +wpos, +pend, _r, hs}:
      st.byte(MFlg{}, 8, skew, Cx{final, left, dist, out, win, wpos, pend, val, hs})
    case False{} _cx:
      st.fail()

# CMF: method 8, window at most 32K
def rd.cmf(+val: U32, +skew: U32, cx: Cx) -> St:
  rd.cmf.ok(Bool.and(U32.is_eq((val .&. 15 : U32), 8), U32.is_le((val >> 4n : U32), 7)), val, skew, cx)

# FLG checked
def rd.flg.ok(zz: Bool, +skew: U32, cx: Cx) -> St:
  match zz:
    case True{}:
      st.byte(MBlk{}, 3, skew, cx)
    case False{}:
      st.fail()

# FLG: the header check, and no preset dictionary
def rd.flg(+val: U32, +skew: U32, cx: Cx) -> St:
  match cx:
    case Cx{final, +left, +dist, out, win, +wpos, +pend, +run, hs}:
      +sum = (((run << 8n : U32) + val : U32) % 31 : U32)
      rd.flg.ok(Bool.and(U32.is_zero(sum), U32.is_zero((val .&. 32 : U32))), skew, Cx{final, left, dist, out, win,
        wpos, pend, run, hs})

# a dynamic header, or the reserved block type
def rd.blk.dyn(z2: Bool, +skew: U32, cx: Cx) -> St:
  match z2:
    case True{}:
      st.byte(MHlit{}, 5, skew, cx)
    case False{}:
      st.fail()

# fixed or dynamic Huffman
def rd.blk.huff(z1: Bool, z2: Bool, +skew: U32, cx: Cx) -> St:
  match z1:
    case True{}:
      st.sym(WLit{}, skew, cx.fixed(cx))
    case False{}:
      rd.blk.dyn(z2, skew, cx)

# a stored block, or a Huffman block with the window brought up to date
def rd.blk.ty(z0: Bool, z1: Bool, z2: Bool, +skew: U32, cx: Cx) -> St:
  match z0:
    case True{}:
      rd.to_align(MLen{}, skew, cx)
    case False{}:
      rd.blk.huff(z1, z2, skew, cx.sync(cx))

# BFINAL is kept; BTYPE picks the block
def rd.blk.go(fin: Bool, z0: Bool, z1: Bool, z2: Bool, +skew: U32, cx: Cx) -> St:
  match cx:
    case Cx{_f, +left, +dist, out, win, +wpos, +pend, +run, hs}:
      rd.blk.ty(z0, z1, z2, skew, Cx{fin, left, dist, out, win, wpos, pend, run, hs})

# BFINAL is the low bit. BTYPE is the next two.
def rd.blk(+val: U32, +skew: U32, cx: Cx) -> St:
  +bt = (val >> 1n : U32)
  rd.blk.go(U32.is_eq((val .&. 1 : U32), 1), U32.is_eq(bt, 0), U32.is_eq(bt, 1), U32.is_eq(bt, 2), skew, cx)

# stored LEN, then NLEN. The LEN bytes are owed to the window.
def rd.len(+val: U32, +skew: U32, cx: Cx) -> St:
  match cx:
    case Cx{final, _l, +dist, out, win, +wpos, +pend, +run, hs}:
      st.byte(MNlen{}, 16, skew, Cx{final, val, dist, out, win, wpos, (pend + val : U32), run, hs})

# an empty stored block ends the block; otherwise the bytes follow
def rd.nlen.ok(zz: Bool, +skew: U32, cx: Cx) -> St:
  match zz:
    case True{}:
      rd.after(skew, cx)
    case False{}:
      st.byte(MData{}, 8, skew, cx)

# NLEN checked
def rd.nlen.chk(zz: Bool, +skew: U32, +cx: Cx) -> St:
  match zz:
    case True{}:
      rd.nlen.ok(U32.is_zero(cx.left(cx)), skew, cx)
    case False{}:
      st.fail()

# NLEN is the one's complement of LEN
def rd.nlen(+val: U32, +skew: U32, +cx: Cx) -> St:
  rd.nlen.chk(U32.is_eq(val, (cx.left(cx) .^. 65535 : U32)), skew, cx)

# the stored block's end, or its next byte
def rd.data.z(zz: Bool, +skew: U32, cx: Cx) -> St:
  match zz:
    case True{}:
      rd.after(skew, cx)
    case False{}:
      st.byte(MData{}, 8, skew, cx)

# consume one stored byte
def rd.data(+val: U32, +skew: U32, cx: Cx) -> St:
  match cx:
    case Cx{final, +left, +dist, out, win, +wpos, +pend, +run, hs}:
      +l2 = (left - 1 : U32)
      rd.data.z(U32.is_zero(l2), skew, Cx{final, l2, dist, {val <> out : List<&2, U32>}, win, wpos, pend, run, hs})

# HLIT checked: at most 286 literal/length codes
def rd.hlit.ok(zz: Bool, +val: U32, +skew: U32, +cx: Cx) -> St:
  match zz:
    case True{}:
      st.byte(MHdist{}, 5, skew, cx.with(cx, hs.hlit(cx.hs(cx), val)))
    case False{}:
      st.fail()

# HLIT, then HDIST
def rd.hlit(+val: U32, +skew: U32, cx: Cx) -> St:
  rd.hlit.ok(U32.is_le(val, 29), val, skew, cx)

# HDIST checked: at most 30 distance codes
def rd.hdist.ok(zz: Bool, +val: U32, +skew: U32, +cx: Cx) -> St:
  match zz:
    case True{}:
      st.byte(MHclen{}, 4, skew, cx.with(cx, hs.hdist(cx.hs(cx), val)))
    case False{}:
      st.fail()

# HDIST, then HCLEN
def rd.hdist(+val: U32, +skew: U32, cx: Cx) -> St:
  rd.hdist.ok(U32.is_le(val, 29), val, skew, cx)

# HCLEN, then that many 3-bit code lengths
def rd.hclen(+val: U32, +skew: U32, cx: Cx) -> St:
  match cx:
    case Cx{final, _l, +dist, out, win, +wpos, +pend, +run, hs}:
      st.byte(MClen{}, 3, skew, Cx{final, (val + 4 : U32), dist, out, win, wpos, pend, run, hs.clear(hs)})

# the code-length table, if its lengths are complete
def rd.clen.got(mm: Maybe<&2, Hc>, +skew: U32, +cx: Cx) -> St:
  match mm:
    case None{}:
      st.fail()
    case Some{ct}:
      st.sym(WClen{}, skew, cx.with(cx, hs.clen(cx.hs(cx), ct)))

# code lengths are in. Build the code-length table and read the rest.
def rd.clen.z(zz: Bool, +skew: U32, +cx: Cx) -> St:
  match zz:
    case False{}:
      st.byte(MClen{}, 3, skew, cx)
    case True{}:
      +placed = clen.place(clen.order(), List.reverse(&2, U32, hs.lens(cx.hs(cx))), huff.zeros(19n))
      rd.clen.got(hc.build(placed, False{}), skew, cx)

# one 3-bit code length
def rd.clen(+val: U32, +skew: U32, cx: Cx) -> St:
  match cx:
    case Cx{final, +left, +dist, out, win, +wpos, +pend, +run, hs}:
      +l2 = (left - 1 : U32)
      rd.clen.z(U32.is_zero(l2), skew, Cx{final, l2, dist, out, win, wpos, pend, run, hs.push(hs, val)})

# the distance table, if its lengths are a set zlib accepts
def rd.finish.dist(mm: Maybe<&2, Hc>, lt: Hc, +skew: U32, +cx: Cx) -> St:
  match mm:
    case None{}:
      st.fail()
    case Some{dt}:
      st.sym(WLit{}, skew, cx.with(cx, hs.tables(cx.hs(cx), lt, dt)))

# the literal/length table, if its lengths are a set zlib accepts
def rd.finish.lit(mm: Maybe<&2, Hc>, +dists: List<&2, U32>, +skew: U32, +cx: Cx) -> St:
  match mm:
    case None{}:
      st.fail()
    case Some{lt}:
      rd.finish.dist(hc.build(dists, True{}), lt, skew, cx)

# the end-of-block code must have a length
def rd.finish.eob(zz: Bool, +lits: List<&2, U32>, +dists: List<&2, U32>, +skew: U32, +cx: Cx) -> St:
  match zz:
    case True{}:
      st.fail()
    case False{}:
      rd.finish.lit(hc.build(lits, True{}), dists, skew, cx)

# both length lists are in
def rd.finish.at(mm: Maybe<&2, lens.Split>, +skew: U32, +cx: Cx) -> St:
  match mm:
    case None{}:
      st.fail()
    case Some{lens.Split{+lits, +dists}}:
      rd.finish.eob(U32.is_zero(tab.at(lits, False{}, 256)), lits, dists, skew, cx)

# split the length list into literal and distance tables
def rd.finish(+skew: U32, +cx: Cx) -> St:
  +hs = cx.hs(cx)
  +chron = List.reverse(&2, U32, hs.lens(hs))
  +nlit = (hs.hlit.of(hs) + 257 : U32)
  rd.finish.at(lens.split(chron, U32.is_zero(nlit), nlit, []), skew, cx)

# all the code lengths are in, or more follow
def rd.clen.more(zz: Bool, +skew: U32, cx: Cx) -> St:
  match zz:
    case True{}:
      rd.finish(skew, cx)
    case False{}:
      st.sym(WClen{}, skew, cx)

# a code length of 0 to 15
def rd.push(+sy: U32, +skew: U32, +cx: Cx) -> St:
  +hs = hs.store(cx.hs(cx), sy)
  rd.clen.more(U32.is_zero(hs.nleft(hs)), skew, cx.with(cx, hs))

# code 16 repeats the last length stored, so one must be
def rd.rep16(ls: List<&2, U32>, +skew: U32, +cx: Cx) -> St:
  match ls:
    case Nil{}:
      st.fail()
    case Con{+h, _t}:
      st.byte(MRep{}, 2, skew, cx.with(cx, hs.rep(cx.hs(cx), h, 3)))

# code 18, or an illegal code-length symbol
def rd.clen.t(z18: Bool, +skew: U32, +cx: Cx) -> St:
  match z18:
    case True{}:
      st.byte(MRep{}, 7, skew, cx.with(cx, hs.rep(cx.hs(cx), 0, 11)))
    case False{}:
      st.fail()

# codes 17 and 18 repeat zero
def rd.clen.s(z17: Bool, z18: Bool, +skew: U32, +cx: Cx) -> St:
  match z17:
    case True{}:
      st.byte(MRep{}, 3, skew, cx.with(cx, hs.rep(cx.hs(cx), 0, 3)))
    case False{}:
      rd.clen.t(z18, skew, cx)

# repeat codes 16, 17, and 18
def rd.clen.r(z16: Bool, z17: Bool, z18: Bool, +skew: U32, +cx: Cx) -> St:
  match z16:
    case True{}:
      rd.rep16(hs.lens(cx.hs(cx)), skew, cx)
    case False{}:
      rd.clen.s(z17, z18, skew, cx)

# one code-length symbol
def rd.clens(z15: Bool, z16: Bool, z17: Bool, z18: Bool, +sy: U32, +skew: U32, cx: Cx) -> St:
  match z15:
    case True{}:
      rd.push(sy, skew, cx)
    case False{}:
      rd.clen.r(z16, z17, z18, skew, cx)

# reject a repeat that runs past the list
def rd.mrep.z(zbad: Bool, +nn: U32, +skew: U32, +cx: Cx) -> St:
  match zbad:
    case True{}:
      st.fail()
    case False{}:
      +hs = hs.fill(cx.hs(cx), nn)
      rd.clen.more(U32.is_zero(hs.nleft(hs)), skew, cx.with(cx, hs))

# extra bits of a repeat code
def rd.mrep(+val: U32, +skew: U32, +cx: Cx) -> St:
  +hs = cx.hs(cx)
  +nn = (hs.rep.of(hs) + val : U32)
  rd.mrep.z(U32.is_gt(nn, hs.nleft(hs)), nn, skew, cx)

# copy `left` bytes from `dd` back, if the output reaches that far
def rd.copy.at(zz: Bool, +dd: U32, +skew: U32, +cx: Cx) -> St:
  match zz:
    case True{}:
      st.fail()
    case False{}:
      st.sym(WLit{}, skew, copy.run(U32.to_nat(cx.left(cx)), dd, cx))

# a back-reference of `left` bytes at distance `dd`
def rd.copy(+dd: U32, +skew: U32, +cx: Cx) -> St:
  rd.copy.at(U32.is_gt(dd, cx.wpos(cx)), dd, skew, cx)

# extra distance bits are added to the base in `dist`
def rd.xdist(+val: U32, +skew: U32, +cx: Cx) -> St:
  rd.copy((cx.dist(cx) + val : U32), skew, cx)

# no extra distance bits: the base is the distance
def rd.xdist0(zz: Bool, +extra: U32, +base: U32, +skew: U32, cx: Cx) -> St:
  match zz:
    case True{}:
      rd.copy(base, skew, cx)
    case False{}:
      st.byte(MXdist{}, extra, skew, cx.set.dist(cx, base))

# a distance symbol
def rd.distsym(zz: Bool, +sy: U32, +skew: U32, cx: Cx) -> St:
  match zz:
    case False{}:
      st.fail()
    case True{}:
      +extra = tab.at(dist.extra(), U32.is_zero(sy), sy)
      rd.xdist0(U32.is_zero(extra), extra, tab.at(dist.base(), U32.is_zero(sy), sy), skew, cx)

# extra length bits added to the base kept in `left`
def rd.xlen(+val: U32, +skew: U32, +cx: Cx) -> St:
  st.sym(WDist{}, skew, cx.set.left(cx, (cx.left(cx) + val : U32)))

# no extra length bits
def rd.xlen0(zz: Bool, +extra: U32, +base: U32, +skew: U32, cx: Cx) -> St:
  match zz:
    case True{}:
      st.sym(WDist{}, skew, cx.set.left(cx, base))
    case False{}:
      st.byte(MXlen{}, extra, skew, cx.set.left(cx, base))

# a length symbol, or an illegal one
def rd.lit.n(zz: Bool, +sy: U32, +skew: U32, cx: Cx) -> St:
  match zz:
    case False{}:
      st.fail()
    case True{}:
      +ix = (sy - 257 : U32)
      +extra = tab.at(len.extra(), U32.is_zero(ix), ix)
      rd.xlen0(U32.is_zero(extra), extra, tab.at(len.base(), U32.is_zero(ix), ix), skew, cx)

# end of block, or a length code
def rd.lit.e(zend: Bool, zlen: Bool, +sy: U32, +skew: U32, cx: Cx) -> St:
  match zend:
    case True{}:
      rd.after(skew, cx)
    case False{}:
      rd.lit.n(zlen, sy, skew, cx)

# a literal byte
def rd.lit(zlit: Bool, zend: Bool, zlen: Bool, +sy: U32, +skew: U32, cx: Cx) -> St:
  match zlit:
    case True{}:
      st.sym(WLit{}, skew, cx.emit(cx, sy))
    case False{}:
      rd.lit.e(zend, zlen, sy, skew, cx)

# dispatch a decoded symbol
def rd.symbol(wh: Wh, +sy: U32, +skew: U32, cx: Cx) -> St:
  match wh:
    case WLit{}:
      rd.lit(U32.is_lt(sy, 256), U32.is_eq(sy, 256), U32.is_le(sy, 285), sy, skew, cx)
    case WDist{}:
      rd.distsym(U32.is_le(sy, 29), sy, skew, cx)
    case WClen{}:
      rd.clens(U32.is_le(sy, 15), U32.is_eq(sy, 16), U32.is_eq(sy, 17), U32.is_eq(sy, 18), sy, skew, cx)

# Adler matches the bytes
def rd.adler.eq(zz: Bool, +skew: U32, cx: Cx) -> St:
  match zz:
    case True{}:
      St{PDone{}, MAdler{}, WLit{}, 0, 0, 0, [], skew, cx}
    case False{}:
      st.fail()

# one more Adler byte, or the check
def rd.adler.z(zz: Bool, +skew: U32, cx: Cx) -> St:
  match zz cx:
    case False{} c2:
      st.byte(MAdler{}, 8, skew, c2)
    case True{} Cx{final, +left, +dist, out, win, +wpos, +pend, +run, hs}:
      +raw = List.reverse(&2, U32, out)
      rd.adler.eq(U32.is_eq(adler.of(raw), run), skew, Cx{final, left, dist, raw, win, wpos, pend, run, hs})

# one big-endian Adler byte
def rd.adler(+val: U32, +skew: U32, cx: Cx) -> St:
  match cx:
    case Cx{final, +left, +dist, out, win, +wpos, +pend, +run, hs}:
      +run2 = ((255 .&. val : U32) .|. (run << 8n : U32) : U32)
      +left2 = (left - 1 : U32)
      rd.adler.z(U32.is_zero(left2), skew, Cx{final, left2, dist, out, win, wpos, pend, run2, hs})

# a finished integer field
def rd.field(md: Md, +val: U32, +skew: U32, cx: Cx) -> St:
  match md:
    case MCmf{}:
      rd.cmf(val, skew, cx)
    case MFlg{}:
      rd.flg(val, skew, cx)
    case MBlk{}:
      rd.blk(val, skew, cx)
    case MLen{}:
      rd.len(val, skew, cx)
    case MNlen{}:
      rd.nlen(val, skew, cx)
    case MData{}:
      rd.data(val, skew, cx)
    case MHlit{}:
      rd.hlit(val, skew, cx)
    case MHdist{}:
      rd.hdist(val, skew, cx)
    case MHclen{}:
      rd.hclen(val, skew, cx)
    case MClen{}:
      rd.clen(val, skew, cx)
    case MXlen{}:
      rd.xlen(val, skew, cx)
    case MXdist{}:
      rd.xdist(val, skew, cx)
    case MAdler{}:
      rd.adler(val, skew, cx)
    case MRep{}:
      rd.mrep(val, skew, cx)

# keep a partial integer, or dispatch it
def rd.raw(zz: Bool, md: Md, +acc: U32, +got: U32, +need: U32, +skew: U32, cx: Cx) -> St:
  match zz:
    case False{}:
      St{PByte{}, md, WLit{}, acc, got, need, [], skew, cx}
    case True{}:
      rd.field(md, acc, skew, cx)

# the code is `index + code - first` in canonical order when it is below
# `first + count`; otherwise try the next length
def rd.hbit.at(
  zz: Bool,
  rest: List<&2, U32>,
  +wh: Wh,
  +code: U32,
  +first: U32,
  +index: U32,
  +cnt: U32,
  +skew: U32,
  +cx: Cx
) -> St:
  match zz:
    case True{}:
      rd.symbol(wh, cx.sym(wh, cx, ((index + code : U32) - first : U32)), skew, cx)
    case False{}:
      St{PSym{}, MBlk{}, wh, (code << 1n : U32), ((first + cnt : U32) << 1n : U32), (index + cnt : U32), rest, skew,
        cx}

# one Huffman bit is in `code`. Past length 15 no symbol is an error.
def rd.hbit(cur: List<&2, U32>, +wh: Wh, +code: U32, +first: U32, +index: U32, +skew: U32, cx: Cx) -> St:
  match cur:
    case Nil{}:
      st.fail()
    case Con{+cnt, rest}:
      rd.hbit.at(U32.is_lt(code, (first + cnt : U32)), rest, wh, code, first, index, cnt, skew, cx)

# one bit of the phase the reader is in
def rd.on(
  ph: Ph,
  md: Md,
  wh: Wh,
  +acc: U32,
  +got: U32,
  +need: U32,
  cur: List<&2, U32>,
  +skew: U32,
  cx: Cx,
  +bit: U32
) -> St:
  match ph:
    case PFail{}:
      st.fail()
    case PDone{}:
      St{PDone{}, md, wh, acc, got, need, cur, skew, cx}
    case PAlign{}:
      rd.align(U32.is_zero(skew), md, skew, cx)
    case PByte{}:
      +acc2 = ((bit << U32.to_nat(got) : U32) .|. acc : U32)
      +got2 = (got + 1 : U32)
      rd.raw(U32.is_eq(got2, need), md, acc2, got2, need, skew, cx)
    case PSym{}:
      rd.hbit(cur, wh, (acc .|. bit : U32), got, need, skew, cx)

# advance one bit. The bit count mod 8 tracks byte alignment.
def rd.step(st: St, +bit: U32) -> St:
  match st:
    case St{ph, md, wh, +acc, +got, +need, cur, +skew, cx}:
      rd.on(ph, md, wh, acc, got, need, cur, ((skew + 1 : U32) .&. 7 : U32), cx, bit)

# advance the eight bits of a byte, low bit first
def rd.step8(st: St, +bb: U32) -> St:
  s1 = rd.step(st, (1 .&. bb : U32))
  s2 = rd.step(s1, (1 .&. (bb >> 1n : U32) : U32))
  s3 = rd.step(s2, (1 .&. (bb >> 2n : U32) : U32))
  s4 = rd.step(s3, (1 .&. (bb >> 3n : U32) : U32))
  s5 = rd.step(s4, (1 .&. (bb >> 4n : U32) : U32))
  s6 = rd.step(s5, (1 .&. (bb >> 5n : U32) : U32))
  s7 = rd.step(s6, (1 .&. (bb >> 6n : U32) : U32))
  rd.step(s7, (1 .&. (bb >> 7n : U32) : U32))

# walk the bytes until the reader finishes or the bytes run out
def inflate.go(xs: List<&2, U32>, st: St) -> Maybe<&2, List<&2, U32>>:
  match xs st:
    case _xs St{PDone{}, _md, _wh, _a, _g, _n, _c, _sk, Cx{_f, _l, _d, out, _w, _wp, _p, _r, _h}}:
      Some{out}
    case _xs St{PFail{}, _md, _wh, _a, _g, _n, _c, _sk, _cx}:
      None{}
    case Nil{} _st:
      None{}
    case Con{+b, t} st2:
      inflate.go(t, rd.step8(st2, b))

# inflate a zlib wrapper around DEFLATE, as PNG compression method 0
def inflate(xs: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  inflate.go(xs, st.empty())
