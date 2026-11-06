# src/jpeg: sequential 8-bit Huffman JPEG (SOF0 baseline, SOF1 extended) in one scan or several (T.81 E.2):
# grayscale, YCbCr, or RGB as coded when an Adobe APP14 or the component ids say so (libjpeg's rule).
#
# Trusted, not proved: decode_jpeg reads the baseline files other encoders
# (libjpeg, Pillow) write, to within the IDCT accuracy T.83 asks of a decoder:
# its IDCT is libjpeg's accurate integer one (jidctint.c, decode.idct1),
# step for step, so on files libjpeg-turbo writes the gray samples are
# libjpeg-turbo's own and colour differs only by the YCbCr conversion's
# rounding (measured with Pillow, a test, not a proof).
# The laws place each decoded sample (laws/JpegPlacesComponentSamples.bend)
# but do not prove its value; that needs the other encoder. The Pillow check
# in bench/ exercises it.

import Base

# a decoded picture: width, height, and row-major samples, each packed
# 0xAARRGGBB with alpha 255
type Pic is Data:
  Pic{w: U32, h: U32, pixels: List<&2, U32>}

# one Huffman table as its code tree (T.81 C): a code's bits, the first highest, lead from the root to the leaf
# holding its symbol, a 0 bit to a node's zero side and a 1 bit to its one side; a gap is where no code leads
type Huff is Data:
  HGap{}
  HLeaf{sym: U32}
  HNode{zero: Huff, one: Huff}

# SOF0 / SOF1 frame geometry. Sampling factors are 1 to 4.
type Frame is Data:
  Frame{w: U32, h: U32, nf: U32, ids: List<&2, U32>, hs: List<&2, U32>, vs: List<&2, U32>,
    tq: List<&2, U32>, hmax: U32, vmax: U32}

# one SOS header
type Scan is Data:
  Scan{ns: U32, sids: List<&2, U32>, td: List<&2, U32>, ta: List<&2, U32>, ss: U32, se: U32, ah: U32}

# four quant tables and four DC / AC Huffman tables
type Tabs is Data:
  Tabs{q0: List<&2, U32>, q1: List<&2, U32>, q2: List<&2, U32>, q3: List<&2, U32>, dc0: Huff, dc1: Huff,
    dc2: Huff, dc3: Huff, ac0: Huff, ac1: Huff, ac2: Huff, ac3: Huff}

# marker walk: seeking, a marker byte, a length, a payload, or the entropy scan. Rest: a scan ended at
# marker mark, not RSTn or EOI, after a frame header; acc holds the bytes after it, last first, for the next walk
# (decode.chain), since tables and further scans may follow a scan (T.81 B.2.1, E.2)
type Phase is Data:
  Seek{}
  Mark{}
  LenHi{mark: U32}
  LenLo{mark: U32, hi: U32}
  Pay{mark: U32, left: Nat, acc: List<&2, U32>}
  Ent{}
  EntFF{}
  Stop{}
  Rest{mark: U32, acc: List<&2, U32>}

# parser state. kind 1 is a baseline frame. bad 1 rejects the file.
type St is Data:
  St{phase: Phase, frame: Frame, scan: Scan, tabs: Tabs, ent: List<&2, U32>, ri: U32, kind: U32, bad: U32}

# bit reader. n bits remain in buf. ok is 0 after a truncated or marked stream.
type Bits is Data:
  Bits{n: U32, ok: U32, buf: U32, xs: List<&2, U32>}

# one decoded Huffman symbol
type Hit is Data:
  Hit{sym: U32, bits: Bits, ok: U32}

# eight values: one row of a block
type R8 is Data:
  R8{v0: U32, v1: U32, v2: U32, v3: U32, v4: U32, v5: U32, v6: U32, v7: U32}

# an 8 by 8 block of values, row by row
type B8 is Data:
  B8{r0: R8, r1: R8, r2: R8, r3: R8, r4: R8, r5: R8, r6: R8, r7: R8}

# AC run state inside one block: the next coefficient's zigzag index k, the dequantised coefficients so far in
# natural order, and the quantisation table's entries from index k on
type Ac is Data:
  Ac{k: U32, zz: B8, qs: List<&2, U32>, bits: Bits, done: U32, ok: U32}

# one decoded 8x8 block, level-shifted samples, and the DC predictor
type Blk is Data:
  Blk{samples: List<&2, U32>, bits: Bits, pred: U32, ok: U32}

# DC predictors, one per scan component
type Preds is Data:
  Preds{a: U32, b: U32, c: U32, d: U32}

# where the current block sits in the frame
type Ctrl is Data:
  Ctrl{comp: U32, bi: U32, mx: U32, my: U32, mcu: U32, rst: U32}

# the block that follows, and whether a restart marker comes first
type Adv is Data:
  Adv{ctrl: Ctrl, due: U32, expect: U32}

# pixel rectangle one block sample covers
type Geom is Data:
  Geom{ox: U32, oy: U32, pw: U32, ph: U32, w: U32, h: U32}

# SOF component lists while they are being read, and whether every component
# so far was read whole with sampling factors the decoder places
type Comps is Data:
  Comps{ids: List<&2, U32>, hs: List<&2, U32>, vs: List<&2, U32>, tq: List<&2, U32>, ok: Bool}

def decode.sign(+aa: U32) -> U32:
  U32.shrn(aa, 31n)

def decode.neg32(+aa: U32) -> U32:
  (U32.not(aa) + 1 : U32)

def decode.abs.s(ss: U32, +aa: U32) -> U32:
  match ss:
    case 0:
      aa
    case _:
      decode.neg32(aa)

def decode.abs(+aa: U32) -> U32:
  decode.abs.s(decode.sign(aa), aa)

def decode.carry.b(cc: Bool) -> U32:
  match cc:
    case True{}:
      1
    case False{}:
      0

def decode.carry(+aa: U32, +sum: U32) -> U32:
  decode.carry.b(U32.is_lt(sum, aa))

def decode.neg64.c(zz: Bool, +nh: U32, +nl: U32) -> U32 & U32:
  match zz:
    case True{}:
      ((nh + 1 : U32), nl)
    case False{}:
      (nh, nl)

def decode.neg64(+hh: U32, +ll: U32) -> U32 & U32:
  +nl = (U32.not(ll) + 1 : U32)
  +nh = U32.not(hh)
  decode.neg64.c(U32.is_eq(nl, 0), nh, nl)

def decode.split(+aa: U32) -> U32 & U32:
  (U32.and(aa, 65535), U32.shrn(aa, 16n))

def decode.widemul.pack(+neg: U32, +hi: U32, +lo: U32) -> U32 & U32:
  match neg:
    case 0:
      (hi, lo)
    case _:
      decode.neg64(hi, lo)

def decode.widemul.bb(+a0: U32, +a1: U32, bb: U32 & U32, +neg: U32) -> U32 & U32:
  (+b0, +b1) = bb
  +p00 = (a0 * b0 : U32)
  +p01 = (a0 * b1 : U32)
  +p10 = (a1 * b0 : U32)
  +p11 = (a1 * b1 : U32)
  +mid = (U32.shrn(p00, 16n) + U32.and(p01, 65535) + U32.and(p10, 65535) : U32)
  +lo = U32.or(U32.and(p00, 65535), U32.shln(U32.and(mid, 65535), 16n))
  +hi = (p11 + U32.shrn(p01, 16n) + U32.shrn(p10, 16n) + U32.shrn(mid, 16n) : U32)
  decode.widemul.pack(neg, hi, lo)

def decode.widemul.aa(aa: U32 & U32, +bb: U32, +neg: U32) -> U32 & U32:
  (+a0, +a1) = aa
  decode.widemul.bb(a0, a1, decode.split(bb), neg)

def decode.widemul.go(+aa: U32, +bb: U32, +neg: U32) -> U32 & U32:
  decode.widemul.aa(decode.split(aa), bb, neg)

def decode.widemul(+aa: U32, +bb: U32) -> U32 & U32:
  decode.widemul.go(decode.abs(aa), decode.abs(bb), U32.and(U32.xor(decode.sign(aa), decode.sign(bb)), 1))

# the encoder's forward DCT (src/jpeg_enc.bend, encode.q17) rounds with this: a 64-bit dot product (hh, ll), in
# units of 2^-16, as the pass's result. The row pass (fine) halves it and keeps four fraction bits (a shift by 13), so
# the column pass rounds once, at the end, from what the row pass computed, taking those four bits off with its half
# (a shift by 21). Rounding to the nearest, half away from 0.
def decode.qs.res(fine: Bool, +hh: U32, +ll: U32) -> U32:
  match fine:
    case True{}:
      U32.or(U32.shrn(ll, 13n), U32.shln(U32.and(hh, 8191), 19n))
    case False{}:
      U32.or(U32.shrn(ll, 21n), U32.shln(U32.and(hh, 2097151), 11n))

# half the pass's last unit, added before the shift so the shift rounds
def decode.qs.half(fine: Bool) -> U32:
  match fine:
    case True{}:
      4096
    case False{}:
      1048576

def decode.qs.sign2(neg: Bool, +res: U32) -> U32:
  match neg:
    case False{}:
      res
    case True{}:
      decode.neg32(res)

def decode.qs.div(+hh: U32, +ll: U32, neg: Bool, +fine: Bool) -> U32:
  +l2 = (ll + decode.qs.half(fine) : U32)
  +h2 = (hh + decode.carry(ll, l2) : U32)
  decode.qs.sign2(neg, decode.qs.res(fine, h2, l2))

def decode.qs.neg(pp: U32 & U32, +fine: Bool) -> U32:
  (h, l) = pp
  decode.qs.div(h, l, True{}, fine)

def decode.qs.pos(pos: Bool, +hh: U32, +ll: U32, +fine: Bool) -> U32:
  match pos:
    case True{}:
      decode.qs.div(hh, ll, False{}, fine)
    case False{}:
      decode.qs.neg(decode.neg64(hh, ll), fine)

def decode.qs(+hh: U32, +ll: U32, +fine: Bool) -> U32:
  decode.qs.pos(U32.is_lt(hh, 2147483648), hh, ll, fine)

def decode.at.m(mm: Maybe<&2, U32>) -> U32:
  match mm:
    case Some{v}:
      v
    case None{}:
      0

def decode.at(xs: List<&2, U32>, +ii: U32) -> U32:
  decode.at.m(List.get(&2, U32, xs, U32.to_nat(ii)))

def decode.cos() -> List<&2, U32>:
  [46341, 64277, 60547, 54491, 46341, 36410, 25080, 12785, 46341, 54491, 25080, 4294954511, 4294920955,
    4294903019, 4294906749, 4294930886, 46341, 36410, 4294942216, 4294903019, 4294920955, 12785, 60547, 54491,
    46341, 12785, 4294906749, 4294930886, 46341, 54491, 4294942216, 4294903019, 46341, 4294954511, 4294906749,
    36410, 46341, 4294912805, 4294942216, 64277, 46341, 4294930886, 4294942216, 64277, 4294920955, 4294954511,
    60547, 4294912805, 46341, 4294912805, 25080, 12785, 4294920955, 64277, 4294906749, 36410, 46341, 4294903019,
    60547, 4294912805, 46341, 4294930886, 25080, 4294954511]

def decode.clamp.hi(hi: Bool, +vv: U32) -> U32:
  match hi:
    case True{}:
      255
    case False{}:
      vv

def decode.clamp8.s(ss: U32, +vv: U32) -> U32:
  match ss:
    case 0:
      decode.clamp.hi(U32.is_gt(vv, 255), vv)
    case _:
      0

def decode.clamp8(+vv: U32) -> U32:
  decode.clamp8.s(decode.sign(vv), vv)

def decode.huff0() -> Huff:
  HGap{}

def decode.frame0() -> Frame:
  Frame{0, 0, 0, [], [], [], [], 1, 1}

def decode.scan0() -> Scan:
  Scan{0, [], [], [], 0, 63, 0}

def decode.tabs0() -> Tabs:
  Tabs{[], [], [], [], decode.huff0(), decode.huff0(), decode.huff0(), decode.huff0(), decode.huff0(),
    decode.huff0(), decode.huff0(), decode.huff0()}

def decode.st0() -> St:
  St{Seek{}, decode.frame0(), decode.scan0(), decode.tabs0(), [], 0, 0, 0}

def decode.nlist(xs: List<&2, U32>, +nn: U32) -> U32:
  match xs:
    case Nil{}:
      nn
    case _h <> t:
      decode.nlist(t, (nn + 1 : U32))

def decode.drop(xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case _h <> t:
      decode.drop(t)

# the nodes at a depth of the code tree from the nodes one level down, left to right, two to a node; a last one
# alone has a gap on its one side
def decode.ht.pair(ns: List<&2, Huff>) -> List<&2, Huff>:
  match ns:
    case Nil{}:
      []
    case aa <> rest:
      match rest:
        case Nil{}:
          [HNode{aa, HGap{}}]
        case bb <> more:
          HNode{aa, bb} <> decode.ht.pair(more)

# a leaf for each symbol, in order, before the nodes ns
def decode.ht.leaves(ys: List<&2, U32>, ns: List<&2, Huff>) -> List<&2, Huff>:
  match ys:
    case Nil{}:
      ns
    case yy <> rest:
      HLeaf{yy} <> decode.ht.leaves(rest, ns)

# the symbols of each code length, the counts' first length first, as a list onto acc, the last length first
def decode.ht.groups(cs: List<&2, U32>, +ys: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match cs:
    case Nil{}:
      acc
    case +cc <> rest:
      decode.ht.groups(rest, List.drop(&2, U32, ys, U32.to_nat(cc)), List.take(&2, U32, ys, U32.to_nat(cc)) <> acc)

# the nodes at each depth from the deepest up: at a depth, the leaves of the codes of that length, left to right
# in symbol order, then the nodes the depth below pairs up. Canonical codes (T.81 C) of one length are consecutive
# and come before every longer code's prefix, so this is the tree of the canonical codes
def decode.ht.up(gs: List<&2, List<&2, U32>>, ns: List<&2, Huff>) -> List<&2, Huff>:
  match gs:
    case Nil{}:
      ns
    case gg <> rest:
      decode.ht.up(rest, decode.ht.leaves(gg, decode.ht.pair(ns)))

# the root of the tree: the one node over depth 1, a gap for no codes
def decode.ht.root(ns: List<&2, Huff>) -> Huff:
  match ns:
    case Nil{}:
      HGap{}
    case aa <> rest:
      +_r = rest
      aa

# the code tree of a DHT table's 16 counts (codes of length 1 to 16) and its symbols in order (T.81 C, Figure C.1
# to C.3), built level by level from the counts, with no code arithmetic
def decode.canon(+counts: List<&2, U32>, +symbols: List<&2, U32>) -> Huff:
  decode.ht.root(decode.ht.pair(decode.ht.up(decode.ht.groups(counts, symbols, []), [])))

def decode.index.add(eq: Bool, +ii: U32) -> U32:
  match eq:
    case True{}:
      ii
    case False{}:
      (ii + 1 : U32)

# the position of want in xs, the first if it is there more than once, 0 when it is absent. eq says the
# element before xs was want, and ii counts the elements before it. Matches with U32.is_eq, so a law reaches it.
def decode.index(xs: List<&2, U32>, eq: Bool, +want: U32, +ii: U32) -> U32:
  match xs:
    case Nil{}:
      match eq:
        case True{}:
          ii
        case False{}:
          0
    case +n <> t:
      match eq:
        case True{}:
          +_d = decode.drop(n <> t)
          ii
        case False{}:
          decode.index(t, U32.is_eq(n, want), want, decode.index.add(U32.is_eq(n, want), ii))

# whether a list of bytes opens with want. U32.is_eq, not a literal pattern, so a law reaches a
# symbolic byte.
def decode.head.is(xs: List<&2, U32>, +want: U32) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case +bb <> _rest:
      U32.is_eq(bb, want)

# left more bits onto acc, most significant first. nn bits remain in buf, top bit first at bit 7; eq
# says buf is empty. ff says the byte before xs was a 255, and h255 and h0 whether xs opens with 255
# or 0, each asked with U32.is_eq so a law reaches a symbolic byte. After a 255, 0 is a stuffed 255
# (eight one bits) and 255 a fill byte; any other byte is a marker, and it or the end of the bytes
# reads zero bits and sets ok to 0.
def decode.nbits(
  left: Nat,
  eq: Bool,
  xs: List<&2, U32>,
  ff: Bool,
  h255: Bool,
  h0: Bool,
  +nn: U32,
  +buf: U32,
  +ok: U32,
  +acc: U32
) -> Bits & U32:
  match left:
    case 0n:
      (Bits{nn, ok, buf, xs}, acc)
    case 1n+p:
      match eq:
        case False{}:
          decode.nbits(p, U32.is_eq((nn - 1 : U32), 0), xs, ff, h255, h0, (nn - 1 : U32), U32.and(255, U32.shl(buf)),
            ok, U32.or(U32.shrn(buf, 7n), U32.shl(acc)))
        case True{}:
          match xs:
            case Nil{}:
              decode.nbits(p, False{}, [], False{}, False{}, False{}, 7, 0, 0, U32.shl(acc))
            case +bb <> +rest:
              match ff:
                case False{}:
                  match h255:
                    case True{}:
                      decode.nbits(Succ{p}, True{}, rest, True{}, decode.head.is(rest, 255), decode.head.is(rest, 0),
                        0, 0, ok, acc)
                    case False{}:
                      decode.nbits(p, False{}, rest, False{}, decode.head.is(rest, 255), decode.head.is(rest, 0), 7,
                        U32.and(255, U32.shl(bb)), ok, U32.or(U32.shrn(bb, 7n), U32.shl(acc)))
                case True{}:
                  match h255:
                    case True{}:
                      decode.nbits(Succ{p}, True{}, rest, True{}, decode.head.is(rest, 255), decode.head.is(rest, 0),
                        0, 0, ok, acc)
                    case False{}:
                      match h0:
                        case True{}:
                          decode.nbits(p, False{}, rest, False{}, decode.head.is(rest, 255), decode.head.is(rest, 0),
                            7, 254, ok, U32.or(1, U32.shl(acc)))
                        case False{}:
                          decode.nbits(p, False{}, rest, False{}, decode.head.is(rest, 255), decode.head.is(rest, 0),
                            7, 0, 0, U32.shl(acc))

# nn more bits from a reader, the first of them at the next byte when its buffer is empty
def decode.nbits.of(left: Nat, +xs: List<&2, U32>, +nn: U32, +buf: U32, +ok: U32) -> Bits & U32:
  decode.nbits(left, U32.is_eq(nn, 0), xs, False{}, decode.head.is(xs, 255), decode.head.is(xs, 0), nn, buf, ok, 0)

def decode.one(bits: Bits) -> Bits & U32:
  match bits:
    case Bits{+n, +ok, +buf, xs}:
      decode.nbits.of(1n, xs, n, buf, ok)

# a symbol found, the reader after its code
def decode.huff.hit(+sym: U32, bits: Bits) -> Hit:
  match bits:
    case Bits{+n, +ok, +buf, xs}:
      Hit{sym, Bits{n, ok, buf, xs}, ok}

# a Huffman lookup in progress: the subtree of the code tree the bits read so far lead to, and the reader after them
type Walk is Data:
  Walk{tab: Huff, bits: Bits}

# the walk after one more bit: the zero side of a node for a 0 bit, else its one side
def decode.huff.next(got: Bits & U32, zero: Huff, one: Huff) -> Walk:
  match got:
    case (bits, +bit):
      match bit:
        case 0:
          +_t = one
          Walk{zero, bits}
        case _:
          +_t = zero
          Walk{one, bits}

# the symbol a walk ends at: a leaf is its symbol, the reader left after its code; a node reads one more bit and
# goes on from the side it leads to, at most left more bits; a gap, or a code longer than that, is no symbol, ok 0
def decode.huff.walk(left: Nat, ww: Walk) -> Hit:
  match left:
    case 0n:
      match ww:
        case Walk{tab, bits}:
          match tab:
            case HLeaf{+s}:
              decode.huff.hit(s, bits)
            case _:
              +_t = tab
              Hit{0, bits, 0}
    case 1n+p:
      match ww:
        case Walk{tab, bits}:
          match tab:
            case HLeaf{+s}:
              decode.huff.hit(s, bits)
            case HGap{}:
              Hit{0, bits, 0}
            case HNode{zero, one}:
              decode.huff.walk(p, decode.huff.next(decode.one(bits), zero, one))

# the symbol whose code the reader holds next, from a table's code tree (T.81 C), codes of at most left bits (T.81
# F.2.2.3 decodes codes of at most 16 bits)
def decode.huff(left: Nat, tab: Huff, bits: Bits) -> Hit:
  decode.huff.walk(left, Walk{tab, bits})

def decode.bits.of(bits: Bits) -> Nat & U32 & List<&2, U32> & U32 & U32:
  match bits:
    case Bits{+n, +ok, +buf, xs}:
      (0n, n, xs, buf, ok)

def decode.read.n(+cat: U32, bits: Bits) -> Bits & U32:
  match bits:
    case Bits{+n, +ok, +buf, xs}:
      decode.nbits.of(U32.to_nat(cat), xs, n, buf, ok)

def decode.extend.s(small: Bool, +mag: U32, +cat: U32) -> U32:
  match small:
    case False{}:
      mag
    case True{}:
      (mag - (U32.shln(1, U32.to_nat(cat)) - 1 : U32) : U32)

def decode.extend(+cat: U32, +mag: U32) -> U32:
  match cat:
    case 0:
      0
    case _:
      decode.extend.s(U32.is_lt(mag, U32.shln(1, U32.to_nat((cat - 1 : U32)))), mag, cat)

# the natural-order position (row * 8 + column) of zigzag index k (T.81 Figure A.6)
def decode.zig.at(+kk: U32) -> U32:
  match kk:
    case 0:
      0
    case 1:
      1
    case 2:
      8
    case 3:
      16
    case 4:
      9
    case 5:
      2
    case 6:
      3
    case 7:
      10
    case 8:
      17
    case 9:
      24
    case 10:
      32
    case 11:
      25
    case 12:
      18
    case 13:
      11
    case 14:
      4
    case 15:
      5
    case 16:
      12
    case 17:
      19
    case 18:
      26
    case 19:
      33
    case 20:
      40
    case 21:
      48
    case 22:
      41
    case 23:
      34
    case 24:
      27
    case 25:
      20
    case 26:
      13
    case 27:
      6
    case 28:
      7
    case 29:
      14
    case 30:
      21
    case 31:
      28
    case 32:
      35
    case 33:
      42
    case 34:
      49
    case 35:
      56
    case 36:
      57
    case 37:
      50
    case 38:
      43
    case 39:
      36
    case 40:
      29
    case 41:
      22
    case 42:
      15
    case 43:
      23
    case 44:
      30
    case 45:
      37
    case 46:
      44
    case 47:
      51
    case 48:
      58
    case 49:
      59
    case 50:
      52
    case 51:
      45
    case 52:
      38
    case 53:
      31
    case 54:
      39
    case 55:
      46
    case 56:
      53
    case 57:
      60
    case 58:
      61
    case 59:
      54
    case 60:
      47
    case 61:
      55
    case 62:
      62
    case _:
      63

# a row with column cc set to vv
def decode.r8.set(rr: R8, +cc: U32, +vv: U32) -> R8:
  match rr:
    case R8{+v0, +v1, +v2, +v3, +v4, +v5, +v6, +v7}:
      match cc:
        case 0:
          +_x = v0
          R8{vv, v1, v2, v3, v4, v5, v6, v7}
        case 1:
          +_x = v1
          R8{v0, vv, v2, v3, v4, v5, v6, v7}
        case 2:
          +_x = v2
          R8{v0, v1, vv, v3, v4, v5, v6, v7}
        case 3:
          +_x = v3
          R8{v0, v1, v2, vv, v4, v5, v6, v7}
        case 4:
          +_x = v4
          R8{v0, v1, v2, v3, vv, v5, v6, v7}
        case 5:
          +_x = v5
          R8{v0, v1, v2, v3, v4, vv, v6, v7}
        case 6:
          +_x = v6
          R8{v0, v1, v2, v3, v4, v5, vv, v7}
        case _:
          +_x = v7
          R8{v0, v1, v2, v3, v4, v5, v6, vv}

# a block with row rw, column cc set to vv
def decode.b8.set(bb: B8, +rw: U32, +cc: U32, +vv: U32) -> B8:
  match bb:
    case B8{r0, r1, r2, r3, r4, r5, r6, r7}:
      match rw:
        case 0:
          B8{decode.r8.set(r0, cc, vv), r1, r2, r3, r4, r5, r6, r7}
        case 1:
          B8{r0, decode.r8.set(r1, cc, vv), r2, r3, r4, r5, r6, r7}
        case 2:
          B8{r0, r1, decode.r8.set(r2, cc, vv), r3, r4, r5, r6, r7}
        case 3:
          B8{r0, r1, r2, decode.r8.set(r3, cc, vv), r4, r5, r6, r7}
        case 4:
          B8{r0, r1, r2, r3, decode.r8.set(r4, cc, vv), r5, r6, r7}
        case 5:
          B8{r0, r1, r2, r3, r4, decode.r8.set(r5, cc, vv), r6, r7}
        case 6:
          B8{r0, r1, r2, r3, r4, r5, decode.r8.set(r6, cc, vv), r7}
        case _:
          B8{r0, r1, r2, r3, r4, r5, r6, decode.r8.set(r7, cc, vv)}

# a block with the coefficient of zigzag index k set to vv
def decode.cf.put(zz: B8, +kk: U32, +vv: U32) -> B8:
  +zp = decode.zig.at(kk)
  decode.b8.set(zz, U32.shrn(zp, 3n), U32.and(zp, 7), vv)

# eight zeros
def decode.r8.zero() -> R8:
  R8{0, 0, 0, 0, 0, 0, 0, 0}

# a block of zeros
def decode.b8.zero() -> B8:
  B8{decode.r8.zero(), decode.r8.zero(), decode.r8.zero(), decode.r8.zero(), decode.r8.zero(), decode.r8.zero(),
    decode.r8.zero(), decode.r8.zero()}

# the entry of a list after left more (a block's samples, a quantisation table's entries), 0 past its end
def decode.nth(left: Nat, qs: List<&2, U32>) -> U32:
  match left:
    case 0n:
      match qs:
        case Nil{}:
          0
        case +qq <> _rest:
          qq
    case 1n+p:
      match qs:
        case Nil{}:
          0
        case _q <> rest:
          decode.nth(p, rest)

# the entries of a list after left more
def decode.skip(left: Nat, qs: List<&2, U32>) -> List<&2, U32>:
  match left:
    case 0n:
      qs
    case 1n+p:
      match qs:
        case Nil{}:
          []
        case _q <> rest:
          decode.skip(p, rest)

def decode.ac.stored(full: Bool, +kk: U32, zz: B8, qs: List<&2, U32>, bits: Bits, +ok: U32) -> Ac:
  match full:
    case True{}:
      Ac{kk, zz, qs, bits, 1, ok}
    case False{}:
      Ac{kk, zz, qs, bits, 0, ok}

# coefficient nk, run places after the coefficient before it, dequantised by its entry; the entries after it go on
def decode.ac.store(got: Bits & U32, +sz: U32, +nk: U32, +run: U32, zz: B8, +qs: List<&2, U32>, +ok: U32) -> Ac:
  (bits, +mag) = got
  +n2 = (nk + 1 : U32)
  decode.ac.stored(U32.is_eq(n2, 64), n2, decode.cf.put(zz, nk, (decode.extend(sz, mag) * decode.nth(U32.to_nat(run),
    qs) : U32)), decode.skip(U32.to_nat((run + 1 : U32)), qs), bits, ok)

def decode.ac.bad(zz: B8, qs: List<&2, U32>, bits: Bits) -> Ac:
  Ac{64, zz, qs, bits, 1, 0}

def decode.ac.run.b(
  zzz: Bool,
  over: Bool,
  +sz: U32,
  +nk: U32,
  +run: U32,
  bits: Bits,
  zz: B8,
  qs: List<&2, U32>,
  +ok: U32
) -> Ac:
  match zzz:
    case True{}:
      decode.ac.bad(zz, qs, bits)
    case False{}:
      match over:
        case True{}:
          decode.ac.bad(zz, qs, bits)
        case False{}:
          decode.ac.store(decode.read.n(sz, bits), sz, nk, run, zz, qs, ok)

def decode.ac.run(+sym: U32, bits: Bits, +kk: U32, zz: B8, qs: List<&2, U32>, +ok: U32) -> Ac:
  +sz = U32.and(15, sym)
  +run = U32.shrn(sym, 4n)
  +nk = (kk + run : U32)
  decode.ac.run.b(U32.is_eq(sz, 0), U32.is_ge(nk, 64), sz, nk, run, bits, zz, qs, ok)

def decode.ac.zrl.eq(eq: Bool, zz: B8, qs: List<&2, U32>, bits: Bits, +ok: U32) -> Ac:
  match eq:
    case True{}:
      Ac{64, zz, qs, bits, 1, ok}
    case False{}:
      Ac{64, zz, qs, bits, 1, 0}

def decode.ac.zrl.k(more: Bool, +nk: U32, zz: B8, qs: List<&2, U32>, bits: Bits, +ok: U32) -> Ac:
  match more:
    case True{}:
      Ac{nk, zz, decode.skip(16n, qs), bits, 0, ok}
    case False{}:
      decode.ac.zrl.eq(U32.is_eq(nk, 64), zz, qs, bits, ok)

def decode.ac.zrl(+kk: U32, zz: B8, qs: List<&2, U32>, bits: Bits, +ok: U32) -> Ac:
  decode.ac.zrl.k(U32.is_lt((kk + 16 : U32), 64), (kk + 16 : U32), zz, qs, bits, ok)

# an AC symbol: EOB (0), ZRL (240), or a run and size. U32.is_eq, not literal patterns, so a law reaches a
# symbolic symbol.
def decode.ac.sym.b(
  eob: Bool,
  zrl: Bool,
  +sym: U32,
  bits: Bits,
  +kk: U32,
  zz: B8,
  qs: List<&2, U32>,
  +ok: U32
) -> Ac:
  match eob:
    case True{}:
      +_s = sym
      +_z = zrl
      Ac{kk, zz, qs, bits, 1, ok}
    case False{}:
      match zrl:
        case True{}:
          +_s = sym
          decode.ac.zrl(kk, zz, qs, bits, ok)
        case False{}:
          decode.ac.run(sym, bits, kk, zz, qs, ok)

def decode.ac.sym(+sym: U32, bits: Bits, +kk: U32, zz: B8, qs: List<&2, U32>, +ok: U32) -> Ac:
  decode.ac.sym.b(U32.is_eq(sym, 0), U32.is_eq(sym, 240), sym, bits, kk, zz, qs, ok)

def decode.ac.step(hit: Hit, +kk: U32, zz: B8, qs: List<&2, U32>, +ok: U32) -> Ac:
  match hit:
    case Hit{+sym, bits, +hok}:
      decode.ac.sym(sym, bits, kk, zz, qs, (ok * hok : U32))

def decode.ac.full(done: Bool, short: Bool, ac: Ac) -> Ac:
  match done:
    case True{}:
      ac
    case False{}:
      match short:
        case False{}:
          ac
        case True{}:
          match ac:
            case Ac{k, zz, qs, bits, _d, _o}:
              Ac{k, zz, qs, bits, 1, 0}

def decode.ac(left: Nat, ac: Ac, +tab: Huff) -> Ac:
  match left:
    case 0n:
      match ac:
        case Ac{+k, _zz, _qs, _bits, +done, _ok}:
          decode.ac.full(U32.is_eq(done, 1), U32.is_lt(k, 64), ac)
    case 1n+p:
      match ac:
        case Ac{+k, +zz, +qs, bits, +done, +ok}:
          match done:
            case 0:
              decode.ac(p, decode.ac.step(decode.huff(16n, tab, bits), k, zz, qs, ok), tab)
            case _:
              +_t = tab
              ac

def decode.zig() -> List<&2, U32>:
  [0, 1, 8, 16, 9, 2, 3, 10, 17, 24, 32, 25, 18, 11, 4, 5, 12, 19, 26, 33, 40, 48, 41, 34, 27, 20, 13, 6, 7,
    14, 21, 28, 35, 42, 49, 56, 57, 50, 43, 36, 29, 22, 15, 23, 30, 37, 44, 51, 58, 59, 52, 45, 38, 31, 39, 46,
    53, 60, 61, 54, 47, 55, 62, 63]

# xx shifted right nn bits, the sign bit copied in (an arithmetic shift)
def decode.asr.s(ss: U32, +xx: U32, nn: Nat) -> U32:
  match ss:
    case 0:
      U32.shrn(xx, nn)
    case _:
      U32.not(U32.shrn(U32.not(xx), nn))

def decode.asr(+xx: U32, nn: Nat) -> U32:
  decode.asr.s(decode.sign(xx), xx, nn)

# one output of a 1-D pass: the row pass (fine) keeps PASS1_BITS = 2 fraction bits, a shift by CONST_BITS -
# PASS1_BITS = 11; the column pass shifts by CONST_BITS + PASS1_BITS + 3 = 18, levels by 128 and clamps
def decode.idct.out(fine: Bool, +xx: U32) -> U32:
  match fine:
    case True{}:
      decode.asr((xx + 1024 : U32), 11n)
    case False{}:
      decode.clamp8((decode.asr((xx + 131072 : U32), 18n) + 128 : U32))

# one 1-D pass of libjpeg's accurate integer IDCT (jidctint.c, jpeg_idct_islow: the Loeffler, Ligtenberg and
# Moschytz factorisation, 12 multiplies, CONST_BITS = 13), over eight values
def decode.idct1(rr: R8, +fine: Bool) -> R8:
  match rr:
    case R8{+d0, +d1, +d2, +d3, +d4, +d5, +d6, +d7}:
      +z1 = ((d2 + d6 : U32) * 4433 : U32)
      +t2 = (z1 - (d6 * 15137 : U32) : U32)
      +t3 = (z1 + (d2 * 6270 : U32) : U32)
      +t0 = U32.shln((d0 + d4 : U32), 13n)
      +t1 = U32.shln((d0 - d4 : U32), 13n)
      +e10 = (t0 + t3 : U32)
      +e13 = (t0 - t3 : U32)
      +e11 = (t1 + t2 : U32)
      +e12 = (t1 - t2 : U32)
      +y1 = ((d7 + d1 : U32) * 7373 : U32)
      +y2 = ((d5 + d3 : U32) * 20995 : U32)
      +y5 = ((d7 + d3 + d5 + d1 : U32) * 9633 : U32)
      +w3 = (y5 - ((d7 + d3 : U32) * 16069 : U32) : U32)
      +w4 = (y5 - ((d5 + d1 : U32) * 3196 : U32) : U32)
      +o0 = ((d7 * 2446 : U32) - y1 + w3 : U32)
      +o1 = ((d5 * 16819 : U32) - y2 + w4 : U32)
      +o2 = ((d3 * 25172 : U32) - y2 + w3 : U32)
      +o3 = ((d1 * 12299 : U32) - y1 + w4 : U32)
      R8{decode.idct.out(fine, (e10 + o3 : U32)), decode.idct.out(fine, (e11 + o2 : U32)),
        decode.idct.out(fine, (e12 + o1 : U32)), decode.idct.out(fine, (e13 + o0 : U32)),
        decode.idct.out(fine, (e13 - o0 : U32)), decode.idct.out(fine, (e12 - o1 : U32)),
        decode.idct.out(fine, (e11 - o2 : U32)), decode.idct.out(fine, (e10 - o3 : U32))}

# a block's rows as its columns
def decode.b8.t(bb: B8) -> B8:
  match bb:
    case B8{R8{a0, a1, a2, a3, a4, a5, a6, a7}, R8{b0, b1, b2, b3, b4, b5, b6, b7}, R8{c0, c1, c2, c3, c4, c5, c6,
      c7}, R8{d0, d1, d2, d3, d4, d5, d6, d7}, R8{e0, e1, e2, e3, e4, e5, e6, e7}, R8{f0, f1, f2, f3, f4, f5, f6, f7},
        R8{g0, g1, g2, g3, g4, g5, g6, g7}, R8{h0, h1, h2, h3, h4, h5, h6, h7}}:
      B8{R8{a0, b0, c0, d0, e0, f0, g0, h0}, R8{a1, b1, c1, d1, e1, f1, g1, h1}, R8{a2, b2, c2, d2, e2, f2, g2, h2},
        R8{a3, b3, c3, d3, e3, f3, g3, h3}, R8{a4, b4, c4, d4, e4, f4, g4, h4}, R8{a5, b5, c5, d5, e5, f5, g5, h5},
          R8{a6, b6, c6, d6, e6, f6, g6, h6}, R8{a7, b7, c7, d7, e7, f7, g7, h7}}

# one 1-D pass over each row
def decode.b8.pass(bb: B8, +fine: Bool) -> B8:
  match bb:
    case B8{r0, r1, r2, r3, r4, r5, r6, r7}:
      B8{decode.idct1(r0, fine), decode.idct1(r1, fine), decode.idct1(r2, fine), decode.idct1(r3, fine),
        decode.idct1(r4, fine), decode.idct1(r5, fine), decode.idct1(r6, fine), decode.idct1(r7, fine)}

# a row's values onto acc
def decode.r8.list(rr: R8, acc: List<&2, U32>) -> List<&2, U32>:
  match rr:
    case R8{v0, v1, v2, v3, v4, v5, v6, v7}:
      v0 <> (v1 <> (v2 <> (v3 <> (v4 <> (v5 <> (v6 <> (v7 <> acc)))))))

# a block's values, row by row
def decode.b8.list(bb: B8) -> List<&2, U32>:
  match bb:
    case B8{r0, r1, r2, r3, r4, r5, r6, r7}:
      decode.r8.list(r0, decode.r8.list(r1, decode.r8.list(r2, decode.r8.list(r3, decode.r8.list(r4,
        decode.r8.list(r5, decode.r8.list(r6, decode.r8.list(r7, []))))))))

# the 2-D IDCT of dequantised coefficients in natural order: the column pass (libjpeg's pass 1, on the columns)
# then the row pass, to level-shifted samples clamped to 0 to 255, row by row
def decode.idct(zz: B8) -> List<&2, U32>:
  decode.b8.list(decode.b8.pass(decode.b8.t(decode.b8.pass(decode.b8.t(zz), True{})), False{}))

def decode.block.ac(ac: Ac, +pred: U32, +qok: U32) -> Blk:
  match ac:
    case Ac{_k, +zz, _qs, bits, _done, +ok}:
      Blk{decode.idct(zz), bits, pred, (ok * qok : U32)}

def decode.block.diff(
  got: Bits & U32,
  +cat: U32,
  +pred: U32,
  +ok: U32,
  ac: Huff,
  +quant: List<&2, U32>,
  +qok: U32
) -> Blk:
  (bits, mag) = got
  +dc = (pred + decode.extend(cat, mag) : U32)
  decode.block.ac(decode.ac(63n, Ac{1, decode.cf.put(decode.b8.zero(), 0, (dc * decode.nth(0n, quant) : U32)),
    decode.skip(1n, quant), bits, 0, ok}, ac), dc, qok)

def decode.block.cat(
  zz: Bool,
  +sym: U32,
  bits: Bits,
  +pred: U32,
  +ok: U32,
  ac: Huff,
  quant: List<&2, U32>,
  +qok: U32
) -> Blk:
  match zz:
    case True{}:
      decode.block.diff((bits, 0), 0, pred, ok, ac, quant, qok)
    case False{}:
      decode.block.diff(decode.read.n(sym, bits), sym, pred, ok, ac, quant, qok)

def decode.block.dc(hit: Hit, +pred: U32, ac: Huff, quant: List<&2, U32>, +qok: U32) -> Blk:
  match hit:
    case Hit{+sym, bits, +ok}:
      decode.block.cat(U32.is_eq(sym, 0), sym, bits, pred, ok, ac, quant, qok)

def decode.qok.b(ok: Bool) -> U32:
  match ok:
    case True{}:
      1
    case False{}:
      0

def decode.qok(quant: List<&2, U32>) -> U32:
  decode.qok.b(U32.is_eq(decode.nlist(quant, 0), 64))

def decode.block.go(bits: Bits, +pred: U32, dc: Huff, ac: Huff, +quant: List<&2, U32>) -> Blk:
  decode.block.dc(decode.huff(16n, dc, bits), pred, ac, quant, decode.qok(quant))

def decode.dc.get(tabs: Tabs, +id: U32) -> Huff:
  match tabs:
    case Tabs{_q0, _q1, _q2, _q3, +dc0, +dc1, +dc2, +dc3, _ac0, _ac1, _ac2, _ac3}:
      match id:
        case 0:
          dc0
        case 1:
          dc1
        case 2:
          dc2
        case _:
          dc3

def decode.ac.get(tabs: Tabs, +id: U32) -> Huff:
  match tabs:
    case Tabs{_q0, _q1, _q2, _q3, _dc0, _dc1, _dc2, _dc3, +ac0, +ac1, +ac2, +ac3}:
      match id:
        case 0:
          ac0
        case 1:
          ac1
        case 2:
          ac2
        case _:
          ac3

# table Tq of a frame component: no table for Tq above 3 (T.81 B.2.2), so the component's blocks are refused as
# for a table never defined
def decode.q.get(tabs: Tabs, +id: U32) -> List<&2, U32>:
  match tabs:
    case Tabs{+q0, +q1, +q2, +q3, _dc0, _dc1, _dc2, _dc3, _ac0, _ac1, _ac2, _ac3}:
      match id:
        case 0:
          q0
        case 1:
          q1
        case 2:
          q2
        case 3:
          q3
        case _:
          +_q = decode.drop(q3)
          []

def decode.pred.get(preds: Preds, +ii: U32) -> U32:
  match preds:
    case Preds{+a, +b, +c, +d}:
      match ii:
        case 0:
          (a + U32.and(b, 0) + U32.and(c, 0) + U32.and(d, 0) : U32)
        case 1:
          b
        case 2:
          c
        case _:
          d

def decode.pred.put(preds: Preds, +ii: U32, +vv: U32) -> Preds:
  match preds:
    case Preds{+a, +b, +c, +d}:
      match ii:
        case 0:
          Preds{vv, b, c, d}
        case 1:
          Preds{a, vv, c, d}
        case 2:
          Preds{a, b, vv, d}
        case _:
          Preds{a, b, c, vv}

def decode.pred.zero() -> Preds:
  Preds{0, 0, 0, 0}

def decode.preds.next(due: U32, preds: Preds, +comp: U32, +pred: U32) -> Preds:
  match due:
    case 0:
      decode.pred.put(preds, comp, pred)
    case _:
      match preds:
        case Preds{_a, _b, _c, _d}:
          decode.pred.zero()

def decode.block.of(bits: Bits, +comp: U32, preds: Preds, frame: Frame, scan: Scan, +tabs: Tabs) -> Blk:
  match bits:
    case bs:
      match comp:
        case +c:
          match preds:
            case ps:
              match frame:
                case Frame{_w, _h, _nf, +ids, _hs, _vs, +tq, _hmax, _vmax}:
                  match scan:
                    case Scan{_ns, +sids, +td, +ta, _ss, _se, _ah}:
                      decode.block.go(bs, decode.pred.get(ps, c), decode.dc.get(tabs, decode.at(td, c)),
                        decode.ac.get(tabs, decode.at(ta, c)),
                        decode.q.get(tabs, decode.at(tq, decode.index(ids, False{}, decode.at(sids, c), 0))))

def decode.rst.ok(eq: Bool, rest: List<&2, U32>) -> Bits:
  match eq:
    case True{}:
      Bits{0, 1, 0, rest}
    case False{}:
      Bits{0, 0, 0, rest}

def decode.rst.xs(xs: List<&2, U32>, +want: U32) -> Bits:
  match xs:
    case 255 <> m <> rest:
      decode.rst.ok(U32.is_eq(m, want), rest)
    case _:
      Bits{0, 0, 0, []}

def decode.rst(bits: Bits, +want: U32) -> Bits:
  match bits:
    case Bits{_n, _ok, _buf, xs}:
      decode.rst.xs(xs, want)

def decode.restart(bits: Bits, +due: U32, +expect: U32) -> Bits:
  match due:
    case 0:
      bits
    case _:
      decode.rst(bits, (208 + expect : U32))

def decode.ceil(+nn: U32, +dd: U32) -> U32:
  U32.div((nn + dd - 1 : U32), dd)

def decode.ri.nz(+ri: U32) -> U32:
  match ri:
    case 0:
      1
    case _:
      ri

def decode.adv.due.b(zero: Bool, hit: Bool, +mcu: U32, +mx: U32, +my: U32, +rst: U32) -> Adv:
  match zero:
    case True{}:
      Adv{Ctrl{0, 0, mx, my, mcu, rst}, 0, rst}
    case False{}:
      match hit:
        case True{}:
          Adv{Ctrl{0, 0, mx, my, mcu, U32.and((rst + 1 : U32), 7)}, 1, rst}
        case False{}:
          Adv{Ctrl{0, 0, mx, my, mcu, rst}, 0, rst}

def decode.adv.due(+mcu: U32, +mx: U32, +my: U32, +rst: U32, +ri: U32) -> Adv:
  decode.adv.due.b(U32.is_eq(ri, 0), U32.is_eq(U32.mod(mcu, decode.ri.nz(ri)), 0), mcu, mx, my, rst)

def decode.adv.mx(inb: Bool, +mcu: U32, +mx: U32, +my: U32, +rst: U32, +ri: U32) -> Adv:
  match inb:
    case True{}:
      decode.adv.due(mcu, mx, my, rst, ri)
    case False{}:
      decode.adv.due(mcu, 0, (my + 1 : U32), rst, ri)

def decode.adv.mcu(+mcu: U32, +mx: U32, +my: U32, +rst: U32, +ww: U32, +hmax: U32, +ri: U32) -> Adv:
  decode.adv.mx(U32.is_lt(mx, decode.ceil(ww, (hmax * 8 : U32))), mcu, mx, my, rst, ri)

def decode.adv.comp(
  more: Bool,
  +comp: U32,
  +mx: U32,
  +my: U32,
  +mcu: U32,
  +rst: U32,
  +ww: U32,
  +hmax: U32,
  +ri: U32
) -> Adv:
  match more:
    case True{}:
      Adv{Ctrl{(comp + 1 : U32), 0, mx, my, mcu, rst}, 0, rst}
    case False{}:
      decode.adv.mcu((mcu + 1 : U32), (mx + 1 : U32), my, rst, ww, hmax, ri)

def decode.adv.bi(
  more: Bool,
  +comp: U32,
  +bi: U32,
  +mx: U32,
  +my: U32,
  +mcu: U32,
  +rst: U32,
  +ww: U32,
  +hmax: U32,
  +ns: U32,
  +ri: U32
) -> Adv:
  match more:
    case True{}:
      Adv{Ctrl{comp, (bi + 1 : U32), mx, my, mcu, rst}, 0, rst}
    case False{}:
      decode.adv.comp(U32.is_lt((comp + 1 : U32), ns), comp, mx, my, mcu, rst, ww, hmax, ri)

def decode.adv.go(
  +comp: U32,
  +bi: U32,
  +mx: U32,
  +my: U32,
  +mcu: U32,
  +rst: U32,
  +ww: U32,
  +hmax: U32,
  +ns: U32,
  sids: List<&2, U32>,
  ids: List<&2, U32>,
  hs: List<&2, U32>,
  vs: List<&2, U32>,
  +ri: U32
) -> Adv:
  +fi = decode.index(ids, False{}, decode.at(sids, comp), 0)
  +hi = decode.at(hs, fi)
  +vi = decode.at(vs, fi)
  decode.adv.bi(U32.is_lt((bi + 1 : U32), (hi * vi : U32)), comp, bi, mx, my, mcu, rst, ww, hmax, ns, ri)

def decode.adv(ctrl: Ctrl, frame: Frame, scan: Scan, +ri: U32) -> Adv:
  match ctrl:
    case Ctrl{+comp, +bi, +mx, +my, +mcu, +rst}:
      match frame:
        case Frame{+w, _h, _nf, +ids, +hs, +vs, _tq, +hmax, _vmax}:
          match scan:
            case Scan{+ns, +sids, _td, _ta, _ss, _se, _ah}:
              decode.adv.go(comp, bi, mx, my, mcu, rst, w, hmax, ns, sids, ids, hs, vs, ri)

def decode.block.next.go(
  adv: Adv,
  bits: Bits,
  preds: Preds,
  +pred: U32,
  +comp: U32,
  frame: Frame,
  scan: Scan,
  tabs: Tabs
) -> Blk:
  match adv:
    case Adv{ctrl, +due, +expect}:
      match ctrl:
        case Ctrl{+ncomp, _bi, _mx, _my, _mcu, _rst}:
          decode.block.of(decode.restart(bits, due, expect), ncomp, decode.preds.next(due, preds, comp, pred),
            frame, scan, tabs)

def decode.block.next(
  bits: Bits,
  preds: Preds,
  +pred: U32,
  ctrl: Ctrl,
  +frame: Frame,
  +scan: Scan,
  tabs: Tabs,
  +ri: U32
) -> Blk:
  match ctrl:
    case Ctrl{+comp, _bi, _mx, _my, _mcu, _rst}:
      decode.block.next.go(decode.adv(ctrl, frame, scan, ri), bits, preds, pred, comp, frame, scan, tabs)

def decode.geom.nz(+nn: U32) -> U32:
  match nn:
    case 0:
      1
    case _:
      nn

# where block bi of a component sits in its MCU: a component's hi * vi blocks
# run left to right, hi to a row, then top to bottom (T.81 A.2.3), so its
# column is bi mod hi and its row bi div hi
def decode.geom.go(
  +comp: U32,
  +bi: U32,
  +mx: U32,
  +my: U32,
  +ww: U32,
  +hh: U32,
  +hmax: U32,
  +vmax: U32,
  sids: List<&2, U32>,
  ids: List<&2, U32>,
  hs: List<&2, U32>,
  vs: List<&2, U32>
) -> Geom:
  +fi = decode.index(ids, False{}, decode.at(sids, comp), 0)
  +hi = decode.at(hs, fi)
  +vi = decode.at(vs, fi)
  +pw = U32.div(hmax, decode.geom.nz(hi))
  +ph = U32.div(vmax, decode.geom.nz(vi))
  +bx = U32.mod(bi, decode.geom.nz(hi))
  +by = U32.div(bi, decode.geom.nz(hi))
  Geom{(mx * hmax * 8 + bx * 8 * pw : U32), (my * vmax * 8 + by * 8 * ph : U32), pw, ph, ww, hh}

def decode.geom(ctrl: Ctrl, frame: Frame, scan: Scan) -> Geom:
  match ctrl:
    case Ctrl{+comp, +bi, +mx, +my, _mcu, _rst}:
      match frame:
        case Frame{+w, +h, _nf, +ids, +hs, +vs, _tq, +hmax, +vmax}:
          match scan:
            case Scan{_ns, +sids, _td, _ta, _ss, _se, _ah}:
              decode.geom.go(comp, bi, mx, my, w, h, hmax, vmax, sids, ids, hs, vs)

def decode.splat.in(xin: Bool, yin: Bool, plane: Array<U32>, +xx: U32, +yy: U32, +ww: U32, +sample: U32) -> Array<U32>:
  match xin:
    case False{}:
      plane
    case True{}:
      match yin:
        case False{}:
          plane
        case True{}:
          Array.set(U32, plane, (yy * ww + xx : U32), sample)

# one pixel row of the pixels a sample covers: columns x0 + px onward, left pixels left, each written
# only when it lies inside the frame
def decode.splat.px(
  left: Nat,
  plane: Array<U32>,
  +x0: U32,
  +yy: U32,
  +px: U32,
  +ww: U32,
  +hh: U32,
  +vv: U32
) -> Array<U32>:
  match left:
    case 0n:
      plane
    case 1n+p:
      decode.splat.px(p, decode.splat.in(U32.is_lt((x0 + px : U32), ww), U32.is_lt(yy, hh), plane, (x0 + px : U32), yy,
        ww, vv), x0, yy, (px + 1 : U32), ww, hh, vv)

# the pw by ph pixels one sample covers, from (x0, y0 + py), row by row
def decode.splat.py(
  left: Nat,
  plane: Array<U32>,
  +x0: U32,
  +y0: U32,
  +py: U32,
  +pw: U32,
  +ww: U32,
  +hh: U32,
  +vv: U32
) -> Array<U32>:
  match left:
    case 0n:
      plane
    case 1n+p:
      decode.splat.py(p, decode.splat.px(U32.to_nat(pw), plane, x0, (y0 + py : U32), 0, ww, hh, vv), x0, y0,
        (py + 1 : U32), pw, ww, hh, vv)

# the samples xs of one block row from column col on, each over the pw by ph pixels at (ox + col * pw, oy + row * ph):
# xs's first sample at column col, the next at col + 1, 0 for a sample past the end of xs
def decode.splat.col(
  left: Nat,
  plane: Array<U32>,
  +xs: List<&2, U32>,
  +row: U32,
  +col: U32,
  +ox: U32,
  +oy: U32,
  +pw: U32,
  +ph: U32,
  +ww: U32,
  +hh: U32
) -> Array<U32>:
  match left:
    case 0n:
      plane
    case 1n+p:
      decode.splat.col(p, decode.splat.py(U32.to_nat(ph), plane, (ox + col * pw : U32), (oy + row * ph : U32), 0, pw,
        ww, hh, decode.nth(0n, xs)), decode.skip(1n, xs), row, (col + 1 : U32), ox, oy, pw, ph, ww, hh)

# the rows of an 8 by 8 block from row down, xs its samples from that row's first, each sample replicated over pw by
# ph pixels; a block's samples are read once, in order
def decode.splat(
  left: Nat,
  plane: Array<U32>,
  +xs: List<&2, U32>,
  +row: U32,
  +ox: U32,
  +oy: U32,
  +pw: U32,
  +ph: U32,
  +ww: U32,
  +hh: U32
) -> Array<U32>:
  match left:
    case 0n:
      plane
    case 1n+p:
      decode.splat(p, decode.splat.col(8n, plane, xs, row, 0, ox, oy, pw, ph, ww, hh), decode.skip(8n, xs),
        (row + 1 : U32), ox, oy, pw, ph, ww, hh)

def decode.paint.which(
  which: Bool,
  samples: List<&2, U32>,
  plane: Array<U32>,
  +ox: U32,
  +oy: U32,
  +pw: U32,
  +ph: U32,
  +ww: U32,
  +hh: U32
) -> Array<U32>:
  match which:
    case False{}:
      +_s = samples
      plane
    case True{}:
      decode.splat(8n, plane, samples, 0, ox, oy, pw, ph, ww, hh)

def decode.paint.use(gg: Geom, which: Bool, samples: List<&2, U32>, plane: Array<U32>) -> Array<U32>:
  match gg:
    case Geom{+ox, +oy, +pw, +ph, +w, +h}:
      decode.paint.which(which, samples, plane, ox, oy, pw, ph, w, h)

def decode.ctrl.comp(ctrl: Ctrl) -> U32:
  match ctrl:
    case Ctrl{+comp, _bi, _mx, _my, _mcu, _rst}:
      comp

def decode.sink.leaf(aa: Array<U32>) -> U32:
  match aa:
    case ALeaf{_x}:
      0
    case ANode{xs, ys}:
      U32.or(decode.sink.leaf(xs), decode.sink.leaf(ys))

def decode.sink.p(pp: Array<U32> & U32) -> U32:
  (a, v) = pp
  U32.or(v, U32.and(decode.sink.leaf(a), 0))

def decode.sink(aa: Array<U32>) -> U32:
  decode.sink.p(Array.get(U32, aa, 0))

# the depth of a plane of nn points: 0 for none, else log2(2 * nn - 1) in U32, so 2^depth >= nn while
# 2 * nn does not wrap
def decode.depth.of(zero: Bool, +nn: U32) -> Nat:
  match zero:
    case True{}:
      0n
    case False{}:
      U32.log2((U32.shl(nn) - 1 : U32))

# U32.is_eq, not a literal pattern, so a law reaches every nn
def decode.depth(+nn: U32) -> Nat:
  decode.depth.of(U32.is_eq(nn, 0), nn)

def decode.plane(+nn: U32) -> Array<U32>:
  Array.new(U32, decode.depth(nn), 0)

# the plane's points in order: got is the plane and the value of point ii - 1, just read, then the
# left - 1 points from ii on. One read past the last point is made and dropped.
def decode.emit(left: Nat, got: Array<U32> & U32, +ii: U32) -> List<&2, U32>:
  match left:
    case 0n:
      (a, +v) = got
      +_a = decode.sink(a)
      +_v = (v - v : U32)
      +_i = (ii - ii : U32)
      []
    case 1n+p:
      (a, v) = got
      v <> decode.emit(p, Array.get(U32, a, ii), (ii + 1 : U32))

# the first nn points of a plane, in order
def decode.points(+nn: Nat, plane: Array<U32>) -> List<&2, U32>:
  decode.emit(nn, Array.get(U32, plane, 0), 1)

# ---- upsampling (libjpeg's jdsample.c) ----

# the upsampling each component gets, as libjpeg-turbo's jinit_upsampler picks it: 1 the triangle filter across
# (h2v1_fancy_upsample) for a component of half the frame's horizontal factor and its vertical one, 2 across and
# down (h2v2_fancy_upsample) for half of both, 3 down (h1v2_fancy_upsample) for the horizontal factor and half the
# vertical one, and 0, each sample repeated over the pixels it covers as decode.paint paints it, for any other
# factors (int_upsample) and for a component of half the horizontal factor at most 2 samples wide, a frame at most
# 4 pixels wide (h2v1_upsample, h2v2_upsample)
def decode.up.mode(+hc: U32, +vc: U32, +hmax: U32, +vmax: U32, +ww: U32) -> U32:
  +h1 = U32.is_eq(hmax, hc)
  +h2 = U32.is_eq(hmax, (hc * 2 : U32))
  +v1 = U32.is_eq(vmax, vc)
  +v2 = U32.is_eq(vmax, (vc * 2 : U32))
  +wide = U32.is_gt(ww, 4)
  Bool.pick(U32, Bool.and(h2, v1), Bool.pick(U32, wide, 1, 0), Bool.pick(U32, Bool.and(h1, v2), 3,
    Bool.pick(U32, Bool.and(h2, v2), Bool.pick(U32, wide, 2, 0), 0)))

# the three components' upsampling
type Ups is Data:
  Ups{m0: U32, m1: U32, m2: U32}

def decode.ups(+hs: List<&2, U32>, +vs: List<&2, U32>, +hmax: U32, +vmax: U32, +ww: U32) -> Ups:
  Ups{decode.up.mode(decode.at(hs, 0), decode.at(vs, 0), hmax, vmax, ww), decode.up.mode(decode.at(hs, 1),
    decode.at(vs, 1), hmax, vmax, ww), decode.up.mode(decode.at(hs, 2), decode.at(vs, 2), hmax, vmax, ww)}

# the pixel, along one axis of nn pixels, that holds the farther sample the filter mixes into pixel xx of a plane
# painted two pixels to a sample: the pixel before an even one, the pixel after an odd one, and xx itself past an
# edge, where libjpeg repeats the edge sample
def decode.up.far(+xx: U32, +nn: U32) -> U32:
  Bool.pick(U32, U32.is_eq(U32.and(xx, 1), 0), Bool.pick(U32, U32.is_eq(xx, 0), xx, (xx - 1 : U32)),
    Bool.pick(U32, U32.is_lt((xx + 1 : U32), nn), (xx + 1 : U32), xx))

# the triangle filter's value at pixel (xx, yy) from the nearer sample v0, the farther one across vh, the farther
# one down vv and the one across and down vd: 3/4 nearer and 1/4 farther along each axis it filters, rounded as
# jdsample.c rounds (a bias of 1 then 2 for the two pixels of a sample across, 1 then 2 down, 8 then 7 across
# after filtering down)
def decode.up.mix(+mode: U32, +xx: U32, +yy: U32, +v0: U32, +vh: U32, +vv: U32, +vd: U32) -> U32:
  +ex = U32.is_eq(U32.and(xx, 1), 0)
  +ey = U32.is_eq(U32.and(yy, 1), 0)
  Bool.pick(U32, U32.is_eq(mode, 1), U32.shrn((v0 * 3 + vh + Bool.pick(U32, ex, 1, 2) : U32), 2n),
    Bool.pick(U32, U32.is_eq(mode, 3), U32.shrn((v0 * 3 + vv + Bool.pick(U32, ey, 1, 2) : U32), 2n),
    U32.shrn(((v0 * 3 + vv : U32) * 3 + (vh * 3 + vd : U32) + Bool.pick(U32, ex, 8, 7) : U32), 4n)))

# pixel (xx, yy) of a plane upsampled by a filter mode, from the plane as painted: four reads, the plane handed on
def decode.up.cell.d(
  got: Array<U32> & U32,
  +mode: U32,
  +xx: U32,
  +yy: U32,
  +v0: U32,
  +vh: U32,
  +vv: U32
) -> Array<U32> & U32:
  (a, vd) = got
  (a, decode.up.mix(mode, xx, yy, v0, vh, vv, vd))

def decode.up.cell.c(
  got: Array<U32> & U32,
  +mode: U32,
  +xx: U32,
  +yy: U32,
  +xf: U32,
  +yf: U32,
  +ww: U32,
  +v0: U32,
  +vh: U32
) -> Array<U32> & U32:
  (a, vv) = got
  decode.up.cell.d(Array.get(U32, a, (yf * ww + xf : U32)), mode, xx, yy, v0, vh, vv)

def decode.up.cell.b(
  got: Array<U32> & U32,
  +mode: U32,
  +xx: U32,
  +yy: U32,
  +xf: U32,
  +yf: U32,
  +ww: U32,
  +v0: U32
) -> Array<U32> & U32:
  (a, vh) = got
  decode.up.cell.c(Array.get(U32, a, (yf * ww + xx : U32)), mode, xx, yy, xf, yf, ww, v0, vh)

def decode.up.cell.a(
  got: Array<U32> & U32,
  +mode: U32,
  +xx: U32,
  +yy: U32,
  +xf: U32,
  +yf: U32,
  +ww: U32
) -> Array<U32> & U32:
  (a, v0) = got
  decode.up.cell.b(Array.get(U32, a, (yy * ww + xf : U32)), mode, xx, yy, xf, yf, ww, v0)

def decode.up.cell(+mode: U32, +xx: U32, +yy: U32, +ww: U32, +hh: U32, plane: Array<U32>) -> Array<U32> & U32:
  decode.up.cell.a(Array.get(U32, plane, (yy * ww + xx : U32)), mode, xx, yy, decode.up.far(xx, ww),
    decode.up.far(yy, hh), ww)

# the pixels from (xx, yy) on: lx more of row yy after it, then ly more rows of 1 + wn pixels. got holds the plane
# and pixel (xx, yy), just read.
def decode.up.walk(
  ly: Nat,
  lx: Nat,
  got: Array<U32> & U32,
  +xx: U32,
  +yy: U32,
  +mode: U32,
  +ww: U32,
  +hh: U32,
  +wn: Nat
) -> List<&2, U32>:
  match ly:
    case 0n:
      match lx:
        case 0n:
          (a, v) = got
          +_a = decode.sink(a)
          [v]
        case 1n+p:
          (a, v) = got
          v <> decode.up.walk(0n, p, decode.up.cell(mode, (xx + 1 : U32), yy, ww, hh, a), (xx + 1 : U32), yy, mode,
            ww, hh, wn)
    case 1n+q:
      match lx:
        case 0n:
          (a, v) = got
          v <> decode.up.walk(q, wn, decode.up.cell(mode, 0, (yy + 1 : U32), ww, hh, a), 0, (yy + 1 : U32), mode,
            ww, hh, wn)
        case 1n+p:
          (a, v) = got
          v <> decode.up.walk(1n+q, p, decode.up.cell(mode, (xx + 1 : U32), yy, ww, hh, a), (xx + 1 : U32), yy,
            mode, ww, hh, wn)

# a plane's rows of ww pixels, hn of them, filtered
def decode.up.rows(hn: Nat, wn: Nat, +mode: U32, +ww: U32, +hh: U32, plane: Array<U32>) -> List<&2, U32>:
  match hn:
    case 0n:
      +_w = wn
      +_a = decode.sink(plane)
      []
    case 1n+q:
      match wn:
        case 0n:
          +_a = decode.sink(plane)
          []
        case 1n+(+p):
          decode.up.walk(q, p, decode.up.cell(mode, 0, 0, ww, hh, plane), 0, 0, mode, ww, hh, p)

# a plane's nn = ww * hh points in order, upsampled by mode: as painted for mode 0, else filtered
def decode.up.out.z(zero: Bool, +mode: U32, +nn: Nat, +ww: U32, +hh: U32, plane: Array<U32>) -> List<&2, U32>:
  match zero:
    case True{}:
      decode.points(nn, plane)
    case False{}:
      decode.up.rows(U32.to_nat(hh), U32.to_nat(ww), mode, ww, hh, plane)

def decode.up.out(+mode: U32, +nn: Nat, +ww: U32, +hh: U32, plane: Array<U32>) -> List<&2, U32>:
  decode.up.out.z(U32.is_eq(mode, 0), mode, nn, ww, hh, plane)

# a sample's colour bits made opaque: alpha 255 over the low 24 bits. The
# constant is the first operand, so a law over any sample sees its alpha
# without a case split on the sample's bits.
def opaque(+xx: U32) -> U32:
  U32.or(4278190080, xx)

# a channel clamped from above: 255 for a quotient past it
def rgb.ch.hi(+qq: U32) -> U32:
  decode.clamp.hi(U32.is_gt(qq, 255), qq)

# a channel whose value, plus one half, is below zero is 0; otherwise the
# whole millions in pos - neg
def rgb.ch.lt(lt: Bool, +pos: U32, +neg: U32) -> U32:
  match lt:
    case True{}:
      0
    case False{}:
      rgb.ch.hi(U32.div((pos - neg : U32), 1000000))

# one channel of T.871 rounded to nearest and clamped to 0..255, from its
# value in millionths split into what is added (pos, with the half for
# rounding already in) and what is subtracted (neg). For inputs 0..255 both
# stay below 2^32, so the arithmetic is exact: no fixed-point constant and one
# rounding per channel.
def rgb.ch(+pos: U32, +neg: U32) -> U32:
  rgb.ch.lt(U32.is_lt(pos, neg), pos, neg)

# YCbCr to colour bits, (R << 16) | (G << 8) | B, per JFIF T.871 exactly:
# R = Y + 1.402 (Cr - 128), G = Y - 0.344136 (Cb - 128) - 0.714136 (Cr - 128),
# B = Y + 1.772 (Cb - 128), each rounded to nearest and clamped. The 128
# offsets are the constants 179456000 = 128 * 1402000, 135458816 =
# 128 * (344136 + 714136) and 226816000 = 128 * 1772000.
def rgb.bits(+yy: U32, +cb: U32, +cr: U32) -> U32:
  +r = rgb.ch((yy * 1000000 + cr * 1402000 + 500000 : U32), 179456000)
  +g = rgb.ch((yy * 1000000 + 135458816 + 500000 : U32), (cb * 344136 + cr * 714136 : U32))
  +b = rgb.ch((yy * 1000000 + cb * 1772000 + 500000 : U32), 226816000)
  U32.or(U32.or(U32.shln(r, 16n), U32.shln(g, 8n)), b)

# YCbCr to a packed opaque sample, 0xFFRRGGBB
#
# Trusted, not proved: rgb is the T.871 YCbCr to RGB conversion, rounded to
# nearest and clamped to 0 to 255, for every y, cb and cr from 0 to 255.
# Checked outside the gate: a Python copy of rgb.bits's U32 arithmetic,
# compared with T.871 computed in exact rationals over all 2^24 inputs,
# differs on none. A proof in the gate needs U32 division and products near
# 10^9, which the Nat lemmas reach only through unary numerals the checker
# cannot hold in memory.
def rgb(+yy: U32, +cb: U32, +cr: U32) -> U32:
  opaque(rgb.bits(yy, cb, cr))

# a gray level's low byte in R, G and B
def gray.bits(+yy: U32) -> U32:
  +vv = U32.and(255, yy)
  U32.or(U32.shln(vv, 16n), U32.or(U32.shln(vv, 8n), vv))

# a gray level as a packed opaque sample, 0xFFvvvvvv
def gray(+yy: U32) -> U32:
  opaque(gray.bits(yy))

# every gray level of a picture as a packed opaque sample
def decode.grays(ys: List<&2, U32>) -> List<&2, U32>:
  match ys:
    case Nil{}:
      Nil{}
    case yv <> rest:
      gray(yv) <> decode.grays(rest)

# an R, G and B sample coded as they are (no colour transform) as a packed opaque sample, each channel's low byte
def direct(+rr: U32, +gg: U32, +bb: U32) -> U32:
  opaque(U32.or(U32.or(U32.shln(U32.and(255, rr), 16n), U32.shln(U32.and(255, gg), 8n)), U32.and(255, bb)))

# every R, G, B triple of a picture coded without a colour transform, as many as the shortest list holds
def decode.directs(rs: List<&2, U32>, gs: List<&2, U32>, bs: List<&2, U32>) -> List<&2, U32>:
  match rs:
    case Nil{}:
      +_g = decode.drop(gs)
      +_b = decode.drop(bs)
      Nil{}
    case rv <> rt:
      match gs:
        case Nil{}:
          +_r = decode.drop(rv <> rt)
          +_b = decode.drop(bs)
          Nil{}
        case gv <> gt:
          match bs:
            case Nil{}:
              +_r = decode.drop(rv <> rt)
              +_g = decode.drop(gv <> gt)
              Nil{}
            case bv <> bt:
              direct(rv, gv, bv) <> decode.directs(rt, gt, bt)

# every Y, Cb, Cr triple of a picture as a packed opaque sample, as many as the shortest list holds
def decode.rgbs(ys: List<&2, U32>, bs: List<&2, U32>, rs: List<&2, U32>) -> List<&2, U32>:
  match ys:
    case Nil{}:
      +_b = decode.drop(bs)
      +_r = decode.drop(rs)
      Nil{}
    case yv <> yt:
      match bs:
        case Nil{}:
          +_y = decode.drop(yv <> yt)
          +_r = decode.drop(rs)
          Nil{}
        case bv <> bt:
          match rs:
            case Nil{}:
              +_y = decode.drop(yv <> yt)
              +_b = decode.drop(bv <> bt)
              Nil{}
            case rv <> rt:
              rgb(yv, bv, rv) <> decode.rgbs(yt, bt, rt)

def decode.done.drop(yy: Array<U32>, cb: Array<U32>, cr: Array<U32>) -> Maybe<&2, Pic>:
  +_a = decode.sink(yy)
  +_b = decode.sink(cb)
  +_c = decode.sink(cr)
  None{}

def decode.done.gray(+ww: U32, +hh: U32, +ups: Ups, yy: Array<U32>, cb: Array<U32>, cr: Array<U32>) -> Maybe<&2, Pic>:
  match ups:
    case Ups{+m0, _m1, _m2}:
      +_b = decode.sink(cb)
      +_c = decode.sink(cr)
      Some{Pic{ww, hh, decode.grays(decode.up.out(m0, U32.to_nat((ww * hh : U32)), ww, hh, yy))}}

# the samples of three components read out in order, each upsampled as libjpeg upsamples it: R, G and B as coded
# when rgb is set, else Y, Cb and Cr converted per T.871
def decode.done.pack(
  rgb: Bool,
  +nn: Nat,
  +ww: U32,
  +hh: U32,
  ups: Ups,
  yy: Array<U32>,
  cb: Array<U32>,
  cr: Array<U32>
) -> List<&2, U32>:
  match rgb:
    case True{}:
      match ups:
        case Ups{+m0, +m1, +m2}:
          decode.directs(decode.up.out(m0, nn, ww, hh, yy), decode.up.out(m1, nn, ww, hh, cb), decode.up.out(m2, nn,
            ww, hh, cr))
    case False{}:
      match ups:
        case Ups{+m0, +m1, +m2}:
          decode.rgbs(decode.up.out(m0, nn, ww, hh, yy), decode.up.out(m1, nn, ww, hh, cb), decode.up.out(m2, nn, ww,
            hh, cr))

# a colour picture: each point's three samples read out in order, then packed
def decode.done.color(
  rgb: Bool,
  +ww: U32,
  +hh: U32,
  ups: Ups,
  yy: Array<U32>,
  cb: Array<U32>,
  cr: Array<U32>
) -> Maybe<&2, Pic>:
  Some{Pic{ww, hh, decode.done.pack(rgb, U32.to_nat((ww * hh : U32)), ww, hh, ups, yy, cb, cr)}}

# three components are colour; any other count is none
def decode.done.nf3(
  three: Bool,
  rgb: Bool,
  +ww: U32,
  +hh: U32,
  ups: Ups,
  yy: Array<U32>,
  cb: Array<U32>,
  cr: Array<U32>
) -> Maybe<&2, Pic>:
  match three:
    case True{}:
      decode.done.color(rgb, ww, hh, ups, yy, cb, cr)
    case False{}:
      +_r = rgb
      +_u = ups
      decode.done.drop(yy, cb, cr)

# one component is gray; the rest is decided by decode.done.nf3
def decode.done.nf1(
  one: Bool,
  +nf: U32,
  rgb: Bool,
  +ww: U32,
  +hh: U32,
  ups: Ups,
  yy: Array<U32>,
  cb: Array<U32>,
  cr: Array<U32>
) -> Maybe<&2, Pic>:
  match one:
    case True{}:
      +_r = rgb
      decode.done.gray(ww, hh, ups, yy, cb, cr)
    case False{}:
      decode.done.nf3(U32.is_eq(nf, 3), rgb, ww, hh, ups, yy, cb, cr)

# the picture by its component count. U32.is_eq, not a literal pattern, so a law reaches every count.
def decode.done.nf(
  +nf: U32,
  rgb: Bool,
  +ww: U32,
  +hh: U32,
  ups: Ups,
  yy: Array<U32>,
  cb: Array<U32>,
  cr: Array<U32>
) -> Maybe<&2, Pic>:
  decode.done.nf1(U32.is_eq(nf, 1), nf, rgb, ww, hh, ups, yy, cb, cr)

# a failed scan is none; otherwise the picture by the frame's component count
def decode.done.ok(
  bad: Bool,
  frame: Frame,
  rgb: Bool,
  yy: Array<U32>,
  cb: Array<U32>,
  cr: Array<U32>
) -> Maybe<&2, Pic>:
  match bad:
    case True{}:
      +_r = rgb
      decode.done.drop(yy, cb, cr)
    case False{}:
      match frame:
        case Frame{+w, +h, +nf, _ids, +hs, +vs, _tq, +hmax, +vmax}:
          decode.done.nf(nf, rgb, w, h, decode.ups(hs, vs, hmax, vmax, w), yy, cb, cr)

# the planes as a picture, or none when ok is 0. rgb says three components are R, G and B as coded, not YCbCr.
def decode.done(+ok: U32, frame: Frame, rgb: Bool, yy: Array<U32>, cb: Array<U32>, cr: Array<U32>) -> Maybe<&2, Pic>:
  decode.done.ok(U32.is_eq(ok, 0), frame, rgb, yy, cb, cr)

def decode.adv.ctrl(adv: Adv) -> Ctrl:
  match adv:
    case Adv{ctrl, _due, _expect}:
      ctrl

def decode.adv.duef(adv: Adv) -> U32:
  match adv:
    case Adv{_ctrl, +due, _expect}:
      due

# a block that decoded: its ok flag is not 0 (its reader stayed inside the data and every code was in its table)
def decode.blk.live(blk: Blk) -> Bool:
  match blk:
    case Blk{_samples, _bits, _pred, +ok}:
      Bool.not(U32.is_eq(ok, 0))

# the block run from blk, left more after it, live saying blk decoded. A block that failed stops the run, none,
# before another block is read; otherwise each block is painted onto its component's plane
def decode.blocks(
  left: Nat,
  live: Bool,
  blk: Blk,
  +ctrl: Ctrl,
  +preds: Preds,
  +frame: Frame,
  +scan: Scan,
  +tabs: Tabs,
  +ri: U32,
  +rgb: Bool,
  yy: Array<U32>,
  cb: Array<U32>,
  cr: Array<U32>,
  +ok: U32
) -> Maybe<&2, Pic>:
  match left:
    case 0n:
      match live:
        case _live:
          match blk:
            case Blk{+samples, _bits, _pred, +bok}:
              +gg = decode.geom(ctrl, frame, scan)
              +cc = decode.ctrl.comp(ctrl)
              decode.done((ok * bok : U32), frame, rgb, decode.paint.use(gg, U32.is_eq(cc, 0), samples, yy),
                decode.paint.use(gg, U32.is_eq(cc, 1), samples, cb), decode.paint.use(gg, U32.is_eq(cc, 2), samples,
                cr))
    case 1n+p:
      match live:
        case False{}:
          +_b = blk
          decode.done(0, frame, rgb, yy, cb, cr)
        case True{}:
          match blk:
            case Blk{+samples, +bits, +pred, +bok}:
              match ctrl:
                case Ctrl{+comp, _bi, _mx, _my, _mcu, _rst}:
                  +av = decode.adv(ctrl, frame, scan, ri)
                  +gg = decode.geom(ctrl, frame, scan)
                  +nx = decode.block.next(bits, preds, pred, ctrl, frame, scan, tabs, ri)
                  decode.blocks(p, decode.blk.live(nx), nx, decode.adv.ctrl(av), decode.preds.next(decode.adv.duef(av),
                    preds, comp, pred), frame, scan, tabs, ri, rgb, decode.paint.use(gg, U32.is_eq(comp, 0), samples,
                    yy), decode.paint.use(gg, U32.is_eq(comp, 1), samples, cb), decode.paint.use(gg, U32.is_eq(comp, 2),
                    samples, cr), (ok * bok : U32))

def decode.blocks.sum(hs: List<&2, U32>, vs: List<&2, U32>, +nn: U32) -> U32:
  match hs:
    case Nil{}:
      match vs:
        case _vs:
          nn
    case h <> ht:
      match vs:
        case Nil{}:
          nn
        case v <> vt:
          decode.blocks.sum(ht, vt, (nn + h * v : U32))

def decode.start(
  nn: Nat,
  bits: Bits,
  +frame: Frame,
  +scan: Scan,
  +tabs: Tabs,
  +ri: U32,
  +rgb: Bool,
  yy: Array<U32>,
  cb: Array<U32>,
  cr: Array<U32>
) -> Maybe<&2, Pic>:
  match nn:
    case 0n:
      +_r = rgb
      decode.done.drop(yy, cb, cr)
    case 1n+p:
      +b0 = decode.block.of(bits, 0, decode.pred.zero(), frame, scan, tabs)
      decode.blocks(p, decode.blk.live(b0), b0, Ctrl{0, 0, 0, 0, 0, 0}, decode.pred.zero(), frame, scan, tabs, ri, rgb,
        yy, cb, cr, 1)

# the blocks a scan of the frame holds: ceil(w / 8 hmax) * ceil(h / 8 vmax) MCUs, each with the frame's
# components' hi * vi data units
def decode.nblocks(
  +ww: U32,
  +hh: U32,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>,
  +hmax: U32,
  +vmax: U32
) -> U32:
  (decode.ceil(ww, (hmax * 8 : U32)) * decode.ceil(hh, (vmax * 8 : U32)) * decode.blocks.sum(hs, vs, 0) : U32)

# a frame of at most 2^31 points, each side at most 65535 (so the U32 product is exact): a larger frame would alias
# in the planes, whose indexes are U32
def decode.area.ok(+ww: U32, +hh: U32) -> Bool:
  Bool.and(Bool.and(U32.is_le(ww, 65535), U32.is_le(hh, 65535)), U32.is_le((ww * hh : U32), 2147483648))

# two bits for each of nn blocks: every block takes at least two, one for its DC code and one for its AC codes
def decode.need.bits(nn: Nat) -> Nat:
  match nn:
    case 0n:
      0n
    case 1n+p:
      1n+1n+decode.need.bits(p)

# the bits entropy-coded bytes hold, eight to a byte
def decode.ent.bits(ent: List<&2, U32>) -> Nat:
  match ent:
    case Nil{}:
      0n
    case _b <> rest:
      Nat.add(8n, decode.ent.bits(rest))

# the scan's component ids are the frame's, in the frame's order, ok saying the ids before matched
def decode.ids.same(xs: List<&2, U32>, ys: List<&2, U32>, +ok: Bool) -> Bool:
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          ok
        case +yy <> yt:
          +_d = decode.drop(yt)
          +_y = (yy - yy : U32)
          False{}
    case +xx <> xt:
      match ys:
        case Nil{}:
          +_d = decode.drop(xt)
          +_x = (xx - xx : U32)
          False{}
        case +yy <> yt:
          decode.ids.same(xt, yt, Bool.and(ok, U32.is_eq(xx, yy)))

# a scan holding every frame component, in the frame's order (T.81 B.2.3), so a block's scan position is its
# frame component: its plane and its quantisation table
def decode.scan.match(+ns: U32, +nf: U32, sids: List<&2, U32>, ids: List<&2, U32>) -> Bool:
  Bool.and(U32.is_eq(ns, nf), decode.ids.same(sids, ids, True{}))

# a scan the decoder runs: the frame's at most 2^31 points, entropy-coded bytes enough for its blocks (two bits a
# block, so a short file cannot ask for planes far larger than itself), and every frame component in the scan, in
# the frame's order
def decode.fits(
  +ww: U32,
  +hh: U32,
  +nb: U32,
  ent: List<&2, U32>,
  +nf: U32,
  ids: List<&2, U32>,
  scan: Scan
) -> Bool:
  match scan:
    case Scan{+ns, sids, _td, _ta, _ss, _se, _ah}:
      Bool.and(decode.area.ok(ww, hh), Bool.and(Nat.is_le(decode.need.bits(U32.to_nat(nb)), decode.ent.bits(ent)),
        decode.scan.match(ns, nf, sids, ids)))

def decode.run.fit(
  fit: Bool,
  +nb: U32,
  +ww: U32,
  +hh: U32,
  frame: Frame,
  scan: Scan,
  tabs: Tabs,
  ent: List<&2, U32>,
  +ri: U32,
  +rgb: Bool
) -> Maybe<&2, Pic>:
  match fit:
    case False{}:
      None{}
    case True{}:
      decode.start(U32.to_nat(nb), Bits{0, 1, 0, ent}, frame, scan, tabs, ri, rgb, decode.plane((ww * hh : U32)),
        decode.plane((ww * hh : U32)), decode.plane((ww * hh : U32)))

def decode.run.n(
  empty: Bool,
  +ww: U32,
  +hh: U32,
  frame: Frame,
  +scan: Scan,
  tabs: Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +rgb: Bool
) -> Maybe<&2, Pic>:
  match empty:
    case True{}:
      None{}
    case False{}:
      match frame:
        case Frame{+w, +h, +nf, +ids, +hs, +vs, +tq, +hmax, +vmax}:
          +nb = decode.nblocks(ww, hh, hs, vs, hmax, vmax)
          decode.run.fit(decode.fits(ww, hh, nb, ent, nf, ids, scan), nb, ww, hh, {Frame{w, h, nf, ids, hs, vs, tq,
            hmax,
            vmax} : Frame}, scan, tabs, ent, ri, rgb)

# the scan decode of a frame. rgb says three components are R, G and B as coded, not YCbCr.
def decode.run(frame: Frame, scan: Scan, tabs: Tabs, ent: List<&2, U32>, +ri: U32, +rgb: Bool) -> Maybe<&2, Pic>:
  match frame:
    case Frame{+w, +h, _nf, _ids, _hs, _vs, _tq, _hmax, _vmax}:
      decode.run.n(Bool.or(U32.is_eq(w, 0), U32.is_eq(h, 0)), w, h, frame, scan, tabs, ent, ri, rgb)

# ---- files of several scans (T.81 B.2.3, E.2) ----
# A sequential frame may code its components over several scans, each holding one component (non-interleaved, A.2.2)
# or several (interleaved, A.2.3), with tables and a restart interval redefined between them (B.2.4). The walk keeps
# each scan with the tables in force when it was read (decode.chain); the passes below decode them in file order
# onto the frame's planes. Every frame component is in exactly one scan, and a scan's components are in the frame's
# order (B.2.3); anything else is refused.

# a scan read: its header, the tables and restart interval it was read with, and its entropy-coded bytes in file order
type Pass is Data:
  Pass{scan: Scan, tabs: Tabs, ent: List<&2, U32>, ri: U32}

# the bit of frame component ii in a mask of components (a frame has at most 3)
def decode.bit(+ii: U32) -> U32:
  match ii:
    case 0:
      1
    case 1:
      2
    case 2:
      4
    case 3:
      8
    case _:
      0

# the position of want in xs, 255 when it is absent. eq says the element before xs was want, and ii counts the
# elements before it (as decode.index, which gives 0 for an absent want)
def decode.pos(xs: List<&2, U32>, eq: Bool, +want: U32, +ii: U32) -> U32:
  match xs:
    case Nil{}:
      match eq:
        case True{}:
          ii
        case False{}:
          255
    case +n <> t:
      match eq:
        case True{}:
          +_d = decode.drop(n <> t)
          ii
        case False{}:
          decode.pos(t, U32.is_eq(n, want), want, decode.index.add(U32.is_eq(n, want), ii))

# the frame position of each scan component
def decode.ix(sids: List<&2, U32>, +ids: List<&2, U32>) -> List<&2, U32>:
  match sids:
    case Nil{}:
      []
    case +sid <> rest:
      decode.pos(ids, False{}, sid, 0) <> decode.ix(rest, ids)

# the components of a scan as a mask over the frame's, 0 when one is not in the frame or they are not in the frame's
# order, each after the one before (B.2.3); lo is the least position the next may have
def decode.ix.mask(ix: List<&2, U32>, ok: Bool, +lo: U32, +nf: U32, +acc: U32) -> U32:
  match ix:
    case Nil{}:
      match ok:
        case True{}:
          acc
        case False{}:
          0
    case +ii <> rest:
      decode.ix.mask(rest, Bool.and(ok, Bool.and(U32.is_ge(ii, lo), U32.is_lt(ii, nf))), (ii + 1 : U32), nf,
        U32.or(acc, decode.bit(ii)))

# the data units in one MCU of an interleaved scan: hi * vi for each of its components (A.2.3)
def decode.units(ix: List<&2, U32>, +hs: List<&2, U32>, +vs: List<&2, U32>, +acc: U32) -> U32:
  match ix:
    case Nil{}:
      acc
    case +ii <> rest:
      decode.units(rest, hs, vs, (acc + decode.at(hs, ii) * decode.at(vs, ii) : U32))

# the frame a scan is decoded over. An interleaved scan keeps the frame: its MCUs hold each of its components' hi * vi
# blocks (A.2.3). A scan of one component has one block to an MCU, in raster order over that component's blocks
# (A.2.2): the frame of that component alone, sampled 1 by 1, with hmax / hi by vmax / vi pixels to a sample.
def decode.pass.frame(
  one: Bool,
  +ww: U32,
  +hh: U32,
  +nf: U32,
  +ids: List<&2, U32>,
  hs: List<&2, U32>,
  vs: List<&2, U32>,
  tq: List<&2, U32>,
  +hmax: U32,
  +vmax: U32,
  +sid: U32,
  +fi: U32
) -> Frame:
  match one:
    case False{}:
      +_s = (sid - sid : U32)
      Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}
    case True{}:
      +_d = decode.drop(ids)
      +_n = (nf - nf : U32)
      Frame{ww, hh, 1, [sid], [1], [1], [decode.at(tq, fi)], U32.div(hmax, decode.geom.nz(decode.at(hs, fi))),
        U32.div(vmax, decode.geom.nz(decode.at(vs, fi)))}

# the units in an MCU of a scan: one for a scan of one component, else its components' hi * vi
def decode.pass.units(one: Bool, +ix: List<&2, U32>, +hs: List<&2, U32>, +vs: List<&2, U32>) -> U32:
  match one:
    case True{}:
      1
    case False{}:
      decode.units(ix, hs, vs, 0)

# the blocks of a scan: ceil(w / 8 hmax) * ceil(h / 8 vmax) MCUs over the frame it is decoded over, units to an MCU
def decode.pass.nb(frame: Frame, +units: U32) -> U32:
  match frame:
    case Frame{+w, +h, _nf, _ids, _hs, _vs, _tq, +hmax, +vmax}:
      (decode.ceil(w, (hmax * 8 : U32)) * decode.ceil(h, (vmax * 8 : U32)) * units : U32)

# how a scan is decoded over a frame: the frame position of each of its components, those components as a mask (0
# when the scan is not one decode.passes.ok takes), the frame it is decoded over, and its blocks
type Plan is Data:
  Plan{ix: List<&2, U32>, mask: U32, frame: Frame, nb: U32}

def decode.frame.ids(frame: Frame) -> List<&2, U32>:
  match frame:
    case Frame{_w, _h, _nf, +ids, _hs, _vs, _tq, _hmax, _vmax}:
      ids

def decode.plan.go(+ns: U32, sids: List<&2, U32>, +ix: List<&2, U32>, frame: Frame) -> Plan:
  match frame:
    case Frame{+w, +h, +nf, +ids, +hs, +vs, +tq, +hmax, +vmax}:
      +one = U32.is_eq(ns, 1)
      +pf = decode.pass.frame(one, w, h, nf, ids, hs, vs, tq, hmax, vmax, decode.at(sids, 0), decode.at(ix, 0))
      Plan{ix, decode.ix.mask(ix, True{}, 0, nf, 0), pf, decode.pass.nb(pf, decode.pass.units(one, ix, hs, vs))}

def decode.plan(scan: Scan, +frame: Frame) -> Plan:
  match scan:
    case Scan{+ns, +sids, _td, _ta, _ss, _se, _ah}:
      decode.plan.go(ns, sids, decode.ix(sids, decode.frame.ids(frame)), frame)

def decode.plan.mask(pl: Plan) -> U32:
  match pl:
    case Plan{_ix, +mask, _frame, _nb}:
      mask

def decode.plan.nb(pl: Plan) -> U32:
  match pl:
    case Plan{_ix, _mask, _frame, +nb}:
      nb

def decode.plan.ix(pl: Plan) -> List<&2, U32>:
  match pl:
    case Plan{+ix, _mask, _frame, _nb}:
      ix

def decode.plan.frame(pl: Plan) -> Frame:
  match pl:
    case Plan{_ix, _mask, +frame, _nb}:
      frame

def decode.frame.nf(frame: Frame) -> U32:
  match frame:
    case Frame{_w, _h, +nf, _ids, _hs, _vs, _tq, _hmax, _vmax}:
      nf

# whether every pass has its components in the frame, in the frame's order, none of them in an earlier pass, and
# entropy-coded bytes enough for its blocks (two bits a block, as decode.fits asks of a single scan); and, at the end,
# every frame component in some pass. mask holds the components of the passes before.
def decode.passes.ok(passes: List<&2, Pass>, +frame: Frame, +mask: U32, ok: Bool) -> Bool:
  match passes:
    case Nil{}:
      Bool.and(ok, U32.is_eq(mask, (decode.bit(decode.frame.nf(frame)) - 1 : U32)))
    case Pass{scan, _tabs, ent, _ri} <> rest:
      +pl = decode.plan(scan, frame)
      +bits = decode.plan.mask(pl)
      decode.passes.ok(rest, frame, U32.or(mask, bits), Bool.and(ok, Bool.and(Bool.not(U32.is_eq(bits, 0)),
        Bool.and(U32.is_eq(U32.and(mask, bits), 0), Nat.is_le(decode.need.bits(U32.to_nat(decode.plan.nb(pl))),
        decode.ent.bits(ent))))))

# the block run of a pass, as decode.blocks runs a single scan, painting each block onto the plane of its frame
# component (ix gives the frame position of each scan component). Gives 0 or 1 for whether every block decoded, and
# the planes.
def decode.pass.blocks(
  left: Nat,
  live: Bool,
  blk: Blk,
  +ctrl: Ctrl,
  +preds: Preds,
  +frame: Frame,
  +scan: Scan,
  +tabs: Tabs,
  +ri: U32,
  +ix: List<&2, U32>,
  yy: Array<U32>,
  cb: Array<U32>,
  cr: Array<U32>,
  +ok: U32
) -> U32 & Array<U32> & Array<U32> & Array<U32>:
  match left:
    case 0n:
      match live:
        case _live:
          match blk:
            case Blk{+samples, _bits, _pred, +bok}:
              +gg = decode.geom(ctrl, frame, scan)
              +fi = decode.at(ix, decode.ctrl.comp(ctrl))
              ((ok * bok : U32), decode.paint.use(gg, U32.is_eq(fi, 0), samples, yy), decode.paint.use(gg,
                U32.is_eq(fi, 1), samples, cb), decode.paint.use(gg, U32.is_eq(fi, 2), samples, cr))
    case 1n+p:
      match live:
        case False{}:
          +_b = blk
          (0, yy, cb, cr)
        case True{}:
          match blk:
            case Blk{+samples, +bits, +pred, +bok}:
              match ctrl:
                case Ctrl{+comp, _bi, _mx, _my, _mcu, _rst}:
                  +av = decode.adv(ctrl, frame, scan, ri)
                  +gg = decode.geom(ctrl, frame, scan)
                  +fi = decode.at(ix, comp)
                  +nx = decode.block.next(bits, preds, pred, ctrl, frame, scan, tabs, ri)
                  decode.pass.blocks(p, decode.blk.live(nx), nx, decode.adv.ctrl(av), decode.preds.next(
                    decode.adv.duef(av), preds, comp, pred), frame, scan, tabs, ri, ix, decode.paint.use(gg,
                    U32.is_eq(fi, 0), samples, yy), decode.paint.use(gg, U32.is_eq(fi, 1), samples, cb),
                    decode.paint.use(gg, U32.is_eq(fi, 2), samples, cr), (ok * bok : U32))

# the nn blocks of a pass from its first, predictors and restart count starting afresh (E.2.4, F.2.1.3.1)
def decode.pass.start(
  nn: Nat,
  bits: Bits,
  +frame: Frame,
  +scan: Scan,
  +tabs: Tabs,
  +ri: U32,
  +ix: List<&2, U32>,
  yy: Array<U32>,
  cb: Array<U32>,
  cr: Array<U32>
) -> U32 & Array<U32> & Array<U32> & Array<U32>:
  match nn:
    case 0n:
      (1, yy, cb, cr)
    case 1n+p:
      +b0 = decode.block.of(bits, 0, decode.pred.zero(), frame, scan, tabs)
      decode.pass.blocks(p, decode.blk.live(b0), b0, Ctrl{0, 0, 0, 0, 0, 0}, decode.pred.zero(), frame, scan, tabs, ri,
        ix, yy, cb, cr, 1)

# the planes after one more pass: ok is 0 once a pass has failed, and a failed pass stops the passes after it
def decode.pass.then(
  +ok: U32,
  got: U32 & Array<U32> & Array<U32> & Array<U32>
) -> U32 & Array<U32> & Array<U32> & Array<U32>:
  (bok, yy, cb, cr) = got
  ((ok * bok : U32), yy, cb, cr)

def decode.pass.run(
  live: Bool,
  pass: Pass,
  frame: Frame,
  +ok: U32,
  yy: Array<U32>,
  cb: Array<U32>,
  cr: Array<U32>
) -> U32 & Array<U32> & Array<U32> & Array<U32>:
  match live:
    case False{}:
      +_p = pass
      (0, yy, cb, cr)
    case True{}:
      match pass:
        case Pass{+scan, +tabs, +ent, +ri}:
          +pl = decode.plan(scan, frame)
          decode.pass.then(ok, decode.pass.start(U32.to_nat(decode.plan.nb(pl)), Bits{0, 1, 0, ent},
            decode.plan.frame(pl), scan, tabs, ri, decode.plan.ix(pl), yy, cb, cr))

def decode.pass.ok.at(
  +ok: U32,
  pass: Pass,
  +frame: Frame,
  yy: Array<U32>,
  cb: Array<U32>,
  cr: Array<U32>
) -> U32 & Array<U32> & Array<U32> & Array<U32>:
  decode.pass.run(Bool.not(U32.is_eq(ok, 0)), pass, frame, ok, yy, cb, cr)

# a pass painted onto the planes got holds, with the ok flag before it
def decode.pass.at(
  pass: Pass,
  +frame: Frame,
  got: U32 & Array<U32> & Array<U32> & Array<U32>
) -> U32 & Array<U32> & Array<U32> & Array<U32>:
  (ok, yy, cb, cr) = got
  decode.pass.ok.at(ok, pass, frame, yy, cb, cr)

# the passes painted in file order onto the planes, got holding the ok flag and the planes so far
def decode.passes.go(
  passes: List<&2, Pass>,
  +frame: Frame,
  got: U32 & Array<U32> & Array<U32> & Array<U32>
) -> U32 & Array<U32> & Array<U32> & Array<U32>:
  match passes:
    case Nil{}:
      got
    case pass <> rest:
      decode.passes.go(rest, frame, decode.pass.at(pass, frame, got))

def decode.passes.done(got: U32 & Array<U32> & Array<U32> & Array<U32>, frame: Frame, rgb: Bool) -> Maybe<&2, Pic>:
  (ok, yy, cb, cr) = got
  decode.done(ok, frame, rgb, yy, cb, cr)

def decode.passes.fit(
  fit: Bool,
  +frame: Frame,
  passes: List<&2, Pass>,
  +ww: U32,
  +hh: U32,
  rgb: Bool
) -> Maybe<&2, Pic>:
  match fit:
    case False{}:
      None{}
    case True{}:
      decode.passes.done(decode.passes.go(passes, frame, (1, decode.plane((ww * hh : U32)), decode.plane((ww * hh :
        U32)), decode.plane((ww * hh : U32)))), frame, rgb)

# the picture of a frame coded over the scans passes: none for an empty frame (DNL is not read), one of more than 2^31
# points, or scans decode.passes.ok refuses; else each pass painted in turn. rgb as for decode.run.
def decode.passes(frame: Frame, +passes: List<&2, Pass>, rgb: Bool) -> Maybe<&2, Pic>:
  match frame:
    case Frame{+w, +h, +nf, +ids, +hs, +vs, +tq, +hmax, +vmax}:
      +frame = {Frame{w, h, nf, ids, hs, vs, tq, hmax, vmax} : Frame}
      decode.passes.fit(Bool.and(Bool.not(Bool.or(U32.is_eq(w, 0), U32.is_eq(h, 0))), Bool.and(decode.area.ok(w, h),
        decode.passes.ok(passes, frame, 0, True{}))), frame, passes, w, h, rgb)

# the file opened with SOI (bit 0 of what decode.facts reads)
def decode.facts.soi(+facts: U32) -> Bool:
  U32.is_eq(U32.and(facts, 1), 1)

# component ids 'R', 'G', 'B'
def decode.rgb.ids(ids: List<&2, U32>) -> Bool:
  match ids:
    case 82 <> 71 <> 66 <> Nil{}:
      True{}
    case _:
      False{}

# YCbCr unless a JFIF APP0 is absent and an Adobe APP14's transform flag is 0, or neither marker is there and the
# component ids are 'R', 'G' and 'B'
def decode.rgb.pick(jfif: Bool, adobe: Bool, t0: Bool, ids: List<&2, U32>) -> Bool:
  match jfif:
    case True{}:
      +_a = adobe
      +_t = t0
      +_i = decode.drop(ids)
      False{}
    case False{}:
      match adobe:
        case True{}:
          +_i = decode.drop(ids)
          t0
        case False{}:
          +_t = t0
          decode.rgb.ids(ids)

# three components coded as R, G and B, no colour transform, chosen as libjpeg-turbo chooses (jdapimin.c,
# default_decompress_parms): a JFIF APP0 means YCbCr; else an Adobe APP14 means RGB when its transform flag is 0;
# else component ids 'R', 'G' and 'B' mean RGB; anything else is YCbCr
def decode.rgb.of(+facts: U32, frame: Frame) -> Bool:
  match frame:
    case Frame{_w, _h, _nf, ids, _hs, _vs, _tq, _hmax, _vmax}:
      decode.rgb.pick(U32.is_eq(U32.and(facts, 2), 2), U32.is_eq(U32.and(facts, 4), 4), U32.is_eq(U32.and(
        U32.shrn(facts, 8n), 255), 0), ids)

def decode.finish.ok(
  ok1: Bool,
  ok2: Bool,
  frame: Frame,
  scan: Scan,
  tabs: Tabs,
  ent: List<&2, U32>,
  +ri: U32,
  +rgb: Bool
) -> Maybe<&2, Pic>:
  match ok1:
    case False{}:
      None{}
    case True{}:
      match ok2:
        case False{}:
          None{}
        case True{}:
          decode.run(frame, scan, tabs, List.reverse(&2, U32, ent), ri, rgb)

def decode.finish.ph(
  done: Bool,
  +frame: Frame,
  scan: Scan,
  tabs: Tabs,
  ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32,
  +facts: U32
) -> Maybe<&2, Pic>:
  match done:
    case True{}:
      decode.finish.ok(Bool.and(U32.is_eq(kind, 1), decode.facts.soi(facts)), U32.is_eq(bad, 0), frame, scan, tabs,
        ent, ri, decode.rgb.of(facts, frame))
    case False{}:
      None{}

def decode.max.b(gt: Bool, +aa: U32, +bb: U32) -> U32:
  match gt:
    case True{}:
      aa
    case False{}:
      bb

def decode.max(+aa: U32, +bb: U32) -> U32:
  decode.max.b(U32.is_gt(aa, bb), aa, bb)

def decode.vmax(vs: List<&2, U32>, +mm: U32) -> U32:
  match vs:
    case Nil{}:
      mm
    case v <> t:
      decode.vmax(t, decode.max(v, mm))

# a sampling factor the decoder places: 1, 2 or 4
# (laws/JpegPlacesComponentSamples.bend). A Bool of U32.is_eq, not a match
# on literals, so a law can case-split on it.
def decode.fac.ok(+ff: U32) -> Bool:
  Bool.or(U32.is_eq(ff, 1), Bool.or(U32.is_eq(ff, 2), U32.is_eq(ff, 4)))

# both sampling factors of one SOF component byte, H in the high nibble and V
# in the low nibble, are ones the decoder places
def decode.fac.pair(+hv: U32) -> Bool:
  Bool.and(decode.fac.ok(U32.shrn(hv, 4n)), decode.fac.ok(U32.and(hv, 15)))

# a component count the decoder reads: 1 (gray) or 3 (YCbCr)
def decode.nf.ok(+nf: U32) -> Bool:
  Bool.or(U32.is_eq(nf, 1), U32.is_eq(nf, 3))

def decode.u16(+hi: U32, +lo: U32) -> U32:
  U32.or(U32.shln(hi, 8n), lo)

def decode.comps.rev(cc: Comps) -> Comps:
  match cc:
    case Comps{ids, hs, vs, tq, ok}:
      Comps{List.reverse(&2, U32, ids), List.reverse(&2, U32, hs), List.reverse(&2, U32, vs),
        List.reverse(&2, U32, tq), ok}

def decode.read.cs(
  left: Nat,
  xs: List<&2, U32>,
  ids: List<&2, U32>,
  hs: List<&2, U32>,
  vs: List<&2, U32>,
  tqs: List<&2, U32>,
  ok: Bool
) -> Comps:
  match left:
    case 0n:
      match xs:
        case _rest:
          decode.comps.rev(Comps{ids, hs, vs, tqs, ok})
    case 1n+p:
      match xs:
        case id <> +hv <> tq <> rest:
          +hsamp = U32.shrn(hv, 4n)
          +vsamp = U32.and(hv, 15)
          decode.read.cs(p, rest, id <> ids, hsamp <> hs, vsamp <> vs, tq <> tqs, Bool.and(ok, decode.fac.pair(hv)))
        case _:
          Comps{[], [], [], [], False{}}

def decode.read.sof.ok(
  good: Bool,
  zmax: Bool,
  +ww: U32,
  +hh: U32,
  +nf: U32,
  ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>,
  tq: List<&2, U32>,
  scan: Scan,
  tabs: Tabs,
  ent: List<&2, U32>,
  +ri: U32,
  +kind: U32
) -> St:
  match good:
    case False{}:
      St{Stop{}, decode.frame0(), scan, tabs, ent, ri, kind, 1}
    case True{}:
      match zmax:
        case True{}:
          St{Stop{}, decode.frame0(), scan, tabs, ent, ri, kind, 1}
        case False{}:
          match kind:
            case 0:
              St{Seek{}, Frame{ww, hh, nf, ids, hs, vs, tq, decode.vmax(hs, 0), decode.vmax(vs, 0)}, scan, tabs, ent,
                ri, 1, 0}
            case _:
              St{Stop{}, decode.frame0(), scan, tabs, ent, ri, kind, 1}

# the components first: a factor outside 1, 2 and 4, or a short component
# list, refuses the file before the count and the refusals so far are asked
def decode.read.sof.c(
  cok: Bool,
  good: Bool,
  zmax: Bool,
  +ww: U32,
  +hh: U32,
  +nf: U32,
  ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>,
  tq: List<&2, U32>,
  scan: Scan,
  tabs: Tabs,
  ent: List<&2, U32>,
  +ri: U32,
  +kind: U32
) -> St:
  match cok:
    case False{}:
      St{Stop{}, decode.frame0(), scan, tabs, ent, ri, kind, 1}
    case True{}:
      decode.read.sof.ok(good, zmax, ww, hh, nf, ids, hs, vs, tq, scan, tabs, ent, ri, kind)

# a sampling factor T.81 B.2.2 allows: 1 to 4
def decode.fac.any(+ff: U32) -> Bool:
  Bool.and(U32.is_gt(ff, 0), U32.is_le(ff, 4))

# the one component of a frame read whole, its factors each 1 to 4
def decode.fac.one(hs: List<&2, U32>, vs: List<&2, U32>) -> Bool:
  match hs:
    case +hh <> ht:
      match vs:
        case +vv <> vt:
          +_h = decode.drop(ht)
          +_v = decode.drop(vt)
          Bool.and(decode.fac.any(hh), decode.fac.any(vv))
        case Nil{}:
          +_h = decode.drop(ht)
          +_x = (hh - hh : U32)
          False{}
    case Nil{}:
      +_v = decode.drop(vs)
      False{}

# a frame of one component has one scan of one component, which T.81 A.2.2 codes non-interleaved: one data unit
# to an MCU, in raster order over the component's own ceil(ceil(X * H / Hmax) / 8) blocks to a row. With one
# component H is Hmax, so that is the grid of a component sampled 1 by 1, which is how such a frame is kept,
# whatever factors 1 to 4 its SOF names. A frame of three components is read as its SOF says, each factor 1, 2
# or 4 (laws/JpegPlacesComponentSamples.bend).
def decode.read.sof.n1(
  one: Bool,
  cok: Bool,
  +ww: U32,
  +hh: U32,
  +nf: U32,
  +ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>,
  +tq: List<&2, U32>,
  scan: Scan,
  tabs: Tabs,
  ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> St:
  match one:
    case True{}:
      +_c = cok
      decode.read.sof.c(decode.fac.one(hs, vs), U32.is_eq(bad, 0), False{}, ww, hh, nf, ids, [1], [1], tq, scan,
        tabs, ent, ri, kind)
    case False{}:
      decode.read.sof.c(cok, Bool.and(decode.nf.ok(nf), U32.is_eq(bad, 0)), U32.is_eq(decode.vmax(hs, 0), 0), ww,
        hh, nf, ids, hs, vs, tq, scan, tabs, ent, ri, kind)

def decode.read.sof.f(
  cc: Comps,
  +ww: U32,
  +hh: U32,
  +nf: U32,
  scan: Scan,
  tabs: Tabs,
  ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> St:
  match cc:
    case Comps{+ids, +hs, +vs, +tq, cok}:
      decode.read.sof.n1(U32.is_eq(nf, 1), cok, ww, hh, nf, ids, hs, vs, tq, scan, tabs, ent, ri, kind, bad)

# the SOF0 body after its precision byte: precision 8 goes on to the size and the components, any other stops
def decode.read.sof.p(
  p8: Bool,
  xs: List<&2, U32>,
  scan: Scan,
  tabs: Tabs,
  ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> St:
  match p8:
    case True{}:
      match xs:
        case hh <> hl <> wh <> wl <> +nf <> rest:
          decode.read.sof.f(decode.read.cs(U32.to_nat(nf), rest, [], [], [], [], True{}), decode.u16(wh, wl),
            decode.u16(hh, hl), nf, scan, tabs, ent, ri, kind, bad)
        case _:
          St{Stop{}, decode.frame0(), scan, tabs, ent, ri, kind, 1}
    case False{}:
      St{Stop{}, decode.frame0(), scan, tabs, ent, ri, kind, 1}

# an SOF0 body. The precision is compared with U32.is_eq, not a literal pattern, so a law reaches it.
def decode.read.sof(
  xs: List<&2, U32>,
  scan: Scan,
  tabs: Tabs,
  ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> St:
  match xs:
    case +pp <> rest:
      decode.read.sof.p(U32.is_eq(pp, 8), rest, scan, tabs, ent, ri, kind, bad)
    case Nil{}:
      St{Stop{}, decode.frame0(), scan, tabs, ent, ri, kind, 1}

def decode.take(left: Nat, xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32> & List<&2, U32>:
  match left:
    case 0n:
      (List.reverse(&2, U32, acc), xs)
    case 1n+p:
      match xs:
        case h <> t:
          decode.take(p, t, h <> acc)
        case Nil{}:
          (List.reverse(&2, U32, acc), [])

def decode.q.put(tabs: Tabs, +id: U32, vals: List<&2, U32>) -> Tabs:
  match tabs:
    case Tabs{q0, q1, q2, q3, dc0, dc1, dc2, dc3, ac0, ac1, ac2, ac3}:
      match id:
        case 0:
          Tabs{vals, q1, q2, q3, dc0, dc1, dc2, dc3, ac0, ac1, ac2, ac3}
        case 1:
          Tabs{q0, vals, q2, q3, dc0, dc1, dc2, dc3, ac0, ac1, ac2, ac3}
        case 2:
          Tabs{q0, q1, vals, q3, dc0, dc1, dc2, dc3, ac0, ac1, ac2, ac3}
        case _:
          Tabs{q0, q1, q2, vals, dc0, dc1, dc2, dc3, ac0, ac1, ac2, ac3}

# 16-bit quantisation entries, two bytes each, high byte first
def decode.q.wide(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      []
    case +hi <> rest:
      match rest:
        case Nil{}:
          +_h = (hi - hi : U32)
          []
        case +lo <> more:
          decode.u16(hi, lo) <> decode.q.wide(more)

# a table's entries as read: one byte each for Pq = 0, two for Pq = 1 (T.81 B.2.4.1)
def decode.q.vals(wide: Bool, xs: List<&2, U32>) -> List<&2, U32>:
  match wide:
    case True{}:
      decode.q.wide(xs)
    case False{}:
      xs

# a DQT body: each table's Pq and Tq byte (Pq 0 or 1, Tq at most 3), then its 64 entries, of 8 or 16 bits
def decode.read.dqt(
  xs: List<&2, U32>,
  ok: Bool,
  phase: Nat,
  +id: U32,
  +wide: Bool,
  acc: List<&2, U32>,
  frame: Frame,
  scan: Scan,
  tabs: Tabs,
  ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> St:
  match xs:
    case Nil{}:
      match ok:
        case False{}:
          +_a = decode.drop(acc)
          St{Stop{}, frame, scan, tabs, ent, ri, kind, 1}
        case True{}:
          match phase:
            case 0n:
              +_a = decode.drop(acc)
              St{Seek{}, frame, scan, tabs, ent, ri, kind, bad}
            case _:
              +_a = decode.drop(acc)
              St{Stop{}, frame, scan, tabs, ent, ri, kind, 1}
    case +b <> rest:
      match ok:
        case False{}:
          +_n = decode.drop(rest)
          +_a = decode.drop(acc)
          +_b = (b - b : U32)
          St{Stop{}, frame, scan, tabs, ent, ri, kind, 1}
        case True{}:
          match phase:
            case 0n:
              +_a = decode.drop(acc)
              +pq = U32.shrn(b, 4n)
              decode.read.dqt(rest, Bool.and(U32.is_le(pq, 1), U32.is_le(U32.and(b, 15), 3)), Bool.pick(Nat,
                U32.is_eq(pq, 1), 128n, 64n), U32.and(b, 15), U32.is_eq(pq, 1), [], frame, scan, tabs, ent, ri, kind,
                bad)
            case 1n+p:
              match p:
                case 0n:
                  decode.read.dqt(rest, True{}, 0n, 0, False{}, [], frame, scan,
                    decode.q.put(tabs, id, decode.q.vals(wide, List.reverse(&2, U32, b <> acc))), ent, ri, kind, bad)
                case _:
                  decode.read.dqt(rest, True{}, p, id, wide, b <> acc, frame, scan, tabs, ent, ri, kind, bad)

def decode.sum.counts(xs: List<&2, U32>, +nn: U32) -> U32:
  match xs:
    case Nil{}:
      nn
    case h <> t:
      decode.sum.counts(t, (nn + h : U32))

# the canonical codes of a table's 16 counts each fit their length without the all-ones code (T.81 C; libjpeg's
# jpeg_make_d_derived_tbl): code is the next code of length si, lim 2^si
def decode.huff.fits(cs: List<&2, U32>, +code: U32, +lim: U32, +ok: Bool) -> Bool:
  match cs:
    case Nil{}:
      ok
    case +cc <> rest:
      +nx = (code + cc : U32)
      decode.huff.fits(rest, (nx * 2 : U32), (lim * 2 : U32), Bool.and(ok, U32.is_lt(nx, lim)))

# a table's counts: at most 256 symbols, and codes that fit
def decode.huff.counts.ok(+cs: List<&2, U32>) -> Bool:
  Bool.and(U32.is_le(decode.sum.counts(cs, 0), 256), decode.huff.fits(cs, 0, 2, True{}))

# a symbol a table may hold: a DC table's (class 0) are difference categories, 0 to 11 for 8-bit samples (T.81
# F.1.2.1); an AC table's are any byte
def decode.huff.sym.ok(+cls: U32, +sym: U32) -> Bool:
  Bool.or(Bool.not(U32.is_eq(cls, 0)), U32.is_le(sym, 11))

def decode.huff.put.dc(
  +id: U32,
  hh: Huff,
  q0: List<&2, U32>,
  q1: List<&2, U32>,
  q2: List<&2, U32>,
  q3: List<&2, U32>,
  dc0: Huff,
  dc1: Huff,
  dc2: Huff,
  dc3: Huff,
  ac0: Huff,
  ac1: Huff,
  ac2: Huff,
  ac3: Huff
) -> Tabs:
  match id:
    case 0:
      Tabs{q0, q1, q2, q3, hh, dc1, dc2, dc3, ac0, ac1, ac2, ac3}
    case 1:
      Tabs{q0, q1, q2, q3, dc0, hh, dc2, dc3, ac0, ac1, ac2, ac3}
    case 2:
      Tabs{q0, q1, q2, q3, dc0, dc1, hh, dc3, ac0, ac1, ac2, ac3}
    case _:
      Tabs{q0, q1, q2, q3, dc0, dc1, dc2, hh, ac0, ac1, ac2, ac3}

def decode.huff.put.ac(
  +id: U32,
  hh: Huff,
  q0: List<&2, U32>,
  q1: List<&2, U32>,
  q2: List<&2, U32>,
  q3: List<&2, U32>,
  dc0: Huff,
  dc1: Huff,
  dc2: Huff,
  dc3: Huff,
  ac0: Huff,
  ac1: Huff,
  ac2: Huff,
  ac3: Huff
) -> Tabs:
  match id:
    case 0:
      Tabs{q0, q1, q2, q3, dc0, dc1, dc2, dc3, hh, ac1, ac2, ac3}
    case 1:
      Tabs{q0, q1, q2, q3, dc0, dc1, dc2, dc3, ac0, hh, ac2, ac3}
    case 2:
      Tabs{q0, q1, q2, q3, dc0, dc1, dc2, dc3, ac0, ac1, hh, ac3}
    case _:
      Tabs{q0, q1, q2, q3, dc0, dc1, dc2, dc3, ac0, ac1, ac2, hh}

def decode.huff.put(tabs: Tabs, +cls: U32, +id: U32, hh: Huff) -> Tabs:
  match tabs:
    case Tabs{q0, q1, q2, q3, dc0, dc1, dc2, dc3, ac0, ac1, ac2, ac3}:
      match cls:
        case 0:
          decode.huff.put.dc(id, hh, q0, q1, q2, q3, dc0, dc1, dc2, dc3, ac0, ac1, ac2, ac3)
        case _:
          decode.huff.put.ac(id, hh, q0, q1, q2, q3, dc0, dc1, dc2, dc3, ac0, ac1, ac2, ac3)

def decode.read.dht(
  xs: List<&2, U32>,
  ok: Bool,
  sym: Bool,
  phase: Nat,
  +cls: U32,
  +id: U32,
  +counts: List<&2, U32>,
  +syms: List<&2, U32>,
  frame: Frame,
  scan: Scan,
  tabs: Tabs,
  ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> St:
  match xs:
    case Nil{}:
      match ok:
        case False{}:
          +_c = decode.drop(counts)
          +_s = decode.drop(syms)
          St{Stop{}, frame, scan, tabs, ent, ri, kind, 1}
        case True{}:
          match sym:
            case False{}:
              match phase:
                case 0n:
                  +_c = decode.drop(counts)
                  +_s = decode.drop(syms)
                  St{Seek{}, frame, scan, tabs, ent, ri, kind, bad}
                case _:
                  +_c = decode.drop(counts)
                  +_s = decode.drop(syms)
                  St{Stop{}, frame, scan, tabs, ent, ri, kind, 1}
            case True{}:
              match phase:
                case 0n:
                  +_s = decode.drop(syms)
                  St{Seek{}, frame, scan, decode.huff.put(tabs, cls, id, decode.canon(counts, [])), ent, ri, kind, bad}
                case _:
                  +_c = decode.drop(counts)
                  +_s = decode.drop(syms)
                  St{Stop{}, frame, scan, tabs, ent, ri, kind, 1}
    case +b <> rest:
      match ok:
        case False{}:
          +_n = decode.drop(rest)
          +_c = decode.drop(counts)
          +_s = decode.drop(syms)
          +_b = (b - b : U32)
          St{Stop{}, frame, scan, tabs, ent, ri, kind, 1}
        case True{}:
          match sym:
            case False{}:
              match phase:
                case 0n:
                  +_c = decode.drop(counts)
                  +_s = decode.drop(syms)
                  decode.read.dht(rest, Bool.and(U32.is_le(U32.shrn(b, 4n), 1), U32.is_le(U32.and(b, 15), 3)),
                    False{}, 16n, U32.shrn(b, 4n), U32.and(b, 15), [], [], frame, scan, tabs, ent, ri, kind, bad)
                case 1n+p:
                  match p:
                    case 0n:
                      +cs = List.reverse(&2, U32, b <> counts)
                      decode.read.dht(rest, decode.huff.counts.ok(cs), True{}, U32.to_nat(decode.sum.counts(cs, 0)),
                        cls, id, cs, [], frame, scan, tabs, ent, ri, kind, bad)
                    case _:
                      +_s = decode.drop(syms)
                      decode.read.dht(rest, True{}, False{}, p, cls, id, b <> counts, [], frame, scan, tabs, ent, ri,
                        kind, bad)
            case True{}:
              match phase:
                case 0n:
                  +_s = decode.drop(syms)
                  decode.read.dht(rest, Bool.and(U32.is_le(U32.shrn(b, 4n), 1), U32.is_le(U32.and(b, 15), 3)),
                    False{}, 16n, U32.shrn(b, 4n), U32.and(b, 15), [], [], frame, scan, decode.huff.put(tabs, cls, id,
                    decode.canon(counts, [])), ent, ri, kind, bad)
                case 1n+p:
                  match p:
                    case 0n:
                      decode.read.dht(rest, decode.huff.sym.ok(cls, b), False{}, 0n, 0, 0, [], [], frame, scan,
                        decode.huff.put(tabs, cls, id, decode.canon(counts, List.reverse(&2, U32, b <> syms))), ent,
                          ri, kind, bad)
                    case _:
                      decode.read.dht(rest, decode.huff.sym.ok(cls, b), True{}, p, cls, id, counts, b <> syms, frame,
                        scan, tabs, ent, ri, kind, bad)

def decode.scan.rev(sids: List<&2, U32>, td: List<&2, U32>, ta: List<&2, U32>, +ns: U32) -> Scan:
  Scan{ns, List.reverse(&2, U32, sids), List.reverse(&2, U32, td), List.reverse(&2, U32, ta), 0, 63, 0}

def decode.read.sos.ok(
  ss0: Bool,
  se63: Bool,
  ah0: Bool,
  sids: List<&2, U32>,
  td: List<&2, U32>,
  ta: List<&2, U32>,
  +ns: U32,
  frame: Frame,
  tabs: Tabs,
  ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> St:
  match ss0:
    case False{}:
      St{Stop{}, frame, decode.scan0(), tabs, ent, ri, kind, 1}
    case True{}:
      match se63:
        case False{}:
          St{Stop{}, frame, decode.scan0(), tabs, ent, ri, kind, 1}
        case True{}:
          match ah0:
            case False{}:
              St{Stop{}, frame, decode.scan0(), tabs, ent, ri, kind, 1}
            case True{}:
              St{Ent{}, frame, decode.scan.rev(sids, td, ta, ns), tabs, ent, ri, kind, bad}

def decode.read.sos.end(
  xs: List<&2, U32>,
  +tok: Bool,
  sids: List<&2, U32>,
  td: List<&2, U32>,
  ta: List<&2, U32>,
  +ns: U32,
  frame: Frame,
  tabs: Tabs,
  ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> St:
  match xs:
    case ss <> se <> ah <> _rest:
      decode.read.sos.ok(Bool.and(tok, U32.is_eq(ss, 0)), U32.is_eq(se, 63), U32.is_eq(ah, 0), sids, td, ta, ns, frame,
        tabs, ent, ri, kind, bad)
    case _:
      St{Stop{}, frame, decode.scan0(), tabs, ent, ri, kind, 1}

def decode.read.sos.cs(
  left: Nat,
  xs: List<&2, U32>,
  +tok: Bool,
  sids: List<&2, U32>,
  td: List<&2, U32>,
  ta: List<&2, U32>,
  +ns: U32,
  frame: Frame,
  tabs: Tabs,
  ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> St:
  match left:
    case 0n:
      decode.read.sos.end(xs, tok, sids, td, ta, ns, frame, tabs, ent, ri, kind, bad)
    case 1n+p:
      match xs:
        case id <> +tdta <> rest:
          decode.read.sos.cs(p, rest, Bool.and(tok, Bool.and(U32.is_le(U32.shrn(tdta, 4n), 3), U32.is_le(U32.and(tdta,
            15), 3))), id <> sids, U32.shrn(tdta, 4n) <> td, U32.and(tdta, 15) <> ta, ns, frame, tabs, ent, ri, kind,
            bad)
        case _:
          St{Stop{}, frame, decode.scan0(), tabs, ent, ri, kind, 1}

def decode.read.sos(
  xs: List<&2, U32>,
  frame: Frame,
  tabs: Tabs,
  ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> St:
  match xs:
    case +ns <> rest:
      decode.read.sos.cs(U32.to_nat(ns), rest, True{}, [], [], [], ns, frame, tabs, ent, ri, kind, bad)
    case _:
      St{Stop{}, frame, decode.scan0(), tabs, ent, ri, kind, 1}

def decode.read.dri(
  xs: List<&2, U32>,
  frame: Frame,
  scan: Scan,
  tabs: Tabs,
  ent: List<&2, U32>,
  +kind: U32,
  +bad: U32
) -> St:
  match xs:
    case hi <> lo <> _rest:
      St{Seek{}, frame, scan, tabs, ent, decode.u16(hi, lo), kind, bad}
    case _:
      St{Stop{}, frame, scan, tabs, ent, 0, kind, 1}

def decode.dispatch(
  +mark: U32,
  xs: List<&2, U32>,
  frame: Frame,
  scan: Scan,
  tabs: Tabs,
  ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> St:
  match mark:
    case 192:
      decode.read.sof(xs, scan, tabs, ent, ri, kind, bad)
    case 193:
      decode.read.sof(xs, scan, tabs, ent, ri, kind, bad)
    case 196:
      decode.read.dht(xs, True{}, False{}, 0n, 0, 0, [], [], frame, scan, tabs, ent, ri, kind, bad)
    case 218:
      decode.read.sos(xs, frame, tabs, ent, ri, kind, bad)
    case 219:
      decode.read.dqt(xs, True{}, 0n, 0, False{}, [], frame, scan, tabs, ent, ri, kind, bad)
    case 221:
      decode.read.dri(xs, frame, scan, tabs, ent, kind, bad)
    case _:
      St{Seek{}, frame, scan, tabs, ent, ri, kind, bad}

def decode.between(+bb: U32, +lo: U32, +hi: U32) -> Bool:
  Bool.and(U32.is_ge(bb, lo), U32.is_le(bb, hi))

def decode.mark.range.b(
  sof: Bool,
  app: Bool,
  rst: Bool,
  +bb: U32,
  frame: Frame,
  scan: Scan,
  tabs: Tabs,
  ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> St:
  match sof:
    case True{}:
      St{Stop{}, frame, scan, tabs, ent, ri, 2, 1}
    case False{}:
      match app:
        case True{}:
          St{LenHi{bb}, frame, scan, tabs, ent, ri, kind, bad}
        case False{}:
          match rst:
            case True{}:
              St{Seek{}, frame, scan, tabs, ent, ri, kind, bad}
            case False{}:
              St{Stop{}, frame, scan, tabs, ent, ri, kind, 1}

def decode.mark.range(
  +bb: U32,
  frame: Frame,
  scan: Scan,
  tabs: Tabs,
  ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> St:
  decode.mark.range.b(decode.between(bb, 192, 207), decode.between(bb, 224, 239), decode.between(bb, 208, 215), bb,
    frame, scan, tabs, ent, ri, kind, bad)

def decode.mark(
  +bb: U32,
  frame: Frame,
  scan: Scan,
  tabs: Tabs,
  ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> St:
  match bb:
    case 1:
      St{Seek{}, frame, scan, tabs, ent, ri, kind, bad}
    case 192:
      St{LenHi{192}, frame, scan, tabs, ent, ri, kind, bad}
    case 193:
      St{LenHi{193}, frame, scan, tabs, ent, ri, kind, bad}
    case 196:
      St{LenHi{196}, frame, scan, tabs, ent, ri, kind, bad}
    case 216:
      St{Seek{}, frame, scan, tabs, ent, ri, kind, bad}
    case 217:
      St{Stop{}, frame, scan, tabs, ent, ri, kind, bad}
    case 218:
      St{LenHi{218}, frame, scan, tabs, ent, ri, kind, bad}
    case 219:
      St{LenHi{219}, frame, scan, tabs, ent, ri, kind, bad}
    case 221:
      St{LenHi{221}, frame, scan, tabs, ent, ri, kind, bad}
    case 254:
      St{LenHi{254}, frame, scan, tabs, ent, ri, kind, bad}
    case 255:
      St{Mark{}, frame, scan, tabs, ent, ri, kind, bad}
    case _:
      decode.mark.range(bb, frame, scan, tabs, ent, ri, kind, bad)

def decode.step.pay0(
  left: Nat,
  +mark: U32,
  frame: Frame,
  scan: Scan,
  tabs: Tabs,
  ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> St:
  match left:
    case 0n:
      decode.dispatch(mark, [], frame, scan, tabs, ent, ri, kind, bad)
    case _:
      St{Pay{mark, left, []}, frame, scan, tabs, ent, ri, kind, bad}

def decode.step.len.b(
  small: Bool,
  +mark: U32,
  +len: U32,
  frame: Frame,
  scan: Scan,
  tabs: Tabs,
  ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> St:
  match small:
    case True{}:
      St{Stop{}, frame, scan, tabs, ent, ri, kind, 1}
    case False{}:
      decode.step.pay0(U32.to_nat((len - 2 : U32)), mark, frame, scan, tabs, ent, ri, kind, bad)

def decode.step.last(
  left: Nat,
  +bb: U32,
  +mark: U32,
  acc: List<&2, U32>,
  frame: Frame,
  scan: Scan,
  tabs: Tabs,
  ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> St:
  match left:
    case 0n:
      decode.dispatch(mark, List.reverse(&2, U32, bb <> acc), frame, scan, tabs, ent, ri, kind, bad)
    case 1n+q:
      St{Pay{mark, Nat.add(1n, q), bb <> acc}, frame, scan, tabs, ent, ri, kind, bad}

def decode.step.pay(
  left: Nat,
  +bb: U32,
  +mark: U32,
  acc: List<&2, U32>,
  frame: Frame,
  scan: Scan,
  tabs: Tabs,
  ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> St:
  match left:
    case 0n:
      St{Stop{}, frame, scan, tabs, ent, ri, kind, 1}
    case 1n+p:
      decode.step.last(p, bb, mark, acc, frame, scan, tabs, ent, ri, kind, bad)

# a marker other than RSTn and EOI inside a scan ends the scan: after a frame header the walk keeps the bytes after
# it (Rest); before one the file is refused
def decode.ent.next(
  framed: Bool,
  +bb: U32,
  frame: Frame,
  scan: Scan,
  tabs: Tabs,
  ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> St:
  match framed:
    case True{}:
      St{Rest{bb, []}, frame, scan, tabs, ent, ri, kind, bad}
    case False{}:
      St{Stop{}, frame, scan, tabs, ent, ri, kind, 1}

def decode.ent.rst.b(
  rst: Bool,
  +bb: U32,
  frame: Frame,
  scan: Scan,
  tabs: Tabs,
  ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> St:
  match rst:
    case True{}:
      St{Ent{}, frame, scan, tabs, bb <> (255 <> ent), ri, kind, bad}
    case False{}:
      decode.ent.next(U32.is_eq(kind, 1), bb, frame, scan, tabs, ent, ri, kind, bad)

# a byte of the entropy-coded data: 255 may open a stuffed pair or a marker, any other byte is data.
# Compares with U32.is_eq, not a literal pattern, so a law reaches a symbolic byte.
def decode.step.ent(
  ff: Bool,
  +bb: U32,
  frame: Frame,
  scan: Scan,
  tabs: Tabs,
  ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> St:
  match ff:
    case True{}:
      +_b = (bb - bb : U32)
      St{EntFF{}, frame, scan, tabs, ent, ri, kind, bad}
    case False{}:
      St{Ent{}, frame, scan, tabs, bb <> ent, ri, kind, bad}

def decode.step.ph(
  phase: Phase,
  +bb: U32,
  frame: Frame,
  scan: Scan,
  tabs: Tabs,
  ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> St:
  match phase:
    case Seek{}:
      match bb:
        case 255:
          St{Mark{}, frame, scan, tabs, ent, ri, kind, bad}
        case _:
          St{Seek{}, frame, scan, tabs, ent, ri, kind, bad}
    case Mark{}:
      decode.mark(bb, frame, scan, tabs, ent, ri, kind, bad)
    case LenHi{+mark}:
      St{LenLo{mark, bb}, frame, scan, tabs, ent, ri, kind, bad}
    case LenLo{+mark, +hi}:
      decode.step.len.b(U32.is_lt(decode.u16(hi, bb), 2), mark, decode.u16(hi, bb), frame, scan, tabs, ent, ri, kind,
        bad)
    case Pay{+mark, +left, +acc}:
      decode.step.pay(left, bb, mark, acc, frame, scan, tabs, ent, ri, kind, bad)
    case Ent{}:
      decode.step.ent(U32.is_eq(bb, 255), bb, frame, scan, tabs, ent, ri, kind, bad)
    case EntFF{}:
      match bb:
        case 0:
          St{Ent{}, frame, scan, tabs, 0 <> (255 <> ent), ri, kind, bad}
        case 255:
          St{EntFF{}, frame, scan, tabs, ent, ri, kind, bad}
        case 217:
          St{Stop{}, frame, scan, tabs, ent, ri, kind, bad}
        case _:
          decode.ent.rst.b(decode.between(bb, 208, 215), bb, frame, scan, tabs, ent, ri, kind, bad)
    case Stop{}:
      St{Stop{}, frame, scan, tabs, ent, ri, kind, bad}
    case Rest{+mark, +acc}:
      St{Rest{mark, bb <> acc}, frame, scan, tabs, ent, ri, kind, bad}

def decode.step(+bb: U32, st: St) -> St:
  match st:
    case St{+phase, +frame, +scan, +tabs, +ent, +ri, +kind, +bad}:
      decode.step.ph(phase, bb, frame, scan, tabs, ent, ri, kind, bad)

def decode.walk(xs: List<&2, U32>, st: St) -> St:
  match xs:
    case Nil{}:
      st
    case b <> t:
      decode.walk(t, decode.step(b, st))

# the scans of a file: whether every walk read them cleanly, and the passes, last first
type Chain is Data:
  Chain{ok: Bool, passes: List<&2, Pass>}

# a walk that read one frame header and no error
def decode.st.good(st: St) -> Bool:
  match st:
    case St{_phase, _frame, _scan, _tabs, _ent, _ri, +kind, +bad}:
      Bool.and(U32.is_eq(kind, 1), U32.is_eq(bad, 0))

def decode.scan.ns(scan: Scan) -> U32:
  match scan:
    case Scan{+ns, _sids, _td, _ta, _ss, _se, _ah}:
      ns

# the passes with the last walk's scan, unless that walk read no SOS (only other segments, then EOI): none says its
# component count is 0, asked with U32.is_eq so a law reaches a symbolic count
def decode.chain.last(
  none: Bool,
  scan: Scan,
  tabs: Tabs,
  ent: List<&2, U32>,
  +ri: U32,
  passes: List<&2, Pass>
) -> List<&2, Pass>:
  match none:
    case True{}:
      match ent:
        case Nil{}:
          passes
        case +e <> et:
          Pass{scan, tabs, List.reverse(&2, U32, e <> et), ri} <> passes
    case False{}:
      Pass{scan, tabs, List.reverse(&2, U32, ent), ri} <> passes

# the scans of the walks from st on, good saying st read cleanly: a walk that ended at a marker after its scan (Rest)
# hands on a pass of its scan, with the tables and restart interval it read it with, and the bytes after the marker
# are walked on from that marker with the same frame, tables and restart interval (T.81 B.2.4: tables may be
# redefined between scans). A walk ending where a scan may end is the last; one ending anywhere else, or with an error
# or a second frame header, refuses the file.
def decode.chain(left: Nat, good: Bool, st: St, passes: List<&2, Pass>) -> Chain:
  match left:
    case 0n:
      Chain{False{}, []}
    case 1n+p:
      match good:
        case False{}:
          Chain{False{}, []}
        case True{}:
          match st:
            case St{phase, +frame, +scan, +tabs, +ent, +ri, _kind, _bad}:
              match phase:
                case Rest{+mark, +acc}:
                  +nx = decode.walk(List.reverse(&2, U32, acc), decode.mark(mark, frame, decode.scan0(), tabs, [], ri,
                    1, 0))
                  decode.chain(p, decode.st.good(nx), nx, Pass{scan, tabs, List.reverse(&2, U32, ent), ri} <> passes)
                case Stop{}:
                  Chain{True{}, decode.chain.last(U32.is_eq(decode.scan.ns(scan), 0), scan, tabs, ent, ri, passes)}
                case Ent{}:
                  Chain{True{}, decode.chain.last(U32.is_eq(decode.scan.ns(scan), 0), scan, tabs, ent, ri, passes)}
                case EntFF{}:
                  Chain{True{}, decode.chain.last(U32.is_eq(decode.scan.ns(scan), 0), scan, tabs, ent, ri, passes)}
                case _:
                  Chain{False{}, []}

def decode.multi.go(ok: Bool, passes: List<&2, Pass>, frame: Frame, rgb: Bool) -> Maybe<&2, Pic>:
  match ok:
    case False{}:
      +_p = passes
      None{}
    case True{}:
      decode.passes(frame, List.reverse(&2, Pass, passes), rgb)

# the picture of a file of several scans: its chain of walks read cleanly from SOI, then its passes
def decode.multi(chain: Chain, +frame: Frame, +facts: U32) -> Maybe<&2, Pic>:
  match chain:
    case Chain{+ok, +passes}:
      decode.multi.go(Bool.and(ok, decode.facts.soi(facts)), passes, frame, decode.rgb.of(facts, frame))

# the picture of a finished walk, facts being what decode.facts read of the file's markers. A walk that ended at a
# marker after its scan reads on (decode.chain). One that read EOI (Stop), or whose bytes ended inside the
# entropy-coded data, which libjpeg also takes as the end of the image (with a warning), hands its scan on; any other
# has no picture.
def decode.finish.at(
  phase: Phase,
  +frame: Frame,
  +scan: Scan,
  +tabs: Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32,
  +facts: U32
) -> Maybe<&2, Pic>:
  match phase:
    case Rest{+mark, +acc}:
      +st = {St{Rest{mark, acc}, frame, scan, tabs, ent, ri, kind, bad} : St}
      decode.multi(decode.chain(1n+1n+List.length(&2, U32, acc), decode.st.good(st), st, []), frame, facts)
    case Stop{}:
      decode.finish.ph(True{}, frame, scan, tabs, ent, ri, kind, bad, facts)
    case Ent{}:
      decode.finish.ph(True{}, frame, scan, tabs, ent, ri, kind, bad, facts)
    case EntFF{}:
      decode.finish.ph(True{}, frame, scan, tabs, ent, ri, kind, bad, facts)
    case _:
      decode.finish.ph(False{}, frame, scan, tabs, ent, ri, kind, bad, facts)

# the picture of a finished walk, facts being what decode.facts read of the file's markers
def decode.finish(st: St, +facts: U32) -> Maybe<&2, Pic>:
  match st:
    case St{+phase, +frame, +scan, +tabs, +ent, +ri, +kind, +bad}:
      decode.finish.at(phase, frame, scan, tabs, ent, ri, kind, bad, facts)

# the JPEG start-of-image marker, FF D8
def soi() -> List<&2, U32>:
  [255, 216]

# the JPEG end-of-image marker, FF D9
def eoi() -> List<&2, U32>:
  [255, 217]

# a segment body opens with the identifier want, ok saying the bytes before matched
def decode.facts.id(want: List<&2, U32>, body: List<&2, U32>, +ok: Bool) -> Bool:
  match want:
    case Nil{}:
      +_b = decode.drop(body)
      ok
    case +ww <> wt:
      match body:
        case Nil{}:
          +_w = decode.drop(wt)
          +_x = (ww - ww : U32)
          False{}
        case +bb <> bt:
          decode.facts.id(wt, bt, Bool.and(ok, U32.is_eq(bb, ww)))

# byte kk of a segment body, 0 past its end
def decode.facts.at(body: List<&2, U32>, kk: Nat) -> U32:
  decode.at.m(List.get(&2, U32, body, kk))

# what an APPn segment's body adds: an APP0 opening with JFIF and its null, at least 14 bytes, sets bit 1; an
# APP14 opening with Adobe, at least 12 bytes, sets bit 2 and puts its transform flag (byte 11) in bits 8 to 15
def decode.facts.app(+mark: U32, +nn: U32, +body: List<&2, U32>, +acc: U32) -> U32:
  match mark:
    case 224:
      Bool.pick(U32, Bool.and(U32.is_ge(nn, 14), decode.facts.id([74, 70, 73, 70, 0], body, True{})), U32.or(acc, 2),
        acc)
    case 238:
      Bool.pick(U32, Bool.and(U32.is_ge(nn, 12), decode.facts.id([65, 100, 111, 98, 101], body, True{})),
        U32.or(U32.or(U32.and(acc, 4294902015), 4), U32.shln(U32.and(decode.facts.at(body, 11n), 255), 8n)), acc)
    case _:
      acc

# the facts pass between two bytes: ph 0 between segments, 1 after an FF, 2 and 3 a length field (its high byte
# in hi), 4 inside a body of left more bytes (its length in hi, its first 16 bytes kept in got, newest first, for
# APP0 and APP14), 5 stopped at the first scan's SOS or at EOI; acc the facts so far
type Fs is Data:
  Fs{ph: U32, mark: U32, hi: U32, left: Nat, got: List<&2, U32>, acc: U32}

# a body byte kept for the facts: only APP0 and APP14 are read, and only their first 16 bytes
def decode.facts.keep(+mark: U32, +bb: U32, +got: List<&2, U32>) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, Bool.and(Bool.or(U32.is_eq(mark, 224), U32.is_eq(mark, 238)), Nat.is_lt(List.length(&2,
    U32, got), 16n)), bb <> got, got)

# a segment's end: its body read for facts, and the pass back between segments
def decode.facts.end(+mark: U32, +nn: U32, got: List<&2, U32>, +acc: U32) -> Fs:
  Fs{0, 0, 0, 0n, [], decode.facts.app(mark, nn, List.reverse(&2, U32, got), acc)}

# a length field read: an empty body ends the segment at once
def decode.facts.len(left: Nat, +mark: U32, +nn: U32, +acc: U32) -> Fs:
  match left:
    case 0n:
      decode.facts.end(mark, nn, [], acc)
    case 1n+p:
      Fs{4, mark, nn, 1n+p, [], acc}

# after an FF: a fill FF, a marker that stands alone (TEM, RST0 to RST7, SOI), the first scan's SOS or EOI, which
# stop the pass, or a marker that opens a segment
def decode.facts.mark(+bb: U32, +acc: U32) -> Fs:
  match bb:
    case 255:
      Fs{1, 0, 0, 0n, [], acc}
    case 218:
      Fs{5, 0, 0, 0n, [], acc}
    case 217:
      Fs{5, 0, 0, 0n, [], acc}
    case 216:
      Fs{0, 0, 0, 0n, [], acc}
    case 1:
      Fs{0, 0, 0, 0n, [], acc}
    case _:
      Bool.pick(Fs, decode.between(bb, 208, 215), Fs{0, 0, 0, 0n, [], acc}, Fs{2, bb, 0, 0n, [], acc})

# one byte of the facts pass. A byte between segments that is not an FF is skipped, as the walk skips it.
def decode.facts.step(+bb: U32, fs: Fs) -> Fs:
  match fs:
    case Fs{+ph, +mark, +hi, +left, +got, +acc}:
      match ph:
        case 0:
          Bool.pick(Fs, U32.is_eq(bb, 255), Fs{1, mark, hi, left, got, acc}, Fs{0, mark, hi, left, got, acc})
        case 1:
          decode.facts.mark(bb, acc)
        case 2:
          Fs{3, mark, bb, left, got, acc}
        case 3:
          +ln = decode.u16(hi, bb)
          +nn = Bool.pick(U32, U32.is_lt(ln, 2), 0, (ln - 2 : U32))
          decode.facts.len(U32.to_nat(nn), mark, nn, acc)
        case 4:
          match left:
            case 0n:
              decode.facts.end(mark, hi, decode.facts.keep(mark, bb, got), acc)
            case 1n+p:
              match p:
                case 0n:
                  decode.facts.end(mark, hi, decode.facts.keep(mark, bb, got), acc)
                case _:
                  Fs{4, mark, hi, p, decode.facts.keep(mark, bb, got), acc}
        case _:
          Fs{5, mark, hi, left, got, acc}

# the facts so far
def decode.facts.acc(fs: Fs) -> U32:
  match fs:
    case Fs{_ph, _mark, _hi, _left, got, +acc}:
      +_g = decode.drop(got)
      acc

# the facts pass over bytes, stopping at the first scan
def decode.facts.walk(xs: List<&2, U32>, fs: Fs) -> U32:
  match xs:
    case Nil{}:
      decode.facts.acc(fs)
    case +bb <> rest:
      match fs:
        case Fs{+ph, +mark, +hi, +left, +got, +acc}:
          match ph:
            case 5:
              +_x = decode.drop(rest)
              decode.facts.acc(Fs{5, mark, (hi + bb : U32), left, got, acc})
            case _:
              decode.facts.walk(rest, decode.facts.step(bb, Fs{ph, mark, hi, left, got, acc}))

# a file that opens with SOI: bit 0, then the colour facts of its markers
def decode.facts.soi.at(soi: Bool, rest: List<&2, U32>) -> U32:
  match soi:
    case True{}:
      decode.facts.walk(rest, Fs{0, 0, 0, 0n, [], 1})
    case False{}:
      +_r = decode.drop(rest)
      0

# what libjpeg reads from a file's markers before its first scan: bit 0 the file opens with SOI (T.81 B.2.1; a
# file that does not is refused), and the colour facts decode.facts.app collects
def decode.facts(bytes: List<&2, U32>) -> U32:
  match bytes:
    case +b0 <> +b1 <> rest:
      decode.facts.soi.at(Bool.and(U32.is_eq(b0, 255), U32.is_eq(b1, 216)), rest)
    case _:
      0

# baseline or extended sequential 8-bit Huffman JPEG bytes, or none when the file is not one this decoder reads
def decode(+bytes: List<&2, U32>) -> Maybe<&2, Pic>:
  decode.finish(decode.walk(bytes, decode.st0()), decode.facts(bytes))
