# src/jpeg: baseline JPEG. Sequential 8-bit Huffman (SOF0), JFIF APP0, grayscale or YCbCr.

import Base

# a decoded picture: width, height, and row-major samples
type Pic is Data:
  Pic{w: U32, h: U32, pixels: List<&2, U32>}

# one Huffman table: canonical codes, lengths, and symbols
type Huff is Data:
  Huff{codes: List<&2, U32>, lens: List<&2, U32>, syms: List<&2, U32>}

# SOF0 frame geometry. Sampling factors are 1, 2, or 4.
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

# marker walk: seeking, a marker byte, a length, a payload, or the entropy scan
type Phase is Data:
  Seek{}
  Mark{}
  LenHi{mark: U32}
  LenLo{mark: U32, hi: U32}
  Pay{mark: U32, left: Nat, acc: List<&2, U32>}
  Ent{}
  EntFF{}
  Stop{}

# parser state. kind 1 is a baseline frame. bad 1 rejects the file.
type St is Data:
  St{phase: Phase, frame: Frame, scan: Scan, tabs: Tabs, ent: List<&2, U32>, ri: U32, kind: U32, bad: U32}

# bit reader. n bits remain in buf. ok is 0 after a truncated or marked stream.
type Bits is Data:
  Bits{n: U32, ok: U32, buf: U32, xs: List<&2, U32>}

# a Huffman lookup in progress
type Ask is Data:
  Ask{hit: Maybe<&2, U32>, code: U32, len: U32, bits: Bits}

# one decoded Huffman symbol
type Hit is Data:
  Hit{sym: U32, bits: Bits, ok: U32}

# AC run state inside one block
type Ac is Data:
  Ac{k: U32, zz: List<&2, U32>, bits: Bits, done: U32, ok: U32}

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

# sample cursor inside an upsampled block
type Cursor is Data:
  Cursor{k: U32, px: U32, py: U32}

# SOF component lists while they are being read
type Comps is Data:
  Comps{ids: List<&2, U32>, hs: List<&2, U32>, vs: List<&2, U32>, tq: List<&2, U32>, bad: U32}

# the eight cosine columns of the A.3.3 matrix, one list per frequency
type Cols is Data:
  Cols{c0: List<&2, U32>, c1: List<&2, U32>, c2: List<&2, U32>, c3: List<&2, U32>, c4: List<&2, U32>,
    c5: List<&2, U32>, c6: List<&2, U32>, c7: List<&2, U32>}

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

def decode.q17.res(+hh: U32, +ll: U32) -> U32:
  U32.or(U32.shrn(ll, 17n), U32.shln(U32.and(hh, 131071), 15n))

def decode.q17.sign2(neg: Bool, +res: U32) -> U32:
  match neg:
    case False{}:
      res
    case True{}:
      decode.neg32(res)

def decode.q17.div(+hh: U32, +ll: U32, neg: Bool) -> U32:
  +l2 = (ll + 65536 : U32)
  +h2 = (hh + decode.carry(ll, l2) : U32)
  decode.q17.sign2(neg, decode.q17.res(h2, l2))

def decode.q17.neg(pp: U32 & U32) -> U32:
  (h, l) = pp
  decode.q17.div(h, l, True{})

def decode.q17.pos(pos: Bool, +hh: U32, +ll: U32) -> U32:
  match pos:
    case True{}:
      decode.q17.div(hh, ll, False{})
    case False{}:
      decode.q17.neg(decode.neg64(hh, ll))

def decode.q17(+hh: U32, +ll: U32) -> U32:
  decode.q17.pos(U32.is_lt(hh, 2147483648), hh, ll)

def decode.dot.end(+lo: U32, +ah: U32, +ph: U32, +al: U32) -> U32:
  decode.q17((ah + ph + decode.carry(al, lo) : U32), lo)

def decode.dot(cs: List<&2, U32>, ks: List<&2, U32>, have: Bool, prod: U32 & U32, +ah: U32, +al: U32) -> U32:
  match cs:
    case Nil{}:
      match ks:
        case _ks:
          match have:
            case False{}:
              (_ph, _pl) = prod
              decode.q17(ah, al)
            case True{}:
              (ph, pl) = prod
              decode.dot.end((al + pl : U32), ah, ph, al)
    case c <> ct:
      match ks:
        case Nil{}:
          match have:
            case False{}:
              (_ph, _pl) = prod
              decode.q17(ah, al)
            case True{}:
              (ph, pl) = prod
              decode.dot.end((al + pl : U32), ah, ph, al)
        case k <> kt:
          match have:
            case False{}:
              (_ph, _pl) = prod
              decode.dot(ct, kt, True{}, decode.widemul(c, k), ah, al)
            case True{}:
              (+ph, +pl) = prod
              decode.dot(ct, kt, True{}, decode.widemul(c, k),
                (ah + ph + decode.carry(al, (al + pl : U32)) : U32), (al + pl : U32))

def decode.at.m(mm: Maybe<&2, U32>) -> U32:
  match mm:
    case Some{v}:
      v
    case None{}:
      0

def decode.at(xs: List<&2, U32>, +ii: U32) -> U32:
  decode.at.m(List.get(&2, U32, xs, U32.to_nat(ii)))

def decode.column(+cs: List<&2, U32>, +xx: U32) -> List<&2, U32>:
  +b = (xx * 8 : U32)
  [decode.at(cs, b), decode.at(cs, (b + 1 : U32)), decode.at(cs, (b + 2 : U32)),
    decode.at(cs, (b + 3 : U32)), decode.at(cs, (b + 4 : U32)), decode.at(cs, (b + 5 : U32)),
    decode.at(cs, (b + 6 : U32)), decode.at(cs, (b + 7 : U32))]

# one copy of each cosine column, reused for every row of the block
def decode.cols(+cs: List<&2, U32>) -> Cols:
  Cols{decode.column(cs, 0), decode.column(cs, 1), decode.column(cs, 2), decode.column(cs, 3),
    decode.column(cs, 4), decode.column(cs, 5), decode.column(cs, 6), decode.column(cs, 7)}

def decode.row8(+row: List<&2, U32>, +cols: Cols) -> List<&2, U32>:
  match cols:
    case Cols{+c0, +c1, +c2, +c3, +c4, +c5, +c6, +c7}:
      [decode.dot(row, c0, False{}, (0, 0), 0, 0), decode.dot(row, c1, False{}, (0, 0), 0, 0),
        decode.dot(row, c2, False{}, (0, 0), 0, 0), decode.dot(row, c3, False{}, (0, 0), 0, 0),
        decode.dot(row, c4, False{}, (0, 0), 0, 0), decode.dot(row, c5, False{}, (0, 0), 0, 0),
        decode.dot(row, c6, False{}, (0, 0), 0, 0), decode.dot(row, c7, False{}, (0, 0), 0, 0)]

def decode.cos() -> List<&2, U32>:
  [46341, 64277, 60547, 54491, 46341, 36410, 25080, 12785, 46341, 54491, 25080, 4294954511, 4294920955,
    4294903019, 4294906749, 4294930886, 46341, 36410, 4294942216, 4294903019, 4294920955, 12785, 60547, 54491,
    46341, 12785, 4294906749, 4294930886, 46341, 54491, 4294942216, 4294903019, 46341, 4294954511, 4294906749,
    36410, 46341, 4294912805, 4294942216, 64277, 46341, 4294930886, 4294942216, 64277, 4294920955, 4294954511,
    60547, 4294912805, 46341, 4294912805, 25080, 12785, 4294920955, 64277, 4294906749, 36410, 46341, 4294903019,
    60547, 4294912805, 46341, 4294930886, 25080, 4294954511]

def decode.pass(
  left: Nat,
  coeffs: List<&2, U32>,
  +cols: Cols,
  acc: List<&2, List<&2, U32>>
) -> List<&2, List<&2, U32>>:
  match left:
    case 0n:
      List.reverse(&2, List<&2, U32>, acc)
    case 1n+p:
      match coeffs:
        case a <> b <> c <> d <> e <> f <> g <> h <> rest:
          decode.pass(p, rest, cols, decode.row8([a, b, c, d, e, f, g, h], cols) <> acc)
        case _:
          List.reverse(&2, List<&2, U32>, acc)

def decode.col(+rows: List<&2, List<&2, U32>>, +xx: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match rows:
    case Nil{}:
      List.reverse(&2, U32, acc)
    case h <> t:
      decode.col(t, xx, decode.at(h, xx) <> acc)

def decode.backs(+rows: List<&2, List<&2, U32>>, +cols: Cols) -> List<&2, List<&2, U32>>:
  [decode.row8(decode.col(rows, 0, []), cols), decode.row8(decode.col(rows, 1, []), cols),
    decode.row8(decode.col(rows, 2, []), cols), decode.row8(decode.col(rows, 3, []), cols),
    decode.row8(decode.col(rows, 4, []), cols), decode.row8(decode.col(rows, 5, []), cols),
    decode.row8(decode.col(rows, 6, []), cols), decode.row8(decode.col(rows, 7, []), cols)]

def decode.rows.of(+backs: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  [decode.col(backs, 0, []), decode.col(backs, 1, []), decode.col(backs, 2, []),
    decode.col(backs, 3, []), decode.col(backs, 4, []), decode.col(backs, 5, []),
    decode.col(backs, 6, []), decode.col(backs, 7, [])]

def decode.flat.row(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      h <> decode.flat.row(t, acc)

def decode.flat(rows: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match rows:
    case Nil{}:
      Nil{}
    case h <> t:
      decode.flat.row(h, decode.flat(t))

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

def decode.level(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      List.reverse(&2, U32, acc)
    case h <> t:
      decode.level(t, decode.clamp8((h + 128 : U32)) <> acc)

def decode.zeros(nn: Nat, acc: List<&2, U32>) -> List<&2, U32>:
  match nn:
    case 0n:
      acc
    case 1n+p:
      decode.zeros(p, 0 <> acc)

def decode.idct(nat: List<&2, U32>) -> List<&2, U32>:
  +cols = decode.cols(decode.cos())
  decode.level(decode.flat(decode.rows.of(decode.backs(decode.pass(8n, nat, cols, []), cols))), [])

def decode.huff0() -> Huff:
  Huff{[], [], []}

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

def decode.rev3(ac: List<&2, U32>, al: List<&2, U32>, ay: List<&2, U32>) -> Huff:
  Huff{List.reverse(&2, U32, ac), List.reverse(&2, U32, al), List.reverse(&2, U32, ay)}

def decode.canon.shift(+len: U32, +code: U32) -> U32:
  match len:
    case 0:
      code
    case _:
      U32.shl(code)

def decode.canon(
  left: Nat,
  tick: Nat,
  counts: List<&2, U32>,
  symbols: List<&2, U32>,
  +code: U32,
  +len: U32,
  ac: List<&2, U32>,
  al: List<&2, U32>,
  ay: List<&2, U32>
) -> Huff:
  match left:
    case 0n:
      match tick:
        case _t:
          match counts:
            case _cs:
              match symbols:
                case _ys:
                  decode.rev3(ac, al, ay)
    case 1n+p:
      match tick:
        case 0n:
          match counts:
            case Nil{}:
              match symbols:
                case _ys:
                  decode.rev3(ac, al, ay)
            case n <> nt:
              decode.canon(p, U32.to_nat(n), nt, symbols, decode.canon.shift(len, code), (len + 1 : U32), ac, al, ay)
        case 1n+q:
          match counts:
            case cs:
              match symbols:
                case Nil{}:
                  decode.huff0()
                case s <> st:
                  decode.canon(p, q, cs, st, (code + 1 : U32), len, code <> ac, len <> al, s <> ay)

def decode.index.keep(+hh: U32, +ii: U32) -> U32:
  (ii + U32.and(hh, 0) : U32)

def decode.index.add(eq: Bool, +ii: U32) -> U32:
  match eq:
    case True{}:
      ii
    case False{}:
      (ii + 1 : U32)

def decode.index(xs: List<&2, U32>, eq: Bool, +hh: U32, +want: U32, +ii: U32) -> U32:
  match xs:
    case Nil{}:
      match eq:
        case True{}:
          decode.index.keep(hh, ii)
        case False{}:
          decode.index.keep(hh, 0)
    case +n <> t:
      match eq:
        case True{}:
          decode.index.keep(n, decode.index.keep(hh, ii))
        case False{}:
          decode.index(t, U32.is_eq(n, want), n, want, decode.index.add(U32.is_eq(n, want), decode.index.keep(hh, ii)))

def decode.look.pref(tail: Maybe<&2, U32>, eqc: Bool, eql: Bool, +ss: U32) -> Maybe<&2, U32>:
  match tail:
    case Some{v}:
      Some{v}
    case None{}:
      match eqc:
        case False{}:
          None{}
        case True{}:
          match eql:
            case True{}:
              Some{ss}
            case False{}:
              None{}

def decode.look(
  codes: List<&2, U32>,
  lens: List<&2, U32>,
  syms: List<&2, U32>,
  +code: U32,
  +len: U32
) -> Maybe<&2, U32>:
  match codes:
    case Nil{}:
      match lens:
        case _ls:
          match syms:
            case _ss:
              None{}
    case c <> ct:
      match lens:
        case Nil{}:
          match syms:
            case _ss:
              None{}
        case l <> lt:
          match syms:
            case Nil{}:
              None{}
            case s <> st:
              decode.look.pref(decode.look(ct, lt, st, code, len), U32.is_eq(c, code), U32.is_eq(l, len), s)

def decode.nbits(left: Nat, eq: Bool, xs: List<&2, U32>, +nn: U32, +buf: U32, +ok: U32, +acc: U32) -> Bits & U32:
  match left:
    case 0n:
      (Bits{nn, ok, buf, xs}, acc)
    case 1n+p:
      match eq:
        case False{}:
          decode.nbits(p, U32.is_eq((nn - 1 : U32), 0), xs, (nn - 1 : U32), U32.and(U32.shl(buf), 255), ok,
            U32.or(U32.shl(acc), U32.shrn(buf, 7n)))
        case True{}:
          match xs:
            case Nil{}:
              decode.nbits(p, False{}, [], 7, 0, 0, U32.shl(acc))
            case 255 <> rest:
              match rest:
                case Nil{}:
                  decode.nbits(p, False{}, [], 7, 0, 0, U32.shl(acc))
                case 0 <> more:
                  decode.nbits(p, False{}, more, 7, 254, ok, U32.or(U32.shl(acc), 1))
                case 255 <> more:
                  decode.nbits(Succ{p}, True{}, more, 0, 0, ok, acc)
                case _m <> more:
                  decode.nbits(p, False{}, more, 7, 0, 0, U32.shl(acc))
            case +b <> rest:
              decode.nbits(p, False{}, rest, 7, U32.and(U32.shl(b), 255), ok, U32.or(U32.shl(acc), U32.shrn(b, 7n)))

def decode.one(bits: Bits) -> Bits & U32:
  match bits:
    case Bits{+n, +ok, +buf, xs}:
      decode.nbits(1n, U32.is_eq(n, 0), xs, n, buf, ok, 0)

def decode.ask.bit(tab: Huff, got: Bits & U32, +code: U32, +len: U32) -> Ask:
  match tab:
    case Huff{+codes, +lens, +syms}:
      match got:
        case (bits, +bit):
          Ask{decode.look(codes, lens, syms, U32.or(U32.shl(code), bit), (len + 1 : U32)), U32.or(U32.shl(code), bit),
            (len + 1 : U32), bits}

def decode.ask(bits: Bits, +code: U32, +len: U32, tab: Huff) -> Ask:
  decode.ask.bit(tab, decode.one(bits), code, len)

def decode.huff.use(hit: Maybe<&2, U32>, bits: Bits) -> Hit:
  match hit:
    case Some{+s}:
      match bits:
        case Bits{+n, +ok, +buf, xs}:
          Hit{s, Bits{n, ok, buf, xs}, ok}
    case None{}:
      Hit{0, bits, 0}

def decode.huff(left: Nat, ask: Ask, +tab: Huff) -> Hit:
  match left:
    case 0n:
      match ask:
        case Ask{hit, _code, _len, bits}:
          decode.huff.use(hit, bits)
    case 1n+p:
      match ask:
        case Ask{hit, +code, +len, bits}:
          match hit:
            case Some{+s}:
              decode.huff.use(Some{s}, bits)
            case None{}:
              decode.huff(p, decode.ask(bits, code, len, tab), tab)

def decode.bits.of(bits: Bits) -> Nat & U32 & List<&2, U32> & U32 & U32:
  match bits:
    case Bits{+n, +ok, +buf, xs}:
      (0n, n, xs, buf, ok)

def decode.read.n(+cat: U32, bits: Bits) -> Bits & U32:
  match bits:
    case Bits{+n, +ok, +buf, xs}:
      decode.nbits(U32.to_nat(cat), U32.is_eq(n, 0), xs, n, buf, ok, 0)

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

def decode.ac.stored(full: Bool, +kk: U32, zz: List<&2, U32>, bits: Bits, +ok: U32) -> Ac:
  match full:
    case True{}:
      Ac{kk, zz, bits, 1, ok}
    case False{}:
      Ac{kk, zz, bits, 0, ok}

def decode.ac.store(got: Bits & U32, +sz: U32, +nk: U32, zz: List<&2, U32>, +ok: U32) -> Ac:
  (bits, mag) = got
  +n2 = (nk + 1 : U32)
  decode.ac.stored(U32.is_eq(n2, 64), n2, List.set(&2, U32, zz, U32.to_nat(nk), decode.extend(sz, mag)), bits, ok)

def decode.ac.bad(zz: List<&2, U32>, bits: Bits) -> Ac:
  Ac{64, zz, bits, 1, 0}

def decode.ac.run.b(zzz: Bool, over: Bool, +sz: U32, +nk: U32, bits: Bits, zz: List<&2, U32>, +ok: U32) -> Ac:
  match zzz:
    case True{}:
      decode.ac.bad(zz, bits)
    case False{}:
      match over:
        case True{}:
          decode.ac.bad(zz, bits)
        case False{}:
          decode.ac.store(decode.read.n(sz, bits), sz, nk, zz, ok)

def decode.ac.run(+sym: U32, bits: Bits, +kk: U32, zz: List<&2, U32>, +ok: U32) -> Ac:
  +sz = U32.and(sym, 15)
  +nk = (kk + U32.shrn(sym, 4n) : U32)
  decode.ac.run.b(U32.is_eq(sz, 0), U32.is_ge(nk, 64), sz, nk, bits, zz, ok)

def decode.ac.zrl.eq(eq: Bool, zz: List<&2, U32>, bits: Bits, +ok: U32) -> Ac:
  match eq:
    case True{}:
      Ac{64, zz, bits, 1, ok}
    case False{}:
      Ac{64, zz, bits, 1, 0}

def decode.ac.zrl.k(more: Bool, +nk: U32, zz: List<&2, U32>, bits: Bits, +ok: U32) -> Ac:
  match more:
    case True{}:
      Ac{nk, zz, bits, 0, ok}
    case False{}:
      decode.ac.zrl.eq(U32.is_eq(nk, 64), zz, bits, ok)

def decode.ac.zrl(+kk: U32, zz: List<&2, U32>, bits: Bits, +ok: U32) -> Ac:
  decode.ac.zrl.k(U32.is_lt((kk + 16 : U32), 64), (kk + 16 : U32), zz, bits, ok)

def decode.ac.sym(+sym: U32, bits: Bits, +kk: U32, zz: List<&2, U32>, +ok: U32) -> Ac:
  match sym:
    case 0:
      Ac{kk, zz, bits, 1, ok}
    case 240:
      decode.ac.zrl(kk, zz, bits, ok)
    case _:
      decode.ac.run(sym, bits, kk, zz, ok)

def decode.ac.step(hit: Hit, +kk: U32, zz: List<&2, U32>, +ok: U32) -> Ac:
  match hit:
    case Hit{+sym, bits, +hok}:
      decode.ac.sym(sym, bits, kk, zz, (ok * hok : U32))

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
            case Ac{k, zz, bits, _d, _o}:
              Ac{k, zz, bits, 1, 0}

def decode.ac(left: Nat, ac: Ac, +tab: Huff) -> Ac:
  match left:
    case 0n:
      match ac:
        case Ac{+k, _zz, _bits, +done, _ok}:
          decode.ac.full(U32.is_eq(done, 1), U32.is_lt(k, 64), ac)
    case 1n+p:
      match ac:
        case Ac{+k, +zz, bits, +done, +ok}:
          match done:
            case 0:
              decode.ac(p, decode.ac.step(decode.huff(16n, Ask{None{}, 0, 0, bits}, tab), k, zz, ok), tab)
            case _:
              match tab:
                case Huff{_c, _l, _s}:
                  ac

def decode.zig() -> List<&2, U32>:
  [0, 1, 8, 16, 9, 2, 3, 10, 17, 24, 32, 25, 18, 11, 4, 5, 12, 19, 26, 33, 40, 48, 41, 34, 27, 20, 13, 6, 7,
    14, 21, 28, 35, 42, 49, 56, 57, 50, 43, 36, 29, 22, 15, 23, 30, 37, 44, 51, 58, 59, 52, 45, 38, 31, 39, 46,
    53, 60, 61, 54, 47, 55, 62, 63]

def decode.nat(zz: List<&2, U32>, quant: List<&2, U32>, zig: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match zz:
    case Nil{}:
      match quant:
        case _q:
          match zig:
            case _g:
              acc
    case z <> zt:
      match quant:
        case Nil{}:
          match zig:
            case _g:
              acc
        case q <> qt:
          match zig:
            case Nil{}:
              acc
            case g <> gt:
              decode.nat(zt, qt, gt, List.set(&2, U32, acc, U32.to_nat(g), (z * q : U32)))

def decode.block.ac(ac: Ac, +pred: U32, quant: List<&2, U32>, +qok: U32) -> Blk:
  match ac:
    case Ac{_k, +zz, bits, _done, +ok}:
      Blk{decode.idct(decode.nat(zz, quant, decode.zig(), decode.zeros(64n, []))), bits, pred, (ok * qok : U32)}

def decode.block.diff(
  got: Bits & U32,
  +cat: U32,
  +pred: U32,
  +ok: U32,
  ac: Huff,
  quant: List<&2, U32>,
  +qok: U32
) -> Blk:
  (bits, mag) = got
  +dc = (pred + decode.extend(cat, mag) : U32)
  decode.block.ac(decode.ac(63n, Ac{1, dc <> decode.zeros(63n, []), bits, 0, ok}, ac), dc, quant, qok)

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
  decode.block.dc(decode.huff(16n, Ask{None{}, 0, 0, bits}, dc), pred, ac, quant, decode.qok(quant))

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
        case _:
          q3

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
                        decode.q.get(tabs, decode.at(tq, decode.index(ids, False{}, 0, decode.at(sids, c), 0))))

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
  +fi = decode.index(ids, False{}, 0, decode.at(sids, comp), 0)
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
  +fi = decode.index(ids, False{}, 0, decode.at(sids, comp), 0)
  +hi = decode.at(hs, fi)
  +vi = decode.at(vs, fi)
  +pw = U32.div(hmax, decode.geom.nz(hi))
  +ph = U32.div(vmax, decode.geom.nz(vi))
  +bx = U32.mod(bi, decode.geom.nz(hi))
  +by = U32.div(bi, decode.geom.nz(vi))
  Geom{(mx * hmax * 8 + bx * 8 * pw : U32), (my * vmax * 8 + by * 8 * ph : U32), pw, ph, ww, hh}

def decode.geom(ctrl: Ctrl, frame: Frame, scan: Scan) -> Geom:
  match ctrl:
    case Ctrl{+comp, +bi, +mx, +my, _mcu, _rst}:
      match frame:
        case Frame{+w, +h, _nf, +ids, +hs, +vs, _tq, +hmax, +vmax}:
          match scan:
            case Scan{_ns, +sids, _td, _ta, _ss, _se, _ah}:
              decode.geom.go(comp, bi, mx, my, w, h, hmax, vmax, sids, ids, hs, vs)

def decode.cursor.py(more: Bool, +kk: U32, +py: U32) -> Cursor:
  match more:
    case True{}:
      Cursor{kk, 0, (py + 1 : U32)}
    case False{}:
      Cursor{(kk + 1 : U32), 0, 0}

def decode.cursor.px(more: Bool, +kk: U32, +px: U32, +py: U32, +ph: U32) -> Cursor:
  match more:
    case True{}:
      Cursor{kk, (px + 1 : U32), py}
    case False{}:
      decode.cursor.py(U32.is_lt((py + 1 : U32), ph), kk, py)

def decode.cursor(+kk: U32, +px: U32, +py: U32, +pw: U32, +ph: U32) -> Cursor:
  decode.cursor.px(U32.is_lt((px + 1 : U32), pw), kk, px, py, ph)

def decode.splat.n(+pw: U32, +ph: U32) -> Nat:
  U32.to_nat(((pw * ph : U32) * 64 : U32))

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

def decode.splat.put(
  plane: Array<U32>,
  +kk: U32,
  +px: U32,
  +py: U32,
  samples: List<&2, U32>,
  +ox: U32,
  +oy: U32,
  +pw: U32,
  +ph: U32,
  +ww: U32,
  +hh: U32
) -> Array<U32>:
  +x = (ox + U32.mod(kk, 8) * pw + px : U32)
  +y = (oy + U32.div(kk, 8) * ph + py : U32)
  decode.splat.in(U32.is_lt(x, ww), U32.is_lt(y, hh), plane, x, y, ww, decode.at(samples, kk))

def decode.splat(
  left: Nat,
  cur: Cursor,
  +samples: List<&2, U32>,
  plane: Array<U32>,
  +ox: U32,
  +oy: U32,
  +pw: U32,
  +ph: U32,
  +ww: U32,
  +hh: U32
) -> Array<U32>:
  match left:
    case 0n:
      match cur:
        case Cursor{_k, _px, _py}:
          +_s = decode.drop(samples)
          plane
    case 1n+p:
      match cur:
        case Cursor{+k, +px, +py}:
          decode.splat(p, decode.cursor(k, px, py, pw, ph), samples,
            decode.splat.put(plane, k, px, py, samples, ox, oy, pw, ph, ww, hh), ox, oy, pw, ph, ww, hh)

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
      +_s = decode.drop(samples)
      plane
    case True{}:
      decode.splat(decode.splat.n(pw, ph), Cursor{0, 0, 0}, samples, plane, ox, oy, pw, ph, ww, hh)

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

def decode.sink.pair(pp: Array<U32> & U32) -> U32:
  (a, v) = pp
  U32.or(decode.sink(a), U32.and(v, 0))

def decode.depth(+nn: U32) -> Nat:
  match nn:
    case 0:
      0n
    case _:
      U32.log2((U32.shl(nn) - 1 : U32))

def decode.plane(+nn: U32) -> Array<U32>:
  Array.new(U32, decode.depth(nn), 0)

def decode.emit(left: Nat, got: Array<U32> & U32, +ii: U32, acc: List<&2, U32>, fresh: Bool) -> List<&2, U32>:
  match left:
    case 0n:
      match got:
        case (a, +v):
          match ii:
            case _j:
              match acc:
                case ys:
                  match fresh:
                    case False{}:
                      +_a = decode.sink(a)
                      +_v = (v - v : U32)
                      List.reverse(&2, U32, ys)
                    case True{}:
                      +_a = decode.sink(a)
                      List.reverse(&2, U32, v <> ys)
    case 1n+p:
      match got:
        case (a, +v):
          match ii:
            case +j:
              match acc:
                case ys:
                  match fresh:
                    case False{}:
                      +_v = (v - v : U32)
                      decode.emit(p, Array.get(U32, a, j), (j + 1 : U32), ys, True{})
                    case True{}:
                      decode.emit(p, Array.get(U32, a, j), (j + 1 : U32), v <> ys, True{})

def decode.round.s(ss: U32, +prod: U32) -> U32:
  match ss:
    case 0:
      U32.shrn((prod + 32768 : U32), 16n)
    case _:
      decode.neg32(U32.shrn((decode.neg32(prod) + 32768 : U32), 16n))

def decode.round(+prod: U32) -> U32:
  decode.round.s(decode.sign(prod), prod)

# YCbCr to a packed sample, (R << 16) | (G << 8) | B, per JFIF T.871
def rgb(+yy: U32, +cb: U32, +cr: U32) -> U32:
  +cbd = (cb - 128 : U32)
  +crd = (cr - 128 : U32)
  +r = decode.clamp8((yy + decode.round((crd * 91881 : U32)) : U32))
  +g = decode.clamp8((yy - decode.round((cbd * 22553 : U32)) - decode.round((crd * 46802 : U32)) : U32))
  +b = decode.clamp8((yy + decode.round((cbd * 116130 : U32)) : U32))
  U32.or(U32.or(U32.shln(r, 16n), U32.shln(g, 8n)), b)

def decode.rgbpass.end(got: Array<U32> & U32, out: Array<U32>) -> Array<U32>:
  +_u = decode.sink.pair(got)
  out

def decode.rgbpass(
  left: Nat,
  +phase: U32,
  got: Array<U32> & U32,
  +ii: U32,
  yy: Array<U32>,
  cb: Array<U32>,
  cr: Array<U32>,
  out: Array<U32>,
  +yv: U32,
  +cbv: U32
) -> Array<U32>:
  match left:
    case 0n:
      +_y = decode.sink(yy)
      +_b = decode.sink(cb)
      +_r = decode.sink(cr)
      decode.rgbpass.end(got, out)
    case 1n+p:
      match phase:
        case 0:
          +_u = decode.sink.pair(got)
          decode.rgbpass(p, 1, Array.get(U32, yy, ii), ii, cb, cr, out, decode.plane(1), 0, 0)
        case 1:
          (arr, v) = got
          decode.rgbpass(p, 2, Array.get(U32, yy, ii), ii, arr, cb, cr, out, v, 0)
        case 2:
          (arr, v) = got
          decode.rgbpass(p, 3, Array.get(U32, cb, ii), ii, yy, arr, cr, out, yv, v)
        case _:
          (arr, +v) = got
          +_d = decode.sink(out)
          decode.rgbpass(p, 0, (decode.plane(1), 0), (ii + 1 : U32), yy, cb, arr, Array.set(U32, cr, ii, rgb(yv, cbv,
            v)), 0, 0)

def decode.done.drop(yy: Array<U32>, cb: Array<U32>, cr: Array<U32>) -> Maybe<&2, Pic>:
  +_a = decode.sink(yy)
  +_b = decode.sink(cb)
  +_c = decode.sink(cr)
  None{}

def decode.done.gray(+ww: U32, +hh: U32, yy: Array<U32>, cb: Array<U32>, cr: Array<U32>) -> Maybe<&2, Pic>:
  +_b = decode.sink(cb)
  +_c = decode.sink(cr)
  Some{Pic{ww, hh, decode.emit(U32.to_nat((ww * hh : U32)), (yy, 0), 0, [], False{})}}

def decode.done.color(+ww: U32, +hh: U32, yy: Array<U32>, cb: Array<U32>, cr: Array<U32>) -> Maybe<&2, Pic>:
  +n = (ww * hh : U32)
  out = decode.rgbpass(U32.to_nat((n * 4 : U32)), 0, (decode.plane(1), 0), 0, yy, cb, cr, decode.plane(n), 0, 0)
  Some{Pic{ww, hh, decode.emit(U32.to_nat(n), (out, 0), 0, [], False{})}}

def decode.done.nf(+nf: U32, +ww: U32, +hh: U32, yy: Array<U32>, cb: Array<U32>, cr: Array<U32>) -> Maybe<&2, Pic>:
  match nf:
    case 1:
      decode.done.gray(ww, hh, yy, cb, cr)
    case 3:
      decode.done.color(ww, hh, yy, cb, cr)
    case _:
      decode.done.drop(yy, cb, cr)

def decode.done(+ok: U32, frame: Frame, yy: Array<U32>, cb: Array<U32>, cr: Array<U32>) -> Maybe<&2, Pic>:
  match ok:
    case 0:
      decode.done.drop(yy, cb, cr)
    case _:
      match frame:
        case Frame{+w, +h, +nf, _ids, _hs, _vs, _tq, _hmax, _vmax}:
          decode.done.nf(nf, w, h, yy, cb, cr)

def decode.adv.ctrl(adv: Adv) -> Ctrl:
  match adv:
    case Adv{ctrl, _due, _expect}:
      ctrl

def decode.adv.duef(adv: Adv) -> U32:
  match adv:
    case Adv{_ctrl, +due, _expect}:
      due

def decode.blocks(
  left: Nat,
  blk: Blk,
  +ctrl: Ctrl,
  +preds: Preds,
  +frame: Frame,
  +scan: Scan,
  +tabs: Tabs,
  +ri: U32,
  yy: Array<U32>,
  cb: Array<U32>,
  cr: Array<U32>,
  +ok: U32
) -> Maybe<&2, Pic>:
  match left:
    case 0n:
      match blk:
        case Blk{+samples, _bits, _pred, +bok}:
          decode.done((ok * bok : U32), frame,
            decode.paint.use(decode.geom(ctrl, frame, scan), U32.is_eq(decode.ctrl.comp(ctrl), 0), samples, yy),
            decode.paint.use(decode.geom(ctrl, frame, scan), U32.is_eq(decode.ctrl.comp(ctrl), 1), samples, cb),
            decode.paint.use(decode.geom(ctrl, frame, scan), U32.is_eq(decode.ctrl.comp(ctrl), 2), samples, cr))
    case 1n+p:
      match blk:
        case Blk{+samples, +bits, +pred, +bok}:
          match ctrl:
            case Ctrl{+comp, _bi, _mx, _my, _mcu, _rst}:
              decode.blocks(p, decode.block.next(bits, preds, pred, ctrl, frame, scan, tabs, ri),
                decode.adv.ctrl(decode.adv(ctrl, frame, scan, ri)),
                decode.preds.next(decode.adv.duef(decode.adv(ctrl, frame, scan, ri)), preds, comp, pred), frame, scan,
                tabs, ri, decode.paint.use(decode.geom(ctrl, frame, scan), U32.is_eq(comp, 0), samples, yy),
                decode.paint.use(decode.geom(ctrl, frame, scan), U32.is_eq(comp, 1), samples, cb),
                decode.paint.use(decode.geom(ctrl, frame, scan), U32.is_eq(comp, 2), samples, cr), (ok * bok : U32))

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
  yy: Array<U32>,
  cb: Array<U32>,
  cr: Array<U32>
) -> Maybe<&2, Pic>:
  match nn:
    case 0n:
      decode.done.drop(yy, cb, cr)
    case 1n+p:
      decode.blocks(p, decode.block.of(bits, 0, decode.pred.zero(), frame, scan, tabs), Ctrl{0, 0, 0, 0, 0, 0},
        decode.pred.zero(), frame, scan, tabs, ri, yy, cb, cr, 1)

def decode.run.n(
  empty: Bool,
  +ww: U32,
  +hh: U32,
  frame: Frame,
  scan: Scan,
  tabs: Tabs,
  ent: List<&2, U32>,
  +ri: U32
) -> Maybe<&2, Pic>:
  match empty:
    case True{}:
      None{}
    case False{}:
      match frame:
        case Frame{_w, _h, _nf, _ids, +hs, +vs, _tq, +hmax, +vmax}:
          +n = (decode.ceil(ww, (hmax * 8 : U32)) * decode.ceil(hh, (vmax * 8 : U32)) * decode.blocks.sum(hs, vs, 0) :
            U32)
          decode.start(U32.to_nat(n), Bits{0, 1, 0, ent}, frame, scan, tabs, ri, decode.plane((ww * hh : U32)),
            decode.plane((ww * hh : U32)), decode.plane((ww * hh : U32)))

def decode.run(frame: Frame, scan: Scan, tabs: Tabs, ent: List<&2, U32>, +ri: U32) -> Maybe<&2, Pic>:
  match frame:
    case Frame{+w, +h, _nf, _ids, _hs, _vs, _tq, _hmax, _vmax}:
      decode.run.n(Bool.or(U32.is_eq(w, 0), U32.is_eq(h, 0)), w, h, frame, scan, tabs, ent, ri)

def decode.finish.ok(
  ok1: Bool,
  ok2: Bool,
  frame: Frame,
  scan: Scan,
  tabs: Tabs,
  ent: List<&2, U32>,
  +ri: U32
) -> Maybe<&2, Pic>:
  match ok1:
    case False{}:
      None{}
    case True{}:
      match ok2:
        case False{}:
          None{}
        case True{}:
          decode.run(frame, scan, tabs, List.reverse(&2, U32, ent), ri)

def decode.finish.ph(
  phase: Phase,
  frame: Frame,
  scan: Scan,
  tabs: Tabs,
  ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> Maybe<&2, Pic>:
  match phase:
    case Stop{}:
      decode.finish.ok(U32.is_eq(kind, 1), U32.is_eq(bad, 0), frame, scan, tabs, ent, ri)
    case _:
      None{}

def decode.finish(st: St) -> Maybe<&2, Pic>:
  match st:
    case St{+phase, +frame, +scan, +tabs, +ent, +ri, +kind, +bad}:
      decode.finish.ph(phase, frame, scan, tabs, ent, ri, kind, bad)

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

def decode.fac.ok(+hh: U32) -> U32:
  match hh:
    case 1:
      1
    case 2:
      1
    case 4:
      1
    case _:
      0

def decode.fac.bad(+hh: U32, +vv: U32, +bad: U32) -> U32:
  (bad + (1 - decode.fac.ok(hh) : U32) + (1 - decode.fac.ok(vv) : U32) : U32)

def decode.nf.ok(+nf: U32) -> U32:
  match nf:
    case 1:
      1
    case 3:
      1
    case _:
      0

def decode.u16(+hi: U32, +lo: U32) -> U32:
  U32.or(U32.shln(hi, 8n), lo)

def decode.comps.rev(cc: Comps) -> Comps:
  match cc:
    case Comps{ids, hs, vs, tq, +bad}:
      Comps{List.reverse(&2, U32, ids), List.reverse(&2, U32, hs), List.reverse(&2, U32, vs),
        List.reverse(&2, U32, tq), bad}

def decode.read.cs(
  left: Nat,
  xs: List<&2, U32>,
  ids: List<&2, U32>,
  hs: List<&2, U32>,
  vs: List<&2, U32>,
  tqs: List<&2, U32>,
  +bad: U32
) -> Comps:
  match left:
    case 0n:
      match xs:
        case _rest:
          decode.comps.rev(Comps{ids, hs, vs, tqs, bad})
    case 1n+p:
      match xs:
        case id <> +hv <> tq <> rest:
          +hsamp = U32.shrn(hv, 4n)
          +vsamp = U32.and(hv, 15)
          decode.read.cs(p, rest, id <> ids, hsamp <> hs, vsamp <> vs, tq <> tqs, decode.fac.bad(hsamp, vsamp, bad))
        case _:
          Comps{[], [], [], [], 1}

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
    case Comps{+ids, +hs, +vs, +tq, +cbad}:
      decode.read.sof.ok(U32.is_eq((bad + cbad + (1 - decode.nf.ok(nf) : U32) : U32), 0),
        U32.is_eq(decode.vmax(hs, 0), 0), ww, hh, nf, ids, hs, vs, tq, scan, tabs, ent, ri, kind)

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
    case 8 <> hh <> hl <> wh <> wl <> +nf <> rest:
      decode.read.sof.f(decode.read.cs(U32.to_nat(nf), rest, [], [], [], [], 0), decode.u16(wh, wl),
        decode.u16(hh, hl), nf, scan, tabs, ent, ri, kind, bad)
    case _:
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

def decode.read.dqt(
  xs: List<&2, U32>,
  ok: Bool,
  phase: Nat,
  +id: U32,
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
              decode.read.dqt(rest, U32.is_eq(U32.shrn(b, 4n), 0), 64n, U32.and(b, 15), [], frame, scan, tabs, ent,
                ri, kind, bad)
            case 1n+p:
              match p:
                case 0n:
                  decode.read.dqt(rest, True{}, 0n, 0, [], frame, scan,
                    decode.q.put(tabs, id, List.reverse(&2, U32, b <> acc)), ent, ri, kind, bad)
                case _:
                  decode.read.dqt(rest, True{}, p, id, b <> acc, frame, scan, tabs, ent, ri, kind, bad)

def decode.sum.counts(xs: List<&2, U32>, +nn: U32) -> U32:
  match xs:
    case Nil{}:
      nn
    case h <> t:
      decode.sum.counts(t, (nn + h : U32))

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
                  St{Seek{}, frame, scan, decode.huff.put(tabs, cls, id, decode.canon(272n, 0n, counts, [], 0, 0, [],
                    [], [])), ent, ri, kind, bad}
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
                      decode.read.dht(rest, True{}, True{}, U32.to_nat(decode.sum.counts(List.reverse(&2, U32,
                        b <> counts), 0)), cls, id, List.reverse(&2, U32, b <> counts), [], frame, scan, tabs, ent, ri,
                        kind, bad)
                    case _:
                      +_s = decode.drop(syms)
                      decode.read.dht(rest, True{}, False{}, p, cls, id, b <> counts, [], frame, scan, tabs, ent, ri,
                        kind, bad)
            case True{}:
              match phase:
                case 0n:
                  +_n = decode.drop(rest)
                  +_b = (b - b : U32)
                  +_s = decode.drop(syms)
                  St{Seek{}, frame, scan, decode.huff.put(tabs, cls, id, decode.canon(272n, 0n, counts, [], 0, 0, [],
                    [], [])), ent, ri, kind, bad}
                case 1n+p:
                  match p:
                    case 0n:
                      decode.read.dht(rest, True{}, False{}, 0n, 0, 0, [], [], frame, scan, decode.huff.put(tabs, cls,
                        id, decode.canon(272n, 0n, counts, List.reverse(&2, U32, b <> syms), 0, 0, [], [], [])), ent,
                        ri, kind, bad)
                    case _:
                      decode.read.dht(rest, True{}, True{}, p, cls, id, counts, b <> syms, frame, scan, tabs, ent, ri,
                        kind, bad)

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
      decode.read.sos.ok(U32.is_eq(ss, 0), U32.is_eq(se, 63), U32.is_eq(ah, 0), sids, td, ta, ns, frame, tabs, ent,
        ri, kind, bad)
    case _:
      St{Stop{}, frame, decode.scan0(), tabs, ent, ri, kind, 1}

def decode.read.sos.cs(
  left: Nat,
  xs: List<&2, U32>,
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
      decode.read.sos.end(xs, sids, td, ta, ns, frame, tabs, ent, ri, kind, bad)
    case 1n+p:
      match xs:
        case id <> +tdta <> rest:
          decode.read.sos.cs(p, rest, id <> sids, U32.shrn(tdta, 4n) <> td, U32.and(tdta, 15) <> ta, ns, frame, tabs,
            ent, ri, kind, bad)
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
      decode.read.sos.cs(U32.to_nat(ns), rest, [], [], [], ns, frame, tabs, ent, ri, kind, bad)
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

def decode.read.app0.den(
  xz: Bool,
  yz: Bool,
  frame: Frame,
  scan: Scan,
  tabs: Tabs,
  ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> St:
  match xz:
    case True{}:
      St{Stop{}, frame, scan, tabs, ent, ri, kind, 1}
    case False{}:
      match yz:
        case True{}:
          St{Stop{}, frame, scan, tabs, ent, ri, kind, 1}
        case False{}:
          St{Seek{}, frame, scan, tabs, ent, ri, kind, bad}

def decode.read.app0(
  xs: List<&2, U32>,
  frame: Frame,
  scan: Scan,
  tabs: Tabs,
  ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> St:
  match xs:
    case 74 <> 70 <> 73 <> 70 <> 0 <> _maj <> _min <> _u <> xh <> xl <> yh <> yl <> _xt <> _yt <> _rest:
      decode.read.app0.den(U32.is_eq(decode.u16(xh, xl), 0), U32.is_eq(decode.u16(yh, yl), 0), frame, scan, tabs,
        ent, ri, kind, bad)
    case _:
      St{Seek{}, frame, scan, tabs, ent, ri, kind, bad}

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
    case 196:
      decode.read.dht(xs, True{}, False{}, 0n, 0, 0, [], [], frame, scan, tabs, ent, ri, kind, bad)
    case 218:
      decode.read.sos(xs, frame, tabs, ent, ri, kind, bad)
    case 219:
      decode.read.dqt(xs, True{}, 0n, 0, [], frame, scan, tabs, ent, ri, kind, bad)
    case 221:
      decode.read.dri(xs, frame, scan, tabs, ent, kind, bad)
    case 224:
      decode.read.app0(xs, frame, scan, tabs, ent, ri, kind, bad)
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
      St{Stop{}, frame, scan, tabs, ent, ri, kind, 1}

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
          St{Stop{}, frame, scan, tabs, ent, ri, kind, 1}
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
      match bb:
        case 255:
          St{EntFF{}, frame, scan, tabs, ent, ri, kind, bad}
        case _:
          St{Ent{}, frame, scan, tabs, bb <> ent, ri, kind, bad}
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

# the JPEG start-of-image marker, FF D8
def soi() -> List<&2, U32>:
  [255, 216]

# the JPEG end-of-image marker, FF D9
def eoi() -> List<&2, U32>:
  [255, 217]

# baseline JPEG bytes, or none when the frame is not sequential Huffman
def decode(bytes: List<&2, U32>) -> Maybe<&2, Pic>:
  decode.finish(decode.walk(bytes, decode.st0()))
