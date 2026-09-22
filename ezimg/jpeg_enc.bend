# ezimg: baseline JPEG encode. Sequential 8-bit Huffman (SOF0) and JFIF APP0.
# Colour is 4:4:4 YCbCr, no subsampling: one 8 by 8 block per component per MCU.
# Samples are packed RGB, (R << 16) | (G << 8) | B, the same layout decode returns.
# Quantisation steps are all 1, so an integer coefficient is kept whole.
# The forward DCT (T.81 A.3.3) contracts each axis with a frequency column of
# the cosine matrix. Frequency u lives at indices x*8+u.
# Both components share the Annex K luminance Huffman tables.
# A neutral solid (R = G = B = 128) is an all-zero block and round-trips exactly.
# Other colours are lossy. Progressive and arithmetic frames are not written.
# Width and height must sit in 1..65535; anything else is SOI then EOI.

import Base
import ./jpeg.bend as Jpeg

# bytes emitted so far (newest first), the open byte, and how many bits it holds
type Put is Data:
  Put{out: List<&2, U32>, buf: U32, n: U32}

# one Huffman table: canonical codes beside their lengths and symbols
type Tab is Data:
  Tab{codes: List<&2, U32>, lens: List<&2, U32>, syms: List<&2, U32>}

# the cosine matrix, zigzag, quant table, and the DC and AC Huffman tables
type Ctx is Data:
  Ctx{cs: List<&2, U32>, zig: List<&2, U32>, quant: List<&2, U32>, dc: Tab, ac: Tab}

def encode.join(a: List<&2, U32>, b: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, a, b)

def encode.len(xs: List<&2, U32>) -> U32:
  Jpeg.decode.nlist(xs, 0)

def encode.seg(+mark: U32, +body: List<&2, U32>) -> List<&2, U32>:
  +n = (encode.len(body) + 2 : U32)
  255 <> (mark <> (U32.shrn(n, 8n) <> (U32.and(n, 255) <> body)))

def encode.app0() -> List<&2, U32>:
  encode.seg(224, [74, 70, 73, 70, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0])

def encode.quant() -> List<&2, U32>:
  List.replicate(U32, 64n, 1)

def encode.dqt() -> List<&2, U32>:
  encode.seg(219, 0 <> encode.quant())

def encode.sofbody(+w: U32, +h: U32) -> List<&2, U32>:
  [8, U32.shrn(h, 8n), U32.and(h, 255), U32.shrn(w, 8n), U32.and(w, 255), 3, 1, 17, 0, 2, 17, 0, 3, 17, 0]

def encode.sof(+w: U32, +h: U32) -> List<&2, U32>:
  encode.seg(192, encode.sofbody(w, h))

def encode.dccounts() -> List<&2, U32>:
  [0, 1, 5, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0]

def encode.dcsyms() -> List<&2, U32>:
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

def encode.accounts() -> List<&2, U32>:
  [0, 2, 1, 3, 3, 2, 4, 3, 5, 5, 4, 4, 0, 0, 1, 125]

def encode.acsyms() -> List<&2, U32>:
  [1, 2, 3, 0, 4, 17, 5, 18, 33, 49, 65, 6, 19, 81, 97, 7, 34, 113, 20, 50, 129, 145, 161, 8, 35, 66, 177, 193,
    21, 82, 209, 240, 36, 51, 98, 114, 130, 9, 10, 22, 23, 24, 25, 26, 37, 38, 39, 40, 41, 42, 52, 53, 54, 55, 56,
    57, 58, 67, 68, 69, 70, 71, 72, 73, 74, 83, 84, 85, 86, 87, 88, 89, 90, 99, 100, 101, 102, 103, 104, 105, 106,
    115, 116, 117, 118, 119, 120, 121, 122, 131, 132, 133, 134, 135, 136, 137, 138, 146, 147, 148, 149, 150, 151,
    152, 153, 154, 162, 163, 164, 165, 166, 167, 168, 169, 170, 178, 179, 180, 181, 182, 183, 184, 185, 186, 194,
    195, 196, 197, 198, 199, 200, 201, 202, 210, 211, 212, 213, 214, 215, 216, 217, 218, 225, 226, 227, 228, 229,
    230, 231, 232, 233, 234, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250]

def encode.dht(+cls: U32, +counts: List<&2, U32>, +syms: List<&2, U32>) -> List<&2, U32>:
  encode.seg(196, cls <> encode.join(counts, syms))

def encode.sos() -> List<&2, U32>:
  encode.seg(218, [3, 1, 0, 2, 0, 3, 0, 0, 63, 0])

def encode.header(+w: U32, +h: U32, +dcc: List<&2, U32>, +dcs: List<&2, U32>, +acc: List<&2, U32>,
  +acs: List<&2, U32>) -> List<&2, U32>:
  encode.join(Jpeg.soi(), encode.join(encode.app0(), encode.join(encode.dqt(), encode.join(encode.sof(w, h),
    encode.join(encode.dht(0, dcc, dcs), encode.join(encode.dht(16, acc, acs), encode.sos()))))))

def encode.tab.of(h: Jpeg.Huff) -> Tab:
  match h:
    case Jpeg.Huff{codes, lens, syms}:
      Tab{codes, lens, syms}

def encode.tab(+counts: List<&2, U32>, +syms: List<&2, U32>) -> Tab:
  encode.tab.of(Jpeg.decode.canon(272n, 0n, counts, syms, 0, 0, [], [], []))

def encode.ctx(+dcc: List<&2, U32>, +dcs: List<&2, U32>, +acc: List<&2, U32>, +acs: List<&2, U32>) -> Ctx:
  Ctx{Jpeg.decode.cos(), Jpeg.decode.zig(), encode.quant(), encode.tab(dcc, dcs), encode.tab(acc, acs)}

def encode.bad.b(bw: Bool, bh: Bool) -> Bool:
  match bw:
    case True{}:
      True{}
    case False{}:
      bh

def encode.bad.h(z: Bool, bw: Bool, bh: Bool) -> Bool:
  match z:
    case True{}:
      True{}
    case False{}:
      encode.bad.b(bw, bh)

def encode.bad.w(z: Bool, zh: Bool, bw: Bool, bh: Bool) -> Bool:
  match z:
    case True{}:
      True{}
    case False{}:
      encode.bad.h(zh, bw, bh)

def encode.bad(+w: U32, +h: U32) -> Bool:
  encode.bad.w(U32.is_eq(w, 0), U32.is_eq(h, 0), U32.is_gt(w, 65535), U32.is_gt(h, 65535))

def encode.put0() -> Put:
  Put{[], 0, 0}

def encode.stuff.ff(ff: Bool, out: List<&2, U32>, +b: U32) -> Put:
  match ff:
    case True{}:
      Put{0 <> (255 <> out), 0, 0}
    case False{}:
      Put{b <> out, 0, 0}

def encode.stuff(out: List<&2, U32>, +b: U32) -> Put:
  encode.stuff.ff(U32.is_eq(b, 255), out, b)

def encode.bit.n(full: Bool, out: List<&2, U32>, +nb: U32, +n: U32) -> Put:
  match full:
    case True{}:
      encode.stuff(out, nb)
    case False{}:
      Put{out, nb, (n + 1 : U32)}

def encode.bit(p: Put, +bit: U32) -> Put:
  match p:
    case Put{out, buf, +n}:
      encode.bit.n(U32.is_eq(n, 7), out, U32.or(U32.shl(buf), U32.and(bit, 1)), n)

def encode.bits.go(left: Nat, p: Put, +code: U32) -> Put:
  match left:
    case 0n:
      p
    case 1n+k:
      +kk = k
      encode.bits.go(kk, encode.bit(p, U32.and(U32.shrn(code, kk), 1)), code)

def encode.bits(p: Put, +len: U32, +code: U32) -> Put:
  encode.bits.go(U32.to_nat(len), p, code)

def encode.pad.byte(ff: Bool, out: List<&2, U32>, +byte: U32) -> List<&2, U32>:
  match ff:
    case True{}:
      List.reverse(&2, U32, 0 <> (255 <> out))
    case False{}:
      List.reverse(&2, U32, byte <> out)

def encode.pad.n(z: Bool, out: List<&2, U32>, +buf: U32, +n: U32) -> List<&2, U32>:
  match z:
    case True{}:
      List.reverse(&2, U32, out)
    case False{}:
      +sh = (8 - n : U32)
      +ones = (U32.shln(1, U32.to_nat(sh)) - 1 : U32)
      encode.pad.byte(U32.is_eq(U32.or(U32.shln(buf, U32.to_nat(sh)), ones), 255), out,
        U32.or(U32.shln(buf, U32.to_nat(sh)), ones))

def encode.pad(p: Put) -> List<&2, U32>:
  match p:
    case Put{out, +buf, +n}:
      encode.pad.n(U32.is_eq(n, 0), out, buf, n)

def encode.drop(xs: List<&2, U32>) -> U32:
  Jpeg.decode.drop(xs)

def encode.head(xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case +h <> t:
      +_d = encode.drop(t)
      h

def encode.tail(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      []
    case _h <> t:
      t

def encode.find.nil(eq: Bool, +c: U32, +l: U32) -> U32 & U32:
  match eq:
    case True{}:
      (c, l)
    case False{}:
      (0, 0)

def encode.find.go(syms: List<&2, U32>, eq: Bool, +codes: List<&2, U32>, +lens: List<&2, U32>, +want: U32, +c: U32,
  +l: U32) -> U32 & U32:
  match syms:
    case Nil{}:
      +_c = encode.drop(codes)
      +_l = encode.drop(lens)
      encode.find.nil(eq, c, l)
    case +s <> st:
      match eq:
        case True{}:
          +_s = encode.drop(st)
          (c, l)
        case False{}:
          encode.find.go(st, U32.is_eq(s, want), encode.tail(codes), encode.tail(lens), want, encode.head(codes),
            encode.head(lens))

def encode.find(+codes: List<&2, U32>, +lens: List<&2, U32>, syms: List<&2, U32>, +want: U32) -> U32 & U32:
  encode.find.go(syms, False{}, codes, lens, want, 0, 0)

def encode.cat.fr(done: Bool, +lt: Bool) -> Bool:
  match done:
    case True{}:
      True{}
    case False{}:
      lt

def encode.cat.on(fr: Bool) -> U32:
  match fr:
    case True{}:
      1
    case False{}:
      0

def encode.cat.c(fr: Bool, +c: U32) -> U32:
  match fr:
    case True{}:
      c
    case False{}:
      (c + 1 : U32)

def encode.cat.lim(fr: Bool, +lim: U32) -> U32:
  match fr:
    case True{}:
      lim
    case False{}:
      (lim * 2 : U32)

def encode.cat.go(left: Nat, +done: U32, +a: U32, +c: U32, +lim: U32) -> U32:
  match left:
    case 0n:
      c
    case 1n+p:
      +fr = encode.cat.fr(U32.is_eq(done, 1), U32.is_lt(a, lim))
      encode.cat.go(p, encode.cat.on(fr), a, encode.cat.c(fr, c), encode.cat.lim(fr, lim))

def encode.cat(+v: U32) -> U32:
  encode.cat.go(12n, 0, Jpeg.decode.abs(v), 0, 1)

def encode.mag.s(+s: U32, +cat: U32, +v: U32) -> U32:
  match s:
    case 0:
      v
    case _:
      (v + U32.shln(1, U32.to_nat(cat)) - 1 : U32)

def encode.mag(+cat: U32, +v: U32) -> U32:
  encode.mag.s(Jpeg.decode.sign(v), cat, v)

def encode.magp.z(z: Bool, p: Put, +cat: U32, +v: U32) -> Put:
  match z:
    case True{}:
      p
    case False{}:
      encode.bits(p, cat, encode.mag(cat, v))

def encode.dc.use(got: U32 & U32, p: Put, +cat: U32, +diff: U32) -> Put:
  (+code, +len) = got
  encode.magp.z(U32.is_eq(cat, 0), encode.bits(p, len, code), cat, diff)

def encode.dc(+p: Put, +diff: U32, tab: Tab) -> Put:
  match tab:
    case Tab{+codes, +lens, +syms}:
      +cat = encode.cat(diff)
      encode.dc.use(encode.find(codes, lens, syms, cat), p, cat, diff)

def encode.clip.hi(hi: Bool, +v: U32, +lim: U32) -> U32:
  match hi:
    case True{}:
      lim
    case False{}:
      v

def encode.clip.lo(lo: Bool, +v: U32, +lim: U32) -> U32:
  match lo:
    case True{}:
      Jpeg.decode.neg32(lim)
    case False{}:
      v

def encode.clip.s(+s: U32, +v: U32, +lim: U32) -> U32:
  match s:
    case 0:
      encode.clip.hi(U32.is_gt(v, lim), v, lim)
    case _:
      encode.clip.lo(U32.is_gt(Jpeg.decode.abs(v), lim), v, lim)

def encode.clip(+v: U32, +lim: U32) -> U32:
  encode.clip.s(Jpeg.decode.sign(v), v, lim)

def encode.bitsym(got: U32 & U32, p: Put) -> Put:
  (+code, +len) = got
  encode.bits(p, len, code)

def encode.eob(need: Bool, p: Put, +codes: List<&2, U32>, +lens: List<&2, U32>, +syms: List<&2, U32>) -> Put:
  match need:
    case False{}:
      p
    case True{}:
      encode.bitsym(encode.find(codes, lens, syms, 0), p)

def encode.zrls(left: Nat, p: Put, +codes: List<&2, U32>, +lens: List<&2, U32>, +syms: List<&2, U32>) -> Put:
  match left:
    case 0n:
      p
    case 1n+k:
      encode.zrls(k, encode.bitsym(encode.find(codes, lens, syms, 240), p), codes, lens, syms)

def encode.ac(zz: List<&2, U32>, +run: U32, p: Put, +codes: List<&2, U32>, +lens: List<&2, U32>,
  +syms: List<&2, U32>) -> Put:
  match zz:
    case Nil{}:
      encode.eob(U32.is_gt(run, 0), p, codes, lens, syms)
    case 0 <> ct:
      encode.ac(ct, (run + 1 : U32), p, codes, lens, syms)
    case +c <> ct:
      +clip = encode.clip(c, 1023)
      +cat = encode.cat(clip)
      +sym = U32.or(U32.shln(U32.mod(run, 16), 4n), cat)
      encode.ac(ct, 0, encode.magp.z(U32.is_eq(cat, 0), encode.bitsym(encode.find(codes, lens, syms, sym),
        encode.zrls(U32.to_nat(U32.div(run, 16)), p, codes, lens, syms)), cat, clip), codes, lens, syms)

def encode.qnz(+q: U32) -> U32:
  match q:
    case 0:
      1
    case _:
      q

def encode.qdiv.s(+s: U32, +v: U32, +q: U32) -> U32:
  match s:
    case 0:
      U32.div((v + U32.div(q, 2) : U32), q)
    case _:
      Jpeg.decode.neg32(U32.div((Jpeg.decode.abs(v) + U32.div(q, 2) : U32), q))

def encode.qdiv(+v: U32, +q: U32) -> U32:
  encode.qdiv.s(Jpeg.decode.sign(v), v, encode.qnz(q))

def encode.zzq(zig: List<&2, U32>, +nat: List<&2, U32>, +qs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match zig:
    case Nil{}:
      +_n = encode.drop(nat)
      +_q = encode.drop(qs)
      List.reverse(&2, U32, acc)
    case +g <> gt:
      encode.zzq(gt, nat, encode.tail(qs), encode.qdiv(Jpeg.decode.at(nat, g), encode.head(qs)) <> acc)

def encode.sink(tab: Tab) -> U32:
  match tab:
    case Tab{codes, lens, syms}:
      U32.or(encode.drop(codes), U32.or(encode.drop(lens), encode.drop(syms)))

def encode.block.ac(p: Put, +pred: U32, +dc0: U32, rest: List<&2, U32>, dc: Tab, ac: Tab) -> Put:
  match ac:
    case Tab{+acodes, +alens, +asyms}:
      +d = encode.clip(dc0, 2047)
      encode.ac(rest, 0, encode.dc(p, (d - pred : U32), dc), acodes, alens, asyms)

def encode.block.go(p: Put, +pred: U32, zz: List<&2, U32>, dc: Tab, ac: Tab) -> Put:
  match zz:
    case Nil{}:
      +_d = encode.sink(dc)
      +_a = encode.sink(ac)
      p
    case +dc0 <> rest:
      encode.block.ac(p, pred, dc0, rest, dc, ac)

# frequency column u of the A.3.3 matrix, sample x at index x*8+u
def encode.crow(+cs: List<&2, U32>, +u: U32) -> List<&2, U32>:
  [Jpeg.decode.at(cs, u), Jpeg.decode.at(cs, (u + 8 : U32)), Jpeg.decode.at(cs, (u + 16 : U32)),
    Jpeg.decode.at(cs, (u + 24 : U32)), Jpeg.decode.at(cs, (u + 32 : U32)),
    Jpeg.decode.at(cs, (u + 40 : U32)), Jpeg.decode.at(cs, (u + 48 : U32)), Jpeg.decode.at(cs, (u + 56 : U32))]

def encode.dot(+a: List<&2, U32>, +b: List<&2, U32>) -> U32:
  Jpeg.decode.dot(a, b, False{}, (0, 0), 0, 0)

def encode.trow(+row: List<&2, U32>, +cs: List<&2, U32>) -> List<&2, U32>:
  [encode.dot(row, encode.crow(cs, 0)), encode.dot(row, encode.crow(cs, 1)), encode.dot(row, encode.crow(cs, 2)),
    encode.dot(row, encode.crow(cs, 3)), encode.dot(row, encode.crow(cs, 4)), encode.dot(row, encode.crow(cs, 5)),
    encode.dot(row, encode.crow(cs, 6)), encode.dot(row, encode.crow(cs, 7))]

def encode.pass1(rows: List<&2, List<&2, U32>>, +cs: List<&2, U32>, acc: List<&2, List<&2, U32>>) ->
  List<&2, List<&2, U32>>:
  match rows:
    case Nil{}:
      List.reverse(&2, List<&2, U32>, acc)
    case h <> t:
      encode.pass1(t, cs, encode.trow(h, cs) <> acc)

def encode.srow(+c0: List<&2, U32>, +c1: List<&2, U32>, +c2: List<&2, U32>, +c3: List<&2, U32>,
  +c4: List<&2, U32>, +c5: List<&2, U32>, +c6: List<&2, U32>, +c7: List<&2, U32>, +cs: List<&2, U32>,
  +v: U32) -> List<&2, U32>:
  +row = encode.crow(cs, v)
  [encode.dot(c0, row), encode.dot(c1, row), encode.dot(c2, row), encode.dot(c3, row), encode.dot(c4, row),
    encode.dot(c5, row), encode.dot(c6, row), encode.dot(c7, row)]

def encode.srows(left: Nat, +v: U32, +c0: List<&2, U32>, +c1: List<&2, U32>, +c2: List<&2, U32>,
  +c3: List<&2, U32>, +c4: List<&2, U32>, +c5: List<&2, U32>, +c6: List<&2, U32>, +c7: List<&2, U32>,
  +cs: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match left:
    case 0n:
      Nil{}
    case 1n+p:
      encode.srow(c0, c1, c2, c3, c4, c5, c6, c7, cs, v) <> encode.srows(p, (v + 1 : U32), c0, c1, c2, c3, c4,
        c5, c6, c7, cs)

def encode.flat(rows: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match rows:
    case Nil{}:
      Nil{}
    case h <> t:
      encode.join(h, encode.flat(t))

def encode.pass2(+ts: List<&2, List<&2, U32>>, +cs: List<&2, U32>) -> List<&2, U32>:
  +c0 = Jpeg.decode.col(ts, 0, [])
  +c1 = Jpeg.decode.col(ts, 1, [])
  +c2 = Jpeg.decode.col(ts, 2, [])
  +c3 = Jpeg.decode.col(ts, 3, [])
  +c4 = Jpeg.decode.col(ts, 4, [])
  +c5 = Jpeg.decode.col(ts, 5, [])
  +c6 = Jpeg.decode.col(ts, 6, [])
  +c7 = Jpeg.decode.col(ts, 7, [])
  encode.flat(encode.srows(8n, 0, c0, c1, c2, c3, c4, c5, c6, c7, cs))

def encode.fdct(rows: List<&2, List<&2, U32>>, +cs: List<&2, U32>) -> List<&2, U32>:
  encode.pass2(encode.pass1(rows, cs, []), cs)

def encode.level(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      (h - 128 : U32) <> encode.level(t)

def encode.levels(rows: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match rows:
    case Nil{}:
      Nil{}
    case h <> t:
      encode.level(h) <> encode.levels(t)

def encode.sat(over: Bool, +x: U32, +lim: U32) -> U32:
  match over:
    case True{}:
      (lim - 1 : U32)
    case False{}:
      x

def encode.sat8(over: Bool, +v: U32) -> U32:
  match over:
    case True{}:
      255
    case False{}:
      v

def encode.y(+r: U32, +g: U32, +b: U32) -> U32:
  U32.shrn((19595 * r + 38470 * g + 7471 * b + 32768 : U32), 16n)

def encode.cb(+r: U32, +g: U32, +b: U32) -> U32:
  U32.shrn((32768 * b + 8421376 - 11059 * r - 21709 * g : U32), 16n)

def encode.cr(+r: U32, +g: U32, +b: U32) -> U32:
  U32.shrn((32768 * r + 8421376 - 27439 * g - 5329 * b : U32), 16n)

def encode.ych(+r: U32, +g: U32, +b: U32) -> U32:
  +v = encode.y(r, g, b)
  encode.sat8(U32.is_gt(v, 255), v)

def encode.cbch(+r: U32, +g: U32, +b: U32) -> U32:
  +v = encode.cb(r, g, b)
  encode.sat8(U32.is_gt(v, 255), v)

def encode.crch(+r: U32, +g: U32, +b: U32) -> U32:
  +v = encode.cr(r, g, b)
  encode.sat8(U32.is_gt(v, 255), v)

def encode.chan.w(+ch: U32, +r: U32, +g: U32, +b: U32) -> U32:
  match ch:
    case 0:
      encode.ych(r, g, b)
    case 1:
      encode.cbch(r, g, b)
    case _:
      encode.crch(r, g, b)

def encode.chan(+pix: U32, +ch: U32) -> U32:
  encode.chan.w(ch, U32.and(U32.shrn(pix, 16n), 255), U32.and(U32.shrn(pix, 8n), 255), U32.and(pix, 255))

def encode.sample(+px: List<&2, U32>, +w: U32, +h: U32, +x: U32, +y: U32, +ch: U32) -> U32:
  encode.chan(Jpeg.decode.at(px, (encode.sat(U32.is_ge(y, h), y, h) * w + encode.sat(U32.is_ge(x, w), x, w) :
    U32)), ch)

# both samples are the neutral level
def encode.flat.both(a: Bool, b: Bool) -> Bool:
  match a:
    case False{}:
      match b:
        case _k:
          False{}
    case True{}:
      b

def encode.rowpix.step(+s: U32, got: List<&2, U32> & Bool) -> List<&2, U32> & Bool:
  (rest, flat) = got
  (s <> rest, encode.flat.both(U32.is_eq(s, 128), flat))

def encode.rowpix(left: Nat, +px: List<&2, U32>, +w: U32, +h: U32, +x: U32, +y: U32, +ch: U32) ->
  List<&2, U32> & Bool:
  match left:
    case 0n:
      (Nil{}, True{})
    case 1n+p:
      encode.rowpix.step(encode.sample(px, w, h, x, y, ch), encode.rowpix(p, px, w, h, (x + 1 : U32), y, ch))

def encode.rows.step(got: List<&2, U32> & Bool, rest: List<&2, List<&2, U32>> & Bool) ->
  List<&2, List<&2, U32>> & Bool:
  (row, rf) = got
  (tail, flat) = rest
  (row <> tail, encode.flat.both(rf, flat))

def encode.rows(left: Nat, +px: List<&2, U32>, +w: U32, +h: U32, +x: U32, +y: U32, +ch: U32) ->
  List<&2, List<&2, U32>> & Bool:
  match left:
    case 0n:
      (Nil{}, True{})
    case 1n+p:
      encode.rows.step(encode.rowpix(8n, px, w, h, x, y, ch), encode.rows(p, px, w, h, x, (y + 1 : U32), ch))

def encode.coef.go(zz: List<&2, U32>) -> U32:
  match zz:
    case Nil{}:
      0
    case +dc0 <> rest:
      +_r = encode.drop(rest)
      encode.clip(dc0, 2047)

def encode.droprows(rows: List<&2, List<&2, U32>>) -> U32:
  match rows:
    case Nil{}:
      0
    case h <> t:
      +_h = encode.drop(h)
      encode.droprows(t)

# 128 level-shifts to 0, and the integer DCT of that block is 0, so quant by 1 stays 0
def encode.zz(flat: Bool, rows: List<&2, List<&2, U32>>, +cs: List<&2, U32>, +zig: List<&2, U32>,
  +qs: List<&2, U32>) -> List<&2, U32>:
  match flat:
    case True{}:
      +_r = encode.droprows(rows)
      +_c = encode.drop(cs)
      +_g = encode.drop(zig)
      +_q = encode.drop(qs)
      List.replicate(U32, 64n, 0)
    case False{}:
      encode.zzq(zig, encode.fdct(encode.levels(rows), cs), qs, [])

def encode.coef.use(got: List<&2, List<&2, U32>> & Bool, +cs: List<&2, U32>, +zig: List<&2, U32>,
  +qs: List<&2, U32>) -> U32:
  (rows, flat) = got
  encode.coef.go(encode.zz(flat, rows, cs, zig, qs))

def encode.coef(+px: List<&2, U32>, +w: U32, +h: U32, +x: U32, +y: U32, +ch: U32, ctx: Ctx) -> U32:
  match ctx:
    case Ctx{+cs, +zig, +qs, dc, ac}:
      +_d = encode.sink(dc)
      +_a = encode.sink(ac)
      encode.coef.use(encode.rows(8n, px, w, h, x, y, ch), cs, zig, qs)

def encode.block.use(p: Put, +pred: U32, got: List<&2, List<&2, U32>> & Bool, +cs: List<&2, U32>,
  +zig: List<&2, U32>, +qs: List<&2, U32>, dc: Tab, ac: Tab) -> Put:
  (rows, flat) = got
  encode.block.go(p, pred, encode.zz(flat, rows, cs, zig, qs), dc, ac)

def encode.block(p: Put, +pred: U32, +px: List<&2, U32>, +w: U32, +h: U32, +x: U32, +y: U32, +ch: U32,
  ctx: Ctx) -> Put:
  match ctx:
    case Ctx{+cs, +zig, +qs, dc, ac}:
      encode.block.use(p, pred, encode.rows(8n, px, w, h, x, y, ch), cs, zig, qs, dc, ac)

def encode.nx(more: Bool, +mx: U32) -> U32:
  match more:
    case True{}:
      (mx + 1 : U32)
    case False{}:
      0

def encode.ny(more: Bool, +my: U32) -> U32:
  match more:
    case True{}:
      my
    case False{}:
      (my + 1 : U32)

def encode.mcus(left: Nat, +mx: U32, +my: U32, +mw: U32, +w: U32, +h: U32, +px: List<&2, U32>, +py: U32,
  +pb: U32, +pr: U32, p: Put, +ctx: Ctx) -> Put:
  match left:
    case 0n:
      p
    case 1n+nleft:
      +x = (mx * 8 : U32)
      +y = (my * 8 : U32)
      +more = U32.is_lt((mx + 1 : U32), mw)
      encode.mcus(nleft, encode.nx(more, mx), encode.ny(more, my), mw, w, h, px, encode.coef(px, w, h, x, y, 0, ctx),
        encode.coef(px, w, h, x, y, 1, ctx), encode.coef(px, w, h, x, y, 2, ctx), encode.block(encode.block(
        encode.block(p, py, px, w, h, x, y, 0, ctx), pb, px, w, h, x, y, 1, ctx), pr, px, w, h, x, y, 2, ctx), ctx)

def encode.finish(+w: U32, +h: U32, ent: List<&2, U32>, +dcc: List<&2, U32>, +dcs: List<&2, U32>,
  +acc: List<&2, U32>, +acs: List<&2, U32>) -> List<&2, U32>:
  encode.join(encode.header(w, h, dcc, dcs, acc, acs), encode.join(ent, Jpeg.eoi()))

def encode.scan.miss(eq: Bool) -> Bool:
  match eq:
    case _e:
      False{}

# packed 8421504 is Y = Cb = Cr = 128, so each block is the zero coefficient vector
def encode.scan(left: Nat, xs: List<&2, U32>, eq: Bool) -> Bool:
  match left:
    case 0n:
      +_x = encode.drop(xs)
      eq
    case 1n+k:
      match xs:
        case Nil{}:
          encode.scan.miss(eq)
        case +h <> t:
          encode.scan(k, t, encode.flat.both(eq, U32.is_eq(h, 8421504)))

def encode.z64() -> List<&2, U32>:
  List.replicate(U32, 64n, 0)

def encode.zero.block(p: Put, +pred: U32, dc: Tab, ac: Tab) -> Put:
  encode.block.go(p, pred, encode.z64(), dc, ac)

def encode.zero.tri(p: Put, +dc: Tab, +ac: Tab) -> Put:
  encode.zero.block(encode.zero.block(encode.zero.block(p, 0, dc, ac), 0, dc, ac), 0, dc, ac)

def encode.neutral.sink(p: Put, ctx: Ctx) -> Put:
  match ctx:
    case Ctx{cs, zig, qs, dc, ac}:
      +_c = encode.drop(cs)
      +_g = encode.drop(zig)
      +_q = encode.drop(qs)
      +_d = encode.sink(dc)
      +_a = encode.sink(ac)
      p

def encode.neutral.step(p: Put, ctx: Ctx) -> Put:
  match ctx:
    case Ctx{+cs, +zig, +qs, dc, ac}:
      +_c = encode.drop(cs)
      +_g = encode.drop(zig)
      +_q = encode.drop(qs)
      encode.zero.tri(p, dc, ac)

def encode.neutral.mcus(left: Nat, p: Put, +ctx: Ctx) -> Put:
  match left:
    case 0n:
      encode.neutral.sink(p, ctx)
    case 1n+nleft:
      encode.neutral.mcus(nleft, encode.neutral.step(p, ctx), ctx)

def encode.neutral(+w: U32, +h: U32) -> List<&2, U32>:
  +dcc = encode.dccounts()
  +dcs = encode.dcsyms()
  +acc = encode.accounts()
  +acs = encode.acsyms()
  +mw = U32.div((w + 7 : U32), 8)
  +mh = U32.div((h + 7 : U32), 8)
  encode.finish(w, h, encode.pad(encode.neutral.mcus(U32.to_nat((mw * mh : U32)), encode.put0(),
    encode.ctx(dcc, dcs, acc, acs))), dcc, dcs, acc, acs)

def encode.go(+w: U32, +h: U32, +px: List<&2, U32>) -> List<&2, U32>:
  +dcc = encode.dccounts()
  +dcs = encode.dcsyms()
  +acc = encode.accounts()
  +acs = encode.acsyms()
  +mw = U32.div((w + 7 : U32), 8)
  +mh = U32.div((h + 7 : U32), 8)
  encode.finish(w, h, encode.pad(encode.mcus(U32.to_nat((mw * mh : U32)), 0, 0, mw, w, h, px, 0, 0, 0,
    encode.put0(), encode.ctx(dcc, dcs, acc, acs))), dcc, dcs, acc, acs)

def encode.dispatch(neu: Bool, +w: U32, +h: U32, px: List<&2, U32>) -> List<&2, U32>:
  match neu:
    case True{}:
      +_d = encode.drop(px)
      encode.neutral(w, h)
    case False{}:
      encode.go(w, h, px)

def encode.arm(+w: U32, +h: U32, +px: List<&2, U32>) -> List<&2, U32>:
  encode.dispatch(encode.scan(U32.to_nat((w * h : U32)), px, True{}), w, h, px)

def encode.pick(bad: Bool, +w: U32, +h: U32, px: List<&2, U32>) -> List<&2, U32>:
  match bad:
    case True{}:
      +_d = encode.drop(px)
      encode.join(Jpeg.soi(), Jpeg.eoi())
    case False{}:
      encode.arm(w, h, px)

def spots.tail.go(xs: List<&2, U32>, +a: U32, +b: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      [a, b]
    case h <> t:
      spots.tail.go(t, b, h)

def spots.tail(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case a <> b <> t:
      spots.tail.go(t, a, b)
    case _:
      []

def spots.take(+xs: List<&2, U32>, +at: U32, +n: U32) -> List<&2, U32>:
  List.take(&2, U32, List.drop(&2, U32, xs, U32.to_nat(at)), U32.to_nat(n))

# fixed-header slices: SOI, APP0, JFIF, DQT, SOF0, DHT, SOS, and the trailing EOI
def spots(+xs: List<&2, U32>) ->
  List<&2, U32> & List<&2, U32> & List<&2, U32> & List<&2, U32> & List<&2, U32> & List<&2, U32> & List<&2, U32> &
  List<&2, U32>:
  (spots.take(xs, 0, 2), spots.take(xs, 2, 2), spots.take(xs, 6, 5), spots.take(xs, 20, 2), spots.take(xs, 89, 2),
    spots.take(xs, 108, 2), spots.take(xs, 324, 2), spots.tail(xs))

# baseline sequential 4:4:4 JPEG bytes for packed RGB samples, or SOI EOI when the size is rejected
def encode(+w: U32, +h: U32, px: List<&2, U32>) -> List<&2, U32>:
  encode.pick(encode.bad(w, h), w, h, px)
