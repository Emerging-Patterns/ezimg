# ezimg: baseline JPEG encode. Sequential 8-bit Huffman (SOF0) and JFIF APP0.
# Colour is 4:4:4 YCbCr, no subsampling: one 8 by 8 block per component per MCU.
# Samples are packed RGB, (R << 16) | (G << 8) | B, the same layout decode returns.
# Quantisation steps are all 1, so an integer coefficient is kept whole.
# The forward DCT (T.81 A.3.3) pairs samples that share a cosine weight, then
# rounds once with the same fixed-point product as a matrix column.
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

# cosine weights shared by symmetric samples: DC, two even weights, four odd weights
type Kern is Data:
  Kern{k0: U32, k2: U32, k6: U32, o0: U32, o1: U32, o2: U32, o3: U32}

# eight values, the first at frequency 0
type Oct is Data:
  Oct{f0: U32, f1: U32, f2: U32, f3: U32, f4: U32, f5: U32, f6: U32, f7: U32}

# the sample plane, the frequency plane, and the next column of one forward DCT
type Planes is Type:
  Planes{src: Array<U32>, dst: Array<U32>, at: U32}

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

def encode.sink(tab: Tab) -> U32:
  match tab:
    case Tab{codes, lens, syms}:
      U32.or(encode.drop(codes), U32.or(encode.drop(lens), encode.drop(syms)))

# the clipped DC is written and kept, so the next block can predict from it
def encode.block.ac(p: Put, +pred: U32, +dc0: U32, rest: List<&2, U32>, dc: Tab, ac: Tab) -> U32 & Put:
  match ac:
    case Tab{+acodes, +alens, +asyms}:
      +d = encode.clip(dc0, 2047)
      (d, encode.ac(rest, 0, encode.dc(p, (d - pred : U32), dc), acodes, alens, asyms))

def encode.block.go(p: Put, +pred: U32, zz: List<&2, U32>, dc: Tab, ac: Tab) -> U32 & Put:
  match zz:
    case Nil{}:
      +_d = encode.sink(dc)
      +_a = encode.sink(ac)
      (0, p)
    case +dc0 <> rest:
      encode.block.ac(p, pred, dc0, rest, dc, ac)

def encode.add64.acc(+ph: U32, +pl: U32, acc: U32 & U32) -> U32 & U32:
  match acc:
    case (+hi, +lo):
      +sum = (lo + pl : U32)
      ((hi + ph + Jpeg.decode.carry(lo, sum) : U32), sum)

# add a signed product onto a 64-bit accumulator
def encode.add64(prod: U32 & U32, acc: U32 & U32) -> U32 & U32:
  match prod:
    case (+ph, +pl):
      encode.add64.acc(ph, pl, acc)

# one more product on the accumulator
def encode.mac(+coef: U32, +samp: U32, acc: U32 & U32) -> U32 & U32:
  encode.add64(Jpeg.decode.widemul(coef, samp), acc)

# the same rounding the matrix product applies to a finished sum
def encode.q17(acc: U32 & U32) -> U32:
  match acc:
    case (+hi, +lo):
      Jpeg.decode.q17(hi, lo)

def encode.scale(+coef: U32, +samp: U32) -> U32:
  encode.q17(Jpeg.decode.widemul(coef, samp))

def encode.two(+c0: U32, +x0: U32, +c1: U32, +x1: U32) -> U32:
  encode.q17(encode.mac(c1, x1, Jpeg.decode.widemul(c0, x0)))

def encode.two.n(+c0: U32, +x0: U32, +c1: U32, +x1: U32) -> U32:
  encode.q17(encode.mac(Jpeg.decode.neg32(c1), x1, Jpeg.decode.widemul(c0, x0)))

def encode.four(+c0: U32, +s0: U32, +c1: U32, +s1: U32, +c2: U32, +s2: U32, +c3: U32, +s3: U32) -> U32:
  encode.q17(encode.mac(c3, s3, encode.mac(c2, s2, encode.mac(c1, s1, Jpeg.decode.widemul(c0, s0)))))

# even frequencies: symmetric samples share one weight
def encode.even(
  +s0: U32, +s1: U32, +s2: U32, +s3: U32, +s4: U32, +s5: U32, +s6: U32, +s7: U32, +k0: U32, +k2: U32,
  +k6: U32
) -> Oct:
  +a0 = (s0 + s7 : U32)
  +a1 = (s1 + s6 : U32)
  +a2 = (s2 + s5 : U32)
  +a3 = (s3 + s4 : U32)
  +e0 = (a0 - a3 : U32)
  +e1 = (a1 - a2 : U32)
  Oct{encode.scale(k0, (a0 + a1 + a2 + a3 : U32)), 0, encode.two(k2, e0, k6, e1), 0,
    encode.scale(k0, ((a0 + a3 : U32) - (a1 + a2 : U32) : U32)), 0, encode.two.n(k6, e0, k2, e1), 0}

# odd frequencies: antisymmetric samples share one weight
def encode.odd(+d0: U32, +d1: U32, +d2: U32, +d3: U32, +o0: U32, +o1: U32, +o2: U32, +o3: U32) -> Oct:
  +n0 = Jpeg.decode.neg32(o0)
  +n2 = Jpeg.decode.neg32(o2)
  +n3 = Jpeg.decode.neg32(o3)
  Oct{0, encode.four(o0, d0, o1, d1, o2, d2, o3, d3), 0, encode.four(o1, d0, n3, d1, n0, d2, n2, d3), 0,
    encode.four(o2, d0, n0, d1, o3, d2, o1, d3), 0, encode.four(o3, d0, n2, d1, o1, d2, n0, d3)}

def encode.dct8.od(+f0: U32, +f2: U32, +f4: U32, +f6: U32, od: Oct) -> Oct:
  match od:
    case Oct{+z0, +f1, +z2, +f3, +z4, +f5, +z6, +f7}:
      +_z = (z0 + z2 + z4 + z6 : U32)
      Oct{f0, f1, f2, f3, f4, f5, f6, f7}

def encode.dct8.at(ev: Oct, od: Oct) -> Oct:
  match ev:
    case Oct{+f0, +z1, +f2, +z3, +f4, +z5, +f6, +z7}:
      +_z = (z1 + z3 + z5 + z7 : U32)
      encode.dct8.od(f0, f2, f4, f6, od)

def encode.dct8.k(
  +s0: U32, +s1: U32, +s2: U32, +s3: U32, +s4: U32, +s5: U32, +s6: U32, +s7: U32, kern: Kern
) -> Oct:
  match kern:
    case Kern{+k0, +k2, +k6, +o0, +o1, +o2, +o3}:
      encode.dct8.at(encode.even(s0, s1, s2, s3, s4, s5, s6, s7, k0, k2, k6),
        encode.odd((s0 - s7 : U32), (s1 - s6 : U32), (s2 - s5 : U32), (s3 - s4 : U32), o0, o1, o2, o3))

# one 8-point transform. Pairing is the matrix product, so the rounded value matches.
def encode.dct8(samp: Oct, kern: Kern) -> Oct:
  match samp:
    case Oct{+s0, +s1, +s2, +s3, +s4, +s5, +s6, +s7}:
      encode.dct8.k(s0, s1, s2, s3, s4, s5, s6, s7, kern)

def encode.take(row: List<&2, U32>) -> Oct:
  match row:
    case +s0 <> +s1 <> +s2 <> +s3 <> +s4 <> +s5 <> +s6 <> +s7 <> rest:
      +_drop = encode.drop(rest)
      Oct{s0, s1, s2, s3, s4, s5, s6, s7}
    case _:
      Oct{0, 0, 0, 0, 0, 0, 0, 0}

def encode.put8(
  +f0: U32, +f1: U32, +f2: U32, +f3: U32, +f4: U32, +f5: U32, +f6: U32, +f7: U32, a: Array<U32>, +at: U32,
  +step: U32
) -> Array<U32>:
  +i1 = (at + step : U32)
  +i2 = (i1 + step : U32)
  +i3 = (i2 + step : U32)
  +i4 = (i3 + step : U32)
  +i5 = (i4 + step : U32)
  +i6 = (i5 + step : U32)
  +i7 = (i6 + step : U32)
  Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32,
    Array.set(U32, a, at, f0), i1, f1), i2, f2), i3, f3), i4, f4), i5, f5), i6, f6), i7, f7)

def encode.lay(o: Oct, a: Array<U32>, +at: U32) -> Array<U32>:
  match o:
    case Oct{+f0, +f1, +f2, +f3, +f4, +f5, +f6, +f7}:
      encode.put8(f0, f1, f2, f3, f4, f5, f6, f7, a, at, 1)

def encode.scatter(o: Oct, a: Array<U32>, +at: U32) -> Array<U32>:
  match o:
    case Oct{+f0, +f1, +f2, +f3, +f4, +f5, +f6, +f7}:
      encode.put8(f0, f1, f2, f3, f4, f5, f6, f7, a, at, 8)

# C[0][0], C[0][2], C[0][6], and the first four weights of frequency 1
def encode.kern(+cs: List<&2, U32>) -> Kern:
  Kern{Jpeg.decode.at(cs, 0), Jpeg.decode.at(cs, 2), Jpeg.decode.at(cs, 6), Jpeg.decode.at(cs, 1),
    Jpeg.decode.at(cs, 9), Jpeg.decode.at(cs, 17), Jpeg.decode.at(cs, 25)}

def encode.kern.drop(kern: Kern) -> U32:
  match kern:
    case Kern{+k0, +k2, +k6, +o0, +o1, +o2, +o3}:
      +z0 = (k0 - k0 : U32)
      +z2 = (k2 - k2 : U32)
      +z6 = (k6 - k6 : U32)
      +a0 = (o0 - o0 : U32)
      +a1 = (o1 - o1 : U32)
      +a2 = (o2 - o2 : U32)
      +a3 = (o3 - o3 : U32)
      (z0 + z2 + z6 + a0 + a1 + a2 + a3 : U32)

def encode.span.pack(got: Array<U32> & U32, +prev: U32, +at: U32, acc: List<&2, U32>) ->
  Array<U32> & U32 & U32 & List<&2, U32>:
  match got:
    case (arr, samp):
      (arr, samp, at, prev <> acc)

# read the sample at `at` and keep the one already in hand
def encode.span.step(st: Array<U32> & U32 & U32 & List<&2, U32>) -> Array<U32> & U32 & U32 & List<&2, U32>:
  (arr, +samp, +at, acc) = st
  encode.span.pack(Array.get(U32, arr, at), samp, (at + 8 : U32), acc)

def encode.span.done(st: Array<U32> & U32 & U32 & List<&2, U32>) -> Array<U32> & List<&2, U32>:
  (arr, samp, +at, acc) = st
  +_at = (at - at : U32)
  (arr, List.reverse(&2, U32, samp <> acc))

# `left` further samples of this column are still unread. The state holds the latest one.
def encode.span(left: Nat, st: Array<U32> & U32 & U32 & List<&2, U32>) -> Array<U32> & List<&2, U32>:
  match left:
    case 0n:
      encode.span.done(st)
    case 1n+rest:
      encode.span(rest, encode.span.step(st))

def encode.col.end(got: Array<U32> & List<&2, U32>, kern: Kern) -> Array<U32> & Oct:
  match got:
    case (arr, xs):
      (arr, encode.dct8(encode.take(xs), kern))

def encode.col.st(got: Array<U32> & U32, +at: U32) -> Array<U32> & U32 & U32 & List<&2, U32>:
  match got:
    case (arr, samp):
      (arr, samp, at, [])

def encode.col(arr: Array<U32>, +at: U32, kern: Kern) -> Array<U32> & Oct:
  encode.col.end(encode.span(7n, encode.col.st(Array.get(U32, arr, at), (at + 8 : U32))), kern)

def encode.pass1(rows: List<&2, List<&2, U32>>, +kern: Kern, arr: Array<U32>, +at: U32) -> Array<U32>:
  match rows:
    case Nil{}:
      +_z = encode.kern.drop(kern)
      arr
    case h <> t:
      encode.pass1(t, kern, encode.lay(encode.dct8(encode.take(h), kern), arr, at), (at + 8 : U32))

def encode.pix.sink(a: Array<U32>) -> U32:
  match a:
    case ALeaf{_x}:
      0
    case ANode{xs, ys}:
      U32.or(encode.pix.sink(xs), encode.pix.sink(ys))

def encode.pass2.done(st: Planes, kern: Kern) -> Array<U32>:
  match st:
    case Planes{src, dst, +at}:
      +_z = encode.kern.drop(kern)
      +_s = encode.pix.sink(src)
      +_at = (at - at : U32)
      dst

def encode.pass2.put(got: Array<U32> & Oct, dst: Array<U32>, +at: U32) -> Planes:
  match got:
    case (src, o):
      Planes{src, encode.scatter(o, dst, at), (at + 1 : U32)}

def encode.pass2.step(st: Planes, kern: Kern) -> Planes:
  match st:
    case Planes{src, dst, +at}:
      encode.pass2.put(encode.col(src, at, kern), dst, at)

def encode.pass2(left: Nat, st: Planes, +kern: Kern) -> Array<U32>:
  match left:
    case 0n:
      encode.pass2.done(st, kern)
    case 1n+rest:
      encode.pass2(rest, encode.pass2.step(st, kern), kern)

def encode.drain.pack(got: Array<U32> & U32, acc: List<&2, U32>) -> Array<U32> & U32 & List<&2, U32>:
  match got:
    case (arr, samp):
      (arr, samp, acc)

def encode.drain.step(st: Array<U32> & U32 & List<&2, U32>, +idx: Nat) -> Array<U32> & U32 & List<&2, U32>:
  (arr, samp, acc) = st
  encode.drain.pack(Array.get(U32, arr, U32.from_nat(idx)), samp <> acc)

def encode.drain.done(st: Array<U32> & U32 & List<&2, U32>) -> List<&2, U32>:
  (arr, samp, acc) = st
  +_s = encode.pix.sink(arr)
  samp <> acc

# read index 63 first, so the cons list comes out in order
def encode.drain(left: Nat, st: Array<U32> & U32 & List<&2, U32>) -> List<&2, U32>:
  match left:
    case 0n:
      encode.drain.done(st)
    case 1n+ +rest:
      encode.drain(rest, encode.drain.step(st, rest))

def encode.drain.st(got: Array<U32> & U32) -> Array<U32> & U32 & List<&2, U32>:
  match got:
    case (arr, samp):
      (arr, samp, [])

def encode.fdct.go(src: Array<U32>, kern: Kern) -> List<&2, U32>:
  encode.drain(63n, encode.drain.st(Array.get(U32, encode.pass2(8n, Planes{src, Jpeg.decode.plane(64), 0}, kern), 63)))

def encode.fdct(rows: List<&2, List<&2, U32>>, +cs: List<&2, U32>) -> List<&2, U32>:
  +kern = encode.kern(cs)
  encode.fdct.go(encode.pass1(rows, kern, Jpeg.decode.plane(64), 0), kern)

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

# the first `left` samples, then the rest of the list is unused
def encode.pix.load(left: Nat, px: List<&2, U32>, a: Array<U32>, +i: U32) -> Array<U32>:
  match left px:
    case 0n rest:
      +_d = encode.drop(rest)
      a
    case 1n+k Nil{}:
      a
    case 1n+k +h <> t:
      encode.pix.load(k, t, Array.set(U32, a, i, h), (i + 1 : U32))

def encode.sample.use(got: Array<U32> & U32, +ch: U32) -> Array<U32> & U32:
  (a, pix) = got
  (a, encode.chan(pix, ch))

# one index into the sample array, instead of a walk from the head of the list
def encode.sample(a: Array<U32>, +w: U32, +h: U32, +x: U32, +y: U32, +ch: U32) -> Array<U32> & U32:
  encode.sample.use(Array.get(U32, a, (encode.sat(U32.is_ge(y, h), y, h) * w + encode.sat(U32.is_ge(x, w), x, w) :
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

def encode.rowpix.step(+s: U32, got: Array<U32> & List<&2, U32> & Bool) -> Array<U32> & List<&2, U32> & Bool:
  (a, rest, flat) = got
  (a, s <> rest, encode.flat.both(U32.is_eq(s, 128), flat))

def encode.rowpix.one(+s: U32, a: Array<U32>) -> Array<U32> & List<&2, U32> & Bool:
  (a, s <> Nil{}, encode.flat.both(U32.is_eq(s, 128), True{}))

# `got` is the sample at x. `left` counts it and the samples after it.
def encode.rowpix(left: Nat, got: Array<U32> & U32, +w: U32, +h: U32, +x: U32, +y: U32, +ch: U32) ->
  Array<U32> & List<&2, U32> & Bool:
  match left:
    case 0n:
      (a, s) = got
      encode.rowpix.one(s, a)
    case 1n+0n:
      (a, s) = got
      encode.rowpix.one(s, a)
    case 1n+1n+q:
      (a, s) = got
      encode.rowpix.step(s, encode.rowpix(1n+q, encode.sample(a, w, h, (x + 1 : U32), y, ch), w, h,
        (x + 1 : U32), y, ch))

def encode.rows.join(+row: List<&2, U32>, rf: Bool, rest: Array<U32> & List<&2, List<&2, U32>> & Bool) ->
  Array<U32> & List<&2, List<&2, U32>> & Bool:
  (a, tail, flat) = rest
  (a, row <> tail, encode.flat.both(rf, flat))

def encode.rows.one(+row: List<&2, U32>, rf: Bool, a: Array<U32>) -> Array<U32> & List<&2, List<&2, U32>> & Bool:
  (a, row <> Nil{}, rf)

# `got` is the row at y. `left` counts it and the rows after it.
def encode.rows(left: Nat, got: Array<U32> & List<&2, U32> & Bool, +w: U32, +h: U32, +x: U32, +y: U32,
  +ch: U32) -> Array<U32> & List<&2, List<&2, U32>> & Bool:
  match left:
    case 0n:
      (a, row, rf) = got
      encode.rows.one(row, rf, a)
    case 1n+0n:
      (a, row, rf) = got
      encode.rows.one(row, rf, a)
    case 1n+1n+q:
      (a, row, rf) = got
      encode.rows.join(row, rf, encode.rows(1n+q, encode.rowpix(8n, encode.sample(a, w, h, x, (y + 1 : U32), ch),
        w, h, x, (y + 1 : U32), ch), w, h, x, (y + 1 : U32), ch))

def encode.droprows(rows: List<&2, List<&2, U32>>) -> U32:
  match rows:
    case Nil{}:
      0
    case h <> t:
      +_h = encode.drop(h)
      encode.droprows(t)

# the next quant step, or 0 when the table has run out (qdiv turns 0 into 1)
def encode.zzq.take(qs: List<&2, U32>) -> U32 & List<&2, U32>:
  match qs:
    case Nil{}:
      (0, [])
    case +q <> qt:
      (q, qt)

# `got` is the coefficient at the zigzag index just read. `rest` is the indexes after it.
def encode.zzq.go(rest: List<&2, U32>, got: Array<U32> & U32, qv: U32 & List<&2, U32>, acc: List<&2, U32>) ->
  List<&2, U32>:
  match rest:
    case Nil{}:
      match got:
        case (a, +v):
          match qv:
            case (+q, qt):
              +_s = encode.pix.sink(a)
              +_d = encode.drop(qt)
              List.reverse(&2, U32, encode.qdiv(v, q) <> acc)
    case +g <> gt:
      match got:
        case (a, +v):
          match qv:
            case (+q, qt):
              encode.zzq.go(gt, Array.get(U32, a, g), encode.zzq.take(qt), encode.qdiv(v, q) <> acc)

def encode.zzq.enter(zig: List<&2, U32>, arr: Array<U32>, qs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match zig:
    case Nil{}:
      +_s = encode.pix.sink(arr)
      +_q = encode.drop(qs)
      List.reverse(&2, U32, acc)
    case +g <> gt:
      encode.zzq.go(gt, Array.get(U32, arr, g), encode.zzq.take(qs), acc)

def encode.zzq.load(nat: List<&2, U32>, arr: Array<U32>, +at: U32) -> Array<U32>:
  match nat:
    case Nil{}:
      arr
    case +h <> t:
      encode.zzq.load(t, Array.set(U32, arr, at, h), (at + 1 : U32))

# the coefficient block is an array, so each zigzag step is an index
def encode.zzq(zig: List<&2, U32>, +nat: List<&2, U32>, +qs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  encode.zzq.enter(zig, encode.zzq.load(nat, Jpeg.decode.plane(64), 0), qs, acc)

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

def encode.block.pair(got: U32 & Put, a: Array<U32>) -> Array<U32> & U32 & Put:
  match got:
    case (+dc, bit):
      (a, dc, bit)

def encode.block.use(p: Put, +pred: U32, got: Array<U32> & List<&2, List<&2, U32>> & Bool, +cs: List<&2, U32>,
  +zig: List<&2, U32>, +qs: List<&2, U32>, dc: Tab, ac: Tab) -> Array<U32> & U32 & Put:
  (a, rows, flat) = got
  encode.block.pair(encode.block.go(p, pred, encode.zz(flat, rows, cs, zig, qs), dc, ac), a)

def encode.block(p: Put, +pred: U32, a: Array<U32>, +w: U32, +h: U32, +x: U32, +y: U32, +ch: U32,
  ctx: Ctx) -> Array<U32> & U32 & Put:
  match ctx:
    case Ctx{+cs, +zig, +qs, dc, ac}:
      encode.block.use(p, pred, encode.rows(8n, encode.rowpix(8n, encode.sample(a, w, h, x, y, ch), w, h, x, y, ch),
        w, h, x, y, ch), cs, zig, qs, dc, ac)

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

def encode.step.end(got: Array<U32> & U32 & Put, +ydc: U32, +bdc: U32) -> Array<U32> & U32 & U32 & U32 & Put:
  (a, rdc, bit) = got
  (a, ydc, bdc, rdc, bit)

def encode.step.r(got: Array<U32> & U32 & Put, +ydc: U32, +pr: U32, +x: U32, +y: U32, +w: U32, +h: U32,
  +ctx: Ctx) -> Array<U32> & U32 & U32 & U32 & Put:
  (a, bdc, bit) = got
  encode.step.end(encode.block(bit, pr, a, w, h, x, y, 2, ctx), ydc, bdc)

def encode.step.b(got: Array<U32> & U32 & Put, +pb: U32, +pr: U32, +x: U32, +y: U32, +w: U32, +h: U32,
  +ctx: Ctx) -> Array<U32> & U32 & U32 & U32 & Put:
  (a, ydc, bit) = got
  encode.step.r(encode.block(bit, pb, a, w, h, x, y, 1, ctx), ydc, pr, x, y, w, h, ctx)

# one pass per channel: the block's clipped DC is the next predictor
def encode.step.y(a: Array<U32>, bit: Put, +py: U32, +pb: U32, +pr: U32, +x: U32, +y: U32, +w: U32,
  +h: U32, +ctx: Ctx) -> Array<U32> & U32 & U32 & U32 & Put:
  encode.step.b(encode.block(bit, py, a, w, h, x, y, 0, ctx), pb, pr, x, y, w, h, ctx)

def encode.mcus.done(got: Array<U32> & U32 & U32 & U32 & Put) -> Put:
  (a, ydc, bdc, rdc, bit) = got
  +_s = encode.pix.sink(a)
  +_u = (ydc + bdc + rdc : U32)
  bit

def encode.mcus(left: Nat, got: Array<U32> & U32 & U32 & U32 & Put, +mx: U32, +my: U32, +mw: U32, +w: U32,
  +h: U32, +ctx: Ctx) -> Put:
  match left:
    case 0n:
      encode.mcus.done(got)
    case 1n+nleft:
      (a, py, pb, pr, bit) = got
      +x = (mx * 8 : U32)
      +y = (my * 8 : U32)
      +more = U32.is_lt((mx + 1 : U32), mw)
      encode.mcus(nleft, encode.step.y(a, bit, py, pb, pr, x, y, w, h, ctx), encode.nx(more, mx),
        encode.ny(more, my), mw, w, h, ctx)

def encode.finish(+w: U32, +h: U32, ent: List<&2, U32>, +dcc: List<&2, U32>, +dcs: List<&2, U32>,
  +acc: List<&2, U32>, +acs: List<&2, U32>) -> List<&2, U32>:
  encode.join(encode.header(w, h, dcc, dcs, acc, acs), encode.join(ent, Jpeg.eoi()))

# samples before a mismatch were packed 8421504, so that prefix can be replayed
def encode.hunt.nil(+seen: U32) -> Bool & List<&2, U32>:
  (False{}, List.replicate(U32, U32.to_nat(seen), 8421504))

def encode.hunt.mix(+seen: U32, +h: U32, t: List<&2, U32>) -> Bool & List<&2, U32>:
  (False{}, List.append(&2, U32, List.replicate(U32, U32.to_nat(seen), 8421504), h <> t))

def encode.hunt.rest(xs: List<&2, U32>) -> Bool & List<&2, U32>:
  +_d = encode.drop(xs)
  (True{}, [])

# no samples remain after `h`
def encode.hunt.done(eq: Bool, +h: U32, xs: List<&2, U32>, +seen: U32) -> Bool & List<&2, U32>:
  match eq:
    case False{}:
      encode.hunt.mix(seen, h, xs)
    case True{}:
      encode.hunt.rest(xs)

# the list ended before the area did
def encode.hunt.empty(eq: Bool, +h: U32, +seen: U32) -> Bool & List<&2, U32>:
  match eq:
    case False{}:
      encode.hunt.mix(seen, h, [])
    case True{}:
      encode.hunt.nil((seen + 1 : U32))

# `h` was just read. `left` samples remain after it. `seen` neutral samples precede it.
def encode.hunt.go(left: Nat, xs: List<&2, U32>, eq: Bool, +h: U32, +seen: U32) -> Bool & List<&2, U32>:
  match left:
    case 0n:
      encode.hunt.done(eq, h, xs, seen)
    case 1n+p:
      match xs:
        case Nil{}:
          encode.hunt.empty(eq, h, seen)
        case +s <> u:
          match eq:
            case False{}:
              encode.hunt.mix(seen, h, s <> u)
            case True{}:
              encode.hunt.go(p, u, U32.is_eq(s, 8421504), s, (seen + 1 : U32))

# the area was one colour. `seen` of those samples are replayed only on a miss.
def encode.hold.no(+seen: U32, +c: U32, tail: List<&2, U32>) -> Bool & List<&2, U32>:
  (False{}, List.append(&2, U32, List.replicate(U32, U32.to_nat(seen), c), tail))

def encode.hold.yes(xs: List<&2, U32>, +c: U32, +h: U32, +seen: U32) -> Bool & List<&2, U32>:
  +_d = encode.drop(xs)
  +_u = (c + h + seen : U32)
  (True{}, [])

def encode.hold.done(eq: Bool, +h: U32, xs: List<&2, U32>, +c: U32, +seen: U32) -> Bool & List<&2, U32>:
  match eq:
    case False{}:
      encode.hold.no(seen, c, h <> xs)
    case True{}:
      encode.hold.yes(xs, c, h, seen)

def encode.hold.empty(eq: Bool, +h: U32, +c: U32, +seen: U32) -> Bool & List<&2, U32>:
  match eq:
    case False{}:
      encode.hold.no(seen, c, h <> [])
    case True{}:
      +_h = (h - h : U32)
      encode.hold.no((seen + 1 : U32), c, [])

# `h` was just read. `left` samples remain after it. `seen` copies of `c` precede it.
def encode.hold.go(left: Nat, xs: List<&2, U32>, eq: Bool, +h: U32, +c: U32, +seen: U32) -> Bool & List<&2, U32>:
  match left:
    case 0n:
      encode.hold.done(eq, h, xs, c, seen)
    case 1n+p:
      match xs:
        case Nil{}:
          encode.hold.empty(eq, h, c, seen)
        case +s <> u:
          match eq:
            case False{}:
              encode.hold.no(seen, c, h <> (s <> u))
            case True{}:
              encode.hold.go(p, u, U32.is_eq(s, c), s, c, (seen + 1 : U32))

# 0 neutral, 1 one other colour, 2 mixed. A short list stays mixed: the plane's gaps are 0.
def encode.watch.neu(got: Bool & List<&2, U32>) -> U32 & U32 & List<&2, U32>:
  (ok, px) = got
  match ok:
    case True{}:
      +_d = encode.drop(px)
      (0, 0, [])
    case False{}:
      (2, 0, px)

def encode.watch.sol(got: Bool & List<&2, U32>, +h: U32) -> U32 & U32 & List<&2, U32>:
  (ok, px) = got
  match ok:
    case True{}:
      +_d = encode.drop(px)
      (1, h, [])
    case False{}:
      +_h = (h - h : U32)
      (2, 0, px)

def encode.watch.pick(neu: Bool, k: Nat, t: List<&2, U32>, +h: U32) -> U32 & U32 & List<&2, U32>:
  match neu:
    case True{}:
      encode.watch.neu(encode.hunt.go(k, t, True{}, h, 0))
    case False{}:
      encode.watch.sol(encode.hold.go(k, t, True{}, h, h, 0), h)

def encode.watch(left: Nat, xs: List<&2, U32>) -> U32 & U32 & List<&2, U32>:
  match left:
    case 0n:
      +_d = encode.drop(xs)
      (0, 0, [])
    case 1n+k:
      match xs:
        case Nil{}:
          (2, 0, [])
        case +h <> t:
          encode.watch.pick(U32.is_eq(h, 8421504), k, t, h)

# low len bits of code join the open byte; a finished byte is stuffed
def encode.pack.byte(+buf: U32, +len: U32, +code: U32) -> U32:
  U32.or(U32.shln(buf, U32.to_nat(len)), code)

def encode.pack.full(full: Bool, out: List<&2, U32>, +buf: U32, +n: U32, +len: U32, +code: U32) -> Put:
  match full:
    case True{}:
      encode.stuff(out, encode.pack.byte(buf, len, code))
    case False{}:
      Put{out, encode.pack.byte(buf, len, code), (n + len : U32)}

def encode.pack.keep(p: Put, +lo: U32, +rest: U32) -> Put:
  match p:
    case Put{out, _buf, _n}:
      Put{out, rest, lo}

def encode.pack.span(out: List<&2, U32>, +buf: U32, +n: U32, +len: U32, +code: U32) -> Put:
  +room = (8 - n : U32)
  +lo = (len - room : U32)
  encode.pack.keep(encode.stuff(out, U32.or(U32.shln(buf, U32.to_nat(room)),
    U32.shrn(code, U32.to_nat(lo)))), lo, U32.and(code, (U32.shln(1, U32.to_nat(lo)) - 1 : U32)))

def encode.pack.fit(fit: Bool, out: List<&2, U32>, +buf: U32, +n: U32, +len: U32, +code: U32) -> Put:
  match fit:
    case True{}:
      encode.pack.full(U32.is_eq((n + len : U32), 8), out, buf, n, len, code)
    case False{}:
      encode.pack.span(out, buf, n, len, code)

def encode.pack(p: Put, +len: U32, +code: U32) -> Put:
  match p:
    case Put{out, +buf, +n}:
      encode.pack.fit(U32.is_le((n + len : U32), 8), out, buf, n, len, code)

# Annex K luminance: a zero block is DC 00 then EOB 1010
def encode.zput(p: Put) -> Put:
  encode.pack(p, 6, 10)

def encode.ztri(p: Put) -> Put:
  encode.zput(encode.zput(encode.zput(p)))

def encode.neutral.mcus(left: Nat, p: Put) -> Put:
  match left:
    case 0n:
      p
    case 1n+nleft:
      encode.neutral.mcus(nleft, encode.ztri(p))

def encode.neutral(+w: U32, +h: U32) -> List<&2, U32>:
  +dcc = encode.dccounts()
  +dcs = encode.dcsyms()
  +acc = encode.accounts()
  +acs = encode.acsyms()
  +mw = U32.div((w + 7 : U32), 8)
  +mh = U32.div((h + 7 : U32), 8)
  encode.finish(w, h, encode.pad(encode.neutral.mcus(U32.to_nat((mw * mh : U32)), encode.put0())),
    dcc, dcs, acc, acs)

# the rest of a solid picture is the same DC, so each later block is a zero difference
def encode.solid.end(got: Array<U32> & U32 & Put) -> Put:
  (a, +dc, bit) = got
  +_s = encode.pix.sink(a)
  +_d = (dc - dc : U32)
  bit

def encode.solid.cr(got: Array<U32> & U32 & Put, +ctx: Ctx) -> Put:
  (a, +dc, bit) = got
  +_d = (dc - dc : U32)
  encode.solid.end(encode.block(bit, 0, a, 1, 1, 0, 0, 2, ctx))

def encode.solid.cb(got: Array<U32> & U32 & Put, +ctx: Ctx) -> Put:
  (a, +dc, bit) = got
  +_d = (dc - dc : U32)
  encode.solid.cr(encode.block(bit, 0, a, 1, 1, 0, 0, 1, ctx), ctx)

def encode.solid.y(a: Array<U32>, bit: Put, +ctx: Ctx) -> Put:
  encode.solid.cb(encode.block(bit, 0, a, 1, 1, 0, 0, 0, ctx), ctx)

# one colour repeated. The first MCU is that block; every later MCU is three zero differences.
def encode.solid(+w: U32, +h: U32, +color: U32) -> List<&2, U32>:
  +dcc = encode.dccounts()
  +dcs = encode.dcsyms()
  +acc = encode.accounts()
  +acs = encode.acsyms()
  +mw = U32.div((w + 7 : U32), 8)
  +mh = U32.div((h + 7 : U32), 8)
  +n = (mw * mh : U32)
  encode.finish(w, h, encode.pad(encode.neutral.mcus(U32.to_nat((n - 1 : U32)),
    encode.solid.y(Array.set(U32, Jpeg.decode.plane(1), 0, color), encode.put0(),
      encode.ctx(dcc, dcs, acc, acs)))), dcc, dcs, acc, acs)

def encode.go(+w: U32, +h: U32, px: List<&2, U32>) -> List<&2, U32>:
  +dcc = encode.dccounts()
  +dcs = encode.dcsyms()
  +acc = encode.accounts()
  +acs = encode.acsyms()
  +mw = U32.div((w + 7 : U32), 8)
  +mh = U32.div((h + 7 : U32), 8)
  +area = (w * h : U32)
  encode.finish(w, h, encode.pad(encode.mcus(U32.to_nat((mw * mh : U32)),
    (encode.pix.load(U32.to_nat(area), px, Jpeg.decode.plane(area), 0), 0, 0, 0, encode.put0()), 0, 0, mw, w, h,
    encode.ctx(dcc, dcs, acc, acs))), dcc, dcs, acc, acs)

def encode.dispatch(+tag: U32, +color: U32, px: List<&2, U32>, +w: U32, +h: U32) -> List<&2, U32>:
  match tag:
    case 0:
      +_c = (color - color : U32)
      +_d = encode.drop(px)
      encode.neutral(w, h)
    case 1:
      +_d = encode.drop(px)
      encode.solid(w, h, color)
    case _:
      +_c = (color - color : U32)
      encode.go(w, h, px)

def encode.arm.use(got: U32 & U32 & List<&2, U32>, +w: U32, +h: U32) -> List<&2, U32>:
  match got:
    case (+tag, +color, px):
      encode.dispatch(tag, color, px, w, h)

def encode.arm(+w: U32, +h: U32, px: List<&2, U32>) -> List<&2, U32>:
  encode.arm.use(encode.watch(U32.to_nat((w * h : U32)), px), w, h)

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
