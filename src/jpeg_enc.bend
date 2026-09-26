# src/jpeg_enc: baseline JPEG encode. Sequential 8-bit Huffman (SOF0) and JFIF APP0.
# Colour is 4:4:4 YCbCr, no subsampling: one 8 by 8 block per component per MCU.
# Samples are packed 0xAARRGGBB, the layout decode returns; the alpha byte is ignored.
# Quantisation steps are all 1, so an integer coefficient is kept whole.
# The forward DCT (T.81 A.3.3) pairs samples that share a cosine weight, then
# rounds once with the same fixed-point product as a matrix column.
# Both components share the Annex K luminance Huffman tables.
# A coefficient indexes its symbol. The scan does not walk the table.
# A mixed MCU reads each pixel once and keeps the three level planes in arrays.
# Quant steps are 1, so the mixed scan emits coefficients without dividing.
# A neutral solid (R = G = B = 128) is an all-zero block and round-trips exactly.
# Other colours are lossy. Progressive and arithmetic frames are not written.
# Width and height must sit in 1..65535; anything else is SOI then EOI.

import Base
import ./jpeg.bend as Jpeg

# bytes emitted so far (newest first), the open byte, and how many bits it holds
type Put is Data:
  Put{out: List<&2, U32>, buf: U32, n: U32}

# cosine weights shared by symmetric samples: DC, two even weights, four odd weights
type Kern is Data:
  Kern{k0: U32, k2: U32, k6: U32, o0: U32, o1: U32, o2: U32, o3: U32}

# the cosine kernel, zigzag, and the all-ones quant table
type Ctx is Data:
  Ctx{kern: Kern, zig: List<&2, U32>, quant: List<&2, U32>}

# DC and AC symbols indexed to a packed code: length in the high half, code in the low half
type Book is Type:
  Book{dc: Array<U32>, ac: Array<U32>}

# one looked-up Huffman code
type Code is Data:
  Code{len: U32, bits: U32}

# eight values, the first at frequency 0
type Oct is Data:
  Oct{f0: U32, f1: U32, f2: U32, f3: U32, f4: U32, f5: U32, f6: U32, f7: U32}

# the sample plane, the frequency plane, and the next column of one forward DCT
type Planes is Type:
  Planes{src: Array<U32>, dst: Array<U32>, at: U32}

# one MCU: packed pixels, three level planes, and whether each plane is the neutral level
type Tile is Type:
  Tile{pix: Array<U32>, ys: Array<U32>, bs: Array<U32>, rs: Array<U32>, fy: Bool, fb: Bool, fr: Bool}

# frequency plane, the open zero run, and the AC coder. Steps are 1, so no quant list.
type Scan is Type:
  Scan{arr: Array<U32>, run: U32, ac: Array<U32>, bit: Put}

def encode.join(aa: List<&2, U32>, bb: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, aa, bb)

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

def encode.sofbody(+ww: U32, +hh: U32) -> List<&2, U32>:
  [8, U32.shrn(hh, 8n), U32.and(hh, 255), U32.shrn(ww, 8n), U32.and(ww, 255), 3, 1, 17, 0, 2, 17, 0, 3, 17, 0]

def encode.sof(+ww: U32, +hh: U32) -> List<&2, U32>:
  encode.seg(192, encode.sofbody(ww, hh))

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

def encode.header(
  +ww: U32,
  +hh: U32,
  +dcc: List<&2, U32>,
  +dcs: List<&2, U32>,
  +acc: List<&2, U32>,
  +acs: List<&2, U32>
) -> List<&2, U32>:
  encode.join(Jpeg.soi(), encode.join(encode.app0(), encode.join(encode.dqt(), encode.join(encode.sof(ww, hh),
    encode.join(encode.dht(0, dcc, dcs), encode.join(encode.dht(16, acc, acs), encode.sos()))))))

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

def encode.ctx() -> Ctx:
  Ctx{encode.kern(Jpeg.decode.cos()), Jpeg.decode.zig(), encode.quant()}

# length sits above the 16-bit code
def encode.word(+len: U32, +code: U32) -> U32:
  U32.or(U32.shln(len, 16n), U32.and(code, 65535))

def encode.bad.b(bw: Bool, bh: Bool) -> Bool:
  match bw:
    case True{}:
      True{}
    case False{}:
      bh

def encode.bad.h(zz: Bool, bw: Bool, bh: Bool) -> Bool:
  match zz:
    case True{}:
      True{}
    case False{}:
      encode.bad.b(bw, bh)

def encode.bad.w(zz: Bool, zh: Bool, bw: Bool, bh: Bool) -> Bool:
  match zz:
    case True{}:
      True{}
    case False{}:
      encode.bad.h(zh, bw, bh)

def encode.bad(+ww: U32, +hh: U32) -> Bool:
  encode.bad.w(U32.is_eq(ww, 0), U32.is_eq(hh, 0), U32.is_gt(ww, 65535), U32.is_gt(hh, 65535))

def encode.put0() -> Put:
  Put{[], 0, 0}

# a finished byte. Bytes are kept as written; encode.pad stuffs them once, at the end.
def encode.stuff(out: List<&2, U32>, +bb: U32) -> Put:
  Put{bb <> out, 0, 0}

def encode.bit.n(full: Bool, out: List<&2, U32>, +nb: U32, +nn: U32) -> Put:
  match full:
    case True{}:
      encode.stuff(out, nb)
    case False{}:
      Put{out, nb, (nn + 1 : U32)}

def encode.bit(pp: Put, +bit: U32) -> Put:
  match pp:
    case Put{out, buf, +n}:
      encode.bit.n(U32.is_eq(n, 7), out, U32.or(U32.shl(buf), U32.and(bit, 1)), n)

def encode.bits.go(left: Nat, pp: Put, +code: U32) -> Put:
  match left:
    case 0n:
      pp
    case 1n+k:
      +kk = k
      encode.bits.go(kk, encode.bit(pp, U32.and(U32.shrn(code, kk), 1)), code)

def encode.bits(pp: Put, +len: U32, +code: U32) -> Put:
  encode.bits.go(U32.to_nat(len), pp, code)

# one byte put in front of the stuffed bytes after it: 255 is followed by a 0
def encode.stuff.put(ff: Bool, +bb: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match ff:
    case True{}:
      bb <> (0 <> acc)
    case False{}:
      bb <> acc

# the written bytes, newest first, stuffed and put in order onto acc: every 255 is followed by a 0
# (T.81 F.1.2.3). U32.is_eq, not a literal pattern, so a law reaches a symbolic byte.
def encode.stuff.all(out: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match out:
    case Nil{}:
      acc
    case +bb <> rest:
      encode.stuff.all(rest, encode.stuff.put(U32.is_eq(bb, 255), bb, acc))

def encode.pad.n(zz: Bool, out: List<&2, U32>, +buf: U32, +nn: U32) -> List<&2, U32>:
  match zz:
    case True{}:
      out
    case False{}:
      +sh = (8 - nn : U32)
      U32.or((U32.shln(1, U32.to_nat(sh)) - 1 : U32), U32.shln(buf, U32.to_nat(sh))) <> out

# the entropy-coded bytes: the open byte padded with 1 bits, then every byte stuffed, in order
def encode.pad(pp: Put) -> List<&2, U32>:
  match pp:
    case Put{out, +buf, +n}:
      encode.stuff.all(encode.pad.n(U32.is_eq(n, 0), out, buf, n), [])

def encode.drop(xs: List<&2, U32>) -> U32:
  Jpeg.decode.drop(xs)

# one canonical table, stored so the symbol is the index
def encode.fill(syms: List<&2, U32>, codes: List<&2, U32>, lens: List<&2, U32>, aa: Array<U32>) -> Array<U32>:
  match syms:
    case Nil{}:
      +_c = encode.drop(codes)
      +_l = encode.drop(lens)
      aa
    case +s <> st:
      match codes:
        case Nil{}:
          +_s = encode.drop(st)
          +_l = encode.drop(lens)
          +_u = (s - s : U32)
          aa
        case +c <> ct:
          match lens:
            case Nil{}:
              +_c = encode.drop(ct)
              +_s = encode.drop(st)
              +_u = (c + s : U32)
              aa
            case +l <> lt:
              encode.fill(st, ct, lt, Array.set(U32, aa, s, encode.word(l, c)))

def encode.huff.of(hh: Jpeg.Huff) -> Array<U32>:
  match hh:
    case Jpeg.Huff{codes, lens, syms}:
      encode.fill(syms, codes, lens, Jpeg.decode.plane(256))

def encode.huff(+counts: List<&2, U32>, +syms: List<&2, U32>) -> Array<U32>:
  encode.huff.of(Jpeg.decode.canon(272n, 0n, counts, syms, 0, 0, [], [], []))

def encode.book(+dcc: List<&2, U32>, +dcs: List<&2, U32>, +acc: List<&2, U32>, +acs: List<&2, U32>) -> Book:
  Book{encode.huff(dcc, dcs), encode.huff(acc, acs)}

# the first of two sizes when the value is below the limit, else the second
def encode.cat.pick(lt: Bool, +cc: U32, +rest: U32) -> U32:
  match lt:
    case True{}:
      +_r = rest
      cc
    case False{}:
      +_c = cc
      rest

# the size of a magnitude: the first cc with aa below lim = 2^cc, left sizes tried, else cc. Each comparison is
# made with a constant limit, so a law over a symbolic value keeps one comparison per size.
def encode.cat.go(left: Nat, +aa: U32, +cc: U32, +lim: U32) -> U32:
  match left:
    case 0n:
      +_a = aa
      +_l = lim
      cc
    case 1n+p:
      encode.cat.pick(U32.is_lt(aa, lim), cc, encode.cat.go(p, aa, (cc + 1 : U32), (lim * 2 : U32)))

def encode.cat(+vv: U32) -> U32:
  encode.cat.go(12n, Jpeg.decode.abs(vv), 0, 1)

def encode.mag.s(+ss: U32, +cat: U32, +vv: U32) -> U32:
  match ss:
    case 0:
      vv
    case _:
      (vv + U32.shln(1, U32.to_nat(cat)) - 1 : U32)

def encode.mag(+cat: U32, +vv: U32) -> U32:
  encode.mag.s(Jpeg.decode.sign(vv), cat, vv)

def encode.magp.z(zz: Bool, pp: Put, +cat: U32, +vv: U32) -> Put:
  match zz:
    case True{}:
      pp
    case False{}:
      encode.bits(pp, cat, encode.mag(cat, vv))

# the indexed word is the length and the code
def encode.coded(got: Array<U32> & U32) -> Array<U32> & Code:
  (a, +packed) = got
  (a, Code{U32.shrn(packed, 16n), U32.and(packed, 65535)})

def encode.sym(aa: Array<U32>, +sym: U32) -> Array<U32> & Code:
  encode.coded(Array.get(U32, aa, sym))

def encode.dc.use(got: Array<U32> & Code, pp: Put, +cat: U32, +diff: U32) -> Array<U32> & Put:
  match got:
    case (a, Code{+len, +bits}):
      (a, encode.magp.z(U32.is_eq(cat, 0), encode.bits(pp, len, bits), cat, diff))

def encode.dc(aa: Array<U32>, +pp: Put, +diff: U32) -> Array<U32> & Put:
  +cat = encode.cat(diff)
  encode.dc.use(encode.sym(aa, cat), pp, cat, diff)

def encode.clip.hi(hi: Bool, +vv: U32, +lim: U32) -> U32:
  match hi:
    case True{}:
      lim
    case False{}:
      vv

def encode.clip.lo(lo: Bool, +vv: U32, +lim: U32) -> U32:
  match lo:
    case True{}:
      Jpeg.decode.neg32(lim)
    case False{}:
      vv

# by the sign, asked with U32.is_eq so a law reaches a symbolic value
def encode.clip.b(pos: Bool, +vv: U32, +lim: U32) -> U32:
  match pos:
    case True{}:
      encode.clip.hi(U32.is_gt(vv, lim), vv, lim)
    case False{}:
      encode.clip.lo(U32.is_gt(Jpeg.decode.abs(vv), lim), vv, lim)

def encode.clip(+vv: U32, +lim: U32) -> U32:
  encode.clip.b(U32.is_eq(Jpeg.decode.sign(vv), 0), vv, lim)

# a DC clipped to T.81's range for 8-bit samples, -1024 to 1023, kept as that plus 1024 (0 to 2047), so the
# difference of two DCs has at most 11 bits (F.1.2.1) and is found without wrapping. The level shift keeps the
# forward DCT's DC in -1024..1015, so the clip never changes it.
def encode.dcbias.b(pos: Bool, +vv: U32) -> U32:
  match pos:
    case True{}:
      (encode.clip.hi(U32.is_gt(vv, 1023), vv, 1023) + 1024 : U32)
    case False{}:
      (1024 - encode.clip.hi(U32.is_gt(Jpeg.decode.abs(vv), 1024), Jpeg.decode.abs(vv), 1024) : U32)

# a DC clipped to -1024 to 1023, plus 1024
def encode.dcbias(+vv: U32) -> U32:
  encode.dcbias.b(U32.is_eq(Jpeg.decode.sign(vv), 0), vv)

# a negative DC difference -mm: its size's code, then its magnitude bits, 2^size - 1 - mm (F.1.2.1)
def encode.magp.n(zz: Bool, pp: Put, +cat: U32, +mm: U32) -> Put:
  match zz:
    case True{}:
      +_u = (cat + mm : U32)
      pp
    case False{}:
      encode.bits(pp, cat, ((U32.shln(1, U32.to_nat(cat)) - 1 : U32) - mm : U32))

# the size's code of a negative DC difference, then its magnitude
def encode.dc.use.neg(got: Array<U32> & Code, pp: Put, +cat: U32, +mm: U32) -> Array<U32> & Put:
  match got:
    case (a, Code{+len, +bits}):
      (a, encode.magp.n(U32.is_eq(cat, 0), encode.bits(pp, len, bits), cat, mm))

# a negative DC difference, -mm
def encode.dc.neg(aa: Array<U32>, +pp: Put, +mm: U32) -> Array<U32> & Put:
  +cat = encode.cat(mm)
  encode.dc.use.neg(encode.sym(aa, cat), pp, cat, mm)

# the DC difference of two biased DCs, by its sign
def encode.dcdiff.b(up: Bool, aa: Array<U32>, pp: Put, +bb: U32, +pb: U32) -> Array<U32> & Put:
  match up:
    case True{}:
      encode.dc(aa, pp, (bb - pb : U32))
    case False{}:
      encode.dc.neg(aa, pp, (pb - bb : U32))

# the DC difference of biased DC bb from biased predictor pb
def encode.dcdiff(aa: Array<U32>, pp: Put, +bb: U32, +pb: U32) -> Array<U32> & Put:
  encode.dcdiff.b(U32.is_ge(bb, pb), aa, pp, bb, pb)

def encode.emit(got: Array<U32> & Code, pp: Put) -> Array<U32> & Put:
  match got:
    case (a, Code{+len, +bits}):
      (a, encode.bits(pp, len, bits))

def encode.eob(need: Bool, aa: Array<U32>, pp: Put) -> Array<U32> & Put:
  match need:
    case False{}:
      (aa, pp)
    case True{}:
      encode.emit(encode.sym(aa, 0), pp)

def encode.eob.on(need: Bool, st: Array<U32> & Put) -> Array<U32> & Put:
  match st:
    case (a, p):
      encode.eob(need, a, p)

def encode.zrls.one(st: Array<U32> & Put) -> Array<U32> & Put:
  match st:
    case (a, p):
      encode.emit(encode.sym(a, 240), p)

def encode.zrls(left: Nat, st: Array<U32> & Put) -> Array<U32> & Put:
  match left:
    case 0n:
      st
    case 1n+k:
      encode.zrls(k, encode.zrls.one(st))

def encode.ac.mag(got: Array<U32> & Put, +cat: U32, +clip: U32) -> Array<U32> & Put:
  match got:
    case (d, r):
      (d, encode.magp.z(U32.is_eq(cat, 0), r, cat, clip))

def encode.ac.hit(got: Array<U32> & Put, +sym: U32, +cat: U32, +clip: U32) -> Array<U32> & Put:
  match got:
    case (b, q):
      encode.ac.mag(encode.emit(encode.sym(b, sym), q), cat, clip)

def encode.ac.step(+cc: U32, +run: U32, st: Array<U32> & Put) -> Array<U32> & Put:
  match st:
    case (a, p):
      +clip = encode.clip(cc, 1023)
      +cat = encode.cat(clip)
      +sym = U32.or(cat, U32.shln(U32.and(15, run), 4n))
      encode.ac.hit(encode.zrls(U32.to_nat(U32.shrn(run, 4n)), (a, p)), sym, cat, clip)

# the zero run after one more coefficient
def encode.ac.run(zero: Bool, +run: U32) -> U32:
  match zero:
    case True{}:
      (run + 1 : U32)
    case False{}:
      +_r = run
      0

# one more coefficient: a zero only lengthens the run
def encode.ac.at(zero: Bool, +cc: U32, +run: U32, st: Array<U32> & Put) -> Array<U32> & Put:
  match zero:
    case True{}:
      +_u = (cc + run : U32)
      st
    case False{}:
      encode.ac.step(cc, run, st)

# the AC coefficients in zigzag order. U32.is_eq, not a literal pattern, so a law reaches a symbolic coefficient.
def encode.ac(zz: List<&2, U32>, +run: U32, st: Array<U32> & Put) -> Array<U32> & Put:
  match zz:
    case Nil{}:
      encode.eob.on(U32.is_gt(run, 0), st)
    case +c <> ct:
      encode.ac(ct, encode.ac.run(U32.is_eq(c, 0), run), encode.ac.at(U32.is_eq(c, 0), c, run, st))

def encode.qnz(+qq: U32) -> U32:
  match qq:
    case 0:
      1
    case _:
      qq

def encode.qdiv.s(+ss: U32, +vv: U32, +qq: U32) -> U32:
  match ss:
    case 0:
      U32.div((vv + U32.div(qq, 2) : U32), qq)
    case _:
      Jpeg.decode.neg32(U32.div((Jpeg.decode.abs(vv) + U32.div(qq, 2) : U32), qq))

def encode.qdiv(+vv: U32, +qq: U32) -> U32:
  encode.qdiv.s(Jpeg.decode.sign(vv), vv, encode.qnz(qq))

def encode.block.join(got: Array<U32> & Put, dc2: Array<U32>, +dd: U32) -> Book & U32 & Put:
  (ac2, p3) = got
  (Book{dc2, ac2}, dd, p3)

def encode.block.dc(got: Array<U32> & Put, ac: Array<U32>, +dd: U32, rest: List<&2, U32>) -> Book & U32 & Put:
  (dc2, p2) = got
  encode.block.join(encode.ac(rest, 0, (ac, p2)), dc2, dd)

# the DC, clipped to T.81's 8-bit range and biased by 1024, is written as its difference from the last and kept,
# so the next block can predict from it
def encode.block.ac(book: Book, pp: Put, +pred: U32, +dc0: U32, rest: List<&2, U32>) -> Book & U32 & Put:
  match book:
    case Book{dc, ac}:
      +d = encode.dcbias(dc0)
      encode.block.dc(encode.dcdiff(dc, pp, d, pred), ac, d, rest)

def encode.block.go(book: Book, pp: Put, +pred: U32, zz: List<&2, U32>) -> Book & U32 & Put:
  match zz:
    case Nil{}:
      (book, 1024, pp)
    case +dc0 <> rest:
      encode.block.ac(book, pp, pred, dc0, rest)

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
  +s0: U32,
  +s1: U32,
  +s2: U32,
  +s3: U32,
  +s4: U32,
  +s5: U32,
  +s6: U32,
  +s7: U32,
  +k0: U32,
  +k2: U32,
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
  +s0: U32,
  +s1: U32,
  +s2: U32,
  +s3: U32,
  +s4: U32,
  +s5: U32,
  +s6: U32,
  +s7: U32,
  kern: Kern
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
  +f0: U32,
  +f1: U32,
  +f2: U32,
  +f3: U32,
  +f4: U32,
  +f5: U32,
  +f6: U32,
  +f7: U32,
  aa: Array<U32>,
  +at: U32,
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
    Array.set(U32, aa, at, f0), i1, f1), i2, f2), i3, f3), i4, f4), i5, f5), i6, f6), i7, f7)

def encode.lay(oo: Oct, aa: Array<U32>, +at: U32) -> Array<U32>:
  match oo:
    case Oct{+f0, +f1, +f2, +f3, +f4, +f5, +f6, +f7}:
      encode.put8(f0, f1, f2, f3, f4, f5, f6, f7, aa, at, 1)

def encode.scatter(oo: Oct, aa: Array<U32>, +at: U32) -> Array<U32>:
  match oo:
    case Oct{+f0, +f1, +f2, +f3, +f4, +f5, +f6, +f7}:
      encode.put8(f0, f1, f2, f3, f4, f5, f6, f7, aa, at, 8)

def encode.oct.pack(
  +s0: U32,
  +s1: U32,
  +s2: U32,
  +s3: U32,
  +s4: U32,
  +s5: U32,
  +s6: U32,
  +s7: U32,
  aa: Array<U32>
) -> Array<U32> & Oct:
  (aa, Oct{s0, s1, s2, s3, s4, s5, s6, s7})

def encode.oct.g7(
  got: Array<U32> & U32,
  +s0: U32,
  +s1: U32,
  +s2: U32,
  +s3: U32,
  +s4: U32,
  +s5: U32,
  +s6: U32
) -> Array<U32> & Oct:
  (a, +s7) = got
  encode.oct.pack(s0, s1, s2, s3, s4, s5, s6, s7, a)

def encode.oct.g6(
  got: Array<U32> & U32,
  +s0: U32,
  +s1: U32,
  +s2: U32,
  +s3: U32,
  +s4: U32,
  +s5: U32,
  +i7: U32
) -> Array<U32> & Oct:
  (a, +s6) = got
  encode.oct.g7(Array.get(U32, a, i7), s0, s1, s2, s3, s4, s5, s6)

def encode.oct.g5(
  got: Array<U32> & U32,
  +s0: U32,
  +s1: U32,
  +s2: U32,
  +s3: U32,
  +s4: U32,
  +i6: U32,
  +i7: U32
) -> Array<U32> & Oct:
  (a, +s5) = got
  encode.oct.g6(Array.get(U32, a, i6), s0, s1, s2, s3, s4, s5, i7)

def encode.oct.g4(
  got: Array<U32> & U32,
  +s0: U32,
  +s1: U32,
  +s2: U32,
  +s3: U32,
  +i5: U32,
  +i6: U32,
  +i7: U32
) -> Array<U32> & Oct:
  (a, +s4) = got
  encode.oct.g5(Array.get(U32, a, i5), s0, s1, s2, s3, s4, i6, i7)

def encode.oct.g3(
  got: Array<U32> & U32,
  +s0: U32,
  +s1: U32,
  +s2: U32,
  +i4: U32,
  +i5: U32,
  +i6: U32,
  +i7: U32
) -> Array<U32> & Oct:
  (a, +s3) = got
  encode.oct.g4(Array.get(U32, a, i4), s0, s1, s2, s3, i5, i6, i7)

def encode.oct.g2(
  got: Array<U32> & U32,
  +s0: U32,
  +s1: U32,
  +i3: U32,
  +i4: U32,
  +i5: U32,
  +i6: U32,
  +i7: U32
) -> Array<U32> & Oct:
  (a, +s2) = got
  encode.oct.g3(Array.get(U32, a, i3), s0, s1, s2, i4, i5, i6, i7)

def encode.oct.g1(
  got: Array<U32> & U32,
  +s0: U32,
  +i2: U32,
  +i3: U32,
  +i4: U32,
  +i5: U32,
  +i6: U32,
  +i7: U32
) -> Array<U32> & Oct:
  (a, +s1) = got
  encode.oct.g2(Array.get(U32, a, i2), s0, s1, i3, i4, i5, i6, i7)

def encode.oct.g0(
  got: Array<U32> & U32,
  +i1: U32,
  +i2: U32,
  +i3: U32,
  +i4: U32,
  +i5: U32,
  +i6: U32,
  +i7: U32
) -> Array<U32> & Oct:
  (a, +s0) = got
  encode.oct.g1(Array.get(U32, a, i1), s0, i2, i3, i4, i5, i6, i7)

# eight samples starting at `at`, every `step` slots
def encode.oct.stride(aa: Array<U32>, +at: U32, +step: U32) -> Array<U32> & Oct:
  +i1 = (at + step : U32)
  +i2 = (i1 + step : U32)
  +i3 = (i2 + step : U32)
  +i4 = (i3 + step : U32)
  +i5 = (i4 + step : U32)
  +i6 = (i5 + step : U32)
  +i7 = (i6 + step : U32)
  encode.oct.g0(Array.get(U32, aa, at), i1, i2, i3, i4, i5, i6, i7)

def encode.col.use(got: Array<U32> & Oct, kern: Kern) -> Array<U32> & Oct:
  match got:
    case (arr, o):
      (arr, encode.dct8(o, kern))

# one frequency column, read straight from the plane
def encode.col(arr: Array<U32>, +at: U32, kern: Kern) -> Array<U32> & Oct:
  encode.col.use(encode.oct.stride(arr, at, 8), kern)

def encode.pass1(rows: List<&2, List<&2, U32>>, +kern: Kern, arr: Array<U32>, +at: U32) -> Array<U32>:
  match rows:
    case Nil{}:
      +_z = encode.kern.drop(kern)
      arr
    case h <> t:
      encode.pass1(t, kern, encode.lay(encode.dct8(encode.take(h), kern), arr, at), (at + 8 : U32))

def encode.pix.sink(aa: Array<U32>) -> U32:
  match aa:
    case ALeaf{_x}:
      0
    case ANode{xs, ys}:
      U32.or(encode.pix.sink(xs), encode.pix.sink(ys))

def encode.book.sink(book: Book) -> U32:
  match book:
    case Book{dc, ac}:
      U32.or(encode.pix.sink(dc), encode.pix.sink(ac))

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

def encode.pass.rows.done(st: Planes, kern: Kern) -> Array<U32>:
  match st:
    case Planes{src, dst, +at}:
      +_k = encode.kern.drop(kern)
      +_s = encode.pix.sink(src)
      +_at = (at - at : U32)
      dst

def encode.pass.rows.lay(got: Array<U32> & Oct, +kern: Kern, dst: Array<U32>, +at: U32) -> Planes:
  match got:
    case (src, o):
      Planes{src, encode.lay(encode.dct8(o, kern), dst, at), (at + 8 : U32)}

def encode.pass.rows.next(st: Planes, +kern: Kern) -> Planes:
  match st:
    case Planes{src, dst, +at}:
      encode.pass.rows.lay(encode.oct.stride(src, at, 1), kern, dst, at)

# eight row transforms. `left` rows are still unread.
def encode.pass.rows(left: Nat, st: Planes, +kern: Kern) -> Array<U32>:
  match left:
    case 0n:
      encode.pass.rows.done(st, kern)
    case 1n+rest:
      encode.pass.rows(rest, encode.pass.rows.next(st, kern), kern)

def encode.pass.mid(src: Array<U32>, +kern: Kern) -> Array<U32>:
  encode.pass.rows(8n, Planes{src, Jpeg.decode.plane(64), 0}, kern)

# level plane in, natural-order frequencies out
def encode.freq(src: Array<U32>, +kern: Kern) -> Array<U32>:
  encode.pass2(8n, Planes{encode.pass.mid(src, kern), Jpeg.decode.plane(64), 0}, kern)

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

def encode.sat(over: Bool, +xx: U32, +lim: U32) -> U32:
  match over:
    case True{}:
      (lim - 1 : U32)
    case False{}:
      xx

def encode.sat8(over: Bool, +vv: U32) -> U32:
  match over:
    case True{}:
      255
    case False{}:
      vv

def encode.y(+rr: U32, +gg: U32, +bb: U32) -> U32:
  U32.shrn((19595 * rr + 38470 * gg + 7471 * bb + 32768 : U32), 16n)

def encode.cb(+rr: U32, +gg: U32, +bb: U32) -> U32:
  U32.shrn((32768 * bb + 8421376 - 11059 * rr - 21709 * gg : U32), 16n)

def encode.cr(+rr: U32, +gg: U32, +bb: U32) -> U32:
  U32.shrn((32768 * rr + 8421376 - 27439 * gg - 5329 * bb : U32), 16n)

def encode.ych(+rr: U32, +gg: U32, +bb: U32) -> U32:
  +v = encode.y(rr, gg, bb)
  encode.sat8(U32.is_gt(v, 255), v)

def encode.cbch(+rr: U32, +gg: U32, +bb: U32) -> U32:
  +v = encode.cb(rr, gg, bb)
  encode.sat8(U32.is_gt(v, 255), v)

def encode.crch(+rr: U32, +gg: U32, +bb: U32) -> U32:
  +v = encode.cr(rr, gg, bb)
  encode.sat8(U32.is_gt(v, 255), v)

def encode.chan.w(+ch: U32, +rr: U32, +gg: U32, +bb: U32) -> U32:
  match ch:
    case 0:
      encode.ych(rr, gg, bb)
    case 1:
      encode.cbch(rr, gg, bb)
    case _:
      encode.crch(rr, gg, bb)

def encode.chan(+pix: U32, +ch: U32) -> U32:
  encode.chan.w(ch, U32.and(U32.shrn(pix, 16n), 255), U32.and(U32.shrn(pix, 8n), 255), U32.and(pix, 255))

# the first `left` samples, then the rest of the list is unused
def encode.pix.load(left: Nat, px: List<&2, U32>, aa: Array<U32>, +ii: U32) -> Array<U32>:
  match left px:
    case 0n rest:
      +_d = encode.drop(rest)
      aa
    case 1n+k Nil{}:
      aa
    case 1n+k +h <> t:
      encode.pix.load(k, t, Array.set(U32, aa, ii, h), (ii + 1 : U32))

def encode.sample.use(got: Array<U32> & U32, +ch: U32) -> Array<U32> & U32:
  (a, pix) = got
  (a, encode.chan(pix, ch))

# one index into the sample array, instead of a walk from the head of the list
def encode.sample(aa: Array<U32>, +ww: U32, +hh: U32, +xx: U32, +yy: U32, +ch: U32) -> Array<U32> & U32:
  encode.sample.use(Array.get(U32, aa,
    (encode.sat(U32.is_ge(yy, hh), yy, hh) * ww + encode.sat(U32.is_ge(xx, ww), xx, ww) : U32)), ch)

# both samples are the neutral level
def encode.flat.both(aa: Bool, bb: Bool) -> Bool:
  match aa:
    case False{}:
      match bb:
        case _k:
          False{}
    case True{}:
      bb

def encode.rowpix.step(+ss: U32, got: Array<U32> & List<&2, U32> & Bool) -> Array<U32> & List<&2, U32> & Bool:
  (a, rest, flat) = got
  (a, ss <> rest, encode.flat.both(U32.is_eq(ss, 128), flat))

def encode.rowpix.one(+ss: U32, aa: Array<U32>) -> Array<U32> & List<&2, U32> & Bool:
  (aa, ss <> Nil{}, encode.flat.both(U32.is_eq(ss, 128), True{}))

# `got` is the sample at x. `left` counts it and the samples after it.
def encode.rowpix(
  left: Nat,
  got: Array<U32> & U32,
  +ww: U32,
  +hh: U32,
  +xx: U32,
  +yy: U32,
  +ch: U32
) -> Array<U32> & List<&2, U32> & Bool:
  match left:
    case 0n:
      (a, s) = got
      encode.rowpix.one(s, a)
    case 1n+0n:
      (a, s) = got
      encode.rowpix.one(s, a)
    case 1n+1n+q:
      (a, s) = got
      encode.rowpix.step(s, encode.rowpix(1n+q, encode.sample(a, ww, hh, (xx + 1 : U32), yy, ch), ww, hh,
        (xx + 1 : U32), yy, ch))

def encode.rows.join(
  +row: List<&2, U32>,
  rf: Bool,
  rest: Array<U32> & List<&2, List<&2, U32>> & Bool
) -> Array<U32> & List<&2, List<&2, U32>> & Bool:
  (a, tail, flat) = rest
  (a, row <> tail, encode.flat.both(rf, flat))

def encode.rows.one(+row: List<&2, U32>, rf: Bool, aa: Array<U32>) -> Array<U32> & List<&2, List<&2, U32>> & Bool:
  (aa, row <> Nil{}, rf)

# `got` is the row at y. `left` counts it and the rows after it.
def encode.rows(
  left: Nat,
  got: Array<U32> & List<&2, U32> & Bool,
  +ww: U32,
  +hh: U32,
  +xx: U32,
  +yy: U32,
  +ch: U32
) -> Array<U32> & List<&2, List<&2, U32>> & Bool:
  match left:
    case 0n:
      (a, row, rf) = got
      encode.rows.one(row, rf, a)
    case 1n+0n:
      (a, row, rf) = got
      encode.rows.one(row, rf, a)
    case 1n+1n+q:
      (a, row, rf) = got
      encode.rows.join(row, rf, encode.rows(1n+q, encode.rowpix(8n, encode.sample(a, ww, hh, xx, (yy + 1 : U32), ch),
        ww, hh, xx, (yy + 1 : U32), ch), ww, hh, xx, (yy + 1 : U32), ch))

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
def encode.zzq.go(
  rest: List<&2, U32>,
  got: Array<U32> & U32,
  qv: U32 & List<&2, U32>,
  acc: List<&2, U32>
) -> List<&2, U32>:
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
def encode.zz(
  flat: Bool,
  rows: List<&2, List<&2, U32>>,
  +kern: Kern,
  +zig: List<&2, U32>,
  +qs: List<&2, U32>
) -> List<&2, U32>:
  match flat:
    case True{}:
      +_r = encode.droprows(rows)
      +_k = encode.kern.drop(kern)
      +_g = encode.drop(zig)
      +_q = encode.drop(qs)
      List.replicate(U32, 64n, 0)
    case False{}:
      encode.zzq(zig, encode.fdct.go(encode.pass1(encode.levels(rows), kern, Jpeg.decode.plane(64), 0), kern), qs, [])

def encode.block.pair(got: Book & U32 & Put, aa: Array<U32>) -> Array<U32> & Book & U32 & Put:
  match got:
    case (book, +dc, bit):
      (aa, book, dc, bit)

def encode.block.use(
  book: Book,
  pp: Put,
  +pred: U32,
  got: Array<U32> & List<&2, List<&2, U32>> & Bool,
  +kern: Kern,
  +zig: List<&2, U32>,
  +qs: List<&2, U32>
) -> Array<U32> & Book & U32 & Put:
  (a, rows, flat) = got
  encode.block.pair(encode.block.go(book, pp, pred, encode.zz(flat, rows, kern, zig, qs)), a)

def encode.block(
  book: Book,
  pp: Put,
  +pred: U32,
  aa: Array<U32>,
  +ww: U32,
  +hh: U32,
  +xx: U32,
  +yy: U32,
  +ch: U32,
  ctx: Ctx
) -> Array<U32> & Book & U32 & Put:
  match ctx:
    case Ctx{+kern, +zig, +qs}:
      encode.block.use(book, pp, pred,
        encode.rows(8n, encode.rowpix(8n, encode.sample(aa, ww, hh, xx, yy, ch), ww, hh, xx, yy, ch),
          ww, hh, xx, yy, ch),
        kern, zig, qs)

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

def encode.step.end(
  got: Array<U32> & Book & U32 & Put,
  +ydc: U32,
  +bdc: U32
) -> Array<U32> & Book & U32 & U32 & U32 & Put:
  (a, book, rdc, bit) = got
  (a, book, ydc, bdc, rdc, bit)

def encode.scan.hit(got: Array<U32> & Put, arr: Array<U32>) -> Scan:
  (ac, bit) = got
  Scan{arr, 0, ac, bit}

def encode.scan.skip(sc: Scan, +cc: U32) -> Scan:
  match sc:
    case Scan{arr, +run, ac, bit}:
      +_c = (cc - cc : U32)
      Scan{arr, (run + 1 : U32), ac, bit}

def encode.scan.keep(sc: Scan, +cc: U32) -> Scan:
  match sc:
    case Scan{arr, +run, ac, bit}:
      encode.scan.hit(encode.ac.step(cc, run, (ac, bit)), arr)

def encode.scan.bump(zz: Bool, sc: Scan, +cc: U32) -> Scan:
  match zz:
    case True{}:
      encode.scan.skip(sc, cc)
    case False{}:
      encode.scan.keep(sc, cc)

# step is 1, so the frequency is the coefficient
def encode.scan.val(got: Array<U32> & U32, +run: U32, st: Array<U32> & Put) -> Scan:
  (arr, +c) = got
  (ac, bit) = st
  encode.scan.bump(U32.is_eq(c, 0), Scan{arr, run, ac, bit}, c)

def encode.scan.step(sc: Scan, +gg: U32) -> Scan:
  match sc:
    case Scan{arr, +run, ac, bit}:
      encode.scan.val(Array.get(U32, arr, gg), run, (ac, bit))

def encode.scan.end(sc: Scan) -> Array<U32> & Put:
  match sc:
    case Scan{arr, +run, ac, bit}:
      +_s = encode.pix.sink(arr)
      encode.eob.on(U32.is_gt(run, 0), (ac, bit))

# the rest of the zigzag, indexed in the frequency plane
def encode.scan.ac(rest: List<&2, U32>, sc: Scan) -> Array<U32> & Put:
  match rest:
    case Nil{}:
      encode.scan.end(sc)
    case +g <> gt:
      encode.scan.ac(gt, encode.scan.step(sc, g))

def encode.scan.book(got: Array<U32> & Put, dc: Array<U32>, +dd: U32) -> Book & U32 & Put:
  (ac, p) = got
  (Book{dc, ac}, dd, p)

def encode.scan.join(
  got: Array<U32> & Put,
  ac: Array<U32>,
  +dd: U32,
  rest: List<&2, U32>,
  arr: Array<U32>
) -> Book & U32 & Put:
  (dc, p) = got
  encode.scan.book(encode.scan.ac(rest, Scan{arr, 0, ac, p}), dc, dd)

def encode.scan.dc(
  book: Book,
  pp: Put,
  +pred: U32,
  +d0: U32,
  rest: List<&2, U32>,
  arr: Array<U32>
) -> Book & U32 & Put:
  match book:
    case Book{dc, ac}:
      +d = encode.dcbias(d0)
      encode.scan.join(encode.dcdiff(dc, pp, d, pred), ac, d, rest, arr)

def encode.scan.open(
  rest: List<&2, U32>,
  got: Array<U32> & U32,
  book: Book,
  pp: Put,
  +pred: U32
) -> Book & U32 & Put:
  (arr, +v) = got
  encode.scan.dc(book, pp, pred, v, rest, arr)

def encode.scan.none(book: Book, pp: Put, arr: Array<U32>, +pred: U32) -> Book & U32 & Put:
  +_s = encode.pix.sink(arr)
  +_p = (pred - pred : U32)
  (book, 1024, pp)

# DC at the first zigzag index, then the AC run, both read from the frequency plane
def encode.scan(book: Book, pp: Put, +pred: U32, arr: Array<U32>, zig: List<&2, U32>) -> Book & U32 & Put:
  match zig:
    case Nil{}:
      encode.scan.none(book, pp, arr, pred)
    case +g <> gt:
      encode.scan.open(gt, Array.get(U32, arr, g), book, pp, pred)

def encode.chan.flat(
  plane: Array<U32>,
  book: Book,
  pp: Put,
  +pred: U32,
  +kern: Kern,
  +zig: List<&2, U32>,
  +qs: List<&2, U32>
) -> Book & U32 & Put:
  +_s = encode.pix.sink(plane)
  +_k = encode.kern.drop(kern)
  +_g = encode.drop(zig)
  +_q = encode.drop(qs)
  encode.block.go(book, pp, pred, List.replicate(U32, 64n, 0))

def encode.chan.mix(
  plane: Array<U32>,
  book: Book,
  pp: Put,
  +pred: U32,
  +kern: Kern,
  zig: List<&2, U32>,
  qs: List<&2, U32>
) -> Book & U32 & Put:
  +_q = encode.drop(qs)
  encode.scan(book, pp, pred, encode.freq(plane, kern), zig)

def encode.chan.go(
  flat: Bool,
  plane: Array<U32>,
  book: Book,
  pp: Put,
  +pred: U32,
  +kern: Kern,
  +zig: List<&2, U32>,
  +qs: List<&2, U32>
) -> Book & U32 & Put:
  match flat:
    case True{}:
      encode.chan.flat(plane, book, pp, pred, kern, zig, qs)
    case False{}:
      encode.chan.mix(plane, book, pp, pred, kern, zig, qs)

def encode.pix.at(aa: Array<U32>, +ww: U32, +hh: U32, +xx: U32, +yy: U32) -> Array<U32> & U32:
  Array.get(U32, aa, (encode.sat(U32.is_ge(yy, hh), yy, hh) * ww + encode.sat(U32.is_ge(xx, ww), xx, ww) : U32))

def encode.tile.store(
  got: Array<U32> & U32,
  ys: Array<U32>,
  bs: Array<U32>,
  rs: Array<U32>,
  fy: Bool,
  fb: Bool,
  fr: Bool,
  +ii: U32
) -> Tile:
  (pix, +p) = got
  +r = U32.and(U32.shrn(p, 16n), 255)
  +g = U32.and(U32.shrn(p, 8n), 255)
  +b = U32.and(p, 255)
  +y8 = encode.ych(r, g, b)
  +b8 = encode.cbch(r, g, b)
  +r8 = encode.crch(r, g, b)
  Tile{pix, Array.set(U32, ys, ii, (y8 - 128 : U32)), Array.set(U32, bs, ii, (b8 - 128 : U32)),
    Array.set(U32, rs, ii, (r8 - 128 : U32)), encode.flat.both(U32.is_eq(y8, 128), fy),
    encode.flat.both(U32.is_eq(b8, 128), fb), encode.flat.both(U32.is_eq(r8, 128), fr)}

def encode.tile.pix(tt: Tile, +ww: U32, +hh: U32, +xx: U32, +yy: U32, +ii: U32) -> Tile:
  match tt:
    case Tile{pix, ys, bs, rs, fy, fb, fr}:
      encode.tile.store(encode.pix.at(pix, ww, hh, xx, yy), ys, bs, rs, fy, fb, fr, ii)

def encode.tile.row(left: Nat, tt: Tile, +ww: U32, +hh: U32, +xx: U32, +yy: U32, +ii: U32) -> Tile:
  match left:
    case 0n:
      +_u = (ww + hh + xx + yy + ii : U32)
      tt
    case 1n+k:
      encode.tile.row(k, encode.tile.pix(tt, ww, hh, xx, yy, ii), ww, hh, (xx + 1 : U32), yy, (ii + 1 : U32))

def encode.tile.rows(left: Nat, tt: Tile, +ww: U32, +hh: U32, +xx: U32, +yy: U32, +ii: U32) -> Tile:
  match left:
    case 0n:
      +_u = (ww + hh + xx + yy + ii : U32)
      tt
    case 1n+k:
      encode.tile.rows(k, encode.tile.row(8n, tt, ww, hh, xx, yy, ii), ww, hh, xx, (yy + 1 : U32), (ii + 8 : U32))

# three level planes from one walk of this MCU
def encode.tile(aa: Array<U32>, +ww: U32, +hh: U32, +xx: U32, +yy: U32) -> Tile:
  encode.tile.rows(8n, Tile{aa, Jpeg.decode.plane(64), Jpeg.decode.plane(64), Jpeg.decode.plane(64), True{}, True{},
    True{}}, ww, hh, xx, yy, 0)

def encode.chan.pair(got: Book & U32 & Put, aa: Array<U32>) -> Array<U32> & Book & U32 & Put:
  match got:
    case (book, +dc, bit):
      (aa, book, dc, bit)

def encode.step.cr(
  got: Book & U32 & Put,
  aa: Array<U32>,
  rs: Array<U32>,
  fr: Bool,
  +ydc: U32,
  +pr: U32,
  +kern: Kern,
  +zig: List<&2, U32>,
  +qs: List<&2, U32>
) -> Array<U32> & Book & U32 & U32 & U32 & Put:
  (book, +bdc, bit) = got
  encode.step.end(encode.chan.pair(encode.chan.go(fr, rs, book, bit, pr, kern, zig, qs), aa), ydc, bdc)

def encode.step.cb(
  got: Book & U32 & Put,
  aa: Array<U32>,
  bs: Array<U32>,
  rs: Array<U32>,
  fb: Bool,
  fr: Bool,
  +pb: U32,
  +pr: U32,
  +kern: Kern,
  +zig: List<&2, U32>,
  +qs: List<&2, U32>
) -> Array<U32> & Book & U32 & U32 & U32 & Put:
  (book, +ydc, bit) = got
  encode.step.cr(encode.chan.go(fb, bs, book, bit, pb, kern, zig, qs), aa, rs, fr, ydc, pr, kern, zig, qs)

def encode.step.tile(
  tt: Tile,
  book: Book,
  bit: Put,
  +py: U32,
  +pb: U32,
  +pr: U32,
  +kern: Kern,
  +zig: List<&2, U32>,
  +qs: List<&2, U32>
) -> Array<U32> & Book & U32 & U32 & U32 & Put:
  match tt:
    case Tile{pix, ys, bs, rs, fy, fb, fr}:
      encode.step.cb(encode.chan.go(fy, ys, book, bit, py, kern, zig, qs), pix, bs, rs, fb, fr, pb, pr, kern, zig, qs)

# one walk of the MCU, then Y, Cb, and Cr. Each clipped DC is the next predictor.
def encode.step.y(
  aa: Array<U32>,
  book: Book,
  bit: Put,
  +py: U32,
  +pb: U32,
  +pr: U32,
  +xx: U32,
  +yy: U32,
  +ww: U32,
  +hh: U32,
  +ctx: Ctx
) -> Array<U32> & Book & U32 & U32 & U32 & Put:
  match ctx:
    case Ctx{+kern, +zig, +qs}:
      encode.step.tile(encode.tile(aa, ww, hh, xx, yy), book, bit, py, pb, pr, kern, zig, qs)

def encode.mcus.done(got: Array<U32> & Book & U32 & U32 & U32 & Put) -> Put:
  (a, book, ydc, bdc, rdc, bit) = got
  +_s = encode.pix.sink(a)
  +_b = encode.book.sink(book)
  +_u = (ydc + bdc + rdc : U32)
  bit

def encode.mcus(
  left: Nat,
  got: Array<U32> & Book & U32 & U32 & U32 & Put,
  +mx: U32,
  +my: U32,
  +mw: U32,
  +ww: U32,
  +hh: U32,
  +ctx: Ctx
) -> Put:
  match left:
    case 0n:
      encode.mcus.done(got)
    case 1n+nleft:
      (a, book, py, pb, pr, bit) = got
      +x = (mx * 8 : U32)
      +y = (my * 8 : U32)
      +more = U32.is_lt((mx + 1 : U32), mw)
      encode.mcus(nleft, encode.step.y(a, book, bit, py, pb, pr, x, y, ww, hh, ctx), encode.nx(more, mx),
        encode.ny(more, my), mw, ww, hh, ctx)

def encode.finish(
  +ww: U32,
  +hh: U32,
  ent: List<&2, U32>,
  +dcc: List<&2, U32>,
  +dcs: List<&2, U32>,
  +acc: List<&2, U32>,
  +acs: List<&2, U32>
) -> List<&2, U32>:
  encode.join(encode.header(ww, hh, dcc, dcs, acc, acs), encode.join(ent, Jpeg.eoi()))

# samples before a mismatch were packed 8421504, so that prefix can be replayed
def encode.hunt.nil(+seen: U32) -> Bool & List<&2, U32>:
  (False{}, List.replicate(U32, U32.to_nat(seen), 8421504))

def encode.hunt.mix(+seen: U32, +hh: U32, tt: List<&2, U32>) -> Bool & List<&2, U32>:
  (False{}, List.append(&2, U32, List.replicate(U32, U32.to_nat(seen), 8421504), hh <> tt))

def encode.hunt.rest(xs: List<&2, U32>) -> Bool & List<&2, U32>:
  +_d = encode.drop(xs)
  (True{}, [])

# no samples remain after `h`
def encode.hunt.done(eq: Bool, +hh: U32, xs: List<&2, U32>, +seen: U32) -> Bool & List<&2, U32>:
  match eq:
    case False{}:
      encode.hunt.mix(seen, hh, xs)
    case True{}:
      encode.hunt.rest(xs)

# the list ended before the area did
def encode.hunt.empty(eq: Bool, +hh: U32, +seen: U32) -> Bool & List<&2, U32>:
  match eq:
    case False{}:
      encode.hunt.mix(seen, hh, [])
    case True{}:
      encode.hunt.nil((seen + 1 : U32))

# `h` was just read. `left` samples remain after it. `seen` neutral samples precede it.
def encode.hunt.go(left: Nat, xs: List<&2, U32>, eq: Bool, +hh: U32, +seen: U32) -> Bool & List<&2, U32>:
  match left:
    case 0n:
      encode.hunt.done(eq, hh, xs, seen)
    case 1n+p:
      match xs:
        case Nil{}:
          encode.hunt.empty(eq, hh, seen)
        case +s <> u:
          match eq:
            case False{}:
              encode.hunt.mix(seen, hh, s <> u)
            case True{}:
              encode.hunt.go(p, u, U32.is_eq(s, 8421504), s, (seen + 1 : U32))

# the area was one colour. `seen` of those samples are replayed only on a miss.
def encode.hold.no(+seen: U32, +cc: U32, tail: List<&2, U32>) -> Bool & List<&2, U32>:
  (False{}, List.append(&2, U32, List.replicate(U32, U32.to_nat(seen), cc), tail))

def encode.hold.yes(xs: List<&2, U32>, +cc: U32, +hh: U32, +seen: U32) -> Bool & List<&2, U32>:
  +_d = encode.drop(xs)
  +_u = (cc + hh + seen : U32)
  (True{}, [])

def encode.hold.done(eq: Bool, +hh: U32, xs: List<&2, U32>, +cc: U32, +seen: U32) -> Bool & List<&2, U32>:
  match eq:
    case False{}:
      encode.hold.no(seen, cc, hh <> xs)
    case True{}:
      encode.hold.yes(xs, cc, hh, seen)

def encode.hold.empty(eq: Bool, +hh: U32, +cc: U32, +seen: U32) -> Bool & List<&2, U32>:
  match eq:
    case False{}:
      encode.hold.no(seen, cc, hh <> [])
    case True{}:
      +_h = (hh - hh : U32)
      encode.hold.no((seen + 1 : U32), cc, [])

# `h` was just read. `left` samples remain after it. `seen` copies of `c` precede it.
def encode.hold.go(left: Nat, xs: List<&2, U32>, eq: Bool, +hh: U32, +cc: U32, +seen: U32) -> Bool & List<&2, U32>:
  match left:
    case 0n:
      encode.hold.done(eq, hh, xs, cc, seen)
    case 1n+p:
      match xs:
        case Nil{}:
          encode.hold.empty(eq, hh, cc, seen)
        case +s <> u:
          match eq:
            case False{}:
              encode.hold.no(seen, cc, hh <> (s <> u))
            case True{}:
              encode.hold.go(p, u, U32.is_eq(s, cc), s, cc, (seen + 1 : U32))

# 0 neutral, 1 one other colour, 2 mixed. A short list stays mixed: the plane's gaps are 0.
def encode.watch.neu(got: Bool & List<&2, U32>) -> U32 & U32 & List<&2, U32>:
  (ok, px) = got
  match ok:
    case True{}:
      +_d = encode.drop(px)
      (0, 0, [])
    case False{}:
      (2, 0, px)

def encode.watch.sol(got: Bool & List<&2, U32>, +hh: U32) -> U32 & U32 & List<&2, U32>:
  (ok, px) = got
  match ok:
    case True{}:
      +_d = encode.drop(px)
      (1, hh, [])
    case False{}:
      +_h = (hh - hh : U32)
      (2, 0, px)

def encode.watch.pick(neu: Bool, kk: Nat, tt: List<&2, U32>, +hh: U32) -> U32 & U32 & List<&2, U32>:
  match neu:
    case True{}:
      encode.watch.neu(encode.hunt.go(kk, tt, True{}, hh, 0))
    case False{}:
      encode.watch.sol(encode.hold.go(kk, tt, True{}, hh, hh, 0), hh)

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
  U32.or(code, U32.shln(buf, U32.to_nat(len)))

def encode.pack.full(full: Bool, out: List<&2, U32>, +buf: U32, +nn: U32, +len: U32, +code: U32) -> Put:
  match full:
    case True{}:
      encode.stuff(out, encode.pack.byte(buf, len, code))
    case False{}:
      Put{out, encode.pack.byte(buf, len, code), (nn + len : U32)}

def encode.pack.keep(pp: Put, +lo: U32, +rest: U32) -> Put:
  match pp:
    case Put{out, _buf, _n}:
      Put{out, rest, lo}

def encode.pack.span(out: List<&2, U32>, +buf: U32, +nn: U32, +len: U32, +code: U32) -> Put:
  +room = (8 - nn : U32)
  +lo = (len - room : U32)
  encode.pack.keep(encode.stuff(out, U32.or(U32.shrn(code, U32.to_nat(lo)), U32.shln(buf,
    U32.to_nat(room)))), lo, U32.and((U32.shln(1, U32.to_nat(lo)) - 1 : U32), code))

def encode.pack.fit(fit: Bool, out: List<&2, U32>, +buf: U32, +nn: U32, +len: U32, +code: U32) -> Put:
  match fit:
    case True{}:
      encode.pack.full(U32.is_eq((nn + len : U32), 8), out, buf, nn, len, code)
    case False{}:
      encode.pack.span(out, buf, nn, len, code)

def encode.pack(pp: Put, +len: U32, +code: U32) -> Put:
  match pp:
    case Put{out, +buf, +n}:
      encode.pack.fit(U32.is_le((n + len : U32), 8), out, buf, n, len, code)

# Annex K luminance: a zero block is DC 00 then EOB 1010
def encode.zput(pp: Put) -> Put:
  encode.pack(pp, 6, 10)

def encode.ztri(pp: Put) -> Put:
  encode.zput(encode.zput(encode.zput(pp)))

def encode.neutral.mcus(left: Nat, pp: Put) -> Put:
  match left:
    case 0n:
      pp
    case 1n+nleft:
      encode.neutral.mcus(nleft, encode.ztri(pp))

# the entropy-coded bytes of a neutral picture: every MCU is three zero blocks
def encode.neutral(+ww: U32, +hh: U32) -> List<&2, U32>:
  +mw = U32.div((ww + 7 : U32), 8)
  +mh = U32.div((hh + 7 : U32), 8)
  encode.pad(encode.neutral.mcus(U32.to_nat((mw * mh : U32)), encode.put0()))

# the rest of a solid picture is the same DC, so each later block is a zero difference
def encode.solid.end(got: Array<U32> & Book & U32 & Put) -> Put:
  (a, book, +dc, bit) = got
  +_s = encode.pix.sink(a)
  +_b = encode.book.sink(book)
  +_d = (dc - dc : U32)
  bit

def encode.solid.cr(got: Array<U32> & Book & U32 & Put, +ctx: Ctx) -> Put:
  (a, book, +dc, bit) = got
  +_d = (dc - dc : U32)
  encode.solid.end(encode.block(book, bit, 1024, a, 1, 1, 0, 0, 2, ctx))

def encode.solid.cb(got: Array<U32> & Book & U32 & Put, +ctx: Ctx) -> Put:
  (a, book, +dc, bit) = got
  +_d = (dc - dc : U32)
  encode.solid.cr(encode.block(book, bit, 1024, a, 1, 1, 0, 0, 1, ctx), ctx)

def encode.solid.y(aa: Array<U32>, book: Book, bit: Put, +ctx: Ctx) -> Put:
  encode.solid.cb(encode.block(book, bit, 1024, aa, 1, 1, 0, 0, 0, ctx), ctx)

# one colour repeated. The first MCU is that block; every later MCU is three zero differences.
# The result is the entropy-coded bytes.
def encode.solid(+ww: U32, +hh: U32, +color: U32) -> List<&2, U32>:
  +mw = U32.div((ww + 7 : U32), 8)
  +mh = U32.div((hh + 7 : U32), 8)
  +n = (mw * mh : U32)
  encode.pad(encode.neutral.mcus(U32.to_nat((n - 1 : U32)),
    encode.solid.y(Array.set(U32, Jpeg.decode.plane(1), 0, color),
      encode.book(encode.dccounts(), encode.dcsyms(), encode.accounts(), encode.acsyms()),
      encode.put0(), encode.ctx())))

# the entropy-coded bytes of any other picture, MCU by MCU
def encode.go(+ww: U32, +hh: U32, px: List<&2, U32>) -> List<&2, U32>:
  +mw = U32.div((ww + 7 : U32), 8)
  +mh = U32.div((hh + 7 : U32), 8)
  +area = (ww * hh : U32)
  book = encode.book(encode.dccounts(), encode.dcsyms(), encode.accounts(), encode.acsyms())
  encode.pad(encode.mcus(U32.to_nat((mw * mh : U32)),
    (encode.pix.load(U32.to_nat(area), px, Jpeg.decode.plane(area), 0), book, 1024, 1024, 1024,
      encode.put0()), 0, 0, mw, ww, hh, encode.ctx()))

# the entropy-coded bytes, by what the watch found: neutral, one solid colour, or anything else
def encode.dispatch.b(neu: Bool, sol: Bool, +color: U32, px: List<&2, U32>, +ww: U32, +hh: U32) -> List<&2, U32>:
  match neu:
    case True{}:
      +_c = (color - color : U32)
      +_d = encode.drop(px)
      +_s = Bool.not(sol)
      encode.neutral(ww, hh)
    case False{}:
      match sol:
        case True{}:
          +_d = encode.drop(px)
          encode.solid(ww, hh, color)
        case False{}:
          +_c = (color - color : U32)
          encode.go(ww, hh, px)

# the watch's tag, 0 neutral, 1 solid, 2 mixed, asked with U32.is_eq so a law reaches every tag
def encode.dispatch(+tag: U32, +color: U32, px: List<&2, U32>, +ww: U32, +hh: U32) -> List<&2, U32>:
  encode.dispatch.b(U32.is_eq(tag, 0), U32.is_eq(tag, 1), color, px, ww, hh)

# the watch's answer, dispatched
def encode.arm.use(got: U32 & U32 & List<&2, U32>, +ww: U32, +hh: U32) -> List<&2, U32>:
  match got:
    case (+tag, +color, px):
      encode.dispatch(tag, color, px, ww, hh)

# the entropy-coded bytes of an accepted size
def encode.arm(+ww: U32, +hh: U32, px: List<&2, U32>) -> List<&2, U32>:
  encode.arm.use(encode.watch(U32.to_nat((ww * hh : U32)), px), ww, hh)

def encode.pick(bad: Bool, +ww: U32, +hh: U32, px: List<&2, U32>) -> List<&2, U32>:
  match bad:
    case True{}:
      +_d = encode.drop(px)
      encode.join(Jpeg.soi(), Jpeg.eoi())
    case False{}:
      encode.finish(ww, hh, encode.arm(ww, hh, px), encode.dccounts(), encode.dcsyms(), encode.accounts(),
        encode.acsyms())

# baseline sequential 4:4:4 JPEG bytes for packed RGB samples, or SOI EOI when the size is rejected
def encode(+ww: U32, +hh: U32, px: List<&2, U32>) -> List<&2, U32>:
  encode.pick(encode.bad(ww, hh), ww, hh, px)
