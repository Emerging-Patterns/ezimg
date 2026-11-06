# src/jpeg_enc: baseline JPEG encode. Sequential 8-bit Huffman (SOF0) and JFIF APP0.
# Colour is 4:4:4 YCbCr, no subsampling: one 8 by 8 block per component per MCU.
# Samples are packed 0xAARRGGBB, the layout decode returns; the alpha byte is ignored.
# Quantisation is T.81 Annex K's tables K.1 (luminance) and K.2 (chrominance),
# scaled for a quality of 1 to 100 as the IJG library scales them, so a file is
# the size libjpeg writes at that quality. Y uses K.1 and the Annex K luminance
# Huffman tables (K.3, K.5); Cb and Cr use K.2 and the chrominance tables (K.4, K.6).
# The forward DCT (T.81 A.3.3) pairs samples that share a cosine weight, then
# rounds once with the same fixed-point product as a matrix column; the column
# pass divides each coefficient by its quantisation step, rounding half away
# from zero, as libjpeg does.
# A coefficient indexes its symbol in a book written out from the Annex K tables. The scan does not walk the table.
# An MCU reads each pixel once and keeps the three level planes in arrays.
# A neutral plane (every sample 128) is an all-zero block, coded without the DCT.
# The coding is lossy. Progressive and arithmetic frames are not written.
# Width and height must sit in 1..65535; anything else is SOI then EOI.

import Base
import ./jpeg.bend as Jpeg

# bytes emitted so far (newest first), the open byte, and how many bits it holds
type Put is Data:
  Put{out: List<&2, U32>, buf: U32, n: U32}

# cosine weights shared by symmetric samples: DC, two even weights, four odd weights
type Kern is Data:
  Kern{k0: U32, k2: U32, k6: U32, o0: U32, o1: U32, o2: U32, o3: U32}

# the cosine kernel, the zigzag, and each table's quantisation steps, one Oct per frequency column
type Ctx is Data:
  Ctx{kern: Kern, zig: List<&2, U32>, ql: List<&2, Oct>, qc: List<&2, Oct>}

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

# frequency plane, the open zero run, and the AC coder
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

# the first value when bb holds, else the second
def encode.either(bb: Bool, +aa: U32, +cc: U32) -> U32:
  match bb:
    case True{}:
      +_c = cc
      aa
    case False{}:
      +_a = aa
      cc

# T.81 Annex K, Table K.1: the luminance quantisation table, row by row
def encode.lumq() -> List<&2, U32>:
  [16, 11, 10, 16, 24, 40, 51, 61, 12, 12, 14, 19, 26, 58, 60, 55, 14, 13, 16, 24, 40, 57, 69, 56, 14, 17, 22, 29, 51,
    87, 80, 62, 18, 22, 37, 56, 68, 109, 103, 77, 24, 35, 55, 64, 81, 104, 113, 92, 49, 64, 78, 87, 103, 121, 120, 101,
    72, 92, 95, 98, 112, 100, 103, 99]

# T.81 Annex K, Table K.2: the chrominance quantisation table, row by row
def encode.chrq() -> List<&2, U32>:
  [17, 18, 24, 47, 99, 99, 99, 99, 18, 21, 26, 66, 99, 99, 99, 99, 24, 26, 56, 99, 99, 99, 99, 99, 47, 66, 99, 99, 99,
    99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99,
    99, 99, 99, 99, 99, 99]

# a quality below 1 is 1 and one above 100 is 100, as the IJG library takes it (jpeg_quality_scaling)
def encode.qual(+qq: U32) -> U32:
  encode.either(U32.is_lt(qq, 1), 1, encode.either(U32.is_gt(qq, 100), 100, qq))

# the IJG percentage of the Annex K tables for a quality of 1 to 100: 5000 / q below 50, else 200 - 2 q
def encode.qscale(+qq: U32) -> U32:
  encode.either(U32.is_lt(qq, 50), U32.div(5000, qq), (200 - qq * 2 : U32))

# one table entry at a percentage: (t s + 50) / 100, kept in 1 to 255 for a baseline table, as the IJG library
# rounds and clamps it (jpeg_add_quant_table with force_baseline)
def encode.qstep(+tt: U32, +ss: U32) -> U32:
  +vv = U32.div((tt * ss + 50 : U32), 100)
  encode.either(U32.is_lt(vv, 1), 1, encode.either(U32.is_gt(vv, 255), 255, vv))

# each entry of a table at a percentage
def encode.qnat(xs: List<&2, U32>, +ss: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      +_s = ss
      Nil{}
    case +tt <> rest:
      encode.qstep(tt, ss) <> encode.qnat(rest, ss)

# a table for a quality, row by row
def encode.qrows(+base: List<&2, U32>, +qq: U32) -> List<&2, U32>:
  encode.qnat(base, encode.qscale(encode.qual(qq)))

# a table's entries in zigzag order, as DQT holds them (T.81 B.2.4.1)
def encode.qzig(zig: List<&2, U32>, +qn: List<&2, U32>) -> List<&2, U32>:
  match zig:
    case Nil{}:
      +_d = encode.len(qn)
      Nil{}
    case +gg <> rest:
      Jpeg.decode.at(qn, gg) <> encode.qzig(rest, qn)

# the DQT entries of a table for a quality
def encode.qz(+base: List<&2, U32>, +qq: U32) -> List<&2, U32>:
  encode.qzig(Jpeg.decode.zig(), encode.qrows(base, qq))

# frequency column cc of a table, row by row
def encode.qcol(+qn: List<&2, U32>, +cc: U32) -> Oct:
  Oct{Jpeg.decode.at(qn, cc), Jpeg.decode.at(qn, (cc + 8 : U32)), Jpeg.decode.at(qn, (cc + 16 : U32)),
    Jpeg.decode.at(qn, (cc + 24 : U32)), Jpeg.decode.at(qn, (cc + 32 : U32)), Jpeg.decode.at(qn, (cc + 40 : U32)),
    Jpeg.decode.at(qn, (cc + 48 : U32)), Jpeg.decode.at(qn, (cc + 56 : U32))}

# a table's eight frequency columns, as the column pass divides them
def encode.qcols(+qn: List<&2, U32>) -> List<&2, Oct>:
  [encode.qcol(qn, 0), encode.qcol(qn, 1), encode.qcol(qn, 2), encode.qcol(qn, 3), encode.qcol(qn, 4),
    encode.qcol(qn, 5), encode.qcol(qn, 6), encode.qcol(qn, 7)]

# both tables: luminance as table 0, chrominance as table 1
def encode.dqt(+qq: U32) -> List<&2, U32>:
  encode.seg(219, 0 <> encode.join(encode.qz(encode.lumq(), qq), 1 <> encode.qz(encode.chrq(), qq)))

# Y sampled 1 by 1 with table 0, Cb and Cr 1 by 1 with table 1
def encode.sofbody(+ww: U32, +hh: U32) -> List<&2, U32>:
  [8, U32.shrn(hh, 8n), U32.and(hh, 255), U32.shrn(ww, 8n), U32.and(ww, 255), 3, 1, 17, 0, 2, 17, 1, 3, 17, 1]

def encode.sof(+ww: U32, +hh: U32) -> List<&2, U32>:
  encode.seg(192, encode.sofbody(ww, hh))

# T.81 Annex K, Table K.3: luminance DC code lengths
def encode.dccounts() -> List<&2, U32>:
  [0, 1, 5, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0]

# the DC symbols of either table: sizes 0 to 11
def encode.dcsyms() -> List<&2, U32>:
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

# Table K.5: luminance AC code lengths
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

# Table K.4: chrominance DC code lengths
def encode.cdccounts() -> List<&2, U32>:
  [0, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0]

# Table K.6: chrominance AC code lengths
def encode.caccounts() -> List<&2, U32>:
  [0, 2, 1, 2, 4, 4, 3, 4, 7, 5, 4, 4, 0, 1, 2, 119]

def encode.cacsyms() -> List<&2, U32>:
  [0, 1, 2, 3, 17, 4, 5, 33, 49, 6, 18, 65, 81, 7, 97, 113, 19, 34, 50, 129, 8, 20, 66, 145, 161, 177, 193, 9, 35,
    51, 82, 240, 21, 98, 114, 209, 10, 22, 36, 52, 225, 37, 241, 23, 24, 25, 26, 38, 39, 40, 41, 42, 53, 54, 55, 56,
    57, 58, 67, 68, 69, 70, 71, 72, 73, 74, 83, 84, 85, 86, 87, 88, 89, 90, 99, 100, 101, 102, 103, 104, 105, 106,
    115, 116, 117, 118, 119, 120, 121, 122, 130, 131, 132, 133, 134, 135, 136, 137, 138, 146, 147, 148, 149, 150, 151,
    152, 153, 154, 162, 163, 164, 165, 166, 167, 168, 169, 170, 178, 179, 180, 181, 182, 183, 184, 185, 186, 194,
    195, 196, 197, 198, 199, 200, 201, 202, 210, 211, 212, 213, 214, 215, 216, 217, 218, 226, 227, 228, 229, 230,
    231, 232, 233, 234, 242, 243, 244, 245, 246, 247, 248, 249, 250]

# one DHT segment holding a class's two tables: luminance as table 0, chrominance as table 1
def encode.dht(
  +cls: U32,
  +lc: List<&2, U32>,
  +ls: List<&2, U32>,
  +cc: List<&2, U32>,
  +cs: List<&2, U32>
) -> List<&2, U32>:
  encode.seg(196, cls <> encode.join(encode.join(lc, ls), (cls + 1 : U32) <> encode.join(cc, cs)))

# Y with Huffman tables 0, Cb and Cr with tables 1
def encode.sos() -> List<&2, U32>:
  encode.seg(218, [3, 1, 0, 2, 17, 3, 17, 0, 63, 0])

def encode.header(+ww: U32, +hh: U32, +qq: U32) -> List<&2, U32>:
  encode.join(Jpeg.soi(), encode.join(encode.app0(), encode.join(encode.dqt(qq), encode.join(encode.sof(ww, hh),
    encode.join(encode.dht(0, encode.dccounts(), encode.dcsyms(), encode.cdccounts(), encode.dcsyms()),
    encode.join(encode.dht(16, encode.accounts(), encode.acsyms(), encode.caccounts(), encode.cacsyms()),
    encode.sos()))))))

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

# the cosine kernel, the zigzag, and the quantisation columns of both tables at a quality
def encode.ctx(+qq: U32) -> Ctx:
  Ctx{encode.kern(Jpeg.decode.cos()), Jpeg.decode.zig(), encode.qcols(encode.qrows(encode.lumq(), qq)),
    encode.qcols(encode.qrows(encode.chrq(), qq))}

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

# the codes of Annex K's tables, one word per symbol: a code's length in the high half, the code in the low half.
# They are the canonical codes of the counts and symbols DHT carries (T.81 C, K.3 to K.6), written out once; for
# every symbol, the decoder's table built from those counts decodes the book's code to the symbol
# (laws/JpegRoundTripKeepsSize.bend, jpeg_huff_dc and jpeg_huff_ac)
def encode.ldc() -> Array<U32>:
  ANode{ANode{ANode{ANode{ALeaf{131072}, ALeaf{196610}}, ANode{ALeaf{196611}, ALeaf{196612}}},
    ANode{ANode{ALeaf{196613}, ALeaf{196614}}, ANode{ALeaf{262158}, ALeaf{327710}}}}, ANode{ANode{ANode{ALeaf{393278},
    ALeaf{458878}}, ANode{ALeaf{524542}, ALeaf{590334}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}

def encode.lac() -> Array<U32>:
  ANode{ANode{ANode{ANode{ANode{ANode{ANode{ANode{ALeaf{262154}, ALeaf{131072}}, ANode{ALeaf{131073}, ALeaf{196612}}},
    ANode{ANode{ALeaf{262155}, ALeaf{327706}}, ANode{ALeaf{458872}, ALeaf{524536}}}}, ANode{ANode{ANode{ALeaf{656374},
    ALeaf{1113986}}, ANode{ALeaf{1113987}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}},
    ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{262156}}, ANode{ALeaf{327707}, ALeaf{458873}}}, ANode{ANode{ALeaf{590326},
    ALeaf{722934}}, ANode{ALeaf{1113988}, ALeaf{1113989}}}}, ANode{ANode{ANode{ALeaf{1113990}, ALeaf{1113991}},
    ANode{ALeaf{1113992}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}},
    ANode{ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{327708}}, ANode{ALeaf{524537}, ALeaf{656375}}},
    ANode{ANode{ALeaf{790516}, ALeaf{1113993}}, ANode{ALeaf{1113994}, ALeaf{1113995}}}},
    ANode{ANode{ANode{ALeaf{1113996}, ALeaf{1113997}}, ANode{ALeaf{1113998}, ALeaf{0}}}, ANode{ANode{ALeaf{0},
    ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{393274}}, ANode{ALeaf{590327},
    ALeaf{790517}}}, ANode{ANode{ALeaf{1113999}, ALeaf{1114000}}, ANode{ALeaf{1114001}, ALeaf{1114002}}}},
    ANode{ANode{ANode{ALeaf{1114003}, ALeaf{1114004}}, ANode{ALeaf{1114005}, ALeaf{0}}}, ANode{ANode{ALeaf{0},
    ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}}}, ANode{ANode{ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{393275}},
    ANode{ALeaf{656376}, ALeaf{1114006}}}, ANode{ANode{ALeaf{1114007}, ALeaf{1114008}}, ANode{ALeaf{1114009},
    ALeaf{1114010}}}}, ANode{ANode{ANode{ALeaf{1114011}, ALeaf{1114012}}, ANode{ALeaf{1114013}, ALeaf{0}}},
    ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{458874}},
    ANode{ALeaf{722935}, ALeaf{1114014}}}, ANode{ANode{ALeaf{1114015}, ALeaf{1114016}}, ANode{ALeaf{1114017},
    ALeaf{1114018}}}}, ANode{ANode{ANode{ALeaf{1114019}, ALeaf{1114020}}, ANode{ALeaf{1114021}, ALeaf{0}}},
    ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}}, ANode{ANode{ANode{ANode{ANode{ALeaf{0},
    ALeaf{458875}}, ANode{ALeaf{790518}, ALeaf{1114022}}}, ANode{ANode{ALeaf{1114023}, ALeaf{1114024}},
    ANode{ALeaf{1114025}, ALeaf{1114026}}}}, ANode{ANode{ANode{ALeaf{1114027}, ALeaf{1114028}}, ANode{ALeaf{1114029},
    ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{0},
    ALeaf{524538}}, ANode{ALeaf{790519}, ALeaf{1114030}}}, ANode{ANode{ALeaf{1114031}, ALeaf{1114032}},
    ANode{ALeaf{1114033}, ALeaf{1114034}}}}, ANode{ANode{ANode{ALeaf{1114035}, ALeaf{1114036}}, ANode{ALeaf{1114037},
    ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}}}},
    ANode{ANode{ANode{ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{590328}}, ANode{ALeaf{1015744}, ALeaf{1114038}}},
    ANode{ANode{ALeaf{1114039}, ALeaf{1114040}}, ANode{ALeaf{1114041}, ALeaf{1114042}}}},
    ANode{ANode{ANode{ALeaf{1114043}, ALeaf{1114044}}, ANode{ALeaf{1114045}, ALeaf{0}}}, ANode{ANode{ALeaf{0},
    ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{590329}}, ANode{ALeaf{1114046},
    ALeaf{1114047}}}, ANode{ANode{ALeaf{1114048}, ALeaf{1114049}}, ANode{ALeaf{1114050}, ALeaf{1114051}}}},
    ANode{ANode{ANode{ALeaf{1114052}, ALeaf{1114053}}, ANode{ALeaf{1114054}, ALeaf{0}}}, ANode{ANode{ALeaf{0},
    ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}}, ANode{ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{590330}},
    ANode{ALeaf{1114055}, ALeaf{1114056}}}, ANode{ANode{ALeaf{1114057}, ALeaf{1114058}}, ANode{ALeaf{1114059},
    ALeaf{1114060}}}}, ANode{ANode{ANode{ALeaf{1114061}, ALeaf{1114062}}, ANode{ALeaf{1114063}, ALeaf{0}}},
    ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{656377}},
    ANode{ALeaf{1114064}, ALeaf{1114065}}}, ANode{ANode{ALeaf{1114066}, ALeaf{1114067}}, ANode{ALeaf{1114068},
    ALeaf{1114069}}}}, ANode{ANode{ANode{ALeaf{1114070}, ALeaf{1114071}}, ANode{ALeaf{1114072}, ALeaf{0}}},
    ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}}}, ANode{ANode{ANode{ANode{ANode{ANode{ALeaf{0},
    ALeaf{656378}}, ANode{ALeaf{1114073}, ALeaf{1114074}}}, ANode{ANode{ALeaf{1114075}, ALeaf{1114076}},
    ANode{ALeaf{1114077}, ALeaf{1114078}}}}, ANode{ANode{ANode{ALeaf{1114079}, ALeaf{1114080}}, ANode{ALeaf{1114081},
    ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{0},
    ALeaf{722936}}, ANode{ALeaf{1114082}, ALeaf{1114083}}}, ANode{ANode{ALeaf{1114084}, ALeaf{1114085}},
    ANode{ALeaf{1114086}, ALeaf{1114087}}}}, ANode{ANode{ANode{ALeaf{1114088}, ALeaf{1114089}}, ANode{ALeaf{1114090},
    ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}}, ANode{ANode{ANode{ANode{ANode{ALeaf{0},
    ALeaf{1114091}}, ANode{ALeaf{1114092}, ALeaf{1114093}}}, ANode{ANode{ALeaf{1114094}, ALeaf{1114095}},
    ANode{ALeaf{1114096}, ALeaf{1114097}}}}, ANode{ANode{ANode{ALeaf{1114098}, ALeaf{1114099}}, ANode{ALeaf{1114100},
    ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{722937},
    ALeaf{1114101}}, ANode{ALeaf{1114102}, ALeaf{1114103}}}, ANode{ANode{ALeaf{1114104}, ALeaf{1114105}},
    ANode{ALeaf{1114106}, ALeaf{1114107}}}}, ANode{ANode{ANode{ALeaf{1114108}, ALeaf{1114109}}, ANode{ALeaf{1114110},
    ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}}}}}

def encode.cdc() -> Array<U32>:
  ANode{ANode{ANode{ANode{ALeaf{131072}, ALeaf{131073}}, ANode{ALeaf{131074}, ALeaf{196614}}},
    ANode{ANode{ALeaf{262158}, ALeaf{327710}}, ANode{ALeaf{393278}, ALeaf{458878}}}}, ANode{ANode{ANode{ALeaf{524542},
    ALeaf{590334}}, ANode{ALeaf{656382}, ALeaf{722942}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}

def encode.cac() -> Array<U32>:
  ANode{ANode{ANode{ANode{ANode{ANode{ANode{ANode{ALeaf{131072}, ALeaf{131073}}, ANode{ALeaf{196612}, ALeaf{262154}}},
    ANode{ANode{ALeaf{327704}, ALeaf{327705}}, ANode{ALeaf{393272}, ALeaf{458872}}}}, ANode{ANode{ANode{ALeaf{590324},
    ALeaf{656374}}, ANode{ALeaf{790516}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}},
    ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{262155}}, ANode{ALeaf{393273}, ALeaf{524534}}}, ANode{ANode{ALeaf{590325},
    ALeaf{722934}}, ANode{ALeaf{790517}, ALeaf{1113992}}}}, ANode{ANode{ANode{ALeaf{1113993}, ALeaf{1113994}},
    ANode{ALeaf{1113995}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}},
    ANode{ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{327706}}, ANode{ALeaf{524535}, ALeaf{656375}}},
    ANode{ANode{ALeaf{790518}, ALeaf{1015746}}, ANode{ALeaf{1113996}, ALeaf{1113997}}}},
    ANode{ANode{ANode{ALeaf{1113998}, ALeaf{1113999}}, ANode{ALeaf{1114000}, ALeaf{0}}}, ANode{ANode{ALeaf{0},
    ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{327707}}, ANode{ALeaf{524536},
    ALeaf{656376}}}, ANode{ANode{ALeaf{790519}, ALeaf{1114001}}, ANode{ALeaf{1114002}, ALeaf{1114003}}}},
    ANode{ANode{ANode{ALeaf{1114004}, ALeaf{1114005}}, ANode{ALeaf{1114006}, ALeaf{0}}}, ANode{ANode{ALeaf{0},
    ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}}}, ANode{ANode{ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{393274}},
    ANode{ALeaf{590326}, ALeaf{1114007}}}, ANode{ANode{ALeaf{1114008}, ALeaf{1114009}}, ANode{ALeaf{1114010},
    ALeaf{1114011}}}}, ANode{ANode{ANode{ALeaf{1114012}, ALeaf{1114013}}, ANode{ALeaf{1114014}, ALeaf{0}}},
    ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{393275}},
    ANode{ALeaf{656377}, ALeaf{1114015}}}, ANode{ANode{ALeaf{1114016}, ALeaf{1114017}}, ANode{ALeaf{1114018},
    ALeaf{1114019}}}}, ANode{ANode{ANode{ALeaf{1114020}, ALeaf{1114021}}, ANode{ALeaf{1114022}, ALeaf{0}}},
    ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}}, ANode{ANode{ANode{ANode{ANode{ALeaf{0},
    ALeaf{458873}}, ANode{ALeaf{722935}, ALeaf{1114023}}}, ANode{ANode{ALeaf{1114024}, ALeaf{1114025}},
    ANode{ALeaf{1114026}, ALeaf{1114027}}}}, ANode{ANode{ANode{ALeaf{1114028}, ALeaf{1114029}}, ANode{ALeaf{1114030},
    ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{0},
    ALeaf{458874}}, ANode{ALeaf{722936}, ALeaf{1114031}}}, ANode{ANode{ALeaf{1114032}, ALeaf{1114033}},
    ANode{ALeaf{1114034}, ALeaf{1114035}}}}, ANode{ANode{ANode{ALeaf{1114036}, ALeaf{1114037}}, ANode{ALeaf{1114038},
    ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}}}},
    ANode{ANode{ANode{ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{524537}}, ANode{ALeaf{1114039}, ALeaf{1114040}}},
    ANode{ANode{ALeaf{1114041}, ALeaf{1114042}}, ANode{ALeaf{1114043}, ALeaf{1114044}}}},
    ANode{ANode{ANode{ALeaf{1114045}, ALeaf{1114046}}, ANode{ALeaf{1114047}, ALeaf{0}}}, ANode{ANode{ALeaf{0},
    ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{590327}}, ANode{ALeaf{1114048},
    ALeaf{1114049}}}, ANode{ANode{ALeaf{1114050}, ALeaf{1114051}}, ANode{ALeaf{1114052}, ALeaf{1114053}}}},
    ANode{ANode{ANode{ALeaf{1114054}, ALeaf{1114055}}, ANode{ALeaf{1114056}, ALeaf{0}}}, ANode{ANode{ALeaf{0},
    ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}}, ANode{ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{590328}},
    ANode{ALeaf{1114057}, ALeaf{1114058}}}, ANode{ANode{ALeaf{1114059}, ALeaf{1114060}}, ANode{ALeaf{1114061},
    ALeaf{1114062}}}}, ANode{ANode{ANode{ALeaf{1114063}, ALeaf{1114064}}, ANode{ALeaf{1114065}, ALeaf{0}}},
    ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{590329}},
    ANode{ALeaf{1114066}, ALeaf{1114067}}}, ANode{ANode{ALeaf{1114068}, ALeaf{1114069}}, ANode{ALeaf{1114070},
    ALeaf{1114071}}}}, ANode{ANode{ANode{ALeaf{1114072}, ALeaf{1114073}}, ANode{ALeaf{1114074}, ALeaf{0}}},
    ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}}}, ANode{ANode{ANode{ANode{ANode{ANode{ALeaf{0},
    ALeaf{590330}}, ANode{ALeaf{1114075}, ALeaf{1114076}}}, ANode{ANode{ALeaf{1114077}, ALeaf{1114078}},
    ANode{ALeaf{1114079}, ALeaf{1114080}}}}, ANode{ANode{ANode{ALeaf{1114081}, ALeaf{1114082}}, ANode{ALeaf{1114083},
    ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{0},
    ALeaf{722937}}, ANode{ALeaf{1114084}, ALeaf{1114085}}}, ANode{ANode{ALeaf{1114086}, ALeaf{1114087}},
    ANode{ALeaf{1114088}, ALeaf{1114089}}}}, ANode{ANode{ANode{ALeaf{1114090}, ALeaf{1114091}}, ANode{ALeaf{1114092},
    ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}}, ANode{ANode{ANode{ANode{ANode{ALeaf{0},
    ALeaf{933856}}, ANode{ALeaf{1114093}, ALeaf{1114094}}}, ANode{ANode{ALeaf{1114095}, ALeaf{1114096}},
    ANode{ALeaf{1114097}, ALeaf{1114098}}}}, ANode{ANode{ANode{ALeaf{1114099}, ALeaf{1114100}}, ANode{ALeaf{1114101},
    ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{656378},
    ALeaf{1015747}}, ANode{ALeaf{1114102}, ALeaf{1114103}}}, ANode{ANode{ALeaf{1114104}, ALeaf{1114105}},
    ANode{ALeaf{1114106}, ALeaf{1114107}}}}, ANode{ANode{ANode{ALeaf{1114108}, ALeaf{1114109}}, ANode{ALeaf{1114110},
    ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}}}}}

# a class's DC book: luminance, or chrominance when cls is set
def encode.dcof(+cls: Bool) -> Array<U32>:
  match cls:
    case False{}:
      encode.ldc()
    case True{}:
      encode.cdc()

# a class's AC book
def encode.acof(+cls: Bool) -> Array<U32>:
  match cls:
    case False{}:
      encode.lac()
    case True{}:
      encode.cac()

# a class's books
def encode.bookof(+cls: Bool) -> Book:
  Book{encode.dcof(cls), encode.acof(cls)}

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

# a finished sum rounded as the decoder's passes round it: the row pass (fine) keeps four fraction bits, the
# column pass takes them off, so a coefficient is rounded once
def encode.q17(acc: U32 & U32, +fine: Bool) -> U32:
  match acc:
    case (+hi, +lo):
      Jpeg.decode.qs(hi, lo, fine)

def encode.scale(+coef: U32, +samp: U32, +fine: Bool) -> U32:
  encode.q17(Jpeg.decode.widemul(coef, samp), fine)

def encode.two(+c0: U32, +x0: U32, +c1: U32, +x1: U32, +fine: Bool) -> U32:
  encode.q17(encode.mac(c1, x1, Jpeg.decode.widemul(c0, x0)), fine)

def encode.two.n(+c0: U32, +x0: U32, +c1: U32, +x1: U32, +fine: Bool) -> U32:
  encode.q17(encode.mac(Jpeg.decode.neg32(c1), x1, Jpeg.decode.widemul(c0, x0)), fine)

def encode.four(
  +c0: U32,
  +s0: U32,
  +c1: U32,
  +s1: U32,
  +c2: U32,
  +s2: U32,
  +c3: U32,
  +s3: U32,
  +fine: Bool
) -> U32:
  encode.q17(encode.mac(c3, s3, encode.mac(c2, s2, encode.mac(c1, s1, Jpeg.decode.widemul(c0, s0)))), fine)

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
  +k6: U32,
  +fine: Bool
) -> Oct:
  +a0 = (s0 + s7 : U32)
  +a1 = (s1 + s6 : U32)
  +a2 = (s2 + s5 : U32)
  +a3 = (s3 + s4 : U32)
  +e0 = (a0 - a3 : U32)
  +e1 = (a1 - a2 : U32)
  Oct{encode.scale(k0, (a0 + a1 + a2 + a3 : U32), fine), 0, encode.two(k2, e0, k6, e1, fine), 0,
    encode.scale(k0, ((a0 + a3 : U32) - (a1 + a2 : U32) : U32), fine), 0, encode.two.n(k6, e0, k2, e1, fine), 0}

# odd frequencies: antisymmetric samples share one weight
def encode.odd(
  +d0: U32,
  +d1: U32,
  +d2: U32,
  +d3: U32,
  +o0: U32,
  +o1: U32,
  +o2: U32,
  +o3: U32,
  +fine: Bool
) -> Oct:
  +n0 = Jpeg.decode.neg32(o0)
  +n2 = Jpeg.decode.neg32(o2)
  +n3 = Jpeg.decode.neg32(o3)
  Oct{0, encode.four(o0, d0, o1, d1, o2, d2, o3, d3, fine), 0, encode.four(o1, d0, n3, d1, n0, d2, n2, d3, fine), 0,
    encode.four(o2, d0, n0, d1, o3, d2, o1, d3, fine), 0, encode.four(o3, d0, n2, d1, o1, d2, n0, d3, fine)}

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
  kern: Kern,
  +fine: Bool
) -> Oct:
  match kern:
    case Kern{+k0, +k2, +k6, +o0, +o1, +o2, +o3}:
      encode.dct8.at(encode.even(s0, s1, s2, s3, s4, s5, s6, s7, k0, k2, k6, fine),
        encode.odd((s0 - s7 : U32), (s1 - s6 : U32), (s2 - s5 : U32), (s3 - s4 : U32), o0, o1, o2, o3, fine))

# one 8-point transform, fine for the row pass. Pairing is the matrix product, so the rounded value matches.
def encode.dct8(samp: Oct, kern: Kern, +fine: Bool) -> Oct:
  match samp:
    case Oct{+s0, +s1, +s2, +s3, +s4, +s5, +s6, +s7}:
      encode.dct8.k(s0, s1, s2, s3, s4, s5, s6, s7, kern, fine)

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
      (arr, encode.dct8(o, kern, False{}))

# one frequency column, read straight from the plane
def encode.col(arr: Array<U32>, +at: U32, kern: Kern) -> Array<U32> & Oct:
  encode.col.use(encode.oct.stride(arr, at, 8), kern)

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

# a frequency column divided by its quantisation steps, each rounded half away from zero
def encode.quant8(oo: Oct, qq: Oct) -> Oct:
  match oo:
    case Oct{+f0, +f1, +f2, +f3, +f4, +f5, +f6, +f7}:
      match qq:
        case Oct{+q0, +q1, +q2, +q3, +q4, +q5, +q6, +q7}:
          Oct{encode.qdiv(f0, q0), encode.qdiv(f1, q1), encode.qdiv(f2, q2), encode.qdiv(f3, q3), encode.qdiv(f4, q4),
            encode.qdiv(f5, q5), encode.qdiv(f6, q6), encode.qdiv(f7, q7)}

# a table's columns, when no longer read
def encode.qdrop(qs: List<&2, Oct>) -> U32:
  match qs:
    case Nil{}:
      0
    case _q <> rest:
      encode.qdrop(rest)

def encode.pass2.done(st: Planes, kern: Kern, qs: List<&2, Oct>) -> Array<U32>:
  match st:
    case Planes{src, dst, +at}:
      +_z = encode.kern.drop(kern)
      +_s = encode.pix.sink(src)
      +_q = encode.qdrop(qs)
      +_at = (at - at : U32)
      dst

def encode.pass2.put(got: Array<U32> & Oct, dst: Array<U32>, +at: U32, qq: Oct) -> Planes:
  match got:
    case (src, o):
      Planes{src, encode.scatter(encode.quant8(o, qq), dst, at), (at + 1 : U32)}

def encode.pass2.step(st: Planes, kern: Kern, qq: Oct) -> Planes:
  match st:
    case Planes{src, dst, +at}:
      encode.pass2.put(encode.col(src, at, kern), dst, at, qq)

# the column transforms, each column divided by its quantisation steps. `left` columns are still unread.
def encode.pass2(left: Nat, st: Planes, +kern: Kern, qs: List<&2, Oct>) -> Array<U32>:
  match left:
    case 0n:
      encode.pass2.done(st, kern, qs)
    case 1n+rest:
      match qs:
        case Nil{}:
          encode.pass2(rest, encode.pass2.step(st, kern, Oct{1, 1, 1, 1, 1, 1, 1, 1}), kern, [])
        case +qq <> qt:
          encode.pass2(rest, encode.pass2.step(st, kern, qq), kern, qt)

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
      Planes{src, encode.lay(encode.dct8(o, kern, True{}), dst, at), (at + 8 : U32)}

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

# level plane in, quantised natural-order coefficients out
def encode.freq(src: Array<U32>, +kern: Kern, qs: List<&2, Oct>) -> Array<U32>:
  encode.pass2(8n, Planes{encode.pass.mid(src, kern), Jpeg.decode.plane(64), 0}, kern, qs)

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

# both samples are the neutral level
def encode.flat.both(aa: Bool, bb: Bool) -> Bool:
  match aa:
    case False{}:
      match bb:
        case _k:
          False{}
    case True{}:
      bb

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
  +qs: List<&2, Oct>
) -> Book & U32 & Put:
  +_s = encode.pix.sink(plane)
  +_k = encode.kern.drop(kern)
  +_g = encode.drop(zig)
  +_q = encode.qdrop(qs)
  encode.block.go(book, pp, pred, List.replicate(U32, 64n, 0))

def encode.chan.mix(
  plane: Array<U32>,
  book: Book,
  pp: Put,
  +pred: U32,
  +kern: Kern,
  zig: List<&2, U32>,
  qs: List<&2, Oct>
) -> Book & U32 & Put:
  encode.scan(book, pp, pred, encode.freq(plane, kern, qs), zig)

def encode.chan.go(
  flat: Bool,
  plane: Array<U32>,
  book: Book,
  pp: Put,
  +pred: U32,
  +kern: Kern,
  +zig: List<&2, U32>,
  +qs: List<&2, Oct>
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

def encode.step.end(
  got: Book & U32 & Put,
  lb: Book,
  aa: Array<U32>,
  +ydc: U32,
  +bdc: U32
) -> Array<U32> & Book & Book & U32 & U32 & U32 & Put:
  (cb, +rdc, bit) = got
  (aa, lb, cb, ydc, bdc, rdc, bit)

def encode.step.cr(
  got: Book & U32 & Put,
  lb: Book,
  aa: Array<U32>,
  rs: Array<U32>,
  fr: Bool,
  +ydc: U32,
  +pr: U32,
  +kern: Kern,
  +zig: List<&2, U32>,
  +qc: List<&2, Oct>
) -> Array<U32> & Book & Book & U32 & U32 & U32 & Put:
  (cb, +bdc, bit) = got
  encode.step.end(encode.chan.go(fr, rs, cb, bit, pr, kern, zig, qc), lb, aa, ydc, bdc)

def encode.step.cb(
  got: Book & U32 & Put,
  cb: Book,
  aa: Array<U32>,
  bs: Array<U32>,
  rs: Array<U32>,
  fb: Bool,
  fr: Bool,
  +pb: U32,
  +pr: U32,
  +kern: Kern,
  +zig: List<&2, U32>,
  +qc: List<&2, Oct>
) -> Array<U32> & Book & Book & U32 & U32 & U32 & Put:
  (lb, +ydc, bit) = got
  encode.step.cr(encode.chan.go(fb, bs, cb, bit, pb, kern, zig, qc), lb, aa, rs, fr, ydc, pr, kern, zig, qc)

# Y with the luminance book and table, then Cb and Cr with the chrominance book and table. Each clipped DC is the
# next predictor.
def encode.step.tile(
  tt: Tile,
  lb: Book,
  cb: Book,
  bit: Put,
  +py: U32,
  +pb: U32,
  +pr: U32,
  +kern: Kern,
  +zig: List<&2, U32>,
  +ql: List<&2, Oct>,
  +qc: List<&2, Oct>
) -> Array<U32> & Book & Book & U32 & U32 & U32 & Put:
  match tt:
    case Tile{pix, ys, bs, rs, fy, fb, fr}:
      encode.step.cb(encode.chan.go(fy, ys, lb, bit, py, kern, zig, ql), cb, pix, bs, rs, fb, fr, pb, pr, kern, zig,
        qc)

# one walk of the MCU, then its three blocks
def encode.step.y(
  aa: Array<U32>,
  lb: Book,
  cb: Book,
  bit: Put,
  +py: U32,
  +pb: U32,
  +pr: U32,
  +xx: U32,
  +yy: U32,
  +ww: U32,
  +hh: U32,
  +ctx: Ctx
) -> Array<U32> & Book & Book & U32 & U32 & U32 & Put:
  match ctx:
    case Ctx{+kern, +zig, +ql, +qc}:
      encode.step.tile(encode.tile(aa, ww, hh, xx, yy), lb, cb, bit, py, pb, pr, kern, zig, ql, qc)

def encode.mcus.done(got: Array<U32> & Book & Book & U32 & U32 & U32 & Put) -> Put:
  (a, lb, cb, ydc, bdc, rdc, bit) = got
  +_s = encode.pix.sink(a)
  +_l = encode.book.sink(lb)
  +_c = encode.book.sink(cb)
  +_u = (ydc + bdc + rdc : U32)
  bit

def encode.mcus(
  left: Nat,
  got: Array<U32> & Book & Book & U32 & U32 & U32 & Put,
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
      (a, lb, cb, py, pb, pr, bit) = got
      +x = (mx * 8 : U32)
      +y = (my * 8 : U32)
      +more = U32.is_lt((mx + 1 : U32), mw)
      encode.mcus(nleft, encode.step.y(a, lb, cb, bit, py, pb, pr, x, y, ww, hh, ctx), encode.nx(more, mx),
        encode.ny(more, my), mw, ww, hh, ctx)

# the entropy-coded bytes of an accepted size at a quality, MCU by MCU
def encode.arm(+ww: U32, +hh: U32, +qq: U32, px: List<&2, U32>) -> List<&2, U32>:
  +mw = U32.div((ww + 7 : U32), 8)
  +mh = U32.div((hh + 7 : U32), 8)
  +area = (ww * hh : U32)
  encode.pad(encode.mcus(U32.to_nat((mw * mh : U32)), (encode.pix.load(U32.to_nat(area), px,
    Jpeg.decode.plane(area), 0), encode.bookof(False{}), encode.bookof(True{}), 1024, 1024, 1024, encode.put0()), 0,
    0, mw, ww, hh, encode.ctx(qq)))

def encode.finish(+ww: U32, +hh: U32, +qq: U32, ent: List<&2, U32>) -> List<&2, U32>:
  encode.join(encode.header(ww, hh, qq), encode.join(ent, Jpeg.eoi()))

def encode.pick(bad: Bool, +ww: U32, +hh: U32, +qq: U32, px: List<&2, U32>) -> List<&2, U32>:
  match bad:
    case True{}:
      +_d = encode.drop(px)
      +_q = qq
      encode.join(Jpeg.soi(), Jpeg.eoi())
    case False{}:
      encode.finish(ww, hh, qq, encode.arm(ww, hh, qq, px))

# baseline sequential 4:4:4 JPEG bytes for packed RGB samples at a quality of 1 to 100 (a quality outside it is the
# nearest end), or SOI EOI when the size is rejected
def encode(+ww: U32, +hh: U32, +qq: U32, px: List<&2, U32>) -> List<&2, U32>:
  encode.pick(encode.bad(ww, hh), ww, hh, qq, px)
