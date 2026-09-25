# ezimg: the laws. Each law carries the SPEC.md row it proves, or proves part
# of, on its own comment line. PROOF.bend fills them; `bend PROOF.bend` is the
# gate. Every row is pending: the 85 closed laws that stood here were retired
# (docs/rfc/ezimg-law-inventory.md keeps what each one pointed toward), and
# the quantified laws land row by row. The imports keep every module under
# the gate's checker until laws reach them.
import Base
import ./main.bend as Img
import ./src/crc.bend as Crc
import ./src/inflate.bend as Inf
import ./src/png.bend as Png
import ./src/jpeg.bend as Jpeg
import ./src/jpeg_enc.bend as Jenc

# LAW: every sample Jpeg.rgb packs is opaque, for every Y, Cb and Cr
# IMG-PIX-1
law jpeg_rgb_opaque:
  for +yy: U32
  for +cb: U32
  for +cr: U32
  {U32.shrn(Jpeg.rgb(yy, cb, cr), 24n) == 255 : U32}

# LAW: every sample Jpeg.gray packs is opaque, for every level
# IMG-PIX-1
law jpeg_gray_opaque:
  for +yy: U32
  {U32.shrn(Jpeg.gray(yy), 24n) == 255 : U32}

# LAW: encode_jpeg refuses exactly the rasters encode_png refuses
# IMG-JPG-4
law jpeg_png_refuse_alike:
  for +img: Img.Raster
  {Maybe.is_none(&2, List<&2, U32>, Img.encode_jpeg(img)) ==
    Maybe.is_none(&2, List<&2, U32>, Img.encode_png(img)) : Bool}

# every sample's colour, alpha cleared: the specification's own copy
def alpha.drop(px: List<&2, U32>) -> List<&2, U32>:
  match px:
    case Nil{}:
      Nil{}
    case pp <> rest:
      U32.and(16777215, pp) <> alpha.drop(rest)

# LAW: two rasters of one size whose samples differ only in alpha encode to the same JPEG bytes
# IMG-PIX-2
law jpeg_alpha_blind:
  for +ww: U32
  for +hh: U32
  for +pa: List<&2, U32>
  for +pb: List<&2, U32>
  for +same: {alpha.drop(pa) == alpha.drop(pb) : List<&2, U32>}
  {Img.encode_jpeg(Img.raster(ww, hh, pa)) == Img.encode_jpeg(Img.raster(ww, hh, pb)) : Maybe<&2, List<&2, U32>>}

# a sample through a function, or none
def opt.map(~ff: U32 -> U32, mm: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match mm:
    case None{}:
      None{}
    case Some{vv}:
      Some{ff(vv)}

# LAW: map keeps the width and the height
# IMG-RAS-5
law map_size:
  for ~ff: U32 -> U32
  for +img: Img.Raster
  {Img.size(Img.map(~ff, img)) == Img.size(img) : U32 & U32}

# LAW: sample k of map(f, r) is f of sample k of r, for every k, and none past the end
# IMG-RAS-5
law map_at:
  for ~ff: U32 -> U32
  for +img: Img.Raster
  for +kk: Nat
  {List.get(&2, U32, Img.pixels(Img.map(~ff, img)), kk) ==
    opt.map(~ff, List.get(&2, U32, Img.pixels(img), kk)) : Maybe<&2, U32>}

# LAW: bytes that open with the eight signature bytes parse as the signature, whatever follows
# IMG-PNG-1
law sig_opens:
  for +rest: List<&2, U32>
  {Img.parse_signature(List.append(&2, U32, Img.png_sig(), rest)) == Some{Img.png_sig()} : Maybe<&2, List<&2, U32>>}

# LAW: parse_signature is some only when the bytes open with the eight signature bytes
# IMG-PNG-1
law sig_only:
  for +xs: List<&2, U32>
  for h_some: {Maybe.is_some(&2, List<&2, U32>, Img.parse_signature(xs)) == True{} : Bool}
  {xs == List.append(&2, U32, Img.png_sig(), List.drop(&2, U32, xs, 8n)) : List<&2, U32>}

# ---- wp7-jpeg-struct ----

# a JPEG marker segment: FF, the marker, the length (the body's plus two) high byte first, then the body
def jfif.seg(+mark: U32, +body: List<&2, U32>) -> List<&2, U32>:
  +nn = (U32.from_nat(List.length(&2, U32, body)) + 2 : U32)
  255 <> (mark <> (U32.shrn(nn, 8n) <> (U32.and(nn, 255) <> body)))

# a baseline JFIF file: SOI; APP0 opening with the JFIF identifier; DQT; SOF0 opening with precision 8,
# the height and the width, each high byte first; two DHT; SOS; the entropy-coded bytes; EOI
def jfif.file(
  +ww: U32,
  +hh: U32,
  app: List<&2, U32>,
  dq: List<&2, U32>,
  sof: List<&2, U32>,
  dc: List<&2, U32>,
  ac: List<&2, U32>,
  sos: List<&2, U32>,
  ent: List<&2, U32>
) -> List<&2, U32>:
  +frame = List.append(&2, U32, [8, U32.shrn(hh, 8n), U32.and(hh, 255), U32.shrn(ww, 8n), U32.and(ww, 255)], sof)
  List.append(&2, U32, List.append(&2, U32, [255, 216], List.append(&2, U32,
    jfif.seg(224, List.append(&2, U32, [74, 70, 73, 70, 0], app)), List.append(&2, U32, jfif.seg(219, dq),
    List.append(&2, U32, jfif.seg(192, frame), List.append(&2, U32, jfif.seg(196, dc),
    List.append(&2, U32, jfif.seg(196, ac), jfif.seg(218, sos))))))), List.append(&2, U32, ent, [255, 217]))

# LAW: when encode_jpeg(r) is some and both sides are at most 65535, it is SOI, APP0 with the JFIF
# identifier, DQT, SOF0 carrying r's width and height, DHT, SOS, the entropy-coded bytes and EOI
# IMG-JPG-5
law jpeg_enc_layout:
  for +img: Img.Raster
  for h_some: {Maybe.is_some(&2, List<&2, U32>, Img.encode_jpeg(img)) == True{} : Bool}
  for h_w: {U32.is_le(Img.width(img), 65535) == True{} : Bool}
  for h_h: {U32.is_le(Img.height(img), 65535) == True{} : Bool}
  exs app: List<&2, U32>
  exs dq: List<&2, U32>
  exs sof: List<&2, U32>
  exs dc: List<&2, U32>
  exs ac: List<&2, U32>
  exs sos: List<&2, U32>
  exs ent: List<&2, U32>
  {Img.encode_jpeg(img) == Some{jfif.file(Img.width(img), Img.height(img), app, dq, sof, dc, ac, sos, ent)}
    : Maybe<&2, List<&2, U32>>}

# LAW: when encode_jpeg(r) is some, it begins with SOI and ends with EOI, whatever r's size
# IMG-JPG-5
law jpeg_enc_ends:
  for +img: Img.Raster
  for h_some: {Maybe.is_some(&2, List<&2, U32>, Img.encode_jpeg(img)) == True{} : Bool}
  exs mid: List<&2, U32>
  {Img.encode_jpeg(img) == Some{List.append(&2, U32, [255, 216], List.append(&2, U32, mid, [255, 217]))}
    : Maybe<&2, List<&2, U32>>}

# the red byte of a packed sample
def chan.r(+pp: U32) -> U32:
  U32.and(255, U32.shrn(pp, 16n))

# the green byte of a packed sample
def chan.g(+pp: U32) -> U32:
  U32.and(255, U32.shrn(pp, 8n))

# the blue byte of a packed sample
def chan.b(+pp: U32) -> U32:
  U32.and(255, pp)

# LAW: a gray sample carries its level's byte in red, green and blue
# IMG-PIX-1
law jpeg_gray_level:
  for +yy: U32
  {chan.r(Jpeg.gray(yy)) == U32.and(255, yy) : U32} & {chan.g(Jpeg.gray(yy)) == U32.and(255, yy) : U32}
    & {chan.b(Jpeg.gray(yy)) == U32.and(255, yy) : U32}

# every level as a gray sample
def jpeg.grays(ys: List<&2, U32>) -> List<&2, U32>:
  match ys:
    case Nil{}:
      Nil{}
    case yv <> rest:
      Jpeg.gray(yv) <> jpeg.grays(rest)

# every Y, Cb, Cr triple as a colour sample, as many as the shortest list holds
def jpeg.rgbs(ys: List<&2, U32>, bs: List<&2, U32>, rs: List<&2, U32>) -> List<&2, U32>:
  match ys bs rs:
    case yv <> yt bv <> bt rv <> rt:
      Jpeg.rgb(yv, bv, rv) <> jpeg.rgbs(yt, bt, rt)
    case _ _ _:
      Nil{}

# gray samples of the levels ys, or colour samples of ys, bs and rs
def jpeg.pack(gray: Bool, ys: List<&2, U32>, bs: List<&2, U32>, rs: List<&2, U32>) -> List<&2, U32>:
  match gray:
    case True{}:
      jpeg.grays(ys)
    case False{}:
      jpeg.rgbs(ys, bs, rs)

# LAW: decode_jpeg packs every sample it returns with Jpeg.gray, or every one with Jpeg.rgb
# IMG-PIX-1
law jpeg_decode_packed:
  for +bytes: List<&2, U32>
  for +img: Img.Raster
  for h_dec: {Img.decode_jpeg(bytes) == Some{img} : Maybe<&2, Img.Raster>}
  exs gray: Bool
  exs ys: List<&2, U32>
  exs bs: List<&2, U32>
  exs rs: List<&2, U32>
  {Img.pixels(img) == jpeg.pack(gray, ys, bs, rs) : List<&2, U32>}

# ok, and every sample of px has alpha 255
def all.opaque(px: List<&2, U32>, ok: Bool) -> Bool:
  match px:
    case Nil{}:
      ok
    case pp <> rest:
      all.opaque(rest, Bool.and(U32.is_eq(U32.shrn(pp, 24n), 255), ok))

# LAW: every sample decode_jpeg returns has alpha 255
# IMG-PIX-1
law jpeg_decode_opaque:
  for +bytes: List<&2, U32>
  for +img: Img.Raster
  for h_dec: {Img.decode_jpeg(bytes) == Some{img} : Maybe<&2, Img.Raster>}
  {all.opaque(Img.pixels(img), True{}) == True{} : Bool}

# the markers of segments that are not frame headers (T.81 Table B.1): DHT, DQT, SOS, DRI, COM, APP0 to APP15
type Mk is Data:
  MDht{}
  MDqt{}
  MSos{}
  MDri{}
  MCom{}
  MApp0{}
  MApp1{}
  MApp2{}
  MApp3{}
  MApp4{}
  MApp5{}
  MApp6{}
  MApp7{}
  MApp8{}
  MApp9{}
  MApp10{}
  MApp11{}
  MApp12{}
  MApp13{}
  MApp14{}
  MApp15{}

# a marker's second byte
def mk.byte(mk: Mk) -> U32:
  match mk:
    case MDht{}:
      196
    case MDqt{}:
      219
    case MSos{}:
      218
    case MDri{}:
      221
    case MCom{}:
      254
    case MApp0{}:
      224
    case MApp1{}:
      225
    case MApp2{}:
      226
    case MApp3{}:
      227
    case MApp4{}:
      228
    case MApp5{}:
      229
    case MApp6{}:
      230
    case MApp7{}:
      231
    case MApp8{}:
      232
    case MApp9{}:
      233
    case MApp10{}:
      234
    case MApp11{}:
      235
    case MApp12{}:
      236
    case MApp13{}:
      237
    case MApp14{}:
      238
    case MApp15{}:
      239

# a segment that is not a frame header: its marker, the two bytes of its length field, and its body
type Seg is Data:
  Seg{mk: Mk, hi: U32, lo: U32, body: List<&2, U32>}

# a segment's bytes: FF, the marker, the length field, the body
def seg.bytes(sg: Seg) -> List<&2, U32>:
  match sg:
    case Seg{mk, hi, lo, body}:
      255 <> (mk.byte(mk) <> (hi <> (lo <> body)))

# the length a length field gives, high byte first
def seg.len(+hi: U32, +lo: U32) -> U32:
  U32.or(U32.shln(hi, 8n), lo)

# a length field fits its body: it is at least 2, and 2 more than the body's length
def seg.Fits(+hi: U32, +lo: U32, +body: List<&2, U32>) -> Type:
  {U32.is_lt(seg.len(hi, lo), 2) == False{} : Bool}
    & {U32.to_nat((seg.len(hi, lo) - 2 : U32)) == List.length(&2, U32, body) : Nat}

# every segment's length field fits its body
def segs.Fit(ss: List<&2, Seg>) -> Type:
  match ss:
    case Nil{}:
      Unit
    case Seg{_mk, +hi, +lo, +body} <> rest:
      seg.Fits(hi, lo, body) & segs.Fit(rest)

# the bytes of the segments, in order
def segs.bytes(ss: List<&2, Seg>) -> List<&2, U32>:
  match ss:
    case Nil{}:
      Nil{}
    case sg <> rest:
      List.append(&2, U32, seg.bytes(sg), segs.bytes(rest))

# SOI, then the segments, then the rest
def jpeg.lead(ss: List<&2, Seg>, rest: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, [255, 216], List.append(&2, U32, segs.bytes(ss), rest))

# the frame headers other than SOF0 (T.81 Table B.1): SOF1 to SOF3, SOF5 to SOF7, SOF9 to SOF11, SOF13 to SOF15
type Sofn is Data:
  Sof1{}
  Sof2{}
  Sof3{}
  Sof5{}
  Sof6{}
  Sof7{}
  Sof9{}
  Sof10{}
  Sof11{}
  Sof13{}
  Sof14{}
  Sof15{}

# a frame header's second byte
def sofn.byte(sn: Sofn) -> U32:
  match sn:
    case Sof1{}:
      193
    case Sof2{}:
      194
    case Sof3{}:
      195
    case Sof5{}:
      197
    case Sof6{}:
      198
    case Sof7{}:
      199
    case Sof9{}:
      201
    case Sof10{}:
      202
    case Sof11{}:
      203
    case Sof13{}:
      205
    case Sof14{}:
      206
    case Sof15{}:
      207

# LAW: bytes that open with SOI and segments that are not frame headers, then a frame header other than SOF0,
# decode to none, whatever follows
# IMG-JPG-1
law jpeg_refuse_sofn:
  for +segs: List<&2, Seg>
  for h_fit: segs.Fit(segs)
  for +sn: Sofn
  for +rest: List<&2, U32>
  {Img.decode_jpeg(jpeg.lead(segs, 255 <> (sofn.byte(sn) <> rest))) == None{} : Maybe<&2, Img.Raster>}

# LAW: bytes that open with SOI and segments that are not frame headers, then an SOF0 segment whose sample
# precision is not 8, decode to none, whatever follows
# IMG-JPG-1
law jpeg_refuse_precision:
  for +segs: List<&2, Seg>
  for h_fit: segs.Fit(segs)
  for +hi: U32
  for +lo: U32
  for +pp: U32
  for +body: List<&2, U32>
  for h_len: seg.Fits(hi, lo, pp <> body)
  for h_pp: {U32.is_eq(pp, 8) == False{} : Bool}
  for +rest: List<&2, U32>
  {Img.decode_jpeg(jpeg.lead(segs, List.append(&2, U32, 255 <> (192 <> (hi <> (lo <> (pp <> body)))), rest)))
    == None{} : Maybe<&2, Img.Raster>}
