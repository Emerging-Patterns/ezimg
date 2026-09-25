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

# ---- wp6-raster ----

# is the raster well formed: its sample count is w * h, computed as a Nat
def wf(img: Img.Raster) -> Bool:
  match img:
    case Img.Raster{ww, hh, px}:
      Nat.is_eq(List.length(&2, U32, px), Nat.mul(U32.to_nat(ww), U32.to_nat(hh)))

# is (x, y) a point of the raster: x < w and y < h, as Nats
def inside(img: Img.Raster, +xx: U32, +yy: U32) -> Bool:
  match img:
    case Img.Raster{ww, hh, _px}:
      Bool.and(Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)), Nat.is_lt(U32.to_nat(yy), U32.to_nat(hh)))

# where (x, y) sits in the samples of a raster of width w: y * w + x, as a Nat
def spot(ww: U32, xx: U32, yy: U32) -> Nat:
  Nat.add(Nat.mul(U32.to_nat(yy), U32.to_nat(ww)), U32.to_nat(xx))

# The laws below take w * h < 2^32 as a U32 `area` whose value is w * h: a
# Nat is below 2^32 exactly when it is some U32's value. (A closed 2^32 in a
# law would be expanded in unary by the checker.)

# LAW: fill(w, h, c) is well formed, for every w and h with w * h < 2^32 and every c
# IMG-RAS-1
law fill_wf:
  for +ww: U32
  for +hh: U32
  for +color: U32
  for +area: U32
  for h_area: {U32.to_nat(area) == Nat.mul(U32.to_nat(ww), U32.to_nat(hh)) : Nat}
  {wf(Img.fill(ww, hh, color)) == True{} : Bool}

# LAW: every sample of fill(w, h, c) is c, for every w, h and c
# IMG-RAS-1
law fill_every:
  for +ww: U32
  for +hh: U32
  for +color: U32
  for kk: Nat
  for +vv: U32
  for h_at: {List.get(&2, U32, Img.pixels(Img.fill(ww, hh, color)), kk) == Some{vv} : Maybe<&2, U32>}
  {vv == color : U32}

# LAW: inside the raster, get(r, x, y) is sample y * w + x, when w * h < 2^32
# IMG-RAS-2
law get_inside:
  for +img: Img.Raster
  for +xx: U32
  for +yy: U32
  for +area: U32
  for h_area: {U32.to_nat(area) == Nat.mul(U32.to_nat(Img.width(img)), U32.to_nat(Img.height(img))) : Nat}
  for +h_in: {inside(img, xx, yy) == True{} : Bool}
  {Img.get(img, xx, yy) == List.get(&2, U32, Img.pixels(img), spot(Img.width(img), xx, yy)) : Maybe<&2, U32>}

# LAW: inside a well-formed raster, get(r, x, y) is some, when w * h < 2^32
# IMG-RAS-2
law get_inside_some:
  for +img: Img.Raster
  for +xx: U32
  for +yy: U32
  for +area: U32
  for h_area: {U32.to_nat(area) == Nat.mul(U32.to_nat(Img.width(img)), U32.to_nat(Img.height(img))) : Nat}
  for h_wf: {wf(img) == True{} : Bool}
  for +h_in: {inside(img, xx, yy) == True{} : Bool}
  {Maybe.is_some(&2, U32, Img.get(img, xx, yy)) == True{} : Bool}

# LAW: outside the raster, get(r, x, y) is none, for every raster
# IMG-RAS-2
law get_outside:
  for +img: Img.Raster
  for +xx: U32
  for +yy: U32
  for h_out: {inside(img, xx, yy) == False{} : Bool}
  {Img.get(img, xx, yy) == None{} : Maybe<&2, U32>}

# LAW: inside the raster, set(r, x, y, c) replaces sample y * w + x with c and
# nothing else, when w * h < 2^32
# IMG-RAS-2
law set_inside:
  for +img: Img.Raster
  for +xx: U32
  for +yy: U32
  for +color: U32
  for +area: U32
  for h_area: {U32.to_nat(area) == Nat.mul(U32.to_nat(Img.width(img)), U32.to_nat(Img.height(img))) : Nat}
  for +h_in: {inside(img, xx, yy) == True{} : Bool}
  {Img.set(img, xx, yy, color) == Img.raster(Img.width(img), Img.height(img),
    List.set(&2, U32, Img.pixels(img), spot(Img.width(img), xx, yy), color)) : Img.Raster}

# LAW: outside the raster, set(r, x, y, c) is r, for every raster
# IMG-RAS-2
law set_outside:
  for +img: Img.Raster
  for +xx: U32
  for +yy: U32
  for +color: U32
  for h_out: {inside(img, xx, yy) == False{} : Bool}
  {Img.set(img, xx, yy, color) == img : Img.Raster}

# how much of the span x .. x + c - 1 lies in 0 .. w - 1: min(c, w - x), and
# 0 when x >= w (Nat.sub stops at 0)
def cut(ww: U32, xx: U32, cc: U32) -> Nat:
  Nat.min(U32.to_nat(cc), Nat.sub(U32.to_nat(ww), U32.to_nat(xx)))

# one side of a crop: the intersection's side aa, or 0 when either side of
# the intersection (aa or bb) is 0
def side(aa: Nat, bb: Nat) -> Nat:
  match aa bb:
    case 0n _bb:
      0n
    case 1n+_pa 0n:
      0n
    case 1n+pa 1n+_pb:
      1n+pa

# LAW: crop's width and height are those of the rectangle's intersection with the raster, 0 by 0 when that is
# empty, for every raster
# IMG-RAS-3
law crop_size:
  for +img: Img.Raster
  for +xx: U32
  for +yy: U32
  for +cw: U32
  for +ch: U32
  {(U32.to_nat(Img.width(Img.crop(img, xx, yy, cw, ch))), U32.to_nat(Img.height(Img.crop(img, xx, yy, cw, ch)))) ==
    (side(cut(Img.width(img), xx, cw), cut(Img.height(img), yy, ch)),
      side(cut(Img.height(img), yy, ch), cut(Img.width(img), xx, cw))) : Nat & Nat}

# LAW: crop of a well-formed raster is well formed, when w * h < 2^32
# IMG-RAS-3
law crop_wf:
  for +img: Img.Raster
  for +xx: U32
  for +yy: U32
  for +cw: U32
  for +ch: U32
  for +area: U32
  for h_area: {U32.to_nat(area) == Nat.mul(U32.to_nat(Img.width(img)), U32.to_nat(Img.height(img))) : Nat}
  for h_wf: {wf(img) == True{} : Bool}
  {wf(Img.crop(img, xx, yy, cw, ch)) == True{} : Bool}

# LAW: the crop's sample at (i, j) is the raster's sample at (x + i, y + j), for every point (i, j) of the crop of
# a well-formed raster, when w * h < 2^32
# IMG-RAS-3
law crop_at:
  for +img: Img.Raster
  for +xx: U32
  for +yy: U32
  for +cw: U32
  for +ch: U32
  for +area: U32
  for h_area: {U32.to_nat(area) == Nat.mul(U32.to_nat(Img.width(img)), U32.to_nat(Img.height(img))) : Nat}
  for h_wf: {wf(img) == True{} : Bool}
  for +ii: Nat
  for +jj: Nat
  for hi: {Nat.is_lt(ii, U32.to_nat(Img.width(Img.crop(img, xx, yy, cw, ch)))) == True{} : Bool}
  for hj: {Nat.is_lt(jj, U32.to_nat(Img.height(Img.crop(img, xx, yy, cw, ch)))) == True{} : Bool}
  {List.get(&2, U32, Img.pixels(Img.crop(img, xx, yy, cw, ch)),
    Nat.add(Nat.mul(jj, U32.to_nat(Img.width(Img.crop(img, xx, yy, cw, ch)))), ii)) ==
    List.get(&2, U32, Img.pixels(img),
      Nat.add(Nat.mul(Nat.add(U32.to_nat(yy), jj), U32.to_nat(Img.width(img))), Nat.add(U32.to_nat(xx), ii))) :
    Maybe<&2, U32>}

# does src, pasted at (x, y), cover the point (i, j): x <= i < x + sw and
# y <= j < y + sh, as Nats
def covers(+xx: U32, +yy: U32, src: Img.Raster, +ii: Nat, +jj: Nat) -> Bool:
  match src:
    case Img.Raster{sw, sh, _sp}:
      Bool.and(Bool.and(Nat.is_le(U32.to_nat(xx), ii), Nat.is_lt(ii, Nat.add(U32.to_nat(xx), U32.to_nat(sw)))),
        Bool.and(Nat.is_le(U32.to_nat(yy), jj), Nat.is_lt(jj, Nat.add(U32.to_nat(yy), U32.to_nat(sh)))))

# LAW: blit(dst, src, x, y) has dst's width and height, for every dst, src and offset
# IMG-RAS-4
law blit_size:
  for +dst: Img.Raster
  for +src: Img.Raster
  for +xx: U32
  for +yy: U32
  {Img.size(Img.blit(dst, src, xx, yy)) == Img.size(dst) : U32 & U32}

# LAW: blit of a well-formed src onto a well-formed dst is well formed, when dst's w * h < 2^32
# IMG-RAS-4
law blit_wf:
  for +dst: Img.Raster
  for +src: Img.Raster
  for +xx: U32
  for +yy: U32
  for +area: U32
  for h_area: {U32.to_nat(area) == Nat.mul(U32.to_nat(Img.width(dst)), U32.to_nat(Img.height(dst))) : Nat}
  for h_dst: {wf(dst) == True{} : Bool}
  for h_src: {wf(src) == True{} : Bool}
  {wf(Img.blit(dst, src, xx, yy)) == True{} : Bool}

# LAW: at every point (i, j) of dst that src covers, blit takes src's sample at (i - x, j - y), for well-formed
# dst and src, when dst's w * h < 2^32
# IMG-RAS-4
law blit_in:
  for +dst: Img.Raster
  for +src: Img.Raster
  for +xx: U32
  for +yy: U32
  for +area: U32
  for h_area: {U32.to_nat(area) == Nat.mul(U32.to_nat(Img.width(dst)), U32.to_nat(Img.height(dst))) : Nat}
  for h_dst: {wf(dst) == True{} : Bool}
  for h_src: {wf(src) == True{} : Bool}
  for +ii: Nat
  for +jj: Nat
  for +hi: {Nat.is_lt(ii, U32.to_nat(Img.width(dst))) == True{} : Bool}
  for +hj: {Nat.is_lt(jj, U32.to_nat(Img.height(dst))) == True{} : Bool}
  for +h_cov: {covers(xx, yy, src, ii, jj) == True{} : Bool}
  {List.get(&2, U32, Img.pixels(Img.blit(dst, src, xx, yy)), Nat.add(Nat.mul(jj, U32.to_nat(Img.width(dst))), ii)) ==
    List.get(&2, U32, Img.pixels(src),
      Nat.add(Nat.mul(Nat.sub(jj, U32.to_nat(yy)), U32.to_nat(Img.width(src))), Nat.sub(ii, U32.to_nat(xx)))) :
    Maybe<&2, U32>}

# LAW: at every point (i, j) of dst that src does not cover, blit keeps dst's sample, for well-formed dst and src,
# when dst's w * h < 2^32
# IMG-RAS-4
law blit_out:
  for +dst: Img.Raster
  for +src: Img.Raster
  for +xx: U32
  for +yy: U32
  for +area: U32
  for h_area: {U32.to_nat(area) == Nat.mul(U32.to_nat(Img.width(dst)), U32.to_nat(Img.height(dst))) : Nat}
  for h_dst: {wf(dst) == True{} : Bool}
  for h_src: {wf(src) == True{} : Bool}
  for +ii: Nat
  for +jj: Nat
  for +hi: {Nat.is_lt(ii, U32.to_nat(Img.width(dst))) == True{} : Bool}
  for +hj: {Nat.is_lt(jj, U32.to_nat(Img.height(dst))) == True{} : Bool}
  for +h_cov: {covers(xx, yy, src, ii, jj) == False{} : Bool}
  {List.get(&2, U32, Img.pixels(Img.blit(dst, src, xx, yy)), Nat.add(Nat.mul(jj, U32.to_nat(Img.width(dst))), ii)) ==
    List.get(&2, U32, Img.pixels(dst), Nat.add(Nat.mul(jj, U32.to_nat(Img.width(dst))), ii)) : Maybe<&2, U32>}

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

# ---- wp2-inflate ----

# every value is at most 255, and `ok` carries that forward
def bytes.go(xs: List<&2, U32>, ok: Bool) -> Bool:
  match xs ok:
    case _xs False{}:
      False{}
    case Nil{} True{}:
      True{}
    case +xx <> tl True{}:
      bytes.go(tl, U32.is_le(xx, 255))

# every value of xs is a byte, 0 to 255
def bytes(xs: List<&2, U32>) -> Bool:
  bytes.go(xs, True{})

# the zlib stream ezimg writes for xs in stored blocks of at most sz bytes:
# CMF and FLG 120 1, the encoder's stored blocks, and the Adler-32 of xs
def zlib.stored(+sz: U32, +xs: List<&2, U32>) -> List<&2, U32>:
  Png.enc.cat([120, 1], Png.enc.cat(Png.enc.blocks(sz, xs), Png.enc.be(Inf.adler.of(xs))))

# LAW: every byte list with fewer than 2^32 bytes, in the zlib stream ezimg writes with stored blocks of any size from 1
# to 65535, inflates to itself
# IMG-PNG-7
law inflate_stored:
  for +sz: U32
  for +xs: List<&2, U32>
  for h_sz: {Bool.and(U32.is_le(1, sz), U32.is_le(sz, 65535)) == True{} : Bool}
  for h_by: {bytes(xs) == True{} : Bool}
  for h_n: {U32.to_nat(Png.enc.len(xs, 0)) == List.length(&2, U32, xs) : Nat}
  {Inf.inflate(zlib.stored(sz, xs)) == Some{xs} : Maybe<&2, List<&2, U32>>}

# LAW: the zlib stream enc.zlib writes for a PNG's IDAT inflates to the bytes it was given
# IMG-PNG-7
law inflate_enc_zlib:
  for +xs: List<&2, U32>
  for h_by: {bytes(xs) == True{} : Bool}
  for h_n: {U32.to_nat(Png.enc.len(xs, 0)) == List.length(&2, U32, xs) : Nat}
  {Inf.inflate(Png.enc.zlib(xs, Png.enc.len(xs, 0))) == Some{xs} : Maybe<&2, List<&2, U32>>}

# ---- wp3-filter ----

# the five filter types of PNG section 9.2 (W3C PNG, 9.2 "Filter types for
# filter method 0"): None, Sub, Up, Average and Paeth
type Ft is Data:
  FNone{}
  FSub{}
  FUp{}
  FAvg{}
  FPaeth{}

# the byte PNG writes before a row filtered with each type: 0 to 4
def ft.code(ft: Ft) -> U32:
  match ft:
    case FNone{}:
      0
    case FSub{}:
      1
    case FUp{}:
      2
    case FAvg{}:
      3
    case FPaeth{}:
      4

# entry nn of a newest-first history of bytes, or 0 past its end (outside the image)
def flt.at(hist: List<&2, U32>, nn: Nat) -> U32:
  match hist nn:
    case Nil{} _nn:
      0
    case +hd <> _tl 0n:
      hd
    case _hd <> tl 1n+pp:
      flt.at(tl, pp)

# b, the byte above: the next byte of the previous row, or 0 on the first row
def flt.up(prev: List<&2, U32>) -> U32:
  match prev:
    case Nil{}:
      0
    case +hd <> _tl:
      hd

# the previous row past the byte above
def flt.next(prev: List<&2, U32>) -> List<&2, U32>:
  match prev:
    case Nil{}:
      Nil{}
    case _hd <> tl:
      tl

# |x - y| of two U32s: the smaller taken from the larger
def flt.dist.at(ge: Bool, +xx: U32, +yy: U32) -> U32:
  match ge:
    case True{}:
      (xx - yy : U32)
    case False{}:
      (yy - xx : U32)

# |x - y| of two U32s
def flt.dist(+xx: U32, +yy: U32) -> U32:
  flt.dist.at(U32.is_ge(xx, yy), xx, yy)

# PaethPredictor's choice, in the specification's order: a when pa <= pb and
# pa <= pc, otherwise b when pb <= pc, otherwise c
def flt.paeth.near(
  ab: Bool,
  ac: Bool,
  bc: Bool,
  +aa: U32,
  +bb: U32,
  +cc: U32
) -> U32:
  match ab ac bc:
    case True{} True{} _bc:
      aa
    case True{} False{} True{}:
      bb
    case True{} False{} False{}:
      cc
    case False{} _ac True{}:
      bb
    case False{} _ac False{}:
      cc

# PaethPredictor(a, b, c) of PNG section 9.4, with p = a + b - c expanded so
# no distance goes below zero: |p - a| = |b - c|, |p - b| = |a - c| and
# |p - c| = |a + b - 2c|, 2c being c shifted left one bit
def flt.paeth(+aa: U32, +bb: U32, +cc: U32) -> U32:
  +pa = flt.dist(bb, cc)
  +pb = flt.dist(aa, cc)
  +pc = flt.dist((aa + bb : U32), (cc << 1n : U32))
  flt.paeth.near(U32.is_le(pa, pb), U32.is_le(pa, pc), U32.is_le(pb, pc), aa, bb, cc)

# the predictor each filter type subtracts: None 0, Sub a, Up b, Average
# floor((a + b) / 2), Paeth PaethPredictor(a, b, c)
def flt.pred(ft: Ft, +aa: U32, +bb: U32, +cc: U32) -> U32:
  match ft:
    case FNone{}:
      0
    case FSub{}:
      aa
    case FUp{}:
      bb
    case FAvg{}:
      ((aa + bb : U32) >> 1n : U32)
    case FPaeth{}:
      flt.paeth(aa, bb, cc)

# Filt(x) = Orig(x) - predictor, mod 256, for each byte of one row. `prev`
# is the rest of the previous row, `hist` and `phist` the bytes of this row
# and of the previous row already passed, newest first; a is `bpp` bytes back
# in `hist`, b the byte above, c `bpp` bytes back in `phist`, each 0 outside
# the image
def flt.row(
  row: List<&2, U32>,
  +ft: Ft,
  +bpp: U32,
  +prev: List<&2, U32>,
  +hist: List<&2, U32>,
  +phist: List<&2, U32>
) -> List<&2, U32>:
  match row:
    case Nil{}:
      Nil{}
    case +xx <> rest:
      +aa = flt.at(hist, U32.to_nat((bpp - 1 : U32)))
      +bb = flt.up(prev)
      +cc = flt.at(phist, U32.to_nat((bpp - 1 : U32)))
      U32.and(255, (xx - flt.pred(ft, aa, bb, cc) : U32)) <>
        flt.row(rest, ft, bpp, flt.next(prev), {xx <> hist : List<&2, U32>}, {bb <> phist : List<&2, U32>})

# the filtered image data: each row filtered with `ft` against the row
# before it (none above the first), after its filter type byte
def flt.rows(rows: List<&2, List<&2, U32>>, +ft: Ft, +bpp: U32, prev: List<&2, U32>) -> List<&2, U32>:
  match rows:
    case Nil{}:
      Nil{}
    case +row <> rest:
      ft.code(ft) <> List.append(&2, U32, flt.row(row, ft, bpp, prev, [], []), flt.rows(rest, ft, bpp, row))

# a row of exactly nn bytes, each below 256, with `ok` the answer so far
def flt.bytes(row: List<&2, U32>, nn: Nat, ok: Bool) -> Bool:
  match row nn:
    case Nil{} 0n:
      ok
    case Nil{} 1n+_pp:
      False{}
    case _xx <> _rest 0n:
      False{}
    case +xx <> rest 1n+pp:
      flt.bytes(rest, pp, Bool.and(ok, U32.is_lt(xx, 256)))

# every row nn bytes, each below 256, with `ok` the answer so far
def flt.fit(rows: List<&2, List<&2, U32>>, +nn: Nat, ok: Bool) -> Bool:
  match rows:
    case Nil{}:
      ok
    case +row <> rest:
      flt.fit(rest, nn, Bool.and(ok, flt.bytes(row, nn, True{})))

# the sizes unfilter reads: a nonzero width and height, 1 to 4 bytes per pixel
def flt.dims(+ww: U32, +hh: U32, +bpp: U32) -> Bool:
  Bool.and(U32.is_gt(ww, 0), Bool.and(U32.is_gt(hh, 0), Bool.and(U32.is_gt(bpp, 0), U32.is_le(bpp, 4))))

# LAW: unfilter undoes the PNG filter of every type: rows of width times bpp bytes, filtered by the specification's
# filter function, unfilter to the rows
# IMG-PNG-6
law unfilter_filter:
  for +ft: Ft
  for +ww: U32
  for +hh: U32
  for +bpp: U32
  for +rows: List<&2, List<&2, U32>>
  for +h_dims: {flt.dims(ww, hh, bpp) == True{} : Bool}
  for +h_wrap: {U32.to_nat((ww * bpp : U32)) == Nat.mul(U32.to_nat(ww), U32.to_nat(bpp)) : Nat}
  for h_rows: {List.length(&2, List<&2, U32>, rows) == U32.to_nat(hh) : Nat}
  for h_fit: {flt.fit(rows, Nat.mul(U32.to_nat(ww), U32.to_nat(bpp)), True{}) == True{} : Bool}
  {Png.unfilter(flt.rows(rows, ft, bpp, []), ww, hh, bpp) == Some{List.concat(&2, U32, rows)}
    : Maybe<&2, List<&2, U32>>}

# ---- wp1-crc ----

# the ISO 3309 / ITU-T V.42 CRC-32 polynomial, reflected (PNG section 5.5
# and Annex D): 0xEDB88320
def crc.ref.poly() -> U32:
  3988292384

# one bit, as the specification's sample code does it: when the low bit of
# the register is set, shift right and xor in the polynomial; else shift right
def crc.ref.shift(odd: Bool, +cc: U32) -> U32:
  match odd:
    case True{}:
      ((cc >> 1n : U32) .^. crc.ref.poly() : U32)
    case False{}:
      (cc >> 1n : U32)

# one bit step of the register, low bit first. The register is taken apart
# first, so a register the checker cannot compute stays one stuck match
# instead of being copied into both the test and the shift at every step
def crc.ref.step(cc: U32) -> U32:
  match cc:
    case U32{+ww}:
      crc.ref.shift(U32.is_eq((U32{ww} .&. 1 : U32), 1), U32{ww})

# nn bit steps
def crc.ref.bits(nn: Nat, +cc: U32) -> U32:
  match nn:
    case 0n:
      cc
    case 1n+pp:
      crc.ref.bits(pp, crc.ref.step(cc))

# one byte: xor it into the register, then eight bit steps. Bytes are U32 in
# ezimg and the byte is xored in whole, so for 0 to 255 this is ISO 3309
def crc.ref.byte(+cc: U32, +bb: U32) -> U32:
  crc.ref.bits(8n, (cc .^. bb : U32))

# every byte in order, the register still inverted
def crc.ref.fold(xs: List<&2, U32>, +cc: U32) -> U32:
  match xs:
    case Nil{}:
      cc
    case +bb <> tl:
      crc.ref.fold(tl, crc.ref.byte(cc, bb))

# the bitwise CRC-32: register preset to all ones, all ones xored at the end
def crc.ref(xs: List<&2, U32>) -> U32:
  (crc.ref.fold(xs, 4294967295) .^. 4294967295 : U32)

# LAW: Crc.crc32 is the bitwise ISO 3309 CRC-32, for every byte list
# IMG-PNG-5
law crc32_bitwise:
  for xs: List<&2, U32>
  {Crc.crc32(xs) == crc.ref(xs) : U32}

# a PNG chunk as bytes (PNG section 5.3): the four length bytes, the four
# chunk type bytes, the data, and the four CRC bytes
type Chunk is Data:
  Chunk{
    +l0: U32, +l1: U32, +l2: U32, +l3: U32, +t0: U32, +t1: U32, +t2: U32, +t3: U32, +data: List<&2, U32>,
    +s0: U32, +s1: U32, +s2: U32, +s3: U32
  }

# four bytes read as one number, most significant byte first (PNG section 7.1)
def be.word(+aa: U32, +bb: U32, +cc: U32, +dd: U32) -> U32:
  ((((aa << 24n : U32) .|. (bb << 16n : U32) : U32) .|. (cc << 8n : U32) : U32) .|. dd : U32)

# a chunk's bytes, then rest
def chunk.onto(ck: Chunk, rest: List<&2, U32>) -> List<&2, U32>:
  match ck:
    case Chunk{l0, l1, l2, l3, t0, t1, t2, t3, data, s0, s1, s2, s3}:
      l0 <> l1 <> l2 <> l3 <> t0 <> t1 <> t2 <> t3 <> List.append(&2, U32, data, s0 <> s1 <> s2 <> s3 <> rest)

# chunks' bytes one after another, then rest
def chunks.onto(cs: List<&2, Chunk>, rest: List<&2, U32>) -> List<&2, U32>:
  match cs:
    case Nil{}:
      rest
    case ck <> tl:
      chunk.onto(ck, chunks.onto(tl, rest))

# the chunk's length field counts its data bytes
def chunk.framed(ck: Chunk) -> Type:
  match ck:
    case Chunk{l0, l1, l2, l3, _t0, _t1, _t2, _t3, data, _s0, _s1, _s2, _s3}:
      {U32.to_nat(be.word(l0, l1, l2, l3)) == List.length(&2, U32, data) : Nat}

# every chunk's length field counts its data bytes
def chunks.framed(cs: List<&2, Chunk>) -> Type:
  match cs:
    case Nil{}:
      Unit
    case ck <> tl:
      chunk.framed(ck) & chunks.framed(tl)

# the CRC a chunk stores
def chunk.stored(ck: Chunk) -> U32:
  match ck:
    case Chunk{_l0, _l1, _l2, _l3, _t0, _t1, _t2, _t3, _data, s0, s1, s2, s3}:
      be.word(s0, s1, s2, s3)

# the CRC-32 of a chunk's type and data
def chunk.sum(ck: Chunk) -> U32:
  match ck:
    case Chunk{_l0, _l1, _l2, _l3, t0, t1, t2, t3, data, _s0, _s1, _s2, _s3}:
      crc.ref(t0 <> t1 <> t2 <> t3 <> data)

# LAW: after the signature and any framed chunks, a framed chunk whose stored CRC differs from the CRC-32 of its type
# and data makes decode_png none, whatever follows
# IMG-PNG-5
law png_crc_refused:
  for +pre: List<&2, Chunk>
  for +bad: Chunk
  for +rest: List<&2, U32>
  for h_pre: chunks.framed(pre)
  for h_bad: chunk.framed(bad)
  for h_crc: {chunk.stored(bad) == chunk.sum(bad) : U32} -> Empty
  {Img.decode_png(List.append(&2, U32, Img.png_sig(), chunks.onto(pre, chunk.onto(bad, rest))))
    == None{} : Maybe<&2, Img.Raster>}

# ---- wp5-png-decode ----

# the four bytes of a U32, most significant first
def spec.be4(+nn: U32) -> List<&2, U32>:
  [U32.and(255, U32.shrn(nn, 24n)), U32.and(255, U32.shrn(nn, 16n)), U32.and(255, U32.shrn(nn, 8n)), U32.and(255, nn)]

# a PNG file whose first chunk is an IHDR: the signature, the length 13, the
# type IHDR, width, height, bit depth, colour type, compression, filter and
# interlace methods, any four CRC bytes, and any bytes after
def spec.ihdr.file(
  +ww: U32,
  +hh: U32,
  +dd: U32,
  +cc: U32,
  +comp: U32,
  +ff: U32,
  +ii: U32,
  +crc: U32,
  rest: List<&2, U32>
) -> List<&2, U32>:
  List.append(&2, U32, Img.png_sig(), List.append(&2, U32, [0, 0, 0, 13, 73, 72, 68, 82],
    List.append(&2, U32, spec.be4(ww), List.append(&2, U32, spec.be4(hh), List.append(&2, U32, [dd, cc, comp, ff, ii],
      List.append(&2, U32, spec.be4(crc), rest))))))

# the colour types the PNG specification defines for bit depth 8
def spec.colour.ok(+cc: U32) -> Bool:
  Bool.or(U32.is_eq(cc, 0), Bool.or(U32.is_eq(cc, 2), Bool.or(U32.is_eq(cc, 3), Bool.or(U32.is_eq(cc, 4),
    U32.is_eq(cc, 6)))))

# LAW: an IHDR whose bit depth is not 8 makes decode_png none, whatever the other fields, the CRC and the rest
# IMG-PNG-8
law png_depth_refused:
  for +ww: U32
  for +hh: U32
  for +dd: U32
  for +cc: U32
  for +comp: U32
  for +ff: U32
  for +ii: U32
  for +crc: U32
  for +rest: List<&2, U32>
  for h_dd: {U32.is_eq(dd, 8) == False{} : Bool}
  {Img.decode_png(spec.ihdr.file(ww, hh, dd, cc, comp, ff, ii, crc, rest)) == None{} : Maybe<&2, Img.Raster>}

# LAW: an IHDR whose interlace method is not 0 makes decode_png none, whatever the other fields, the CRC and the rest
# IMG-PNG-8
law png_interlace_refused:
  for +ww: U32
  for +hh: U32
  for +dd: U32
  for +cc: U32
  for +comp: U32
  for +ff: U32
  for +ii: U32
  for +crc: U32
  for +rest: List<&2, U32>
  for h_ii: {U32.is_eq(ii, 0) == False{} : Bool}
  {Img.decode_png(spec.ihdr.file(ww, hh, dd, cc, comp, ff, ii, crc, rest)) == None{} : Maybe<&2, Img.Raster>}

# LAW: an IHDR whose colour type is not 0, 2, 3, 4 or 6 makes decode_png none, whatever the other fields, the CRC
# and the rest
# IMG-PNG-8
law png_colour_refused:
  for +ww: U32
  for +hh: U32
  for +dd: U32
  for +cc: U32
  for +comp: U32
  for +ff: U32
  for +ii: U32
  for +crc: U32
  for +rest: List<&2, U32>
  for h_cc: {spec.colour.ok(cc) == False{} : Bool}
  {Img.decode_png(spec.ihdr.file(ww, hh, dd, cc, comp, ff, ii, crc, rest)) == None{} : Maybe<&2, Img.Raster>}

# a sample packed 0xAARRGGBB: alpha in the top byte, then red, green and blue
def spec.argb(+aa: U32, +rr: U32, +gg: U32, +bb: U32) -> U32:
  ((((aa << 24n : U32) .|. (rr << 16n : U32) : U32) .|. (gg << 8n : U32) : U32) .|. bb : U32)

# the alpha of a sample checked against a tRNS key: 0 when it matches, 255 otherwise
def spec.key.alpha(hit: Bool) -> U32:
  match hit:
    case True{}:
      0
    case False{}:
      255

# a list of samples, or none
def spec.cons(+hd: U32, mm: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match mm:
    case None{}:
      None{}
    case Some{tl}:
      Some{hd <> tl}

# colour type 0: each gray byte g is 0xFFgggggg
def spec.grey(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case +gg <> tl:
      spec.argb(255, gg, gg, gg) <> spec.grey(tl)

# colour type 0 with a tRNS key: a gray byte equal to the key has alpha 0
def spec.grey.key(xs: List<&2, U32>, +kk: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case +gg <> tl:
      spec.argb(spec.key.alpha(U32.is_eq(gg, kk)), gg, gg, gg) <> spec.grey.key(tl, kk)

# colour type 4: each gray and alpha pair is 0xAAgggggg; none when a pair is cut short
def spec.ga(xs: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case +gg <> +aa <> tl:
      spec.cons(spec.argb(aa, gg, gg, gg), spec.ga(tl))
    case _xs:
      None{}

# colour type 2: each RGB triple is 0xFFrrggbb; none when a triple is cut short
def spec.rgb(xs: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case +rr <> +gg <> +bb <> tl:
      spec.cons(spec.argb(255, rr, gg, bb), spec.rgb(tl))
    case _xs:
      None{}

# colour type 2 with a tRNS key: a triple equal to the key in all three channels has alpha 0
def spec.rgb.key(xs: List<&2, U32>, +kr: U32, +kg: U32, +kb: U32) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case +rr <> +gg <> +bb <> tl:
      spec.cons(spec.argb(spec.key.alpha(Bool.and(U32.is_eq(rr, kr), Bool.and(U32.is_eq(gg, kg), U32.is_eq(bb, kb)))),
        rr, gg, bb), spec.rgb.key(tl, kr, kg, kb))
    case _xs:
      None{}

# colour type 6: each RGBA quadruple is 0xAArrggbb; none when one is cut short
def spec.rgba(xs: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case +rr <> +gg <> +bb <> +aa <> tl:
      spec.cons(spec.argb(aa, rr, gg, bb), spec.rgba(tl))
    case _xs:
      None{}

# the palette: entry k is PLTE's triple k packed with alpha tRNS byte k, or
# 255 past the end of tRNS
def spec.pal(xs: List<&2, U32>, als: List<&2, U32>) -> List<&2, U32>:
  match xs als:
    case +rr <> +gg <> +bb <> tl Nil{}:
      spec.argb(255, rr, gg, bb) <> spec.pal(tl, [])
    case +rr <> +gg <> +bb <> tl +aa <> at:
      spec.argb(aa, rr, gg, bb) <> spec.pal(tl, at)
    case _xs _als:
      Nil{}

# one index's entry, if the palette has it, before the rest
def spec.idx.at(me: Maybe<&2, U32>, rest: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match me:
    case None{}:
      None{}
    case Some{+cc}:
      spec.cons(cc, rest)

# colour type 3: each index is its palette entry; none when an index is past the palette
def spec.idx(xs: List<&2, U32>, +pal: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case +ix <> tl:
      spec.idx.at(List.get(&2, U32, pal, U32.to_nat(ix)), spec.idx(tl, pal))

# LAW: colour type 0 without tRNS: each gray byte g decodes to 0xFFgggggg
# IMG-PNG-9
law png_px_grey:
  for +xs: List<&2, U32>
  {Png.px.of(0, xs, [], []) == Some{spec.grey(xs)} : Maybe<&2, List<&2, U32>>}

# LAW: colour type 0 with tRNS key k: each gray byte g decodes to 0xFFgggggg, alpha 0 when g is k
# IMG-PNG-9
law png_px_grey_key:
  for +xs: List<&2, U32>
  for +kk: U32
  {Png.px.of(0, xs, [], [0, kk]) == Some{spec.grey.key(xs, kk)} : Maybe<&2, List<&2, U32>>}

# LAW: colour type 4: each gray and alpha pair decodes to 0xAAgggggg
# IMG-PNG-9
law png_px_ga:
  for +xs: List<&2, U32>
  {Png.px.of(4, xs, [], []) == spec.ga(xs) : Maybe<&2, List<&2, U32>>}

# LAW: colour type 2 without tRNS: each RGB triple decodes to 0xFFrrggbb, whatever suggested palette there is
# IMG-PNG-9
law png_px_rgb:
  for +xs: List<&2, U32>
  for +plte: List<&2, U32>
  {Png.px.of(2, xs, plte, []) == spec.rgb(xs) : Maybe<&2, List<&2, U32>>}

# LAW: colour type 2 with tRNS key (kr, kg, kb): each triple decodes to 0xFFrrggbb, alpha 0 when it is the key
# IMG-PNG-9
law png_px_rgb_key:
  for +xs: List<&2, U32>
  for +plte: List<&2, U32>
  for +kr: U32
  for +kg: U32
  for +kb: U32
  {Png.px.of(2, xs, plte, [0, kr, 0, kg, 0, kb]) == spec.rgb.key(xs, kr, kg, kb) : Maybe<&2, List<&2, U32>>}

# LAW: colour type 6: each RGBA quadruple decodes to 0xAArrggbb, whatever suggested palette there is
# IMG-PNG-9
law png_px_rgba:
  for +xs: List<&2, U32>
  for +plte: List<&2, U32>
  {Png.px.of(6, xs, plte, []) == spec.rgba(xs) : Maybe<&2, List<&2, U32>>}

# LAW: colour type 3: when the indices decode, each is its palette entry with alpha from tRNS or 255
# IMG-PNG-9
law png_px_indexed:
  for +xs: List<&2, U32>
  for +plte: List<&2, U32>
  for +trns: List<&2, U32>
  for h_some: {Maybe.is_some(&2, List<&2, U32>, Png.px.of(3, xs, plte, trns)) == True{} : Bool}
  {Png.px.of(3, xs, plte, trns) == spec.idx(xs, spec.pal(plte, trns)) : Maybe<&2, List<&2, U32>>}

# the samples of the unfiltered bytes, when the scanlines unfilter
def spec.px.then(
  mm: Maybe<&2, List<&2, U32>>,
  +colour: U32,
  plte: List<&2, U32>,
  trns: List<&2, U32>
) -> Maybe<&2, List<&2, U32>>:
  match mm:
    case None{}:
      None{}
    case Some{raw}:
      Png.px.of(colour, raw, plte, trns)

# a picture of those samples, when there are some
def spec.pic(mm: Maybe<&2, List<&2, U32>>, +ww: U32, +hh: U32) -> Maybe<&2, Png.Pic>:
  match mm:
    case None{}:
      None{}
    case Some{px}:
      Some{Png.Pic{ww, hh, px}}

# LAW: the decoder's last stage packs the unfiltered bytes of the inflated IDAT data with px.of, for the IHDR's
# colour type, PLTE and tRNS, and keeps the width and height
# IMG-PNG-9
law png_samples_frame:
  for +raw: List<&2, U32>
  for +ww: U32
  for +hh: U32
  for +colour: U32
  for +plte: List<&2, U32>
  for +trns: List<&2, U32>
  {Png.png.samples(Some{raw}, ww, hh, colour, plte, trns) ==
    spec.pic(spec.px.then(Png.unfilter(raw, ww, hh, Png.png.bpp(colour)), colour, plte, trns), ww, hh)
    : Maybe<&2, Png.Pic>}

# ---- wp4-png-encode ----

# a sample's alpha is 255: its top byte, shifted down, is 255
def opaque(cc: U32) -> Bool:
  U32.is_eq(U32.shrn(cc, 24n), 255)

# every sample's alpha is 255
def all_opaque(px: List<&2, U32>) -> Bool:
  List.all(~&2, ~U32, ~opaque, px)

# the colour type the PNG specification gives an 8-bit picture: 2 (RGB) when
# every sample is opaque, 6 (RGBA) otherwise
def colour_type(opq: Bool) -> U32:
  match opq:
    case True{}:
      2
    case False{}:
      6

# a word's four bytes, most significant first
def be32(+nn: U32) -> List<&2, U32>:
  [(255 .&. (nn >> 24n : U32) : U32), (255 .&. (nn >> 16n : U32) : U32), (255 .&. (nn >> 8n : U32) : U32),
    (255 .&. nn : U32)]

# the signature, then IHDR's length (13), its type, and its data: width,
# height, bit depth 8, the colour type, compression 0, filter 0, interlace 0
def ihdr_head(+ww: U32, +hh: U32, +ct: U32) -> List<&2, U32>:
  List.append(&2, U32, Img.png_sig(), List.append(&2, U32, [0, 0, 0, 13, 73, 72, 68, 82],
    List.append(&2, U32, be32(ww), List.append(&2, U32, be32(hh), [8, ct, 0, 0, 0]))))

# LAW: an encoded PNG opens with the signature and an IHDR chunk of the
# raster's width and height, bit depth 8, compression, filter and interlace 0,
# and colour type 2 when every sample has alpha 255, 6 otherwise
# IMG-PNG-4
law png_ihdr:
  for +ww: U32
  for +hh: U32
  for +px: List<&2, U32>
  for h_some: {Maybe.is_some(&2, List<&2, U32>, Img.encode_png(Img.raster(ww, hh, px))) == True{} : Bool}
  exs rest: List<&2, U32>
  {Img.encode_png(Img.raster(ww, hh, px)) ==
    Some{List.append(&2, U32, ihdr_head(ww, hh, colour_type(all_opaque(px))), rest)} : Maybe<&2, List<&2, U32>>}

# half of x, rounded down
def half(xx: Nat) -> Nat:
  match xx:
    case 0n:
      0n
    case 1n+pp:
      match pp:
        case 0n:
          0n
        case 1n+qq:
          1n+half(qq)

# x < 2^n: halving x n times leaves 0
def below(nn: Nat, xx: Nat) -> Bool:
  match nn:
    case 0n:
      Nat.is_eq(xx, 0n)
    case 1n+pp:
      below(pp, half(xx))

# the rasters the row calls encodable: neither side 0, the area w * h (h rows
# of w, as natural numbers) below 2^32, and w * h samples
def png_ok(+ww: U32, +hh: U32, +px: List<&2, U32>) -> Bool:
  +area = Nat.mul(U32.to_nat(hh), U32.to_nat(ww))
  Bool.and(Bool.and(Bool.not(Nat.is_eq(U32.to_nat(ww), 0n)), Bool.not(Nat.is_eq(U32.to_nat(hh), 0n))),
    Bool.and(below(32n, area), Nat.is_eq(List.length(&2, U32, px), area)))

# LAW: a raster with both sides above 0, w * h below 2^32 and w * h samples encodes
# IMG-PNG-3
law png_encodes:
  for +ww: U32
  for +hh: U32
  for +px: List<&2, U32>
  for h_ok: {png_ok(ww, hh, px) == True{} : Bool}
  {Maybe.is_some(&2, List<&2, U32>, Img.encode_png(Img.raster(ww, hh, px))) == True{} : Bool}

# LAW: for a raster of fewer than 2^32 samples, encode_png is none exactly when
# a side is 0, w * h is 2^32 or more, or the sample count is not w * h
# IMG-PNG-3
law png_refuses:
  for +ww: U32
  for +hh: U32
  for +px: List<&2, U32>
  for h_len: {below(32n, List.length(&2, U32, px)) == True{} : Bool}
  {Maybe.is_none(&2, List<&2, U32>, Img.encode_png(Img.raster(ww, hh, px))) == Bool.not(png_ok(ww, hh, px)) : Bool}

# ---- wp8-jpeg-numeric ----

# a sampling factor IMG-JPG-2 allows: 1, 2 or 4
def jpg.fac(+ff: U32) -> Bool:
  Bool.or(U32.is_eq(ff, 1), Bool.or(U32.is_eq(ff, 2), U32.is_eq(ff, 4)))

# both sampling factors of one SOF component are allowed: H is the high
# nibble of its second byte and V the low nibble (T.81 B.2.2)
def jpg.facs(+hv: U32) -> Bool:
  Bool.and(jpg.fac(U32.shrn(hv, 4n)), jpg.fac(U32.and(hv, 15)))

# LAW: a SOF0 segment of one component whose sampling factor is outside 1, 2 and 4, met where a
# segment may start, makes decode_jpeg none, whatever came before and whatever follows
# IMG-JPG-2
law jpeg_refuse_factor1:
  for +pre: List<&2, U32>
  for +frame: Jpeg.Frame
  for +scan: Jpeg.Scan
  for +tabs: Jpeg.Tabs
  for +ent: List<&2, U32>
  for +ri: U32
  for +kind: U32
  for +bad: U32
  for h_walk: {Jpeg.decode.walk(pre, Jpeg.decode.st0()) == Jpeg.St{Jpeg.Seek{}, frame, scan, tabs, ent, ri, kind, bad} :
    Jpeg.St}
  for +yh: U32
  for +yl: U32
  for +xh: U32
  for +xl: U32
  for +c1: U32
  for +f1: U32
  for +q1: U32
  for h_fac: {jpg.facs(f1) == False{} : Bool}
  for +rest: List<&2, U32>
  {Img.decode_jpeg(List.append(&2, U32, pre, 255 <> 192 <> 0 <> 11 <> 8 <> yh <> yl <> xh <> xl <> 1 <> c1 <> f1 <>
    q1 <> rest)) == None{} : Maybe<&2, Img.Raster>}

# LAW: a SOF0 segment of three components, one of them with a sampling factor outside 1, 2 and 4,
# met where a segment may start, makes decode_jpeg none, whatever came before and whatever follows
# IMG-JPG-2
law jpeg_refuse_factor3:
  for +pre: List<&2, U32>
  for +frame: Jpeg.Frame
  for +scan: Jpeg.Scan
  for +tabs: Jpeg.Tabs
  for +ent: List<&2, U32>
  for +ri: U32
  for +kind: U32
  for +bad: U32
  for h_walk: {Jpeg.decode.walk(pre, Jpeg.decode.st0()) == Jpeg.St{Jpeg.Seek{}, frame, scan, tabs, ent, ri, kind, bad} :
    Jpeg.St}
  for +yh: U32
  for +yl: U32
  for +xh: U32
  for +xl: U32
  for +c1: U32
  for +f1: U32
  for +q1: U32
  for +c2: U32
  for +f2: U32
  for +q2: U32
  for +c3: U32
  for +f3: U32
  for +q3: U32
  for h_fac: {Bool.and(Bool.and(jpg.facs(f1), jpg.facs(f2)), jpg.facs(f3)) == False{} : Bool}
  for +rest: List<&2, U32>
  {Img.decode_jpeg(List.append(&2, U32, pre, 255 <> 192 <> 0 <> 17 <> 8 <> yh <> yl <> xh <> xl <> 3 <> c1 <> f1 <>
    q1 <> c2 <> f2 <> q2 <> c3 <> f3 <> q3 <> rest)) == None{} : Maybe<&2, Img.Raster>}

# the data unit at column bx and row by of a component's grid in MCU (mx, my): its pixel origin, and the
# hmax / hi by vmax / vi pixels each of its samples covers (pw, ph), in the frame of width ww and height hh
def jpg.unit(
  +mx: U32,
  +my: U32,
  +hmax: U32,
  +vmax: U32,
  +pw: U32,
  +ph: U32,
  +bx: U32,
  +by: U32,
  +ww: U32,
  +hh: U32
) -> Jpeg.Geom:
  Jpeg.Geom{(mx * hmax * 8 + bx * 8 * pw : U32), (my * vmax * 8 + by * 8 * ph : U32), pw, ph, ww, hh}

# one row of a component's grid in an MCU, left to right from column bx
def jpg.grid.row(
  cols: Nat,
  +bx: U32,
  +by: U32,
  +mx: U32,
  +my: U32,
  +hmax: U32,
  +vmax: U32,
  +pw: U32,
  +ph: U32,
  +ww: U32,
  +hh: U32
) -> List<&2, Jpeg.Geom>:
  match cols:
    case 0n:
      []
    case 1n+pp:
      jpg.unit(mx, my, hmax, vmax, pw, ph, bx, by, ww, hh) <>
        jpg.grid.row(pp, (bx + 1 : U32), by, mx, my, hmax, vmax, pw, ph, ww, hh)

# a component's hi by vi grid in an MCU as T.81 A.2.3 orders it: hi units to a row, rows top to bottom from row by
def jpg.grid(
  rows: Nat,
  +by: U32,
  +hi: U32,
  +mx: U32,
  +my: U32,
  +hmax: U32,
  +vmax: U32,
  +pw: U32,
  +ph: U32,
  +ww: U32,
  +hh: U32
) -> List<&2, Jpeg.Geom>:
  match rows:
    case 0n:
      []
    case 1n+pp:
      List.append(&2, Jpeg.Geom, jpg.grid.row(U32.to_nat(hi), 0, by, mx, my, hmax, vmax, pw, ph, ww, hh),
        jpg.grid(pp, (by + 1 : U32), hi, mx, my, hmax, vmax, pw, ph, ww, hh))

# where the decoder puts the component's data units bi, bi + 1, ..., in scan order, for a
# one-component scan whose component has factors hi and vi
def jpg.blocks(
  left: Nat,
  +bi: U32,
  +hi: U32,
  +vi: U32,
  +mx: U32,
  +my: U32,
  +hmax: U32,
  +vmax: U32,
  +ww: U32,
  +hh: U32
) -> List<&2, Jpeg.Geom>:
  match left:
    case 0n:
      []
    case 1n+pp:
      Jpeg.decode.geom.go(0, bi, mx, my, ww, hh, hmax, vmax, [0], [0], [hi], [vi]) <>
        jpg.blocks(pp, (bi + 1 : U32), hi, vi, mx, my, hmax, vmax, ww, hh)

# LAW: for sampling factors 1, 2 or 4, the decoder places a component's hi * vi data units of an MCU
# in T.81 A.2.3's order, hi to a row, each sample covering hmax / hi by vmax / vi pixels
# IMG-JPG-2
law jpeg_mcu_grid:
  for +hi: U32
  for +vi: U32
  for h_hi: {jpg.fac(hi) == True{} : Bool}
  for +h_vi: {jpg.fac(vi) == True{} : Bool}
  for +mx: U32
  for +my: U32
  for +hmax: U32
  for +vmax: U32
  for +ww: U32
  for +hh: U32
  {jpg.blocks(U32.to_nat((hi * vi : U32)), 0, hi, vi, mx, my, hmax, vmax, ww, hh) ==
    jpg.grid(U32.to_nat(vi), 0, hi, mx, my, hmax, vmax, U32.div(hmax, hi), U32.div(vmax, vi), ww, hh) :
    List<&2, Jpeg.Geom>}

# one pixel row of the pixels a sample covers: columns x0 + px onward, left pixels left. Each pixel is
# written by the decoder's own Jpeg.decode.splat.in, which writes a pixel only when it lies inside the frame
def jpg.cover.px(
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
    case 1n+pp:
      jpg.cover.px(pp, Jpeg.decode.splat.in(U32.is_lt((x0 + px : U32), ww), U32.is_lt(yy, hh), plane, (x0 + px : U32),
        yy, ww, vv), x0, yy, (px + 1 : U32), ww, hh, vv)

# the pw by ph pixels one sample covers, from (x0, y0 + py), row by row
def jpg.cover.py(
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
    case 1n+pp:
      jpg.cover.py(pp, jpg.cover.px(U32.to_nat(pw), plane, x0, (y0 + py : U32), 0, ww, hh, vv), x0, y0, (py + 1 : U32),
        pw, ww, hh, vv)

# samples k = 8 * row + col onward of an 8 by 8 block, each replicated over the pw by ph pixels at
# (ox + col * pw, oy + row * ph): sample col to col 7 of this row, then the rows below
def jpg.cover.col(
  left: Nat,
  plane: Array<U32>,
  +samples: List<&2, U32>,
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
    case 1n+pp:
      jpg.cover.col(pp, jpg.cover.py(U32.to_nat(ph), plane, (ox + col * pw : U32), (oy + row * ph : U32), 0, pw, ww,
        hh, Jpeg.decode.at(samples, (row * 8 + col : U32))), samples, row, (col + 1 : U32), ox, oy, pw, ph, ww, hh)

# the eight rows of samples of a block, top to bottom from row
def jpg.cover(
  left: Nat,
  plane: Array<U32>,
  +samples: List<&2, U32>,
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
    case 1n+pp:
      jpg.cover(pp, jpg.cover.col(8n, plane, samples, row, 0, ox, oy, pw, ph, ww, hh), samples, (row + 1 : U32), ox,
        oy, pw, ph, ww, hh)

# LAW: painting one 8 by 8 block whose samples each cover pw by ph pixels, pw and ph each 1, 2 or 4 but not
# both 4, writes its sample k over the pw by ph pixels at (ox + (k mod 8) * pw, oy + (k div 8) * ph) that lie
# inside the frame, row by row, and nothing else. The 4 by 4 case is left out to keep the gate fast: its
# proof normalises 1024 nested writes and takes about 100 seconds on its own.
# IMG-JPG-2
law jpeg_block_cover:
  for +pw: U32
  for +ph: U32
  for +h_pw: {jpg.fac(pw) == True{} : Bool}
  for +h_ph: {jpg.fac(ph) == True{} : Bool}
  for h_44: {Bool.and(U32.is_eq(pw, 4), U32.is_eq(ph, 4)) == False{} : Bool}
  for +ox: U32
  for +oy: U32
  for +ww: U32
  for +hh: U32
  for +samples: List<&2, U32>
  for +nn: U32
  {Jpeg.decode.paint.use(Jpeg.Geom{ox, oy, pw, ph, ww, hh}, True{}, samples, Jpeg.decode.plane(nn)) ==
    jpg.cover(8n, Jpeg.decode.plane(nn), samples, 0, ox, oy, pw, ph, ww, hh) : Array<U32>}

# three samples' colour, when all three are there
def jpg.rgb3(yy: Maybe<&2, U32>, bb: Maybe<&2, U32>, rr: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match yy:
    case None{}:
      None{}
    case Some{yv}:
      match bb:
        case None{}:
          None{}
        case Some{bv}:
          match rr:
            case None{}:
              None{}
            case Some{rv}:
              Some{Jpeg.rgb(yv, bv, rv)}

# LAW: the colour pass is pointwise: sample k of decode.rgbs is Jpeg.rgb of point k's Y, Cb and Cr,
# and there is no sample k when a plane has no point k
# IMG-JPG-2
law jpeg_rgbs_at:
  for +ys: List<&2, U32>
  for +bs: List<&2, U32>
  for +rs: List<&2, U32>
  for +kk: Nat
  {List.get(&2, U32, Jpeg.decode.rgbs(ys, bs, rs), kk) ==
    jpg.rgb3(List.get(&2, U32, ys, kk), List.get(&2, U32, bs, kk), List.get(&2, U32, rs, kk)) : Maybe<&2, U32>}

# true when no element of xs is want
def jpg.absent(xs: List<&2, U32>, +want: U32) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case xx <> rest:
      Bool.and(Bool.not(U32.is_eq(xx, want)), jpg.absent(rest, want))

# nn plus the number of elements of xs, as a U32
def jpg.count(xs: List<&2, U32>, +nn: U32) -> U32:
  match xs:
    case Nil{}:
      nn
    case _xx <> rest:
      jpg.count(rest, (nn + 1 : U32))

# LAW: the frame component a scan component names is found at its first place in the frame's
# identifiers, so a component of a scan with several takes that frame component's factors and table
# IMG-JPG-2
law jpeg_comp_index:
  for +pre: List<&2, U32>
  for +want: U32
  for +post: List<&2, U32>
  for +h_new: {jpg.absent(pre, want) == True{} : Bool}
  {Jpeg.decode.index(List.append(&2, U32, pre, want <> post), False{}, want, 0) == jpg.count(pre, 0) : U32}

# the data units the scan's component comp has in an MCU: its frame component's hi * vi
def jpg.units(+comp: U32, +sids: List<&2, U32>, +ids: List<&2, U32>, +hs: List<&2, U32>, +vs: List<&2, U32>) -> U32:
  +fi = Jpeg.decode.index(ids, False{}, Jpeg.decode.at(sids, comp), 0)
  (Jpeg.decode.at(hs, fi) * Jpeg.decode.at(vs, fi) : U32)

# LAW: the MCU walk goes from data unit bi of a scan component to unit bi + 1 of the same component
# while the component has more units in the MCU, with no restart between
# IMG-JPG-2
law jpeg_walk_unit:
  for +comp: U32
  for +bi: U32
  for +mx: U32
  for +my: U32
  for +mcu: U32
  for +rst: U32
  for +ww: U32
  for +hh: U32
  for +nf: U32
  for +ids: List<&2, U32>
  for +hs: List<&2, U32>
  for +vs: List<&2, U32>
  for +tq: List<&2, U32>
  for +hmax: U32
  for +vmax: U32
  for +ns: U32
  for +sids: List<&2, U32>
  for +td: List<&2, U32>
  for +ta: List<&2, U32>
  for +ss: U32
  for +se: U32
  for +ah: U32
  for +ri: U32
  for h_more: {U32.is_lt((bi + 1 : U32), jpg.units(comp, sids, ids, hs, vs)) == True{} : Bool}
  {Jpeg.decode.adv(Jpeg.Ctrl{comp, bi, mx, my, mcu, rst}, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax},
    Jpeg.Scan{ns, sids, td, ta, ss, se, ah}, ri) ==
    Jpeg.Adv{Jpeg.Ctrl{comp, (bi + 1 : U32), mx, my, mcu, rst}, 0, rst} : Jpeg.Adv}

# LAW: after a scan component's last data unit in an MCU, the walk goes to unit 0 of the next scan
# component of the same MCU, with no restart between
# IMG-JPG-2
law jpeg_walk_comp:
  for +comp: U32
  for +bi: U32
  for +mx: U32
  for +my: U32
  for +mcu: U32
  for +rst: U32
  for +ww: U32
  for +hh: U32
  for +nf: U32
  for +ids: List<&2, U32>
  for +hs: List<&2, U32>
  for +vs: List<&2, U32>
  for +tq: List<&2, U32>
  for +hmax: U32
  for +vmax: U32
  for +ns: U32
  for +sids: List<&2, U32>
  for +td: List<&2, U32>
  for +ta: List<&2, U32>
  for +ss: U32
  for +se: U32
  for +ah: U32
  for +ri: U32
  for h_last: {U32.is_lt((bi + 1 : U32), jpg.units(comp, sids, ids, hs, vs)) == False{} : Bool}
  for h_next: {U32.is_lt((comp + 1 : U32), ns) == True{} : Bool}
  {Jpeg.decode.adv(Jpeg.Ctrl{comp, bi, mx, my, mcu, rst}, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax},
    Jpeg.Scan{ns, sids, td, ta, ss, se, ah}, ri) == Jpeg.Adv{Jpeg.Ctrl{(comp + 1 : U32), 0, mx, my, mcu, rst}, 0, rst} :
    Jpeg.Adv}

# the scan component, data unit and MCU number the walk moves to
def jpg.adv.at(adv: Jpeg.Adv) -> U32 & U32 & U32:
  match adv:
    case Jpeg.Adv{ctrl, _due, _expect}:
      match ctrl:
        case Jpeg.Ctrl{comp, bi, _mx, _my, mcu, _rst}:
          (comp, bi, mcu)

# LAW: after the last data unit of the last scan component of MCU mcu, the walk goes to unit 0 of
# the first scan component of MCU mcu + 1
# IMG-JPG-2
law jpeg_walk_mcu:
  for +comp: U32
  for +bi: U32
  for +mx: U32
  for +my: U32
  for +mcu: U32
  for +rst: U32
  for +ww: U32
  for +hh: U32
  for +nf: U32
  for +ids: List<&2, U32>
  for +hs: List<&2, U32>
  for +vs: List<&2, U32>
  for +tq: List<&2, U32>
  for +hmax: U32
  for +vmax: U32
  for +ns: U32
  for +sids: List<&2, U32>
  for +td: List<&2, U32>
  for +ta: List<&2, U32>
  for +ss: U32
  for +se: U32
  for +ah: U32
  for +ri: U32
  for h_last: {U32.is_lt((bi + 1 : U32), jpg.units(comp, sids, ids, hs, vs)) == False{} : Bool}
  for h_end: {U32.is_lt((comp + 1 : U32), ns) == False{} : Bool}
  {jpg.adv.at(Jpeg.decode.adv(Jpeg.Ctrl{comp, bi, mx, my, mcu, rst}, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax,
    vmax}, Jpeg.Scan{ns, sids, td, ta, ss, se, ah}, ri)) == (0, 0, (mcu + 1 : U32)) : U32 & U32 & U32}
# ---- wp9-png-roundtrip ----

# a chunk as PNG section 5.3 lays it out, then rest: the length of the data,
# the four type bytes, the data, and the CRC-32 of the type and the data, the
# length and the CRC four bytes each, most significant first
def spec.chunk(+typ: List<&2, U32>, +data: List<&2, U32>, rest: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, spec.be4(U32.from_nat(List.length(&2, U32, data))), List.append(&2, U32, typ,
    List.append(&2, U32, data, List.append(&2, U32, spec.be4(crc.ref(List.append(&2, U32, typ, data))), rest))))

# a chunk that may be left out, then rest
def spec.chunk.opt(+typ: List<&2, U32>, mm: Maybe<&2, List<&2, U32>>, rest: List<&2, U32>) -> List<&2, U32>:
  match mm:
    case None{}:
      rest
    case Some{data}:
      spec.chunk(typ, data, rest)

# one IDAT chunk for each list of bytes, in order, then rest
def spec.idats(ds: List<&2, List<&2, U32>>, rest: List<&2, U32>) -> List<&2, U32>:
  match ds:
    case Nil{}:
      rest
    case data <> tl:
      spec.chunk([73, 68, 65, 84], data, spec.idats(tl, rest))

# the IHDR data: width, height, bit depth 8, the colour type, and compression,
# filter and interlace methods 0
def spec.ihdr.data(+ww: U32, +hh: U32, +cc: U32) -> List<&2, U32>:
  List.append(&2, U32, spec.be4(ww), List.append(&2, U32, spec.be4(hh), [8, cc, 0, 0, 0]))

# a PNG file in the order PNG section 5.6 gives: the signature, IHDR, PLTE if
# there is one, tRNS if there is one, the IDAT chunks, and IEND
def spec.png(
  +ww: U32,
  +hh: U32,
  +cc: U32,
  plte: Maybe<&2, List<&2, U32>>,
  trns: Maybe<&2, List<&2, U32>>,
  idats: List<&2, List<&2, U32>>
) -> List<&2, U32>:
  List.append(&2, U32, Img.png_sig(), spec.chunk([73, 72, 68, 82], spec.ihdr.data(ww, hh, cc),
    spec.chunk.opt([80, 76, 84, 69], plte, spec.chunk.opt([116, 82, 78, 83], trns,
      spec.idats(idats, spec.chunk([73, 69, 78, 68], [], []))))))

# a list's length, counted in a U32, does not wrap: the list is shorter than 2^32
def spec.fits(xs: List<&2, U32>) -> Type:
  {U32.to_nat(U32.from_nat(List.length(&2, U32, xs))) == List.length(&2, U32, xs) : Nat}

# a chunk that may be left out fits
def spec.fits.opt(mm: Maybe<&2, List<&2, U32>>) -> Type:
  match mm:
    case None{}:
      Unit
    case Some{xs}:
      spec.fits(xs)

# every list fits
def spec.fits.all(ds: List<&2, List<&2, U32>>) -> Type:
  match ds:
    case Nil{}:
      Unit
    case xs <> tl:
      spec.fits(xs) & spec.fits.all(tl)

# a palette's length is a multiple of 3 from 3 to 768: 1 to 256 entries
def spec.pal.len(xs: List<&2, U32>) -> Bool:
  +nn = U32.from_nat(List.length(&2, U32, xs))
  Bool.and(U32.is_gt(nn, 0), Bool.and(U32.is_zero((nn % 3 : U32)), U32.is_le(nn, 768)))

# PLTE (PNG section 11.2.3): colour type 3 needs one; it may appear for colour
# types 2, 3 and 6, with a palette's length
def spec.plte.ok(+cc: U32, mm: Maybe<&2, List<&2, U32>>) -> Bool:
  match mm:
    case None{}:
      Bool.not(U32.is_eq(cc, 3))
    case Some{xs}:
      Bool.and(Bool.or(U32.is_eq(cc, 2), Bool.or(U32.is_eq(cc, 3), U32.is_eq(cc, 6))), spec.pal.len(xs))

# tRNS (PNG section 11.3.2.1): it may appear for colour types 0 and 2, and for
# colour type 3 after a PLTE
def spec.trns.ok(+cc: U32, plte: Maybe<&2, List<&2, U32>>, trns: Maybe<&2, List<&2, U32>>) -> Bool:
  match trns:
    case None{}:
      True{}
    case Some{_xs}:
      Bool.or(Bool.or(U32.is_eq(cc, 0), U32.is_eq(cc, 2)), Bool.and(U32.is_eq(cc, 3), Maybe.is_some(&2, List<&2, U32>,
        plte)))

# a chunk's data, or no bytes when it is left out
def spec.or.nil(mm: Maybe<&2, List<&2, U32>>) -> List<&2, U32>:
  match mm:
    case None{}:
      []
    case Some{xs}:
      xs

# a raster of the samples, when there are some
def spec.raster(mm: Maybe<&2, List<&2, U32>>, +ww: U32, +hh: U32) -> Maybe<&2, Img.Raster>:
  match mm:
    case None{}:
      None{}
    case Some{px}:
      Some{Img.raster(ww, hh, px)}

# the pixel stage's raster from the inflated data: the scanlines unfiltered,
# then packed by px.of for the colour type, PLTE and tRNS; none when the data
# does not inflate or a stage refuses
def spec.decoded(
  mm: Maybe<&2, List<&2, U32>>,
  +ww: U32,
  +hh: U32,
  +cc: U32,
  plte: List<&2, U32>,
  trns: List<&2, U32>
) -> Maybe<&2, Img.Raster>:
  match mm:
    case None{}:
      None{}
    case Some{raw}:
      spec.raster(spec.px.then(Png.unfilter(raw, ww, hh, Png.png.bpp(cc)), cc, plte, trns), ww, hh)

# LAW: the chunk walker hands the pixel stage the IHDR's size and colour type,
# the PLTE and tRNS data, and the IDAT data concatenated: a file of the
# signature, IHDR, PLTE and tRNS where allowed, any IDAT chunks and IEND
# decodes to the raster px.of packs from the unfiltered inflated data
# IMG-PNG-9
law png_walk:
  for +ww: U32
  for +hh: U32
  for +cc: U32
  for +plte: Maybe<&2, List<&2, U32>>
  for +trns: Maybe<&2, List<&2, U32>>
  for +idats: List<&2, List<&2, U32>>
  for h_ww: {U32.is_gt(ww, 0) == True{} : Bool}
  for h_hh: {U32.is_gt(hh, 0) == True{} : Bool}
  for h_cc: {spec.colour.ok(cc) == True{} : Bool}
  for h_pl: {spec.plte.ok(cc, plte) == True{} : Bool}
  for h_tr: {spec.trns.ok(cc, plte, trns) == True{} : Bool}
  for h_fp: spec.fits.opt(plte)
  for h_ft: spec.fits.opt(trns)
  for h_fi: spec.fits.all(idats)
  {Img.decode_png(spec.png(ww, hh, cc, plte, trns, idats)) == spec.decoded(Inf.inflate(List.concat(&2, U32, idats)),
    ww, hh, cc, spec.or.nil(plte), spec.or.nil(trns)) : Maybe<&2, Img.Raster>}

# the channels encode_png writes for each sample: red, green and blue when
# every sample is opaque, and alpha too otherwise
def spec.nch(op: Bool) -> Nat:
  match op:
    case True{}:
      3n
    case False{}:
      4n

# the scanline bytes encode_png writes for a raster: each of the h rows is a
# filter byte, then the channels of its w samples
def spec.scan.len(+ww: U32, +hh: U32, op: Bool) -> Nat:
  Nat.mul(U32.to_nat(hh), 1n+Nat.mul(U32.to_nat(ww), spec.nch(op)))

# what decode_png makes of an encoding, when there is one
def spec.png.back(mm: Maybe<&2, List<&2, U32>>) -> Maybe<&2, Img.Raster>:
  match mm:
    case None{}:
      None{}
    case Some{bytes}:
      Img.decode_png(bytes)

# LAW: a well-formed raster with both sides nonzero whose scanlines fit one
# stored block decodes from its PNG to itself: nb, the scanline byte count
# as a U32, is at most 65535
# IMG-PNG-2
law png_roundtrip_one:
  for +ww: U32
  for +hh: U32
  for +px: List<&2, U32>
  for +nb: U32
  for h_ok: {png_ok(ww, hh, px) == True{} : Bool}
  for h_nb: {U32.to_nat(nb) == spec.scan.len(ww, hh, all_opaque(px)) : Nat}
  for h_one: {U32.is_le(nb, 65535) == True{} : Bool}
  {spec.png.back(Img.encode_png(Img.raster(ww, hh, px))) == Some{Img.raster(ww, hh, px)} : Maybe<&2, Img.Raster>}


# ---- wp10-jpeg-finish ----

# LAW: painting one 8 by 8 block whose samples each cover pw by ph pixels, for every pw and ph (4 by 4
# included) and onto any plane, one that earlier blocks painted included, writes its sample k over the
# pw by ph pixels at (ox + (k mod 8) * pw, oy + (k div 8) * ph) that lie inside the frame, row by row,
# and nothing else
# IMG-JPG-2
law jpeg_block_cover_all:
  for +pw: U32
  for +ph: U32
  for +ox: U32
  for +oy: U32
  for +ww: U32
  for +hh: U32
  for +samples: List<&2, U32>
  for plane: Array<U32>
  {Jpeg.decode.paint.use(Jpeg.Geom{ox, oy, pw, ph, ww, hh}, True{}, samples, plane) ==
    jpg.cover(8n, plane, samples, 0, ox, oy, pw, ph, ww, hh) : Array<U32>}

# LAW: a SOF0 segment of one component whose sampling factor is outside 1, 2 and 4 makes decode_jpeg
# none, whatever came before its marker (fill bytes included), however much longer than the component
# its length field makes the segment, and whatever follows
# IMG-JPG-2
law jpeg_refuse_factor1_any:
  for +pre: List<&2, U32>
  for +frame: Jpeg.Frame
  for +scan: Jpeg.Scan
  for +tabs: Jpeg.Tabs
  for +ent: List<&2, U32>
  for +ri: U32
  for +kind: U32
  for +bad: U32
  for h_walk: {Jpeg.decode.walk(pre, Jpeg.decode.st0()) == Jpeg.St{Jpeg.LenHi{192}, frame, scan, tabs, ent, ri, kind,
    bad} : Jpeg.St}
  for +lh: U32
  for +ll: U32
  for +yh: U32
  for +yl: U32
  for +xh: U32
  for +xl: U32
  for +c1: U32
  for +f1: U32
  for +q1: U32
  for +extra: List<&2, U32>
  for h_len: {U32.is_lt(Jpeg.decode.u16(lh, ll), 2) == False{} : Bool}
  for h_body: {U32.to_nat((Jpeg.decode.u16(lh, ll) - 2 : U32)) == List.length(&2, U32, List.append(&2, U32,
    [8, yh, yl, xh, xl, 1, c1, f1, q1], extra)) : Nat}
  for h_fac: {jpg.facs(f1) == False{} : Bool}
  for +rest: List<&2, U32>
  {Img.decode_jpeg(List.append(&2, U32, pre, lh <> ll <> List.append(&2, U32, List.append(&2, U32,
    [8, yh, yl, xh, xl, 1, c1, f1, q1], extra), rest))) == None{} : Maybe<&2, Img.Raster>}

# LAW: a SOF0 segment of three components, one of them with a sampling factor outside 1, 2 and 4,
# makes decode_jpeg none, whatever came before its marker (fill bytes included), however much longer
# than the components its length field makes the segment, and whatever follows
# IMG-JPG-2
law jpeg_refuse_factor3_any:
  for +pre: List<&2, U32>
  for +frame: Jpeg.Frame
  for +scan: Jpeg.Scan
  for +tabs: Jpeg.Tabs
  for +ent: List<&2, U32>
  for +ri: U32
  for +kind: U32
  for +bad: U32
  for h_walk: {Jpeg.decode.walk(pre, Jpeg.decode.st0()) == Jpeg.St{Jpeg.LenHi{192}, frame, scan, tabs, ent, ri, kind,
    bad} : Jpeg.St}
  for +lh: U32
  for +ll: U32
  for +yh: U32
  for +yl: U32
  for +xh: U32
  for +xl: U32
  for +c1: U32
  for +f1: U32
  for +q1: U32
  for +c2: U32
  for +f2: U32
  for +q2: U32
  for +c3: U32
  for +f3: U32
  for +q3: U32
  for +extra: List<&2, U32>
  for h_len: {U32.is_lt(Jpeg.decode.u16(lh, ll), 2) == False{} : Bool}
  for h_body: {U32.to_nat((Jpeg.decode.u16(lh, ll) - 2 : U32)) == List.length(&2, U32, List.append(&2, U32,
    [8, yh, yl, xh, xl, 3, c1, f1, q1, c2, f2, q2, c3, f3, q3], extra)) : Nat}
  for h_fac: {Bool.and(Bool.and(jpg.facs(f1), jpg.facs(f2)), jpg.facs(f3)) == False{} : Bool}
  for +rest: List<&2, U32>
  {Img.decode_jpeg(List.append(&2, U32, pre, lh <> ll <> List.append(&2, U32, List.append(&2, U32,
    [8, yh, yl, xh, xl, 3, c1, f1, q1, c2, f2, q2, c3, f3, q3], extra), rest))) == None{} : Maybe<&2, Img.Raster>}

# LAW: a SOF0 segment whose component count is neither 1 nor 3 makes decode_jpeg none, whatever its
# components and their sampling factors, whatever came before its marker and whatever follows; with the
# two laws above, a SOF0 frame with a factor outside 1, 2 and 4 is none for every component count
# IMG-JPG-2
law jpeg_refuse_count:
  for +pre: List<&2, U32>
  for +frame: Jpeg.Frame
  for +scan: Jpeg.Scan
  for +tabs: Jpeg.Tabs
  for +ent: List<&2, U32>
  for +ri: U32
  for +kind: U32
  for +bad: U32
  for h_walk: {Jpeg.decode.walk(pre, Jpeg.decode.st0()) == Jpeg.St{Jpeg.LenHi{192}, frame, scan, tabs, ent, ri, kind,
    bad} : Jpeg.St}
  for +lh: U32
  for +ll: U32
  for +yh: U32
  for +yl: U32
  for +xh: U32
  for +xl: U32
  for +nf: U32
  for h_nf: {Bool.or(U32.is_eq(nf, 1), U32.is_eq(nf, 3)) == False{} : Bool}
  for +comps: List<&2, U32>
  for h_len: {U32.is_lt(Jpeg.decode.u16(lh, ll), 2) == False{} : Bool}
  for h_body: {U32.to_nat((Jpeg.decode.u16(lh, ll) - 2 : U32)) == List.length(&2, U32, 8 <> yh <> yl <> xh <> xl <>
    nf <> comps) : Nat}
  for +rest: List<&2, U32>
  {Img.decode_jpeg(List.append(&2, U32, pre, lh <> ll <> List.append(&2, U32, 8 <> yh <> yl <> xh <> xl <> nf <> comps,
    rest))) == None{} : Maybe<&2, Img.Raster>}

# the sampling factor in fs (hs or vs) of the frame component that scan component comp names: the
# first frame component whose identifier is the one the scan lists for comp (jpeg_comp_index)
def jpg.fac.of(+comp: U32, +sids: List<&2, U32>, +ids: List<&2, U32>, +fs: List<&2, U32>) -> U32:
  Jpeg.decode.at(fs, Jpeg.decode.index(ids, False{}, Jpeg.decode.at(sids, comp), 0))

# where the decoder puts data units bi, bi + 1, ... of scan component comp of a scan that lists the
# identifiers sids, in a frame whose components have identifiers ids and factors hs and vs
def jpg.blocks.of(
  left: Nat,
  +bi: U32,
  +comp: U32,
  +sids: List<&2, U32>,
  +ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>,
  +mx: U32,
  +my: U32,
  +hmax: U32,
  +vmax: U32,
  +ww: U32,
  +hh: U32
) -> List<&2, Jpeg.Geom>:
  match left:
    case 0n:
      []
    case 1n+pp:
      Jpeg.decode.geom.go(comp, bi, mx, my, ww, hh, hmax, vmax, sids, ids, hs, vs) <>
        jpg.blocks.of(pp, (bi + 1 : U32), comp, sids, ids, hs, vs, mx, my, hmax, vmax, ww, hh)

# LAW: for every scan component, not only the frame's first, whose frame component has sampling factors
# hi and vi of 1, 2 or 4, the decoder places the component's hi * vi data units of an MCU in T.81
# A.2.3's order, hi to a row, each sample covering hmax / hi by vmax / vi pixels
# IMG-JPG-2
law jpeg_mcu_grid_comp:
  for +comp: U32
  for +sids: List<&2, U32>
  for +ids: List<&2, U32>
  for +hs: List<&2, U32>
  for +vs: List<&2, U32>
  for h_hi: {jpg.fac(jpg.fac.of(comp, sids, ids, hs)) == True{} : Bool}
  for h_vi: {jpg.fac(jpg.fac.of(comp, sids, ids, vs)) == True{} : Bool}
  for +mx: U32
  for +my: U32
  for +hmax: U32
  for +vmax: U32
  for +ww: U32
  for +hh: U32
  {jpg.blocks.of(U32.to_nat((jpg.fac.of(comp, sids, ids, hs) * jpg.fac.of(comp, sids, ids, vs) : U32)), 0, comp, sids,
    ids, hs, vs, mx, my, hmax, vmax, ww, hh) == jpg.grid(U32.to_nat(jpg.fac.of(comp, sids, ids, vs)), 0,
    jpg.fac.of(comp, sids, ids, hs), mx, my, hmax, vmax, U32.div(hmax, jpg.fac.of(comp, sids, ids, hs)),
    U32.div(vmax, jpg.fac.of(comp, sids, ids, vs)), ww, hh) : List<&2, Jpeg.Geom>}

# the value a read of a plane finds
def jpg.val(pp: Array<U32> & U32) -> U32:
  (_aa, vv) = pp
  vv

# LAW: the decoder reads a plane out point by point: sample k of the first nn points is the value
# Array.get finds at index k, for every plane and every k below nn
# IMG-JPG-2
law jpeg_points_at:
  for +nn: Nat
  for plane: Array<U32>
  for +kk: U32
  for h_kk: {Nat.is_lt(U32.to_nat(kk), nn) == True{} : Bool}
  {List.get(&2, U32, Jpeg.decode.points(nn, plane), U32.to_nat(kk)) == Some{jpg.val(Array.get(U32, plane, kk))} :
    Maybe<&2, U32>}

# jj advanced by one, kk times, in U32
def jpg.idx(kk: Nat, +jj: U32) -> U32:
  match kk:
    case 0n:
      jj
    case 1n+pp:
      jpg.idx(pp, (jj + 1 : U32))

# where a block sits in the walk: scan component, data unit, MCU column, MCU row and MCU number (the
# restart count left at 0)
def jpg.pos(ctrl: Jpeg.Ctrl) -> Jpeg.Ctrl:
  match ctrl:
    case Jpeg.Ctrl{comp, bi, mx, my, mcu, _rst}:
      Jpeg.Ctrl{comp, bi, mx, my, mcu, 0}

# the positions of the next left blocks the decoder walks to from ctrl, each step its own decode.adv
def jpg.trace(
  left: Nat,
  +ctrl: Jpeg.Ctrl,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +ri: U32
) -> List<&2, Jpeg.Ctrl>:
  match left:
    case 0n:
      []
    case 1n+pp:
      jpg.pos(ctrl) <> jpg.trace(pp, Jpeg.decode.adv.ctrl(Jpeg.decode.adv(ctrl, frame, scan, ri)), frame, scan, ri)

# T.81 A.2.3: data units bi onward of scan component comp in MCU (mx, my), number mcu
def jpg.o.units(
  left: Nat,
  +comp: U32,
  +bi: U32,
  +mx: U32,
  +my: U32,
  +mcu: U32
) -> List<&2, Jpeg.Ctrl>:
  match left:
    case 0n:
      []
    case 1n+pp:
      Jpeg.Ctrl{comp, bi, mx, my, mcu, 0} <> jpg.o.units(pp, comp, (bi + 1 : U32), mx, my, mcu)

# scan components comp onward of one MCU, each with its frame component's hi * vi data units
def jpg.o.comps(
  left: Nat,
  +comp: U32,
  +mx: U32,
  +my: U32,
  +mcu: U32,
  +sids: List<&2, U32>,
  +ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>
) -> List<&2, Jpeg.Ctrl>:
  match left:
    case 0n:
      []
    case 1n+pp:
      List.append(&2, Jpeg.Ctrl, jpg.o.units(U32.to_nat(jpg.units(comp, sids, ids, hs, vs)), comp, 0,
        mx, my, mcu), jpg.o.comps(pp, (comp + 1 : U32), mx, my, mcu, sids, ids, hs, vs))

# MCUs mx onward of MCU row my, left to right, numbered from mcu, each with the scan's components in order
def jpg.o.row(
  left: Nat,
  +mx: U32,
  +my: U32,
  +mcu: U32,
  +ns: U32,
  +sids: List<&2, U32>,
  +ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>
) -> List<&2, Jpeg.Ctrl>:
  match left:
    case 0n:
      []
    case 1n+pp:
      List.append(&2, Jpeg.Ctrl, jpg.o.comps(U32.to_nat(ns), 0, mx, my, mcu, sids, ids, hs, vs),
        jpg.o.row(pp, (mx + 1 : U32), my, (mcu + 1 : U32), ns, sids, ids, hs, vs))

# MCU rows my onward, top to bottom, mw MCUs to a row, numbered from mcu
def jpg.o.rows(
  left: Nat,
  +my: U32,
  +mcu: U32,
  +mw: U32,
  +ns: U32,
  +sids: List<&2, U32>,
  +ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>
) -> List<&2, Jpeg.Ctrl>:
  match left:
    case 0n:
      []
    case 1n+pp:
      List.append(&2, Jpeg.Ctrl, jpg.o.row(U32.to_nat(mw), 0, my, mcu, ns, sids, ids, hs, vs),
        jpg.o.rows(pp, (my + 1 : U32), jpg.idx(U32.to_nat(mw), mcu), mw, ns, sids, ids, hs, vs))

# ok, and every scan component from comp on, left of them, has at least one data unit
def jpg.units.ok(
  left: Nat,
  +comp: U32,
  +sids: List<&2, U32>,
  +ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>,
  ok: Bool
) -> Bool:
  match left:
    case 0n:
      ok
    case 1n+pp:
      jpg.units.ok(pp, (comp + 1 : U32), sids, ids, hs, vs, Bool.and(ok, U32.is_lt(0, jpg.units(comp, sids, ids, hs,
        vs))))

# LAW: from the first block of a scan, the decoder's walk (its own decode.adv at every step) visits the
# frame's MCUs in raster order, mw = ceil(w / 8 hmax) to a row and any number of rows, and inside each MCU
# the scan's components in order, each component's hi * vi data units in order (T.81 A.2.1 and A.2.3).
# The U32 counters for the data unit, the component and the MCU column never wrap: each stays below the
# count it is compared with, and the MCU row and number count up in step with the order's own.
# IMG-JPG-2
law jpeg_walk_frame:
  for +ww: U32
  for +hh: U32
  for +nf: U32
  for +ids: List<&2, U32>
  for +hs: List<&2, U32>
  for +vs: List<&2, U32>
  for +tq: List<&2, U32>
  for +hmax: U32
  for +vmax: U32
  for +ns: U32
  for +sids: List<&2, U32>
  for +td: List<&2, U32>
  for +ta: List<&2, U32>
  for +ss: U32
  for +se: U32
  for +ah: U32
  for +ri: U32
  for +rst: U32
  for +mh: U32
  for h_ns: {U32.is_lt(0, ns) == True{} : Bool}
  for h_mw: {U32.is_lt(0, Jpeg.decode.ceil(ww, (hmax * 8 : U32))) == True{} : Bool}
  for h_units: {jpg.units.ok(U32.to_nat(ns), 0, sids, ids, hs, vs, True{}) == True{} : Bool}
  {jpg.trace(List.length(&2, Jpeg.Ctrl, jpg.o.rows(U32.to_nat(mh), 0, 0, Jpeg.decode.ceil(ww,
    (hmax * 8 : U32)), ns, sids, ids, hs, vs)), Jpeg.Ctrl{0, 0, 0, 0, 0, rst}, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq,
    hmax, vmax}, Jpeg.Scan{ns, sids, td, ta, ss, se, ah}, ri) == jpg.o.rows(U32.to_nat(mh), 0, 0,
    Jpeg.decode.ceil(ww, (hmax * 8 : U32)), ns, sids, ids, hs, vs) : List<&2, Jpeg.Ctrl>}
