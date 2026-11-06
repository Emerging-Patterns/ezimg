# ezimg: images for Bend 2, with PNG and baseline JPEG decode and encode
#
# A Raster is a width, a height, and row-major samples. PNG decode reads every
# colour type and bit depth, interlaced or not. PNG encode writes colour type
# 2 or 6. JPEG decode reads a baseline sequential frame, and encode_jpeg
# writes one.
import Base
import ./src/png.bend as Png
import ./src/jpeg.bend as Jpeg
import ./src/jpeg_enc.bend as Jenc

# a picture: width, height, and row-major samples, each packed 0xAARRGGBB
type Raster is Data:
  Raster{w: U32, h: U32, pixels: List<&2, U32>}

# the PNG signature: 137 80 78 71 13 10 26 10
def png_sig() -> List<&2, U32>:
  [137, 80, 78, 71, 13, 10, 26, 10]

# the JPEG start-of-image marker: 255 216
def jpeg_soi() -> List<&2, U32>:
  [255, 216]

# how many samples a byte list holds
def nbytes(bytes: List<&2, U32>) -> U32:
  U32.from_nat(List.length(&2, U32, bytes))

# a picture from its width, height, and samples. The samples are taken as
# they are: when there are not w * h of them the raster is not well formed,
# and encode_png and encode_jpeg refuse it. checked_raster checks the count.
def raster(ww: U32, hh: U32, pixels: List<&2, U32>) -> Raster:
  Raster{ww, hh, pixels}

# is ll the start acc plus w steps of h: ll == acc + w * h. `over` says acc
# has already passed ll, and the walk stops there, so no number past ll + h
# is built.
def area.is(wn: Nat, over: Bool, +hn: Nat, +ll: Nat, +acc: Nat) -> Bool:
  match wn over:
    case _wn True{}:
      False{}
    case 0n False{}:
      Nat.is_eq(ll, acc)
    case 1n+p False{}:
      area.is(p, Nat.is_lt(ll, Nat.add(acc, hn)), hn, ll, Nat.add(acc, hn))

# is ll the area w * h. A zero height answers at once; otherwise the area is
# walked a row of h at a time.
def area.of(+wn: Nat, hn: Nat, +ll: Nat) -> Bool:
  match hn:
    case 0n:
      Nat.is_eq(ll, Nat.mul(wn, 0n))
    case 1n+p:
      area.is(wn, False{}, 1n+p, ll, 0n)

def checked.keep(ok: Bool, +ww: U32, +hh: U32, px: List<&2, U32>) -> Maybe<&2, Raster>:
  match ok:
    case True{}:
      Some{Raster{ww, hh, px}}
    case False{}:
      None{}

# a picture from its width, height, and samples, or none unless there are
# exactly w * h samples (w * h a natural number, never wrapped)
def checked_raster(+ww: U32, +hh: U32, +px: List<&2, U32>) -> Maybe<&2, Raster>:
  checked.keep(area.of(U32.to_nat(ww), U32.to_nat(hh), List.length(&2, U32, px)), ww, hh, px)

# the width
def width(img: Raster) -> U32:
  match img:
    case Raster{+w, _h, _px}:
      w

# the height
def height(img: Raster) -> U32:
  match img:
    case Raster{w, +h, _px}:
      h

# the samples
def pixels(img: Raster) -> List<&2, U32>:
  match img:
    case Raster{w, h, +px}:
      px

# width and height together
def size(img: Raster) -> U32 & U32:
  match img:
    case Raster{+w, +h, _px}:
      (w, h)

# how many samples the picture has, as a natural number: w * h for a
# well-formed raster. It counts the samples rather than multiply the sides,
# so it never wraps and never builds a number larger than the samples.
def count(img: Raster) -> Nat:
  match img:
    case Raster{_w, _h, px}:
      List.length(&2, U32, px)

# w rows of h samples of one colour: no count past a side is built
def fill.go(wn: Nat, +hn: Nat, +color: U32) -> List<&2, U32>:
  match wn:
    case 0n:
      Nil{}
    case 1n+p:
      List.append(&2, U32, List.replicate(U32, hn, color), fill.go(p, hn, color))

# the samples of a solid picture; a zero height has none
def fill.px(+wn: Nat, hn: Nat, +color: U32) -> List<&2, U32>:
  match hn:
    case 0n:
      Nil{}
    case 1n+p:
      fill.go(wn, 1n+p, color)

# a solid picture of one sample, w * h of them, for every w and h. The
# samples are built a row at a time and their count is never computed, so a
# side past 2^16 cannot wrap it; a picture too large for memory fails the
# way any allocation does.
def fill(+ww: U32, +hh: U32, +color: U32) -> Raster:
  Raster{ww, hh, fill.px(U32.to_nat(ww), U32.to_nat(hh), color)}

def u.min.pick(le: Bool, +aa: U32, +bb: U32) -> U32:
  match le:
    case True{}:
      aa
    case False{}:
      bb

def u.min(+aa: U32, +bb: U32) -> U32:
  u.min.pick(U32.is_le(aa, bb), aa, bb)

# the first n rows of w samples dropped, a row at a time: the row-major
# index n * w is never built, so it cannot wrap or pass a Nat's range, and
# the walk stops when the samples run out
def skip.rows(nn: Nat, +px: List<&2, U32>, +ww: Nat) -> List<&2, U32>:
  match nn px:
    case 0n _px:
      px
    case 1n+_p Nil{}:
      Nil{}
    case 1n+p _hd <> _tl:
      skip.rows(p, List.drop(&2, U32, px, ww), ww)

# the first n rows of w samples, a row at a time
def take.rows(nn: Nat, +px: List<&2, U32>, +ww: Nat) -> List<&2, U32>:
  match nn px:
    case 0n _px:
      Nil{}
    case 1n+_p Nil{}:
      Nil{}
    case 1n+p _hd <> _tl:
      List.append(&2, U32, List.take(&2, U32, px, ww), take.rows(p, List.drop(&2, U32, px, ww), ww))

# sample x of row n replaced by color, the rows before it walked one at a
# time
def set.rows(nn: Nat, +px: List<&2, U32>, +ww: Nat, +xx: Nat, +color: U32) -> List<&2, U32>:
  match nn px:
    case 0n _px:
      List.set(&2, U32, px, xx, color)
    case 1n+_p Nil{}:
      Nil{}
    case 1n+p _hd <> _tl:
      List.append(&2, U32, List.take(&2, U32, px, ww), set.rows(p, List.drop(&2, U32, px, ww), ww, xx, color))

def get.y(yin: Bool, px: List<&2, U32>, +ww: U32, +xx: U32, +yy: U32) -> Maybe<&2, U32>:
  match yin:
    case False{}:
      None{}
    case True{}:
      List.get(&2, U32, skip.rows(U32.to_nat(yy), px, U32.to_nat(ww)), U32.to_nat(xx))

def get.x(xin: Bool, px: List<&2, U32>, +ww: U32, +hh: U32, +xx: U32, +yy: U32) -> Maybe<&2, U32>:
  match xin:
    case False{}:
      None{}
    case True{}:
      get.y(U32.is_lt(yy, hh), px, ww, xx, yy)

# the sample at (x, y), or none when that point is outside the picture.
# Sample y * w + x is reached a row at a time, so the index never wraps.
def get(img: Raster, +xx: U32, +yy: U32) -> Maybe<&2, U32>:
  match img:
    case Raster{+w, +h, +px}:
      get.x(U32.is_lt(xx, w), px, w, h, xx, yy)

def set.y(
  yin: Bool,
  +ww: U32,
  +hh: U32,
  px: List<&2, U32>,
  +xx: U32,
  +yy: U32,
  +color: U32
) -> Raster:
  match yin:
    case False{}:
      Raster{ww, hh, px}
    case True{}:
      Raster{ww, hh, set.rows(U32.to_nat(yy), px, U32.to_nat(ww), U32.to_nat(xx), color)}

def set.x(
  xin: Bool,
  +ww: U32,
  +hh: U32,
  px: List<&2, U32>,
  +xx: U32,
  +yy: U32,
  +color: U32
) -> Raster:
  match xin:
    case False{}:
      Raster{ww, hh, px}
    case True{}:
      set.y(U32.is_lt(yy, hh), ww, hh, px, xx, yy, color)

# the picture with (x, y) replaced by color; outside, the picture is
# unchanged. Sample y * w + x is reached a row at a time.
def set(img: Raster, +xx: U32, +yy: U32, +color: U32) -> Raster:
  match img:
    case Raster{+w, +h, +px}:
      set.x(U32.is_lt(xx, w), w, h, px, xx, yy, color)

def crop.rows(+nn: Nat, +px: List<&2, U32>, +rw: Nat, +gap: Nat) -> List<&2, U32>:
  match nn:
    case 0n:
      Nil{}
    case 1n+p:
      List.append(&2, U32, List.take(&2, U32, px, rw),
        crop.rows(p, List.drop(&2, U32, px, Nat.add(rw, gap)), rw, gap))

def crop.use(
  zh: Bool,
  +px: List<&2, U32>,
  +ww: U32,
  +xx: U32,
  +yy: U32,
  +rw: U32,
  +rh: U32
) -> Raster:
  match zh:
    case True{}:
      Raster{0, 0, []}
    case False{}:
      Raster{rw, rh,
        crop.rows(U32.to_nat(rh), List.drop(&2, U32, skip.rows(U32.to_nat(yy), px, U32.to_nat(ww)), U32.to_nat(xx)),
          U32.to_nat(rw), U32.to_nat((ww - rw : U32)))}

def crop.open(
  zw: Bool,
  zh: Bool,
  +px: List<&2, U32>,
  +ww: U32,
  +xx: U32,
  +yy: U32,
  +rw: U32,
  +rh: U32
) -> Raster:
  match zw:
    case True{}:
      Raster{0, 0, []}
    case False{}:
      crop.use(zh, px, ww, xx, yy, rw, rh)

def crop.box(
  +px: List<&2, U32>,
  +ww: U32,
  +hh: U32,
  +xx: U32,
  +yy: U32,
  +cw: U32,
  +ch: U32
) -> Raster:
  +rw = u.min(cw, (ww - xx : U32))
  +rh = u.min(ch, (hh - yy : U32))
  crop.open(U32.is_zero(rw), U32.is_zero(rh), px, ww, xx, yy, rw, rh)

def crop.y(
  yin: Bool,
  +px: List<&2, U32>,
  +ww: U32,
  +hh: U32,
  +xx: U32,
  +yy: U32,
  +cw: U32,
  +ch: U32
) -> Raster:
  match yin:
    case False{}:
      Raster{0, 0, []}
    case True{}:
      crop.box(px, ww, hh, xx, yy, cw, ch)

def crop.x(
  xin: Bool,
  +px: List<&2, U32>,
  +ww: U32,
  +hh: U32,
  +xx: U32,
  +yy: U32,
  +cw: U32,
  +ch: U32
) -> Raster:
  match xin:
    case False{}:
      Raster{0, 0, []}
    case True{}:
      crop.y(U32.is_lt(yy, hh), px, ww, hh, xx, yy, cw, ch)

# the intersection of rectangle (x, y, cw, ch) with the picture.
# A miss, or a zero side, is an empty picture.
def crop(img: Raster, +xx: U32, +yy: U32, +cw: U32, +ch: U32) -> Raster:
  match img:
    case Raster{+w, +h, +px}:
      crop.x(U32.is_lt(xx, w), px, w, h, xx, yy, cw, ch)

def blit.row(
  +dp: List<&2, U32>,
  +sp: List<&2, U32>,
  +left: Nat,
  +cover: Nat,
  +tail: Nat
) -> List<&2, U32>:
  List.append(&2, U32, List.take(&2, U32, dp, left), List.append(&2, U32,
    List.take(&2, U32, sp, cover),
    List.take(&2, U32, List.drop(&2, U32, dp, Nat.add(left, cover)), tail)))

def blit.rows(
  +nn: Nat,
  +dp: List<&2, U32>,
  +sp: List<&2, U32>,
  +left: Nat,
  +cover: Nat,
  +tail: Nat,
  +dw: Nat,
  +sw: Nat
) -> List<&2, U32>:
  match nn:
    case 0n:
      Nil{}
    case 1n+p:
      List.append(&2, U32, blit.row(dp, sp, left, cover, tail), blit.rows(p,
        List.drop(&2, U32, dp, dw), List.drop(&2, U32, sp, sw), left, cover, tail, dw, sw))

def blit.join(
  +dp: List<&2, U32>,
  +sp: List<&2, U32>,
  +dw: U32,
  +dh: U32,
  +sw: U32,
  +sh: U32,
  +ox: U32,
  +oy: U32
) -> List<&2, U32>:
  +left = u.min(ox, dw)
  +room = (dw - left : U32)
  +cover = u.min(sw, room)
  +tail = (room - cover : U32)
  +rows = u.min(sh, (dh - oy : U32))
  +yn = U32.to_nat(oy)
  +wn = U32.to_nat(dw)
  +rest = skip.rows(yn, dp, wn)
  List.append(&2, U32, take.rows(yn, dp, wn), List.append(&2, U32,
    blit.rows(U32.to_nat(rows), rest, sp, U32.to_nat(left), U32.to_nat(cover), U32.to_nat(tail), wn,
      U32.to_nat(sw)),
    skip.rows(U32.to_nat(rows), rest, wn)))

def blit.y(
  inside: Bool,
  +dp: List<&2, U32>,
  +sp: List<&2, U32>,
  +dw: U32,
  +dh: U32,
  +sw: U32,
  +sh: U32,
  +ox: U32,
  +oy: U32
) -> List<&2, U32>:
  match inside:
    case False{}:
      dp
    case True{}:
      blit.join(dp, sp, dw, dh, sw, sh, ox, oy)

def blit.src(src: Raster, +dw: U32, +dh: U32, dp: List<&2, U32>, +xx: U32, +yy: U32) -> Raster:
  match src:
    case Raster{+sw, +sh, +sp}:
      Raster{dw, dh, blit.y(U32.is_lt(yy, dh), dp, sp, dw, dh, sw, sh, xx, yy)}

# src pasted onto dst at (x, y). dst keeps its size; samples past its edge are
# dropped, and an overlapping sample takes the source.
def blit(dst: Raster, src: Raster, +xx: U32, +yy: U32) -> Raster:
  match dst:
    case Raster{+dw, +dh, +dp}:
      blit.src(src, dw, dh, dp, xx, yy)

def map.go(~ff: U32 -> U32, px: List<&2, U32>) -> List<&2, U32>:
  match px:
    case Nil{}:
      Nil{}
    case h <> t:
      ff(h) <> map.go(~ff, t)

# every sample passed through f; the width and the height stay
def map(~ff: U32 -> U32, img: Raster) -> Raster:
  match img:
    case Raster{+w, +h, +px}:
      Raster{w, h, map.go(~ff, px)}

# do the bytes open with the bytes of want? Each byte is compared with
# U32.is_eq, not a literal pattern: a literal pattern matches bit by bit, so a
# law over a symbolic byte cannot get past it, while is_eq has a lemma (ueq).
# ok carries the answer so far, so the walk is a tail call.
def sig.match(want: List<&2, U32>, bytes: List<&2, U32>, ok: Bool) -> Bool:
  match want bytes:
    case Nil{} _bytes:
      ok
    case _wh <> _wt Nil{}:
      +_o = ok
      False{}
    case wh <> wt bh <> bt:
      sig.match(wt, bt, Bool.and(ok, U32.is_eq(bh, wh)))

def sig.pick(ok: Bool) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}:
      Some{png_sig()}
    case False{}:
      None{}

# the PNG signature when the bytes open with it, otherwise none
def parse_signature(bytes: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  sig.pick(sig.match(png_sig(), bytes, True{}))

# the raster of the decoded samples when there are exactly h * w of them,
# otherwise none
def decode_png.keep(ok: Bool, +ww: U32, +hh: U32, px: List<&2, U32>) -> Maybe<&2, Raster>:
  match ok:
    case True{}:
      Some{Raster{ww, hh, px}}
    case False{}:
      None{}

# a decoded picture as a raster. The sample count is checked against the
# header's h * w, computed as a natural number, so a header whose scanline
# length wraps a U32 cannot hand back a raster that is not well formed.
def decode_png.pic(mm: Maybe<&2, Png.Pic>) -> Maybe<&2, Raster>:
  match mm:
    case None{}:
      None{}
    case Some{Png.Pic{+w, +h, +px}}:
      decode_png.keep(Nat.is_eq(List.length(&2, U32, px), Nat.mul(U32.to_nat(h), U32.to_nat(w))), w, h, px)

# the picture of the chunks after the signature, when the bytes open with it
def decode_png.of(mm: Maybe<&2, List<&2, U32>>, +bytes: List<&2, U32>) -> Maybe<&2, Png.Pic>:
  match mm bytes:
    case None{} _bytes:
      None{}
    case Some{_sig} 137 <> 80 <> 78 <> 71 <> 13 <> 10 <> 26 <> 10 <> rest:
      Png.decode(rest)
    case Some{_sig} _other:
      None{}

# PNG bytes, or none when the signature or the encoding is rejected
def decode_png(+bytes: List<&2, U32>) -> Maybe<&2, Raster>:
  decode_png.pic(decode_png.of(parse_signature(bytes), bytes))

# ISO/IEC 15948 / W3C PNG — bytes of an 8-bit picture, interlace method 0.
# Colour type 2 when every sample is opaque, otherwise colour type 6.
# None when a side is zero, the sample count is not the area, or the area
# is 2^28 samples or more: below that bound every count the encoder keeps is
# exact and its one IDAT chunk is shorter than PNG's 2^31 - 1 byte limit, and
# decode_png reads every encoding back (laws/PngRoundTrips.bend).
#
# Not compressed: every row has filter type None and the zlib stream is
# stored (uncompressed) DEFLATE blocks, so a file is the h (k w + 1)
# filtered bytes (k = 3 or 4 channels), 5 more bytes per 65535 of them, and
# about 60 bytes of chunks. A 320x260 RGB picture is about 250 KB, where
# zlib at level 6 makes about 33 KB of it. The round-trip proof rests on
# the stored blocks; re-compress the file elsewhere when size matters.
def encode_png(img: Raster) -> Maybe<&2, List<&2, U32>>:
  match img:
    case Raster{+w, +h, +px}:
      Png.enc.file(w, h, px)

def decode_jpeg.out(got: Maybe<&2, Jpeg.Pic>) -> Maybe<&2, Raster>:
  match got:
    case None{}:
      None{}
    case Some{Jpeg.Pic{w, h, px}}:
      Some{Raster{w, h, px}}

# a baseline sequential JPEG, or none when the bytes are not one
def decode_jpeg(bytes: List<&2, U32>) -> Maybe<&2, Raster>:
  decode_jpeg.out(Jpeg.decode(bytes))

# a sample's colour, alpha cleared. The mask is the first operand, so a law
# one channel of a sample flattened onto white: a / 255 of the channel over (255 - a) / 255 of white, rounded
def colour.ch(+cc: U32, +aa: U32) -> U32:
  U32.div((cc * aa + (255 - aa) * 255 + 127 : U32), 255)

# a sample's colour flattened onto white, alpha cleared: a JPEG holds no alpha, so a sample shows as it would over
# a white page. An opaque sample keeps its colour, (255 c + 127) / 255 = c.
def colour(+pp: U32) -> U32:
  +aa = U32.shrn(pp, 24n)
  +rr = colour.ch(U32.and(U32.shrn(pp, 16n), 255), aa)
  +gg = colour.ch(U32.and(U32.shrn(pp, 8n), 255), aa)
  +bb = colour.ch(U32.and(pp, 255), aa)
  U32.or(U32.or(U32.shln(rr, 16n), U32.shln(gg, 8n)), bb)

# every sample's colour flattened onto white
def colours(px: List<&2, U32>) -> List<&2, U32>:
  match px:
    case Nil{}:
      Nil{}
    case pp <> rest:
      colour(pp) <> colours(rest)

def encode_jpeg.pick(ok: Bool, +ww: U32, +hh: U32, +qq: U32, px: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case False{}:
      +_q = qq
      None{}
    case True{}:
      Some{Jenc.encode(ww, hh, qq, px)}

# a side a JPEG frame holds: 1 to 65535, the 16 bits T.81 B.2.2 gives X and Y
def encode_jpeg.side(+nn: U32) -> Bool:
  Bool.and(U32.is_gt(nn, 0), U32.is_le(nn, 65535))

# the rasters encode_jpeg writes: both sides from 1 to 65535, at most 2^31
# points, and exactly w * h samples, counted as natural numbers. For sides of
# at most 65535, w * h is below 2^32, so its U32 product is exact. These are
# encode_jpeg's own limits, not encode_png's: a JPEG frame cannot hold a side
# past 65535, and the decoder refuses a frame of more than 2^31 points.
def encode_jpeg.good(+ww: U32, +hh: U32, px: List<&2, U32>) -> Bool:
  Bool.and(Bool.and(encode_jpeg.side(ww), encode_jpeg.side(hh)), Bool.and(U32.is_le((ww * hh : U32), 2147483648),
    Nat.is_eq(List.length(&2, U32, px), Nat.mul(U32.to_nat(ww), U32.to_nat(hh)))))

# a baseline sequential 4:4:4 JPEG of the samples' colour at a quality of 1
# to 100 (IJG's scale: T.81 Annex K's tables K.1 and K.2 at 5000 / q percent
# below 50, else 200 - 2 q percent; a quality outside 1 to 100 is the nearest
# end), each sample flattened onto white before the encoder sees it
# (laws/JpegEncodeFlattensAlpha.bend). When every flattened sample has red,
# green and blue the same, it is one gray component with the luminance tables
# alone, as libjpeg writes a grayscale image. None exactly when
# encode_jpeg.good says the raster is not one it writes
# (laws/JpegEncodeRefusesBadRasters.bend).
#
# Trusted, not proved: for every raster r it writes, every colour channel of
# decode_jpeg(encode_jpeg_q(r, q)) is within E(q) of r's: E is 8 at quality
# 100, 32 at 95, 64 at 90 and 128 at 75; below 75 no bound short of 255 is
# claimed. Measured, not proved: the largest error over 400 rasters (random,
# gradients, saturated colours, checkerboards, stripes, gray, sizes 1 to 64)
# is 4 at 100, 24 at 95, 45 at 90, 114 at 75, 209 at 50 and 255 at 25 and
# below (saturated colour noise); libjpeg-turbo (Pillow) at the same quality
# and subsampling reaches 4, 21, 42, 113, 217 and 255. A proof needs error
# bounds on the fixed-point DCT and IDCT and on the quantisation.
def encode_jpeg_q(img: Raster, +qq: U32) -> Maybe<&2, List<&2, U32>>:
  match img:
    case Raster{+w, +h, +px}:
      encode_jpeg.pick(encode_jpeg.good(w, h, px), w, h, qq, colours(px))

# the quality encode_jpeg writes: 75, the IJG library's default (and Pillow's)
def encode_jpeg.quality() -> U32:
  75

# encode_jpeg_q at quality 75 (laws/JpegRoundTripKeepsSize.bend states its
# round trip for every quality, and this one through it)
#
# Trusted, not proved: every colour channel of decode_jpeg(encode_jpeg(r)) is
# within 128 of r's (encode_jpeg_q's bound at quality 75; measured worst 114,
# libjpeg-turbo's 113).
def encode_jpeg(img: Raster) -> Maybe<&2, List<&2, U32>>:
  encode_jpeg_q(img, encode_jpeg.quality())
