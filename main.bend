# ezimg: images for Bend 2, with PNG and baseline JPEG decode and encode
#
# A Raster is a width, a height, and row-major samples. PNG decode reads 8-bit
# images. PNG encode writes colour type 2 or 6. JPEG decode reads a baseline
# sequential frame, and encode_jpeg writes one.
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

# a picture from its width, height, and samples
def raster(ww: U32, hh: U32, pixels: List<&2, U32>) -> Raster:
  Raster{ww, hh, pixels}

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

# width times height
def count(img: Raster) -> U32:
  match img:
    case Raster{+w, +h, _px}:
      (w * h : U32)

# a solid picture of one sample
def fill(+ww: U32, +hh: U32, +color: U32) -> Raster:
  Raster{ww, hh, List.replicate(U32, U32.to_nat((ww * hh : U32)), color)}

def u.min.pick(le: Bool, +aa: U32, +bb: U32) -> U32:
  match le:
    case True{}:
      aa
    case False{}:
      bb

def u.min(+aa: U32, +bb: U32) -> U32:
  u.min.pick(U32.is_le(aa, bb), aa, bb)

def get.y(yin: Bool, px: List<&2, U32>, +ww: U32, +xx: U32, +yy: U32) -> Maybe<&2, U32>:
  match yin:
    case False{}:
      None{}
    case True{}:
      List.get(&2, U32, px, U32.to_nat((yy * ww + xx : U32)))

def get.x(xin: Bool, px: List<&2, U32>, +ww: U32, +hh: U32, +xx: U32, +yy: U32) -> Maybe<&2, U32>:
  match xin:
    case False{}:
      None{}
    case True{}:
      get.y(U32.is_lt(yy, hh), px, ww, xx, yy)

# the sample at (x, y), or none when that point is outside the picture
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
      Raster{ww, hh, List.set(&2, U32, px, U32.to_nat((yy * ww + xx : U32)), color)}

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

# the picture with (x, y) replaced by color; outside, the picture is unchanged
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
        crop.rows(U32.to_nat(rh), List.drop(&2, U32, px, U32.to_nat((yy * ww + xx : U32))),
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
  +top = U32.to_nat((oy * dw : U32))
  +span = U32.to_nat(((oy + rows) * dw : U32))
  List.append(&2, U32, List.take(&2, U32, dp, top), List.append(&2, U32,
    blit.rows(U32.to_nat(rows), List.drop(&2, U32, dp, top), sp, U32.to_nat(left),
      U32.to_nat(cover), U32.to_nat(tail), U32.to_nat(dw), U32.to_nat(sw)),
    List.drop(&2, U32, dp, span)))

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

# the PNG signature when the bytes open with it, otherwise none
def parse_signature(bytes: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match bytes:
    case 137 <> 80 <> 78 <> 71 <> 13 <> 10 <> 26 <> 10 <> _rest:
      Some{png_sig()}
    case _other:
      None{}

def decode_png.pic(mm: Maybe<&2, Png.Pic>) -> Maybe<&2, Raster>:
  match mm:
    case None{}:
      None{}
    case Some{Png.Pic{+w, +h, px}}:
      Some{Raster{w, h, px}}

def decode_png.of(mm: Maybe<&2, List<&2, U32>>, +bytes: List<&2, U32>) -> Maybe<&2, Raster>:
  match mm bytes:
    case None{} _bytes:
      None{}
    case Some{_sig} 137 <> 80 <> 78 <> 71 <> 13 <> 10 <> 26 <> 10 <> rest:
      decode_png.pic(Png.decode(rest))
    case Some{_sig} _other:
      None{}

# PNG bytes, or none when the signature or the encoding is rejected
def decode_png(+bytes: List<&2, U32>) -> Maybe<&2, Raster>:
  decode_png.of(parse_signature(bytes), bytes)

# ISO/IEC 15948 / W3C PNG — bytes of an 8-bit picture, interlace method 0.
# Colour type 2 when every sample is opaque, otherwise colour type 6.
# None when a side is zero or the sample count is not the area.
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

def encode_jpeg.pick(ok: Bool, +ww: U32, +hh: U32, px: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case False{}:
      None{}
    case True{}:
      Some{Jenc.encode(ww, hh, px)}

# a baseline sequential 4:4:4 JPEG of the samples' colour, alpha dropped. None
# exactly when encode_png is none: a side is zero, the area passes 2^32, or the
# sample count is not the area. Both ask the same guard, Png.enc.good.
def encode_jpeg(img: Raster) -> Maybe<&2, List<&2, U32>>:
  match img:
    case Raster{+w, +h, +px}:
      encode_jpeg.pick(Png.enc.good(w, h, px), w, h, px)
