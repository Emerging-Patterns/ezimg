# ezimg: images for Bend 2. A Raster is a width, a height, and row-major
# samples. PNG decode reads 8-bit images; JPEG decode returns none.
import Base
import ./png.bend as Png

# a picture: width, height, and opaque U32 samples in row-major order
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
def raster(w: U32, h: U32, pixels: List<&2, U32>) -> Raster:
  Raster{w, h, pixels}

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
def fill(+w: U32, +h: U32, +color: U32) -> Raster:
  Raster{w, h, List.replicate(U32, U32.to_nat((w * h : U32)), color)}

def u.min.pick(le: Bool, +a: U32, +b: U32) -> U32:
  match le:
    case True{}:
      a
    case False{}:
      b

def u.min(+a: U32, +b: U32) -> U32:
  u.min.pick(U32.is_le(a, b), a, b)

def get.y(yin: Bool, px: List<&2, U32>, +w: U32, +x: U32, +y: U32) -> Maybe<&2, U32>:
  match yin:
    case False{}:
      None{}
    case True{}:
      List.get(&2, U32, px, U32.to_nat((y * w + x : U32)))

def get.x(xin: Bool, px: List<&2, U32>, +w: U32, +h: U32, +x: U32, +y: U32) -> Maybe<&2, U32>:
  match xin:
    case False{}:
      None{}
    case True{}:
      get.y(U32.is_lt(y, h), px, w, x, y)

# the sample at (x, y), or none when that point is outside the picture
def get(img: Raster, +x: U32, +y: U32) -> Maybe<&2, U32>:
  match img:
    case Raster{+w, +h, +px}:
      get.x(U32.is_lt(x, w), px, w, h, x, y)

def set.y(
  yin: Bool, +w: U32, +h: U32, px: List<&2, U32>, +x: U32, +y: U32, +color: U32
) -> Raster:
  match yin:
    case False{}:
      Raster{w, h, px}
    case True{}:
      Raster{w, h, List.set(&2, U32, px, U32.to_nat((y * w + x : U32)), color)}

def set.x(
  xin: Bool, +w: U32, +h: U32, px: List<&2, U32>, +x: U32, +y: U32, +color: U32
) -> Raster:
  match xin:
    case False{}:
      Raster{w, h, px}
    case True{}:
      set.y(U32.is_lt(y, h), w, h, px, x, y, color)

# the picture with (x, y) replaced by color; outside, the picture is unchanged
def set(img: Raster, +x: U32, +y: U32, +color: U32) -> Raster:
  match img:
    case Raster{+w, +h, +px}:
      set.x(U32.is_lt(x, w), w, h, px, x, y, color)

def crop.rows(+n: Nat, +px: List<&2, U32>, +rw: Nat, +gap: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      List.append(&2, U32, List.take(&2, U32, px, rw),
        crop.rows(p, List.drop(&2, U32, px, Nat.add(rw, gap)), rw, gap))

def crop.use(
  zh: Bool, +px: List<&2, U32>, +w: U32, +x: U32, +y: U32, +rw: U32, +rh: U32
) -> Raster:
  match zh:
    case True{}:
      Raster{0, 0, []}
    case False{}:
      Raster{rw, rh,
        crop.rows(U32.to_nat(rh), List.drop(&2, U32, px, U32.to_nat((y * w + x : U32))),
          U32.to_nat(rw), U32.to_nat((w - rw : U32)))}

def crop.open(
  zw: Bool, zh: Bool, +px: List<&2, U32>, +w: U32, +x: U32, +y: U32, +rw: U32, +rh: U32
) -> Raster:
  match zw:
    case True{}:
      Raster{0, 0, []}
    case False{}:
      crop.use(zh, px, w, x, y, rw, rh)

def crop.box(
  +px: List<&2, U32>, +w: U32, +h: U32, +x: U32, +y: U32, +cw: U32, +ch: U32
) -> Raster:
  +rw = u.min(cw, (w - x : U32))
  +rh = u.min(ch, (h - y : U32))
  crop.open(U32.is_zero(rw), U32.is_zero(rh), px, w, x, y, rw, rh)

def crop.y(
  yin: Bool, +px: List<&2, U32>, +w: U32, +h: U32, +x: U32, +y: U32, +cw: U32, +ch: U32
) -> Raster:
  match yin:
    case False{}:
      Raster{0, 0, []}
    case True{}:
      crop.box(px, w, h, x, y, cw, ch)

def crop.x(
  xin: Bool, +px: List<&2, U32>, +w: U32, +h: U32, +x: U32, +y: U32, +cw: U32, +ch: U32
) -> Raster:
  match xin:
    case False{}:
      Raster{0, 0, []}
    case True{}:
      crop.y(U32.is_lt(y, h), px, w, h, x, y, cw, ch)

# the intersection of rectangle (x, y, cw, ch) with the picture.
# A miss, or a zero side, is an empty picture.
def crop(img: Raster, +x: U32, +y: U32, +cw: U32, +ch: U32) -> Raster:
  match img:
    case Raster{+w, +h, +px}:
      crop.x(U32.is_lt(x, w), px, w, h, x, y, cw, ch)

def blit.row(
  +dp: List<&2, U32>, +sp: List<&2, U32>, +left: Nat, +cover: Nat, +tail: Nat
) -> List<&2, U32>:
  List.append(&2, U32, List.take(&2, U32, dp, left), List.append(&2, U32,
    List.take(&2, U32, sp, cover),
    List.take(&2, U32, List.drop(&2, U32, dp, Nat.add(left, cover)), tail)))

def blit.rows(
  +n: Nat, +dp: List<&2, U32>, +sp: List<&2, U32>, +left: Nat, +cover: Nat, +tail: Nat,
  +dw: Nat, +sw: Nat
) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      List.append(&2, U32, blit.row(dp, sp, left, cover, tail), blit.rows(p,
        List.drop(&2, U32, dp, dw), List.drop(&2, U32, sp, sw), left, cover, tail, dw, sw))

def blit.join(
  +dp: List<&2, U32>, +sp: List<&2, U32>, +dw: U32, +dh: U32, +sw: U32, +sh: U32,
  +ox: U32, +oy: U32
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
  inside: Bool, +dp: List<&2, U32>, +sp: List<&2, U32>, +dw: U32, +dh: U32, +sw: U32,
  +sh: U32, +ox: U32, +oy: U32
) -> List<&2, U32>:
  match inside:
    case False{}:
      dp
    case True{}:
      blit.join(dp, sp, dw, dh, sw, sh, ox, oy)

def blit.src(src: Raster, +dw: U32, +dh: U32, dp: List<&2, U32>, +x: U32, +y: U32) -> Raster:
  match src:
    case Raster{+sw, +sh, +sp}:
      Raster{dw, dh, blit.y(U32.is_lt(y, dh), dp, sp, dw, dh, sw, sh, x, y)}

# src pasted onto dst at (x, y). dst keeps its size; samples past its edge are
# dropped, and an overlapping sample takes the source.
def blit(dst: Raster, src: Raster, +x: U32, +y: U32) -> Raster:
  match dst:
    case Raster{+dw, +dh, +dp}:
      blit.src(src, dw, dh, dp, x, y)

def map.go(~f: U32 -> U32, px: List<&2, U32>) -> List<&2, U32>:
  match px:
    case Nil{}:
      Nil{}
    case h <> t:
      f(h) <> map.go(~f, t)

# every sample passed through f; the width and the height stay
def map(~f: U32 -> U32, img: Raster) -> Raster:
  match img:
    case Raster{+w, +h, +px}:
      Raster{w, h, map.go(~f, px)}

# an opaque U32 sample has no alpha to scale, so this is the picture
def premultiply(img: Raster) -> Raster:
  img

# an opaque U32 sample has no alpha to divide back out, so this is the picture
def straight(img: Raster) -> Raster:
  img

# the PNG signature when the bytes open with it, otherwise none
def parse_signature(bytes: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match bytes:
    case 137 <> 80 <> 78 <> 71 <> 13 <> 10 <> 26 <> 10 <> _rest:
      Some{png_sig()}
    case _other:
      None{}

def decode_png.pic(m: Maybe<&2, Png.Pic>) -> Maybe<&2, Raster>:
  match m:
    case None{}:
      None{}
    case Some{Png.Pic{+w, +h, px}}:
      Some{Raster{w, h, px}}

def decode_png.of(m: Maybe<&2, List<&2, U32>>, +bytes: List<&2, U32>) -> Maybe<&2, Raster>:
  match m bytes:
    case None{} _bytes:
      None{}
    case Some{_sig} 137 <> 80 <> 78 <> 71 <> 13 <> 10 <> 26 <> 10 <> rest:
      decode_png.pic(Png.decode(rest))
    case Some{_sig} _other:
      None{}

# PNG bytes, or none when the signature or the encoding is rejected
def decode_png(+bytes: List<&2, U32>) -> Maybe<&2, Raster>:
  decode_png.of(parse_signature(bytes), bytes)

# JPEG bytes, or none: the codec is not here yet
def decode_jpeg(bytes: List<&2, U32>) -> Maybe<&2, Raster>:
  +_n = List.length(&2, U32, bytes)
  None{}
