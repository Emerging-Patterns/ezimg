# Every sample `decode_png` and `decode_jpeg` return is packed `0xAARRGGBB`.
# Every JPEG sample has alpha 255, and a gray JPEG sample carries its Y value
# in R, G and B.
#
# also rests on: laws/PngAncillaryChunksIgnored.bend
import Base
import ../main.bend as Img
import ../src/jpeg.bend as Jpeg
import ./defs/PngSpecification.bend as D1

# LAW: every sample Jpeg.rgb packs is opaque, for every Y, Cb and Cr
law jpeg_rgb_opaque:
  for +yy: U32
  for +cb: U32
  for +cr: U32
  {U32.shrn(Jpeg.rgb(yy, cb, cr), 24n) == 255 : U32}

# LAW: every sample Jpeg.gray packs is opaque, for every level
law jpeg_gray_opaque:
  for +yy: U32
  {U32.shrn(Jpeg.gray(yy), 24n) == 255 : U32}

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
law jpeg_decode_packed:
  for +bytes: List<&2, U32>
  for +img: Img.Raster
  for h_dec: {Img.decode_jpeg(bytes) == Some{img} : Maybe<&2, Img.Raster>}
  exs gray: Bool
  exs ys: List<&2, U32>
  exs bs: List<&2, U32>
  exs rs: List<&2, U32>
  {Img.pixels(img) == jpeg.pack(gray, ys, bs, rs) : List<&2, U32>}

# LAW: every sample decode_jpeg returns has alpha 255
law jpeg_decode_opaque:
  for +bytes: List<&2, U32>
  for +img: Img.Raster
  for h_dec: {Img.decode_jpeg(bytes) == Some{img} : Maybe<&2, Img.Raster>}
  {D1.all.opaque(Img.pixels(img), True{}) == True{} : Bool}
