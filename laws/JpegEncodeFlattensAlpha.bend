# `encode_jpeg` and `encode_jpeg_q` write each sample flattened onto white: a
# JPEG holds no alpha, so a sample of alpha a is a / 255 of its colour over
# (255 - a) / 255 of white, rounded, as a viewer shows it over a white page.
# Two rasters of one size whose samples flatten alike encode to the same bytes,
# at every quality. An opaque sample
# (alpha 255) flattens to its own colour: (255 c + 127) / 255 = c for every c
# from 0 to 255, computed outside the gate, so an opaque raster encodes as its
# colours, as it did before encode_jpeg flattened.
import Base
import ../main.bend as Img

# one channel flattened onto white: the specification's own copy
def flat.ch(+cc: U32, +aa: U32) -> U32:
  U32.div((cc * aa + (255 - aa) * 255 + 127 : U32), 255)

# a sample flattened onto white, alpha cleared
def flat.px(+pp: U32) -> U32:
  +aa = U32.shrn(pp, 24n)
  +rr = flat.ch(U32.and(U32.shrn(pp, 16n), 255), aa)
  +gg = flat.ch(U32.and(U32.shrn(pp, 8n), 255), aa)
  +bb = flat.ch(U32.and(pp, 255), aa)
  U32.or(U32.or(U32.shln(rr, 16n), U32.shln(gg, 8n)), bb)

# every sample flattened onto white
def flat(px: List<&2, U32>) -> List<&2, U32>:
  match px:
    case Nil{}:
      Nil{}
    case pp <> rest:
      flat.px(pp) <> flat(rest)

# LAW: two rasters of one size whose samples flatten onto white alike encode to the same JPEG bytes at any quality
law jpeg_flatten_alike_q:
  for +ww: U32
  for +hh: U32
  for +qq: U32
  for +pa: List<&2, U32>
  for +pb: List<&2, U32>
  for +same: {flat(pa) == flat(pb) : List<&2, U32>}
  {Img.encode_jpeg_q(Img.raster(ww, hh, pa), qq) == Img.encode_jpeg_q(Img.raster(ww, hh, pb), qq) :
    Maybe<&2, List<&2, U32>>}

# LAW: two rasters of one size whose samples flatten onto white alike encode to the same JPEG bytes
law jpeg_flatten_alike:
  for +ww: U32
  for +hh: U32
  for +pa: List<&2, U32>
  for +pb: List<&2, U32>
  for +same: {flat(pa) == flat(pb) : List<&2, U32>}
  {Img.encode_jpeg(Img.raster(ww, hh, pa)) == Img.encode_jpeg(Img.raster(ww, hh, pb)) : Maybe<&2, List<&2, U32>>}
