# ezimg: images for Bend 2. A Raster is a width, a height, and row-major
# samples. PNG and JPEG decode return none until the codecs land.
import Base

# a picture: width, height, and samples in row-major order
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

# the PNG signature when the bytes open with it, otherwise none
def parse_signature(bytes: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match bytes:
    case 137 <> 80 <> 78 <> 71 <> 13 <> 10 <> 26 <> 10 <> _rest:
      Some{png_sig()}
    case _other:
      None{}

# PNG bytes, or none: the codec is not here yet
def decode_png(bytes: List<&2, U32>) -> Maybe<&2, Raster>:
  +_n = List.length(&2, U32, bytes)
  None{}

# JPEG bytes, or none: the codec is not here yet
def decode_jpeg(bytes: List<&2, U32>) -> Maybe<&2, Raster>:
  +_n = List.length(&2, U32, bytes)
  None{}
