# When `encode_png(r)` is some, its IHDR has bit depth 8 and interlace 0, and
# colour type 2 exactly when every sample of `r` has alpha 255, colour type 6
# otherwise.
import Base
import ../main.bend as Img
import ./defs/PngSpecification.bend as D1

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
law png_ihdr:
  for +ww: U32
  for +hh: U32
  for +px: List<&2, U32>
  for h_some: {Maybe.is_some(&2, List<&2, U32>, Img.encode_png(Img.raster(ww, hh, px))) == True{} : Bool}
  exs rest: List<&2, U32>
  {Img.encode_png(Img.raster(ww, hh, px)) ==
    Some{List.append(&2, U32, ihdr_head(ww, hh, colour_type(D1.all_opaque(px))), rest)} : Maybe<&2, List<&2, U32>>}
