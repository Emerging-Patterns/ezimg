# For every raster `r` of fewer than 2^32 samples, `encode_png(r)` is none
# exactly when a side of `r` is 0, `r` is not well formed, or `w * h` is 2^32
# or more.
import Base
import ../main.bend as Img
import ./defs/SizeBounds.bend as D1

# LAW: a raster with both sides above 0, w * h below 2^32 and w * h samples encodes
law png_encodes:
  for +ww: U32
  for +hh: U32
  for +px: List<&2, U32>
  for h_ok: {D1.png_ok(ww, hh, px) == True{} : Bool}
  {Maybe.is_some(&2, List<&2, U32>, Img.encode_png(Img.raster(ww, hh, px))) == True{} : Bool}

# LAW: for a raster of fewer than 2^32 samples, encode_png is none exactly when
# a side is 0, w * h is 2^32 or more, or the sample count is not w * h
law png_refuses:
  for +ww: U32
  for +hh: U32
  for +px: List<&2, U32>
  for h_len: {D1.below(32n, List.length(&2, U32, px)) == True{} : Bool}
  {Maybe.is_none(&2, List<&2, U32>, Img.encode_png(Img.raster(ww, hh, px))) == Bool.not(D1.png_ok(ww, hh, px)) : Bool}
