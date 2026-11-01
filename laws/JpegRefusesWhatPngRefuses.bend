# `encode_jpeg(r)` is none exactly when `encode_png(r)` is none.
import Base
import ../main.bend as Img

# LAW: encode_jpeg refuses exactly the rasters encode_png refuses
law jpeg_png_refuse_alike:
  for +img: Img.Raster
  {Maybe.is_none(&2, List<&2, U32>, Img.encode_jpeg(img)) ==
    Maybe.is_none(&2, List<&2, U32>, Img.encode_png(img)) : Bool}
