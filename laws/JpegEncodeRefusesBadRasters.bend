# `encode_jpeg(r)`, and `encode_jpeg_with(r, q, s)` at every quality and
# either subsampling (so `encode_jpeg_q(r, q)` too), is none
# exactly when `r` is a raster it cannot write: a side is 0 or past 65535
# (T.81 B.2.2 gives a frame's X and Y 16 bits), `r` has more than 2^31 points
# (the decoder refuses such a frame), or `r`'s sample count is not `w * h`.
# For sides of at most 65535, `w * h` is below 2^32, so its U32 product is
# exact.
import Base
import ../main.bend as Img

# a side a JPEG frame holds: 1 to 65535
def jpg.side(+nn: U32) -> Bool:
  Bool.and(U32.is_gt(nn, 0), U32.is_le(nn, 65535))

# a raster encode_jpeg can write: both sides frame sides, at most 2^31 points, and w * h samples
def jpg.writable(+ww: U32, +hh: U32, px: List<&2, U32>) -> Bool:
  Bool.and(Bool.and(jpg.side(ww), jpg.side(hh)), Bool.and(U32.is_le((ww * hh : U32), 2147483648),
    Nat.is_eq(List.length(&2, U32, px), Nat.mul(U32.to_nat(ww), U32.to_nat(hh)))))

# LAW: encode_jpeg_with, at every quality and either subsampling, refuses exactly the rasters it cannot write
law jpeg_refuse_exactly_q:
  for +ww: U32
  for +hh: U32
  for +qq: U32
  for +sub: Bool
  for +px: List<&2, U32>
  {Maybe.is_none(&2, List<&2, U32>, Img.encode_jpeg_with(Img.Raster{ww, hh, px}, qq, sub)) ==
    Bool.not(jpg.writable(ww, hh, px)) : Bool}

# LAW: encode_jpeg refuses exactly the rasters it cannot write
law jpeg_refuse_exactly:
  for +ww: U32
  for +hh: U32
  for +px: List<&2, U32>
  {Maybe.is_none(&2, List<&2, U32>, Img.encode_jpeg(Img.Raster{ww, hh, px})) == Bool.not(jpg.writable(ww, hh, px)) :
    Bool}
