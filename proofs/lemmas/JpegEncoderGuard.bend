# what encode_jpeg's own guard (encode_jpeg.good in main.bend) gives the proofs: each side from 1 to 65535, at
# most 2^31 points, and the JPEG encoder's own size test passed
import Base
import ../../main.bend as Img
import ../../src/jpeg_enc.bend as Jenc
import ./BasicFacts.bend as M1

# the sides of a raster the guard passes
def sides(
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  hg: {Img.encode_jpeg.good(ww, hh, px) == True{} : Bool}
) -> {Bool.and(Img.encode_jpeg.side(ww), Img.encode_jpeg.side(hh)) == True{} : Bool}:
  M1.and_left(Bool.and(Img.encode_jpeg.side(ww), Img.encode_jpeg.side(hh)), Bool.and(U32.is_le((ww * hh : U32),
    2147483648), Nat.is_eq(List.length(&2, U32, px), Nat.mul(U32.to_nat(ww), U32.to_nat(hh)))), hg)

# the width of a raster the guard passes is above 0
def w_pos(
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  hg: {Img.encode_jpeg.good(ww, hh, px) == True{} : Bool}
) -> {U32.is_gt(ww, 0) == True{} : Bool}:
  M1.and_left(U32.is_gt(ww, 0), U32.is_le(ww, 65535), M1.and_left(Img.encode_jpeg.side(ww), Img.encode_jpeg.side(hh),
    sides(ww, hh, px, hg)))

# the height of a raster the guard passes is above 0
def h_pos(
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  hg: {Img.encode_jpeg.good(ww, hh, px) == True{} : Bool}
) -> {U32.is_gt(hh, 0) == True{} : Bool}:
  M1.and_left(U32.is_gt(hh, 0), U32.is_le(hh, 65535), M1.and_right(Img.encode_jpeg.side(ww), Img.encode_jpeg.side(hh),
    sides(ww, hh, px, hg)))

# the width of a raster the guard passes is at most 65535
def w_le(
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  hg: {Img.encode_jpeg.good(ww, hh, px) == True{} : Bool}
) -> {U32.is_le(ww, 65535) == True{} : Bool}:
  M1.and_right(U32.is_gt(ww, 0), U32.is_le(ww, 65535), M1.and_left(Img.encode_jpeg.side(ww), Img.encode_jpeg.side(hh),
    sides(ww, hh, px, hg)))

# the height of a raster the guard passes is at most 65535
def h_le(
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  hg: {Img.encode_jpeg.good(ww, hh, px) == True{} : Bool}
) -> {U32.is_le(hh, 65535) == True{} : Bool}:
  M1.and_right(U32.is_gt(hh, 0), U32.is_le(hh, 65535), M1.and_right(Img.encode_jpeg.side(ww),
    Img.encode_jpeg.side(hh), sides(ww, hh, px, hg)))

# a raster the guard passes has at most 2^31 points
def area(
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  hg: {Img.encode_jpeg.good(ww, hh, px) == True{} : Bool}
) -> {U32.is_le((ww * hh : U32), 2147483648) == True{} : Bool}:
  M1.and_left(U32.is_le((ww * hh : U32), 2147483648), Nat.is_eq(List.length(&2, U32, px), Nat.mul(U32.to_nat(ww),
    U32.to_nat(hh))), M1.and_right(Bool.and(Img.encode_jpeg.side(ww), Img.encode_jpeg.side(hh)),
    Bool.and(U32.is_le((ww * hh : U32), 2147483648), Nat.is_eq(List.length(&2, U32, px), Nat.mul(U32.to_nat(ww),
    U32.to_nat(hh)))), hg))

# a raster the guard passes passes the JPEG encoder's own size test
def bad(
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  +hg: {Img.encode_jpeg.good(ww, hh, px) == True{} : Bool}
) -> {Jenc.encode.bad(ww, hh) == False{} : Bool}:
  M1.bad_no(U32.is_eq(ww, 0), U32.is_eq(hh, 0), U32.is_gt(ww, 65535), U32.is_gt(hh, 65535),
    M1.gt_ne(U32.cmp(ww, 0), w_pos(ww, hh, px, hg)), M1.gt_ne(U32.cmp(hh, 0), h_pos(ww, hh, px, hg)),
    M1.le_ngt(U32.cmp(ww, 65535), w_le(ww, hh, px, hg)), M1.le_ngt(U32.cmp(hh, 65535), h_le(ww, hh, px, hg)))
