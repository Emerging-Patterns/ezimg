# For every rectangle `(x, y, cw, ch)`, `crop`'s size is the rectangle's
# intersection with `r` (0 by 0 when that is empty), and for every
# well-formed `r`, whatever its sides, `crop` is well formed and its sample
# at `(i, j)` is `r`'s sample at `(x + i, y + j)`.
import Base
import ../main.bend as Img
import ./defs/CropSpan.bend as D1
import ./defs/SizeBounds.bend as D2
import ./defs/WellFormed.bend as D3

# LAW: crop's width and height are those of the rectangle's intersection with the raster, 0 by 0 when that is
# empty, for every raster
law crop_size:
  for +img: Img.Raster
  for +xx: U32
  for +yy: U32
  for +cw: U32
  for +ch: U32
  {(U32.to_nat(Img.width(Img.crop(img, xx, yy, cw, ch))), U32.to_nat(Img.height(Img.crop(img, xx, yy, cw, ch)))) ==
    (D2.side(D1.cut(Img.width(img), xx, cw), D1.cut(Img.height(img), yy, ch)),
      D2.side(D1.cut(Img.height(img), yy, ch), D1.cut(Img.width(img), xx, cw))) : Nat & Nat}

# LAW: crop of a well-formed raster is well formed
law crop_wf:
  for +img: Img.Raster
  for +xx: U32
  for +yy: U32
  for +cw: U32
  for +ch: U32
  for h_wf: {D3.wf(img) == True{} : Bool}
  {D3.wf(Img.crop(img, xx, yy, cw, ch)) == True{} : Bool}

# LAW: the crop's sample at (i, j) is the raster's sample at (x + i, y + j), for every point (i, j) of the crop of
# a well-formed raster
law crop_at:
  for +img: Img.Raster
  for +xx: U32
  for +yy: U32
  for +cw: U32
  for +ch: U32
  for h_wf: {D3.wf(img) == True{} : Bool}
  for +ii: Nat
  for +jj: Nat
  for hi: {Nat.is_lt(ii, U32.to_nat(Img.width(Img.crop(img, xx, yy, cw, ch)))) == True{} : Bool}
  for hj: {Nat.is_lt(jj, U32.to_nat(Img.height(Img.crop(img, xx, yy, cw, ch)))) == True{} : Bool}
  {List.get(&2, U32, Img.pixels(Img.crop(img, xx, yy, cw, ch)),
    Nat.add(Nat.mul(jj, U32.to_nat(Img.width(Img.crop(img, xx, yy, cw, ch)))), ii)) ==
    List.get(&2, U32, Img.pixels(img),
      Nat.add(Nat.mul(Nat.add(U32.to_nat(yy), jj), U32.to_nat(Img.width(img))), Nat.add(U32.to_nat(xx), ii))) :
    Maybe<&2, U32>}
