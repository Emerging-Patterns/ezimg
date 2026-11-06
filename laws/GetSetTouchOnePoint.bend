# For every raster `r` and every `x`, `y`: `get(r, x, y)` is sample
# `y * w + x` when `x < w` and `y < h` (some when `r` is well formed), and
# none otherwise; `set(r, x, y, c)` changes exactly that sample to `c` when
# the point is inside and returns `r` unchanged otherwise. The index is a
# natural number, so it never wraps, whatever the sides.
import Base
import ../main.bend as Img
import ./defs/PointInside.bend as D1
import ./defs/WellFormed.bend as D2

# where (x, y) sits in the samples of a raster of width w: y * w + x, as a Nat
def spot(ww: U32, xx: U32, yy: U32) -> Nat:
  Nat.add(Nat.mul(U32.to_nat(yy), U32.to_nat(ww)), U32.to_nat(xx))

# LAW: inside the raster, get(r, x, y) is sample y * w + x, for every raster
law get_inside:
  for +img: Img.Raster
  for +xx: U32
  for +yy: U32
  for +h_in: {D1.inside(img, xx, yy) == True{} : Bool}
  {Img.get(img, xx, yy) == List.get(&2, U32, Img.pixels(img), spot(Img.width(img), xx, yy)) : Maybe<&2, U32>}

# LAW: inside a well-formed raster, get(r, x, y) is some
law get_inside_some:
  for +img: Img.Raster
  for +xx: U32
  for +yy: U32
  for h_wf: {D2.wf(img) == True{} : Bool}
  for +h_in: {D1.inside(img, xx, yy) == True{} : Bool}
  {Maybe.is_some(&2, U32, Img.get(img, xx, yy)) == True{} : Bool}

# LAW: outside the raster, get(r, x, y) is none, for every raster
law get_outside:
  for +img: Img.Raster
  for +xx: U32
  for +yy: U32
  for h_out: {D1.inside(img, xx, yy) == False{} : Bool}
  {Img.get(img, xx, yy) == None{} : Maybe<&2, U32>}

# LAW: inside the raster, set(r, x, y, c) replaces sample y * w + x with c and
# nothing else, for every raster
law set_inside:
  for +img: Img.Raster
  for +xx: U32
  for +yy: U32
  for +color: U32
  for +h_in: {D1.inside(img, xx, yy) == True{} : Bool}
  {Img.set(img, xx, yy, color) == Img.raster(Img.width(img), Img.height(img),
    List.set(&2, U32, Img.pixels(img), spot(Img.width(img), xx, yy), color)) : Img.Raster}

# LAW: outside the raster, set(r, x, y, c) is r, for every raster
law set_outside:
  for +img: Img.Raster
  for +xx: U32
  for +yy: U32
  for +color: U32
  for h_out: {D1.inside(img, xx, yy) == False{} : Bool}
  {Img.set(img, xx, yy, color) == img : Img.Raster}
