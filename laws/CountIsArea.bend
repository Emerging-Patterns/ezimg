# `count(r)` is the number of `r`'s samples, a natural number, so it never
# wraps: for every well-formed raster `r`, whatever its sides, it is `w * h`.
import Base
import ../main.bend as Img
import ./defs/WellFormed.bend as D1

# LAW: count(r) is the number of r's samples, for every raster
law count_samples:
  for +img: Img.Raster
  {Img.count(img) == List.length(&2, U32, Img.pixels(img)) : Nat}

# LAW: count(r) is w * h, as natural numbers, for every well-formed raster
law count_area:
  for +img: Img.Raster
  for h_wf: {D1.wf(img) == True{} : Bool}
  {Img.count(img) == Nat.mul(U32.to_nat(Img.width(img)), U32.to_nat(Img.height(img))) : Nat}
