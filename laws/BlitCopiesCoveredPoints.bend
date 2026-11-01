# For every well-formed `dst` with `w * h < 2^32`, well-formed `src` and
# offset `(x, y)`, `blit(dst, src, x, y)` has `dst`'s size, takes `src`'s
# sample at every point of `dst` that `src` covers, and leaves every other
# sample of `dst` unchanged.
import Base
import ../main.bend as Img
import ./defs/BlitCover.bend as D1
import ./defs/WellFormed.bend as D2

# LAW: blit(dst, src, x, y) has dst's width and height, for every dst, src and offset
law blit_size:
  for +dst: Img.Raster
  for +src: Img.Raster
  for +xx: U32
  for +yy: U32
  {Img.size(Img.blit(dst, src, xx, yy)) == Img.size(dst) : U32 & U32}

# LAW: blit of a well-formed src onto a well-formed dst is well formed, when dst's w * h < 2^32
law blit_wf:
  for +dst: Img.Raster
  for +src: Img.Raster
  for +xx: U32
  for +yy: U32
  for +area: U32
  for h_area: {U32.to_nat(area) == Nat.mul(U32.to_nat(Img.width(dst)), U32.to_nat(Img.height(dst))) : Nat}
  for h_dst: {D2.wf(dst) == True{} : Bool}
  for h_src: {D2.wf(src) == True{} : Bool}
  {D2.wf(Img.blit(dst, src, xx, yy)) == True{} : Bool}

# LAW: at every point (i, j) of dst that src covers, blit takes src's sample at (i - x, j - y), for well-formed
# dst and src, when dst's w * h < 2^32
law blit_in:
  for +dst: Img.Raster
  for +src: Img.Raster
  for +xx: U32
  for +yy: U32
  for +area: U32
  for h_area: {U32.to_nat(area) == Nat.mul(U32.to_nat(Img.width(dst)), U32.to_nat(Img.height(dst))) : Nat}
  for h_dst: {D2.wf(dst) == True{} : Bool}
  for h_src: {D2.wf(src) == True{} : Bool}
  for +ii: Nat
  for +jj: Nat
  for +hi: {Nat.is_lt(ii, U32.to_nat(Img.width(dst))) == True{} : Bool}
  for +hj: {Nat.is_lt(jj, U32.to_nat(Img.height(dst))) == True{} : Bool}
  for +h_cov: {D1.covers(xx, yy, src, ii, jj) == True{} : Bool}
  {List.get(&2, U32, Img.pixels(Img.blit(dst, src, xx, yy)), Nat.add(Nat.mul(jj, U32.to_nat(Img.width(dst))), ii)) ==
    List.get(&2, U32, Img.pixels(src),
      Nat.add(Nat.mul(Nat.sub(jj, U32.to_nat(yy)), U32.to_nat(Img.width(src))), Nat.sub(ii, U32.to_nat(xx)))) :
    Maybe<&2, U32>}

# LAW: at every point (i, j) of dst that src does not cover, blit keeps dst's sample, for well-formed dst and src,
# when dst's w * h < 2^32
law blit_out:
  for +dst: Img.Raster
  for +src: Img.Raster
  for +xx: U32
  for +yy: U32
  for +area: U32
  for h_area: {U32.to_nat(area) == Nat.mul(U32.to_nat(Img.width(dst)), U32.to_nat(Img.height(dst))) : Nat}
  for h_dst: {D2.wf(dst) == True{} : Bool}
  for h_src: {D2.wf(src) == True{} : Bool}
  for +ii: Nat
  for +jj: Nat
  for +hi: {Nat.is_lt(ii, U32.to_nat(Img.width(dst))) == True{} : Bool}
  for +hj: {Nat.is_lt(jj, U32.to_nat(Img.height(dst))) == True{} : Bool}
  for +h_cov: {D1.covers(xx, yy, src, ii, jj) == False{} : Bool}
  {List.get(&2, U32, Img.pixels(Img.blit(dst, src, xx, yy)), Nat.add(Nat.mul(jj, U32.to_nat(Img.width(dst))), ii)) ==
    List.get(&2, U32, Img.pixels(dst), Nat.add(Nat.mul(jj, U32.to_nat(Img.width(dst))), ii)) : Maybe<&2, U32>}
