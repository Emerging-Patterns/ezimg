# `fill(w, h, c)` is a well-formed `w` by `h` raster and every sample is `c`,
# for every `w`, `h` and `c`: its samples are built a row at a time, so the
# count `w * h` never wraps.
import Base
import ../main.bend as Img
import ./defs/WellFormed.bend as D1

# LAW: fill(w, h, c) is well formed, for every w, h and c
law fill_wf:
  for +ww: U32
  for +hh: U32
  for +color: U32
  {D1.wf(Img.fill(ww, hh, color)) == True{} : Bool}

# LAW: fill(w, h, c) is w wide and h high, for every w, h and c
law fill_size:
  for +ww: U32
  for +hh: U32
  for +color: U32
  {Img.size(Img.fill(ww, hh, color)) == (ww, hh) : U32 & U32}

# LAW: every sample of fill(w, h, c) is c, for every w, h and c
law fill_every:
  for +ww: U32
  for +hh: U32
  for +color: U32
  for kk: Nat
  for +vv: U32
  for h_at: {List.get(&2, U32, Img.pixels(Img.fill(ww, hh, color)), kk) == Some{vv} : Maybe<&2, U32>}
  {vv == color : U32}
