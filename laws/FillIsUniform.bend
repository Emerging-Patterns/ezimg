# `fill(w, h, c)` is well formed and every sample is `c`, for every `w`, `h`
# with `w * h < 2^32` and every `c`.
import Base
import ../main.bend as Img
import ./defs/WellFormed.bend as D1

# The laws below take w * h < 2^32 as a U32 `area` whose value is w * h: a
# Nat is below 2^32 exactly when it is some U32's value. (A closed 2^32 in a
# law would be expanded in unary by the checker.)

# LAW: fill(w, h, c) is well formed, for every w and h with w * h < 2^32 and every c
law fill_wf:
  for +ww: U32
  for +hh: U32
  for +color: U32
  for +area: U32
  for h_area: {U32.to_nat(area) == Nat.mul(U32.to_nat(ww), U32.to_nat(hh)) : Nat}
  {D1.wf(Img.fill(ww, hh, color)) == True{} : Bool}

# LAW: every sample of fill(w, h, c) is c, for every w, h and c
law fill_every:
  for +ww: U32
  for +hh: U32
  for +color: U32
  for kk: Nat
  for +vv: U32
  for h_at: {List.get(&2, U32, Img.pixels(Img.fill(ww, hh, color)), kk) == Some{vv} : Maybe<&2, U32>}
  {vv == color : U32}
