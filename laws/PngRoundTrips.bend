# For every raster `r` that `encode_png` accepts (well formed, both sides
# nonzero, fewer than 2^28 samples: laws/PngRefusesBadRasters.bend),
# `decode_png(encode_png(r))` is `Some(r)`.
import Base
import ../main.bend as Img
import ./defs/PngSpecification.bend as D1
import ./defs/SizeBounds.bend as D2

# the channels encode_png writes for each sample: red, green and blue when
# every sample is opaque, and alpha too otherwise
def spec.nch(op: Bool) -> Nat:
  match op:
    case True{}:
      3n
    case False{}:
      4n

# the scanline bytes encode_png writes for a raster: each of the h rows is a
# filter byte, then the channels of its w samples
def spec.scan.len(+ww: U32, +hh: U32, op: Bool) -> Nat:
  Nat.mul(U32.to_nat(hh), 1n+Nat.mul(U32.to_nat(ww), spec.nch(op)))

# what decode_png makes of an encoding, when there is one
def spec.png.back(mm: Maybe<&2, List<&2, U32>>) -> Maybe<&2, Img.Raster>:
  match mm:
    case None{}:
      None{}
    case Some{bytes}:
      Img.decode_png(bytes)

# LAW: a well-formed raster with both sides nonzero whose scanlines fit one
# stored block decodes from its PNG to itself: nb, the scanline byte count
# as a U32, is at most 65535
law png_roundtrip_one:
  for +ww: U32
  for +hh: U32
  for +px: List<&2, U32>
  for +nb: U32
  for h_ok: {D2.png_ok(ww, hh, px) == True{} : Bool}
  for h_nb: {U32.to_nat(nb) == spec.scan.len(ww, hh, D1.all_opaque(px)) : Nat}
  for h_one: {U32.is_le(nb, 65535) == True{} : Bool}
  {spec.png.back(Img.encode_png(Img.raster(ww, hh, px))) == Some{Img.raster(ww, hh, px)} : Maybe<&2, Img.Raster>}

# LAW: every raster encode_png accepts, a well-formed raster with both sides nonzero and fewer than 2^28 samples,
# decodes from its PNG to itself
law png_roundtrip:
  for +ww: U32
  for +hh: U32
  for +px: List<&2, U32>
  for h_ok: {D2.png_ok(ww, hh, px) == True{} : Bool}
  {spec.png.back(Img.encode_png(Img.raster(ww, hh, px))) == Some{Img.raster(ww, hh, px)} : Maybe<&2, Img.Raster>}
