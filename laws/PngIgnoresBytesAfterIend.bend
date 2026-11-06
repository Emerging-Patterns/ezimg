# `decode_png` stops reading at IEND: a file laid out as PNG section 5.6
# gives decodes the same whatever bytes follow its IEND chunk, to the raster
# laws/PngSamplesFollowColourType.bend's png_walk gives the file alone, as
# libpng, stb_image and image-rs read it. IEND marks the end of the datastream
# (PNG section 11.2.5); nothing after it is a chunk, so nothing after it is
# checked or refused.
import Base
import ../main.bend as Img
import ../src/inflate.bend as Inf
import ./defs/PngSpecification.bend as D1

# LAW: a file laid out as PNG section 5.6 gives, with any bytes after IEND, decodes to the raster png_walk gives the
# file without them
law png_after_iend:
  for +ww: U32
  for +hh: U32
  for +cc: U32
  for +plte: Maybe<&2, List<&2, U32>>
  for +trns: Maybe<&2, List<&2, U32>>
  for +idats: List<&2, List<&2, U32>>
  for +rest: List<&2, U32>
  for h_ww: {U32.is_gt(ww, 0) == True{} : Bool}
  for h_hh: {U32.is_gt(hh, 0) == True{} : Bool}
  for h_cc: {D1.spec.colour.ok(cc) == True{} : Bool}
  for h_pl: {D1.spec.plte.ok(cc, plte) == True{} : Bool}
  for h_tr: {D1.spec.trns.ok(cc, plte, trns) == True{} : Bool}
  for h_fp: D1.spec.fits.opt(plte)
  for h_ft: D1.spec.fits.opt(trns)
  for h_fi: D1.spec.fits.all(idats)
  {Img.decode_png(D1.spec.png.then(ww, hh, cc, plte, trns, idats, rest)) == D1.spec.decoded(Inf.inflate(
    List.concat(&2, U32, idats)), ww, hh, cc, D1.spec.or.nil(plte), D1.spec.or.nil(trns)) : Maybe<&2, Img.Raster>}
