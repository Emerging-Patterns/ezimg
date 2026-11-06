# Every raster `decode_png` returns is well formed: it holds exactly `w * h`
# samples, for every input. A header whose width times bytes per pixel wraps
# a U32 decodes to none, not to a raster too short for its sides.
import Base
import ../main.bend as Img
import ./defs/WellFormed.bend as D1

# LAW: every raster decode_png returns, whatever the bytes, has w * h samples
law png_decode_well_formed:
  for +bytes: List<&2, U32>
  for +img: Img.Raster
  for h_dec: {Img.decode_png(bytes) == Some{img} : Maybe<&2, Img.Raster>}
  {D1.wf(img) == True{} : Bool}
