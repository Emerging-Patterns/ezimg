# `checked_raster(w, h, px)` is `raster(w, h, px)` exactly when that raster
# is well formed (`px` has `w * h` samples, `w * h` a natural number), and
# none otherwise, for every `w`, `h` and `px`.
import Base
import ../main.bend as Img
import ./defs/WellFormed.bend as D1

# the raster when ok holds, otherwise none
def keep(ok: Bool, img: Img.Raster) -> Maybe<&2, Img.Raster>:
  match ok:
    case True{}:
      Some{img}
    case False{}:
      None{}

# LAW: checked_raster(w, h, px) is raster(w, h, px) when that raster is well formed, and none otherwise
law checked_keeps:
  for +ww: U32
  for +hh: U32
  for +px: List<&2, U32>
  {Img.checked_raster(ww, hh, px) == keep(D1.wf(Img.raster(ww, hh, px)), Img.raster(ww, hh, px)) :
    Maybe<&2, Img.Raster>}
