# proofs of laws/PngDecodesWellFormed.bend
import Base
import ../main.bend as Img
import ../src/png.bend as Png
import ../laws/PngDecodesWellFormed.bend as Laws
import ../laws/defs/WellFormed.bend as D1
import ./lemmas/BasicFacts.bend as M1

# well formed when there is a raster; nothing to say of none
def wf.of(mm: Maybe<&2, Img.Raster>) -> Bool:
  match mm:
    case None{}:
      True{}
    case Some{img}:
      D1.wf(img)

# what wf.of says of a result equal to Some(img), it says of img
def wf.some(
  +mm: Maybe<&2, Img.Raster>,
  +img: Img.Raster,
  h_eq: {mm == Some{img} : Maybe<&2, Img.Raster>},
  h_ok: {wf.of(mm) == True{} : Bool}
) -> {D1.wf(img) == True{} : Bool}:
  Equal.trans(Bool, D1.wf(img), wf.of(mm), True{},
    Equal.cong(Maybe<&2, Img.Raster>, Bool, xx => wf.of(xx), Some{img}, mm,
      Equal.sym(Maybe<&2, Img.Raster>, mm, Some{img}, h_eq)),
    h_ok)

# a kept raster passed the count check: h * w samples, so w * h
def keep.wf(
  ok: Bool,
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  eo: {Nat.is_eq(List.length(&2, U32, px), Nat.mul(U32.to_nat(hh), U32.to_nat(ww))) == ok : Bool}
) -> {wf.of(Img.decode_png.keep(ok, ww, hh, px)) == True{} : Bool}:
  match ok:
    case False{}:
      {==}
    case True{}:
      Equal.trans(Bool, Nat.is_eq(List.length(&2, U32, px), Nat.mul(U32.to_nat(ww), U32.to_nat(hh))),
        Nat.is_eq(List.length(&2, U32, px), Nat.mul(U32.to_nat(hh), U32.to_nat(ww))), True{},
        Equal.cong(Nat, Bool, kk => Nat.is_eq(List.length(&2, U32, px), kk),
          Nat.mul(U32.to_nat(ww), U32.to_nat(hh)), Nat.mul(U32.to_nat(hh), U32.to_nat(ww)),
          M1.mul_comm(U32.to_nat(ww), U32.to_nat(hh))),
        eo)

# whatever picture the PNG decoder hands over, the raster made of it is well formed
def pic.wf(mm: Maybe<&2, Png.Pic>) -> {wf.of(Img.decode_png.pic(mm)) == True{} : Bool}:
  match mm:
    case None{}:
      {==}
    case Some{Png.Pic{+ww, +hh, +px}}:
      keep.wf(Nat.is_eq(List.length(&2, U32, px), Nat.mul(U32.to_nat(hh), U32.to_nat(ww))), ww, hh, px, {==})

def Laws.png_decode_well_formed(bytes, img, h_dec):
  wf.some(Img.decode_png(bytes), img, h_dec, pic.wf(Img.decode_png.of(Img.parse_signature(bytes), bytes)))
