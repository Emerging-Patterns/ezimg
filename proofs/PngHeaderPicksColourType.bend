# proofs of laws/PngHeaderPicksColourType.bend
import Base
import ../src/png.bend as Png
import ../laws/PngHeaderPicksColourType.bend as Laws
import ../laws/defs/PngSpecification.bend as D1
import ./lemmas/BasicFacts.bend as M1

# out opens with the signature and an IHDR of colour type ct
def head.ty(+ww: U32, +hh: U32, +ct: U32, out: List<&2, U32>) -> Type:
  &rest: List<&2, U32> -> {out == List.append(&2, U32, Laws.ihdr_head(ww, hh, ct), rest) : List<&2, U32>}

# one stored block or several: either way the signature and IHDR come first
def head.seal.at(
  zz: Bool,
  +ww: U32,
  +hh: U32,
  +op: Bool,
  +raw: List<&2, U32>,
  +nn: U32
) -> head.ty(ww, hh, Png.enc.ct(op), Png.enc.seal.at(zz, ww, hh, op, raw, nn)):
  match zz:
    case False{}:
      (List.drop(&2, U32, Png.enc.seal.one(ww, hh, op, raw, nn), 29n), {==})
    case True{}:
      (List.drop(&2, U32, Png.enc.seal.wide(ww, hh, op, raw, nn), 29n), {==})

# whatever the scanlines and their count, sealing puts the signature and IHDR first
def head.seal(
  +ww: U32,
  +hh: U32,
  +op: Bool,
  got: List<&2, U32> & U32
) -> head.ty(ww, hh, Png.enc.ct(op), Png.enc.seal(ww, hh, op, got)):
  match got:
    case (raw, +nn):
      head.seal.at(U32.is_gt(nn, 65535), ww, hh, op, raw, nn)

# every path paint takes puts the signature and IHDR first
def head.paint.at(
  zz: Bool,
  +ww: U32,
  +hh: U32,
  op: Bool,
  +px: List<&2, U32>,
  +nn: U32
) -> head.ty(ww, hh, Png.enc.ct(op), Png.enc.paint.at(zz, ww, hh, op, px, nn)):
  match zz op:
    case False{} False{}:
      head.seal(ww, hh, False{}, Png.enc.raw(px, 0n, U32.to_nat(ww), False{}, [], 0))
    case False{} True{}:
      head.seal(ww, hh, True{}, Png.enc.raw(px, 0n, U32.to_nat(ww), True{}, [], 0))
    case True{} False{}:
      head.seal(ww, hh, False{}, Png.enc.raw(px, 0n, U32.to_nat(ww), False{}, [], 0))
    case True{} True{}:
      (List.drop(&2, U32, Png.enc.wide.rgb(ww, hh, px, nn), 29n), {==})

# the law's form, over a Maybe
def head.some.ty(+ww: U32, +hh: U32, +ct: U32, mm: Maybe<&2, List<&2, U32>>) -> Type:
  &rest: List<&2, U32> -> {mm == Some{List.append(&2, U32, Laws.ihdr_head(ww, hh, ct), rest)} :
    Maybe<&2, List<&2, U32>>}

# a head of one colour type is a head of an equal one, under Some
def head.some(
  +ww: U32,
  +hh: U32,
  +ca: U32,
  +cb: U32,
  +out: List<&2, U32>,
  ec: {ca == cb : U32},
  hd: head.ty(ww, hh, ca, out)
) -> head.some.ty(ww, hh, cb, Some{out}):
  (rest, eo) = hd
  +e_head = Equal.cong(U32, List<&2, U32>, cc => List.append(&2, U32, Laws.ihdr_head(ww, hh, cc), rest), ca, cb, ec)
  (rest, Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, ll => Some{ll}, out,
    List.append(&2, U32, Laws.ihdr_head(ww, hh, cb), rest),
    Equal.trans(List<&2, U32>, out, List.append(&2, U32, Laws.ihdr_head(ww, hh, ca), rest),
      List.append(&2, U32, Laws.ihdr_head(ww, hh, cb), rest), eo, e_head)))

# enc.ct is the law's colour_type
def ct.same(bb: Bool) -> {Png.enc.ct(bb) == Laws.colour_type(bb) : U32}:
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# the code's colour type is the law's
def ct.law(
  +px: List<&2, U32>
) -> {Png.enc.ct(Png.enc.opaque(px, True{})) == Laws.colour_type(D1.all_opaque(px)) : U32}:
  Equal.trans(U32, Png.enc.ct(Png.enc.opaque(px, True{})), Png.enc.ct(D1.all_opaque(px)),
    Laws.colour_type(D1.all_opaque(px)),
    Equal.cong(Bool, U32, bb => Png.enc.ct(bb), Png.enc.opaque(px, True{}), D1.all_opaque(px),
      M1.opaque.all(px, True{})),
    ct.same(D1.all_opaque(px)))

# the guard passed, or h_some is false
def head.open(
  zz: Bool,
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  h_some: {Maybe.is_some(&2, List<&2, U32>, Png.enc.open(zz, ww, hh, px)) == True{} : Bool}
) -> head.some.ty(ww, hh, Laws.colour_type(D1.all_opaque(px)), Png.enc.open(zz, ww, hh, px)):
  match zz:
    case False{}:
      Empty.absurd(head.some.ty(ww, hh, Laws.colour_type(D1.all_opaque(px)), None{}), M1.false_true(h_some))
    case True{}:
      +op = Png.enc.opaque(px, True{})
      +nn = Png.enc.nbytes(op, ww, hh)
      head.some(ww, hh, Png.enc.ct(op), Laws.colour_type(D1.all_opaque(px)), Png.enc.paint(ww, hh, op, px),
        ct.law(px), head.paint.at(U32.is_gt(nn, 65535), ww, hh, op, px, nn))

def Laws.png_ihdr(ww, hh, px, h_some):
  head.open(Png.enc.good(ww, hh, px), ww, hh, px, h_some)
