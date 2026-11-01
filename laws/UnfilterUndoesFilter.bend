# For every filter type 0 to 4 and every scanlines of a given width and bytes
# per pixel, `Png.unfilter` applied to the rows filtered by the PNG
# specification's filter function returns `Some` of the rows.
import Base
import ../src/png.bend as Png

# the five filter types of PNG section 9.2 (W3C PNG, 9.2 "Filter types for
# filter method 0"): None, Sub, Up, Average and Paeth
type Ft is Data:
  FNone{}
  FSub{}
  FUp{}
  FAvg{}
  FPaeth{}

# the byte PNG writes before a row filtered with each type: 0 to 4
def ft.code(ft: Ft) -> U32:
  match ft:
    case FNone{}:
      0
    case FSub{}:
      1
    case FUp{}:
      2
    case FAvg{}:
      3
    case FPaeth{}:
      4

# entry nn of a newest-first history of bytes, or 0 past its end (outside the image)
def flt.at(hist: List<&2, U32>, nn: Nat) -> U32:
  match hist nn:
    case Nil{} _nn:
      0
    case +hd <> _tl 0n:
      hd
    case _hd <> tl 1n+pp:
      flt.at(tl, pp)

# b, the byte above: the next byte of the previous row, or 0 on the first row
def flt.up(prev: List<&2, U32>) -> U32:
  match prev:
    case Nil{}:
      0
    case +hd <> _tl:
      hd

# the previous row past the byte above
def flt.next(prev: List<&2, U32>) -> List<&2, U32>:
  match prev:
    case Nil{}:
      Nil{}
    case _hd <> tl:
      tl

# |x - y| of two U32s: the smaller taken from the larger
def flt.dist.at(ge: Bool, +xx: U32, +yy: U32) -> U32:
  match ge:
    case True{}:
      (xx - yy : U32)
    case False{}:
      (yy - xx : U32)

# |x - y| of two U32s
def flt.dist(+xx: U32, +yy: U32) -> U32:
  flt.dist.at(U32.is_ge(xx, yy), xx, yy)

# PaethPredictor's choice, in the specification's order: a when pa <= pb and
# pa <= pc, otherwise b when pb <= pc, otherwise c
def flt.paeth.near(
  ab: Bool,
  ac: Bool,
  bc: Bool,
  +aa: U32,
  +bb: U32,
  +cc: U32
) -> U32:
  match ab ac bc:
    case True{} True{} _bc:
      aa
    case True{} False{} True{}:
      bb
    case True{} False{} False{}:
      cc
    case False{} _ac True{}:
      bb
    case False{} _ac False{}:
      cc

# PaethPredictor(a, b, c) of PNG section 9.4, with p = a + b - c expanded so
# no distance goes below zero: |p - a| = |b - c|, |p - b| = |a - c| and
# |p - c| = |a + b - 2c|, 2c being c shifted left one bit
def flt.paeth(+aa: U32, +bb: U32, +cc: U32) -> U32:
  +pa = flt.dist(bb, cc)
  +pb = flt.dist(aa, cc)
  +pc = flt.dist((aa + bb : U32), (cc << 1n : U32))
  flt.paeth.near(U32.is_le(pa, pb), U32.is_le(pa, pc), U32.is_le(pb, pc), aa, bb, cc)

# the predictor each filter type subtracts: None 0, Sub a, Up b, Average
# floor((a + b) / 2), Paeth PaethPredictor(a, b, c)
def flt.pred(ft: Ft, +aa: U32, +bb: U32, +cc: U32) -> U32:
  match ft:
    case FNone{}:
      0
    case FSub{}:
      aa
    case FUp{}:
      bb
    case FAvg{}:
      ((aa + bb : U32) >> 1n : U32)
    case FPaeth{}:
      flt.paeth(aa, bb, cc)

# Filt(x) = Orig(x) - predictor, mod 256, for each byte of one row. `prev`
# is the rest of the previous row, `hist` and `phist` the bytes of this row
# and of the previous row already passed, newest first; a is `bpp` bytes back
# in `hist`, b the byte above, c `bpp` bytes back in `phist`, each 0 outside
# the image
def flt.row(
  row: List<&2, U32>,
  +ft: Ft,
  +bpp: U32,
  +prev: List<&2, U32>,
  +hist: List<&2, U32>,
  +phist: List<&2, U32>
) -> List<&2, U32>:
  match row:
    case Nil{}:
      Nil{}
    case +xx <> rest:
      +aa = flt.at(hist, U32.to_nat((bpp - 1 : U32)))
      +bb = flt.up(prev)
      +cc = flt.at(phist, U32.to_nat((bpp - 1 : U32)))
      U32.and(255, (xx - flt.pred(ft, aa, bb, cc) : U32)) <>
        flt.row(rest, ft, bpp, flt.next(prev), {xx <> hist : List<&2, U32>}, {bb <> phist : List<&2, U32>})

# the filtered image data: each row filtered with `ft` against the row
# before it (none above the first), after its filter type byte
def flt.rows(rows: List<&2, List<&2, U32>>, +ft: Ft, +bpp: U32, prev: List<&2, U32>) -> List<&2, U32>:
  match rows:
    case Nil{}:
      Nil{}
    case +row <> rest:
      ft.code(ft) <> List.append(&2, U32, flt.row(row, ft, bpp, prev, [], []), flt.rows(rest, ft, bpp, row))

# a row of exactly nn bytes, each below 256, with `ok` the answer so far
def flt.bytes(row: List<&2, U32>, nn: Nat, ok: Bool) -> Bool:
  match row nn:
    case Nil{} 0n:
      ok
    case Nil{} 1n+_pp:
      False{}
    case _xx <> _rest 0n:
      False{}
    case +xx <> rest 1n+pp:
      flt.bytes(rest, pp, Bool.and(ok, U32.is_lt(xx, 256)))

# every row nn bytes, each below 256, with `ok` the answer so far
def flt.fit(rows: List<&2, List<&2, U32>>, +nn: Nat, ok: Bool) -> Bool:
  match rows:
    case Nil{}:
      ok
    case +row <> rest:
      flt.fit(rest, nn, Bool.and(ok, flt.bytes(row, nn, True{})))

# the sizes unfilter reads: a nonzero width and height, 1 to 4 bytes per pixel
def flt.dims(+ww: U32, +hh: U32, +bpp: U32) -> Bool:
  Bool.and(U32.is_gt(ww, 0), Bool.and(U32.is_gt(hh, 0), Bool.and(U32.is_gt(bpp, 0), U32.is_le(bpp, 4))))

# LAW: unfilter undoes the PNG filter of every type: rows of width times bpp bytes, filtered by the specification's
# filter function, unfilter to the rows
law unfilter_filter:
  for +ft: Ft
  for +ww: U32
  for +hh: U32
  for +bpp: U32
  for +rows: List<&2, List<&2, U32>>
  for +h_dims: {flt.dims(ww, hh, bpp) == True{} : Bool}
  for +h_wrap: {U32.to_nat((ww * bpp : U32)) == Nat.mul(U32.to_nat(ww), U32.to_nat(bpp)) : Nat}
  for h_rows: {List.length(&2, List<&2, U32>, rows) == U32.to_nat(hh) : Nat}
  for h_fit: {flt.fit(rows, Nat.mul(U32.to_nat(ww), U32.to_nat(bpp)), True{}) == True{} : Bool}
  {Png.unfilter(flt.rows(rows, ft, bpp, []), ww, hh, bpp) == Some{List.concat(&2, U32, rows)}
    : Maybe<&2, List<&2, U32>>}
