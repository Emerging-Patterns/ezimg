# ezimg: the laws. Each law carries the SPEC.md row it proves, or proves part
# of, on its own comment line. PROOF.bend fills them; `bend PROOF.bend` is the
# gate. Every row is pending: the 85 closed laws that stood here were retired
# (docs/rfc/ezimg-law-inventory.md keeps what each one pointed toward), and
# the quantified laws land row by row. The imports keep every module under
# the gate's checker until laws reach them.
import Base
import ./main.bend as Img
import ./src/crc.bend as Crc
import ./src/inflate.bend as Inf
import ./src/png.bend as Png
import ./src/jpeg.bend as Jpeg
import ./src/jpeg_enc.bend as Jenc

# LAW: every sample Jpeg.rgb packs is opaque, for every Y, Cb and Cr
# IMG-PIX-1
law jpeg_rgb_opaque:
  for +yy: U32
  for +cb: U32
  for +cr: U32
  {U32.shrn(Jpeg.rgb(yy, cb, cr), 24n) == 255 : U32}

# LAW: every sample Jpeg.gray packs is opaque, for every level
# IMG-PIX-1
law jpeg_gray_opaque:
  for +yy: U32
  {U32.shrn(Jpeg.gray(yy), 24n) == 255 : U32}

# LAW: encode_jpeg refuses exactly the rasters encode_png refuses
# IMG-JPG-4
law jpeg_png_refuse_alike:
  for +img: Img.Raster
  {Maybe.is_none(&2, List<&2, U32>, Img.encode_jpeg(img)) ==
    Maybe.is_none(&2, List<&2, U32>, Img.encode_png(img)) : Bool}

# every sample's colour, alpha cleared: the specification's own copy
def alpha.drop(px: List<&2, U32>) -> List<&2, U32>:
  match px:
    case Nil{}:
      Nil{}
    case pp <> rest:
      U32.and(16777215, pp) <> alpha.drop(rest)

# LAW: two rasters of one size whose samples differ only in alpha encode to the same JPEG bytes
# IMG-PIX-2
law jpeg_alpha_blind:
  for +ww: U32
  for +hh: U32
  for +pa: List<&2, U32>
  for +pb: List<&2, U32>
  for +same: {alpha.drop(pa) == alpha.drop(pb) : List<&2, U32>}
  {Img.encode_jpeg(Img.raster(ww, hh, pa)) == Img.encode_jpeg(Img.raster(ww, hh, pb)) : Maybe<&2, List<&2, U32>>}

# a sample through a function, or none
def opt.map(~ff: U32 -> U32, mm: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match mm:
    case None{}:
      None{}
    case Some{vv}:
      Some{ff(vv)}

# LAW: map keeps the width and the height
# IMG-RAS-5
law map_size:
  for ~ff: U32 -> U32
  for +img: Img.Raster
  {Img.size(Img.map(~ff, img)) == Img.size(img) : U32 & U32}

# LAW: sample k of map(f, r) is f of sample k of r, for every k, and none past the end
# IMG-RAS-5
law map_at:
  for ~ff: U32 -> U32
  for +img: Img.Raster
  for +kk: Nat
  {List.get(&2, U32, Img.pixels(Img.map(~ff, img)), kk) ==
    opt.map(~ff, List.get(&2, U32, Img.pixels(img), kk)) : Maybe<&2, U32>}

# LAW: bytes that open with the eight signature bytes parse as the signature, whatever follows
# IMG-PNG-1
law sig_opens:
  for +rest: List<&2, U32>
  {Img.parse_signature(List.append(&2, U32, Img.png_sig(), rest)) == Some{Img.png_sig()} : Maybe<&2, List<&2, U32>>}

# LAW: parse_signature is some only when the bytes open with the eight signature bytes
# IMG-PNG-1
law sig_only:
  for +xs: List<&2, U32>
  for h_some: {Maybe.is_some(&2, List<&2, U32>, Img.parse_signature(xs)) == True{} : Bool}
  {xs == List.append(&2, U32, Img.png_sig(), List.drop(&2, U32, xs, 8n)) : List<&2, U32>}

# ---- wp3-filter ----

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
# IMG-PNG-6
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
