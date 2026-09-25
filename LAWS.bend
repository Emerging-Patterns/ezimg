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

# ---- wp6-raster ----

# is the raster well formed: its sample count is w * h, computed as a Nat
def wf(img: Img.Raster) -> Bool:
  match img:
    case Img.Raster{ww, hh, px}:
      Nat.is_eq(List.length(&2, U32, px), Nat.mul(U32.to_nat(ww), U32.to_nat(hh)))

# is (x, y) a point of the raster: x < w and y < h, as Nats
def inside(img: Img.Raster, +xx: U32, +yy: U32) -> Bool:
  match img:
    case Img.Raster{ww, hh, _px}:
      Bool.and(Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)), Nat.is_lt(U32.to_nat(yy), U32.to_nat(hh)))

# where (x, y) sits in the samples of a raster of width w: y * w + x, as a Nat
def spot(ww: U32, xx: U32, yy: U32) -> Nat:
  Nat.add(Nat.mul(U32.to_nat(yy), U32.to_nat(ww)), U32.to_nat(xx))

# The laws below take w * h < 2^32 as a U32 `area` whose value is w * h: a
# Nat is below 2^32 exactly when it is some U32's value. (A closed 2^32 in a
# law would be expanded in unary by the checker.)

# LAW: fill(w, h, c) is well formed, for every w and h with w * h < 2^32 and every c
# IMG-RAS-1
law fill_wf:
  for +ww: U32
  for +hh: U32
  for +color: U32
  for +area: U32
  for h_area: {U32.to_nat(area) == Nat.mul(U32.to_nat(ww), U32.to_nat(hh)) : Nat}
  {wf(Img.fill(ww, hh, color)) == True{} : Bool}

# LAW: every sample of fill(w, h, c) is c, for every w, h and c
# IMG-RAS-1
law fill_every:
  for +ww: U32
  for +hh: U32
  for +color: U32
  for kk: Nat
  for +vv: U32
  for h_at: {List.get(&2, U32, Img.pixels(Img.fill(ww, hh, color)), kk) == Some{vv} : Maybe<&2, U32>}
  {vv == color : U32}

# LAW: inside the raster, get(r, x, y) is sample y * w + x, when w * h < 2^32
# IMG-RAS-2
law get_inside:
  for +img: Img.Raster
  for +xx: U32
  for +yy: U32
  for +area: U32
  for h_area: {U32.to_nat(area) == Nat.mul(U32.to_nat(Img.width(img)), U32.to_nat(Img.height(img))) : Nat}
  for +h_in: {inside(img, xx, yy) == True{} : Bool}
  {Img.get(img, xx, yy) == List.get(&2, U32, Img.pixels(img), spot(Img.width(img), xx, yy)) : Maybe<&2, U32>}

# LAW: inside a well-formed raster, get(r, x, y) is some, when w * h < 2^32
# IMG-RAS-2
law get_inside_some:
  for +img: Img.Raster
  for +xx: U32
  for +yy: U32
  for +area: U32
  for h_area: {U32.to_nat(area) == Nat.mul(U32.to_nat(Img.width(img)), U32.to_nat(Img.height(img))) : Nat}
  for h_wf: {wf(img) == True{} : Bool}
  for +h_in: {inside(img, xx, yy) == True{} : Bool}
  {Maybe.is_some(&2, U32, Img.get(img, xx, yy)) == True{} : Bool}

# LAW: outside the raster, get(r, x, y) is none, for every raster
# IMG-RAS-2
law get_outside:
  for +img: Img.Raster
  for +xx: U32
  for +yy: U32
  for h_out: {inside(img, xx, yy) == False{} : Bool}
  {Img.get(img, xx, yy) == None{} : Maybe<&2, U32>}

# LAW: inside the raster, set(r, x, y, c) replaces sample y * w + x with c and
# nothing else, when w * h < 2^32
# IMG-RAS-2
law set_inside:
  for +img: Img.Raster
  for +xx: U32
  for +yy: U32
  for +color: U32
  for +area: U32
  for h_area: {U32.to_nat(area) == Nat.mul(U32.to_nat(Img.width(img)), U32.to_nat(Img.height(img))) : Nat}
  for +h_in: {inside(img, xx, yy) == True{} : Bool}
  {Img.set(img, xx, yy, color) == Img.raster(Img.width(img), Img.height(img),
    List.set(&2, U32, Img.pixels(img), spot(Img.width(img), xx, yy), color)) : Img.Raster}

# LAW: outside the raster, set(r, x, y, c) is r, for every raster
# IMG-RAS-2
law set_outside:
  for +img: Img.Raster
  for +xx: U32
  for +yy: U32
  for +color: U32
  for h_out: {inside(img, xx, yy) == False{} : Bool}
  {Img.set(img, xx, yy, color) == img : Img.Raster}

# how much of the span x .. x + c - 1 lies in 0 .. w - 1: min(c, w - x), and
# 0 when x >= w (Nat.sub stops at 0)
def cut(ww: U32, xx: U32, cc: U32) -> Nat:
  Nat.min(U32.to_nat(cc), Nat.sub(U32.to_nat(ww), U32.to_nat(xx)))

# one side of a crop: the intersection's side aa, or 0 when either side of
# the intersection (aa or bb) is 0
def side(aa: Nat, bb: Nat) -> Nat:
  match aa bb:
    case 0n _bb:
      0n
    case 1n+_pa 0n:
      0n
    case 1n+pa 1n+_pb:
      1n+pa

# LAW: crop's width and height are those of the rectangle's intersection with the raster, 0 by 0 when that is
# empty, for every raster
# IMG-RAS-3
law crop_size:
  for +img: Img.Raster
  for +xx: U32
  for +yy: U32
  for +cw: U32
  for +ch: U32
  {(U32.to_nat(Img.width(Img.crop(img, xx, yy, cw, ch))), U32.to_nat(Img.height(Img.crop(img, xx, yy, cw, ch)))) ==
    (side(cut(Img.width(img), xx, cw), cut(Img.height(img), yy, ch)),
      side(cut(Img.height(img), yy, ch), cut(Img.width(img), xx, cw))) : Nat & Nat}

# LAW: crop of a well-formed raster is well formed, when w * h < 2^32
# IMG-RAS-3
law crop_wf:
  for +img: Img.Raster
  for +xx: U32
  for +yy: U32
  for +cw: U32
  for +ch: U32
  for +area: U32
  for h_area: {U32.to_nat(area) == Nat.mul(U32.to_nat(Img.width(img)), U32.to_nat(Img.height(img))) : Nat}
  for h_wf: {wf(img) == True{} : Bool}
  {wf(Img.crop(img, xx, yy, cw, ch)) == True{} : Bool}

# LAW: the crop's sample at (i, j) is the raster's sample at (x + i, y + j), for every point (i, j) of the crop of
# a well-formed raster, when w * h < 2^32
# IMG-RAS-3
law crop_at:
  for +img: Img.Raster
  for +xx: U32
  for +yy: U32
  for +cw: U32
  for +ch: U32
  for +area: U32
  for h_area: {U32.to_nat(area) == Nat.mul(U32.to_nat(Img.width(img)), U32.to_nat(Img.height(img))) : Nat}
  for h_wf: {wf(img) == True{} : Bool}
  for +ii: Nat
  for +jj: Nat
  for hi: {Nat.is_lt(ii, U32.to_nat(Img.width(Img.crop(img, xx, yy, cw, ch)))) == True{} : Bool}
  for hj: {Nat.is_lt(jj, U32.to_nat(Img.height(Img.crop(img, xx, yy, cw, ch)))) == True{} : Bool}
  {List.get(&2, U32, Img.pixels(Img.crop(img, xx, yy, cw, ch)),
    Nat.add(Nat.mul(jj, U32.to_nat(Img.width(Img.crop(img, xx, yy, cw, ch)))), ii)) ==
    List.get(&2, U32, Img.pixels(img),
      Nat.add(Nat.mul(Nat.add(U32.to_nat(yy), jj), U32.to_nat(Img.width(img))), Nat.add(U32.to_nat(xx), ii))) :
    Maybe<&2, U32>}

# does src, pasted at (x, y), cover the point (i, j): x <= i < x + sw and
# y <= j < y + sh, as Nats
def covers(+xx: U32, +yy: U32, src: Img.Raster, +ii: Nat, +jj: Nat) -> Bool:
  match src:
    case Img.Raster{sw, sh, _sp}:
      Bool.and(Bool.and(Nat.is_le(U32.to_nat(xx), ii), Nat.is_lt(ii, Nat.add(U32.to_nat(xx), U32.to_nat(sw)))),
        Bool.and(Nat.is_le(U32.to_nat(yy), jj), Nat.is_lt(jj, Nat.add(U32.to_nat(yy), U32.to_nat(sh)))))

# LAW: blit(dst, src, x, y) has dst's width and height, for every dst, src and offset
# IMG-RAS-4
law blit_size:
  for +dst: Img.Raster
  for +src: Img.Raster
  for +xx: U32
  for +yy: U32
  {Img.size(Img.blit(dst, src, xx, yy)) == Img.size(dst) : U32 & U32}

# LAW: blit of a well-formed src onto a well-formed dst is well formed, when dst's w * h < 2^32
# IMG-RAS-4
law blit_wf:
  for +dst: Img.Raster
  for +src: Img.Raster
  for +xx: U32
  for +yy: U32
  for +area: U32
  for h_area: {U32.to_nat(area) == Nat.mul(U32.to_nat(Img.width(dst)), U32.to_nat(Img.height(dst))) : Nat}
  for h_dst: {wf(dst) == True{} : Bool}
  for h_src: {wf(src) == True{} : Bool}
  {wf(Img.blit(dst, src, xx, yy)) == True{} : Bool}

# LAW: at every point (i, j) of dst that src covers, blit takes src's sample at (i - x, j - y), for well-formed
# dst and src, when dst's w * h < 2^32
# IMG-RAS-4
law blit_in:
  for +dst: Img.Raster
  for +src: Img.Raster
  for +xx: U32
  for +yy: U32
  for +area: U32
  for h_area: {U32.to_nat(area) == Nat.mul(U32.to_nat(Img.width(dst)), U32.to_nat(Img.height(dst))) : Nat}
  for h_dst: {wf(dst) == True{} : Bool}
  for h_src: {wf(src) == True{} : Bool}
  for +ii: Nat
  for +jj: Nat
  for +hi: {Nat.is_lt(ii, U32.to_nat(Img.width(dst))) == True{} : Bool}
  for +hj: {Nat.is_lt(jj, U32.to_nat(Img.height(dst))) == True{} : Bool}
  for +h_cov: {covers(xx, yy, src, ii, jj) == True{} : Bool}
  {List.get(&2, U32, Img.pixels(Img.blit(dst, src, xx, yy)), Nat.add(Nat.mul(jj, U32.to_nat(Img.width(dst))), ii)) ==
    List.get(&2, U32, Img.pixels(src),
      Nat.add(Nat.mul(Nat.sub(jj, U32.to_nat(yy)), U32.to_nat(Img.width(src))), Nat.sub(ii, U32.to_nat(xx)))) :
    Maybe<&2, U32>}

# LAW: at every point (i, j) of dst that src does not cover, blit keeps dst's sample, for well-formed dst and src,
# when dst's w * h < 2^32
# IMG-RAS-4
law blit_out:
  for +dst: Img.Raster
  for +src: Img.Raster
  for +xx: U32
  for +yy: U32
  for +area: U32
  for h_area: {U32.to_nat(area) == Nat.mul(U32.to_nat(Img.width(dst)), U32.to_nat(Img.height(dst))) : Nat}
  for h_dst: {wf(dst) == True{} : Bool}
  for h_src: {wf(src) == True{} : Bool}
  for +ii: Nat
  for +jj: Nat
  for +hi: {Nat.is_lt(ii, U32.to_nat(Img.width(dst))) == True{} : Bool}
  for +hj: {Nat.is_lt(jj, U32.to_nat(Img.height(dst))) == True{} : Bool}
  for +h_cov: {covers(xx, yy, src, ii, jj) == False{} : Bool}
  {List.get(&2, U32, Img.pixels(Img.blit(dst, src, xx, yy)), Nat.add(Nat.mul(jj, U32.to_nat(Img.width(dst))), ii)) ==
    List.get(&2, U32, Img.pixels(dst), Nat.add(Nat.mul(jj, U32.to_nat(Img.width(dst))), ii)) : Maybe<&2, U32>}
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

# ---- wp1-crc ----

# the ISO 3309 / ITU-T V.42 CRC-32 polynomial, reflected (PNG section 5.5
# and Annex D): 0xEDB88320
def crc.ref.poly() -> U32:
  3988292384

# one bit, as the specification's sample code does it: when the low bit of
# the register is set, shift right and xor in the polynomial; else shift right
def crc.ref.shift(odd: Bool, +cc: U32) -> U32:
  match odd:
    case True{}:
      ((cc >> 1n : U32) .^. crc.ref.poly() : U32)
    case False{}:
      (cc >> 1n : U32)

# one bit step of the register, low bit first. The register is taken apart
# first, so a register the checker cannot compute stays one stuck match
# instead of being copied into both the test and the shift at every step
def crc.ref.step(cc: U32) -> U32:
  match cc:
    case U32{+ww}:
      crc.ref.shift(U32.is_eq((U32{ww} .&. 1 : U32), 1), U32{ww})

# nn bit steps
def crc.ref.bits(nn: Nat, +cc: U32) -> U32:
  match nn:
    case 0n:
      cc
    case 1n+pp:
      crc.ref.bits(pp, crc.ref.step(cc))

# one byte: xor it into the register, then eight bit steps. Bytes are U32 in
# ezimg and the byte is xored in whole, so for 0 to 255 this is ISO 3309
def crc.ref.byte(+cc: U32, +bb: U32) -> U32:
  crc.ref.bits(8n, (cc .^. bb : U32))

# every byte in order, the register still inverted
def crc.ref.fold(xs: List<&2, U32>, +cc: U32) -> U32:
  match xs:
    case Nil{}:
      cc
    case +bb <> tl:
      crc.ref.fold(tl, crc.ref.byte(cc, bb))

# the bitwise CRC-32: register preset to all ones, all ones xored at the end
def crc.ref(xs: List<&2, U32>) -> U32:
  (crc.ref.fold(xs, 4294967295) .^. 4294967295 : U32)

# LAW: Crc.crc32 is the bitwise ISO 3309 CRC-32, for every byte list
# IMG-PNG-5
law crc32_bitwise:
  for xs: List<&2, U32>
  {Crc.crc32(xs) == crc.ref(xs) : U32}

# a PNG chunk as bytes (PNG section 5.3): the four length bytes, the four
# chunk type bytes, the data, and the four CRC bytes
type Chunk is Data:
  Chunk{
    +l0: U32, +l1: U32, +l2: U32, +l3: U32, +t0: U32, +t1: U32, +t2: U32, +t3: U32, +data: List<&2, U32>,
    +s0: U32, +s1: U32, +s2: U32, +s3: U32
  }

# four bytes read as one number, most significant byte first (PNG section 7.1)
def be.word(+aa: U32, +bb: U32, +cc: U32, +dd: U32) -> U32:
  ((((aa << 24n : U32) .|. (bb << 16n : U32) : U32) .|. (cc << 8n : U32) : U32) .|. dd : U32)

# a chunk's bytes, then rest
def chunk.onto(ck: Chunk, rest: List<&2, U32>) -> List<&2, U32>:
  match ck:
    case Chunk{l0, l1, l2, l3, t0, t1, t2, t3, data, s0, s1, s2, s3}:
      l0 <> l1 <> l2 <> l3 <> t0 <> t1 <> t2 <> t3 <> List.append(&2, U32, data, s0 <> s1 <> s2 <> s3 <> rest)

# chunks' bytes one after another, then rest
def chunks.onto(cs: List<&2, Chunk>, rest: List<&2, U32>) -> List<&2, U32>:
  match cs:
    case Nil{}:
      rest
    case ck <> tl:
      chunk.onto(ck, chunks.onto(tl, rest))

# the chunk's length field counts its data bytes
def chunk.framed(ck: Chunk) -> Type:
  match ck:
    case Chunk{l0, l1, l2, l3, _t0, _t1, _t2, _t3, data, _s0, _s1, _s2, _s3}:
      {U32.to_nat(be.word(l0, l1, l2, l3)) == List.length(&2, U32, data) : Nat}

# every chunk's length field counts its data bytes
def chunks.framed(cs: List<&2, Chunk>) -> Type:
  match cs:
    case Nil{}:
      Unit
    case ck <> tl:
      chunk.framed(ck) & chunks.framed(tl)

# the CRC a chunk stores
def chunk.stored(ck: Chunk) -> U32:
  match ck:
    case Chunk{_l0, _l1, _l2, _l3, _t0, _t1, _t2, _t3, _data, s0, s1, s2, s3}:
      be.word(s0, s1, s2, s3)

# the CRC-32 of a chunk's type and data
def chunk.sum(ck: Chunk) -> U32:
  match ck:
    case Chunk{_l0, _l1, _l2, _l3, t0, t1, t2, t3, data, _s0, _s1, _s2, _s3}:
      crc.ref(t0 <> t1 <> t2 <> t3 <> data)

# LAW: after the signature and any framed chunks, a framed chunk whose stored CRC differs from the CRC-32 of its type
# and data makes decode_png none, whatever follows
# IMG-PNG-5
law png_crc_refused:
  for +pre: List<&2, Chunk>
  for +bad: Chunk
  for +rest: List<&2, U32>
  for h_pre: chunks.framed(pre)
  for h_bad: chunk.framed(bad)
  for h_crc: {chunk.stored(bad) == chunk.sum(bad) : U32} -> Empty
  {Img.decode_png(List.append(&2, U32, Img.png_sig(), chunks.onto(pre, chunk.onto(bad, rest))))
    == None{} : Maybe<&2, Img.Raster>}

# ---- wp5-png-decode ----

# the four bytes of a U32, most significant first
def spec.be4(+nn: U32) -> List<&2, U32>:
  [U32.and(255, U32.shrn(nn, 24n)), U32.and(255, U32.shrn(nn, 16n)), U32.and(255, U32.shrn(nn, 8n)), U32.and(255, nn)]

# a PNG file whose first chunk is an IHDR: the signature, the length 13, the
# type IHDR, width, height, bit depth, colour type, compression, filter and
# interlace methods, any four CRC bytes, and any bytes after
def spec.ihdr.file(
  +ww: U32,
  +hh: U32,
  +dd: U32,
  +cc: U32,
  +comp: U32,
  +ff: U32,
  +ii: U32,
  +crc: U32,
  rest: List<&2, U32>
) -> List<&2, U32>:
  List.append(&2, U32, Img.png_sig(), List.append(&2, U32, [0, 0, 0, 13, 73, 72, 68, 82],
    List.append(&2, U32, spec.be4(ww), List.append(&2, U32, spec.be4(hh), List.append(&2, U32, [dd, cc, comp, ff, ii],
      List.append(&2, U32, spec.be4(crc), rest))))))

# the colour types the PNG specification defines for bit depth 8
def spec.colour.ok(+cc: U32) -> Bool:
  Bool.or(U32.is_eq(cc, 0), Bool.or(U32.is_eq(cc, 2), Bool.or(U32.is_eq(cc, 3), Bool.or(U32.is_eq(cc, 4),
    U32.is_eq(cc, 6)))))

# LAW: an IHDR whose bit depth is not 8 makes decode_png none, whatever the other fields, the CRC and the rest
# IMG-PNG-8
law png_depth_refused:
  for +ww: U32
  for +hh: U32
  for +dd: U32
  for +cc: U32
  for +comp: U32
  for +ff: U32
  for +ii: U32
  for +crc: U32
  for +rest: List<&2, U32>
  for h_dd: {U32.is_eq(dd, 8) == False{} : Bool}
  {Img.decode_png(spec.ihdr.file(ww, hh, dd, cc, comp, ff, ii, crc, rest)) == None{} : Maybe<&2, Img.Raster>}

# LAW: an IHDR whose interlace method is not 0 makes decode_png none, whatever the other fields, the CRC and the rest
# IMG-PNG-8
law png_interlace_refused:
  for +ww: U32
  for +hh: U32
  for +dd: U32
  for +cc: U32
  for +comp: U32
  for +ff: U32
  for +ii: U32
  for +crc: U32
  for +rest: List<&2, U32>
  for h_ii: {U32.is_eq(ii, 0) == False{} : Bool}
  {Img.decode_png(spec.ihdr.file(ww, hh, dd, cc, comp, ff, ii, crc, rest)) == None{} : Maybe<&2, Img.Raster>}

# LAW: an IHDR whose colour type is not 0, 2, 3, 4 or 6 makes decode_png none, whatever the other fields, the CRC
# and the rest
# IMG-PNG-8
law png_colour_refused:
  for +ww: U32
  for +hh: U32
  for +dd: U32
  for +cc: U32
  for +comp: U32
  for +ff: U32
  for +ii: U32
  for +crc: U32
  for +rest: List<&2, U32>
  for h_cc: {spec.colour.ok(cc) == False{} : Bool}
  {Img.decode_png(spec.ihdr.file(ww, hh, dd, cc, comp, ff, ii, crc, rest)) == None{} : Maybe<&2, Img.Raster>}

# a sample packed 0xAARRGGBB: alpha in the top byte, then red, green and blue
def spec.argb(+aa: U32, +rr: U32, +gg: U32, +bb: U32) -> U32:
  ((((aa << 24n : U32) .|. (rr << 16n : U32) : U32) .|. (gg << 8n : U32) : U32) .|. bb : U32)

# the alpha of a sample checked against a tRNS key: 0 when it matches, 255 otherwise
def spec.key.alpha(hit: Bool) -> U32:
  match hit:
    case True{}:
      0
    case False{}:
      255

# a list of samples, or none
def spec.cons(+hd: U32, mm: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match mm:
    case None{}:
      None{}
    case Some{tl}:
      Some{hd <> tl}

# colour type 0: each gray byte g is 0xFFgggggg
def spec.grey(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case +gg <> tl:
      spec.argb(255, gg, gg, gg) <> spec.grey(tl)

# colour type 0 with a tRNS key: a gray byte equal to the key has alpha 0
def spec.grey.key(xs: List<&2, U32>, +kk: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case +gg <> tl:
      spec.argb(spec.key.alpha(U32.is_eq(gg, kk)), gg, gg, gg) <> spec.grey.key(tl, kk)

# colour type 4: each gray and alpha pair is 0xAAgggggg; none when a pair is cut short
def spec.ga(xs: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case +gg <> +aa <> tl:
      spec.cons(spec.argb(aa, gg, gg, gg), spec.ga(tl))
    case _xs:
      None{}

# colour type 2: each RGB triple is 0xFFrrggbb; none when a triple is cut short
def spec.rgb(xs: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case +rr <> +gg <> +bb <> tl:
      spec.cons(spec.argb(255, rr, gg, bb), spec.rgb(tl))
    case _xs:
      None{}

# colour type 2 with a tRNS key: a triple equal to the key in all three channels has alpha 0
def spec.rgb.key(xs: List<&2, U32>, +kr: U32, +kg: U32, +kb: U32) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case +rr <> +gg <> +bb <> tl:
      spec.cons(spec.argb(spec.key.alpha(Bool.and(U32.is_eq(rr, kr), Bool.and(U32.is_eq(gg, kg), U32.is_eq(bb, kb)))),
        rr, gg, bb), spec.rgb.key(tl, kr, kg, kb))
    case _xs:
      None{}

# colour type 6: each RGBA quadruple is 0xAArrggbb; none when one is cut short
def spec.rgba(xs: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case +rr <> +gg <> +bb <> +aa <> tl:
      spec.cons(spec.argb(aa, rr, gg, bb), spec.rgba(tl))
    case _xs:
      None{}

# the palette: entry k is PLTE's triple k packed with alpha tRNS byte k, or
# 255 past the end of tRNS
def spec.pal(xs: List<&2, U32>, als: List<&2, U32>) -> List<&2, U32>:
  match xs als:
    case +rr <> +gg <> +bb <> tl Nil{}:
      spec.argb(255, rr, gg, bb) <> spec.pal(tl, [])
    case +rr <> +gg <> +bb <> tl +aa <> at:
      spec.argb(aa, rr, gg, bb) <> spec.pal(tl, at)
    case _xs _als:
      Nil{}

# one index's entry, if the palette has it, before the rest
def spec.idx.at(me: Maybe<&2, U32>, rest: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match me:
    case None{}:
      None{}
    case Some{+cc}:
      spec.cons(cc, rest)

# colour type 3: each index is its palette entry; none when an index is past the palette
def spec.idx(xs: List<&2, U32>, +pal: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case +ix <> tl:
      spec.idx.at(List.get(&2, U32, pal, U32.to_nat(ix)), spec.idx(tl, pal))

# LAW: colour type 0 without tRNS: each gray byte g decodes to 0xFFgggggg
# IMG-PNG-9
law png_px_grey:
  for +xs: List<&2, U32>
  {Png.px.of(0, xs, [], []) == Some{spec.grey(xs)} : Maybe<&2, List<&2, U32>>}

# LAW: colour type 0 with tRNS key k: each gray byte g decodes to 0xFFgggggg, alpha 0 when g is k
# IMG-PNG-9
law png_px_grey_key:
  for +xs: List<&2, U32>
  for +kk: U32
  {Png.px.of(0, xs, [], [0, kk]) == Some{spec.grey.key(xs, kk)} : Maybe<&2, List<&2, U32>>}

# LAW: colour type 4: each gray and alpha pair decodes to 0xAAgggggg
# IMG-PNG-9
law png_px_ga:
  for +xs: List<&2, U32>
  {Png.px.of(4, xs, [], []) == spec.ga(xs) : Maybe<&2, List<&2, U32>>}

# LAW: colour type 2 without tRNS: each RGB triple decodes to 0xFFrrggbb, whatever suggested palette there is
# IMG-PNG-9
law png_px_rgb:
  for +xs: List<&2, U32>
  for +plte: List<&2, U32>
  {Png.px.of(2, xs, plte, []) == spec.rgb(xs) : Maybe<&2, List<&2, U32>>}

# LAW: colour type 2 with tRNS key (kr, kg, kb): each triple decodes to 0xFFrrggbb, alpha 0 when it is the key
# IMG-PNG-9
law png_px_rgb_key:
  for +xs: List<&2, U32>
  for +plte: List<&2, U32>
  for +kr: U32
  for +kg: U32
  for +kb: U32
  {Png.px.of(2, xs, plte, [0, kr, 0, kg, 0, kb]) == spec.rgb.key(xs, kr, kg, kb) : Maybe<&2, List<&2, U32>>}

# LAW: colour type 6: each RGBA quadruple decodes to 0xAArrggbb, whatever suggested palette there is
# IMG-PNG-9
law png_px_rgba:
  for +xs: List<&2, U32>
  for +plte: List<&2, U32>
  {Png.px.of(6, xs, plte, []) == spec.rgba(xs) : Maybe<&2, List<&2, U32>>}

# LAW: colour type 3: when the indices decode, each is its palette entry with alpha from tRNS or 255
# IMG-PNG-9
law png_px_indexed:
  for +xs: List<&2, U32>
  for +plte: List<&2, U32>
  for +trns: List<&2, U32>
  for h_some: {Maybe.is_some(&2, List<&2, U32>, Png.px.of(3, xs, plte, trns)) == True{} : Bool}
  {Png.px.of(3, xs, plte, trns) == spec.idx(xs, spec.pal(plte, trns)) : Maybe<&2, List<&2, U32>>}

# the samples of the unfiltered bytes, when the scanlines unfilter
def spec.px.then(
  mm: Maybe<&2, List<&2, U32>>,
  +colour: U32,
  plte: List<&2, U32>,
  trns: List<&2, U32>
) -> Maybe<&2, List<&2, U32>>:
  match mm:
    case None{}:
      None{}
    case Some{raw}:
      Png.px.of(colour, raw, plte, trns)

# a picture of those samples, when there are some
def spec.pic(mm: Maybe<&2, List<&2, U32>>, +ww: U32, +hh: U32) -> Maybe<&2, Png.Pic>:
  match mm:
    case None{}:
      None{}
    case Some{px}:
      Some{Png.Pic{ww, hh, px}}

# LAW: the decoder's last stage packs the unfiltered bytes of the inflated IDAT data with px.of, for the IHDR's
# colour type, PLTE and tRNS, and keeps the width and height
# IMG-PNG-9
law png_samples_frame:
  for +raw: List<&2, U32>
  for +ww: U32
  for +hh: U32
  for +colour: U32
  for +plte: List<&2, U32>
  for +trns: List<&2, U32>
  {Png.png.samples(Some{raw}, ww, hh, colour, plte, trns) ==
    spec.pic(spec.px.then(Png.unfilter(raw, ww, hh, Png.png.bpp(colour)), colour, plte, trns), ww, hh)
    : Maybe<&2, Png.Pic>}
