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

# ---- wp8-jpeg-numeric ----

# a sampling factor IMG-JPG-2 allows: 1, 2 or 4
def jpg.fac(+ff: U32) -> Bool:
  Bool.or(U32.is_eq(ff, 1), Bool.or(U32.is_eq(ff, 2), U32.is_eq(ff, 4)))

# both sampling factors of one SOF component are allowed: H is the high
# nibble of its second byte and V the low nibble (T.81 B.2.2)
def jpg.facs(+hv: U32) -> Bool:
  Bool.and(jpg.fac(U32.shrn(hv, 4n)), jpg.fac(U32.and(hv, 15)))

# LAW: a SOF0 segment of one component whose sampling factor is outside 1, 2 and 4, met where a
# segment may start, makes decode_jpeg none, whatever came before and whatever follows
# IMG-JPG-2
law jpeg_refuse_factor1:
  for +pre: List<&2, U32>
  for +frame: Jpeg.Frame
  for +scan: Jpeg.Scan
  for +tabs: Jpeg.Tabs
  for +ent: List<&2, U32>
  for +ri: U32
  for +kind: U32
  for +bad: U32
  for h_walk: {Jpeg.decode.walk(pre, Jpeg.decode.st0()) == Jpeg.St{Jpeg.Seek{}, frame, scan, tabs, ent, ri, kind, bad} :
    Jpeg.St}
  for +yh: U32
  for +yl: U32
  for +xh: U32
  for +xl: U32
  for +c1: U32
  for +f1: U32
  for +q1: U32
  for h_fac: {jpg.facs(f1) == False{} : Bool}
  for +rest: List<&2, U32>
  {Img.decode_jpeg(List.append(&2, U32, pre, 255 <> 192 <> 0 <> 11 <> 8 <> yh <> yl <> xh <> xl <> 1 <> c1 <> f1 <>
    q1 <> rest)) == None{} : Maybe<&2, Img.Raster>}

# LAW: a SOF0 segment of three components, one of them with a sampling factor outside 1, 2 and 4,
# met where a segment may start, makes decode_jpeg none, whatever came before and whatever follows
# IMG-JPG-2
law jpeg_refuse_factor3:
  for +pre: List<&2, U32>
  for +frame: Jpeg.Frame
  for +scan: Jpeg.Scan
  for +tabs: Jpeg.Tabs
  for +ent: List<&2, U32>
  for +ri: U32
  for +kind: U32
  for +bad: U32
  for h_walk: {Jpeg.decode.walk(pre, Jpeg.decode.st0()) == Jpeg.St{Jpeg.Seek{}, frame, scan, tabs, ent, ri, kind, bad} :
    Jpeg.St}
  for +yh: U32
  for +yl: U32
  for +xh: U32
  for +xl: U32
  for +c1: U32
  for +f1: U32
  for +q1: U32
  for +c2: U32
  for +f2: U32
  for +q2: U32
  for +c3: U32
  for +f3: U32
  for +q3: U32
  for h_fac: {Bool.and(Bool.and(jpg.facs(f1), jpg.facs(f2)), jpg.facs(f3)) == False{} : Bool}
  for +rest: List<&2, U32>
  {Img.decode_jpeg(List.append(&2, U32, pre, 255 <> 192 <> 0 <> 17 <> 8 <> yh <> yl <> xh <> xl <> 3 <> c1 <> f1 <>
    q1 <> c2 <> f2 <> q2 <> c3 <> f3 <> q3 <> rest)) == None{} : Maybe<&2, Img.Raster>}

# the data unit at column bx and row by of a component's grid in MCU (mx, my): its pixel origin, and the
# hmax / hi by vmax / vi pixels each of its samples covers (pw, ph), in the frame of width ww and height hh
def jpg.unit(
  +mx: U32,
  +my: U32,
  +hmax: U32,
  +vmax: U32,
  +pw: U32,
  +ph: U32,
  +bx: U32,
  +by: U32,
  +ww: U32,
  +hh: U32
) -> Jpeg.Geom:
  Jpeg.Geom{(mx * hmax * 8 + bx * 8 * pw : U32), (my * vmax * 8 + by * 8 * ph : U32), pw, ph, ww, hh}

# one row of a component's grid in an MCU, left to right from column bx
def jpg.grid.row(
  cols: Nat,
  +bx: U32,
  +by: U32,
  +mx: U32,
  +my: U32,
  +hmax: U32,
  +vmax: U32,
  +pw: U32,
  +ph: U32,
  +ww: U32,
  +hh: U32
) -> List<&2, Jpeg.Geom>:
  match cols:
    case 0n:
      []
    case 1n+pp:
      jpg.unit(mx, my, hmax, vmax, pw, ph, bx, by, ww, hh) <>
        jpg.grid.row(pp, (bx + 1 : U32), by, mx, my, hmax, vmax, pw, ph, ww, hh)

# a component's hi by vi grid in an MCU as T.81 A.2.3 orders it: hi units to a row, rows top to bottom from row by
def jpg.grid(
  rows: Nat,
  +by: U32,
  +hi: U32,
  +mx: U32,
  +my: U32,
  +hmax: U32,
  +vmax: U32,
  +pw: U32,
  +ph: U32,
  +ww: U32,
  +hh: U32
) -> List<&2, Jpeg.Geom>:
  match rows:
    case 0n:
      []
    case 1n+pp:
      List.append(&2, Jpeg.Geom, jpg.grid.row(U32.to_nat(hi), 0, by, mx, my, hmax, vmax, pw, ph, ww, hh),
        jpg.grid(pp, (by + 1 : U32), hi, mx, my, hmax, vmax, pw, ph, ww, hh))

# where the decoder puts the component's data units bi, bi + 1, ..., in scan order, for a
# one-component scan whose component has factors hi and vi
def jpg.blocks(
  left: Nat,
  +bi: U32,
  +hi: U32,
  +vi: U32,
  +mx: U32,
  +my: U32,
  +hmax: U32,
  +vmax: U32,
  +ww: U32,
  +hh: U32
) -> List<&2, Jpeg.Geom>:
  match left:
    case 0n:
      []
    case 1n+pp:
      Jpeg.decode.geom.go(0, bi, mx, my, ww, hh, hmax, vmax, [0], [0], [hi], [vi]) <>
        jpg.blocks(pp, (bi + 1 : U32), hi, vi, mx, my, hmax, vmax, ww, hh)

# LAW: for sampling factors 1, 2 or 4, the decoder places a component's hi * vi data units of an MCU
# in T.81 A.2.3's order, hi to a row, each sample covering hmax / hi by vmax / vi pixels
# IMG-JPG-2
law jpeg_mcu_grid:
  for +hi: U32
  for +vi: U32
  for h_hi: {jpg.fac(hi) == True{} : Bool}
  for +h_vi: {jpg.fac(vi) == True{} : Bool}
  for +mx: U32
  for +my: U32
  for +hmax: U32
  for +vmax: U32
  for +ww: U32
  for +hh: U32
  {jpg.blocks(U32.to_nat((hi * vi : U32)), 0, hi, vi, mx, my, hmax, vmax, ww, hh) ==
    jpg.grid(U32.to_nat(vi), 0, hi, mx, my, hmax, vmax, U32.div(hmax, hi), U32.div(vmax, vi), ww, hh) :
    List<&2, Jpeg.Geom>}

# one pixel row of the pixels a sample covers: columns x0 + px onward, left pixels left. Each pixel is
# written by the decoder's own Jpeg.decode.splat.in, which writes a pixel only when it lies inside the frame
def jpg.cover.px(
  left: Nat,
  plane: Array<U32>,
  +x0: U32,
  +yy: U32,
  +px: U32,
  +ww: U32,
  +hh: U32,
  +vv: U32
) -> Array<U32>:
  match left:
    case 0n:
      plane
    case 1n+pp:
      jpg.cover.px(pp, Jpeg.decode.splat.in(U32.is_lt((x0 + px : U32), ww), U32.is_lt(yy, hh), plane, (x0 + px : U32),
        yy, ww, vv), x0, yy, (px + 1 : U32), ww, hh, vv)

# the pw by ph pixels one sample covers, from (x0, y0 + py), row by row
def jpg.cover.py(
  left: Nat,
  plane: Array<U32>,
  +x0: U32,
  +y0: U32,
  +py: U32,
  +pw: U32,
  +ww: U32,
  +hh: U32,
  +vv: U32
) -> Array<U32>:
  match left:
    case 0n:
      plane
    case 1n+pp:
      jpg.cover.py(pp, jpg.cover.px(U32.to_nat(pw), plane, x0, (y0 + py : U32), 0, ww, hh, vv), x0, y0, (py + 1 : U32),
        pw, ww, hh, vv)

# samples k = 8 * row + col onward of an 8 by 8 block, each replicated over the pw by ph pixels at
# (ox + col * pw, oy + row * ph): sample col to col 7 of this row, then the rows below
def jpg.cover.col(
  left: Nat,
  plane: Array<U32>,
  +samples: List<&2, U32>,
  +row: U32,
  +col: U32,
  +ox: U32,
  +oy: U32,
  +pw: U32,
  +ph: U32,
  +ww: U32,
  +hh: U32
) -> Array<U32>:
  match left:
    case 0n:
      plane
    case 1n+pp:
      jpg.cover.col(pp, jpg.cover.py(U32.to_nat(ph), plane, (ox + col * pw : U32), (oy + row * ph : U32), 0, pw, ww,
        hh, Jpeg.decode.at(samples, (row * 8 + col : U32))), samples, row, (col + 1 : U32), ox, oy, pw, ph, ww, hh)

# the eight rows of samples of a block, top to bottom from row
def jpg.cover(
  left: Nat,
  plane: Array<U32>,
  +samples: List<&2, U32>,
  +row: U32,
  +ox: U32,
  +oy: U32,
  +pw: U32,
  +ph: U32,
  +ww: U32,
  +hh: U32
) -> Array<U32>:
  match left:
    case 0n:
      plane
    case 1n+pp:
      jpg.cover(pp, jpg.cover.col(8n, plane, samples, row, 0, ox, oy, pw, ph, ww, hh), samples, (row + 1 : U32), ox,
        oy, pw, ph, ww, hh)

# LAW: painting one 8 by 8 block whose samples each cover pw by ph pixels, pw and ph each 1, 2 or 4, writes
# its sample k over the pw by ph pixels at (ox + (k mod 8) * pw, oy + (k div 8) * ph) that lie inside the
# frame, row by row, and nothing else
# IMG-JPG-2
law jpeg_block_cover:
  for +pw: U32
  for +ph: U32
  for +h_pw: {jpg.fac(pw) == True{} : Bool}
  for +h_ph: {jpg.fac(ph) == True{} : Bool}
  for +ox: U32
  for +oy: U32
  for +ww: U32
  for +hh: U32
  for +samples: List<&2, U32>
  for +nn: U32
  {Jpeg.decode.paint.use(Jpeg.Geom{ox, oy, pw, ph, ww, hh}, True{}, samples, Jpeg.decode.plane(nn)) ==
    jpg.cover(8n, Jpeg.decode.plane(nn), samples, 0, ox, oy, pw, ph, ww, hh) : Array<U32>}
