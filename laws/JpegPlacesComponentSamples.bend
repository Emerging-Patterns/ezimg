# For a SOF0 frame of at most 2^31 points whose components' sampling factors
# are each 1, 2 or 4, `decode_jpeg` places each component's samples in the
# order T.81 A.2.3 gives and replicates each sample over the pixels its
# sampling covers; for a factor outside 1, 2 and 4, `decode_jpeg` returns
# none. The sample values themselves are not proved: decoding them is
# trusted in src/jpeg.bend. This covers every sampling layout the frame
# parser accepts.
import Base
import ../main.bend as Img
import ../src/jpeg.bend as Jpeg
import ./defs/PointInside.bend as D1

# a sampling factor laws/JpegPlacesComponentSamples.bend allows: 1, 2 or 4
def jpg.fac(+ff: U32) -> Bool:
  Bool.or(U32.is_eq(ff, 1), Bool.or(U32.is_eq(ff, 2), U32.is_eq(ff, 4)))

# both sampling factors of one SOF component are allowed: H is the high
# nibble of its second byte and V the low nibble (T.81 B.2.2)
def jpg.facs(+hv: U32) -> Bool:
  Bool.and(jpg.fac(U32.shrn(hv, 4n)), jpg.fac(U32.and(hv, 15)))

# LAW: a SOF0 segment of one component whose sampling factor is outside 1, 2 and 4, met where a
# segment may start, makes decode_jpeg none, whatever came before and whatever follows
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

# LAW: painting one 8 by 8 block whose samples each cover pw by ph pixels, pw and ph each 1, 2 or 4 but not
# both 4, writes its sample k over the pw by ph pixels at (ox + (k mod 8) * pw, oy + (k div 8) * ph) that lie
# inside the frame, row by row, and nothing else. The 4 by 4 case is left out to keep the gate fast: its
# proof normalises 1024 nested writes and takes about 100 seconds on its own.
law jpeg_block_cover:
  for +pw: U32
  for +ph: U32
  for +h_pw: {jpg.fac(pw) == True{} : Bool}
  for +h_ph: {jpg.fac(ph) == True{} : Bool}
  for h_44: {Bool.and(U32.is_eq(pw, 4), U32.is_eq(ph, 4)) == False{} : Bool}
  for +ox: U32
  for +oy: U32
  for +ww: U32
  for +hh: U32
  for +samples: List<&2, U32>
  for +nn: U32
  {Jpeg.decode.paint.use(Jpeg.Geom{ox, oy, pw, ph, ww, hh}, True{}, samples, Jpeg.decode.plane(nn)) ==
    jpg.cover(8n, Jpeg.decode.plane(nn), samples, 0, ox, oy, pw, ph, ww, hh) : Array<U32>}

# three samples' colour, when all three are there
def jpg.rgb3(yy: Maybe<&2, U32>, bb: Maybe<&2, U32>, rr: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match yy:
    case None{}:
      None{}
    case Some{yv}:
      match bb:
        case None{}:
          None{}
        case Some{bv}:
          match rr:
            case None{}:
              None{}
            case Some{rv}:
              Some{Jpeg.rgb(yv, bv, rv)}

# LAW: the colour pass is pointwise: sample k of decode.rgbs is Jpeg.rgb of point k's Y, Cb and Cr,
# and there is no sample k when a plane has no point k
law jpeg_rgbs_at:
  for +ys: List<&2, U32>
  for +bs: List<&2, U32>
  for +rs: List<&2, U32>
  for +kk: Nat
  {List.get(&2, U32, Jpeg.decode.rgbs(ys, bs, rs), kk) ==
    jpg.rgb3(List.get(&2, U32, ys, kk), List.get(&2, U32, bs, kk), List.get(&2, U32, rs, kk)) : Maybe<&2, U32>}

# true when no element of xs is want
def jpg.absent(xs: List<&2, U32>, +want: U32) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case xx <> rest:
      Bool.and(Bool.not(U32.is_eq(xx, want)), jpg.absent(rest, want))

# nn plus the number of elements of xs, as a U32
def jpg.count(xs: List<&2, U32>, +nn: U32) -> U32:
  match xs:
    case Nil{}:
      nn
    case _xx <> rest:
      jpg.count(rest, (nn + 1 : U32))

# LAW: the frame component a scan component names is found at its first place in the frame's
# identifiers, so a component of a scan with several takes that frame component's factors and table
law jpeg_comp_index:
  for +pre: List<&2, U32>
  for +want: U32
  for +post: List<&2, U32>
  for +h_new: {jpg.absent(pre, want) == True{} : Bool}
  {Jpeg.decode.index(List.append(&2, U32, pre, want <> post), False{}, want, 0) == jpg.count(pre, 0) : U32}

# the data units the scan's component comp has in an MCU: its frame component's hi * vi
def jpg.units(+comp: U32, +sids: List<&2, U32>, +ids: List<&2, U32>, +hs: List<&2, U32>, +vs: List<&2, U32>) -> U32:
  +fi = Jpeg.decode.index(ids, False{}, Jpeg.decode.at(sids, comp), 0)
  (Jpeg.decode.at(hs, fi) * Jpeg.decode.at(vs, fi) : U32)

# LAW: the MCU walk goes from data unit bi of a scan component to unit bi + 1 of the same component
# while the component has more units in the MCU, with no restart between
law jpeg_walk_unit:
  for +comp: U32
  for +bi: U32
  for +mx: U32
  for +my: U32
  for +mcu: U32
  for +rst: U32
  for +ww: U32
  for +hh: U32
  for +nf: U32
  for +ids: List<&2, U32>
  for +hs: List<&2, U32>
  for +vs: List<&2, U32>
  for +tq: List<&2, U32>
  for +hmax: U32
  for +vmax: U32
  for +ns: U32
  for +sids: List<&2, U32>
  for +td: List<&2, U32>
  for +ta: List<&2, U32>
  for +ss: U32
  for +se: U32
  for +ah: U32
  for +ri: U32
  for h_more: {U32.is_lt((bi + 1 : U32), jpg.units(comp, sids, ids, hs, vs)) == True{} : Bool}
  {Jpeg.decode.adv(Jpeg.Ctrl{comp, bi, mx, my, mcu, rst}, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax},
    Jpeg.Scan{ns, sids, td, ta, ss, se, ah}, ri) ==
    Jpeg.Adv{Jpeg.Ctrl{comp, (bi + 1 : U32), mx, my, mcu, rst}, 0, rst} : Jpeg.Adv}

# LAW: after a scan component's last data unit in an MCU, the walk goes to unit 0 of the next scan
# component of the same MCU, with no restart between
law jpeg_walk_comp:
  for +comp: U32
  for +bi: U32
  for +mx: U32
  for +my: U32
  for +mcu: U32
  for +rst: U32
  for +ww: U32
  for +hh: U32
  for +nf: U32
  for +ids: List<&2, U32>
  for +hs: List<&2, U32>
  for +vs: List<&2, U32>
  for +tq: List<&2, U32>
  for +hmax: U32
  for +vmax: U32
  for +ns: U32
  for +sids: List<&2, U32>
  for +td: List<&2, U32>
  for +ta: List<&2, U32>
  for +ss: U32
  for +se: U32
  for +ah: U32
  for +ri: U32
  for h_last: {U32.is_lt((bi + 1 : U32), jpg.units(comp, sids, ids, hs, vs)) == False{} : Bool}
  for h_next: {U32.is_lt((comp + 1 : U32), ns) == True{} : Bool}
  {Jpeg.decode.adv(Jpeg.Ctrl{comp, bi, mx, my, mcu, rst}, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax},
    Jpeg.Scan{ns, sids, td, ta, ss, se, ah}, ri) == Jpeg.Adv{Jpeg.Ctrl{(comp + 1 : U32), 0, mx, my, mcu, rst}, 0, rst} :
    Jpeg.Adv}

# the scan component, data unit and MCU number the walk moves to
def jpg.adv.at(adv: Jpeg.Adv) -> U32 & U32 & U32:
  match adv:
    case Jpeg.Adv{ctrl, _due, _expect}:
      match ctrl:
        case Jpeg.Ctrl{comp, bi, _mx, _my, mcu, _rst}:
          (comp, bi, mcu)

# LAW: after the last data unit of the last scan component of MCU mcu, the walk goes to unit 0 of
# the first scan component of MCU mcu + 1
law jpeg_walk_mcu:
  for +comp: U32
  for +bi: U32
  for +mx: U32
  for +my: U32
  for +mcu: U32
  for +rst: U32
  for +ww: U32
  for +hh: U32
  for +nf: U32
  for +ids: List<&2, U32>
  for +hs: List<&2, U32>
  for +vs: List<&2, U32>
  for +tq: List<&2, U32>
  for +hmax: U32
  for +vmax: U32
  for +ns: U32
  for +sids: List<&2, U32>
  for +td: List<&2, U32>
  for +ta: List<&2, U32>
  for +ss: U32
  for +se: U32
  for +ah: U32
  for +ri: U32
  for h_last: {U32.is_lt((bi + 1 : U32), jpg.units(comp, sids, ids, hs, vs)) == False{} : Bool}
  for h_end: {U32.is_lt((comp + 1 : U32), ns) == False{} : Bool}
  {jpg.adv.at(Jpeg.decode.adv(Jpeg.Ctrl{comp, bi, mx, my, mcu, rst}, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax,
    vmax}, Jpeg.Scan{ns, sids, td, ta, ss, se, ah}, ri)) == (0, 0, (mcu + 1 : U32)) : U32 & U32 & U32}

# LAW: painting one 8 by 8 block whose samples each cover pw by ph pixels, for every pw and ph (4 by 4
# included) and onto any plane, one that earlier blocks painted included, writes its sample k over the
# pw by ph pixels at (ox + (k mod 8) * pw, oy + (k div 8) * ph) that lie inside the frame, row by row,
# and nothing else
law jpeg_block_cover_all:
  for +pw: U32
  for +ph: U32
  for +ox: U32
  for +oy: U32
  for +ww: U32
  for +hh: U32
  for +samples: List<&2, U32>
  for plane: Array<U32>
  {Jpeg.decode.paint.use(Jpeg.Geom{ox, oy, pw, ph, ww, hh}, True{}, samples, plane) ==
    jpg.cover(8n, plane, samples, 0, ox, oy, pw, ph, ww, hh) : Array<U32>}

# LAW: a SOF0 segment of one component whose sampling factor is outside 1, 2 and 4 makes decode_jpeg
# none, whatever came before its marker (fill bytes included), however much longer than the component
# its length field makes the segment, and whatever follows
law jpeg_refuse_factor1_any:
  for +pre: List<&2, U32>
  for +frame: Jpeg.Frame
  for +scan: Jpeg.Scan
  for +tabs: Jpeg.Tabs
  for +ent: List<&2, U32>
  for +ri: U32
  for +kind: U32
  for +bad: U32
  for h_walk: {Jpeg.decode.walk(pre, Jpeg.decode.st0()) == Jpeg.St{Jpeg.LenHi{192}, frame, scan, tabs, ent, ri, kind,
    bad} : Jpeg.St}
  for +lh: U32
  for +ll: U32
  for +yh: U32
  for +yl: U32
  for +xh: U32
  for +xl: U32
  for +c1: U32
  for +f1: U32
  for +q1: U32
  for +extra: List<&2, U32>
  for h_len: {U32.is_lt(Jpeg.decode.u16(lh, ll), 2) == False{} : Bool}
  for h_body: {U32.to_nat((Jpeg.decode.u16(lh, ll) - 2 : U32)) == List.length(&2, U32, List.append(&2, U32,
    [8, yh, yl, xh, xl, 1, c1, f1, q1], extra)) : Nat}
  for h_fac: {jpg.facs(f1) == False{} : Bool}
  for +rest: List<&2, U32>
  {Img.decode_jpeg(List.append(&2, U32, pre, lh <> ll <> List.append(&2, U32, List.append(&2, U32,
    [8, yh, yl, xh, xl, 1, c1, f1, q1], extra), rest))) == None{} : Maybe<&2, Img.Raster>}

# LAW: a SOF0 segment of three components, one of them with a sampling factor outside 1, 2 and 4,
# makes decode_jpeg none, whatever came before its marker (fill bytes included), however much longer
# than the components its length field makes the segment, and whatever follows
law jpeg_refuse_factor3_any:
  for +pre: List<&2, U32>
  for +frame: Jpeg.Frame
  for +scan: Jpeg.Scan
  for +tabs: Jpeg.Tabs
  for +ent: List<&2, U32>
  for +ri: U32
  for +kind: U32
  for +bad: U32
  for h_walk: {Jpeg.decode.walk(pre, Jpeg.decode.st0()) == Jpeg.St{Jpeg.LenHi{192}, frame, scan, tabs, ent, ri, kind,
    bad} : Jpeg.St}
  for +lh: U32
  for +ll: U32
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
  for +extra: List<&2, U32>
  for h_len: {U32.is_lt(Jpeg.decode.u16(lh, ll), 2) == False{} : Bool}
  for h_body: {U32.to_nat((Jpeg.decode.u16(lh, ll) - 2 : U32)) == List.length(&2, U32, List.append(&2, U32,
    [8, yh, yl, xh, xl, 3, c1, f1, q1, c2, f2, q2, c3, f3, q3], extra)) : Nat}
  for h_fac: {Bool.and(Bool.and(jpg.facs(f1), jpg.facs(f2)), jpg.facs(f3)) == False{} : Bool}
  for +rest: List<&2, U32>
  {Img.decode_jpeg(List.append(&2, U32, pre, lh <> ll <> List.append(&2, U32, List.append(&2, U32,
    [8, yh, yl, xh, xl, 3, c1, f1, q1, c2, f2, q2, c3, f3, q3], extra), rest))) == None{} : Maybe<&2, Img.Raster>}

# LAW: a SOF0 segment whose component count is neither 1 nor 3 makes decode_jpeg none, whatever its
# components and their sampling factors, whatever came before its marker and whatever follows; with the
# two laws above, a SOF0 frame with a factor outside 1, 2 and 4 is none for every component count
law jpeg_refuse_count:
  for +pre: List<&2, U32>
  for +frame: Jpeg.Frame
  for +scan: Jpeg.Scan
  for +tabs: Jpeg.Tabs
  for +ent: List<&2, U32>
  for +ri: U32
  for +kind: U32
  for +bad: U32
  for h_walk: {Jpeg.decode.walk(pre, Jpeg.decode.st0()) == Jpeg.St{Jpeg.LenHi{192}, frame, scan, tabs, ent, ri, kind,
    bad} : Jpeg.St}
  for +lh: U32
  for +ll: U32
  for +yh: U32
  for +yl: U32
  for +xh: U32
  for +xl: U32
  for +nf: U32
  for h_nf: {Bool.or(U32.is_eq(nf, 1), U32.is_eq(nf, 3)) == False{} : Bool}
  for +comps: List<&2, U32>
  for h_len: {U32.is_lt(Jpeg.decode.u16(lh, ll), 2) == False{} : Bool}
  for h_body: {U32.to_nat((Jpeg.decode.u16(lh, ll) - 2 : U32)) == List.length(&2, U32, 8 <> yh <> yl <> xh <> xl <>
    nf <> comps) : Nat}
  for +rest: List<&2, U32>
  {Img.decode_jpeg(List.append(&2, U32, pre, lh <> ll <> List.append(&2, U32, 8 <> yh <> yl <> xh <> xl <> nf <> comps,
    rest))) == None{} : Maybe<&2, Img.Raster>}

# the sampling factor in fs (hs or vs) of the frame component that scan component comp names: the
# first frame component whose identifier is the one the scan lists for comp (jpeg_comp_index)
def jpg.fac.of(+comp: U32, +sids: List<&2, U32>, +ids: List<&2, U32>, +fs: List<&2, U32>) -> U32:
  Jpeg.decode.at(fs, Jpeg.decode.index(ids, False{}, Jpeg.decode.at(sids, comp), 0))

# where the decoder puts data units bi, bi + 1, ... of scan component comp of a scan that lists the
# identifiers sids, in a frame whose components have identifiers ids and factors hs and vs
def jpg.blocks.of(
  left: Nat,
  +bi: U32,
  +comp: U32,
  +sids: List<&2, U32>,
  +ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>,
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
      Jpeg.decode.geom.go(comp, bi, mx, my, ww, hh, hmax, vmax, sids, ids, hs, vs) <>
        jpg.blocks.of(pp, (bi + 1 : U32), comp, sids, ids, hs, vs, mx, my, hmax, vmax, ww, hh)

# LAW: for every scan component, not only the frame's first, whose frame component has sampling factors
# hi and vi of 1, 2 or 4, the decoder places the component's hi * vi data units of an MCU in T.81
# A.2.3's order, hi to a row, each sample covering hmax / hi by vmax / vi pixels
law jpeg_mcu_grid_comp:
  for +comp: U32
  for +sids: List<&2, U32>
  for +ids: List<&2, U32>
  for +hs: List<&2, U32>
  for +vs: List<&2, U32>
  for h_hi: {jpg.fac(jpg.fac.of(comp, sids, ids, hs)) == True{} : Bool}
  for h_vi: {jpg.fac(jpg.fac.of(comp, sids, ids, vs)) == True{} : Bool}
  for +mx: U32
  for +my: U32
  for +hmax: U32
  for +vmax: U32
  for +ww: U32
  for +hh: U32
  {jpg.blocks.of(U32.to_nat((jpg.fac.of(comp, sids, ids, hs) * jpg.fac.of(comp, sids, ids, vs) : U32)), 0, comp, sids,
    ids, hs, vs, mx, my, hmax, vmax, ww, hh) == jpg.grid(U32.to_nat(jpg.fac.of(comp, sids, ids, vs)), 0,
    jpg.fac.of(comp, sids, ids, hs), mx, my, hmax, vmax, U32.div(hmax, jpg.fac.of(comp, sids, ids, hs)),
    U32.div(vmax, jpg.fac.of(comp, sids, ids, vs)), ww, hh) : List<&2, Jpeg.Geom>}

# LAW: the decoder reads a plane out point by point: sample k of the first nn points is the value
# Array.get finds at index k, for every plane and every k below nn
law jpeg_points_at:
  for +nn: Nat
  for plane: Array<U32>
  for +kk: U32
  for h_kk: {Nat.is_lt(U32.to_nat(kk), nn) == True{} : Bool}
  {List.get(&2, U32, Jpeg.decode.points(nn, plane), U32.to_nat(kk)) == Some{D1.jpg.val(Array.get(U32, plane, kk))} :
    Maybe<&2, U32>}

# jj advanced by one, kk times, in U32
def jpg.idx(kk: Nat, +jj: U32) -> U32:
  match kk:
    case 0n:
      jj
    case 1n+pp:
      jpg.idx(pp, (jj + 1 : U32))

# where a block sits in the walk: scan component, data unit, MCU column, MCU row and MCU number (the
# restart count left at 0)
def jpg.pos(ctrl: Jpeg.Ctrl) -> Jpeg.Ctrl:
  match ctrl:
    case Jpeg.Ctrl{comp, bi, mx, my, mcu, _rst}:
      Jpeg.Ctrl{comp, bi, mx, my, mcu, 0}

# the positions of the next left blocks the decoder walks to from ctrl, each step its own decode.adv
def jpg.trace(
  left: Nat,
  +ctrl: Jpeg.Ctrl,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +ri: U32
) -> List<&2, Jpeg.Ctrl>:
  match left:
    case 0n:
      []
    case 1n+pp:
      jpg.pos(ctrl) <> jpg.trace(pp, Jpeg.decode.adv.ctrl(Jpeg.decode.adv(ctrl, frame, scan, ri)), frame, scan, ri)

# T.81 A.2.3: data units bi onward of scan component comp in MCU (mx, my), number mcu
def jpg.o.units(
  left: Nat,
  +comp: U32,
  +bi: U32,
  +mx: U32,
  +my: U32,
  +mcu: U32
) -> List<&2, Jpeg.Ctrl>:
  match left:
    case 0n:
      []
    case 1n+pp:
      Jpeg.Ctrl{comp, bi, mx, my, mcu, 0} <> jpg.o.units(pp, comp, (bi + 1 : U32), mx, my, mcu)

# scan components comp onward of one MCU, each with its frame component's hi * vi data units
def jpg.o.comps(
  left: Nat,
  +comp: U32,
  +mx: U32,
  +my: U32,
  +mcu: U32,
  +sids: List<&2, U32>,
  +ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>
) -> List<&2, Jpeg.Ctrl>:
  match left:
    case 0n:
      []
    case 1n+pp:
      List.append(&2, Jpeg.Ctrl, jpg.o.units(U32.to_nat(jpg.units(comp, sids, ids, hs, vs)), comp, 0,
        mx, my, mcu), jpg.o.comps(pp, (comp + 1 : U32), mx, my, mcu, sids, ids, hs, vs))

# MCUs mx onward of MCU row my, left to right, numbered from mcu, each with the scan's components in order
def jpg.o.row(
  left: Nat,
  +mx: U32,
  +my: U32,
  +mcu: U32,
  +ns: U32,
  +sids: List<&2, U32>,
  +ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>
) -> List<&2, Jpeg.Ctrl>:
  match left:
    case 0n:
      []
    case 1n+pp:
      List.append(&2, Jpeg.Ctrl, jpg.o.comps(U32.to_nat(ns), 0, mx, my, mcu, sids, ids, hs, vs),
        jpg.o.row(pp, (mx + 1 : U32), my, (mcu + 1 : U32), ns, sids, ids, hs, vs))

# MCU rows my onward, top to bottom, mw MCUs to a row, numbered from mcu
def jpg.o.rows(
  left: Nat,
  +my: U32,
  +mcu: U32,
  +mw: U32,
  +ns: U32,
  +sids: List<&2, U32>,
  +ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>
) -> List<&2, Jpeg.Ctrl>:
  match left:
    case 0n:
      []
    case 1n+pp:
      List.append(&2, Jpeg.Ctrl, jpg.o.row(U32.to_nat(mw), 0, my, mcu, ns, sids, ids, hs, vs),
        jpg.o.rows(pp, (my + 1 : U32), jpg.idx(U32.to_nat(mw), mcu), mw, ns, sids, ids, hs, vs))

# ok, and every scan component from comp on, left of them, has at least one data unit
def jpg.units.ok(
  left: Nat,
  +comp: U32,
  +sids: List<&2, U32>,
  +ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>,
  ok: Bool
) -> Bool:
  match left:
    case 0n:
      ok
    case 1n+pp:
      jpg.units.ok(pp, (comp + 1 : U32), sids, ids, hs, vs, Bool.and(ok, U32.is_lt(0, jpg.units(comp, sids, ids, hs,
        vs))))

# LAW: from the first block of a scan, the decoder's walk (its own decode.adv at every step) visits the
# frame's MCUs in raster order, mw = ceil(w / 8 hmax) to a row and any number of rows, and inside each MCU
# the scan's components in order, each component's hi * vi data units in order (T.81 A.2.1 and A.2.3).
# The U32 counters for the data unit, the component and the MCU column never wrap: each stays below the
# count it is compared with, and the MCU row and number count up in step with the order's own.
law jpeg_walk_frame:
  for +ww: U32
  for +hh: U32
  for +nf: U32
  for +ids: List<&2, U32>
  for +hs: List<&2, U32>
  for +vs: List<&2, U32>
  for +tq: List<&2, U32>
  for +hmax: U32
  for +vmax: U32
  for +ns: U32
  for +sids: List<&2, U32>
  for +td: List<&2, U32>
  for +ta: List<&2, U32>
  for +ss: U32
  for +se: U32
  for +ah: U32
  for +ri: U32
  for +rst: U32
  for +mh: U32
  for h_ns: {U32.is_lt(0, ns) == True{} : Bool}
  for h_mw: {U32.is_lt(0, Jpeg.decode.ceil(ww, (hmax * 8 : U32))) == True{} : Bool}
  for h_units: {jpg.units.ok(U32.to_nat(ns), 0, sids, ids, hs, vs, True{}) == True{} : Bool}
  {jpg.trace(List.length(&2, Jpeg.Ctrl, jpg.o.rows(U32.to_nat(mh), 0, 0, Jpeg.decode.ceil(ww,
    (hmax * 8 : U32)), ns, sids, ids, hs, vs)), Jpeg.Ctrl{0, 0, 0, 0, 0, rst}, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq,
    hmax, vmax}, Jpeg.Scan{ns, sids, td, ta, ss, se, ah}, ri) == jpg.o.rows(U32.to_nat(mh), 0, 0,
    Jpeg.decode.ceil(ww, (hmax * 8 : U32)), ns, sids, ids, hs, vs) : List<&2, Jpeg.Ctrl>}

# the data units of the scan's components from comp on, left of them: each one's hi * vi, summed
def jpg.usum(
  left: Nat,
  +comp: U32,
  +sids: List<&2, U32>,
  +ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>
) -> Nat:
  match left:
    case 0n:
      0n
    case 1n+pp:
      Nat.add(U32.to_nat(jpg.units(comp, sids, ids, hs, vs)), jpg.usum(pp, (comp + 1 : U32), sids, ids, hs, vs))

# LAW: the number of blocks the decoder reads, decode.nblocks (ceil(w / 8 hmax) * ceil(h / 8 vmax) MCUs times
# the frame's data units per MCU, all in U32), is the length of jpeg_walk_frame's order over ceil(h / 8 vmax) MCU rows,
# when the scan's components carry the frame's data units and the product fits a U32 (the witness top), so
# the walk visits every MCU of the frame and no counter wraps
law jpeg_walk_count:
  for +ww: U32
  for +hh: U32
  for +ids: List<&2, U32>
  for +hs: List<&2, U32>
  for +vs: List<&2, U32>
  for +hmax: U32
  for +vmax: U32
  for +ns: U32
  for +sids: List<&2, U32>
  for +top: U32
  for h_ns: {U32.is_lt(0, ns) == True{} : Bool}
  for h_units: {jpg.units.ok(U32.to_nat(ns), 0, sids, ids, hs, vs, True{}) == True{} : Bool}
  for h_sum: {U32.to_nat(Jpeg.decode.blocks.sum(hs, vs, 0)) == jpg.usum(U32.to_nat(ns), 0, sids, ids, hs, vs) : Nat}
  for h_fit: {Nat.is_le(Nat.mul(Nat.mul(U32.to_nat(Jpeg.decode.ceil(ww, (hmax * 8 : U32))),
    U32.to_nat(Jpeg.decode.ceil(hh, (vmax * 8 : U32)))), jpg.usum(U32.to_nat(ns), 0, sids, ids, hs, vs)),
    U32.to_nat(top)) == True{} : Bool}
  {U32.to_nat(Jpeg.decode.nblocks(ww, hh, hs, vs, hmax, vmax)) == List.length(&2, Jpeg.Ctrl,
    jpg.o.rows(U32.to_nat(Jpeg.decode.ceil(hh, (vmax * 8 : U32))), 0, 0, Jpeg.decode.ceil(ww, (hmax * 8 : U32)), ns,
    sids, ids, hs, vs)) : Nat}

# a plane is a perfect binary tree of 2^d leaves, every leaf d nodes down, as decode.plane builds it
def jpg.perfect(+dd: Nat, aa: Array<U32>) -> Bool:
  match dd aa:
    case 0n ALeaf{_xx}:
      True{}
    case 0n ANode{_xs, _ys}:
      False{}
    case 1n+_ee ALeaf{_xx}:
      False{}
    case 1n+ee ANode{xs, ys}:
      +pl = jpg.perfect(ee, xs)
      +ph = jpg.perfect(ee, ys)
      Bool.and(pl, ph)

# LAW: Array.get at an index finds the value the last Array.set at that index wrote, in any array
law jpeg_get_set:
  for plane: Array<U32>
  for +ii: U32
  for +vv: U32
  {D1.jpg.val(Array.get(U32, Array.set(U32, plane, ii, vv), ii)) == vv : U32}

# LAW: on a plane that is a perfect binary tree of 2^d leaves, d below 32, an Array.set at one index below 2^d
# leaves what Array.get finds at another index below 2^d
law jpeg_get_set_other:
  for +dd: Nat
  for plane: Array<U32>
  for h_perfect: {jpg.perfect(dd, plane) == True{} : Bool}
  for h_dd: {Nat.is_lt(dd, 32n) == True{} : Bool}
  for +ii: U32
  for +jj: U32
  for +vv: U32
  for h_ii: {Nat.is_lt(U32.to_nat(ii), Nat.pow(2n, dd)) == True{} : Bool}
  for h_jj: {Nat.is_lt(U32.to_nat(jj), Nat.pow(2n, dd)) == True{} : Bool}
  for h_ne: {U32.is_eq(ii, jj) == False{} : Bool}
  {D1.jpg.val(Array.get(U32, Array.set(U32, plane, ii, vv), jj)) == D1.jpg.val(Array.get(U32, plane, jj)) : U32}

# whether xx is one of the left coordinates x0 + pp, x0 + pp + 1, ..., added in U32 as the decoder adds them
def jpg.span(left: Nat, +x0: U32, +pp: U32, +xx: U32) -> Bool:
  match left:
    case 0n:
      False{}
    case 1n+rest:
      +here = U32.is_eq((x0 + pp : U32), xx)
      +more = jpg.span(rest, x0, (pp + 1 : U32), xx)
      Bool.or(here, more)

# whether sample (row, col) of a block at (ox, oy), each sample covering pw by ph pixels, covers pixel (xx, yy):
# the pw pixels from ox + col * pw across and the ph pixels from oy + row * ph down
def jpg.covers(+row: U32, +col: U32, +ox: U32, +oy: U32, +pw: U32, +ph: U32, +xx: U32, +yy: U32) -> Bool:
  Bool.and(jpg.span(U32.to_nat(pw), (ox + col * pw : U32), 0, xx), jpg.span(U32.to_nat(ph), (oy + row * ph : U32), 0,
    yy))

# the value pixel (xx, yy) holds once samples col onward of a block row are painted over a plane where it held acc:
# each sample that covers the pixel replaces the value, in the order of the samples
def jpg.blk.col(
  left: Nat,
  +samples: List<&2, U32>,
  +row: U32,
  +col: U32,
  +ox: U32,
  +oy: U32,
  +pw: U32,
  +ph: U32,
  +xx: U32,
  +yy: U32,
  +acc: U32
) -> U32:
  match left:
    case 0n:
      acc
    case 1n+pp:
      jpg.blk.col(pp, samples, row, (col + 1 : U32), ox, oy, pw, ph, xx, yy, Bool.pick(U32, jpg.covers(row, col, ox, oy,
        pw, ph, xx, yy), Jpeg.decode.at(samples, (row * 8 + col : U32)), acc))

# the value pixel (xx, yy) holds once rows row onward of a block are painted over a plane where it held acc
def jpg.blk(
  left: Nat,
  +samples: List<&2, U32>,
  +row: U32,
  +ox: U32,
  +oy: U32,
  +pw: U32,
  +ph: U32,
  +xx: U32,
  +yy: U32,
  +acc: U32
) -> U32:
  match left:
    case 0n:
      acc
    case 1n+pp:
      jpg.blk(pp, samples, (row + 1 : U32), ox, oy, pw, ph, xx, yy, jpg.blk.col(8n, samples, row, 0, ox, oy, pw, ph, xx,
        yy, acc))

# the value pixel (xx, yy) holds once a block is painted at gg over a plane where it held acc: the block's sample
# k = 8 * row + col, the last in that order whose pw by ph pixels at (ox + col * pw, oy + row * ph) take in the
# pixel, or acc when none does
def jpg.block.at(gg: Jpeg.Geom, +samples: List<&2, U32>, +xx: U32, +yy: U32, +acc: U32) -> U32:
  match gg:
    case Jpeg.Geom{+ox, +oy, +pw, +ph, _ww, _hh}:
      jpg.blk(8n, samples, 0, ox, oy, pw, ph, xx, yy, acc)

# LAW: painting a block onto a plane that is a perfect binary tree of 2^d leaves, d below 32, the frame's
# w * h points at most 2^d, leaves at pixel (x, y) of the frame, point y * w + x, the sample of the block whose
# pixels take it in, the last in the block's order, and what the point held before when no sample's do
law jpeg_paint_at:
  for +dd: Nat
  for plane: Array<U32>
  for h_perfect: {jpg.perfect(dd, plane) == True{} : Bool}
  for h_dd: {Nat.is_lt(dd, 32n) == True{} : Bool}
  for +ox: U32
  for +oy: U32
  for +pw: U32
  for +ph: U32
  for +ww: U32
  for +hh: U32
  for +samples: List<&2, U32>
  for h_fit: {Nat.is_le(Nat.mul(U32.to_nat(ww), U32.to_nat(hh)), Nat.pow(2n, dd)) == True{} : Bool}
  for +xx: U32
  for +yy: U32
  for h_xx: {U32.is_lt(xx, ww) == True{} : Bool}
  for h_yy: {U32.is_lt(yy, hh) == True{} : Bool}
  {D1.jpg.val(Array.get(U32, Jpeg.decode.paint.use(Jpeg.Geom{ox, oy, pw, ph, ww, hh}, True{}, samples, plane),
    (yy * ww + xx : U32))) == jpg.block.at(Jpeg.Geom{ox, oy, pw, ph, ww, hh}, samples, xx, yy, D1.jpg.val(Array.get(U32,
    plane, (yy * ww + xx : U32)))) : U32}

# LAW: the depth decode.plane takes for nn points, 1 to 2^d with d at most 31, is below 32, and the plane's 2^depth
# leaves are at least nn: every point has a leaf of its own, 2^31 points, where U32 shl wraps, included
law jpeg_plane_depth:
  for +nn: U32
  for +dd: Nat
  for h_pos: {Nat.is_lt(0n, U32.to_nat(nn)) == True{} : Bool}
  for h_dd: {Nat.is_le(dd, 31n) == True{} : Bool}
  for h_nn: {Nat.is_le(U32.to_nat(nn), Nat.pow(2n, dd)) == True{} : Bool}
  {Bool.and(Nat.is_lt(Jpeg.decode.depth(nn), 32n), Nat.is_le(U32.to_nat(nn), Nat.pow(2n, Jpeg.decode.depth(nn)))) ==
    True{} : Bool}

# a data unit the decoder decoded: where the walk had it and its 64 samples (values trusted in src/jpeg.bend)
type JUnit is Data:
  JUnit{ctrl: Jpeg.Ctrl, samples: List<&2, U32>}

# the samples of the data units decode.blocks decodes, the unit in blk and left more after it, in the order it
# decodes them (values trusted in src/jpeg.bend)
def jpg.samples.run(
  left: Nat,
  blk: Jpeg.Blk,
  +ctrl: Jpeg.Ctrl,
  +preds: Jpeg.Preds,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ri: U32
) -> List<&2, List<&2, U32>>:
  match left:
    case 0n:
      match blk:
        case Jpeg.Blk{+samples, _bits, _pred, _bok}:
          [samples]
    case 1n+pp:
      match blk:
        case Jpeg.Blk{+samples, +bits, +pred, _bok}:
          match ctrl:
            case Jpeg.Ctrl{+comp, _bi, _mx, _my, _mcu, _rst}:
              samples <> jpg.samples.run(pp, Jpeg.decode.block.next(bits, preds, pred, ctrl, frame, scan, tabs, ri),
                Jpeg.decode.adv.ctrl(Jpeg.decode.adv(ctrl, frame, scan, ri)),
                Jpeg.decode.preds.next(Jpeg.decode.adv.duef(Jpeg.decode.adv(ctrl, frame, scan, ri)), preds, comp, pred),
                frame, scan, tabs, ri)

# places and samples, paired in order, as many as the shorter list holds
def jpg.zip(ps: List<&2, Jpeg.Ctrl>, ss: List<&2, List<&2, U32>>) -> List<&2, JUnit>:
  match ps ss:
    case Nil{} _ss:
      []
    case _pc <> _pt Nil{}:
      []
    case pc <> pt sc <> st:
      JUnit{pc, sc} <> jpg.zip(pt, st)

# the data units decode.blocks decodes from blk on, left more after it: the k-th at the k-th place the decoder's walk
# visits (jpg.trace, which jpeg_walk_frame shows is T.81 A.2.3's order), with the k-th unit's samples
def jpg.units.run(
  +left: Nat,
  +blk: Jpeg.Blk,
  +ctrl: Jpeg.Ctrl,
  +preds: Jpeg.Preds,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ri: U32
) -> List<&2, JUnit>:
  jpg.zip(jpg.trace(1n+left, ctrl, frame, scan, ri), jpg.samples.run(left, blk, ctrl, preds, frame, scan, tabs, ri))

# the ok flag decode.blocks ends with: ok times every decoded unit's
def jpg.run.ok(
  left: Nat,
  blk: Jpeg.Blk,
  +ctrl: Jpeg.Ctrl,
  +preds: Jpeg.Preds,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ri: U32,
  +ok: U32
) -> U32:
  match left:
    case 0n:
      match blk:
        case Jpeg.Blk{_samples, _bits, _pred, +bok}:
          (ok * bok : U32)
    case 1n+pp:
      match blk:
        case Jpeg.Blk{_samples, +bits, +pred, +bok}:
          match ctrl:
            case Jpeg.Ctrl{+comp, _bi, _mx, _my, _mcu, _rst}:
              jpg.run.ok(pp, Jpeg.decode.block.next(bits, preds, pred, ctrl, frame, scan, tabs, ri),
                Jpeg.decode.adv.ctrl(Jpeg.decode.adv(ctrl, frame, scan, ri)),
                Jpeg.decode.preds.next(Jpeg.decode.adv.duef(Jpeg.decode.adv(ctrl, frame, scan, ri)), preds, comp, pred),
                frame, scan, tabs, ri, (ok * bok : U32))

# a plane with the units of scan component comp painted in order, each at decode.geom of its place
def jpg.paint.all(
  us: List<&2, JUnit>,
  +comp: U32,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  plane: Array<U32>
) -> Array<U32>:
  match us:
    case Nil{}:
      plane
    case JUnit{+ctrl, +samples} <> rest:
      jpg.paint.all(rest, comp, frame, scan, Jpeg.decode.paint.use(Jpeg.decode.geom(ctrl, frame, scan),
        U32.is_eq(Jpeg.decode.ctrl.comp(ctrl), comp), samples, plane))

# the value pixel (xx, yy) holds once the units of scan component comp are painted in order over a plane where it
# held acc: each unit's block, at decode.geom of its place, as jpg.block.at says
def jpg.point(
  us: List<&2, JUnit>,
  +comp: U32,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +xx: U32,
  +yy: U32,
  +acc: U32
) -> U32:
  match us:
    case Nil{}:
      acc
    case JUnit{+ctrl, +samples} <> rest:
      jpg.point(rest, comp, frame, scan, xx, yy, Bool.pick(U32, U32.is_eq(Jpeg.decode.ctrl.comp(ctrl), comp),
        jpg.block.at(Jpeg.decode.geom(ctrl, frame, scan), samples, xx, yy, acc), acc))

# LAW: decode.blocks paints the k-th unit it decodes at decode.geom of the k-th place its walk visits (jpg.trace), onto
# the plane of that place's scan component (0 Y, 1 Cb, 2 Cr), and hands the three planes to decode.done
law jpeg_blocks_paint:
  for +left: Nat
  for +blk: Jpeg.Blk
  for +ctrl: Jpeg.Ctrl
  for +preds: Jpeg.Preds
  for +frame: Jpeg.Frame
  for +scan: Jpeg.Scan
  for +tabs: Jpeg.Tabs
  for +ri: U32
  for yy: Array<U32>
  for cb: Array<U32>
  for cr: Array<U32>
  for +ok: U32
  {Jpeg.decode.blocks(left, blk, ctrl, preds, frame, scan, tabs, ri, yy, cb, cr, ok) ==
    Jpeg.decode.done(jpg.run.ok(left, blk, ctrl, preds, frame, scan, tabs, ri, ok), frame,
    jpg.paint.all(jpg.units.run(left, blk, ctrl, preds, frame, scan, tabs, ri), 0, frame, scan, yy),
    jpg.paint.all(jpg.units.run(left, blk, ctrl, preds, frame, scan, tabs, ri), 1, frame, scan, cb),
    jpg.paint.all(jpg.units.run(left, blk, ctrl, preds, frame, scan, tabs, ri), 2, frame, scan, cr)) :
    Maybe<&2, Jpeg.Pic>}

# LAW: painting a scan component's units onto a plane that is a perfect binary tree of 2^d leaves, d below 32, the
# frame's w * h points at most 2^d, leaves at pixel (x, y) of the frame, point y * w + x, the value jpg.point gives:
# each unit's sample whose pixels take the pixel in, the last in order, over what the point held before
law jpeg_plane_at:
  for +dd: Nat
  for plane: Array<U32>
  for h_perfect: {jpg.perfect(dd, plane) == True{} : Bool}
  for h_dd: {Nat.is_lt(dd, 32n) == True{} : Bool}
  for +us: List<&2, JUnit>
  for +comp: U32
  for +ww: U32
  for +hh: U32
  for +nf: U32
  for +ids: List<&2, U32>
  for +hs: List<&2, U32>
  for +vs: List<&2, U32>
  for +tq: List<&2, U32>
  for +hmax: U32
  for +vmax: U32
  for +scan: Jpeg.Scan
  for h_fit: {Nat.is_le(Nat.mul(U32.to_nat(ww), U32.to_nat(hh)), Nat.pow(2n, dd)) == True{} : Bool}
  for +xx: U32
  for +yy: U32
  for h_xx: {U32.is_lt(xx, ww) == True{} : Bool}
  for h_yy: {U32.is_lt(yy, hh) == True{} : Bool}
  {D1.jpg.val(Array.get(U32, jpg.paint.all(us, comp, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, plane),
    (yy * ww + xx : U32))) == jpg.point(us, comp, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy,
    D1.jpg.val(Array.get(U32, plane, (yy * ww + xx : U32)))) : U32}

# the data units a scan decode of nb blocks decodes: none for no blocks, else from the scan's first block, at the
# walk's first place, the DC predictors zero
def jpg.decoded.n(
  nb: Nat,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32
) -> List<&2, JUnit>:
  match nb:
    case 0n:
      []
    case 1n+pp:
      jpg.units.run(pp, Jpeg.decode.block.of(Jpeg.Bits{0, 1, 0, ent}, 0, Jpeg.decode.pred.zero(), frame, scan, tabs),
        Jpeg.Ctrl{0, 0, 0, 0, 0, 0}, Jpeg.decode.pred.zero(), frame, scan, tabs, ri)

# the data units decode_jpeg decodes from the entropy-coded bytes ent of a scan in a frame: decode.nblocks of them
def jpg.decoded(
  +ww: U32,
  +hh: U32,
  +nf: U32,
  +ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>,
  +tq: List<&2, U32>,
  +hmax: U32,
  +vmax: U32,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32
) -> List<&2, JUnit>:
  jpg.decoded.n(U32.to_nat(Jpeg.decode.nblocks(ww, hh, hs, vs, hmax, vmax)), Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq,
    hmax,
    vmax}, scan, tabs, ent, ri)

# a pixel from its Y, Cb and Cr: gray for a frame of one component, else the T.871 colour (trusted in src/jpeg.bend)
def jpg.colour(+nf: U32, +yv: U32, +bv: U32, +rv: U32) -> U32:
  Bool.pick(U32, U32.is_eq(nf, 1), Jpeg.gray(yv), Jpeg.rgb(yv, bv, rv))

# sample kk of a decoded raster, if any
def jpg.px.at(mm: Maybe<&2, Img.Raster>, +kk: Nat) -> Maybe<&2, U32>:
  match mm:
    case None{}:
      None{}
    case Some{Img.Raster{_ww, _hh, px}}:
      List.get(&2, U32, px, kk)

# vv, when there is a decoded raster
def jpg.px.want(mm: Maybe<&2, Img.Raster>, +vv: U32) -> Maybe<&2, U32>:
  match mm:
    case None{}:
      None{}
    case Some{_rr}:
      Some{vv}

# LAW: for a SOF0 frame of at most 2^31 points (w * h at most 2^d, d at most
# 31), whatever the bytes before and the scan, when decode_jpeg returns a
# raster, its pixel (x, y) is the pixel of the component values at (x, y):
# gray of Y for one component, else rgb of Y, Cb and Cr. Each component's
# value is jpg.point over the data units the decoder decodes, their samples
# as src/jpeg.bend decodes them (trusted there): the k-th unit placed at
# decode.geom of the k-th place of the decoder's walk (jpg.trace;
# jpeg_walk_frame: T.81 A.2.3's order; jpeg_mcu_grid_comp: the A.2.3 grid),
# each of its samples replicated over the pw by ph pixels it covers
# (jpg.block.at, jpeg_paint_at)
law jpeg_place:
  for +bytes: List<&2, U32>
  for +ww: U32
  for +hh: U32
  for +nf: U32
  for +ids: List<&2, U32>
  for +hs: List<&2, U32>
  for +vs: List<&2, U32>
  for +tq: List<&2, U32>
  for +hmax: U32
  for +vmax: U32
  for +scan: Jpeg.Scan
  for +tabs: Jpeg.Tabs
  for +ent: List<&2, U32>
  for +ri: U32
  for +kind: U32
  for +bad: U32
  for h_walk: {Jpeg.decode.walk(bytes, Jpeg.decode.st0()) == Jpeg.St{Jpeg.Stop{}, Jpeg.Frame{ww, hh, nf, ids, hs, vs,
    tq,
    hmax, vmax}, scan, tabs, ent, ri, kind, bad} : Jpeg.St}
  for +dd: Nat
  for +h_dd: {Nat.is_le(dd, 31n) == True{} : Bool}
  for +h_fit: {Nat.is_le(Nat.mul(U32.to_nat(ww), U32.to_nat(hh)), Nat.pow(2n, dd)) == True{} : Bool}
  for +xx: U32
  for +yy: U32
  for +h_xx: {U32.is_lt(xx, ww) == True{} : Bool}
  for +h_yy: {U32.is_lt(yy, hh) == True{} : Bool}
  {jpg.px.at(Img.decode_jpeg(bytes), U32.to_nat((yy * ww + xx : U32))) == jpg.px.want(Img.decode_jpeg(bytes),
    jpg.colour(nf, jpg.point(jpg.decoded(ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan, tabs, List.reverse(&2, U32,
    ent),
    ri), 0, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy, 0), jpg.point(jpg.decoded(ww, hh, nf,
    ids,
    hs, vs, tq, hmax, vmax, scan, tabs, List.reverse(&2, U32, ent), ri), 1, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq,
    hmax,
    vmax}, scan, xx, yy, 0), jpg.point(jpg.decoded(ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan, tabs, List.reverse(&2,
    U32, ent), ri), 2, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy, 0))) : Maybe<&2, U32>}
