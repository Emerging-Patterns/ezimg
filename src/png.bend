# src/png: PNG decode and encode (ISO/IEC 15948 / W3C PNG). Chunks, IHDR,
# zlib method 0, and filter method 0. Decode reads every colour type and bit
# depth of PNG table 11.1, interlace methods 0 and Adam7. Encode writes colour
# type 2 or 6, filter None, and a stored IDAT.
import Base
import ./crc.bend as Crc
import ./inflate.bend as Inf

# a decoded picture: width, height, and 0xAARRGGBB samples
type Pic is Data:
  Pic{+w: U32, +h: U32, px: List<&2, U32>}

# IHDR fields, in specification order
type Ihdr is Data:
  Ihdr{+w: U32, +h: U32, +depth: U32, +colour: U32, +comp: U32, +filter: U32, +inter: U32}

# chunk reader phase
type Pz is Data:
  ZLen{}
  ZTyp{}
  ZDat{}
  ZCrc{}

# where the IDAT chunks are (PNG section 5.6: they are consecutive): none
# yet, a run still open, or a run a later chunk has closed
type Run is Data:
  RNone{}
  ROpen{}
  RShut{}

# image state while chunks are read: before IHDR, or after it with the IHDR
# fields, the IDAT data so far (newest first), the PLTE and tRNS data once
# each has come, and where the IDAT run is. IEND is no state: the walk
# stops there (NEnd)
type Pg is Data:
  PgStart{}
  Pg{
    +w: U32, +h: U32, +depth: U32, +colour: U32, +comp: U32, +filt: U32, +inter: U32,
    idat: List<&2, U32>, plte: Maybe<&2, List<&2, U32>>, trns: Maybe<&2, List<&2, U32>>, run: Run
  }

# a chunk was rejected, ended the image, or left more chunks
type Nx is Data:
  NBad{}
  NEnd{pg: Pg}
  NMore{pg: Pg}

# scanline phase
type Uf is Data:
  UFilt{}
  UBody{}
  UBad{}

# transparency key carried by tRNS, at the samples' full width
type Key is Data:
  KNone{}
  KGrey{+g: U32}
  KRgb{+r: U32, +g: U32, +b: U32}

# a palette for lookup by index: none, one entry, the entries at even and at
# odd positions (an index's low bit picks one, the rest of it the entry
# there), or, past the fuel, the list itself
type Pt is Data:
  PNone{}
  POne{+v: U32}
  PTwo{ev: Pt, od: Pt}
  PList{xs: List<&2, U32>}

# what the header and the PLTE and tRNS chunks say of the samples: the
# picture's width and height, bit depth, colour type, palette and
# transparency
type Hd is Data:
  Hd{+w: U32, +h: U32, +depth: U32, +colour: U32, +plte: List<&2, U32>, +trns: List<&2, U32>}

# a pass read from the front of the inflated data: its pixel rows and the
# bytes after it, or refused
type Pass is Data:
  PBad{}
  PGot{rows: List<&2, List<&2, U32>>, rest: List<&2, U32>}

# big-endian unsigned 32
def be.u32(+aa: U32, +bb: U32, +cc: U32, +dd: U32) -> U32:
  ((((aa << 24n : U32) .|. (bb << 16n : U32) : U32) .|. (cc << 8n : U32) : U32) .|. dd : U32)

# IHDR
def tag.ihdr() -> U32:
  1229472850

# IDAT
def tag.idat() -> U32:
  1229209940

# IEND
def tag.iend() -> U32:
  1229278788

# PLTE
def tag.plte() -> U32:
  1347179589

# tRNS
def tag.trns() -> U32:
  1951551059

# the ancillary bit of a chunk type (bit 5 of the first byte)
def tag.anc(+typ: U32) -> Bool:
  U32.is_eq(((typ >> 24n : U32) .&. 32 : U32), 32)

# the bit depths of gray: 1, 2, 4, 8 and 16
def png.d.grey(+dd: U32) -> Bool:
  Bool.or(U32.is_eq(dd, 1), Bool.or(U32.is_eq(dd, 2), Bool.or(U32.is_eq(dd, 4), Bool.or(U32.is_eq(dd, 8),
    U32.is_eq(dd, 16)))))

# the bit depths of RGB, gray and alpha, and RGBA: 8 and 16
def png.d.wide(+dd: U32) -> Bool:
  Bool.or(U32.is_eq(dd, 8), U32.is_eq(dd, 16))

# the bit depths of indexed colour: 1, 2, 4 and 8
def png.d.index(+dd: U32) -> Bool:
  Bool.or(U32.is_eq(dd, 1), Bool.or(U32.is_eq(dd, 2), Bool.or(U32.is_eq(dd, 4), U32.is_eq(dd, 8))))

# a colour type and bit depth PNG table 11.1 allows. The depth is asked
# first in each arm, so at a known depth the test is one about the colour
def png.depth.ok(+cc: U32, +dd: U32) -> Bool:
  Bool.or(Bool.and(png.d.grey(dd), U32.is_eq(cc, 0)), Bool.or(Bool.and(png.d.wide(dd), U32.is_eq(cc, 2)),
    Bool.or(Bool.and(png.d.index(dd), U32.is_eq(cc, 3)), Bool.or(Bool.and(png.d.wide(dd), U32.is_eq(cc, 4)),
      Bool.and(png.d.wide(dd), U32.is_eq(cc, 6))))))

# interlace method 0 (none) or 1 (Adam7)
def png.inter.ok(+ii: U32) -> Bool:
  Bool.or(U32.is_zero(ii), U32.is_eq(ii, 1))

# below 2^31: the bound PNG section 7.1 puts on a chunk's length and
# section 11.2.1 on the width and height (each at most 2^31 - 1)
def png.short(+nn: U32) -> Bool:
  U32.is_zero(U32.shrn(nn, 31n))

# a width or height IHDR may give: from 1 to 2^31 - 1
def png.side(+nn: U32) -> Bool:
  Bool.and(U32.is_gt(nn, 0), png.short(nn))

# IHDR constraints: sides from 1 to 2^31 - 1, a colour type and bit depth of
# table 11.1, compression and filter method 0, and interlace method 0 or 1
def png.good(+ww: U32, +hh: U32, +dd: U32, +cc: U32, +comp: U32, +ff: U32, +ii: U32) -> Bool:
  Bool.and(
    Bool.and(png.side(ww), png.side(hh)),
    Bool.and(
      png.depth.ok(cc, dd),
      Bool.and(U32.is_zero(comp), Bool.and(U32.is_zero(ff), png.inter.ok(ii)))
    )
  )

# the state before IHDR
def pg.empty() -> Pg:
  PgStart{}

# state after a valid IHDR
def pg.ihdr(+ww: U32, +hh: U32, +dd: U32, +cc: U32, +comp: U32, +ff: U32, +ii: U32) -> Pg:
  Pg{ww, hh, dd, cc, comp, ff, ii, [], None{}, None{}, RNone{}}

# an open IDAT run closes; none, or a closed one, stays as it is
def run.seal(run: Run) -> Run:
  match run:
    case RNone{}:
      RNone{}
    case ROpen{}:
      RShut{}
    case RShut{}:
      RShut{}

# close the IDAT sequence once a later chunk appears
def png.seal(pg: Pg) -> Pg:
  match pg:
    case PgStart{}:
      PgStart{}
    case Pg{+w, +h, +d, +c, +comp, +f, +i, idat, plte, trns, run}:
      Pg{w, h, d, c, comp, f, i, idat, plte, trns, run.seal(run)}

def png.bpp.ix(z3: Bool) -> U32:
  match z3:
    case True{}:
      1
    case False{}:
      0

def png.bpp.one(z0: Bool, z3: Bool) -> U32:
  match z0:
    case True{}:
      1
    case False{}:
      png.bpp.ix(z3)

def png.bpp6(z6: Bool, +cc: U32) -> U32:
  match z6:
    case True{}:
      4
    case False{}:
      png.bpp.one(U32.is_eq(cc, 0), U32.is_eq(cc, 3))

def png.bpp4(z4: Bool, z6: Bool, +cc: U32) -> U32:
  match z4:
    case True{}:
      2
    case False{}:
      png.bpp6(z6, cc)

def png.bpp0(z2: Bool, z4: Bool, z6: Bool, +cc: U32) -> U32:
  match z2:
    case True{}:
      3
    case False{}:
      png.bpp4(z4, z6, cc)

# bytes per pixel for an 8-bit colour type
def png.bpp(+cc: U32) -> U32:
  png.bpp0(U32.is_eq(cc, 2), U32.is_eq(cc, 4), U32.is_eq(cc, 6), cc)

# ISO/IEC 15948 / W3C PNG — IHDR is width, height, bit depth, colour type,
# compression method, filter method, and interlace method, each big-endian.
def parse_ihdr(xs: List<&2, U32>) -> Maybe<&2, Ihdr>:
  match xs:
    case +a <> +b <> +c <> +d <> +e <> +f <> +g <> +h <> +i <> +j <> +k <> +l <> +m <> Nil{}:
      Some{Ihdr{be.u32(a, b, c, d), be.u32(e, f, g, h), i, j, k, l, m}}
    case _other:
      None{}

# ---- scanline filters (None, Sub, Up, Average, Paeth) ----

def uf.nth(xs: List<&2, U32>, zz: Bool, +ii: U32) -> U32:
  match xs zz:
    case Nil{} _z:
      0
    case +h <> _t True{}:
      h
    case _h <> t False{}:
      uf.nth(t, U32.is_zero((ii - 1 : U32)), (ii - 1 : U32))

# the byte `bpp` back, or zero before the first pixel: `xs` holds the bytes
# before this one in the row, newest first, so it is too short there
def uf.back(xs: List<&2, U32>, +bpp: U32) -> U32:
  uf.nth(xs, U32.is_zero((bpp - 1 : U32)), (bpp - 1 : U32))

def uf.bb(prest: List<&2, U32>) -> U32:
  match prest:
    case Nil{}:
      0
    case +h <> _t:
      h

def uf.drop(prest: List<&2, U32>) -> List<&2, U32>:
  match prest:
    case Nil{}:
      []
    case _h <> t:
      t

def uf.push(prest: List<&2, U32>, phist: List<&2, U32>) -> List<&2, U32>:
  {uf.bb(prest) <> phist : List<&2, U32>}

def uf.abs.at(+hi: U32, +lo: U32, zz: Bool) -> U32:
  match zz:
    case True{}:
      hi
    case False{}:
      lo

def uf.abs(+xx: U32, +yy: U32) -> U32:
  uf.abs.at((xx - yy : U32), (yy - xx : U32), U32.is_ge(xx, yy))

def uf.paeth.b(zb: Bool, +bb: U32, +cc: U32) -> U32:
  match zb:
    case True{}:
      bb
    case False{}:
      cc

def uf.paeth.at(za: Bool, zb: Bool, +aa: U32, +bb: U32, +cc: U32) -> U32:
  match za:
    case True{}:
      aa
    case False{}:
      uf.paeth.b(zb, bb, cc)

# PaethPredictor from the PNG specification
def uf.paeth(+aa: U32, +bb: U32, +cc: U32) -> U32:
  +pa = uf.abs(bb, cc)
  +pb = uf.abs(aa, cc)
  +pc = uf.abs((aa + bb : U32), (cc << 1n : U32))
  uf.paeth.at(Bool.and(U32.is_le(pa, pb), U32.is_le(pa, pc)), U32.is_le(pb, pc), aa, bb, cc)

def uf.avg(+aa: U32, +bb: U32) -> U32:
  ((aa + bb : U32) >> 1n : U32)

# a reconstructed byte: filtered byte plus predictor, mod 256 (mask first)
def uf.add(+ff: U32, +pp: U32) -> U32:
  U32.and(255, (ff + pp : U32))

def uf.p4(z4: Bool, +aa: U32, +bb: U32, +cc: U32) -> U32:
  match z4:
    case True{}:
      uf.paeth(aa, bb, cc)
    case False{}:
      0

def uf.p3(z3: Bool, z4: Bool, +aa: U32, +bb: U32, +cc: U32) -> U32:
  match z3:
    case True{}:
      uf.avg(aa, bb)
    case False{}:
      uf.p4(z4, aa, bb, cc)

def uf.p2(z2: Bool, z3: Bool, z4: Bool, +aa: U32, +bb: U32, +cc: U32) -> U32:
  match z2:
    case True{}:
      bb
    case False{}:
      uf.p3(z3, z4, aa, bb, cc)

def uf.p1(z1: Bool, z2: Bool, z3: Bool, z4: Bool, +aa: U32, +bb: U32, +cc: U32) -> U32:
  match z1:
    case True{}:
      aa
    case False{}:
      uf.p2(z2, z3, z4, aa, bb, cc)

def uf.pred(+ft: U32, +aa: U32, +bb: U32, +cc: U32) -> U32:
  uf.p1(U32.is_eq(ft, 1), U32.is_eq(ft, 2), U32.is_eq(ft, 3), U32.is_eq(ft, 4), aa, bb, cc)

def uf.recon(
  +ff: U32,
  +ft: U32,
  +bpp: U32,
  prest: List<&2, U32>,
  phist: List<&2, U32>,
  cur: List<&2, U32>
) -> U32:
  uf.add(ff, uf.pred(ft, uf.back(cur, bpp), uf.bb(prest), uf.back(phist, bpp)))

def uf.phase(zz: Bool) -> Uf:
  match zz:
    case True{}:
      UBody{}
    case False{}:
      UBad{}

def uf.ok(+ww: U32, +hh: U32, +bpp: U32) -> Bool:
  Bool.and(U32.is_gt(ww, 0), Bool.and(U32.is_gt(hh, 0), Bool.and(U32.is_gt(bpp, 0), U32.is_le(bpp, 4))))

def uf.done(rows: Nat, all: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match rows:
    case 0n:
      Some{List.reverse(&2, U32, all)}
    case 1n+_p:
      None{}

# where unfilter stands in a row: the row above from the current byte on
# (prest), the bytes of it already passed (phist), the row so far, reversed
# (cur), the row's bytes after the current one (left) and its filter type (ft)
type Ur is Data:
  Ur{+prest: List<&2, U32>, +phist: List<&2, U32>, +cur: List<&2, U32>, +left: U32, +ft: U32}

# walk the filtered stream: a filter byte opens each row (UFilt), then its
# bytes (UBody). `zlast`, whether the row's `left` is zero, marks the row's
# last byte.
def uf.go(
  xs: List<&2, U32>,
  ph: Uf,
  zlast: Bool,
  +bpp: U32,
  +stride: U32,
  rows: Nat,
  ur: Ur,
  all: List<&2, U32>
) -> Maybe<&2, List<&2, U32>>:
  match xs ph zlast rows ur:
    case _xs UBad{} _z _r _u:
      None{}
    case Nil{} UFilt{} _z _r _u:
      uf.done(rows, all)
    case _b <> _rest UFilt{} _z 0n _u:
      None{}
    case +b <> rest UFilt{} _z 1n++r Ur{+prest, _h, _c, _l, _f}:
      uf.go(rest, uf.phase(U32.is_le(b, 4)), U32.is_zero((stride - 1 : U32)), bpp, stride, r,
        Ur{prest, [], [], (stride - 1 : U32), b}, all)
    case +b <> rest UBody{} True{} _r Ur{+prest, +phist, +cur, _l, +ft}:
      +y = uf.recon(b, ft, bpp, prest, phist, cur)
      +cur2 = {y <> cur : List<&2, U32>}
      uf.go(rest, UFilt{}, False{}, bpp, stride, rows, Ur{List.reverse(&2, U32, cur2), [], [], 0, 0},
        {y <> all : List<&2, U32>})
    case +b <> rest UBody{} False{} _r Ur{+prest, +phist, +cur, +left, +ft}:
      +y = uf.recon(b, ft, bpp, prest, phist, cur)
      +nl = (left - 1 : U32)
      uf.go(rest, UBody{}, U32.is_zero(nl), bpp, stride, rows,
        Ur{uf.drop(prest), uf.push(prest, phist), {y <> cur : List<&2, U32>}, nl, ft}, {y <> all : List<&2, U32>})
    case Nil{} UBody{} _z _r _u:
      None{}

def uf.start(zz: Bool, raw: List<&2, U32>, +ww: U32, +hh: U32, +bpp: U32) -> Maybe<&2, List<&2, U32>>:
  match zz:
    case False{}:
      None{}
    case True{}:
      uf.go(raw, UFilt{}, False{}, bpp, (ww * bpp : U32), U32.to_nat(hh), Ur{[], [], [], 0, 0}, [])

# ISO/IEC 15948 / W3C PNG — undo filter types None, Sub, Up, Average, and Paeth.
def unfilter(raw: List<&2, U32>, +ww: U32, +hh: U32, +bpp: U32) -> Maybe<&2, List<&2, U32>>:
  uf.start(uf.ok(ww, hh, bpp), raw, ww, hh, bpp)

# ---- samples to 0xAARRGGBB ----

def px.pack(+aa: U32, +rr: U32, +gg: U32, +bb: U32) -> U32:
  ((((aa << 24n : U32) .|. (rr << 16n : U32) : U32) .|. (gg << 8n : U32) : U32) .|. bb : U32)

def px.hit.at(zz: Bool) -> U32:
  match zz:
    case True{}:
      0
    case False{}:
      255

def px.hit(+ss: U32, +kk: U32) -> U32:
  px.hit.at(U32.is_eq(ss, kk))

def px.rgb.hit(+rr: U32, +gg: U32, +bb: U32, +kr: U32, +kg: U32, +kb: U32) -> U32:
  px.hit.at(Bool.and(U32.is_eq(rr, kr), Bool.and(U32.is_eq(gg, kg), U32.is_eq(bb, kb))))

def px.grey(xs: List<&2, U32>, key: Key, acc: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match xs key:
    case Nil{} _k:
      Some{List.reverse(&2, U32, acc)}
    case +g <> t KNone{}:
      px.grey(t, KNone{}, {px.pack(255, g, g, g) <> acc : List<&2, U32>})
    case +g <> t KGrey{+k}:
      px.grey(t, KGrey{k}, {px.pack(px.hit(g, k), g, g, g) <> acc : List<&2, U32>})
    case _xs _k:
      None{}

def px.rgb(xs: List<&2, U32>, key: Key, acc: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match xs key:
    case Nil{} _k:
      Some{List.reverse(&2, U32, acc)}
    case +r <> +g <> +b <> t KNone{}:
      px.rgb(t, KNone{}, {px.pack(255, r, g, b) <> acc : List<&2, U32>})
    case +r <> +g <> +b <> t KRgb{+kr, +kg, +kb}:
      px.rgb(t, KRgb{kr, kg, kb}, {px.pack(px.rgb.hit(r, g, b, kr, kg, kb), r, g, b) <> acc : List<&2, U32>})
    case _xs _k:
      None{}

def px.ga(xs: List<&2, U32>, acc: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Some{List.reverse(&2, U32, acc)}
    case +g <> +a <> t:
      px.ga(t, {px.pack(a, g, g, g) <> acc : List<&2, U32>})
    case _other:
      None{}

def px.rgba(xs: List<&2, U32>, acc: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Some{List.reverse(&2, U32, acc)}
    case +r <> +g <> +b <> +a <> t:
      px.rgba(t, {px.pack(a, r, g, b) <> acc : List<&2, U32>})
    case _other:
      None{}

# ---- the palette, for lookup by index ----

# every other entry, from the first when `keep` and from the second otherwise
def pt.alt(xs: List<&2, U32>, keep: Bool) -> List<&2, U32>:
  match xs keep:
    case Nil{} _keep:
      []
    case +hd <> tl True{}:
      {hd <> pt.alt(tl, False{}) : List<&2, U32>}
    case _hd <> tl False{}:
      pt.alt(tl, True{})

# the tree once the fuel is spent: no entry, one, or the list itself
def pt.leaf(xs: List<&2, U32>) -> Pt:
  match xs:
    case Nil{}:
      PNone{}
    case +hd <> tl:
      match tl:
        case Nil{}:
          POne{hd}
        case +yy <> rr:
          PList{{hd <> {yy <> rr : List<&2, U32>} : List<&2, U32>}}

# a lookup tree of the entries: an index's low bit picks the half its entry
# is in, so a palette of 256 entries is found in eight steps, not 256
def pt.build(fuel: Nat, xs: List<&2, U32>) -> Pt:
  match fuel xs:
    case 0n _xs:
      pt.leaf(xs)
    case 1n+_f Nil{}:
      PNone{}
    case 1n+_f Con{+hd, Nil{}}:
      POne{hd}
    case 1n+(+ff) Con{+hd, Con{+yy, rr}}:
      +all = {hd <> {yy <> rr : List<&2, U32>} : List<&2, U32>}
      PTwo{pt.build(ff, pt.alt(all, True{})), pt.build(ff, pt.alt(all, False{}))}

# the lookup tree of a list: as many halvings as there are entries is more
# fuel than the halving needs, so the tree never falls back on the list
def pt.tree(+xs: List<&2, U32>) -> Pt:
  pt.build(List.length(&2, U32, xs), xs)

# the entry at an index of a list the fuel ran out on: never reached from
# pt.tree, there for a tree built with too little fuel
def pt.list(xs: List<&2, U32>, +ix: U32) -> Maybe<&2, U32>:
  List.get(&2, U32, xs, U32.to_nat(ix))

# the entry when the index left is zero
def pt.hit(zz: Bool, +vv: U32) -> Maybe<&2, U32>:
  match zz:
    case True{}:
      Some{vv}
    case False{}:
      None{}

# whether an index is even: its low bit is clear
def pt.even(+ix: U32) -> Bool:
  U32.is_zero(U32.and(1, ix))

# the entry at an index, none past the last; `even` is pt.even(ix), which
# picks the half of a split the entry is in
def pt.at(tr: Pt, even: Bool, +ix: U32) -> Maybe<&2, U32>:
  match tr even:
    case PNone{} _even:
      None{}
    case POne{+vv} _even:
      pt.hit(U32.is_zero(ix), vv)
    case PTwo{ev, _od} True{}:
      pt.at(ev, pt.even(U32.shr(ix)), U32.shr(ix))
    case PTwo{_ev, od} False{}:
      pt.at(od, pt.even(U32.shr(ix)), U32.shr(ix))
    case PList{xs} _even:
      pt.list(xs, ix)

def px.use(mm: Maybe<&2, U32>, kk: U32 -> Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match mm:
    case None{}:
      None{}
    case Some{+c}:
      kk(c)

def px.idx(xs: List<&2, U32>, +pal: Pt, acc: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Some{List.reverse(&2, U32, acc)}
    case +i <> t:
      px.use(pt.at(pal, pt.even(i), i), c => px.idx(t, pal, {c <> acc : List<&2, U32>}))

# the palette's entries, 0xAARRGGBB, each alpha from tRNS while it lasts and
# 255 after; a last entry cut short is no entry
def pal.make(xs: List<&2, U32>, als: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs als:
    case Nil{} _als:
      List.reverse(&2, U32, acc)
    case +r <> +g <> +b <> t Nil{}:
      pal.make(t, [], {px.pack(255, r, g, b) <> acc : List<&2, U32>})
    case +r <> +g <> +b <> t +a <> at:
      pal.make(t, at, {px.pack(a, r, g, b) <> acc : List<&2, U32>})
    case _xs _als:
      List.reverse(&2, U32, acc)

# tRNS's alphas when it has no more entries than PLTE; none otherwise, as
# libpng ignores a palette tRNS longer than the palette
def pal.alphas(zz: Bool, als: List<&2, U32>) -> List<&2, U32>:
  match zz:
    case True{}:
      als
    case False{}:
      []

# the palette's lookup tree, with alphas from tRNS
def pal.tree(+plte: List<&2, U32>, +trns: List<&2, U32>) -> Pt:
  +fits = Nat.is_le(List.length(&2, U32, trns), Nat.div(List.length(&2, U32, plte), 3n))
  pt.tree(pal.make(plte, pal.alphas(fits, trns), []))

def px.indexed(samples: List<&2, U32>, +plte: List<&2, U32>, +trns: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  px.idx(samples, pal.tree(plte, trns), [])

# a 16-bit tRNS value from its two bytes, most significant first
def key.u16(zz: Bool, +hi: U32, +lo: U32) -> U32:
  match zz:
    case True{}:
      lo
    case False{}:
      ((hi << 8n : U32) .|. lo : U32)

# a gray key: tRNS of exactly two bytes. Any other length is a faulty tRNS,
# ignored (PNG section 13.1)
def key.grey(xs: List<&2, U32>) -> Key:
  match xs:
    case +g1 <> +g0 <> Nil{}:
      KGrey{key.u16(U32.is_zero(g1), g1, g0)}
    case _other:
      KNone{}

# an RGB key: tRNS of exactly six bytes; any other length is ignored
def key.rgb(xs: List<&2, U32>) -> Key:
  match xs:
    case +r1 <> +r0 <> +g1 <> +g0 <> +b1 <> +b0 <> Nil{}:
      KRgb{key.u16(U32.is_zero(r1), r1, r0), key.u16(U32.is_zero(g1), g1, g0), key.u16(U32.is_zero(b1), b1, b0)}
    case _other:
      KNone{}

def px.k4(z6: Bool, samples: List<&2, U32>, plte: List<&2, U32>, trns: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match z6:
    case True{}:
      px.rgba(samples, [])
    case False{}:
      px.indexed(samples, plte, trns)

# gray and alpha, and RGBA, carry their own alpha: a tRNS there is ignored
def px.k3(
  z4: Bool,
  z6: Bool,
  samples: List<&2, U32>,
  plte: List<&2, U32>,
  trns: List<&2, U32>
) -> Maybe<&2, List<&2, U32>>:
  match z4:
    case False{}:
      px.k4(z6, samples, plte, trns)
    case True{}:
      px.ga(samples, [])

def px.k2(
  z2: Bool,
  z4: Bool,
  z6: Bool,
  samples: List<&2, U32>,
  plte: List<&2, U32>,
  trns: List<&2, U32>
) -> Maybe<&2, List<&2, U32>>:
  match z2:
    case True{}:
      px.rgb(samples, key.rgb(trns), [])
    case False{}:
      px.k3(z4, z6, samples, plte, trns)

def px.k0(
  z0: Bool,
  z2: Bool,
  z4: Bool,
  z6: Bool,
  samples: List<&2, U32>,
  plte: List<&2, U32>,
  trns: List<&2, U32>
) -> Maybe<&2, List<&2, U32>>:
  match z0:
    case True{}:
      px.grey(samples, key.grey(trns), [])
    case False{}:
      px.k2(z2, z4, z6, samples, plte, trns)

# 8-bit samples to 0xAARRGGBB for a colour type
def px.of(+colour: U32, samples: List<&2, U32>, plte: List<&2, U32>, trns: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  px.k0(U32.is_eq(colour, 0), U32.is_eq(colour, 2), U32.is_eq(colour, 4), U32.is_eq(colour, 6), samples, plte, trns)

# ---- chunks ----

def png.mod3(xs: List<&2, U32>) -> Bool:
  +n = U32.from_nat(List.length(&2, U32, xs))
  Bool.and(U32.is_gt(n, 0), Bool.and(U32.is_zero((n % 3 : U32)), U32.is_le(n, 768)))

def png.ihdr.ok(zz: Bool, +ww: U32, +hh: U32, +dd: U32, +cc: U32, +comp: U32, +ff: U32, +ii: U32) -> Nx:
  match zz:
    case False{}:
      NBad{}
    case True{}:
      NMore{pg.ihdr(ww, hh, dd, cc, comp, ff, ii)}

def png.ihdr.put(mm: Maybe<&2, Ihdr>) -> Nx:
  match mm:
    case None{}:
      NBad{}
    case Some{Ihdr{+w, +h, +d, +c, +comp, +f, +i}}:
      png.ihdr.ok(png.good(w, h, d, c, comp, f, i), w, h, d, c, comp, f, i)

def png.allow(zz: Bool, pg: Pg) -> Nx:
  match zz:
    case True{}:
      NMore{pg}
    case False{}:
      NBad{}

def pg.idat(pg: Pg, extra: List<&2, U32>) -> Pg:
  match pg:
    case PgStart{}:
      PgStart{}
    case Pg{+w, +h, +d, +c, +comp, +f, +i, idat, plte, trns, _run}:
      Pg{w, h, d, c, comp, f, i, List.append(&2, U32, extra, idat), plte, trns, ROpen{}}

def pg.plte(pg: Pg, bytes: List<&2, U32>) -> Pg:
  match pg:
    case PgStart{}:
      PgStart{}
    case Pg{+w, +h, +d, +c, +comp, +f, +i, idat, _pl, trns, run}:
      Pg{w, h, d, c, comp, f, i, idat, Some{bytes}, trns, run}

def pg.trns(pg: Pg, bytes: List<&2, U32>) -> Pg:
  match pg:
    case PgStart{}:
      PgStart{}
    case Pg{+w, +h, +d, +c, +comp, +f, +i, idat, plte, _tr, run}:
      Pg{w, h, d, c, comp, f, i, idat, plte, Some{bytes}, run}

def png.idat.try(zz: Bool, data: List<&2, U32>, pg: Pg) -> Nx:
  match zz:
    case False{}:
      NBad{}
    case True{}:
      NMore{pg.idat(pg, data)}

# the first chunk: IHDR starts the state; any other is refused
def png.on.start(zihdr: Bool, data: List<&2, U32>) -> Nx:
  match zihdr:
    case False{}:
      NBad{}
    case True{}:
      png.ihdr.put(parse_ihdr(List.reverse(&2, U32, data)))

# an IDAT opens or extends the run, when the colour type has what it needs;
# one after the run has closed is refused
def png.on.idat(run: Run, need: Bool, data: List<&2, U32>, pg: Pg) -> Nx:
  match run:
    case RShut{}:
      NBad{}
    case RNone{}:
      png.idat.try(need, data, pg)
    case ROpen{}:
      png.idat.try(need, data, pg)

def png.plte.ok(+cc: U32) -> Bool:
  Bool.or(U32.is_eq(cc, 2), Bool.or(U32.is_eq(cc, 3), U32.is_eq(cc, 6)))

def png.trns.ok(+cc: U32, saw_plte: Bool) -> Bool:
  Bool.or(
    Bool.or(U32.is_eq(cc, 0), U32.is_eq(cc, 2)),
    Bool.and(U32.is_eq(cc, 3), saw_plte)
  )

# a PLTE is taken before any IDAT, when it is the first, the colour type
# allows one and its length is a palette's
def png.on.plte(run: Run, saw_plte: Bool, +colour: U32, +data: List<&2, U32>, pg: Pg) -> Nx:
  match run:
    case RNone{}:
      png.allow(Bool.and(Bool.not(saw_plte), Bool.and(png.plte.ok(colour), png.mod3(data))),
        pg.plte(pg, List.reverse(&2, U32, data)))
    case ROpen{}:
      NBad{}
    case RShut{}:
      NBad{}

# a tRNS the decoder takes: the first, before IDAT, for a colour type that
# allows one. Any other is ignored as a faulty ancillary chunk (PNG section
# 13.1; libpng's benign error), the way png.other.at passes an unknown one
def png.trns.take(zz: Bool, data: List<&2, U32>, pg: Pg) -> Nx:
  match zz:
    case True{}:
      NMore{pg.trns(pg, List.reverse(&2, U32, data))}
    case False{}:
      NMore{png.seal(pg)}

def png.on.trns(run: Run, saw_trns: Bool, +colour: U32, saw_plte: Bool, data: List<&2, U32>, pg: Pg) -> Nx:
  match run:
    case RNone{}:
      png.trns.take(Bool.and(Bool.not(saw_trns), png.trns.ok(colour, saw_plte)), data, pg)
    case ROpen{}:
      NMore{png.seal(pg)}
    case RShut{}:
      NMore{png.seal(pg)}

def png.iend.ok(zz: Bool, pg: Pg) -> Nx:
  match zz:
    case False{}:
      NBad{}
    case True{}:
      NEnd{pg}

def png.iend.at(zempty: Bool, zpal: Bool, pg: Pg) -> Nx:
  match zempty:
    case False{}:
      NBad{}
    case True{}:
      png.iend.ok(zpal, pg)

def png.on.iend(+colour: U32, saw_plte: Bool, data: List<&2, U32>, pg: Pg) -> Nx:
  png.iend.at(List.is_empty(&2, U32, data), Bool.or(U32.is_ne(colour, 3), saw_plte), pg)

def png.other.at(anc: Bool, pg: Pg) -> Nx:
  match anc:
    case False{}:
      NBad{}
    case True{}:
      NMore{png.seal(pg)}

# what a chunk after IHDR is: IHDR again, IDAT, IEND, PLTE, tRNS, and
# whether its type has the ancillary bit
type Tags is Data:
  Tags{+ihdr: Bool, +idat: Bool, +iend: Bool, +plte: Bool, +trns: Bool, +anc: Bool}

# what the state has seen when a chunk after IHDR comes: where the IDAT run
# is, whether tRNS and PLTE have come, and the colour type
type Seen is Data:
  Seen{run: Run, +saw_trns: Bool, +saw_plte: Bool, +colour: U32}

def png.seen.idat(sn: Seen, data: List<&2, U32>, pg: Pg) -> Nx:
  match sn:
    case Seen{run, _st, +saw_plte, +colour}:
      png.on.idat(run, Bool.or(U32.is_ne(colour, 3), saw_plte), data, pg)

def png.seen.iend(sn: Seen, data: List<&2, U32>, pg: Pg) -> Nx:
  match sn:
    case Seen{_r, _st, +saw_plte, +colour}:
      png.on.iend(colour, saw_plte, data, pg)

def png.seen.plte(sn: Seen, data: List<&2, U32>, pg: Pg) -> Nx:
  match sn:
    case Seen{run, _st, +saw_plte, +colour}:
      png.on.plte(run, saw_plte, colour, data, pg)

def png.seen.trns(sn: Seen, data: List<&2, U32>, pg: Pg) -> Nx:
  match sn:
    case Seen{run, +saw_trns, +saw_plte, +colour}:
      png.on.trns(run, saw_trns, colour, saw_plte, data, pg)

def png.apply.tr(ztrns: Bool, anc: Bool, sn: Seen, data: List<&2, U32>, pg: Pg) -> Nx:
  match ztrns:
    case True{}:
      png.seen.trns(sn, data, pg)
    case False{}:
      png.other.at(anc, pg)

def png.apply.pl(zplte: Bool, ztrns: Bool, anc: Bool, sn: Seen, data: List<&2, U32>, pg: Pg) -> Nx:
  match zplte:
    case True{}:
      png.seen.plte(sn, data, pg)
    case False{}:
      png.apply.tr(ztrns, anc, sn, data, pg)

def png.apply.ie(ziend: Bool, zplte: Bool, ztrns: Bool, anc: Bool, sn: Seen, data: List<&2, U32>, pg: Pg) -> Nx:
  match ziend:
    case True{}:
      png.seen.iend(sn, data, pg)
    case False{}:
      png.apply.pl(zplte, ztrns, anc, sn, data, pg)

def png.apply.id(
  zidat: Bool,
  ziend: Bool,
  zplte: Bool,
  ztrns: Bool,
  anc: Bool,
  sn: Seen,
  data: List<&2, U32>,
  pg: Pg
) -> Nx:
  match zidat:
    case True{}:
      png.seen.idat(sn, data, pg)
    case False{}:
      png.apply.ie(ziend, zplte, ztrns, anc, sn, data, pg)

# a chunk after IHDR: a second IHDR is refused
def png.apply.go(tags: Tags, sn: Seen, data: List<&2, U32>, pg: Pg) -> Nx:
  match tags:
    case Tags{True{}, _id, _ie, _pl, _tr, _an}:
      NBad{}
    case Tags{False{}, +zidat, +ziend, +zplte, +ztrns, +anc}:
      png.apply.id(zidat, ziend, zplte, ztrns, anc, sn, data, pg)

def png.apply(+typ: U32, data: List<&2, U32>, pg: Pg) -> Nx:
  match pg:
    case PgStart{}:
      png.on.start(U32.is_eq(typ, tag.ihdr()), data)
    case Pg{+w, +h, +d, +colour, +comp, +f, +i, idat, +plte, +trns, +run}:
      png.apply.go(
        Tags{
          U32.is_eq(typ, tag.ihdr()), U32.is_eq(typ, tag.idat()), U32.is_eq(typ, tag.iend()),
          U32.is_eq(typ, tag.plte()), U32.is_eq(typ, tag.trns()), tag.anc(typ)
        },
        Seen{run, Maybe.is_some(&2, List<&2, U32>, trns), Maybe.is_some(&2, List<&2, U32>, plte), colour}, data,
        Pg{w, h, d, colour, comp, f, i, idat, plte, trns, run}
      )

def png.judge.at(zz: Bool, +typ: U32, data: List<&2, U32>, pg: Pg) -> Nx:
  match zz:
    case False{}:
      NBad{}
    case True{}:
      png.apply(typ, data, pg)

def png.judge(+got: U32, crc: List<&2, U32>, +typ: U32, data: List<&2, U32>, pg: Pg) -> Nx:
  png.judge.at(U32.is_eq(got, Crc.crc32(List.reverse(&2, U32, crc))), typ, data, pg)

def png.zp(zz: Bool) -> Pz:
  match zz:
    case True{}:
      ZCrc{}
    case False{}:
      ZDat{}

def png.pic(mm: Maybe<&2, List<&2, U32>>, +ww: U32, +hh: U32) -> Maybe<&2, Pic>:
  match mm:
    case None{}:
      None{}
    case Some{px}:
      Some{Pic{ww, hh, px}}

def png.pack(
  mm: Maybe<&2, List<&2, U32>>,
  +ww: U32,
  +hh: U32,
  +colour: U32,
  plte: List<&2, U32>,
  trns: List<&2, U32>
) -> Maybe<&2, Pic>:
  match mm:
    case None{}:
      None{}
    case Some{samples}:
      png.pic(px.of(colour, samples, plte, trns), ww, hh)

def png.samples(
  mm: Maybe<&2, List<&2, U32>>,
  +ww: U32,
  +hh: U32,
  +colour: U32,
  plte: List<&2, U32>,
  trns: List<&2, U32>
) -> Maybe<&2, Pic>:
  match mm:
    case None{}:
      None{}
    case Some{raw}:
      png.pack(unfilter(raw, ww, hh, png.bpp(colour)), ww, hh, colour, plte, trns)

# ---- bit depths other than 8, and Adam7 ----

# the bits of one pixel: the bit depth times the channels
def png.bits(+dd: U32, +cc: U32) -> U32:
  (dd * png.bpp(cc) : U32)

def png.fbpp.at(zz: Bool, +nn: U32) -> U32:
  match zz:
    case True{}:
      1
    case False{}:
      nn

# the filters' bytes per pixel (PNG section 9.2): a pixel's whole bytes, at
# least one
def png.fbpp(+bits: U32) -> U32:
  png.fbpp.at(U32.is_zero(U32.shrn(bits, 3n)), U32.shrn(bits, 3n))

# a scanline's bytes after its filter byte, for pw pixels: ceil(pw * bits / 8)
def png.stride(pw: Nat, +bits: U32) -> Nat:
  Nat.div(Nat.add(Nat.mul(pw, U32.to_nat(bits)), 7n), 8n)

def uf.rows.at(zz: Bool, raw: List<&2, U32>, +stride: U32, +hh: U32, +bpp: U32) -> Maybe<&2, List<&2, U32>>:
  match zz:
    case False{}:
      None{}
    case True{}:
      uf.go(raw, UFilt{}, False{}, bpp, stride, U32.to_nat(hh), Ur{[], [], [], 0, 0}, [])

# undo the filters of hh rows of `stride` bytes each, `bpp` bytes per pixel
# back (1 to 8): the scanlines of any bit depth, or of one Adam7 pass
def unfilter.rows(raw: List<&2, U32>, +stride: U32, +hh: U32, +bpp: U32) -> Maybe<&2, List<&2, U32>>:
  +ok = Bool.and(U32.is_gt(stride, 0), Bool.and(U32.is_gt(hh, 0), Bool.and(U32.is_gt(bpp, 0), U32.is_le(bpp, 8))))
  uf.rows.at(ok, raw, stride, hh, bpp)

# the samples of one byte at bit depth 1, 2 or 4, most significant first,
# pushed onto acc newest first
def unpack.byte(z1: Bool, z2: Bool, +bb: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match z1 z2:
    case True{} _z2:
      {U32.and(U32.shrn(bb, 0n), 1) <> {U32.and(U32.shrn(bb, 1n), 1) <> {U32.and(U32.shrn(bb, 2n), 1) <>
        {U32.and(U32.shrn(bb, 3n), 1) <> {U32.and(U32.shrn(bb, 4n), 1) <> {U32.and(U32.shrn(bb, 5n), 1) <>
        {U32.and(U32.shrn(bb, 6n), 1) <> {U32.and(U32.shrn(bb, 7n), 1) <> acc : List<&2, U32>} : List<&2, U32>}
        : List<&2, U32>} : List<&2, U32>} : List<&2, U32>} : List<&2, U32>} : List<&2, U32>} : List<&2, U32>}
    case False{} True{}:
      {U32.and(U32.shrn(bb, 0n), 3) <> {U32.and(U32.shrn(bb, 2n), 3) <> {U32.and(U32.shrn(bb, 4n), 3) <>
        {U32.and(U32.shrn(bb, 6n), 3) <> acc : List<&2, U32>} : List<&2, U32>} : List<&2, U32>} : List<&2, U32>}
    case False{} False{}:
      {U32.and(U32.shrn(bb, 0n), 15) <> {U32.and(U32.shrn(bb, 4n), 15) <> acc : List<&2, U32>} : List<&2, U32>}

# every sample of a row's bytes at bit depth 1, 2 or 4, newest first
def unpack.low(+dd: U32, row: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match row:
    case Nil{}:
      acc
    case +bb <> tl:
      unpack.low(dd, tl, unpack.byte(U32.is_eq(dd, 1), U32.is_eq(dd, 2), bb, acc))

# the 16-bit samples of a row, two bytes each, most significant first; newest first
def unpack.wide(row: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match row:
    case +hi <> +lo <> tl:
      unpack.wide(tl, {((hi << 8n : U32) .|. lo : U32) <> acc : List<&2, U32>})
    case _other:
      acc

def unpack.row.at(z8: Bool, z16: Bool, +dd: U32, +count: Nat, row: List<&2, U32>) -> List<&2, U32>:
  match z8 z16:
    case True{} _z16:
      row
    case False{} True{}:
      List.reverse(&2, U32, unpack.wide(row, []))
    case False{} False{}:
      List.take(&2, U32, List.reverse(&2, U32, unpack.low(dd, row, [])), count)

# the samples of one scanline, in order: count samples of dd bits (PNG
# section 7.2: packed most significant bit first, 16-bit samples most
# significant byte first), the unused bits at the end of a row dropped
def unpack.row(+dd: U32, +count: Nat, row: List<&2, U32>) -> List<&2, U32>:
  unpack.row.at(U32.is_eq(dd, 8), U32.is_eq(dd, 16), dd, count, row)

# the samples of a pass's unfiltered rows, `stride` bytes each, in order
def pass.samples(
  rows: Nat,
  +dd: U32,
  +bytes: List<&2, U32>,
  +stride: Nat,
  +count: Nat,
  acc: List<&2, U32>
) -> List<&2, U32>:
  match rows:
    case 0n:
      List.reverse(&2, U32, acc)
    case 1n+rr:
      pass.samples(rr, dd, List.drop(&2, U32, bytes, stride), stride, count,
        List.reverse.go(&2, U32, unpack.row(dd, count, List.take(&2, U32, bytes, stride)), acc))

# a 16-bit sample reduced to 8 bits: its high byte
def px.hi(+vv: U32) -> U32:
  U32.shrn(vv, 8n)

# a sample of bit depth 1, 2 or 4 scaled to 8 bits as libpng and Pillow do,
# v * 255 / (2^d - 1): bit replication (PNG section 13.12)
def px.up(+mx: U32, +vv: U32) -> U32:
  U32.div((vv * 255 : U32), mx)

# 16-bit gray, the key compared at 16 bits
def px.grey16(xs: List<&2, U32>, key: Key, acc: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match xs key:
    case Nil{} _k:
      Some{List.reverse(&2, U32, acc)}
    case +g <> t KNone{}:
      px.grey16(t, KNone{}, {px.pack(255, px.hi(g), px.hi(g), px.hi(g)) <> acc : List<&2, U32>})
    case +g <> t KGrey{+k}:
      px.grey16(t, KGrey{k}, {px.pack(px.hit(g, k), px.hi(g), px.hi(g), px.hi(g)) <> acc : List<&2, U32>})
    case _xs _k:
      None{}

# 16-bit RGB, the key compared at 16 bits
def px.rgb16(xs: List<&2, U32>, key: Key, acc: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match xs key:
    case Nil{} _k:
      Some{List.reverse(&2, U32, acc)}
    case +r <> +g <> +b <> t KNone{}:
      px.rgb16(t, KNone{}, {px.pack(255, px.hi(r), px.hi(g), px.hi(b)) <> acc : List<&2, U32>})
    case +r <> +g <> +b <> t KRgb{+kr, +kg, +kb}:
      px.rgb16(t, KRgb{kr, kg, kb}, {px.pack(px.rgb.hit(r, g, b, kr, kg, kb), px.hi(r), px.hi(g), px.hi(b)) <> acc
        : List<&2, U32>})
    case _xs _k:
      None{}

# every 16-bit sample reduced to its high byte
def px.his(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      []
    case +vv <> tl:
      {px.hi(vv) <> px.his(tl) : List<&2, U32>}

# gray of bit depth 1, 2 or 4 (mx = 2^d - 1), the key compared unscaled
def px.grey.low(+mx: U32, xs: List<&2, U32>, key: Key, acc: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match xs key:
    case Nil{} _k:
      Some{List.reverse(&2, U32, acc)}
    case +g <> t KNone{}:
      px.grey.low(mx, t, KNone{}, {px.pack(255, px.up(mx, g), px.up(mx, g), px.up(mx, g)) <> acc : List<&2, U32>})
    case +g <> t KGrey{+k}:
      px.grey.low(mx, t, KGrey{k}, {px.pack(px.hit(g, k), px.up(mx, g), px.up(mx, g), px.up(mx, g)) <> acc
        : List<&2, U32>})
    case _xs _k:
      None{}

def px.w2(z2: Bool, z4: Bool, samples: List<&2, U32>, trns: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match z2 z4:
    case True{} _z4:
      px.rgb16(samples, key.rgb(trns), [])
    case False{} True{}:
      px.ga(px.his(samples), [])
    case False{} False{}:
      px.rgba(px.his(samples), [])

def px.wide.at(zz: Bool, +cc: U32, samples: List<&2, U32>, trns: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match zz:
    case True{}:
      px.grey16(samples, key.grey(trns), [])
    case False{}:
      px.w2(U32.is_eq(cc, 2), U32.is_eq(cc, 4), samples, trns)

# 16-bit samples to 0xAARRGGBB for a colour type (0, 2, 4 or 6)
def px.wide(+cc: U32, samples: List<&2, U32>, trns: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  px.wide.at(U32.is_zero(cc), cc, samples, trns)

def px.low.at(
  zz: Bool,
  +dd: U32,
  samples: List<&2, U32>,
  plte: List<&2, U32>,
  trns: List<&2, U32>
) -> Maybe<&2, List<&2, U32>>:
  match zz:
    case True{}:
      px.grey.low(U32.sub(U32.shln(1, U32.to_nat(dd)), 1), samples, key.grey(trns), [])
    case False{}:
      px.indexed(samples, plte, trns)

# samples of bit depth 1, 2 or 4 to 0xAARRGGBB: gray scaled up, or palette
# indices
def px.low(
  +cc: U32,
  +dd: U32,
  samples: List<&2, U32>,
  plte: List<&2, U32>,
  trns: List<&2, U32>
) -> Maybe<&2, List<&2, U32>>:
  px.low.at(U32.is_zero(cc), dd, samples, plte, trns)

def px.deep.at(
  z8: Bool,
  z16: Bool,
  +cc: U32,
  +dd: U32,
  samples: List<&2, U32>,
  plte: List<&2, U32>,
  trns: List<&2, U32>
) -> Maybe<&2, List<&2, U32>>:
  match z8 z16:
    case True{} _z16:
      px.of(cc, samples, plte, trns)
    case False{} True{}:
      px.wide(cc, samples, trns)
    case False{} False{}:
      px.low(cc, dd, samples, plte, trns)

# samples of any bit depth to 0xAARRGGBB for a colour type
def px.deep(
  +cc: U32,
  +dd: U32,
  samples: List<&2, U32>,
  plte: List<&2, U32>,
  trns: List<&2, U32>
) -> Maybe<&2, List<&2, U32>>:
  px.deep.at(U32.is_eq(dd, 8), U32.is_eq(dd, 16), cc, dd, samples, plte, trns)

# rows of nn samples each, `rows` of them
def rows.split(rows: Nat, +xs: List<&2, U32>, +nn: Nat) -> List<&2, List<&2, U32>>:
  match rows:
    case 0n:
      []
    case 1n+rr:
      {List.take(&2, U32, xs, nn) <> rows.split(rr, List.drop(&2, U32, xs, nn), nn) : List<&2, List<&2, U32>>}

def pass.rows(mm: Maybe<&2, List<&2, U32>>, rest: List<&2, U32>, +pw: U32, +ph: U32) -> Pass:
  match mm:
    case None{}:
      PBad{}
    case Some{+px}:
      PGot{rows.split(U32.to_nat(ph), px, U32.to_nat(pw)), rest}

def pass.px(mm: Maybe<&2, List<&2, U32>>, rest: List<&2, U32>, +sn: Nat, +pw: U32, +ph: U32, +hd: Hd) -> Pass:
  match mm hd:
    case None{} _h:
      PBad{}
    case Some{+bytes} Hd{_w, _h, +dd, +cc, +plte, +trns}:
      +count = Nat.mul(U32.to_nat(pw), U32.to_nat(png.bpp(cc)))
      pass.rows(px.deep(cc, dd, pass.samples(U32.to_nat(ph), dd, bytes, sn, count, []), plte, trns), rest, pw, ph)

# bits per pixel of the header's bit depth and colour type
def hd.bits(hd: Hd) -> U32:
  match hd:
    case Hd{_w, _h, +dd, +cc, _p, _t}:
      png.bits(dd, cc)

def pass.fit(zz: Bool, +raw: List<&2, U32>, +sn: Nat, +pw: U32, +ph: U32, +hd: Hd) -> Pass:
  match zz:
    case False{}:
      PBad{}
    case True{}:
      +nn = Nat.mul(U32.to_nat(ph), 1n+sn)
      pass.px(unfilter.rows(List.take(&2, U32, raw, nn), U32.from_nat(sn), ph, png.fbpp(hd.bits(hd))),
        List.drop(&2, U32, raw, nn), sn, pw, ph, hd)

def pass.open(zz: Bool, +raw: List<&2, U32>, +pw: U32, +ph: U32, +hd: Hd) -> Pass:
  match zz:
    case True{}:
      PGot{[], raw}
    case False{}:
      +sn = png.stride(U32.to_nat(pw), hd.bits(hd))
      pass.fit(Nat.is_eq(U32.to_nat(U32.from_nat(sn)), sn), raw, sn, pw, ph, hd)

# a pass of pw by ph pixels, its scanlines filtered on their own (PNG section
# 8.2); a pass with a side 0 is empty and has no bytes. hd's samples format
# is the pass's; its size is the whole picture's
def pass.read(+raw: List<&2, U32>, +pw: U32, +ph: U32, +hd: Hd) -> Pass:
  pass.open(Bool.or(U32.is_zero(pw), U32.is_zero(ph)), raw, pw, ph, hd)

# ceil(n / 2)
def png.up(+nn: U32) -> U32:
  (U32.shr(nn) + U32.and(1, nn) : U32)

# floor(n / 2)
def png.dn(+nn: U32) -> U32:
  U32.shr(nn)

# a's samples at even places and b's at odd: a0 b0 a1 b1 and so on, to the
# end of a
def ilv.px(aa: List<&2, U32>, bb: List<&2, U32>) -> List<&2, U32>:
  match aa:
    case Nil{}:
      []
    case +ha <> ta:
      match bb:
        case Nil{}:
          [ha]
        case +hb <> tb:
          {ha <> {hb <> ilv.px(ta, tb) : List<&2, U32>} : List<&2, U32>}

# a's rows at even places and b's at odd
def ilv.rows(aa: List<&2, List<&2, U32>>, bb: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match aa:
    case Nil{}:
      []
    case ha <> ta:
      match bb:
        case Nil{}:
          [ha]
        case hb <> tb:
          {ha <> {hb <> ilv.rows(ta, tb) : List<&2, List<&2, U32>>} : List<&2, List<&2, U32>>}

# the first row, or an empty one when there is none
def rows.head(bb: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match bb:
    case Nil{}:
      []
    case rb <> _tb:
      rb

# the rows after the first
def rows.tail(bb: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match bb:
    case Nil{}:
      []
    case _rb <> tb:
      tb

# each row of a with b's row of the same place, a's samples at even columns
# and b's at odd; a row b lacks is empty
def ilv.cols(aa: List<&2, List<&2, U32>>, +bb: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match aa:
    case Nil{}:
      []
    case ra <> ta:
      {ilv.px(ra, rows.head(bb)) <> ilv.cols(ta, rows.tail(bb)) : List<&2, List<&2, U32>>}

# the picture's samples, when the data held exactly the passes
def a7.end(zz: Bool, rows: List<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match zz:
    case True{}:
      Some{List.concat(&2, U32, rows)}
    case False{}:
      None{}

# the seven passes put back together (PNG section 8.2), by halves: pass 7
# holds the odd rows and passes 1 to 6 the even ones; of those, pass 6 holds
# the odd columns and passes 1 to 5 the even ones; and so on down to pass 1,
# every eighth sample of every eighth row. Each step interleaves rows
# (ilv.rows) or columns (ilv.cols)
def a7.merge(
  r1: List<&2, List<&2, U32>>,
  +r2: List<&2, List<&2, U32>>,
  r3: List<&2, List<&2, U32>>,
  +r4: List<&2, List<&2, U32>>,
  r5: List<&2, List<&2, U32>>,
  +r6: List<&2, List<&2, U32>>,
  r7: List<&2, List<&2, U32>>
) -> List<&2, List<&2, U32>>:
  ilv.rows(ilv.cols(ilv.rows(ilv.cols(ilv.rows(ilv.cols(r1, r2), r3), r4), r5), r6), r7)

def a7.s7(
  r1: List<&2, List<&2, U32>>,
  r2: List<&2, List<&2, U32>>,
  r3: List<&2, List<&2, U32>>,
  r4: List<&2, List<&2, U32>>,
  r5: List<&2, List<&2, U32>>,
  r6: List<&2, List<&2, U32>>,
  pp: Pass
) -> Maybe<&2, List<&2, U32>>:
  match pp:
    case PBad{}:
      None{}
    case PGot{r7, t7}:
      a7.end(List.is_empty(&2, U32, t7), a7.merge(r1, r2, r3, r4, r5, r6, r7))

def a7.s6(
  r1: List<&2, List<&2, U32>>,
  r2: List<&2, List<&2, U32>>,
  r3: List<&2, List<&2, U32>>,
  r4: List<&2, List<&2, U32>>,
  r5: List<&2, List<&2, U32>>,
  pp: Pass,
  +hd: Hd
) -> Maybe<&2, List<&2, U32>>:
  match pp hd:
    case PBad{} _h:
      None{}
    case PGot{r6, t6} Hd{+ww, +hh, _d, _c, _p, _t}:
      a7.s7(r1, r2, r3, r4, r5, r6, pass.read(t6, ww, png.dn(hh), hd))

def a7.s5(
  r1: List<&2, List<&2, U32>>,
  r2: List<&2, List<&2, U32>>,
  r3: List<&2, List<&2, U32>>,
  r4: List<&2, List<&2, U32>>,
  pp: Pass,
  +hd: Hd
) -> Maybe<&2, List<&2, U32>>:
  match pp hd:
    case PBad{} _h:
      None{}
    case PGot{r5, t5} Hd{+ww, +hh, _d, _c, _p, _t}:
      a7.s6(r1, r2, r3, r4, r5, pass.read(t5, png.dn(ww), png.up(hh), hd), hd)

def a7.s4(
  r1: List<&2, List<&2, U32>>,
  r2: List<&2, List<&2, U32>>,
  r3: List<&2, List<&2, U32>>,
  pp: Pass,
  +hd: Hd
) -> Maybe<&2, List<&2, U32>>:
  match pp hd:
    case PBad{} _h:
      None{}
    case PGot{r4, t4} Hd{+ww, +hh, _d, _c, _p, _t}:
      +w1 = png.up(ww)
      a7.s5(r1, r2, r3, r4, pass.read(t4, w1, png.dn(png.up(hh)), hd), hd)

def a7.s3(
  r1: List<&2, List<&2, U32>>,
  r2: List<&2, List<&2, U32>>,
  pp: Pass,
  +hd: Hd
) -> Maybe<&2, List<&2, U32>>:
  match pp hd:
    case PBad{} _h:
      None{}
    case PGot{r3, t3} Hd{+ww, +hh, _d, _c, _p, _t}:
      +w1 = png.up(ww)
      +h2 = png.up(png.up(hh))
      a7.s4(r1, r2, r3, pass.read(t3, png.dn(w1), h2, hd), hd)

def a7.s2(
  r1: List<&2, List<&2, U32>>,
  pp: Pass,
  +hd: Hd
) -> Maybe<&2, List<&2, U32>>:
  match pp hd:
    case PBad{} _h:
      None{}
    case PGot{r2, t2} Hd{+ww, +hh, _d, _c, _p, _t}:
      +w2 = png.up(png.up(ww))
      +h2 = png.up(png.up(hh))
      a7.s3(r1, r2, pass.read(t2, w2, png.dn(h2), hd), hd)

def a7.s1(
  pp: Pass,
  +hd: Hd
) -> Maybe<&2, List<&2, U32>>:
  match pp hd:
    case PBad{} _h:
      None{}
    case PGot{r1, t1} Hd{+ww, +hh, _d, _c, _p, _t}:
      +w2 = png.up(png.up(ww))
      +h3 = png.up(png.up(png.up(hh)))
      a7.s2(r1, pass.read(t1, png.dn(w2), h3, hd), hd)

# Adam7 (PNG section 8.2): seven passes in order, each a picture of its own,
# read at the sizes png.a7.len counts and put back together by a7.merge
def a7.go(+raw: List<&2, U32>, +hd: Hd) -> Maybe<&2, List<&2, U32>>:
  match hd:
    case Hd{+ww, +hh, _d, _c, _p, _t}:
      +w3 = png.up(png.up(png.up(ww)))
      +h3 = png.up(png.up(png.up(hh)))
      a7.s1(pass.read(raw, w3, h3, hd), hd)

# the filtered bytes of a pass of pw by ph pixels: a filter byte and a
# scanline for each row, none for an empty pass
def png.pass.len.at(zz: Bool, +pw: U32, +ph: U32, +bits: U32) -> Nat:
  match zz:
    case True{}:
      0n
    case False{}:
      Nat.mul(U32.to_nat(ph), 1n+png.stride(U32.to_nat(pw), bits))

def png.pass.len(+pw: U32, +ph: U32, +bits: U32) -> Nat:
  png.pass.len.at(Bool.or(U32.is_zero(pw), U32.is_zero(ph)), pw, ph, bits)

# the filtered bytes of the seven Adam7 passes, as a7.go reads them
def png.a7.len(+ww: U32, +hh: U32, +bits: U32) -> Nat:
  +w1 = png.up(ww)
  +w2 = png.up(w1)
  +h1 = png.up(hh)
  +h2 = png.up(h1)
  Nat.add(png.pass.len(png.up(w2), png.up(h2), bits), Nat.add(png.pass.len(png.dn(w2), png.up(h2), bits),
    Nat.add(png.pass.len(w2, png.dn(h2), bits), Nat.add(png.pass.len(png.dn(w1), h2, bits),
    Nat.add(png.pass.len(w1, png.dn(h1), bits), Nat.add(png.pass.len(png.dn(ww), h1, bits),
    png.pass.len(ww, png.dn(hh), bits)))))))

def png.budget.at(zz: Bool, +ww: U32, +hh: U32, +bits: U32) -> Nat:
  match zz:
    case True{}:
      png.pass.len(ww, hh, bits)
    case False{}:
      png.a7.len(ww, hh, bits)

# the exact length the inflated IDAT data must have for the header: what
# unfilter reads, so the inflater can stop as soon as a stream passes it
def png.budget(+ww: U32, +hh: U32, +dd: U32, +cc: U32, +ii: U32) -> Nat:
  png.budget.at(U32.is_zero(ii), ww, hh, png.bits(dd, cc))

# a picture without interlacing: one pass of the whole size
def png.flat(pp: Pass) -> Maybe<&2, List<&2, U32>>:
  match pp:
    case PBad{}:
      None{}
    case PGot{rows, rest}:
      a7.end(List.is_empty(&2, U32, rest), rows)

def png.deep.at(
  zz: Bool,
  +raw: List<&2, U32>,
  +ww: U32,
  +hh: U32,
  +dd: U32,
  +cc: U32,
  +plte: List<&2, U32>,
  +trns: List<&2, U32>
) -> Maybe<&2, List<&2, U32>>:
  match zz:
    case True{}:
      png.flat(pass.read(raw, ww, hh, Hd{ww, hh, dd, cc, plte, trns}))
    case False{}:
      a7.go(raw, Hd{ww, hh, dd, cc, plte, trns})

# the picture of any bit depth and interlace method from the inflated data
def png.deep(
  mm: Maybe<&2, List<&2, U32>>,
  +ww: U32,
  +hh: U32,
  +dd: U32,
  +cc: U32,
  +ii: U32,
  plte: List<&2, U32>,
  trns: List<&2, U32>
) -> Maybe<&2, Pic>:
  match mm:
    case None{}:
      None{}
    case Some{+raw}:
      png.pic(png.deep.at(U32.is_zero(ii), raw, ww, hh, dd, cc, plte, trns), ww, hh)

# the filtered bytes of 8-bit samples without interlacing: h rows, each a
# filter byte and w pixels of bpp bytes. png.budget at bit depth 8 and
# interlace method 0, in the form the round trip reads
def png.budget8(+ww: U32, +hh: U32, +cc: U32) -> Nat:
  Nat.mul(U32.to_nat(hh), 1n+Nat.mul(U32.to_nat(ww), U32.to_nat(png.bpp(cc))))

# 8-bit samples without interlacing take png.samples; any other bit depth,
# or Adam7, png.deep. Either way the inflater stops once the data passes the
# length the header implies
def png.finish.go(zenc: Bool, +ii: U32, idat: List<&2, U32>, hd: Hd) -> Maybe<&2, Pic>:
  match zenc hd:
    case True{} Hd{+ww, +hh, _d, +colour, plte, trns}:
      png.samples(Inf.inflate.upto(png.budget8(ww, hh, colour), List.reverse(&2, U32, idat)), ww, hh, colour, plte,
        trns)
    case False{} Hd{+ww, +hh, +dd, +colour, plte, trns}:
      png.deep(Inf.inflate.upto(png.budget(ww, hh, dd, colour, ii), List.reverse(&2, U32, idat)), ww, hh, dd,
        colour, ii, plte, trns)

# the data of a chunk that came, none for one that did not
def png.or.nil(mm: Maybe<&2, List<&2, U32>>) -> List<&2, U32>:
  match mm:
    case None{}:
      []
    case Some{xs}:
      xs

# the picture of the state IEND ended: none before IHDR
def png.finish(pg: Pg) -> Maybe<&2, Pic>:
  match pg:
    case PgStart{}:
      None{}
    case Pg{+w, +h, +d, +colour, +comp, +f, +i, idat, plte, trns, _run}:
      png.finish.go(Bool.and(U32.is_eq(d, 8), Bool.and(U32.is_zero(comp), Bool.and(U32.is_zero(f), U32.is_zero(i)))),
        i, idat, Hd{w, h, d, colour, png.or.nil(plte), png.or.nil(trns)})

# after a judged chunk: none when it was refused, the picture when it was
# IEND (whatever bytes follow it, as libpng and other decoders stop reading
# there), and the walk over the rest otherwise. The walk is started only in
# that last case: a refusal or IEND reads nothing more
# the state a judged chunk leaves; any state for one refused
def png.pgof(nx: Nx) -> Pg:
  match nx:
    case NBad{}:
      pg.empty()
    case NEnd{pg}:
      pg
    case NMore{pg}:
      pg

# after a judged chunk: none when it was refused, the picture when it was
# IEND (whatever bytes follow it, as libpng and other decoders stop reading
# there), and the walk over the rest otherwise. The walk is a thunk, forced
# only in that last case: after a refusal or IEND nothing more is read
def png.crc(nx: Nx, more: Unit -> Maybe<&2, Pic>) -> Maybe<&2, Pic>:
  match nx:
    case NBad{}:
      None{}
    case NEnd{pg}:
      png.finish(pg)
    case NMore{_pg}:
      more(Unit{})

# after a chunk's length field: the walk over the rest when the length is
# below 2^31 (PNG section 7.1), none otherwise. The walk is a thunk, forced
# only when the length is taken
def png.len.ok(zz: Bool, more: Unit -> Maybe<&2, Pic>) -> Maybe<&2, Pic>:
  match zz:
    case True{}:
      more(Unit{})
    case False{}:
      None{}

# one byte of a PNG chunk stream. `zlast` is the last data byte of the chunk.
def png.go(
  xs: List<&2, U32>,
  pz: Pz,
  zlast: Bool,
  +left: U32,
  +typ: U32,
  crc: List<&2, U32>,
  data: List<&2, U32>,
  pg: Pg
) -> Maybe<&2, Pic>:
  match xs pz zlast:
    case Nil{} _pz _z:
      None{}
    case +a <> +b <> +c <> +d <> rest ZLen{} _z:
      +n = be.u32(a, b, c, d)
      png.len.ok(png.short(n), _u => png.go(rest, ZTyp{}, False{}, n, 0, [], [], pg))
    case _xs ZLen{} _z:
      None{}
    case +a <> +b <> +c <> +d <> rest ZTyp{} _z:
      png.go(rest, png.zp(U32.is_zero(left)), U32.is_eq(left, 1), left, be.u32(a, b, c, d), [d, c, b, a], [], pg)
    case _xs ZTyp{} _z:
      None{}
    case +b <> rest ZDat{} True{}:
      png.go(rest, ZCrc{}, False{}, 0, typ, {b <> crc : List<&2, U32>}, {b <> data : List<&2, U32>}, pg)
    case +b <> rest ZDat{} False{}:
      +n = (left - 1 : U32)
      png.go(rest, ZDat{}, U32.is_eq(n, 1), n, typ, {b <> crc : List<&2, U32>}, {b <> data : List<&2, U32>}, pg)
    case +a <> +b <> +c <> +d <> rest ZCrc{} _z:
      +nx = png.judge(be.u32(a, b, c, d), crc, typ, data, pg)
      png.crc(nx, _u => png.go(rest, ZLen{}, False{}, 0, 0, [], [], png.pgof(nx)))
    case _xs _pz _z:
      None{}

# ISO/IEC 15948 / W3C PNG — chunks after the signature, CRC-32 over type and
# data, then IDAT inflated as zlib DEFLATE (compression method 0).
def decode(xs: List<&2, U32>) -> Maybe<&2, Pic>:
  png.go(xs, ZLen{}, False{}, 0, 0, [], [], pg.empty())

# ---- encode (colour type 2 or 6, filter None, stored-block IDAT) ----

# the low byte
def enc.byte(+nn: U32) -> U32:
  (255 .&. nn : U32)

# the next byte up
def enc.hi(+nn: U32) -> U32:
  (255 .&. (nn >> 8n : U32) : U32)

# four bytes, big-endian
def enc.be(+nn: U32) -> List<&2, U32>:
  [(255 .&. (nn >> 24n : U32) : U32), (255 .&. (nn >> 16n : U32) : U32), enc.hi(nn), enc.byte(nn)]

# alpha of a 0xAARRGGBB sample. The mask is the first operand, so once a
# law takes the sample's bits apart, the masked byte reduces to them.
def enc.a(+cc: U32) -> U32:
  U32.and(255, U32.shrn(cc, 24n))

# red of a 0xAARRGGBB sample. The mask goes first here too, so a sample's
# bits, once taken apart, reduce to the byte.
def enc.r(+cc: U32) -> U32:
  (255 .&. (cc >> 16n : U32) : U32)

# green of a 0xAARRGGBB sample
def enc.g(+cc: U32) -> U32:
  (255 .&. (cc >> 8n : U32) : U32)

# blue of a 0xAARRGGBB sample
def enc.b(+cc: U32) -> U32:
  (255 .&. cc : U32)

# one opaque pixel, newest-first, so a later reverse is R, G, B
def enc.push.rgb(+cc: U32, acc: List<&2, U32>) -> List<&2, U32>:
  {enc.b(cc) <> enc.g(cc) <> enc.r(cc) <> acc : List<&2, U32>}

# one pixel, newest-first, so a later reverse is R, G, B, A
def enc.push.rgba(+cc: U32, acc: List<&2, U32>) -> List<&2, U32>:
  {enc.a(cc) <> enc.b(cc) <> enc.g(cc) <> enc.r(cc) <> acc : List<&2, U32>}

# the channels of one sample
def enc.push(op: Bool, +cc: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match op:
    case True{}:
      enc.push.rgb(cc, acc)
    case False{}:
      enc.push.rgba(cc, acc)

# one less, or zero
def enc.pred(nn: Nat) -> Nat:
  match nn:
    case 0n:
      0n
    case 1n+p:
      p

# how many bytes, counted in a word
def enc.len(xs: List<&2, U32>, +nn: U32) -> U32:
  match xs:
    case Nil{}:
      nn
    case _h <> t:
      enc.len(t, (nn + 1 : U32))

# a reversed prefix, consed onto the suffix
def enc.cat.go(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      ys
    case +h <> t:
      enc.cat.go(t, {h <> ys : List<&2, U32>})

# xs, then ys
def enc.cat(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  enc.cat.go(List.reverse(&2, U32, xs), ys)

# channels written for one sample
def enc.nch(op: Bool) -> U32:
  match op:
    case True{}:
      3
    case False{}:
      4

# scanlines, filter None, newest-first. `left` is 0 at the first sample of a
# row, where the filter byte is written; otherwise it is the samples still
# to come after this one. `n` is how many bytes are in `acc`. One reverse at
# the end puts the bytes in order.
def enc.raw(
  px: List<&2, U32>,
  left: Nat,
  +ww: Nat,
  +op: Bool,
  acc: List<&2, U32>,
  +nn: U32
) -> List<&2, U32> & U32:
  match px left:
    case Nil{} _left:
      (List.reverse(&2, U32, acc), nn)
    case +c <> t 0n:
      +n2 = ((nn + 1 : U32) + enc.nch(op) : U32)
      enc.raw(t, enc.pred(ww), ww, op, enc.push(op, c, {0 <> acc : List<&2, U32>}), n2)
    case +c <> t 1n+p:
      enc.raw(t, p, ww, op, enc.push(op, c, acc), (nn + enc.nch(op) : U32))

# the five-byte stored-block header: BFINAL, then LEN and NLEN, little-endian
def enc.head(fin: Bool, +len: U32, +nlen: U32) -> List<&2, U32>:
  match fin:
    case True{}:
      [1, enc.byte(len), enc.hi(len), enc.byte(nlen), enc.hi(nlen)]
    case False{}:
      [0, enc.byte(len), enc.hi(len), enc.byte(nlen), enc.hi(nlen)]

# one stored DEFLATE block. `data` is chronological.
def enc.stored(fin: Bool, +data: List<&2, U32>) -> List<&2, U32>:
  +len = enc.len(data, 0)
  enc.cat(enc.head(fin, len, (len .^. 65535 : U32)), data)

# stored blocks of at most `max` bytes. `z` means this byte opens a block.
# `acc` is the open block, newest-first.
def enc.feed(
  xs: List<&2, U32>,
  zz: Bool,
  +room: U32,
  +max: U32,
  acc: List<&2, U32>
) -> List<&2, U32>:
  match xs zz:
    case Nil{} _z:
      enc.stored(True{}, List.reverse(&2, U32, acc))
    case +h <> t True{}:
      +nxt = (max - 1 : U32)
      +blk = enc.stored(False{}, List.reverse(&2, U32, acc))
      enc.cat(blk, enc.feed(t, U32.is_zero(nxt), nxt, max, [h]))
    case +h <> t False{}:
      +nxt = (room - 1 : U32)
      enc.feed(t, U32.is_zero(nxt), nxt, max, {h <> acc : List<&2, U32>})

# one final stored block when the payload already fits
def enc.blocks.fit(zz: Bool, +max: U32, +nn: U32, +xs: List<&2, U32>) -> List<&2, U32>:
  match zz:
    case True{}:
      enc.cat(enc.head(True{}, nn, (nn .^. 65535 : U32)), xs)
    case False{}:
      enc.feed(xs, U32.is_zero(max), max, max, [])

# stored DEFLATE blocks, each at most `max` bytes, the last one final
def enc.blocks(+max: U32, +xs: List<&2, U32>) -> List<&2, U32>:
  +n = enc.len(xs, 0)
  enc.blocks.fit(U32.is_le(n, max), max, n, xs)

# a chunk: length, type, data, and CRC-32 over the type and the data
def enc.chunk(+tag: U32, +data: List<&2, U32>) -> List<&2, U32>:
  +body = enc.cat(enc.be(tag), data)
  +crc = Crc.crc32(body)
  +n = enc.len(data, 0)
  enc.cat(enc.be(n), enc.cat(body, enc.be(crc)))

# IHDR: width, height, depth 8, colour type, method 0, filter 0, interlace 0
def enc.ihdr(+ww: U32, +hh: U32, +ct: U32) -> List<&2, U32>:
  enc.cat(enc.be(ww), enc.cat(enc.be(hh), [8, ct, 0, 0, 0]))

# the eight-byte signature
def enc.sig() -> List<&2, U32>:
  [137, 80, 78, 71, 13, 10, 26, 10]

# colour type 2 when opaque, otherwise 6
def enc.ct(op: Bool) -> U32:
  match op:
    case True{}:
      2
    case False{}:
      6

# zlib wrapper, CMF/FLG 120 1, around stored DEFLATE blocks and an Adler-32.
# `n` is the length of `raw`, already counted while the scanlines were built.
def enc.zlib(+raw: List<&2, U32>, +nn: U32) -> List<&2, U32>:
  +sum = Inf.adler.of(raw)
  enc.cat([120, 1], enc.cat(enc.blocks.fit(U32.is_le(nn, 65535), 65535, nn, raw), enc.be(sum)))

# how many stored blocks cover `n` raw bytes
def enc.nblk.at(zz: Bool, +qq: U32) -> U32:
  match zz:
    case True{}:
      qq
    case False{}:
      (qq + 1 : U32)

# ceil(n / 65535). An exact multiple stays `q`.
def enc.nblk(+nn: U32) -> U32:
  enc.nblk.at(U32.is_zero((nn % 65535 : U32)), U32.div(nn, 65535))

# IDAT data length: zlib header, stored-block headers, raw bytes, Adler-32
def enc.idat.ln(+nn: U32) -> U32:
  ((nn + (enc.nblk(nn) * 5 : U32) : U32) + 6 : U32)

# CRC-32 and cons chronological bytes onto a newest-first accumulator
def enc.crc.list(xs: List<&2, U32>, +cc: U32, acc: List<&2, U32>) -> U32 & List<&2, U32>:
  match xs:
    case Nil{}:
      (cc, acc)
    case +h <> t:
      enc.crc.list(t, Crc.crc.byte(cc, h), {h <> acc : List<&2, U32>})

# the stored-block length: the bytes still open, at most 65535
def enc.cap.at(zz: Bool, +nn: U32) -> U32:
  match zz:
    case True{}:
      nn
    case False{}:
      65535

# min(n, 65535)
def enc.cap(+nn: U32) -> U32:
  enc.cap.at(U32.is_le(nn, 65535), nn)

# BFINAL is 1 when this block holds every byte still open
def enc.bf.at(zz: Bool) -> U32:
  match zz:
    case True{}:
      1
    case False{}:
      0

# 1 when `n` fits in one stored block, otherwise 0
def enc.bf(+nn: U32) -> U32:
  enc.bf.at(U32.is_le(nn, 65535))

# where enc.pour stands in its stored blocks: `room` is the data bytes left
# in the open block, including this one; `left` counts raw bytes still to
# come, including this one; `len` and `bf` are the length and BFINAL of the
# block a new header opens
type Pb is Data:
  Pb{+room: U32, +left: U32, +len: U32, +bf: U32}

# a stored block's header bytes, BFINAL first, with the CRC run over them
def enc.head.crc(+len: U32, +bf: U32, +cc: U32) -> U32:
  +nlen = (len .^. 65535 : U32)
  +c1 = Crc.crc.byte(cc, bf)
  +c2 = Crc.crc.byte(c1, enc.byte(len))
  +c3 = Crc.crc.byte(c2, enc.hi(len))
  +c4 = Crc.crc.byte(c3, enc.byte(nlen))
  Crc.crc.byte(c4, enc.hi(nlen))

# a stored block's header bytes, BFINAL first, consed newest-first
def enc.head.acc(+len: U32, +bf: U32, acc: List<&2, U32>) -> List<&2, U32>:
  +nlen = (len .^. 65535 : U32)
  +a0 = {bf <> acc : List<&2, U32>}
  +a1 = {enc.byte(len) <> a0 : List<&2, U32>}
  +a2 = {enc.hi(len) <> a1 : List<&2, U32>}
  +a3 = {enc.byte(nlen) <> a2 : List<&2, U32>}
  {enc.hi(nlen) <> a3 : List<&2, U32>}

# stored blocks, newest-first, CRC running over headers and data. `znew` means
# this byte opens a block of length `len` with BFINAL `bf`. `zlast` means this
# data byte closes the block.
def enc.pour(xs: List<&2, U32>, znew: Bool, zlast: Bool, pb: Pb, +cc: U32, acc: List<&2, U32>) -> U32 & List<&2, U32>:
  match xs znew zlast pb:
    case Nil{} _z _last _pb:
      (cc, acc)
    case +h <> t False{} False{} Pb{+room, +left, +len, +bf}:
      +room2 = (room - 1 : U32)
      enc.pour(t, False{}, U32.is_eq(room2, 1), Pb{room2, (left - 1 : U32), len, bf}, Crc.crc.byte(cc, h),
        {h <> acc : List<&2, U32>})
    case +h <> t False{} True{} Pb{_r, +left, _l, _b}:
      +left2 = (left - 1 : U32)
      enc.pour(t, True{}, False{}, Pb{0, left2, enc.cap(left2), enc.bf(left2)}, Crc.crc.byte(cc, h),
        {h <> acc : List<&2, U32>})
    case +h <> t True{} _last Pb{_r, +left, +len, +bf}:
      +left2 = (left - 1 : U32)
      +room2 = (len - 1 : U32)
      enc.pour(t, U32.is_zero(room2), U32.is_eq(room2, 1), Pb{room2, left2, enc.cap(left2), enc.bf(left2)},
        Crc.crc.byte(enc.head.crc(len, bf, cc), h), {h <> enc.head.acc(len, bf, acc) : List<&2, U32>})

# Adler-32, then the CRC field, then IEND, then one reverse of the whole file
def enc.seal.crc(pp: U32 & List<&2, U32>, ie: List<&2, U32>) -> List<&2, U32>:
  match pp:
    case (+c, acc):
      +crc = (c .^. 4294967295 : U32)
      List.reverse(&2, U32, enc.cat.go(ie, enc.cat.go(enc.be(crc), acc)))

# the four Adler bytes belong to the IDAT data and to its CRC
def enc.seal.adler(pp: U32 & List<&2, U32>, +sum: U32, ie: List<&2, U32>) -> List<&2, U32>:
  match pp:
    case (+c, acc):
      enc.seal.crc(enc.crc.list(enc.be(sum), c, acc), ie)

# zlib header, then the stored blocks
def enc.seal.run(
  pp: U32 & List<&2, U32>,
  raw: List<&2, U32>,
  +nn: U32,
  +sum: U32,
  ie: List<&2, U32>
) -> List<&2, U32>:
  match pp:
    case (+c, acc):
      enc.seal.adler(enc.pour(raw, True{}, False{}, Pb{0, nn, enc.cap(nn), enc.bf(nn)}, c, acc), sum, ie)

# IDAT type, then the zlib stream
def enc.seal.body(
  pp: U32 & List<&2, U32>,
  raw: List<&2, U32>,
  +nn: U32,
  +sum: U32,
  ie: List<&2, U32>
) -> List<&2, U32>:
  match pp:
    case (+c, acc):
      enc.seal.run(enc.crc.list([120, 1], c, acc), raw, nn, sum, ie)

# Adler-32 reduced once. The sum stays below twice the modulus.
def enc.add.at(zz: Bool, +tt: U32) -> U32:
  match zz:
    case True{}:
      (tt - 65521 : U32)
    case False{}:
      tt

# one Adler-32 add, modulo 65521
def enc.add(+ss: U32, +xx: U32) -> U32:
  +t = (ss + xx : U32)
  enc.add.at(U32.is_ge(t, 65521), t)

# the running CRC, the newest-first bytes, and the packed Adler-32
def enc.rgb.fin(+cc: U32, acc: List<&2, U32>, +aa: U32, +bb: U32) -> (U32 & List<&2, U32>) & U32:
  ((cc, acc), ((bb << 16n : U32) .|. aa : U32))

# where enc.rgb.go's stored blocks stand: zblock opens a block and zdone
# says no raw bytes are left for one; zspan says a block is open and zneed
# that it is full. `need` counts the bytes still open in the block, `left`
# the raw bytes from the open block's start on, and `len` the open block's
# length
type Bk is Data:
  Bk{+zblock: Bool, +zdone: Bool, +zspan: Bool, +zneed: Bool, +need: U32, +left: U32, +len: U32}

# enc.rgb.go's cursor over the samples: a filter byte, red, green, or the
# last sample of the row is next. px holds the samples after col, the
# sample being written, and row counts the row's samples from col on, of ww
type Cr is Data:
  Cr{+filt: Bool, +zred: Bool, +zgrn: Bool, +zlast: Bool, +px: List<&2, U32>, +col: U32, +row: U32, +ww: U32}

# what enc.rgb.go has written: the running CRC, the newest-first bytes and
# the two Adler-32 sums
type Out is Data:
  Out{+cc: U32, acc: List<&2, U32>, +aa: U32, +bb: U32}

# a stored block's header for the `left` raw bytes still to come, its CRC run
def enc.rgb.head(+left: U32, +cc: U32, acc: List<&2, U32>, +aa: U32, +bb: U32) -> Out:
  +len2 = enc.cap(left)
  +bf = enc.bf(left)
  Out{enc.head.crc(len2, bf, cc), enc.head.acc(len2, bf, acc), aa, bb}

# the raw byte the cursor is at: 0 for a filter byte (and for red past the
# samples), else the sample's red, green or blue
def enc.rgb.byte(cr: Cr) -> U32:
  match cr:
    case Cr{True{}, _r, _g, _l, _p, _c, _w, _ww}:
      0
    case Cr{False{}, True{}, _g, _l, Nil{}, _c, _w, _ww}:
      0
    case Cr{False{}, True{}, _g, _l, Con{+smp, _t}, _c, _w, _ww}:
      enc.r(smp)
    case Cr{False{}, False{}, True{}, _l, _p, +col, _w, _ww}:
      enc.g(col)
    case Cr{False{}, False{}, False{}, _l, _p, +col, _w, _ww}:
      enc.b(col)

# the cursor one raw byte on
def enc.rgb.step(cr: Cr) -> Cr:
  match cr:
    case Cr{True{}, _r, _g, _l, +px, +col, +row, +ww}:
      Cr{False{}, True{}, False{}, False{}, px, col, row, ww}
    case Cr{False{}, True{}, _g, _l, Nil{}, _c, +row, +ww}:
      Cr{False{}, False{}, True{}, False{}, [], 0, row, ww}
    case Cr{False{}, True{}, _g, _l, Con{+smp, +rest}, _c, +row, +ww}:
      Cr{False{}, False{}, True{}, False{}, rest, smp, row, ww}
    case Cr{False{}, False{}, True{}, _l, +px, +col, +row, +ww}:
      Cr{False{}, False{}, False{}, U32.is_eq(row, 1), px, col, row, ww}
    case Cr{False{}, False{}, False{}, True{}, +px, +col, _r, +ww}:
      Cr{True{}, True{}, False{}, False{}, px, col, ww, ww}
    case Cr{False{}, False{}, False{}, False{}, +px, +col, +row, +ww}:
      Cr{False{}, True{}, False{}, False{}, px, col, (row - 1 : U32), ww}

# one raw byte written: CRC, the bytes, and Adler-32
def enc.rgb.put(+xx: U32, +cc: U32, acc: List<&2, U32>, +aa: U32, +bb: U32) -> Out:
  +a2 = enc.add(aa, xx)
  +b2 = enc.add(bb, a2)
  Out{Crc.crc.byte(cc, xx), {xx <> acc : List<&2, U32>}, a2, b2}

# stored blocks for colour type 2, one decreasing step at a time: a block's
# header, a raw byte the cursor gives, or the step that closes a full block.
# Block headers match enc.pour. Adler-32 covers the raw bytes only.
def enc.rgb.go(fuel: Nat, bk: Bk, +cr: Cr, out: Out) -> (U32 & List<&2, U32>) & U32:
  match fuel bk out:
    case 0n _b Out{+cc, acc, +aa, +bb}:
      enc.rgb.fin(cc, acc, aa, bb)
    case 1n+_p Bk{True{}, True{}, _s, _n, _nd, _l, _ln} Out{+cc, acc, +aa, +bb}:
      enc.rgb.fin(cc, acc, aa, bb)
    case 1n+p Bk{True{}, False{}, _s, _n, _nd, +left, _ln} Out{+cc, acc, +aa, +bb}:
      +len2 = enc.cap(left)
      enc.rgb.go(p, Bk{False{}, False{}, True{}, False{}, len2, left, len2}, cr, enc.rgb.head(left, cc, acc, aa, bb))
    case 1n+_p Bk{False{}, _d, False{}, _n, _nd, _l, _ln} Out{+cc, acc, +aa, +bb}:
      enc.rgb.fin(cc, acc, aa, bb)
    case 1n+p Bk{False{}, _d, True{}, True{}, +need, +left, +len} Out{+cc, acc, +aa, +bb}:
      +left2 = (left - len : U32)
      enc.rgb.go(p, Bk{True{}, U32.is_zero(left2), False{}, False{}, need, left2, len}, cr, Out{cc, acc, aa, bb})
    case 1n+p Bk{False{}, _d, True{}, False{}, +need, +left, +len} Out{+cc, acc, +aa, +bb}:
      +need2 = (need - 1 : U32)
      enc.rgb.go(p, Bk{False{}, False{}, True{}, U32.is_zero(need2), need2, left, len}, enc.rgb.step(cr),
        enc.rgb.put(enc.rgb.byte(cr), cc, acc, aa, bb))

def enc.wide.rgb.out(pp: (U32 & List<&2, U32>) & U32, ie: List<&2, U32>) -> List<&2, U32>:
  match pp:
    case ((+c, acc), +sum):
      enc.seal.adler((c, acc), sum, ie)

# zlib header, then the stored blocks written from the samples
def enc.wide.rgb.z(
  pp: U32 & List<&2, U32>,
  px: List<&2, U32>,
  +ww: U32,
  +nn: U32,
  ie: List<&2, U32>
) -> List<&2, U32>:
  match pp:
    case (+c, acc):
      +steps = ((nn + (enc.nblk(nn) * 2 : U32) : U32) - 1 : U32)
      got = enc.rgb.go(U32.to_nat(steps), Bk{True{}, False{}, False{}, False{}, 0, nn, 0},
        Cr{True{}, True{}, False{}, False{}, px, 0, ww, ww}, Out{c, acc, 1, 0})
      enc.wide.rgb.out(got, ie)

# IDAT type, then the zlib stream
def enc.wide.rgb.go(
  pp: U32 & List<&2, U32>,
  px: List<&2, U32>,
  +ww: U32,
  +nn: U32,
  ie: List<&2, U32>
) -> List<&2, U32>:
  match pp:
    case (+c, acc):
      enc.wide.rgb.z(enc.crc.list([120, 1], c, acc), px, ww, nn, ie)

# a colour-type-2 picture whose filtered bytes do not fit in one stored block.
# Each filter and channel byte is consed into its stored block, with Adler-32
# and the IDAT CRC, so the raw scanline list is not built. The signature and
# IHDR go in front once the rest is reversed.
def enc.wide.rgb(+ww: U32, +hh: U32, px: List<&2, U32>, +nn: U32) -> List<&2, U32>:
  +ih = enc.chunk(tag.ihdr(), enc.ihdr(ww, hh, enc.ct(True{})))
  +ie = enc.chunk(tag.iend(), [])
  +acc = enc.cat.go(enc.be(enc.idat.ln(nn)), [])
  enc.cat(enc.sig(), enc.cat(ih, enc.wide.rgb.go(enc.crc.list(enc.be(tag.idat()), 4294967295, acc), px, ww, nn, ie)))

# one picture whose filtered bytes do not fit in a single stored block. The
# IDAT length and the payload are consed newest-first and reversed once, then
# the signature and IHDR go in front. Adler-32 stays a separate pass over the
# raw bytes.
def enc.seal.wide(
  +ww: U32,
  +hh: U32,
  op: Bool,
  +raw: List<&2, U32>,
  +nn: U32
) -> List<&2, U32>:
  +ih = enc.chunk(tag.ihdr(), enc.ihdr(ww, hh, enc.ct(op)))
  +ie = enc.chunk(tag.iend(), [])
  +sum = Inf.adler.of(raw)
  +acc = enc.cat.go(enc.be(enc.idat.ln(nn)), [])
  enc.cat(enc.sig(), enc.cat(ih, enc.seal.body(enc.crc.list(enc.be(tag.idat()), 4294967295, acc), raw, nn, sum, ie)))

# signature, IHDR, IDAT, IEND when the raw bytes fit in one stored block
def enc.seal.one(+ww: U32, +hh: U32, op: Bool, +raw: List<&2, U32>, +nn: U32) -> List<&2, U32>:
  +ihdr = enc.chunk(tag.ihdr(), enc.ihdr(ww, hh, enc.ct(op)))
  +idat = enc.chunk(tag.idat(), enc.zlib(raw, nn))
  enc.cat(enc.sig(), enc.cat(ihdr, enc.cat(idat, enc.chunk(tag.iend(), []))))

# one stored block when the payload fits; several blocks written once otherwise
def enc.seal.at(
  zz: Bool,
  +ww: U32,
  +hh: U32,
  op: Bool,
  raw: List<&2, U32>,
  +nn: U32
) -> List<&2, U32>:
  match zz:
    case False{}:
      enc.seal.one(ww, hh, op, raw, nn)
    case True{}:
      enc.seal.wide(ww, hh, op, raw, nn)

# signature, IHDR, IDAT, IEND
def enc.seal(+ww: U32, +hh: U32, op: Bool, got: List<&2, U32> & U32) -> List<&2, U32>:
  match got:
    case (raw, +n):
      enc.seal.at(U32.is_gt(n, 65535), ww, hh, op, raw, n)

# every sample so far is opaque, and `z` carries that fact forward
def enc.opaque(px: List<&2, U32>, zz: Bool) -> Bool:
  match px zz:
    case _px False{}:
      False{}
    case Nil{} True{}:
      True{}
    case +c <> t True{}:
      enc.opaque(t, U32.is_eq(enc.a(c), 255))

# c less w, h times over: for w above 0, true exactly when c is w * h. `zh`
# means no rows are left, `zlt` that c is below w. The samples are fuel: c is
# at most their count, so the walk stops before they run out.
def enc.rows(
  fuel: List<&2, U32>,
  zh: Bool,
  zlt: Bool,
  +ww: U32,
  +hh: U32,
  +cc: U32
) -> Bool:
  match fuel zh zlt:
    case _fuel True{} _zlt:
      U32.is_zero(cc)
    case _fuel False{} True{}:
      False{}
    case Nil{} False{} False{}:
      False{}
    case _px <> rest False{} False{}:
      +c2 = (cc - ww : U32)
      +h2 = (hh - 1 : U32)
      enc.rows(rest, U32.is_zero(h2), U32.is_lt(c2, ww), ww, h2, c2)

# fewer than 2^28 samples: the count's top four bits are clear
def enc.small(+nn: U32) -> Bool:
  U32.is_zero((nn >> 28n : U32))

# a positive area whose sample list covers it, below 2^28 samples: both
# sides above 0, the sample count, taken in a word, is w * h, and that count
# is below 2^28.
#
# The bound keeps every count the encoder takes in a word exact and the one
# IDAT chunk inside PNG's chunk-length limit (ISO/IEC 15948 5.3, 2^31 - 1
# bytes): below 2^28 samples the filtered bytes h (k w + 1), k at most 4,
# are at most 5 * 2^28 - 5, and with a 5-byte header per 65535-byte stored
# block and 6 bytes of zlib framing the IDAT data stays below 1.35e9 bytes.
# That margin is computed here, not proved; the round trip
# (laws/PngRoundTrips.bend) is proved for every raster this accepts.
def enc.good(+ww: U32, +hh: U32, +px: List<&2, U32>) -> Bool:
  +n = enc.len(px, 0)
  Bool.and(Bool.and(U32.is_gt(ww, 0), U32.is_gt(hh, 0)),
    Bool.and(enc.rows(px, U32.is_zero(hh), U32.is_lt(n, ww), ww, hh, n), enc.small(n)))

# filtered bytes: one per row, plus the channels of every sample. enc.good's
# bound keeps the product below 2^31, so the word does not wrap.
def enc.nbytes(op: Bool, +ww: U32, +hh: U32) -> U32:
  (hh * ((ww * enc.nch(op) : U32) + 1 : U32) : U32)

# colour type 6, and a colour type 2 that fits in one block, still build the
# raw list. A larger colour type 2 writes its stored blocks from the samples.
def enc.paint.wide(
  op: Bool,
  +ww: U32,
  +hh: U32,
  px: List<&2, U32>,
  +nn: U32
) -> List<&2, U32>:
  match op:
    case True{}:
      enc.wide.rgb(ww, hh, px, nn)
    case False{}:
      enc.seal(ww, hh, False{}, enc.raw(px, 0n, U32.to_nat(ww), False{}, [], 0))

def enc.paint.at(
  zz: Bool,
  +ww: U32,
  +hh: U32,
  +op: Bool,
  px: List<&2, U32>,
  +nn: U32
) -> List<&2, U32>:
  match zz:
    case False{}:
      enc.seal(ww, hh, op, enc.raw(px, 0n, U32.to_nat(ww), op, [], 0))
    case True{}:
      enc.paint.wide(op, ww, hh, px, nn)

# the PNG bytes of a picture already known to be in range
def enc.paint(+ww: U32, +hh: U32, +op: Bool, px: List<&2, U32>) -> List<&2, U32>:
  +n = enc.nbytes(op, ww, hh)
  enc.paint.at(U32.is_gt(n, 65535), ww, hh, op, px, n)

# the bytes, or none when the picture is not encodable
def enc.open(zz: Bool, +ww: U32, +hh: U32, +px: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match zz:
    case False{}:
      None{}
    case True{}:
      Some{enc.paint(ww, hh, enc.opaque(px, True{}), px)}

# ISO/IEC 15948 / W3C PNG — an 8-bit encoding, interlace 0, filter None.
# Colour type 2 when every sample is opaque, otherwise colour type 6.
def enc.file(+ww: U32, +hh: U32, +px: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  enc.open(enc.good(ww, hh, px), ww, hh, px)
