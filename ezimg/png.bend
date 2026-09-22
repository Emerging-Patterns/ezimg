# ezimg/png: PNG decode and encode (ISO/IEC 15948 / W3C PNG). Chunks, IHDR,
# zlib method 0, and filter method 0. Decode reads 8-bit colour types 0, 2, 3,
# 4, and 6. Encode writes colour type 2 or 6, filter None, and a stored IDAT.
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

# image state while chunks are read
type Pg is Data:
  Pg{
    +w: U32, +h: U32, +depth: U32, +colour: U32, +comp: U32, +filt: U32, +inter: U32,
    idat: List<&2, U32>, plte: List<&2, U32>, trns: List<&2, U32>,
    ihdr: Bool, saw_plte: Bool, saw_idat: Bool, idat_done: Bool, saw_trns: Bool, iend: Bool
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

# transparency key carried by tRNS
type Key is Data:
  KNone{}
  KBad{}
  KGrey{+g: U32}
  KRgb{+r: U32, +g: U32, +b: U32}

# big-endian unsigned 32
def be.u32(+a: U32, +b: U32, +c: U32, +d: U32) -> U32:
  ((((a << 24n : U32) .|. (b << 16n : U32) : U32) .|. (c << 8n : U32) : U32) .|. d : U32)

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

# colour types this decoder accepts
def png.col(+c: U32) -> Bool:
  Bool.or(
    Bool.or(U32.is_eq(c, 0), U32.is_eq(c, 2)),
    Bool.or(U32.is_eq(c, 3), Bool.or(U32.is_eq(c, 4), U32.is_eq(c, 6)))
  )

# IHDR constraints for the supported subset
def png.good(+w: U32, +h: U32, +d: U32, +c: U32, +comp: U32, +f: U32, +i: U32) -> Bool:
  Bool.and(
    Bool.and(U32.is_gt(w, 0), U32.is_gt(h, 0)),
    Bool.and(
      Bool.and(U32.is_eq(d, 8), png.col(c)),
      Bool.and(U32.is_zero(comp), Bool.and(U32.is_zero(f), U32.is_zero(i)))
    )
  )

# an empty image state
def pg.empty() -> Pg:
  Pg{0, 0, 0, 0, 0, 0, 0, [], [], [], False{}, False{}, False{}, False{}, False{}, False{}}

# state after a valid IHDR
def pg.ihdr(+w: U32, +h: U32, +d: U32, +c: U32, +comp: U32, +f: U32, +i: U32) -> Pg:
  Pg{w, h, d, c, comp, f, i, [], [], [], True{}, False{}, False{}, False{}, False{}, False{}}

# close the IDAT sequence once a later chunk appears
def png.seal(pg: Pg) -> Pg:
  match pg:
    case Pg{+w, +h, +d, +c, +comp, +f, +i, idat, plte, trns, ihdr, saw_plte, +saw_idat, idat_done, saw_trns, iend}:
      Pg{w, h, d, c, comp, f, i, idat, plte, trns, ihdr, saw_plte, saw_idat, Bool.or(saw_idat, idat_done), saw_trns,
        iend}

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

def png.bpp6(z6: Bool, +c: U32) -> U32:
  match z6:
    case True{}:
      4
    case False{}:
      png.bpp.one(U32.is_eq(c, 0), U32.is_eq(c, 3))

def png.bpp4(z4: Bool, z6: Bool, +c: U32) -> U32:
  match z4:
    case True{}:
      2
    case False{}:
      png.bpp6(z6, c)

def png.bpp0(z2: Bool, z4: Bool, z6: Bool, +c: U32) -> U32:
  match z2:
    case True{}:
      3
    case False{}:
      png.bpp4(z4, z6, c)

# bytes per pixel for an 8-bit colour type
def png.bpp(+c: U32) -> U32:
  png.bpp0(U32.is_eq(c, 2), U32.is_eq(c, 4), U32.is_eq(c, 6), c)

# ISO/IEC 15948 / W3C PNG — IHDR is width, height, bit depth, colour type,
# compression method, filter method, and interlace method, each big-endian.
def parse_ihdr(xs: List<&2, U32>) -> Maybe<&2, Ihdr>:
  match xs:
    case +a <> +b <> +c <> +d <> +e <> +f <> +g <> +h <> +i <> +j <> +k <> +l <> +m <> Nil{}:
      Some{Ihdr{be.u32(a, b, c, d), be.u32(e, f, g, h), i, j, k, l, m}}
    case _other:
      None{}

# ---- scanline filters (None, Sub, Up, Average, Paeth) ----

def uf.nth(xs: List<&2, U32>, z: Bool, +i: U32) -> U32:
  match xs z:
    case Nil{} _z:
      0
    case +h <> _t True{}:
      h
    case _h <> t False{}:
      uf.nth(t, U32.is_zero((i - 1 : U32)), (i - 1 : U32))

def uf.back.at(z: Bool, xs: List<&2, U32>, +i: U32) -> U32:
  match z:
    case True{}:
      0
    case False{}:
      uf.nth(xs, U32.is_zero(i), i)

# the byte `bpp` back, or zero before the first pixel
def uf.back(xs: List<&2, U32>, +bpp: U32, +x: U32) -> U32:
  uf.back.at(U32.is_lt(x, bpp), xs, (bpp - 1 : U32))

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

def uf.abs.at(+hi: U32, +lo: U32, z: Bool) -> U32:
  match z:
    case True{}:
      hi
    case False{}:
      lo

def uf.abs(+x: U32, +y: U32) -> U32:
  uf.abs.at((x - y : U32), (y - x : U32), U32.is_ge(x, y))

def uf.paeth.b(zb: Bool, +b: U32, +c: U32) -> U32:
  match zb:
    case True{}:
      b
    case False{}:
      c

def uf.paeth.at(za: Bool, zb: Bool, +a: U32, +b: U32, +c: U32) -> U32:
  match za:
    case True{}:
      a
    case False{}:
      uf.paeth.b(zb, b, c)

# PaethPredictor from the PNG specification
def uf.paeth(+a: U32, +b: U32, +c: U32) -> U32:
  +pa = uf.abs(b, c)
  +pb = uf.abs(a, c)
  +pc = uf.abs((a + b : U32), (c << 1n : U32))
  uf.paeth.at(Bool.and(U32.is_le(pa, pb), U32.is_le(pa, pc)), U32.is_le(pb, pc), a, b, c)

def uf.avg(+a: U32, +b: U32) -> U32:
  ((a + b : U32) >> 1n : U32)

def uf.add(+f: U32, +p: U32) -> U32:
  ((f + p : U32) .&. 255 : U32)

def uf.p4(z4: Bool, +a: U32, +b: U32, +c: U32) -> U32:
  match z4:
    case True{}:
      uf.paeth(a, b, c)
    case False{}:
      0

def uf.p3(z3: Bool, z4: Bool, +a: U32, +b: U32, +c: U32) -> U32:
  match z3:
    case True{}:
      uf.avg(a, b)
    case False{}:
      uf.p4(z4, a, b, c)

def uf.p2(z2: Bool, z3: Bool, z4: Bool, +a: U32, +b: U32, +c: U32) -> U32:
  match z2:
    case True{}:
      b
    case False{}:
      uf.p3(z3, z4, a, b, c)

def uf.p1(z1: Bool, z2: Bool, z3: Bool, z4: Bool, +a: U32, +b: U32, +c: U32) -> U32:
  match z1:
    case True{}:
      a
    case False{}:
      uf.p2(z2, z3, z4, a, b, c)

def uf.pred(+ft: U32, +a: U32, +b: U32, +c: U32) -> U32:
  uf.p1(U32.is_eq(ft, 1), U32.is_eq(ft, 2), U32.is_eq(ft, 3), U32.is_eq(ft, 4), a, b, c)

def uf.recon(+f: U32, +ft: U32, +bpp: U32, +x: U32, prest: List<&2, U32>, phist: List<&2, U32>,
  cur: List<&2, U32>) -> U32:
  uf.add(f, uf.pred(ft, uf.back(cur, bpp, x), uf.bb(prest), uf.back(phist, bpp, x)))

def uf.phase(z: Bool) -> Uf:
  match z:
    case True{}:
      UBody{}
    case False{}:
      UBad{}

def uf.ok(+w: U32, +h: U32, +bpp: U32) -> Bool:
  Bool.and(U32.is_gt(w, 0), Bool.and(U32.is_gt(h, 0), Bool.and(U32.is_gt(bpp, 0), U32.is_le(bpp, 4))))

def uf.done(rows: Nat, all: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match rows:
    case 0n:
      Some{List.reverse(&2, U32, all)}
    case 1n+_p:
      None{}

def uf.go(
  xs: List<&2, U32>, ph: Uf, zlast: Bool, +bpp: U32, +stride: U32, rows: Nat,
  +prest: List<&2, U32>, +phist: List<&2, U32>, +cur: List<&2, U32>, all: List<&2, U32>,
  +x: U32, +ft: U32
) -> Maybe<&2, List<&2, U32>>:
  match xs ph zlast:
    case _xs UBad{} _z:
      None{}
    case Nil{} UFilt{} _z:
      uf.done(rows, all)
    case +b <> rest UFilt{} _z:
      match rows:
        case 0n:
          None{}
        case 1n++r:
          uf.go(
            rest, uf.phase(U32.is_le(b, 4)), U32.is_eq(stride, 1), bpp, stride, r,
            prest, [], [], all, 0, b
          )
    case +b <> rest UBody{} True{}:
      +y = uf.recon(b, ft, bpp, x, prest, phist, cur)
      +cur2 = {y <> cur : List<&2, U32>}
      uf.go(
        rest, UFilt{}, False{}, bpp, stride, rows, List.reverse(&2, U32, cur2),
        [], [], {y <> all : List<&2, U32>}, 0, 0
      )
    case +b <> rest UBody{} False{}:
      +y = uf.recon(b, ft, bpp, x, prest, phist, cur)
      uf.go(
        rest, UBody{}, U32.is_eq((x + 2 : U32), stride), bpp, stride, rows,
        uf.drop(prest), uf.push(prest, phist), {y <> cur : List<&2, U32>},
        {y <> all : List<&2, U32>}, (x + 1 : U32), ft
      )
    case Nil{} UBody{} _z:
      None{}

def uf.start(z: Bool, raw: List<&2, U32>, +w: U32, +h: U32, +bpp: U32) -> Maybe<&2, List<&2, U32>>:
  match z:
    case False{}:
      None{}
    case True{}:
      uf.go(raw, UFilt{}, False{}, bpp, (w * bpp : U32), U32.to_nat(h), [], [], [], [], 0, 0)

# ISO/IEC 15948 / W3C PNG — undo filter types None, Sub, Up, Average, and Paeth.
def unfilter(raw: List<&2, U32>, +w: U32, +h: U32, +bpp: U32) -> Maybe<&2, List<&2, U32>>:
  uf.start(uf.ok(w, h, bpp), raw, w, h, bpp)

# ---- samples to 0xAARRGGBB ----

def px.pack(+a: U32, +r: U32, +g: U32, +b: U32) -> U32:
  ((((a << 24n : U32) .|. (r << 16n : U32) : U32) .|. (g << 8n : U32) : U32) .|. b : U32)

def px.seta(+c: U32, +a: U32) -> U32:
  (((c .&. 16777215 : U32) .|. (a << 24n : U32) : U32))

def px.hit.at(z: Bool) -> U32:
  match z:
    case True{}:
      0
    case False{}:
      255

def px.hit(+s: U32, +k: U32) -> U32:
  px.hit.at(U32.is_eq(s, k))

def px.rgb.hit(+r: U32, +g: U32, +b: U32, +kr: U32, +kg: U32, +kb: U32) -> U32:
  px.hit.at(Bool.and(U32.is_eq(r, kr), Bool.and(U32.is_eq(g, kg), U32.is_eq(b, kb))))

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

def px.at(xs: List<&2, U32>, z: Bool, +i: U32) -> Maybe<&2, U32>:
  match xs z:
    case Nil{} _z:
      None{}
    case +h <> _t True{}:
      Some{h}
    case _h <> t False{}:
      px.at(t, U32.is_zero((i - 1 : U32)), (i - 1 : U32))

def px.use(m: Maybe<&2, U32>, k: U32 -> Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}:
      None{}
    case Some{+c}:
      k(c)

def px.idx(xs: List<&2, U32>, +pal: List<&2, U32>, acc: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Some{List.reverse(&2, U32, acc)}
    case +i <> t:
      px.use(px.at(pal, U32.is_zero(i), i), c => px.idx(t, pal, {c <> acc : List<&2, U32>}))

def pal.make(xs: List<&2, U32>, acc: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Some{List.reverse(&2, U32, acc)}
    case +r <> +g <> +b <> t:
      pal.make(t, {px.pack(255, r, g, b) <> acc : List<&2, U32>})
    case _other:
      None{}

def pal.tint(pxs: List<&2, U32>, als: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match pxs als:
    case Nil{} _als:
      List.reverse(&2, U32, acc)
    case +c <> t Nil{}:
      pal.tint(t, [], {px.seta(c, 255) <> acc : List<&2, U32>})
    case +c <> t +a <> at:
      pal.tint(t, at, {px.seta(c, a) <> acc : List<&2, U32>})

def png.le(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  U32.is_le(U32.from_nat(List.length(&2, U32, xs)), U32.from_nat(List.length(&2, U32, ys)))

def pal.gate(z: Bool, +als: List<&2, U32>, +pxs: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match z:
    case False{}:
      None{}
    case True{}:
      Some{pal.tint(pxs, als, [])}

def pal.ready(m: Maybe<&2, List<&2, U32>>, +als: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}:
      None{}
    case Some{+pxs}:
      pal.gate(png.le(als, pxs), als, pxs)

def px.indexed.at(m: Maybe<&2, List<&2, U32>>, samples: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}:
      None{}
    case Some{pal}:
      px.idx(samples, pal, [])

def px.indexed(samples: List<&2, U32>, plte: List<&2, U32>, trns: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  px.indexed.at(pal.ready(pal.make(plte, []), trns), samples)

def key.grey(xs: List<&2, U32>) -> Key:
  match xs:
    case Nil{}:
      KNone{}
    case 0 <> +g <> Nil{}:
      KGrey{g}
    case _other:
      KBad{}

def key.rgb(xs: List<&2, U32>) -> Key:
  match xs:
    case Nil{}:
      KNone{}
    case 0 <> +r <> 0 <> +g <> 0 <> +b <> Nil{}:
      KRgb{r, g, b}
    case _other:
      KBad{}

def key.none(xs: List<&2, U32>) -> Key:
  match xs:
    case Nil{}:
      KNone{}
    case _other:
      KBad{}

def px.ga.ok(key: Key, samples: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match key:
    case KNone{}:
      px.ga(samples, [])
    case _k:
      None{}

def px.rgba.ok(key: Key, samples: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match key:
    case KNone{}:
      px.rgba(samples, [])
    case _k:
      None{}

def px.rgba.go(samples: List<&2, U32>, trns: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  px.rgba.ok(key.none(trns), samples)

def px.k4(z6: Bool, samples: List<&2, U32>, plte: List<&2, U32>, trns: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match z6:
    case True{}:
      px.rgba.go(samples, trns)
    case False{}:
      px.indexed(samples, plte, trns)

def px.k3(z4: Bool, z6: Bool, samples: List<&2, U32>, plte: List<&2, U32>,
  trns: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match z4:
    case False{}:
      px.k4(z6, samples, plte, trns)
    case True{}:
      px.ga.ok(key.none(trns), samples)

def px.k2(z2: Bool, z4: Bool, z6: Bool, samples: List<&2, U32>, plte: List<&2, U32>,
  trns: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match z2:
    case True{}:
      px.rgb(samples, key.rgb(trns), [])
    case False{}:
      px.k3(z4, z6, samples, plte, trns)

def px.k0(z0: Bool, z2: Bool, z4: Bool, z6: Bool, samples: List<&2, U32>, plte: List<&2, U32>,
  trns: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match z0:
    case True{}:
      px.grey(samples, key.grey(trns), [])
    case False{}:
      px.k2(z2, z4, z6, samples, plte, trns)

def px.of(+colour: U32, samples: List<&2, U32>, plte: List<&2, U32>, trns: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  px.k0(U32.is_eq(colour, 0), U32.is_eq(colour, 2), U32.is_eq(colour, 4), U32.is_eq(colour, 6), samples, plte, trns)

# ---- chunks ----

def png.mod3(xs: List<&2, U32>) -> Bool:
  +n = U32.from_nat(List.length(&2, U32, xs))
  Bool.and(U32.is_gt(n, 0), Bool.and(U32.is_zero((n % 3 : U32)), U32.is_le(n, 768)))

def png.ihdr.ok(z: Bool, +w: U32, +h: U32, +d: U32, +c: U32, +comp: U32, +f: U32, +i: U32) -> Nx:
  match z:
    case False{}:
      NBad{}
    case True{}:
      NMore{pg.ihdr(w, h, d, c, comp, f, i)}

def png.ihdr.put(m: Maybe<&2, Ihdr>) -> Nx:
  match m:
    case None{}:
      NBad{}
    case Some{Ihdr{+w, +h, +d, +c, +comp, +f, +i}}:
      png.ihdr.ok(png.good(w, h, d, c, comp, f, i), w, h, d, c, comp, f, i)

def png.allow(z: Bool, pg: Pg) -> Nx:
  match z:
    case True{}:
      NMore{pg}
    case False{}:
      NBad{}

def pg.idat(pg: Pg, extra: List<&2, U32>) -> Pg:
  match pg:
    case Pg{+w, +h, +d, +c, +comp, +f, +i, idat, plte, trns, ihdr, saw_plte, _sid, idat_done, saw_trns, iend}:
      Pg{w, h, d, c, comp, f, i, List.append(&2, U32, extra, idat), plte, trns, ihdr, saw_plte, True{}, idat_done,
        saw_trns, iend}

def pg.plte(pg: Pg, bytes: List<&2, U32>) -> Pg:
  match pg:
    case Pg{+w, +h, +d, +c, +comp, +f, +i, idat, _pl, trns, ihdr, _sp, saw_idat, idat_done, saw_trns, iend}:
      Pg{w, h, d, c, comp, f, i, idat, bytes, trns, ihdr, True{}, saw_idat, idat_done, saw_trns, iend}

def pg.trns(pg: Pg, bytes: List<&2, U32>) -> Pg:
  match pg:
    case Pg{+w, +h, +d, +c, +comp, +f, +i, idat, plte, _tr, ihdr, saw_plte, saw_idat, idat_done, _st, iend}:
      Pg{w, h, d, c, comp, f, i, idat, plte, bytes, ihdr, saw_plte, saw_idat, idat_done, True{}, iend}

def pg.iend(pg: Pg) -> Pg:
  match pg:
    case Pg{+w, +h, +d, +c, +comp, +f, +i, idat, plte, trns, ihdr, saw_plte, saw_idat, _done, saw_trns, _ie}:
      Pg{w, h, d, c, comp, f, i, idat, plte, trns, ihdr, saw_plte, saw_idat, True{}, saw_trns, True{}}

def png.idat.try(z: Bool, data: List<&2, U32>, pg: Pg) -> Nx:
  match z:
    case False{}:
      NBad{}
    case True{}:
      NMore{pg.idat(pg, data)}

def png.on.ihdr(ihdr: Bool, data: List<&2, U32>) -> Nx:
  match ihdr:
    case True{}:
      NBad{}
    case False{}:
      png.ihdr.put(parse_ihdr(List.reverse(&2, U32, data)))

def png.on.idat(ihdr: Bool, idat_done: Bool, need: Bool, data: List<&2, U32>, pg: Pg) -> Nx:
  match ihdr:
    case False{}:
      NBad{}
    case True{}:
      png.idat.try(Bool.and(Bool.not(idat_done), need), data, pg)

def png.plte.ok(+c: U32) -> Bool:
  Bool.or(U32.is_eq(c, 2), Bool.or(U32.is_eq(c, 3), U32.is_eq(c, 6)))

def png.trns.ok(+c: U32, saw_plte: Bool) -> Bool:
  Bool.or(
    Bool.or(U32.is_eq(c, 0), U32.is_eq(c, 2)),
    Bool.and(U32.is_eq(c, 3), saw_plte)
  )

def png.on.plte(ihdr: Bool, saw_plte: Bool, saw_idat: Bool, +colour: U32, +data: List<&2, U32>, pg: Pg) -> Nx:
  match ihdr:
    case False{}:
      NBad{}
    case True{}:
      png.allow(
        Bool.and(Bool.not(saw_plte), Bool.and(Bool.not(saw_idat), Bool.and(png.plte.ok(colour), png.mod3(data)))),
        pg.plte(pg, List.reverse(&2, U32, data))
      )

def png.on.trns(ihdr: Bool, saw_trns: Bool, saw_idat: Bool, +colour: U32, saw_plte: Bool, data: List<&2, U32>,
  pg: Pg) -> Nx:
  match ihdr:
    case False{}:
      NBad{}
    case True{}:
      png.allow(
        Bool.and(Bool.not(saw_trns), Bool.and(Bool.not(saw_idat), png.trns.ok(colour, saw_plte))),
        pg.trns(pg, List.reverse(&2, U32, data))
      )

def png.iend.ok(z: Bool, pg: Pg) -> Nx:
  match z:
    case False{}:
      NBad{}
    case True{}:
      NEnd{pg.iend(pg)}

def png.iend.at(zempty: Bool, zpal: Bool, pg: Pg) -> Nx:
  match zempty:
    case False{}:
      NBad{}
    case True{}:
      png.iend.ok(zpal, pg)

def png.on.iend(ihdr: Bool, +colour: U32, saw_plte: Bool, data: List<&2, U32>, pg: Pg) -> Nx:
  match ihdr:
    case False{}:
      NBad{}
    case True{}:
      png.iend.at(List.is_empty(&2, U32, data), Bool.or(Bool.not(U32.is_eq(colour, 3)), saw_plte), pg)

def png.other.at(anc: Bool, pg: Pg) -> Nx:
  match anc:
    case False{}:
      NBad{}
    case True{}:
      NMore{png.seal(pg)}

def png.on.other(ihdr: Bool, anc: Bool, pg: Pg) -> Nx:
  match ihdr:
    case False{}:
      NBad{}
    case True{}:
      png.other.at(anc, pg)

def png.apply.tr(
  ztrns: Bool, anc: Bool, ihdr: Bool, saw_plte: Bool, saw_idat: Bool, saw_trns: Bool,
  +colour: U32, data: List<&2, U32>, pg: Pg
) -> Nx:
  match ztrns:
    case True{}:
      png.on.trns(ihdr, saw_trns, saw_idat, colour, saw_plte, data, pg)
    case False{}:
      png.on.other(ihdr, anc, pg)

def png.apply.pl(
  zplte: Bool, ztrns: Bool, anc: Bool, ihdr: Bool, saw_plte: Bool, saw_idat: Bool, saw_trns: Bool,
  +colour: U32, data: List<&2, U32>, pg: Pg
) -> Nx:
  match zplte:
    case True{}:
      png.on.plte(ihdr, saw_plte, saw_idat, colour, data, pg)
    case False{}:
      png.apply.tr(ztrns, anc, ihdr, saw_plte, saw_idat, saw_trns, colour, data, pg)

def png.apply.ie(
  ziend: Bool, zplte: Bool, ztrns: Bool, anc: Bool,
  ihdr: Bool, saw_plte: Bool, saw_idat: Bool, saw_trns: Bool,
  +colour: U32, data: List<&2, U32>, pg: Pg
) -> Nx:
  match ziend:
    case True{}:
      png.on.iend(ihdr, colour, saw_plte, data, pg)
    case False{}:
      png.apply.pl(zplte, ztrns, anc, ihdr, saw_plte, saw_idat, saw_trns, colour, data, pg)

def png.apply.id(
  zidat: Bool, ziend: Bool, zplte: Bool, ztrns: Bool, anc: Bool,
  ihdr: Bool, saw_plte: Bool, saw_idat: Bool, idat_done: Bool, saw_trns: Bool,
  +colour: U32, data: List<&2, U32>, pg: Pg
) -> Nx:
  match zidat:
    case True{}:
      png.on.idat(ihdr, idat_done, Bool.or(Bool.not(U32.is_eq(colour, 3)), saw_plte), data, pg)
    case False{}:
      png.apply.ie(ziend, zplte, ztrns, anc, ihdr, saw_plte, saw_idat, saw_trns, colour, data, pg)

def png.apply.go(
  zihdr: Bool, zidat: Bool, ziend: Bool, zplte: Bool, ztrns: Bool, anc: Bool,
  ihdr: Bool, saw_plte: Bool, saw_idat: Bool, idat_done: Bool, saw_trns: Bool,
  +colour: U32, data: List<&2, U32>, pg: Pg
) -> Nx:
  match zihdr:
    case True{}:
      png.on.ihdr(ihdr, data)
    case False{}:
      png.apply.id(zidat, ziend, zplte, ztrns, anc, ihdr, saw_plte, saw_idat, idat_done, saw_trns, colour, data, pg)

def png.apply.at(
  iend: Bool, zihdr: Bool, zidat: Bool, ziend: Bool, zplte: Bool, ztrns: Bool, anc: Bool,
  ihdr: Bool, saw_plte: Bool, saw_idat: Bool, idat_done: Bool, saw_trns: Bool,
  +colour: U32, data: List<&2, U32>, pg: Pg
) -> Nx:
  match iend:
    case True{}:
      NBad{}
    case False{}:
      png.apply.go(zihdr, zidat, ziend, zplte, ztrns, anc, ihdr, saw_plte, saw_idat, idat_done, saw_trns, colour, data,
        pg)

def png.apply(+typ: U32, data: List<&2, U32>, pg: Pg) -> Nx:
  match pg:
    case Pg{+w, +h, +d, +colour, +comp, +f, +i, idat, plte, trns, +ihdr, +saw_plte, +saw_idat, +idat_done, +saw_trns,
      +iend}:
      png.apply.at(
        iend, U32.is_eq(typ, tag.ihdr()), U32.is_eq(typ, tag.idat()), U32.is_eq(typ, tag.iend()),
        U32.is_eq(typ, tag.plte()), U32.is_eq(typ, tag.trns()), tag.anc(typ),
        ihdr, saw_plte, saw_idat, idat_done, saw_trns, colour, data,
        Pg{w, h, d, colour, comp, f, i, idat, plte, trns, ihdr, saw_plte, saw_idat, idat_done, saw_trns, iend}
      )

def png.judge.at(z: Bool, +typ: U32, data: List<&2, U32>, pg: Pg) -> Nx:
  match z:
    case False{}:
      NBad{}
    case True{}:
      png.apply(typ, data, pg)

def png.judge(+got: U32, crc: List<&2, U32>, +typ: U32, data: List<&2, U32>, pg: Pg) -> Nx:
  png.judge.at(U32.is_eq(got, Crc.crc32(List.reverse(&2, U32, crc))), typ, data, pg)

def png.pgof(nx: Nx) -> Pg:
  match nx:
    case NBad{}:
      pg.empty()
    case NEnd{pg}:
      pg
    case NMore{pg}:
      pg

def png.zp(z: Bool) -> Pz:
  match z:
    case True{}:
      ZCrc{}
    case False{}:
      ZDat{}

def png.pic(m: Maybe<&2, List<&2, U32>>, +w: U32, +h: U32) -> Maybe<&2, Pic>:
  match m:
    case None{}:
      None{}
    case Some{px}:
      Some{Pic{w, h, px}}

def png.pack(m: Maybe<&2, List<&2, U32>>, +w: U32, +h: U32, +colour: U32, plte: List<&2, U32>,
  trns: List<&2, U32>) -> Maybe<&2, Pic>:
  match m:
    case None{}:
      None{}
    case Some{samples}:
      png.pic(px.of(colour, samples, plte, trns), w, h)

def png.samples(m: Maybe<&2, List<&2, U32>>, +w: U32, +h: U32, +colour: U32, plte: List<&2, U32>,
  trns: List<&2, U32>) -> Maybe<&2, Pic>:
  match m:
    case None{}:
      None{}
    case Some{raw}:
      png.pack(unfilter(raw, w, h, png.bpp(colour)), w, h, colour, plte, trns)

def png.finish.go(zenc: Bool, +w: U32, +h: U32, +colour: U32, idat: List<&2, U32>, plte: List<&2, U32>,
  trns: List<&2, U32>) -> Maybe<&2, Pic>:
  match zenc:
    case False{}:
      None{}
    case True{}:
      png.samples(Inf.inflate(List.reverse(&2, U32, idat)), w, h, colour, plte, trns)

def png.finish.at(z: Bool, zenc: Bool, +w: U32, +h: U32, +colour: U32, idat: List<&2, U32>, plte: List<&2, U32>,
  trns: List<&2, U32>) -> Maybe<&2, Pic>:
  match z:
    case False{}:
      None{}
    case True{}:
      png.finish.go(zenc, w, h, colour, idat, plte, trns)

def png.finish(pg: Pg) -> Maybe<&2, Pic>:
  match pg:
    case Pg{+w, +h, +d, +colour, +comp, +f, +i, idat, plte, trns, ihdr, _sp, _si, _sd, _st, iend}:
      png.finish.at(Bool.and(ihdr, iend), Bool.and(U32.is_eq(d, 8), Bool.and(U32.is_zero(comp), Bool.and(U32.is_zero(f),
        U32.is_zero(i)))), w, h, colour, idat, plte, trns)

def png.crc(nx: Nx, empty: Bool, more: Maybe<&2, Pic>) -> Maybe<&2, Pic>:
  match nx empty:
    case NBad{} _e:
      None{}
    case NEnd{_pg} False{}:
      None{}
    case NEnd{pg} True{}:
      png.finish(pg)
    case NMore{_pg} _e:
      more

# one byte of a PNG chunk stream. `zlast` is the last data byte of the chunk.
def png.go(
  xs: List<&2, U32>, pz: Pz, zlast: Bool, +left: U32, +typ: U32,
  crc: List<&2, U32>, data: List<&2, U32>, pg: Pg
) -> Maybe<&2, Pic>:
  match xs pz zlast:
    case Nil{} _pz _z:
      None{}
    case +a <> +b <> +c <> +d <> rest ZLen{} _z:
      png.go(rest, ZTyp{}, False{}, be.u32(a, b, c, d), 0, [], [], pg)
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
    case +a <> +b <> +c <> +d <> +rest ZCrc{} _z:
      +nx = png.judge(be.u32(a, b, c, d), crc, typ, data, pg)
      png.crc(nx, List.is_empty(&2, U32, rest), png.go(rest, ZLen{}, False{}, 0, 0, [], [], png.pgof(nx)))
    case _xs _pz _z:
      None{}

# ISO/IEC 15948 / W3C PNG — chunks after the signature, CRC-32 over type and
# data, then IDAT inflated as zlib DEFLATE (compression method 0).
def decode(xs: List<&2, U32>) -> Maybe<&2, Pic>:
  png.go(xs, ZLen{}, False{}, 0, 0, [], [], pg.empty())

# ---- encode (colour type 2 or 6, filter None, stored-block IDAT) ----

# the low byte
def enc.byte(+n: U32) -> U32:
  (n .&. 255 : U32)

# the next byte up
def enc.hi(+n: U32) -> U32:
  ((n >> 8n : U32) .&. 255 : U32)

# four bytes, big-endian
def enc.be(+n: U32) -> List<&2, U32>:
  [((n >> 24n : U32) .&. 255 : U32), ((n >> 16n : U32) .&. 255 : U32), enc.hi(n), enc.byte(n)]

# alpha of a 0xAARRGGBB sample
def enc.a(+c: U32) -> U32:
  ((c >> 24n : U32) .&. 255 : U32)


# one less, or zero
def enc.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

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

# Adler-32 sum reduced once. s is below twice the modulus.
def enc.add.at(z: Bool, +t: U32) -> U32:
  match z:
    case True{}:
      (t - 65521 : U32)
    case False{}:
      t

# one Adler add, modulo 65521
def enc.add(+s: U32, +x: U32) -> U32:
  +t = (s + x : U32)
  enc.add.at(U32.is_ge(t, 65521), t)

# the five-byte stored-block header: BFINAL, then LEN and NLEN, little-endian
def enc.head(fin: Bool, +len: U32, +nlen: U32) -> List<&2, U32>:
  match fin:
    case True{}:
      [1, enc.byte(len), enc.hi(len), enc.byte(nlen), enc.hi(nlen)]
    case False{}:
      [0, enc.byte(len), enc.hi(len), enc.byte(nlen), enc.hi(nlen)]

# one stored DEFLATE block. `data` is chronological and is used once.
def enc.stored(fin: Bool, +len: U32, data: List<&2, U32>) -> List<&2, U32>:
  enc.cat(enc.head(fin, len, (len .^. 65535 : U32)), data)

# stored blocks of at most `max` bytes. `z` means this byte opens a block.
# `room` is the space left in the open block, so its length is `max - room`.
def enc.feed(
  xs: List<&2, U32>,
  z: Bool,
  +room: U32,
  +max: U32,
  acc: List<&2, U32>
) -> List<&2, U32>:
  match xs z:
    case Nil{} _z:
      enc.stored(True{}, (max - room : U32), List.reverse(&2, U32, acc))
    case +h <> t True{}:
      +nxt = (max - 1 : U32)
      +len = (max - room : U32)
      +blk = enc.stored(False{}, len, List.reverse(&2, U32, acc))
      enc.cat(blk, enc.feed(t, U32.is_zero(nxt), nxt, max, [h]))
    case +h <> t False{}:
      +nxt = (room - 1 : U32)
      enc.feed(t, U32.is_zero(nxt), nxt, max, {h <> acc : List<&2, U32>})

# stored DEFLATE blocks, each at most `max` bytes, the last one final
def enc.blocks(+max: U32, xs: List<&2, U32>) -> List<&2, U32>:
  enc.feed(xs, U32.is_zero(max), max, max, [])

# a chunk: length, type, data, and a CRC-32 already folded over type and data
def enc.chunk(+tag: U32, data: List<&2, U32>, +n: U32, +crc: U32) -> List<&2, U32>:
  +body = enc.cat(enc.be(tag), data)
  enc.cat(enc.be(n), enc.cat(body, enc.be(crc)))

# IHDR: width, height, depth 8, colour type, method 0, filter 0, interlace 0
def enc.ihdr(+w: U32, +h: U32, +ct: U32) -> List<&2, U32>:
  enc.cat(enc.be(w), enc.cat(enc.be(h), [8, ct, 0, 0, 0]))

# CRC-32 of the IHDR type and its thirteen data bytes
def enc.ihdr.crc(+w: U32, +h: U32, +ct: U32) -> U32:
  +body = enc.cat(enc.be(tag.ihdr()), enc.ihdr(w, h, ct))
  (Crc.crc.fold(body, 4294967295) .^. 4294967295 : U32)

# CRC-32 of the IEND type
def enc.iend.crc() -> U32:
  (Crc.crc.fold(enc.be(tag.iend()), 4294967295) .^. 4294967295 : U32)

# running CRC after the IDAT type, the zlib header, and one stored-block header
def enc.idat.crc0(+n: U32) -> U32:
  +nlen = (n .^. 65535 : U32)
  +pre = enc.cat(enc.be(tag.idat()), enc.cat([120, 1], enc.head(True{}, n, nlen)))
  Crc.crc.fold(pre, 4294967295)

# the eight-byte signature
def enc.sig() -> List<&2, U32>:
  [137, 80, 78, 71, 13, 10, 26, 10]

# signature, IHDR, IDAT, IEND. Each list is consumed once.
def enc.wrap(
  +w: U32,
  +h: U32,
  +ct: U32,
  idat: List<&2, U32>,
  +ln: U32,
  +crc: U32
) -> List<&2, U32>:
  +ih = enc.chunk(tag.ihdr(), enc.ihdr(w, h, ct), 13, enc.ihdr.crc(w, h, ct))
  +id = enc.chunk(tag.idat(), idat, ln, crc)
  +ie = enc.chunk(tag.iend(), [], 0, enc.iend.crc())
  enc.cat(enc.sig(), enc.cat(ih, enc.cat(id, ie)))

# how many stored blocks cover `n` raw bytes
def enc.nblk(+n: U32) -> U32:
  U32.div((n + 65534 : U32), 65535)

# fold CRC while reversing, then the fix restores order
def enc.crc.spin(xs: List<&2, U32>, acc: List<&2, U32>, +c: U32) -> List<&2, U32> & U32:
  match xs:
    case Nil{}:
      (acc, c)
    case +h <> t:
      enc.crc.spin(t, {h <> acc : List<&2, U32>}, Crc.crc.byte(c, h))

# chronological bytes and the running CRC from a newest-first fold
def enc.crc.fix(got: List<&2, U32> & U32) -> List<&2, U32> & U32:
  match got:
    case (rev, +c):
      (List.reverse(&2, U32, rev), c)

# IDAT from a rebuilt chunk body and its running CRC
def enc.large.crc(
  +w: U32,
  +h: U32,
  +ct: U32,
  +ln: U32,
  got: List<&2, U32> & U32
) -> List<&2, U32>:
  match got:
    case (body, +c):
      enc.wrap(w, h, ct, body, ln, (c .^. 4294967295 : U32))

# zlib bytes of several stored blocks. `raw` is newest-first.
def enc.large(
  +w: U32,
  +h: U32,
  +ct: U32,
  +n: U32,
  raw: List<&2, U32>,
  +a: U32,
  +b: U32,
  _c: U32
) -> List<&2, U32>:
  +sum = ((b << 16n : U32) .|. a : U32)
  +ln = ((n + (enc.nblk(n) * 5 : U32) : U32) + 6 : U32)
  +z = enc.cat([120, 1], enc.cat(enc.blocks(65535, List.reverse(&2, U32, raw)), enc.be(sum)))
  +body = enc.cat(enc.be(tag.idat()), z)
  enc.large.crc(w, h, ct, ln, enc.crc.fix(enc.crc.spin(body, [], 4294967295)))

# one stored block. `raw` is newest-first; `c` already covers the block header.
def enc.small(
  +w: U32,
  +h: U32,
  +ct: U32,
  +n: U32,
  raw: List<&2, U32>,
  +a: U32,
  +b: U32,
  +c: U32
) -> List<&2, U32>:
  +sum = ((b << 16n : U32) .|. a : U32)
  +crc = (Crc.crc.fold(enc.be(sum), c) .^. 4294967295 : U32)
  +nlen = (n .^. 65535 : U32)
  +body = enc.cat.go(raw, enc.be(sum))
  +payload = enc.cat([120, 1], enc.cat(enc.head(True{}, n, nlen), body))
  enc.wrap(w, h, ct, payload, (n + 11 : U32), crc)

# one block when the raw bytes fit, otherwise several
def enc.fit(
  z: Bool,
  +w: U32,
  +h: U32,
  +ct: U32,
  +n: U32,
  raw: List<&2, U32>,
  +a: U32,
  +b: U32,
  +c: U32
) -> List<&2, U32>:
  match z:
    case True{}:
      enc.small(w, h, ct, n, raw, a, b, c)
    case False{}:
      enc.large(w, h, ct, n, raw, a, b, c)

# RGB fold: newest-first bytes, Adler, CRC, backup samples, samples seen
type Es is Data:
  Es{acc: List<&2, U32>, +a: U32, +b: U32, +c: U32, bak: List<&2, U32>, +seen: U32}

# RGBA fold: newest-first bytes, Adler, CRC, samples seen
type Ea is Data:
  Ea{acc: List<&2, U32>, +a: U32, +b: U32, +c: U32, +seen: U32}

# an RGB fold result: bytes or restored samples, sums, and whether to retry
type Ey is Data:
  Ey{raw: List<&2, U32>, +a: U32, +b: U32, +c: U32, ok: Bool, redo: Bool}

# an RGBA fold result
type Ez is Data:
  Ez{raw: List<&2, U32>, +a: U32, +b: U32, +c: U32, ok: Bool}

# free a list
def enc.drop(xs: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      None{}
    case _h <> t:
      enc.drop(t)

# drop the backup pixels and keep the scanline bytes
def enc.free(xs: List<&2, U32>, acc: List<&2, U32>, +a: U32, +b: U32, +c: U32) -> Ey:
  match xs:
    case Nil{}:
      Ey{acc, a, b, c, True{}, False{}}
    case _h <> t:
      enc.free(t, acc, a, b, c)

# drop both buffers; the picture was the wrong length
def enc.bad.ys(ys: List<&2, U32>) -> Ey:
  match ys:
    case Nil{}:
      Ey{[], 0, 0, 0, False{}, False{}}
    case _h <> t:
      enc.bad.ys(t)

# drop the backup, then the scanline bytes
def enc.bad(xs: List<&2, U32>, ys: List<&2, U32>) -> Ey:
  match xs:
    case Nil{}:
      enc.bad.ys(ys)
    case _h <> t:
      enc.bad(t, ys)

# bytes when the sample count matches the area, otherwise nothing
def enc.end(ok: Bool, bak: List<&2, U32>, acc: List<&2, U32>, +a: U32, +b: U32, +c: U32) -> Ey:
  match ok:
    case True{}:
      enc.free(bak, acc, a, b, c)
    case False{}:
      enc.bad(bak, acc)

# drop the RGB bytes and hand back every sample, chronological
def enc.redo(acc: List<&2, U32>, px: List<&2, U32>) -> Ey:
  match acc:
    case Nil{}:
      Ey{px, 0, 0, 0, False{}, True{}}
    case _h <> t:
      enc.redo(t, px)

# a later sample is translucent: encode the whole picture as RGBA instead
def enc.redo.at(acc: List<&2, U32>, bak: List<&2, U32>, +s: U32, rest: List<&2, U32>) -> Ey:
  enc.redo(acc, enc.cat.go(bak, {s <> rest : List<&2, U32>}))

# open the RGB fold and restart from its state
def enc.rgb.back(st: Es, +s: U32, rest: List<&2, U32>) -> Ey:
  match st:
    case Es{acc, +_a, +_b, +_c, bak, +_seen}:
      enc.redo.at(acc, bak, s, rest)

# close the RGB fold when the last sample has been written
def enc.rgb.fin(st: Es, +need: U32) -> Ey:
  match st:
    case Es{acc, +a, +b, +c, bak, +seen}:
      enc.end(U32.is_eq(seen, need), bak, acc, a, b, c)

# filter None, then R, G, B. Adler and CRC follow that order.
def enc.rgb.row(+s: U32, st: Es) -> Es:
  match st:
    case Es{acc, +a, +b, +c, bak, +seen}:
      +r = ((s >> 16n : U32) .&. 255 : U32)
      +g = ((s >> 8n : U32) .&. 255 : U32)
      +bb = (s .&. 255 : U32)
      +bak2 = {s <> bak : List<&2, U32>}
      +seen2 = (seen + 1 : U32)
      +b0 = enc.add(b, a)
      +c0 = Crc.crc.byte(c, 0)
      +a1 = enc.add(a, r)
      +b1 = enc.add(b0, a1)
      +c1 = Crc.crc.byte(c0, r)
      +a2 = enc.add(a1, g)
      +b2 = enc.add(b1, a2)
      +c2 = Crc.crc.byte(c1, g)
      +a3 = enc.add(a2, bb)
      +b3 = enc.add(b2, a3)
      +c3 = Crc.crc.byte(c2, bb)
      +acc2 = {bb <> g <> r <> 0 <> acc : List<&2, U32>}
      Es{acc2, a3, b3, c3, bak2, seen2}

# R, G, B in the middle of a scanline
def enc.rgb.mid(+s: U32, st: Es) -> Es:
  match st:
    case Es{acc, +a, +b, +c, bak, +seen}:
      +r = ((s >> 16n : U32) .&. 255 : U32)
      +g = ((s >> 8n : U32) .&. 255 : U32)
      +bb = (s .&. 255 : U32)
      +bak2 = {s <> bak : List<&2, U32>}
      +seen2 = (seen + 1 : U32)
      +a1 = enc.add(a, r)
      +b1 = enc.add(b, a1)
      +c1 = Crc.crc.byte(c, r)
      +a2 = enc.add(a1, g)
      +b2 = enc.add(b1, a2)
      +c2 = Crc.crc.byte(c1, g)
      +a3 = enc.add(a2, bb)
      +b3 = enc.add(b2, a3)
      +c3 = Crc.crc.byte(c2, bb)
      +acc2 = {bb <> g <> r <> acc : List<&2, U32>}
      Es{acc2, a3, b3, c3, bak2, seen2}

# one owner of the samples. Opaque bytes carry Adler and CRC; a translucent
# sample rebuilds the picture and the caller encodes it as RGBA.
def enc.raw.rgb(
  rest: List<&2, U32>, +s: U32, op: Bool, left: Nat, +w: Nat, st: Es, +need: U32
) -> Ey:
  match rest op left:
    case Nil{} False{} _left:
      enc.rgb.back(st, s, [])
    case +s2 <> t2 False{} _left:
      enc.rgb.back(st, s, {s2 <> t2 : List<&2, U32>})
    case Nil{} True{} 0n:
      enc.rgb.fin(enc.rgb.row(s, st), need)
    case Nil{} True{} 1n+p:
      enc.rgb.fin(enc.rgb.mid(s, st), need)
    case +s2 <> t2 True{} 0n:
      enc.raw.rgb(t2, s2, U32.is_eq(enc.a(s2), 255), enc.pred(w), w, enc.rgb.row(s, st), need)
    case +s2 <> t2 True{} 1n+p:
      enc.raw.rgb(t2, s2, U32.is_eq(enc.a(s2), 255), p, w, enc.rgb.mid(s, st), need)

# the first sample, then the fold
def enc.rgb.enter(px: List<&2, U32>, left: Nat, +w: Nat, st: Es, +need: U32) -> Ey:
  match px:
    case Nil{}:
      enc.rgb.fin(st, need)
    case +s <> t:
      enc.raw.rgb(t, s, U32.is_eq(enc.a(s), 255), left, w, st, need)

# drop scanline bytes after a short or long sample list
def enc.rgba.bad(acc: List<&2, U32>) -> Ez:
  match acc:
    case Nil{}:
      Ez{[], 0, 0, 0, False{}}
    case _h <> t:
      enc.rgba.bad(t)

# the byte list when the sample count matches, otherwise an empty failure
def enc.rgba.ok(ok: Bool, acc: List<&2, U32>, +a: U32, +b: U32, +c: U32) -> Ez:
  match ok:
    case True{}:
      Ez{acc, a, b, c, True{}}
    case False{}:
      enc.rgba.bad(acc)

# close an RGBA fold
def enc.rgba.fin(st: Ea, +need: U32) -> Ez:
  match st:
    case Ea{acc, +a, +b, +c, +seen}:
      enc.rgba.ok(U32.is_eq(seen, need), acc, a, b, c)

# filter None, then R, G, B, A
def enc.rgba.row(+s: U32, st: Ea) -> Ea:
  match st:
    case Ea{acc, +a, +b, +c, +seen}:
      +r = ((s >> 16n : U32) .&. 255 : U32)
      +g = ((s >> 8n : U32) .&. 255 : U32)
      +bb = (s .&. 255 : U32)
      +aa = enc.a(s)
      +seen2 = (seen + 1 : U32)
      +b0 = enc.add(b, a)
      +c0 = Crc.crc.byte(c, 0)
      +a1 = enc.add(a, r)
      +b1 = enc.add(b0, a1)
      +c1 = Crc.crc.byte(c0, r)
      +a2 = enc.add(a1, g)
      +b2 = enc.add(b1, a2)
      +c2 = Crc.crc.byte(c1, g)
      +a3 = enc.add(a2, bb)
      +b3 = enc.add(b2, a3)
      +c3 = Crc.crc.byte(c2, bb)
      +a4 = enc.add(a3, aa)
      +b4 = enc.add(b3, a4)
      +c4 = Crc.crc.byte(c3, aa)
      +acc2 = {aa <> bb <> g <> r <> 0 <> acc : List<&2, U32>}
      Ea{acc2, a4, b4, c4, seen2}

# R, G, B, A in the middle of a scanline
def enc.rgba.mid(+s: U32, st: Ea) -> Ea:
  match st:
    case Ea{acc, +a, +b, +c, +seen}:
      +r = ((s >> 16n : U32) .&. 255 : U32)
      +g = ((s >> 8n : U32) .&. 255 : U32)
      +bb = (s .&. 255 : U32)
      +aa = enc.a(s)
      +seen2 = (seen + 1 : U32)
      +a1 = enc.add(a, r)
      +b1 = enc.add(b, a1)
      +c1 = Crc.crc.byte(c, r)
      +a2 = enc.add(a1, g)
      +b2 = enc.add(b1, a2)
      +c2 = Crc.crc.byte(c1, g)
      +a3 = enc.add(a2, bb)
      +b3 = enc.add(b2, a3)
      +c3 = Crc.crc.byte(c2, bb)
      +a4 = enc.add(a3, aa)
      +b4 = enc.add(b3, a4)
      +c4 = Crc.crc.byte(c3, aa)
      +acc2 = {aa <> bb <> g <> r <> acc : List<&2, U32>}
      Ea{acc2, a4, b4, c4, seen2}

# filter-None RGBA scanlines, newest-first, with Adler and CRC inline
def enc.raw.rgba(px: List<&2, U32>, left: Nat, +w: Nat, st: Ea, +need: U32) -> Ez:
  match px left:
    case Nil{} _left:
      enc.rgba.fin(st, need)
    case +s <> t 0n:
      enc.raw.rgba(t, enc.pred(w), w, enc.rgba.row(s, st), need)
    case +s <> t 1n+p:
      enc.raw.rgba(t, p, w, enc.rgba.mid(s, st), need)

# wrap a finished RGBA fold, or none when the sample count was wrong
def enc.rgba.out(+w: U32, +h: U32, +n: U32, got: Ez) -> Maybe<&2, List<&2, U32>>:
  match got:
    case Ez{raw, +a, +b, +c, True{}}:
      Some{enc.fit(U32.is_le(n, 65535), w, h, 6, n, raw, a, b, c)}
    case Ez{raw, _a, _b, _c, False{}}:
      enc.drop(raw)

# Adler 1, 0 and a running CRC, before any RGBA byte
def enc.rgba.st(+c: U32) -> Ea:
  Ea{[], 1, 0, c, 0}

# colour type 6 from samples already known to need an alpha channel
def enc.image.rgba(+w: U32, +h: U32, px: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  +n = (h * ((w * 4 : U32) + 1 : U32) : U32)
  +need = (w * h : U32)
  +wn = U32.to_nat(w)
  enc.rgba.out(w, h, n, enc.raw.rgba(px, 0n, wn, enc.rgba.st(enc.idat.crc0(n)), need))

# a translucent sample restarts; a bad count is none
def enc.route.no(redo: Bool, +w: U32, +h: U32, raw: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match redo:
    case True{}:
      enc.image.rgba(w, h, raw)
    case False{}:
      enc.drop(raw)

# RGB bytes, or a restart as RGBA, or none when the count is wrong
def enc.route(+w: U32, +h: U32, +n: U32, got: Ey) -> Maybe<&2, List<&2, U32>>:
  match got:
    case Ey{raw, +a, +b, +c, True{}, _redo}:
      Some{enc.fit(U32.is_le(n, 65535), w, h, 2, n, raw, a, b, c)}
    case Ey{raw, _a, _b, _c, False{}, redo}:
      enc.route.no(redo, w, h, raw)

# Adler 1, 0, a running CRC, and an empty sample backup
def enc.rgb.st(+c: U32) -> Es:
  Es{[], 1, 0, c, [], 0}

# colour type 2 until a translucent sample appears
def enc.image(+w: U32, +h: U32, px: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  +n = (h * ((w * 3 : U32) + 1 : U32) : U32)
  +need = (w * h : U32)
  +wn = U32.to_nat(w)
  enc.route(w, h, n, enc.rgb.enter(px, 0n, wn, enc.rgb.st(enc.idat.crc0(n)), need))

# width times height fits in a U32
def enc.area(+w: U32, +h: U32) -> Bool:
  Bool.or(U32.is_zero(w), U32.is_le(h, U32.div(4294967295, w)))

# the bytes when the sides are in range, otherwise none
def enc.live(z: Bool, +w: U32, +h: U32, px: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match z:
    case False{}:
      enc.drop(px)
    case True{}:
      enc.image(w, h, px)

# ISO/IEC 15948 / W3C PNG — an 8-bit encoding, interlace 0, filter None.
# Colour type 2 when every sample is opaque, otherwise colour type 6.
# Each byte list has one owner: Adler-32 and CRC-32 fold as the bytes are written.
def enc.file(+w: U32, +h: U32, px: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  +z = Bool.and(Bool.and(U32.is_gt(w, 0), U32.is_gt(h, 0)), enc.area(w, h))
  enc.live(z, w, h, px)
