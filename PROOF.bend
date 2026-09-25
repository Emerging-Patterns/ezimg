# ezimg: the proofs. `bend PROOF.bend` is the gate: its first line must be
# exactly `All terms check.`
import Base
import ./LAWS.bend as Laws
import ./proof/u32.bend as U32L
import ./main.bend as Img
import ./src/png.bend as Png
import ./src/jpeg.bend as Jpeg
import ./proof/wp8-jpeg-numeric.bend as W8

# U32.or with 0xFF000000 first has alpha 255, whatever the other operand:
# the 32 bits are taken apart four at a time, and Bool.or(True, b) is True.
def alpha.first(xx: U32) -> {U32.shrn(U32.or(4278190080, xx), 24n) == 255 : U32}:
  match xx:
    case U32{w0}:
      match w0:
        case WCon{_b0, WCon{_b1, WCon{_b2, WCon{_b3, w4}}}}:
          match w4:
            case WCon{_b4, WCon{_b5, WCon{_b6, WCon{_b7, w8}}}}:
              match w8:
                case WCon{_b8, WCon{_b9, WCon{_b10, WCon{_b11, w12}}}}:
                  match w12:
                    case WCon{_b12, WCon{_b13, WCon{_b14, WCon{_b15, w16}}}}:
                      match w16:
                        case WCon{_b16, WCon{_b17, WCon{_b18, WCon{_b19, w20}}}}:
                          match w20:
                            case WCon{_b20, WCon{_b21, WCon{_b22, WCon{_b23, w24}}}}:
                              match w24:
                                case WCon{_b24, WCon{_b25, WCon{_b26, WCon{_b27, w28}}}}:
                                  match w28:
                                    case WCon{_b28, WCon{_b29, WCon{_b30, WCon{_b31, w32}}}}:
                                      match w32:
                                        case WNil{}:
                                          {==}

def Laws.jpeg_rgb_opaque(yy, cb, cr):
  alpha.first(Jpeg.rgb.bits(yy, cb, cr))

def Laws.jpeg_gray_opaque(yy):
  alpha.first(Jpeg.gray.bits(yy))

# encode_jpeg and encode_png branch on the same guard, so they are none together
def refuse.alike(
  ok: Bool,
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  +qx: List<&2, U32>
) -> {Maybe.is_none(&2, List<&2, U32>, Img.encode_jpeg.pick(ok, ww, hh, qx)) ==
  Maybe.is_none(&2, List<&2, U32>, Png.enc.open(ok, ww, hh, px)) : Bool}:
  match ok:
    case False{}:
      {==}
    case True{}:
      {==}

def Laws.jpeg_png_refuse_alike(img):
  match img:
    case Img.Raster{+ww, +hh, +px}:
      refuse.alike(Png.enc.good(ww, hh, px), ww, hh, px, Img.colours(px))

# the code's colours is the specification's alpha.drop
def colours.drop(+px: List<&2, U32>) -> {Img.colours(px) == Laws.alpha.drop(px) : List<&2, U32>}:
  match px:
    case Nil{}:
      {==}
    case +pp <> rest:
      Equal.cong(List<&2, U32>, List<&2, U32>, tl => {U32.and(16777215, pp) <> tl : List<&2, U32>}, Img.colours(rest),
        Laws.alpha.drop(rest), colours.drop(rest))

# clearing alpha keeps the count Png.enc.len takes
def len.drop(
  +px: List<&2, U32>,
  +nn: U32
) -> {Png.enc.len(Laws.alpha.drop(px), nn) == Png.enc.len(px, nn) : U32}:
  match px:
    case Nil{}:
      {==}
    case _pp <> rest:
      len.drop(rest, (nn + 1 : U32))

# so the guard answers the same for a list and its colours
def good.drop(
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>
) -> {Png.enc.good(ww, hh, Laws.alpha.drop(px)) == Png.enc.good(ww, hh, px) : Bool}:
  Equal.cong(U32, Bool, nn => Bool.and(Bool.and(U32.is_gt(ww, 0), U32.is_gt(hh, 0)), Bool.and(Png.enc.area(ww, hh),
    U32.is_eq(nn, (ww * hh : U32)))), Png.enc.len(Laws.alpha.drop(px), 0), Png.enc.len(px, 0), len.drop(px, 0))

def Laws.jpeg_alpha_blind(ww, hh, pa, pb, same):
  +gab = Equal.trans(Bool, Png.enc.good(ww, hh, pa), Png.enc.good(ww, hh, Laws.alpha.drop(pa)),
    Png.enc.good(ww, hh, pb),
    Equal.sym(Bool, Png.enc.good(ww, hh, Laws.alpha.drop(pa)), Png.enc.good(ww, hh, pa), good.drop(ww, hh, pa)),
    Equal.trans(Bool, Png.enc.good(ww, hh, Laws.alpha.drop(pa)), Png.enc.good(ww, hh, Laws.alpha.drop(pb)),
      Png.enc.good(ww, hh, pb),
      Equal.cong(List<&2, U32>, Bool, ll => Png.enc.good(ww, hh, ll), Laws.alpha.drop(pa), Laws.alpha.drop(pb), same),
      good.drop(ww, hh, pb)))
  +cab = Equal.trans(List<&2, U32>, Img.colours(pa), Laws.alpha.drop(pa), Img.colours(pb), colours.drop(pa),
    Equal.trans(List<&2, U32>, Laws.alpha.drop(pa), Laws.alpha.drop(pb), Img.colours(pb), same,
      Equal.sym(List<&2, U32>, Img.colours(pb), Laws.alpha.drop(pb), colours.drop(pb))))
  Equal.trans(Maybe<&2, List<&2, U32>>,
    Img.encode_jpeg.pick(Png.enc.good(ww, hh, pa), ww, hh, Img.colours(pa)),
    Img.encode_jpeg.pick(Png.enc.good(ww, hh, pb), ww, hh, Img.colours(pa)),
    Img.encode_jpeg.pick(Png.enc.good(ww, hh, pb), ww, hh, Img.colours(pb)),
    Equal.cong(Bool, Maybe<&2, List<&2, U32>>, bb => Img.encode_jpeg.pick(bb, ww, hh, Img.colours(pa)),
      Png.enc.good(ww, hh, pa), Png.enc.good(ww, hh, pb), gab),
    Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>,
      ll => Img.encode_jpeg.pick(Png.enc.good(ww, hh, pb), ww, hh, ll), Img.colours(pa), Img.colours(pb), cab))

def Laws.map_size(_ff, img):
  match img:
    case Img.Raster{_ww, _hh, _px}:
      {==}

# sample k of map.go is f of sample k
def map.go.at(
  ~ff: U32 -> U32,
  px: List<&2, U32>,
  kk: Nat
) -> {List.get(&2, U32, Img.map.go(~ff, px), kk) == Laws.opt.map(~ff, List.get(&2, U32, px, kk)) : Maybe<&2, U32>}:
  match px kk:
    case Nil{} _kk:
      {==}
    case _hd <> _tl 0n:
      {==}
    case _hd <> tl 1n+pp:
      map.go.at(~ff, tl, pp)

def Laws.map_at(ff, img, kk):
  match img:
    case Img.Raster{_ww, _hh, px}:
      map.go.at(~ff, px, kk)

def Laws.sig_opens(_rest):
  {==}

# dropping nothing is the list
def drop.zero(+xs: List<&2, U32>) -> {xs == List.drop(&2, U32, xs, 0n) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case _hd <> _tl:
      {==}

# two lists with equal heads and equal tails are equal
def cons.eq(
  +aa: U32,
  +bb: U32,
  +ta: List<&2, U32>,
  +tb: List<&2, U32>,
  eh: {aa == bb : U32},
  et: {ta == tb : List<&2, U32>}
) -> {aa <> ta == bb <> tb : List<&2, U32>}:
  Equal.trans(List<&2, U32>, aa <> ta, bb <> ta, bb <> tb,
    Equal.cong(U32, List<&2, U32>, xx => {xx <> ta : List<&2, U32>}, aa, bb, eh),
    Equal.cong(List<&2, U32>, List<&2, U32>, ll => {bb <> ll : List<&2, U32>}, ta, tb, et))

# what sig.match says of want and xs, when it answers true: the answer it
# started from was true, and xs is want followed by the rest
def prefix.only.ty(+want: List<&2, U32>, +xs: List<&2, U32>, +ok: Bool) -> Type:
  {ok == True{} : Bool} &
    {xs == List.append(&2, U32, want, List.drop(&2, U32, xs, List.length(&2, U32, want))) : List<&2, U32>}

# one byte further: what the rest proves gives the answer so far and this byte
def prefix.only.cons(
  +ok: Bool,
  +wh: U32,
  +wt: List<&2, U32>,
  +bh: U32,
  +bt: List<&2, U32>,
  pr: prefix.only.ty(wt, bt, Bool.and(ok, U32.is_eq(bh, wh)))
) -> prefix.only.ty(wh <> wt, bh <> bt, ok):
  (e_and, e_tail) = pr
  +e_and2 = {e_and : {Bool.and(ok, U32.is_eq(bh, wh)) == True{} : Bool}}
  (U32L.and_left(ok, U32.is_eq(bh, wh), e_and2),
    cons.eq(bh, wh, bt, List.append(&2, U32, wt, List.drop(&2, U32, bt, List.length(&2, U32, wt))),
      U32L.ueq(bh, wh, U32L.and_right(ok, U32.is_eq(bh, wh), e_and2)), e_tail))

# bytes that sig.match finds open with want are want followed by the rest
def prefix.only(
  +want: List<&2, U32>,
  +xs: List<&2, U32>,
  +ok: Bool,
  +h_match: {Img.sig.match(want, xs, ok) == True{} : Bool}
) -> prefix.only.ty(want, xs, ok):
  match want xs:
    case Nil{} _xs:
      (h_match, drop.zero(_xs))
    case +wh <> +wt Nil{}:
      Empty.absurd(prefix.only.ty(wh <> wt, Nil{}, ok), U32L.false_true(h_match))
    case +wh <> +wt +bh <> +bt:
      prefix.only.cons(ok, wh, wt, bh, bt, prefix.only(wt, bt, Bool.and(ok, U32.is_eq(bh, wh)), h_match))

# the second half of what prefix.only proves
def prefix.only.rest(
  +want: List<&2, U32>,
  +xs: List<&2, U32>,
  +ok: Bool,
  pr: prefix.only.ty(want, xs, ok)
) -> {xs == List.append(&2, U32, want, List.drop(&2, U32, xs, List.length(&2, U32, want))) : List<&2, U32>}:
  (_e_ok, e_xs) = pr
  e_xs

# split on what sig.match answers: false gives none, which h_some rules out
def sig.only.go(
  ok: Bool,
  +xs: List<&2, U32>,
  e_ok: {Img.sig.match(Img.png_sig(), xs, True{}) == ok : Bool},
  h_some: {Maybe.is_some(&2, List<&2, U32>, Img.sig.pick(ok)) == True{} : Bool}
) -> {xs == List.append(&2, U32, Img.png_sig(), List.drop(&2, U32, xs, 8n)) : List<&2, U32>}:
  match ok:
    case False{}:
      Empty.absurd({xs == List.append(&2, U32, Img.png_sig(), List.drop(&2, U32, xs, 8n)) : List<&2, U32>},
        U32L.false_true(h_some))
    case True{}:
      prefix.only.rest(Img.png_sig(), xs, True{}, prefix.only(Img.png_sig(), xs, True{}, e_ok))

def Laws.sig_only(xs, h_some):
  sig.only.go(Img.sig.match(Img.png_sig(), xs, True{}), xs, {==}, h_some)

# ---- wp8-jpeg-numeric ----

# decode_jpeg of the state a walk ends in
def w8.out(st: Jpeg.St) -> Maybe<&2, Img.Raster>:
  Img.decode_jpeg.out(Jpeg.decode.finish(st))

# a refused frame is none whether or not a frame was read before it
def w8.none(
  ok1: Bool,
  +sc: Jpeg.Scan,
  +tb: Jpeg.Tabs,
  +en: List<&2, U32>,
  +ri: U32
) -> {Img.decode_jpeg.out(Jpeg.decode.finish.ok(ok1, False{}, Jpeg.decode.frame0(), sc, tb, en, ri)) ==
  None{} : Maybe<&2, Img.Raster>}:
  match ok1:
    case False{}:
      {==}
    case True{}:
      {==}

# the state a refused frame header leaves the walk in
def w8.stop(+sc: Jpeg.Scan, +tb: Jpeg.Tabs, +en: List<&2, U32>, +ri: U32, +kd: U32) -> Jpeg.St:
  Jpeg.St{Jpeg.Stop{}, Jpeg.decode.frame0(), sc, tb, en, ri, kd, 1}

# from where the prefix leaves the walk: a segment that stops the walk with
# the refusal flag set gives none, whatever follows it
def w8.tail(
  +pre: List<&2, U32>,
  +seg: List<&2, U32>,
  +mid: Jpeg.St,
  +rest: List<&2, U32>,
  +sc: Jpeg.Scan,
  +tb: Jpeg.Tabs,
  +en: List<&2, U32>,
  +ri: U32,
  +kd: U32,
  h_walk: {Jpeg.decode.walk(pre, Jpeg.decode.st0()) == mid : Jpeg.St},
  h_seg: {Jpeg.decode.walk(seg, mid) == Jpeg.decode.walk(rest, w8.stop(sc, tb, en, ri, kd)) : Jpeg.St}
) -> {Img.decode_jpeg(List.append(&2, U32, pre, seg)) == None{} : Maybe<&2, Img.Raster>}:
  +stop = {w8.stop(sc, tb, en, ri, kd) : Jpeg.St}
  Equal.trans(Maybe<&2, Img.Raster>, w8.out(Jpeg.decode.walk(List.append(&2, U32, pre, seg), Jpeg.decode.st0())),
    w8.out(Jpeg.decode.walk(seg, Jpeg.decode.walk(pre, Jpeg.decode.st0()))), None{},
    Equal.cong(Jpeg.St, Maybe<&2, Img.Raster>, st => w8.out(st),
      Jpeg.decode.walk(List.append(&2, U32, pre, seg), Jpeg.decode.st0()),
      Jpeg.decode.walk(seg, Jpeg.decode.walk(pre, Jpeg.decode.st0())), W8.walk_app(pre, seg, Jpeg.decode.st0())),
    Equal.trans(Maybe<&2, Img.Raster>, w8.out(Jpeg.decode.walk(seg, Jpeg.decode.walk(pre, Jpeg.decode.st0()))),
      w8.out(Jpeg.decode.walk(seg, mid)), None{},
      Equal.cong(Jpeg.St, Maybe<&2, Img.Raster>, st => w8.out(Jpeg.decode.walk(seg, st)),
        Jpeg.decode.walk(pre, Jpeg.decode.st0()), mid, h_walk),
      Equal.trans(Maybe<&2, Img.Raster>, w8.out(Jpeg.decode.walk(seg, mid)), w8.out(Jpeg.decode.walk(rest, stop)),
        None{},
        Equal.cong(Jpeg.St, Maybe<&2, Img.Raster>, st => w8.out(st), Jpeg.decode.walk(seg, mid),
          Jpeg.decode.walk(rest, stop), h_seg),
        Equal.trans(Maybe<&2, Img.Raster>, w8.out(Jpeg.decode.walk(rest, stop)), w8.out(stop), None{},
          Equal.cong(Jpeg.St, Maybe<&2, Img.Raster>, st => w8.out(st), Jpeg.decode.walk(rest, stop), stop,
            W8.walk_stop(rest, Jpeg.decode.frame0(), sc, tb, en, ri, kd, 1)),
          w8.none(U32.is_eq(kd, 1), sc, tb, en, ri)))))

def Laws.jpeg_refuse_factor1(
  pre,
  frame,
  scan,
  tabs,
  ent,
  ri,
  kind,
  bad,
  h_walk,
  yh,
  yl,
  xh,
  xl,
  c1,
  f1,
  q1,
  h_fac,
  rest
):
  w8.tail(pre, 255 <> 192 <> 0 <> 11 <> 8 <> yh <> yl <> xh <> xl <> 1 <> c1 <> f1 <> q1 <> rest,
    Jpeg.St{Jpeg.Seek{}, frame, scan, tabs, ent, ri, kind, bad}, rest, scan, tabs, ent, ri, kind, h_walk,
    Equal.cong(Bool, Jpeg.St, ok => Jpeg.decode.walk(rest, Jpeg.decode.read.sof.c(ok,
      Bool.and(Jpeg.decode.nf.ok(1), U32.is_eq(bad, 0)), U32.is_eq(Jpeg.decode.vmax([U32.shrn(f1, 4n)], 0), 0),
      Jpeg.decode.u16(xh, xl), Jpeg.decode.u16(yh, yl), 1, [c1], [U32.shrn(f1, 4n)], [U32.and(f1, 15)], [q1], scan,
      tabs, ent, ri, kind)), Laws.jpg.facs(f1), False{}, h_fac))

def Laws.jpeg_refuse_factor3(
  pre,
  frame,
  scan,
  tabs,
  ent,
  ri,
  kind,
  bad,
  h_walk,
  yh,
  yl,
  xh,
  xl,
  c1,
  f1,
  q1,
  c2,
  f2,
  q2,
  c3,
  f3,
  q3,
  h_fac,
  rest
):
  w8.tail(pre, 255 <> 192 <> 0 <> 17 <> 8 <> yh <> yl <> xh <> xl <> 3 <> c1 <> f1 <> q1 <> c2 <> f2 <> q2 <> c3 <>
    f3 <> q3 <> rest, Jpeg.St{Jpeg.Seek{}, frame, scan, tabs, ent, ri, kind, bad}, rest, scan, tabs, ent, ri, kind,
    h_walk,
    Equal.cong(Bool, Jpeg.St, ok => Jpeg.decode.walk(rest, Jpeg.decode.read.sof.c(ok,
      Bool.and(Jpeg.decode.nf.ok(3), U32.is_eq(bad, 0)),
      U32.is_eq(Jpeg.decode.vmax([U32.shrn(f1, 4n), U32.shrn(f2, 4n), U32.shrn(f3, 4n)], 0), 0),
      Jpeg.decode.u16(xh, xl), Jpeg.decode.u16(yh, yl), 3, [c1, c2, c3],
      [U32.shrn(f1, 4n), U32.shrn(f2, 4n), U32.shrn(f3, 4n)], [U32.and(f1, 15), U32.and(f2, 15), U32.and(f3, 15)],
      [q1, q2, q3], scan, tabs, ent, ri, kind)),
      Bool.and(Bool.and(Laws.jpg.facs(f1), Laws.jpg.facs(f2)), Laws.jpg.facs(f3)), False{}, h_fac))

# what jpeg_mcu_grid says for factors hi and vi
def w8.grid.ty(
  +hi: U32,
  +vi: U32,
  +mx: U32,
  +my: U32,
  +hmax: U32,
  +vmax: U32,
  +ww: U32,
  +hh: U32
) -> Type:
  {Laws.jpg.blocks(U32.to_nat((hi * vi : U32)), 0, hi, vi, mx, my, hmax, vmax, ww, hh) ==
    Laws.jpg.grid(U32.to_nat(vi), 0, hi, mx, my, hmax, vmax, U32.div(hmax, hi), U32.div(vmax, vi), ww, hh) :
    List<&2, Jpeg.Geom>}

# for one factor hi of 1, 2 or 4: every allowed vi, one concrete case each
def w8.grid.vi(
  +hi: U32,
  +vi: U32,
  +h_vi: {Laws.jpg.fac(vi) == True{} : Bool},
  +mx: U32,
  +my: U32,
  +hmax: U32,
  +vmax: U32,
  +ww: U32,
  +hh: U32,
  p1: w8.grid.ty(hi, 1, mx, my, hmax, vmax, ww, hh),
  p2: w8.grid.ty(hi, 2, mx, my, hmax, vmax, ww, hh),
  p4: w8.grid.ty(hi, 4, mx, my, hmax, vmax, ww, hh)
) -> w8.grid.ty(hi, vi, mx, my, hmax, vmax, ww, hh):
  W8.fac_elim(vv => w8.grid.ty(hi, vv, mx, my, hmax, vmax, ww, hh), vi, U32.is_eq(vi, 1), {==}, h_vi, p1, p2, p4)

def Laws.jpeg_mcu_grid(hi, vi, h_hi, h_vi, mx, my, hmax, vmax, ww, hh):
  W8.fac_elim(hv => w8.grid.ty(hv, vi, mx, my, hmax, vmax, ww, hh), hi, U32.is_eq(hi, 1), {==}, h_hi,
    w8.grid.vi(1, vi, h_vi, mx, my, hmax, vmax, ww, hh, {==}, {==}, {==}),
    w8.grid.vi(2, vi, h_vi, mx, my, hmax, vmax, ww, hh, {==}, {==}, {==}),
    w8.grid.vi(4, vi, h_vi, mx, my, hmax, vmax, ww, hh, {==}, {==}, {==}))

# what jpeg_block_cover says for sample sizes pw and ph
def w8.cover.ty(
  +pw: U32,
  +ph: U32,
  +ox: U32,
  +oy: U32,
  +ww: U32,
  +hh: U32,
  +samples: List<&2, U32>,
  +nn: U32
) -> Type:
  {Jpeg.decode.paint.use(Jpeg.Geom{ox, oy, pw, ph, ww, hh}, True{}, samples, Jpeg.decode.plane(nn)) ==
    Laws.jpg.cover(8n, Jpeg.decode.plane(nn), samples, 0, ox, oy, pw, ph, ww, hh) : Array<U32>}

# for one width pw of 1, 2 or 4: every allowed height, one concrete case each
def w8.cover.ph(
  +pw: U32,
  +ph: U32,
  +h_ph: {Laws.jpg.fac(ph) == True{} : Bool},
  +ox: U32,
  +oy: U32,
  +ww: U32,
  +hh: U32,
  +samples: List<&2, U32>,
  +nn: U32,
  p1: w8.cover.ty(pw, 1, ox, oy, ww, hh, samples, nn),
  p2: w8.cover.ty(pw, 2, ox, oy, ww, hh, samples, nn),
  p4: w8.cover.ty(pw, 4, ox, oy, ww, hh, samples, nn)
) -> w8.cover.ty(pw, ph, ox, oy, ww, hh, samples, nn):
  W8.fac_elim(vv => w8.cover.ty(pw, vv, ox, oy, ww, hh, samples, nn), ph, U32.is_eq(ph, 1), {==}, h_ph, p1, p2, p4)

def Laws.jpeg_block_cover(pw, ph, h_pw, h_ph, ox, oy, ww, hh, samples, nn):
  W8.fac_elim(vv => w8.cover.ty(vv, ph, ox, oy, ww, hh, samples, nn), pw, U32.is_eq(pw, 1), {==}, h_pw,
    w8.cover.ph(1, ph, h_ph, ox, oy, ww, hh, samples, nn, {==}, {==}, {==}),
    w8.cover.ph(2, ph, h_ph, ox, oy, ww, hh, samples, nn, {==}, {==}, {==}),
    w8.cover.ph(4, ph, h_ph, ox, oy, ww, hh, samples, nn, {==}, {==}, {==}))
