# ezimg: the proofs. `bend PROOF.bend` is the gate: its first line must be
# exactly `All terms check.`
import Base
import ./LAWS.bend as Laws
import ./proof/u32.bend as U32L
import ./proof/wp6-raster.bend as R
import ./main.bend as Img
import ./src/png.bend as Png
import ./src/jpeg.bend as Jpeg
import ./src/crc.bend as Crc
import ./proof/wp5-png-decode.bend as W5

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

# ---- wp6-raster ----

def Laws.fill_wf(ww, hh, color, area, h_area):
  +wh = Nat.mul(U32.to_nat(ww), U32.to_nat(hh))
  +nn = U32.to_nat(U32.mul(ww, hh))
  +en = {R.u32_mul_below(ww, hh, area, R.le_rw_r(wh, wh, U32.to_nat(area), Equal.sym(Nat, U32.to_nat(area), wh, h_area),
    R.le_refl(wh))) : {nn == wh : Nat}}
  +el = {Equal.trans(Nat, List.length(&2, U32, List.replicate(U32, nn, color)), nn, wh,
    R.length_replicate(nn, color), en) : {List.length(&2, U32, List.replicate(U32, nn, color)) == wh : Nat}}
  Equal.trans(Bool, Nat.is_eq(List.length(&2, U32, List.replicate(U32, nn, color)), wh), Nat.is_eq(wh, wh), True{},
    Equal.cong(Nat, Bool, xx => Nat.is_eq(xx, wh), List.length(&2, U32, List.replicate(U32, nn, color)), wh, el),
    R.nat_eq_refl(wh))

def Laws.fill_every(ww, hh, color, kk, vv, h_at):
  R.get_replicate(U32.to_nat(U32.mul(ww, hh)), kk, color, vv, h_at)

# x < w as U32 when x < w as Nat
def ras.lt(
  +aa: U32,
  +bb: U32,
  hh: {Nat.is_lt(U32.to_nat(aa), U32.to_nat(bb)) == True{} : Bool}
) -> {U32.is_lt(aa, bb) == True{} : Bool}:
  Equal.trans(Bool, U32.is_lt(aa, bb), Nat.is_lt(U32.to_nat(aa), U32.to_nat(bb)), True{}, R.u32_lt(aa, bb), hh)

# a point test, as Nats
def ras.In(+ww: U32, +hh: U32, +xx: U32, +yy: U32) -> Bool:
  Bool.and(Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)), Nat.is_lt(U32.to_nat(yy), U32.to_nat(hh)))

# the x half of a point inside
def ras.hx(
  +ww: U32,
  +hh: U32,
  +xx: U32,
  +yy: U32,
  h_in: {ras.In(ww, hh, xx, yy) == True{} : Bool}
) -> {Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)) == True{} : Bool}:
  U32L.and_left(Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)), Nat.is_lt(U32.to_nat(yy), U32.to_nat(hh)), h_in)

# the y half of a point inside
def ras.hy(
  +ww: U32,
  +hh: U32,
  +xx: U32,
  +yy: U32,
  h_in: {ras.In(ww, hh, xx, yy) == True{} : Bool}
) -> {Nat.is_lt(U32.to_nat(yy), U32.to_nat(hh)) == True{} : Bool}:
  U32L.and_right(Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)), Nat.is_lt(U32.to_nat(yy), U32.to_nat(hh)), h_in)

# get at a point inside, once the raster is taken apart
def ras.get_in(
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  +xx: U32,
  +yy: U32,
  +area: U32,
  h_area: {U32.to_nat(area) == Nat.mul(U32.to_nat(ww), U32.to_nat(hh)) : Nat},
  +hx: {Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)) == True{} : Bool},
  +hy: {Nat.is_lt(U32.to_nat(yy), U32.to_nat(hh)) == True{} : Bool}
) -> {Img.get.x(U32.is_lt(xx, ww), px, ww, hh, xx, yy) == List.get(&2, U32, px, Laws.spot(ww, xx, yy)) :
  Maybe<&2, U32>}:
  Equal.trans(Maybe<&2, U32>, Img.get.x(U32.is_lt(xx, ww), px, ww, hh, xx, yy), Img.get.x(True{}, px, ww, hh, xx, yy),
    List.get(&2, U32, px, Laws.spot(ww, xx, yy)),
    Equal.cong(Bool, Maybe<&2, U32>, bb => Img.get.x(bb, px, ww, hh, xx, yy), U32.is_lt(xx, ww), True{},
      ras.lt(xx, ww, hx)),
    Equal.trans(Maybe<&2, U32>, Img.get.y(U32.is_lt(yy, hh), px, ww, xx, yy), Img.get.y(True{}, px, ww, xx, yy),
      List.get(&2, U32, px, Laws.spot(ww, xx, yy)),
      Equal.cong(Bool, Maybe<&2, U32>, bb => Img.get.y(bb, px, ww, xx, yy), U32.is_lt(yy, hh), True{},
        ras.lt(yy, hh, hy)),
      Equal.cong(Nat, Maybe<&2, U32>, nn => List.get(&2, U32, px, nn), U32.to_nat(U32.add(U32.mul(yy, ww), xx)),
        Laws.spot(ww, xx, yy), R.u32_index(ww, xx, yy, hh, area, h_area, hx, hy))))

def Laws.get_inside(img, xx, yy, area, h_area, h_in):
  match img:
    case Img.Raster{+ww, +hh, +px}:
      ras.get_in(ww, hh, px, xx, yy, area, h_area, ras.hx(ww, hh, xx, yy, h_in), ras.hy(ww, hh, xx, yy, h_in))

def Laws.get_inside_some(img, xx, yy, area, h_area, h_wf, h_in):
  match img:
    case Img.Raster{+ww, +hh, +px}:
      +hx = {ras.hx(ww, hh, xx, yy, h_in) : {Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)) == True{} : Bool}}
      +hy = {ras.hy(ww, hh, xx, yy, h_in) : {Nat.is_lt(U32.to_nat(yy), U32.to_nat(hh)) == True{} : Bool}}
      +wh = Nat.mul(U32.to_nat(ww), U32.to_nat(hh))
      +el = {R.nat_eq_true(List.length(&2, U32, px), wh, h_wf) : {List.length(&2, U32, px) == wh : Nat}}
      +hk = {R.lt_rw_r(Laws.spot(ww, xx, yy), wh, List.length(&2, U32, px),
        Equal.sym(Nat, List.length(&2, U32, px), wh, el),
        R.index_lt(U32.to_nat(xx), U32.to_nat(yy), U32.to_nat(ww), U32.to_nat(hh), hx, hy)) :
        {Nat.is_lt(Laws.spot(ww, xx, yy), List.length(&2, U32, px)) == True{} : Bool}}
      Equal.trans(Bool, Maybe.is_some(&2, U32, Img.get.x(U32.is_lt(xx, ww), px, ww, hh, xx, yy)),
        Maybe.is_some(&2, U32, List.get(&2, U32, px, Laws.spot(ww, xx, yy))), True{},
        Equal.cong(Maybe<&2, U32>, Bool, mm => Maybe.is_some(&2, U32, mm),
          Img.get.x(U32.is_lt(xx, ww), px, ww, hh, xx, yy), List.get(&2, U32, px, Laws.spot(ww, xx, yy)),
          ras.get_in(ww, hh, px, xx, yy, area, h_area, hx, hy)),
        R.get_some_lt(px, Laws.spot(ww, xx, yy), hk))

# the Nat test of a point and the U32 test agree
def ras.in_u32(
  +ww: U32,
  +hh: U32,
  +xx: U32,
  +yy: U32
) -> {Bool.and(U32.is_lt(xx, ww), U32.is_lt(yy, hh)) ==
  Bool.and(Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)), Nat.is_lt(U32.to_nat(yy), U32.to_nat(hh))) : Bool}:
  Equal.trans(Bool, Bool.and(U32.is_lt(xx, ww), U32.is_lt(yy, hh)),
    Bool.and(Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)), U32.is_lt(yy, hh)),
    Bool.and(Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)), Nat.is_lt(U32.to_nat(yy), U32.to_nat(hh))),
    Equal.cong(Bool, Bool, bb => Bool.and(bb, U32.is_lt(yy, hh)), U32.is_lt(xx, ww),
      Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)), R.u32_lt(xx, ww)),
    Equal.cong(Bool, Bool, bb => Bool.and(Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)), bb), U32.is_lt(yy, hh),
      Nat.is_lt(U32.to_nat(yy), U32.to_nat(hh)), R.u32_lt(yy, hh)))

# get outside: split on the x test, then the y test
def ras.get_out(
  xin: Bool,
  yin: Bool,
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  +xx: U32,
  +yy: U32,
  ey: {U32.is_lt(yy, hh) == yin : Bool},
  hb: {Bool.and(xin, yin) == False{} : Bool}
) -> {Img.get.x(xin, px, ww, hh, xx, yy) == None{} : Maybe<&2, U32>}:
  match xin:
    case False{}:
      {==}
    case True{}:
      Equal.cong(Bool, Maybe<&2, U32>, bb => Img.get.y(bb, px, ww, xx, yy), U32.is_lt(yy, hh), False{},
        Equal.trans(Bool, U32.is_lt(yy, hh), yin, False{}, ey, hb))

def Laws.get_outside(img, xx, yy, h_out):
  match img:
    case Img.Raster{+ww, +hh, +px}:
      ras.get_out(U32.is_lt(xx, ww), U32.is_lt(yy, hh), ww, hh, px, xx, yy, {==},
        Equal.trans(Bool, Bool.and(U32.is_lt(xx, ww), U32.is_lt(yy, hh)),
          Bool.and(Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)), Nat.is_lt(U32.to_nat(yy), U32.to_nat(hh))), False{},
          ras.in_u32(ww, hh, xx, yy), h_out))

def Laws.set_inside(img, xx, yy, color, area, h_area, h_in):
  match img:
    case Img.Raster{+ww, +hh, +px}:
      +hx = {ras.hx(ww, hh, xx, yy, h_in) : {Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)) == True{} : Bool}}
      +hy = {ras.hy(ww, hh, xx, yy, h_in) : {Nat.is_lt(U32.to_nat(yy), U32.to_nat(hh)) == True{} : Bool}}
      Equal.trans(Img.Raster, Img.set.x(U32.is_lt(xx, ww), ww, hh, px, xx, yy, color),
        Img.set.x(True{}, ww, hh, px, xx, yy, color),
        Img.raster(ww, hh, List.set(&2, U32, px, Laws.spot(ww, xx, yy), color)),
        Equal.cong(Bool, Img.Raster, bb => Img.set.x(bb, ww, hh, px, xx, yy, color), U32.is_lt(xx, ww), True{},
          ras.lt(xx, ww, hx)),
        Equal.trans(Img.Raster, Img.set.y(U32.is_lt(yy, hh), ww, hh, px, xx, yy, color),
          Img.set.y(True{}, ww, hh, px, xx, yy, color),
          Img.raster(ww, hh, List.set(&2, U32, px, Laws.spot(ww, xx, yy), color)),
          Equal.cong(Bool, Img.Raster, bb => Img.set.y(bb, ww, hh, px, xx, yy, color), U32.is_lt(yy, hh), True{},
            ras.lt(yy, hh, hy)),
          Equal.cong(Nat, Img.Raster, nn => Img.raster(ww, hh, List.set(&2, U32, px, nn, color)),
            U32.to_nat(U32.add(U32.mul(yy, ww), xx)), Laws.spot(ww, xx, yy),
            R.u32_index(ww, xx, yy, hh, area, h_area, hx, hy))))

# set outside: split on the x test, then the y test
def ras.set_out(
  xin: Bool,
  yin: Bool,
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  +xx: U32,
  +yy: U32,
  +color: U32,
  ey: {U32.is_lt(yy, hh) == yin : Bool},
  hb: {Bool.and(xin, yin) == False{} : Bool}
) -> {Img.set.x(xin, ww, hh, px, xx, yy, color) == Img.Raster{ww, hh, px} : Img.Raster}:
  match xin:
    case False{}:
      {==}
    case True{}:
      Equal.cong(Bool, Img.Raster, bb => Img.set.y(bb, ww, hh, px, xx, yy, color), U32.is_lt(yy, hh), False{},
        Equal.trans(Bool, U32.is_lt(yy, hh), yin, False{}, ey, hb))

def Laws.set_outside(img, xx, yy, color, h_out):
  match img:
    case Img.Raster{+ww, +hh, +px}:
      ras.set_out(U32.is_lt(xx, ww), U32.is_lt(yy, hh), ww, hh, px, xx, yy, color, {==},
        Equal.trans(Bool, Bool.and(U32.is_lt(xx, ww), U32.is_lt(yy, hh)),
          Bool.and(Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)), Nat.is_lt(U32.to_nat(yy), U32.to_nat(hh))), False{},
          ras.in_u32(ww, hh, xx, yy), h_out))

# ---- wp6-raster: crop ----

# the rows walk's first row is whole: rw <= length
def crop.rows_head(
  +pp: Nat,
  +xs: List<&2, U32>,
  +rw: Nat,
  +gap: Nat,
  hh: {Nat.is_le(Nat.mul(1n+pp, Nat.add(rw, gap)), Nat.add(List.length(&2, U32, xs), gap)) == True{} : Bool}
) -> {Nat.is_le(rw, List.length(&2, U32, xs)) == True{} : Bool}:
  +ln = List.length(&2, U32, xs)
  R.le_cancel(gap, rw, ln, R.le_rw_r(Nat.add(gap, rw), Nat.add(ln, gap), Nat.add(gap, ln), R.add_comm(ln, gap),
    R.le_rw_l(Nat.add(rw, gap), Nat.add(gap, rw), Nat.add(ln, gap), R.add_comm(rw, gap),
      R.le_add_r(Nat.add(rw, gap), Nat.mul(pp, Nat.add(rw, gap)), Nat.add(ln, gap), hh))))

# the rows walk's bound holds again one row on
def crop.rows_next(
  +pp: Nat,
  +xs: List<&2, U32>,
  +rw: Nat,
  +gap: Nat,
  hh: {Nat.is_le(Nat.mul(1n+pp, Nat.add(rw, gap)), Nat.add(List.length(&2, U32, xs), gap)) == True{} : Bool}
) -> {Nat.is_le(Nat.mul(pp, Nat.add(rw, gap)),
  Nat.add(List.length(&2, U32, List.drop(&2, U32, xs, Nat.add(rw, gap))), gap)) == True{} : Bool}:
  R.drop_le(xs, Nat.add(rw, gap), Nat.mul(pp, Nat.add(rw, gap)), gap, hh)

# n rows of rw samples, when the list holds them, are n * rw samples
def crop.rows_len(
  nn: Nat,
  +xs: List<&2, U32>,
  +rw: Nat,
  +gap: Nat,
  +hh: {Nat.is_le(Nat.mul(nn, Nat.add(rw, gap)), Nat.add(List.length(&2, U32, xs), gap)) == True{} : Bool}
) -> {List.length(&2, U32, Img.crop.rows(nn, xs, rw, gap)) == Nat.mul(nn, rw) : Nat}:
  match nn:
    case 0n:
      {==}
    case 1n+(+pp):
      +tk = List.take(&2, U32, xs, rw)
      +rest = Img.crop.rows(pp, List.drop(&2, U32, xs, Nat.add(rw, gap)), rw, gap)
      Equal.trans(Nat, List.length(&2, U32, List.append(&2, U32, tk, rest)),
        Nat.add(List.length(&2, U32, tk), List.length(&2, U32, rest)), Nat.add(rw, Nat.mul(pp, rw)),
        R.len_append(tk, rest),
        Equal.trans(Nat, Nat.add(List.length(&2, U32, tk), List.length(&2, U32, rest)),
          Nat.add(rw, List.length(&2, U32, rest)), Nat.add(rw, Nat.mul(pp, rw)),
          Equal.cong(Nat, Nat, xx => Nat.add(xx, List.length(&2, U32, rest)), List.length(&2, U32, tk), rw,
            R.len_take(xs, rw, crop.rows_head(pp, xs, rw, gap, hh))),
          Equal.cong(Nat, Nat, xx => Nat.add(rw, xx), List.length(&2, U32, rest), Nat.mul(pp, rw),
            crop.rows_len(pp, List.drop(&2, U32, xs, Nat.add(rw, gap)), rw, gap, crop.rows_next(pp, xs, rw, gap, hh)))))

# sample (i, j) of the rows walk is sample j * (rw + gap) + i of the list
def crop.rows_get(
  nn: Nat,
  +xs: List<&2, U32>,
  +rw: Nat,
  +gap: Nat,
  +ii: Nat,
  jj: Nat,
  +hi: {Nat.is_lt(ii, rw) == True{} : Bool},
  hj: {Nat.is_lt(jj, nn) == True{} : Bool},
  +hh: {Nat.is_le(Nat.mul(nn, Nat.add(rw, gap)), Nat.add(List.length(&2, U32, xs), gap)) == True{} : Bool}
) -> {List.get(&2, U32, Img.crop.rows(nn, xs, rw, gap), Nat.add(Nat.mul(jj, rw), ii)) ==
  List.get(&2, U32, xs, Nat.add(Nat.mul(jj, Nat.add(rw, gap)), ii)) : Maybe<&2, U32>}:
  match nn jj:
    case 0n _jj:
      Empty.absurd({List.get(&2, U32, Img.crop.rows(0n, xs, rw, gap), Nat.add(Nat.mul(_jj, rw), ii)) ==
        List.get(&2, U32, xs, Nat.add(Nat.mul(_jj, Nat.add(rw, gap)), ii)) : Maybe<&2, U32>},
        U32L.false_true(Equal.trans(Bool, False{}, Nat.is_lt(_jj, 0n), True{}, R.lt_zero_false(_jj), hj)))
    case 1n+(+pp) 0n:
      R.get_append_take(xs, rw, ii, Img.crop.rows(pp, List.drop(&2, U32, xs, Nat.add(rw, gap)), rw, gap), hi,
        crop.rows_head(pp, xs, rw, gap, hh))
    case 1n+(+pp) 1n+(+qq):
      +ss = Nat.add(rw, gap)
      +dx = List.drop(&2, U32, xs, ss)
      +rest = Img.crop.rows(pp, dx, rw, gap)
      +both = List.append(&2, U32, List.take(&2, U32, xs, rw), rest)
      +mq = Nat.mul(qq, rw)
      +ms = Nat.mul(qq, ss)
      Equal.trans(Maybe<&2, U32>, List.get(&2, U32, both, Nat.add(Nat.add(rw, mq), ii)),
        List.get(&2, U32, both, Nat.add(rw, Nat.add(mq, ii))), List.get(&2, U32, xs, Nat.add(Nat.add(ss, ms), ii)),
        Equal.cong(Nat, Maybe<&2, U32>, kk => List.get(&2, U32, both, kk), Nat.add(Nat.add(rw, mq), ii),
          Nat.add(rw, Nat.add(mq, ii)), R.add_assoc(rw, mq, ii)),
        Equal.trans(Maybe<&2, U32>, List.get(&2, U32, both, Nat.add(rw, Nat.add(mq, ii))),
          List.get(&2, U32, rest, Nat.add(mq, ii)), List.get(&2, U32, xs, Nat.add(Nat.add(ss, ms), ii)),
          R.get_append_skip(xs, rw, Nat.add(mq, ii), rest, crop.rows_head(pp, xs, rw, gap, hh)),
          Equal.trans(Maybe<&2, U32>, List.get(&2, U32, rest, Nat.add(mq, ii)),
            List.get(&2, U32, dx, Nat.add(ms, ii)), List.get(&2, U32, xs, Nat.add(Nat.add(ss, ms), ii)),
            crop.rows_get(pp, dx, rw, gap, ii, qq, hi, hj, crop.rows_next(pp, xs, rw, gap, hh)),
            Equal.trans(Maybe<&2, U32>, List.get(&2, U32, dx, Nat.add(ms, ii)),
              List.get(&2, U32, xs, Nat.add(ss, Nat.add(ms, ii))), List.get(&2, U32, xs, Nat.add(Nat.add(ss, ms), ii)),
              R.get_drop(xs, ss, Nat.add(ms, ii)),
              Equal.cong(Nat, Maybe<&2, U32>, kk => List.get(&2, U32, xs, kk), Nat.add(ss, Nat.add(ms, ii)),
                Nat.add(Nat.add(ss, ms), ii), Equal.sym(Nat, Nat.add(Nat.add(ss, ms), ii), Nat.add(ss, Nat.add(ms, ii)),
                  R.add_assoc(ss, ms, ii)))))))

# is the rectangle's intersection with the raster nonempty
def crop.ok(+ww: U32, +hh: U32, +xx: U32, +yy: U32, +cw: U32, +ch: U32) -> Bool:
  Bool.and(Nat.is_lt(0n, Laws.cut(ww, xx, cw)), Nat.is_lt(0n, Laws.cut(hh, yy, ch)))

# what crop returns, once whether the intersection is empty is known
def crop.nf(
  ok: Bool,
  +px: List<&2, U32>,
  +ww: U32,
  +xx: U32,
  +yy: U32,
  +rw: U32,
  +rh: U32
) -> Img.Raster:
  match ok:
    case False{}:
      Img.Raster{0, 0, []}
    case True{}:
      Img.Raster{rw, rh,
        Img.crop.rows(U32.to_nat(rh), List.drop(&2, U32, px, U32.to_nat((yy * ww + xx : U32))),
          U32.to_nat(rw), U32.to_nat((ww - rw : U32)))}

# crop.open is crop.nf on "neither side is zero"
def crop.open_nf(
  zw: Bool,
  zh: Bool,
  +px: List<&2, U32>,
  +ww: U32,
  +xx: U32,
  +yy: U32,
  +rw: U32,
  +rh: U32
) -> {Img.crop.open(zw, zh, px, ww, xx, yy, rw, rh) ==
  crop.nf(Bool.and(Bool.not(zw), Bool.not(zh)), px, ww, xx, yy, rw, rh) : Img.Raster}:
  match zw zh:
    case True{} _zh:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# u.min read as Nat, once the comparison is named
def ras.umin.pick(
  le: Bool,
  +aa: U32,
  +bb: U32,
  ee: {U32.is_le(aa, bb) == le : Bool}
) -> {U32.to_nat(Img.u.min.pick(le, aa, bb)) == Nat.min(U32.to_nat(aa), U32.to_nat(bb)) : Nat}:
  match le:
    case True{}:
      Equal.sym(Nat, Nat.min(U32.to_nat(aa), U32.to_nat(bb)), U32.to_nat(aa), R.min_of_le(U32.to_nat(aa),
        U32.to_nat(bb),
        Equal.trans(Bool, Nat.is_le(U32.to_nat(aa), U32.to_nat(bb)), U32.is_le(aa, bb), True{},
          Equal.sym(Bool, U32.is_le(aa, bb), Nat.is_le(U32.to_nat(aa), U32.to_nat(bb)), R.u32_le(aa, bb)), ee)))
    case False{}:
      Equal.sym(Nat, Nat.min(U32.to_nat(aa), U32.to_nat(bb)), U32.to_nat(bb), R.min_of_gt(U32.to_nat(aa),
        U32.to_nat(bb),
        Equal.trans(Bool, Nat.is_le(U32.to_nat(aa), U32.to_nat(bb)), U32.is_le(aa, bb), False{},
          Equal.sym(Bool, U32.is_le(aa, bb), Nat.is_le(U32.to_nat(aa), U32.to_nat(bb)), R.u32_le(aa, bb)), ee)))

# u.min read as Nat
def ras.umin(+aa: U32, +bb: U32) -> {U32.to_nat(Img.u.min(aa, bb)) == Nat.min(U32.to_nat(aa), U32.to_nat(bb)) : Nat}:
  ras.umin.pick(U32.is_le(aa, bb), aa, bb, {==})

# the side crop computes, min(c, w - x) in U32, is cut(w, x, c) when x < w
def crop.side_nat(
  +ww: U32,
  +xx: U32,
  +cc: U32,
  hx: {Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)) == True{} : Bool}
) -> {U32.to_nat(Img.u.min(cc, (ww - xx : U32))) == Laws.cut(ww, xx, cc) : Nat}:
  Equal.trans(Nat, U32.to_nat(Img.u.min(cc, (ww - xx : U32))), Nat.min(U32.to_nat(cc), U32.to_nat((ww - xx : U32))),
    Laws.cut(ww, xx, cc), ras.umin(cc, (ww - xx : U32)),
    Equal.cong(Nat, Nat, nn => Nat.min(U32.to_nat(cc), nn), U32.to_nat((ww - xx : U32)),
      Nat.sub(U32.to_nat(ww), U32.to_nat(xx)),
      R.u32_sub_nat(ww, xx, R.lt_le(U32.to_nat(xx), U32.to_nat(ww), hx))))

# a U32 side read as n: it is not zero exactly when 0 < n
def crop.nz(
  +ru: U32,
  +nn: Nat,
  ee: {U32.to_nat(ru) == nn : Nat}
) -> {Bool.not(U32.is_zero(ru)) == Nat.is_lt(0n, nn) : Bool}:
  Equal.trans(Bool, Bool.not(U32.is_zero(ru)), Bool.not(Nat.is_eq(nn, 0n)), Nat.is_lt(0n, nn),
    Equal.cong(Bool, Bool, bb => Bool.not(bb), U32.is_zero(ru), Nat.is_eq(nn, 0n),
      Equal.trans(Bool, U32.is_zero(ru), Nat.is_eq(U32.to_nat(ru), 0n), Nat.is_eq(nn, 0n), R.u32_eq(ru, 0),
        Equal.cong(Nat, Bool, mm => Nat.is_eq(mm, 0n), U32.to_nat(ru), nn, ee))),
    Equal.sym(Bool, Nat.is_lt(0n, nn), Bool.not(Nat.is_eq(nn, 0n)), R.pos_eq(nn)))

# x >= w leaves nothing of the span: cut(w, x, c) is 0
def crop.cut_out(
  +ww: U32,
  +xx: U32,
  +cc: U32,
  hx: {Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)) == False{} : Bool}
) -> {Laws.cut(ww, xx, cc) == 0n : Nat}:
  Equal.trans(Nat, Laws.cut(ww, xx, cc), Nat.min(U32.to_nat(cc), 0n), 0n,
    Equal.cong(Nat, Nat, nn => Nat.min(U32.to_nat(cc), nn), Nat.sub(U32.to_nat(ww), U32.to_nat(xx)), 0n,
      R.sub_zero_le(U32.to_nat(ww), U32.to_nat(xx), R.not_lt_le(U32.to_nat(xx), U32.to_nat(ww), hx))),
    R.min_zero_r(U32.to_nat(cc)))

# the box, once both points are inside
def crop.nf_box(
  +px: List<&2, U32>,
  +ww: U32,
  +hh: U32,
  +xx: U32,
  +yy: U32,
  +cw: U32,
  +ch: U32,
  hx: {Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)) == True{} : Bool},
  hy: {Nat.is_lt(U32.to_nat(yy), U32.to_nat(hh)) == True{} : Bool}
) -> {Img.crop.box(px, ww, hh, xx, yy, cw, ch) == crop.nf(crop.ok(ww, hh, xx, yy, cw, ch), px, ww, xx, yy,
  Img.u.min(cw, (ww - xx : U32)), Img.u.min(ch, (hh - yy : U32))) : Img.Raster}:
  +rw = Img.u.min(cw, (ww - xx : U32))
  +rh = Img.u.min(ch, (hh - yy : U32))
  Equal.trans(Img.Raster, Img.crop.open(U32.is_zero(rw), U32.is_zero(rh), px, ww, xx, yy, rw, rh),
    crop.nf(Bool.and(Bool.not(U32.is_zero(rw)), Bool.not(U32.is_zero(rh))), px, ww, xx, yy, rw, rh),
    crop.nf(crop.ok(ww, hh, xx, yy, cw, ch), px, ww, xx, yy, rw, rh),
    crop.open_nf(U32.is_zero(rw), U32.is_zero(rh), px, ww, xx, yy, rw, rh),
    Equal.cong(Bool, Img.Raster, bb => crop.nf(bb, px, ww, xx, yy, rw, rh),
      Bool.and(Bool.not(U32.is_zero(rw)), Bool.not(U32.is_zero(rh))), crop.ok(ww, hh, xx, yy, cw, ch),
      Equal.trans(Bool, Bool.and(Bool.not(U32.is_zero(rw)), Bool.not(U32.is_zero(rh))),
        Bool.and(Nat.is_lt(0n, Laws.cut(ww, xx, cw)), Bool.not(U32.is_zero(rh))), crop.ok(ww, hh, xx, yy, cw, ch),
        Equal.cong(Bool, Bool, bb => Bool.and(bb, Bool.not(U32.is_zero(rh))), Bool.not(U32.is_zero(rw)),
          Nat.is_lt(0n, Laws.cut(ww, xx, cw)), crop.nz(rw, Laws.cut(ww, xx, cw), crop.side_nat(ww, xx, cw, hx))),
        Equal.cong(Bool, Bool, bb => Bool.and(Nat.is_lt(0n, Laws.cut(ww, xx, cw)), bb), Bool.not(U32.is_zero(rh)),
          Nat.is_lt(0n, Laws.cut(hh, yy, ch)), crop.nz(rh, Laws.cut(hh, yy, ch), crop.side_nat(hh, yy, ch, hy))))))

# crop.y is crop.nf, once x is inside
def crop.nf_y(
  yin: Bool,
  +px: List<&2, U32>,
  +ww: U32,
  +hh: U32,
  +xx: U32,
  +yy: U32,
  +cw: U32,
  +ch: U32,
  ey: {Nat.is_lt(U32.to_nat(yy), U32.to_nat(hh)) == yin : Bool},
  hx: {Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)) == True{} : Bool}
) -> {Img.crop.y(yin, px, ww, hh, xx, yy, cw, ch) == crop.nf(crop.ok(ww, hh, xx, yy, cw, ch), px, ww, xx, yy,
  Img.u.min(cw, (ww - xx : U32)), Img.u.min(ch, (hh - yy : U32))) : Img.Raster}:
  match yin:
    case False{}:
      Equal.cong(Bool, Img.Raster, bb => crop.nf(bb, px, ww, xx, yy, Img.u.min(cw, (ww - xx : U32)),
        Img.u.min(ch, (hh - yy : U32))), False{}, crop.ok(ww, hh, xx, yy, cw, ch),
        Equal.sym(Bool, crop.ok(ww, hh, xx, yy, cw, ch), False{},
          Equal.trans(Bool, crop.ok(ww, hh, xx, yy, cw, ch), Bool.and(Nat.is_lt(0n, Laws.cut(ww, xx, cw)), False{}),
            False{}, Equal.cong(Nat, Bool, nn => Bool.and(Nat.is_lt(0n, Laws.cut(ww, xx, cw)), Nat.is_lt(0n, nn)),
              Laws.cut(hh, yy, ch), 0n, crop.cut_out(hh, yy, ch, ey)),
            R.and_false_r(Nat.is_lt(0n, Laws.cut(ww, xx, cw))))))
    case True{}:
      crop.nf_box(px, ww, hh, xx, yy, cw, ch, hx, ey)

# crop.x is crop.nf
def crop.nf_x(
  xin: Bool,
  +px: List<&2, U32>,
  +ww: U32,
  +hh: U32,
  +xx: U32,
  +yy: U32,
  +cw: U32,
  +ch: U32,
  ex: {Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)) == xin : Bool}
) -> {Img.crop.x(xin, px, ww, hh, xx, yy, cw, ch) == crop.nf(crop.ok(ww, hh, xx, yy, cw, ch), px, ww, xx, yy,
  Img.u.min(cw, (ww - xx : U32)), Img.u.min(ch, (hh - yy : U32))) : Img.Raster}:
  match xin:
    case False{}:
      Equal.cong(Bool, Img.Raster, bb => crop.nf(bb, px, ww, xx, yy, Img.u.min(cw, (ww - xx : U32)),
        Img.u.min(ch, (hh - yy : U32))), False{}, crop.ok(ww, hh, xx, yy, cw, ch),
        Equal.sym(Bool, crop.ok(ww, hh, xx, yy, cw, ch), False{},
          Equal.cong(Nat, Bool, nn => Bool.and(Nat.is_lt(0n, nn), Nat.is_lt(0n, Laws.cut(hh, yy, ch))),
            Laws.cut(ww, xx, cw), 0n, crop.cut_out(ww, xx, cw, ex))))
    case True{}:
      Equal.trans(Img.Raster, Img.crop.y(U32.is_lt(yy, hh), px, ww, hh, xx, yy, cw, ch),
        Img.crop.y(Nat.is_lt(U32.to_nat(yy), U32.to_nat(hh)), px, ww, hh, xx, yy, cw, ch),
        crop.nf(crop.ok(ww, hh, xx, yy, cw, ch), px, ww, xx, yy, Img.u.min(cw, (ww - xx : U32)),
          Img.u.min(ch, (hh - yy : U32))),
        Equal.cong(Bool, Img.Raster, bb => Img.crop.y(bb, px, ww, hh, xx, yy, cw, ch), U32.is_lt(yy, hh),
          Nat.is_lt(U32.to_nat(yy), U32.to_nat(hh)), R.u32_lt(yy, hh)),
        crop.nf_y(Nat.is_lt(U32.to_nat(yy), U32.to_nat(hh)), px, ww, hh, xx, yy, cw, ch, {==}, ex))

# crop, taken apart, is crop.nf
def crop.nf_eq(
  +px: List<&2, U32>,
  +ww: U32,
  +hh: U32,
  +xx: U32,
  +yy: U32,
  +cw: U32,
  +ch: U32
) -> {Img.crop(Img.Raster{ww, hh, px}, xx, yy, cw, ch) == crop.nf(crop.ok(ww, hh, xx, yy, cw, ch), px, ww, xx, yy,
  Img.u.min(cw, (ww - xx : U32)), Img.u.min(ch, (hh - yy : U32))) : Img.Raster}:
  Equal.trans(Img.Raster, Img.crop.x(U32.is_lt(xx, ww), px, ww, hh, xx, yy, cw, ch),
    Img.crop.x(Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)), px, ww, hh, xx, yy, cw, ch),
    crop.nf(crop.ok(ww, hh, xx, yy, cw, ch), px, ww, xx, yy, Img.u.min(cw, (ww - xx : U32)),
      Img.u.min(ch, (hh - yy : U32))),
    Equal.cong(Bool, Img.Raster, bb => Img.crop.x(bb, px, ww, hh, xx, yy, cw, ch), U32.is_lt(xx, ww),
      Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)), R.u32_lt(xx, ww)),
    crop.nf_x(Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)), px, ww, hh, xx, yy, cw, ch, {==}))

# a nonempty span starts inside: 0 < cut(w, x, c) gives x < w
def crop.cut_pos(
  +ww: U32,
  +xx: U32,
  +cc: U32,
  hh: {Nat.is_lt(0n, Laws.cut(ww, xx, cc)) == True{} : Bool}
) -> {Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)) == True{} : Bool}:
  +dd = Nat.sub(U32.to_nat(ww), U32.to_nat(xx))
  R.sub_pos(U32.to_nat(ww), U32.to_nat(xx), R.lt_le_trans(0n, Laws.cut(ww, xx, cc), dd, hh,
    R.min_le_r(U32.to_nat(cc), dd)))

# the span crop keeps ends inside: x + rw <= w
def crop.fit(
  +ww: U32,
  +xx: U32,
  +cc: U32,
  +hx: {Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)) == True{} : Bool}
) -> {Nat.is_le(Nat.add(U32.to_nat(xx), U32.to_nat(Img.u.min(cc, (ww - xx : U32)))), U32.to_nat(ww)) == True{} :
  Bool}:
  +wn = U32.to_nat(ww)
  +xn = U32.to_nat(xx)
  +dd = Nat.sub(wn, xn)
  +rn = U32.to_nat(Img.u.min(cc, (ww - xx : U32)))
  +er = {crop.side_nat(ww, xx, cc, hx) : {rn == Laws.cut(ww, xx, cc) : Nat}}
  R.le_rw_r(Nat.add(xn, rn), Nat.add(xn, dd), wn, R.add_sub(xn, wn, R.lt_le(xn, wn, hx)),
    R.le_add_mono(xn, rn, dd, R.le_rw_l(Laws.cut(ww, xx, cc), rn, dd, Equal.sym(Nat, rn, Laws.cut(ww, xx, cc), er),
      R.min_le_r(U32.to_nat(cc), dd))))

# the span and the gap crop steps over make up a row: rw + (w - rw) = w
def crop.row(
  +ww: U32,
  +xx: U32,
  +cc: U32,
  +hx: {Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)) == True{} : Bool}
) -> {Nat.add(U32.to_nat(Img.u.min(cc, (ww - xx : U32))), U32.to_nat((ww - Img.u.min(cc, (ww - xx : U32)) : U32))) ==
  U32.to_nat(ww) : Nat}:
  +rw = Img.u.min(cc, (ww - xx : U32))
  +rn = U32.to_nat(rw)
  +wn = U32.to_nat(ww)
  +hr = {R.le_add_l(U32.to_nat(xx), rn, wn, crop.fit(ww, xx, cc, hx)) : {Nat.is_le(rn, wn) == True{} : Bool}}
  Equal.trans(Nat, Nat.add(rn, U32.to_nat((ww - rw : U32))), Nat.add(rn, Nat.sub(wn, rn)), wn,
    Equal.cong(Nat, Nat, nn => Nat.add(rn, nn), U32.to_nat((ww - rw : U32)), Nat.sub(wn, rn),
      R.u32_sub_nat(ww, rw, hr)),
    R.add_sub(rn, wn, hr))

# the gap crop steps over holds the start: x <= w - rw
def crop.gap(
  +ww: U32,
  +xx: U32,
  +cc: U32,
  +hx: {Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)) == True{} : Bool}
) -> {Nat.is_le(U32.to_nat(xx), U32.to_nat((ww - Img.u.min(cc, (ww - xx : U32)) : U32))) == True{} : Bool}:
  +rw = Img.u.min(cc, (ww - xx : U32))
  +rn = U32.to_nat(rw)
  +wn = U32.to_nat(ww)
  +hf = {crop.fit(ww, xx, cc, hx) : {Nat.is_le(Nat.add(U32.to_nat(xx), rn), wn) == True{} : Bool}}
  R.le_rw_r(U32.to_nat(xx), Nat.sub(wn, rn), U32.to_nat((ww - rw : U32)),
    Equal.sym(Nat, U32.to_nat((ww - rw : U32)), Nat.sub(wn, rn), R.u32_sub_nat(ww, rw, R.le_add_l(U32.to_nat(xx), rn,
      wn, hf))),
    R.le_sub_of_add(U32.to_nat(xx), rn, wn, hf))

# the rows walk over a well-formed raster has what it reads: rh * (rw + gap) <= length after the start + gap
def crop.cond(
  +px: List<&2, U32>,
  +ww: U32,
  +hh: U32,
  +xx: U32,
  +yy: U32,
  +cw: U32,
  +ch: U32,
  +area: U32,
  h_area: {U32.to_nat(area) == Nat.mul(U32.to_nat(ww), U32.to_nat(hh)) : Nat},
  h_wf: {Laws.wf(Img.Raster{ww, hh, px}) == True{} : Bool},
  +hx: {Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)) == True{} : Bool},
  +hy: {Nat.is_lt(U32.to_nat(yy), U32.to_nat(hh)) == True{} : Bool}
) -> {Nat.is_le(Nat.mul(U32.to_nat(Img.u.min(ch, (hh - yy : U32))), Nat.add(U32.to_nat(Img.u.min(cw, (ww - xx : U32))),
  U32.to_nat((ww - Img.u.min(cw, (ww - xx : U32)) : U32)))), Nat.add(List.length(&2, U32, List.drop(&2, U32, px,
  U32.to_nat((yy * ww + xx : U32)))), U32.to_nat((ww - Img.u.min(cw, (ww - xx : U32)) : U32)))) == True{} : Bool}:
  +wn = U32.to_nat(ww)
  +hn = U32.to_nat(hh)
  +xn = U32.to_nat(xx)
  +yn = U32.to_nat(yy)
  +rw = Img.u.min(cw, (ww - xx : U32))
  +rhn = U32.to_nat(Img.u.min(ch, (hh - yy : U32)))
  +gn = U32.to_nat((ww - rw : U32))
  +s0 = U32.to_nat((yy * ww + xx : U32))
  +yw = Nat.mul(yn, wn)
  +ln = List.length(&2, U32, px)
  +el = {R.nat_eq_true(ln, Nat.mul(wn, hn), h_wf) : {ln == Nat.mul(wn, hn) : Nat}}
  +es = {R.u32_index(ww, xx, yy, hh, area, h_area, hx, hy) : {s0 == Nat.add(yw, xn) : Nat}}
  +hr = {R.le_rw_r(Nat.mul(Nat.add(yn, rhn), wn), Nat.mul(hn, wn), Nat.mul(wn, hn), R.mul_comm(hn, wn),
    R.le_mul_mono(Nat.add(yn, rhn), hn, wn, crop.fit(hh, yy, ch, hy))) :
    {Nat.is_le(Nat.mul(Nat.add(yn, rhn), wn), Nat.mul(wn, hn)) == True{} : Bool}}
  +e_lhs = {Equal.trans(Nat, Nat.add(s0, Nat.mul(rhn, wn)), Nat.add(Nat.add(yw, xn), Nat.mul(rhn, wn)),
    Nat.add(Nat.mul(Nat.add(yn, rhn), wn), xn),
    Equal.cong(Nat, Nat, nn => Nat.add(nn, Nat.mul(rhn, wn)), s0, Nat.add(yw, xn), es),
    Equal.trans(Nat, Nat.add(Nat.add(yw, xn), Nat.mul(rhn, wn)), Nat.add(Nat.add(yw, Nat.mul(rhn, wn)), xn),
      Nat.add(Nat.mul(Nat.add(yn, rhn), wn), xn), R.add_right_swap(yw, xn, Nat.mul(rhn, wn)),
      Equal.cong(Nat, Nat, nn => Nat.add(nn, xn), Nat.add(yw, Nat.mul(rhn, wn)), Nat.mul(Nat.add(yn, rhn), wn),
        Equal.sym(Nat, Nat.mul(Nat.add(yn, rhn), wn), Nat.add(yw, Nat.mul(rhn, wn)), R.mul_add(yn, rhn, wn))))) :
    {Nat.add(s0, Nat.mul(rhn, wn)) == Nat.add(Nat.mul(Nat.add(yn, rhn), wn), xn) : Nat}}
  +h_main = {R.le_rw_r(Nat.add(s0, Nat.mul(rhn, wn)), Nat.add(Nat.mul(wn, hn), gn), Nat.add(ln, gn),
    Equal.cong(Nat, Nat, nn => Nat.add(nn, gn), Nat.mul(wn, hn), ln, Equal.sym(Nat, ln, Nat.mul(wn, hn), el)),
    R.le_rw_l(Nat.add(Nat.mul(Nat.add(yn, rhn), wn), xn), Nat.add(s0, Nat.mul(rhn, wn)), Nat.add(Nat.mul(wn, hn), gn),
      Equal.sym(Nat, Nat.add(s0, Nat.mul(rhn, wn)), Nat.add(Nat.mul(Nat.add(yn, rhn), wn), xn), e_lhs),
      R.le_add_both(Nat.mul(Nat.add(yn, rhn), wn), Nat.mul(wn, hn), xn, gn, hr, crop.gap(ww, xx, cw, hx)))) :
    {Nat.is_le(Nat.add(s0, Nat.mul(rhn, wn)), Nat.add(ln, gn)) == True{} : Bool}}
  R.le_rw_l(Nat.mul(rhn, wn), Nat.mul(rhn, Nat.add(U32.to_nat(rw), gn)),
    Nat.add(List.length(&2, U32, List.drop(&2, U32, px, s0)), gn),
    Equal.cong(Nat, Nat, nn => Nat.mul(rhn, nn), wn, Nat.add(U32.to_nat(rw), gn),
      Equal.sym(Nat, Nat.add(U32.to_nat(rw), gn), wn, crop.row(ww, xx, cw, hx))),
    R.drop_le(px, s0, Nat.mul(rhn, wn), gn, h_main))

# both sides of an empty intersection's crop are 0
def crop.side_zero(
  aa: Nat,
  bb: Nat,
  hh: {Bool.and(Nat.is_lt(0n, aa), Nat.is_lt(0n, bb)) == False{} : Bool}
) -> {(0n, 0n) == (Laws.side(aa, bb), Laws.side(bb, aa)) : Nat & Nat}:
  match aa bb:
    case 0n 0n:
      {==}
    case 0n 1n+_qq:
      {==}
    case 1n+_pp 0n:
      {==}
    case 1n+_pp 1n+_qq:
      Empty.absurd({(0n, 0n) == (1n+_pp, 1n+_qq) : Nat & Nat}, U32L.false_true(Equal.sym(Bool, True{}, False{}, hh)))

# both sides of a nonempty intersection's crop are the intersection's
def crop.side_pos(
  aa: Nat,
  bb: Nat,
  hh: {Bool.and(Nat.is_lt(0n, aa), Nat.is_lt(0n, bb)) == True{} : Bool}
) -> {(aa, bb) == (Laws.side(aa, bb), Laws.side(bb, aa)) : Nat & Nat}:
  match aa bb:
    case 0n _bb:
      Empty.absurd({(0n, _bb) == (Laws.side(0n, _bb), Laws.side(_bb, 0n)) : Nat & Nat}, U32L.false_true(hh))
    case 1n+_pp 0n:
      Empty.absurd({(1n+_pp, 0n) == (0n, 0n) : Nat & Nat}, U32L.false_true(
        Equal.trans(Bool, False{}, Bool.and(True{}, False{}), True{}, {==}, hh)))
    case 1n+_pp 1n+_qq:
      {==}

# crop's size, once whether the intersection is empty is known
def crop.size_nf(
  ok: Bool,
  +px: List<&2, U32>,
  +ww: U32,
  +hh: U32,
  +xx: U32,
  +yy: U32,
  +cw: U32,
  +ch: U32,
  e_ok: {crop.ok(ww, hh, xx, yy, cw, ch) == ok : Bool}
) -> {(U32.to_nat(Img.width(crop.nf(ok, px, ww, xx, yy, Img.u.min(cw, (ww - xx : U32)), Img.u.min(ch,
  (hh - yy : U32))))),
  U32.to_nat(Img.height(crop.nf(ok, px, ww, xx, yy, Img.u.min(cw, (ww - xx : U32)), Img.u.min(ch,
    (hh - yy : U32)))))) ==
  (Laws.side(Laws.cut(ww, xx, cw), Laws.cut(hh, yy, ch)), Laws.side(Laws.cut(hh, yy, ch), Laws.cut(ww, xx, cw))) :
  Nat & Nat}:
  match ok:
    case False{}:
      crop.side_zero(Laws.cut(ww, xx, cw), Laws.cut(hh, yy, ch), e_ok)
    case True{}:
      +iw = Laws.cut(ww, xx, cw)
      +ih = Laws.cut(hh, yy, ch)
      +e2 = {e_ok : {Bool.and(Nat.is_lt(0n, iw), Nat.is_lt(0n, ih)) == True{} : Bool}}
      +rn = U32.to_nat(Img.u.min(cw, (ww - xx : U32)))
      +hn = U32.to_nat(Img.u.min(ch, (hh - yy : U32)))
      +er = {crop.side_nat(ww, xx, cw, crop.cut_pos(ww, xx, cw, U32L.and_left(Nat.is_lt(0n, iw), Nat.is_lt(0n, ih),
        e2))) :
        {rn == iw : Nat}}
      +eh = {crop.side_nat(hh, yy, ch, crop.cut_pos(hh, yy, ch, U32L.and_right(Nat.is_lt(0n, iw), Nat.is_lt(0n, ih),
        e2)))
        : {hn == ih : Nat}}
      Equal.trans(Nat & Nat, (rn, hn), (iw, ih), (Laws.side(iw, ih), Laws.side(ih, iw)),
        Equal.trans(Nat & Nat, (rn, hn), (iw, hn), (iw, ih),
          Equal.cong(Nat, Nat & Nat, nn => (nn, hn), rn, iw, er),
          Equal.cong(Nat, Nat & Nat, nn => (iw, nn), hn, ih, eh)),
        crop.side_pos(iw, ih, e2))

def Laws.crop_size(img, xx, yy, cw, ch):
  match img:
    case Img.Raster{+ww, +hh, +px}:
      +rw = Img.u.min(cw, (ww - xx : U32))
      +rh = Img.u.min(ch, (hh - yy : U32))
      +nf = crop.nf(crop.ok(ww, hh, xx, yy, cw, ch), px, ww, xx, yy, rw, rh)
      Equal.trans(Nat & Nat, (U32.to_nat(Img.width(Img.crop(Img.Raster{ww, hh, px}, xx, yy, cw, ch))),
        U32.to_nat(Img.height(Img.crop(Img.Raster{ww, hh, px}, xx, yy, cw, ch)))),
        (U32.to_nat(Img.width(nf)), U32.to_nat(Img.height(nf))),
        (Laws.side(Laws.cut(ww, xx, cw), Laws.cut(hh, yy, ch)), Laws.side(Laws.cut(hh, yy, ch), Laws.cut(ww, xx, cw))),
        Equal.cong(Img.Raster, Nat & Nat, +rr => (U32.to_nat(Img.width(rr)), U32.to_nat(Img.height(rr))),
          Img.crop(Img.Raster{ww, hh, px}, xx, yy, cw, ch), nf, crop.nf_eq(px, ww, hh, xx, yy, cw, ch)),
        crop.size_nf(crop.ok(ww, hh, xx, yy, cw, ch), px, ww, hh, xx, yy, cw, ch, {==}))

# a nonempty crop's facts: x < w and y < h
def crop.in_x(
  +ww: U32,
  +hh: U32,
  +xx: U32,
  +yy: U32,
  +cw: U32,
  +ch: U32,
  e_ok: {crop.ok(ww, hh, xx, yy, cw, ch) == True{} : Bool}
) -> {Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)) == True{} : Bool}:
  crop.cut_pos(ww, xx, cw, U32L.and_left(Nat.is_lt(0n, Laws.cut(ww, xx, cw)), Nat.is_lt(0n, Laws.cut(hh, yy, ch)),
    e_ok))

# the y half of crop.in_x
def crop.in_y(
  +ww: U32,
  +hh: U32,
  +xx: U32,
  +yy: U32,
  +cw: U32,
  +ch: U32,
  e_ok: {crop.ok(ww, hh, xx, yy, cw, ch) == True{} : Bool}
) -> {Nat.is_lt(U32.to_nat(yy), U32.to_nat(hh)) == True{} : Bool}:
  crop.cut_pos(hh, yy, ch, U32L.and_right(Nat.is_lt(0n, Laws.cut(ww, xx, cw)), Nat.is_lt(0n, Laws.cut(hh, yy, ch)),
    e_ok))

# crop is well formed, once whether the intersection is empty is known
def crop.wf_nf(
  ok: Bool,
  +px: List<&2, U32>,
  +ww: U32,
  +hh: U32,
  +xx: U32,
  +yy: U32,
  +cw: U32,
  +ch: U32,
  +e_ok: {crop.ok(ww, hh, xx, yy, cw, ch) == ok : Bool},
  +area: U32,
  h_area: {U32.to_nat(area) == Nat.mul(U32.to_nat(ww), U32.to_nat(hh)) : Nat},
  h_wf: {Laws.wf(Img.Raster{ww, hh, px}) == True{} : Bool}
) -> {Laws.wf(crop.nf(ok, px, ww, xx, yy, Img.u.min(cw, (ww - xx : U32)), Img.u.min(ch, (hh - yy : U32)))) == True{} :
  Bool}:
  match ok:
    case False{}:
      {==}
    case True{}:
      +rw = Img.u.min(cw, (ww - xx : U32))
      +rh = Img.u.min(ch, (hh - yy : U32))
      +rows = Img.crop.rows(U32.to_nat(rh), List.drop(&2, U32, px, U32.to_nat((yy * ww + xx : U32))), U32.to_nat(rw),
        U32.to_nat((ww - rw : U32)))
      +el = {Equal.trans(Nat, List.length(&2, U32, rows), Nat.mul(U32.to_nat(rh), U32.to_nat(rw)),
        Nat.mul(U32.to_nat(rw), U32.to_nat(rh)),
        crop.rows_len(U32.to_nat(rh), List.drop(&2, U32, px, U32.to_nat((yy * ww + xx : U32))), U32.to_nat(rw),
          U32.to_nat((ww - rw : U32)), crop.cond(px, ww, hh, xx, yy, cw, ch, area, h_area, h_wf,
            crop.in_x(ww, hh, xx, yy, cw, ch, e_ok), crop.in_y(ww, hh, xx, yy, cw, ch, e_ok))),
        R.mul_comm(U32.to_nat(rh), U32.to_nat(rw))) :
        {List.length(&2, U32, rows) == Nat.mul(U32.to_nat(rw), U32.to_nat(rh)) : Nat}}
      Equal.trans(Bool, Nat.is_eq(List.length(&2, U32, rows), Nat.mul(U32.to_nat(rw), U32.to_nat(rh))),
        Nat.is_eq(Nat.mul(U32.to_nat(rw), U32.to_nat(rh)), Nat.mul(U32.to_nat(rw), U32.to_nat(rh))), True{},
        Equal.cong(Nat, Bool, nn => Nat.is_eq(nn, Nat.mul(U32.to_nat(rw), U32.to_nat(rh))), List.length(&2, U32, rows),
          Nat.mul(U32.to_nat(rw), U32.to_nat(rh)), el),
        R.nat_eq_refl(Nat.mul(U32.to_nat(rw), U32.to_nat(rh))))

def Laws.crop_wf(img, xx, yy, cw, ch, area, h_area, h_wf):
  match img:
    case Img.Raster{+ww, +hh, +px}:
      +nf = crop.nf(crop.ok(ww, hh, xx, yy, cw, ch), px, ww, xx, yy, Img.u.min(cw, (ww - xx : U32)),
        Img.u.min(ch, (hh - yy : U32)))
      Equal.trans(Bool, Laws.wf(Img.crop(Img.Raster{ww, hh, px}, xx, yy, cw, ch)), Laws.wf(nf), True{},
        Equal.cong(Img.Raster, Bool, rr => Laws.wf(rr), Img.crop(Img.Raster{ww, hh, px}, xx, yy, cw, ch), nf,
          crop.nf_eq(px, ww, hh, xx, yy, cw, ch)),
        crop.wf_nf(crop.ok(ww, hh, xx, yy, cw, ch), px, ww, hh, xx, yy, cw, ch, {==}, area, h_area, h_wf))

# crop.nf at crop's own sides
def crop.nfx(
  ok: Bool,
  +px: List<&2, U32>,
  +ww: U32,
  +hh: U32,
  +xx: U32,
  +yy: U32,
  +cw: U32,
  +ch: U32
) -> Img.Raster:
  crop.nf(ok, px, ww, xx, yy, Img.u.min(cw, (ww - xx : U32)), Img.u.min(ch, (hh - yy : U32)))

# crop's sample at (i, j), once whether the intersection is empty is known
def crop.at_nf(
  ok: Bool,
  +px: List<&2, U32>,
  +ww: U32,
  +hh: U32,
  +xx: U32,
  +yy: U32,
  +cw: U32,
  +ch: U32,
  +e_ok: {crop.ok(ww, hh, xx, yy, cw, ch) == ok : Bool},
  +area: U32,
  +h_area: {U32.to_nat(area) == Nat.mul(U32.to_nat(ww), U32.to_nat(hh)) : Nat},
  h_wf: {Laws.wf(Img.Raster{ww, hh, px}) == True{} : Bool},
  +ii: Nat,
  +jj: Nat,
  hi: {Nat.is_lt(ii, U32.to_nat(Img.width(crop.nfx(ok, px, ww, hh, xx, yy, cw, ch)))) == True{} : Bool},
  hj: {Nat.is_lt(jj, U32.to_nat(Img.height(crop.nfx(ok, px, ww, hh, xx, yy, cw, ch)))) == True{} : Bool}
) -> {List.get(&2, U32, Img.pixels(crop.nfx(ok, px, ww, hh, xx, yy, cw, ch)),
  Nat.add(Nat.mul(jj, U32.to_nat(Img.width(crop.nfx(ok, px, ww, hh, xx, yy, cw, ch)))), ii)) ==
  List.get(&2, U32, px, Nat.add(Nat.mul(Nat.add(U32.to_nat(yy), jj), U32.to_nat(ww)), Nat.add(U32.to_nat(xx), ii))) :
  Maybe<&2, U32>}:
  match ok:
    case False{}:
      Empty.absurd({List.get(&2, U32, [], Nat.add(Nat.mul(jj, 0n), ii)) == List.get(&2, U32, px,
        Nat.add(Nat.mul(Nat.add(U32.to_nat(yy), jj), U32.to_nat(ww)), Nat.add(U32.to_nat(xx), ii))) : Maybe<&2, U32>},
        U32L.false_true(Equal.trans(Bool, False{}, Nat.is_lt(ii, 0n), True{}, R.lt_zero_false(ii), hi)))
    case True{}:
      +wn = U32.to_nat(ww)
      +xn = U32.to_nat(xx)
      +yn = U32.to_nat(yy)
      +rw = Img.u.min(cw, (ww - xx : U32))
      +rn = U32.to_nat(rw)
      +gn = U32.to_nat((ww - rw : U32))
      +s0 = U32.to_nat((yy * ww + xx : U32))
      +ll = List.drop(&2, U32, px, s0)
      +hx = {crop.in_x(ww, hh, xx, yy, cw, ch, e_ok) : {Nat.is_lt(xn, wn) == True{} : Bool}}
      +hy = {crop.in_y(ww, hh, xx, yy, cw, ch, e_ok) : {Nat.is_lt(yn, U32.to_nat(hh)) == True{} : Bool}}
      +jw = Nat.mul(jj, wn)
      +yw = Nat.mul(yn, wn)
      Equal.trans(Maybe<&2, U32>,
        List.get(&2, U32, Img.crop.rows(U32.to_nat(Img.u.min(ch, (hh - yy : U32))), ll, rn, gn), Nat.add(Nat.mul(jj,
          rn), ii)),
        List.get(&2, U32, ll, Nat.add(Nat.mul(jj, Nat.add(rn, gn)), ii)),
        List.get(&2, U32, px, Nat.add(Nat.mul(Nat.add(yn, jj), wn), Nat.add(xn, ii))),
        crop.rows_get(U32.to_nat(Img.u.min(ch, (hh - yy : U32))), ll, rn, gn, ii, jj, hi, hj,
          crop.cond(px, ww, hh, xx, yy, cw, ch, area, h_area, h_wf, hx, hy)),
        Equal.trans(Maybe<&2, U32>, List.get(&2, U32, ll, Nat.add(Nat.mul(jj, Nat.add(rn, gn)), ii)),
          List.get(&2, U32, ll, Nat.add(jw, ii)),
          List.get(&2, U32, px, Nat.add(Nat.mul(Nat.add(yn, jj), wn), Nat.add(xn, ii))),
          Equal.cong(Nat, Maybe<&2, U32>, nn => List.get(&2, U32, ll, Nat.add(Nat.mul(jj, nn), ii)), Nat.add(rn,
            gn), wn,
            crop.row(ww, xx, cw, hx)),
          Equal.trans(Maybe<&2, U32>, List.get(&2, U32, ll, Nat.add(jw, ii)),
            List.get(&2, U32, px, Nat.add(s0, Nat.add(jw, ii))),
            List.get(&2, U32, px, Nat.add(Nat.mul(Nat.add(yn, jj), wn), Nat.add(xn, ii))),
            R.get_drop(px, s0, Nat.add(jw, ii)),
            Equal.cong(Nat, Maybe<&2, U32>, nn => List.get(&2, U32, px, nn), Nat.add(s0, Nat.add(jw, ii)),
              Nat.add(Nat.mul(Nat.add(yn, jj), wn), Nat.add(xn, ii)),
              Equal.trans(Nat, Nat.add(s0, Nat.add(jw, ii)), Nat.add(Nat.add(yw, xn), Nat.add(jw, ii)),
                Nat.add(Nat.mul(Nat.add(yn, jj), wn), Nat.add(xn, ii)),
                Equal.cong(Nat, Nat, nn => Nat.add(nn, Nat.add(jw, ii)), s0, Nat.add(yw, xn),
                  R.u32_index(ww, xx, yy, hh, area, h_area, hx, hy)),
                Equal.trans(Nat, Nat.add(Nat.add(yw, xn), Nat.add(jw, ii)), Nat.add(Nat.add(yw, jw), Nat.add(xn, ii)),
                  Nat.add(Nat.mul(Nat.add(yn, jj), wn), Nat.add(xn, ii)), R.add4(yw, xn, jw, ii),
                  Equal.cong(Nat, Nat, nn => Nat.add(nn, Nat.add(xn, ii)), Nat.add(yw, jw), Nat.mul(Nat.add(yn, jj),
                    wn),
                    Equal.sym(Nat, Nat.mul(Nat.add(yn, jj), wn), Nat.add(yw, jw), R.mul_add(yn, jj, wn)))))))))

def Laws.crop_at(img, xx, yy, cw, ch, area, h_area, h_wf, ii, jj, hi, hj):
  match img:
    case Img.Raster{+ww, +hh, +px}:
      +cr = Img.crop(Img.Raster{ww, hh, px}, xx, yy, cw, ch)
      +nf = crop.nf(crop.ok(ww, hh, xx, yy, cw, ch), px, ww, xx, yy, Img.u.min(cw, (ww - xx : U32)),
        Img.u.min(ch, (hh - yy : U32)))
      +en = {crop.nf_eq(px, ww, hh, xx, yy, cw, ch) : {cr == nf : Img.Raster}}
      Equal.trans(Maybe<&2, U32>,
        List.get(&2, U32, Img.pixels(cr), Nat.add(Nat.mul(jj, U32.to_nat(Img.width(cr))), ii)),
        List.get(&2, U32, Img.pixels(nf), Nat.add(Nat.mul(jj, U32.to_nat(Img.width(nf))), ii)),
        List.get(&2, U32, px, Nat.add(Nat.mul(Nat.add(U32.to_nat(yy), jj), U32.to_nat(ww)), Nat.add(U32.to_nat(xx),
          ii))),
        Equal.cong(Img.Raster, Maybe<&2, U32>,
          +rr => List.get(&2, U32, Img.pixels(rr), Nat.add(Nat.mul(jj, U32.to_nat(Img.width(rr))), ii)), cr, nf, en),
        crop.at_nf(crop.ok(ww, hh, xx, yy, cw, ch), px, ww, hh, xx, yy, cw, ch, {==}, area, h_area, h_wf, ii, jj,
          Equal.trans(Bool, Nat.is_lt(ii, U32.to_nat(Img.width(nf))), Nat.is_lt(ii, U32.to_nat(Img.width(cr))), True{},
            Equal.cong(Img.Raster, Bool, rr => Nat.is_lt(ii, U32.to_nat(Img.width(rr))), nf, cr,
              Equal.sym(Img.Raster, cr, nf, en)), hi),
          Equal.trans(Bool, Nat.is_lt(jj, U32.to_nat(Img.height(nf))), Nat.is_lt(jj, U32.to_nat(Img.height(cr))),
            True{},
            Equal.cong(Img.Raster, Bool, rr => Nat.is_lt(jj, U32.to_nat(Img.height(rr))), nf, cr,
              Equal.sym(Img.Raster, cr, nf, en)), hj)))

# ---- wp6-raster: blit ----

# one pasted row has l + c + t samples, when the rows it reads hold them
def blit.row_len(
  +dp: List<&2, U32>,
  +sp: List<&2, U32>,
  +ll: Nat,
  +cc: Nat,
  +tt: Nat,
  +hd: {Nat.is_le(Nat.add(ll, Nat.add(cc, tt)), List.length(&2, U32, dp)) == True{} : Bool},
  hs: {Nat.is_le(cc, List.length(&2, U32, sp)) == True{} : Bool}
) -> {List.length(&2, U32, Img.blit.row(dp, sp, ll, cc, tt)) == Nat.add(ll, Nat.add(cc, tt)) : Nat}:
  +ln = List.length(&2, U32, dp)
  +dr = List.drop(&2, U32, dp, Nat.add(ll, cc))
  +tk = List.take(&2, U32, dr, tt)
  +sk = List.take(&2, U32, sp, cc)
  +inner = List.append(&2, U32, sk, tk)
  +ht = {R.drop_le0(dp, Nat.add(ll, cc), tt, R.le_rw_l(Nat.add(ll, Nat.add(cc, tt)), Nat.add(Nat.add(ll, cc), tt), ln,
    Equal.sym(Nat, Nat.add(Nat.add(ll, cc), tt), Nat.add(ll, Nat.add(cc, tt)), R.add_assoc(ll, cc, tt)), hd)) :
    {Nat.is_le(tt, List.length(&2, U32, dr)) == True{} : Bool}}
  +e_in = {Equal.trans(Nat, List.length(&2, U32, inner), Nat.add(List.length(&2, U32, sk), List.length(&2, U32, tk)),
    Nat.add(cc, tt), R.len_append(sk, tk),
    Equal.trans(Nat, Nat.add(List.length(&2, U32, sk), List.length(&2, U32, tk)), Nat.add(cc, List.length(&2, U32, tk)),
      Nat.add(cc, tt),
      Equal.cong(Nat, Nat, nn => Nat.add(nn, List.length(&2, U32, tk)), List.length(&2, U32, sk), cc,
        R.len_take(sp, cc, hs)),
      Equal.cong(Nat, Nat, nn => Nat.add(cc, nn), List.length(&2, U32, tk), tt, R.len_take(dr, tt, ht)))) :
    {List.length(&2, U32, inner) == Nat.add(cc, tt) : Nat}}
  Equal.trans(Nat, List.length(&2, U32, List.append(&2, U32, List.take(&2, U32, dp, ll), inner)),
    Nat.add(List.length(&2, U32, List.take(&2, U32, dp, ll)), List.length(&2, U32, inner)), Nat.add(ll, Nat.add(cc,
      tt)),
    R.len_append(List.take(&2, U32, dp, ll), inner),
    Equal.trans(Nat, Nat.add(List.length(&2, U32, List.take(&2, U32, dp, ll)), List.length(&2, U32, inner)),
      Nat.add(ll, List.length(&2, U32, inner)), Nat.add(ll, Nat.add(cc, tt)),
      Equal.cong(Nat, Nat, nn => Nat.add(nn, List.length(&2, U32, inner)), List.length(&2, U32, List.take(&2, U32,
        dp, ll)),
        ll, R.len_take(dp, ll, R.le_add_r(ll, Nat.add(cc, tt), ln, hd))),
      Equal.cong(Nat, Nat, nn => Nat.add(ll, nn), List.length(&2, U32, inner), Nat.add(cc, tt), e_in)))

# left of the pasted span, a row reads the destination
def blit.row_left(
  +dp: List<&2, U32>,
  +sp: List<&2, U32>,
  +ll: Nat,
  +cc: Nat,
  +tt: Nat,
  +ii: Nat,
  hi: {Nat.is_lt(ii, ll) == True{} : Bool},
  hl: {Nat.is_le(ll, List.length(&2, U32, dp)) == True{} : Bool}
) -> {List.get(&2, U32, Img.blit.row(dp, sp, ll, cc, tt), ii) == List.get(&2, U32, dp, ii) : Maybe<&2, U32>}:
  R.get_append_take(dp, ll, ii, List.append(&2, U32, List.take(&2, U32, sp, cc),
    List.take(&2, U32, List.drop(&2, U32, dp, Nat.add(ll, cc)), tt)), hi, hl)

# in the pasted span, a row reads the source
def blit.row_mid(
  +dp: List<&2, U32>,
  +sp: List<&2, U32>,
  +ll: Nat,
  +cc: Nat,
  +tt: Nat,
  +kk: Nat,
  hk: {Nat.is_lt(kk, cc) == True{} : Bool},
  hl: {Nat.is_le(ll, List.length(&2, U32, dp)) == True{} : Bool},
  hc: {Nat.is_le(cc, List.length(&2, U32, sp)) == True{} : Bool}
) -> {List.get(&2, U32, Img.blit.row(dp, sp, ll, cc, tt), Nat.add(ll, kk)) == List.get(&2, U32, sp, kk) :
  Maybe<&2, U32>}:
  +r2 = List.take(&2, U32, List.drop(&2, U32, dp, Nat.add(ll, cc)), tt)
  Equal.trans(Maybe<&2, U32>, List.get(&2, U32, Img.blit.row(dp, sp, ll, cc, tt), Nat.add(ll, kk)),
    List.get(&2, U32, List.append(&2, U32, List.take(&2, U32, sp, cc), r2), kk), List.get(&2, U32, sp, kk),
    R.get_append_skip(dp, ll, kk, List.append(&2, U32, List.take(&2, U32, sp, cc), r2), hl),
    R.get_append_take(sp, cc, kk, r2, hk, hc))

# right of the pasted span, a row reads the destination
def blit.row_right(
  +dp: List<&2, U32>,
  +sp: List<&2, U32>,
  +ll: Nat,
  +cc: Nat,
  +tt: Nat,
  +kk: Nat,
  hk: {Nat.is_lt(kk, tt) == True{} : Bool},
  hl: {Nat.is_le(ll, List.length(&2, U32, dp)) == True{} : Bool},
  hc: {Nat.is_le(cc, List.length(&2, U32, sp)) == True{} : Bool}
) -> {List.get(&2, U32, Img.blit.row(dp, sp, ll, cc, tt), Nat.add(ll, Nat.add(cc, kk))) ==
  List.get(&2, U32, dp, Nat.add(Nat.add(ll, cc), kk)) : Maybe<&2, U32>}:
  +dr = List.drop(&2, U32, dp, Nat.add(ll, cc))
  +r2 = List.take(&2, U32, dr, tt)
  Equal.trans(Maybe<&2, U32>, List.get(&2, U32, Img.blit.row(dp, sp, ll, cc, tt), Nat.add(ll, Nat.add(cc, kk))),
    List.get(&2, U32, List.append(&2, U32, List.take(&2, U32, sp, cc), r2), Nat.add(cc, kk)),
    List.get(&2, U32, dp, Nat.add(Nat.add(ll, cc), kk)),
    R.get_append_skip(dp, ll, Nat.add(cc, kk), List.append(&2, U32, List.take(&2, U32, sp, cc), r2), hl),
    Equal.trans(Maybe<&2, U32>, List.get(&2, U32, List.append(&2, U32, List.take(&2, U32, sp, cc), r2), Nat.add(cc,
      kk)),
      List.get(&2, U32, r2, kk), List.get(&2, U32, dp, Nat.add(Nat.add(ll, cc), kk)),
      R.get_append_skip(sp, cc, kk, r2, hc),
      Equal.trans(Maybe<&2, U32>, List.get(&2, U32, r2, kk), List.get(&2, U32, dr, kk),
        List.get(&2, U32, dp, Nat.add(Nat.add(ll, cc), kk)), R.get_take(dr, tt, kk, hk),
        R.get_drop(dp, Nat.add(ll, cc), kk))))

# the source rows hold the first pasted span: c <= length
def blit.src_head(
  +pp: Nat,
  +sp: List<&2, U32>,
  +sw: Nat,
  +cc: Nat,
  hs: {Nat.is_le(Nat.add(Nat.mul(1n+pp, sw), cc), Nat.add(List.length(&2, U32, sp), sw)) == True{} : Bool}
) -> {Nat.is_le(cc, List.length(&2, U32, sp)) == True{} : Bool}:
  +ln = List.length(&2, U32, sp)
  +ms = Nat.mul(pp, sw)
  R.le_add_l(ms, cc, ln, R.le_cancel(sw, Nat.add(ms, cc), ln, R.le_rw_r(Nat.add(sw, Nat.add(ms, cc)), Nat.add(ln, sw),
    Nat.add(sw, ln), R.add_comm(ln, sw), R.le_rw_l(Nat.add(Nat.add(sw, ms), cc), Nat.add(sw, Nat.add(ms, cc)),
      Nat.add(ln, sw), R.add_assoc(sw, ms, cc), hs))))

# the source bound holds again one row on
def blit.src_next(
  +pp: Nat,
  +sp: List<&2, U32>,
  +sw: Nat,
  +cc: Nat,
  hs: {Nat.is_le(Nat.add(Nat.mul(1n+pp, sw), cc), Nat.add(List.length(&2, U32, sp), sw)) == True{} : Bool}
) -> {Nat.is_le(Nat.add(Nat.mul(pp, sw), cc), Nat.add(List.length(&2, U32, List.drop(&2, U32, sp, sw)), sw)) == True{} :
  Bool}:
  +ms = Nat.mul(pp, sw)
  R.drop_le(sp, sw, Nat.add(ms, cc), sw, R.le_rw_l(Nat.add(Nat.add(sw, ms), cc), Nat.add(sw, Nat.add(ms, cc)),
    Nat.add(List.length(&2, U32, sp), sw), R.add_assoc(sw, ms, cc), hs))

# n pasted rows of dw samples each, when the lists hold them, are n * dw samples
def blit.rows_len(
  nn: Nat,
  +dp: List<&2, U32>,
  +sp: List<&2, U32>,
  +ll: Nat,
  +cc: Nat,
  +tt: Nat,
  +dw: Nat,
  +sw: Nat,
  +e_row: {Nat.add(ll, Nat.add(cc, tt)) == dw : Nat},
  +hd: {Nat.is_le(Nat.mul(nn, dw), List.length(&2, U32, dp)) == True{} : Bool},
  +hs: {Nat.is_le(Nat.add(Nat.mul(nn, sw), cc), Nat.add(List.length(&2, U32, sp), sw)) == True{} : Bool}
) -> {List.length(&2, U32, Img.blit.rows(nn, dp, sp, ll, cc, tt, dw, sw)) == Nat.mul(nn, dw) : Nat}:
  match nn:
    case 0n:
      {==}
    case 1n+(+pp):
      +row = Img.blit.row(dp, sp, ll, cc, tt)
      +rest = Img.blit.rows(pp, List.drop(&2, U32, dp, dw), List.drop(&2, U32, sp, sw), ll, cc, tt, dw, sw)
      +hrow = {R.le_rw_l(dw, Nat.add(ll, Nat.add(cc, tt)), List.length(&2, U32, dp),
        Equal.sym(Nat, Nat.add(ll, Nat.add(cc, tt)), dw, e_row),
        R.le_add_r(dw, Nat.mul(pp, dw), List.length(&2, U32, dp), hd)) :
        {Nat.is_le(Nat.add(ll, Nat.add(cc, tt)), List.length(&2, U32, dp)) == True{} : Bool}}
      Equal.trans(Nat, List.length(&2, U32, List.append(&2, U32, row, rest)),
        Nat.add(List.length(&2, U32, row), List.length(&2, U32, rest)), Nat.add(dw, Nat.mul(pp, dw)),
        R.len_append(row, rest),
        Equal.trans(Nat, Nat.add(List.length(&2, U32, row), List.length(&2, U32, rest)),
          Nat.add(dw, List.length(&2, U32, rest)), Nat.add(dw, Nat.mul(pp, dw)),
          Equal.cong(Nat, Nat, nn => Nat.add(nn, List.length(&2, U32, rest)), List.length(&2, U32, row), dw,
            Equal.trans(Nat, List.length(&2, U32, row), Nat.add(ll, Nat.add(cc, tt)), dw,
              blit.row_len(dp, sp, ll, cc, tt, hrow, blit.src_head(pp, sp, sw, cc, hs)), e_row)),
          Equal.cong(Nat, Nat, nn => Nat.add(dw, nn), List.length(&2, U32, rest), Nat.mul(pp, dw),
            blit.rows_len(pp, List.drop(&2, U32, dp, dw), List.drop(&2, U32, sp, sw), ll, cc, tt, dw, sw, e_row,
              R.drop_le0(dp, dw, Nat.mul(pp, dw), hd), blit.src_next(pp, sp, sw, cc, hs)))))

# sample (i, j) of the pasted rows is sample i of row j
def blit.rows_get(
  nn: Nat,
  +dp: List<&2, U32>,
  +sp: List<&2, U32>,
  +ll: Nat,
  +cc: Nat,
  +tt: Nat,
  +dw: Nat,
  +sw: Nat,
  +ii: Nat,
  jj: Nat,
  +e_row: {Nat.add(ll, Nat.add(cc, tt)) == dw : Nat},
  +hi: {Nat.is_lt(ii, dw) == True{} : Bool},
  hj: {Nat.is_lt(jj, nn) == True{} : Bool},
  +hd: {Nat.is_le(Nat.mul(nn, dw), List.length(&2, U32, dp)) == True{} : Bool},
  +hs: {Nat.is_le(Nat.add(Nat.mul(nn, sw), cc), Nat.add(List.length(&2, U32, sp), sw)) == True{} : Bool}
) -> {List.get(&2, U32, Img.blit.rows(nn, dp, sp, ll, cc, tt, dw, sw), Nat.add(Nat.mul(jj, dw), ii)) ==
  List.get(&2, U32, Img.blit.row(List.drop(&2, U32, dp, Nat.mul(jj, dw)), List.drop(&2, U32, sp, Nat.mul(jj, sw)),
    ll, cc,
    tt), ii) : Maybe<&2, U32>}:
  match nn jj:
    case 0n _jj:
      Empty.absurd({List.get(&2, U32, Img.blit.rows(0n, dp, sp, ll, cc, tt, dw, sw), Nat.add(Nat.mul(_jj, dw), ii)) ==
        List.get(&2, U32, Img.blit.row(List.drop(&2, U32, dp, Nat.mul(_jj, dw)), List.drop(&2, U32, sp, Nat.mul(_jj,
          sw)),
          ll, cc, tt), ii) : Maybe<&2, U32>},
        U32L.false_true(Equal.trans(Bool, False{}, Nat.is_lt(_jj, 0n), True{}, R.lt_zero_false(_jj), hj)))
    case 1n+(+pp) 0n:
      +row = Img.blit.row(dp, sp, ll, cc, tt)
      +rest = Img.blit.rows(pp, List.drop(&2, U32, dp, dw), List.drop(&2, U32, sp, sw), ll, cc, tt, dw, sw)
      +hrow = {R.le_rw_l(dw, Nat.add(ll, Nat.add(cc, tt)), List.length(&2, U32, dp),
        Equal.sym(Nat, Nat.add(ll, Nat.add(cc, tt)), dw, e_row),
        R.le_add_r(dw, Nat.mul(pp, dw), List.length(&2, U32, dp), hd)) :
        {Nat.is_le(Nat.add(ll, Nat.add(cc, tt)), List.length(&2, U32, dp)) == True{} : Bool}}
      +el = {Equal.trans(Nat, List.length(&2, U32, row), Nat.add(ll, Nat.add(cc, tt)), dw,
        blit.row_len(dp, sp, ll, cc, tt, hrow, blit.src_head(pp, sp, sw, cc, hs)), e_row) :
        {List.length(&2, U32, row) == dw : Nat}}
      Equal.trans(Maybe<&2, U32>, List.get(&2, U32, List.append(&2, U32, row, rest), ii), List.get(&2, U32, row, ii),
        List.get(&2, U32, Img.blit.row(List.drop(&2, U32, dp, 0n), List.drop(&2, U32, sp, 0n), ll, cc, tt), ii),
        R.get_append_lt(row, ii, rest, R.lt_rw_r(ii, dw, List.length(&2, U32, row), Equal.sym(Nat, List.length(&2,
          U32, row),
          dw, el), hi)),
        Equal.trans(Maybe<&2, U32>, List.get(&2, U32, row, ii),
          List.get(&2, U32, Img.blit.row(List.drop(&2, U32, dp, 0n), sp, ll, cc, tt), ii),
          List.get(&2, U32, Img.blit.row(List.drop(&2, U32, dp, 0n), List.drop(&2, U32, sp, 0n), ll, cc, tt), ii),
          Equal.cong(List<&2, U32>, Maybe<&2, U32>, xs => List.get(&2, U32, Img.blit.row(xs, sp, ll, cc, tt), ii), dp,
            List.drop(&2, U32, dp, 0n), Equal.sym(List<&2, U32>, List.drop(&2, U32, dp, 0n), dp, R.drop_zero(dp))),
          Equal.cong(List<&2, U32>, Maybe<&2, U32>,
            xs => List.get(&2, U32, Img.blit.row(List.drop(&2, U32, dp, 0n), xs, ll, cc, tt), ii), sp,
            List.drop(&2, U32, sp, 0n), Equal.sym(List<&2, U32>, List.drop(&2, U32, sp, 0n), sp, R.drop_zero(sp)))))
    case 1n+(+pp) 1n+(+qq):
      +row = Img.blit.row(dp, sp, ll, cc, tt)
      +d1 = List.drop(&2, U32, dp, dw)
      +s1 = List.drop(&2, U32, sp, sw)
      +rest = Img.blit.rows(pp, d1, s1, ll, cc, tt, dw, sw)
      +mq = Nat.mul(qq, dw)
      +ms = Nat.mul(qq, sw)
      +hrow = {R.le_rw_l(dw, Nat.add(ll, Nat.add(cc, tt)), List.length(&2, U32, dp),
        Equal.sym(Nat, Nat.add(ll, Nat.add(cc, tt)), dw, e_row),
        R.le_add_r(dw, Nat.mul(pp, dw), List.length(&2, U32, dp), hd)) :
        {Nat.is_le(Nat.add(ll, Nat.add(cc, tt)), List.length(&2, U32, dp)) == True{} : Bool}}
      +el = {Equal.trans(Nat, List.length(&2, U32, row), Nat.add(ll, Nat.add(cc, tt)), dw,
        blit.row_len(dp, sp, ll, cc, tt, hrow, blit.src_head(pp, sp, sw, cc, hs)), e_row) :
        {List.length(&2, U32, row) == dw : Nat}}
      +both = List.append(&2, U32, row, rest)
      Equal.trans(Maybe<&2, U32>, List.get(&2, U32, both, Nat.add(Nat.add(dw, mq), ii)),
        List.get(&2, U32, both, Nat.add(List.length(&2, U32, row), Nat.add(mq, ii))),
        List.get(&2, U32, Img.blit.row(List.drop(&2, U32, dp, Nat.add(dw, mq)), List.drop(&2, U32, sp, Nat.add(sw,
          ms)), ll,
          cc, tt), ii),
        Equal.cong(Nat, Maybe<&2, U32>, kk => List.get(&2, U32, both, kk), Nat.add(Nat.add(dw, mq), ii),
          Nat.add(List.length(&2, U32, row), Nat.add(mq, ii)),
          Equal.trans(Nat, Nat.add(Nat.add(dw, mq), ii), Nat.add(dw, Nat.add(mq, ii)),
            Nat.add(List.length(&2, U32, row), Nat.add(mq, ii)), R.add_assoc(dw, mq, ii),
            Equal.cong(Nat, Nat, nn => Nat.add(nn, Nat.add(mq, ii)), dw, List.length(&2, U32, row),
              Equal.sym(Nat, List.length(&2, U32, row), dw, el)))),
        Equal.trans(Maybe<&2, U32>, List.get(&2, U32, both, Nat.add(List.length(&2, U32, row), Nat.add(mq, ii))),
          List.get(&2, U32, rest, Nat.add(mq, ii)),
          List.get(&2, U32, Img.blit.row(List.drop(&2, U32, dp, Nat.add(dw, mq)), List.drop(&2, U32, sp, Nat.add(sw,
            ms)),
            ll, cc, tt), ii),
          R.get_append_len(row, Nat.add(mq, ii), rest),
          Equal.trans(Maybe<&2, U32>, List.get(&2, U32, rest, Nat.add(mq, ii)),
            List.get(&2, U32, Img.blit.row(List.drop(&2, U32, d1, mq), List.drop(&2, U32, s1, ms), ll, cc, tt), ii),
            List.get(&2, U32, Img.blit.row(List.drop(&2, U32, dp, Nat.add(dw, mq)),
              List.drop(&2, U32, sp, Nat.add(sw, ms)), ll, cc, tt), ii),
            blit.rows_get(pp, d1, s1, ll, cc, tt, dw, sw, ii, qq, e_row, hi, hj, R.drop_le0(dp, dw, Nat.mul(pp, dw),
              hd),
              blit.src_next(pp, sp, sw, cc, hs)),
            Equal.trans(Maybe<&2, U32>,
              List.get(&2, U32, Img.blit.row(List.drop(&2, U32, d1, mq), List.drop(&2, U32, s1, ms), ll, cc, tt), ii),
              List.get(&2, U32, Img.blit.row(List.drop(&2, U32, dp, Nat.add(dw, mq)), List.drop(&2, U32, s1, ms),
                ll, cc,
                tt), ii),
              List.get(&2, U32, Img.blit.row(List.drop(&2, U32, dp, Nat.add(dw, mq)),
                List.drop(&2, U32, sp, Nat.add(sw, ms)), ll, cc, tt), ii),
              Equal.cong(List<&2, U32>, Maybe<&2, U32>,
                xs => List.get(&2, U32, Img.blit.row(xs, List.drop(&2, U32, s1, ms), ll, cc, tt), ii),
                List.drop(&2, U32, d1, mq), List.drop(&2, U32, dp, Nat.add(dw, mq)), R.drop_drop(dp, dw, mq)),
              Equal.cong(List<&2, U32>, Maybe<&2, U32>,
                xs => List.get(&2, U32, Img.blit.row(List.drop(&2, U32, dp, Nat.add(dw, mq)), xs, ll, cc, tt), ii),
                List.drop(&2, U32, s1, ms), List.drop(&2, U32, sp, Nat.add(sw, ms)), R.drop_drop(sp, sw, ms))))))

def Laws.blit_size(dst, src, _xx, _yy):
  match dst src:
    case Img.Raster{_dw, _dh, _dp} Img.Raster{_sw, _sh, _sp}:
      {==}

# the samples blit.join builds: the rows above, the pasted rows, the rows below
def bj.J(
  +dp: List<&2, U32>,
  +sp: List<&2, U32>,
  +top: Nat,
  +span: Nat,
  +nn: Nat,
  +ll: Nat,
  +cc: Nat,
  +tt: Nat,
  +dw: Nat,
  +sw: Nat
) -> List<&2, U32>:
  List.append(&2, U32, List.take(&2, U32, dp, top), List.append(&2, U32,
    Img.blit.rows(nn, List.drop(&2, U32, dp, top), sp, ll, cc, tt, dw, sw), List.drop(&2, U32, dp, span)))

# the rows above the paste end inside dst
def bj.htop(
  +dp: List<&2, U32>,
  +top: Nat,
  +span: Nat,
  +nn: Nat,
  +dw: Nat,
  e_span: {span == Nat.add(top, Nat.mul(nn, dw)) : Nat},
  h_len: {Nat.is_le(span, List.length(&2, U32, dp)) == True{} : Bool}
) -> {Nat.is_le(top, List.length(&2, U32, dp)) == True{} : Bool}:
  R.le_add_r(top, Nat.mul(nn, dw), List.length(&2, U32, dp), R.le_rw_l(span, Nat.add(top, Nat.mul(nn, dw)),
    List.length(&2, U32, dp), e_span, h_len))

# the pasted rows read inside dst
def bj.hd(
  +dp: List<&2, U32>,
  +top: Nat,
  +span: Nat,
  +nn: Nat,
  +dw: Nat,
  e_span: {span == Nat.add(top, Nat.mul(nn, dw)) : Nat},
  h_len: {Nat.is_le(span, List.length(&2, U32, dp)) == True{} : Bool}
) -> {Nat.is_le(Nat.mul(nn, dw), List.length(&2, U32, List.drop(&2, U32, dp, top))) == True{} : Bool}:
  R.drop_le0(dp, top, Nat.mul(nn, dw), R.le_rw_l(span, Nat.add(top, Nat.mul(nn, dw)), List.length(&2, U32, dp), e_span,
    h_len))

# the pasted rows are n * dw samples
def bj.rows_len(
  +dp: List<&2, U32>,
  +sp: List<&2, U32>,
  +top: Nat,
  +span: Nat,
  +nn: Nat,
  +ll: Nat,
  +cc: Nat,
  +tt: Nat,
  +dw: Nat,
  +sw: Nat,
  +e_row: {Nat.add(ll, Nat.add(cc, tt)) == dw : Nat},
  +e_span: {span == Nat.add(top, Nat.mul(nn, dw)) : Nat},
  +h_len: {Nat.is_le(span, List.length(&2, U32, dp)) == True{} : Bool},
  +hs: {Nat.is_le(Nat.add(Nat.mul(nn, sw), cc), Nat.add(List.length(&2, U32, sp), sw)) == True{} : Bool}
) -> {List.length(&2, U32, Img.blit.rows(nn, List.drop(&2, U32, dp, top), sp, ll, cc, tt, dw, sw)) == Nat.mul(nn, dw) :
  Nat}:
  blit.rows_len(nn, List.drop(&2, U32, dp, top), sp, ll, cc, tt, dw, sw, e_row, bj.hd(dp, top, span, nn, dw, e_span,
    h_len),
    hs)

# above the paste, blit reads dst
def bj.top(
  +dp: List<&2, U32>,
  +sp: List<&2, U32>,
  +top: Nat,
  +span: Nat,
  +nn: Nat,
  +ll: Nat,
  +cc: Nat,
  +tt: Nat,
  +dw: Nat,
  +sw: Nat,
  +kk: Nat,
  hk: {Nat.is_lt(kk, top) == True{} : Bool},
  e_span: {span == Nat.add(top, Nat.mul(nn, dw)) : Nat},
  h_len: {Nat.is_le(span, List.length(&2, U32, dp)) == True{} : Bool}
) -> {List.get(&2, U32, bj.J(dp, sp, top, span, nn, ll, cc, tt, dw, sw), kk) == List.get(&2, U32, dp, kk) :
  Maybe<&2, U32>}:
  R.get_append_take(dp, top, kk, List.append(&2, U32,
    Img.blit.rows(nn, List.drop(&2, U32, dp, top), sp, ll, cc, tt, dw, sw), List.drop(&2, U32, dp, span)), hk,
    bj.htop(dp, top, span, nn, dw, e_span, h_len))

# in the band of pasted rows, blit reads row j of the paste
def bj.band(
  +dp: List<&2, U32>,
  +sp: List<&2, U32>,
  +top: Nat,
  +span: Nat,
  +nn: Nat,
  +ll: Nat,
  +cc: Nat,
  +tt: Nat,
  +dw: Nat,
  +sw: Nat,
  +ii: Nat,
  +jj: Nat,
  +hi: {Nat.is_lt(ii, dw) == True{} : Bool},
  +hj: {Nat.is_lt(jj, nn) == True{} : Bool},
  +e_row: {Nat.add(ll, Nat.add(cc, tt)) == dw : Nat},
  +e_span: {span == Nat.add(top, Nat.mul(nn, dw)) : Nat},
  +h_len: {Nat.is_le(span, List.length(&2, U32, dp)) == True{} : Bool},
  +hs: {Nat.is_le(Nat.add(Nat.mul(nn, sw), cc), Nat.add(List.length(&2, U32, sp), sw)) == True{} : Bool}
) -> {List.get(&2, U32, bj.J(dp, sp, top, span, nn, ll, cc, tt, dw, sw), Nat.add(top, Nat.add(Nat.mul(jj, dw), ii))) ==
  List.get(&2, U32, Img.blit.row(List.drop(&2, U32, dp, Nat.add(top, Nat.mul(jj, dw))),
    List.drop(&2, U32, sp, Nat.mul(jj, sw)), ll, cc, tt), ii) : Maybe<&2, U32>}:
  +dt = List.drop(&2, U32, dp, top)
  +rows = Img.blit.rows(nn, dt, sp, ll, cc, tt, dw, sw)
  +kk = Nat.add(Nat.mul(jj, dw), ii)
  +srow = List.drop(&2, U32, sp, Nat.mul(jj, sw))
  +e_rl = {bj.rows_len(dp, sp, top, span, nn, ll, cc, tt, dw, sw, e_row, e_span, h_len, hs) :
    {List.length(&2, U32, rows) == Nat.mul(nn, dw) : Nat}}
  +hk = {R.lt_rw_r(kk, Nat.mul(dw, nn), List.length(&2, U32, rows), Equal.trans(Nat, Nat.mul(dw, nn), Nat.mul(nn, dw),
    List.length(&2, U32, rows), R.mul_comm(dw, nn), Equal.sym(Nat, List.length(&2, U32, rows), Nat.mul(nn, dw), e_rl)),
    R.index_lt(ii, jj, dw, nn, hi, hj)) : {Nat.is_lt(kk, List.length(&2, U32, rows)) == True{} : Bool}}
  Equal.trans(Maybe<&2, U32>, List.get(&2, U32, bj.J(dp, sp, top, span, nn, ll, cc, tt, dw, sw), Nat.add(top, kk)),
    List.get(&2, U32, List.append(&2, U32, rows, List.drop(&2, U32, dp, span)), kk),
    List.get(&2, U32, Img.blit.row(List.drop(&2, U32, dp, Nat.add(top, Nat.mul(jj, dw))), srow, ll, cc, tt), ii),
    R.get_append_skip(dp, top, kk, List.append(&2, U32, rows, List.drop(&2, U32, dp, span)),
      bj.htop(dp, top, span, nn, dw, e_span, h_len)),
    Equal.trans(Maybe<&2, U32>, List.get(&2, U32, List.append(&2, U32, rows, List.drop(&2, U32, dp, span)), kk),
      List.get(&2, U32, rows, kk),
      List.get(&2, U32, Img.blit.row(List.drop(&2, U32, dp, Nat.add(top, Nat.mul(jj, dw))), srow, ll, cc, tt), ii),
      R.get_append_lt(rows, kk, List.drop(&2, U32, dp, span), hk),
      Equal.trans(Maybe<&2, U32>, List.get(&2, U32, rows, kk),
        List.get(&2, U32, Img.blit.row(List.drop(&2, U32, dt, Nat.mul(jj, dw)), srow, ll, cc, tt), ii),
        List.get(&2, U32, Img.blit.row(List.drop(&2, U32, dp, Nat.add(top, Nat.mul(jj, dw))), srow, ll, cc, tt), ii),
        blit.rows_get(nn, dt, sp, ll, cc, tt, dw, sw, ii, jj, e_row, hi, hj, bj.hd(dp, top, span, nn, dw, e_span,
          h_len),
          hs),
        Equal.cong(List<&2, U32>, Maybe<&2, U32>, xs => List.get(&2, U32, Img.blit.row(xs, srow, ll, cc, tt), ii),
          List.drop(&2, U32, dt, Nat.mul(jj, dw)), List.drop(&2, U32, dp, Nat.add(top, Nat.mul(jj, dw))),
          R.drop_drop(dp, top, Nat.mul(jj, dw))))))

# below the paste, blit reads dst
def bj.bottom(
  +dp: List<&2, U32>,
  +sp: List<&2, U32>,
  +top: Nat,
  +span: Nat,
  +nn: Nat,
  +ll: Nat,
  +cc: Nat,
  +tt: Nat,
  +dw: Nat,
  +sw: Nat,
  +mm: Nat,
  +e_row: {Nat.add(ll, Nat.add(cc, tt)) == dw : Nat},
  +e_span: {span == Nat.add(top, Nat.mul(nn, dw)) : Nat},
  +h_len: {Nat.is_le(span, List.length(&2, U32, dp)) == True{} : Bool},
  +hs: {Nat.is_le(Nat.add(Nat.mul(nn, sw), cc), Nat.add(List.length(&2, U32, sp), sw)) == True{} : Bool}
) -> {List.get(&2, U32, bj.J(dp, sp, top, span, nn, ll, cc, tt, dw, sw), Nat.add(span, mm)) ==
  List.get(&2, U32, dp, Nat.add(span, mm)) : Maybe<&2, U32>}:
  +rows = Img.blit.rows(nn, List.drop(&2, U32, dp, top), sp, ll, cc, tt, dw, sw)
  +low = List.drop(&2, U32, dp, span)
  +e_rl = {bj.rows_len(dp, sp, top, span, nn, ll, cc, tt, dw, sw, e_row, e_span, h_len, hs) :
    {List.length(&2, U32, rows) == Nat.mul(nn, dw) : Nat}}
  +ek = {Equal.trans(Nat, Nat.add(span, mm), Nat.add(Nat.add(top, Nat.mul(nn, dw)), mm),
    Nat.add(top, Nat.add(List.length(&2, U32, rows), mm)),
    Equal.cong(Nat, Nat, xx => Nat.add(xx, mm), span, Nat.add(top, Nat.mul(nn, dw)), e_span),
    Equal.trans(Nat, Nat.add(Nat.add(top, Nat.mul(nn, dw)), mm), Nat.add(top, Nat.add(Nat.mul(nn, dw), mm)),
      Nat.add(top, Nat.add(List.length(&2, U32, rows), mm)), R.add_assoc(top, Nat.mul(nn, dw), mm),
      Equal.cong(Nat, Nat, xx => Nat.add(top, Nat.add(xx, mm)), Nat.mul(nn, dw), List.length(&2, U32, rows),
        Equal.sym(Nat, List.length(&2, U32, rows), Nat.mul(nn, dw), e_rl)))) :
    {Nat.add(span, mm) == Nat.add(top, Nat.add(List.length(&2, U32, rows), mm)) : Nat}}
  Equal.trans(Maybe<&2, U32>, List.get(&2, U32, bj.J(dp, sp, top, span, nn, ll, cc, tt, dw, sw), Nat.add(span, mm)),
    List.get(&2, U32, bj.J(dp, sp, top, span, nn, ll, cc, tt, dw, sw), Nat.add(top, Nat.add(List.length(&2, U32,
      rows), mm))),
    List.get(&2, U32, dp, Nat.add(span, mm)),
    Equal.cong(Nat, Maybe<&2, U32>, kk => List.get(&2, U32, bj.J(dp, sp, top, span, nn, ll, cc, tt, dw, sw), kk),
      Nat.add(span, mm), Nat.add(top, Nat.add(List.length(&2, U32, rows), mm)), ek),
    Equal.trans(Maybe<&2, U32>,
      List.get(&2, U32, bj.J(dp, sp, top, span, nn, ll, cc, tt, dw, sw), Nat.add(top, Nat.add(List.length(&2, U32,
        rows),
        mm))),
      List.get(&2, U32, List.append(&2, U32, rows, low), Nat.add(List.length(&2, U32, rows), mm)),
      List.get(&2, U32, dp, Nat.add(span, mm)),
      R.get_append_skip(dp, top, Nat.add(List.length(&2, U32, rows), mm), List.append(&2, U32, rows, low),
        bj.htop(dp, top, span, nn, dw, e_span, h_len)),
      Equal.trans(Maybe<&2, U32>, List.get(&2, U32, List.append(&2, U32, rows, low), Nat.add(List.length(&2, U32,
        rows), mm)),
        List.get(&2, U32, low, mm), List.get(&2, U32, dp, Nat.add(span, mm)),
        R.get_append_len(rows, mm, low), R.get_drop(dp, span, mm))))

# blit.join's samples are as many as dst's
def bj.len(
  +dp: List<&2, U32>,
  +sp: List<&2, U32>,
  +top: Nat,
  +span: Nat,
  +nn: Nat,
  +ll: Nat,
  +cc: Nat,
  +tt: Nat,
  +dw: Nat,
  +sw: Nat,
  +e_row: {Nat.add(ll, Nat.add(cc, tt)) == dw : Nat},
  +e_span: {span == Nat.add(top, Nat.mul(nn, dw)) : Nat},
  +h_len: {Nat.is_le(span, List.length(&2, U32, dp)) == True{} : Bool},
  +hs: {Nat.is_le(Nat.add(Nat.mul(nn, sw), cc), Nat.add(List.length(&2, U32, sp), sw)) == True{} : Bool}
) -> {List.length(&2, U32, bj.J(dp, sp, top, span, nn, ll, cc, tt, dw, sw)) == List.length(&2, U32, dp) : Nat}:
  +hd = List.take(&2, U32, dp, top)
  +rows = Img.blit.rows(nn, List.drop(&2, U32, dp, top), sp, ll, cc, tt, dw, sw)
  +low = List.drop(&2, U32, dp, span)
  +nl = List.length(&2, U32, low)
  +e_rl = {bj.rows_len(dp, sp, top, span, nn, ll, cc, tt, dw, sw, e_row, e_span, h_len, hs) :
    {List.length(&2, U32, rows) == Nat.mul(nn, dw) : Nat}}
  Equal.trans(Nat, List.length(&2, U32, bj.J(dp, sp, top, span, nn, ll, cc, tt, dw, sw)),
    Nat.add(List.length(&2, U32, hd), List.length(&2, U32, List.append(&2, U32, rows, low))), List.length(&2, U32, dp),
    R.len_append(hd, List.append(&2, U32, rows, low)),
    Equal.trans(Nat, Nat.add(List.length(&2, U32, hd), List.length(&2, U32, List.append(&2, U32, rows, low))),
      Nat.add(top, Nat.add(Nat.mul(nn, dw), nl)), List.length(&2, U32, dp),
      Equal.trans(Nat, Nat.add(List.length(&2, U32, hd), List.length(&2, U32, List.append(&2, U32, rows, low))),
        Nat.add(top, List.length(&2, U32, List.append(&2, U32, rows, low))), Nat.add(top, Nat.add(Nat.mul(nn, dw), nl)),
        Equal.cong(Nat, Nat, xx => Nat.add(xx, List.length(&2, U32, List.append(&2, U32, rows, low))),
          List.length(&2, U32, hd), top, R.len_take(dp, top, bj.htop(dp, top, span, nn, dw, e_span, h_len))),
        Equal.cong(Nat, Nat, xx => Nat.add(top, xx), List.length(&2, U32, List.append(&2, U32, rows, low)),
          Nat.add(Nat.mul(nn, dw), nl), Equal.trans(Nat, List.length(&2, U32, List.append(&2, U32, rows, low)),
            Nat.add(List.length(&2, U32, rows), nl), Nat.add(Nat.mul(nn, dw), nl), R.len_append(rows, low),
            Equal.cong(Nat, Nat, xx => Nat.add(xx, nl), List.length(&2, U32, rows), Nat.mul(nn, dw), e_rl)))),
      Equal.trans(Nat, Nat.add(top, Nat.add(Nat.mul(nn, dw), nl)), Nat.add(span, nl), List.length(&2, U32, dp),
        Equal.trans(Nat, Nat.add(top, Nat.add(Nat.mul(nn, dw), nl)), Nat.add(Nat.add(top, Nat.mul(nn, dw)), nl),
          Nat.add(span, nl), Equal.sym(Nat, Nat.add(Nat.add(top, Nat.mul(nn, dw)), nl),
            Nat.add(top, Nat.add(Nat.mul(nn, dw), nl)), R.add_assoc(top, Nat.mul(nn, dw), nl)),
          Equal.cong(Nat, Nat, xx => Nat.add(xx, nl), Nat.add(top, Nat.mul(nn, dw)), span,
            Equal.sym(Nat, span, Nat.add(top, Nat.mul(nn, dw)), e_span))),
        R.len_drop_add(dp, span, h_len))))
# blit.join's numbers, as the code computes them: the columns left of the
# paste, the room right of them, the pasted columns, the columns after them,
# the pasted rows, and where the pasted rows start and end
def bl.Lc(+ox: U32, +dw: U32) -> Nat:
  U32.to_nat(Img.u.min(ox, dw))

# the room right of the left columns
def bl.Rm(+ox: U32, +dw: U32) -> Nat:
  U32.to_nat((dw - Img.u.min(ox, dw) : U32))

# the pasted columns
def bl.Cc(+sw: U32, +ox: U32, +dw: U32) -> Nat:
  U32.to_nat(Img.u.min(sw, (dw - Img.u.min(ox, dw) : U32)))

# the columns after the pasted ones
def bl.Tc(+sw: U32, +ox: U32, +dw: U32) -> Nat:
  U32.to_nat(((dw - Img.u.min(ox, dw) : U32) - Img.u.min(sw, (dw - Img.u.min(ox, dw) : U32)) : U32))

# the pasted rows
def bl.Rw(+sh: U32, +dh: U32, +oy: U32) -> Nat:
  U32.to_nat(Img.u.min(sh, (dh - oy : U32)))

# where the pasted rows start
def bl.top(+oy: U32, +dw: U32) -> Nat:
  U32.to_nat((oy * dw : U32))

# where the pasted rows end
def bl.span(+sh: U32, +dh: U32, +oy: U32, +dw: U32) -> Nat:
  U32.to_nat(((oy + Img.u.min(sh, (dh - oy : U32))) * dw : U32))

# the left columns are min(x, dw)
def bl.eL(+ox: U32, +dw: U32) -> {bl.Lc(ox, dw) == Nat.min(U32.to_nat(ox), U32.to_nat(dw)) : Nat}:
  ras.umin(ox, dw)

# the left columns fit in a row
def bl.hL(+ox: U32, +dw: U32) -> {Nat.is_le(bl.Lc(ox, dw), U32.to_nat(dw)) == True{} : Bool}:
  R.le_rw_l(Nat.min(U32.to_nat(ox), U32.to_nat(dw)), bl.Lc(ox, dw), U32.to_nat(dw),
    Equal.sym(Nat, bl.Lc(ox, dw), Nat.min(U32.to_nat(ox), U32.to_nat(dw)), bl.eL(ox, dw)),
    R.min_le_r(U32.to_nat(ox), U32.to_nat(dw)))

# the room is dw - left
def bl.eRm(+ox: U32, +dw: U32) -> {bl.Rm(ox, dw) == Nat.sub(U32.to_nat(dw), bl.Lc(ox, dw)) : Nat}:
  R.u32_sub_nat(dw, Img.u.min(ox, dw), bl.hL(ox, dw))

# the pasted columns are min(sw, room)
def bl.eC(+sw: U32, +ox: U32, +dw: U32) -> {bl.Cc(sw, ox, dw) == Nat.min(U32.to_nat(sw), bl.Rm(ox, dw)) : Nat}:
  ras.umin(sw, (dw - Img.u.min(ox, dw) : U32))

# the pasted columns fit in the room
def bl.hC(+sw: U32, +ox: U32, +dw: U32) -> {Nat.is_le(bl.Cc(sw, ox, dw), bl.Rm(ox, dw)) == True{} : Bool}:
  R.le_rw_l(Nat.min(U32.to_nat(sw), bl.Rm(ox, dw)), bl.Cc(sw, ox, dw), bl.Rm(ox, dw),
    Equal.sym(Nat, bl.Cc(sw, ox, dw), Nat.min(U32.to_nat(sw), bl.Rm(ox, dw)), bl.eC(sw, ox, dw)),
    R.min_le_r(U32.to_nat(sw), bl.Rm(ox, dw)))

# the pasted columns are at most sw
def bl.hCs(+sw: U32, +ox: U32, +dw: U32) -> {Nat.is_le(bl.Cc(sw, ox, dw), U32.to_nat(sw)) == True{} : Bool}:
  R.le_rw_l(Nat.min(U32.to_nat(sw), bl.Rm(ox, dw)), bl.Cc(sw, ox, dw), U32.to_nat(sw),
    Equal.sym(Nat, bl.Cc(sw, ox, dw), Nat.min(U32.to_nat(sw), bl.Rm(ox, dw)), bl.eC(sw, ox, dw)),
    R.min_le_l(U32.to_nat(sw), bl.Rm(ox, dw)))

# left, pasted and after make up a row
def bl.e_row(
  +sw: U32,
  +ox: U32,
  +dw: U32
) -> {Nat.add(bl.Lc(ox, dw), Nat.add(bl.Cc(sw, ox, dw), bl.Tc(sw, ox, dw))) ==
  U32.to_nat(dw) : Nat}:
  +lc = bl.Lc(ox, dw)
  +rm = bl.Rm(ox, dw)
  +cc = bl.Cc(sw, ox, dw)
  +tc = bl.Tc(sw, ox, dw)
  +et = {R.u32_sub_nat((dw - Img.u.min(ox, dw) : U32), Img.u.min(sw, (dw - Img.u.min(ox, dw) : U32)), bl.hC(sw, ox,
    dw)) :
    {tc == Nat.sub(rm, cc) : Nat}}
  +e_ct = {Equal.trans(Nat, Nat.add(cc, tc), Nat.add(cc, Nat.sub(rm, cc)), rm,
    Equal.cong(Nat, Nat, nn => Nat.add(cc, nn), tc, Nat.sub(rm, cc), et), R.add_sub(cc, rm, bl.hC(sw, ox, dw))) :
    {Nat.add(cc, tc) == rm : Nat}}
  Equal.trans(Nat, Nat.add(lc, Nat.add(cc, tc)), Nat.add(lc, rm), U32.to_nat(dw),
    Equal.cong(Nat, Nat, nn => Nat.add(lc, nn), Nat.add(cc, tc), rm, e_ct),
    Equal.trans(Nat, Nat.add(lc, rm), Nat.add(lc, Nat.sub(U32.to_nat(dw), lc)), U32.to_nat(dw),
      Equal.cong(Nat, Nat, nn => Nat.add(lc, nn), rm, Nat.sub(U32.to_nat(dw), lc), bl.eRm(ox, dw)),
      R.add_sub(lc, U32.to_nat(dw), bl.hL(ox, dw))))

# the pasted rows are min(sh, dh - y), when y < dh
def bl.eRw(
  +sh: U32,
  +dh: U32,
  +oy: U32,
  hy: {Nat.is_lt(U32.to_nat(oy), U32.to_nat(dh)) == True{} : Bool}
) -> {bl.Rw(sh, dh, oy) == Nat.min(U32.to_nat(sh), Nat.sub(U32.to_nat(dh), U32.to_nat(oy))) : Nat}:
  Equal.trans(Nat, bl.Rw(sh, dh, oy), Nat.min(U32.to_nat(sh), U32.to_nat((dh - oy : U32))),
    Nat.min(U32.to_nat(sh), Nat.sub(U32.to_nat(dh), U32.to_nat(oy))), ras.umin(sh, (dh - oy : U32)),
    Equal.cong(Nat, Nat, nn => Nat.min(U32.to_nat(sh), nn), U32.to_nat((dh - oy : U32)),
      Nat.sub(U32.to_nat(dh), U32.to_nat(oy)), R.u32_sub_nat(dh, oy, R.lt_le(U32.to_nat(oy), U32.to_nat(dh), hy))))

# the pasted rows are at most sh
def bl.hRs(+sh: U32, +dh: U32, +oy: U32) -> {Nat.is_le(bl.Rw(sh, dh, oy), U32.to_nat(sh)) == True{} : Bool}:
  R.le_rw_l(Nat.min(U32.to_nat(sh), U32.to_nat((dh - oy : U32))), bl.Rw(sh, dh, oy), U32.to_nat(sh),
    Equal.sym(Nat, bl.Rw(sh, dh, oy), Nat.min(U32.to_nat(sh), U32.to_nat((dh - oy : U32))), ras.umin(sh,
      (dh - oy : U32))),
    R.min_le_l(U32.to_nat(sh), U32.to_nat((dh - oy : U32))))

# the pasted rows end inside dst: y + rows <= dh
def bl.hyr(
  +sh: U32,
  +dh: U32,
  +oy: U32,
  +hy: {Nat.is_lt(U32.to_nat(oy), U32.to_nat(dh)) == True{} : Bool}
) -> {Nat.is_le(Nat.add(U32.to_nat(oy), bl.Rw(sh, dh, oy)), U32.to_nat(dh)) == True{} : Bool}:
  +yn = U32.to_nat(oy)
  +dn = U32.to_nat(dh)
  +dd = Nat.sub(dn, yn)
  R.le_rw_r(Nat.add(yn, bl.Rw(sh, dh, oy)), Nat.add(yn, dd), dn, R.add_sub(yn, dn, R.lt_le(yn, dn, hy)),
    R.le_add_mono(yn, bl.Rw(sh, dh, oy), dd, R.le_rw_l(Nat.min(U32.to_nat(sh), dd), bl.Rw(sh, dh, oy), dd,
      Equal.sym(Nat, bl.Rw(sh, dh, oy), Nat.min(U32.to_nat(sh), dd), bl.eRw(sh, dh, oy, hy)),
      R.min_le_r(U32.to_nat(sh), dd))))

# a row count at most dh times dw is at most the area
def bl.below_area(
  +an: Nat,
  +dw: U32,
  +dh: U32,
  +area: U32,
  h_area: {U32.to_nat(area) == Nat.mul(U32.to_nat(dw), U32.to_nat(dh)) : Nat},
  hh: {Nat.is_le(an, U32.to_nat(dh)) == True{} : Bool}
) -> {Nat.is_le(Nat.mul(an, U32.to_nat(dw)), U32.to_nat(area)) == True{} : Bool}:
  R.le_rw_r(Nat.mul(an, U32.to_nat(dw)), Nat.mul(U32.to_nat(dw), U32.to_nat(dh)), U32.to_nat(area),
    Equal.sym(Nat, U32.to_nat(area), Nat.mul(U32.to_nat(dw), U32.to_nat(dh)), h_area),
    R.le_rw_r(Nat.mul(an, U32.to_nat(dw)), Nat.mul(U32.to_nat(dh), U32.to_nat(dw)), Nat.mul(U32.to_nat(dw),
      U32.to_nat(dh)),
      R.mul_comm(U32.to_nat(dh), U32.to_nat(dw)), R.le_mul_mono(an, U32.to_nat(dh), U32.to_nat(dw), hh)))

# the pasted rows start at y * dw
def bl.e_top(
  +oy: U32,
  +dw: U32,
  +dh: U32,
  +area: U32,
  h_area: {U32.to_nat(area) == Nat.mul(U32.to_nat(dw), U32.to_nat(dh)) : Nat},
  hy: {Nat.is_lt(U32.to_nat(oy), U32.to_nat(dh)) == True{} : Bool}
) -> {bl.top(oy, dw) == Nat.mul(U32.to_nat(oy), U32.to_nat(dw)) : Nat}:
  R.u32_mul_below(oy, dw, area, bl.below_area(U32.to_nat(oy), dw, dh, area, h_area,
    R.lt_le(U32.to_nat(oy), U32.to_nat(dh), hy)))

# the pasted rows end at (y + rows) * dw
def bl.e_spanv(
  +sh: U32,
  +oy: U32,
  +dw: U32,
  +dh: U32,
  +area: U32,
  +h_area: {U32.to_nat(area) == Nat.mul(U32.to_nat(dw), U32.to_nat(dh)) : Nat},
  +hy: {Nat.is_lt(U32.to_nat(oy), U32.to_nat(dh)) == True{} : Bool}
) -> {bl.span(sh, dh, oy, dw) == Nat.mul(Nat.add(U32.to_nat(oy), bl.Rw(sh, dh, oy)), U32.to_nat(dw)) : Nat}:
  +rows = Img.u.min(sh, (dh - oy : U32))
  +yr = Nat.add(U32.to_nat(oy), bl.Rw(sh, dh, oy))
  +e_or = {R.u32_add_below(oy, rows, dh, bl.hyr(sh, dh, oy, hy)) : {U32.to_nat((oy + rows : U32)) == yr : Nat}}
  Equal.trans(Nat, bl.span(sh, dh, oy, dw), Nat.mul(U32.to_nat((oy + rows : U32)), U32.to_nat(dw)),
    Nat.mul(yr, U32.to_nat(dw)),
    R.u32_mul_below((oy + rows : U32), dw, area, bl.below_area(U32.to_nat((oy + rows : U32)), dw, dh, area, h_area,
      R.le_rw_l(yr, U32.to_nat((oy + rows : U32)), U32.to_nat(dh), Equal.sym(Nat, U32.to_nat((oy + rows : U32)), yr,
        e_or),
        bl.hyr(sh, dh, oy, hy)))),
    Equal.cong(Nat, Nat, nn => Nat.mul(nn, U32.to_nat(dw)), U32.to_nat((oy + rows : U32)), yr, e_or))

# the pasted rows end rows * dw after they start
def bl.e_span(
  +sh: U32,
  +oy: U32,
  +dw: U32,
  +dh: U32,
  +area: U32,
  +h_area: {U32.to_nat(area) == Nat.mul(U32.to_nat(dw), U32.to_nat(dh)) : Nat},
  +hy: {Nat.is_lt(U32.to_nat(oy), U32.to_nat(dh)) == True{} : Bool}
) -> {bl.span(sh, dh, oy, dw) == Nat.add(bl.top(oy, dw), Nat.mul(bl.Rw(sh, dh, oy), U32.to_nat(dw))) : Nat}:
  +yn = U32.to_nat(oy)
  +wn = U32.to_nat(dw)
  +rn = bl.Rw(sh, dh, oy)
  Equal.trans(Nat, bl.span(sh, dh, oy, dw), Nat.mul(Nat.add(yn, rn), wn), Nat.add(bl.top(oy, dw), Nat.mul(rn, wn)),
    bl.e_spanv(sh, oy, dw, dh, area, h_area, hy),
    Equal.trans(Nat, Nat.mul(Nat.add(yn, rn), wn), Nat.add(Nat.mul(yn, wn), Nat.mul(rn, wn)),
      Nat.add(bl.top(oy, dw), Nat.mul(rn, wn)), R.mul_add(yn, rn, wn),
      Equal.cong(Nat, Nat, nn => Nat.add(nn, Nat.mul(rn, wn)), Nat.mul(yn, wn), bl.top(oy, dw),
        Equal.sym(Nat, bl.top(oy, dw), Nat.mul(yn, wn), bl.e_top(oy, dw, dh, area, h_area, hy)))))

# the pasted rows end inside dst's samples
def bl.h_len(
  +dp: List<&2, U32>,
  +sh: U32,
  +oy: U32,
  +dw: U32,
  +dh: U32,
  +area: U32,
  +h_area: {U32.to_nat(area) == Nat.mul(U32.to_nat(dw), U32.to_nat(dh)) : Nat},
  h_dst: {Laws.wf(Img.Raster{dw, dh, dp}) == True{} : Bool},
  +hy: {Nat.is_lt(U32.to_nat(oy), U32.to_nat(dh)) == True{} : Bool}
) -> {Nat.is_le(bl.span(sh, dh, oy, dw), List.length(&2, U32, dp)) == True{} : Bool}:
  +wh = Nat.mul(U32.to_nat(dw), U32.to_nat(dh))
  +sv = Nat.mul(Nat.add(U32.to_nat(oy), bl.Rw(sh, dh, oy)), U32.to_nat(dw))
  R.le_rw_l(sv, bl.span(sh, dh, oy, dw), List.length(&2, U32, dp),
    Equal.sym(Nat, bl.span(sh, dh, oy, dw), sv, bl.e_spanv(sh, oy, dw, dh, area, h_area, hy)),
    R.le_rw_r(sv, wh, List.length(&2, U32, dp),
      Equal.sym(Nat, List.length(&2, U32, dp), wh, R.nat_eq_true(List.length(&2, U32, dp), wh, h_dst)),
      R.le_rw_r(sv, U32.to_nat(area), wh, h_area,
        bl.below_area(Nat.add(U32.to_nat(oy), bl.Rw(sh, dh, oy)), dw, dh, area, h_area, bl.hyr(sh, dh, oy, hy)))))

# the source holds the pasted rows
def bl.hs(
  +sp: List<&2, U32>,
  +sw: U32,
  +sh: U32,
  +ox: U32,
  +oy: U32,
  +dw: U32,
  +dh: U32,
  h_src: {Laws.wf(Img.Raster{sw, sh, sp}) == True{} : Bool}
) -> {Nat.is_le(Nat.add(Nat.mul(bl.Rw(sh, dh, oy), U32.to_nat(sw)), bl.Cc(sw, ox, dw)),
  Nat.add(List.length(&2, U32, sp), U32.to_nat(sw))) == True{} : Bool}:
  +sn = U32.to_nat(sw)
  +hn = U32.to_nat(sh)
  +ln = List.length(&2, U32, sp)
  R.le_add_both(Nat.mul(bl.Rw(sh, dh, oy), sn), ln, bl.Cc(sw, ox, dw), sn,
    R.le_rw_r(Nat.mul(bl.Rw(sh, dh, oy), sn), Nat.mul(sn, hn), ln,
      Equal.sym(Nat, ln, Nat.mul(sn, hn), R.nat_eq_true(ln, Nat.mul(sn, hn), h_src)),
      R.le_rw_r(Nat.mul(bl.Rw(sh, dh, oy), sn), Nat.mul(hn, sn), Nat.mul(sn, hn), R.mul_comm(hn, sn),
        R.le_mul_mono(bl.Rw(sh, dh, oy), hn, sn, bl.hRs(sh, dh, oy)))),
    bl.hCs(sw, ox, dw))

# row j of the paste has a whole dst row to read
def bl.row_room(
  +dp: List<&2, U32>,
  +top: Nat,
  +span: Nat,
  +nn: Nat,
  +dw: Nat,
  +jj: Nat,
  hj: {Nat.is_lt(jj, nn) == True{} : Bool},
  e_span: {span == Nat.add(top, Nat.mul(nn, dw)) : Nat},
  h_len: {Nat.is_le(span, List.length(&2, U32, dp)) == True{} : Bool}
) -> {Nat.is_le(dw, List.length(&2, U32, List.drop(&2, U32, dp, Nat.add(top, Nat.mul(jj, dw))))) == True{} : Bool}:
  +mj = Nat.mul(jj, dw)
  +e1 = {Equal.trans(Nat, Nat.add(Nat.add(top, mj), dw), Nat.add(top, Nat.add(mj, dw)), Nat.add(top, Nat.add(dw, mj)),
    R.add_assoc(top, mj, dw), Equal.cong(Nat, Nat, xx => Nat.add(top, xx), Nat.add(mj, dw), Nat.add(dw, mj),
      R.add_comm(mj, dw))) : {Nat.add(Nat.add(top, mj), dw) == Nat.add(top, Nat.add(dw, mj)) : Nat}}
  R.drop_le0(dp, Nat.add(top, mj), dw, R.le_rw_l(Nat.add(top, Nat.add(dw, mj)), Nat.add(Nat.add(top, mj), dw),
    List.length(&2, U32, dp), Equal.sym(Nat, Nat.add(Nat.add(top, mj), dw), Nat.add(top, Nat.add(dw, mj)), e1),
    R.le_trans(Nat.add(top, Nat.add(dw, mj)), span, List.length(&2, U32, dp),
      R.le_rw_r(Nat.add(top, Nat.add(dw, mj)), Nat.add(top, Nat.mul(nn, dw)), span,
        Equal.sym(Nat, span, Nat.add(top, Nat.mul(nn, dw)), e_span),
        R.le_add_mono(top, Nat.mul(1n+jj, dw), Nat.mul(nn, dw), R.le_mul_mono(1n+jj, nn, dw,
          Equal.trans(Bool, Nat.is_le(1n+jj, nn), Nat.is_lt(jj, nn), True{},
            Equal.sym(Bool, Nat.is_lt(jj, nn), Nat.is_le(1n+jj, nn), R.lt_le_succ(jj, nn)), hj)))),
      h_len)))

# row j of the paste has its source span to read
def bl.src_room(
  +sp: List<&2, U32>,
  +nn: Nat,
  +sw: Nat,
  +cc: Nat,
  +jj: Nat,
  hj: {Nat.is_lt(jj, nn) == True{} : Bool},
  hs: {Nat.is_le(Nat.add(Nat.mul(nn, sw), cc), Nat.add(List.length(&2, U32, sp), sw)) == True{} : Bool}
) -> {Nat.is_le(cc, List.length(&2, U32, List.drop(&2, U32, sp, Nat.mul(jj, sw)))) == True{} : Bool}:
  +ln = List.length(&2, U32, sp)
  +mj = Nat.mul(jj, sw)
  +h1 = {R.le_trans(Nat.add(Nat.mul(1n+jj, sw), cc), Nat.add(Nat.mul(nn, sw), cc), Nat.add(ln, sw),
    R.le_add_both(Nat.mul(1n+jj, sw), Nat.mul(nn, sw), cc, cc, R.le_mul_mono(1n+jj, nn, sw,
      Equal.trans(Bool, Nat.is_le(1n+jj, nn), Nat.is_lt(jj, nn), True{},
        Equal.sym(Bool, Nat.is_lt(jj, nn), Nat.is_le(1n+jj, nn), R.lt_le_succ(jj, nn)), hj)), R.le_refl(cc)), hs) :
    {Nat.is_le(Nat.add(Nat.add(sw, mj), cc), Nat.add(ln, sw)) == True{} : Bool}}
  R.drop_le0(sp, mj, cc, R.le_cancel(sw, Nat.add(mj, cc), ln, R.le_rw_r(Nat.add(sw, Nat.add(mj, cc)), Nat.add(ln, sw),
    Nat.add(sw, ln), R.add_comm(ln, sw), R.le_rw_l(Nat.add(Nat.add(sw, mj), cc), Nat.add(sw, Nat.add(mj, cc)),
      Nat.add(ln, sw), R.add_assoc(sw, mj, cc), h1))))

# both halves true, the and is true
def bl.and_tt(
  aa: Bool,
  bb: Bool,
  ha: {aa == True{} : Bool},
  hb: {bb == True{} : Bool}
) -> {Bool.and(aa, bb) == True{} : Bool}:
  match aa:
    case True{}:
      hb
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, U32L.false_true(ha))

# the point (i, j) = (top + j' * dw) + i: where row j = y + j' of dst starts, plus i
def bl.e_band(
  +yn: Nat,
  +jj: Nat,
  +wn: Nat,
  +ii: Nat,
  +top: Nat,
  e_top: {top == Nat.mul(yn, wn) : Nat},
  h_le: {Nat.is_le(yn, jj) == True{} : Bool}
) -> {Nat.add(Nat.mul(jj, wn), ii) == Nat.add(top, Nat.add(Nat.mul(Nat.sub(jj, yn), wn), ii)) : Nat}:
  +jp = Nat.sub(jj, yn)
  Equal.trans(Nat, Nat.add(Nat.mul(jj, wn), ii), Nat.add(Nat.mul(Nat.add(yn, jp), wn), ii),
    Nat.add(top, Nat.add(Nat.mul(jp, wn), ii)),
    Equal.cong(Nat, Nat, nn => Nat.add(Nat.mul(nn, wn), ii), jj, Nat.add(yn, jp),
      Equal.sym(Nat, Nat.add(yn, jp), jj, R.add_sub(yn, jj, h_le))),
    Equal.trans(Nat, Nat.add(Nat.mul(Nat.add(yn, jp), wn), ii), Nat.add(Nat.add(Nat.mul(yn, wn), Nat.mul(jp, wn)), ii),
      Nat.add(top, Nat.add(Nat.mul(jp, wn), ii)),
      Equal.cong(Nat, Nat, nn => Nat.add(nn, ii), Nat.mul(Nat.add(yn, jp), wn), Nat.add(Nat.mul(yn, wn), Nat.mul(jp,
        wn)),
        R.mul_add(yn, jp, wn)),
      Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(yn, wn), Nat.mul(jp, wn)), ii),
        Nat.add(Nat.mul(yn, wn), Nat.add(Nat.mul(jp, wn), ii)), Nat.add(top, Nat.add(Nat.mul(jp, wn), ii)),
        R.add_assoc(Nat.mul(yn, wn), Nat.mul(jp, wn), ii),
        Equal.cong(Nat, Nat, nn => Nat.add(nn, Nat.add(Nat.mul(jp, wn), ii)), Nat.mul(yn, wn), top,
          Equal.sym(Nat, top, Nat.mul(yn, wn), e_top)))))

# j - y below the pasted rows, when y <= j < y + sh and j < dh
def bl.hjp(
  +sh: U32,
  +dh: U32,
  +oy: U32,
  +jj: Nat,
  +hy: {Nat.is_lt(U32.to_nat(oy), U32.to_nat(dh)) == True{} : Bool},
  +b1: {Nat.is_le(U32.to_nat(oy), jj) == True{} : Bool},
  b2: {Nat.is_lt(jj, Nat.add(U32.to_nat(oy), U32.to_nat(sh))) == True{} : Bool},
  hj: {Nat.is_lt(jj, U32.to_nat(dh)) == True{} : Bool}
) -> {Nat.is_lt(Nat.sub(jj, U32.to_nat(oy)), bl.Rw(sh, dh, oy)) == True{} : Bool}:
  +yn = U32.to_nat(oy)
  +dn = U32.to_nat(dh)
  +dd = Nat.sub(dn, yn)
  R.lt_rw_r(Nat.sub(jj, yn), Nat.min(U32.to_nat(sh), dd), bl.Rw(sh, dh, oy),
    Equal.sym(Nat, bl.Rw(sh, dh, oy), Nat.min(U32.to_nat(sh), dd), bl.eRw(sh, dh, oy, hy)),
    R.lt_min(Nat.sub(jj, yn), U32.to_nat(sh), dd, R.sub_lt(yn, jj, U32.to_nat(sh), b1, b2),
      R.sub_lt(yn, jj, dd, b1, R.lt_rw_r(jj, dn, Nat.add(yn, dd),
        Equal.sym(Nat, Nat.add(yn, dd), dn, R.add_sub(yn, dn, R.lt_le(yn, dn, hy))), hj))))

# blit.y is well formed, once whether y < dh is known
def bl.wf_y(
  yin: Bool,
  +dp: List<&2, U32>,
  +sp: List<&2, U32>,
  +dw: U32,
  +dh: U32,
  +sw: U32,
  +sh: U32,
  +ox: U32,
  +oy: U32,
  +area: U32,
  +h_area: {U32.to_nat(area) == Nat.mul(U32.to_nat(dw), U32.to_nat(dh)) : Nat},
  +h_dst: {Laws.wf(Img.Raster{dw, dh, dp}) == True{} : Bool},
  h_src: {Laws.wf(Img.Raster{sw, sh, sp}) == True{} : Bool},
  +ey: {Nat.is_lt(U32.to_nat(oy), U32.to_nat(dh)) == yin : Bool}
) -> {Nat.is_eq(List.length(&2, U32, Img.blit.y(yin, dp, sp, dw, dh, sw, sh, ox, oy)),
  Nat.mul(U32.to_nat(dw), U32.to_nat(dh))) == True{} : Bool}:
  match yin:
    case False{}:
      h_dst
    case True{}:
      +wh = Nat.mul(U32.to_nat(dw), U32.to_nat(dh))
      +jn = bj.J(dp, sp, bl.top(oy, dw), bl.span(sh, dh, oy, dw), bl.Rw(sh, dh, oy), bl.Lc(ox, dw), bl.Cc(sw, ox, dw),
        bl.Tc(sw, ox, dw), U32.to_nat(dw), U32.to_nat(sw))
      Equal.trans(Bool, Nat.is_eq(List.length(&2, U32, jn), wh), Nat.is_eq(List.length(&2, U32, dp), wh), True{},
        Equal.cong(Nat, Bool, nn => Nat.is_eq(nn, wh), List.length(&2, U32, jn), List.length(&2, U32, dp),
          bj.len(dp, sp, bl.top(oy, dw), bl.span(sh, dh, oy, dw), bl.Rw(sh, dh, oy), bl.Lc(ox, dw), bl.Cc(sw, ox, dw),
            bl.Tc(sw, ox, dw), U32.to_nat(dw), U32.to_nat(sw), bl.e_row(sw, ox, dw),
            bl.e_span(sh, oy, dw, dh, area, h_area, ey), bl.h_len(dp, sh, oy, dw, dh, area, h_area, h_dst, ey),
            bl.hs(sp, sw, sh, ox, oy, dw, dh, h_src))),
        h_dst)

def Laws.blit_wf(dst, src, xx, yy, area, h_area, h_dst, h_src):
  match dst src:
    case Img.Raster{+dw, +dh, +dp} Img.Raster{+sw, +sh, +sp}:
      +wh = Nat.mul(U32.to_nat(dw), U32.to_nat(dh))
      Equal.trans(Bool, Nat.is_eq(List.length(&2, U32, Img.blit.y(U32.is_lt(yy, dh), dp, sp, dw, dh, sw, sh, xx,
        yy)), wh),
        Nat.is_eq(List.length(&2, U32, Img.blit.y(Nat.is_lt(U32.to_nat(yy), U32.to_nat(dh)), dp, sp, dw, dh, sw, sh, xx,
          yy)), wh), True{},
        Equal.cong(Bool, Bool, bb => Nat.is_eq(List.length(&2, U32, Img.blit.y(bb, dp, sp, dw, dh, sw, sh, xx, yy)),
          wh),
          U32.is_lt(yy, dh), Nat.is_lt(U32.to_nat(yy), U32.to_nat(dh)), R.u32_lt(yy, dh)),
        bl.wf_y(Nat.is_lt(U32.to_nat(yy), U32.to_nat(dh)), dp, sp, dw, dh, sw, sh, xx, yy, area, h_area, h_dst,
          h_src, {==}))

# blit.join's samples, as bj.J
def bl.join_J(
  +dp: List<&2, U32>,
  +sp: List<&2, U32>,
  +dw: U32,
  +dh: U32,
  +sw: U32,
  +sh: U32,
  +ox: U32,
  +oy: U32
) -> {Img.blit.join(dp, sp, dw, dh, sw, sh, ox, oy) == bj.J(dp, sp, bl.top(oy, dw), bl.span(sh, dh, oy, dw),
  bl.Rw(sh, dh, oy), bl.Lc(ox, dw), bl.Cc(sw, ox, dw), bl.Tc(sw, ox, dw), U32.to_nat(dw), U32.to_nat(sw)) :
  List<&2, U32>}:
  {==}

# at a point src covers, blit reads src, once y < dh
def bl.in_go(
  +dp: List<&2, U32>,
  +sp: List<&2, U32>,
  +dw: U32,
  +dh: U32,
  +sw: U32,
  +sh: U32,
  +ox: U32,
  +oy: U32,
  +area: U32,
  +h_area: {U32.to_nat(area) == Nat.mul(U32.to_nat(dw), U32.to_nat(dh)) : Nat},
  +h_dst: {Laws.wf(Img.Raster{dw, dh, dp}) == True{} : Bool},
  +h_src: {Laws.wf(Img.Raster{sw, sh, sp}) == True{} : Bool},
  +ii: Nat,
  +jj: Nat,
  +hi: {Nat.is_lt(ii, U32.to_nat(dw)) == True{} : Bool},
  +hj: {Nat.is_lt(jj, U32.to_nat(dh)) == True{} : Bool},
  +a1: {Nat.is_le(U32.to_nat(ox), ii) == True{} : Bool},
  +a2: {Nat.is_lt(ii, Nat.add(U32.to_nat(ox), U32.to_nat(sw))) == True{} : Bool},
  +b1: {Nat.is_le(U32.to_nat(oy), jj) == True{} : Bool},
  +b2: {Nat.is_lt(jj, Nat.add(U32.to_nat(oy), U32.to_nat(sh))) == True{} : Bool},
  +hy: {Nat.is_lt(U32.to_nat(oy), U32.to_nat(dh)) == True{} : Bool}
) -> {List.get(&2, U32, Img.blit.join(dp, sp, dw, dh, sw, sh, ox, oy), Nat.add(Nat.mul(jj, U32.to_nat(dw)), ii)) ==
  List.get(&2, U32, sp, Nat.add(Nat.mul(Nat.sub(jj, U32.to_nat(oy)), U32.to_nat(sw)), Nat.sub(ii, U32.to_nat(ox)))) :
  Maybe<&2, U32>}:
  +xn = U32.to_nat(ox)
  +yn = U32.to_nat(oy)
  +wn = U32.to_nat(dw)
  +sn = U32.to_nat(sw)
  +top = bl.top(oy, dw)
  +span = bl.span(sh, dh, oy, dw)
  +rw = bl.Rw(sh, dh, oy)
  +lc = bl.Lc(ox, dw)
  +cc = bl.Cc(sw, ox, dw)
  +tc = bl.Tc(sw, ox, dw)
  +jp = Nat.sub(jj, yn)
  +ip = Nat.sub(ii, xn)
  +jn = bj.J(dp, sp, top, span, rw, lc, cc, tc, wn, sn)
  +drow = List.drop(&2, U32, dp, Nat.add(top, Nat.mul(jp, wn)))
  +srow = List.drop(&2, U32, sp, Nat.mul(jp, sn))
  +row = Img.blit.row(drow, srow, lc, cc, tc)
  +e_span = {bl.e_span(sh, oy, dw, dh, area, h_area, hy) : {span == Nat.add(top, Nat.mul(rw, wn)) : Nat}}
  +h_len = {bl.h_len(dp, sh, oy, dw, dh, area, h_area, h_dst, hy) :
    {Nat.is_le(span, List.length(&2, U32, dp)) == True{} : Bool}}
  +hs = {bl.hs(sp, sw, sh, ox, oy, dw, dh, h_src) :
    {Nat.is_le(Nat.add(Nat.mul(rw, sn), cc), Nat.add(List.length(&2, U32, sp), sn)) == True{} : Bool}}
  +hjp = {bl.hjp(sh, dh, oy, jj, hy, b1, b2, hj) : {Nat.is_lt(jp, rw) == True{} : Bool}}
  +e1 = {bl.e_band(yn, jj, wn, ii, top, bl.e_top(oy, dw, dh, area, h_area, hy), b1) :
    {Nat.add(Nat.mul(jj, wn), ii) == Nat.add(top, Nat.add(Nat.mul(jp, wn), ii)) : Nat}}
  +hxw = {R.lt_le(xn, wn, R.le_lt_trans(xn, ii, wn, a1, hi)) : {Nat.is_le(xn, wn) == True{} : Bool}}
  +elx = {Equal.trans(Nat, lc, Nat.min(xn, wn), xn, bl.eL(ox, dw), R.min_of_le(xn, wn, hxw)) : {lc == xn : Nat}}
  +eii = {Equal.trans(Nat, ii, Nat.add(xn, ip), Nat.add(lc, ip), Equal.sym(Nat, Nat.add(xn, ip), ii, R.add_sub(xn,
    ii, a1)),
    Equal.cong(Nat, Nat, nn => Nat.add(nn, ip), xn, lc, Equal.sym(Nat, lc, xn, elx))) : {ii == Nat.add(lc, ip) : Nat}}
  +dx = Nat.sub(wn, xn)
  +ecd = {Equal.trans(Nat, cc, Nat.min(sn, bl.Rm(ox, dw)), Nat.min(sn, dx), bl.eC(sw, ox, dw),
    Equal.cong(Nat, Nat, nn => Nat.min(sn, nn), bl.Rm(ox, dw), dx, Equal.trans(Nat, bl.Rm(ox, dw), Nat.sub(wn, lc), dx,
      bl.eRm(ox, dw), Equal.cong(Nat, Nat, nn => Nat.sub(wn, nn), lc, xn, elx)))) : {cc == Nat.min(sn, dx) : Nat}}
  +hk = {R.lt_rw_r(ip, Nat.min(sn, dx), cc, Equal.sym(Nat, cc, Nat.min(sn, dx), ecd), R.lt_min(ip, sn, dx,
    R.sub_lt(xn, ii, sn, a1, a2), R.sub_lt(xn, ii, dx, a1, R.lt_rw_r(ii, wn, Nat.add(xn, dx),
      Equal.sym(Nat, Nat.add(xn, dx), wn, R.add_sub(xn, wn, hxw)), hi)))) : {Nat.is_lt(ip, cc) == True{} : Bool}}
  +hl = {R.le_trans(lc, wn, List.length(&2, U32, drow), bl.hL(ox, dw),
    bl.row_room(dp, top, span, rw, wn, jp, hjp, e_span, h_len)) : {Nat.is_le(lc, List.length(&2, U32, drow)) == True{} :
    Bool}}
  +hc = {bl.src_room(sp, rw, sn, cc, jp, hjp, hs) : {Nat.is_le(cc, List.length(&2, U32, srow)) == True{} : Bool}}
  Equal.trans(Maybe<&2, U32>, List.get(&2, U32, jn, Nat.add(Nat.mul(jj, wn), ii)),
    List.get(&2, U32, jn, Nat.add(top, Nat.add(Nat.mul(jp, wn), ii))),
    List.get(&2, U32, sp, Nat.add(Nat.mul(jp, sn), ip)),
    Equal.cong(Nat, Maybe<&2, U32>, kk => List.get(&2, U32, jn, kk), Nat.add(Nat.mul(jj, wn), ii),
      Nat.add(top, Nat.add(Nat.mul(jp, wn), ii)), e1),
    Equal.trans(Maybe<&2, U32>, List.get(&2, U32, jn, Nat.add(top, Nat.add(Nat.mul(jp, wn), ii))),
      List.get(&2, U32, row, ii), List.get(&2, U32, sp, Nat.add(Nat.mul(jp, sn), ip)),
      bj.band(dp, sp, top, span, rw, lc, cc, tc, wn, sn, ii, jp, hi, hjp, bl.e_row(sw, ox, dw), e_span, h_len, hs),
      Equal.trans(Maybe<&2, U32>, List.get(&2, U32, row, ii), List.get(&2, U32, row, Nat.add(lc, ip)),
        List.get(&2, U32, sp, Nat.add(Nat.mul(jp, sn), ip)),
        Equal.cong(Nat, Maybe<&2, U32>, kk => List.get(&2, U32, row, kk), ii, Nat.add(lc, ip), eii),
        Equal.trans(Maybe<&2, U32>, List.get(&2, U32, row, Nat.add(lc, ip)), List.get(&2, U32, srow, ip),
          List.get(&2, U32, sp, Nat.add(Nat.mul(jp, sn), ip)),
          blit.row_mid(drow, srow, lc, cc, tc, ip, hk, hl, hc), R.get_drop(sp, Nat.mul(jp, sn), ip)))))

def Laws.blit_in(dst, src, xx, yy, area, h_area, h_dst, h_src, ii, jj, hi, hj, h_cov):
  match dst src:
    case Img.Raster{+dw, +dh, +dp} Img.Raster{+sw, +sh, +sp}:
      +xn = U32.to_nat(xx)
      +yn = U32.to_nat(yy)
      +a1b = Nat.is_le(xn, ii)
      +a2b = Nat.is_lt(ii, Nat.add(xn, U32.to_nat(sw)))
      +b1b = Nat.is_le(yn, jj)
      +b2b = Nat.is_lt(jj, Nat.add(yn, U32.to_nat(sh)))
      +cx = {U32L.and_left(Bool.and(a1b, a2b), Bool.and(b1b, b2b), h_cov) : {Bool.and(a1b, a2b) == True{} : Bool}}
      +cy = {U32L.and_right(Bool.and(a1b, a2b), Bool.and(b1b, b2b), h_cov) : {Bool.and(b1b, b2b) == True{} : Bool}}
      +b1 = {U32L.and_left(b1b, b2b, cy) : {b1b == True{} : Bool}}
      +hy = {R.le_lt_trans(yn, jj, U32.to_nat(dh), b1, hj) : {Nat.is_lt(yn, U32.to_nat(dh)) == True{} : Bool}}
      +kk = Nat.add(Nat.mul(jj, U32.to_nat(dw)), ii)
      Equal.trans(Maybe<&2, U32>, List.get(&2, U32, Img.blit.y(U32.is_lt(yy, dh), dp, sp, dw, dh, sw, sh, xx, yy), kk),
        List.get(&2, U32, Img.blit.y(True{}, dp, sp, dw, dh, sw, sh, xx, yy), kk),
        List.get(&2, U32, sp, Nat.add(Nat.mul(Nat.sub(jj, yn), U32.to_nat(sw)), Nat.sub(ii, xn))),
        Equal.cong(Bool, Maybe<&2, U32>, bb => List.get(&2, U32, Img.blit.y(bb, dp, sp, dw, dh, sw, sh, xx, yy), kk),
          U32.is_lt(yy, dh), True{}, ras.lt(yy, dh, hy)),
        bl.in_go(dp, sp, dw, dh, sw, sh, xx, yy, area, h_area, h_dst, h_src, ii, jj, hi, hj,
          U32L.and_left(a1b, a2b, cx), U32L.and_right(a1b, a2b, cx), b1, U32L.and_right(b1b, b2b, cy), hy))

# a pasted row away from its source span reads dst: after the split on the
# right part
def bl.row_out_b(
  bm: Bool,
  +drow: List<&2, U32>,
  +srow: List<&2, U32>,
  +ll: Nat,
  +cc: Nat,
  +tt: Nat,
  +dw: Nat,
  +ii: Nat,
  e_row: {Nat.add(ll, Nat.add(cc, tt)) == dw : Nat},
  hi: {Nat.is_lt(ii, dw) == True{} : Bool},
  hl: {Nat.is_le(ll, List.length(&2, U32, drow)) == True{} : Bool},
  hc: {Nat.is_le(cc, List.length(&2, U32, srow)) == True{} : Bool},
  +hle: {Nat.is_le(ll, ii) == True{} : Bool},
  eb: {Nat.is_lt(Nat.sub(ii, ll), cc) == bm : Bool},
  notmid: {Nat.is_le(ll, ii) == True{} : Bool} -> {Nat.is_lt(Nat.sub(ii, ll), cc) == True{} : Bool} -> Empty
) -> {List.get(&2, U32, Img.blit.row(drow, srow, ll, cc, tt), ii) == List.get(&2, U32, drow, ii) : Maybe<&2, U32>}:
  match bm:
    case True{}:
      Empty.absurd({List.get(&2, U32, Img.blit.row(drow, srow, ll, cc, tt), ii) == List.get(&2, U32, drow, ii) :
        Maybe<&2, U32>}, notmid(hle, eb))
    case False{}:
      +ip = Nat.sub(ii, ll)
      +hcle = {R.not_lt_le(ip, cc, eb) : {Nat.is_le(cc, ip) == True{} : Bool}}
      +tp = Nat.sub(ip, cc)
      +eii = {Equal.trans(Nat, ii, Nat.add(ll, ip), Nat.add(ll, Nat.add(cc, tp)),
        Equal.sym(Nat, Nat.add(ll, ip), ii, R.add_sub(ll, ii, hle)),
        Equal.cong(Nat, Nat, nn => Nat.add(ll, nn), ip, Nat.add(cc, tp), Equal.sym(Nat, Nat.add(cc, tp), ip,
          R.add_sub(cc, ip, hcle)))) : {ii == Nat.add(ll, Nat.add(cc, tp)) : Nat}}
      +hk = {R.lt_cancel(cc, tp, tt, R.lt_cancel(ll, Nat.add(cc, tp), Nat.add(cc, tt), R.lt_rw_l(ii,
        Nat.add(ll, Nat.add(cc, tp)), Nat.add(ll, Nat.add(cc, tt)), eii, R.lt_rw_r(ii, dw, Nat.add(ll, Nat.add(cc, tt)),
          Equal.sym(Nat, Nat.add(ll, Nat.add(cc, tt)), dw, e_row), hi)))) : {Nat.is_lt(tp, tt) == True{} : Bool}}
      Equal.trans(Maybe<&2, U32>, List.get(&2, U32, Img.blit.row(drow, srow, ll, cc, tt), ii),
        List.get(&2, U32, Img.blit.row(drow, srow, ll, cc, tt), Nat.add(ll, Nat.add(cc, tp))), List.get(&2, U32,
          drow, ii),
        Equal.cong(Nat, Maybe<&2, U32>, kk => List.get(&2, U32, Img.blit.row(drow, srow, ll, cc, tt), kk), ii,
          Nat.add(ll, Nat.add(cc, tp)), eii),
        Equal.trans(Maybe<&2, U32>, List.get(&2, U32, Img.blit.row(drow, srow, ll, cc, tt), Nat.add(ll, Nat.add(cc,
          tp))),
          List.get(&2, U32, drow, Nat.add(Nat.add(ll, cc), tp)), List.get(&2, U32, drow, ii),
          blit.row_right(drow, srow, ll, cc, tt, tp, hk, hl, hc),
          Equal.cong(Nat, Maybe<&2, U32>, kk => List.get(&2, U32, drow, kk), Nat.add(Nat.add(ll, cc), tp), ii,
            Equal.trans(Nat, Nat.add(Nat.add(ll, cc), tp), Nat.add(ll, Nat.add(cc, tp)), ii, R.add_assoc(ll, cc, tp),
              Equal.sym(Nat, ii, Nat.add(ll, Nat.add(cc, tp)), eii)))))

# a pasted row away from its source span reads dst: split on the left part
def bl.row_out(
  ba: Bool,
  +drow: List<&2, U32>,
  +srow: List<&2, U32>,
  +ll: Nat,
  +cc: Nat,
  +tt: Nat,
  +dw: Nat,
  +ii: Nat,
  e_row: {Nat.add(ll, Nat.add(cc, tt)) == dw : Nat},
  hi: {Nat.is_lt(ii, dw) == True{} : Bool},
  +hl: {Nat.is_le(ll, List.length(&2, U32, drow)) == True{} : Bool},
  hc: {Nat.is_le(cc, List.length(&2, U32, srow)) == True{} : Bool},
  eb: {Nat.is_lt(ii, ll) == ba : Bool},
  notmid: {Nat.is_le(ll, ii) == True{} : Bool} -> {Nat.is_lt(Nat.sub(ii, ll), cc) == True{} : Bool} -> Empty
) -> {List.get(&2, U32, Img.blit.row(drow, srow, ll, cc, tt), ii) == List.get(&2, U32, drow, ii) : Maybe<&2, U32>}:
  match ba:
    case True{}:
      blit.row_left(drow, srow, ll, cc, tt, ii, eb, hl)
    case False{}:
      bl.row_out_b(Nat.is_lt(Nat.sub(ii, ll), cc), drow, srow, ll, cc, tt, dw, ii, e_row, hi, hl, hc,
        R.not_lt_le(ii, ll, eb), {==}, notmid)

# in the band of pasted rows, at a point src does not cover, blit reads dst
def bl.out_band(
  +dp: List<&2, U32>,
  +sp: List<&2, U32>,
  +dw: U32,
  +dh: U32,
  +sw: U32,
  +sh: U32,
  +ox: U32,
  +oy: U32,
  +area: U32,
  +h_area: {U32.to_nat(area) == Nat.mul(U32.to_nat(dw), U32.to_nat(dh)) : Nat},
  +h_dst: {Laws.wf(Img.Raster{dw, dh, dp}) == True{} : Bool},
  +h_src: {Laws.wf(Img.Raster{sw, sh, sp}) == True{} : Bool},
  +ii: Nat,
  +jj: Nat,
  +hi: {Nat.is_lt(ii, U32.to_nat(dw)) == True{} : Bool},
  +h_cov: {Laws.covers(ox, oy, Img.Raster{sw, sh, sp}, ii, jj) == False{} : Bool},
  +hy: {Nat.is_lt(U32.to_nat(oy), U32.to_nat(dh)) == True{} : Bool},
  +hle: {Nat.is_le(U32.to_nat(oy), jj) == True{} : Bool},
  +hjp: {Nat.is_lt(Nat.sub(jj, U32.to_nat(oy)), bl.Rw(sh, dh, oy)) == True{} : Bool}
) -> {List.get(&2, U32, bj.J(dp, sp, bl.top(oy, dw), bl.span(sh, dh, oy, dw), bl.Rw(sh, dh, oy), bl.Lc(ox, dw),
  bl.Cc(sw, ox, dw), bl.Tc(sw, ox, dw), U32.to_nat(dw), U32.to_nat(sw)), Nat.add(Nat.mul(jj, U32.to_nat(dw)), ii)) ==
  List.get(&2, U32, dp, Nat.add(Nat.mul(jj, U32.to_nat(dw)), ii)) : Maybe<&2, U32>}:
  +xn = U32.to_nat(ox)
  +yn = U32.to_nat(oy)
  +wn = U32.to_nat(dw)
  +sn = U32.to_nat(sw)
  +top = bl.top(oy, dw)
  +span = bl.span(sh, dh, oy, dw)
  +rw = bl.Rw(sh, dh, oy)
  +lc = bl.Lc(ox, dw)
  +cc = bl.Cc(sw, ox, dw)
  +tc = bl.Tc(sw, ox, dw)
  +jp = Nat.sub(jj, yn)
  +kk = Nat.add(Nat.mul(jj, wn), ii)
  +jn = bj.J(dp, sp, top, span, rw, lc, cc, tc, wn, sn)
  +doff = Nat.add(top, Nat.mul(jp, wn))
  +drow = List.drop(&2, U32, dp, doff)
  +srow = List.drop(&2, U32, sp, Nat.mul(jp, sn))
  +row = Img.blit.row(drow, srow, lc, cc, tc)
  +e_span = {bl.e_span(sh, oy, dw, dh, area, h_area, hy) : {span == Nat.add(top, Nat.mul(rw, wn)) : Nat}}
  +h_len = {bl.h_len(dp, sh, oy, dw, dh, area, h_area, h_dst, hy) :
    {Nat.is_le(span, List.length(&2, U32, dp)) == True{} : Bool}}
  +hs = {bl.hs(sp, sw, sh, ox, oy, dw, dh, h_src) :
    {Nat.is_le(Nat.add(Nat.mul(rw, sn), cc), Nat.add(List.length(&2, U32, sp), sn)) == True{} : Bool}}
  +e1 = {bl.e_band(yn, jj, wn, ii, top, bl.e_top(oy, dw, dh, area, h_area, hy), hle) :
    {kk == Nat.add(top, Nat.add(Nat.mul(jp, wn), ii)) : Nat}}
  +hl = {R.le_trans(lc, wn, List.length(&2, U32, drow), bl.hL(ox, dw),
    bl.row_room(dp, top, span, rw, wn, jp, hjp, e_span, h_len)) : {Nat.is_le(lc, List.length(&2, U32, drow)) == True{} :
    Bool}}
  +hc = {bl.src_room(sp, rw, sn, cc, jp, hjp, hs) : {Nat.is_le(cc, List.length(&2, U32, srow)) == True{} : Bool}}
  +b2 = {R.lt_rw_l(Nat.add(yn, jp), jj, Nat.add(yn, U32.to_nat(sh)), R.add_sub(yn, jj, hle),
    R.lt_add_mono(yn, jp, U32.to_nat(sh), R.lt_le_trans(jp, rw, U32.to_nat(sh), hjp, bl.hRs(sh, dh, oy)))) :
    {Nat.is_lt(jj, Nat.add(yn, U32.to_nat(sh))) == True{} : Bool}}
  notmid = {+hl2 => +hm =>
    +hlw = {R.sub_pos(wn, lc, R.lt_pos(Nat.sub(ii, lc), Nat.sub(wn, lc), R.lt_rw_r(Nat.sub(ii, lc), bl.Rm(ox, dw),
      Nat.sub(wn, lc), bl.eRm(ox, dw), R.lt_le_trans(Nat.sub(ii, lc), cc, bl.Rm(ox, dw), hm, bl.hC(sw, ox, dw))))) :
      {Nat.is_lt(lc, wn) == True{} : Bool}}
    +elx = {Equal.trans(Nat, lc, Nat.min(xn, wn), xn, bl.eL(ox, dw), R.min_lt_r(xn, wn,
      R.lt_rw_l(lc, Nat.min(xn, wn), wn, bl.eL(ox, dw), hlw))) : {lc == xn : Nat}}
    +a1 = {R.le_rw_l(lc, xn, ii, elx, hl2) : {Nat.is_le(xn, ii) == True{} : Bool}}
    +a2 = {R.lt_rw_r(ii, Nat.add(lc, sn), Nat.add(xn, sn), Equal.cong(Nat, Nat, nn => Nat.add(nn, sn), lc, xn, elx),
      R.lt_rw_l(Nat.add(lc, Nat.sub(ii, lc)), ii, Nat.add(lc, sn), R.add_sub(lc, ii, hl2),
        R.lt_add_mono(lc, Nat.sub(ii, lc), sn, R.lt_le_trans(Nat.sub(ii, lc), cc, sn, hm, bl.hCs(sw, ox, dw))))) :
      {Nat.is_lt(ii, Nat.add(xn, sn)) == True{} : Bool}}
    U32L.false_true(Equal.trans(Bool, False{}, Laws.covers(ox, oy, Img.Raster{sw, sh, sp}, ii, jj), True{},
      Equal.sym(Bool, Laws.covers(ox, oy, Img.Raster{sw, sh, sp}, ii, jj), False{}, h_cov),
      bl.and_tt(Bool.and(Nat.is_le(xn, ii), Nat.is_lt(ii, Nat.add(xn, sn))),
        Bool.and(Nat.is_le(yn, jj), Nat.is_lt(jj, Nat.add(yn, U32.to_nat(sh)))),
        bl.and_tt(Nat.is_le(xn, ii), Nat.is_lt(ii, Nat.add(xn, sn)), a1, a2),
        bl.and_tt(Nat.is_le(yn, jj), Nat.is_lt(jj, Nat.add(yn, U32.to_nat(sh))), hle, b2)))) :
    {Nat.is_le(lc, ii) == True{} : Bool} -> {Nat.is_lt(Nat.sub(ii, lc), cc) == True{} : Bool} -> Empty}
  Equal.trans(Maybe<&2, U32>, List.get(&2, U32, jn, kk), List.get(&2, U32, jn, Nat.add(top, Nat.add(Nat.mul(jp, wn),
    ii))),
    List.get(&2, U32, dp, kk),
    Equal.cong(Nat, Maybe<&2, U32>, nn => List.get(&2, U32, jn, nn), kk, Nat.add(top, Nat.add(Nat.mul(jp, wn), ii)),
      e1),
    Equal.trans(Maybe<&2, U32>, List.get(&2, U32, jn, Nat.add(top, Nat.add(Nat.mul(jp, wn), ii))),
      List.get(&2, U32, row, ii), List.get(&2, U32, dp, kk),
      bj.band(dp, sp, top, span, rw, lc, cc, tc, wn, sn, ii, jp, hi, hjp, bl.e_row(sw, ox, dw), e_span, h_len, hs),
      Equal.trans(Maybe<&2, U32>, List.get(&2, U32, row, ii), List.get(&2, U32, drow, ii), List.get(&2, U32, dp, kk),
        bl.row_out(Nat.is_lt(ii, lc), drow, srow, lc, cc, tc, wn, ii, bl.e_row(sw, ox, dw), hi, hl, hc, {==}, notmid),
        Equal.trans(Maybe<&2, U32>, List.get(&2, U32, drow, ii), List.get(&2, U32, dp, Nat.add(doff, ii)),
          List.get(&2, U32, dp, kk), R.get_drop(dp, doff, ii),
          Equal.cong(Nat, Maybe<&2, U32>, nn => List.get(&2, U32, dp, nn), Nat.add(doff, ii), kk,
            Equal.trans(Nat, Nat.add(doff, ii), Nat.add(top, Nat.add(Nat.mul(jp, wn), ii)), kk,
              R.add_assoc(top, Nat.mul(jp, wn), ii),
              Equal.sym(Nat, kk, Nat.add(top, Nat.add(Nat.mul(jp, wn), ii)), e1)))))))

# below the band, at or after y + rows, blit reads dst
def bl.out_below(
  +dp: List<&2, U32>,
  +sp: List<&2, U32>,
  +dw: U32,
  +dh: U32,
  +sw: U32,
  +sh: U32,
  +ox: U32,
  +oy: U32,
  +area: U32,
  +h_area: {U32.to_nat(area) == Nat.mul(U32.to_nat(dw), U32.to_nat(dh)) : Nat},
  +h_dst: {Laws.wf(Img.Raster{dw, dh, dp}) == True{} : Bool},
  +h_src: {Laws.wf(Img.Raster{sw, sh, sp}) == True{} : Bool},
  +ii: Nat,
  +jj: Nat,
  +hy: {Nat.is_lt(U32.to_nat(oy), U32.to_nat(dh)) == True{} : Bool},
  +hle: {Nat.is_le(U32.to_nat(oy), jj) == True{} : Bool},
  +hr: {Nat.is_le(bl.Rw(sh, dh, oy), Nat.sub(jj, U32.to_nat(oy))) == True{} : Bool}
) -> {List.get(&2, U32, bj.J(dp, sp, bl.top(oy, dw), bl.span(sh, dh, oy, dw), bl.Rw(sh, dh, oy), bl.Lc(ox, dw),
  bl.Cc(sw, ox, dw), bl.Tc(sw, ox, dw), U32.to_nat(dw), U32.to_nat(sw)), Nat.add(Nat.mul(jj, U32.to_nat(dw)), ii)) ==
  List.get(&2, U32, dp, Nat.add(Nat.mul(jj, U32.to_nat(dw)), ii)) : Maybe<&2, U32>}:
  +yn = U32.to_nat(oy)
  +wn = U32.to_nat(dw)
  +rw = bl.Rw(sh, dh, oy)
  +span = bl.span(sh, dh, oy, dw)
  +jp = Nat.sub(jj, yn)
  +dd = Nat.sub(jp, rw)
  +mm = Nat.add(Nat.mul(dd, wn), ii)
  +kk = Nat.add(Nat.mul(jj, wn), ii)
  +jn = bj.J(dp, sp, bl.top(oy, dw), span, rw, bl.Lc(ox, dw), bl.Cc(sw, ox, dw), bl.Tc(sw, ox, dw), wn, U32.to_nat(sw))
  +ejj = {Equal.trans(Nat, jj, Nat.add(yn, jp), Nat.add(Nat.add(yn, rw), dd),
    Equal.sym(Nat, Nat.add(yn, jp), jj, R.add_sub(yn, jj, hle)),
    Equal.trans(Nat, Nat.add(yn, jp), Nat.add(yn, Nat.add(rw, dd)), Nat.add(Nat.add(yn, rw), dd),
      Equal.cong(Nat, Nat, nn => Nat.add(yn, nn), jp, Nat.add(rw, dd), Equal.sym(Nat, Nat.add(rw, dd), jp,
        R.add_sub(rw, jp, hr))),
      Equal.sym(Nat, Nat.add(Nat.add(yn, rw), dd), Nat.add(yn, Nat.add(rw, dd)), R.add_assoc(yn, rw, dd)))) :
    {jj == Nat.add(Nat.add(yn, rw), dd) : Nat}}
  +ek = {Equal.trans(Nat, kk, Nat.add(Nat.mul(Nat.add(Nat.add(yn, rw), dd), wn), ii), Nat.add(span, mm),
    Equal.cong(Nat, Nat, nn => Nat.add(Nat.mul(nn, wn), ii), jj, Nat.add(Nat.add(yn, rw), dd), ejj),
    Equal.trans(Nat, Nat.add(Nat.mul(Nat.add(Nat.add(yn, rw), dd), wn), ii),
      Nat.add(Nat.add(Nat.mul(Nat.add(yn, rw), wn), Nat.mul(dd, wn)), ii), Nat.add(span, mm),
      Equal.cong(Nat, Nat, nn => Nat.add(nn, ii), Nat.mul(Nat.add(Nat.add(yn, rw), dd), wn),
        Nat.add(Nat.mul(Nat.add(yn, rw), wn), Nat.mul(dd, wn)), R.mul_add(Nat.add(yn, rw), dd, wn)),
      Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(Nat.add(yn, rw), wn), Nat.mul(dd, wn)), ii),
        Nat.add(Nat.mul(Nat.add(yn, rw), wn), mm), Nat.add(span, mm),
        R.add_assoc(Nat.mul(Nat.add(yn, rw), wn), Nat.mul(dd, wn), ii),
        Equal.cong(Nat, Nat, nn => Nat.add(nn, mm), Nat.mul(Nat.add(yn, rw), wn), span,
          Equal.sym(Nat, span, Nat.mul(Nat.add(yn, rw), wn), bl.e_spanv(sh, oy, dw, dh, area, h_area, hy)))))) :
    {kk == Nat.add(span, mm) : Nat}}
  Equal.trans(Maybe<&2, U32>, List.get(&2, U32, jn, kk), List.get(&2, U32, jn, Nat.add(span, mm)), List.get(&2, U32,
    dp, kk),
    Equal.cong(Nat, Maybe<&2, U32>, nn => List.get(&2, U32, jn, nn), kk, Nat.add(span, mm), ek),
    Equal.trans(Maybe<&2, U32>, List.get(&2, U32, jn, Nat.add(span, mm)), List.get(&2, U32, dp, Nat.add(span, mm)),
      List.get(&2, U32, dp, kk),
      bj.bottom(dp, sp, bl.top(oy, dw), span, rw, bl.Lc(ox, dw), bl.Cc(sw, ox, dw), bl.Tc(sw, ox, dw), wn,
        U32.to_nat(sw),
        mm, bl.e_row(sw, ox, dw), bl.e_span(sh, oy, dw, dh, area, h_area, hy),
        bl.h_len(dp, sh, oy, dw, dh, area, h_area, h_dst, hy), bl.hs(sp, sw, sh, ox, oy, dw, dh, h_src)),
      Equal.cong(Nat, Maybe<&2, U32>, nn => List.get(&2, U32, dp, nn), Nat.add(span, mm), kk,
        Equal.sym(Nat, kk, Nat.add(span, mm), ek))))

# at or below row y, split on the band
def bl.out_r(
  br: Bool,
  +dp: List<&2, U32>,
  +sp: List<&2, U32>,
  +dw: U32,
  +dh: U32,
  +sw: U32,
  +sh: U32,
  +ox: U32,
  +oy: U32,
  +area: U32,
  +h_area: {U32.to_nat(area) == Nat.mul(U32.to_nat(dw), U32.to_nat(dh)) : Nat},
  +h_dst: {Laws.wf(Img.Raster{dw, dh, dp}) == True{} : Bool},
  +h_src: {Laws.wf(Img.Raster{sw, sh, sp}) == True{} : Bool},
  +ii: Nat,
  +jj: Nat,
  +hi: {Nat.is_lt(ii, U32.to_nat(dw)) == True{} : Bool},
  +h_cov: {Laws.covers(ox, oy, Img.Raster{sw, sh, sp}, ii, jj) == False{} : Bool},
  +hy: {Nat.is_lt(U32.to_nat(oy), U32.to_nat(dh)) == True{} : Bool},
  +hle: {Nat.is_le(U32.to_nat(oy), jj) == True{} : Bool},
  eb: {Nat.is_lt(Nat.sub(jj, U32.to_nat(oy)), bl.Rw(sh, dh, oy)) == br : Bool}
) -> {List.get(&2, U32, bj.J(dp, sp, bl.top(oy, dw), bl.span(sh, dh, oy, dw), bl.Rw(sh, dh, oy), bl.Lc(ox, dw),
  bl.Cc(sw, ox, dw), bl.Tc(sw, ox, dw), U32.to_nat(dw), U32.to_nat(sw)), Nat.add(Nat.mul(jj, U32.to_nat(dw)), ii)) ==
  List.get(&2, U32, dp, Nat.add(Nat.mul(jj, U32.to_nat(dw)), ii)) : Maybe<&2, U32>}:
  match br:
    case True{}:
      bl.out_band(dp, sp, dw, dh, sw, sh, ox, oy, area, h_area, h_dst, h_src, ii, jj, hi, h_cov, hy, hle, eb)
    case False{}:
      bl.out_below(dp, sp, dw, dh, sw, sh, ox, oy, area, h_area, h_dst, h_src, ii, jj, hy, hle,
        R.not_lt_le(Nat.sub(jj, U32.to_nat(oy)), bl.Rw(sh, dh, oy), eb))

# once y < dh, split on the rows above the paste
def bl.out_j(
  ba: Bool,
  +dp: List<&2, U32>,
  +sp: List<&2, U32>,
  +dw: U32,
  +dh: U32,
  +sw: U32,
  +sh: U32,
  +ox: U32,
  +oy: U32,
  +area: U32,
  +h_area: {U32.to_nat(area) == Nat.mul(U32.to_nat(dw), U32.to_nat(dh)) : Nat},
  +h_dst: {Laws.wf(Img.Raster{dw, dh, dp}) == True{} : Bool},
  +h_src: {Laws.wf(Img.Raster{sw, sh, sp}) == True{} : Bool},
  +ii: Nat,
  +jj: Nat,
  +hi: {Nat.is_lt(ii, U32.to_nat(dw)) == True{} : Bool},
  +h_cov: {Laws.covers(ox, oy, Img.Raster{sw, sh, sp}, ii, jj) == False{} : Bool},
  +hy: {Nat.is_lt(U32.to_nat(oy), U32.to_nat(dh)) == True{} : Bool},
  eb: {Nat.is_lt(jj, U32.to_nat(oy)) == ba : Bool}
) -> {List.get(&2, U32, bj.J(dp, sp, bl.top(oy, dw), bl.span(sh, dh, oy, dw), bl.Rw(sh, dh, oy), bl.Lc(ox, dw),
  bl.Cc(sw, ox, dw), bl.Tc(sw, ox, dw), U32.to_nat(dw), U32.to_nat(sw)), Nat.add(Nat.mul(jj, U32.to_nat(dw)), ii)) ==
  List.get(&2, U32, dp, Nat.add(Nat.mul(jj, U32.to_nat(dw)), ii)) : Maybe<&2, U32>}:
  match ba:
    case True{}:
      +yn = U32.to_nat(oy)
      +wn = U32.to_nat(dw)
      bj.top(dp, sp, bl.top(oy, dw), bl.span(sh, dh, oy, dw), bl.Rw(sh, dh, oy), bl.Lc(ox, dw), bl.Cc(sw, ox, dw),
        bl.Tc(sw, ox, dw), wn, U32.to_nat(sw), Nat.add(Nat.mul(jj, wn), ii),
        R.lt_rw_r(Nat.add(Nat.mul(jj, wn), ii), Nat.mul(wn, yn), bl.top(oy, dw), Equal.trans(Nat, Nat.mul(wn, yn),
          Nat.mul(yn, wn), bl.top(oy, dw), R.mul_comm(wn, yn), Equal.sym(Nat, bl.top(oy, dw), Nat.mul(yn, wn),
            bl.e_top(oy, dw, dh, area, h_area, hy))), R.index_lt(ii, jj, wn, yn, hi, eb)),
        bl.e_span(sh, oy, dw, dh, area, h_area, hy), bl.h_len(dp, sh, oy, dw, dh, area, h_area, h_dst, hy))
    case False{}:
      bl.out_r(Nat.is_lt(Nat.sub(jj, U32.to_nat(oy)), bl.Rw(sh, dh, oy)), dp, sp, dw, dh, sw, sh, ox, oy, area, h_area,
        h_dst, h_src, ii, jj, hi, h_cov, hy, R.not_lt_le(jj, U32.to_nat(oy), eb), {==})

# split on y < dh
def bl.out_y(
  yin: Bool,
  +dp: List<&2, U32>,
  +sp: List<&2, U32>,
  +dw: U32,
  +dh: U32,
  +sw: U32,
  +sh: U32,
  +ox: U32,
  +oy: U32,
  +area: U32,
  +h_area: {U32.to_nat(area) == Nat.mul(U32.to_nat(dw), U32.to_nat(dh)) : Nat},
  +h_dst: {Laws.wf(Img.Raster{dw, dh, dp}) == True{} : Bool},
  +h_src: {Laws.wf(Img.Raster{sw, sh, sp}) == True{} : Bool},
  +ii: Nat,
  +jj: Nat,
  +hi: {Nat.is_lt(ii, U32.to_nat(dw)) == True{} : Bool},
  +h_cov: {Laws.covers(ox, oy, Img.Raster{sw, sh, sp}, ii, jj) == False{} : Bool},
  ey: {Nat.is_lt(U32.to_nat(oy), U32.to_nat(dh)) == yin : Bool}
) -> {List.get(&2, U32, Img.blit.y(yin, dp, sp, dw, dh, sw, sh, ox, oy), Nat.add(Nat.mul(jj, U32.to_nat(dw)), ii)) ==
  List.get(&2, U32, dp, Nat.add(Nat.mul(jj, U32.to_nat(dw)), ii)) : Maybe<&2, U32>}:
  match yin:
    case False{}:
      {==}
    case True{}:
      bl.out_j(Nat.is_lt(jj, U32.to_nat(oy)), dp, sp, dw, dh, sw, sh, ox, oy, area, h_area, h_dst, h_src, ii, jj,
        hi, h_cov,
        ey, {==})

def Laws.blit_out(dst, src, xx, yy, area, h_area, h_dst, h_src, ii, jj, hi, _hj, h_cov):
  match dst src:
    case Img.Raster{+dw, +dh, +dp} Img.Raster{+sw, +sh, +sp}:
      +kk = Nat.add(Nat.mul(jj, U32.to_nat(dw)), ii)
      Equal.trans(Maybe<&2, U32>, List.get(&2, U32, Img.blit.y(U32.is_lt(yy, dh), dp, sp, dw, dh, sw, sh, xx, yy), kk),
        List.get(&2, U32, Img.blit.y(Nat.is_lt(U32.to_nat(yy), U32.to_nat(dh)), dp, sp, dw, dh, sw, sh, xx, yy), kk),
        List.get(&2, U32, dp, kk),
        Equal.cong(Bool, Maybe<&2, U32>, bb => List.get(&2, U32, Img.blit.y(bb, dp, sp, dw, dh, sw, sh, xx, yy), kk),
          U32.is_lt(yy, dh), Nat.is_lt(U32.to_nat(yy), U32.to_nat(dh)), R.u32_lt(yy, dh)),
        bl.out_y(Nat.is_lt(U32.to_nat(yy), U32.to_nat(dh)), dp, sp, dw, dh, sw, sh, xx, yy, area, h_area, h_dst,
          h_src, ii,
          jj, hi, h_cov, {==}))

# ---- wp5-png-decode ----

# byte 3, 2, 1 and 0 of a U32, as spec.be4 writes them
def by3(+nn: U32) -> U32:
  U32.and(255, U32.shrn(nn, 24n))

def by2(+nn: U32) -> U32:
  U32.and(255, U32.shrn(nn, 16n))

def by1(+nn: U32) -> U32:
  U32.and(255, U32.shrn(nn, 8n))

def by0(+nn: U32) -> U32:
  U32.and(255, nn)

# the width or height the decoder reads back from spec.be4's bytes
def be.back(+nn: U32) -> U32:
  Png.be.u32(by3(nn), by2(nn), by1(nn), by0(nn))

# the IHDR data as the walker holds it, last byte first
def ihdr.held(+ww: U32, +hh: U32, +dd: U32, +cc: U32, +comp: U32, +ff: U32, +ii: U32) -> List<&2, U32>:
  [ii, ff, comp, cc, dd, by0(hh), by1(hh), by2(hh), by3(hh), by0(ww), by1(ww), by2(ww), by3(ww)]

# the IHDR chunk judged, CRC right or wrong: png.good refuses the fields, so the chunk is refused
def ihdr.judged(
  zz: Bool,
  +ww: U32,
  +hh: U32,
  +dd: U32,
  +cc: U32,
  +comp: U32,
  +ff: U32,
  +ii: U32,
  empty: Bool,
  more: Maybe<&2, Png.Pic>,
  hg: {Png.png.good(be.back(ww), be.back(hh), dd, cc, comp, ff, ii) == False{} : Bool}
) -> {Img.decode_png.pic(Png.png.crc(Png.png.judge.at(zz, Png.tag.ihdr(), ihdr.held(ww, hh, dd, cc, comp, ff, ii),
  Png.pg.empty()), empty, more)) == None{} : Maybe<&2, Img.Raster>}:
  match zz:
    case False{}:
      {==}
    case True{}:
      Equal.cong(Bool, Maybe<&2, Img.Raster>,
        gg => Img.decode_png.pic(Png.png.crc(Png.png.ihdr.ok(gg, be.back(ww), be.back(hh), dd, cc, comp, ff, ii),
          empty, more)),
        Png.png.good(be.back(ww), be.back(hh), dd, cc, comp, ff, ii), False{}, hg)

# the walker at the CRC of that IHDR chunk, whatever the CRC bytes, the bytes after and the CRC register so far
def ihdr.at.crc(
  +c3: U32,
  +c2: U32,
  +c1: U32,
  +c0: U32,
  +rest: List<&2, U32>,
  +crc: List<&2, U32>,
  +ww: U32,
  +hh: U32,
  +dd: U32,
  +cc: U32,
  +comp: U32,
  +ff: U32,
  +ii: U32,
  hg: {Png.png.good(be.back(ww), be.back(hh), dd, cc, comp, ff, ii) == False{} : Bool}
) -> {Img.decode_png.pic(Png.png.go(c3 <> c2 <> c1 <> c0 <> rest, Png.ZCrc{}, False{}, 0, Png.tag.ihdr(), crc,
  ihdr.held(ww, hh, dd, cc, comp, ff, ii), Png.pg.empty())) == None{} : Maybe<&2, Img.Raster>}:
  ihdr.judged(U32.is_eq(Png.be.u32(c3, c2, c1, c0), Crc.crc32(List.reverse(&2, U32, crc))), ww, hh, dd, cc, comp, ff,
    ii, List.is_empty(&2, U32, rest),
    Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], Png.png.pgof(Png.png.judge(Png.be.u32(c3, c2, c1, c0), crc,
      Png.tag.ihdr(), ihdr.held(ww, hh, dd, cc, comp, ff, ii), Png.pg.empty()))),
    hg)

# a file whose IHDR png.good refuses decodes to none
def ihdr.refused(
  +ww: U32,
  +hh: U32,
  +dd: U32,
  +cc: U32,
  +comp: U32,
  +ff: U32,
  +ii: U32,
  +crc: U32,
  +rest: List<&2, U32>,
  hg: {Png.png.good(be.back(ww), be.back(hh), dd, cc, comp, ff, ii) == False{} : Bool}
) -> {Img.decode_png(Laws.spec.ihdr.file(ww, hh, dd, cc, comp, ff, ii, crc, rest)) == None{} : Maybe<&2, Img.Raster>}:
  ihdr.at.crc(by3(crc), by2(crc), by1(crc), by0(crc), rest,
    List.append(&2, U32, ihdr.held(ww, hh, dd, cc, comp, ff, ii), [82, 68, 72, 73]), ww, hh, dd, cc, comp, ff, ii, hg)

# png.good refuses a bit depth other than 8
def good.depth(
  +ww: U32,
  +hh: U32,
  +dd: U32,
  +cc: U32,
  +comp: U32,
  +ff: U32,
  +ii: U32,
  h_dd: {U32.is_eq(dd, 8) == False{} : Bool}
) -> {Png.png.good(ww, hh, dd, cc, comp, ff, ii) == False{} : Bool}:
  W5.shape_second(Bool.and(U32.is_gt(ww, 0), U32.is_gt(hh, 0)), U32.is_eq(dd, 8), Png.png.col(cc), U32.is_zero(comp),
    U32.is_zero(ff), U32.is_zero(ii), h_dd)

# png.good refuses an interlace method other than 0
def good.interlace(
  +ww: U32,
  +hh: U32,
  +dd: U32,
  +cc: U32,
  +comp: U32,
  +ff: U32,
  +ii: U32,
  h_ii: {U32.is_eq(ii, 0) == False{} : Bool}
) -> {Png.png.good(ww, hh, dd, cc, comp, ff, ii) == False{} : Bool}:
  W5.shape_sixth(Bool.and(U32.is_gt(ww, 0), U32.is_gt(hh, 0)), U32.is_eq(dd, 8), Png.png.col(cc), U32.is_zero(comp),
    U32.is_zero(ff), U32.is_zero(ii), h_ii)

# png.good refuses a colour type outside 0, 2, 3, 4 and 6
def good.colour(
  +ww: U32,
  +hh: U32,
  +dd: U32,
  +cc: U32,
  +comp: U32,
  +ff: U32,
  +ii: U32,
  h_cc: {Laws.spec.colour.ok(cc) == False{} : Bool}
) -> {Png.png.good(ww, hh, dd, cc, comp, ff, ii) == False{} : Bool}:
  W5.shape_third(Bool.and(U32.is_gt(ww, 0), U32.is_gt(hh, 0)), U32.is_eq(dd, 8), Png.png.col(cc), U32.is_zero(comp),
    U32.is_zero(ff), U32.is_zero(ii),
    W5.or_regroup(U32.is_eq(cc, 0), U32.is_eq(cc, 2), Bool.or(U32.is_eq(cc, 3), Bool.or(U32.is_eq(cc, 4),
      U32.is_eq(cc, 6))), h_cc))

def Laws.png_depth_refused(ww, hh, dd, cc, comp, ff, ii, crc, rest, h_dd):
  ihdr.refused(ww, hh, dd, cc, comp, ff, ii, crc, rest,
    good.depth(be.back(ww), be.back(hh), dd, cc, comp, ff, ii, h_dd))

def Laws.png_interlace_refused(ww, hh, dd, cc, comp, ff, ii, crc, rest, h_ii):
  ihdr.refused(ww, hh, dd, cc, comp, ff, ii, crc, rest,
    good.interlace(be.back(ww), be.back(hh), dd, cc, comp, ff, ii, h_ii))

def Laws.png_colour_refused(ww, hh, dd, cc, comp, ff, ii, crc, rest, h_cc):
  ihdr.refused(ww, hh, dd, cc, comp, ff, ii, crc, rest,
    good.colour(be.back(ww), be.back(hh), dd, cc, comp, ff, ii, h_cc))

# samples built onto an accumulator: the accumulator reversed, then the list, or none
def onto(acc: List<&2, U32>, mm: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match mm:
    case None{}:
      None{}
    case Some{ll}:
      Some{List.reverse.go(&2, U32, acc, ll)}

# one sample more on the accumulator is one sample more in front of the list
def onto.cons(
  +hd: U32,
  +acc: List<&2, U32>,
  mm: Maybe<&2, List<&2, U32>>
) -> {onto(hd <> acc, mm) == onto(acc, Laws.spec.cons(hd, mm)) : Maybe<&2, List<&2, U32>>}:
  match mm:
    case None{}:
      {==}
    case Some{_ll}:
      {==}

# onto an empty accumulator is the list itself
def onto.nil(mm: Maybe<&2, List<&2, U32>>) -> {onto([], mm) == mm : Maybe<&2, List<&2, U32>>}:
  match mm:
    case None{}:
      {==}
    case Some{_ll}:
      {==}

# px.grey without a key packs each byte as spec.grey does
def grey.acc(
  xs: List<&2, U32>,
  +acc: List<&2, U32>
) -> {Png.px.grey(xs, Png.KNone{}, acc) == Some{List.reverse.go(&2, U32, acc, Laws.spec.grey(xs))}
  : Maybe<&2, List<&2, U32>>}:
  match xs:
    case Nil{}:
      {==}
    case +gg <> tl:
      grey.acc(tl, Png.px.pack(255, gg, gg, gg) <> acc)

def Laws.png_px_grey(xs):
  grey.acc(xs, [])

# the code's key alpha is the specification's
def hit.alpha(zz: Bool) -> {Png.px.hit.at(zz) == Laws.spec.key.alpha(zz) : U32}:
  match zz:
    case True{}:
      {==}
    case False{}:
      {==}

# px.grey with a key packs each byte as spec.grey.key does
def grey.key.acc(
  xs: List<&2, U32>,
  +kk: U32,
  +acc: List<&2, U32>
) -> {Png.px.grey(xs, Png.KGrey{kk}, acc) == Some{List.reverse.go(&2, U32, acc, Laws.spec.grey.key(xs, kk))}
  : Maybe<&2, List<&2, U32>>}:
  match xs:
    case Nil{}:
      {==}
    case +gg <> +tl:
      Equal.trans(Maybe<&2, List<&2, U32>>,
        Png.px.grey(tl, Png.KGrey{kk}, Png.px.pack(Png.px.hit(gg, kk), gg, gg, gg) <> acc),
        Some{List.reverse.go(&2, U32, acc, Png.px.pack(Png.px.hit(gg, kk), gg, gg, gg) <> Laws.spec.grey.key(tl, kk))},
        Some{List.reverse.go(&2, U32, acc, Laws.spec.argb(Laws.spec.key.alpha(U32.is_eq(gg, kk)), gg, gg, gg) <>
          Laws.spec.grey.key(tl, kk))},
        grey.key.acc(tl, kk, Png.px.pack(Png.px.hit(gg, kk), gg, gg, gg) <> acc),
        Equal.cong(U32, Maybe<&2, List<&2, U32>>,
          aa => Some{List.reverse.go(&2, U32, acc, Laws.spec.argb(aa, gg, gg, gg) <> Laws.spec.grey.key(tl, kk))},
          Png.px.hit.at(U32.is_eq(gg, kk)), Laws.spec.key.alpha(U32.is_eq(gg, kk)), hit.alpha(U32.is_eq(gg, kk))))

def Laws.png_px_grey_key(xs, kk):
  grey.key.acc(xs, kk, [])

# px.ga packs each pair as spec.ga does
def ga.acc(
  xs: List<&2, U32>,
  +acc: List<&2, U32>
) -> {Png.px.ga(xs, acc) == onto(acc, Laws.spec.ga(xs)) : Maybe<&2, List<&2, U32>>}:
  match xs:
    case Nil{}:
      {==}
    case +gg <> t1:
      match t1:
        case Nil{}:
          {==}
        case +aa <> +tl:
          Equal.trans(Maybe<&2, List<&2, U32>>,
            Png.px.ga(tl, Png.px.pack(aa, gg, gg, gg) <> acc),
            onto(Png.px.pack(aa, gg, gg, gg) <> acc, Laws.spec.ga(tl)),
            onto(acc, Laws.spec.cons(Png.px.pack(aa, gg, gg, gg), Laws.spec.ga(tl))),
            ga.acc(tl, Png.px.pack(aa, gg, gg, gg) <> acc),
            onto.cons(Png.px.pack(aa, gg, gg, gg), acc, Laws.spec.ga(tl)))

def Laws.png_px_ga(xs):
  Equal.trans(Maybe<&2, List<&2, U32>>, Png.px.ga(xs, []), onto([], Laws.spec.ga(xs)), Laws.spec.ga(xs),
    ga.acc(xs, []), onto.nil(Laws.spec.ga(xs)))

# px.rgb without a key packs each triple as spec.rgb does
def rgb.acc(
  xs: List<&2, U32>,
  +acc: List<&2, U32>
) -> {Png.px.rgb(xs, Png.KNone{}, acc) == onto(acc, Laws.spec.rgb(xs)) : Maybe<&2, List<&2, U32>>}:
  match xs:
    case Nil{}:
      {==}
    case +rr <> t1:
      match t1:
        case Nil{}:
          {==}
        case +gg <> t2:
          match t2:
            case Nil{}:
              {==}
            case +bb <> +tl:
              Equal.trans(Maybe<&2, List<&2, U32>>,
                Png.px.rgb(tl, Png.KNone{}, Png.px.pack(255, rr, gg, bb) <> acc),
                onto(Png.px.pack(255, rr, gg, bb) <> acc, Laws.spec.rgb(tl)),
                onto(acc, Laws.spec.cons(Png.px.pack(255, rr, gg, bb), Laws.spec.rgb(tl))),
                rgb.acc(tl, Png.px.pack(255, rr, gg, bb) <> acc),
                onto.cons(Png.px.pack(255, rr, gg, bb), acc, Laws.spec.rgb(tl)))

def Laws.png_px_rgb(xs, _plte):
  Equal.trans(Maybe<&2, List<&2, U32>>, Png.px.rgb(xs, Png.KNone{}, []), onto([], Laws.spec.rgb(xs)),
    Laws.spec.rgb(xs), rgb.acc(xs, []), onto.nil(Laws.spec.rgb(xs)))

# the key alpha of one triple
def rgb.hit(+rr: U32, +gg: U32, +bb: U32, +kr: U32, +kg: U32, +kb: U32) -> Bool:
  Bool.and(U32.is_eq(rr, kr), Bool.and(U32.is_eq(gg, kg), U32.is_eq(bb, kb)))

# px.rgb with a key packs each triple as spec.rgb.key does
def rgb.key.acc(
  xs: List<&2, U32>,
  +kr: U32,
  +kg: U32,
  +kb: U32,
  +acc: List<&2, U32>
) -> {Png.px.rgb(xs, Png.KRgb{kr, kg, kb}, acc) == onto(acc, Laws.spec.rgb.key(xs, kr, kg, kb))
  : Maybe<&2, List<&2, U32>>}:
  match xs:
    case Nil{}:
      {==}
    case +rr <> t1:
      match t1:
        case Nil{}:
          {==}
        case +gg <> t2:
          match t2:
            case Nil{}:
              {==}
            case +bb <> +tl:
              Equal.trans(Maybe<&2, List<&2, U32>>,
                Png.px.rgb(tl, Png.KRgb{kr, kg, kb}, Png.px.pack(Png.px.rgb.hit(rr, gg, bb, kr, kg, kb), rr, gg, bb) <>
                  acc),
                onto(Png.px.pack(Png.px.rgb.hit(rr, gg, bb, kr, kg, kb), rr, gg, bb) <> acc,
                  Laws.spec.rgb.key(tl, kr, kg, kb)),
                onto(acc, Laws.spec.cons(Laws.spec.argb(Laws.spec.key.alpha(rgb.hit(rr, gg, bb, kr, kg, kb)), rr, gg,
                  bb), Laws.spec.rgb.key(tl, kr, kg, kb))),
                rgb.key.acc(tl, kr, kg, kb, Png.px.pack(Png.px.rgb.hit(rr, gg, bb, kr, kg, kb), rr, gg, bb) <> acc),
                Equal.trans(Maybe<&2, List<&2, U32>>,
                  onto(Png.px.pack(Png.px.rgb.hit(rr, gg, bb, kr, kg, kb), rr, gg, bb) <> acc,
                    Laws.spec.rgb.key(tl, kr, kg, kb)),
                  onto(Laws.spec.argb(Laws.spec.key.alpha(rgb.hit(rr, gg, bb, kr, kg, kb)), rr, gg, bb) <> acc,
                    Laws.spec.rgb.key(tl, kr, kg, kb)),
                  onto(acc, Laws.spec.cons(Laws.spec.argb(Laws.spec.key.alpha(rgb.hit(rr, gg, bb, kr, kg, kb)), rr,
                    gg, bb), Laws.spec.rgb.key(tl, kr, kg, kb))),
                  Equal.cong(U32, Maybe<&2, List<&2, U32>>,
                    aa => onto(Laws.spec.argb(aa, rr, gg, bb) <> acc, Laws.spec.rgb.key(tl, kr, kg, kb)),
                    Png.px.hit.at(rgb.hit(rr, gg, bb, kr, kg, kb)),
                    Laws.spec.key.alpha(rgb.hit(rr, gg, bb, kr, kg, kb)),
                    hit.alpha(rgb.hit(rr, gg, bb, kr, kg, kb))),
                  onto.cons(Laws.spec.argb(Laws.spec.key.alpha(rgb.hit(rr, gg, bb, kr, kg, kb)), rr, gg, bb), acc,
                    Laws.spec.rgb.key(tl, kr, kg, kb))))

def Laws.png_px_rgb_key(xs, _plte, kr, kg, kb):
  Equal.trans(Maybe<&2, List<&2, U32>>, Png.px.rgb(xs, Png.KRgb{kr, kg, kb}, []),
    onto([], Laws.spec.rgb.key(xs, kr, kg, kb)), Laws.spec.rgb.key(xs, kr, kg, kb), rgb.key.acc(xs, kr, kg, kb, []),
    onto.nil(Laws.spec.rgb.key(xs, kr, kg, kb)))

# px.rgba packs each quadruple as spec.rgba does
def rgba.acc(
  xs: List<&2, U32>,
  +acc: List<&2, U32>
) -> {Png.px.rgba(xs, acc) == onto(acc, Laws.spec.rgba(xs)) : Maybe<&2, List<&2, U32>>}:
  match xs:
    case Nil{}:
      {==}
    case +rr <> t1:
      match t1:
        case Nil{}:
          {==}
        case +gg <> t2:
          match t2:
            case Nil{}:
              {==}
            case +bb <> t3:
              match t3:
                case Nil{}:
                  {==}
                case +aa <> +tl:
                  Equal.trans(Maybe<&2, List<&2, U32>>,
                    Png.px.rgba(tl, Png.px.pack(aa, rr, gg, bb) <> acc),
                    onto(Png.px.pack(aa, rr, gg, bb) <> acc, Laws.spec.rgba(tl)),
                    onto(acc, Laws.spec.cons(Png.px.pack(aa, rr, gg, bb), Laws.spec.rgba(tl))),
                    rgba.acc(tl, Png.px.pack(aa, rr, gg, bb) <> acc),
                    onto.cons(Png.px.pack(aa, rr, gg, bb), acc, Laws.spec.rgba(tl)))

def Laws.png_px_rgba(xs, _plte):
  Equal.trans(Maybe<&2, List<&2, U32>>, Png.px.rgba(xs, []), onto([], Laws.spec.rgba(xs)), Laws.spec.rgba(xs),
    rgba.acc(xs, []), onto.nil(Laws.spec.rgba(xs)))

# PLTE holds whole entries
def triples(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case _rr <> _gg <> _bb <> tl:
      triples(tl)
    case _xs:
      False{}

# a list when the answer is true, none otherwise
def gate(zz: Bool, ll: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match zz:
    case False{}:
      None{}
    case True{}:
      Some{ll}

# pal.make builds spec.pal's entries, when PLTE holds whole entries
def pal.acc(
  xs: List<&2, U32>,
  +als: List<&2, U32>,
  +acc: List<&2, U32>
) -> {Png.pal.make(xs, als, acc) == gate(triples(xs), List.reverse.go(&2, U32, acc, Laws.spec.pal(xs, als)))
  : Maybe<&2, List<&2, U32>>}:
  match xs:
    case Nil{}:
      {==}
    case +rr <> t1:
      match t1:
        case Nil{}:
          {==}
        case +gg <> t2:
          match t2:
            case Nil{}:
              {==}
            case +bb <> tl:
              match als:
                case Nil{}:
                  pal.acc(tl, [], Png.px.pack(255, rr, gg, bb) <> acc)
                case +aa <> at:
                  pal.acc(tl, at, Png.px.pack(aa, rr, gg, bb) <> acc)

# px.at one entry further on, at the index less one
def at.prev(tl: List<&2, U32>, +ix: U32) -> Maybe<&2, U32>:
  Png.px.at(tl, U32.is_zero(U32.sub(ix, 1)), U32.sub(ix, 1))

# one step of px.at, once whether the index is zero is known
def at.step(
  +hd: U32,
  +tl: List<&2, U32>,
  +ix: U32,
  bz: Bool,
  ez: {U32.is_zero(ix) == bz : Bool},
  ih: {at.prev(tl, ix) == List.get(&2, U32, tl, U32.to_nat(U32.sub(ix, 1))) : Maybe<&2, U32>}
) -> {Png.px.at(hd <> tl, bz, ix) == List.get(&2, U32, hd <> tl, U32.to_nat(ix)) : Maybe<&2, U32>}:
  match bz:
    case True{}:
      e0 = Equal.sym(U32, ix, 0, U32L.ueq(ix, 0, ez))
      %e0 : {Some{hd} == List.get(&2, U32, hd <> tl, U32.to_nat(_)) : Maybe<&2, U32>}
      {==}
    case False{}:
      en = Equal.sym(Nat, U32.to_nat(ix), 1n+U32.to_nat(U32.sub(ix, 1)), W5.u32_dec(ix, ez))
      %en : {Png.px.at(tl, U32.is_zero(U32.sub(ix, 1)), U32.sub(ix, 1)) == List.get(&2, U32, hd <> tl, _)
        : Maybe<&2, U32>}
      ih

# px.at is the palette's entry at the index, as a Nat
def at.get(
  pal: List<&2, U32>,
  +ix: U32
) -> {Png.px.at(pal, U32.is_zero(ix), ix) == List.get(&2, U32, pal, U32.to_nat(ix)) : Maybe<&2, U32>}:
  match pal:
    case Nil{}:
      {==}
    case +hd <> +tl:
      at.step(hd, tl, ix, U32.is_zero(ix), {==}, at.get(tl, U32.sub(ix, 1)))

# what idx.acc says of the rest, with one entry more on the accumulator
def idx.ih(+tl: List<&2, U32>, +pal: List<&2, U32>, +acc: List<&2, U32>, +cc: U32) -> Type:
  {Png.px.idx(tl, pal, cc <> acc) == onto(cc <> acc, Laws.spec.idx(tl, pal)) : Maybe<&2, List<&2, U32>>}

# one index of px.idx, once its entry is known
def idx.step(
  mm: Maybe<&2, U32>,
  +tl: List<&2, U32>,
  +pal: List<&2, U32>,
  +acc: List<&2, U32>,
  ih: @cc: U32 -> idx.ih(tl, pal, acc, cc)
) -> {Png.px.use(mm, cc => Png.px.idx(tl, pal, {cc <> acc : List<&2, U32>})) ==
  onto(acc, Laws.spec.idx.at(mm, Laws.spec.idx(tl, pal))) : Maybe<&2, List<&2, U32>>}:
  match mm:
    case None{}:
      {==}
    case Some{+cc}:
      Equal.trans(Maybe<&2, List<&2, U32>>, Png.px.idx(tl, pal, cc <> acc), onto(cc <> acc, Laws.spec.idx(tl, pal)),
        onto(acc, Laws.spec.cons(cc, Laws.spec.idx(tl, pal))), ih(cc), onto.cons(cc, acc, Laws.spec.idx(tl, pal)))

# px.idx looks each index up as spec.idx does
def idx.acc(
  xs: List<&2, U32>,
  +pal: List<&2, U32>,
  +acc: List<&2, U32>
) -> {Png.px.idx(xs, pal, acc) == onto(acc, Laws.spec.idx(xs, pal)) : Maybe<&2, List<&2, U32>>}:
  match xs:
    case Nil{}:
      {==}
    case +ix <> +tl:
      Equal.trans(Maybe<&2, List<&2, U32>>,
        Png.px.use(Png.px.at(pal, U32.is_zero(ix), ix), cc => Png.px.idx(tl, pal, {cc <> acc : List<&2, U32>})),
        Png.px.use(List.get(&2, U32, pal, U32.to_nat(ix)), cc => Png.px.idx(tl, pal, {cc <> acc : List<&2, U32>})),
        onto(acc, Laws.spec.idx.at(List.get(&2, U32, pal, U32.to_nat(ix)), Laws.spec.idx(tl, pal))),
        Equal.cong(Maybe<&2, U32>, Maybe<&2, List<&2, U32>>,
          mm => Png.px.use(mm, cc => Png.px.idx(tl, pal, {cc <> acc : List<&2, U32>})),
          Png.px.at(pal, U32.is_zero(ix), ix), List.get(&2, U32, pal, U32.to_nat(ix)), at.get(pal, ix)),
        idx.step(List.get(&2, U32, pal, U32.to_nat(ix)), tl, pal, acc, cc => idx.acc(tl, pal, cc <> acc)))

# the palette passed the length check: the indices look up spec.idx
def indexed.le(
  zz: Bool,
  +xs: List<&2, U32>,
  +pal: List<&2, U32>,
  h_some: {Maybe.is_some(&2, List<&2, U32>, Png.px.indexed.at(Png.pal.gate(zz, pal), xs)) == True{} : Bool}
) -> {Png.px.indexed.at(Png.pal.gate(zz, pal), xs) == Laws.spec.idx(xs, pal) : Maybe<&2, List<&2, U32>>}:
  match zz:
    case False{}:
      Empty.absurd({None{} == Laws.spec.idx(xs, pal) : Maybe<&2, List<&2, U32>>}, U32L.false_true(h_some))
    case True{}:
      Equal.trans(Maybe<&2, List<&2, U32>>, Png.px.idx(xs, pal, []), onto([], Laws.spec.idx(xs, pal)),
        Laws.spec.idx(xs, pal), idx.acc(xs, pal, []), onto.nil(Laws.spec.idx(xs, pal)))

# the indexed samples of a palette that is some or none
def ixd(tr: Bool, xs: List<&2, U32>, trns: List<&2, U32>, pal: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  Png.px.indexed.at(Png.pal.ready(gate(tr, pal), trns), xs)

# PLTE held whole entries or not: none is ruled out, and the rest is indexed.le
def indexed.tr(
  tr: Bool,
  +xs: List<&2, U32>,
  +trns: List<&2, U32>,
  +pal: List<&2, U32>,
  h_some: {Maybe.is_some(&2, List<&2, U32>, ixd(tr, xs, trns, pal)) == True{} : Bool}
) -> {ixd(tr, xs, trns, pal) == Laws.spec.idx(xs, pal) : Maybe<&2, List<&2, U32>>}:
  match tr:
    case False{}:
      Empty.absurd({None{} == Laws.spec.idx(xs, pal) : Maybe<&2, List<&2, U32>>}, U32L.false_true(h_some))
    case True{}:
      indexed.le(Png.png.le(trns, pal), xs, pal, h_some)

def Laws.png_px_indexed(xs, plte, trns, h_some):
  +ep = {pal.acc(plte, trns, []) : {Png.pal.make(plte, trns, []) == gate(triples(plte), Laws.spec.pal(plte, trns))
    : Maybe<&2, List<&2, U32>>}}
  +hs = Equal.trans(Bool,
    Maybe.is_some(&2, List<&2, U32>, Png.px.indexed.at(Png.pal.ready(gate(triples(plte), Laws.spec.pal(plte, trns)),
      trns), xs)),
    Maybe.is_some(&2, List<&2, U32>, Png.px.indexed.at(Png.pal.ready(Png.pal.make(plte, trns, []), trns), xs)),
    True{},
    Equal.sym(Bool,
      Maybe.is_some(&2, List<&2, U32>, Png.px.indexed.at(Png.pal.ready(Png.pal.make(plte, trns, []), trns), xs)),
      Maybe.is_some(&2, List<&2, U32>, Png.px.indexed.at(Png.pal.ready(gate(triples(plte), Laws.spec.pal(plte,
        trns)), trns), xs)),
      Equal.cong(Maybe<&2, List<&2, U32>>, Bool,
        mm => Maybe.is_some(&2, List<&2, U32>, Png.px.indexed.at(Png.pal.ready(mm, trns), xs)),
        Png.pal.make(plte, trns, []), gate(triples(plte), Laws.spec.pal(plte, trns)), ep)),
    h_some)
  Equal.trans(Maybe<&2, List<&2, U32>>,
    Png.px.indexed.at(Png.pal.ready(Png.pal.make(plte, trns, []), trns), xs),
    Png.px.indexed.at(Png.pal.ready(gate(triples(plte), Laws.spec.pal(plte, trns)), trns), xs),
    Laws.spec.idx(xs, Laws.spec.pal(plte, trns)),
    Equal.cong(Maybe<&2, List<&2, U32>>, Maybe<&2, List<&2, U32>>,
      mm => Png.px.indexed.at(Png.pal.ready(mm, trns), xs),
      Png.pal.make(plte, trns, []), gate(triples(plte), Laws.spec.pal(plte, trns)), ep),
    indexed.tr(triples(plte), xs, trns, Laws.spec.pal(plte, trns), hs))

# png.pic is spec.pic
def pic.frame(
  mm: Maybe<&2, List<&2, U32>>,
  +ww: U32,
  +hh: U32
) -> {Png.png.pic(mm, ww, hh) == Laws.spec.pic(mm, ww, hh) : Maybe<&2, Png.Pic>}:
  match mm:
    case None{}:
      {==}
    case Some{_px}:
      {==}

# png.pack is px.of of the unfiltered bytes, whatever unfilter answered
def pack.frame(
  mm: Maybe<&2, List<&2, U32>>,
  +ww: U32,
  +hh: U32,
  +colour: U32,
  +plte: List<&2, U32>,
  +trns: List<&2, U32>
) -> {Png.png.pack(mm, ww, hh, colour, plte, trns) == Laws.spec.pic(Laws.spec.px.then(mm, colour, plte, trns), ww, hh)
  : Maybe<&2, Png.Pic>}:
  match mm:
    case None{}:
      {==}
    case Some{raw}:
      pic.frame(Png.px.of(colour, raw, plte, trns), ww, hh)

def Laws.png_samples_frame(raw, ww, hh, colour, plte, trns):
  pack.frame(Png.unfilter(raw, ww, hh, Png.png.bpp(colour)), ww, hh, colour, plte, trns)
