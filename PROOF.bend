# ezimg: the proofs. `bend PROOF.bend` is the gate: its first line must be
# exactly `All terms check.`
import Base
import ./LAWS.bend as Laws
import ./proof/u32.bend as U32L
import ./proof/wp2-inflate.bend as Wp2
import ./proof/wp6-raster.bend as R
import ./proof/wp3-filter.bend as Flt
import ./proof/wp1-crc.bend as Wp1
import ./proof/wp4-png-encode.bend as Wp4
import ./main.bend as Img
import ./src/png.bend as Png
import ./src/jpeg.bend as Jpeg
import ./src/crc.bend as Crc
import ./proof/wp5-png-decode.bend as W5
import ./proof/wp7-jpeg-struct.bend as W7
import ./src/jpeg_enc.bend as Jenc
import ./proof/wp8-jpeg-numeric.bend as W8
import ./proof/wp9-png-roundtrip.bend as W9
import ./src/inflate.bend as Inf
import ./proof/wp10-jpeg-finish.bend as W10
import ./proof/wp12-jpeg-huffman.bend as W12

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

# the guard's walk uses the samples only as fuel, so clearing alpha keeps it
def rows.drop(
  px: List<&2, U32>,
  zh: Bool,
  zlt: Bool,
  +ww: U32,
  +hh: U32,
  +cc: U32
) -> {Png.enc.rows(Laws.alpha.drop(px), zh, zlt, ww, hh, cc) == Png.enc.rows(px, zh, zlt, ww, hh, cc) : Bool}:
  match px zh zlt:
    case Nil{} True{} _zlt:
      {==}
    case Nil{} False{} True{}:
      {==}
    case Nil{} False{} False{}:
      {==}
    case _pp <> _rest True{} _zlt:
      {==}
    case _pp <> _rest False{} True{}:
      {==}
    case _pp <> rest False{} False{}:
      +c2 = (cc - ww : U32)
      +h2 = (hh - 1 : U32)
      rows.drop(rest, U32.is_zero(h2), U32.is_lt(c2, ww), ww, h2, c2)

# the guard with a count n and the samples as fuel
def good.at(+ww: U32, +hh: U32, +px: List<&2, U32>, +nn: U32) -> Bool:
  Bool.and(Bool.and(U32.is_gt(ww, 0), U32.is_gt(hh, 0)), Png.enc.rows(px, U32.is_zero(hh), U32.is_lt(nn, ww), ww, hh,
    nn))

# so the guard answers the same for a list and its colours
def good.drop(
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>
) -> {Png.enc.good(ww, hh, Laws.alpha.drop(px)) == Png.enc.good(ww, hh, px) : Bool}:
  +na = Png.enc.len(Laws.alpha.drop(px), 0)
  +nb = Png.enc.len(px, 0)
  Equal.trans(Bool, good.at(ww, hh, Laws.alpha.drop(px), na), good.at(ww, hh, px, na), good.at(ww, hh, px, nb),
    Equal.cong(Bool, Bool, bb => Bool.and(Bool.and(U32.is_gt(ww, 0), U32.is_gt(hh, 0)), bb),
      Png.enc.rows(Laws.alpha.drop(px), U32.is_zero(hh), U32.is_lt(na, ww), ww, hh, na),
      Png.enc.rows(px, U32.is_zero(hh), U32.is_lt(na, ww), ww, hh, na),
      rows.drop(px, U32.is_zero(hh), U32.is_lt(na, ww), ww, hh, na)),
    Equal.cong(U32, Bool, nn => good.at(ww, hh, px, nn), na, nb, len.drop(px, 0)))

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

# ---- wp7-jpeg-struct ----

# what jpeg_enc_layout says of an encoding mm of a raster of width ww and height hh
def lay.Ty(mm: Maybe<&2, List<&2, U32>>, ww: U32, hh: U32) -> Type:
  &app: List<&2, U32> -> &dq: List<&2, U32> -> &sof: List<&2, U32> -> &dc: List<&2, U32>
    -> &ac: List<&2, U32> -> &sos: List<&2, U32> -> &ent: List<&2, U32>
    -> {mm == Some{Laws.jfif.file(ww, hh, app, dq, sof, dc, ac, sos, ent)} : Maybe<&2, List<&2, U32>>}

# an accepted raster's encoding is the header, the entropy-coded bytes and EOI
def lay.pick(
  ok: Bool,
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  e_ok: {Png.enc.good(ww, hh, px) == ok : Bool},
  h_some: {Maybe.is_some(&2, List<&2, U32>, Img.encode_jpeg.pick(ok, ww, hh, Img.colours(px))) == True{} : Bool},
  h_w: {U32.is_le(ww, 65535) == True{} : Bool},
  h_h: {U32.is_le(hh, 65535) == True{} : Bool}
) -> lay.Ty(Img.encode_jpeg.pick(ok, ww, hh, Img.colours(px)), ww, hh):
  match ok:
    case False{}:
      Empty.absurd(lay.Ty(None{}, ww, hh), U32L.false_true(h_some))
    case True{}:
      +cp = Img.colours(px)
      ([1, 1, 0, 0, 1, 0, 1, 0, 0], (0 <> Jenc.encode.quant(), ([3, 1, 17, 0, 2, 17, 0, 3, 17, 0],
        (0 <> Jenc.encode.join(Jenc.encode.dccounts(), Jenc.encode.dcsyms()),
        (16 <> Jenc.encode.join(Jenc.encode.accounts(), Jenc.encode.acsyms()), ([3, 1, 0, 2, 0, 3, 0, 0, 63, 0],
        (Jenc.encode.arm(ww, hh, cp),
        Equal.cong(Bool, Maybe<&2, List<&2, U32>>, bb => Some{Jenc.encode.pick(bb, ww, hh, cp)},
          Jenc.encode.bad(ww, hh), False{}, W7.bad_of_good(ww, hh, px, e_ok, h_w, h_h)))))))))

def Laws.jpeg_enc_layout(img, h_some, h_w, h_h):
  match img:
    case Img.Raster{+ww, +hh, +px}:
      lay.pick(Png.enc.good(ww, hh, px), ww, hh, px, {==}, h_some, h_w, h_h)

# what jpeg_enc_ends says of an encoding mm
def ends.Ty(mm: Maybe<&2, List<&2, U32>>) -> Type:
  &mid: List<&2, U32>
    -> {mm == Some{List.append(&2, U32, [255, 216], List.append(&2, U32, mid, [255, 217]))} : Maybe<&2, List<&2, U32>>}

# the encoder's output opens with SOI and closes with EOI, whichever way its size test goes
def ends.bad(bad: Bool, +ww: U32, +hh: U32, +cp: List<&2, U32>) -> ends.Ty(Some{Jenc.encode.pick(bad, ww, hh, cp)}):
  match bad:
    case True{}:
      ([], {==})
    case False{}:
      (List.append(&2, U32, Jenc.encode.join(Jenc.encode.app0(), Jenc.encode.join(Jenc.encode.dqt(),
        Jenc.encode.join(Jenc.encode.sof(ww, hh), Jenc.encode.join(Jenc.encode.dht(0, Jenc.encode.dccounts(),
        Jenc.encode.dcsyms()), Jenc.encode.join(Jenc.encode.dht(16, Jenc.encode.accounts(), Jenc.encode.acsyms()),
        Jenc.encode.sos()))))), Jenc.encode.arm(ww, hh, cp)), {==})

# an accepted raster's encoding opens with SOI and closes with EOI
def ends.pick(
  ok: Bool,
  +ww: U32,
  +hh: U32,
  +cp: List<&2, U32>,
  h_some: {Maybe.is_some(&2, List<&2, U32>, Img.encode_jpeg.pick(ok, ww, hh, cp)) == True{} : Bool}
) -> ends.Ty(Img.encode_jpeg.pick(ok, ww, hh, cp)):
  match ok:
    case False{}:
      Empty.absurd(ends.Ty(None{}), U32L.false_true(h_some))
    case True{}:
      ends.bad(Jenc.encode.bad(ww, hh), ww, hh, cp)

def Laws.jpeg_enc_ends(img, h_some):
  match img:
    case Img.Raster{+ww, +hh, +px}:
      ends.pick(Png.enc.good(ww, hh, px), ww, hh, Img.colours(px), h_some)

def Laws.jpeg_gray_level(yy):
  match yy:
    case U32{w0}:
      match w0:
        case WCon{b0, WCon{b1, WCon{b2, WCon{b3, w4}}}}:
          match w4:
            case WCon{b4, WCon{b5, WCon{b6, WCon{b7, w8}}}}:
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
                                          (W7.or_byte(b0, b1, b2, b3, b4, b5, b6, b7),
                                            (W7.or_byte(b0, b1, b2, b3, b4, b5, b6, b7), {==}))

# the samples of a decoded picture, or none
def pic.px(mm: Maybe<&2, Jpeg.Pic>) -> List<&2, U32>:
  match mm:
    case None{}:
      []
    case Some{Jpeg.Pic{_ww, _hh, px}}:
      px

# what jpeg_decode_packed says of samples px
def pk.Ty(px: List<&2, U32>) -> Type:
  &gray: Bool -> &ys: List<&2, U32> -> &bs: List<&2, U32> -> &rs: List<&2, U32>
    -> {px == Laws.jpeg.pack(gray, ys, bs, rs) : List<&2, U32>}

# the code's gray packing is the law's
def grays.eq(+ys: List<&2, U32>) -> {Jpeg.decode.grays(ys) == Laws.jpeg.grays(ys) : List<&2, U32>}:
  match ys:
    case Nil{}:
      {==}
    case +yv <> rest:
      Equal.cong(List<&2, U32>, List<&2, U32>, tl => {Jpeg.gray(yv) <> tl : List<&2, U32>}, Jpeg.decode.grays(rest),
        Laws.jpeg.grays(rest), grays.eq(rest))

# the code's colour packing is the law's
def rgbs.eq(
  +ys: List<&2, U32>,
  +bs: List<&2, U32>,
  +rs: List<&2, U32>
) -> {Jpeg.decode.rgbs(ys, bs, rs) == Laws.jpeg.rgbs(ys, bs, rs) : List<&2, U32>}:
  match ys bs rs:
    case Nil{} _bs _rs:
      {==}
    case _yv <> _yt Nil{} _rs:
      {==}
    case _yv <> _yt _bv <> _bt Nil{}:
      {==}
    case +yv <> yt +bv <> bt +rv <> rt:
      Equal.cong(List<&2, U32>, List<&2, U32>, tl => {Jpeg.rgb(yv, bv, rv) <> tl : List<&2, U32>},
        Jpeg.decode.rgbs(yt, bt, rt), Laws.jpeg.rgbs(yt, bt, rt), rgbs.eq(yt, bt, rt))

# no picture has no samples
def none.pk() -> pk.Ty([]):
  (True{}, ([], ([], ([], {==}))))

# gray or colour, by the component count
def nf3.pk(
  three: Bool,
  +ww: U32,
  +hh: U32,
  yy: Array<U32>,
  cb: Array<U32>,
  cr: Array<U32>
) -> pk.Ty(pic.px(Jpeg.decode.done.nf3(three, ww, hh, yy, cb, cr))):
  match three:
    case True{}:
      +nn = U32.to_nat((ww * hh : U32))
      +ey = Jpeg.decode.points(nn, yy)
      +eb = Jpeg.decode.points(nn, cb)
      +er = Jpeg.decode.points(nn, cr)
      (False{}, (ey, (eb, (er, rgbs.eq(ey, eb, er)))))
    case False{}:
      none.pk()

# one component is gray
def nf1.pk(
  one: Bool,
  +nf: U32,
  +ww: U32,
  +hh: U32,
  yy: Array<U32>,
  cb: Array<U32>,
  cr: Array<U32>
) -> pk.Ty(pic.px(Jpeg.decode.done.nf1(one, nf, ww, hh, yy, cb, cr))):
  match one:
    case True{}:
      +ey = Jpeg.decode.points(U32.to_nat((ww * hh : U32)), yy)
      (True{}, (ey, ([], ([], grays.eq(ey)))))
    case False{}:
      nf3.pk(U32.is_eq(nf, 3), ww, hh, yy, cb, cr)

# a failed scan has no samples, and a finished one is packed by its component count
def dok.pk(
  bad: Bool,
  frame: Jpeg.Frame,
  yy: Array<U32>,
  cb: Array<U32>,
  cr: Array<U32>
) -> pk.Ty(pic.px(Jpeg.decode.done.ok(bad, frame, yy, cb, cr))):
  match bad:
    case True{}:
      none.pk()
    case False{}:
      match frame:
        case Jpeg.Frame{+ww, +hh, +nf, _ids, _hs, _vs, _tq, _hmax, _vmax}:
          nf1.pk(U32.is_eq(nf, 1), nf, ww, hh, yy, cb, cr)

# the blocks' walk ends in decode.done, whose samples are packed
def blocks.pk(
  left: Nat,
  blk: Jpeg.Blk,
  +ctrl: Jpeg.Ctrl,
  +preds: Jpeg.Preds,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ri: U32,
  yy: Array<U32>,
  cb: Array<U32>,
  cr: Array<U32>,
  +ok: U32
) -> pk.Ty(pic.px(Jpeg.decode.blocks(left, blk, ctrl, preds, frame, scan, tabs, ri, yy, cb, cr, ok))):
  match left:
    case 0n:
      match blk:
        case Jpeg.Blk{+samples, _bits, _pred, +bok}:
          dok.pk(U32.is_eq((ok * bok : U32), 0), frame,
            Jpeg.decode.paint.use(Jpeg.decode.geom(ctrl, frame, scan), U32.is_eq(Jpeg.decode.ctrl.comp(ctrl), 0),
              samples, yy),
            Jpeg.decode.paint.use(Jpeg.decode.geom(ctrl, frame, scan), U32.is_eq(Jpeg.decode.ctrl.comp(ctrl), 1),
              samples, cb),
            Jpeg.decode.paint.use(Jpeg.decode.geom(ctrl, frame, scan), U32.is_eq(Jpeg.decode.ctrl.comp(ctrl), 2),
              samples, cr))
    case 1n+pp:
      match blk:
        case Jpeg.Blk{+samples, +bits, +pred, +bok}:
          match ctrl:
            case Jpeg.Ctrl{+comp, _bi, _mx, _my, _mcu, _rst}:
              blocks.pk(pp, Jpeg.decode.block.next(bits, preds, pred, ctrl, frame, scan, tabs, ri),
                Jpeg.decode.adv.ctrl(Jpeg.decode.adv(ctrl, frame, scan, ri)),
                Jpeg.decode.preds.next(Jpeg.decode.adv.duef(Jpeg.decode.adv(ctrl, frame, scan, ri)), preds, comp, pred),
                frame, scan, tabs, ri,
                Jpeg.decode.paint.use(Jpeg.decode.geom(ctrl, frame, scan), U32.is_eq(comp, 0), samples, yy),
                Jpeg.decode.paint.use(Jpeg.decode.geom(ctrl, frame, scan), U32.is_eq(comp, 1), samples, cb),
                Jpeg.decode.paint.use(Jpeg.decode.geom(ctrl, frame, scan), U32.is_eq(comp, 2), samples, cr),
                (ok * bok : U32))

# the scan starts the blocks' walk, or has no blocks
def start.pk(
  nn: Nat,
  bits: Jpeg.Bits,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ri: U32,
  yy: Array<U32>,
  cb: Array<U32>,
  cr: Array<U32>
) -> pk.Ty(pic.px(Jpeg.decode.start(nn, bits, frame, scan, tabs, ri, yy, cb, cr))):
  match nn:
    case 0n:
      none.pk()
    case 1n+pp:
      blocks.pk(pp, Jpeg.decode.block.of(bits, 0, Jpeg.decode.pred.zero(), frame, scan, tabs),
        Jpeg.Ctrl{0, 0, 0, 0, 0, 0}, Jpeg.decode.pred.zero(), frame, scan, tabs, ri, yy, cb, cr, 1)

# an empty frame has no samples; any other starts the scan
def runn.pk(
  empty: Bool,
  +ww: U32,
  +hh: U32,
  frame: Jpeg.Frame,
  scan: Jpeg.Scan,
  tabs: Jpeg.Tabs,
  ent: List<&2, U32>,
  +ri: U32
) -> pk.Ty(pic.px(Jpeg.decode.run.n(empty, ww, hh, frame, scan, tabs, ent, ri))):
  match empty:
    case True{}:
      none.pk()
    case False{}:
      match frame:
        case Jpeg.Frame{_w, _h, _nf, _ids, +hs, +vs, _tq, +hmax, +vmax}:
          start.pk(U32.to_nat((Jpeg.decode.ceil(ww, (hmax * 8 : U32)) * Jpeg.decode.ceil(hh, (vmax * 8 : U32))
            * Jpeg.decode.blocks.sum(hs, vs, 0) : U32)), Jpeg.Bits{0, 1, 0, ent}, frame, scan, tabs, ri,
            Jpeg.decode.plane((ww * hh : U32)), Jpeg.decode.plane((ww * hh : U32)), Jpeg.decode.plane((ww * hh : U32)))

# a run's samples are packed
def run.pk(
  frame: Jpeg.Frame,
  scan: Jpeg.Scan,
  tabs: Jpeg.Tabs,
  ent: List<&2, U32>,
  +ri: U32
) -> pk.Ty(pic.px(Jpeg.decode.run(frame, scan, tabs, ent, ri))):
  match frame:
    case Jpeg.Frame{+ww, +hh, _nf, _ids, _hs, _vs, _tq, _hmax, _vmax}:
      runn.pk(Bool.or(U32.is_eq(ww, 0), U32.is_eq(hh, 0)), ww, hh, frame, scan, tabs, ent, ri)

# a walk that did not reach a baseline frame cleanly has no samples; one that did runs
def fok.pk(
  ok1: Bool,
  ok2: Bool,
  frame: Jpeg.Frame,
  scan: Jpeg.Scan,
  tabs: Jpeg.Tabs,
  ent: List<&2, U32>,
  +ri: U32
) -> pk.Ty(pic.px(Jpeg.decode.finish.ok(ok1, ok2, frame, scan, tabs, ent, ri))):
  match ok1 ok2:
    case False{} _ok2:
      none.pk()
    case True{} False{}:
      none.pk()
    case True{} True{}:
      run.pk(frame, scan, tabs, List.reverse(&2, U32, ent), ri)

# a walk that did not stop has no samples
def fph.pk(
  phase: Jpeg.Phase,
  frame: Jpeg.Frame,
  scan: Jpeg.Scan,
  tabs: Jpeg.Tabs,
  ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> pk.Ty(pic.px(Jpeg.decode.finish.ph(phase, frame, scan, tabs, ent, ri, kind, bad))):
  match phase:
    case Jpeg.Stop{}:
      fok.pk(U32.is_eq(kind, 1), U32.is_eq(bad, 0), frame, scan, tabs, ent, ri)
    case Jpeg.Seek{}:
      none.pk()
    case Jpeg.Mark{}:
      none.pk()
    case Jpeg.LenHi{_mark}:
      none.pk()
    case Jpeg.LenLo{_mark, _hi}:
      none.pk()
    case Jpeg.Pay{_mark, _left, _acc}:
      none.pk()
    case Jpeg.Ent{}:
      none.pk()
    case Jpeg.EntFF{}:
      none.pk()

# whatever the walk's state, the picture decode finishes with is packed
def finish.pk(st: Jpeg.St) -> pk.Ty(pic.px(Jpeg.decode.finish(st))):
  match st:
    case Jpeg.St{+phase, +frame, +scan, +tabs, +ent, +ri, +kind, +bad}:
      fph.pk(phase, frame, scan, tabs, ent, ri, kind, bad)

# the samples of a raster, or none
def raster.px(mr: Maybe<&2, Img.Raster>) -> List<&2, U32>:
  match mr:
    case None{}:
      []
    case Some{rr}:
      Img.pixels(rr)

# a raster decode_jpeg returns has the samples of the picture decode returns
def out.px(
  mm: Maybe<&2, Jpeg.Pic>,
  +img: Img.Raster,
  h_dec: {Img.decode_jpeg.out(mm) == Some{img} : Maybe<&2, Img.Raster>}
) -> {Img.pixels(img) == pic.px(mm) : List<&2, U32>}:
  match mm:
    case None{}:
      Empty.absurd({Img.pixels(img) == [] : List<&2, U32>}, W7.none_some(Img.Raster, img, h_dec))
    case Some{Jpeg.Pic{ww, hh, px}}:
      Equal.sym(List<&2, U32>, px, Img.pixels(img), Equal.cong(Maybe<&2, Img.Raster>, List<&2, U32>,
        mr => raster.px(mr), Some{Img.Raster{ww, hh, px}}, Some{img}, h_dec))

# samples equal to packed samples are packed
def pk.move(
  +aa: List<&2, U32>,
  +bb: List<&2, U32>,
  eab: {aa == bb : List<&2, U32>},
  pr: pk.Ty(bb)
) -> pk.Ty(aa):
  (gray, (ys, (bs, (rs, eb)))) = pr
  (gray, (ys, (bs, (rs, Equal.trans(List<&2, U32>, aa, bb, Laws.jpeg.pack(gray, ys, bs, rs), eab, eb)))))

def Laws.jpeg_decode_packed(bytes, img, h_dec):
  pk.move(Img.pixels(img), pic.px(Jpeg.decode(bytes)), out.px(Jpeg.decode(bytes), img, h_dec),
    finish.pk(Jpeg.decode.walk(bytes, Jpeg.decode.st0())))

# a sample with alpha 255 passes the alpha test
def op.one(+pp: U32, ea: {U32.shrn(pp, 24n) == 255 : U32}) -> {U32.is_eq(U32.shrn(pp, 24n), 255) == True{} : Bool}:
  Equal.cong(U32, Bool, xx => U32.is_eq(xx, 255), U32.shrn(pp, 24n), 255, ea)

# one opaque sample in front leaves the answer as it was
def op.step(
  +pp: U32,
  +rest: List<&2, U32>,
  +ok: Bool,
  ea: {U32.shrn(pp, 24n) == 255 : U32},
  ih: {Laws.all.opaque(rest, ok) == ok : Bool}
) -> {Laws.all.opaque(pp <> rest, ok) == ok : Bool}:
  Equal.trans(Bool, Laws.all.opaque(rest, Bool.and(U32.is_eq(U32.shrn(pp, 24n), 255), ok)),
    Laws.all.opaque(rest, ok), ok,
    Equal.cong(Bool, Bool, bb => Laws.all.opaque(rest, Bool.and(bb, ok)), U32.is_eq(U32.shrn(pp, 24n), 255), True{},
      op.one(pp, ea)), ih)

# gray samples are all opaque
def op.grays(+ys: List<&2, U32>, +ok: Bool) -> {Laws.all.opaque(Laws.jpeg.grays(ys), ok) == ok : Bool}:
  match ys:
    case Nil{}:
      {==}
    case +yv <> +rest:
      op.step(Jpeg.gray(yv), Laws.jpeg.grays(rest), ok, Laws.jpeg_gray_opaque(yv), op.grays(rest, ok))

# colour samples are all opaque
def op.rgbs(
  +ys: List<&2, U32>,
  +bs: List<&2, U32>,
  +rs: List<&2, U32>,
  +ok: Bool
) -> {Laws.all.opaque(Laws.jpeg.rgbs(ys, bs, rs), ok) == ok : Bool}:
  match ys bs rs:
    case Nil{} _bs _rs:
      {==}
    case _yv <> _yt Nil{} _rs:
      {==}
    case _yv <> _yt _bv <> _bt Nil{}:
      {==}
    case +yv <> +yt +bv <> +bt +rv <> +rt:
      op.step(Jpeg.rgb(yv, bv, rv), Laws.jpeg.rgbs(yt, bt, rt), ok, Laws.jpeg_rgb_opaque(yv, bv, rv),
        op.rgbs(yt, bt, rt, ok))

# packed samples are all opaque
def op.pack(
  gray: Bool,
  +ys: List<&2, U32>,
  +bs: List<&2, U32>,
  +rs: List<&2, U32>
) -> {Laws.all.opaque(Laws.jpeg.pack(gray, ys, bs, rs), True{}) == True{} : Bool}:
  match gray:
    case True{}:
      op.grays(ys, True{})
    case False{}:
      op.rgbs(ys, bs, rs, True{})

# samples that are packed are all opaque
def op.of(+px: List<&2, U32>, pr: pk.Ty(px)) -> {Laws.all.opaque(px, True{}) == True{} : Bool}:
  (gray, (ys, (bs, (rs, ep)))) = pr
  Equal.trans(Bool, Laws.all.opaque(px, True{}), Laws.all.opaque(Laws.jpeg.pack(gray, ys, bs, rs), True{}), True{},
    Equal.cong(List<&2, U32>, Bool, ll => Laws.all.opaque(ll, True{}), px, Laws.jpeg.pack(gray, ys, bs, rs), ep),
    op.pack(gray, ys, bs, rs))

def Laws.jpeg_decode_opaque(bytes, img, h_dec):
  op.of(Img.pixels(img), Laws.jpeg_decode_packed(bytes, img, h_dec))

# a segment marker starts its length field
def mk.mark(
  mk: Laws.Mk,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> {Jpeg.decode.mark(Laws.mk.byte(mk), frame, scan, tabs, ent, ri, kind, bad)
  == Jpeg.St{Jpeg.LenHi{Laws.mk.byte(mk)}, frame, scan, tabs, ent, ri, kind, bad} : Jpeg.St}:
  match mk:
    case Laws.MDht{}:
      {==}
    case Laws.MDqt{}:
      {==}
    case Laws.MSos{}:
      {==}
    case Laws.MDri{}:
      {==}
    case Laws.MCom{}:
      {==}
    case Laws.MApp0{}:
      {==}
    case Laws.MApp1{}:
      {==}
    case Laws.MApp2{}:
      {==}
    case Laws.MApp3{}:
      {==}
    case Laws.MApp4{}:
      {==}
    case Laws.MApp5{}:
      {==}
    case Laws.MApp6{}:
      {==}
    case Laws.MApp7{}:
      {==}
    case Laws.MApp8{}:
      {==}
    case Laws.MApp9{}:
      {==}
    case Laws.MApp10{}:
      {==}
    case Laws.MApp11{}:
      {==}
    case Laws.MApp12{}:
      {==}
    case Laws.MApp13{}:
      {==}
    case Laws.MApp14{}:
      {==}
    case Laws.MApp15{}:
      {==}

# a segment marker inside a scan stops the walk on an error
def mk.ent(
  mk: Laws.Mk,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> {Jpeg.decode.step.ph(Jpeg.EntFF{}, Laws.mk.byte(mk), frame, scan, tabs, ent, ri, kind, bad)
  == Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, 1} : Jpeg.St}:
  match mk:
    case Laws.MDht{}:
      {==}
    case Laws.MDqt{}:
      {==}
    case Laws.MSos{}:
      {==}
    case Laws.MDri{}:
      {==}
    case Laws.MCom{}:
      {==}
    case Laws.MApp0{}:
      {==}
    case Laws.MApp1{}:
      {==}
    case Laws.MApp2{}:
      {==}
    case Laws.MApp3{}:
      {==}
    case Laws.MApp4{}:
      {==}
    case Laws.MApp5{}:
      {==}
    case Laws.MApp6{}:
      {==}
    case Laws.MApp7{}:
      {==}
    case Laws.MApp8{}:
      {==}
    case Laws.MApp9{}:
      {==}
    case Laws.MApp10{}:
      {==}
    case Laws.MApp11{}:
      {==}
    case Laws.MApp12{}:
      {==}
    case Laws.MApp13{}:
      {==}
    case Laws.MApp14{}:
      {==}
    case Laws.MApp15{}:
      {==}

# a segment's reader leaves kind as it found it, and the walk seeking, in a scan, or stopped
def mk.disp(
  mk: Laws.Mk,
  body: List<&2, U32>,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> {W7.inv(Jpeg.decode.dispatch(Laws.mk.byte(mk), body, frame, scan, tabs, ent, ri, kind, bad))
  == U32.is_eq(kind, 0) : Bool}:
  match mk:
    case Laws.MDht{}:
      W7.dht.inv(body, True{}, False{}, 0n, 0, 0, [], [], frame, scan, tabs, ent, ri, kind, bad)
    case Laws.MDqt{}:
      W7.dqt.inv(body, True{}, 0n, 0, [], frame, scan, tabs, ent, ri, kind, bad)
    case Laws.MSos{}:
      W7.sos.inv(body, frame, tabs, ent, ri, kind, bad)
    case Laws.MDri{}:
      W7.dri.inv(body, frame, scan, tabs, ent, kind, bad)
    case Laws.MCom{}:
      {==}
    case Laws.MApp0{}:
      W7.app0.inv(body, frame, scan, tabs, ent, ri, kind, bad)
    case Laws.MApp1{}:
      {==}
    case Laws.MApp2{}:
      {==}
    case Laws.MApp3{}:
      {==}
    case Laws.MApp4{}:
      {==}
    case Laws.MApp5{}:
      {==}
    case Laws.MApp6{}:
      {==}
    case Laws.MApp7{}:
      {==}
    case Laws.MApp8{}:
      {==}
    case Laws.MApp9{}:
      {==}
    case Laws.MApp10{}:
      {==}
    case Laws.MApp11{}:
      {==}
    case Laws.MApp12{}:
      {==}
    case Laws.MApp13{}:
      {==}
    case Laws.MApp14{}:
      {==}
    case Laws.MApp15{}:
      {==}

# a frame header other than SOF0 stops the walk on an error
def sofn.mark(
  sn: Laws.Sofn,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> {Jpeg.decode.mark(Laws.sofn.byte(sn), frame, scan, tabs, ent, ri, kind, bad)
  == Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, 2, 1} : Jpeg.St}:
  match sn:
    case Laws.Sof1{}:
      {==}
    case Laws.Sof2{}:
      {==}
    case Laws.Sof3{}:
      {==}
    case Laws.Sof5{}:
      {==}
    case Laws.Sof6{}:
      {==}
    case Laws.Sof7{}:
      {==}
    case Laws.Sof9{}:
      {==}
    case Laws.Sof10{}:
      {==}
    case Laws.Sof11{}:
      {==}
    case Laws.Sof13{}:
      {==}
    case Laws.Sof14{}:
      {==}
    case Laws.Sof15{}:
      {==}

# a frame header's marker inside a scan stops the walk on an error
def sofn.ent(
  sn: Laws.Sofn,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> {Jpeg.decode.step.ph(Jpeg.EntFF{}, Laws.sofn.byte(sn), frame, scan, tabs, ent, ri, kind, bad)
  == Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, 1} : Jpeg.St}:
  match sn:
    case Laws.Sof1{}:
      {==}
    case Laws.Sof2{}:
      {==}
    case Laws.Sof3{}:
      {==}
    case Laws.Sof5{}:
      {==}
    case Laws.Sof6{}:
      {==}
    case Laws.Sof7{}:
      {==}
    case Laws.Sof9{}:
      {==}
    case Laws.Sof10{}:
      {==}
    case Laws.Sof11{}:
      {==}
    case Laws.Sof13{}:
      {==}
    case Laws.Sof14{}:
      {==}
    case Laws.Sof15{}:
      {==}

# what a segment's walk leaves: the kind it found and a phase between segments
def seg.Goal(
  ph: Jpeg.Phase,
  mk: Laws.Mk,
  hi: U32,
  lo: U32,
  body: List<&2, U32>,
  frame: Jpeg.Frame,
  scan: Jpeg.Scan,
  tabs: Jpeg.Tabs,
  ent: List<&2, U32>,
  ri: U32,
  kind: U32,
  bad: U32
) -> Type:
  {W7.inv(Jpeg.decode.walk(Laws.seg.bytes(Laws.Seg{mk, hi, lo, body}), Jpeg.St{ph, frame, scan, tabs, ent, ri, kind,
    bad})) == True{} : Bool}

# a segment walked from a state between segments that read no frame header ends in one
def seg.ph(
  ph: Jpeg.Phase,
  +mk: Laws.Mk,
  +hi: U32,
  +lo: U32,
  +body: List<&2, U32>,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32,
  h_fit: Laws.seg.Fits(hi, lo, body),
  h_inv: {W7.inv(Jpeg.St{ph, frame, scan, tabs, ent, ri, kind, bad}) == True{} : Bool}
) -> seg.Goal(ph, mk, hi, lo, body, frame, scan, tabs, ent, ri, kind, bad):
  match ph:
    case Jpeg.Seek{}:
      (e_lt, e_len) = h_fit
      +tail = {hi <> (lo <> body) : List<&2, U32>}
      +mm = Laws.mk.byte(mk)
      +lenhi = {Jpeg.St{Jpeg.LenHi{mm}, frame, scan, tabs, ent, ri, kind, bad} : Jpeg.St}
      +disp = Jpeg.decode.dispatch(mm, body, frame, scan, tabs, ent, ri, kind, bad)
      Equal.trans(Bool, W7.inv(Jpeg.decode.walk(tail, Jpeg.decode.mark(mm, frame, scan, tabs, ent, ri, kind, bad))),
        W7.inv(disp), True{},
        Equal.cong(Jpeg.St, Bool, ss => W7.inv(ss),
          Jpeg.decode.walk(tail, Jpeg.decode.mark(mm, frame, scan, tabs, ent, ri, kind, bad)), disp,
          Equal.trans(Jpeg.St, Jpeg.decode.walk(tail, Jpeg.decode.mark(mm, frame, scan, tabs, ent, ri, kind, bad)),
            Jpeg.decode.walk(tail, lenhi), disp,
            Equal.cong(Jpeg.St, Jpeg.St, ss => Jpeg.decode.walk(tail, ss),
              Jpeg.decode.mark(mm, frame, scan, tabs, ent, ri, kind, bad), lenhi,
              mk.mark(mk, frame, scan, tabs, ent, ri, kind, bad)),
            W7.seg.read(U32.is_lt(Laws.seg.len(hi, lo), 2), Laws.seg.len(hi, lo), body, mm, frame, scan, tabs, ent, ri,
              kind, bad, e_lt, e_len))),
        Equal.trans(Bool, W7.inv(disp), U32.is_eq(kind, 0), True{}, mk.disp(mk, body, frame, scan, tabs, ent, ri, kind,
          bad), h_inv))
    case Jpeg.Stop{}:
      +tail = {hi <> (lo <> body) : List<&2, U32>}
      +stop = {Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad} : Jpeg.St}
      Equal.trans(Bool, W7.inv(Jpeg.decode.walk(255 <> (Laws.mk.byte(mk) <> tail), stop)), U32.is_eq(kind, 0), True{},
        Equal.cong(Jpeg.St, Bool, ss => W7.inv(ss), Jpeg.decode.walk(255 <> (Laws.mk.byte(mk) <> tail), stop), stop,
          W7.stop.walk(255 <> (Laws.mk.byte(mk) <> tail), frame, scan, tabs, ent, ri, kind, bad)), h_inv)
    case Jpeg.Ent{}:
      +tail = {hi <> (lo <> body) : List<&2, U32>}
      +mm = Laws.mk.byte(mk)
      +stop = {Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, 1} : Jpeg.St}
      +ff = {Jpeg.St{Jpeg.EntFF{}, frame, scan, tabs, ent, ri, kind, bad} : Jpeg.St}
      Equal.trans(Bool, W7.inv(Jpeg.decode.walk(tail, Jpeg.decode.step(mm, ff))), U32.is_eq(kind, 0), True{},
        Equal.cong(Jpeg.St, Bool, ss => W7.inv(ss), Jpeg.decode.walk(tail, Jpeg.decode.step(mm, ff)), stop,
          Equal.trans(Jpeg.St, Jpeg.decode.walk(tail, Jpeg.decode.step(mm, ff)), Jpeg.decode.walk(tail, stop), stop,
            Equal.cong(Jpeg.St, Jpeg.St, ss => Jpeg.decode.walk(tail, ss), Jpeg.decode.step(mm, ff), stop,
              mk.ent(mk, frame, scan, tabs, ent, ri, kind, bad)),
            W7.stop.walk(tail, frame, scan, tabs, ent, ri, kind, 1))), h_inv)
    case Jpeg.Mark{}:
      Empty.absurd(seg.Goal(Jpeg.Mark{}, mk, hi, lo, body, frame, scan, tabs, ent, ri, kind, bad),
        U32L.false_true(h_inv))
    case Jpeg.LenHi{mark}:
      Empty.absurd(seg.Goal(Jpeg.LenHi{mark}, mk, hi, lo, body, frame, scan, tabs, ent, ri, kind, bad),
        U32L.false_true(h_inv))
    case Jpeg.LenLo{mark, mhi}:
      Empty.absurd(seg.Goal(Jpeg.LenLo{mark, mhi}, mk, hi, lo, body, frame, scan, tabs, ent, ri, kind, bad),
        U32L.false_true(h_inv))
    case Jpeg.Pay{mark, left, acc}:
      Empty.absurd(seg.Goal(Jpeg.Pay{mark, left, acc}, mk, hi, lo, body, frame, scan, tabs, ent, ri, kind, bad),
        U32L.false_true(h_inv))
    case Jpeg.EntFF{}:
      Empty.absurd(seg.Goal(Jpeg.EntFF{}, mk, hi, lo, body, frame, scan, tabs, ent, ri, kind, bad),
        U32L.false_true(h_inv))

# a segment walked from a state between segments that read no frame header ends in one
def seg.inv(
  +mk: Laws.Mk,
  +hi: U32,
  +lo: U32,
  +body: List<&2, U32>,
  st: Jpeg.St,
  h_fit: Laws.seg.Fits(hi, lo, body),
  h_inv: {W7.inv(st) == True{} : Bool}
) -> {W7.inv(Jpeg.decode.walk(Laws.seg.bytes(Laws.Seg{mk, hi, lo, body}), st)) == True{} : Bool}:
  match st:
    case Jpeg.St{ph, +frame, +scan, +tabs, +ent, +ri, +kind, +bad}:
      seg.ph(ph, mk, hi, lo, body, frame, scan, tabs, ent, ri, kind, bad, h_fit, h_inv)

# segments walked from a state between segments that read no frame header end in one
def segs.inv(
  ss: List<&2, Laws.Seg>,
  +st: Jpeg.St,
  h_fit: Laws.segs.Fit(ss),
  h_inv: {W7.inv(st) == True{} : Bool}
) -> {W7.inv(Jpeg.decode.walk(Laws.segs.bytes(ss), st)) == True{} : Bool}:
  match ss:
    case Nil{}:
      h_inv
    case Laws.Seg{+mk, +hi, +lo, +body} <> +rest:
      (h_one, h_rest) = h_fit
      +sb = Laws.seg.bytes(Laws.Seg{mk, hi, lo, body})
      +rb = Laws.segs.bytes(rest)
      Equal.trans(Bool, W7.inv(Jpeg.decode.walk(List.append(&2, U32, sb, rb), st)),
        W7.inv(Jpeg.decode.walk(rb, Jpeg.decode.walk(sb, st))), True{},
        Equal.cong(Jpeg.St, Bool, xx => W7.inv(xx), Jpeg.decode.walk(List.append(&2, U32, sb, rb), st),
          Jpeg.decode.walk(rb, Jpeg.decode.walk(sb, st)), W7.walk.app(sb, rb, st)),
        segs.inv(rest, Jpeg.decode.walk(sb, st), h_rest, seg.inv(mk, hi, lo, body, st, h_one, h_inv)))

# a walk from st over xs decodes to none
def fin.Goal(xs: List<&2, U32>, st: Jpeg.St) -> Type:
  {Jpeg.decode.finish(Jpeg.decode.walk(xs, st)) == None{} : Maybe<&2, Jpeg.Pic>}

# after the segments, a frame header other than SOF0 decodes to none
def sofn.ph(
  ph: Jpeg.Phase,
  +sn: Laws.Sofn,
  +rest: List<&2, U32>,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32,
  h_inv: {W7.inv(Jpeg.St{ph, frame, scan, tabs, ent, ri, kind, bad}) == True{} : Bool}
) -> fin.Goal(255 <> (Laws.sofn.byte(sn) <> rest), Jpeg.St{ph, frame, scan, tabs, ent, ri, kind, bad}):
  match ph:
    case Jpeg.Seek{}:
      W7.fin.after(rest, Jpeg.decode.mark(Laws.sofn.byte(sn), frame, scan, tabs, ent, ri, kind, bad), frame, scan, tabs,
        ent, ri, 2, 1, sofn.mark(sn, frame, scan, tabs, ent, ri, kind, bad), W7.fin.bad(frame, scan, tabs, ent, ri, 2))
    case Jpeg.Ent{}:
      W7.fin.after(rest, Jpeg.decode.step.ph(Jpeg.EntFF{}, Laws.sofn.byte(sn), frame, scan, tabs, ent, ri, kind, bad),
        frame, scan, tabs, ent, ri, kind, 1, sofn.ent(sn, frame, scan, tabs, ent, ri, kind, bad),
        W7.fin.bad(frame, scan, tabs, ent, ri, kind))
    case Jpeg.Stop{}:
      W7.fin.after(255 <> (Laws.sofn.byte(sn) <> rest), Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad},
        frame, scan, tabs, ent, ri, kind, bad, {==}, W7.fin.none(frame, scan, tabs, ent, ri, kind, bad, h_inv))
    case Jpeg.Mark{}:
      Empty.absurd(fin.Goal(255 <> (Laws.sofn.byte(sn) <> rest), Jpeg.St{Jpeg.Mark{}, frame, scan, tabs, ent, ri,
        kind, bad}),
        U32L.false_true(h_inv))
    case Jpeg.LenHi{mark}:
      Empty.absurd(fin.Goal(255 <> (Laws.sofn.byte(sn) <> rest), Jpeg.St{Jpeg.LenHi{mark}, frame, scan, tabs, ent, ri,
        kind, bad}),
        U32L.false_true(h_inv))
    case Jpeg.LenLo{mark, mhi}:
      Empty.absurd(fin.Goal(255 <> (Laws.sofn.byte(sn) <> rest), Jpeg.St{Jpeg.LenLo{mark, mhi}, frame, scan, tabs, ent,
        ri, kind, bad}),
        U32L.false_true(h_inv))
    case Jpeg.Pay{mark, left, acc}:
      Empty.absurd(fin.Goal(255 <> (Laws.sofn.byte(sn) <> rest), Jpeg.St{Jpeg.Pay{mark, left, acc}, frame, scan, tabs,
        ent, ri, kind, bad}),
        U32L.false_true(h_inv))
    case Jpeg.EntFF{}:
      Empty.absurd(fin.Goal(255 <> (Laws.sofn.byte(sn) <> rest), Jpeg.St{Jpeg.EntFF{}, frame, scan, tabs, ent, ri,
        kind, bad}),
        U32L.false_true(h_inv))

# after the segments, a frame header other than SOF0 decodes to none, whatever the state's phase
def sofn.st(
  +sn: Laws.Sofn,
  +rest: List<&2, U32>,
  st: Jpeg.St,
  h_inv: {W7.inv(st) == True{} : Bool}
) -> fin.Goal(255 <> (Laws.sofn.byte(sn) <> rest), st):
  match st:
    case Jpeg.St{ph, +frame, +scan, +tabs, +ent, +ri, +kind, +bad}:
      sofn.ph(ph, sn, rest, frame, scan, tabs, ent, ri, kind, bad, h_inv)

# the walk of SOI and the segments decodes to none when a walk from where they leave it does
def lead.none(
  +ss: List<&2, Laws.Seg>,
  +tail: List<&2, U32>,
  h_fit: Laws.segs.Fit(ss),
  h_tail: @st: Jpeg.St -> {W7.inv(st) == True{} : Bool} -> fin.Goal(tail, st)
) -> {Img.decode_jpeg(Laws.jpeg.lead(ss, tail)) == None{} : Maybe<&2, Img.Raster>}:
  +s1 = {Jpeg.St{Jpeg.Seek{}, Jpeg.decode.frame0(), Jpeg.decode.scan0(), Jpeg.decode.tabs0(), [], 0, 0, 0} : Jpeg.St}
  +sb = Laws.segs.bytes(ss)
  +s2 = Jpeg.decode.walk(sb, s1)
  Equal.cong(Maybe<&2, Jpeg.Pic>, Maybe<&2, Img.Raster>, mm => Img.decode_jpeg.out(mm),
    Jpeg.decode.finish(Jpeg.decode.walk(List.append(&2, U32, sb, tail), s1)), None{},
    Equal.trans(Maybe<&2, Jpeg.Pic>, Jpeg.decode.finish(Jpeg.decode.walk(List.append(&2, U32, sb, tail), s1)),
      Jpeg.decode.finish(Jpeg.decode.walk(tail, s2)), None{},
      Equal.cong(Jpeg.St, Maybe<&2, Jpeg.Pic>, xx => Jpeg.decode.finish(xx),
        Jpeg.decode.walk(List.append(&2, U32, sb, tail), s1), Jpeg.decode.walk(tail, s2), W7.walk.app(sb, tail, s1)),
      h_tail(s2, segs.inv(ss, s1, h_fit, {==}))))

def Laws.jpeg_refuse_sofn(segs, h_fit, sn, rest):
  lead.none(segs, 255 <> (Laws.sofn.byte(sn) <> rest), h_fit, st => hi => sofn.st(sn, rest, st, hi))

# an SOF0 segment whose precision is not 8, and what follows, as bytes
def prec.bytes(+hi: U32, +lo: U32, +pp: U32, +body: List<&2, U32>, +rest: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, 255 <> (192 <> (hi <> (lo <> (pp <> body)))), rest)

# after the segments, an SOF0 segment whose precision is not 8 decodes to none
def prec.ph(
  ph: Jpeg.Phase,
  +hi: U32,
  +lo: U32,
  +pp: U32,
  +body: List<&2, U32>,
  +rest: List<&2, U32>,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32,
  h_len: Laws.seg.Fits(hi, lo, pp <> body),
  h_pp: {U32.is_eq(pp, 8) == False{} : Bool},
  h_inv: {W7.inv(Jpeg.St{ph, frame, scan, tabs, ent, ri, kind, bad}) == True{} : Bool}
) -> fin.Goal(prec.bytes(hi, lo, pp, body, rest), Jpeg.St{W7.ph.norm(ph), frame, scan, tabs, ent, ri, kind, bad}):
  match ph:
    case Jpeg.Seek{}:
      (e_lt, e_len) = h_len
      +sof = {255 <> (192 <> (hi <> (lo <> (pp <> body)))) : List<&2, U32>}
      +st = {Jpeg.St{Jpeg.Seek{}, frame, scan, tabs, ent, ri, kind, bad} : Jpeg.St}
      Equal.trans(Maybe<&2, Jpeg.Pic>, Jpeg.decode.finish(Jpeg.decode.walk(List.append(&2, U32, sof, rest), st)),
        Jpeg.decode.finish(Jpeg.decode.walk(rest, Jpeg.decode.walk(sof, st))), None{},
        Equal.cong(Jpeg.St, Maybe<&2, Jpeg.Pic>, xx => Jpeg.decode.finish(xx),
          Jpeg.decode.walk(List.append(&2, U32, sof, rest), st), Jpeg.decode.walk(rest, Jpeg.decode.walk(sof, st)),
          W7.walk.app(sof, rest, st)),
        W7.fin.after(rest, Jpeg.decode.walk(sof, st), Jpeg.decode.frame0(), scan, tabs, ent, ri, kind, 1,
          Equal.trans(Jpeg.St, Jpeg.decode.walk(sof, st),
            Jpeg.decode.read.sof.p(U32.is_eq(pp, 8), body, scan, tabs, ent, ri, kind, bad),
            Jpeg.St{Jpeg.Stop{}, Jpeg.decode.frame0(), scan, tabs, ent, ri, kind, 1},
            W7.seg.read(U32.is_lt(Laws.seg.len(hi, lo), 2), Laws.seg.len(hi, lo), pp <> body, 192, frame, scan, tabs,
              ent, ri, kind, bad, e_lt, e_len),
            Equal.cong(Bool, Jpeg.St, bb => Jpeg.decode.read.sof.p(bb, body, scan, tabs, ent, ri, kind, bad),
              U32.is_eq(pp, 8), False{}, h_pp)),
          W7.fin.bad(Jpeg.decode.frame0(), scan, tabs, ent, ri, kind)))
    case Jpeg.Ent{}:
      +sof = {255 <> (192 <> (hi <> (lo <> (pp <> body)))) : List<&2, U32>}
      +st = {Jpeg.St{Jpeg.Ent{}, frame, scan, tabs, ent, ri, kind, bad} : Jpeg.St}
      Equal.trans(Maybe<&2, Jpeg.Pic>, Jpeg.decode.finish(Jpeg.decode.walk(List.append(&2, U32, sof, rest), st)),
        Jpeg.decode.finish(Jpeg.decode.walk(rest, Jpeg.decode.walk(sof, st))), None{},
        Equal.cong(Jpeg.St, Maybe<&2, Jpeg.Pic>, xx => Jpeg.decode.finish(xx),
          Jpeg.decode.walk(List.append(&2, U32, sof, rest), st), Jpeg.decode.walk(rest, Jpeg.decode.walk(sof, st)),
          W7.walk.app(sof, rest, st)),
        W7.fin.after(rest, Jpeg.decode.walk(sof, st), frame, scan, tabs, ent, ri, kind, 1,
          W7.stop.walk(hi <> (lo <> (pp <> body)), frame, scan, tabs, ent, ri, kind, 1),
          W7.fin.bad(frame, scan, tabs, ent, ri, kind)))
    case Jpeg.Stop{}:
      W7.fin.after(prec.bytes(hi, lo, pp, body, rest), Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad},
        frame, scan, tabs, ent, ri, kind, bad, {==}, W7.fin.none(frame, scan, tabs, ent, ri, kind, bad, h_inv))
    case Jpeg.Mark{}:
      W7.fin.after(prec.bytes(hi, lo, pp, body, rest), Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad},
        frame, scan, tabs, ent, ri, kind, bad, {==}, W7.fin.none(frame, scan, tabs, ent, ri, kind, bad,
          Empty.absurd({U32.is_eq(kind, 0) == True{} : Bool}, U32L.false_true(h_inv))))
    case Jpeg.LenHi{_mark}:
      W7.fin.after(prec.bytes(hi, lo, pp, body, rest), Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad},
        frame, scan, tabs, ent, ri, kind, bad, {==}, W7.fin.none(frame, scan, tabs, ent, ri, kind, bad,
          Empty.absurd({U32.is_eq(kind, 0) == True{} : Bool}, U32L.false_true(h_inv))))
    case Jpeg.LenLo{_mark, _mhi}:
      W7.fin.after(prec.bytes(hi, lo, pp, body, rest), Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad},
        frame, scan, tabs, ent, ri, kind, bad, {==}, W7.fin.none(frame, scan, tabs, ent, ri, kind, bad,
          Empty.absurd({U32.is_eq(kind, 0) == True{} : Bool}, U32L.false_true(h_inv))))
    case Jpeg.Pay{_mark, _left, _acc}:
      W7.fin.after(prec.bytes(hi, lo, pp, body, rest), Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad},
        frame, scan, tabs, ent, ri, kind, bad, {==}, W7.fin.none(frame, scan, tabs, ent, ri, kind, bad,
          Empty.absurd({U32.is_eq(kind, 0) == True{} : Bool}, U32L.false_true(h_inv))))
    case Jpeg.EntFF{}:
      W7.fin.after(prec.bytes(hi, lo, pp, body, rest), Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad},
        frame, scan, tabs, ent, ri, kind, bad, {==}, W7.fin.none(frame, scan, tabs, ent, ri, kind, bad,
          Empty.absurd({U32.is_eq(kind, 0) == True{} : Bool}, U32L.false_true(h_inv))))

# after the segments, an SOF0 segment whose precision is not 8 decodes to none, whatever the state's phase
def prec.st(
  +hi: U32,
  +lo: U32,
  +pp: U32,
  +body: List<&2, U32>,
  +rest: List<&2, U32>,
  st: Jpeg.St,
  h_len: Laws.seg.Fits(hi, lo, pp <> body),
  h_pp: {U32.is_eq(pp, 8) == False{} : Bool},
  h_inv: {W7.inv(st) == True{} : Bool}
) -> fin.Goal(prec.bytes(hi, lo, pp, body, rest), st):
  match st:
    case Jpeg.St{+ph, +frame, +scan, +tabs, +ent, +ri, +kind, +bad}:
      +xs = prec.bytes(hi, lo, pp, body, rest)
      +h_st = {h_inv : {W7.inv(Jpeg.St{ph, frame, scan, tabs, ent, ri, kind, bad}) == True{} : Bool}}
      Equal.trans(Maybe<&2, Jpeg.Pic>,
        Jpeg.decode.finish(Jpeg.decode.walk(xs, Jpeg.St{ph, frame, scan, tabs, ent, ri, kind, bad})),
        Jpeg.decode.finish(Jpeg.decode.walk(xs, Jpeg.St{W7.ph.norm(ph), frame, scan, tabs, ent, ri, kind, bad})),
        None{},
        Equal.cong(Jpeg.Phase, Maybe<&2, Jpeg.Pic>, qq => Jpeg.decode.finish(Jpeg.decode.walk(xs, Jpeg.St{qq, frame,
          scan, tabs, ent, ri, kind, bad})), ph, W7.ph.norm(ph), W7.ph.norm.eq(ph, U32L.and_left(W7.ph.ok(ph),
          U32.is_eq(kind, 0), h_st))),
        prec.ph(ph, hi, lo, pp, body, rest, frame, scan, tabs, ent, ri, kind, bad, h_len, h_pp, h_st))

def Laws.jpeg_refuse_precision(segs, h_fit, hi, lo, pp, body, h_len, h_pp, rest):
  lead.none(segs, prec.bytes(hi, lo, pp, body, rest), h_fit,
    st => hs => prec.st(hi, lo, pp, body, rest, st, h_len, h_pp, hs))

# ---- wp2-inflate ----

def Laws.inflate_stored(sz, xs, h_sz, h_by, h_n):
  Wp2.inflate_stored(sz, xs, h_sz, h_by, h_n)

def Laws.inflate_enc_zlib(xs, h_by, h_n):
  Wp2.inflate_stored(65535, xs, {==}, h_by, h_n)

# ---- wp3-filter ----

# rows_go from the law's hypotheses: the stride is not zero, and the fit is
# stated at the stride
def Laws.unfilter_filter(ft, ww, hh, bpp, rows, h_dims, h_wrap, h_rows, h_fit):
  +d_ww = U32L.and_left(U32.is_gt(ww, 0), Bool.and(U32.is_gt(hh, 0), Bool.and(U32.is_gt(bpp, 0), U32.is_le(bpp, 4))),
    h_dims)
  +d_rest = U32L.and_right(U32.is_gt(ww, 0), Bool.and(U32.is_gt(hh, 0), Bool.and(U32.is_gt(bpp, 0), U32.is_le(bpp, 4))),
    h_dims)
  +d_bpp = U32L.and_left(U32.is_gt(bpp, 0), U32.is_le(bpp, 4),
    U32L.and_right(U32.is_gt(hh, 0), Bool.and(U32.is_gt(bpp, 0), U32.is_le(bpp, 4)), d_rest))
  +en = Flt.stride_nz(ww, bpp, d_ww, d_bpp, h_wrap)
  +fit = Equal.trans(Bool, Laws.flt.fit(rows, U32.to_nat(U32.mul(ww, bpp)), True{}),
    Laws.flt.fit(rows, Nat.mul(U32.to_nat(ww), U32.to_nat(bpp)), True{}), True{},
    Equal.cong(Nat, Bool, nn => Laws.flt.fit(rows, nn, True{}), U32.to_nat(U32.mul(ww, bpp)),
      Nat.mul(U32.to_nat(ww), U32.to_nat(bpp)), h_wrap),
    h_fit)
  Flt.top.go(Png.uf.ok(ww, hh, bpp), h_dims, ft, ww, hh, bpp, rows,
    Flt.rows_go(rows, U32.to_nat(hh), h_rows, ft, bpp, U32.mul(ww, bpp), en, True{}, fit, [], []))

# ---- wp1-crc ----

def Laws.crc32_bitwise(xs):
  Wp1.crc32_ref(xs)

def Laws.png_crc_refused(pre, bad, rest, h_pre, h_bad, h_crc):
  Equal.cong(Maybe<&2, Png.Pic>, Maybe<&2, Img.Raster>, mm => Img.decode_png.pic(mm),
    Png.png.go(Laws.chunks.onto(pre, Laws.chunk.onto(bad, rest)), Png.ZLen{}, False{}, 0, 0, [], [], Png.pg.empty()),
    None{}, Wp1.walk_all(pre, bad, rest, Png.pg.empty(), h_pre, h_bad, h_crc))

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

# ---- wp4-png-encode ----

# the alpha byte with the mask first is the top byte shifted down: the 32
# bits taken apart, both sides are the same word
def alpha.mask(cc: U32) -> {Png.enc.a(cc) == U32.shrn(cc, 24n) : U32}:
  match cc:
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

# enc.opaque with the flag z is z and every sample opaque
def opaque.all(
  px: List<&2, U32>,
  zz: Bool
) -> {Png.enc.opaque(px, zz) == Bool.and(zz, Laws.all_opaque(px)) : Bool}:
  match px zz:
    case Nil{} False{}:
      {==}
    case Nil{} True{}:
      {==}
    case _cc <> _tl False{}:
      {==}
    case +cc <> tl True{}:
      +ea = Equal.cong(U32, Bool, uu => U32.is_eq(uu, 255), Png.enc.a(cc), U32.shrn(cc, 24n), alpha.mask(cc))
      Equal.trans(Bool, Png.enc.opaque(tl, U32.is_eq(Png.enc.a(cc), 255)),
        Bool.and(U32.is_eq(Png.enc.a(cc), 255), Laws.all_opaque(tl)),
        Bool.and(Laws.opaque(cc), Laws.all_opaque(tl)),
        opaque.all(tl, U32.is_eq(Png.enc.a(cc), 255)),
        Equal.cong(Bool, Bool, bb => Bool.and(bb, Laws.all_opaque(tl)), U32.is_eq(Png.enc.a(cc), 255),
          Laws.opaque(cc), ea))

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
) -> {Png.enc.ct(Png.enc.opaque(px, True{})) == Laws.colour_type(Laws.all_opaque(px)) : U32}:
  Equal.trans(U32, Png.enc.ct(Png.enc.opaque(px, True{})), Png.enc.ct(Laws.all_opaque(px)),
    Laws.colour_type(Laws.all_opaque(px)),
    Equal.cong(Bool, U32, bb => Png.enc.ct(bb), Png.enc.opaque(px, True{}), Laws.all_opaque(px),
      opaque.all(px, True{})),
    ct.same(Laws.all_opaque(px)))

# the guard passed, or h_some is false
def head.open(
  zz: Bool,
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  h_some: {Maybe.is_some(&2, List<&2, U32>, Png.enc.open(zz, ww, hh, px)) == True{} : Bool}
) -> head.some.ty(ww, hh, Laws.colour_type(Laws.all_opaque(px)), Png.enc.open(zz, ww, hh, px)):
  match zz:
    case False{}:
      Empty.absurd(head.some.ty(ww, hh, Laws.colour_type(Laws.all_opaque(px)), None{}), U32L.false_true(h_some))
    case True{}:
      +op = Png.enc.opaque(px, True{})
      +nn = Png.enc.nbytes(op, ww, hh)
      head.some(ww, hh, Png.enc.ct(op), Laws.colour_type(Laws.all_opaque(px)), Png.enc.paint(ww, hh, op, px),
        ct.law(px), head.paint.at(U32.is_gt(nn, 65535), ww, hh, op, px, nn))

def Laws.png_ihdr(ww, hh, px, h_some):
  head.open(Png.enc.good(ww, hh, px), ww, hh, px, h_some)

# U32.is_lt as Nat order
def lt.nat(
  +cc: U32,
  +ww: U32,
  zz: Bool,
  ee: {U32.is_lt(cc, ww) == zz : Bool}
) -> {Cmp.is_lt(Nat.cmp(U32.to_nat(cc), U32.to_nat(ww))) == zz : Bool}:
  Equal.trans(Bool, Cmp.is_lt(Nat.cmp(U32.to_nat(cc), U32.to_nat(ww))), U32.is_lt(cc, ww), zz,
    Equal.cong(Cmp, Bool, xx => Cmp.is_lt(xx), Nat.cmp(U32.to_nat(cc), U32.to_nat(ww)), U32.cmp(cc, ww),
      Equal.sym(Cmp, U32.cmp(cc, ww), Nat.cmp(U32.to_nat(cc), U32.to_nat(ww)), Wp4.u32_cmp_nat(cc, ww))), ee)

# U32.is_zero as Nat equality with 0
def zero.nat(
  +hh: U32,
  zz: Bool,
  ee: {U32.is_zero(hh) == zz : Bool}
) -> {Cmp.is_eq(Nat.cmp(U32.to_nat(hh), 0n)) == zz : Bool}:
  Equal.trans(Bool, Cmp.is_eq(Nat.cmp(U32.to_nat(hh), 0n)), U32.is_zero(hh), zz,
    Equal.cong(Cmp, Bool, xx => Cmp.is_eq(xx), Nat.cmp(U32.to_nat(hh), 0n), U32.cmp(hh, 0),
      Equal.sym(Cmp, U32.cmp(hh, 0), Nat.cmp(U32.to_nat(hh), 0n), Wp4.u32_cmp_nat(hh, 0))), ee)

# the count and the rows, rewritten: the question the walk answers is the same
def iseq.mul(
  +aa: Nat,
  +ab: Nat,
  +ha: Nat,
  +hb: Nat,
  +ww: Nat,
  ea: {aa == ab : Nat},
  eh: {ha == hb : Nat}
) -> {Nat.is_eq(aa, Nat.mul(ha, ww)) == Nat.is_eq(ab, Nat.mul(hb, ww)) : Bool}:
  Equal.trans(Bool, Nat.is_eq(aa, Nat.mul(ha, ww)), Nat.is_eq(ab, Nat.mul(ha, ww)), Nat.is_eq(ab, Nat.mul(hb, ww)),
    Equal.cong(Nat, Bool, xx => Nat.is_eq(xx, Nat.mul(ha, ww)), aa, ab, ea),
    Equal.cong(Nat, Bool, xx => Nat.is_eq(ab, Nat.mul(xx, ww)), ha, hb, eh))

# no rows left: the walk asks whether c is 0, and 0 rows of w is 0
def rows.done(
  +hh: U32,
  +cc: U32,
  +ww: U32,
  e_zh: {U32.is_zero(hh) == True{} : Bool}
) -> {U32.is_zero(cc) == Nat.is_eq(U32.to_nat(cc), Nat.mul(U32.to_nat(hh), U32.to_nat(ww))) : Bool}:
  +e0 = {U32L.ueq(hh, 0, e_zh) : {hh == 0 : U32}}
  Equal.trans(Bool, U32.is_zero(cc), Nat.is_eq(U32.to_nat(cc), Nat.mul(U32.to_nat(0), U32.to_nat(ww))),
    Nat.is_eq(U32.to_nat(cc), Nat.mul(U32.to_nat(hh), U32.to_nat(ww))),
    Equal.sym(Bool, Cmp.is_eq(Nat.cmp(U32.to_nat(cc), 0n)), U32.is_zero(cc), zero.nat(cc, U32.is_zero(cc), {==})),
    Equal.cong(U32, Bool, uu => Nat.is_eq(U32.to_nat(cc), Nat.mul(U32.to_nat(uu), U32.to_nat(ww))), 0, hh,
      Equal.sym(U32, hh, 0, e0)))

# a row left and fewer than w samples: never h rows of w
def rows.short.go(
  +cc: Nat,
  +hh: Nat,
  +ww: Nat,
  pr: &hp: Nat -> {hh == 1n+hp : Nat},
  hl: {Cmp.is_lt(Nat.cmp(cc, ww)) == True{} : Bool}
) -> {False{} == Nat.is_eq(cc, Nat.mul(hh, ww)) : Bool}:
  (hp, e_h) = pr
  Equal.trans(Bool, False{}, Nat.is_eq(cc, Nat.mul(1n+hp, ww)), Nat.is_eq(cc, Nat.mul(hh, ww)),
    Equal.sym(Bool, Nat.is_eq(cc, Nat.add(ww, Nat.mul(hp, ww))), False{}, Wp4.lt_add(cc, ww, Nat.mul(hp, ww), hl)),
    Equal.cong(Nat, Bool, xx => Nat.is_eq(cc, Nat.mul(xx, ww)), 1n+hp, hh, Equal.sym(Nat, hh, 1n+hp, e_h)))

# a row left and fewer than w samples
def rows.short(
  +hh: U32,
  +cc: U32,
  +ww: U32,
  e_zh: {U32.is_zero(hh) == False{} : Bool},
  e_zlt: {U32.is_lt(cc, ww) == True{} : Bool}
) -> {False{} == Nat.is_eq(U32.to_nat(cc), Nat.mul(U32.to_nat(hh), U32.to_nat(ww))) : Bool}:
  rows.short.go(U32.to_nat(cc), U32.to_nat(hh), U32.to_nat(ww),
    Wp4.nat_pos(U32.to_nat(hh), zero.nat(hh, False{}, e_zh)), lt.nat(cc, ww, True{}, e_zlt))

# the fuel ran out with c at least w: c is 0 then, and w is not
def rows.nil(
  +cc: Nat,
  +ef: Nat,
  +wp: Nat,
  hl: {Cmp.is_lt(Nat.cmp(cc, 1n+wp)) == False{} : Bool},
  e0: {0n == Nat.add(cc, ef) : Nat}
) -> Empty:
  match cc:
    case 0n:
      U32L.false_true(Equal.sym(Bool, True{}, False{}, hl))
    case 1n+(+qc):
      Wp4.zero_succ(Nat.add(qc, ef), e0)

# what the walk proves of the rest, for any slack in the fuel
def rows.ih(
  rest: List<&2, U32>,
  +ww: U32,
  +c2: U32,
  +h2: U32
) -> Type:
  @ef2: Nat -> {List.length(&2, U32, rest) == Nat.add(U32.to_nat(c2), ef2) : Nat} ->
    {Png.enc.rows(rest, U32.is_zero(h2), U32.is_lt(c2, ww), ww, h2, c2) ==
      Nat.is_eq(U32.to_nat(c2), Nat.mul(U32.to_nat(h2), U32.to_nat(ww))) : Bool}

# the fuel left after one row: w - 1 more than the count left
def rows.fuel(
  +rl: Nat,
  +wp: Nat,
  +dd: Nat,
  +ef: Nat,
  ee: {1n+rl == Nat.add(Nat.add(1n+wp, dd), ef) : Nat}
) -> {rl == Nat.add(dd, Nat.add(ef, wp)) : Nat}:
  +e1 = {Wp4.succ_inj(rl, Nat.add(Nat.add(wp, dd), ef), ee) : {rl == Nat.add(Nat.add(wp, dd), ef) : Nat}}
  Equal.trans(Nat, rl, Nat.add(Nat.add(wp, dd), ef), Nat.add(dd, Nat.add(ef, wp)), e1,
    Equal.trans(Nat, Nat.add(Nat.add(wp, dd), ef), Nat.add(Nat.add(dd, wp), ef), Nat.add(dd, Nat.add(ef, wp)),
      Equal.cong(Nat, Nat, xx => Nat.add(xx, ef), Nat.add(wp, dd), Nat.add(dd, wp), Wp4.add_comm(wp, dd)),
      Equal.trans(Nat, Nat.add(Nat.add(dd, wp), ef), Nat.add(dd, Nat.add(wp, ef)), Nat.add(dd, Nat.add(ef, wp)),
        Wp4.add_assoc(dd, wp, ef),
        Equal.cong(Nat, Nat, xx => Nat.add(dd, xx), Nat.add(wp, ef), Nat.add(ef, wp), Wp4.add_comm(wp, ef)))))

# one row taken: c is w and d, h is 1 and hp; the rest answers for d and hp
def rows.step.go(
  +rest: List<&2, U32>,
  +ww: U32,
  +hh: U32,
  +cc: U32,
  +wp: Nat,
  +ef: Nat,
  e_w: {U32.to_nat(ww) == 1n+wp : Nat},
  e_f: {1n+List.length(&2, U32, rest) == Nat.add(U32.to_nat(cc), ef) : Nat},
  pd: &dd: Nat -> {U32.to_nat(cc) == Nat.add(U32.to_nat(ww), dd) : Nat},
  ph: &hp: Nat -> {U32.to_nat(hh) == 1n+hp : Nat},
  ih: rows.ih(rest, ww, (cc - ww : U32), (hh - 1 : U32))
) -> {Png.enc.rows(rest, U32.is_zero((hh - 1 : U32)), U32.is_lt((cc - ww : U32), ww), ww, (hh - 1 : U32),
  (cc - ww : U32)) == Nat.is_eq(U32.to_nat(cc), Nat.mul(U32.to_nat(hh), U32.to_nat(ww))) : Bool}:
  (+dd, e_c0) = pd
  (+hp, e_h0) = ph
  +e_c = {e_c0 : {U32.to_nat(cc) == Nat.add(U32.to_nat(ww), dd) : Nat}}
  +e_h = {e_h0 : {U32.to_nat(hh) == 1n+hp : Nat}}
  +c2 = (cc - ww : U32)
  +h2 = (hh - 1 : U32)
  +e_c2 = {Wp4.u32_sub_nat(cc, ww, dd, e_c) : {U32.to_nat(c2) == dd : Nat}}
  +e_h2 = {Wp4.u32_sub_nat(hh, 1, hp, e_h) : {U32.to_nat(h2) == hp : Nat}}
  +vw = U32.to_nat(ww)
  +e_cw = {Equal.trans(Nat, U32.to_nat(cc), Nat.add(vw, dd), Nat.add(1n+wp, dd), e_c,
    Equal.cong(Nat, Nat, xx => Nat.add(xx, dd), vw, 1n+wp, e_w)) : {U32.to_nat(cc) == Nat.add(1n+wp, dd) : Nat}}
  +e_rl = {rows.fuel(List.length(&2, U32, rest), wp, dd, ef,
    Equal.trans(Nat, 1n+List.length(&2, U32, rest), Nat.add(U32.to_nat(cc), ef), Nat.add(Nat.add(1n+wp, dd), ef), e_f,
      Equal.cong(Nat, Nat, xx => Nat.add(xx, ef), U32.to_nat(cc), Nat.add(1n+wp, dd), e_cw))) :
    {List.length(&2, U32, rest) == Nat.add(dd, Nat.add(ef, wp)) : Nat}}
  +e_f2 = {Equal.trans(Nat, List.length(&2, U32, rest), Nat.add(dd, Nat.add(ef, wp)),
    Nat.add(U32.to_nat(c2), Nat.add(ef, wp)), e_rl,
    Equal.cong(Nat, Nat, xx => Nat.add(xx, Nat.add(ef, wp)), dd, U32.to_nat(c2),
      Equal.sym(Nat, U32.to_nat(c2), dd, e_c2))) :
    {List.length(&2, U32, rest) == Nat.add(U32.to_nat(c2), Nat.add(ef, wp)) : Nat}}
  +e_rest = {ih(Nat.add(ef, wp), e_f2) :
    {Png.enc.rows(rest, U32.is_zero(h2), U32.is_lt(c2, ww), ww, h2, c2) ==
      Nat.is_eq(U32.to_nat(c2), Nat.mul(U32.to_nat(h2), vw)) : Bool}}
  Equal.trans(Bool, Png.enc.rows(rest, U32.is_zero(h2), U32.is_lt(c2, ww), ww, h2, c2),
    Nat.is_eq(dd, Nat.mul(hp, vw)), Nat.is_eq(U32.to_nat(cc), Nat.mul(U32.to_nat(hh), vw)),
    Equal.trans(Bool, Png.enc.rows(rest, U32.is_zero(h2), U32.is_lt(c2, ww), ww, h2, c2),
      Nat.is_eq(U32.to_nat(c2), Nat.mul(U32.to_nat(h2), vw)), Nat.is_eq(dd, Nat.mul(hp, vw)), e_rest,
      iseq.mul(U32.to_nat(c2), dd, U32.to_nat(h2), hp, vw, e_c2, e_h2)),
    Equal.trans(Bool, Nat.is_eq(dd, Nat.mul(hp, vw)), Nat.is_eq(Nat.add(vw, dd), Nat.mul(1n+hp, vw)),
      Nat.is_eq(U32.to_nat(cc), Nat.mul(U32.to_nat(hh), vw)),
      Equal.sym(Bool, Nat.is_eq(Nat.add(vw, dd), Nat.add(vw, Nat.mul(hp, vw))), Nat.is_eq(dd, Nat.mul(hp, vw)),
        Equal.cong(Cmp, Bool, xx => Cmp.is_eq(xx), Nat.cmp(Nat.add(vw, dd), Nat.add(vw, Nat.mul(hp, vw))),
          Nat.cmp(dd, Nat.mul(hp, vw)), Wp4.cmp_add(vw, dd, Nat.mul(hp, vw)))),
      iseq.mul(Nat.add(vw, dd), U32.to_nat(cc), 1n+hp, U32.to_nat(hh), vw,
        Equal.sym(Nat, U32.to_nat(cc), Nat.add(vw, dd), e_c), Equal.sym(Nat, U32.to_nat(hh), 1n+hp, e_h))))

# the walk over the samples answers whether c is h rows of w, for w above 0
# and at most as many as there is fuel for
def rows.nat(
  fuel: List<&2, U32>,
  zh: Bool,
  zlt: Bool,
  +ww: U32,
  +hh: U32,
  +cc: U32,
  +wp: Nat,
  +ef: Nat,
  +e_zh: {U32.is_zero(hh) == zh : Bool},
  +e_zlt: {U32.is_lt(cc, ww) == zlt : Bool},
  +e_w: {U32.to_nat(ww) == 1n+wp : Nat},
  +e_f: {List.length(&2, U32, fuel) == Nat.add(U32.to_nat(cc), ef) : Nat}
) -> {Png.enc.rows(fuel, zh, zlt, ww, hh, cc) ==
  Nat.is_eq(U32.to_nat(cc), Nat.mul(U32.to_nat(hh), U32.to_nat(ww))) : Bool}:
  match fuel zh zlt:
    case Nil{} True{} _zlt:
      rows.done(hh, cc, ww, e_zh)
    case Nil{} False{} True{}:
      rows.short(hh, cc, ww, e_zh, e_zlt)
    case _px <> _rest True{} _zlt:
      rows.done(hh, cc, ww, e_zh)
    case _px <> _rest False{} True{}:
      rows.short(hh, cc, ww, e_zh, e_zlt)
    case Nil{} False{} False{}:
      +hl = Equal.trans(Bool, Cmp.is_lt(Nat.cmp(U32.to_nat(cc), 1n+wp)),
        Cmp.is_lt(Nat.cmp(U32.to_nat(cc), U32.to_nat(ww))), False{},
        Equal.cong(Nat, Bool, xx => Cmp.is_lt(Nat.cmp(U32.to_nat(cc), xx)), 1n+wp, U32.to_nat(ww),
          Equal.sym(Nat, U32.to_nat(ww), 1n+wp, e_w)), lt.nat(cc, ww, False{}, e_zlt))
      Empty.absurd({False{} == Nat.is_eq(U32.to_nat(cc), Nat.mul(U32.to_nat(hh), U32.to_nat(ww))) : Bool},
        rows.nil(U32.to_nat(cc), ef, wp, hl, e_f))
    case _px <> +rest False{} False{}:
      rows.step.go(rest, ww, hh, cc, wp, ef, e_w, e_f,
        Wp4.ge_split(U32.to_nat(cc), U32.to_nat(ww), lt.nat(cc, ww, False{}, e_zlt)),
        Wp4.nat_pos(U32.to_nat(hh), zero.nat(hh, False{}, e_zh)),
        ef2 => e2 => rows.nat(rest, U32.is_zero((hh - 1 : U32)), U32.is_lt((cc - ww : U32), ww), ww, (hh - 1 : U32),
          (cc - ww : U32), wp, ef2, {==}, {==}, e_w, e2))

# the count enc.len keeps, below 2^32, is the start and the samples
def len.nat(
  px: List<&2, U32>,
  +nn: U32,
  +hb: {Laws.below(32n, Nat.add(U32.to_nat(nn), List.length(&2, U32, px))) == True{} : Bool}
) -> {U32.to_nat(Png.enc.len(px, nn)) == Nat.add(U32.to_nat(nn), List.length(&2, U32, px)) : Nat}:
  match px:
    case Nil{}:
      Equal.sym(Nat, Nat.add(U32.to_nat(nn), 0n), U32.to_nat(nn), Wp4.add_zero(U32.to_nat(nn)))
    case _pp <> +tl:
      +vn = U32.to_nat(nn)
      +lt = List.length(&2, U32, tl)
      +es = {Wp4.add_succ(vn, lt) : {Nat.add(vn, 1n+lt) == 1n+Nat.add(vn, lt) : Nat}}
      +hb1 = {Equal.trans(Bool, Laws.below(32n, 1n+Nat.add(vn, lt)), Laws.below(32n, Nat.add(vn, 1n+lt)), True{},
        Equal.cong(Nat, Bool, xx => Laws.below(32n, xx), 1n+Nat.add(vn, lt), Nat.add(vn, 1n+lt),
          Equal.sym(Nat, Nat.add(vn, 1n+lt), 1n+Nat.add(vn, lt), es)), hb) :
        {Laws.below(32n, 1n+Nat.add(vn, lt)) == True{} : Bool}}
      +n1 = (nn + 1 : U32)
      +ei = {Wp4.u32_inc_nat(nn, Wp4.below_mono(32n, 1n+vn, lt, hb1)) : {U32.to_nat(n1) == 1n+vn : Nat}}
      +hb2 = {Equal.trans(Bool, Laws.below(32n, Nat.add(U32.to_nat(n1), lt)), Laws.below(32n, 1n+Nat.add(vn, lt)),
        True{},
        Equal.cong(Nat, Bool, xx => Laws.below(32n, Nat.add(xx, lt)), U32.to_nat(n1), 1n+vn, ei), hb1) :
        {Laws.below(32n, Nat.add(U32.to_nat(n1), lt)) == True{} : Bool}}
      Equal.trans(Nat, U32.to_nat(Png.enc.len(tl, n1)), Nat.add(U32.to_nat(n1), lt), Nat.add(vn, 1n+lt),
        len.nat(tl, n1, hb2),
        Equal.trans(Nat, Nat.add(U32.to_nat(n1), lt), 1n+Nat.add(vn, lt), Nat.add(vn, 1n+lt),
          Equal.cong(Nat, Nat, xx => Nat.add(xx, lt), U32.to_nat(n1), 1n+vn, ei),
          Equal.sym(Nat, Nat.add(vn, 1n+lt), 1n+Nat.add(vn, lt), es)))

# anything and false is false
def and.false(bb: Bool) -> {False{} == Bool.and(bb, False{}) : Bool}:
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# is_eq(L, A) is A below 2^32 and is_eq(L, A), when L is below 2^32
def fits.and(
  zz: Bool,
  +ll: Nat,
  +aa: Nat,
  ez: {Nat.is_eq(ll, aa) == zz : Bool},
  hb: {Laws.below(32n, ll) == True{} : Bool}
) -> {zz == Bool.and(Laws.below(32n, aa), zz) : Bool}:
  match zz:
    case True{}:
      +eb = {Equal.trans(Bool, Laws.below(32n, aa), Laws.below(32n, ll), True{},
        Equal.cong(Nat, Bool, xx => Laws.below(32n, xx), aa, ll, Equal.sym(Nat, ll, aa, Wp4.nat_eq_true(ll, aa, ez))),
        hb) : {Laws.below(32n, aa) == True{} : Bool}}
      Equal.cong(Bool, Bool, bb => Bool.and(bb, True{}), True{}, Laws.below(32n, aa),
        Equal.sym(Bool, Laws.below(32n, aa), True{}, eb))
    case False{}:
      and.false(Laws.below(32n, aa))

# not x true: x false
def not.true(xx: Bool, ee: {Bool.not(xx) == True{} : Bool}) -> {xx == False{} : Bool}:
  match xx:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, U32L.false_true(ee))

# the two side tests agree, and the rest agrees when the width is above 0
def good.pick(
  nw: Bool,
  nh: Bool,
  +rr: Bool,
  +ss: Bool,
  fn: {nw == True{} : Bool} -> {rr == ss : Bool}
) -> {Bool.and(Bool.and(nw, nh), rr) == Bool.and(Bool.and(nw, nh), ss) : Bool}:
  match nw nh:
    case True{} True{}:
      fn({==})
    case True{} False{}:
      {==}
    case False{} _nh:
      {==}

# a U32 above 0 is one whose value is not 0
def gt.nat(+ww: U32) -> {U32.is_gt(ww, 0) == Bool.not(Nat.is_eq(U32.to_nat(ww), 0n)) : Bool}:
  Equal.trans(Bool, U32.is_gt(ww, 0), Cmp.is_gt(Nat.cmp(U32.to_nat(ww), 0n)), Bool.not(Nat.is_eq(U32.to_nat(ww), 0n)),
    Equal.cong(Cmp, Bool, xx => Cmp.is_gt(xx), U32.cmp(ww, 0), Nat.cmp(U32.to_nat(ww), 0n), Wp4.u32_cmp_nat(ww, 0)),
    Wp4.gt_zero(U32.to_nat(ww)))

# with the width 1 and wp: the walk, the count, and the law's test agree
def good.rows(
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  +hb: {Laws.below(32n, List.length(&2, U32, px)) == True{} : Bool},
  pw: &wp: Nat -> {U32.to_nat(ww) == 1n+wp : Nat}
) -> {Png.enc.rows(px, U32.is_zero(hh), U32.is_lt(Png.enc.len(px, 0), ww), ww, hh, Png.enc.len(px, 0)) ==
  Bool.and(Laws.below(32n, Nat.mul(U32.to_nat(hh), U32.to_nat(ww))),
    Nat.is_eq(List.length(&2, U32, px), Nat.mul(U32.to_nat(hh), U32.to_nat(ww)))) : Bool}:
  (+wp, e_w0) = pw
  +e_w = {e_w0 : {U32.to_nat(ww) == 1n+wp : Nat}}
  +nn = Png.enc.len(px, 0)
  +ll = List.length(&2, U32, px)
  +aa = Nat.mul(U32.to_nat(hh), U32.to_nat(ww))
  +e_n = {len.nat(px, 0, hb) : {U32.to_nat(nn) == ll : Nat}}
  +e_f = {Equal.trans(Nat, ll, U32.to_nat(nn), Nat.add(U32.to_nat(nn), 0n), Equal.sym(Nat, U32.to_nat(nn), ll, e_n),
    Equal.sym(Nat, Nat.add(U32.to_nat(nn), 0n), U32.to_nat(nn), Wp4.add_zero(U32.to_nat(nn)))) :
    {ll == Nat.add(U32.to_nat(nn), 0n) : Nat}}
  Equal.trans(Bool, Png.enc.rows(px, U32.is_zero(hh), U32.is_lt(nn, ww), ww, hh, nn), Nat.is_eq(ll, aa),
    Bool.and(Laws.below(32n, aa), Nat.is_eq(ll, aa)),
    Equal.trans(Bool, Png.enc.rows(px, U32.is_zero(hh), U32.is_lt(nn, ww), ww, hh, nn),
      Nat.is_eq(U32.to_nat(nn), aa), Nat.is_eq(ll, aa),
      rows.nat(px, U32.is_zero(hh), U32.is_lt(nn, ww), ww, hh, nn, wp, 0n, {==}, {==}, e_w, e_f),
      Equal.cong(Nat, Bool, xx => Nat.is_eq(xx, aa), U32.to_nat(nn), ll, e_n)),
    fits.and(Nat.is_eq(ll, aa), ll, aa, {==}, hb))

# for fewer than 2^32 samples, the guard is the law's test
def good.nat(
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  +hb: {Laws.below(32n, List.length(&2, U32, px)) == True{} : Bool}
) -> {Png.enc.good(ww, hh, px) == Laws.png_ok(ww, hh, px) : Bool}:
  +nn = Png.enc.len(px, 0)
  +rr = Png.enc.rows(px, U32.is_zero(hh), U32.is_lt(nn, ww), ww, hh, nn)
  +nw = Bool.not(Nat.is_eq(U32.to_nat(ww), 0n))
  +nh = Bool.not(Nat.is_eq(U32.to_nat(hh), 0n))
  +aa = Nat.mul(U32.to_nat(hh), U32.to_nat(ww))
  +ss = Bool.and(Laws.below(32n, aa), Nat.is_eq(List.length(&2, U32, px), aa))
  Equal.trans(Bool, Bool.and(Bool.and(U32.is_gt(ww, 0), U32.is_gt(hh, 0)), rr), Bool.and(Bool.and(nw, nh), rr),
    Bool.and(Bool.and(nw, nh), ss),
    Equal.trans(Bool, Bool.and(Bool.and(U32.is_gt(ww, 0), U32.is_gt(hh, 0)), rr),
      Bool.and(Bool.and(nw, U32.is_gt(hh, 0)), rr), Bool.and(Bool.and(nw, nh), rr),
      Equal.cong(Bool, Bool, bb => Bool.and(Bool.and(bb, U32.is_gt(hh, 0)), rr), U32.is_gt(ww, 0), nw, gt.nat(ww)),
      Equal.cong(Bool, Bool, bb => Bool.and(Bool.and(nw, bb), rr), U32.is_gt(hh, 0), nh, gt.nat(hh))),
    good.pick(nw, nh, rr, ss, en => good.rows(ww, hh, px, hb, Wp4.nat_pos(U32.to_nat(ww),
      not.true(Nat.is_eq(U32.to_nat(ww), 0n), en)))))

# enc.open is none exactly when its guard is false
def open.none(
  zz: Bool,
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>
) -> {Maybe.is_none(&2, List<&2, U32>, Png.enc.open(zz, ww, hh, px)) == Bool.not(zz) : Bool}:
  match zz:
    case True{}:
      {==}
    case False{}:
      {==}

# enc.open with its guard true is some
def open.some(
  zz: Bool,
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  ez: {zz == True{} : Bool}
) -> {Maybe.is_some(&2, List<&2, U32>, Png.enc.open(zz, ww, hh, px)) == True{} : Bool}:
  match zz:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, U32L.false_true(ez))

def Laws.png_refuses(ww, hh, px, h_len):
  Equal.trans(Bool, Maybe.is_none(&2, List<&2, U32>, Png.enc.open(Png.enc.good(ww, hh, px), ww, hh, px)),
    Bool.not(Png.enc.good(ww, hh, px)), Bool.not(Laws.png_ok(ww, hh, px)),
    open.none(Png.enc.good(ww, hh, px), ww, hh, px),
    Equal.cong(Bool, Bool, bb => Bool.not(bb), Png.enc.good(ww, hh, px), Laws.png_ok(ww, hh, px),
      good.nat(ww, hh, px, h_len)))

def Laws.png_encodes(ww, hh, px, h_ok):
  +aa = Nat.mul(U32.to_nat(hh), U32.to_nat(ww))
  +ll = List.length(&2, U32, px)
  +nw = Bool.not(Nat.is_eq(U32.to_nat(ww), 0n))
  +nh = Bool.not(Nat.is_eq(U32.to_nat(hh), 0n))
  +ok = {h_ok : {Laws.png_ok(ww, hh, px) == True{} : Bool}}
  +e_r = {U32L.and_right(Bool.and(nw, nh), Bool.and(Laws.below(32n, aa), Nat.is_eq(ll, aa)), ok) :
    {Bool.and(Laws.below(32n, aa), Nat.is_eq(ll, aa)) == True{} : Bool}}
  +e_la = {Wp4.nat_eq_true(ll, aa, U32L.and_right(Laws.below(32n, aa), Nat.is_eq(ll, aa), e_r)) : {ll == aa : Nat}}
  +hb = {Equal.trans(Bool, Laws.below(32n, ll), Laws.below(32n, aa), True{},
    Equal.cong(Nat, Bool, xx => Laws.below(32n, xx), ll, aa, e_la),
    U32L.and_left(Laws.below(32n, aa), Nat.is_eq(ll, aa), e_r)) : {Laws.below(32n, ll) == True{} : Bool}}
  open.some(Png.enc.good(ww, hh, px), ww, hh, px,
    Equal.trans(Bool, Png.enc.good(ww, hh, px), Laws.png_ok(ww, hh, px), True{}, good.nat(ww, hh, px, hb), ok))

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

# no Cb sample: no colour, whatever the Y and Cr samples
def w8.rgb3.nb(aa: Maybe<&2, U32>, cc: Maybe<&2, U32>) -> {None{} == Laws.jpg.rgb3(aa, None{}, cc) : Maybe<&2, U32>}:
  match aa:
    case None{}:
      {==}
    case Some{_av}:
      {==}

# no Cr sample: no colour, whatever the Y and Cb samples
def w8.rgb3.nr(aa: Maybe<&2, U32>, bb: Maybe<&2, U32>) -> {None{} == Laws.jpg.rgb3(aa, bb, None{}) : Maybe<&2, U32>}:
  match aa bb:
    case None{} _bb:
      {==}
    case Some{_av} None{}:
      {==}
    case Some{_av} Some{_bv}:
      {==}

# jpeg_rgbs_at by induction on the three planes together
def w8.rgbs.at(
  +ys: List<&2, U32>,
  +bs: List<&2, U32>,
  +rs: List<&2, U32>,
  +kk: Nat
) -> {List.get(&2, U32, Jpeg.decode.rgbs(ys, bs, rs), kk) ==
  Laws.jpg.rgb3(List.get(&2, U32, ys, kk), List.get(&2, U32, bs, kk), List.get(&2, U32, rs, kk)) : Maybe<&2, U32>}:
  match ys bs rs kk:
    case Nil{} _bs _rs _kk:
      {==}
    case _yv <> _yt Nil{} _rs 0n:
      {==}
    case _yv <> yt Nil{} rs 1n+pp:
      w8.rgb3.nb(List.get(&2, U32, yt, pp), List.get(&2, U32, rs, 1n+pp))
    case _yv <> _yt _bv <> _bt Nil{} 0n:
      {==}
    case _yv <> yt _bv <> bt Nil{} 1n+pp:
      w8.rgb3.nr(List.get(&2, U32, yt, pp), List.get(&2, U32, bt, pp))
    case _yv <> _yt _bv <> _bt _rv <> _rt 0n:
      {==}
    case _yv <> yt _bv <> bt _rv <> rt 1n+pp:
      w8.rgbs.at(yt, bt, rt, pp)

def Laws.jpeg_rgbs_at(ys, bs, rs, kk):
  w8.rgbs.at(ys, bs, rs, kk)

# the absent test's first conjunct: this element is not want
def w8.idx.ne(
  bb: Bool,
  +rest: Bool,
  h_new: {Bool.and(Bool.not(bb), rest) == True{} : Bool}
) -> {bb == False{} : Bool}:
  match bb:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, U32L.false_true(h_new))

# the absent test's second conjunct: no later element is want
def w8.idx.rest(
  bb: Bool,
  +rest: Bool,
  h_new: {Bool.and(Bool.not(bb), rest) == True{} : Bool}
) -> {rest == True{} : Bool}:
  match bb:
    case False{}:
      h_new
    case True{}:
      Empty.absurd({rest == True{} : Bool}, U32L.false_true(h_new))

# decode.index after the element that was want is the count so far
def w8.idx.seen(
  xs: List<&2, U32>,
  +want: U32,
  +ii: U32
) -> {Jpeg.decode.index(xs, True{}, want, ii) == ii : U32}:
  match xs:
    case Nil{}:
      {==}
    case _xx <> _rest:
      {==}

# decode.index from ii over pre, then want: ii plus pre's length
def w8.idx.go(
  +pre: List<&2, U32>,
  +want: U32,
  +post: List<&2, U32>,
  +ii: U32,
  +h_new: {Laws.jpg.absent(pre, want) == True{} : Bool}
) -> {Jpeg.decode.index(List.append(&2, U32, pre, want <> post), False{}, want, ii) == Laws.jpg.count(pre, ii) : U32}:
  match pre:
    case Nil{}:
      Equal.trans(U32, Jpeg.decode.index(post, U32.is_eq(want, want), want,
        Jpeg.decode.index.add(U32.is_eq(want, want), ii)), Jpeg.decode.index(post, True{}, want,
        Jpeg.decode.index.add(True{}, ii)), ii,
        Equal.cong(Bool, U32, bb => Jpeg.decode.index(post, bb, want, Jpeg.decode.index.add(bb, ii)),
          U32.is_eq(want, want), True{}, U32L.u32_eq_refl(want)),
        w8.idx.seen(post, want, ii))
    case +xx <> rest:
      Equal.trans(U32, Jpeg.decode.index(List.append(&2, U32, rest, want <> post), U32.is_eq(xx, want), want,
        Jpeg.decode.index.add(U32.is_eq(xx, want), ii)), Jpeg.decode.index(List.append(&2, U32, rest, want <> post),
        False{}, want, Jpeg.decode.index.add(False{}, ii)), Laws.jpg.count(rest, (ii + 1 : U32)),
        Equal.cong(Bool, U32, bb => Jpeg.decode.index(List.append(&2, U32, rest, want <> post), bb, want,
          Jpeg.decode.index.add(bb, ii)), U32.is_eq(xx, want), False{},
          w8.idx.ne(U32.is_eq(xx, want), Laws.jpg.absent(rest, want), h_new)),
        w8.idx.go(rest, want, post, (ii + 1 : U32),
          w8.idx.rest(U32.is_eq(xx, want), Laws.jpg.absent(rest, want), h_new)))

def Laws.jpeg_comp_index(pre, want, post, h_new):
  w8.idx.go(pre, want, post, 0, h_new)

# one step of the walk, from where it tests for more data units
def w8.walk.more(
  more: Bool,
  +comp: U32,
  +bi: U32,
  +mx: U32,
  +my: U32,
  +mcu: U32,
  +rst: U32,
  +ww: U32,
  +hmax: U32,
  +ns: U32,
  +ri: U32,
  h_more: {more == True{} : Bool}
) -> {Jpeg.decode.adv.bi(more, comp, bi, mx, my, mcu, rst, ww, hmax, ns, ri) ==
  Jpeg.Adv{Jpeg.Ctrl{comp, (bi + 1 : U32), mx, my, mcu, rst}, 0, rst} : Jpeg.Adv}:
  match more:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Jpeg.decode.adv.bi(False{}, comp, bi, mx, my, mcu, rst, ww, hmax, ns, ri) ==
        Jpeg.Adv{Jpeg.Ctrl{comp, (bi + 1 : U32), mx, my, mcu, rst}, 0, rst} : Jpeg.Adv}, U32L.false_true(h_more))

def Laws.jpeg_walk_unit(
  comp,
  bi,
  mx,
  my,
  mcu,
  rst,
  ww,
  _hh,
  _nf,
  ids,
  hs,
  vs,
  _tq,
  hmax,
  _vmax,
  ns,
  sids,
  _td,
  _ta,
  _ss,
  _se,
  _ah,
  ri,
  h_more
):
  w8.walk.more(U32.is_lt((bi + 1 : U32), Laws.jpg.units(comp, sids, ids, hs, vs)), comp, bi, mx, my, mcu, rst, ww,
    hmax, ns, ri, h_more)

# the step after a component's last unit, once it has found more components: unit 0 of the next one
def w8.walk.next(
  next: Bool,
  +comp: U32,
  +mx: U32,
  +my: U32,
  +mcu: U32,
  +rst: U32,
  +ww: U32,
  +hmax: U32,
  +ri: U32,
  h_next: {next == True{} : Bool}
) -> {Jpeg.decode.adv.comp(next, comp, mx, my, mcu, rst, ww, hmax, ri) ==
  Jpeg.Adv{Jpeg.Ctrl{(comp + 1 : U32), 0, mx, my, mcu, rst}, 0, rst} : Jpeg.Adv}:
  match next:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Jpeg.decode.adv.comp(False{}, comp, mx, my, mcu, rst, ww, hmax, ri) ==
        Jpeg.Adv{Jpeg.Ctrl{(comp + 1 : U32), 0, mx, my, mcu, rst}, 0, rst} : Jpeg.Adv}, U32L.false_true(h_next))

# the step after a component's last unit, from where it tests for more units
def w8.walk.comp(
  more: Bool,
  +comp: U32,
  +bi: U32,
  +mx: U32,
  +my: U32,
  +mcu: U32,
  +rst: U32,
  +ww: U32,
  +hmax: U32,
  +ns: U32,
  +ri: U32,
  h_last: {more == False{} : Bool},
  h_next: {U32.is_lt((comp + 1 : U32), ns) == True{} : Bool}
) -> {Jpeg.decode.adv.bi(more, comp, bi, mx, my, mcu, rst, ww, hmax, ns, ri) ==
  Jpeg.Adv{Jpeg.Ctrl{(comp + 1 : U32), 0, mx, my, mcu, rst}, 0, rst} : Jpeg.Adv}:
  match more:
    case True{}:
      Empty.absurd({Jpeg.decode.adv.bi(True{}, comp, bi, mx, my, mcu, rst, ww, hmax, ns, ri) ==
        Jpeg.Adv{Jpeg.Ctrl{(comp + 1 : U32), 0, mx, my, mcu, rst}, 0, rst} : Jpeg.Adv},
        U32L.false_true(Equal.sym(Bool, True{}, False{}, h_last)))
    case False{}:
      w8.walk.next(U32.is_lt((comp + 1 : U32), ns), comp, mx, my, mcu, rst, ww, hmax, ri, h_next)

def Laws.jpeg_walk_comp(
  comp,
  bi,
  mx,
  my,
  mcu,
  rst,
  ww,
  _hh,
  _nf,
  ids,
  hs,
  vs,
  _tq,
  hmax,
  _vmax,
  ns,
  sids,
  _td,
  _ta,
  _ss,
  _se,
  _ah,
  ri,
  h_last,
  h_next
):
  w8.walk.comp(U32.is_lt((bi + 1 : U32), Laws.jpg.units(comp, sids, ids, hs, vs)), comp, bi, mx, my, mcu, rst, ww,
    hmax, ns, ri, h_last, h_next)

# a new MCU starts at unit 0 of component 0, restart or not
def w8.walk.due(
  zero: Bool,
  hit: Bool,
  +mcu: U32,
  +mx: U32,
  +my: U32,
  +rst: U32
) -> {Laws.jpg.adv.at(Jpeg.decode.adv.due.b(zero, hit, mcu, mx, my, rst)) == (0, 0, mcu) : U32 & U32 & U32}:
  match zero hit:
    case True{} _hit:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# a new MCU starts at unit 0 of component 0, in this MCU row or the next
def w8.walk.mx(
  inb: Bool,
  +mcu: U32,
  +mx: U32,
  +my: U32,
  +rst: U32,
  +ri: U32
) -> {Laws.jpg.adv.at(Jpeg.decode.adv.mx(inb, mcu, mx, my, rst, ri)) == (0, 0, mcu) : U32 & U32 & U32}:
  match inb:
    case True{}:
      w8.walk.due(U32.is_eq(ri, 0), U32.is_eq(U32.mod(mcu, Jpeg.decode.ri.nz(ri)), 0), mcu, mx, my, rst)
    case False{}:
      w8.walk.due(U32.is_eq(ri, 0), U32.is_eq(U32.mod(mcu, Jpeg.decode.ri.nz(ri)), 0), mcu, 0, (my + 1 : U32), rst)

# after the last component's last unit: the next MCU
def w8.walk.end(
  next: Bool,
  +comp: U32,
  +mx: U32,
  +my: U32,
  +mcu: U32,
  +rst: U32,
  +ww: U32,
  +hmax: U32,
  +ri: U32,
  h_end: {next == False{} : Bool}
) -> {Laws.jpg.adv.at(Jpeg.decode.adv.comp(next, comp, mx, my, mcu, rst, ww, hmax, ri)) == (0, 0, (mcu + 1 : U32)) :
  U32 & U32 & U32}:
  match next:
    case False{}:
      w8.walk.mx(U32.is_lt((mx + 1 : U32), Jpeg.decode.ceil(ww, (hmax * 8 : U32))), (mcu + 1 : U32), (mx + 1 : U32),
        my, rst, ri)
    case True{}:
      Empty.absurd({Laws.jpg.adv.at(Jpeg.decode.adv.comp(True{}, comp, mx, my, mcu, rst, ww, hmax, ri)) ==
        (0, 0, (mcu + 1 : U32)) : U32 & U32 & U32}, U32L.false_true(Equal.sym(Bool, True{}, False{}, h_end)))

# the step after the last unit of a component, when no component follows
def w8.walk.last(
  more: Bool,
  +comp: U32,
  +bi: U32,
  +mx: U32,
  +my: U32,
  +mcu: U32,
  +rst: U32,
  +ww: U32,
  +hmax: U32,
  +ns: U32,
  +ri: U32,
  h_last: {more == False{} : Bool},
  h_end: {U32.is_lt((comp + 1 : U32), ns) == False{} : Bool}
) -> {Laws.jpg.adv.at(Jpeg.decode.adv.bi(more, comp, bi, mx, my, mcu, rst, ww, hmax, ns, ri)) ==
  (0, 0, (mcu + 1 : U32)) : U32 & U32 & U32}:
  match more:
    case True{}:
      Empty.absurd({Laws.jpg.adv.at(Jpeg.decode.adv.bi(True{}, comp, bi, mx, my, mcu, rst, ww, hmax, ns, ri)) ==
        (0, 0, (mcu + 1 : U32)) : U32 & U32 & U32}, U32L.false_true(Equal.sym(Bool, True{}, False{}, h_last)))
    case False{}:
      w8.walk.end(U32.is_lt((comp + 1 : U32), ns), comp, mx, my, mcu, rst, ww, hmax, ri, h_end)

def Laws.jpeg_walk_mcu(
  comp,
  bi,
  mx,
  my,
  mcu,
  rst,
  ww,
  _hh,
  _nf,
  ids,
  hs,
  vs,
  _tq,
  hmax,
  _vmax,
  ns,
  sids,
  _td,
  _ta,
  _ss,
  _se,
  _ah,
  ri,
  h_last,
  h_end
):
  w8.walk.last(U32.is_lt((bi + 1 : U32), Laws.jpg.units(comp, sids, ids, hs, vs)), comp, bi, mx, my, mcu, rst, ww,
    hmax, ns, ri, h_last, h_end)
# ---- wp9-png-roundtrip ----

# IMG-PNG-9: the walker takes each chunk and leaves the pixel stage's inputs
def Laws.png_walk(ww, hh, cc, plte, trns, idats, h_ww, h_hh, h_cc, h_pl, h_tr, h_fp, h_ft, h_fi):
  +mm = Inf.inflate(List.concat(&2, U32, idats))
  +pl = Laws.spec.or.nil(plte)
  +tr = Laws.spec.or.nil(trns)
  Equal.trans(Maybe<&2, Img.Raster>, Img.decode_png.pic(Png.decode(Laws.spec.chunk([73, 72, 68, 82],
    Laws.spec.ihdr.data(ww, hh, cc), Laws.spec.chunk.opt([80, 76, 84, 69], plte, Laws.spec.chunk.opt([116, 82, 78, 83],
    trns, Laws.spec.idats(idats, Laws.spec.chunk([73, 69, 78, 68], [], []))))))),
    Img.decode_png.pic(Png.png.samples(mm, ww, hh, cc, pl, tr)),
    Laws.spec.decoded(mm, ww, hh, cc, pl, tr),
    Equal.cong(Maybe<&2, Png.Pic>, Maybe<&2, Img.Raster>, xx => Img.decode_png.pic(xx), Png.decode(Laws.spec.chunk([73,
      72, 68, 82], Laws.spec.ihdr.data(ww, hh, cc), Laws.spec.chunk.opt([80, 76, 84, 69], plte,
      Laws.spec.chunk.opt([116, 82, 78, 83], trns, Laws.spec.idats(idats, Laws.spec.chunk([73, 69, 78, 68], [],
      [])))))), Png.png.samples(mm, ww, hh, cc, pl, tr),
      W9.walk.png(ww, hh, cc, plte, trns, idats, h_ww, h_hh, h_cc, h_pl, h_tr, h_fp, h_ft, h_fi)),
    W9.frame.decoded(mm, ww, hh, cc, pl, tr))

# IMG-PNG-2 for one stored block. The guard enc.good passed, since png_encodes says the encoding is some
def rt.good.at(
  zz: Bool,
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  hs: {Maybe.is_some(&2, List<&2, U32>, Png.enc.open(zz, ww, hh, px)) == True{} : Bool}
) -> {zz == True{} : Bool}:
  match zz:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, U32L.false_true(hs))

# the colour type the encoder writes is one the decoder reads
def rt.col(op: Bool) -> {Laws.spec.colour.ok(Png.enc.ct(op)) == True{} : Bool}:
  match op:
    case True{}:
      {==}
    case False{}:
      {==}

# the encoder's colour types need no PLTE
def rt.plte(op: Bool) -> {Laws.spec.plte.ok(Png.enc.ct(op), None{}) == True{} : Bool}:
  match op:
    case True{}:
      {==}
    case False{}:
      {==}

# the bytes per pixel are 1 to 4
def rt.bpp(
  op: Bool
) -> {Bool.and(U32.is_gt(Png.png.bpp(Png.enc.ct(op)), 0), U32.is_le(Png.png.bpp(Png.enc.ct(op)), 4)) == True{} : Bool}:
  match op:
    case True{}:
      {==}
    case False{}:
      {==}

# the sizes unfilter reads
def rt.dims(
  +ww: U32,
  +hh: U32,
  +op: Bool,
  h_ww: {U32.is_gt(ww, 0) == True{} : Bool},
  h_hh: {U32.is_gt(hh, 0) == True{} : Bool}
) -> {Laws.flt.dims(ww, hh, Png.png.bpp(Png.enc.ct(op))) == True{} : Bool}:
  +bp = Png.png.bpp(Png.enc.ct(op))
  %Equal.sym(Bool, U32.is_gt(ww, 0), True{}, h_ww) : {Bool.and(_, Bool.and(U32.is_gt(hh, 0), Bool.and(U32.is_gt(bp, 0),
    U32.is_le(bp, 4)))) == True{} : Bool}
  %Equal.sym(Bool, U32.is_gt(hh, 0), True{}, h_hh) : {Bool.and(True{}, Bool.and(_, Bool.and(U32.is_gt(bp, 0),
    U32.is_le(bp, 4)))) == True{} : Bool}
  rt.bpp(op)

# the row width in bytes does not wrap: bpp is the channel count
def rt.wrap(
  +ww: U32,
  +op: Bool,
  e_m: {U32.to_nat(U32.mul(ww, Png.enc.nch(op))) == Nat.mul(U32.to_nat(ww), U32.to_nat(Png.enc.nch(op))) : Nat}
) -> {U32.to_nat(U32.mul(ww, Png.png.bpp(Png.enc.ct(op)))) == Nat.mul(U32.to_nat(ww), U32.to_nat(Png.png.bpp(
  Png.enc.ct(op)))) : Nat}:
  %Equal.sym(U32, Png.png.bpp(Png.enc.ct(op)), Png.enc.nch(op), W9.bpp.eq(op)) : {U32.to_nat(U32.mul(ww, _)) ==
    Nat.mul(U32.to_nat(ww), U32.to_nat(_)) : Nat}
  e_m

# the samples px.of packs from the channels are the raster's
def rt.pix(
  op: Bool,
  +px: List<&2, U32>,
  hao: {Laws.all_opaque(px) == op : Bool}
) -> {Png.px.of(Png.enc.ct(op), W9.chans.all(op, px), [], []) == Some{px} : Maybe<&2, List<&2, U32>>}:
  match op:
    case True{}:
      Equal.trans(Maybe<&2, List<&2, U32>>, Png.px.of(2, W9.chans.all(True{}, px), [], []),
        Laws.spec.rgb(W9.chans.all(True{}, px)), Some{px}, Laws.png_px_rgb(W9.chans.all(True{}, px), []),
        W9.rgb.back(px, hao))
    case False{}:
      Equal.trans(Maybe<&2, List<&2, U32>>, Png.px.of(6, W9.chans.all(False{}, px), [], []),
        Laws.spec.rgba(W9.chans.all(False{}, px)), Some{px}, Laws.png_px_rgba(W9.chans.all(False{}, px), []),
        W9.rgba.back(px))

# the pixel stage: the scanlines unfilter to the rows, and the rows pack to the samples
def rt.px(
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  +op: Bool,
  +wp: Nat,
  +hp: Nat,
  hao: {Laws.all_opaque(px) == op : Bool},
  +e_w: {U32.to_nat(ww) == 1n+wp : Nat},
  +e_h: {U32.to_nat(hh) == 1n+hp : Nat},
  +hl: {List.length(&2, U32, px) == Nat.mul(1n+hp, 1n+wp) : Nat},
  e_m: {U32.to_nat(U32.mul(ww, Png.enc.nch(op))) == Nat.mul(U32.to_nat(ww), U32.to_nat(Png.enc.nch(op))) : Nat}
) -> {Laws.spec.decoded(Some{W9.sc(px, 0n, 1n+wp, op)}, ww, hh, Png.enc.ct(op), [], []) == Some{Img.raster(ww, hh,
  px)} : Maybe<&2, Img.Raster>}:
  +ww1 = {1n+wp : Nat}
  +hh1 = {1n+hp : Nat}
  +ct = Png.enc.ct(op)
  +bp = Png.png.bpp(ct)
  +rows = W9.rows.of(hh1, ww1, op, px)
  +ss = W9.sc(px, 0n, ww1, op)
  +fr = Laws.flt.rows(rows, Laws.FNone{}, bp, [])
  +e_s = {Equal.trans(List<&2, U32>, ss, W9.scan(rows), fr, W9.sc.rows(hh1, wp, op, px, hl), Equal.sym(List<&2, U32>,
    fr, W9.scan(rows), W9.frows(rows, bp, [], W9.masked.rows.of(hh1, ww1, op, px)))) : {ss == fr : List<&2, U32>}}
  +h_ww = W9.gt.pos(ww, wp, e_w)
  +h_hh = W9.gt.pos(hh, hp, e_h)
  +h_rows = {Equal.trans(Nat, List.length(&2, List<&2, U32>, rows), hh1, U32.to_nat(hh), W9.rows.len(hh1, ww1, op, px),
    Equal.sym(Nat, U32.to_nat(hh), hh1, e_h)) : {List.length(&2, List<&2, U32>, rows) == U32.to_nat(hh) : Nat}}
  +e_nb = {Equal.trans(Nat, Nat.mul(U32.to_nat(ww), U32.to_nat(bp)), Nat.mul(ww1, U32.to_nat(bp)), Nat.mul(ww1,
    Laws.spec.nch(op)), Equal.cong(Nat, Nat, kk => Nat.mul(kk, U32.to_nat(bp)), U32.to_nat(ww), ww1, e_w),
    Equal.trans(Nat, Nat.mul(ww1, U32.to_nat(bp)), Nat.mul(ww1, U32.to_nat(Png.enc.nch(op))), Nat.mul(ww1,
    Laws.spec.nch(op)), Equal.cong(U32, Nat, uu => Nat.mul(ww1, U32.to_nat(uu)), bp, Png.enc.nch(op), W9.bpp.eq(op)),
    Equal.cong(Nat, Nat, kk => Nat.mul(ww1, kk), U32.to_nat(Png.enc.nch(op)), Laws.spec.nch(op), W9.nch.val(op)))) :
    {Nat.mul(U32.to_nat(ww), U32.to_nat(bp)) == Nat.mul(ww1, Laws.spec.nch(op)) : Nat}}
  +h_fit = {Equal.trans(Bool, Laws.flt.fit(rows, Nat.mul(U32.to_nat(ww), U32.to_nat(bp)), True{}),
    Laws.flt.fit(rows, Nat.mul(ww1, Laws.spec.nch(op)), True{}), True{}, Equal.cong(Nat, Bool, kk => Laws.flt.fit(rows,
    kk, True{}), Nat.mul(U32.to_nat(ww), U32.to_nat(bp)), Nat.mul(ww1, Laws.spec.nch(op)), e_nb), W9.fit.rows(hh1, ww1,
    op, px, hl)) : {Laws.flt.fit(rows, Nat.mul(U32.to_nat(ww), U32.to_nat(bp)), True{}) == True{} : Bool}}
  +e_un = {Laws.unfilter_filter(Laws.FNone{}, ww, hh, bp, rows, rt.dims(ww, hh, op, h_ww, h_hh), rt.wrap(ww, op, e_m),
    h_rows, h_fit) : {Png.unfilter(fr, ww, hh, bp) == Some{List.concat(&2, U32, rows)} : Maybe<&2, List<&2, U32>>}}
  +e_cat = {W9.rows.cat(hh1, ww1, op, px, hl) : {List.concat(&2, U32, rows) == W9.chans.all(op, px) : List<&2, U32>}}
  Equal.trans(Maybe<&2, Img.Raster>,
    Laws.spec.raster(Laws.spec.px.then(Png.unfilter(ss, ww, hh, bp), ct, [], []), ww, hh),
    Laws.spec.raster(Laws.spec.px.then(Some{W9.chans.all(op, px)}, ct, [], []), ww, hh),
    Some{Img.raster(ww, hh, px)},
    Equal.cong(Maybe<&2, List<&2, U32>>, Maybe<&2, Img.Raster>, mm => Laws.spec.raster(Laws.spec.px.then(mm, ct, [],
      []), ww, hh), Png.unfilter(ss, ww, hh, bp), Some{W9.chans.all(op, px)},
      Equal.trans(Maybe<&2, List<&2, U32>>, Png.unfilter(ss, ww, hh, bp), Png.unfilter(fr, ww, hh, bp),
        Some{W9.chans.all(op, px)},
        Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, xs => Png.unfilter(xs, ww, hh, bp), ss, fr, e_s),
        Equal.trans(Maybe<&2, List<&2, U32>>, Png.unfilter(fr, ww, hh, bp), Some{List.concat(&2, U32, rows)},
          Some{W9.chans.all(op, px)}, e_un, Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, xs => Some{xs},
          List.concat(&2, U32, rows), W9.chans.all(op, px), e_cat)))),
    Equal.cong(Maybe<&2, List<&2, U32>>, Maybe<&2, Img.Raster>, mm => Laws.spec.raster(mm, ww, hh),
      Png.px.of(ct, W9.chans.all(op, px), [], []), Some{px}, rt.pix(op, px, hao)))

# the one-block round trip, with the width and height 1 + w' and 1 + h', and
# op whether every sample is opaque
def rt.go(
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  +nb: U32,
  +op: Bool,
  +wp: Nat,
  +hp: Nat,
  e_op: {Png.enc.opaque(px, True{}) == op : Bool},
  hao: {Laws.all_opaque(px) == op : Bool},
  e_good: {Png.enc.good(ww, hh, px) == True{} : Bool},
  +e_w: {U32.to_nat(ww) == 1n+wp : Nat},
  +e_h: {U32.to_nat(hh) == 1n+hp : Nat},
  +hl: {List.length(&2, U32, px) == Nat.mul(1n+hp, 1n+wp) : Nat},
  h_nb: {U32.to_nat(nb) == Nat.mul(1n+hp, 1n+Nat.mul(1n+wp, Laws.spec.nch(op))) : Nat},
  h_one: {U32.is_le(nb, 65535) == True{} : Bool},
  +cap: U32,
  +cap2: U32,
  +ec: {cap == 65535 : U32},
  hc: {Nat.is_le(11n+U32.to_nat(cap), U32.to_nat(cap2)) == True{} : Bool}
) -> {Laws.spec.png.back(Img.encode_png(Img.raster(ww, hh, px))) == Some{Img.raster(ww, hh, px)} :
  Maybe<&2, Img.Raster>}:
  +ww1 = {1n+wp : Nat}
  +hh1 = {1n+hp : Nat}
  +kk = Laws.spec.nch(op)
  +wk = Nat.mul(ww1, kk)
  +nn = Nat.mul(hh1, 1n+wk)
  +cn = U32.to_nat(cap)
  +h_oc = {Equal.trans(Bool, U32.is_le(nb, cap), U32.is_le(nb, 65535), True{}, Equal.cong(U32, Bool, cu => U32.is_le(nb,
    cu), cap, 65535, ec), h_one) : {U32.is_le(nb, cap) == True{} : Bool}}
  +h_n = {Equal.trans(Bool, Nat.is_le(nn, cn), Nat.is_le(U32.to_nat(nb), cn), True{}, Equal.cong(Nat, Bool, xx =>
    Nat.is_le(xx, cn), nn, U32.to_nat(nb), Equal.sym(Nat, U32.to_nat(nb), nn, h_nb)), Equal.trans(Bool,
    Nat.is_le(U32.to_nat(nb), cn), U32.is_le(nb, cap), True{}, Equal.sym(Bool, U32.is_le(nb, cap),
    Nat.is_le(U32.to_nat(nb), cn), Wp2.u_le(nb, cap)), h_oc)) : {Nat.is_le(nn, cn) == True{} : Bool}}
  +h_y = {R.le_add_r(1n+wk, Nat.mul(hp, 1n+wk), cn, h_n) : {Nat.is_le(1n+wk, cn) == True{} : Bool}}
  +h_wk = {R.le_trans(wk, 1n+wk, cn, W9.le.succ(wk), h_y) : {Nat.is_le(wk, cn) == True{} : Bool}}
  +nc = Png.enc.nch(op)
  +m1 = U32.mul(ww, nc)
  +e_m1n = {Equal.trans(Nat, Nat.mul(U32.to_nat(ww), U32.to_nat(nc)), Nat.mul(ww1, U32.to_nat(nc)), wk,
    Equal.cong(Nat, Nat, xx => Nat.mul(xx, U32.to_nat(nc)), U32.to_nat(ww), ww1, e_w), Equal.cong(Nat, Nat, xx =>
    Nat.mul(ww1, xx), U32.to_nat(nc), kk, W9.nch.val(op))) : {Nat.mul(U32.to_nat(ww), U32.to_nat(nc)) == wk : Nat}}
  +e_m = {R.u32_mul_below(ww, nc, cap, R.le_rw_l(wk, Nat.mul(U32.to_nat(ww), U32.to_nat(nc)), cn, Equal.sym(Nat,
    Nat.mul(U32.to_nat(ww), U32.to_nat(nc)), wk, e_m1n), h_wk)) : {U32.to_nat(m1) == Nat.mul(U32.to_nat(ww),
    U32.to_nat(nc)) : Nat}}
  +t1 = {Equal.trans(Nat, U32.to_nat(m1), Nat.mul(U32.to_nat(ww), U32.to_nat(nc)), wk, e_m, e_m1n) : {U32.to_nat(m1) ==
    wk : Nat}}
  +x1 = U32.add(m1, 1)
  +e_x = {Equal.trans(Nat, Nat.add(U32.to_nat(m1), 1n), Nat.add(wk, 1n), 1n+wk, Equal.cong(Nat, Nat, xx => Nat.add(xx,
    1n), U32.to_nat(m1), wk, t1), W9.add.one.nat(wk)) : {Nat.add(U32.to_nat(m1), 1n) == 1n+wk : Nat}}
  +t2 = {Equal.trans(Nat, U32.to_nat(x1), Nat.add(U32.to_nat(m1), 1n), 1n+wk, R.u32_add_below(m1, 1, cap,
    R.le_rw_l(1n+wk, Nat.add(U32.to_nat(m1), 1n), cn, Equal.sym(Nat, Nat.add(U32.to_nat(m1), 1n), 1n+wk, e_x), h_y)),
    e_x) : {U32.to_nat(x1) == 1n+wk : Nat}}
  +n_b = U32.mul(hh, x1)
  +e_3 = {Equal.trans(Nat, Nat.mul(U32.to_nat(hh), U32.to_nat(x1)), Nat.mul(hh1, U32.to_nat(x1)), nn, Equal.cong(Nat,
    Nat, xx => Nat.mul(xx, U32.to_nat(x1)), U32.to_nat(hh), hh1, e_h), Equal.cong(Nat, Nat, xx => Nat.mul(hh1, xx),
    U32.to_nat(x1), 1n+wk, t2)) : {Nat.mul(U32.to_nat(hh), U32.to_nat(x1)) == nn : Nat}}
  +t3 = {Equal.trans(Nat, U32.to_nat(n_b), Nat.mul(U32.to_nat(hh), U32.to_nat(x1)), nn, R.u32_mul_below(hh, x1, cap,
    R.le_rw_l(nn, Nat.mul(U32.to_nat(hh), U32.to_nat(x1)), cn, Equal.sym(Nat, Nat.mul(U32.to_nat(hh), U32.to_nat(x1)),
    nn, e_3), h_n)), e_3) : {U32.to_nat(n_b) == nn : Nat}}
  +ss = W9.sc(px, 0n, ww1, op)
  +rows = W9.rows.of(hh1, ww1, op, px)
  +ls = List.length(&2, U32, ss)
  +e_s = {W9.sc.rows(hh1, wp, op, px, hl) : {ss == W9.scan(rows) : List<&2, U32>}}
  +e_ls = {Equal.trans(Nat, ls, List.length(&2, U32, W9.scan(rows)), nn, Equal.cong(List<&2, U32>, Nat, xs =>
    List.length(&2, U32, xs), ss, W9.scan(rows), e_s), W9.len.scan(hh1, ww1, op, px, hl)) : {ls == nn : Nat}}
  +h_ls = {R.le_rw_l(nn, ls, cn, Equal.sym(Nat, ls, nn, e_ls), h_n) : {Nat.is_le(ls, cn) == True{} : Bool}}
  +ll = Png.enc.len(ss, 0)
  +t_l = {Equal.trans(Nat, U32.to_nat(ll), U32.to_nat(U32.from_nat(ls)), nn, Equal.cong(U32, Nat, uu => U32.to_nat(uu),
    ll, U32.from_nat(ls), W9.len.word(ss)), Equal.trans(Nat, U32.to_nat(U32.from_nat(ls)), ls, nn, W9.nat.fits(ls,
    cap, h_ls), e_ls)) : {U32.to_nat(ll) == nn : Nat}}
  +r0 = List.reverse(&2, U32, List.reverse.go(&2, U32, ss, []))
  +m0 = W9.cnt(px, 0n, ww1, op, 0)
  +e_m0 = {Equal.trans(U32, m0, U32.from_nat(ls), ll, W9.cnt.word(px, 0n, ww1, op, 0n), Equal.sym(U32, ll,
    U32.from_nat(ls), W9.len.word(ss))) : {m0 == ll : U32}}
  +zz = Png.enc.zlib(ss, ll)
  +le_l = {Equal.trans(Bool, U32.is_le(ll, 65535), U32.is_le(ll, cap), True{}, Equal.cong(U32, Bool, cu => U32.is_le(ll,
    cu), 65535, cap, Equal.sym(U32, cap, 65535, ec)), W9.le.yes(ll, cap, nn, t_l, h_n)) : {U32.is_le(ll,
    65535) == True{} : Bool}}
  +f_nb = {Equal.trans(Bool, U32.is_gt(n_b, 65535), U32.is_gt(n_b, cap), False{}, Equal.cong(U32, Bool, cu =>
    U32.is_gt(n_b, cu), 65535, cap, Equal.sym(U32, cap, 65535, ec)), W9.gt.no(n_b, cap, nn, t3, h_n)) :
    {U32.is_gt(n_b, 65535) == False{} : Bool}}
  +f_ll = {Equal.trans(Bool, U32.is_gt(ll, 65535), U32.is_gt(ll, cap), False{}, Equal.cong(U32, Bool, cu =>
    U32.is_gt(ll, cu), 65535, cap, Equal.sym(U32, cap, 65535, ec)), W9.gt.no(ll, cap, nn, t_l, h_n)) :
    {U32.is_gt(ll, 65535) == False{} : Bool}}
  h_fz = {W9.fits.small(zz, ls, cap, cap2, W9.zlib.len(ss, ll, le_l), h_ls, hc) :
    Laws.spec.fits(zz)}
  +h_by = {Equal.trans(Bool, Laws.bytes(ss), Laws.bytes.go(W9.scan(rows), True{}), True{}, Equal.cong(List<&2, U32>,
    Bool, xs => Laws.bytes.go(xs, True{}), ss, W9.scan(rows), e_s), W9.bytes.scan(rows, W9.masked.rows.of(hh1, ww1, op,
    px))) : {Laws.bytes(ss) == True{} : Bool}}
  +h_nl = {Equal.trans(Nat, U32.to_nat(ll), nn, ls, t_l, Equal.sym(Nat, ls, nn, e_ls)) : {U32.to_nat(ll) == ls : Nat}}
  +e_inf = {Laws.inflate_enc_zlib(ss, h_by, h_nl) : {Inf.inflate(zz) == Some{ss} : Maybe<&2, List<&2, U32>>}}
  +ct = Png.enc.ct(op)
  +h_ww = W9.gt.pos(ww, wp, e_w)
  +h_hh = W9.gt.pos(hh, hp, e_h)
  +a2 = Img.decode_png(Png.enc.paint(ww, hh, op, px))
  +a4 = Img.decode_png(Png.enc.seal(ww, hh, op, Png.enc.raw(px, 0n, ww1, op, [], 0)))
  +a6 = Img.decode_png(Png.enc.seal.at(U32.is_gt(ll, 65535), ww, hh, op, ss, ll))
  +a8 = Img.decode_png(Laws.spec.png(ww, hh, ct, None{}, None{}, [zz]))
  +a9 = Laws.spec.decoded(Inf.inflate(List.concat(&2, U32, [zz])), ww, hh, ct, [], [])
  +a10 = Laws.spec.decoded(Some{ss}, ww, hh, ct, [], [])
  Equal.trans(Maybe<&2, Img.Raster>, Laws.spec.png.back(Png.enc.open(Png.enc.good(ww, hh, px), ww, hh, px)), a2,
    Some{Img.raster(ww, hh, px)},
    Equal.trans(Maybe<&2, Img.Raster>, Laws.spec.png.back(Png.enc.open(Png.enc.good(ww, hh, px), ww, hh, px)),
      Laws.spec.png.back(Png.enc.open(True{}, ww, hh, px)), a2,
      Equal.cong(Bool, Maybe<&2, Img.Raster>, zb => Laws.spec.png.back(Png.enc.open(zb, ww, hh, px)), Png.enc.good(ww,
        hh, px), True{}, e_good),
      Equal.cong(Bool, Maybe<&2, Img.Raster>, ob => Img.decode_png(Png.enc.paint(ww, hh, ob, px)), Png.enc.opaque(px,
        True{}), op, e_op)),
    Equal.trans(Maybe<&2, Img.Raster>, a2, a4, Some{Img.raster(ww, hh, px)},
      Equal.trans(Maybe<&2, Img.Raster>, a2, Img.decode_png(Png.enc.paint.at(False{}, ww, hh, op, px, n_b)), a4,
        Equal.cong(Bool, Maybe<&2, Img.Raster>, zb => Img.decode_png(Png.enc.paint.at(zb, ww, hh, op, px, n_b)),
          U32.is_gt(n_b, 65535), False{}, f_nb),
        Equal.cong(Nat, Maybe<&2, Img.Raster>, kn => Img.decode_png(Png.enc.seal(ww, hh, op, Png.enc.raw(px, 0n, kn, op,
          [], 0))), U32.to_nat(ww), ww1, e_w)),
      Equal.trans(Maybe<&2, Img.Raster>, a4, a6, Some{Img.raster(ww, hh, px)},
        Equal.trans(Maybe<&2, Img.Raster>, a4, Img.decode_png(Png.enc.seal(ww, hh, op, (r0, m0))), a6,
          Equal.cong(List<&2, U32> & U32, Maybe<&2, Img.Raster>, pr => Img.decode_png(Png.enc.seal(ww, hh, op, pr)),
            Png.enc.raw(px, 0n, ww1, op, [], 0), (r0, m0), W9.raw.eq(px, 0n, ww1, op, [], 0)),
          Equal.trans(Maybe<&2, Img.Raster>, Img.decode_png(Png.enc.seal(ww, hh, op, (r0, m0))),
            Img.decode_png(Png.enc.seal(ww, hh, op, (ss, m0))), a6,
            Equal.cong(List<&2, U32>, Maybe<&2, Img.Raster>, xs => Img.decode_png(Png.enc.seal(ww, hh, op, (xs, m0))),
              r0, ss, Wp2.rev_rev(ss)),
            Equal.cong(U32, Maybe<&2, Img.Raster>, uu => Img.decode_png(Png.enc.seal(ww, hh, op, (ss, uu))), m0, ll,
              e_m0))),
        Equal.trans(Maybe<&2, Img.Raster>, a6, a8, Some{Img.raster(ww, hh, px)},
          Equal.trans(Maybe<&2, Img.Raster>, a6, Img.decode_png(Png.enc.seal.one(ww, hh, op, ss, ll)), a8,
            Equal.cong(Bool, Maybe<&2, Img.Raster>, zb => Img.decode_png(Png.enc.seal.at(zb, ww, hh, op, ss, ll)),
              U32.is_gt(ll, 65535), False{}, f_ll),
            Equal.cong(List<&2, U32>, Maybe<&2, Img.Raster>, xs => Img.decode_png(xs), Png.enc.seal.one(ww, hh, op, ss,
              ll), Laws.spec.png(ww, hh, ct, None{}, None{}, [zz]), W9.seal.one.same(ww, hh, op, ss, ll))),
          Equal.trans(Maybe<&2, Img.Raster>, a8, a9, Some{Img.raster(ww, hh, px)},
            Laws.png_walk(ww, hh, ct, None{}, None{}, [zz], h_ww, h_hh, rt.col(op), rt.plte(op), {==}, Unit{}, Unit{},
              (h_fz, Unit{})),
            Equal.trans(Maybe<&2, Img.Raster>, a9, Laws.spec.decoded(Inf.inflate(zz), ww, hh, ct, [], []),
              Some{Img.raster(ww, hh, px)},
              Equal.cong(List<&2, U32>, Maybe<&2, Img.Raster>, xs => Laws.spec.decoded(Inf.inflate(xs), ww, hh, ct, [],
                []), List.append(&2, U32, zz, []), zz, Wp2.app_nil(zz)),
              Equal.trans(Maybe<&2, Img.Raster>, Laws.spec.decoded(Inf.inflate(zz), ww, hh, ct, [], []), a10,
                Some{Img.raster(ww, hh, px)},
                Equal.cong(Maybe<&2, List<&2, U32>>, Maybe<&2, Img.Raster>, mm => Laws.spec.decoded(mm, ww, hh, ct, [],
                  []), Inf.inflate(zz), Some{ss}, e_inf),
                rt.px(ww, hh, px, op, wp, hp, hao, e_w, e_h, hl, e_m))))))))

# the width and height as successors
def rt.pos(
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  +nb: U32,
  e_good: {Png.enc.good(ww, hh, px) == True{} : Bool},
  +hl: {List.length(&2, U32, px) == Nat.mul(U32.to_nat(hh), U32.to_nat(ww)) : Nat},
  h_nb: {U32.to_nat(nb) == Laws.spec.scan.len(ww, hh, Laws.all_opaque(px)) : Nat},
  h_one: {U32.is_le(nb, 65535) == True{} : Bool},
  pw: &wp: Nat -> {U32.to_nat(ww) == 1n+wp : Nat},
  ph: &hp: Nat -> {U32.to_nat(hh) == 1n+hp : Nat}
) -> {Laws.spec.png.back(Img.encode_png(Img.raster(ww, hh, px))) == Some{Img.raster(ww, hh, px)} :
  Maybe<&2, Img.Raster>}:
  (+wp, e_w0) = pw
  (+hp, e_h0) = ph
  +e_w = {e_w0 : {U32.to_nat(ww) == 1n+wp : Nat}}
  +e_h = {e_h0 : {U32.to_nat(hh) == 1n+hp : Nat}}
  +op = Laws.all_opaque(px)
  +kk = Laws.spec.nch(op)
  +e_l2 = {Equal.trans(Nat, List.length(&2, U32, px), Nat.mul(U32.to_nat(hh), U32.to_nat(ww)), Nat.mul(1n+hp, 1n+wp),
    hl, Equal.trans(Nat, Nat.mul(U32.to_nat(hh), U32.to_nat(ww)), Nat.mul(1n+hp, U32.to_nat(ww)), Nat.mul(1n+hp, 1n+wp),
    Equal.cong(Nat, Nat, xx => Nat.mul(xx, U32.to_nat(ww)), U32.to_nat(hh), 1n+hp, e_h), Equal.cong(Nat, Nat, xx =>
    Nat.mul(1n+hp, xx), U32.to_nat(ww), 1n+wp, e_w))) : {List.length(&2, U32, px) == Nat.mul(1n+hp, 1n+wp) : Nat}}
  +e_n2 = {Equal.trans(Nat, U32.to_nat(nb), Nat.mul(U32.to_nat(hh), 1n+Nat.mul(U32.to_nat(ww), kk)), Nat.mul(1n+hp,
    1n+Nat.mul(1n+wp, kk)), h_nb, Equal.trans(Nat, Nat.mul(U32.to_nat(hh), 1n+Nat.mul(U32.to_nat(ww), kk)),
    Nat.mul(1n+hp, 1n+Nat.mul(U32.to_nat(ww), kk)), Nat.mul(1n+hp, 1n+Nat.mul(1n+wp, kk)), Equal.cong(Nat, Nat, xx =>
    Nat.mul(xx, 1n+Nat.mul(U32.to_nat(ww), kk)), U32.to_nat(hh), 1n+hp, e_h), Equal.cong(Nat, Nat, xx => Nat.mul(1n+hp,
    1n+Nat.mul(xx, kk)), U32.to_nat(ww), 1n+wp, e_w))) : {U32.to_nat(nb) == Nat.mul(1n+hp, 1n+Nat.mul(1n+wp, kk)) :
    Nat}}
  rt.go(ww, hh, px, nb, op, wp, hp, opaque.all(px, True{}), {==}, e_good, e_w, e_h, e_l2, e_n2, h_one, 65535, 65546,
    {==}, {==})

# IMG-PNG-2 for one stored block
def Laws.png_roundtrip_one(ww, hh, px, nb, h_ok, h_nb, h_one):
  +aa = Nat.mul(U32.to_nat(hh), U32.to_nat(ww))
  +ll = List.length(&2, U32, px)
  +nw = Bool.not(Nat.is_eq(U32.to_nat(ww), 0n))
  +nh = Bool.not(Nat.is_eq(U32.to_nat(hh), 0n))
  +ok = {h_ok : {Laws.png_ok(ww, hh, px) == True{} : Bool}}
  +e_sides = {U32L.and_left(Bool.and(nw, nh), Bool.and(Laws.below(32n, aa), Nat.is_eq(ll, aa)), ok) :
    {Bool.and(nw, nh) == True{} : Bool}}
  +e_r = {U32L.and_right(Bool.and(nw, nh), Bool.and(Laws.below(32n, aa), Nat.is_eq(ll, aa)), ok) :
    {Bool.and(Laws.below(32n, aa), Nat.is_eq(ll, aa)) == True{} : Bool}}
  +e_la = {Wp4.nat_eq_true(ll, aa, U32L.and_right(Laws.below(32n, aa), Nat.is_eq(ll, aa), e_r)) : {ll == aa : Nat}}
  +z_w = not.true(Nat.is_eq(U32.to_nat(ww), 0n), U32L.and_left(nw, nh, e_sides))
  +z_h = not.true(Nat.is_eq(U32.to_nat(hh), 0n), U32L.and_right(nw, nh, e_sides))
  +e_good = rt.good.at(Png.enc.good(ww, hh, px), ww, hh, px, Laws.png_encodes(ww, hh, px, ok))
  rt.pos(ww, hh, px, nb, e_good, e_la, h_nb, h_one, Wp4.nat_pos(U32.to_nat(ww), z_w), Wp4.nat_pos(U32.to_nat(hh), z_h))


# ---- wp10-jpeg-finish ----

def Laws.jpeg_block_cover_all(pw, ph, ox, oy, ww, hh, samples, plane):
  W10.cv.all(8n, plane, samples, 0, ox, oy, pw, ph, ww, hh)

def Laws.jpeg_block_cover(pw, ph, _h_pw, _h_ph, _h_44, ox, oy, ww, hh, samples, nn):
  W10.cv.all(8n, Jpeg.decode.plane(nn), samples, 0, ox, oy, pw, ph, ww, hh)

def Laws.jpeg_mcu_grid_comp(comp, sids, ids, hs, vs, h_hi, h_vi, mx, my, hmax, vmax, ww, hh):
  +hi = Laws.jpg.fac.of(comp, sids, ids, hs)
  +vi = Laws.jpg.fac.of(comp, sids, ids, vs)
  Equal.trans(List<&2, Jpeg.Geom>, Laws.jpg.blocks.of(U32.to_nat((hi * vi : U32)), 0, comp, sids, ids, hs, vs, mx, my,
    hmax, vmax, ww, hh), Laws.jpg.blocks(U32.to_nat((hi * vi : U32)), 0, hi, vi, mx, my, hmax, vmax, ww, hh),
    Laws.jpg.grid(U32.to_nat(vi), 0, hi, mx, my, hmax, vmax, U32.div(hmax, hi), U32.div(vmax, vi), ww, hh),
    W10.grid.of(U32.to_nat((hi * vi : U32)), 0, comp, sids, ids, hs, vs, mx, my, hmax, vmax, ww, hh),
    Laws.jpeg_mcu_grid(hi, vi, h_hi, h_vi, mx, my, hmax, vmax, ww, hh))

def Laws.jpeg_refuse_factor1_any(
  pre,
  frame,
  scan,
  tabs,
  ent,
  ri,
  kind,
  bad,
  h_walk,
  lh,
  ll,
  yh,
  yl,
  xh,
  xl,
  c1,
  f1,
  q1,
  extra,
  h_len,
  h_body,
  h_fac,
  rest
):
  +body = {List.append(&2, U32, [8, yh, yl, xh, xl, 1, c1, f1, q1], extra) : List<&2, U32>}
  w8.tail(pre, lh <> ll <> List.append(&2, U32, body, rest), Jpeg.St{Jpeg.LenHi{192}, frame, scan, tabs, ent, ri,
    kind, bad}, rest, scan, tabs, ent, ri, kind, h_walk,
    W10.sof.seg(lh, ll, body, rest, frame, scan, tabs, ent, ri, kind, bad, h_len, h_body,
      Equal.cong(Bool, Jpeg.St, ok => Jpeg.decode.read.sof.c(ok, Bool.and(Jpeg.decode.nf.ok(1), U32.is_eq(bad, 0)),
        U32.is_eq(Jpeg.decode.vmax([U32.shrn(f1, 4n)], 0), 0), Jpeg.decode.u16(xh, xl), Jpeg.decode.u16(yh, yl), 1,
        [c1], [U32.shrn(f1, 4n)], [U32.and(f1, 15)], [q1], scan, tabs, ent, ri, kind), Laws.jpg.facs(f1), False{},
        h_fac)))

def Laws.jpeg_refuse_factor3_any(
  pre,
  frame,
  scan,
  tabs,
  ent,
  ri,
  kind,
  bad,
  h_walk,
  lh,
  ll,
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
  extra,
  h_len,
  h_body,
  h_fac,
  rest
):
  +body = {List.append(&2, U32, [8, yh, yl, xh, xl, 3, c1, f1, q1, c2, f2, q2, c3, f3, q3], extra) : List<&2, U32>}
  w8.tail(pre, lh <> ll <> List.append(&2, U32, body, rest), Jpeg.St{Jpeg.LenHi{192}, frame, scan, tabs, ent, ri,
    kind, bad}, rest, scan, tabs, ent, ri, kind, h_walk,
    W10.sof.seg(lh, ll, body, rest, frame, scan, tabs, ent, ri, kind, bad, h_len, h_body,
      Equal.cong(Bool, Jpeg.St, ok => Jpeg.decode.read.sof.c(ok, Bool.and(Jpeg.decode.nf.ok(3), U32.is_eq(bad, 0)),
        U32.is_eq(Jpeg.decode.vmax([U32.shrn(f1, 4n), U32.shrn(f2, 4n), U32.shrn(f3, 4n)], 0), 0),
        Jpeg.decode.u16(xh, xl), Jpeg.decode.u16(yh, yl), 3, [c1, c2, c3],
        [U32.shrn(f1, 4n), U32.shrn(f2, 4n), U32.shrn(f3, 4n)], [U32.and(f1, 15), U32.and(f2, 15), U32.and(f3, 15)],
        [q1, q2, q3], scan, tabs, ent, ri, kind),
        Bool.and(Bool.and(Laws.jpg.facs(f1), Laws.jpg.facs(f2)), Laws.jpg.facs(f3)), False{}, h_fac)))

def Laws.jpeg_refuse_count(
  pre,
  frame,
  scan,
  tabs,
  ent,
  ri,
  kind,
  bad,
  h_walk,
  lh,
  ll,
  yh,
  yl,
  xh,
  xl,
  nf,
  h_nf,
  comps,
  h_len,
  h_body,
  rest
):
  +body = {8 <> yh <> yl <> xh <> xl <> nf <> comps : List<&2, U32>}
  w8.tail(pre, lh <> ll <> List.append(&2, U32, body, rest), Jpeg.St{Jpeg.LenHi{192}, frame, scan, tabs, ent, ri,
    kind, bad}, rest, scan, tabs, ent, ri, kind, h_walk,
    W10.sof.seg(lh, ll, body, rest, frame, scan, tabs, ent, ri, kind, bad, h_len, h_body,
      W10.sof.cnt(Jpeg.decode.read.cs(U32.to_nat(nf), comps, [], [], [], [], True{}), Jpeg.decode.u16(xh, xl),
        Jpeg.decode.u16(yh, yl), nf, scan, tabs, ent, ri, kind, bad, h_nf)))

def Laws.jpeg_points_at(nn, plane, kk, h_kk):
  ee = W10.idx.of(kk)
  %ee : {List.get(&2, U32, Jpeg.decode.points(nn, plane), U32.to_nat(kk)) ==
    Some{Laws.jpg.val(Array.get(U32, plane, _))} : Maybe<&2, U32>}
  W10.emit.at(nn, U32.to_nat(kk), plane, 0, W10.dup(plane), h_kk)

def Laws.jpeg_walk_frame(
  ww,
  hh,
  nf,
  ids,
  hs,
  vs,
  tq,
  hmax,
  vmax,
  ns,
  sids,
  td,
  ta,
  ss,
  se,
  ah,
  ri,
  rst,
  mh,
  h_ns,
  h_mw,
  h_units
):
  W10.walk.frame(ww, hh, nf, ids, hs, vs, tq, hmax, vmax, ns, sids, td, ta, ss, se, ah, ri, rst, mh, h_ns, h_mw,
    h_units)

def Laws.jpeg_enc_stuffed(ww, hh, px):
  W10.st.use(Jenc.encode.watch(U32.to_nat((ww * hh : U32)), px), ww, hh)

# the decoder's state after the encoder's header, with the sizes as it reads them back
def w10.hdr.st(+ww: U32, +hh: U32) -> Jpeg.St:
  Jpeg.St{Jpeg.Ent{}, Jpeg.Frame{ww, hh, 3, [1, 2, 3], [1, 1, 1], [1, 1, 1], [0, 0, 0], 1, 1}, Laws.jpg.enc.scan(),
    Laws.jpg.enc.tabs(), [], 0, 1, 0}

def Laws.jpeg_enc_header_walk(ww, hh):
  +wr = Jpeg.decode.u16(U32.shrn(ww, 8n), U32.and(ww, 255))
  +hr = Jpeg.decode.u16(U32.shrn(hh, 8n), U32.and(hh, 255))
  Equal.trans(Jpeg.St, Jpeg.decode.walk(Jenc.encode.header(ww, hh, Jenc.encode.dccounts(), Jenc.encode.dcsyms(),
    Jenc.encode.accounts(), Jenc.encode.acsyms()), Jpeg.decode.st0()), w10.hdr.st(wr, hr), w10.hdr.st(ww, hh), {==},
    Equal.trans(Jpeg.St, w10.hdr.st(wr, hr), w10.hdr.st(ww, hr), w10.hdr.st(ww, hh), Equal.cong(U32, Jpeg.St,
    xx => w10.hdr.st(xx, hr), wr, ww, W10.u16.eq(ww)), Equal.cong(U32, Jpeg.St, xx => w10.hdr.st(ww, xx), hr, hh,
    W10.u16.eq(hh))))

def Laws.jpeg_ent_walk(xs, h_stuffed, frame, scan, tabs, ent, ri, kind, bad):
  W10.ent.go(xs, False{}, frame, scan, tabs, ent, ri, kind, bad, h_stuffed)

def Laws.jpeg_round_trip_scan(ww, hh, px, h_good, h_w, h_h):
  +cp = Img.colours(px)
  +ee = Jenc.encode.arm(ww, hh, cp)
  +hd = Jenc.encode.header(ww, hh, Jenc.encode.dccounts(), Jenc.encode.dcsyms(), Jenc.encode.accounts(),
    Jenc.encode.acsyms())
  +rr = List.append(&2, U32, ee, [255, 217])
  +fr = Laws.jpg.enc.frame(ww, hh)
  +sc = Laws.jpg.enc.scan()
  +tb = Laws.jpg.enc.tabs()
  +ent = {Jpeg.St{Jpeg.Ent{}, fr, sc, tb, [], 0, 1, 0} : Jpeg.St}
  +stop = {Jpeg.St{Jpeg.Stop{}, fr, sc, tb, List.reverse.go(&2, U32, ee, []), 0, 1, 0} : Jpeg.St}
  Equal.trans(Maybe<&2, Img.Raster>, Laws.jpg.back(Img.encode_jpeg(Img.Raster{ww, hh, px})),
    Laws.jpg.back(Img.encode_jpeg.pick(True{}, ww, hh, cp)), Img.decode_jpeg.out(Jpeg.decode.run(fr, sc, tb, ee, 0)),
    Equal.cong(Bool, Maybe<&2, Img.Raster>, bb => Laws.jpg.back(Img.encode_jpeg.pick(bb, ww, hh, cp)),
    Png.enc.good(ww, hh, px), True{}, h_good),
    Equal.trans(Maybe<&2, Img.Raster>, Img.decode_jpeg(Jenc.encode.pick(Jenc.encode.bad(ww, hh), ww, hh, cp)),
    Img.decode_jpeg(Jenc.encode.pick(False{}, ww, hh, cp)), Img.decode_jpeg.out(Jpeg.decode.run(fr, sc, tb, ee, 0)),
    Equal.cong(Bool, Maybe<&2, Img.Raster>, bb => Img.decode_jpeg(Jenc.encode.pick(bb, ww, hh, cp)),
    Jenc.encode.bad(ww, hh), False{}, W7.bad_of_good(ww, hh, px, h_good, h_w, h_h)),
    Equal.trans(Maybe<&2, Img.Raster>, w8.out(Jpeg.decode.walk(List.append(&2, U32, hd, rr), Jpeg.decode.st0())),
    w8.out(Jpeg.decode.walk(rr, Jpeg.decode.walk(hd, Jpeg.decode.st0()))),
    Img.decode_jpeg.out(Jpeg.decode.run(fr, sc, tb, ee, 0)), Equal.cong(Jpeg.St, Maybe<&2, Img.Raster>,
    st => w8.out(st), Jpeg.decode.walk(List.append(&2, U32, hd, rr), Jpeg.decode.st0()), Jpeg.decode.walk(rr,
    Jpeg.decode.walk(hd, Jpeg.decode.st0())), W8.walk_app(hd, rr, Jpeg.decode.st0())),
    Equal.trans(Maybe<&2, Img.Raster>, w8.out(Jpeg.decode.walk(rr, Jpeg.decode.walk(hd, Jpeg.decode.st0()))),
    w8.out(Jpeg.decode.walk(rr, ent)), Img.decode_jpeg.out(Jpeg.decode.run(fr, sc, tb, ee, 0)),
    Equal.cong(Jpeg.St, Maybe<&2, Img.Raster>, st => w8.out(Jpeg.decode.walk(rr, st)), Jpeg.decode.walk(hd,
    Jpeg.decode.st0()), ent, Laws.jpeg_enc_header_walk(ww, hh)),
    Equal.trans(Maybe<&2, Img.Raster>, w8.out(Jpeg.decode.walk(rr, ent)), w8.out(stop),
    Img.decode_jpeg.out(Jpeg.decode.run(fr, sc, tb, ee, 0)), Equal.cong(Jpeg.St, Maybe<&2, Img.Raster>,
    st => w8.out(st), Jpeg.decode.walk(rr, ent), stop, Laws.jpeg_ent_walk(ee, Laws.jpeg_enc_stuffed(ww, hh, cp), fr,
    sc, tb, [], 0, 1, 0)), Equal.cong(List<&2, U32>, Maybe<&2, Img.Raster>, xs => Img.decode_jpeg.out(
    Jpeg.decode.run(fr, sc, tb, xs, 0)), List.reverse(&2, U32, List.reverse.go(&2, U32, ee, [])), ee,
    Flt.rev_rev(ee)))))))

def Laws.jpeg_run_sized(ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan, tabs, ent, ri):
  W10.run.sized(ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan, tabs, ent, ri)

def Laws.jpeg_round_trip_sized(ww, hh, px, h_good, h_w, h_h):
  +ee = Jenc.encode.arm(ww, hh, Img.colours(px))
  Equal.trans(Bool, Laws.jpg.sized(Laws.jpg.back(Img.encode_jpeg(Img.Raster{ww, hh, px})), ww, hh),
    Laws.jpg.sized(Img.decode_jpeg.out(Jpeg.decode.run(Laws.jpg.enc.frame(ww, hh), Laws.jpg.enc.scan(),
    Laws.jpg.enc.tabs(), ee, 0)), ww, hh), True{}, Equal.cong(Maybe<&2, Img.Raster>, Bool, mm => Laws.jpg.sized(mm, ww,
    hh), Laws.jpg.back(Img.encode_jpeg(Img.Raster{ww, hh, px})), Img.decode_jpeg.out(Jpeg.decode.run(
    Laws.jpg.enc.frame(ww, hh), Laws.jpg.enc.scan(), Laws.jpg.enc.tabs(), ee, 0)), Laws.jpeg_round_trip_scan(ww, hh,
    px, h_good, h_w, h_h)), Laws.jpeg_run_sized(ww, hh, 3, [1, 2, 3], [1, 1, 1], [1, 1, 1], [0, 0, 0], 1, 1,
    Laws.jpg.enc.scan(), Laws.jpg.enc.tabs(), ee, 0))

def Laws.jpeg_walk_count(ww, hh, ids, hs, vs, hmax, vmax, ns, sids, top, h_ns, h_units, h_sum, h_fit):
  W10.walk.count(Jpeg.decode.ceil(ww, (hmax * 8 : U32)), Jpeg.decode.ceil(hh, (vmax * 8 : U32)),
    Jpeg.decode.blocks.sum(hs, vs, 0), ns, sids, ids, hs, vs, top, W10.usum.pos(ns, sids, ids, hs, vs, h_ns, h_units),
    h_sum, h_fit)

def Laws.jpeg_unstuff(bs, ok):
  +xs = Laws.jpg.bytes(bs)
  +nn = List.length(&2, Laws.JByte, bs)
  Equal.trans(List<&2, U32>, Laws.jpg.read8(nn, Jpeg.decode.read.n(8, Jpeg.Bits{0, ok, 0,
    Jenc.encode.stuff.all(List.reverse(&2, U32, xs), [])})), Laws.jpg.read8(nn, Jpeg.decode.read.n(8, Jpeg.Bits{0, ok,
    0, W10.stf(xs, [])})), xs, Equal.cong(List<&2, U32>, List<&2, U32>, zs => Laws.jpg.read8(nn, Jpeg.decode.read.n(8,
    Jpeg.Bits{0, ok, 0, zs})), Jenc.encode.stuff.all(List.reverse(&2, U32, xs), []), W10.stf(xs, []),
    W10.stall.rev(xs, [], [])), W10.rd.list(bs, ok, []))

# ---- wp12-jpeg-huffman ----

def Laws.jpeg_bits_round_trip(cs, h_len):
  W12.round_trip(cs, h_len)

def Laws.jpeg_huff_dc(pre, h_pre, sy, h_sy, post, h_post):
  W12.huff_law.dc(pre, h_pre, sy, h_sy, post, h_post)

def Laws.jpeg_huff_ac(pre, h_pre, sy, h_sy, post, h_post):
  W12.huff_law.ac(pre, h_pre, sy, h_sy, post, h_post)
