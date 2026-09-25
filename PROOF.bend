# ezimg: the proofs. `bend PROOF.bend` is the gate: its first line must be
# exactly `All terms check.`
import Base
import ./LAWS.bend as Laws
import ./proof/u32.bend as U32L
import ./proof/wp4-png-encode.bend as Wp4
import ./main.bend as Img
import ./src/png.bend as Png
import ./src/jpeg.bend as Jpeg

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
def lt.nat(+cc: U32, +ww: U32, zz: Bool, ee: {U32.is_lt(cc, ww) == zz : Bool}) ->
  {Cmp.is_lt(Nat.cmp(U32.to_nat(cc), U32.to_nat(ww))) == zz : Bool}:
  Equal.trans(Bool, Cmp.is_lt(Nat.cmp(U32.to_nat(cc), U32.to_nat(ww))), U32.is_lt(cc, ww), zz,
    Equal.cong(Cmp, Bool, xx => Cmp.is_lt(xx), Nat.cmp(U32.to_nat(cc), U32.to_nat(ww)), U32.cmp(cc, ww),
      Equal.sym(Cmp, U32.cmp(cc, ww), Nat.cmp(U32.to_nat(cc), U32.to_nat(ww)), Wp4.u32_cmp_nat(cc, ww))), ee)

# U32.is_zero as Nat equality with 0
def zero.nat(+hh: U32, zz: Bool, ee: {U32.is_zero(hh) == zz : Bool}) ->
  {Cmp.is_eq(Nat.cmp(U32.to_nat(hh), 0n)) == zz : Bool}:
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
def rows.done(+hh: U32, +cc: U32, +ww: U32, e_zh: {U32.is_zero(hh) == True{} : Bool}) ->
  {U32.is_zero(cc) == Nat.is_eq(U32.to_nat(cc), Nat.mul(U32.to_nat(hh), U32.to_nat(ww))) : Bool}:
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
    Equal.cong(Nat, Nat, xx => Nat.add(xx, Nat.add(ef, wp)), dd, U32.to_nat(c2), Equal.sym(Nat, U32.to_nat(c2), dd, e_c2))) :
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
      +hb2 = {Equal.trans(Bool, Laws.below(32n, Nat.add(U32.to_nat(n1), lt)), Laws.below(32n, 1n+Nat.add(vn, lt)), True{},
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
