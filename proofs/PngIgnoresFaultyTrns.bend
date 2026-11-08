# proofs of laws/PngIgnoresFaultyTrns.bend
import Base
import ../src/png.bend as Png
import ../laws/PngIgnoresFaultyTrns.bend as Laws
import ../laws/PngSamplesFollowColourType.bend as L1
import ./lemmas/BasicFacts.bend as M1
import ./lemmas/PngImageWalk.bend as M2
import ./PngSamplesFollowColourType.bend as P1

# a gray tRNS of other than two bytes is no key
def grey.none(
  trns: List<&2, U32>,
  h_len: {Nat.is_eq(List.length(&2, U32, trns), 2n) == False{} : Bool}
) -> {Png.key.grey(trns) == Png.KNone{} : Png.Key}:
  match trns:
    case Nil{}:
      {==}
    case _t0 <> t1:
      match t1:
        case Nil{}:
          {==}
        case _t2 <> t3:
          match t3:
            case Nil{}:
              Empty.absurd({Png.key.grey(_t0 <> _t2 <> Nil{}) == Png.KNone{} : Png.Key}, M1.pdec.true_false(h_len))
            case _t4 <> _t5:
              {==}

# an RGB tRNS of other than six bytes is no key
def rgb.none(
  trns: List<&2, U32>,
  h_len: {Nat.is_eq(List.length(&2, U32, trns), 6n) == False{} : Bool}
) -> {Png.key.rgb(trns) == Png.KNone{} : Png.Key}:
  match trns:
    case Nil{}:
      {==}
    case _a0 <> a1:
      match a1:
        case Nil{}:
          {==}
        case _b0 <> b1:
          match b1:
            case Nil{}:
              {==}
            case _c0 <> c1:
              match c1:
                case Nil{}:
                  {==}
                case _d0 <> d1:
                  match d1:
                    case Nil{}:
                      {==}
                    case _e0 <> e1:
                      match e1:
                        case Nil{}:
                          {==}
                        case _f0 <> f1:
                          match f1:
                            case Nil{}:
                              Empty.absurd({Png.key.rgb(_a0 <> _b0 <> _c0 <> _d0 <> _e0 <> _f0 <> Nil{}) == Png.KNone{}
                                : Png.Key}, M1.pdec.true_false(h_len))
                            case _g0 <> _g1:
                              {==}

def Laws.png_trns_grey_len(xs, _plte, trns, h_len):
  Equal.trans(Maybe<&2, List<&2, U32>>, Png.px.grey(xs, Png.key.grey(trns), []), Png.px.grey(xs, Png.KNone{}, []),
    Some{L1.spec.grey(xs)},
    Equal.cong(Png.Key, Maybe<&2, List<&2, U32>>, kk => Png.px.grey(xs, kk, []), Png.key.grey(trns), Png.KNone{},
      grey.none(trns, h_len)),
    L1.png_px_grey(xs))

def Laws.png_trns_rgb_len(xs, plte, trns, h_len):
  Equal.trans(Maybe<&2, List<&2, U32>>, Png.px.rgb(xs, Png.key.rgb(trns), []), Png.px.rgb(xs, Png.KNone{}, []),
    L1.spec.rgb(xs),
    Equal.cong(Png.Key, Maybe<&2, List<&2, U32>>, kk => Png.px.rgb(xs, kk, []), Png.key.rgb(trns), Png.KNone{},
      rgb.none(trns, h_len)),
    L1.png_px_rgb(xs, plte))

# gray at each bit depth reads tRNS only through its key
def grey.deep(
  z8: Bool,
  z16: Bool,
  +dd: U32,
  +xs: List<&2, U32>,
  +plte: List<&2, U32>,
  +trns: List<&2, U32>,
  ek: {Png.key.grey(trns) == Png.KNone{} : Png.Key}
) -> {Png.px.deep.at(z8, z16, 0, dd, xs, plte, trns) == Png.px.deep.at(z8, z16, 0, dd, xs, plte, [])
  : Maybe<&2, List<&2, U32>>}:
  match z8 z16:
    case True{} _z16:
      Equal.cong(Png.Key, Maybe<&2, List<&2, U32>>, kk => Png.px.grey(xs, kk, []), Png.key.grey(trns), Png.KNone{}, ek)
    case False{} True{}:
      Equal.cong(Png.Key, Maybe<&2, List<&2, U32>>, kk => Png.px.grey16(xs, kk, []), Png.key.grey(trns), Png.KNone{},
        ek)
    case False{} False{}:
      Equal.cong(Png.Key, Maybe<&2, List<&2, U32>>, kk => Png.px.grey.low(U32.sub(U32.shln(1, U32.to_nat(dd)), 1), xs,
        kk, []), Png.key.grey(trns), Png.KNone{}, ek)

def Laws.png_trns_grey_deep(dd, xs, plte, trns, h_len):
  grey.deep(U32.is_eq(dd, 8), U32.is_eq(dd, 16), dd, xs, plte, trns, grey.none(trns, h_len))

# RGB at 8 and 16 bits reads tRNS only through its key
def rgb.deep(
  z8: Bool,
  z16: Bool,
  +dd: U32,
  +xs: List<&2, U32>,
  +plte: List<&2, U32>,
  +trns: List<&2, U32>,
  h_dd: {Bool.or(z8, z16) == True{} : Bool},
  ek: {Png.key.rgb(trns) == Png.KNone{} : Png.Key}
) -> {Png.px.deep.at(z8, z16, 2, dd, xs, plte, trns) == Png.px.deep.at(z8, z16, 2, dd, xs, plte, [])
  : Maybe<&2, List<&2, U32>>}:
  match z8 z16:
    case True{} _z16:
      Equal.cong(Png.Key, Maybe<&2, List<&2, U32>>, kk => Png.px.rgb(xs, kk, []), Png.key.rgb(trns), Png.KNone{}, ek)
    case False{} True{}:
      Equal.cong(Png.Key, Maybe<&2, List<&2, U32>>, kk => Png.px.rgb16(xs, kk, []), Png.key.rgb(trns), Png.KNone{}, ek)
    case False{} False{}:
      Empty.absurd({Png.px.deep.at(False{}, False{}, 2, dd, xs, plte, trns) == Png.px.deep.at(False{}, False{}, 2, dd,
        xs, plte, []) : Maybe<&2, List<&2, U32>>}, M1.false_true(h_dd))

def Laws.png_trns_rgb_deep(dd, xs, plte, trns, h_dd, h_len):
  rgb.deep(U32.is_eq(dd, 8), U32.is_eq(dd, 16), dd, xs, plte, trns, h_dd, rgb.none(trns, h_len))

# not true is false
def not.true(bb: Bool, hh: {Bool.not(bb) == True{} : Bool}) -> {bb == False{} : Bool}:
  match bb:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, M1.false_true(hh))
    case False{}:
      {==}

# the take test for a misplaced tRNS before any IDAT is false
def take.false(
  st: Bool,
  +ok: Bool,
  h_bad: {Bool.or(st, Bool.not(ok)) == True{} : Bool}
) -> {Bool.and(Bool.not(st), ok) == False{} : Bool}:
  match st:
    case True{}:
      {==}
    case False{}:
      not.true(ok, h_bad)

def Laws.png_trns_placed(ww, hh, dd, cc, comp, ff, ii, idat, plte, trns, run, data, h_bad):
  match run:
    case Png.RNone{}:
      +pg = {Png.Pg{ww, hh, dd, cc, comp, ff, ii, idat, plte, trns, Png.RNone{}} : Png.Pg}
      +ok = Png.png.trns.ok(cc, Maybe.is_some(&2, List<&2, U32>, plte))
      +st = Maybe.is_some(&2, List<&2, U32>, trns)
      Equal.cong(Bool, Png.Nx, zz => Png.png.trns.take(zz, data, pg), Bool.and(Bool.not(st), ok), False{},
        take.false(st, ok, h_bad))
    case Png.ROpen{}:
      {==}
    case Png.RShut{}:
      {==}
