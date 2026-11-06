# proofs of laws/PngSamplesFollowBitDepth.bend
import Base
import ../src/png.bend as Png
import ../laws/PngSamplesFollowBitDepth.bend as Laws
import ../laws/PngSamplesFollowColourType.bend as L1
import ./lemmas/BasicFacts.bend as M1
import ./lemmas/PngChunkWalker.bend as M2
import ./lemmas/PngImageWalk.bend as M3
import ./PngSamplesFollowColourType.bend as P1

# ---- unpacking ----

# every 16-bit pair of a row, pushed onto acc newest first
def wide.acc(
  row: List<&2, U32>,
  +acc: List<&2, U32>
) -> {Png.unpack.wide(row, acc) == List.reverse.go(&2, U32, Laws.spec.pairs(row), acc) : List<&2, U32>}:
  match row:
    case Nil{}:
      {==}
    case +hi <> tl:
      match tl:
        case Nil{}:
          {==}
        case +lo <> rest:
          wide.acc(rest, Laws.spec.u16(hi, lo) <> acc)

def Laws.png_unpack_16(_count, row):
  Equal.trans(List<&2, U32>, List.reverse(&2, U32, Png.unpack.wide(row, [])), List.reverse(&2, U32,
    List.reverse.go(&2, U32, Laws.spec.pairs(row), [])), Laws.spec.pairs(row),
    Equal.cong(List<&2, U32>, List<&2, U32>, xs => List.reverse(&2, U32, xs), Png.unpack.wide(row, []),
      List.reverse.go(&2, U32, Laws.spec.pairs(row), []), wide.acc(row, [])),
    M1.inf.rev_rev(Laws.spec.pairs(row)))

def Laws.png_unpack_8(_count, _row):
  {==}

# every sample of a row at bit depth 1, pushed onto acc newest first
def low1.acc(
  row: List<&2, U32>,
  +acc: List<&2, U32>
) -> {Png.unpack.low(1, row, acc) == List.reverse.go(&2, U32, Laws.spec.samples(1, row), acc) : List<&2, U32>}:
  match row:
    case Nil{}:
      {==}
    case +bb <> +tl:
      +by = Laws.spec.byte(1, bb)
      +st = Laws.spec.samples(1, tl)
      Equal.trans(List<&2, U32>, Png.unpack.low(1, tl, Png.unpack.byte(U32.is_eq(1, 1), U32.is_eq(1, 2), bb, acc)),
        List.reverse.go(&2, U32, st, Png.unpack.byte(U32.is_eq(1, 1), U32.is_eq(1, 2), bb, acc)),
        List.reverse.go(&2, U32, List.append(&2, U32, by, st), acc),
        low1.acc(tl, Png.unpack.byte(U32.is_eq(1, 1), U32.is_eq(1, 2), bb, acc)),
        Equal.sym(List<&2, U32>, List.reverse.go(&2, U32, List.append(&2, U32, by, st), acc),
          List.reverse.go(&2, U32, st, Png.unpack.byte(U32.is_eq(1, 1), U32.is_eq(1, 2), bb, acc)),
          M2.revgo_app(by, st, acc)))

def Laws.png_unpack_1(count, row):
  +ss = Laws.spec.samples(1, row)
  Equal.trans(List<&2, U32>, List.take(&2, U32, List.reverse(&2, U32, Png.unpack.low(1, row, [])), count),
    List.take(&2, U32, List.reverse(&2, U32, List.reverse.go(&2, U32, ss, [])), count), List.take(&2, U32, ss, count),
    Equal.cong(List<&2, U32>, List<&2, U32>, xs => List.take(&2, U32, List.reverse(&2, U32, xs), count),
      Png.unpack.low(1, row, []), List.reverse.go(&2, U32, ss, []), low1.acc(row, [])),
    Equal.cong(List<&2, U32>, List<&2, U32>, xs => List.take(&2, U32, xs, count), List.reverse(&2, U32,
      List.reverse.go(&2, U32, ss, [])), ss, M1.inf.rev_rev(ss)))

# every sample of a row at bit depth 2, pushed onto acc newest first
def low2.acc(
  row: List<&2, U32>,
  +acc: List<&2, U32>
) -> {Png.unpack.low(2, row, acc) == List.reverse.go(&2, U32, Laws.spec.samples(2, row), acc) : List<&2, U32>}:
  match row:
    case Nil{}:
      {==}
    case +bb <> +tl:
      +by = Laws.spec.byte(2, bb)
      +st = Laws.spec.samples(2, tl)
      Equal.trans(List<&2, U32>, Png.unpack.low(2, tl, Png.unpack.byte(U32.is_eq(2, 1), U32.is_eq(2, 2), bb, acc)),
        List.reverse.go(&2, U32, st, Png.unpack.byte(U32.is_eq(2, 1), U32.is_eq(2, 2), bb, acc)),
        List.reverse.go(&2, U32, List.append(&2, U32, by, st), acc),
        low2.acc(tl, Png.unpack.byte(U32.is_eq(2, 1), U32.is_eq(2, 2), bb, acc)),
        Equal.sym(List<&2, U32>, List.reverse.go(&2, U32, List.append(&2, U32, by, st), acc),
          List.reverse.go(&2, U32, st, Png.unpack.byte(U32.is_eq(2, 1), U32.is_eq(2, 2), bb, acc)),
          M2.revgo_app(by, st, acc)))

def Laws.png_unpack_2(count, row):
  +ss = Laws.spec.samples(2, row)
  Equal.trans(List<&2, U32>, List.take(&2, U32, List.reverse(&2, U32, Png.unpack.low(2, row, [])), count),
    List.take(&2, U32, List.reverse(&2, U32, List.reverse.go(&2, U32, ss, [])), count), List.take(&2, U32, ss, count),
    Equal.cong(List<&2, U32>, List<&2, U32>, xs => List.take(&2, U32, List.reverse(&2, U32, xs), count),
      Png.unpack.low(2, row, []), List.reverse.go(&2, U32, ss, []), low2.acc(row, [])),
    Equal.cong(List<&2, U32>, List<&2, U32>, xs => List.take(&2, U32, xs, count), List.reverse(&2, U32,
      List.reverse.go(&2, U32, ss, [])), ss, M1.inf.rev_rev(ss)))

# every sample of a row at bit depth 4, pushed onto acc newest first
def low4.acc(
  row: List<&2, U32>,
  +acc: List<&2, U32>
) -> {Png.unpack.low(4, row, acc) == List.reverse.go(&2, U32, Laws.spec.samples(4, row), acc) : List<&2, U32>}:
  match row:
    case Nil{}:
      {==}
    case +bb <> +tl:
      +by = Laws.spec.byte(4, bb)
      +st = Laws.spec.samples(4, tl)
      Equal.trans(List<&2, U32>, Png.unpack.low(4, tl, Png.unpack.byte(U32.is_eq(4, 1), U32.is_eq(4, 2), bb, acc)),
        List.reverse.go(&2, U32, st, Png.unpack.byte(U32.is_eq(4, 1), U32.is_eq(4, 2), bb, acc)),
        List.reverse.go(&2, U32, List.append(&2, U32, by, st), acc),
        low4.acc(tl, Png.unpack.byte(U32.is_eq(4, 1), U32.is_eq(4, 2), bb, acc)),
        Equal.sym(List<&2, U32>, List.reverse.go(&2, U32, List.append(&2, U32, by, st), acc),
          List.reverse.go(&2, U32, st, Png.unpack.byte(U32.is_eq(4, 1), U32.is_eq(4, 2), bb, acc)),
          M2.revgo_app(by, st, acc)))

def Laws.png_unpack_4(count, row):
  +ss = Laws.spec.samples(4, row)
  Equal.trans(List<&2, U32>, List.take(&2, U32, List.reverse(&2, U32, Png.unpack.low(4, row, [])), count),
    List.take(&2, U32, List.reverse(&2, U32, List.reverse.go(&2, U32, ss, [])), count), List.take(&2, U32, ss, count),
    Equal.cong(List<&2, U32>, List<&2, U32>, xs => List.take(&2, U32, List.reverse(&2, U32, xs), count),
      Png.unpack.low(4, row, []), List.reverse.go(&2, U32, ss, []), low4.acc(row, [])),
    Equal.cong(List<&2, U32>, List<&2, U32>, xs => List.take(&2, U32, xs, count), List.reverse(&2, U32,
      List.reverse.go(&2, U32, ss, [])), ss, M1.inf.rev_rev(ss)))

# ---- the depth's dispatch ----

# a depth of 1, 2 or 4 is not kk, when none of 1, 2 and 4 is
def low.ne(
  z1: Bool,
  z2: Bool,
  z4: Bool,
  +dd: U32,
  +kk: U32,
  e1: {U32.is_eq(dd, 1) == z1 : Bool},
  e2: {U32.is_eq(dd, 2) == z2 : Bool},
  e4: {U32.is_eq(dd, 4) == z4 : Bool},
  hh: {Bool.or(z1, Bool.or(z2, z4)) == True{} : Bool},
  k1: {U32.is_eq(1, kk) == False{} : Bool},
  k2: {U32.is_eq(2, kk) == False{} : Bool},
  k4: {U32.is_eq(4, kk) == False{} : Bool}
) -> {U32.is_eq(dd, kk) == False{} : Bool}:
  match z1 z2 z4:
    case True{} _z2 _z4:
      Equal.trans(Bool, U32.is_eq(dd, kk), U32.is_eq(1, kk), False{}, Equal.cong(U32, Bool, uu => U32.is_eq(uu, kk), dd,
        1, M1.ueq(dd, 1, e1)), k1)
    case False{} True{} _z4:
      Equal.trans(Bool, U32.is_eq(dd, kk), U32.is_eq(2, kk), False{}, Equal.cong(U32, Bool, uu => U32.is_eq(uu, kk), dd,
        2, M1.ueq(dd, 2, e2)), k2)
    case False{} False{} True{}:
      Equal.trans(Bool, U32.is_eq(dd, kk), U32.is_eq(4, kk), False{}, Equal.cong(U32, Bool, uu => U32.is_eq(uu, kk), dd,
        4, M1.ueq(dd, 4, e4)), k4)
    case False{} False{} False{}:
      Empty.absurd({U32.is_eq(dd, kk) == False{} : Bool}, M1.false_true(hh))

# a low depth is not 8
def low.n8(+dd: U32, hh: {Laws.spec.low(dd) == True{} : Bool}) -> {U32.is_eq(dd, 8) == False{} : Bool}:
  low.ne(U32.is_eq(dd, 1), U32.is_eq(dd, 2), U32.is_eq(dd, 4), dd, 8, {==}, {==}, {==}, hh, {==}, {==}, {==})

# a low depth is not 16
def low.n16(+dd: U32, hh: {Laws.spec.low(dd) == True{} : Bool}) -> {U32.is_eq(dd, 16) == False{} : Bool}:
  low.ne(U32.is_eq(dd, 1), U32.is_eq(dd, 2), U32.is_eq(dd, 4), dd, 16, {==}, {==}, {==}, hh, {==}, {==}, {==})

# px.deep at a low depth is px.low
def low.deep(
  +cc: U32,
  +dd: U32,
  +xs: List<&2, U32>,
  +plte: List<&2, U32>,
  +trns: List<&2, U32>,
  +hh: {Laws.spec.low(dd) == True{} : Bool}
) -> {Png.px.deep(cc, dd, xs, plte, trns) == Png.px.low(cc, dd, xs, plte, trns) : Maybe<&2, List<&2, U32>>}:
  Equal.trans(Maybe<&2, List<&2, U32>>, Png.px.deep.at(U32.is_eq(dd, 8), U32.is_eq(dd, 16), cc, dd, xs, plte, trns),
    Png.px.deep.at(False{}, U32.is_eq(dd, 16), cc, dd, xs, plte, trns), Png.px.low(cc, dd, xs, plte, trns),
    Equal.cong(Bool, Maybe<&2, List<&2, U32>>, zz => Png.px.deep.at(zz, U32.is_eq(dd, 16), cc, dd, xs, plte, trns),
      U32.is_eq(dd, 8), False{}, low.n8(dd, hh)),
    Equal.cong(Bool, Maybe<&2, List<&2, U32>>, zz => Png.px.deep.at(False{}, zz, cc, dd, xs, plte, trns),
      U32.is_eq(dd, 16), False{}, low.n16(dd, hh)))

# ---- packing ----

# a word or'd onto zero is the word
def wor.zero(nn: Nat, ww: Word(nn)) -> {Word.or(nn, Word.zero(nn), ww) == ww : Word(nn)}:
  match nn:
    case 0n:
      match ww:
        case WNil{}:
          {==}
    case 1n+pp:
      match ww:
        case WCon{+bb, tt}:
          Equal.cong(Word(pp), Word.Con<pp>, vv => WCon{bb, vv}, Word.or(pp, Word.zero(pp), tt), tt, wor.zero(pp, tt))

# zero shifted up and or'd onto a value is the value
def or.zero(uu: U32) -> {Laws.spec.u16(0, uu) == uu : U32}:
  match uu:
    case U32{ww}:
      Equal.cong(Word(32n), U32, vv => U32{vv}, Word.or(32n, Word.zero(32n), ww), ww, wor.zero(32n, ww))

# a 16-bit tRNS value read as the specification reads it
def u16.same(
  zz: Bool,
  +hi: U32,
  +lo: U32,
  ez: {U32.is_zero(hi) == zz : Bool}
) -> {Png.key.u16(zz, hi, lo) == Laws.spec.u16(hi, lo) : U32}:
  match zz:
    case False{}:
      {==}
    case True{}:
      +e0 = {M1.ueq(hi, 0, ez) : {hi == 0 : U32}}
      Equal.trans(U32, lo, Laws.spec.u16(0, lo), Laws.spec.u16(hi, lo), Equal.sym(U32, Laws.spec.u16(0, lo), lo,
        or.zero(lo)), Equal.cong(U32, U32, uu => Laws.spec.u16(uu, lo), 0, hi, Equal.sym(U32, hi, 0, e0)))

# low gray without a key
def glow.acc(
  +dd: U32,
  xs: List<&2, U32>,
  +acc: List<&2, U32>
) -> {Png.px.grey.low(Laws.spec.max(dd), xs, Png.KNone{}, acc) == Some{List.reverse.go(&2, U32, acc,
  Laws.spec.grey.low(dd, xs, None{}))} : Maybe<&2, List<&2, U32>>}:
  match xs:
    case Nil{}:
      {==}
    case +gg <> tl:
      glow.acc(dd, tl, Png.px.pack(255, Png.px.up(Laws.spec.max(dd), gg), Png.px.up(Laws.spec.max(dd), gg),
        Png.px.up(Laws.spec.max(dd), gg)) <> acc)

# low gray with a key
def glow.key(
  +dd: U32,
  xs: List<&2, U32>,
  +kk: U32,
  +acc: List<&2, U32>
) -> {Png.px.grey.low(Laws.spec.max(dd), xs, Png.KGrey{kk}, acc) == Some{List.reverse.go(&2, U32, acc,
  Laws.spec.grey.low(dd, xs, Some{kk}))} : Maybe<&2, List<&2, U32>>}:
  match xs:
    case Nil{}:
      {==}
    case +gg <> +tl:
      +up = Png.px.up(Laws.spec.max(dd), gg)
      Equal.trans(Maybe<&2, List<&2, U32>>,
        Png.px.grey.low(Laws.spec.max(dd), tl, Png.KGrey{kk}, Png.px.pack(Png.px.hit(gg, kk), up, up, up) <> acc),
        Some{List.reverse.go(&2, U32, acc, Png.px.pack(Png.px.hit(gg, kk), up, up, up) <> Laws.spec.grey.low(dd, tl,
          Some{kk}))},
        Some{List.reverse.go(&2, U32, acc, L1.spec.argb(L1.spec.key.alpha(U32.is_eq(gg, kk)), up, up, up) <>
          Laws.spec.grey.low(dd, tl, Some{kk}))},
        glow.key(dd, tl, kk, Png.px.pack(Png.px.hit(gg, kk), up, up, up) <> acc),
        Equal.cong(U32, Maybe<&2, List<&2, U32>>,
          aa => Some{List.reverse.go(&2, U32, acc, L1.spec.argb(aa, up, up, up) <> Laws.spec.grey.low(dd, tl,
            Some{kk}))}, Png.px.hit.at(U32.is_eq(gg, kk)), L1.spec.key.alpha(U32.is_eq(gg, kk)),
          P1.hit.alpha(U32.is_eq(gg, kk))))

def Laws.png_px_grey_low(dd, xs, plte, h_dd):
  Equal.trans(Maybe<&2, List<&2, U32>>, Png.px.deep(0, dd, xs, plte, []), Png.px.low(0, dd, xs, plte, []),
    Some{Laws.spec.grey.low(dd, xs, None{})}, low.deep(0, dd, xs, plte, [], h_dd), glow.acc(dd, xs, []))

def Laws.png_px_grey_low_key(dd, xs, plte, k1, k0, h_dd):
  +kk = Png.key.u16(U32.is_zero(k1), k1, k0)
  Equal.trans(Maybe<&2, List<&2, U32>>, Png.px.deep(0, dd, xs, plte, [k1, k0]), Png.px.low(0, dd, xs, plte, [k1, k0]),
    Some{Laws.spec.grey.low(dd, xs, Some{Laws.spec.u16(k1, k0)})}, low.deep(0, dd, xs, plte, [k1, k0], h_dd),
    Equal.trans(Maybe<&2, List<&2, U32>>, Png.px.grey.low(Laws.spec.max(dd), xs, Png.KGrey{kk}, []),
      Some{Laws.spec.grey.low(dd, xs, Some{kk})}, Some{Laws.spec.grey.low(dd, xs, Some{Laws.spec.u16(k1, k0)})},
      glow.key(dd, xs, kk, []),
      Equal.cong(U32, Maybe<&2, List<&2, U32>>, uu => Some{Laws.spec.grey.low(dd, xs, Some{uu})}, kk,
        Laws.spec.u16(k1, k0), u16.same(U32.is_zero(k1), k1, k0, {==}))))

# 16-bit gray without a key
def g16.acc(
  xs: List<&2, U32>,
  +acc: List<&2, U32>
) -> {Png.px.grey16(xs, Png.KNone{}, acc) == Some{List.reverse.go(&2, U32, acc, Laws.spec.grey16(xs, None{}))}
  : Maybe<&2, List<&2, U32>>}:
  match xs:
    case Nil{}:
      {==}
    case +gg <> tl:
      g16.acc(tl, Png.px.pack(255, Png.px.hi(gg), Png.px.hi(gg), Png.px.hi(gg)) <> acc)

# 16-bit gray with a key
def g16.key(
  xs: List<&2, U32>,
  +kk: U32,
  +acc: List<&2, U32>
) -> {Png.px.grey16(xs, Png.KGrey{kk}, acc) == Some{List.reverse.go(&2, U32, acc, Laws.spec.grey16(xs, Some{kk}))}
  : Maybe<&2, List<&2, U32>>}:
  match xs:
    case Nil{}:
      {==}
    case +gg <> +tl:
      +hv = Png.px.hi(gg)
      Equal.trans(Maybe<&2, List<&2, U32>>,
        Png.px.grey16(tl, Png.KGrey{kk}, Png.px.pack(Png.px.hit(gg, kk), hv, hv, hv) <> acc),
        Some{List.reverse.go(&2, U32, acc, Png.px.pack(Png.px.hit(gg, kk), hv, hv, hv) <> Laws.spec.grey16(tl,
          Some{kk}))},
        Some{List.reverse.go(&2, U32, acc, L1.spec.argb(L1.spec.key.alpha(U32.is_eq(gg, kk)), hv, hv, hv) <>
          Laws.spec.grey16(tl, Some{kk}))},
        g16.key(tl, kk, Png.px.pack(Png.px.hit(gg, kk), hv, hv, hv) <> acc),
        Equal.cong(U32, Maybe<&2, List<&2, U32>>,
          aa => Some{List.reverse.go(&2, U32, acc, L1.spec.argb(aa, hv, hv, hv) <> Laws.spec.grey16(tl, Some{kk}))},
          Png.px.hit.at(U32.is_eq(gg, kk)), L1.spec.key.alpha(U32.is_eq(gg, kk)), P1.hit.alpha(U32.is_eq(gg, kk))))

def Laws.png_px_grey16(xs, _plte):
  g16.acc(xs, [])

def Laws.png_px_grey16_key(xs, _plte, k1, k0):
  +kk = Png.key.u16(U32.is_zero(k1), k1, k0)
  Equal.trans(Maybe<&2, List<&2, U32>>, Png.px.grey16(xs, Png.KGrey{kk}, []), Some{Laws.spec.grey16(xs, Some{kk})},
    Some{Laws.spec.grey16(xs, Some{Laws.spec.u16(k1, k0)})}, g16.key(xs, kk, []),
    Equal.cong(U32, Maybe<&2, List<&2, U32>>, uu => Some{Laws.spec.grey16(xs, Some{uu})}, kk, Laws.spec.u16(k1, k0),
      u16.same(U32.is_zero(k1), k1, k0, {==})))

# 16-bit RGB, with or without a key: what rgb16.acc proves
def rgb16.ty(xs: List<&2, U32>, key: Png.Key, skey: Maybe<&2, Laws.Key3>, +acc: List<&2, U32>) -> Type:
  {Png.px.rgb16(xs, key, acc) == M1.onto(acc, Laws.spec.rgb16(xs, skey)) : Maybe<&2, List<&2, U32>>}

# 16-bit RGB without a key
def rgb16.acc(xs: List<&2, U32>, +acc: List<&2, U32>) -> rgb16.ty(xs, Png.KNone{}, None{}, acc):
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
              +pk = Png.px.pack(255, Png.px.hi(rr), Png.px.hi(gg), Png.px.hi(bb))
              Equal.trans(Maybe<&2, List<&2, U32>>, Png.px.rgb16(tl, Png.KNone{}, pk <> acc),
                M1.onto(pk <> acc, Laws.spec.rgb16(tl, None{})),
                M1.onto(acc, L1.spec.cons(pk, Laws.spec.rgb16(tl, None{}))),
                rgb16.acc(tl, pk <> acc), M3.onto.cons(pk, acc, Laws.spec.rgb16(tl, None{})))

# 16-bit RGB with a key
def rgb16.key(
  xs: List<&2, U32>,
  +kr: U32,
  +kg: U32,
  +kb: U32,
  +acc: List<&2, U32>
) -> rgb16.ty(xs, Png.KRgb{kr, kg, kb}, Some{Laws.Key3{kr, kg, kb}}, acc):
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
              +hit = Bool.and(U32.is_eq(rr, kr), Bool.and(U32.is_eq(gg, kg), U32.is_eq(bb, kb)))
              +pk = Png.px.pack(Png.px.rgb.hit(rr, gg, bb, kr, kg, kb), Png.px.hi(rr), Png.px.hi(gg), Png.px.hi(bb))
              +sk = L1.spec.argb(L1.spec.key.alpha(hit), Png.px.hi(rr), Png.px.hi(gg), Png.px.hi(bb))
              +sp = Laws.spec.rgb16(tl, Some{Laws.Key3{kr, kg, kb}})
              Equal.trans(Maybe<&2, List<&2, U32>>, Png.px.rgb16(tl, Png.KRgb{kr, kg, kb}, pk <> acc),
                M1.onto(pk <> acc, sp), M1.onto(acc, L1.spec.cons(sk, sp)),
                rgb16.key(tl, kr, kg, kb, pk <> acc),
                Equal.trans(Maybe<&2, List<&2, U32>>, M1.onto(pk <> acc, sp), M1.onto(sk <> acc, sp),
                  M1.onto(acc, L1.spec.cons(sk, sp)),
                  Equal.cong(U32, Maybe<&2, List<&2, U32>>,
                    aa => M1.onto(L1.spec.argb(aa, Png.px.hi(rr), Png.px.hi(gg), Png.px.hi(bb)) <> acc, sp),
                    Png.px.hit.at(hit), L1.spec.key.alpha(hit), P1.hit.alpha(hit)),
                  M3.onto.cons(sk, acc, sp)))

def Laws.png_px_rgb16(xs, _plte):
  Equal.trans(Maybe<&2, List<&2, U32>>, Png.px.rgb16(xs, Png.KNone{}, []), M1.onto([], Laws.spec.rgb16(xs, None{})),
    Laws.spec.rgb16(xs, None{}), rgb16.acc(xs, []), M3.onto.nil(Laws.spec.rgb16(xs, None{})))

def Laws.png_px_rgb16_key(xs, _plte, r1, r0, g1, g0, b1, b0):
  +kr = Png.key.u16(U32.is_zero(r1), r1, r0)
  +kg = Png.key.u16(U32.is_zero(g1), g1, g0)
  +kb = Png.key.u16(U32.is_zero(b1), b1, b0)
  +sr = Laws.spec.u16(r1, r0)
  +sg = Laws.spec.u16(g1, g0)
  +sb = Laws.spec.u16(b1, b0)
  +er = {u16.same(U32.is_zero(r1), r1, r0, {==}) : {kr == sr : U32}}
  +eg = {u16.same(U32.is_zero(g1), g1, g0, {==}) : {kg == sg : U32}}
  +eb = {u16.same(U32.is_zero(b1), b1, b0, {==}) : {kb == sb : U32}}
  Equal.trans(Maybe<&2, List<&2, U32>>, Png.px.rgb16(xs, Png.KRgb{kr, kg, kb}, []),
    Laws.spec.rgb16(xs, Some{Laws.Key3{kr, kg, kb}}), Laws.spec.rgb16(xs, Some{Laws.Key3{sr, sg, sb}}),
    Equal.trans(Maybe<&2, List<&2, U32>>, Png.px.rgb16(xs, Png.KRgb{kr, kg, kb}, []),
      M1.onto([], Laws.spec.rgb16(xs, Some{Laws.Key3{kr, kg, kb}})), Laws.spec.rgb16(xs, Some{Laws.Key3{kr, kg, kb}}),
      rgb16.key(xs, kr, kg, kb, []), M3.onto.nil(Laws.spec.rgb16(xs, Some{Laws.Key3{kr, kg, kb}}))),
    Equal.trans(Maybe<&2, List<&2, U32>>, Laws.spec.rgb16(xs, Some{Laws.Key3{kr, kg, kb}}),
      Laws.spec.rgb16(xs, Some{Laws.Key3{sr, kg, kb}}), Laws.spec.rgb16(xs, Some{Laws.Key3{sr, sg, sb}}),
      Equal.cong(U32, Maybe<&2, List<&2, U32>>, uu => Laws.spec.rgb16(xs, Some{Laws.Key3{uu, kg, kb}}), kr, sr, er),
      Equal.trans(Maybe<&2, List<&2, U32>>, Laws.spec.rgb16(xs, Some{Laws.Key3{sr, kg, kb}}),
        Laws.spec.rgb16(xs, Some{Laws.Key3{sr, sg, kb}}), Laws.spec.rgb16(xs, Some{Laws.Key3{sr, sg, sb}}),
        Equal.cong(U32, Maybe<&2, List<&2, U32>>, uu => Laws.spec.rgb16(xs, Some{Laws.Key3{sr, uu, kb}}), kg, sg, eg),
        Equal.cong(U32, Maybe<&2, List<&2, U32>>, uu => Laws.spec.rgb16(xs, Some{Laws.Key3{sr, sg, uu}}), kb, sb, eb))))

# 16-bit gray and alpha: the high bytes, packed as 8-bit gray and alpha
def ga16.same(xs: List<&2, U32>) -> {L1.spec.ga(Png.px.his(xs)) == Laws.spec.ga16(xs) : Maybe<&2, List<&2, U32>>}:
  match xs:
    case Nil{}:
      {==}
    case +gg <> t1:
      match t1:
        case Nil{}:
          {==}
        case +aa <> tl:
          Equal.cong(Maybe<&2, List<&2, U32>>, Maybe<&2, List<&2, U32>>, mm => L1.spec.cons(L1.spec.argb(Png.px.hi(aa),
            Png.px.hi(gg), Png.px.hi(gg), Png.px.hi(gg)), mm), L1.spec.ga(Png.px.his(tl)), Laws.spec.ga16(tl),
            ga16.same(tl))

# 16-bit RGBA: the high bytes, packed as 8-bit RGBA
def rgba16.same(
  xs: List<&2, U32>
) -> {L1.spec.rgba(Png.px.his(xs)) == Laws.spec.rgba16(xs) : Maybe<&2, List<&2, U32>>}:
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
                case +aa <> tl:
                  Equal.cong(Maybe<&2, List<&2, U32>>, Maybe<&2, List<&2, U32>>, mm =>
                    L1.spec.cons(L1.spec.argb(Png.px.hi(aa), Png.px.hi(rr), Png.px.hi(gg), Png.px.hi(bb)), mm),
                    L1.spec.rgba(Png.px.his(tl)), Laws.spec.rgba16(tl), rgba16.same(tl))

def Laws.png_px_ga16(xs, plte, trns):
  Equal.trans(Maybe<&2, List<&2, U32>>, Png.px.ga(Png.px.his(xs), []), L1.spec.ga(Png.px.his(xs)),
    Laws.spec.ga16(xs), L1.png_px_ga(Png.px.his(xs), plte, trns), ga16.same(xs))

def Laws.png_px_rgba16(xs, plte, trns):
  Equal.trans(Maybe<&2, List<&2, U32>>, Png.px.rgba(Png.px.his(xs), []), L1.spec.rgba(Png.px.his(xs)),
    Laws.spec.rgba16(xs), L1.png_px_rgba(Png.px.his(xs), plte, trns), rgba16.same(xs))

# indexed colour at a low depth or 8
def idx.deep(
  zl: Bool,
  +dd: U32,
  +xs: List<&2, U32>,
  +plte: List<&2, U32>,
  +trns: List<&2, U32>,
  el: {Laws.spec.low(dd) == zl : Bool},
  h_dd: {Bool.or(zl, U32.is_eq(dd, 8)) == True{} : Bool}
) -> {Png.px.deep(3, dd, xs, plte, trns) == L1.spec.idx(xs, L1.spec.pal(plte, L1.spec.alphas(plte, trns)))
  : Maybe<&2, List<&2, U32>>}:
  match zl:
    case True{}:
      Equal.trans(Maybe<&2, List<&2, U32>>, Png.px.deep(3, dd, xs, plte, trns), Png.px.low(3, dd, xs, plte, trns),
        L1.spec.idx(xs, L1.spec.pal(plte, L1.spec.alphas(plte, trns))), low.deep(3, dd, xs, plte, trns, el),
        L1.png_px_indexed(xs, plte, trns))
    case False{}:
      +e8 = {M1.ueq(dd, 8, h_dd) : {dd == 8 : U32}}
      Equal.trans(Maybe<&2, List<&2, U32>>, Png.px.deep(3, dd, xs, plte, trns), Png.px.deep(3, 8, xs, plte, trns),
        L1.spec.idx(xs, L1.spec.pal(plte, L1.spec.alphas(plte, trns))),
        Equal.cong(U32, Maybe<&2, List<&2, U32>>, uu => Png.px.deep(3, uu, xs, plte, trns), dd, 8, e8),
        L1.png_px_indexed(xs, plte, trns))

def Laws.png_px_indexed_deep(dd, xs, plte, trns, h_dd):
  idx.deep(Laws.spec.low(dd), dd, xs, plte, trns, {==}, h_dd)
