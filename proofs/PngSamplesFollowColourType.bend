# proofs of laws/PngSamplesFollowColourType.bend
import Base
import ../src/png.bend as Png
import ../laws/PngSamplesFollowColourType.bend as Laws
import ../laws/defs/PngSpecification.bend as D1
import ./lemmas/BasicFacts.bend as M1
import ./lemmas/PngImageWalk.bend as M2

# a word whose first bit is clear and that is not zero: the rest is not zero
law pdec.fin_ff:
  for cc: Cmp
  for h_nz: {Cmp.is_eq(Word.cmp.fin(False{}, False{}, cc)) == False{} : Bool}
  {Cmp.is_eq(cc) == False{} : Bool}

# the proof of pdec.fin_ff
def pdec.fin_ff(cc, h_nz):
  match cc:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({Cmp.is_eq(EQ{}) == False{} : Bool}, M1.pdec.true_false(h_nz))
    case GT{}:
      {==}

# subtracting zero with no carry in takes one: a - 0 - 1, one less than a
# when a is not zero
law pdec.adc_zero_borrow:
  for +pp: Nat
  for +aw: Word(pp)
  for h_nz: {Cmp.is_eq(Word.cmp(pp, aw, Word.zero(pp))) == False{} : Bool}
  {1n+Word.to_nat(pp, Word.adc(pp, aw, Word.zero(pp), True{}, False{})) == Word.to_nat(pp, aw) : Nat}

# the proof of pdec.adc_zero_borrow
def pdec.adc_zero_borrow(pp, aw, h_nz):
  match pp:
    case 0n:
      match aw:
        case WNil{}:
          Empty.absurd({1n == 0n : Nat}, M1.pdec.true_false(h_nz))
    case 1n+(+qq):
      match aw:
        case WCon{True{}, +at}:
          lc = Equal.sym(Word(qq), Word.adc(qq, at, Word.zero(qq), True{}, True{}), at, M1.adc_zero_carry(qq, at))
          %lc : {1n+Nat.double(Word.to_nat(qq, _)) == 1n+Nat.double(Word.to_nat(qq, at)) : Nat}
          {==}
        case WCon{False{}, +at}:
          ih = pdec.adc_zero_borrow(qq, at, pdec.fin_ff(Word.cmp(qq, at, Word.zero(qq)), h_nz))
          %ih : {2n+Nat.double(Word.to_nat(qq, Word.adc(qq, at, Word.zero(qq), True{}, False{})))
            == Nat.double(_) : Nat}
          {==}

# one less than a nonzero U32, as a Nat
law pdec.u32_dec:
  for +uu: U32
  for h_nz: {U32.is_zero(uu) == False{} : Bool}
  {U32.to_nat(uu) == 1n+U32.to_nat(U32.sub(uu, 1)) : Nat}

# the proof of pdec.u32_dec
def pdec.u32_dec(uu, h_nz):
  match uu:
    case U32{WCon{True{}, +at}}:
      lc = Equal.sym(Word(31n), Word.adc(31n, at, Word.zero(31n), True{}, True{}), at, M1.adc_zero_carry(31n, at))
      %lc : {1n+Nat.double(Word.to_nat(31n, at)) == 1n+Nat.double(Word.to_nat(31n, _)) : Nat}
      {==}
    case U32{WCon{False{}, +at}}:
      ih = pdec.adc_zero_borrow(31n, at, pdec.fin_ff(Word.cmp(31n, at, Word.zero(31n)), h_nz))
      %ih : {Nat.double(_)
        == 2n+Nat.double(Word.to_nat(31n, Word.adc(31n, at, Word.zero(31n), True{}, False{}))) : Nat}
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
) -> {Png.px.ga(xs, acc) == M1.onto(acc, Laws.spec.ga(xs)) : Maybe<&2, List<&2, U32>>}:
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
            M1.onto(Png.px.pack(aa, gg, gg, gg) <> acc, Laws.spec.ga(tl)),
            M1.onto(acc, Laws.spec.cons(Png.px.pack(aa, gg, gg, gg), Laws.spec.ga(tl))),
            ga.acc(tl, Png.px.pack(aa, gg, gg, gg) <> acc),
            M2.onto.cons(Png.px.pack(aa, gg, gg, gg), acc, Laws.spec.ga(tl)))

def Laws.png_px_ga(xs):
  Equal.trans(Maybe<&2, List<&2, U32>>, Png.px.ga(xs, []), M1.onto([], Laws.spec.ga(xs)), Laws.spec.ga(xs),
    ga.acc(xs, []), M2.onto.nil(Laws.spec.ga(xs)))

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
) -> {Png.px.rgb(xs, Png.KRgb{kr, kg, kb}, acc) == M1.onto(acc, Laws.spec.rgb.key(xs, kr, kg, kb))
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
                M1.onto(Png.px.pack(Png.px.rgb.hit(rr, gg, bb, kr, kg, kb), rr, gg, bb) <> acc,
                  Laws.spec.rgb.key(tl, kr, kg, kb)),
                M1.onto(acc, Laws.spec.cons(Laws.spec.argb(Laws.spec.key.alpha(rgb.hit(rr, gg, bb, kr, kg, kb)), rr, gg,
                  bb), Laws.spec.rgb.key(tl, kr, kg, kb))),
                rgb.key.acc(tl, kr, kg, kb, Png.px.pack(Png.px.rgb.hit(rr, gg, bb, kr, kg, kb), rr, gg, bb) <> acc),
                Equal.trans(Maybe<&2, List<&2, U32>>,
                  M1.onto(Png.px.pack(Png.px.rgb.hit(rr, gg, bb, kr, kg, kb), rr, gg, bb) <> acc,
                    Laws.spec.rgb.key(tl, kr, kg, kb)),
                  M1.onto(Laws.spec.argb(Laws.spec.key.alpha(rgb.hit(rr, gg, bb, kr, kg, kb)), rr, gg, bb) <> acc,
                    Laws.spec.rgb.key(tl, kr, kg, kb)),
                  M1.onto(acc, Laws.spec.cons(Laws.spec.argb(Laws.spec.key.alpha(rgb.hit(rr, gg, bb, kr, kg, kb)), rr,
                    gg, bb), Laws.spec.rgb.key(tl, kr, kg, kb))),
                  Equal.cong(U32, Maybe<&2, List<&2, U32>>,
                    aa => M1.onto(Laws.spec.argb(aa, rr, gg, bb) <> acc, Laws.spec.rgb.key(tl, kr, kg, kb)),
                    Png.px.hit.at(rgb.hit(rr, gg, bb, kr, kg, kb)),
                    Laws.spec.key.alpha(rgb.hit(rr, gg, bb, kr, kg, kb)),
                    hit.alpha(rgb.hit(rr, gg, bb, kr, kg, kb))),
                  M2.onto.cons(Laws.spec.argb(Laws.spec.key.alpha(rgb.hit(rr, gg, bb, kr, kg, kb)), rr, gg, bb), acc,
                    Laws.spec.rgb.key(tl, kr, kg, kb))))

def Laws.png_px_rgb_key(xs, _plte, kr, kg, kb):
  Equal.trans(Maybe<&2, List<&2, U32>>, Png.px.rgb(xs, Png.KRgb{kr, kg, kb}, []),
    M1.onto([], Laws.spec.rgb.key(xs, kr, kg, kb)), Laws.spec.rgb.key(xs, kr, kg, kb), rgb.key.acc(xs, kr, kg, kb, []),
    M2.onto.nil(Laws.spec.rgb.key(xs, kr, kg, kb)))

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
      e0 = Equal.sym(U32, ix, 0, M1.ueq(ix, 0, ez))
      %e0 : {Some{hd} == List.get(&2, U32, hd <> tl, U32.to_nat(_)) : Maybe<&2, U32>}
      {==}
    case False{}:
      en = Equal.sym(Nat, U32.to_nat(ix), 1n+U32.to_nat(U32.sub(ix, 1)), pdec.u32_dec(ix, ez))
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
  {Png.px.idx(tl, pal, cc <> acc) == M1.onto(cc <> acc, Laws.spec.idx(tl, pal)) : Maybe<&2, List<&2, U32>>}

# one index of px.idx, once its entry is known
def idx.step(
  mm: Maybe<&2, U32>,
  +tl: List<&2, U32>,
  +pal: List<&2, U32>,
  +acc: List<&2, U32>,
  ih: @cc: U32 -> idx.ih(tl, pal, acc, cc)
) -> {Png.px.use(mm, cc => Png.px.idx(tl, pal, {cc <> acc : List<&2, U32>})) ==
  M1.onto(acc, Laws.spec.idx.at(mm, Laws.spec.idx(tl, pal))) : Maybe<&2, List<&2, U32>>}:
  match mm:
    case None{}:
      {==}
    case Some{+cc}:
      Equal.trans(Maybe<&2, List<&2, U32>>, Png.px.idx(tl, pal, cc <> acc), M1.onto(cc <> acc, Laws.spec.idx(tl, pal)),
        M1.onto(acc, Laws.spec.cons(cc, Laws.spec.idx(tl, pal))), ih(cc), M2.onto.cons(cc, acc, Laws.spec.idx(tl, pal)))

# px.idx looks each index up as spec.idx does
def idx.acc(
  xs: List<&2, U32>,
  +pal: List<&2, U32>,
  +acc: List<&2, U32>
) -> {Png.px.idx(xs, pal, acc) == M1.onto(acc, Laws.spec.idx(xs, pal)) : Maybe<&2, List<&2, U32>>}:
  match xs:
    case Nil{}:
      {==}
    case +ix <> +tl:
      Equal.trans(Maybe<&2, List<&2, U32>>,
        Png.px.use(Png.px.at(pal, U32.is_zero(ix), ix), cc => Png.px.idx(tl, pal, {cc <> acc : List<&2, U32>})),
        Png.px.use(List.get(&2, U32, pal, U32.to_nat(ix)), cc => Png.px.idx(tl, pal, {cc <> acc : List<&2, U32>})),
        M1.onto(acc, Laws.spec.idx.at(List.get(&2, U32, pal, U32.to_nat(ix)), Laws.spec.idx(tl, pal))),
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
      Empty.absurd({None{} == Laws.spec.idx(xs, pal) : Maybe<&2, List<&2, U32>>}, M1.false_true(h_some))
    case True{}:
      Equal.trans(Maybe<&2, List<&2, U32>>, Png.px.idx(xs, pal, []), M1.onto([], Laws.spec.idx(xs, pal)),
        Laws.spec.idx(xs, pal), idx.acc(xs, pal, []), M2.onto.nil(Laws.spec.idx(xs, pal)))

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
      Empty.absurd({None{} == Laws.spec.idx(xs, pal) : Maybe<&2, List<&2, U32>>}, M1.false_true(h_some))
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
) -> {Png.png.pack(mm, ww, hh, colour, plte, trns) == Laws.spec.pic(D1.spec.px.then(mm, colour, plte, trns), ww, hh)
  : Maybe<&2, Png.Pic>}:
  match mm:
    case None{}:
      {==}
    case Some{raw}:
      pic.frame(Png.px.of(colour, raw, plte, trns), ww, hh)

def Laws.png_samples_frame(raw, ww, hh, colour, plte, trns):
  pack.frame(Png.unfilter(raw, ww, hh, Png.png.bpp(colour)), ww, hh, colour, plte, trns)
