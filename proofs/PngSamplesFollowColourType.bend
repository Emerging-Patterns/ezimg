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

def Laws.png_px_ga(xs, _plte, _trns):
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

# pal.make builds spec.pal's entries, onto acc
def pal.acc(
  xs: List<&2, U32>,
  +als: List<&2, U32>,
  +acc: List<&2, U32>
) -> {Png.pal.make(xs, als, acc) == List.reverse.go(&2, U32, acc, Laws.spec.pal(xs, als)) : List<&2, U32>}:
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

# the code's choice of tRNS alphas is the specification's
def alphas.same(
  fits: Bool,
  +als: List<&2, U32>
) -> {Png.pal.alphas(fits, als) == Laws.spec.alphas.keep(fits, als) : List<&2, U32>}:
  match fits:
    case True{}:
      {==}
    case False{}:
      {==}

# ---- the palette's lookup tree is the list's index ----

# an index from its low bit and the rest: twice the rest, plus one when the
# index is odd (even says it is not)
def bit.nat(even: Bool, +nn: Nat) -> Nat:
  match even:
    case True{}:
      Nat.double(nn)
    case False{}:
      1n+Nat.double(nn)

# a word masked with zero is zero
def and.zero(nn: Nat, ww: Word(nn)) -> {Word.and(nn, Word.zero(nn), ww) == Word.zero(nn) : Word(nn)}:
  match nn:
    case 0n:
      match ww:
        case WNil{}:
          {==}
    case 1n+pp:
      match ww:
        case WCon{_bb, tt}:
          Equal.cong(Word(pp), Word.Con<pp>, vv => WCon{False{}, vv}, Word.and(pp, Word.zero(pp), tt), Word.zero(pp),
            and.zero(pp, tt))

# a word shifted down a place, a clear bit put on top, is the same number
def pad.nat(nn: Nat, ww: Word(nn)) -> {Word.to_nat(1n+nn, Word.shr.pad(nn, ww)) == Word.to_nat(nn, ww) : Nat}:
  match nn:
    case 0n:
      match ww:
        case WNil{}:
          {==}
    case 1n+pp:
      match ww:
        case WCon{True{}, tt}:
          Equal.cong(Nat, Nat, kk => 1n+Nat.double(kk), Word.to_nat(1n+pp, Word.shr.pad(pp, tt)), Word.to_nat(pp, tt),
            pad.nat(pp, tt))
        case WCon{False{}, tt}:
          Equal.cong(Nat, Nat, kk => Nat.double(kk), Word.to_nat(1n+pp, Word.shr.pad(pp, tt)), Word.to_nat(pp, tt),
            pad.nat(pp, tt))

# an index is its low bit and the rest shifted down
def bit.split(ix: U32) -> {U32.to_nat(ix) == bit.nat(Png.pt.even(ix), U32.to_nat(U32.shr(ix))) : Nat}:
  match ix:
    case U32{WCon{True{}, +rr}}:
      %Equal.sym(Word(31n), Word.and(31n, Word.zero(31n), rr), Word.zero(31n), and.zero(31n, rr)) : {U32.to_nat(U32{
        WCon{True{}, rr}}) == bit.nat(Cmp.is_eq(Word.cmp.fin(True{}, False{}, Word.cmp(31n, _, Word.zero(31n)))),
        U32.to_nat(U32.shr(U32{WCon{True{}, rr}}))) : Nat}
      Equal.sym(Nat, 1n+Nat.double(Word.to_nat(32n, Word.shr.pad(31n, rr))), 1n+Nat.double(Word.to_nat(31n, rr)),
        Equal.cong(Nat, Nat, kk => 1n+Nat.double(kk), Word.to_nat(32n, Word.shr.pad(31n, rr)), Word.to_nat(31n, rr),
          pad.nat(31n, rr)))
    case U32{WCon{False{}, +rr}}:
      %Equal.sym(Word(31n), Word.and(31n, Word.zero(31n), rr), Word.zero(31n), and.zero(31n, rr)) : {U32.to_nat(U32{
        WCon{False{}, rr}}) == bit.nat(Cmp.is_eq(Word.cmp.fin(False{}, False{}, Word.cmp(31n, _, Word.zero(31n)))),
        U32.to_nat(U32.shr(U32{WCon{False{}, rr}}))) : Nat}
      Equal.sym(Nat, Nat.double(Word.to_nat(32n, Word.shr.pad(31n, rr))), Nat.double(Word.to_nat(31n, rr)),
        Equal.cong(Nat, Nat, kk => Nat.double(kk), Word.to_nat(32n, Word.shr.pad(31n, rr)), Word.to_nat(31n, rr),
          pad.nat(31n, rr)))

# an index is its low bit, once named, and the rest shifted down
def bit.of(
  +ix: U32,
  ev: Bool,
  ee: {Png.pt.even(ix) == ev : Bool}
) -> {U32.to_nat(ix) == bit.nat(ev, U32.to_nat(U32.shr(ix))) : Nat}:
  Equal.trans(Nat, U32.to_nat(ix), bit.nat(Png.pt.even(ix), U32.to_nat(U32.shr(ix))), bit.nat(ev,
    U32.to_nat(U32.shr(ix))), bit.split(ix), Equal.cong(Bool, Nat, bb => bit.nat(bb, U32.to_nat(U32.shr(ix))),
    Png.pt.even(ix), ev, ee))

# every other entry from the first is the entry at twice the place, and
# from the second at twice the place plus one
def alt.get(
  xs: List<&2, U32>,
  keep: Bool,
  +nn: Nat
) -> {List.get(&2, U32, Png.pt.alt(xs, keep), nn) == List.get(&2, U32, xs, bit.nat(keep, nn)) : Maybe<&2, U32>}:
  match xs keep:
    case Nil{} True{}:
      {==}
    case Nil{} False{}:
      {==}
    case +hd <> tl True{}:
      match nn:
        case 0n:
          {==}
        case 1n+mm:
          alt.get(tl, False{}, mm)
    case _hd <> tl False{}:
      alt.get(tl, True{}, nn)

# one entry: the entry at index 0, none past it
def one.get(
  +vv: U32,
  +ix: U32,
  zz: Bool,
  ez: {U32.is_zero(ix) == zz : Bool}
) -> {Png.pt.hit(zz, vv) == List.get(&2, U32, [vv], U32.to_nat(ix)) : Maybe<&2, U32>}:
  match zz:
    case True{}:
      e0 = Equal.sym(U32, ix, 0, M1.ueq(ix, 0, ez))
      %e0 : {Some{vv} == List.get(&2, U32, [vv], U32.to_nat(_)) : Maybe<&2, U32>}
      {==}
    case False{}:
      en = Equal.sym(Nat, U32.to_nat(ix), 1n+U32.to_nat(U32.sub(ix, 1)), pdec.u32_dec(ix, ez))
      %en : {None{} == List.get(&2, U32, [vv], _) : Maybe<&2, U32>}
      {==}

# the tree once the fuel is spent looks each index up as the list does
def leaf.get(
  xs: List<&2, U32>,
  ev: Bool,
  +ix: U32
) -> {Png.pt.at(Png.pt.leaf(xs), ev, ix) == List.get(&2, U32, xs, U32.to_nat(ix)) : Maybe<&2, U32>}:
  match xs:
    case Nil{}:
      match ev:
        case True{}:
          {==}
        case False{}:
          {==}
    case +hd <> tl:
      match tl:
        case Nil{}:
          match ev:
            case True{}:
              one.get(hd, ix, U32.is_zero(ix), {==})
            case False{}:
              one.get(hd, ix, U32.is_zero(ix), {==})
        case +_yy <> _rr:
          match ev:
            case True{}:
              {==}
            case False{}:
              {==}

# what tree.get proves of a tree and a list
def tree.ty(tr: Png.Pt, xs: List<&2, U32>) -> Type:
  @ix: U32 -> {Png.pt.at(tr, Png.pt.even(ix), ix) == List.get(&2, U32, xs, U32.to_nat(ix)) : Maybe<&2, U32>}

# a split: the low bit picks the half, and the half's entry at the rest is
# the list's at the index
def two.get(
  +ix: U32,
  ev: Bool,
  ee: {Png.pt.even(ix) == ev : Bool},
  +bt: Png.Pt,
  +bf: Png.Pt,
  +xs: List<&2, U32>,
  ht: tree.ty(bt, Png.pt.alt(xs, True{})),
  hf: tree.ty(bf, Png.pt.alt(xs, False{}))
) -> {Png.pt.at(Png.PTwo{bt, bf}, ev, ix) == List.get(&2, U32, xs, U32.to_nat(ix)) : Maybe<&2, U32>}:
  match ev:
    case True{}:
      +sh = U32.shr(ix)
      +es = {bit.of(ix, True{}, ee) : {U32.to_nat(ix) == bit.nat(True{}, U32.to_nat(sh)) : Nat}}
      Equal.trans(Maybe<&2, U32>, Png.pt.at(bt, Png.pt.even(sh), sh),
        List.get(&2, U32, Png.pt.alt(xs, True{}), U32.to_nat(sh)), List.get(&2, U32, xs, U32.to_nat(ix)), ht(sh),
        Equal.trans(Maybe<&2, U32>, List.get(&2, U32, Png.pt.alt(xs, True{}), U32.to_nat(sh)),
          List.get(&2, U32, xs, bit.nat(True{}, U32.to_nat(sh))), List.get(&2, U32, xs, U32.to_nat(ix)),
          alt.get(xs, True{}, U32.to_nat(sh)),
          Equal.cong(Nat, Maybe<&2, U32>, kk => List.get(&2, U32, xs, kk), bit.nat(True{}, U32.to_nat(sh)),
            U32.to_nat(ix), Equal.sym(Nat, U32.to_nat(ix), bit.nat(True{}, U32.to_nat(sh)), es))))
    case False{}:
      +sh = U32.shr(ix)
      +es = {bit.of(ix, False{}, ee) : {U32.to_nat(ix) == bit.nat(False{}, U32.to_nat(sh)) : Nat}}
      Equal.trans(Maybe<&2, U32>, Png.pt.at(bf, Png.pt.even(sh), sh),
        List.get(&2, U32, Png.pt.alt(xs, False{}), U32.to_nat(sh)), List.get(&2, U32, xs, U32.to_nat(ix)), hf(sh),
        Equal.trans(Maybe<&2, U32>, List.get(&2, U32, Png.pt.alt(xs, False{}), U32.to_nat(sh)),
          List.get(&2, U32, xs, bit.nat(False{}, U32.to_nat(sh))), List.get(&2, U32, xs, U32.to_nat(ix)),
          alt.get(xs, False{}, U32.to_nat(sh)),
          Equal.cong(Nat, Maybe<&2, U32>, kk => List.get(&2, U32, xs, kk), bit.nat(False{}, U32.to_nat(sh)),
            U32.to_nat(ix), Equal.sym(Nat, U32.to_nat(ix), bit.nat(False{}, U32.to_nat(sh)), es))))

# the lookup tree, whatever the fuel, looks each index up as the list does
def tree.get(fuel: Nat, xs: List<&2, U32>) -> tree.ty(Png.pt.build(fuel, xs), xs):
  match fuel:
    case 0n:
      +ix => leaf.get(xs, Png.pt.even(ix), ix)
    case 1n+(+ff):
      match xs:
        case Nil{}:
          +ix => leaf.get([], Png.pt.even(ix), ix)
        case +hd <> tl:
          match tl:
            case Nil{}:
              +ix => leaf.get([hd], Png.pt.even(ix), ix)
            case +yy <> +rr:
              +all = {hd <> {yy <> rr : List<&2, U32>} : List<&2, U32>}
              +ix => two.get(ix, Png.pt.even(ix), {==}, Png.pt.build(ff, Png.pt.alt(all, True{})),
                Png.pt.build(ff, Png.pt.alt(all, False{})), all, tree.get(ff, Png.pt.alt(all, True{})),
                tree.get(ff, Png.pt.alt(all, False{})))

# what idx.acc says of the rest, with one entry more on the accumulator
def idx.ih(+tl: List<&2, U32>, +tr: Png.Pt, +pal: List<&2, U32>, +acc: List<&2, U32>, +cc: U32) -> Type:
  {Png.px.idx(tl, tr, cc <> acc) == M1.onto(cc <> acc, Laws.spec.idx(tl, pal)) : Maybe<&2, List<&2, U32>>}

# one index of px.idx, once its entry is known
def idx.step(
  mm: Maybe<&2, U32>,
  +tl: List<&2, U32>,
  +tr: Png.Pt,
  +pal: List<&2, U32>,
  +acc: List<&2, U32>,
  ih: @cc: U32 -> idx.ih(tl, tr, pal, acc, cc)
) -> {Png.px.use(mm, cc => Png.px.idx(tl, tr, {cc <> acc : List<&2, U32>})) ==
  M1.onto(acc, Laws.spec.idx.at(mm, Laws.spec.idx(tl, pal))) : Maybe<&2, List<&2, U32>>}:
  match mm:
    case None{}:
      {==}
    case Some{+cc}:
      Equal.trans(Maybe<&2, List<&2, U32>>, Png.px.idx(tl, tr, cc <> acc), M1.onto(cc <> acc, Laws.spec.idx(tl, pal)),
        M1.onto(acc, Laws.spec.cons(cc, Laws.spec.idx(tl, pal))), ih(cc), M2.onto.cons(cc, acc, Laws.spec.idx(tl, pal)))

# px.idx looks each index up as spec.idx does, with the palette's lookup tree
def idx.acc(
  xs: List<&2, U32>,
  +fuel: Nat,
  +pal: List<&2, U32>,
  +acc: List<&2, U32>
) -> {Png.px.idx(xs, Png.pt.build(fuel, pal), acc) == M1.onto(acc, Laws.spec.idx(xs, pal)) : Maybe<&2, List<&2, U32>>}:
  match xs:
    case Nil{}:
      {==}
    case +ix <> +tl:
      +tr = Png.pt.build(fuel, pal)
      Equal.trans(Maybe<&2, List<&2, U32>>,
        Png.px.use(Png.pt.at(tr, Png.pt.even(ix), ix), cc => Png.px.idx(tl, tr, {cc <> acc : List<&2, U32>})),
        Png.px.use(List.get(&2, U32, pal, U32.to_nat(ix)), cc => Png.px.idx(tl, tr, {cc <> acc : List<&2, U32>})),
        M1.onto(acc, Laws.spec.idx.at(List.get(&2, U32, pal, U32.to_nat(ix)), Laws.spec.idx(tl, pal))),
        Equal.cong(Maybe<&2, U32>, Maybe<&2, List<&2, U32>>,
          mm => Png.px.use(mm, cc => Png.px.idx(tl, tr, {cc <> acc : List<&2, U32>})),
          Png.pt.at(tr, Png.pt.even(ix), ix), List.get(&2, U32, pal, U32.to_nat(ix)), tree.get(fuel, pal)(ix)),
        idx.step(List.get(&2, U32, pal, U32.to_nat(ix)), tl, tr, pal, acc, cc => idx.acc(tl, fuel, pal, cc <> acc)))

def Laws.png_px_indexed(xs, plte, trns):
  +fits = Nat.is_le(List.length(&2, U32, trns), Nat.div(List.length(&2, U32, plte), 3n))
  +als = Laws.spec.alphas.keep(fits, trns)
  +pal = Laws.spec.pal(plte, als)
  +ea = {alphas.same(fits, trns) : {Png.pal.alphas(fits, trns) == als : List<&2, U32>}}
  +ep = {Equal.trans(List<&2, U32>, Png.pal.make(plte, Png.pal.alphas(fits, trns), []), Png.pal.make(plte, als, []),
    pal,
    Equal.cong(List<&2, U32>, List<&2, U32>, aa => Png.pal.make(plte, aa, []), Png.pal.alphas(fits, trns), als, ea),
    pal.acc(plte, als, [])) : {Png.pal.make(plte, Png.pal.alphas(fits, trns), []) == pal : List<&2, U32>}}
  Equal.trans(Maybe<&2, List<&2, U32>>,
    Png.px.idx(xs, Png.pt.tree(Png.pal.make(plte, Png.pal.alphas(fits, trns), [])), []),
    Png.px.idx(xs, Png.pt.tree(pal), []), Laws.spec.idx(xs, pal),
    Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, ll => Png.px.idx(xs, Png.pt.tree(ll), []),
      Png.pal.make(plte, Png.pal.alphas(fits, trns), []), pal, ep),
    Equal.trans(Maybe<&2, List<&2, U32>>, Png.px.idx(xs, Png.pt.tree(pal), []), M1.onto([], Laws.spec.idx(xs,
      pal)), Laws.spec.idx(xs, pal), idx.acc(xs, List.length(&2, U32, pal), pal, []),
      M2.onto.nil(Laws.spec.idx(xs, pal))))

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
