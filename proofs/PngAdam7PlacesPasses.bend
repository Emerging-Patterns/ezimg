# proofs of laws/PngAdam7PlacesPasses.bend: each step of a7.merge places
# the halves it interleaves, when their sizes are the halves of the step's
import Base
import ../src/png.bend as Png
import ../laws/PngAdam7PlacesPasses.bend as A
import ../laws/defs/SizeBounds.bend as D2
import ./lemmas/BasicFacts.bend as M1

# ---- what the interleaves need ----

# a has as many samples as b, or one more
def hv.px(aa: List<&2, U32>, bb: List<&2, U32>) -> Bool:
  match aa bb:
    case Nil{} Nil{}:
      True{}
    case Nil{} _h <> _t:
      False{}
    case _h <> ta Nil{}:
      List.is_empty(&2, U32, ta)
    case _ha <> ta _hb <> tb:
      hv.px(ta, tb)

# a has as many rows as b, or one more
def hv.rows(aa: List<&2, List<&2, U32>>, bb: List<&2, List<&2, U32>>) -> Bool:
  match aa bb:
    case Nil{} Nil{}:
      True{}
    case Nil{} _h <> _t:
      False{}
    case _h <> ta Nil{}:
      List.is_empty(&2, List<&2, U32>, ta)
    case _ha <> ta _hb <> tb:
      hv.rows(ta, tb)

# every row is empty
def rows.none(bb: List<&2, List<&2, U32>>) -> Bool:
  match bb:
    case Nil{}:
      True{}
    case rb <> tb:
      Bool.and(List.is_empty(&2, U32, rb), rows.none(tb))

# each row of a has as many samples as b's row of the same place, or one
# more, and the rows b has past a's are empty
def cols.ok(aa: List<&2, List<&2, U32>>, +bb: List<&2, List<&2, U32>>) -> Bool:
  match aa:
    case Nil{}:
      rows.none(bb)
    case ra <> ta:
      Bool.and(hv.px(ra, Png.rows.head(bb)), cols.ok(ta, Png.rows.tail(bb)))

# both true
def and.tt(xx: Bool, +yy: Bool, hx: {xx == True{} : Bool}, hy: {yy == True{} : Bool}) -> {Bool.and(xx, yy) == True{} :
  Bool}:
  match xx:
    case True{}:
      hy
    case False{}:
      Empty.absurd({Bool.and(False{}, yy) == True{} : Bool}, M1.false_true(hx))

# ---- placement: samples ----

# a list of one sample whose rest is empty
def px.even.one(
  ta: List<&2, U32>,
  +ha: U32,
  kk: Nat,
  hh: {List.is_empty(&2, U32, ta) == True{} : Bool}
) -> {A.spec.nth([ha], Nat.double(kk)) == A.spec.nth(ha <> ta, kk) : Maybe<&2, U32>}:
  match ta:
    case Nil{}:
      match kk:
        case 0n:
          {==}
        case 1n+_p:
          {==}
    case th <> tt:
      Empty.absurd({A.spec.nth([ha], Nat.double(kk)) == A.spec.nth(ha <> th <> tt, kk) : Maybe<&2, U32>},
        M1.false_true(hh))

# LAW: sample 2k of a's and b's samples interleaved is a's sample k
law px.even:
  for +aa: List<&2, U32>
  for +bb: List<&2, U32>
  for +kk: Nat
  for hh: {hv.px(aa, bb) == True{} : Bool}
  {A.spec.nth(Png.ilv.px(aa, bb), Nat.double(kk)) == A.spec.nth(aa, kk) : Maybe<&2, U32>}

# the proof of px.even
def px.even(aa, bb, kk, hh):
  match aa:
    case Nil{}:
      {==}
    case +ha <> ta:
      match bb:
        case Nil{}:
          px.even.one(ta, ha, kk, hh)
        case _hb <> tb:
          match kk:
            case 0n:
              {==}
            case 1n+(+pp):
              px.even(ta, tb, pp, hh)

# LAW: sample 2k + 1 of a's and b's samples interleaved is b's sample k
law px.odd:
  for +aa: List<&2, U32>
  for +bb: List<&2, U32>
  for +kk: Nat
  for hh: {hv.px(aa, bb) == True{} : Bool}
  {A.spec.nth(Png.ilv.px(aa, bb), 1n+Nat.double(kk)) == A.spec.nth(bb, kk) : Maybe<&2, U32>}

# the proof of px.odd
def px.odd(aa, bb, kk, hh):
  match aa:
    case Nil{}:
      match bb:
        case Nil{}:
          {==}
        case hb <> tb:
          Empty.absurd({A.spec.nth(Png.ilv.px([], hb <> tb), 1n+Nat.double(kk)) == A.spec.nth(hb <> tb, kk) :
            Maybe<&2, U32>}, M1.false_true(hh))
    case _ha <> ta:
      match bb:
        case Nil{}:
          {==}
        case _hb <> tb:
          match kk:
            case 0n:
              {==}
            case 1n+(+pp):
              px.odd(ta, tb, pp, hh)

# ---- placement: rows ----

# a list of one row whose rest is empty
def rw.even.one(
  ta: List<&2, List<&2, U32>>,
  ha: List<&2, U32>,
  kk: Nat,
  hh: {List.is_empty(&2, List<&2, U32>, ta) == True{} : Bool}
) -> {A.spec.row([ha], Nat.double(kk)) == A.spec.row(ha <> ta, kk) : List<&2, U32>}:
  match ta:
    case Nil{}:
      match kk:
        case 0n:
          {==}
        case 1n+_p:
          {==}
    case th <> tt:
      Empty.absurd({A.spec.row([ha], Nat.double(kk)) == A.spec.row(ha <> th <> tt, kk) : List<&2, U32>},
        M1.false_true(hh))

# LAW: row 2k of a's and b's rows interleaved is a's row k
law rw.even:
  for +aa: List<&2, List<&2, U32>>
  for +bb: List<&2, List<&2, U32>>
  for +kk: Nat
  for hh: {hv.rows(aa, bb) == True{} : Bool}
  {A.spec.row(Png.ilv.rows(aa, bb), Nat.double(kk)) == A.spec.row(aa, kk) : List<&2, U32>}

# the proof of rw.even
def rw.even(aa, bb, kk, hh):
  match aa:
    case Nil{}:
      {==}
    case ha <> ta:
      match bb:
        case Nil{}:
          rw.even.one(ta, ha, kk, hh)
        case _hb <> tb:
          match kk:
            case 0n:
              {==}
            case 1n+(+pp):
              rw.even(ta, tb, pp, hh)

# LAW: row 2k + 1 of a's and b's rows interleaved is b's row k
law rw.odd:
  for +aa: List<&2, List<&2, U32>>
  for +bb: List<&2, List<&2, U32>>
  for +kk: Nat
  for hh: {hv.rows(aa, bb) == True{} : Bool}
  {A.spec.row(Png.ilv.rows(aa, bb), 1n+Nat.double(kk)) == A.spec.row(bb, kk) : List<&2, U32>}

# the proof of rw.odd
def rw.odd(aa, bb, kk, hh):
  match aa:
    case Nil{}:
      match bb:
        case Nil{}:
          {==}
        case hb <> tb:
          Empty.absurd({A.spec.row(Png.ilv.rows([], hb <> tb), 1n+Nat.double(kk)) == A.spec.row(hb <> tb, kk) :
            List<&2, U32>}, M1.false_true(hh))
    case _ha <> ta:
      match bb:
        case Nil{}:
          {==}
        case _hb <> tb:
          match kk:
            case 0n:
              {==}
            case 1n+(+pp):
              rw.odd(ta, tb, pp, hh)

# the sample at (x, 2k) of interleaved rows is a's at (x, k)
def rw.even.at(
  +aa: List<&2, List<&2, U32>>,
  +bb: List<&2, List<&2, U32>>,
  +xx: Nat,
  +kk: Nat,
  hh: {hv.rows(aa, bb) == True{} : Bool}
) -> {A.spec.at(Png.ilv.rows(aa, bb), xx, Nat.double(kk)) == A.spec.at(aa, xx, kk) : Maybe<&2, U32>}:
  Equal.cong(List<&2, U32>, Maybe<&2, U32>, rr => A.spec.nth(rr, xx), A.spec.row(Png.ilv.rows(aa, bb), Nat.double(kk)),
    A.spec.row(aa, kk), rw.even(aa, bb, kk, hh))

# the sample at (x, 2k + 1) of interleaved rows is b's at (x, k)
def rw.odd.at(
  +aa: List<&2, List<&2, U32>>,
  +bb: List<&2, List<&2, U32>>,
  +xx: Nat,
  +kk: Nat,
  hh: {hv.rows(aa, bb) == True{} : Bool}
) -> {A.spec.at(Png.ilv.rows(aa, bb), xx, 1n+Nat.double(kk)) == A.spec.at(bb, xx, kk) : Maybe<&2, U32>}:
  Equal.cong(List<&2, U32>, Maybe<&2, U32>, rr => A.spec.nth(rr, xx), A.spec.row(Png.ilv.rows(aa, bb),
    1n+Nat.double(kk)),
    A.spec.row(bb, kk), rw.odd(aa, bb, kk, hh))

# ---- placement: columns ----

# row y of interleaved columns interleaves a's and b's rows y
def cl.row(
  aa: List<&2, List<&2, U32>>,
  yy: Nat,
  bb: List<&2, List<&2, U32>>
) -> {A.spec.row(Png.ilv.cols(aa, bb), yy) == Png.ilv.px(A.spec.row(aa, yy), A.spec.row(bb, yy)) : List<&2, U32>}:
  match aa:
    case Nil{}:
      {==}
    case _ra <> ta:
      match yy:
        case 0n:
          match bb:
            case Nil{}:
              {==}
            case _rb <> _tb:
              {==}
        case 1n+(+pp):
          match bb:
            case Nil{}:
              cl.row(ta, pp, [])
            case _rb <> tb:
              cl.row(ta, pp, tb)

# a row that is empty is a's empty half
def empty.hv(rb: List<&2, U32>, hh: {List.is_empty(&2, U32, rb) == True{} : Bool}) -> {hv.px([], rb) == True{} : Bool}:
  match rb:
    case Nil{}:
      {==}
    case xx <> tt:
      Empty.absurd({hv.px([], xx <> tt) == True{} : Bool}, M1.false_true(hh))

# rows all empty: each is the empty row's half
def none.row(
  bb: List<&2, List<&2, U32>>,
  yy: Nat,
  hh: {rows.none(bb) == True{} : Bool}
) -> {hv.px([], A.spec.row(bb, yy)) == True{} :
  Bool}:
  match bb:
    case Nil{}:
      {==}
    case +rb <> tb:
      match yy:
        case 0n:
          empty.hv(rb, M1.and_left(List.is_empty(&2, U32, rb), rows.none(tb), hh))
        case 1n+(+pp):
          none.row(tb, pp, M1.and_right(List.is_empty(&2, U32, rb), rows.none(tb), hh))

# cols.ok gives each row pair its halves
def ok.row(
  aa: List<&2, List<&2, U32>>,
  yy: Nat,
  bb: List<&2, List<&2, U32>>,
  hh: {cols.ok(aa, bb) == True{} : Bool}
) -> {hv.px(A.spec.row(aa, yy), A.spec.row(bb, yy)) == True{} : Bool}:
  match aa:
    case Nil{}:
      none.row(bb, yy, hh)
    case +ra <> ta:
      match yy:
        case 0n:
          match bb:
            case Nil{}:
              M1.and_left(hv.px(ra, []), cols.ok(ta, []), hh)
            case +rb <> tb:
              M1.and_left(hv.px(ra, rb), cols.ok(ta, tb), hh)
        case 1n+(+pp):
          match bb:
            case Nil{}:
              ok.row(ta, pp, [], M1.and_right(hv.px(ra, []), cols.ok(ta, []), hh))
            case +rb <> tb:
              ok.row(ta, pp, tb, M1.and_right(hv.px(ra, rb), cols.ok(ta, tb), hh))

# the sample at (2i, y) of interleaved columns is a's at (i, y)
def cl.even(
  +aa: List<&2, List<&2, U32>>,
  +bb: List<&2, List<&2, U32>>,
  +ii: Nat,
  +yy: Nat,
  hh: {cols.ok(aa, bb) == True{} : Bool}
) -> {A.spec.at(Png.ilv.cols(aa, bb), Nat.double(ii), yy) == A.spec.at(aa, ii, yy) : Maybe<&2, U32>}:
  +ra = A.spec.row(aa, yy)
  +rb = A.spec.row(bb, yy)
  Equal.trans(Maybe<&2, U32>, A.spec.nth(A.spec.row(Png.ilv.cols(aa, bb), yy), Nat.double(ii)),
    A.spec.nth(Png.ilv.px(ra, rb), Nat.double(ii)), A.spec.nth(ra, ii),
    Equal.cong(List<&2, U32>, Maybe<&2, U32>, xs => A.spec.nth(xs, Nat.double(ii)), A.spec.row(Png.ilv.cols(aa, bb),
      yy),
      Png.ilv.px(ra, rb), cl.row(aa, yy, bb)),
    px.even(ra, rb, ii, ok.row(aa, yy, bb, hh)))

# the sample at (2i + 1, y) of interleaved columns is b's at (i, y)
def cl.odd(
  +aa: List<&2, List<&2, U32>>,
  +bb: List<&2, List<&2, U32>>,
  +ii: Nat,
  +yy: Nat,
  hh: {cols.ok(aa, bb) == True{} : Bool}
) -> {A.spec.at(Png.ilv.cols(aa, bb), 1n+Nat.double(ii), yy) == A.spec.at(bb, ii, yy) : Maybe<&2, U32>}:
  +ra = A.spec.row(aa, yy)
  +rb = A.spec.row(bb, yy)
  Equal.trans(Maybe<&2, U32>, A.spec.nth(A.spec.row(Png.ilv.cols(aa, bb), yy), 1n+Nat.double(ii)),
    A.spec.nth(Png.ilv.px(ra, rb), 1n+Nat.double(ii)), A.spec.nth(rb, ii),
    Equal.cong(List<&2, U32>, Maybe<&2, U32>, xs => A.spec.nth(xs, 1n+Nat.double(ii)), A.spec.row(Png.ilv.cols(aa,
      bb), yy),
      Png.ilv.px(ra, rb), cl.row(aa, yy, bb)),
    px.odd(ra, rb, ii, ok.row(aa, yy, bb, hh)))

# ---- sizes ----

# rows of ceil(n / 2) and floor(n / 2) samples are halves
def len.hv(
  nn: Nat,
  ra: List<&2, U32>,
  rb: List<&2, U32>,
  ea: {Nat.is_eq(List.length(&2, U32, ra), A.spec.up(nn)) == True{} : Bool},
  eb: {Nat.is_eq(List.length(&2, U32, rb), D2.half(nn)) == True{} : Bool}
) -> {hv.px(ra, rb) == True{} : Bool}:
  match nn:
    case 0n:
      match ra:
        case Nil{}:
          match rb:
            case Nil{}:
              {==}
            case yy <> tb:
              Empty.absurd({hv.px([], yy <> tb) == True{} : Bool}, M1.false_true(eb))
        case xx <> ta:
          Empty.absurd({hv.px(xx <> ta, rb) == True{} : Bool}, M1.false_true(ea))
    case 1n+(+pp):
      match pp:
        case 0n:
          match ra:
            case Nil{}:
              Empty.absurd({hv.px([], rb) == True{} : Bool}, M1.false_true(ea))
            case xx <> ta:
              match ta:
                case Nil{}:
                  match rb:
                    case Nil{}:
                      {==}
                    case yy <> tb:
                      Empty.absurd({hv.px([xx], yy <> tb) == True{} : Bool}, M1.false_true(eb))
                case x2 <> t2:
                  Empty.absurd({hv.px(xx <> x2 <> t2, rb) == True{} : Bool}, M1.false_true(ea))
        case 1n+(+qq):
          match ra:
            case Nil{}:
              Empty.absurd({hv.px([], rb) == True{} : Bool}, M1.false_true(ea))
            case _xx <> ta:
              match rb:
                case Nil{}:
                  Empty.absurd({hv.px(_xx <> ta, []) == True{} : Bool}, M1.false_true(eb))
                case _yy <> tb:
                  len.hv(qq, ta, tb, ea, eb)

# rows of ceil(n / 2) and floor(n / 2) samples interleave to n samples
def len.ilv(
  nn: Nat,
  ra: List<&2, U32>,
  rb: List<&2, U32>,
  ea: {Nat.is_eq(List.length(&2, U32, ra), A.spec.up(nn)) == True{} : Bool},
  eb: {Nat.is_eq(List.length(&2, U32, rb), D2.half(nn)) == True{} : Bool}
) -> {Nat.is_eq(List.length(&2, U32, Png.ilv.px(ra, rb)), nn) == True{} : Bool}:
  match nn:
    case 0n:
      match ra:
        case Nil{}:
          {==}
        case xx <> ta:
          Empty.absurd({Nat.is_eq(List.length(&2, U32, Png.ilv.px(xx <> ta, rb)), 0n) == True{} : Bool},
            M1.false_true(ea))
    case 1n+(+pp):
      match pp:
        case 0n:
          match ra:
            case Nil{}:
              Empty.absurd({Nat.is_eq(List.length(&2, U32, Png.ilv.px([], rb)), 1n) == True{} : Bool},
                M1.false_true(ea))
            case xx <> ta:
              match ta:
                case Nil{}:
                  match rb:
                    case Nil{}:
                      {==}
                    case yy <> tb:
                      Empty.absurd({Nat.is_eq(List.length(&2, U32, Png.ilv.px([xx], yy <> tb)), 1n) == True{} : Bool},
                        M1.false_true(eb))
                case x2 <> t2:
                  Empty.absurd({Nat.is_eq(List.length(&2, U32, Png.ilv.px(xx <> x2 <> t2, rb)), 1n) == True{} :
                    Bool}, M1.false_true(ea))
        case 1n+(+qq):
          match ra:
            case Nil{}:
              Empty.absurd({Nat.is_eq(List.length(&2, U32, Png.ilv.px([], rb)), 2n+qq) == True{} : Bool},
                M1.false_true(ea))
            case xx <> ta:
              match rb:
                case Nil{}:
                  Empty.absurd({Nat.is_eq(List.length(&2, U32, Png.ilv.px(xx <> ta, [])), 2n+qq) == True{} : Bool},
                    M1.false_true(eb))
                case _yy <> tb:
                  len.ilv(qq, ta, tb, ea, eb)

# h rows and the h rows of ceil and floor halves are halves
def ro.hv(
  +ww: Nat,
  hh: Nat,
  aa: List<&2, List<&2, U32>>,
  bb: List<&2, List<&2, U32>>,
  +ga: {A.spec.rows.of(ww, A.spec.up(hh), aa) == True{} : Bool},
  +gb: {A.spec.rows.of(ww, D2.half(hh), bb) == True{} : Bool}
) -> {hv.rows(aa, bb) == True{} : Bool}:
  match hh:
    case 0n:
      match aa:
        case Nil{}:
          match bb:
            case Nil{}:
              {==}
            case yy <> tb:
              Empty.absurd({hv.rows([], yy <> tb) == True{} : Bool}, M1.false_true(gb))
        case xx <> ta:
          Empty.absurd({hv.rows(xx <> ta, bb) == True{} : Bool}, M1.false_true(ga))
    case 1n+(+pp):
      match pp:
        case 0n:
          match aa:
            case Nil{}:
              Empty.absurd({hv.rows([], bb) == True{} : Bool}, M1.false_true(ga))
            case xx <> ta:
              match ta:
                case Nil{}:
                  match bb:
                    case Nil{}:
                      {==}
                    case yy <> tb:
                      Empty.absurd({hv.rows([xx], yy <> tb) == True{} : Bool}, M1.false_true(gb))
                case x2 <> t2:
                  Empty.absurd({hv.rows(xx <> x2 <> t2, bb) == True{} : Bool}, M1.false_true(M1.and_right(
                    Nat.is_eq(List.length(&2, U32, xx), ww), False{}, ga)))
        case 1n+(+qq):
          match aa:
            case Nil{}:
              Empty.absurd({hv.rows([], bb) == True{} : Bool}, M1.false_true(ga))
            case +xx <> +ta:
              match bb:
                case Nil{}:
                  Empty.absurd({hv.rows(xx <> ta, []) == True{} : Bool}, M1.false_true(gb))
                case +yy <> +tb:
                  ro.hv(ww, qq, ta, tb, M1.and_right(Nat.is_eq(List.length(&2, U32, xx), ww),
                    A.spec.rows.of(ww, A.spec.up(qq), ta), ga), M1.and_right(Nat.is_eq(List.length(&2, U32,
                    yy), ww), A.spec.rows.of(ww, D2.half(qq), tb), gb))

# h rows from the h rows of ceil and floor halves
def ro.grid(
  +ww: Nat,
  hh: Nat,
  aa: List<&2, List<&2, U32>>,
  bb: List<&2, List<&2, U32>>,
  +ga: {A.spec.rows.of(ww, A.spec.up(hh), aa) == True{} : Bool},
  +gb: {A.spec.rows.of(ww, D2.half(hh), bb) == True{} : Bool}
) -> {A.spec.rows.of(ww, hh, Png.ilv.rows(aa, bb)) == True{} : Bool}:
  match hh:
    case 0n:
      match aa:
        case Nil{}:
          {==}
        case xx <> ta:
          Empty.absurd({A.spec.rows.of(ww, 0n, Png.ilv.rows(xx <> ta, bb)) == True{} : Bool}, M1.false_true(ga))
    case 1n+(+pp):
      match pp:
        case 0n:
          match aa:
            case Nil{}:
              Empty.absurd({A.spec.rows.of(ww, 1n, Png.ilv.rows([], bb)) == True{} : Bool}, M1.false_true(ga))
            case +xx <> +ta:
              match ta:
                case Nil{}:
                  match bb:
                    case Nil{}:
                      and.tt(Nat.is_eq(List.length(&2, U32, xx), ww), True{}, M1.and_left(Nat.is_eq(List.length(&2,
                        U32, xx), ww), True{}, ga), {==})
                    case yy <> tb:
                      Empty.absurd({A.spec.rows.of(ww, 1n, Png.ilv.rows([xx], yy <> tb)) == True{} : Bool},
                        M1.false_true(gb))
                case x2 <> t2:
                  Empty.absurd({A.spec.rows.of(ww, 1n, Png.ilv.rows(xx <> x2 <> t2, bb)) == True{} : Bool},
                    M1.false_true(M1.and_right(Nat.is_eq(List.length(&2, U32, xx), ww), False{}, ga)))
        case 1n+(+qq):
          match aa:
            case Nil{}:
              Empty.absurd({A.spec.rows.of(ww, 2n+qq, Png.ilv.rows([], bb)) == True{} : Bool}, M1.false_true(ga))
            case +xx <> +ta:
              match bb:
                case Nil{}:
                  Empty.absurd({A.spec.rows.of(ww, 2n+qq, Png.ilv.rows(xx <> ta, [])) == True{} : Bool},
                    M1.false_true(gb))
                case +yy <> +tb:
                  +ex = Nat.is_eq(List.length(&2, U32, xx), ww)
                  +ey = Nat.is_eq(List.length(&2, U32, yy), ww)
                  +ra = A.spec.rows.of(ww, A.spec.up(qq), ta)
                  +rb = A.spec.rows.of(ww, D2.half(qq), tb)
                  and.tt(ex, Bool.and(ey, A.spec.rows.of(ww, qq, Png.ilv.rows(ta, tb))), M1.and_left(ex, ra, ga),
                    and.tt(ey, A.spec.rows.of(ww, qq, Png.ilv.rows(ta, tb)), M1.and_left(ey, rb, gb),
                      ro.grid(ww, qq, ta, tb, M1.and_right(ex, ra, ga), M1.and_right(ey, rb, gb))))

# h rows of one sample, with no rows beside them, are halves
def c1.ok(
  hh: Nat,
  aa: List<&2, List<&2, U32>>,
  +ga: {A.spec.rows.of(1n, hh, aa) == True{} : Bool}
) -> {cols.ok(aa, []) == True{} : Bool}:
  match hh:
    case 0n:
      match aa:
        case Nil{}:
          {==}
        case xx <> ta:
          Empty.absurd({cols.ok(xx <> ta, []) == True{} : Bool}, M1.false_true(ga))
    case 1n+(+pp):
      match aa:
        case Nil{}:
          Empty.absurd({cols.ok([], []) == True{} : Bool}, M1.false_true(ga))
        case +xx <> +ta:
          +ex = Nat.is_eq(List.length(&2, U32, xx), 1n)
          +rt = A.spec.rows.of(1n, pp, ta)
          and.tt(hv.px(xx, []), cols.ok(ta, []), len.hv(1n, xx, [], M1.and_left(ex, rt, ga), {==}),
            c1.ok(pp, ta, M1.and_right(ex, rt, ga)))

# h rows of one sample, with no rows beside them, interleave to h rows of one sample
def c1.grid(
  hh: Nat,
  aa: List<&2, List<&2, U32>>,
  +ga: {A.spec.rows.of(1n, hh, aa) == True{} : Bool}
) -> {A.spec.rows.of(1n, hh, Png.ilv.cols(aa, [])) == True{} : Bool}:
  match hh:
    case 0n:
      match aa:
        case Nil{}:
          {==}
        case xx <> ta:
          Empty.absurd({A.spec.rows.of(1n, 0n, Png.ilv.cols(xx <> ta, [])) == True{} : Bool}, M1.false_true(ga))
    case 1n+(+pp):
      match aa:
        case Nil{}:
          Empty.absurd({A.spec.rows.of(1n, 1n+pp, Png.ilv.cols([], [])) == True{} : Bool}, M1.false_true(ga))
        case +xx <> +ta:
          +ex = Nat.is_eq(List.length(&2, U32, xx), 1n)
          +rt = A.spec.rows.of(1n, pp, ta)
          and.tt(Nat.is_eq(List.length(&2, U32, Png.ilv.px(xx, [])), 1n), A.spec.rows.of(1n, pp,
            Png.ilv.cols(ta, [])), len.ilv(1n, xx, [], M1.and_left(ex, rt, ga), {==}),
            c1.grid(pp, ta, M1.and_right(ex, rt, ga)))

# h rows of ceil(n / 2) samples and h of floor(n / 2) are halves
def c2.ok(
  +nn: Nat,
  hh: Nat,
  aa: List<&2, List<&2, U32>>,
  bb: List<&2, List<&2, U32>>,
  +ga: {A.spec.rows.of(A.spec.up(nn), hh, aa) == True{} : Bool},
  +gb: {A.spec.rows.of(D2.half(nn), hh, bb) == True{} : Bool}
) -> {cols.ok(aa, bb) == True{} : Bool}:
  match hh:
    case 0n:
      match aa:
        case Nil{}:
          match bb:
            case Nil{}:
              {==}
            case yy <> tb:
              Empty.absurd({cols.ok([], yy <> tb) == True{} : Bool}, M1.false_true(gb))
        case xx <> ta:
          Empty.absurd({cols.ok(xx <> ta, bb) == True{} : Bool}, M1.false_true(ga))
    case 1n+(+pp):
      match aa:
        case Nil{}:
          Empty.absurd({cols.ok([], bb) == True{} : Bool}, M1.false_true(ga))
        case +xx <> +ta:
          match bb:
            case Nil{}:
              Empty.absurd({cols.ok(xx <> ta, []) == True{} : Bool}, M1.false_true(gb))
            case +yy <> +tb:
              +ex = Nat.is_eq(List.length(&2, U32, xx), A.spec.up(nn))
              +ey = Nat.is_eq(List.length(&2, U32, yy), D2.half(nn))
              +ra = A.spec.rows.of(A.spec.up(nn), pp, ta)
              +rb = A.spec.rows.of(D2.half(nn), pp, tb)
              and.tt(hv.px(xx, yy), cols.ok(ta, tb), len.hv(nn, xx, yy, M1.and_left(ex, ra, ga), M1.and_left(ey, rb,
                gb)), c2.ok(nn, pp, ta, tb, M1.and_right(ex, ra, ga), M1.and_right(ey, rb, gb)))

# h rows of ceil(n / 2) samples and h of floor(n / 2) interleave to h rows of n
def c2.grid(
  +nn: Nat,
  hh: Nat,
  aa: List<&2, List<&2, U32>>,
  bb: List<&2, List<&2, U32>>,
  +ga: {A.spec.rows.of(A.spec.up(nn), hh, aa) == True{} : Bool},
  +gb: {A.spec.rows.of(D2.half(nn), hh, bb) == True{} : Bool}
) -> {A.spec.rows.of(nn, hh, Png.ilv.cols(aa, bb)) == True{} : Bool}:
  match hh:
    case 0n:
      match aa:
        case Nil{}:
          {==}
        case xx <> ta:
          Empty.absurd({A.spec.rows.of(nn, 0n, Png.ilv.cols(xx <> ta, bb)) == True{} : Bool}, M1.false_true(ga))
    case 1n+(+pp):
      match aa:
        case Nil{}:
          Empty.absurd({A.spec.rows.of(nn, 1n+pp, Png.ilv.cols([], bb)) == True{} : Bool}, M1.false_true(ga))
        case +xx <> +ta:
          match bb:
            case Nil{}:
              Empty.absurd({A.spec.rows.of(nn, 1n+pp, Png.ilv.cols(xx <> ta, [])) == True{} : Bool},
                M1.false_true(gb))
            case +yy <> +tb:
              +ex = Nat.is_eq(List.length(&2, U32, xx), A.spec.up(nn))
              +ey = Nat.is_eq(List.length(&2, U32, yy), D2.half(nn))
              +ra = A.spec.rows.of(A.spec.up(nn), pp, ta)
              +rb = A.spec.rows.of(D2.half(nn), pp, tb)
              and.tt(Nat.is_eq(List.length(&2, U32, Png.ilv.px(xx, yy)), nn), A.spec.rows.of(nn, pp,
                Png.ilv.cols(ta, tb)), len.ilv(nn, xx, yy, M1.and_left(ex, ra, ga), M1.and_left(ey, rb, gb)),
                c2.grid(nn, pp, ta, tb, M1.and_right(ex, ra, ga), M1.and_right(ey, rb, gb)))

# ---- each step of the merge ----

# a step interleaving rows: its halves are halves
def rows.cond(
  ww: Nat,
  +hh: Nat,
  aa: List<&2, List<&2, U32>>,
  bb: List<&2, List<&2, U32>>,
  ga: {A.spec.grid(ww, A.spec.up(hh), aa) == True{} : Bool},
  gb: {A.spec.grid(ww, D2.half(hh), bb) == True{} : Bool}
) -> {hv.rows(aa, bb) == True{} : Bool}:
  match ww:
    case 0n:
      match aa:
        case Nil{}:
          match bb:
            case Nil{}:
              {==}
            case yy <> tb:
              Empty.absurd({hv.rows([], yy <> tb) == True{} : Bool}, M1.false_true(gb))
        case xx <> ta:
          Empty.absurd({hv.rows(xx <> ta, bb) == True{} : Bool}, M1.false_true(ga))
    case 1n+pw:
      ro.hv(1n+pw, hh, aa, bb, ga, gb)

# a step interleaving rows: a w by h picture
def rows.grid(
  ww: Nat,
  +hh: Nat,
  aa: List<&2, List<&2, U32>>,
  bb: List<&2, List<&2, U32>>,
  ga: {A.spec.grid(ww, A.spec.up(hh), aa) == True{} : Bool},
  gb: {A.spec.grid(ww, D2.half(hh), bb) == True{} : Bool}
) -> {A.spec.grid(ww, hh, Png.ilv.rows(aa, bb)) == True{} : Bool}:
  match ww:
    case 0n:
      match aa:
        case Nil{}:
          match bb:
            case Nil{}:
              {==}
            case yy <> tb:
              Empty.absurd({A.spec.grid(0n, hh, Png.ilv.rows([], yy <> tb)) == True{} : Bool}, M1.false_true(gb))
        case xx <> ta:
          Empty.absurd({A.spec.grid(0n, hh, Png.ilv.rows(xx <> ta, bb)) == True{} : Bool}, M1.false_true(ga))
    case 1n+pw:
      ro.grid(1n+pw, hh, aa, bb, ga, gb)

# a step interleaving columns: its halves are halves
def cols.cond(
  ww: Nat,
  +hh: Nat,
  aa: List<&2, List<&2, U32>>,
  bb: List<&2, List<&2, U32>>,
  ga: {A.spec.grid(A.spec.up(ww), hh, aa) == True{} : Bool},
  gb: {A.spec.grid(D2.half(ww), hh, bb) == True{} : Bool}
) -> {cols.ok(aa, bb) == True{} : Bool}:
  match ww:
    case 0n:
      match aa:
        case Nil{}:
          match bb:
            case Nil{}:
              {==}
            case yy <> tb:
              Empty.absurd({cols.ok([], yy <> tb) == True{} : Bool}, M1.false_true(gb))
        case xx <> ta:
          Empty.absurd({cols.ok(xx <> ta, bb) == True{} : Bool}, M1.false_true(ga))
    case 1n+pw:
      match pw:
        case 0n:
          match bb:
            case Nil{}:
              c1.ok(hh, aa, ga)
            case yy <> tb:
              Empty.absurd({cols.ok(aa, yy <> tb) == True{} : Bool}, M1.false_true(gb))
        case 1n+(+qq):
          c2.ok(2n+qq, hh, aa, bb, ga, gb)

# a step interleaving columns: a w by h picture
def cols.grid(
  ww: Nat,
  +hh: Nat,
  aa: List<&2, List<&2, U32>>,
  bb: List<&2, List<&2, U32>>,
  ga: {A.spec.grid(A.spec.up(ww), hh, aa) == True{} : Bool},
  gb: {A.spec.grid(D2.half(ww), hh, bb) == True{} : Bool}
) -> {A.spec.grid(ww, hh, Png.ilv.cols(aa, bb)) == True{} : Bool}:
  match ww:
    case 0n:
      match aa:
        case Nil{}:
          {==}
        case xx <> ta:
          Empty.absurd({A.spec.grid(0n, hh, Png.ilv.cols(xx <> ta, bb)) == True{} : Bool}, M1.false_true(ga))
    case 1n+pw:
      match pw:
        case 0n:
          match bb:
            case Nil{}:
              c1.grid(hh, aa, ga)
            case yy <> tb:
              Empty.absurd({A.spec.grid(1n, hh, Png.ilv.cols(aa, yy <> tb)) == True{} : Bool}, M1.false_true(gb))
        case 1n+(+qq):
          c2.grid(2n+qq, hh, aa, bb, ga, gb)

# the merge so far, as a picture
def a7.g1(
  +ww: Nat,
  +hh: Nat,
  +r1: List<&2, List<&2, U32>>,
  +r2: List<&2, List<&2, U32>>,
  +g1: {A.spec.grid(A.spec.up(A.spec.up(A.spec.up(ww))), A.spec.up(A.spec.up(A.spec.up(hh))), r1) == True{} : Bool},
  +g2: {A.spec.grid(D2.half(A.spec.up(A.spec.up(ww))), A.spec.up(A.spec.up(A.spec.up(hh))), r2) == True{} : Bool}
) -> {A.spec.grid(A.spec.up(A.spec.up(ww)), A.spec.up(A.spec.up(A.spec.up(hh))), Png.ilv.cols(r1,
  r2)) == True{} : Bool}:
  cols.grid(A.spec.up(A.spec.up(ww)), A.spec.up(A.spec.up(A.spec.up(hh))), r1, r2, g1, g2)

# the merge so far, as a picture
def a7.g2(
  +ww: Nat,
  +hh: Nat,
  +r1: List<&2, List<&2, U32>>,
  +r2: List<&2, List<&2, U32>>,
  +r3: List<&2, List<&2, U32>>,
  +g1: {A.spec.grid(A.spec.up(A.spec.up(A.spec.up(ww))), A.spec.up(A.spec.up(A.spec.up(hh))), r1) == True{} : Bool},
  +g2: {A.spec.grid(D2.half(A.spec.up(A.spec.up(ww))), A.spec.up(A.spec.up(A.spec.up(hh))), r2) == True{} : Bool},
  +g3: {A.spec.grid(A.spec.up(A.spec.up(ww)), D2.half(A.spec.up(A.spec.up(hh))), r3) == True{} : Bool}
) -> {A.spec.grid(A.spec.up(A.spec.up(ww)), A.spec.up(A.spec.up(hh)), Png.ilv.rows(Png.ilv.cols(r1, r2),
  r3)) == True{} : Bool}:
  rows.grid(A.spec.up(A.spec.up(ww)), A.spec.up(A.spec.up(hh)), Png.ilv.cols(r1, r2), r3, a7.g1(ww, hh, r1, r2, g1,
    g2), g3)

# the merge so far, as a picture
def a7.g3(
  +ww: Nat,
  +hh: Nat,
  +r1: List<&2, List<&2, U32>>,
  +r2: List<&2, List<&2, U32>>,
  +r3: List<&2, List<&2, U32>>,
  +r4: List<&2, List<&2, U32>>,
  +g1: {A.spec.grid(A.spec.up(A.spec.up(A.spec.up(ww))), A.spec.up(A.spec.up(A.spec.up(hh))), r1) == True{} : Bool},
  +g2: {A.spec.grid(D2.half(A.spec.up(A.spec.up(ww))), A.spec.up(A.spec.up(A.spec.up(hh))), r2) == True{} : Bool},
  +g3: {A.spec.grid(A.spec.up(A.spec.up(ww)), D2.half(A.spec.up(A.spec.up(hh))), r3) == True{} : Bool},
  +g4: {A.spec.grid(D2.half(A.spec.up(ww)), A.spec.up(A.spec.up(hh)), r4) == True{} : Bool}
) -> {A.spec.grid(A.spec.up(ww), A.spec.up(A.spec.up(hh)), Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3),
  r4)) == True{} : Bool}:
  cols.grid(A.spec.up(ww), A.spec.up(A.spec.up(hh)), Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4, a7.g2(ww, hh, r1, r2,
    r3, g1, g2, g3), g4)

# the merge so far, as a picture
def a7.g4(
  +ww: Nat,
  +hh: Nat,
  +r1: List<&2, List<&2, U32>>,
  +r2: List<&2, List<&2, U32>>,
  +r3: List<&2, List<&2, U32>>,
  +r4: List<&2, List<&2, U32>>,
  +r5: List<&2, List<&2, U32>>,
  +g1: {A.spec.grid(A.spec.up(A.spec.up(A.spec.up(ww))), A.spec.up(A.spec.up(A.spec.up(hh))), r1) == True{} : Bool},
  +g2: {A.spec.grid(D2.half(A.spec.up(A.spec.up(ww))), A.spec.up(A.spec.up(A.spec.up(hh))), r2) == True{} : Bool},
  +g3: {A.spec.grid(A.spec.up(A.spec.up(ww)), D2.half(A.spec.up(A.spec.up(hh))), r3) == True{} : Bool},
  +g4: {A.spec.grid(D2.half(A.spec.up(ww)), A.spec.up(A.spec.up(hh)), r4) == True{} : Bool},
  +g5: {A.spec.grid(A.spec.up(ww), D2.half(A.spec.up(hh)), r5) == True{} : Bool}
) -> {A.spec.grid(A.spec.up(ww), A.spec.up(hh), Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4),
  r5)) == True{} : Bool}:
  rows.grid(A.spec.up(ww), A.spec.up(hh), Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4), r5, a7.g3(ww, hh,
    r1, r2, r3, r4, g1, g2, g3, g4), g5)

# the merge so far, as a picture
def a7.g5(
  +ww: Nat,
  +hh: Nat,
  +r1: List<&2, List<&2, U32>>,
  +r2: List<&2, List<&2, U32>>,
  +r3: List<&2, List<&2, U32>>,
  +r4: List<&2, List<&2, U32>>,
  +r5: List<&2, List<&2, U32>>,
  +r6: List<&2, List<&2, U32>>,
  +g1: {A.spec.grid(A.spec.up(A.spec.up(A.spec.up(ww))), A.spec.up(A.spec.up(A.spec.up(hh))), r1) == True{} : Bool},
  +g2: {A.spec.grid(D2.half(A.spec.up(A.spec.up(ww))), A.spec.up(A.spec.up(A.spec.up(hh))), r2) == True{} : Bool},
  +g3: {A.spec.grid(A.spec.up(A.spec.up(ww)), D2.half(A.spec.up(A.spec.up(hh))), r3) == True{} : Bool},
  +g4: {A.spec.grid(D2.half(A.spec.up(ww)), A.spec.up(A.spec.up(hh)), r4) == True{} : Bool},
  +g5: {A.spec.grid(A.spec.up(ww), D2.half(A.spec.up(hh)), r5) == True{} : Bool},
  +g6: {A.spec.grid(D2.half(ww), A.spec.up(hh), r6) == True{} : Bool}
) -> {A.spec.grid(ww, A.spec.up(hh), Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3),
  r4), r5), r6)) == True{} : Bool}:
  cols.grid(ww, A.spec.up(hh), Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4), r5), r6,
    a7.g4(ww, hh, r1, r2, r3, r4, r5, g1, g2, g3, g4, g5), g6)

# the halves of a step of the merge
def a7.c1(
  +ww: Nat,
  +hh: Nat,
  +r1: List<&2, List<&2, U32>>,
  +r2: List<&2, List<&2, U32>>,
  +g1: {A.spec.grid(A.spec.up(A.spec.up(A.spec.up(ww))), A.spec.up(A.spec.up(A.spec.up(hh))), r1) == True{} : Bool},
  +g2: {A.spec.grid(D2.half(A.spec.up(A.spec.up(ww))), A.spec.up(A.spec.up(A.spec.up(hh))), r2) == True{} : Bool}
) -> {cols.ok(r1, r2) == True{} : Bool}:
  cols.cond(A.spec.up(A.spec.up(ww)), A.spec.up(A.spec.up(A.spec.up(hh))), r1, r2, g1, g2)

# the halves of a step of the merge
def a7.c2(
  +ww: Nat,
  +hh: Nat,
  +r1: List<&2, List<&2, U32>>,
  +r2: List<&2, List<&2, U32>>,
  +r3: List<&2, List<&2, U32>>,
  +g1: {A.spec.grid(A.spec.up(A.spec.up(A.spec.up(ww))), A.spec.up(A.spec.up(A.spec.up(hh))), r1) == True{} : Bool},
  +g2: {A.spec.grid(D2.half(A.spec.up(A.spec.up(ww))), A.spec.up(A.spec.up(A.spec.up(hh))), r2) == True{} : Bool},
  +g3: {A.spec.grid(A.spec.up(A.spec.up(ww)), D2.half(A.spec.up(A.spec.up(hh))), r3) == True{} : Bool}
) -> {hv.rows(Png.ilv.cols(r1, r2), r3) == True{} : Bool}:
  rows.cond(A.spec.up(A.spec.up(ww)), A.spec.up(A.spec.up(hh)), Png.ilv.cols(r1, r2), r3, a7.g1(ww, hh, r1, r2, g1,
    g2), g3)

# the halves of a step of the merge
def a7.c3(
  +ww: Nat,
  +hh: Nat,
  +r1: List<&2, List<&2, U32>>,
  +r2: List<&2, List<&2, U32>>,
  +r3: List<&2, List<&2, U32>>,
  +r4: List<&2, List<&2, U32>>,
  +g1: {A.spec.grid(A.spec.up(A.spec.up(A.spec.up(ww))), A.spec.up(A.spec.up(A.spec.up(hh))), r1) == True{} : Bool},
  +g2: {A.spec.grid(D2.half(A.spec.up(A.spec.up(ww))), A.spec.up(A.spec.up(A.spec.up(hh))), r2) == True{} : Bool},
  +g3: {A.spec.grid(A.spec.up(A.spec.up(ww)), D2.half(A.spec.up(A.spec.up(hh))), r3) == True{} : Bool},
  +g4: {A.spec.grid(D2.half(A.spec.up(ww)), A.spec.up(A.spec.up(hh)), r4) == True{} : Bool}
) -> {cols.ok(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4) == True{} : Bool}:
  cols.cond(A.spec.up(ww), A.spec.up(A.spec.up(hh)), Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4, a7.g2(ww, hh, r1, r2,
    r3, g1, g2, g3), g4)

# the halves of a step of the merge
def a7.c4(
  +ww: Nat,
  +hh: Nat,
  +r1: List<&2, List<&2, U32>>,
  +r2: List<&2, List<&2, U32>>,
  +r3: List<&2, List<&2, U32>>,
  +r4: List<&2, List<&2, U32>>,
  +r5: List<&2, List<&2, U32>>,
  +g1: {A.spec.grid(A.spec.up(A.spec.up(A.spec.up(ww))), A.spec.up(A.spec.up(A.spec.up(hh))), r1) == True{} : Bool},
  +g2: {A.spec.grid(D2.half(A.spec.up(A.spec.up(ww))), A.spec.up(A.spec.up(A.spec.up(hh))), r2) == True{} : Bool},
  +g3: {A.spec.grid(A.spec.up(A.spec.up(ww)), D2.half(A.spec.up(A.spec.up(hh))), r3) == True{} : Bool},
  +g4: {A.spec.grid(D2.half(A.spec.up(ww)), A.spec.up(A.spec.up(hh)), r4) == True{} : Bool},
  +g5: {A.spec.grid(A.spec.up(ww), D2.half(A.spec.up(hh)), r5) == True{} : Bool}
) -> {hv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4), r5) == True{} : Bool}:
  rows.cond(A.spec.up(ww), A.spec.up(hh), Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4), r5, a7.g3(ww, hh,
    r1, r2, r3, r4, g1, g2, g3, g4), g5)

# the halves of a step of the merge
def a7.c5(
  +ww: Nat,
  +hh: Nat,
  +r1: List<&2, List<&2, U32>>,
  +r2: List<&2, List<&2, U32>>,
  +r3: List<&2, List<&2, U32>>,
  +r4: List<&2, List<&2, U32>>,
  +r5: List<&2, List<&2, U32>>,
  +r6: List<&2, List<&2, U32>>,
  +g1: {A.spec.grid(A.spec.up(A.spec.up(A.spec.up(ww))), A.spec.up(A.spec.up(A.spec.up(hh))), r1) == True{} : Bool},
  +g2: {A.spec.grid(D2.half(A.spec.up(A.spec.up(ww))), A.spec.up(A.spec.up(A.spec.up(hh))), r2) == True{} : Bool},
  +g3: {A.spec.grid(A.spec.up(A.spec.up(ww)), D2.half(A.spec.up(A.spec.up(hh))), r3) == True{} : Bool},
  +g4: {A.spec.grid(D2.half(A.spec.up(ww)), A.spec.up(A.spec.up(hh)), r4) == True{} : Bool},
  +g5: {A.spec.grid(A.spec.up(ww), D2.half(A.spec.up(hh)), r5) == True{} : Bool},
  +g6: {A.spec.grid(D2.half(ww), A.spec.up(hh), r6) == True{} : Bool}
) -> {cols.ok(Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4), r5), r6) == True{} : Bool}:
  cols.cond(ww, A.spec.up(hh), Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4), r5), r6,
    a7.g4(ww, hh, r1, r2, r3, r4, r5, g1, g2, g3, g4, g5), g6)

# the halves of a step of the merge
def a7.c6(
  +ww: Nat,
  +hh: Nat,
  +r1: List<&2, List<&2, U32>>,
  +r2: List<&2, List<&2, U32>>,
  +r3: List<&2, List<&2, U32>>,
  +r4: List<&2, List<&2, U32>>,
  +r5: List<&2, List<&2, U32>>,
  +r6: List<&2, List<&2, U32>>,
  +r7: List<&2, List<&2, U32>>,
  +g1: {A.spec.grid(A.spec.up(A.spec.up(A.spec.up(ww))), A.spec.up(A.spec.up(A.spec.up(hh))), r1) == True{} : Bool},
  +g2: {A.spec.grid(D2.half(A.spec.up(A.spec.up(ww))), A.spec.up(A.spec.up(A.spec.up(hh))), r2) == True{} : Bool},
  +g3: {A.spec.grid(A.spec.up(A.spec.up(ww)), D2.half(A.spec.up(A.spec.up(hh))), r3) == True{} : Bool},
  +g4: {A.spec.grid(D2.half(A.spec.up(ww)), A.spec.up(A.spec.up(hh)), r4) == True{} : Bool},
  +g5: {A.spec.grid(A.spec.up(ww), D2.half(A.spec.up(hh)), r5) == True{} : Bool},
  +g6: {A.spec.grid(D2.half(ww), A.spec.up(hh), r6) == True{} : Bool},
  +g7: {A.spec.grid(ww, D2.half(hh), r7) == True{} : Bool}
) -> {hv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4), r5), r6),
  r7) == True{} : Bool}:
  rows.cond(ww, hh, Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4), r5), r6), r7,
    a7.g5(ww, hh, r1, r2, r3, r4, r5, r6, g1, g2, g3, g4, g5, g6), g7)

def A.png_a7_grid(ww, hh, r1, r2, r3, r4, r5, r6, r7, g1, g2, g3, g4, g5, g6, g7):
  rows.grid(ww, hh, Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4), r5), r6), r7,
    a7.g5(ww, hh, r1, r2, r3, r4, r5, r6, g1, g2, g3, g4, g5, g6), g7)

def A.png_a7_pass1(ww, hh, r1, r2, r3, r4, r5, r6, r7, g1, g2, g3, g4, g5, g6, g7, ii, kk):
  Equal.trans(Maybe<&2, U32>, A.spec.at(Png.a7.merge(r1, r2, r3, r4, r5, r6, r7),
    Nat.double(Nat.double(Nat.double(ii))), Nat.double(Nat.double(Nat.double(kk)))),
      A.spec.at(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4), r5), r6),
        Nat.double(Nat.double(Nat.double(ii))), Nat.double(Nat.double(kk))), A.spec.at(r1, ii, kk),
      rw.even.at(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4), r5), r6), r7,
        Nat.double(Nat.double(Nat.double(ii))), Nat.double(Nat.double(kk)), a7.c6(ww, hh, r1, r2, r3, r4, r5, r6, r7,
          g1, g2, g3, g4, g5, g6, g7)),
      Equal.trans(Maybe<&2, U32>, A.spec.at(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2),
        r3), r4), r5), r6), Nat.double(Nat.double(Nat.double(ii))), Nat.double(Nat.double(kk))),
          A.spec.at(Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4), r5),
            Nat.double(Nat.double(ii)), Nat.double(Nat.double(kk))), A.spec.at(r1, ii, kk),
      cl.even(Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4), r5), r6,
        Nat.double(Nat.double(ii)), Nat.double(Nat.double(kk)), a7.c5(ww, hh, r1, r2, r3, r4, r5, r6, g1, g2, g3, g4,
          g5, g6)),
      Equal.trans(Maybe<&2, U32>, A.spec.at(Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4),
        r5), Nat.double(Nat.double(ii)), Nat.double(Nat.double(kk))),
          A.spec.at(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4), Nat.double(Nat.double(ii)),
            Nat.double(kk)), A.spec.at(r1, ii, kk),
      rw.even.at(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4), r5, Nat.double(Nat.double(ii)),
        Nat.double(kk), a7.c4(ww, hh, r1, r2, r3, r4, r5, g1, g2, g3, g4, g5)),
      Equal.trans(Maybe<&2, U32>, A.spec.at(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4),
        Nat.double(Nat.double(ii)), Nat.double(kk)), A.spec.at(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), Nat.double(ii),
          Nat.double(kk)), A.spec.at(r1, ii, kk),
      cl.even(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4, Nat.double(ii), Nat.double(kk), a7.c3(ww, hh, r1, r2, r3,
        r4, g1, g2, g3, g4)),
      Equal.trans(Maybe<&2, U32>, A.spec.at(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), Nat.double(ii), Nat.double(kk)),
        A.spec.at(Png.ilv.cols(r1, r2), Nat.double(ii), kk), A.spec.at(r1, ii, kk),
      rw.even.at(Png.ilv.cols(r1, r2), r3, Nat.double(ii), kk, a7.c2(ww, hh, r1, r2, r3, g1, g2, g3)),
      cl.even(r1, r2, ii, kk, a7.c1(ww, hh, r1, r2, g1, g2)))))))

def A.png_a7_pass2(ww, hh, r1, r2, r3, r4, r5, r6, r7, g1, g2, g3, g4, g5, g6, g7, ii, kk):
  Equal.trans(Maybe<&2, U32>, A.spec.at(Png.a7.merge(r1, r2, r3, r4, r5, r6, r7),
    Nat.double(Nat.double(1n+Nat.double(ii))), Nat.double(Nat.double(Nat.double(kk)))),
      A.spec.at(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4), r5), r6),
        Nat.double(Nat.double(1n+Nat.double(ii))), Nat.double(Nat.double(kk))), A.spec.at(r2, ii, kk),
      rw.even.at(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4), r5), r6), r7,
        Nat.double(Nat.double(1n+Nat.double(ii))), Nat.double(Nat.double(kk)), a7.c6(ww, hh, r1, r2, r3, r4, r5, r6,
          r7, g1, g2, g3, g4, g5, g6, g7)),
      Equal.trans(Maybe<&2, U32>, A.spec.at(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2),
        r3), r4), r5), r6), Nat.double(Nat.double(1n+Nat.double(ii))), Nat.double(Nat.double(kk))),
          A.spec.at(Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4), r5),
            Nat.double(1n+Nat.double(ii)), Nat.double(Nat.double(kk))), A.spec.at(r2, ii, kk),
      cl.even(Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4), r5), r6,
        Nat.double(1n+Nat.double(ii)), Nat.double(Nat.double(kk)), a7.c5(ww, hh, r1, r2, r3, r4, r5, r6, g1, g2, g3,
          g4, g5, g6)),
      Equal.trans(Maybe<&2, U32>, A.spec.at(Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4),
        r5), Nat.double(1n+Nat.double(ii)), Nat.double(Nat.double(kk))),
          A.spec.at(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4), Nat.double(1n+Nat.double(ii)),
            Nat.double(kk)), A.spec.at(r2, ii, kk),
      rw.even.at(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4), r5, Nat.double(1n+Nat.double(ii)),
        Nat.double(kk), a7.c4(ww, hh, r1, r2, r3, r4, r5, g1, g2, g3, g4, g5)),
      Equal.trans(Maybe<&2, U32>, A.spec.at(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4),
        Nat.double(1n+Nat.double(ii)), Nat.double(kk)), A.spec.at(Png.ilv.rows(Png.ilv.cols(r1, r2), r3),
          1n+Nat.double(ii), Nat.double(kk)), A.spec.at(r2, ii, kk),
      cl.even(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4, 1n+Nat.double(ii), Nat.double(kk), a7.c3(ww, hh, r1, r2, r3,
        r4, g1, g2, g3, g4)),
      Equal.trans(Maybe<&2, U32>, A.spec.at(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), 1n+Nat.double(ii),
        Nat.double(kk)), A.spec.at(Png.ilv.cols(r1, r2), 1n+Nat.double(ii), kk), A.spec.at(r2, ii, kk),
      rw.even.at(Png.ilv.cols(r1, r2), r3, 1n+Nat.double(ii), kk, a7.c2(ww, hh, r1, r2, r3, g1, g2, g3)),
      cl.odd(r1, r2, ii, kk, a7.c1(ww, hh, r1, r2, g1, g2)))))))

def A.png_a7_pass3(ww, hh, r1, r2, r3, r4, r5, r6, r7, g1, g2, g3, g4, g5, g6, g7, ii, kk):
  Equal.trans(Maybe<&2, U32>, A.spec.at(Png.a7.merge(r1, r2, r3, r4, r5, r6, r7), Nat.double(Nat.double(ii)),
    Nat.double(Nat.double(1n+Nat.double(kk)))),
      A.spec.at(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4), r5), r6),
        Nat.double(Nat.double(ii)), Nat.double(1n+Nat.double(kk))), A.spec.at(r3, ii, kk),
      rw.even.at(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4), r5), r6), r7,
        Nat.double(Nat.double(ii)), Nat.double(1n+Nat.double(kk)), a7.c6(ww, hh, r1, r2, r3, r4, r5, r6, r7, g1, g2,
          g3, g4, g5, g6, g7)),
      Equal.trans(Maybe<&2, U32>, A.spec.at(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2),
        r3), r4), r5), r6), Nat.double(Nat.double(ii)), Nat.double(1n+Nat.double(kk))),
          A.spec.at(Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4), r5), Nat.double(ii),
            Nat.double(1n+Nat.double(kk))), A.spec.at(r3, ii, kk),
      cl.even(Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4), r5), r6, Nat.double(ii),
        Nat.double(1n+Nat.double(kk)), a7.c5(ww, hh, r1, r2, r3, r4, r5, r6, g1, g2, g3, g4, g5, g6)),
      Equal.trans(Maybe<&2, U32>, A.spec.at(Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4),
        r5), Nat.double(ii), Nat.double(1n+Nat.double(kk))), A.spec.at(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2),
          r3), r4), Nat.double(ii), 1n+Nat.double(kk)), A.spec.at(r3, ii, kk),
      rw.even.at(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4), r5, Nat.double(ii), 1n+Nat.double(kk),
        a7.c4(ww, hh, r1, r2, r3, r4, r5, g1, g2, g3, g4, g5)),
      Equal.trans(Maybe<&2, U32>, A.spec.at(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4), Nat.double(ii),
        1n+Nat.double(kk)), A.spec.at(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), ii, 1n+Nat.double(kk)), A.spec.at(r3,
          ii, kk),
      cl.even(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4, ii, 1n+Nat.double(kk), a7.c3(ww, hh, r1, r2, r3, r4, g1, g2,
        g3, g4)),
      rw.odd.at(Png.ilv.cols(r1, r2), r3, ii, kk, a7.c2(ww, hh, r1, r2, r3, g1, g2, g3))))))

def A.png_a7_pass4(ww, hh, r1, r2, r3, r4, r5, r6, r7, g1, g2, g3, g4, g5, g6, g7, ii, kk):
  Equal.trans(Maybe<&2, U32>, A.spec.at(Png.a7.merge(r1, r2, r3, r4, r5, r6, r7), Nat.double(1n+Nat.double(ii)),
    Nat.double(Nat.double(kk))), A.spec.at(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2),
      r3), r4), r5), r6), Nat.double(1n+Nat.double(ii)), Nat.double(kk)), A.spec.at(r4, ii, kk),
      rw.even.at(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4), r5), r6), r7,
        Nat.double(1n+Nat.double(ii)), Nat.double(kk), a7.c6(ww, hh, r1, r2, r3, r4, r5, r6, r7, g1, g2, g3, g4, g5,
          g6, g7)),
      Equal.trans(Maybe<&2, U32>, A.spec.at(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2),
        r3), r4), r5), r6), Nat.double(1n+Nat.double(ii)), Nat.double(kk)),
          A.spec.at(Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4), r5), 1n+Nat.double(ii),
            Nat.double(kk)), A.spec.at(r4, ii, kk),
      cl.even(Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4), r5), r6, 1n+Nat.double(ii),
        Nat.double(kk), a7.c5(ww, hh, r1, r2, r3, r4, r5, r6, g1, g2, g3, g4, g5, g6)),
      Equal.trans(Maybe<&2, U32>, A.spec.at(Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4),
        r5), 1n+Nat.double(ii), Nat.double(kk)), A.spec.at(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4),
          1n+Nat.double(ii), kk), A.spec.at(r4, ii, kk),
      rw.even.at(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4), r5, 1n+Nat.double(ii), kk, a7.c4(ww, hh,
        r1, r2, r3, r4, r5, g1, g2, g3, g4, g5)),
      cl.odd(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4, ii, kk, a7.c3(ww, hh, r1, r2, r3, r4, g1, g2, g3, g4)))))

def A.png_a7_pass5(ww, hh, r1, r2, r3, r4, r5, r6, r7, g1, g2, g3, g4, g5, g6, g7, ii, kk):
  Equal.trans(Maybe<&2, U32>, A.spec.at(Png.a7.merge(r1, r2, r3, r4, r5, r6, r7), Nat.double(ii),
    Nat.double(1n+Nat.double(kk))), A.spec.at(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1,
      r2), r3), r4), r5), r6), Nat.double(ii), 1n+Nat.double(kk)), A.spec.at(r5, ii, kk),
      rw.even.at(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4), r5), r6), r7,
        Nat.double(ii), 1n+Nat.double(kk), a7.c6(ww, hh, r1, r2, r3, r4, r5, r6, r7, g1, g2, g3, g4, g5, g6, g7)),
      Equal.trans(Maybe<&2, U32>, A.spec.at(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2),
        r3), r4), r5), r6), Nat.double(ii), 1n+Nat.double(kk)),
          A.spec.at(Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4), r5), ii,
            1n+Nat.double(kk)), A.spec.at(r5, ii, kk),
      cl.even(Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4), r5), r6, ii, 1n+Nat.double(kk),
        a7.c5(ww, hh, r1, r2, r3, r4, r5, r6, g1, g2, g3, g4, g5, g6)),
      rw.odd.at(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4), r5, ii, kk, a7.c4(ww, hh, r1, r2, r3, r4,
        r5, g1, g2, g3, g4, g5))))

def A.png_a7_pass6(ww, hh, r1, r2, r3, r4, r5, r6, r7, g1, g2, g3, g4, g5, g6, g7, ii, kk):
  Equal.trans(Maybe<&2, U32>, A.spec.at(Png.a7.merge(r1, r2, r3, r4, r5, r6, r7), 1n+Nat.double(ii), Nat.double(kk)),
    A.spec.at(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4), r5), r6),
      1n+Nat.double(ii), kk), A.spec.at(r6, ii, kk),
      rw.even.at(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4), r5), r6), r7,
        1n+Nat.double(ii), kk, a7.c6(ww, hh, r1, r2, r3, r4, r5, r6, r7, g1, g2, g3, g4, g5, g6, g7)),
      cl.odd(Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4), r5), r6, ii, kk, a7.c5(ww, hh, r1,
        r2, r3, r4, r5, r6, g1, g2, g3, g4, g5, g6)))

def A.png_a7_pass7(ww, hh, r1, r2, r3, r4, r5, r6, r7, g1, g2, g3, g4, g5, g6, g7, ii, kk):
  rw.odd.at(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(Png.ilv.rows(Png.ilv.cols(r1, r2), r3), r4), r5), r6), r7, ii, kk,
    a7.c6(ww, hh, r1, r2, r3, r4, r5, r6, r7, g1, g2, g3, g4, g5, g6, g7))
