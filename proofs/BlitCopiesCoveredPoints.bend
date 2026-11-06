# proofs of laws/BlitCopiesCoveredPoints.bend
import Base
import ../main.bend as Img
import ../laws/BlitCopiesCoveredPoints.bend as Laws
import ../laws/defs/BlitCover.bend as D1
import ../laws/defs/WellFormed.bend as D2
import ./lemmas/BasicFacts.bend as M1
import ./lemmas/ListTakeDrop.bend as M2
import ./lemmas/RowMajorIndex.bend as M3
import ./lemmas/RowWalk.bend as M6
import ./lemmas/SubtractionAndHuffmanWalk.bend as M4
import ./lemmas/WordAddition.bend as M5

# ---- more on append, take and drop ----

# below the first list's length, an append reads as the first list
law get_append_lt:
  for aa: List<&2, U32>
  for kk: Nat
  for -rest: List<&2, U32>
  for hk: {Nat.is_lt(kk, List.length(&2, U32, aa)) == True{} : Bool}
  {List.get(&2, U32, List.append(&2, U32, aa, rest), kk) == List.get(&2, U32, aa, kk) : Maybe<&2, U32>}

# the proof of get_append_lt
def get_append_lt(aa, kk, rest, hk):
  match aa kk:
    case Nil{} _kk:
      Empty.absurd({List.get(&2, U32, rest, _kk) == None{} : Maybe<&2, U32>}, M1.false_true(
        Equal.trans(Bool, False{}, Nat.is_lt(_kk, 0n), True{}, M1.lt_zero_false(_kk), hk)))
    case _hd <> _tl 0n:
      {==}
    case _hd <> tl 1n+qq:
      get_append_lt(tl, qq, rest, hk)

# past the first list's length, an append reads as the second list
law get_append_len:
  for aa: List<&2, U32>
  for -kk: Nat
  for -rest: List<&2, U32>
  {List.get(&2, U32, List.append(&2, U32, aa, rest), Nat.add(List.length(&2, U32, aa), kk)) ==
    List.get(&2, U32, rest, kk) : Maybe<&2, U32>}

# the proof of get_append_len
def get_append_len(aa, kk, rest):
  match aa:
    case Nil{}:
      {==}
    case _hd <> tl:
      get_append_len(tl, kk, rest)

# below n, the first n elements read as the list
law get_take:
  for xs: List<&2, U32>
  for nn: Nat
  for kk: Nat
  for hk: {Nat.is_lt(kk, nn) == True{} : Bool}
  {List.get(&2, U32, List.take(&2, U32, xs, nn), kk) == List.get(&2, U32, xs, kk) : Maybe<&2, U32>}

# the proof of get_take
def get_take(xs, nn, kk, hk):
  match xs nn kk:
    case Nil{} _nn _kk:
      {==}
    case _hd <> _tl 0n _kk:
      Empty.absurd({None{} == List.get(&2, U32, _hd <> _tl, _kk) : Maybe<&2, U32>}, M1.false_true(
        Equal.trans(Bool, False{}, Nat.is_lt(_kk, 0n), True{}, M1.lt_zero_false(_kk), hk)))
    case _hd <> _tl 1n+_qq 0n:
      {==}
    case _hd <> tl 1n+qq 1n+pk:
      get_take(tl, qq, pk, hk)

# dropping from the empty list leaves it empty
law drop_nil:
  for nn: Nat
  {List.drop(&2, U32, Nil{}, nn) == Nil{} : List<&2, U32>}

# the proof of drop_nil
def drop_nil(_nn):
  {==}

# dropping a then b drops a + b
law drop_drop:
  for xs: List<&2, U32>
  for aa: Nat
  for bb: Nat
  {List.drop(&2, U32, List.drop(&2, U32, xs, aa), bb) == List.drop(&2, U32, xs, Nat.add(aa, bb)) : List<&2, U32>}

# the proof of drop_drop
def drop_drop(xs, aa, bb):
  match xs aa:
    case Nil{} _aa:
      drop_nil(bb)
    case _hd <> _tl 0n:
      {==}
    case _hd <> tl 1n+qq:
      drop_drop(tl, qq, bb)

# dropping nothing is the list
law drop_zero:
  for xs: List<&2, U32>
  {List.drop(&2, U32, xs, 0n) == xs : List<&2, U32>}

# the proof of drop_zero
def drop_zero(xs):
  match xs:
    case Nil{}:
      {==}
    case _hd <> _tl:
      {==}

# m + k <= length gives k <= length after dropping m
law drop_le0:
  for +xs: List<&2, U32>
  for +mm: Nat
  for +kk: Nat
  for hh: {Nat.is_le(Nat.add(mm, kk), List.length(&2, U32, xs)) == True{} : Bool}
  {Nat.is_le(kk, List.length(&2, U32, List.drop(&2, U32, xs, mm))) == True{} : Bool}

# the proof of drop_le0
def drop_le0(xs, mm, kk, hh):
  +ln = List.length(&2, U32, List.drop(&2, U32, xs, mm))
  M1.le_rw_r(kk, Nat.add(ln, 0n), ln, M1.ras.add_zero(ln), M2.drop_le(xs, mm, kk, 0n,
    M1.le_rw_r(Nat.add(mm, kk), List.length(&2, U32, xs), Nat.add(List.length(&2, U32, xs), 0n),
      Equal.sym(Nat, Nat.add(List.length(&2, U32, xs), 0n), List.length(&2, U32, xs),
        M1.ras.add_zero(List.length(&2, U32, xs))), hh)))

# ---- more order facts ----

# min(a, b) <= a
law min_le_l:
  for aa: Nat
  for bb: Nat
  {Nat.is_le(Nat.min(aa, bb), aa) == True{} : Bool}

# the proof of min_le_l
def min_le_l(aa, bb):
  match aa bb:
    case 0n _bb:
      {==}
    case 1n+pa 0n:
      M1.le_zero(1n+pa)
    case 1n+pa 1n+pb:
      min_le_l(pa, pb)

# below both, below their min
law lt_min:
  for xx: Nat
  for aa: Nat
  for bb: Nat
  for ha: {Nat.is_lt(xx, aa) == True{} : Bool}
  for hb: {Nat.is_lt(xx, bb) == True{} : Bool}
  {Nat.is_lt(xx, Nat.min(aa, bb)) == True{} : Bool}

# the proof of lt_min
def lt_min(xx, aa, bb, ha, hb):
  match xx aa bb:
    case _xx 0n _bb:
      Empty.absurd({Nat.is_lt(_xx, Nat.min(0n, _bb)) == True{} : Bool}, M1.false_true(
        Equal.trans(Bool, False{}, Nat.is_lt(_xx, 0n), True{}, M1.lt_zero_false(_xx), ha)))
    case _xx 1n+_pa 0n:
      Empty.absurd({Nat.is_lt(_xx, 0n) == True{} : Bool}, M1.false_true(
        Equal.trans(Bool, False{}, Nat.is_lt(_xx, 0n), True{}, M1.lt_zero_false(_xx), hb)))
    case 0n 1n+_pa 1n+_pb:
      {==}
    case 1n+px 1n+pa 1n+pb:
      lt_min(px, pa, pb, ha, hb)

# min(a, b) < b gives min(a, b) = a
law min_lt_r:
  for aa: Nat
  for bb: Nat
  for hh: {Nat.is_lt(Nat.min(aa, bb), bb) == True{} : Bool}
  {Nat.min(aa, bb) == aa : Nat}

# the proof of min_lt_r
def min_lt_r(aa, bb, hh):
  match aa bb:
    case 0n _bb:
      {==}
    case 1n+_pa 0n:
      Empty.absurd({0n == 1n+_pa : Nat}, M1.false_true(hh))
    case 1n+pa 1n+pb:
      Equal.cong(Nat, Nat, xx => 1n+xx, Nat.min(pa, pb), pa, min_lt_r(pa, pb, hh))

# what dropping m <= length leaves, and m, make up the length
law len_drop_add:
  for xs: List<&2, U32>
  for mm: Nat
  for hh: {Nat.is_le(mm, List.length(&2, U32, xs)) == True{} : Bool}
  {Nat.add(mm, List.length(&2, U32, List.drop(&2, U32, xs, mm))) == List.length(&2, U32, xs) : Nat}

# the proof of len_drop_add
def len_drop_add(xs, mm, hh):
  match xs mm:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+_qq:
      Empty.absurd({Nat.add(1n+_qq, 0n) == 0n : Nat}, M1.false_true(hh))
    case _hd <> _tl 0n:
      {==}
    case _hd <> tl 1n+qq:
      Equal.cong(Nat, Nat, xx => 1n+xx, Nat.add(qq, List.length(&2, U32, List.drop(&2, U32, tl, qq))),
        List.length(&2, U32, tl), len_drop_add(tl, qq, hh))

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
  +ht = {drop_le0(dp, Nat.add(ll, cc), tt, M1.le_rw_l(Nat.add(ll, Nat.add(cc, tt)), Nat.add(Nat.add(ll, cc), tt), ln,
    Equal.sym(Nat, Nat.add(Nat.add(ll, cc), tt), Nat.add(ll, Nat.add(cc, tt)), M1.ras.add_assoc(ll, cc, tt)), hd)) :
    {Nat.is_le(tt, List.length(&2, U32, dr)) == True{} : Bool}}
  +e_in = {Equal.trans(Nat, List.length(&2, U32, inner), Nat.add(List.length(&2, U32, sk), List.length(&2, U32, tk)),
    Nat.add(cc, tt), M2.len_append(sk, tk),
    Equal.trans(Nat, Nat.add(List.length(&2, U32, sk), List.length(&2, U32, tk)), Nat.add(cc, List.length(&2, U32, tk)),
      Nat.add(cc, tt),
      Equal.cong(Nat, Nat, nn => Nat.add(nn, List.length(&2, U32, tk)), List.length(&2, U32, sk), cc,
        M2.len_take(sp, cc, hs)),
      Equal.cong(Nat, Nat, nn => Nat.add(cc, nn), List.length(&2, U32, tk), tt, M2.len_take(dr, tt, ht)))) :
    {List.length(&2, U32, inner) == Nat.add(cc, tt) : Nat}}
  Equal.trans(Nat, List.length(&2, U32, List.append(&2, U32, List.take(&2, U32, dp, ll), inner)),
    Nat.add(List.length(&2, U32, List.take(&2, U32, dp, ll)), List.length(&2, U32, inner)), Nat.add(ll, Nat.add(cc,
      tt)),
    M2.len_append(List.take(&2, U32, dp, ll), inner),
    Equal.trans(Nat, Nat.add(List.length(&2, U32, List.take(&2, U32, dp, ll)), List.length(&2, U32, inner)),
      Nat.add(ll, List.length(&2, U32, inner)), Nat.add(ll, Nat.add(cc, tt)),
      Equal.cong(Nat, Nat, nn => Nat.add(nn, List.length(&2, U32, inner)), List.length(&2, U32, List.take(&2, U32,
        dp, ll)),
        ll, M2.len_take(dp, ll, M5.le_add_r(ll, Nat.add(cc, tt), ln, hd))),
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
  M2.get_append_take(dp, ll, ii, List.append(&2, U32, List.take(&2, U32, sp, cc),
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
    M2.get_append_skip(dp, ll, kk, List.append(&2, U32, List.take(&2, U32, sp, cc), r2), hl),
    M2.get_append_take(sp, cc, kk, r2, hk, hc))

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
    M2.get_append_skip(dp, ll, Nat.add(cc, kk), List.append(&2, U32, List.take(&2, U32, sp, cc), r2), hl),
    Equal.trans(Maybe<&2, U32>, List.get(&2, U32, List.append(&2, U32, List.take(&2, U32, sp, cc), r2), Nat.add(cc,
      kk)),
      List.get(&2, U32, r2, kk), List.get(&2, U32, dp, Nat.add(Nat.add(ll, cc), kk)),
      M2.get_append_skip(sp, cc, kk, r2, hc),
      Equal.trans(Maybe<&2, U32>, List.get(&2, U32, r2, kk), List.get(&2, U32, dr, kk),
        List.get(&2, U32, dp, Nat.add(Nat.add(ll, cc), kk)), get_take(dr, tt, kk, hk),
        M2.get_drop(dp, Nat.add(ll, cc), kk))))

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
  M4.le_add_l(ms, cc, ln, M4.le_cancel(sw, Nat.add(ms, cc), ln, M1.le_rw_r(Nat.add(sw, Nat.add(ms, cc)), Nat.add(ln,
      sw),
    Nat.add(sw, ln), M1.ras.add_comm(ln, sw), M1.le_rw_l(Nat.add(Nat.add(sw, ms), cc), Nat.add(sw, Nat.add(ms, cc)),
      Nat.add(ln, sw), M1.ras.add_assoc(sw, ms, cc), hs))))

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
  M2.drop_le(sp, sw, Nat.add(ms, cc), sw, M1.le_rw_l(Nat.add(Nat.add(sw, ms), cc), Nat.add(sw, Nat.add(ms, cc)),
    Nat.add(List.length(&2, U32, sp), sw), M1.ras.add_assoc(sw, ms, cc), hs))

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
      +hrow = {M1.le_rw_l(dw, Nat.add(ll, Nat.add(cc, tt)), List.length(&2, U32, dp),
        Equal.sym(Nat, Nat.add(ll, Nat.add(cc, tt)), dw, e_row),
        M5.le_add_r(dw, Nat.mul(pp, dw), List.length(&2, U32, dp), hd)) :
        {Nat.is_le(Nat.add(ll, Nat.add(cc, tt)), List.length(&2, U32, dp)) == True{} : Bool}}
      Equal.trans(Nat, List.length(&2, U32, List.append(&2, U32, row, rest)),
        Nat.add(List.length(&2, U32, row), List.length(&2, U32, rest)), Nat.add(dw, Nat.mul(pp, dw)),
        M2.len_append(row, rest),
        Equal.trans(Nat, Nat.add(List.length(&2, U32, row), List.length(&2, U32, rest)),
          Nat.add(dw, List.length(&2, U32, rest)), Nat.add(dw, Nat.mul(pp, dw)),
          Equal.cong(Nat, Nat, nn => Nat.add(nn, List.length(&2, U32, rest)), List.length(&2, U32, row), dw,
            Equal.trans(Nat, List.length(&2, U32, row), Nat.add(ll, Nat.add(cc, tt)), dw,
              blit.row_len(dp, sp, ll, cc, tt, hrow, blit.src_head(pp, sp, sw, cc, hs)), e_row)),
          Equal.cong(Nat, Nat, nn => Nat.add(dw, nn), List.length(&2, U32, rest), Nat.mul(pp, dw),
            blit.rows_len(pp, List.drop(&2, U32, dp, dw), List.drop(&2, U32, sp, sw), ll, cc, tt, dw, sw, e_row,
              drop_le0(dp, dw, Nat.mul(pp, dw), hd), blit.src_next(pp, sp, sw, cc, hs)))))

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
        M1.false_true(Equal.trans(Bool, False{}, Nat.is_lt(_jj, 0n), True{}, M1.lt_zero_false(_jj), hj)))
    case 1n+(+pp) 0n:
      +row = Img.blit.row(dp, sp, ll, cc, tt)
      +rest = Img.blit.rows(pp, List.drop(&2, U32, dp, dw), List.drop(&2, U32, sp, sw), ll, cc, tt, dw, sw)
      +hrow = {M1.le_rw_l(dw, Nat.add(ll, Nat.add(cc, tt)), List.length(&2, U32, dp),
        Equal.sym(Nat, Nat.add(ll, Nat.add(cc, tt)), dw, e_row),
        M5.le_add_r(dw, Nat.mul(pp, dw), List.length(&2, U32, dp), hd)) :
        {Nat.is_le(Nat.add(ll, Nat.add(cc, tt)), List.length(&2, U32, dp)) == True{} : Bool}}
      +el = {Equal.trans(Nat, List.length(&2, U32, row), Nat.add(ll, Nat.add(cc, tt)), dw,
        blit.row_len(dp, sp, ll, cc, tt, hrow, blit.src_head(pp, sp, sw, cc, hs)), e_row) :
        {List.length(&2, U32, row) == dw : Nat}}
      Equal.trans(Maybe<&2, U32>, List.get(&2, U32, List.append(&2, U32, row, rest), ii), List.get(&2, U32, row, ii),
        List.get(&2, U32, Img.blit.row(List.drop(&2, U32, dp, 0n), List.drop(&2, U32, sp, 0n), ll, cc, tt), ii),
        get_append_lt(row, ii, rest, M1.lt_rw_r(ii, dw, List.length(&2, U32, row), Equal.sym(Nat, List.length(&2,
          U32, row),
          dw, el), hi)),
        Equal.trans(Maybe<&2, U32>, List.get(&2, U32, row, ii),
          List.get(&2, U32, Img.blit.row(List.drop(&2, U32, dp, 0n), sp, ll, cc, tt), ii),
          List.get(&2, U32, Img.blit.row(List.drop(&2, U32, dp, 0n), List.drop(&2, U32, sp, 0n), ll, cc, tt), ii),
          Equal.cong(List<&2, U32>, Maybe<&2, U32>, xs => List.get(&2, U32, Img.blit.row(xs, sp, ll, cc, tt), ii), dp,
            List.drop(&2, U32, dp, 0n), Equal.sym(List<&2, U32>, List.drop(&2, U32, dp, 0n), dp, drop_zero(dp))),
          Equal.cong(List<&2, U32>, Maybe<&2, U32>,
            xs => List.get(&2, U32, Img.blit.row(List.drop(&2, U32, dp, 0n), xs, ll, cc, tt), ii), sp,
            List.drop(&2, U32, sp, 0n), Equal.sym(List<&2, U32>, List.drop(&2, U32, sp, 0n), sp, drop_zero(sp)))))
    case 1n+(+pp) 1n+(+qq):
      +row = Img.blit.row(dp, sp, ll, cc, tt)
      +d1 = List.drop(&2, U32, dp, dw)
      +s1 = List.drop(&2, U32, sp, sw)
      +rest = Img.blit.rows(pp, d1, s1, ll, cc, tt, dw, sw)
      +mq = Nat.mul(qq, dw)
      +ms = Nat.mul(qq, sw)
      +hrow = {M1.le_rw_l(dw, Nat.add(ll, Nat.add(cc, tt)), List.length(&2, U32, dp),
        Equal.sym(Nat, Nat.add(ll, Nat.add(cc, tt)), dw, e_row),
        M5.le_add_r(dw, Nat.mul(pp, dw), List.length(&2, U32, dp), hd)) :
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
            Nat.add(List.length(&2, U32, row), Nat.add(mq, ii)), M1.ras.add_assoc(dw, mq, ii),
            Equal.cong(Nat, Nat, nn => Nat.add(nn, Nat.add(mq, ii)), dw, List.length(&2, U32, row),
              Equal.sym(Nat, List.length(&2, U32, row), dw, el)))),
        Equal.trans(Maybe<&2, U32>, List.get(&2, U32, both, Nat.add(List.length(&2, U32, row), Nat.add(mq, ii))),
          List.get(&2, U32, rest, Nat.add(mq, ii)),
          List.get(&2, U32, Img.blit.row(List.drop(&2, U32, dp, Nat.add(dw, mq)), List.drop(&2, U32, sp, Nat.add(sw,
            ms)),
            ll, cc, tt), ii),
          get_append_len(row, Nat.add(mq, ii), rest),
          Equal.trans(Maybe<&2, U32>, List.get(&2, U32, rest, Nat.add(mq, ii)),
            List.get(&2, U32, Img.blit.row(List.drop(&2, U32, d1, mq), List.drop(&2, U32, s1, ms), ll, cc, tt), ii),
            List.get(&2, U32, Img.blit.row(List.drop(&2, U32, dp, Nat.add(dw, mq)),
              List.drop(&2, U32, sp, Nat.add(sw, ms)), ll, cc, tt), ii),
            blit.rows_get(pp, d1, s1, ll, cc, tt, dw, sw, ii, qq, e_row, hi, hj, drop_le0(dp, dw, Nat.mul(pp, dw),
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
                List.drop(&2, U32, d1, mq), List.drop(&2, U32, dp, Nat.add(dw, mq)), drop_drop(dp, dw, mq)),
              Equal.cong(List<&2, U32>, Maybe<&2, U32>,
                xs => List.get(&2, U32, Img.blit.row(List.drop(&2, U32, dp, Nat.add(dw, mq)), xs, ll, cc, tt), ii),
                List.drop(&2, U32, s1, ms), List.drop(&2, U32, sp, Nat.add(sw, ms)), drop_drop(sp, sw, ms))))))

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
  M5.le_add_r(top, Nat.mul(nn, dw), List.length(&2, U32, dp), M1.le_rw_l(span, Nat.add(top, Nat.mul(nn, dw)),
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
  drop_le0(dp, top, Nat.mul(nn, dw), M1.le_rw_l(span, Nat.add(top, Nat.mul(nn, dw)), List.length(&2, U32, dp), e_span,
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
  M2.get_append_take(dp, top, kk, List.append(&2, U32,
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
  +hk = {M1.lt_rw_r(kk, Nat.mul(dw, nn), List.length(&2, U32, rows), Equal.trans(Nat, Nat.mul(dw, nn), Nat.mul(nn, dw),
    List.length(&2, U32, rows), M1.mul_comm(dw, nn), Equal.sym(Nat, List.length(&2, U32, rows), Nat.mul(nn, dw), e_rl)),
    M3.index_lt(ii, jj, dw, nn, hi, hj)) : {Nat.is_lt(kk, List.length(&2, U32, rows)) == True{} : Bool}}
  Equal.trans(Maybe<&2, U32>, List.get(&2, U32, bj.J(dp, sp, top, span, nn, ll, cc, tt, dw, sw), Nat.add(top, kk)),
    List.get(&2, U32, List.append(&2, U32, rows, List.drop(&2, U32, dp, span)), kk),
    List.get(&2, U32, Img.blit.row(List.drop(&2, U32, dp, Nat.add(top, Nat.mul(jj, dw))), srow, ll, cc, tt), ii),
    M2.get_append_skip(dp, top, kk, List.append(&2, U32, rows, List.drop(&2, U32, dp, span)),
      bj.htop(dp, top, span, nn, dw, e_span, h_len)),
    Equal.trans(Maybe<&2, U32>, List.get(&2, U32, List.append(&2, U32, rows, List.drop(&2, U32, dp, span)), kk),
      List.get(&2, U32, rows, kk),
      List.get(&2, U32, Img.blit.row(List.drop(&2, U32, dp, Nat.add(top, Nat.mul(jj, dw))), srow, ll, cc, tt), ii),
      get_append_lt(rows, kk, List.drop(&2, U32, dp, span), hk),
      Equal.trans(Maybe<&2, U32>, List.get(&2, U32, rows, kk),
        List.get(&2, U32, Img.blit.row(List.drop(&2, U32, dt, Nat.mul(jj, dw)), srow, ll, cc, tt), ii),
        List.get(&2, U32, Img.blit.row(List.drop(&2, U32, dp, Nat.add(top, Nat.mul(jj, dw))), srow, ll, cc, tt), ii),
        blit.rows_get(nn, dt, sp, ll, cc, tt, dw, sw, ii, jj, e_row, hi, hj, bj.hd(dp, top, span, nn, dw, e_span,
          h_len),
          hs),
        Equal.cong(List<&2, U32>, Maybe<&2, U32>, xs => List.get(&2, U32, Img.blit.row(xs, srow, ll, cc, tt), ii),
          List.drop(&2, U32, dt, Nat.mul(jj, dw)), List.drop(&2, U32, dp, Nat.add(top, Nat.mul(jj, dw))),
          drop_drop(dp, top, Nat.mul(jj, dw))))))

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
      Nat.add(top, Nat.add(List.length(&2, U32, rows), mm)), M1.ras.add_assoc(top, Nat.mul(nn, dw), mm),
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
      M2.get_append_skip(dp, top, Nat.add(List.length(&2, U32, rows), mm), List.append(&2, U32, rows, low),
        bj.htop(dp, top, span, nn, dw, e_span, h_len)),
      Equal.trans(Maybe<&2, U32>, List.get(&2, U32, List.append(&2, U32, rows, low), Nat.add(List.length(&2, U32,
        rows), mm)),
        List.get(&2, U32, low, mm), List.get(&2, U32, dp, Nat.add(span, mm)),
        get_append_len(rows, mm, low), M2.get_drop(dp, span, mm))))

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
    M2.len_append(hd, List.append(&2, U32, rows, low)),
    Equal.trans(Nat, Nat.add(List.length(&2, U32, hd), List.length(&2, U32, List.append(&2, U32, rows, low))),
      Nat.add(top, Nat.add(Nat.mul(nn, dw), nl)), List.length(&2, U32, dp),
      Equal.trans(Nat, Nat.add(List.length(&2, U32, hd), List.length(&2, U32, List.append(&2, U32, rows, low))),
        Nat.add(top, List.length(&2, U32, List.append(&2, U32, rows, low))), Nat.add(top, Nat.add(Nat.mul(nn, dw), nl)),
        Equal.cong(Nat, Nat, xx => Nat.add(xx, List.length(&2, U32, List.append(&2, U32, rows, low))),
          List.length(&2, U32, hd), top, M2.len_take(dp, top, bj.htop(dp, top, span, nn, dw, e_span, h_len))),
        Equal.cong(Nat, Nat, xx => Nat.add(top, xx), List.length(&2, U32, List.append(&2, U32, rows, low)),
          Nat.add(Nat.mul(nn, dw), nl), Equal.trans(Nat, List.length(&2, U32, List.append(&2, U32, rows, low)),
            Nat.add(List.length(&2, U32, rows), nl), Nat.add(Nat.mul(nn, dw), nl), M2.len_append(rows, low),
            Equal.cong(Nat, Nat, xx => Nat.add(xx, nl), List.length(&2, U32, rows), Nat.mul(nn, dw), e_rl)))),
      Equal.trans(Nat, Nat.add(top, Nat.add(Nat.mul(nn, dw), nl)), Nat.add(span, nl), List.length(&2, U32, dp),
        Equal.trans(Nat, Nat.add(top, Nat.add(Nat.mul(nn, dw), nl)), Nat.add(Nat.add(top, Nat.mul(nn, dw)), nl),
          Nat.add(span, nl), Equal.sym(Nat, Nat.add(Nat.add(top, Nat.mul(nn, dw)), nl),
            Nat.add(top, Nat.add(Nat.mul(nn, dw), nl)), M1.ras.add_assoc(top, Nat.mul(nn, dw), nl)),
          Equal.cong(Nat, Nat, xx => Nat.add(xx, nl), Nat.add(top, Nat.mul(nn, dw)), span,
            Equal.sym(Nat, span, Nat.add(top, Nat.mul(nn, dw)), e_span))),
        len_drop_add(dp, span, h_len))))

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

# where the pasted rows start: y * dw, which the code reaches a row at a time
def bl.top(+oy: U32, +dw: U32) -> Nat:
  Nat.mul(U32.to_nat(oy), U32.to_nat(dw))

# where the pasted rows end: (y + rows) * dw
def bl.span(+sh: U32, +dh: U32, +oy: U32, +dw: U32) -> Nat:
  Nat.mul(Nat.add(U32.to_nat(oy), U32.to_nat(Img.u.min(sh, (dh - oy : U32)))), U32.to_nat(dw))

# the left columns are min(x, dw)
def bl.eL(+ox: U32, +dw: U32) -> {bl.Lc(ox, dw) == Nat.min(U32.to_nat(ox), U32.to_nat(dw)) : Nat}:
  M2.ras.umin(ox, dw)

# the left columns fit in a row
def bl.hL(+ox: U32, +dw: U32) -> {Nat.is_le(bl.Lc(ox, dw), U32.to_nat(dw)) == True{} : Bool}:
  M1.le_rw_l(Nat.min(U32.to_nat(ox), U32.to_nat(dw)), bl.Lc(ox, dw), U32.to_nat(dw),
    Equal.sym(Nat, bl.Lc(ox, dw), Nat.min(U32.to_nat(ox), U32.to_nat(dw)), bl.eL(ox, dw)),
    M2.min_le_r(U32.to_nat(ox), U32.to_nat(dw)))

# the room is dw - left
def bl.eRm(+ox: U32, +dw: U32) -> {bl.Rm(ox, dw) == Nat.sub(U32.to_nat(dw), bl.Lc(ox, dw)) : Nat}:
  M4.ras.u32_sub_nat(dw, Img.u.min(ox, dw), bl.hL(ox, dw))

# the pasted columns are min(sw, room)
def bl.eC(+sw: U32, +ox: U32, +dw: U32) -> {bl.Cc(sw, ox, dw) == Nat.min(U32.to_nat(sw), bl.Rm(ox, dw)) : Nat}:
  M2.ras.umin(sw, (dw - Img.u.min(ox, dw) : U32))

# the pasted columns fit in the room
def bl.hC(+sw: U32, +ox: U32, +dw: U32) -> {Nat.is_le(bl.Cc(sw, ox, dw), bl.Rm(ox, dw)) == True{} : Bool}:
  M1.le_rw_l(Nat.min(U32.to_nat(sw), bl.Rm(ox, dw)), bl.Cc(sw, ox, dw), bl.Rm(ox, dw),
    Equal.sym(Nat, bl.Cc(sw, ox, dw), Nat.min(U32.to_nat(sw), bl.Rm(ox, dw)), bl.eC(sw, ox, dw)),
    M2.min_le_r(U32.to_nat(sw), bl.Rm(ox, dw)))

# the pasted columns are at most sw
def bl.hCs(+sw: U32, +ox: U32, +dw: U32) -> {Nat.is_le(bl.Cc(sw, ox, dw), U32.to_nat(sw)) == True{} : Bool}:
  M1.le_rw_l(Nat.min(U32.to_nat(sw), bl.Rm(ox, dw)), bl.Cc(sw, ox, dw), U32.to_nat(sw),
    Equal.sym(Nat, bl.Cc(sw, ox, dw), Nat.min(U32.to_nat(sw), bl.Rm(ox, dw)), bl.eC(sw, ox, dw)),
    min_le_l(U32.to_nat(sw), bl.Rm(ox, dw)))

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
  +et = {M4.ras.u32_sub_nat((dw - Img.u.min(ox, dw) : U32), Img.u.min(sw, (dw - Img.u.min(ox, dw) : U32)), bl.hC(sw, ox,
    dw)) :
    {tc == Nat.sub(rm, cc) : Nat}}
  +e_ct = {Equal.trans(Nat, Nat.add(cc, tc), Nat.add(cc, Nat.sub(rm, cc)), rm,
    Equal.cong(Nat, Nat, nn => Nat.add(cc, nn), tc, Nat.sub(rm, cc), et), M4.add_sub(cc, rm, bl.hC(sw, ox, dw))) :
    {Nat.add(cc, tc) == rm : Nat}}
  Equal.trans(Nat, Nat.add(lc, Nat.add(cc, tc)), Nat.add(lc, rm), U32.to_nat(dw),
    Equal.cong(Nat, Nat, nn => Nat.add(lc, nn), Nat.add(cc, tc), rm, e_ct),
    Equal.trans(Nat, Nat.add(lc, rm), Nat.add(lc, Nat.sub(U32.to_nat(dw), lc)), U32.to_nat(dw),
      Equal.cong(Nat, Nat, nn => Nat.add(lc, nn), rm, Nat.sub(U32.to_nat(dw), lc), bl.eRm(ox, dw)),
      M4.add_sub(lc, U32.to_nat(dw), bl.hL(ox, dw))))

# the pasted rows are min(sh, dh - y), when y < dh
def bl.eRw(
  +sh: U32,
  +dh: U32,
  +oy: U32,
  hy: {Nat.is_lt(U32.to_nat(oy), U32.to_nat(dh)) == True{} : Bool}
) -> {bl.Rw(sh, dh, oy) == Nat.min(U32.to_nat(sh), Nat.sub(U32.to_nat(dh), U32.to_nat(oy))) : Nat}:
  Equal.trans(Nat, bl.Rw(sh, dh, oy), Nat.min(U32.to_nat(sh), U32.to_nat((dh - oy : U32))),
    Nat.min(U32.to_nat(sh), Nat.sub(U32.to_nat(dh), U32.to_nat(oy))), M2.ras.umin(sh, (dh - oy : U32)),
    Equal.cong(Nat, Nat, nn => Nat.min(U32.to_nat(sh), nn), U32.to_nat((dh - oy : U32)),
      Nat.sub(U32.to_nat(dh), U32.to_nat(oy)), M4.ras.u32_sub_nat(dh, oy, M1.lt_le(U32.to_nat(oy), U32.to_nat(dh),
          hy))))

# the pasted rows are at most sh
def bl.hRs(+sh: U32, +dh: U32, +oy: U32) -> {Nat.is_le(bl.Rw(sh, dh, oy), U32.to_nat(sh)) == True{} : Bool}:
  M1.le_rw_l(Nat.min(U32.to_nat(sh), U32.to_nat((dh - oy : U32))), bl.Rw(sh, dh, oy), U32.to_nat(sh),
    Equal.sym(Nat, bl.Rw(sh, dh, oy), Nat.min(U32.to_nat(sh), U32.to_nat((dh - oy : U32))), M2.ras.umin(sh,
      (dh - oy : U32))),
    min_le_l(U32.to_nat(sh), U32.to_nat((dh - oy : U32))))

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
  M1.le_rw_r(Nat.add(yn, bl.Rw(sh, dh, oy)), Nat.add(yn, dd), dn, M4.add_sub(yn, dn, M1.lt_le(yn, dn, hy)),
    M1.le_add_mono(yn, bl.Rw(sh, dh, oy), dd, M1.le_rw_l(Nat.min(U32.to_nat(sh), dd), bl.Rw(sh, dh, oy), dd,
      Equal.sym(Nat, bl.Rw(sh, dh, oy), Nat.min(U32.to_nat(sh), dd), bl.eRw(sh, dh, oy, hy)),
      M2.min_le_r(U32.to_nat(sh), dd))))

# a row count at most dh times dw is at most the area
def bl.below_area(
  +an: Nat,
  +dw: U32,
  +dh: U32,
  hh: {Nat.is_le(an, U32.to_nat(dh)) == True{} : Bool}
) -> {Nat.is_le(Nat.mul(an, U32.to_nat(dw)), Nat.mul(U32.to_nat(dw), U32.to_nat(dh))) == True{} : Bool}:
  M1.le_rw_r(Nat.mul(an, U32.to_nat(dw)), Nat.mul(U32.to_nat(dh), U32.to_nat(dw)), Nat.mul(U32.to_nat(dw),
    U32.to_nat(dh)),
    M1.mul_comm(U32.to_nat(dh), U32.to_nat(dw)), M5.le_mul_mono(an, U32.to_nat(dh), U32.to_nat(dw), hh))

# the pasted rows start at y * dw
def bl.e_top(
  +oy: U32,
  +dw: U32
) -> {bl.top(oy, dw) == Nat.mul(U32.to_nat(oy), U32.to_nat(dw)) : Nat}:
  {==}

# the pasted rows end at (y + rows) * dw
def bl.e_spanv(
  +sh: U32,
  +oy: U32,
  +dw: U32,
  +dh: U32
) -> {bl.span(sh, dh, oy, dw) == Nat.mul(Nat.add(U32.to_nat(oy), bl.Rw(sh, dh, oy)), U32.to_nat(dw)) : Nat}:
  {==}

# the pasted rows end rows * dw after they start
def bl.e_span(
  +sh: U32,
  +oy: U32,
  +dw: U32,
  +dh: U32
) -> {bl.span(sh, dh, oy, dw) == Nat.add(bl.top(oy, dw), Nat.mul(bl.Rw(sh, dh, oy), U32.to_nat(dw))) : Nat}:
  +yn = U32.to_nat(oy)
  +wn = U32.to_nat(dw)
  +rn = bl.Rw(sh, dh, oy)
  Equal.trans(Nat, bl.span(sh, dh, oy, dw), Nat.mul(Nat.add(yn, rn), wn), Nat.add(bl.top(oy, dw), Nat.mul(rn, wn)),
    bl.e_spanv(sh, oy, dw, dh),
    Equal.trans(Nat, Nat.mul(Nat.add(yn, rn), wn), Nat.add(Nat.mul(yn, wn), Nat.mul(rn, wn)),
      Nat.add(bl.top(oy, dw), Nat.mul(rn, wn)), M1.mul_add(yn, rn, wn),
      Equal.cong(Nat, Nat, nn => Nat.add(nn, Nat.mul(rn, wn)), Nat.mul(yn, wn), bl.top(oy, dw),
        Equal.sym(Nat, bl.top(oy, dw), Nat.mul(yn, wn), bl.e_top(oy, dw)))))

# the pasted rows end inside dst's samples
def bl.h_len(
  +dp: List<&2, U32>,
  +sh: U32,
  +oy: U32,
  +dw: U32,
  +dh: U32,
  h_dst: {D2.wf(Img.Raster{dw, dh, dp}) == True{} : Bool},
  +hy: {Nat.is_lt(U32.to_nat(oy), U32.to_nat(dh)) == True{} : Bool}
) -> {Nat.is_le(bl.span(sh, dh, oy, dw), List.length(&2, U32, dp)) == True{} : Bool}:
  +wh = Nat.mul(U32.to_nat(dw), U32.to_nat(dh))
  M1.le_rw_r(bl.span(sh, dh, oy, dw), wh, List.length(&2, U32, dp),
    Equal.sym(Nat, List.length(&2, U32, dp), wh, M1.ras.nat_eq_true(List.length(&2, U32, dp), wh, h_dst)),
    bl.below_area(Nat.add(U32.to_nat(oy), bl.Rw(sh, dh, oy)), dw, dh, bl.hyr(sh, dh, oy, hy)))

# blit.join walks dst a row at a time: it is bj.J at the row-major offsets
def bl.join(
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
  +yn = U32.to_nat(oy)
  +wn = U32.to_nat(dw)
  +sn = U32.to_nat(sw)
  +rn = bl.Rw(sh, dh, oy)
  +lc = bl.Lc(ox, dw)
  +cc = bl.Cc(sw, ox, dw)
  +tc = bl.Tc(sw, ox, dw)
  +top = bl.top(oy, dw)
  +span = bl.span(sh, dh, oy, dw)
  +ta = Img.take.rows(yn, dp, wn)
  +tb = List.take(&2, U32, dp, top)
  +ra = Img.skip.rows(yn, dp, wn)
  +rb = List.drop(&2, U32, dp, top)
  +ba = Img.skip.rows(rn, ra, wn)
  +bb = List.drop(&2, U32, dp, span)
  +e_r = {M6.skip_drop(yn, dp, wn) : {ra == rb : List<&2, U32>}}
  +e_b = {Equal.trans(List<&2, U32>, ba, List.drop(&2, U32, ra, Nat.mul(rn, wn)), bb, M6.skip_drop(rn, ra, wn),
    Equal.trans(List<&2, U32>, List.drop(&2, U32, ra, Nat.mul(rn, wn)), List.drop(&2, U32, rb, Nat.mul(rn, wn)), bb,
      Equal.cong(List<&2, U32>, List<&2, U32>, xs => List.drop(&2, U32, xs, Nat.mul(rn, wn)), ra, rb, e_r),
      Equal.trans(List<&2, U32>, List.drop(&2, U32, rb, Nat.mul(rn, wn)),
        List.drop(&2, U32, dp, Nat.add(top, Nat.mul(rn, wn))), bb, M6.drop_drop(dp, top, Nat.mul(rn, wn)),
        Equal.cong(Nat, List<&2, U32>, kk => List.drop(&2, U32, dp, kk), Nat.add(top, Nat.mul(rn, wn)), span,
          Equal.sym(Nat, span, Nat.add(top, Nat.mul(rn, wn)), M1.mul_add(yn, rn, wn)))))) : {ba == bb : List<&2, U32>}}
  Equal.trans(List<&2, U32>,
    List.append(&2, U32, ta, List.append(&2, U32, Img.blit.rows(rn, ra, sp, lc, cc, tc, wn, sn), ba)),
    List.append(&2, U32, tb, List.append(&2, U32, Img.blit.rows(rn, ra, sp, lc, cc, tc, wn, sn), ba)),
    bj.J(dp, sp, top, span, rn, lc, cc, tc, wn, sn),
    Equal.cong(List<&2, U32>, List<&2, U32>, xs => List.append(&2, U32, xs, List.append(&2, U32, Img.blit.rows(rn, ra,
      sp, lc, cc, tc, wn, sn), ba)), ta, tb, M6.take_rows(yn, dp, wn)),
    Equal.trans(List<&2, U32>,
      List.append(&2, U32, tb, List.append(&2, U32, Img.blit.rows(rn, ra, sp, lc, cc, tc, wn, sn), ba)),
      List.append(&2, U32, tb, List.append(&2, U32, Img.blit.rows(rn, rb, sp, lc, cc, tc, wn, sn), ba)),
      bj.J(dp, sp, top, span, rn, lc, cc, tc, wn, sn),
      Equal.cong(List<&2, U32>, List<&2, U32>, xs => List.append(&2, U32, tb, List.append(&2, U32, Img.blit.rows(rn,
        xs, sp, lc, cc, tc, wn, sn), ba)), ra, rb, e_r),
      Equal.cong(List<&2, U32>, List<&2, U32>, xs => List.append(&2, U32, tb, List.append(&2, U32, Img.blit.rows(rn,
        rb, sp, lc, cc, tc, wn, sn), xs)), ba, bb, e_b)))

# the source holds the pasted rows
def bl.hs(
  +sp: List<&2, U32>,
  +sw: U32,
  +sh: U32,
  +ox: U32,
  +oy: U32,
  +dw: U32,
  +dh: U32,
  h_src: {D2.wf(Img.Raster{sw, sh, sp}) == True{} : Bool}
) -> {Nat.is_le(Nat.add(Nat.mul(bl.Rw(sh, dh, oy), U32.to_nat(sw)), bl.Cc(sw, ox, dw)),
  Nat.add(List.length(&2, U32, sp), U32.to_nat(sw))) == True{} : Bool}:
  +sn = U32.to_nat(sw)
  +hn = U32.to_nat(sh)
  +ln = List.length(&2, U32, sp)
  M1.le_add_both(Nat.mul(bl.Rw(sh, dh, oy), sn), ln, bl.Cc(sw, ox, dw), sn,
    M1.le_rw_r(Nat.mul(bl.Rw(sh, dh, oy), sn), Nat.mul(sn, hn), ln,
      Equal.sym(Nat, ln, Nat.mul(sn, hn), M1.ras.nat_eq_true(ln, Nat.mul(sn, hn), h_src)),
      M1.le_rw_r(Nat.mul(bl.Rw(sh, dh, oy), sn), Nat.mul(hn, sn), Nat.mul(sn, hn), M1.mul_comm(hn, sn),
        M5.le_mul_mono(bl.Rw(sh, dh, oy), hn, sn, bl.hRs(sh, dh, oy)))),
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
    M1.ras.add_assoc(top, mj, dw), Equal.cong(Nat, Nat, xx => Nat.add(top, xx), Nat.add(mj, dw), Nat.add(dw, mj),
      M1.ras.add_comm(mj, dw))) : {Nat.add(Nat.add(top, mj), dw) == Nat.add(top, Nat.add(dw, mj)) : Nat}}
  drop_le0(dp, Nat.add(top, mj), dw, M1.le_rw_l(Nat.add(top, Nat.add(dw, mj)), Nat.add(Nat.add(top, mj), dw),
    List.length(&2, U32, dp), Equal.sym(Nat, Nat.add(Nat.add(top, mj), dw), Nat.add(top, Nat.add(dw, mj)), e1),
    M1.le_trans(Nat.add(top, Nat.add(dw, mj)), span, List.length(&2, U32, dp),
      M1.le_rw_r(Nat.add(top, Nat.add(dw, mj)), Nat.add(top, Nat.mul(nn, dw)), span,
        Equal.sym(Nat, span, Nat.add(top, Nat.mul(nn, dw)), e_span),
        M1.le_add_mono(top, Nat.mul(1n+jj, dw), Nat.mul(nn, dw), M5.le_mul_mono(1n+jj, nn, dw,
          Equal.trans(Bool, Nat.is_le(1n+jj, nn), Nat.is_lt(jj, nn), True{},
            Equal.sym(Bool, Nat.is_lt(jj, nn), Nat.is_le(1n+jj, nn), M1.lt_le_succ(jj, nn)), hj)))),
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
  +h1 = {M1.le_trans(Nat.add(Nat.mul(1n+jj, sw), cc), Nat.add(Nat.mul(nn, sw), cc), Nat.add(ln, sw),
    M1.le_add_both(Nat.mul(1n+jj, sw), Nat.mul(nn, sw), cc, cc, M5.le_mul_mono(1n+jj, nn, sw,
      Equal.trans(Bool, Nat.is_le(1n+jj, nn), Nat.is_lt(jj, nn), True{},
        Equal.sym(Bool, Nat.is_lt(jj, nn), Nat.is_le(1n+jj, nn), M1.lt_le_succ(jj, nn)), hj)), M1.le_refl(cc)), hs) :
    {Nat.is_le(Nat.add(Nat.add(sw, mj), cc), Nat.add(ln, sw)) == True{} : Bool}}
  drop_le0(sp, mj, cc, M4.le_cancel(sw, Nat.add(mj, cc), ln, M1.le_rw_r(Nat.add(sw, Nat.add(mj, cc)), Nat.add(ln, sw),
    Nat.add(sw, ln), M1.ras.add_comm(ln, sw), M1.le_rw_l(Nat.add(Nat.add(sw, mj), cc), Nat.add(sw, Nat.add(mj, cc)),
      Nat.add(ln, sw), M1.ras.add_assoc(sw, mj, cc), h1))))

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
      Empty.absurd({False{} == True{} : Bool}, M1.false_true(ha))

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
      Equal.sym(Nat, Nat.add(yn, jp), jj, M4.add_sub(yn, jj, h_le))),
    Equal.trans(Nat, Nat.add(Nat.mul(Nat.add(yn, jp), wn), ii), Nat.add(Nat.add(Nat.mul(yn, wn), Nat.mul(jp, wn)), ii),
      Nat.add(top, Nat.add(Nat.mul(jp, wn), ii)),
      Equal.cong(Nat, Nat, nn => Nat.add(nn, ii), Nat.mul(Nat.add(yn, jp), wn), Nat.add(Nat.mul(yn, wn), Nat.mul(jp,
        wn)),
        M1.mul_add(yn, jp, wn)),
      Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(yn, wn), Nat.mul(jp, wn)), ii),
        Nat.add(Nat.mul(yn, wn), Nat.add(Nat.mul(jp, wn), ii)), Nat.add(top, Nat.add(Nat.mul(jp, wn), ii)),
        M1.ras.add_assoc(Nat.mul(yn, wn), Nat.mul(jp, wn), ii),
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
  M1.lt_rw_r(Nat.sub(jj, yn), Nat.min(U32.to_nat(sh), dd), bl.Rw(sh, dh, oy),
    Equal.sym(Nat, bl.Rw(sh, dh, oy), Nat.min(U32.to_nat(sh), dd), bl.eRw(sh, dh, oy, hy)),
    lt_min(Nat.sub(jj, yn), U32.to_nat(sh), dd, M4.sub_lt(yn, jj, U32.to_nat(sh), b1, b2),
      M4.sub_lt(yn, jj, dd, b1, M1.lt_rw_r(jj, dn, Nat.add(yn, dd),
        Equal.sym(Nat, Nat.add(yn, dd), dn, M4.add_sub(yn, dn, M1.lt_le(yn, dn, hy))), hj))))

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
  +h_dst: {D2.wf(Img.Raster{dw, dh, dp}) == True{} : Bool},
  h_src: {D2.wf(Img.Raster{sw, sh, sp}) == True{} : Bool},
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
      +jc = Img.blit.join(dp, sp, dw, dh, sw, sh, ox, oy)
      Equal.trans(Bool, Nat.is_eq(List.length(&2, U32, jc), wh), Nat.is_eq(List.length(&2, U32, jn), wh), True{},
        Equal.cong(List<&2, U32>, Bool, xs => Nat.is_eq(List.length(&2, U32, xs), wh), jc, jn, bl.join(dp, sp, dw, dh,
          sw, sh, ox, oy)),
      Equal.trans(Bool, Nat.is_eq(List.length(&2, U32, jn), wh), Nat.is_eq(List.length(&2, U32, dp), wh), True{},
        Equal.cong(Nat, Bool, nn => Nat.is_eq(nn, wh), List.length(&2, U32, jn), List.length(&2, U32, dp),
          bj.len(dp, sp, bl.top(oy, dw), bl.span(sh, dh, oy, dw), bl.Rw(sh, dh, oy), bl.Lc(ox, dw), bl.Cc(sw, ox, dw),
            bl.Tc(sw, ox, dw), U32.to_nat(dw), U32.to_nat(sw), bl.e_row(sw, ox, dw),
            bl.e_span(sh, oy, dw, dh), bl.h_len(dp, sh, oy, dw, dh, h_dst, ey),
            bl.hs(sp, sw, sh, ox, oy, dw, dh, h_src))),
        h_dst))

def Laws.blit_wf(dst, src, xx, yy, h_dst, h_src):
  match dst src:
    case Img.Raster{+dw, +dh, +dp} Img.Raster{+sw, +sh, +sp}:
      +wh = Nat.mul(U32.to_nat(dw), U32.to_nat(dh))
      Equal.trans(Bool, Nat.is_eq(List.length(&2, U32, Img.blit.y(U32.is_lt(yy, dh), dp, sp, dw, dh, sw, sh, xx,
        yy)), wh),
        Nat.is_eq(List.length(&2, U32, Img.blit.y(Nat.is_lt(U32.to_nat(yy), U32.to_nat(dh)), dp, sp, dw, dh, sw, sh, xx,
          yy)), wh), True{},
        Equal.cong(Bool, Bool, bb => Nat.is_eq(List.length(&2, U32, Img.blit.y(bb, dp, sp, dw, dh, sw, sh, xx, yy)),
          wh),
          U32.is_lt(yy, dh), Nat.is_lt(U32.to_nat(yy), U32.to_nat(dh)), M5.u32_lt(yy, dh)),
        bl.wf_y(Nat.is_lt(U32.to_nat(yy), U32.to_nat(dh)), dp, sp, dw, dh, sw, sh, xx, yy, h_dst,
          h_src, {==}))

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
  +h_dst: {D2.wf(Img.Raster{dw, dh, dp}) == True{} : Bool},
  +h_src: {D2.wf(Img.Raster{sw, sh, sp}) == True{} : Bool},
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
  +e_span = {bl.e_span(sh, oy, dw, dh) : {span == Nat.add(top, Nat.mul(rw, wn)) : Nat}}
  +h_len = {bl.h_len(dp, sh, oy, dw, dh, h_dst, hy) :
    {Nat.is_le(span, List.length(&2, U32, dp)) == True{} : Bool}}
  +hs = {bl.hs(sp, sw, sh, ox, oy, dw, dh, h_src) :
    {Nat.is_le(Nat.add(Nat.mul(rw, sn), cc), Nat.add(List.length(&2, U32, sp), sn)) == True{} : Bool}}
  +hjp = {bl.hjp(sh, dh, oy, jj, hy, b1, b2, hj) : {Nat.is_lt(jp, rw) == True{} : Bool}}
  +e1 = {bl.e_band(yn, jj, wn, ii, top, bl.e_top(oy, dw), b1) :
    {Nat.add(Nat.mul(jj, wn), ii) == Nat.add(top, Nat.add(Nat.mul(jp, wn), ii)) : Nat}}
  +hxw = {M1.lt_le(xn, wn, M1.le_lt_trans(xn, ii, wn, a1, hi)) : {Nat.is_le(xn, wn) == True{} : Bool}}
  +elx = {Equal.trans(Nat, lc, Nat.min(xn, wn), xn, bl.eL(ox, dw), M2.min_of_le(xn, wn, hxw)) : {lc == xn : Nat}}
  +eii = {Equal.trans(Nat, ii, Nat.add(xn, ip), Nat.add(lc, ip), Equal.sym(Nat, Nat.add(xn, ip), ii, M4.add_sub(xn,
    ii, a1)),
    Equal.cong(Nat, Nat, nn => Nat.add(nn, ip), xn, lc, Equal.sym(Nat, lc, xn, elx))) : {ii == Nat.add(lc, ip) : Nat}}
  +dx = Nat.sub(wn, xn)
  +ecd = {Equal.trans(Nat, cc, Nat.min(sn, bl.Rm(ox, dw)), Nat.min(sn, dx), bl.eC(sw, ox, dw),
    Equal.cong(Nat, Nat, nn => Nat.min(sn, nn), bl.Rm(ox, dw), dx, Equal.trans(Nat, bl.Rm(ox, dw), Nat.sub(wn, lc), dx,
      bl.eRm(ox, dw), Equal.cong(Nat, Nat, nn => Nat.sub(wn, nn), lc, xn, elx)))) : {cc == Nat.min(sn, dx) : Nat}}
  +hk = {M1.lt_rw_r(ip, Nat.min(sn, dx), cc, Equal.sym(Nat, cc, Nat.min(sn, dx), ecd), lt_min(ip, sn, dx,
    M4.sub_lt(xn, ii, sn, a1, a2), M4.sub_lt(xn, ii, dx, a1, M1.lt_rw_r(ii, wn, Nat.add(xn, dx),
      Equal.sym(Nat, Nat.add(xn, dx), wn, M4.add_sub(xn, wn, hxw)), hi)))) : {Nat.is_lt(ip, cc) == True{} : Bool}}
  +hl = {M1.le_trans(lc, wn, List.length(&2, U32, drow), bl.hL(ox, dw),
    bl.row_room(dp, top, span, rw, wn, jp, hjp, e_span, h_len)) : {Nat.is_le(lc, List.length(&2, U32, drow)) == True{} :
    Bool}}
  +hc = {bl.src_room(sp, rw, sn, cc, jp, hjp, hs) : {Nat.is_le(cc, List.length(&2, U32, srow)) == True{} : Bool}}
  +jc = Img.blit.join(dp, sp, dw, dh, sw, sh, ox, oy)
  Equal.trans(Maybe<&2, U32>, List.get(&2, U32, jc, Nat.add(Nat.mul(jj, wn), ii)),
    List.get(&2, U32, jn, Nat.add(Nat.mul(jj, wn), ii)), List.get(&2, U32, sp, Nat.add(Nat.mul(jp, sn), ip)),
    Equal.cong(List<&2, U32>, Maybe<&2, U32>, xs => List.get(&2, U32, xs, Nat.add(Nat.mul(jj, wn), ii)), jc, jn,
      bl.join(dp, sp, dw, dh, sw, sh, ox, oy)),
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
          blit.row_mid(drow, srow, lc, cc, tc, ip, hk, hl, hc), M2.get_drop(sp, Nat.mul(jp, sn), ip))))))

def Laws.blit_in(dst, src, xx, yy, h_dst, h_src, ii, jj, hi, hj, h_cov):
  match dst src:
    case Img.Raster{+dw, +dh, +dp} Img.Raster{+sw, +sh, +sp}:
      +xn = U32.to_nat(xx)
      +yn = U32.to_nat(yy)
      +a1b = Nat.is_le(xn, ii)
      +a2b = Nat.is_lt(ii, Nat.add(xn, U32.to_nat(sw)))
      +b1b = Nat.is_le(yn, jj)
      +b2b = Nat.is_lt(jj, Nat.add(yn, U32.to_nat(sh)))
      +cx = {M1.and_left(Bool.and(a1b, a2b), Bool.and(b1b, b2b), h_cov) : {Bool.and(a1b, a2b) == True{} : Bool}}
      +cy = {M1.and_right(Bool.and(a1b, a2b), Bool.and(b1b, b2b), h_cov) : {Bool.and(b1b, b2b) == True{} : Bool}}
      +b1 = {M1.and_left(b1b, b2b, cy) : {b1b == True{} : Bool}}
      +hy = {M1.le_lt_trans(yn, jj, U32.to_nat(dh), b1, hj) : {Nat.is_lt(yn, U32.to_nat(dh)) == True{} : Bool}}
      +kk = Nat.add(Nat.mul(jj, U32.to_nat(dw)), ii)
      Equal.trans(Maybe<&2, U32>, List.get(&2, U32, Img.blit.y(U32.is_lt(yy, dh), dp, sp, dw, dh, sw, sh, xx, yy), kk),
        List.get(&2, U32, Img.blit.y(True{}, dp, sp, dw, dh, sw, sh, xx, yy), kk),
        List.get(&2, U32, sp, Nat.add(Nat.mul(Nat.sub(jj, yn), U32.to_nat(sw)), Nat.sub(ii, xn))),
        Equal.cong(Bool, Maybe<&2, U32>, bb => List.get(&2, U32, Img.blit.y(bb, dp, sp, dw, dh, sw, sh, xx, yy), kk),
          U32.is_lt(yy, dh), True{}, M3.ras.lt(yy, dh, hy)),
        bl.in_go(dp, sp, dw, dh, sw, sh, xx, yy, h_dst, h_src, ii, jj, hi, hj,
          M1.and_left(a1b, a2b, cx), M1.and_right(a1b, a2b, cx), b1, M1.and_right(b1b, b2b, cy), hy))

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
      +hcle = {M3.not_lt_le(ip, cc, eb) : {Nat.is_le(cc, ip) == True{} : Bool}}
      +tp = Nat.sub(ip, cc)
      +eii = {Equal.trans(Nat, ii, Nat.add(ll, ip), Nat.add(ll, Nat.add(cc, tp)),
        Equal.sym(Nat, Nat.add(ll, ip), ii, M4.add_sub(ll, ii, hle)),
        Equal.cong(Nat, Nat, nn => Nat.add(ll, nn), ip, Nat.add(cc, tp), Equal.sym(Nat, Nat.add(cc, tp), ip,
          M4.add_sub(cc, ip, hcle)))) : {ii == Nat.add(ll, Nat.add(cc, tp)) : Nat}}
      +hk = {M4.lt_cancel(cc, tp, tt, M4.lt_cancel(ll, Nat.add(cc, tp), Nat.add(cc, tt), M1.lt_rw_l(ii,
        Nat.add(ll, Nat.add(cc, tp)), Nat.add(ll, Nat.add(cc, tt)), eii, M1.lt_rw_r(ii, dw, Nat.add(ll, Nat.add(cc,
            tt)),
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
            Equal.trans(Nat, Nat.add(Nat.add(ll, cc), tp), Nat.add(ll, Nat.add(cc, tp)), ii, M1.ras.add_assoc(ll, cc,
                tp),
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
        M3.not_lt_le(ii, ll, eb), {==}, notmid)

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
  +h_dst: {D2.wf(Img.Raster{dw, dh, dp}) == True{} : Bool},
  +h_src: {D2.wf(Img.Raster{sw, sh, sp}) == True{} : Bool},
  +ii: Nat,
  +jj: Nat,
  +hi: {Nat.is_lt(ii, U32.to_nat(dw)) == True{} : Bool},
  +h_cov: {D1.covers(ox, oy, Img.Raster{sw, sh, sp}, ii, jj) == False{} : Bool},
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
  +e_span = {bl.e_span(sh, oy, dw, dh) : {span == Nat.add(top, Nat.mul(rw, wn)) : Nat}}
  +h_len = {bl.h_len(dp, sh, oy, dw, dh, h_dst, hy) :
    {Nat.is_le(span, List.length(&2, U32, dp)) == True{} : Bool}}
  +hs = {bl.hs(sp, sw, sh, ox, oy, dw, dh, h_src) :
    {Nat.is_le(Nat.add(Nat.mul(rw, sn), cc), Nat.add(List.length(&2, U32, sp), sn)) == True{} : Bool}}
  +e1 = {bl.e_band(yn, jj, wn, ii, top, bl.e_top(oy, dw), hle) :
    {kk == Nat.add(top, Nat.add(Nat.mul(jp, wn), ii)) : Nat}}
  +hl = {M1.le_trans(lc, wn, List.length(&2, U32, drow), bl.hL(ox, dw),
    bl.row_room(dp, top, span, rw, wn, jp, hjp, e_span, h_len)) : {Nat.is_le(lc, List.length(&2, U32, drow)) == True{} :
    Bool}}
  +hc = {bl.src_room(sp, rw, sn, cc, jp, hjp, hs) : {Nat.is_le(cc, List.length(&2, U32, srow)) == True{} : Bool}}
  +b2 = {M1.lt_rw_l(Nat.add(yn, jp), jj, Nat.add(yn, U32.to_nat(sh)), M4.add_sub(yn, jj, hle),
    M1.lt_add_mono(yn, jp, U32.to_nat(sh), M1.lt_le_trans(jp, rw, U32.to_nat(sh), hjp, bl.hRs(sh, dh, oy)))) :
    {Nat.is_lt(jj, Nat.add(yn, U32.to_nat(sh))) == True{} : Bool}}
  notmid = {+hl2 => +hm =>
    +hlw = {M2.sub_pos(wn, lc, M3.lt_pos(Nat.sub(ii, lc), Nat.sub(wn, lc), M1.lt_rw_r(Nat.sub(ii, lc), bl.Rm(ox, dw),
      Nat.sub(wn, lc), bl.eRm(ox, dw), M1.lt_le_trans(Nat.sub(ii, lc), cc, bl.Rm(ox, dw), hm, bl.hC(sw, ox, dw))))) :
      {Nat.is_lt(lc, wn) == True{} : Bool}}
    +elx = {Equal.trans(Nat, lc, Nat.min(xn, wn), xn, bl.eL(ox, dw), min_lt_r(xn, wn,
      M1.lt_rw_l(lc, Nat.min(xn, wn), wn, bl.eL(ox, dw), hlw))) : {lc == xn : Nat}}
    +a1 = {M1.le_rw_l(lc, xn, ii, elx, hl2) : {Nat.is_le(xn, ii) == True{} : Bool}}
    +a2 = {M1.lt_rw_r(ii, Nat.add(lc, sn), Nat.add(xn, sn), Equal.cong(Nat, Nat, nn => Nat.add(nn, sn), lc, xn, elx),
      M1.lt_rw_l(Nat.add(lc, Nat.sub(ii, lc)), ii, Nat.add(lc, sn), M4.add_sub(lc, ii, hl2),
        M1.lt_add_mono(lc, Nat.sub(ii, lc), sn, M1.lt_le_trans(Nat.sub(ii, lc), cc, sn, hm, bl.hCs(sw, ox, dw))))) :
      {Nat.is_lt(ii, Nat.add(xn, sn)) == True{} : Bool}}
    M1.false_true(Equal.trans(Bool, False{}, D1.covers(ox, oy, Img.Raster{sw, sh, sp}, ii, jj), True{},
      Equal.sym(Bool, D1.covers(ox, oy, Img.Raster{sw, sh, sp}, ii, jj), False{}, h_cov),
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
          List.get(&2, U32, dp, kk), M2.get_drop(dp, doff, ii),
          Equal.cong(Nat, Maybe<&2, U32>, nn => List.get(&2, U32, dp, nn), Nat.add(doff, ii), kk,
            Equal.trans(Nat, Nat.add(doff, ii), Nat.add(top, Nat.add(Nat.mul(jp, wn), ii)), kk,
              M1.ras.add_assoc(top, Nat.mul(jp, wn), ii),
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
  +h_dst: {D2.wf(Img.Raster{dw, dh, dp}) == True{} : Bool},
  +h_src: {D2.wf(Img.Raster{sw, sh, sp}) == True{} : Bool},
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
    Equal.sym(Nat, Nat.add(yn, jp), jj, M4.add_sub(yn, jj, hle)),
    Equal.trans(Nat, Nat.add(yn, jp), Nat.add(yn, Nat.add(rw, dd)), Nat.add(Nat.add(yn, rw), dd),
      Equal.cong(Nat, Nat, nn => Nat.add(yn, nn), jp, Nat.add(rw, dd), Equal.sym(Nat, Nat.add(rw, dd), jp,
        M4.add_sub(rw, jp, hr))),
      Equal.sym(Nat, Nat.add(Nat.add(yn, rw), dd), Nat.add(yn, Nat.add(rw, dd)), M1.ras.add_assoc(yn, rw, dd)))) :
    {jj == Nat.add(Nat.add(yn, rw), dd) : Nat}}
  +ek = {Equal.trans(Nat, kk, Nat.add(Nat.mul(Nat.add(Nat.add(yn, rw), dd), wn), ii), Nat.add(span, mm),
    Equal.cong(Nat, Nat, nn => Nat.add(Nat.mul(nn, wn), ii), jj, Nat.add(Nat.add(yn, rw), dd), ejj),
    Equal.trans(Nat, Nat.add(Nat.mul(Nat.add(Nat.add(yn, rw), dd), wn), ii),
      Nat.add(Nat.add(Nat.mul(Nat.add(yn, rw), wn), Nat.mul(dd, wn)), ii), Nat.add(span, mm),
      Equal.cong(Nat, Nat, nn => Nat.add(nn, ii), Nat.mul(Nat.add(Nat.add(yn, rw), dd), wn),
        Nat.add(Nat.mul(Nat.add(yn, rw), wn), Nat.mul(dd, wn)), M1.mul_add(Nat.add(yn, rw), dd, wn)),
      Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(Nat.add(yn, rw), wn), Nat.mul(dd, wn)), ii),
        Nat.add(Nat.mul(Nat.add(yn, rw), wn), mm), Nat.add(span, mm),
        M1.ras.add_assoc(Nat.mul(Nat.add(yn, rw), wn), Nat.mul(dd, wn), ii),
        Equal.cong(Nat, Nat, nn => Nat.add(nn, mm), Nat.mul(Nat.add(yn, rw), wn), span,
          Equal.sym(Nat, span, Nat.mul(Nat.add(yn, rw), wn), bl.e_spanv(sh, oy, dw, dh)))))) :
    {kk == Nat.add(span, mm) : Nat}}
  Equal.trans(Maybe<&2, U32>, List.get(&2, U32, jn, kk), List.get(&2, U32, jn, Nat.add(span, mm)), List.get(&2, U32,
    dp, kk),
    Equal.cong(Nat, Maybe<&2, U32>, nn => List.get(&2, U32, jn, nn), kk, Nat.add(span, mm), ek),
    Equal.trans(Maybe<&2, U32>, List.get(&2, U32, jn, Nat.add(span, mm)), List.get(&2, U32, dp, Nat.add(span, mm)),
      List.get(&2, U32, dp, kk),
      bj.bottom(dp, sp, bl.top(oy, dw), span, rw, bl.Lc(ox, dw), bl.Cc(sw, ox, dw), bl.Tc(sw, ox, dw), wn,
        U32.to_nat(sw),
        mm, bl.e_row(sw, ox, dw), bl.e_span(sh, oy, dw, dh),
        bl.h_len(dp, sh, oy, dw, dh, h_dst, hy), bl.hs(sp, sw, sh, ox, oy, dw, dh, h_src)),
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
  +h_dst: {D2.wf(Img.Raster{dw, dh, dp}) == True{} : Bool},
  +h_src: {D2.wf(Img.Raster{sw, sh, sp}) == True{} : Bool},
  +ii: Nat,
  +jj: Nat,
  +hi: {Nat.is_lt(ii, U32.to_nat(dw)) == True{} : Bool},
  +h_cov: {D1.covers(ox, oy, Img.Raster{sw, sh, sp}, ii, jj) == False{} : Bool},
  +hy: {Nat.is_lt(U32.to_nat(oy), U32.to_nat(dh)) == True{} : Bool},
  +hle: {Nat.is_le(U32.to_nat(oy), jj) == True{} : Bool},
  eb: {Nat.is_lt(Nat.sub(jj, U32.to_nat(oy)), bl.Rw(sh, dh, oy)) == br : Bool}
) -> {List.get(&2, U32, bj.J(dp, sp, bl.top(oy, dw), bl.span(sh, dh, oy, dw), bl.Rw(sh, dh, oy), bl.Lc(ox, dw),
  bl.Cc(sw, ox, dw), bl.Tc(sw, ox, dw), U32.to_nat(dw), U32.to_nat(sw)), Nat.add(Nat.mul(jj, U32.to_nat(dw)), ii)) ==
  List.get(&2, U32, dp, Nat.add(Nat.mul(jj, U32.to_nat(dw)), ii)) : Maybe<&2, U32>}:
  match br:
    case True{}:
      bl.out_band(dp, sp, dw, dh, sw, sh, ox, oy, h_dst, h_src, ii, jj, hi, h_cov, hy, hle, eb)
    case False{}:
      bl.out_below(dp, sp, dw, dh, sw, sh, ox, oy, h_dst, h_src, ii, jj, hy, hle,
        M3.not_lt_le(Nat.sub(jj, U32.to_nat(oy)), bl.Rw(sh, dh, oy), eb))

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
  +h_dst: {D2.wf(Img.Raster{dw, dh, dp}) == True{} : Bool},
  +h_src: {D2.wf(Img.Raster{sw, sh, sp}) == True{} : Bool},
  +ii: Nat,
  +jj: Nat,
  +hi: {Nat.is_lt(ii, U32.to_nat(dw)) == True{} : Bool},
  +h_cov: {D1.covers(ox, oy, Img.Raster{sw, sh, sp}, ii, jj) == False{} : Bool},
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
        M1.lt_rw_r(Nat.add(Nat.mul(jj, wn), ii), Nat.mul(wn, yn), bl.top(oy, dw), Equal.trans(Nat, Nat.mul(wn, yn),
          Nat.mul(yn, wn), bl.top(oy, dw), M1.mul_comm(wn, yn), Equal.sym(Nat, bl.top(oy, dw), Nat.mul(yn, wn),
            bl.e_top(oy, dw))), M3.index_lt(ii, jj, wn, yn, hi, eb)),
        bl.e_span(sh, oy, dw, dh), bl.h_len(dp, sh, oy, dw, dh, h_dst, hy))
    case False{}:
      bl.out_r(Nat.is_lt(Nat.sub(jj, U32.to_nat(oy)), bl.Rw(sh, dh, oy)), dp, sp, dw, dh, sw, sh, ox, oy,
        h_dst, h_src, ii, jj, hi, h_cov, hy, M3.not_lt_le(jj, U32.to_nat(oy), eb), {==})

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
  +h_dst: {D2.wf(Img.Raster{dw, dh, dp}) == True{} : Bool},
  +h_src: {D2.wf(Img.Raster{sw, sh, sp}) == True{} : Bool},
  +ii: Nat,
  +jj: Nat,
  +hi: {Nat.is_lt(ii, U32.to_nat(dw)) == True{} : Bool},
  +h_cov: {D1.covers(ox, oy, Img.Raster{sw, sh, sp}, ii, jj) == False{} : Bool},
  ey: {Nat.is_lt(U32.to_nat(oy), U32.to_nat(dh)) == yin : Bool}
) -> {List.get(&2, U32, Img.blit.y(yin, dp, sp, dw, dh, sw, sh, ox, oy), Nat.add(Nat.mul(jj, U32.to_nat(dw)), ii)) ==
  List.get(&2, U32, dp, Nat.add(Nat.mul(jj, U32.to_nat(dw)), ii)) : Maybe<&2, U32>}:
  match yin:
    case False{}:
      {==}
    case True{}:
      +kk = Nat.add(Nat.mul(jj, U32.to_nat(dw)), ii)
      +jc = Img.blit.join(dp, sp, dw, dh, sw, sh, ox, oy)
      +jn = bj.J(dp, sp, bl.top(oy, dw), bl.span(sh, dh, oy, dw), bl.Rw(sh, dh, oy), bl.Lc(ox, dw), bl.Cc(sw, ox, dw),
        bl.Tc(sw, ox, dw), U32.to_nat(dw), U32.to_nat(sw))
      Equal.trans(Maybe<&2, U32>, List.get(&2, U32, jc, kk), List.get(&2, U32, jn, kk), List.get(&2, U32, dp, kk),
        Equal.cong(List<&2, U32>, Maybe<&2, U32>, xs => List.get(&2, U32, xs, kk), jc, jn, bl.join(dp, sp, dw, dh, sw,
          sh, ox, oy)),
        bl.out_j(Nat.is_lt(jj, U32.to_nat(oy)), dp, sp, dw, dh, sw, sh, ox, oy, h_dst, h_src, ii, jj, hi, h_cov, ey,
          {==}))

def Laws.blit_out(dst, src, xx, yy, h_dst, h_src, ii, jj, hi, _hj, h_cov):
  match dst src:
    case Img.Raster{+dw, +dh, +dp} Img.Raster{+sw, +sh, +sp}:
      +kk = Nat.add(Nat.mul(jj, U32.to_nat(dw)), ii)
      Equal.trans(Maybe<&2, U32>, List.get(&2, U32, Img.blit.y(U32.is_lt(yy, dh), dp, sp, dw, dh, sw, sh, xx, yy), kk),
        List.get(&2, U32, Img.blit.y(Nat.is_lt(U32.to_nat(yy), U32.to_nat(dh)), dp, sp, dw, dh, sw, sh, xx, yy), kk),
        List.get(&2, U32, dp, kk),
        Equal.cong(Bool, Maybe<&2, U32>, bb => List.get(&2, U32, Img.blit.y(bb, dp, sp, dw, dh, sw, sh, xx, yy), kk),
          U32.is_lt(yy, dh), Nat.is_lt(U32.to_nat(yy), U32.to_nat(dh)), M5.u32_lt(yy, dh)),
        bl.out_y(Nat.is_lt(U32.to_nat(yy), U32.to_nat(dh)), dp, sp, dw, dh, sw, sh, xx, yy, h_dst,
          h_src, ii,
          jj, hi, h_cov, {==}))
