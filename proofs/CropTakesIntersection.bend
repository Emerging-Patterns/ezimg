# proofs of laws/CropTakesIntersection.bend
import Base
import ../main.bend as Img
import ../laws/CropTakesIntersection.bend as Laws
import ../laws/defs/CropSpan.bend as D1
import ../laws/defs/SizeBounds.bend as D2
import ../laws/defs/WellFormed.bend as D3
import ./lemmas/BasicFacts.bend as M1
import ./lemmas/ListTakeDrop.bend as M2
import ./lemmas/RowMajorIndex.bend as M3
import ./lemmas/RowWalk.bend as M6
import ./lemmas/SubtractionAndHuffmanWalk.bend as M4
import ./lemmas/WordAddition.bend as M5

# x + r <= w gives x <= w - r
law le_sub_of_add:
  for +xx: Nat
  for +rr: Nat
  for +ww: Nat
  for +hh: {Nat.is_le(Nat.add(xx, rr), ww) == True{} : Bool}
  {Nat.is_le(xx, Nat.sub(ww, rr)) == True{} : Bool}

# the proof of le_sub_of_add
def le_sub_of_add(xx, rr, ww, hh):
  +hr = {M5.le_add_r(rr, xx, ww, M1.le_rw_l(Nat.add(xx, rr), Nat.add(rr, xx), ww, M1.ras.add_comm(xx, rr), hh)) :
    {Nat.is_le(rr, ww) == True{} : Bool}}
  M4.le_cancel(rr, xx, Nat.sub(ww, rr), M1.le_rw_r(Nat.add(rr, xx), ww, Nat.add(rr, Nat.sub(ww, rr)),
    Equal.sym(Nat, Nat.add(rr, Nat.sub(ww, rr)), ww, M4.add_sub(rr, ww, hr)),
    M1.le_rw_l(Nat.add(xx, rr), Nat.add(rr, xx), ww, M1.ras.add_comm(xx, rr), hh)))

# min(a, 0) is 0
law min_zero_r:
  for aa: Nat
  {Nat.min(aa, 0n) == 0n : Nat}

# the proof of min_zero_r
def min_zero_r(aa):
  match aa:
    case 0n:
      {==}
    case 1n+_pp:
      {==}

# (a + b) + c regrouped as (a + c) + b
law add_right_swap:
  for +aa: Nat
  for +bb: Nat
  for +cc: Nat
  {Nat.add(Nat.add(aa, bb), cc) == Nat.add(Nat.add(aa, cc), bb) : Nat}

# the proof of add_right_swap
def add_right_swap(aa, bb, cc):
  Equal.trans(Nat, Nat.add(Nat.add(aa, bb), cc), Nat.add(aa, Nat.add(bb, cc)), Nat.add(Nat.add(aa, cc), bb),
    M1.ras.add_assoc(aa, bb, cc),
    Equal.trans(Nat, Nat.add(aa, Nat.add(bb, cc)), Nat.add(aa, Nat.add(cc, bb)), Nat.add(Nat.add(aa, cc), bb),
      Equal.cong(Nat, Nat, xx => Nat.add(aa, xx), Nat.add(bb, cc), Nat.add(cc, bb), M1.ras.add_comm(bb, cc)),
      Equal.sym(Nat, Nat.add(Nat.add(aa, cc), bb), Nat.add(aa, Nat.add(cc, bb)), M1.ras.add_assoc(aa, cc, bb))))

# the rows walk's first row is whole: rw <= length
def crop.rows_head(
  +pp: Nat,
  +xs: List<&2, U32>,
  +rw: Nat,
  +gap: Nat,
  hh: {Nat.is_le(Nat.mul(1n+pp, Nat.add(rw, gap)), Nat.add(List.length(&2, U32, xs), gap)) == True{} : Bool}
) -> {Nat.is_le(rw, List.length(&2, U32, xs)) == True{} : Bool}:
  +ln = List.length(&2, U32, xs)
  M4.le_cancel(gap, rw, ln, M1.le_rw_r(Nat.add(gap, rw), Nat.add(ln, gap), Nat.add(gap, ln), M1.ras.add_comm(ln, gap),
    M1.le_rw_l(Nat.add(rw, gap), Nat.add(gap, rw), Nat.add(ln, gap), M1.ras.add_comm(rw, gap),
      M5.le_add_r(Nat.add(rw, gap), Nat.mul(pp, Nat.add(rw, gap)), Nat.add(ln, gap), hh))))

# the rows walk's bound holds again one row on
def crop.rows_next(
  +pp: Nat,
  +xs: List<&2, U32>,
  +rw: Nat,
  +gap: Nat,
  hh: {Nat.is_le(Nat.mul(1n+pp, Nat.add(rw, gap)), Nat.add(List.length(&2, U32, xs), gap)) == True{} : Bool}
) -> {Nat.is_le(Nat.mul(pp, Nat.add(rw, gap)),
  Nat.add(List.length(&2, U32, List.drop(&2, U32, xs, Nat.add(rw, gap))), gap)) == True{} : Bool}:
  M2.drop_le(xs, Nat.add(rw, gap), Nat.mul(pp, Nat.add(rw, gap)), gap, hh)

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
        M2.len_append(tk, rest),
        Equal.trans(Nat, Nat.add(List.length(&2, U32, tk), List.length(&2, U32, rest)),
          Nat.add(rw, List.length(&2, U32, rest)), Nat.add(rw, Nat.mul(pp, rw)),
          Equal.cong(Nat, Nat, xx => Nat.add(xx, List.length(&2, U32, rest)), List.length(&2, U32, tk), rw,
            M2.len_take(xs, rw, crop.rows_head(pp, xs, rw, gap, hh))),
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
        M1.false_true(Equal.trans(Bool, False{}, Nat.is_lt(_jj, 0n), True{}, M1.lt_zero_false(_jj), hj)))
    case 1n+(+pp) 0n:
      M2.get_append_take(xs, rw, ii, Img.crop.rows(pp, List.drop(&2, U32, xs, Nat.add(rw, gap)), rw, gap), hi,
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
          Nat.add(rw, Nat.add(mq, ii)), M1.ras.add_assoc(rw, mq, ii)),
        Equal.trans(Maybe<&2, U32>, List.get(&2, U32, both, Nat.add(rw, Nat.add(mq, ii))),
          List.get(&2, U32, rest, Nat.add(mq, ii)), List.get(&2, U32, xs, Nat.add(Nat.add(ss, ms), ii)),
          M2.get_append_skip(xs, rw, Nat.add(mq, ii), rest, crop.rows_head(pp, xs, rw, gap, hh)),
          Equal.trans(Maybe<&2, U32>, List.get(&2, U32, rest, Nat.add(mq, ii)),
            List.get(&2, U32, dx, Nat.add(ms, ii)), List.get(&2, U32, xs, Nat.add(Nat.add(ss, ms), ii)),
            crop.rows_get(pp, dx, rw, gap, ii, qq, hi, hj, crop.rows_next(pp, xs, rw, gap, hh)),
            Equal.trans(Maybe<&2, U32>, List.get(&2, U32, dx, Nat.add(ms, ii)),
              List.get(&2, U32, xs, Nat.add(ss, Nat.add(ms, ii))), List.get(&2, U32, xs, Nat.add(Nat.add(ss, ms), ii)),
              M2.get_drop(xs, ss, Nat.add(ms, ii)),
              Equal.cong(Nat, Maybe<&2, U32>, kk => List.get(&2, U32, xs, kk), Nat.add(ss, Nat.add(ms, ii)),
                Nat.add(Nat.add(ss, ms), ii), Equal.sym(Nat, Nat.add(Nat.add(ss, ms), ii), Nat.add(ss, Nat.add(ms, ii)),
                  M1.ras.add_assoc(ss, ms, ii)))))))

# where crop's rows start: x after y rows of w, reached a row at a time
def crop.ll(+px: List<&2, U32>, +ww: U32, +xx: U32, +yy: U32) -> List<&2, U32>:
  List.drop(&2, U32, Img.skip.rows(U32.to_nat(yy), px, U32.to_nat(ww)), U32.to_nat(xx))

# is the rectangle's intersection with the raster nonempty
def crop.ok(+ww: U32, +hh: U32, +xx: U32, +yy: U32, +cw: U32, +ch: U32) -> Bool:
  Bool.and(Nat.is_lt(0n, D1.cut(ww, xx, cw)), Nat.is_lt(0n, D1.cut(hh, yy, ch)))

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
        Img.crop.rows(U32.to_nat(rh), crop.ll(px, ww, xx, yy),
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

# the side crop computes, min(c, w - x) in U32, is cut(w, x, c) when x < w
def crop.side_nat(
  +ww: U32,
  +xx: U32,
  +cc: U32,
  hx: {Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)) == True{} : Bool}
) -> {U32.to_nat(Img.u.min(cc, (ww - xx : U32))) == D1.cut(ww, xx, cc) : Nat}:
  Equal.trans(Nat, U32.to_nat(Img.u.min(cc, (ww - xx : U32))), Nat.min(U32.to_nat(cc), U32.to_nat((ww - xx : U32))),
    D1.cut(ww, xx, cc), M2.ras.umin(cc, (ww - xx : U32)),
    Equal.cong(Nat, Nat, nn => Nat.min(U32.to_nat(cc), nn), U32.to_nat((ww - xx : U32)),
      Nat.sub(U32.to_nat(ww), U32.to_nat(xx)),
      M4.ras.u32_sub_nat(ww, xx, M1.lt_le(U32.to_nat(xx), U32.to_nat(ww), hx))))

# a U32 side read as n: it is not zero exactly when 0 < n
def crop.nz(
  +ru: U32,
  +nn: Nat,
  ee: {U32.to_nat(ru) == nn : Nat}
) -> {Bool.not(U32.is_zero(ru)) == Nat.is_lt(0n, nn) : Bool}:
  Equal.trans(Bool, Bool.not(U32.is_zero(ru)), Bool.not(Nat.is_eq(nn, 0n)), Nat.is_lt(0n, nn),
    Equal.cong(Bool, Bool, bb => Bool.not(bb), U32.is_zero(ru), Nat.is_eq(nn, 0n),
      Equal.trans(Bool, U32.is_zero(ru), Nat.is_eq(U32.to_nat(ru), 0n), Nat.is_eq(nn, 0n), M1.u32_eq(ru, 0),
        Equal.cong(Nat, Bool, mm => Nat.is_eq(mm, 0n), U32.to_nat(ru), nn, ee))),
    Equal.sym(Bool, Nat.is_lt(0n, nn), Bool.not(Nat.is_eq(nn, 0n)), M4.pos_eq(nn)))

# x >= w leaves nothing of the span: cut(w, x, c) is 0
def crop.cut_out(
  +ww: U32,
  +xx: U32,
  +cc: U32,
  hx: {Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)) == False{} : Bool}
) -> {D1.cut(ww, xx, cc) == 0n : Nat}:
  Equal.trans(Nat, D1.cut(ww, xx, cc), Nat.min(U32.to_nat(cc), 0n), 0n,
    Equal.cong(Nat, Nat, nn => Nat.min(U32.to_nat(cc), nn), Nat.sub(U32.to_nat(ww), U32.to_nat(xx)), 0n,
      M4.sub_zero_le(U32.to_nat(ww), U32.to_nat(xx), M3.not_lt_le(U32.to_nat(xx), U32.to_nat(ww), hx))),
    min_zero_r(U32.to_nat(cc)))

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
        Bool.and(Nat.is_lt(0n, D1.cut(ww, xx, cw)), Bool.not(U32.is_zero(rh))), crop.ok(ww, hh, xx, yy, cw, ch),
        Equal.cong(Bool, Bool, bb => Bool.and(bb, Bool.not(U32.is_zero(rh))), Bool.not(U32.is_zero(rw)),
          Nat.is_lt(0n, D1.cut(ww, xx, cw)), crop.nz(rw, D1.cut(ww, xx, cw), crop.side_nat(ww, xx, cw, hx))),
        Equal.cong(Bool, Bool, bb => Bool.and(Nat.is_lt(0n, D1.cut(ww, xx, cw)), bb), Bool.not(U32.is_zero(rh)),
          Nat.is_lt(0n, D1.cut(hh, yy, ch)), crop.nz(rh, D1.cut(hh, yy, ch), crop.side_nat(hh, yy, ch, hy))))))

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
          Equal.trans(Bool, crop.ok(ww, hh, xx, yy, cw, ch), Bool.and(Nat.is_lt(0n, D1.cut(ww, xx, cw)), False{}),
            False{}, Equal.cong(Nat, Bool, nn => Bool.and(Nat.is_lt(0n, D1.cut(ww, xx, cw)), Nat.is_lt(0n, nn)),
              D1.cut(hh, yy, ch), 0n, crop.cut_out(hh, yy, ch, ey)),
            M4.and_false_r(Nat.is_lt(0n, D1.cut(ww, xx, cw))))))
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
          Equal.cong(Nat, Bool, nn => Bool.and(Nat.is_lt(0n, nn), Nat.is_lt(0n, D1.cut(hh, yy, ch))),
            D1.cut(ww, xx, cw), 0n, crop.cut_out(ww, xx, cw, ex))))
    case True{}:
      Equal.trans(Img.Raster, Img.crop.y(U32.is_lt(yy, hh), px, ww, hh, xx, yy, cw, ch),
        Img.crop.y(Nat.is_lt(U32.to_nat(yy), U32.to_nat(hh)), px, ww, hh, xx, yy, cw, ch),
        crop.nf(crop.ok(ww, hh, xx, yy, cw, ch), px, ww, xx, yy, Img.u.min(cw, (ww - xx : U32)),
          Img.u.min(ch, (hh - yy : U32))),
        Equal.cong(Bool, Img.Raster, bb => Img.crop.y(bb, px, ww, hh, xx, yy, cw, ch), U32.is_lt(yy, hh),
          Nat.is_lt(U32.to_nat(yy), U32.to_nat(hh)), M5.u32_lt(yy, hh)),
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
      Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)), M5.u32_lt(xx, ww)),
    crop.nf_x(Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)), px, ww, hh, xx, yy, cw, ch, {==}))

# a nonempty span starts inside: 0 < cut(w, x, c) gives x < w
def crop.cut_pos(
  +ww: U32,
  +xx: U32,
  +cc: U32,
  hh: {Nat.is_lt(0n, D1.cut(ww, xx, cc)) == True{} : Bool}
) -> {Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)) == True{} : Bool}:
  +dd = Nat.sub(U32.to_nat(ww), U32.to_nat(xx))
  M2.sub_pos(U32.to_nat(ww), U32.to_nat(xx), M1.lt_le_trans(0n, D1.cut(ww, xx, cc), dd, hh,
    M2.min_le_r(U32.to_nat(cc), dd)))

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
  +er = {crop.side_nat(ww, xx, cc, hx) : {rn == D1.cut(ww, xx, cc) : Nat}}
  M1.le_rw_r(Nat.add(xn, rn), Nat.add(xn, dd), wn, M4.add_sub(xn, wn, M1.lt_le(xn, wn, hx)),
    M1.le_add_mono(xn, rn, dd, M1.le_rw_l(D1.cut(ww, xx, cc), rn, dd, Equal.sym(Nat, rn, D1.cut(ww, xx, cc), er),
      M2.min_le_r(U32.to_nat(cc), dd))))

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
  +hr = {M4.le_add_l(U32.to_nat(xx), rn, wn, crop.fit(ww, xx, cc, hx)) : {Nat.is_le(rn, wn) == True{} : Bool}}
  Equal.trans(Nat, Nat.add(rn, U32.to_nat((ww - rw : U32))), Nat.add(rn, Nat.sub(wn, rn)), wn,
    Equal.cong(Nat, Nat, nn => Nat.add(rn, nn), U32.to_nat((ww - rw : U32)), Nat.sub(wn, rn),
      M4.ras.u32_sub_nat(ww, rw, hr)),
    M4.add_sub(rn, wn, hr))

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
  M1.le_rw_r(U32.to_nat(xx), Nat.sub(wn, rn), U32.to_nat((ww - rw : U32)),
    Equal.sym(Nat, U32.to_nat((ww - rw : U32)), Nat.sub(wn, rn), M4.ras.u32_sub_nat(ww, rw, M4.le_add_l(U32.to_nat(xx),
        rn,
      wn, hf))),
    le_sub_of_add(U32.to_nat(xx), rn, wn, hf))

# the rows walk over a well-formed raster has what it reads: rh * (rw + gap) <= length after the start + gap
def crop.cond(
  +px: List<&2, U32>,
  +ww: U32,
  +hh: U32,
  +xx: U32,
  +yy: U32,
  +cw: U32,
  +ch: U32,
  h_wf: {D3.wf(Img.Raster{ww, hh, px}) == True{} : Bool},
  +hx: {Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)) == True{} : Bool},
  +hy: {Nat.is_lt(U32.to_nat(yy), U32.to_nat(hh)) == True{} : Bool}
) -> {Nat.is_le(Nat.mul(U32.to_nat(Img.u.min(ch, (hh - yy : U32))), Nat.add(U32.to_nat(Img.u.min(cw, (ww - xx : U32))),
  U32.to_nat((ww - Img.u.min(cw, (ww - xx : U32)) : U32)))), Nat.add(List.length(&2, U32,
  crop.ll(px, ww, xx, yy)), U32.to_nat((ww - Img.u.min(cw, (ww - xx : U32)) : U32)))) == True{} : Bool}:
  +wn = U32.to_nat(ww)
  +hn = U32.to_nat(hh)
  +xn = U32.to_nat(xx)
  +yn = U32.to_nat(yy)
  +rw = Img.u.min(cw, (ww - xx : U32))
  +rhn = U32.to_nat(Img.u.min(ch, (hh - yy : U32)))
  +gn = U32.to_nat((ww - rw : U32))
  +yw = Nat.mul(yn, wn)
  +s0 = Nat.add(yw, xn)
  +ln = List.length(&2, U32, px)
  +el = {M1.ras.nat_eq_true(ln, Nat.mul(wn, hn), h_wf) : {ln == Nat.mul(wn, hn) : Nat}}
  +es = {{==} : {s0 == Nat.add(yw, xn) : Nat}}
  +hr = {M1.le_rw_r(Nat.mul(Nat.add(yn, rhn), wn), Nat.mul(hn, wn), Nat.mul(wn, hn), M1.mul_comm(hn, wn),
    M5.le_mul_mono(Nat.add(yn, rhn), hn, wn, crop.fit(hh, yy, ch, hy))) :
    {Nat.is_le(Nat.mul(Nat.add(yn, rhn), wn), Nat.mul(wn, hn)) == True{} : Bool}}
  +e_lhs = {Equal.trans(Nat, Nat.add(s0, Nat.mul(rhn, wn)), Nat.add(Nat.add(yw, xn), Nat.mul(rhn, wn)),
    Nat.add(Nat.mul(Nat.add(yn, rhn), wn), xn),
    Equal.cong(Nat, Nat, nn => Nat.add(nn, Nat.mul(rhn, wn)), s0, Nat.add(yw, xn), es),
    Equal.trans(Nat, Nat.add(Nat.add(yw, xn), Nat.mul(rhn, wn)), Nat.add(Nat.add(yw, Nat.mul(rhn, wn)), xn),
      Nat.add(Nat.mul(Nat.add(yn, rhn), wn), xn), add_right_swap(yw, xn, Nat.mul(rhn, wn)),
      Equal.cong(Nat, Nat, nn => Nat.add(nn, xn), Nat.add(yw, Nat.mul(rhn, wn)), Nat.mul(Nat.add(yn, rhn), wn),
        Equal.sym(Nat, Nat.mul(Nat.add(yn, rhn), wn), Nat.add(yw, Nat.mul(rhn, wn)), M1.mul_add(yn, rhn, wn))))) :
    {Nat.add(s0, Nat.mul(rhn, wn)) == Nat.add(Nat.mul(Nat.add(yn, rhn), wn), xn) : Nat}}
  +h_main = {M1.le_rw_r(Nat.add(s0, Nat.mul(rhn, wn)), Nat.add(Nat.mul(wn, hn), gn), Nat.add(ln, gn),
    Equal.cong(Nat, Nat, nn => Nat.add(nn, gn), Nat.mul(wn, hn), ln, Equal.sym(Nat, ln, Nat.mul(wn, hn), el)),
    M1.le_rw_l(Nat.add(Nat.mul(Nat.add(yn, rhn), wn), xn), Nat.add(s0, Nat.mul(rhn, wn)), Nat.add(Nat.mul(wn, hn), gn),
      Equal.sym(Nat, Nat.add(s0, Nat.mul(rhn, wn)), Nat.add(Nat.mul(Nat.add(yn, rhn), wn), xn), e_lhs),
      M1.le_add_both(Nat.mul(Nat.add(yn, rhn), wn), Nat.mul(wn, hn), xn, gn, hr, crop.gap(ww, xx, cw, hx)))) :
    {Nat.is_le(Nat.add(s0, Nat.mul(rhn, wn)), Nat.add(ln, gn)) == True{} : Bool}}
  +ll = crop.ll(px, ww, xx, yy)
  +e_ll = {M6.drop_rows(yn, px, wn, xn) : {ll == List.drop(&2, U32, px, s0) : List<&2, U32>}}
  M1.le_rw_l(Nat.mul(rhn, wn), Nat.mul(rhn, Nat.add(U32.to_nat(rw), gn)),
    Nat.add(List.length(&2, U32, ll), gn),
    Equal.cong(Nat, Nat, nn => Nat.mul(rhn, nn), wn, Nat.add(U32.to_nat(rw), gn),
      Equal.sym(Nat, Nat.add(U32.to_nat(rw), gn), wn, crop.row(ww, xx, cw, hx))),
    M1.le_rw_r(Nat.mul(rhn, wn), Nat.add(List.length(&2, U32, List.drop(&2, U32, px, s0)), gn),
      Nat.add(List.length(&2, U32, ll), gn),
      Equal.cong(List<&2, U32>, Nat, xs => Nat.add(List.length(&2, U32, xs), gn), List.drop(&2, U32, px, s0), ll,
        Equal.sym(List<&2, U32>, ll, List.drop(&2, U32, px, s0), e_ll)),
      M2.drop_le(px, s0, Nat.mul(rhn, wn), gn, h_main)))

# both sides of an empty intersection's crop are 0
def crop.side_zero(
  aa: Nat,
  bb: Nat,
  hh: {Bool.and(Nat.is_lt(0n, aa), Nat.is_lt(0n, bb)) == False{} : Bool}
) -> {(0n, 0n) == (D2.side(aa, bb), D2.side(bb, aa)) : Nat & Nat}:
  match aa bb:
    case 0n 0n:
      {==}
    case 0n 1n+_qq:
      {==}
    case 1n+_pp 0n:
      {==}
    case 1n+_pp 1n+_qq:
      Empty.absurd({(0n, 0n) == (1n+_pp, 1n+_qq) : Nat & Nat}, M1.false_true(Equal.sym(Bool, True{}, False{}, hh)))

# both sides of a nonempty intersection's crop are the intersection's
def crop.side_pos(
  aa: Nat,
  bb: Nat,
  hh: {Bool.and(Nat.is_lt(0n, aa), Nat.is_lt(0n, bb)) == True{} : Bool}
) -> {(aa, bb) == (D2.side(aa, bb), D2.side(bb, aa)) : Nat & Nat}:
  match aa bb:
    case 0n _bb:
      Empty.absurd({(0n, _bb) == (D2.side(0n, _bb), D2.side(_bb, 0n)) : Nat & Nat}, M1.false_true(hh))
    case 1n+_pp 0n:
      Empty.absurd({(1n+_pp, 0n) == (0n, 0n) : Nat & Nat}, M1.false_true(
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
  (D2.side(D1.cut(ww, xx, cw), D1.cut(hh, yy, ch)), D2.side(D1.cut(hh, yy, ch), D1.cut(ww, xx, cw))) :
  Nat & Nat}:
  match ok:
    case False{}:
      crop.side_zero(D1.cut(ww, xx, cw), D1.cut(hh, yy, ch), e_ok)
    case True{}:
      +iw = D1.cut(ww, xx, cw)
      +ih = D1.cut(hh, yy, ch)
      +e2 = {e_ok : {Bool.and(Nat.is_lt(0n, iw), Nat.is_lt(0n, ih)) == True{} : Bool}}
      +rn = U32.to_nat(Img.u.min(cw, (ww - xx : U32)))
      +hn = U32.to_nat(Img.u.min(ch, (hh - yy : U32)))
      +er = {crop.side_nat(ww, xx, cw, crop.cut_pos(ww, xx, cw, M1.and_left(Nat.is_lt(0n, iw), Nat.is_lt(0n, ih),
        e2))) :
        {rn == iw : Nat}}
      +eh = {crop.side_nat(hh, yy, ch, crop.cut_pos(hh, yy, ch, M1.and_right(Nat.is_lt(0n, iw), Nat.is_lt(0n, ih),
        e2)))
        : {hn == ih : Nat}}
      Equal.trans(Nat & Nat, (rn, hn), (iw, ih), (D2.side(iw, ih), D2.side(ih, iw)),
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
        (D2.side(D1.cut(ww, xx, cw), D1.cut(hh, yy, ch)), D2.side(D1.cut(hh, yy, ch), D1.cut(ww, xx, cw))),
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
  crop.cut_pos(ww, xx, cw, M1.and_left(Nat.is_lt(0n, D1.cut(ww, xx, cw)), Nat.is_lt(0n, D1.cut(hh, yy, ch)),
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
  crop.cut_pos(hh, yy, ch, M1.and_right(Nat.is_lt(0n, D1.cut(ww, xx, cw)), Nat.is_lt(0n, D1.cut(hh, yy, ch)),
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
  h_wf: {D3.wf(Img.Raster{ww, hh, px}) == True{} : Bool}
) -> {D3.wf(crop.nf(ok, px, ww, xx, yy, Img.u.min(cw, (ww - xx : U32)), Img.u.min(ch, (hh - yy : U32)))) == True{} :
  Bool}:
  match ok:
    case False{}:
      {==}
    case True{}:
      +rw = Img.u.min(cw, (ww - xx : U32))
      +rh = Img.u.min(ch, (hh - yy : U32))
      +rows = Img.crop.rows(U32.to_nat(rh), crop.ll(px, ww, xx, yy), U32.to_nat(rw),
        U32.to_nat((ww - rw : U32)))
      +el = {Equal.trans(Nat, List.length(&2, U32, rows), Nat.mul(U32.to_nat(rh), U32.to_nat(rw)),
        Nat.mul(U32.to_nat(rw), U32.to_nat(rh)),
        crop.rows_len(U32.to_nat(rh), crop.ll(px, ww, xx, yy), U32.to_nat(rw),
          U32.to_nat((ww - rw : U32)), crop.cond(px, ww, hh, xx, yy, cw, ch, h_wf,
            crop.in_x(ww, hh, xx, yy, cw, ch, e_ok), crop.in_y(ww, hh, xx, yy, cw, ch, e_ok))),
        M1.mul_comm(U32.to_nat(rh), U32.to_nat(rw))) :
        {List.length(&2, U32, rows) == Nat.mul(U32.to_nat(rw), U32.to_nat(rh)) : Nat}}
      Equal.trans(Bool, Nat.is_eq(List.length(&2, U32, rows), Nat.mul(U32.to_nat(rw), U32.to_nat(rh))),
        Nat.is_eq(Nat.mul(U32.to_nat(rw), U32.to_nat(rh)), Nat.mul(U32.to_nat(rw), U32.to_nat(rh))), True{},
        Equal.cong(Nat, Bool, nn => Nat.is_eq(nn, Nat.mul(U32.to_nat(rw), U32.to_nat(rh))), List.length(&2, U32, rows),
          Nat.mul(U32.to_nat(rw), U32.to_nat(rh)), el),
        M1.nat_eq_refl(Nat.mul(U32.to_nat(rw), U32.to_nat(rh))))

def Laws.crop_wf(img, xx, yy, cw, ch, h_wf):
  match img:
    case Img.Raster{+ww, +hh, +px}:
      +nf = crop.nf(crop.ok(ww, hh, xx, yy, cw, ch), px, ww, xx, yy, Img.u.min(cw, (ww - xx : U32)),
        Img.u.min(ch, (hh - yy : U32)))
      Equal.trans(Bool, D3.wf(Img.crop(Img.Raster{ww, hh, px}, xx, yy, cw, ch)), D3.wf(nf), True{},
        Equal.cong(Img.Raster, Bool, rr => D3.wf(rr), Img.crop(Img.Raster{ww, hh, px}, xx, yy, cw, ch), nf,
          crop.nf_eq(px, ww, hh, xx, yy, cw, ch)),
        crop.wf_nf(crop.ok(ww, hh, xx, yy, cw, ch), px, ww, hh, xx, yy, cw, ch, {==}, h_wf))

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
  h_wf: {D3.wf(Img.Raster{ww, hh, px}) == True{} : Bool},
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
        M1.false_true(Equal.trans(Bool, False{}, Nat.is_lt(ii, 0n), True{}, M1.lt_zero_false(ii), hi)))
    case True{}:
      +wn = U32.to_nat(ww)
      +xn = U32.to_nat(xx)
      +yn = U32.to_nat(yy)
      +rw = Img.u.min(cw, (ww - xx : U32))
      +rn = U32.to_nat(rw)
      +gn = U32.to_nat((ww - rw : U32))
      +s0 = Nat.add(Nat.mul(yn, wn), xn)
      +ll = crop.ll(px, ww, xx, yy)
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
          crop.cond(px, ww, hh, xx, yy, cw, ch, h_wf, hx, hy)),
        Equal.trans(Maybe<&2, U32>, List.get(&2, U32, ll, Nat.add(Nat.mul(jj, Nat.add(rn, gn)), ii)),
          List.get(&2, U32, ll, Nat.add(jw, ii)),
          List.get(&2, U32, px, Nat.add(Nat.mul(Nat.add(yn, jj), wn), Nat.add(xn, ii))),
          Equal.cong(Nat, Maybe<&2, U32>, nn => List.get(&2, U32, ll, Nat.add(Nat.mul(jj, nn), ii)), Nat.add(rn,
            gn), wn,
            crop.row(ww, xx, cw, hx)),
          Equal.trans(Maybe<&2, U32>, List.get(&2, U32, ll, Nat.add(jw, ii)),
            List.get(&2, U32, px, Nat.add(s0, Nat.add(jw, ii))),
            List.get(&2, U32, px, Nat.add(Nat.mul(Nat.add(yn, jj), wn), Nat.add(xn, ii))),
            Equal.trans(Maybe<&2, U32>, List.get(&2, U32, ll, Nat.add(jw, ii)),
              List.get(&2, U32, List.drop(&2, U32, px, s0), Nat.add(jw, ii)), List.get(&2, U32, px, Nat.add(s0,
                Nat.add(jw, ii))),
              Equal.cong(List<&2, U32>, Maybe<&2, U32>, xs => List.get(&2, U32, xs, Nat.add(jw, ii)), ll,
                List.drop(&2, U32, px, s0), M6.drop_rows(yn, px, wn, xn)),
              M2.get_drop(px, s0, Nat.add(jw, ii))),
            Equal.cong(Nat, Maybe<&2, U32>, nn => List.get(&2, U32, px, nn), Nat.add(s0, Nat.add(jw, ii)),
              Nat.add(Nat.mul(Nat.add(yn, jj), wn), Nat.add(xn, ii)),
              Equal.trans(Nat, Nat.add(s0, Nat.add(jw, ii)), Nat.add(Nat.add(yw, xn), Nat.add(jw, ii)),
                Nat.add(Nat.mul(Nat.add(yn, jj), wn), Nat.add(xn, ii)),
                Equal.cong(Nat, Nat, nn => Nat.add(nn, Nat.add(jw, ii)), s0, Nat.add(yw, xn), {==}),
                Equal.trans(Nat, Nat.add(Nat.add(yw, xn), Nat.add(jw, ii)), Nat.add(Nat.add(yw, jw), Nat.add(xn, ii)),
                  Nat.add(Nat.mul(Nat.add(yn, jj), wn), Nat.add(xn, ii)), M5.add4(yw, xn, jw, ii),
                  Equal.cong(Nat, Nat, nn => Nat.add(nn, Nat.add(xn, ii)), Nat.add(yw, jw), Nat.mul(Nat.add(yn, jj),
                    wn),
                    Equal.sym(Nat, Nat.mul(Nat.add(yn, jj), wn), Nat.add(yw, jw), M1.mul_add(yn, jj, wn)))))))))

def Laws.crop_at(img, xx, yy, cw, ch, h_wf, ii, jj, hi, hj):
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
        crop.at_nf(crop.ok(ww, hh, xx, yy, cw, ch), px, ww, hh, xx, yy, cw, ch, {==}, h_wf, ii, jj,
          Equal.trans(Bool, Nat.is_lt(ii, U32.to_nat(Img.width(nf))), Nat.is_lt(ii, U32.to_nat(Img.width(cr))), True{},
            Equal.cong(Img.Raster, Bool, rr => Nat.is_lt(ii, U32.to_nat(Img.width(rr))), nf, cr,
              Equal.sym(Img.Raster, cr, nf, en)), hi),
          Equal.trans(Bool, Nat.is_lt(jj, U32.to_nat(Img.height(nf))), Nat.is_lt(jj, U32.to_nat(Img.height(cr))),
            True{},
            Equal.cong(Img.Raster, Bool, rr => Nat.is_lt(jj, U32.to_nat(Img.height(rr))), nf, cr,
              Equal.sym(Img.Raster, cr, nf, en)), hj)))
