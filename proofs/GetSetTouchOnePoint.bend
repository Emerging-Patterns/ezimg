# proofs of laws/GetSetTouchOnePoint.bend
import Base
import ../main.bend as Img
import ../laws/GetSetTouchOnePoint.bend as Laws
import ./lemmas/BasicFacts.bend as M1
import ./lemmas/RowMajorIndex.bend as M2
import ./lemmas/RowWalk.bend as M4
import ./lemmas/WordAddition.bend as M3

# an index below the length finds an element
law get_some_lt:
  for xs: List<&2, U32>
  for kk: Nat
  for hh: {Nat.is_lt(kk, List.length(&2, U32, xs)) == True{} : Bool}
  {Maybe.is_some(&2, U32, List.get(&2, U32, xs, kk)) == True{} : Bool}

# the proof of get_some_lt
def get_some_lt(xs, kk, hh):
  match xs kk:
    case Nil{} _kk:
      Empty.absurd({Maybe.is_some(&2, U32, List.get(&2, U32, Nil{}, _kk)) == True{} : Bool}, M1.false_true(
        Equal.trans(Bool, False{}, Nat.is_lt(_kk, 0n), True{}, M1.lt_zero_false(_kk), hh)))
    case _hd <> _tl 0n:
      {==}
    case _hd <> tl 1n+qq:
      get_some_lt(tl, qq, hh)

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
  M1.and_left(Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)), Nat.is_lt(U32.to_nat(yy), U32.to_nat(hh)), h_in)

# the y half of a point inside
def ras.hy(
  +ww: U32,
  +hh: U32,
  +xx: U32,
  +yy: U32,
  h_in: {ras.In(ww, hh, xx, yy) == True{} : Bool}
) -> {Nat.is_lt(U32.to_nat(yy), U32.to_nat(hh)) == True{} : Bool}:
  M1.and_right(Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)), Nat.is_lt(U32.to_nat(yy), U32.to_nat(hh)), h_in)

# get at a point inside, once the raster is taken apart
def ras.get_in(
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  +xx: U32,
  +yy: U32,
  +hx: {Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)) == True{} : Bool},
  +hy: {Nat.is_lt(U32.to_nat(yy), U32.to_nat(hh)) == True{} : Bool}
) -> {Img.get.x(U32.is_lt(xx, ww), px, ww, hh, xx, yy) == List.get(&2, U32, px, Laws.spot(ww, xx, yy)) :
  Maybe<&2, U32>}:
  Equal.trans(Maybe<&2, U32>, Img.get.x(U32.is_lt(xx, ww), px, ww, hh, xx, yy), Img.get.x(True{}, px, ww, hh, xx, yy),
    List.get(&2, U32, px, Laws.spot(ww, xx, yy)),
    Equal.cong(Bool, Maybe<&2, U32>, bb => Img.get.x(bb, px, ww, hh, xx, yy), U32.is_lt(xx, ww), True{},
      M2.ras.lt(xx, ww, hx)),
    Equal.trans(Maybe<&2, U32>, Img.get.y(U32.is_lt(yy, hh), px, ww, xx, yy), Img.get.y(True{}, px, ww, xx, yy),
      List.get(&2, U32, px, Laws.spot(ww, xx, yy)),
      Equal.cong(Bool, Maybe<&2, U32>, bb => Img.get.y(bb, px, ww, xx, yy), U32.is_lt(yy, hh), True{},
        M2.ras.lt(yy, hh, hy)),
      M4.get_rows(U32.to_nat(yy), px, U32.to_nat(ww), U32.to_nat(xx))))

def Laws.get_inside(img, xx, yy, h_in):
  match img:
    case Img.Raster{+ww, +hh, +px}:
      ras.get_in(ww, hh, px, xx, yy, ras.hx(ww, hh, xx, yy, h_in), ras.hy(ww, hh, xx, yy, h_in))

def Laws.get_inside_some(img, xx, yy, h_wf, h_in):
  match img:
    case Img.Raster{+ww, +hh, +px}:
      +hx = {ras.hx(ww, hh, xx, yy, h_in) : {Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)) == True{} : Bool}}
      +hy = {ras.hy(ww, hh, xx, yy, h_in) : {Nat.is_lt(U32.to_nat(yy), U32.to_nat(hh)) == True{} : Bool}}
      +wh = Nat.mul(U32.to_nat(ww), U32.to_nat(hh))
      +el = {M1.ras.nat_eq_true(List.length(&2, U32, px), wh, h_wf) : {List.length(&2, U32, px) == wh : Nat}}
      +hk = {M1.lt_rw_r(Laws.spot(ww, xx, yy), wh, List.length(&2, U32, px),
        Equal.sym(Nat, List.length(&2, U32, px), wh, el),
        M2.index_lt(U32.to_nat(xx), U32.to_nat(yy), U32.to_nat(ww), U32.to_nat(hh), hx, hy)) :
        {Nat.is_lt(Laws.spot(ww, xx, yy), List.length(&2, U32, px)) == True{} : Bool}}
      Equal.trans(Bool, Maybe.is_some(&2, U32, Img.get.x(U32.is_lt(xx, ww), px, ww, hh, xx, yy)),
        Maybe.is_some(&2, U32, List.get(&2, U32, px, Laws.spot(ww, xx, yy))), True{},
        Equal.cong(Maybe<&2, U32>, Bool, mm => Maybe.is_some(&2, U32, mm),
          Img.get.x(U32.is_lt(xx, ww), px, ww, hh, xx, yy), List.get(&2, U32, px, Laws.spot(ww, xx, yy)),
          ras.get_in(ww, hh, px, xx, yy, hx, hy)),
        get_some_lt(px, Laws.spot(ww, xx, yy), hk))

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
      Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)), M3.u32_lt(xx, ww)),
    Equal.cong(Bool, Bool, bb => Bool.and(Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)), bb), U32.is_lt(yy, hh),
      Nat.is_lt(U32.to_nat(yy), U32.to_nat(hh)), M3.u32_lt(yy, hh)))

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

def Laws.set_inside(img, xx, yy, color, h_in):
  match img:
    case Img.Raster{+ww, +hh, +px}:
      +hx = {ras.hx(ww, hh, xx, yy, h_in) : {Nat.is_lt(U32.to_nat(xx), U32.to_nat(ww)) == True{} : Bool}}
      +hy = {ras.hy(ww, hh, xx, yy, h_in) : {Nat.is_lt(U32.to_nat(yy), U32.to_nat(hh)) == True{} : Bool}}
      Equal.trans(Img.Raster, Img.set.x(U32.is_lt(xx, ww), ww, hh, px, xx, yy, color),
        Img.set.x(True{}, ww, hh, px, xx, yy, color),
        Img.raster(ww, hh, List.set(&2, U32, px, Laws.spot(ww, xx, yy), color)),
        Equal.cong(Bool, Img.Raster, bb => Img.set.x(bb, ww, hh, px, xx, yy, color), U32.is_lt(xx, ww), True{},
          M2.ras.lt(xx, ww, hx)),
        Equal.trans(Img.Raster, Img.set.y(U32.is_lt(yy, hh), ww, hh, px, xx, yy, color),
          Img.set.y(True{}, ww, hh, px, xx, yy, color),
          Img.raster(ww, hh, List.set(&2, U32, px, Laws.spot(ww, xx, yy), color)),
          Equal.cong(Bool, Img.Raster, bb => Img.set.y(bb, ww, hh, px, xx, yy, color), U32.is_lt(yy, hh), True{},
            M2.ras.lt(yy, hh, hy)),
          Equal.cong(List<&2, U32>, Img.Raster, qs => Img.raster(ww, hh, qs),
            Img.set.rows(U32.to_nat(yy), px, U32.to_nat(ww), U32.to_nat(xx), color),
            List.set(&2, U32, px, Laws.spot(ww, xx, yy), color),
            M4.set_rows(U32.to_nat(yy), px, U32.to_nat(ww), U32.to_nat(xx), color))))

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
