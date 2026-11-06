# the row walks of main.bend (skip.rows, take.rows, set.rows, fill.go) are
# the list operations at the row-major index they never build
import Base
import ../../main.bend as Img
import ./BasicFacts.bend as M1
import ./ListTakeDrop.bend as M2

# ---- drop, take and set at a sum ----

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
      {==}
    case _hd <> _tl 0n:
      {==}
    case _hd <> tl 1n+qq:
      drop_drop(tl, qq, bb)

# taking a + b is taking a, then b of what follows
law take_add:
  for xs: List<&2, U32>
  for aa: Nat
  for +bb: Nat
  {List.take(&2, U32, xs, Nat.add(aa, bb)) ==
    List.append(&2, U32, List.take(&2, U32, xs, aa), List.take(&2, U32, List.drop(&2, U32, xs, aa), bb)) :
    List<&2, U32>}

# the proof of take_add
def take_add(xs, aa, bb):
  match xs aa:
    case Nil{} _aa:
      {==}
    case _hd <> _tl 0n:
      {==}
    case +hd <> tl 1n+qq:
      Equal.cong(List<&2, U32>, List<&2, U32>, ys => {hd <> ys : List<&2, U32>},
        List.take(&2, U32, tl, Nat.add(qq, bb)),
        List.append(&2, U32, List.take(&2, U32, tl, qq), List.take(&2, U32, List.drop(&2, U32, tl, qq), bb)),
        take_add(tl, qq, bb))

# setting at a + b is setting at b after the first a
law set_add:
  for xs: List<&2, U32>
  for aa: Nat
  for +bb: Nat
  for +cc: U32
  {List.set(&2, U32, xs, Nat.add(aa, bb), cc) ==
    List.append(&2, U32, List.take(&2, U32, xs, aa), List.set(&2, U32, List.drop(&2, U32, xs, aa), bb, cc)) :
    List<&2, U32>}

# the proof of set_add
def set_add(xs, aa, bb, cc):
  match xs aa:
    case Nil{} _aa:
      {==}
    case _hd <> _tl 0n:
      {==}
    case +hd <> tl 1n+qq:
      Equal.cong(List<&2, U32>, List<&2, U32>, ys => {hd <> ys : List<&2, U32>},
        List.set(&2, U32, tl, Nat.add(qq, bb), cc),
        List.append(&2, U32, List.take(&2, U32, tl, qq), List.set(&2, U32, List.drop(&2, U32, tl, qq), bb, cc)),
        set_add(tl, qq, bb, cc))

# ---- the row walks ----

# skip.rows drops n rows of w: n * w samples
law skip_drop:
  for nn: Nat
  for +px: List<&2, U32>
  for +ww: Nat
  {Img.skip.rows(nn, px, ww) == List.drop(&2, U32, px, Nat.mul(nn, ww)) : List<&2, U32>}

# the proof of skip_drop
def skip_drop(nn, px, ww):
  match nn:
    case 0n:
      Equal.sym(List<&2, U32>, List.drop(&2, U32, px, 0n), px, drop_zero(px))
    case 1n+(+pp):
      match px:
        case Nil{}:
          {==}
        case +hd <> +tl:
          +xs = {hd <> tl : List<&2, U32>}
          Equal.trans(List<&2, U32>, Img.skip.rows(pp, List.drop(&2, U32, xs, ww), ww),
            List.drop(&2, U32, List.drop(&2, U32, xs, ww), Nat.mul(pp, ww)),
            List.drop(&2, U32, xs, Nat.add(ww, Nat.mul(pp, ww))),
            skip_drop(pp, List.drop(&2, U32, xs, ww), ww), drop_drop(xs, ww, Nat.mul(pp, ww)))

# take.rows takes n rows of w: n * w samples
law take_rows:
  for nn: Nat
  for +px: List<&2, U32>
  for +ww: Nat
  {Img.take.rows(nn, px, ww) == List.take(&2, U32, px, Nat.mul(nn, ww)) : List<&2, U32>}

# the proof of take_rows
def take_rows(nn, px, ww):
  match nn:
    case 0n:
      match px:
        case Nil{}:
          {==}
        case _hd <> _tl:
          {==}
    case 1n+(+pp):
      match px:
        case Nil{}:
          {==}
        case +hd <> +tl:
          +xs = {hd <> tl : List<&2, U32>}
          +pw = Nat.mul(pp, ww)
          Equal.trans(List<&2, U32>,
            List.append(&2, U32, List.take(&2, U32, xs, ww), Img.take.rows(pp, List.drop(&2, U32, xs, ww), ww)),
            List.append(&2, U32, List.take(&2, U32, xs, ww), List.take(&2, U32, List.drop(&2, U32, xs, ww), pw)),
            List.take(&2, U32, xs, Nat.add(ww, pw)),
            Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.append(&2, U32, List.take(&2, U32, xs, ww), ys),
              Img.take.rows(pp, List.drop(&2, U32, xs, ww), ww), List.take(&2, U32, List.drop(&2, U32, xs, ww), pw),
              take_rows(pp, List.drop(&2, U32, xs, ww), ww)),
            Equal.sym(List<&2, U32>, List.take(&2, U32, xs, Nat.add(ww, pw)),
              List.append(&2, U32, List.take(&2, U32, xs, ww), List.take(&2, U32, List.drop(&2, U32, xs, ww), pw)),
              take_add(xs, ww, pw)))

# set.rows sets sample n * w + x
law set_rows:
  for nn: Nat
  for +px: List<&2, U32>
  for +ww: Nat
  for +xx: Nat
  for +cc: U32
  {Img.set.rows(nn, px, ww, xx, cc) == List.set(&2, U32, px, Nat.add(Nat.mul(nn, ww), xx), cc) : List<&2, U32>}

# the proof of set_rows
def set_rows(nn, px, ww, xx, cc):
  match nn:
    case 0n:
      {==}
    case 1n+(+pp):
      match px:
        case Nil{}:
          {==}
        case +hd <> +tl:
          +xs = {hd <> tl : List<&2, U32>}
          +pw = Nat.mul(pp, ww)
          +rs = List.drop(&2, U32, xs, ww)
          Equal.trans(List<&2, U32>,
            List.append(&2, U32, List.take(&2, U32, xs, ww), Img.set.rows(pp, rs, ww, xx, cc)),
            List.append(&2, U32, List.take(&2, U32, xs, ww), List.set(&2, U32, rs, Nat.add(pw, xx), cc)),
            List.set(&2, U32, xs, Nat.add(Nat.add(ww, pw), xx), cc),
            Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.append(&2, U32, List.take(&2, U32, xs, ww), ys),
              Img.set.rows(pp, rs, ww, xx, cc), List.set(&2, U32, rs, Nat.add(pw, xx), cc),
              set_rows(pp, rs, ww, xx, cc)),
            Equal.trans(List<&2, U32>,
              List.append(&2, U32, List.take(&2, U32, xs, ww), List.set(&2, U32, rs, Nat.add(pw, xx), cc)),
              List.set(&2, U32, xs, Nat.add(ww, Nat.add(pw, xx)), cc),
              List.set(&2, U32, xs, Nat.add(Nat.add(ww, pw), xx), cc),
              Equal.sym(List<&2, U32>, List.set(&2, U32, xs, Nat.add(ww, Nat.add(pw, xx)), cc),
                List.append(&2, U32, List.take(&2, U32, xs, ww), List.set(&2, U32, rs, Nat.add(pw, xx), cc)),
                set_add(xs, ww, Nat.add(pw, xx), cc)),
              Equal.cong(Nat, List<&2, U32>, kk => List.set(&2, U32, xs, kk, cc), Nat.add(ww, Nat.add(pw, xx)),
                Nat.add(Nat.add(ww, pw), xx), Equal.sym(Nat, Nat.add(Nat.add(ww, pw), xx), Nat.add(ww, Nat.add(pw, xx)),
                  M1.ras.add_assoc(ww, pw, xx)))))

# reading x after n rows of w reads sample n * w + x
law get_rows:
  for +nn: Nat
  for +px: List<&2, U32>
  for +ww: Nat
  for +xx: Nat
  {List.get(&2, U32, Img.skip.rows(nn, px, ww), xx) == List.get(&2, U32, px, Nat.add(Nat.mul(nn, ww), xx)) :
    Maybe<&2, U32>}

# the proof of get_rows
def get_rows(nn, px, ww, xx):
  Equal.trans(Maybe<&2, U32>, List.get(&2, U32, Img.skip.rows(nn, px, ww), xx),
    List.get(&2, U32, List.drop(&2, U32, px, Nat.mul(nn, ww)), xx), List.get(&2, U32, px, Nat.add(Nat.mul(nn, ww), xx)),
    Equal.cong(List<&2, U32>, Maybe<&2, U32>, ys => List.get(&2, U32, ys, xx), Img.skip.rows(nn, px, ww),
      List.drop(&2, U32, px, Nat.mul(nn, ww)), skip_drop(nn, px, ww)),
    M2.get_drop(px, Nat.mul(nn, ww), xx))

# dropping x after n rows of w drops n * w + x
law drop_rows:
  for +nn: Nat
  for +px: List<&2, U32>
  for +ww: Nat
  for +xx: Nat
  {List.drop(&2, U32, Img.skip.rows(nn, px, ww), xx) == List.drop(&2, U32, px, Nat.add(Nat.mul(nn, ww), xx)) :
    List<&2, U32>}

# the proof of drop_rows
def drop_rows(nn, px, ww, xx):
  Equal.trans(List<&2, U32>, List.drop(&2, U32, Img.skip.rows(nn, px, ww), xx),
    List.drop(&2, U32, List.drop(&2, U32, px, Nat.mul(nn, ww)), xx),
    List.drop(&2, U32, px, Nat.add(Nat.mul(nn, ww), xx)),
    Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.drop(&2, U32, ys, xx), Img.skip.rows(nn, px, ww),
      List.drop(&2, U32, px, Nat.mul(nn, ww)), skip_drop(nn, px, ww)),
    drop_drop(px, Nat.mul(nn, ww), xx))

# ---- a solid picture's samples ----

# a copies of c, then b copies, are a + b copies
law rep_add:
  for aa: Nat
  for +bb: Nat
  for +cc: U32
  {List.append(&2, U32, List.replicate(U32, aa, cc), List.replicate(U32, bb, cc)) ==
    List.replicate(U32, Nat.add(aa, bb), cc) : List<&2, U32>}

# the proof of rep_add
def rep_add(aa, bb, cc):
  match aa:
    case 0n:
      {==}
    case 1n+(+pp):
      Equal.cong(List<&2, U32>, List<&2, U32>, ys => {cc <> ys : List<&2, U32>},
        List.append(&2, U32, List.replicate(U32, pp, cc), List.replicate(U32, bb, cc)),
        List.replicate(U32, Nat.add(pp, bb), cc), rep_add(pp, bb, cc))

# w rows of h copies of c are w * h copies
law fill_rep:
  for wn: Nat
  for +hn: Nat
  for +cc: U32
  {Img.fill.go(wn, hn, cc) == List.replicate(U32, Nat.mul(wn, hn), cc) : List<&2, U32>}

# the proof of fill_rep
def fill_rep(wn, hn, cc):
  match wn:
    case 0n:
      {==}
    case 1n+(+pp):
      Equal.trans(List<&2, U32>, List.append(&2, U32, List.replicate(U32, hn, cc), Img.fill.go(pp, hn, cc)),
        List.append(&2, U32, List.replicate(U32, hn, cc), List.replicate(U32, Nat.mul(pp, hn), cc)),
        List.replicate(U32, Nat.add(hn, Nat.mul(pp, hn)), cc),
        Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.append(&2, U32, List.replicate(U32, hn, cc), ys),
          Img.fill.go(pp, hn, cc), List.replicate(U32, Nat.mul(pp, hn), cc), fill_rep(pp, hn, cc)),
        rep_add(hn, Nat.mul(pp, hn), cc))

# a solid picture's samples are w * h copies of its colour
law fill_px:
  for +wn: Nat
  for hn: Nat
  for +cc: U32
  {Img.fill.px(wn, hn, cc) == List.replicate(U32, Nat.mul(wn, hn), cc) : List<&2, U32>}

# the proof of fill_px
def fill_px(wn, hn, cc):
  match hn:
    case 0n:
      Equal.cong(Nat, List<&2, U32>, kk => List.replicate(U32, kk, cc), 0n, Nat.mul(wn, 0n),
        Equal.sym(Nat, Nat.mul(wn, 0n), 0n, M1.mul_zero(wn)))
    case 1n+(+pp):
      fill_rep(wn, 1n+pp, cc)
