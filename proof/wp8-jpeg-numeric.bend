# proof/wp8-jpeg-numeric: lemmas about the JPEG marker walk that IMG-JPG-2's
# refusal laws rest on. Each is a law proved here; PROOF.bend imports this
# file, so the gate checks it.
import Base
import ../src/jpeg.bend as Jpeg
import ./u32.bend as U32L

# walking two byte lists one after the other is walking the second from
# where the first left off
law walk_app:
  for xs: List<&2, U32>
  for +ys: List<&2, U32>
  for st: Jpeg.St
  {Jpeg.decode.walk(List.append(&2, U32, xs, ys), st) == Jpeg.decode.walk(ys, Jpeg.decode.walk(xs, st)) : Jpeg.St}

# the proof of walk_app, by induction on the first list
def walk_app(xs, ys, st):
  match xs:
    case Nil{}:
      {==}
    case hd <> tl:
      walk_app(tl, ys, Jpeg.decode.step(hd, st))

# a stopped walk stays where it stopped, whatever bytes follow
law walk_stop:
  for xs: List<&2, U32>
  for +fr: Jpeg.Frame
  for +sc: Jpeg.Scan
  for +tb: Jpeg.Tabs
  for +en: List<&2, U32>
  for +ri: U32
  for +kd: U32
  for +bd: U32
  {Jpeg.decode.walk(xs, Jpeg.St{Jpeg.Stop{}, fr, sc, tb, en, ri, kd, bd}) ==
    Jpeg.St{Jpeg.Stop{}, fr, sc, tb, en, ri, kd, bd} : Jpeg.St}

# the proof of walk_stop, by induction on the bytes
def walk_stop(xs, fr, sc, tb, en, ri, kd, bd):
  match xs:
    case Nil{}:
      {==}
    case _hd <> tl:
      walk_stop(tl, fr, sc, tb, en, ri, kd, bd)

# a factor of 1, 2 or 4 (the or IMG-JPG-2's allowed factors unfold to): a
# property of all three holds of it. The last test: 4, or nothing left.
law fac_elim4:
  for -pp: U32 -> Type
  for +ff: U32
  for b4: Bool
  for e4: {U32.is_eq(ff, 4) == b4 : Bool}
  for h_ok: {b4 == True{} : Bool}
  for p4: pp(4)
  pp(ff)

# the proof of fac_elim4
def fac_elim4(pp, ff, b4, e4, h_ok, p4):
  match b4:
    case True{}:
      es = Equal.sym(U32, ff, 4, U32L.ueq(ff, 4, e4))
      %es : pp(_)
      p4
    case False{}:
      Empty.absurd(pp(ff), U32L.false_true(h_ok))

# the middle test: 2, or on to 4
law fac_elim2:
  for -pp: U32 -> Type
  for +ff: U32
  for b2: Bool
  for e2: {U32.is_eq(ff, 2) == b2 : Bool}
  for h_ok: {Bool.or(b2, U32.is_eq(ff, 4)) == True{} : Bool}
  for p2: pp(2)
  for p4: pp(4)
  pp(ff)

# the proof of fac_elim2
def fac_elim2(pp, ff, b2, e2, h_ok, p2, p4):
  match b2:
    case True{}:
      es = Equal.sym(U32, ff, 2, U32L.ueq(ff, 2, e2))
      %es : pp(_)
      p2
    case False{}:
      fac_elim4(pp, ff, U32.is_eq(ff, 4), {==}, h_ok, p4)

# the first test: 1, or on to 2 and 4
law fac_elim:
  for -pp: U32 -> Type
  for +ff: U32
  for b1: Bool
  for e1: {U32.is_eq(ff, 1) == b1 : Bool}
  for h_ok: {Bool.or(b1, Bool.or(U32.is_eq(ff, 2), U32.is_eq(ff, 4))) == True{} : Bool}
  for p1: pp(1)
  for p2: pp(2)
  for p4: pp(4)
  pp(ff)

# the proof of fac_elim
def fac_elim(pp, ff, b1, e1, h_ok, p1, p2, p4):
  match b1:
    case True{}:
      es = Equal.sym(U32, ff, 1, U32L.ueq(ff, 1, e1))
      %es : pp(_)
      p1
    case False{}:
      fac_elim2(pp, ff, U32.is_eq(ff, 2), {==}, h_ok, p2, p4)
