# An Adam7 picture (PNG section 8.2) is put back together from its seven
# passes by `Png.a7.merge`, which a7.go applies to the passes it reads. For
# passes of the sizes section 8.2 gives a w by h image, the merge is a w by
# h grid, and every sample of every pass lands where the Adam7 matrix puts
# it:
#
#   1 6 4 6 2 6 4 6
#   7 7 7 7 7 7 7 7
#   5 6 5 6 5 6 5 6
#   7 7 7 7 7 7 7 7
#   3 6 4 6 3 6 4 6
#   7 7 7 7 7 7 7 7
#   5 6 5 6 5 6 5 6
#   7 7 7 7 7 7 7 7
#
# Sample (i, k) of pass 1 is at (8i, 8k), of pass 2 at (8i + 4, 8k), of
# pass 3 at (4i, 8k + 4), of pass 4 at (4i + 2, 4k), of pass 5 at
# (2i, 4k + 2), of pass 6 at (2i + 1, 2k), and of pass 7 at (i, 2k + 1).
# These cover every place of the image once. The laws write 2n as
# Nat.double(n). That pass.read gives the passes those sizes is not stated
# here; the corpus checks the decoded pictures against Pillow and ImageMagick.
import Base
import ../src/png.bend as Png
import ./defs/SizeBounds.bend as D2

# ceil(n / 2), as D2.half is floor(n / 2)
def spec.up(nn: Nat) -> Nat:
  match nn:
    case 0n:
      0n
    case 1n+pp:
      match pp:
        case 0n:
          1n
        case 1n+qq:
          1n+spec.up(qq)

# exactly h rows of w samples each
def spec.rows.of(+ww: Nat, hh: Nat, rs: List<&2, List<&2, U32>>) -> Bool:
  match hh rs:
    case 0n Nil{}:
      True{}
    case 0n _r <> _t:
      False{}
    case 1n+_p Nil{}:
      False{}
    case 1n+pp r <> tl:
      Bool.and(Nat.is_eq(List.length(&2, U32, r), ww), spec.rows.of(ww, pp, tl))

# a w by h picture as rows, as pass.read gives it: no rows when w is 0,
# h rows of w samples otherwise
def spec.grid(ww: Nat, hh: Nat, rs: List<&2, List<&2, U32>>) -> Bool:
  match ww:
    case 0n:
      List.is_empty(&2, List<&2, U32>, rs)
    case 1n+pw:
      spec.rows.of(1n+pw, hh, rs)

# row y, or no samples past the last row
def spec.row(rs: List<&2, List<&2, U32>>, nn: Nat) -> List<&2, U32>:
  match rs nn:
    case Nil{} _n:
      []
    case r <> _t 0n:
      r
    case _r <> tl 1n+pp:
      spec.row(tl, pp)

# sample x of a row, none past its end
def spec.nth(xs: List<&2, U32>, nn: Nat) -> Maybe<&2, U32>:
  match xs nn:
    case Nil{} _n:
      None{}
    case +hd <> _t 0n:
      Some{hd}
    case _h <> tl 1n+pp:
      spec.nth(tl, pp)

# the sample at column x of row y
def spec.at(rs: List<&2, List<&2, U32>>, xx: Nat, yy: Nat) -> Maybe<&2, U32>:
  spec.nth(spec.row(rs, yy), xx)

# LAW: passes of the sizes PNG section 8.2 gives a w by h image merge to a w by h picture
law png_a7_grid:
  for +ww: Nat
  for +hh: Nat
  for +r1: List<&2, List<&2, U32>>
  for +r2: List<&2, List<&2, U32>>
  for +r3: List<&2, List<&2, U32>>
  for +r4: List<&2, List<&2, U32>>
  for +r5: List<&2, List<&2, U32>>
  for +r6: List<&2, List<&2, U32>>
  for +r7: List<&2, List<&2, U32>>
  for +g1: {spec.grid(spec.up(spec.up(spec.up(ww))), spec.up(spec.up(spec.up(hh))), r1) == True{} : Bool}
  for +g2: {spec.grid(D2.half(spec.up(spec.up(ww))), spec.up(spec.up(spec.up(hh))), r2) == True{} : Bool}
  for +g3: {spec.grid(spec.up(spec.up(ww)), D2.half(spec.up(spec.up(hh))), r3) == True{} : Bool}
  for +g4: {spec.grid(D2.half(spec.up(ww)), spec.up(spec.up(hh)), r4) == True{} : Bool}
  for +g5: {spec.grid(spec.up(ww), D2.half(spec.up(hh)), r5) == True{} : Bool}
  for +g6: {spec.grid(D2.half(ww), spec.up(hh), r6) == True{} : Bool}
  for +g7: {spec.grid(ww, D2.half(hh), r7) == True{} : Bool}
  {spec.grid(ww, hh, Png.a7.merge(r1, r2, r3, r4, r5, r6, r7)) == True{} : Bool}

# LAW: with passes of the section 8.2 sizes, sample (i, k) of pass 1 is at (8i, 8k)
law png_a7_pass1:
  for +ww: Nat
  for +hh: Nat
  for +r1: List<&2, List<&2, U32>>
  for +r2: List<&2, List<&2, U32>>
  for +r3: List<&2, List<&2, U32>>
  for +r4: List<&2, List<&2, U32>>
  for +r5: List<&2, List<&2, U32>>
  for +r6: List<&2, List<&2, U32>>
  for +r7: List<&2, List<&2, U32>>
  for +g1: {spec.grid(spec.up(spec.up(spec.up(ww))), spec.up(spec.up(spec.up(hh))), r1) == True{} : Bool}
  for +g2: {spec.grid(D2.half(spec.up(spec.up(ww))), spec.up(spec.up(spec.up(hh))), r2) == True{} : Bool}
  for +g3: {spec.grid(spec.up(spec.up(ww)), D2.half(spec.up(spec.up(hh))), r3) == True{} : Bool}
  for +g4: {spec.grid(D2.half(spec.up(ww)), spec.up(spec.up(hh)), r4) == True{} : Bool}
  for +g5: {spec.grid(spec.up(ww), D2.half(spec.up(hh)), r5) == True{} : Bool}
  for +g6: {spec.grid(D2.half(ww), spec.up(hh), r6) == True{} : Bool}
  for +g7: {spec.grid(ww, D2.half(hh), r7) == True{} : Bool}
  for +ii: Nat
  for +kk: Nat
  {spec.at(Png.a7.merge(r1, r2, r3, r4, r5, r6, r7), Nat.double(Nat.double(Nat.double(ii))),
    Nat.double(Nat.double(Nat.double(kk)))) == spec.at(r1, ii, kk) : Maybe<&2, U32>}

# LAW: with passes of the section 8.2 sizes, sample (i, k) of pass 2 is at (8i + 4, 8k)
law png_a7_pass2:
  for +ww: Nat
  for +hh: Nat
  for +r1: List<&2, List<&2, U32>>
  for +r2: List<&2, List<&2, U32>>
  for +r3: List<&2, List<&2, U32>>
  for +r4: List<&2, List<&2, U32>>
  for +r5: List<&2, List<&2, U32>>
  for +r6: List<&2, List<&2, U32>>
  for +r7: List<&2, List<&2, U32>>
  for +g1: {spec.grid(spec.up(spec.up(spec.up(ww))), spec.up(spec.up(spec.up(hh))), r1) == True{} : Bool}
  for +g2: {spec.grid(D2.half(spec.up(spec.up(ww))), spec.up(spec.up(spec.up(hh))), r2) == True{} : Bool}
  for +g3: {spec.grid(spec.up(spec.up(ww)), D2.half(spec.up(spec.up(hh))), r3) == True{} : Bool}
  for +g4: {spec.grid(D2.half(spec.up(ww)), spec.up(spec.up(hh)), r4) == True{} : Bool}
  for +g5: {spec.grid(spec.up(ww), D2.half(spec.up(hh)), r5) == True{} : Bool}
  for +g6: {spec.grid(D2.half(ww), spec.up(hh), r6) == True{} : Bool}
  for +g7: {spec.grid(ww, D2.half(hh), r7) == True{} : Bool}
  for +ii: Nat
  for +kk: Nat
  {spec.at(Png.a7.merge(r1, r2, r3, r4, r5, r6, r7), Nat.double(Nat.double(1n+Nat.double(ii))),
    Nat.double(Nat.double(Nat.double(kk)))) == spec.at(r2, ii, kk) : Maybe<&2, U32>}

# LAW: with passes of the section 8.2 sizes, sample (i, k) of pass 3 is at (4i, 8k + 4)
law png_a7_pass3:
  for +ww: Nat
  for +hh: Nat
  for +r1: List<&2, List<&2, U32>>
  for +r2: List<&2, List<&2, U32>>
  for +r3: List<&2, List<&2, U32>>
  for +r4: List<&2, List<&2, U32>>
  for +r5: List<&2, List<&2, U32>>
  for +r6: List<&2, List<&2, U32>>
  for +r7: List<&2, List<&2, U32>>
  for +g1: {spec.grid(spec.up(spec.up(spec.up(ww))), spec.up(spec.up(spec.up(hh))), r1) == True{} : Bool}
  for +g2: {spec.grid(D2.half(spec.up(spec.up(ww))), spec.up(spec.up(spec.up(hh))), r2) == True{} : Bool}
  for +g3: {spec.grid(spec.up(spec.up(ww)), D2.half(spec.up(spec.up(hh))), r3) == True{} : Bool}
  for +g4: {spec.grid(D2.half(spec.up(ww)), spec.up(spec.up(hh)), r4) == True{} : Bool}
  for +g5: {spec.grid(spec.up(ww), D2.half(spec.up(hh)), r5) == True{} : Bool}
  for +g6: {spec.grid(D2.half(ww), spec.up(hh), r6) == True{} : Bool}
  for +g7: {spec.grid(ww, D2.half(hh), r7) == True{} : Bool}
  for +ii: Nat
  for +kk: Nat
  {spec.at(Png.a7.merge(r1, r2, r3, r4, r5, r6, r7), Nat.double(Nat.double(ii)),
    Nat.double(Nat.double(1n+Nat.double(kk)))) == spec.at(r3, ii, kk) : Maybe<&2, U32>}

# LAW: with passes of the section 8.2 sizes, sample (i, k) of pass 4 is at (4i + 2, 4k)
law png_a7_pass4:
  for +ww: Nat
  for +hh: Nat
  for +r1: List<&2, List<&2, U32>>
  for +r2: List<&2, List<&2, U32>>
  for +r3: List<&2, List<&2, U32>>
  for +r4: List<&2, List<&2, U32>>
  for +r5: List<&2, List<&2, U32>>
  for +r6: List<&2, List<&2, U32>>
  for +r7: List<&2, List<&2, U32>>
  for +g1: {spec.grid(spec.up(spec.up(spec.up(ww))), spec.up(spec.up(spec.up(hh))), r1) == True{} : Bool}
  for +g2: {spec.grid(D2.half(spec.up(spec.up(ww))), spec.up(spec.up(spec.up(hh))), r2) == True{} : Bool}
  for +g3: {spec.grid(spec.up(spec.up(ww)), D2.half(spec.up(spec.up(hh))), r3) == True{} : Bool}
  for +g4: {spec.grid(D2.half(spec.up(ww)), spec.up(spec.up(hh)), r4) == True{} : Bool}
  for +g5: {spec.grid(spec.up(ww), D2.half(spec.up(hh)), r5) == True{} : Bool}
  for +g6: {spec.grid(D2.half(ww), spec.up(hh), r6) == True{} : Bool}
  for +g7: {spec.grid(ww, D2.half(hh), r7) == True{} : Bool}
  for +ii: Nat
  for +kk: Nat
  {spec.at(Png.a7.merge(r1, r2, r3, r4, r5, r6, r7), Nat.double(1n+Nat.double(ii)),
    Nat.double(Nat.double(kk))) == spec.at(r4, ii, kk) : Maybe<&2, U32>}

# LAW: with passes of the section 8.2 sizes, sample (i, k) of pass 5 is at (2i, 4k + 2)
law png_a7_pass5:
  for +ww: Nat
  for +hh: Nat
  for +r1: List<&2, List<&2, U32>>
  for +r2: List<&2, List<&2, U32>>
  for +r3: List<&2, List<&2, U32>>
  for +r4: List<&2, List<&2, U32>>
  for +r5: List<&2, List<&2, U32>>
  for +r6: List<&2, List<&2, U32>>
  for +r7: List<&2, List<&2, U32>>
  for +g1: {spec.grid(spec.up(spec.up(spec.up(ww))), spec.up(spec.up(spec.up(hh))), r1) == True{} : Bool}
  for +g2: {spec.grid(D2.half(spec.up(spec.up(ww))), spec.up(spec.up(spec.up(hh))), r2) == True{} : Bool}
  for +g3: {spec.grid(spec.up(spec.up(ww)), D2.half(spec.up(spec.up(hh))), r3) == True{} : Bool}
  for +g4: {spec.grid(D2.half(spec.up(ww)), spec.up(spec.up(hh)), r4) == True{} : Bool}
  for +g5: {spec.grid(spec.up(ww), D2.half(spec.up(hh)), r5) == True{} : Bool}
  for +g6: {spec.grid(D2.half(ww), spec.up(hh), r6) == True{} : Bool}
  for +g7: {spec.grid(ww, D2.half(hh), r7) == True{} : Bool}
  for +ii: Nat
  for +kk: Nat
  {spec.at(Png.a7.merge(r1, r2, r3, r4, r5, r6, r7), Nat.double(ii), Nat.double(1n+Nat.double(kk))) ==
    spec.at(r5, ii, kk) : Maybe<&2, U32>}

# LAW: with passes of the section 8.2 sizes, sample (i, k) of pass 6 is at (2i + 1, 2k)
law png_a7_pass6:
  for +ww: Nat
  for +hh: Nat
  for +r1: List<&2, List<&2, U32>>
  for +r2: List<&2, List<&2, U32>>
  for +r3: List<&2, List<&2, U32>>
  for +r4: List<&2, List<&2, U32>>
  for +r5: List<&2, List<&2, U32>>
  for +r6: List<&2, List<&2, U32>>
  for +r7: List<&2, List<&2, U32>>
  for +g1: {spec.grid(spec.up(spec.up(spec.up(ww))), spec.up(spec.up(spec.up(hh))), r1) == True{} : Bool}
  for +g2: {spec.grid(D2.half(spec.up(spec.up(ww))), spec.up(spec.up(spec.up(hh))), r2) == True{} : Bool}
  for +g3: {spec.grid(spec.up(spec.up(ww)), D2.half(spec.up(spec.up(hh))), r3) == True{} : Bool}
  for +g4: {spec.grid(D2.half(spec.up(ww)), spec.up(spec.up(hh)), r4) == True{} : Bool}
  for +g5: {spec.grid(spec.up(ww), D2.half(spec.up(hh)), r5) == True{} : Bool}
  for +g6: {spec.grid(D2.half(ww), spec.up(hh), r6) == True{} : Bool}
  for +g7: {spec.grid(ww, D2.half(hh), r7) == True{} : Bool}
  for +ii: Nat
  for +kk: Nat
  {spec.at(Png.a7.merge(r1, r2, r3, r4, r5, r6, r7), 1n+Nat.double(ii), Nat.double(kk)) == spec.at(r6, ii, kk) :
    Maybe<&2, U32>}

# LAW: with passes of the section 8.2 sizes, sample (i, k) of pass 7 is at (i, 2k + 1)
law png_a7_pass7:
  for +ww: Nat
  for +hh: Nat
  for +r1: List<&2, List<&2, U32>>
  for +r2: List<&2, List<&2, U32>>
  for +r3: List<&2, List<&2, U32>>
  for +r4: List<&2, List<&2, U32>>
  for +r5: List<&2, List<&2, U32>>
  for +r6: List<&2, List<&2, U32>>
  for +r7: List<&2, List<&2, U32>>
  for +g1: {spec.grid(spec.up(spec.up(spec.up(ww))), spec.up(spec.up(spec.up(hh))), r1) == True{} : Bool}
  for +g2: {spec.grid(D2.half(spec.up(spec.up(ww))), spec.up(spec.up(spec.up(hh))), r2) == True{} : Bool}
  for +g3: {spec.grid(spec.up(spec.up(ww)), D2.half(spec.up(spec.up(hh))), r3) == True{} : Bool}
  for +g4: {spec.grid(D2.half(spec.up(ww)), spec.up(spec.up(hh)), r4) == True{} : Bool}
  for +g5: {spec.grid(spec.up(ww), D2.half(spec.up(hh)), r5) == True{} : Bool}
  for +g6: {spec.grid(D2.half(ww), spec.up(hh), r6) == True{} : Bool}
  for +g7: {spec.grid(ww, D2.half(hh), r7) == True{} : Bool}
  for +ii: Nat
  for +kk: Nat
  {spec.at(Png.a7.merge(r1, r2, r3, r4, r5, r6, r7), ii, 1n+Nat.double(kk)) == spec.at(r7, ii, kk) :
    Maybe<&2, U32>}
