# take, drop and append on lists, and min and subtraction on Nat
import Base
import ../../main.bend as Img
import ./BasicFacts.bend as M1
import ./SubtractionAndHuffmanWalk.bend as M2
import ./WordAddition.bend as M3

# ---- min and sub ----

# min(a, b) is a when a <= b
law min_of_le:
  for aa: Nat
  for bb: Nat
  for hh: {Nat.is_le(aa, bb) == True{} : Bool}
  {Nat.min(aa, bb) == aa : Nat}

# the proof of min_of_le
def min_of_le(aa, bb, hh):
  match aa bb:
    case 0n _bb:
      {==}
    case 1n+_pa 0n:
      Empty.absurd({0n == 1n+_pa : Nat}, M1.false_true(hh))
    case 1n+pa 1n+pb:
      Equal.cong(Nat, Nat, xx => 1n+xx, Nat.min(pa, pb), pa, min_of_le(pa, pb, hh))

# min(a, b) is b when a <= b is false
law min_of_gt:
  for aa: Nat
  for bb: Nat
  for hh: {Nat.is_le(aa, bb) == False{} : Bool}
  {Nat.min(aa, bb) == bb : Nat}

# the proof of min_of_gt
def min_of_gt(aa, bb, hh):
  match aa bb:
    case 0n _bb:
      Empty.absurd({0n == _bb : Nat}, M1.false_true(Equal.trans(Bool, False{}, Nat.is_le(0n, _bb), True{},
        Equal.sym(Bool, Nat.is_le(0n, _bb), False{}, hh), M1.le_zero(_bb))))
    case 1n+_pa 0n:
      {==}
    case 1n+pa 1n+pb:
      Equal.cong(Nat, Nat, xx => 1n+xx, Nat.min(pa, pb), pb, min_of_gt(pa, pb, hh))

# min(a, b) <= b
law min_le_r:
  for aa: Nat
  for bb: Nat
  {Nat.is_le(Nat.min(aa, bb), bb) == True{} : Bool}

# the proof of min_le_r
def min_le_r(aa, bb):
  match aa bb:
    case 0n _bb:
      M1.le_zero(_bb)
    case 1n+_pa 0n:
      {==}
    case 1n+pa 1n+pb:
      min_le_r(pa, pb)

# 0 < a - b gives b < a
law sub_pos:
  for aa: Nat
  for bb: Nat
  for hh: {Nat.is_lt(0n, Nat.sub(aa, bb)) == True{} : Bool}
  {Nat.is_lt(bb, aa) == True{} : Bool}

# the proof of sub_pos
def sub_pos(aa, bb, hh):
  match aa bb:
    case 0n 0n:
      Empty.absurd({False{} == True{} : Bool}, M1.false_true(hh))
    case 0n 1n+_pb:
      Empty.absurd({False{} == True{} : Bool}, M1.false_true(hh))
    case 1n+_pa 0n:
      {==}
    case 1n+pa 1n+pb:
      sub_pos(pa, pb, hh)

# ---- take, drop and append ----

# element k after dropping m is element m + k
law get_drop:
  for xs: List<&2, U32>
  for mm: Nat
  for -kk: Nat
  {List.get(&2, U32, List.drop(&2, U32, xs, mm), kk) == List.get(&2, U32, xs, Nat.add(mm, kk)) : Maybe<&2, U32>}

# the proof of get_drop
def get_drop(xs, mm, kk):
  match xs mm:
    case Nil{} _mm:
      {==}
    case _hd <> _tl 0n:
      {==}
    case _hd <> tl 1n+qq:
      get_drop(tl, qq, kk)

# m + k <= length + g gives k <= length after dropping m, + g
law drop_le:
  for xs: List<&2, U32>
  for mm: Nat
  for +kk: Nat
  for +gg: Nat
  for hh: {Nat.is_le(Nat.add(mm, kk), Nat.add(List.length(&2, U32, xs), gg)) == True{} : Bool}
  {Nat.is_le(kk, Nat.add(List.length(&2, U32, List.drop(&2, U32, xs, mm)), gg)) == True{} : Bool}

# the proof of drop_le
def drop_le(xs, mm, kk, gg, hh):
  match xs mm:
    case Nil{} 0n:
      hh
    case Nil{} 1n+(+qq):
      M3.le_add_r(kk, 1n+qq, gg, M1.le_rw_l(Nat.add(1n+qq, kk), Nat.add(kk, 1n+qq), gg, M1.ras.add_comm(1n+qq, kk), hh))
    case _hd <> _tl 0n:
      hh
    case _hd <> tl 1n+qq:
      drop_le(tl, qq, kk, gg, hh)

# the length of an append is the sum of the lengths
law len_append:
  for aa: List<&2, U32>
  for -bb: List<&2, U32>
  {List.length(&2, U32, List.append(&2, U32, aa, bb)) ==
    Nat.add(List.length(&2, U32, aa), List.length(&2, U32, bb)) : Nat}

# the proof of len_append
def len_append(aa, bb):
  match aa:
    case Nil{}:
      {==}
    case _hd <> tl:
      Equal.cong(Nat, Nat, xx => 1n+xx, List.length(&2, U32, List.append(&2, U32, tl, bb)),
        Nat.add(List.length(&2, U32, tl), List.length(&2, U32, bb)), len_append(tl, bb))

# taking n <= length elements takes n
law len_take:
  for xs: List<&2, U32>
  for nn: Nat
  for hh: {Nat.is_le(nn, List.length(&2, U32, xs)) == True{} : Bool}
  {List.length(&2, U32, List.take(&2, U32, xs, nn)) == nn : Nat}

# the proof of len_take
def len_take(xs, nn, hh):
  match xs nn:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+_qq:
      Empty.absurd({0n == 1n+_qq : Nat}, M1.false_true(hh))
    case _hd <> _tl 0n:
      {==}
    case _hd <> tl 1n+qq:
      Equal.cong(Nat, Nat, xx => 1n+xx, List.length(&2, U32, List.take(&2, U32, tl, qq)), qq, len_take(tl, qq, hh))

# below n, the first n elements followed by anything read as the list
law get_append_take:
  for xs: List<&2, U32>
  for nn: Nat
  for kk: Nat
  for -rest: List<&2, U32>
  for hk: {Nat.is_lt(kk, nn) == True{} : Bool}
  for hl: {Nat.is_le(nn, List.length(&2, U32, xs)) == True{} : Bool}
  {List.get(&2, U32, List.append(&2, U32, List.take(&2, U32, xs, nn), rest), kk) == List.get(&2, U32, xs, kk) :
    Maybe<&2, U32>}

# the proof of get_append_take
def get_append_take(xs, nn, kk, rest, hk, hl):
  match xs nn kk:
    case _xs 0n _kk:
      Empty.absurd({List.get(&2, U32, List.append(&2, U32, List.take(&2, U32, _xs, 0n), rest), _kk) ==
        List.get(&2, U32, _xs, _kk) : Maybe<&2, U32>}, M1.false_true(
        Equal.trans(Bool, False{}, Nat.is_lt(_kk, 0n), True{}, M1.lt_zero_false(_kk), hk)))
    case Nil{} 1n+_qq _kk:
      Empty.absurd({List.get(&2, U32, List.append(&2, U32, List.take(&2, U32, Nil{}, 1n+_qq), rest), _kk) ==
        List.get(&2, U32, Nil{}, _kk) : Maybe<&2, U32>}, M1.false_true(hl))
    case _hd <> _tl 1n+_qq 0n:
      {==}
    case _hd <> tl 1n+qq 1n+pk:
      get_append_take(tl, qq, pk, rest, hk, hl)

# past the first n elements (n <= length), the rest reads on
law get_append_skip:
  for xs: List<&2, U32>
  for nn: Nat
  for -kk: Nat
  for -rest: List<&2, U32>
  for hl: {Nat.is_le(nn, List.length(&2, U32, xs)) == True{} : Bool}
  {List.get(&2, U32, List.append(&2, U32, List.take(&2, U32, xs, nn), rest), Nat.add(nn, kk)) ==
    List.get(&2, U32, rest, kk) : Maybe<&2, U32>}

# the proof of get_append_skip
def get_append_skip(xs, nn, kk, rest, hl):
  match xs nn:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+_qq:
      Empty.absurd({List.get(&2, U32, List.append(&2, U32, List.take(&2, U32, Nil{}, 1n+_qq), rest),
        Nat.add(1n+_qq, kk)) == List.get(&2, U32, rest, kk) : Maybe<&2, U32>}, M1.false_true(hl))
    case _hd <> _tl 0n:
      {==}
    case _hd <> tl 1n+qq:
      get_append_skip(tl, qq, kk, rest, hl)

# u.min read as Nat, once the comparison is named
def ras.umin.pick(
  le: Bool,
  +aa: U32,
  +bb: U32,
  ee: {U32.is_le(aa, bb) == le : Bool}
) -> {U32.to_nat(Img.u.min.pick(le, aa, bb)) == Nat.min(U32.to_nat(aa), U32.to_nat(bb)) : Nat}:
  match le:
    case True{}:
      Equal.sym(Nat, Nat.min(U32.to_nat(aa), U32.to_nat(bb)), U32.to_nat(aa), min_of_le(U32.to_nat(aa),
        U32.to_nat(bb),
        Equal.trans(Bool, Nat.is_le(U32.to_nat(aa), U32.to_nat(bb)), U32.is_le(aa, bb), True{},
          Equal.sym(Bool, U32.is_le(aa, bb), Nat.is_le(U32.to_nat(aa), U32.to_nat(bb)), M2.u32_le(aa, bb)), ee)))
    case False{}:
      Equal.sym(Nat, Nat.min(U32.to_nat(aa), U32.to_nat(bb)), U32.to_nat(bb), min_of_gt(U32.to_nat(aa),
        U32.to_nat(bb),
        Equal.trans(Bool, Nat.is_le(U32.to_nat(aa), U32.to_nat(bb)), U32.is_le(aa, bb), False{},
          Equal.sym(Bool, U32.is_le(aa, bb), Nat.is_le(U32.to_nat(aa), U32.to_nat(bb)), M2.u32_le(aa, bb)), ee)))

# u.min read as Nat
def ras.umin(+aa: U32, +bb: U32) -> {U32.to_nat(Img.u.min(aa, bb)) == Nat.min(U32.to_nat(aa), U32.to_nat(bb)) : Nat}:
  ras.umin.pick(U32.is_le(aa, bb), aa, bb, {==})
