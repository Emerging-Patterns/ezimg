# proofs of laws/InflateUptoKeepsBudget.bend: inflate.upto.go steps the
# reader exactly as inflate.go does, only failing it once it is past the
# budget, so an answer of some bytes is inflate.go's, and it passed the final
# length check. The reader's phase is split in full: a reader of an unknown
# phase other than done or failed leaves either walk stuck.
import Base
import ../src/inflate.bend as Inf
import ../laws/InflateUptoKeepsBudget.bend as Laws

# the Type a Maybe names for telling none from some: Unit for none
def none_ty(mm: Maybe<&2, List<&2, U32>>) -> Type:
  match mm:
    case None{}:
      Unit
    case Some{_xs}:
      Empty

# none is no answer of some bytes
def none_some(+ys: List<&2, U32>, ee: {None{} == Some{ys} : Maybe<&2, List<&2, U32>>}) -> Empty:
  %ee : none_ty(_)
  Unit{}

# the final check passed: the answer is the reader's output
def fin_out(
  zz: Bool,
  +out: List<&2, U32>,
  +ys: List<&2, U32>,
  ee: {Inf.inflate.upto.fin(zz, out) == Some{ys} : Maybe<&2, List<&2, U32>>}
) -> {Some{out} == Some{ys} : Maybe<&2, List<&2, U32>>}:
  match zz:
    case True{}:
      ee
    case False{}:
      Empty.absurd({Some{out} == Some{ys} : Maybe<&2, List<&2, U32>>}, none_some(ys, ee))

# the final check passed: it was true
def fin_ok(
  zz: Bool,
  +out: List<&2, U32>,
  +ys: List<&2, U32>,
  ee: {Inf.inflate.upto.fin(zz, out) == Some{ys} : Maybe<&2, List<&2, U32>>}
) -> {zz == True{} : Bool}:
  match zz:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, none_some(ys, ee))

# the length of some bytes, zero for none
def len.some(mm: Maybe<&2, List<&2, U32>>) -> Nat:
  match mm:
    case None{}:
      0n
    case Some{xs}:
      List.length(&2, U32, xs)

# the final check passed: the answer has at most the budget of bytes
def fin_within(
  +out: List<&2, U32>,
  +lim: Nat,
  +ys: List<&2, U32>,
  +ee: {Inf.inflate.upto.fin(Nat.is_le(List.length(&2, U32, out), lim), out) == Some{ys} : Maybe<&2, List<&2, U32>>}
) -> {Nat.is_le(List.length(&2, U32, ys), lim) == True{} : Bool}:
  +ck = Nat.is_le(List.length(&2, U32, out), lim)
  +el = Equal.cong(Maybe<&2, List<&2, U32>>, Nat, mm => len.some(mm), Some{out}, Some{ys}, fin_out(ck, out, ys, ee))
  Equal.trans(Bool, Nat.is_le(List.length(&2, U32, ys), lim), ck, True{},
    Equal.cong(Nat, Bool, nn => Nat.is_le(nn, lim), List.length(&2, U32, ys), List.length(&2, U32, out),
      Equal.sym(Nat, List.length(&2, U32, out), List.length(&2, U32, ys), el)),
    fin_ok(ck, out, ys, ee))

# a failed reader answers none, whatever bytes are left
def fail_none(
  xs: List<&2, U32>,
  +ys: List<&2, U32>,
  ee: {Inf.inflate.go(xs, Inf.st.fail()) == Some{ys} : Maybe<&2, List<&2, U32>>}
) -> Empty:
  match xs:
    case Nil{}:
      none_some(ys, ee)
    case Con{_b, _t}:
      none_some(ys, ee)

# a reader capped by `zz` that answers some bytes was not capped
def cap_some.at(
  zz: Bool,
  xs: List<&2, U32>,
  st: Inf.St,
  +ys: List<&2, U32>,
  ee: {Inf.inflate.go(xs, Inf.st.cap.at(zz, st)) == Some{ys} : Maybe<&2, List<&2, U32>>}
) -> {Inf.inflate.go(xs, st) == Some{ys} : Maybe<&2, List<&2, U32>>}:
  match zz:
    case False{}:
      ee
    case True{}:
      Empty.absurd({Inf.inflate.go(xs, st) == Some{ys} : Maybe<&2, List<&2, U32>>}, fail_none(xs, ys, ee))

# a capped reader that answers some bytes was not capped
def cap_some(
  xs: List<&2, U32>,
  +st: Inf.St,
  +lim: Nat,
  +ys: List<&2, U32>,
  ee: {Inf.inflate.go(xs, Inf.st.cap(st, lim)) == Some{ys} : Maybe<&2, List<&2, U32>>}
) -> {Inf.inflate.go(xs, st) == Some{ys} : Maybe<&2, List<&2, U32>>}:
  cap_some.at(Inf.st.over(st, lim), xs, st, ys, ee)

# no bytes left: the budgeted walk answers some bytes only for a finished reader, as inflate.go
def nil_some(
  ph: Inf.Ph,
  md: Inf.Md,
  wh: Inf.Wh,
  +ac: U32,
  +gt: U32,
  +nd: U32,
  cu: List<&2, U32>,
  +sk: U32,
  cx: Inf.Cx,
  +lim: Nat,
  +ys: List<&2, U32>,
  ee: {Inf.inflate.upto.go([], Inf.St{ph, md, wh, ac, gt, nd, cu, sk, cx}, lim) == Some{ys} : Maybe<&2, List<&2, U32>>}
) -> {Inf.inflate.go([], Inf.St{ph, md, wh, ac, gt, nd, cu, sk, cx}) == Some{ys} : Maybe<&2, List<&2, U32>>}:
  match ph cx:
    case Inf.PDone{} Inf.Cx{_f, _l, _d, +out, _w, _wp, _p, _r, _h}:
      fin_out(Nat.is_le(List.length(&2, U32, out), lim), out, ys, ee)
    case Inf.PFail{} _cx:
      Empty.absurd({None{} == Some{ys} : Maybe<&2, List<&2, U32>>}, none_some(ys, ee))
    case Inf.PByte{} _cx:
      Empty.absurd({None{} == Some{ys} : Maybe<&2, List<&2, U32>>}, none_some(ys, ee))
    case Inf.PAlign{} _cx:
      Empty.absurd({None{} == Some{ys} : Maybe<&2, List<&2, U32>>}, none_some(ys, ee))
    case Inf.PSym{} _cx:
      Empty.absurd({None{} == Some{ys} : Maybe<&2, List<&2, U32>>}, none_some(ys, ee))

# no bytes left: an answer of some bytes has at most the budget of them
def nil_within(
  ph: Inf.Ph,
  md: Inf.Md,
  wh: Inf.Wh,
  +ac: U32,
  +gt: U32,
  +nd: U32,
  cu: List<&2, U32>,
  +sk: U32,
  cx: Inf.Cx,
  +lim: Nat,
  +ys: List<&2, U32>,
  +ee: {Inf.inflate.upto.go([], Inf.St{ph, md, wh, ac, gt, nd, cu, sk, cx}, lim) == Some{ys} : Maybe<&2, List<&2, U32>>}
) -> {Nat.is_le(List.length(&2, U32, ys), lim) == True{} : Bool}:
  match ph cx:
    case Inf.PDone{} Inf.Cx{_f, _l, _d, +out, _w, _wp, _p, _r, _h}:
      fin_within(out, lim, ys, ee)
    case Inf.PFail{} _cx:
      Empty.absurd({Nat.is_le(List.length(&2, U32, ys), lim) == True{} : Bool}, none_some(ys, ee))
    case Inf.PByte{} _cx:
      Empty.absurd({Nat.is_le(List.length(&2, U32, ys), lim) == True{} : Bool}, none_some(ys, ee))
    case Inf.PAlign{} _cx:
      Empty.absurd({Nat.is_le(List.length(&2, U32, ys), lim) == True{} : Bool}, none_some(ys, ee))
    case Inf.PSym{} _cx:
      Empty.absurd({Nat.is_le(List.length(&2, U32, ys), lim) == True{} : Bool}, none_some(ys, ee))

# an answer of some bytes from the budgeted walk is the unbudgeted walk's
def go_some(
  xs: List<&2, U32>,
  st: Inf.St,
  +lim: Nat,
  +ys: List<&2, U32>,
  h_up: {Inf.inflate.upto.go(xs, st, lim) == Some{ys} : Maybe<&2, List<&2, U32>>}
) -> {Inf.inflate.go(xs, st) == Some{ys} : Maybe<&2, List<&2, U32>>}:
  match xs st:
    case Nil{} Inf.St{ph, md, wh, +acc, +got, +need, cur, +skew, cx}:
      nil_some(ph, md, wh, acc, got, need, cur, skew, cx, lim, ys, h_up)
    case Con{+b, +t} Inf.St{ph, md, wh, +acc, +got, +need, cur, +skew, cx}:
      match ph cx:
        case Inf.PDone{} Inf.Cx{_f, _l, _d, +out, _w, _wp, _p, _r, _h}:
          fin_out(Nat.is_le(List.length(&2, U32, out), lim), out, ys, h_up)
        case Inf.PFail{} _cx:
          Empty.absurd({None{} == Some{ys} : Maybe<&2, List<&2, U32>>}, none_some(ys, h_up))
        case Inf.PByte{} c2:
          +s2 = Inf.rd.step8(Inf.St{Inf.PByte{}, md, wh, acc, got, need, cur, skew, c2}, b)
          cap_some(t, s2, lim, ys, go_some(t, Inf.st.cap(s2, lim), lim, ys, h_up))
        case Inf.PAlign{} c2:
          +s2 = Inf.rd.step8(Inf.St{Inf.PAlign{}, md, wh, acc, got, need, cur, skew, c2}, b)
          cap_some(t, s2, lim, ys, go_some(t, Inf.st.cap(s2, lim), lim, ys, h_up))
        case Inf.PSym{} c2:
          +s2 = Inf.rd.step8(Inf.St{Inf.PSym{}, md, wh, acc, got, need, cur, skew, c2}, b)
          cap_some(t, s2, lim, ys, go_some(t, Inf.st.cap(s2, lim), lim, ys, h_up))

# an answer of some bytes from the budgeted walk has at most the budget of them
def go_within(
  xs: List<&2, U32>,
  st: Inf.St,
  +lim: Nat,
  +ys: List<&2, U32>,
  +h_up: {Inf.inflate.upto.go(xs, st, lim) == Some{ys} : Maybe<&2, List<&2, U32>>}
) -> {Nat.is_le(List.length(&2, U32, ys), lim) == True{} : Bool}:
  match xs st:
    case Nil{} Inf.St{ph, md, wh, +acc, +got, +need, cur, +skew, cx}:
      nil_within(ph, md, wh, acc, got, need, cur, skew, cx, lim, ys, h_up)
    case Con{+b, t} Inf.St{ph, md, wh, +acc, +got, +need, cur, +skew, cx}:
      match ph cx:
        case Inf.PDone{} Inf.Cx{_f, _l, _d, +out, _w, _wp, _p, _r, _h}:
          fin_within(out, lim, ys, h_up)
        case Inf.PFail{} _cx:
          Empty.absurd({Nat.is_le(List.length(&2, U32, ys), lim) == True{} : Bool}, none_some(ys, h_up))
        case Inf.PByte{} c2:
          go_within(t, Inf.st.cap(Inf.rd.step8(Inf.St{Inf.PByte{}, md, wh, acc, got, need, cur, skew, c2}, b), lim),
            lim, ys, h_up)
        case Inf.PAlign{} c2:
          go_within(t, Inf.st.cap(Inf.rd.step8(Inf.St{Inf.PAlign{}, md, wh, acc, got, need, cur, skew, c2}, b), lim),
            lim, ys, h_up)
        case Inf.PSym{} c2:
          go_within(t, Inf.st.cap(Inf.rd.step8(Inf.St{Inf.PSym{}, md, wh, acc, got, need, cur, skew, c2}, b), lim),
            lim, ys, h_up)

def Laws.upto_is_inflate(lim, xs, ys, h_up):
  go_some(xs, Inf.st.empty(), lim, ys, h_up)

def Laws.upto_within(lim, xs, ys, h_up):
  go_within(xs, Inf.st.empty(), lim, ys, h_up)
