# proofs of laws/SignatureMatchesPngMagic.bend
import Base
import ../main.bend as Img
import ../laws/SignatureMatchesPngMagic.bend as Laws
import ./lemmas/BasicFacts.bend as M1

def Laws.sig_opens(_rest):
  {==}

# dropping nothing is the list
def drop.zero(+xs: List<&2, U32>) -> {xs == List.drop(&2, U32, xs, 0n) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case _hd <> _tl:
      {==}

# two lists with equal heads and equal tails are equal
def cons.eq(
  +aa: U32,
  +bb: U32,
  +ta: List<&2, U32>,
  +tb: List<&2, U32>,
  eh: {aa == bb : U32},
  et: {ta == tb : List<&2, U32>}
) -> {aa <> ta == bb <> tb : List<&2, U32>}:
  Equal.trans(List<&2, U32>, aa <> ta, bb <> ta, bb <> tb,
    Equal.cong(U32, List<&2, U32>, xx => {xx <> ta : List<&2, U32>}, aa, bb, eh),
    Equal.cong(List<&2, U32>, List<&2, U32>, ll => {bb <> ll : List<&2, U32>}, ta, tb, et))

# what sig.match says of want and xs, when it answers true: the answer it
# started from was true, and xs is want followed by the rest
def prefix.only.ty(+want: List<&2, U32>, +xs: List<&2, U32>, +ok: Bool) -> Type:
  {ok == True{} : Bool} &
    {xs == List.append(&2, U32, want, List.drop(&2, U32, xs, List.length(&2, U32, want))) : List<&2, U32>}

# one byte further: what the rest proves gives the answer so far and this byte
def prefix.only.cons(
  +ok: Bool,
  +wh: U32,
  +wt: List<&2, U32>,
  +bh: U32,
  +bt: List<&2, U32>,
  pr: prefix.only.ty(wt, bt, Bool.and(ok, U32.is_eq(bh, wh)))
) -> prefix.only.ty(wh <> wt, bh <> bt, ok):
  (e_and, e_tail) = pr
  +e_and2 = {e_and : {Bool.and(ok, U32.is_eq(bh, wh)) == True{} : Bool}}
  (M1.and_left(ok, U32.is_eq(bh, wh), e_and2),
    cons.eq(bh, wh, bt, List.append(&2, U32, wt, List.drop(&2, U32, bt, List.length(&2, U32, wt))),
      M1.ueq(bh, wh, M1.and_right(ok, U32.is_eq(bh, wh), e_and2)), e_tail))

# bytes that sig.match finds open with want are want followed by the rest
def prefix.only(
  +want: List<&2, U32>,
  +xs: List<&2, U32>,
  +ok: Bool,
  +h_match: {Img.sig.match(want, xs, ok) == True{} : Bool}
) -> prefix.only.ty(want, xs, ok):
  match want xs:
    case Nil{} _xs:
      (h_match, drop.zero(_xs))
    case +wh <> +wt Nil{}:
      Empty.absurd(prefix.only.ty(wh <> wt, Nil{}, ok), M1.false_true(h_match))
    case +wh <> +wt +bh <> +bt:
      prefix.only.cons(ok, wh, wt, bh, bt, prefix.only(wt, bt, Bool.and(ok, U32.is_eq(bh, wh)), h_match))

# the second half of what prefix.only proves
def prefix.only.rest(
  +want: List<&2, U32>,
  +xs: List<&2, U32>,
  +ok: Bool,
  pr: prefix.only.ty(want, xs, ok)
) -> {xs == List.append(&2, U32, want, List.drop(&2, U32, xs, List.length(&2, U32, want))) : List<&2, U32>}:
  (_e_ok, e_xs) = pr
  e_xs

# split on what sig.match answers: false gives none, which h_some rules out
def sig.only.go(
  ok: Bool,
  +xs: List<&2, U32>,
  e_ok: {Img.sig.match(Img.png_sig(), xs, True{}) == ok : Bool},
  h_some: {Maybe.is_some(&2, List<&2, U32>, Img.sig.pick(ok)) == True{} : Bool}
) -> {xs == List.append(&2, U32, Img.png_sig(), List.drop(&2, U32, xs, 8n)) : List<&2, U32>}:
  match ok:
    case False{}:
      Empty.absurd({xs == List.append(&2, U32, Img.png_sig(), List.drop(&2, U32, xs, 8n)) : List<&2, U32>},
        M1.false_true(h_some))
    case True{}:
      prefix.only.rest(Img.png_sig(), xs, True{}, prefix.only(Img.png_sig(), xs, True{}, e_ok))

def Laws.sig_only(xs, h_some):
  sig.only.go(Img.sig.match(Img.png_sig(), xs, True{}), xs, {==}, h_some)
