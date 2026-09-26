# proof/wp13-jpeg-planes: lemmas for IMG-JPG-2's planes: what Array.get finds after Array.set, on the perfect
# binary trees the decoder's planes are, and what painting and reading a plane out give. PROOF.bend imports this
# file as W13, so the gate checks it.
import Base
import ./u32.bend as U32L
import ./wp6-raster.bend as R
import ../LAWS.bend as Laws
import ../src/jpeg.bend as Jpeg

# ---- a plane as data ----

# an array's tree as data, so a proof may use it more than once
type Tr is Data:
  TLeaf{value: U32}
  TNode{lo: Tr, hi: Tr}

# the array a tree stands for
def arr(tt: Tr) -> Array<U32>:
  match tt:
    case TLeaf{xx}:
      ALeaf{xx}
    case TNode{lo, hi}:
      ANode{arr(lo), arr(hi)}

# an array and a tree it is the array of
def Of(-aa: Array<U32>) -> Type:
  &tt: Tr -> {aa == arr(tt) : Array<U32>}

# a node's tree from its halves' trees
def of.node(-xs: Array<U32>, -ys: Array<U32>, ox: Of(xs), oy: Of(ys)) -> Of(ANode{xs, ys}):
  (tx, ex) = ox
  (ty, ey) = oy
  sx = Equal.sym(Array<U32>, xs, arr(tx), ex)
  sy = Equal.sym(Array<U32>, ys, arr(ty), ey)
  %sx : Of(ANode{_, ys})
  %sy : Of(ANode{arr(tx), _})
  (TNode{tx, ty}, {==})

# every array is the array of a tree
def of(aa: Array<U32>) -> Of(aa):
  match aa:
    case ALeaf{+xx}:
      (TLeaf{xx}, {==})
    case ANode{xs, ys}:
      of.node(xs, ys, of(xs), of(ys))

# the size Array.size reads: the leftmost path, doubled at each node
def size(tt: Tr) -> U32:
  match tt:
    case TLeaf{_xx}:
      1
    case TNode{lo, _hi}:
      U32.shl(size(lo))

# the value Array.get.go finds, the tree walked as it walks the array
def get(tt: Tr, +nn: U32, +ii: U32) -> U32:
  match tt:
    case TLeaf{xx}:
      xx
    case TNode{lo, hi}:
      +hh = U32.shr(nn)
      +gl = get(lo, hh, ii)
      +gh = get(hi, hh, U32.sub(ii, hh))
      Bool.pick(U32, U32.is_lt(ii, hh), gl, gh)

# the node a write leaves: the low half written, or the high half
def put.if(zz: Bool, +lo: Tr, +hi: Tr, +pl: Tr, +ph: Tr) -> Tr:
  match zz:
    case True{}:
      TNode{pl, hi}
    case False{}:
      TNode{lo, ph}

# the tree Array.swap.go leaves, walked as it walks the array
def put(+tt: Tr, +nn: U32, +ii: U32, +vv: U32) -> Tr:
  match tt:
    case TLeaf{_xx}:
      TLeaf{vv}
    case TNode{lo, hi}:
      +hh = U32.shr(nn)
      put.if(U32.is_lt(ii, hh), lo, hi, put(lo, hh, ii, vv), put(hi, hh, U32.sub(ii, hh), vv))

# ---- the array walks, on the tree ----

# the size walk of a tree's array hands the array back with the tree's size
def size_eq(tt: Tr) -> {Array.size(U32, arr(tt)) == (arr(tt), size(tt)) : Array<U32> & U32}:
  match tt:
    case TLeaf{_xx}:
      {==}
    case TNode{lo, hi}:
      ee = Equal.sym(Array<U32> & U32, Array.size(U32, arr(lo)), (arr(lo), size(lo)), size_eq(lo))
      %ee : {Array.size.node(U32, arr(hi), _) == (ANode{arr(lo), arr(hi)}, U32.shl(size(lo))) : Array<U32> & U32}
      {==}

# a read's step at a node: the half the index falls in, the other half kept
def get_if(
  +lo: Tr,
  +hi: Tr,
  +hh: U32,
  +ii: U32,
  zz: Bool,
  +el: {Array.get.go(U32, arr(lo), hh, ii) == (arr(lo), get(lo, hh, ii)) : Array<U32> & U32},
  +eh: {Array.get.go(U32, arr(hi), hh, U32.sub(ii, hh)) == (arr(hi), get(hi, hh, U32.sub(ii, hh))) : Array<U32> & U32}
) -> {Array.get.if(U32, arr(lo), arr(hi), hh, ii, zz) == (ANode{arr(lo), arr(hi)}, Bool.pick(U32, zz, get(lo, hh, ii),
  get(hi, hh, U32.sub(ii, hh)))) : Array<U32> & U32}:
  match zz:
    case True{}:
      sl = Equal.sym(Array<U32> & U32, Array.get.go(U32, arr(lo), hh, ii), (arr(lo), get(lo, hh, ii)), el)
      %sl : {Array.swap.lo(U32, arr(hi), _) == (ANode{arr(lo), arr(hi)}, get(lo, hh, ii)) : Array<U32> & U32}
      {==}
    case False{}:
      sh = Equal.sym(Array<U32> & U32, Array.get.go(U32, arr(hi), hh, U32.sub(ii, hh)), (arr(hi), get(hi, hh,
        U32.sub(ii, hh))), eh)
      %sh : {Array.swap.hi(U32, arr(lo), _) == (ANode{arr(lo), arr(hi)}, get(hi, hh, U32.sub(ii, hh))) :
        Array<U32> & U32}
      {==}

# a read's tree walk hands the array back with the value the tree walk finds
def get_eq(+tt: Tr, +nn: U32, +ii: U32) -> {Array.get.go(U32, arr(tt), nn, ii) == (arr(tt), get(tt, nn, ii)) :
  Array<U32> & U32}:
  match tt:
    case TLeaf{_xx}:
      {==}
    case TNode{lo, hi}:
      +hh = U32.shr(nn)
      get_if(lo, hi, hh, ii, U32.is_lt(ii, hh), get_eq(lo, hh, ii), get_eq(hi, hh, U32.sub(ii, hh)))

# a write's tree walk, as swap_eq says it
def SwapHalf(+tt: Tr, +hh: U32, +ii: U32, +vv: U32) -> Type:
  {Array.swap.go(U32, arr(tt), hh, ii, vv) == (arr(put(tt, hh, ii, vv)), get(tt, hh, ii)) : Array<U32> & U32}

# a write's step at a node: the half the index falls in written, the other half kept
def swap_if(
  +lo: Tr,
  +hi: Tr,
  +hh: U32,
  +ii: U32,
  +vv: U32,
  zz: Bool,
  el: SwapHalf(lo, hh, ii, vv),
  eh: SwapHalf(hi, hh, U32.sub(ii, hh), vv)
) -> {Array.swap.if(U32, arr(lo), arr(hi), hh, ii, vv, zz) == (arr(put.if(zz, lo, hi, put(lo, hh, ii, vv), put(hi, hh,
  U32.sub(ii, hh), vv))), Bool.pick(U32, zz, get(lo, hh, ii), get(hi, hh, U32.sub(ii, hh)))) :
  Array<U32> & U32}:
  match zz:
    case True{}:
      sl = Equal.sym(Array<U32> & U32, Array.swap.go(U32, arr(lo), hh, ii, vv), (arr(put(lo, hh, ii, vv)), get(lo, hh,
        ii)), el)
      %sl : {Array.swap.lo(U32, arr(hi), _) == (ANode{arr(put(lo, hh, ii, vv)), arr(hi)}, get(lo, hh, ii)) :
        Array<U32> & U32}
      {==}
    case False{}:
      sh = Equal.sym(Array<U32> & U32, Array.swap.go(U32, arr(hi), hh, U32.sub(ii, hh), vv), (arr(put(hi, hh,
        U32.sub(ii, hh), vv)), get(hi, hh, U32.sub(ii, hh))), eh)
      %sh : {Array.swap.hi(U32, arr(lo), _) == (ANode{arr(lo), arr(put(hi, hh, U32.sub(ii, hh), vv))}, get(hi, hh,
        U32.sub(ii, hh))) : Array<U32> & U32}
      {==}

# a write's tree walk leaves the array of the tree put leaves, and hands back the value get finds
def swap_eq(
  +tt: Tr,
  +nn: U32,
  +ii: U32,
  +vv: U32
) -> {Array.swap.go(U32, arr(tt), nn, ii, vv) == (arr(put(tt, nn, ii, vv)), get(tt, nn, ii)) : Array<U32> & U32}:
  match tt:
    case TLeaf{_xx}:
      {==}
    case TNode{lo, hi}:
      +hh = U32.shr(nn)
      swap_if(lo, hi, hh, ii, vv, U32.is_lt(ii, hh), swap_eq(lo, hh, ii, vv), swap_eq(hi, hh, U32.sub(ii, hh), vv))

# the index Array.get and Array.set walk to: the index masked by the size less one
def mask(+ii: U32, +nn: U32) -> U32:
  U32.and(ii, U32.sub(nn, 1))

# Array.get of a tree's array: the array back, and the value get finds at the masked index
def get_arr(+tt: Tr, +ii: U32) -> {Array.get(U32, arr(tt), ii) == (arr(tt), get(tt, size(tt), mask(ii, size(tt)))) :
  Array<U32> & U32}:
  ss = Equal.sym(Array<U32> & U32, Array.size(U32, arr(tt)), (arr(tt), size(tt)), size_eq(tt))
  %ss : {Array.get.at(U32, ii, _) == (arr(tt), get(tt, size(tt), mask(ii, size(tt)))) : Array<U32> & U32}
  get_eq(tt, size(tt), mask(ii, size(tt)))

# the tree Array.set leaves: put at the masked index
def set(+tt: Tr, +ii: U32, +vv: U32) -> Tr:
  put(tt, size(tt), mask(ii, size(tt)), vv)

# Array.set of a tree's array is the array of the tree set leaves
def set_arr(+tt: Tr, +ii: U32, +vv: U32) -> {Array.set(U32, arr(tt), ii, vv) == arr(set(tt, ii, vv)) : Array<U32>}:
  ss = Equal.sym(Array<U32> & U32, Array.size(U32, arr(tt)), (arr(tt), size(tt)), size_eq(tt))
  sw = Equal.sym(Array<U32> & U32, Array.swap.go(U32, arr(tt), size(tt), mask(ii, size(tt)), vv), (arr(set(tt, ii,
    vv)), get(tt, size(tt), mask(ii, size(tt)))), swap_eq(tt, size(tt), mask(ii, size(tt)), vv))
  %ss : {Array.set.fin(U32, Array.swap.at(U32, ii, vv, _)) == arr(set(tt, ii, vv)) : Array<U32>}
  %sw : {Array.set.fin(U32, _) == arr(set(tt, ii, vv)) : Array<U32>}
  {==}

# a write at a node keeps the size, given that a write to the low half does
def size_put.if(
  zz: Bool,
  +lo: Tr,
  +hi: Tr,
  +pl: Tr,
  +ph: Tr,
  +el: {size(pl) == size(lo) : U32}
) -> {size(put.if(zz, lo, hi, pl, ph)) == U32.shl(size(lo)) : U32}:
  match zz:
    case True{}:
      Equal.cong(U32, U32, xx => U32.shl(xx), size(pl), size(lo), el)
    case False{}:
      {==}

# a write keeps the size
def size_put(+tt: Tr, +nn: U32, +ii: U32, +vv: U32) -> {size(put(tt, nn, ii, vv)) == size(tt) : U32}:
  match tt:
    case TLeaf{_xx}:
      {==}
    case TNode{lo, hi}:
      +hh = U32.shr(nn)
      size_put.if(U32.is_lt(ii, hh), lo, hi, put(lo, hh, ii, vv), put(hi, hh, U32.sub(ii, hh), vv),
        size_put(lo, hh, ii, vv))

# ---- a read after a write ----

# at a node: a read at the index just written finds the value, given that it does in each half
def gps_if(
  zz: Bool,
  +lo: Tr,
  +hi: Tr,
  +nn: U32,
  +ii: U32,
  +vv: U32,
  +ez: {U32.is_lt(ii, U32.shr(nn)) == zz : Bool},
  +el: {get(put(lo, U32.shr(nn), ii, vv), U32.shr(nn), ii) == vv : U32},
  +eh: {get(put(hi, U32.shr(nn), U32.sub(ii, U32.shr(nn)), vv), U32.shr(nn), U32.sub(ii, U32.shr(nn))) == vv : U32}
) -> {get(put.if(zz, lo, hi, put(lo, U32.shr(nn), ii, vv), put(hi, U32.shr(nn), U32.sub(ii, U32.shr(nn)), vv)), nn,
  ii) == vv : U32}:
  match zz:
    case True{}:
      +hh = U32.shr(nn)
      +ih = U32.sub(ii, hh)
      se = Equal.sym(Bool, U32.is_lt(ii, hh), True{}, ez)
      %se : {Bool.pick(U32, _, get(put(lo, hh, ii, vv), hh, ii), get(hi, hh, ih)) == vv : U32}
      el
    case False{}:
      +hh = U32.shr(nn)
      +ih = U32.sub(ii, hh)
      se = Equal.sym(Bool, U32.is_lt(ii, hh), False{}, ez)
      %se : {Bool.pick(U32, _, get(lo, hh, ii), get(put(hi, hh, ih, vv), hh, ih)) == vv : U32}
      eh

# a read at the index just written finds the value, in any tree
def get_put_same(+tt: Tr, +nn: U32, +ii: U32, +vv: U32) -> {get(put(tt, nn, ii, vv), nn, ii) == vv : U32}:
  match tt:
    case TLeaf{_xx}:
      {==}
    case TNode{lo, hi}:
      +hh = U32.shr(nn)
      gps_if(U32.is_lt(ii, hh), lo, hi, nn, ii, vv, {==}, get_put_same(lo, hh, ii, vv), get_put_same(hi, hh,
        U32.sub(ii, hh), vv))

# a perfect binary tree of 2^d leaves
def pf(+dd: Nat, +tt: Tr) -> Bool:
  match dd tt:
    case 0n TLeaf{_xx}:
      True{}
    case 0n TNode{_lo, _hi}:
      False{}
    case 1n+_ee TLeaf{_xx}:
      False{}
    case 1n+ee TNode{lo, hi}:
      +pl = pf(ee, lo)
      +ph = pf(ee, hi)
      Bool.and(pl, ph)

# both walks go the same way: on to the next level, or they part
def same.if(zi: Bool, zj: Bool, next: Bool) -> Bool:
  match zi zj:
    case True{} True{}:
      next
    case False{} False{}:
      next
    case True{} False{}:
      False{}
    case False{} True{}:
      False{}

# whether the walks of two indices down a perfect tree of 2^d leaves, the root's size nn, end at one leaf
def same(dd: Nat, +nn: U32, +ii: U32, +jj: U32) -> Bool:
  match dd:
    case 0n:
      True{}
    case 1n+ee:
      +hh = U32.shr(nn)
      same.if(U32.is_lt(ii, hh), U32.is_lt(jj, hh), same(ee, hh, Bool.pick(U32, U32.is_lt(ii, hh), ii, U32.sub(ii,
        hh)), Bool.pick(U32, U32.is_lt(jj, hh), jj, U32.sub(jj, hh))))

# the value a read finds after a write: the written value when both walks end at one leaf, else the old one
def after(+ok: Bool, +vv: U32, +old: U32) -> U32:
  Bool.pick(U32, ok, vv, old)

# the right-hand side of get_put at a node, for walks going a and b at the root
def gp.rhs(
  +aa: Bool,
  +bb: Bool,
  +ee: Nat,
  +lo: Tr,
  +hi: Tr,
  +hh: U32,
  +ii: U32,
  +jj: U32,
  +vv: U32
) -> U32:
  +gl = get(lo, hh, jj)
  +gh = get(hi, hh, U32.sub(jj, hh))
  after(same.if(aa, bb, same(ee, hh, Bool.pick(U32, aa, ii, U32.sub(ii, hh)), Bool.pick(U32, bb, jj, U32.sub(jj,
    hh)))), vv, Bool.pick(U32, bb, gl, gh))

# a read after a write in a half, as get_put says it
def GpHalf(+tt: Tr, +ee: Nat, +hh: U32, +ii: U32, +jj: U32, +vv: U32) -> Type:
  {get(put(tt, hh, ii, vv), hh, jj) == after(same(ee, hh, ii, jj), vv, get(tt, hh, jj)) : U32}

# at a node of a perfect tree: a read after a write, given the halves
def gp_if(
  zi: Bool,
  zj: Bool,
  +ee: Nat,
  +lo: Tr,
  +hi: Tr,
  +nn: U32,
  +ii: U32,
  +jj: U32,
  +vv: U32,
  +ezi: {U32.is_lt(ii, U32.shr(nn)) == zi : Bool},
  +ezj: {U32.is_lt(jj, U32.shr(nn)) == zj : Bool},
  el: GpHalf(lo, ee, U32.shr(nn), ii, jj, vv),
  eh: GpHalf(hi, ee, U32.shr(nn), U32.sub(ii, U32.shr(nn)), U32.sub(jj, U32.shr(nn)), vv)
) -> {get(put.if(zi, lo, hi, put(lo, U32.shr(nn), ii, vv), put(hi, U32.shr(nn), U32.sub(ii, U32.shr(nn)), vv)), nn,
  jj) == gp.rhs(U32.is_lt(ii, U32.shr(nn)), U32.is_lt(jj, U32.shr(nn)), ee, lo, hi, U32.shr(nn), ii, jj, vv) : U32}:
  match zi zj:
    case True{} True{}:
      +hh = U32.shr(nn)
      +sj = U32.sub(jj, hh)
      +pl = put(lo, hh, ii, vv)
      si1 = Equal.sym(Bool, U32.is_lt(ii, hh), True{}, ezi)
      sj1 = Equal.sym(Bool, U32.is_lt(jj, hh), True{}, ezj)
      %si1 : {get(TNode{pl, hi}, nn, jj) == gp.rhs(_, U32.is_lt(jj, hh), ee, lo, hi, hh, ii, jj, vv) : U32}
      %sj1 : {Bool.pick(U32, _, get(pl, hh, jj), get(hi, hh, sj)) == gp.rhs(True{}, _, ee, lo, hi, hh,
        ii, jj, vv) : U32}
      el
    case True{} False{}:
      +hh = U32.shr(nn)
      +sj = U32.sub(jj, hh)
      +pl = put(lo, hh, ii, vv)
      si1 = Equal.sym(Bool, U32.is_lt(ii, hh), True{}, ezi)
      sj1 = Equal.sym(Bool, U32.is_lt(jj, hh), False{}, ezj)
      %si1 : {get(TNode{pl, hi}, nn, jj) == gp.rhs(_, U32.is_lt(jj, hh), ee, lo, hi, hh, ii, jj, vv) : U32}
      %sj1 : {Bool.pick(U32, _, get(pl, hh, jj), get(hi, hh, sj)) == gp.rhs(True{}, _, ee, lo, hi, hh,
        ii, jj, vv) : U32}
      {==}
    case False{} True{}:
      +hh = U32.shr(nn)
      +si = U32.sub(ii, hh)
      +sj = U32.sub(jj, hh)
      +ph = put(hi, hh, si, vv)
      si1 = Equal.sym(Bool, U32.is_lt(ii, hh), False{}, ezi)
      sj1 = Equal.sym(Bool, U32.is_lt(jj, hh), True{}, ezj)
      %si1 : {get(TNode{lo, ph}, nn, jj) == gp.rhs(_, U32.is_lt(jj, hh), ee, lo, hi, hh, ii, jj, vv) : U32}
      %sj1 : {Bool.pick(U32, _, get(lo, hh, jj), get(ph, hh, sj)) == gp.rhs(False{}, _, ee, lo, hi, hh,
        ii, jj, vv) : U32}
      {==}
    case False{} False{}:
      +hh = U32.shr(nn)
      +si = U32.sub(ii, hh)
      +sj = U32.sub(jj, hh)
      +ph = put(hi, hh, si, vv)
      si1 = Equal.sym(Bool, U32.is_lt(ii, hh), False{}, ezi)
      sj1 = Equal.sym(Bool, U32.is_lt(jj, hh), False{}, ezj)
      %si1 : {get(TNode{lo, ph}, nn, jj) == gp.rhs(_, U32.is_lt(jj, hh), ee, lo, hi, hh, ii, jj, vv) : U32}
      %sj1 : {Bool.pick(U32, _, get(lo, hh, jj), get(ph, hh, sj)) == gp.rhs(False{}, _, ee, lo, hi, hh,
        ii, jj, vv) : U32}
      eh

# a read after a write to a perfect tree finds the written value when both walks end at one leaf, and what it
# found before otherwise
def get_put(
  +dd: Nat,
  +tt: Tr,
  +nn: U32,
  +ii: U32,
  +jj: U32,
  +vv: U32,
  +hp: {pf(dd, tt) == True{} : Bool}
) -> {get(put(tt, nn, ii, vv), nn, jj) == after(same(dd, nn, ii, jj), vv, get(tt, nn, jj)) : U32}:
  match dd tt:
    case 0n TLeaf{_xx}:
      {==}
    case 1n+ee TLeaf{+xx}:
      Empty.absurd({get(put(TLeaf{xx}, nn, ii, vv), nn, jj) == after(same(1n+ee, nn, ii, jj), vv, xx) : U32},
        U32L.false_true(hp))
    case 0n TNode{lo, hi}:
      Empty.absurd({get(put(TNode{lo, hi}, nn, ii, vv), nn, jj) == after(True{}, vv, get(TNode{lo, hi}, nn, jj)) :
        U32}, U32L.false_true(hp))
    case 1n+ee TNode{lo, hi}:
      +hh = U32.shr(nn)
      +ha = U32L.and_left(pf(ee, lo), pf(ee, hi), hp)
      +hb = U32L.and_right(pf(ee, lo), pf(ee, hi), hp)
      gp_if(U32.is_lt(ii, hh), U32.is_lt(jj, hh), ee, lo, hi, nn, ii, jj, vv, {==}, {==}, get_put(ee, lo, hh, ii, jj,
        vv, ha), get_put(ee, hi, hh, U32.sub(ii, hh), U32.sub(jj, hh), vv, hb))

# at a node of depth one more than ee: a write keeps the tree perfect, given that a write to the low half does
def pfp_if(
  zz: Bool,
  +ee: Nat,
  +lo: Tr,
  +hi: Tr,
  +pl: Tr,
  +ph: Tr,
  +el: {pf(ee, pl) == pf(ee, lo) : Bool},
  +eh: {pf(ee, ph) == pf(ee, hi) : Bool}
) -> {pf(1n+ee, put.if(zz, lo, hi, pl, ph)) == pf(1n+ee, TNode{lo, hi}) : Bool}:
  match zz:
    case True{}:
      Equal.cong(Bool, Bool, bb => Bool.and(bb, pf(ee, hi)), pf(ee, pl), pf(ee, lo), el)
    case False{}:
      Equal.cong(Bool, Bool, bb => Bool.and(pf(ee, lo), bb), pf(ee, ph), pf(ee, hi), eh)

# at a node of depth zero: a write leaves it not perfect, as it was
def pfp_zero(zz: Bool, +lo: Tr, +hi: Tr, +pl: Tr, +ph: Tr) -> {pf(0n, put.if(zz, lo, hi, pl, ph)) == False{} :
  Bool}:
  match zz:
    case True{}:
      {==}
    case False{}:
      {==}

# a write keeps a tree perfect, and a tree that is not stays not
def pf_put(+dd: Nat, +tt: Tr, +nn: U32, +ii: U32, +vv: U32) -> {pf(dd, put(tt, nn, ii, vv)) == pf(dd, tt) : Bool}:
  match dd tt:
    case 0n TLeaf{_xx}:
      {==}
    case 1n+_ee TLeaf{_xx}:
      {==}
    case 0n TNode{lo, hi}:
      +hh = U32.shr(nn)
      pfp_zero(U32.is_lt(ii, hh), lo, hi, put(lo, hh, ii, vv), put(hi, hh, U32.sub(ii, hh), vv))
    case 1n+ee TNode{lo, hi}:
      +hh = U32.shr(nn)
      pfp_if(U32.is_lt(ii, hh), ee, lo, hi, put(lo, hh, ii, vv), put(hi, hh, U32.sub(ii, hh), vv), pf_put(ee, lo, hh,
        ii, vv), pf_put(ee, hi, hh, U32.sub(ii, hh), vv))

# ---- powers of two ----

# the double of a number above zero is above one
def dbl_pos(+xx: Nat, hh: {Nat.is_lt(0n, xx) == True{} : Bool}) -> {Nat.is_lt(1n, Nat.double(xx)) == True{} : Bool}:
  match xx:
    case 0n:
      Empty.absurd({Nat.is_lt(1n, 0n) == True{} : Bool}, U32L.false_true(hh))
    case 1n+_pp:
      {==}

# doubling keeps an order
def dbl_lt(
  +xx: Nat,
  +yy: Nat,
  hh: {Nat.is_lt(xx, yy) == True{} : Bool}
) -> {Nat.is_lt(Nat.double(xx), Nat.double(yy)) == True{} : Bool}:
  match xx yy:
    case _xx 0n:
      Empty.absurd({Nat.is_lt(Nat.double(xx), 0n) == True{} : Bool}, U32L.false_true(Equal.trans(Bool, False{},
        Nat.is_lt(xx, 0n), True{}, R.lt_zero_false(xx), hh)))
    case 0n 1n+_qq:
      {==}
    case 1n+pp 1n+qq:
      dbl_lt(pp, qq, hh)

# two to any power is above zero
def pow_pos(+pp: Nat) -> {Nat.is_lt(0n, Nat.pow(2n, pp)) == True{} : Bool}:
  match pp:
    case 0n:
      {==}
    case 1n+qq:
      R.lt_rw_r(0n, Nat.double(Nat.pow(2n, qq)), Nat.pow(2n, 1n+qq), Equal.sym(Nat, Nat.pow(2n, 1n+qq),
        Nat.double(Nat.pow(2n, qq)), R.pow2_succ(qq)), R.lt_le_trans(0n, 1n, Nat.double(Nat.pow(2n, qq)), {==},
        R.lt_le(1n, Nat.double(Nat.pow(2n, qq)), dbl_pos(Nat.pow(2n, qq), pow_pos(qq)))))

# two to a smaller power is smaller
def pow_lt(
  +aa: Nat,
  +bb: Nat,
  hh: {Nat.is_lt(aa, bb) == True{} : Bool}
) -> {Nat.is_lt(Nat.pow(2n, aa), Nat.pow(2n, bb)) == True{} : Bool}:
  match aa bb:
    case _aa 0n:
      Empty.absurd({Nat.is_lt(Nat.pow(2n, aa), 1n) == True{} : Bool}, U32L.false_true(Equal.trans(Bool, False{},
        Nat.is_lt(aa, 0n), True{}, R.lt_zero_false(aa), hh)))
    case 0n 1n+qq:
      R.lt_rw_r(1n, Nat.double(Nat.pow(2n, qq)), Nat.pow(2n, 1n+qq), Equal.sym(Nat, Nat.pow(2n, 1n+qq),
        Nat.double(Nat.pow(2n, qq)), R.pow2_succ(qq)), dbl_pos(Nat.pow(2n, qq), pow_pos(qq)))
    case 1n+pp 1n+qq:
      R.lt_rw_l(Nat.double(Nat.pow(2n, pp)), Nat.pow(2n, 1n+pp), Nat.pow(2n, 1n+qq), Equal.sym(Nat, Nat.pow(2n, 1n+pp),
        Nat.double(Nat.pow(2n, pp)), R.pow2_succ(pp)), R.lt_rw_r(Nat.double(Nat.pow(2n, pp)),
        Nat.double(Nat.pow(2n, qq)), Nat.pow(2n, 1n+qq), Equal.sym(Nat, Nat.pow(2n, 1n+qq), Nat.double(Nat.pow(2n, qq)),
        R.pow2_succ(qq)), dbl_lt(Nat.pow(2n, pp), Nat.pow(2n, qq), pow_lt(pp, qq, hh))))

# ---- the size of a perfect tree ----

# the word of p bits with only bit e set
def sbit(pp: Nat, +ee: Nat) -> Word(pp):
  match pp:
    case 0n:
      WNil{}
    case 1n+qq:
      match ee:
        case 0n:
          WCon{True{}, Word.zero(qq)}
        case 1n+ff:
          WCon{False{}, sbit(qq, ff)}

# shifting zero in over zero leaves zero
def shl_zero(pp: Nat) -> {Word.shl.put(pp, False{}, Word.zero(pp)) == Word.zero(pp) : Word(pp)}:
  match pp:
    case 0n:
      {==}
    case 1n+qq:
      Equal.cong(Word(qq), Word(1n+qq), ww => WCon{False{}, ww}, Word.shl.put(qq, False{}, Word.zero(qq)),
        Word.zero(qq), shl_zero(qq))

# shifting one in over zero sets bit 0
def shl_one(
  +pp: Nat,
  hh: {Nat.is_lt(0n, pp) == True{} : Bool}
) -> {Word.shl.put(pp, True{}, Word.zero(pp)) == sbit(pp, 0n) : Word(pp)}:
  match pp:
    case 0n:
      Empty.absurd({WNil{} == WNil{} : Word(0n)}, U32L.false_true(hh))
    case 1n+qq:
      Equal.cong(Word(qq), Word(1n+qq), ww => WCon{True{}, ww}, Word.shl.put(qq, False{}, Word.zero(qq)),
        Word.zero(qq), shl_zero(qq))

# shifting zero in over the word of bit f sets bit f + 1, when that is below p
def shl_sb(
  +pp: Nat,
  +ff: Nat,
  hh: {Nat.is_lt(1n+ff, pp) == True{} : Bool}
) -> {Word.shl.put(pp, False{}, sbit(pp, ff)) == sbit(pp, 1n+ff) : Word(pp)}:
  match pp:
    case 0n:
      Empty.absurd({WNil{} == WNil{} : Word(0n)}, U32L.false_true(hh))
    case 1n+rr:
      match ff:
        case 0n:
          Equal.cong(Word(rr), Word(1n+rr), ww => WCon{False{}, ww}, Word.shl.put(rr, True{}, Word.zero(rr)),
            sbit(rr, 0n), shl_one(rr, hh))
        case 1n+gg:
          Equal.cong(Word(rr), Word(1n+rr), ww => WCon{False{}, ww}, Word.shl.put(rr, False{}, sbit(rr, gg)),
            sbit(rr, 1n+gg), shl_sb(rr, gg, hh))

# shifting the word of bit e left gives the word of bit e + 1, when that is below p
def shl_sbit(
  +pp: Nat,
  +ee: Nat,
  hh: {Nat.is_lt(1n+ee, pp) == True{} : Bool}
) -> {Word.shl(pp, sbit(pp, ee)) == sbit(pp, 1n+ee) : Word(pp)}:
  match pp:
    case 0n:
      Empty.absurd({WNil{} == WNil{} : Word(0n)}, U32L.false_true(hh))
    case 1n+qq:
      match ee:
        case 0n:
          Equal.cong(Word(qq), Word(1n+qq), ww => WCon{False{}, ww}, Word.shl.put(qq, True{}, Word.zero(qq)),
            sbit(qq, 0n), shl_one(qq, hh))
        case 1n+ff:
          Equal.cong(Word(qq), Word(1n+qq), ww => WCon{False{}, ww}, Word.shl.put(qq, False{}, sbit(qq, ff)),
            sbit(qq, 1n+ff), shl_sb(qq, ff, hh))

# the word of bit e is 2^e, when e is below p
def sbit_nat(
  +pp: Nat,
  +ee: Nat,
  hh: {Nat.is_lt(ee, pp) == True{} : Bool}
) -> {Word.to_nat(pp, sbit(pp, ee)) == Nat.pow(2n, ee) : Nat}:
  match pp:
    case 0n:
      Empty.absurd({0n == Nat.pow(2n, ee) : Nat}, U32L.false_true(Equal.trans(Bool, False{}, Nat.is_lt(ee, 0n),
        True{}, R.lt_zero_false(ee), hh)))
    case 1n+qq:
      match ee:
        case 0n:
          Equal.cong(Nat, Nat, xx => 1n+Nat.double(xx), Word.to_nat(qq, Word.zero(qq)), 0n, R.word_zero_nat(qq))
        case 1n+ff:
          Equal.trans(Nat, Nat.double(Word.to_nat(qq, sbit(qq, ff))), Nat.double(Nat.pow(2n, ff)), Nat.pow(2n, 1n+ff),
            Equal.cong(Nat, Nat, xx => Nat.double(xx), Word.to_nat(qq, sbit(qq, ff)), Nat.pow(2n, ff), sbit_nat(qq,
            ff, hh)), Equal.sym(Nat, Nat.pow(2n, 1n+ff), Nat.double(Nat.pow(2n, ff)), R.pow2_succ(ff)))

# the size of a perfect tree of 2^d leaves, d below 32, is the U32 of bit d
def size_bits(
  +dd: Nat,
  +tt: Tr,
  +hp: {pf(dd, tt) == True{} : Bool},
  +hd: {Nat.is_lt(dd, 32n) == True{} : Bool}
) -> {size(tt) == U32{sbit(32n, dd)} : U32}:
  match dd tt:
    case 0n TLeaf{_xx}:
      {==}
    case 1n+ee TLeaf{+xx}:
      Empty.absurd({size(TLeaf{xx}) == U32{sbit(32n, 1n+ee)} : U32}, U32L.false_true(hp))
    case 0n TNode{lo, hi}:
      Empty.absurd({size(TNode{lo, hi}) == U32{sbit(32n, 0n)} : U32}, U32L.false_true(hp))
    case 1n+ee TNode{lo, _hi}:
      +he = {R.lt_le_trans(ee, 31n, 32n, hd, R.le_succ(31n)) : {Nat.is_lt(ee, 32n) == True{} : Bool}}
      +ih = size_bits(ee, lo, U32L.and_left(pf(ee, lo), pf(ee, _hi), hp), he)
      Equal.trans(U32, U32.shl(size(lo)), U32.shl(U32{sbit(32n, ee)}), U32{sbit(32n, 1n+ee)}, Equal.cong(U32, U32,
        uu => U32.shl(uu), size(lo), U32{sbit(32n, ee)}, ih), Equal.cong(Word(32n), U32, ww => U32{ww},
        Word.shl(32n, sbit(32n, ee)), sbit(32n, 1n+ee), shl_sbit(32n, ee, hd)))

# the size of a perfect tree of 2^d leaves, d below 32, is 2^d
def size_nat(
  +dd: Nat,
  +tt: Tr,
  +hp: {pf(dd, tt) == True{} : Bool},
  +hd: {Nat.is_lt(dd, 32n) == True{} : Bool}
) -> {U32.to_nat(size(tt)) == Nat.pow(2n, dd) : Nat}:
  Equal.trans(Nat, U32.to_nat(size(tt)), U32.to_nat(U32{sbit(32n, dd)}), Nat.pow(2n, dd), Equal.cong(U32, Nat,
    uu => U32.to_nat(uu), size(tt), U32{sbit(32n, dd)}, size_bits(dd, tt, hp, hd)), sbit_nat(32n, dd, hd))

# ---- numbers ----

# one less, zero staying zero
def pred(nn: Nat) -> Nat:
  match nn:
    case 0n:
      0n
    case 1n+pp:
      pp

# a successor is not zero
def succ_ne(-xx: Nat, ee: {1n+xx == 0n : Nat}) -> Empty:
  U32L.false_true(Equal.cong(Nat, Bool, nn => Nat.is_eq(nn, 0n), 1n+xx, 0n, ee))

# successors equal have equal predecessors
def succ_inj(-xx: Nat, -yy: Nat, ee: {1n+xx == 1n+yy : Nat}) -> {xx == yy : Nat}:
  Equal.cong(Nat, Nat, nn => pred(nn), 1n+xx, 1n+yy, ee)

# an odd number is not an even one
def odd_even(+xx: Nat, +yy: Nat, ee: {1n+Nat.double(xx) == Nat.double(yy) : Nat}) -> Empty:
  match xx yy:
    case 0n 0n:
      succ_ne(0n, ee)
    case 0n 1n+qq:
      succ_ne(Nat.double(qq), Equal.sym(Nat, 0n, 1n+Nat.double(qq), succ_inj(0n, 1n+Nat.double(qq), ee)))
    case 1n+pp 0n:
      succ_ne(2n+Nat.double(pp), ee)
    case 1n+pp 1n+qq:
      odd_even(pp, qq, succ_inj(1n+Nat.double(pp), Nat.double(qq), succ_inj(2n+Nat.double(pp), 1n+Nat.double(qq), ee)))

# doubling is one to one
def dbl_inj(+xx: Nat, +yy: Nat, ee: {Nat.double(xx) == Nat.double(yy) : Nat}) -> {xx == yy : Nat}:
  match xx yy:
    case 0n 0n:
      {==}
    case 0n 1n+qq:
      Empty.absurd({0n == 1n+qq : Nat}, succ_ne(1n+Nat.double(qq), Equal.sym(Nat, 0n, 2n+Nat.double(qq), ee)))
    case 1n+pp 0n:
      Empty.absurd({1n+pp == 0n : Nat}, succ_ne(1n+Nat.double(pp), ee))
    case 1n+pp 1n+qq:
      Equal.cong(Nat, Nat, nn => 1n+nn, pp, qq, dbl_inj(pp, qq, succ_inj(Nat.double(pp), Nat.double(qq),
        succ_inj(1n+Nat.double(pp), 1n+Nat.double(qq), ee))))

# a number below one is zero
def lt1_zero(+xx: Nat, hh: {Nat.is_lt(xx, 1n) == True{} : Bool}) -> {xx == 0n : Nat}:
  match xx:
    case 0n:
      {==}
    case 1n+pp:
      Empty.absurd({1n+pp == 0n : Nat}, U32L.false_true(Equal.trans(Bool, False{}, Nat.is_lt(pp, 0n), True{},
        R.lt_zero_false(pp), hh)))

# a number below another is not it
def lt_neq(+xx: Nat, +yy: Nat, hh: {Nat.is_lt(xx, yy) == True{} : Bool}) -> {Nat.is_eq(xx, yy) == False{} : Bool}:
  match xx yy:
    case _xx 0n:
      Empty.absurd({Nat.is_eq(xx, 0n) == False{} : Bool}, U32L.false_true(Equal.trans(Bool, False{}, Nat.is_lt(xx,
        0n), True{}, R.lt_zero_false(xx), hh)))
    case 0n 1n+_qq:
      {==}
    case 1n+pp 1n+qq:
      lt_neq(pp, qq, hh)

# a number above another is not it
def gt_neq(+xx: Nat, +yy: Nat, hh: {Nat.is_lt(yy, xx) == True{} : Bool}) -> {Nat.is_eq(xx, yy) == False{} : Bool}:
  match xx yy:
    case 0n _yy:
      Empty.absurd({Nat.is_eq(0n, yy) == False{} : Bool}, U32L.false_true(Equal.trans(Bool, False{}, Nat.is_lt(yy,
        0n), True{}, R.lt_zero_false(yy), hh)))
    case 1n+_pp 0n:
      {==}
    case 1n+pp 1n+qq:
      gt_neq(pp, qq, hh)

# taking the same amount off two numbers it fits in keeps whether they are equal
def eq_sub(
  +aa: Nat,
  +xx: Nat,
  +yy: Nat,
  +hx: {Nat.is_le(aa, xx) == True{} : Bool},
  +hy: {Nat.is_le(aa, yy) == True{} : Bool}
) -> {Nat.is_eq(Nat.sub(xx, aa), Nat.sub(yy, aa)) == Nat.is_eq(xx, yy) : Bool}:
  match aa xx yy:
    case 0n _xx _yy:
      +ex = Equal.sym(Nat, Nat.sub(xx, 0n), xx, R.sub_zero(xx))
      +ey = Equal.sym(Nat, Nat.sub(yy, 0n), yy, R.sub_zero(yy))
      %ex : {Nat.is_eq(_, Nat.sub(yy, 0n)) == Nat.is_eq(xx, yy) : Bool}
      %ey : {Nat.is_eq(xx, _) == Nat.is_eq(xx, yy) : Bool}
      {==}
    case 1n+cc 0n _yy:
      Empty.absurd({Nat.is_eq(0n, Nat.sub(yy, 1n+cc)) == Nat.is_eq(0n, yy) : Bool}, U32L.false_true(hx))
    case 1n+cc 1n+_pp 0n:
      Empty.absurd({Nat.is_eq(Nat.sub(1n+_pp, 1n+cc), 0n) == Nat.is_eq(1n+_pp, 0n) : Bool}, U32L.false_true(hy))
    case 1n+cc 1n+pp 1n+qq:
      eq_sub(cc, pp, qq, hx, hy)

# ---- U32 halving ----

# padding a zero on top keeps a word's number
def pad_nat(+pp: Nat, +tt: Word(pp)) -> {Word.to_nat(1n+pp, Word.shr.pad(pp, tt)) == Word.to_nat(pp, tt) : Nat}:
  match pp:
    case 0n:
      match tt:
        case WNil{}:
          {==}
    case 1n+qq:
      match tt:
        case WCon{+bb, +rest}:
          match bb:
            case False{}:
              Equal.cong(Nat, Nat, nn => Nat.double(nn), Word.to_nat(1n+qq, Word.shr.pad(qq, rest)), Word.to_nat(qq,
                rest), pad_nat(qq, rest))
            case True{}:
              Equal.cong(Nat, Nat, nn => 1n+Nat.double(nn), Word.to_nat(1n+qq, Word.shr.pad(qq, rest)),
                Word.to_nat(qq, rest), pad_nat(qq, rest))

# U32 shr of the double of m is m
def shr_half(uu: U32, +mm: Nat, ee: {U32.to_nat(uu) == Nat.double(mm) : Nat}) -> {U32.to_nat(U32.shr(uu)) == mm :
  Nat}:
  match uu:
    case U32{+ww}:
      match ww:
        case WCon{+bb, +rest}:
          match bb:
            case False{}:
              Equal.trans(Nat, Word.to_nat(32n, Word.shr.pad(31n, rest)), Word.to_nat(31n, rest), mm, pad_nat(31n,
                rest), dbl_inj(Word.to_nat(31n, rest), mm, ee))
            case True{}:
              Empty.absurd({Word.to_nat(32n, Word.shr.pad(31n, rest)) == mm : Nat}, odd_even(Word.to_nat(31n, rest),
                mm, ee))

# ---- where two walks part ----

# the index a walk takes into the half it goes to is below the half's size
def ix_lt(
  zz: Bool,
  +ii: U32,
  +hh: U32,
  +ee: Nat,
  +ez: {U32.is_lt(ii, hh) == zz : Bool},
  +eh: {U32.to_nat(hh) == Nat.pow(2n, ee) : Nat},
  +hi: {Nat.is_lt(U32.to_nat(ii), Nat.double(Nat.pow(2n, ee))) == True{} : Bool}
) -> {Nat.is_lt(U32.to_nat(Bool.pick(U32, zz, ii, U32.sub(ii, hh))), Nat.pow(2n, ee)) == True{} : Bool}:
  match zz:
    case True{}:
      R.lt_rw_r(U32.to_nat(ii), U32.to_nat(hh), Nat.pow(2n, ee), eh, Equal.trans(Bool, Nat.is_lt(U32.to_nat(ii),
        U32.to_nat(hh)), U32.is_lt(ii, hh), True{}, Equal.sym(Bool, U32.is_lt(ii, hh), Nat.is_lt(U32.to_nat(ii),
        U32.to_nat(hh)), R.u32_lt(ii, hh)), ez))
    case False{}:
      +pw = Nat.pow(2n, ee)
      +ni = U32.to_nat(ii)
      +hle = {R.not_lt_le(ni, U32.to_nat(hh), Equal.trans(Bool, Nat.is_lt(ni, U32.to_nat(hh)), U32.is_lt(ii, hh),
        False{}, Equal.sym(Bool, U32.is_lt(ii, hh), Nat.is_lt(ni, U32.to_nat(hh)), R.u32_lt(ii, hh)), ez)) :
        {Nat.is_le(U32.to_nat(hh), ni) == True{} : Bool}}
      +es = {R.u32_sub_nat(ii, hh, hle) : {U32.to_nat(U32.sub(ii, hh)) == Nat.sub(ni, U32.to_nat(hh)) : Nat}}
      +hle2 = {R.le_rw_l(U32.to_nat(hh), pw, ni, eh, hle) : {Nat.is_le(pw, ni) == True{} : Bool}}
      +hlt = {R.lt_rw_r(ni, Nat.double(pw), Nat.add(pw, pw), R.double_add(pw), hi) :
        {Nat.is_lt(ni, Nat.add(pw, pw)) == True{} : Bool}}
      +hs = {R.sub_lt(pw, ni, pw, hle2, hlt) : {Nat.is_lt(Nat.sub(ni, pw), pw) == True{} : Bool}}
      +e2 = {Equal.trans(Nat, U32.to_nat(U32.sub(ii, hh)), Nat.sub(ni, U32.to_nat(hh)), Nat.sub(ni, pw), es,
        Equal.cong(Nat, Nat, xx => Nat.sub(ni, xx), U32.to_nat(hh), pw, eh)) :
        {U32.to_nat(U32.sub(ii, hh)) == Nat.sub(ni, pw) : Nat}}
      R.lt_rw_l(Nat.sub(ni, pw), U32.to_nat(U32.sub(ii, hh)), pw, Equal.sym(Nat, U32.to_nat(U32.sub(ii, hh)),
        Nat.sub(ni, pw), e2), hs)

# the U32 below-test as the Nat one
def lt_nat(
  +aa: U32,
  +bb: U32,
  +zz: Bool,
  ez: {U32.is_lt(aa, bb) == zz : Bool}
) -> {Nat.is_lt(U32.to_nat(aa), U32.to_nat(bb)) == zz : Bool}:
  Equal.trans(Bool, Nat.is_lt(U32.to_nat(aa), U32.to_nat(bb)), U32.is_lt(aa, bb), zz, Equal.sym(Bool, U32.is_lt(aa,
    bb), Nat.is_lt(U32.to_nat(aa), U32.to_nat(bb)), R.u32_lt(aa, bb)), ez)

# two walks end at one leaf exactly when the indices are equal, as same_nat says it
def SameNat(+ee: Nat, +hh: U32, +ii: U32, +jj: U32) -> Type:
  {same(ee, hh, ii, jj) == Nat.is_eq(U32.to_nat(ii), U32.to_nat(jj)) : Bool}

# at the root of a perfect tree: two walks end at one leaf exactly when their indices are equal, given the halves
def sn_if(
  zi: Bool,
  zj: Bool,
  +ee: Nat,
  +hh: U32,
  +ii: U32,
  +jj: U32,
  +ezi: {U32.is_lt(ii, hh) == zi : Bool},
  +ezj: {U32.is_lt(jj, hh) == zj : Bool},
  ih: SameNat(ee, hh, Bool.pick(U32, zi, ii, U32.sub(ii, hh)), Bool.pick(U32, zj, jj, U32.sub(jj, hh)))
) -> {same.if(zi, zj, same(ee, hh, Bool.pick(U32, zi, ii, U32.sub(ii, hh)), Bool.pick(U32, zj, jj, U32.sub(jj,
  hh)))) == Nat.is_eq(U32.to_nat(ii), U32.to_nat(jj)) : Bool}:
  match zi zj:
    case True{} True{}:
      ih
    case False{} False{}:
      +ni = U32.to_nat(ii)
      +nj = U32.to_nat(jj)
      +nh = U32.to_nat(hh)
      +hi = {R.not_lt_le(ni, nh, lt_nat(ii, hh, False{}, ezi)) : {Nat.is_le(nh, ni) == True{} : Bool}}
      +hj = {R.not_lt_le(nj, nh, lt_nat(jj, hh, False{}, ezj)) : {Nat.is_le(nh, nj) == True{} : Bool}}
      +es = {Equal.trans(Bool, Nat.is_eq(U32.to_nat(U32.sub(ii, hh)), U32.to_nat(U32.sub(jj, hh))),
        Nat.is_eq(Nat.sub(ni,
        nh), U32.to_nat(U32.sub(jj, hh))), Nat.is_eq(Nat.sub(ni, nh), Nat.sub(nj, nh)), Equal.cong(Nat, Bool,
        xx => Nat.is_eq(xx, U32.to_nat(U32.sub(jj, hh))), U32.to_nat(U32.sub(ii, hh)), Nat.sub(ni, nh),
        R.u32_sub_nat(ii, hh, hi)), Equal.cong(Nat, Bool, xx => Nat.is_eq(Nat.sub(ni, nh), xx), U32.to_nat(U32.sub(jj,
        hh)), Nat.sub(nj, nh), R.u32_sub_nat(jj, hh, hj))) : {Nat.is_eq(U32.to_nat(U32.sub(ii, hh)),
        U32.to_nat(U32.sub(jj, hh))) == Nat.is_eq(Nat.sub(ni, nh), Nat.sub(nj, nh)) : Bool}}
      Equal.trans(Bool, same(ee, hh, U32.sub(ii, hh), U32.sub(jj, hh)), Nat.is_eq(U32.to_nat(U32.sub(ii, hh)),
        U32.to_nat(U32.sub(jj, hh))), Nat.is_eq(ni, nj), ih, Equal.trans(Bool, Nat.is_eq(U32.to_nat(U32.sub(ii, hh)),
        U32.to_nat(U32.sub(jj, hh))), Nat.is_eq(Nat.sub(ni, nh), Nat.sub(nj, nh)), Nat.is_eq(ni, nj), es, eq_sub(nh,
        ni, nj, hi, hj)))
    case True{} False{}:
      +ni = U32.to_nat(ii)
      +nj = U32.to_nat(jj)
      +nh = U32.to_nat(hh)
      +hj = {R.not_lt_le(nj, nh, lt_nat(jj, hh, False{}, ezj)) : {Nat.is_le(nh, nj) == True{} : Bool}}
      Equal.sym(Bool, Nat.is_eq(ni, nj), False{}, lt_neq(ni, nj, R.lt_le_trans(ni, nh, nj, lt_nat(ii, hh, True{}, ezi),
        hj)))
    case False{} True{}:
      +ni = U32.to_nat(ii)
      +nj = U32.to_nat(jj)
      +nh = U32.to_nat(hh)
      +hi = {R.not_lt_le(ni, nh, lt_nat(ii, hh, False{}, ezi)) : {Nat.is_le(nh, ni) == True{} : Bool}}
      Equal.sym(Bool, Nat.is_eq(ni, nj), False{}, gt_neq(ni, nj, R.lt_le_trans(nj, nh, ni, lt_nat(jj, hh, True{}, ezj),
        hi)))

# two walks down a perfect tree of 2^d leaves, the root's size 2^d and both indices below it, end at one leaf
# exactly when the indices are equal
def same_nat(
  +dd: Nat,
  +nn: U32,
  +ii: U32,
  +jj: U32,
  +hn: {U32.to_nat(nn) == Nat.pow(2n, dd) : Nat},
  +hi: {Nat.is_lt(U32.to_nat(ii), Nat.pow(2n, dd)) == True{} : Bool},
  +hj: {Nat.is_lt(U32.to_nat(jj), Nat.pow(2n, dd)) == True{} : Bool}
) -> {same(dd, nn, ii, jj) == Nat.is_eq(U32.to_nat(ii), U32.to_nat(jj)) : Bool}:
  match dd:
    case 0n:
      +ei = Equal.sym(Nat, U32.to_nat(ii), 0n, lt1_zero(U32.to_nat(ii), hi))
      +ej = Equal.sym(Nat, U32.to_nat(jj), 0n, lt1_zero(U32.to_nat(jj), hj))
      %ei : {True{} == Nat.is_eq(_, U32.to_nat(jj)) : Bool}
      %ej : {True{} == Nat.is_eq(0n, _) : Bool}
      {==}
    case 1n+ee:
      +hh = U32.shr(nn)
      +pw = Nat.pow(2n, ee)
      +sp = {R.pow2_succ(ee) : {Nat.pow(2n, 1n+ee) == Nat.double(pw) : Nat}}
      +eh = {shr_half(nn, pw, Equal.trans(Nat, U32.to_nat(nn), Nat.pow(2n, 1n+ee), Nat.double(pw), hn, sp)) :
        {U32.to_nat(hh) == pw : Nat}}
      +hi2 = {R.lt_rw_r(U32.to_nat(ii), Nat.pow(2n, 1n+ee), Nat.double(pw), sp, hi) :
        {Nat.is_lt(U32.to_nat(ii), Nat.double(pw)) == True{} : Bool}}
      +hj2 = {R.lt_rw_r(U32.to_nat(jj), Nat.pow(2n, 1n+ee), Nat.double(pw), sp, hj) :
        {Nat.is_lt(U32.to_nat(jj), Nat.double(pw)) == True{} : Bool}}
      +ix = Bool.pick(U32, U32.is_lt(ii, hh), ii, U32.sub(ii, hh))
      +jx = Bool.pick(U32, U32.is_lt(jj, hh), jj, U32.sub(jj, hh))
      sn_if(U32.is_lt(ii, hh), U32.is_lt(jj, hh), ee, hh, ii, jj, {==}, {==}, same_nat(ee, hh, ix, jx, eh,
        ix_lt(U32.is_lt(ii, hh), ii, hh, ee, {==}, eh, hi2), ix_lt(U32.is_lt(jj, hh), jj, hh, ee, {==}, eh, hj2)))

# ---- the mask ----

# and with True keeps a bit
def band_true(bb: Bool) -> {Bool.and(bb, True{}) == bb : Bool}:
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# a double below one is of zero
def dbl_lt1(+xx: Nat, +hh: {Nat.is_lt(Nat.double(xx), 1n) == True{} : Bool}) -> {Nat.is_lt(xx, 1n) == True{} : Bool}:
  match xx:
    case 0n:
      {==}
    case 1n+pp:
      Empty.absurd({Nat.is_lt(1n+pp, 1n) == True{} : Bool}, U32L.false_true(hh))

# a mask of no ones: its bit is clear, and the rest is a mask of no ones
def mw.u0(
  +qq: Nat,
  cc: Bool,
  +uu: Word(qq),
  +hm: {1n+Word.to_nat(1n+qq, WCon{cc, uu}) == 1n : Nat}
) -> {1n+Word.to_nat(qq, uu) == 1n : Nat}:
  match cc:
    case True{}:
      Empty.absurd({1n+Word.to_nat(qq, uu) == 1n : Nat}, succ_ne(Nat.double(Word.to_nat(qq, uu)),
        succ_inj(1n+Nat.double(Word.to_nat(qq, uu)), 0n, hm)))
    case False{}:
      +un = Word.to_nat(qq, uu)
      Equal.cong(Nat, Nat, xx => 1n+xx, un, 0n, dbl_inj(un, 0n, succ_inj(Nat.double(un), 0n, hm)))

# a word below one: its bit is clear, and the rest is below one
def mw.t0(
  +qq: Nat,
  bb: Bool,
  +tt: Word(qq),
  +hw: {Nat.is_lt(Word.to_nat(1n+qq, WCon{bb, tt}), 1n) == True{} : Bool}
) -> {Nat.is_lt(Word.to_nat(qq, tt), 1n) == True{} : Bool}:
  match bb:
    case True{}:
      Empty.absurd({Nat.is_lt(Word.to_nat(qq, tt), 1n) == True{} : Bool}, U32L.false_true(Equal.trans(Bool, False{},
        Nat.is_lt(Nat.double(Word.to_nat(qq, tt)), 0n), True{}, R.lt_zero_false(Nat.double(Word.to_nat(qq, tt))), hw)))
    case False{}:
      dbl_lt1(Word.to_nat(qq, tt), hw)

# the lowest bit of a word below one, and with the lowest bit of a mask of no ones: the word's bit
def mw.a0(
  bb: Bool,
  cc: Bool,
  +qq: Nat,
  +tt: Word(qq),
  +hw: {Nat.is_lt(Word.to_nat(1n+qq, WCon{bb, tt}), 1n) == True{} : Bool}
) -> {Bool.and(bb, cc) == bb : Bool}:
  match bb cc:
    case False{} _cc:
      {==}
    case True{} True{}:
      {==}
    case True{} False{}:
      Empty.absurd({False{} == True{} : Bool}, U32L.false_true(Equal.trans(Bool, False{},
        Nat.is_lt(Nat.double(Word.to_nat(qq, tt)), 0n), True{}, R.lt_zero_false(Nat.double(Word.to_nat(qq, tt))), hw)))

# a mask of f + 1 ones: its bit is set, and the rest is a mask of f ones
def mw.u1(
  +qq: Nat,
  +ff: Nat,
  cc: Bool,
  +uu: Word(qq),
  +hm: {1n+Word.to_nat(1n+qq, WCon{cc, uu}) == Nat.pow(2n, 1n+ff) : Nat}
) -> {1n+Word.to_nat(qq, uu) == Nat.pow(2n, ff) : Nat}:
  match cc:
    case False{}:
      Empty.absurd({1n+Word.to_nat(qq, uu) == Nat.pow(2n, ff) : Nat}, odd_even(Word.to_nat(qq, uu), Nat.pow(2n, ff),
        Equal.trans(Nat, 1n+Nat.double(Word.to_nat(qq, uu)), Nat.pow(2n, 1n+ff), Nat.double(Nat.pow(2n, ff)), hm,
        R.pow2_succ(ff))))
    case True{}:
      +un = Word.to_nat(qq, uu)
      dbl_inj(1n+un, Nat.pow(2n, ff), Equal.trans(Nat, 2n+Nat.double(un), Nat.pow(2n, 1n+ff), Nat.double(Nat.pow(2n,
        ff)), hm, R.pow2_succ(ff)))

# any bit and with the lowest bit of a mask of f + 1 ones: the bit
def mw.a1(
  bb: Bool,
  cc: Bool,
  +qq: Nat,
  +ff: Nat,
  +uu: Word(qq),
  +hm: {1n+Word.to_nat(1n+qq, WCon{cc, uu}) == Nat.pow(2n, 1n+ff) : Nat}
) -> {Bool.and(bb, cc) == bb : Bool}:
  match cc:
    case False{}:
      Empty.absurd({Bool.and(bb, False{}) == bb : Bool}, odd_even(Word.to_nat(qq, uu), Nat.pow(2n, ff),
        Equal.trans(Nat, 1n+Nat.double(Word.to_nat(qq, uu)), Nat.pow(2n, 1n+ff), Nat.double(Nat.pow(2n, ff)), hm,
        R.pow2_succ(ff))))
    case True{}:
      band_true(bb)

# a word and a mask of e ones, below 2^e: the word
def mask_w(
  +pp: Nat,
  +ee: Nat,
  +ww: Word(pp),
  +mw: Word(pp),
  +hm: {1n+Word.to_nat(pp, mw) == Nat.pow(2n, ee) : Nat},
  +hw: {Nat.is_lt(Word.to_nat(pp, ww), Nat.pow(2n, ee)) == True{} : Bool}
) -> {Word.and(pp, ww, mw) == ww : Word(pp)}:
  match pp ee:
    case 0n _ee:
      match ww mw:
        case WNil{} WNil{}:
          {==}
    case 1n+qq 0n:
      match ww mw:
        case WCon{+bb, +tt} WCon{+cc, +uu}:
          +ea = {mask_w(qq, 0n, tt, uu, mw.u0(qq, cc, uu, hm), mw.t0(qq, bb, tt, hw)) : {Word.and(qq, tt, uu) == tt :
            Word(qq)}}
          Equal.trans(Word(1n+qq), WCon{Bool.and(bb, cc), Word.and(qq, tt, uu)}, WCon{bb, Word.and(qq, tt, uu)},
            WCon{bb, tt}, Equal.cong(Bool, Word(1n+qq), xx => WCon{xx, Word.and(qq, tt, uu)}, Bool.and(bb, cc), bb,
            mw.a0(bb, cc, qq, tt, hw)), Equal.cong(Word(qq), Word(1n+qq), xx => WCon{bb, xx}, Word.and(qq, tt,
            uu), tt, ea))
    case 1n+qq 1n+ff:
      match ww mw:
        case WCon{+bb, +tt} WCon{+cc, +uu}:
          +tn = Word.to_nat(qq, tt)
          +pw = Nat.pow(2n, ff)
          +hx = {R.lt_rw_l(Word.to_nat(1n+qq, WCon{bb, tt}), Nat.add(R.bit(bb), Nat.double(tn)), Nat.double(pw),
            R.to_nat_con(qq, bb, tt), R.lt_rw_r(Word.to_nat(1n+qq, WCon{bb, tt}), Nat.pow(2n, 1n+ff),
            Nat.double(pw), R.pow2_succ(ff), hw)) : {Nat.is_lt(Nat.add(R.bit(bb), Nat.double(tn)),
            Nat.double(pw)) == True{} : Bool}}
          +ea = {mask_w(qq, ff, tt, uu, mw.u1(qq, ff, cc, uu, hm), R.lt_half(bb, tn, pw, hx)) : {Word.and(qq, tt, uu) ==
            tt : Word(qq)}}
          Equal.trans(Word(1n+qq), WCon{Bool.and(bb, cc), Word.and(qq, tt, uu)}, WCon{bb, Word.and(qq, tt, uu)},
            WCon{bb, tt}, Equal.cong(Bool, Word(1n+qq), xx => WCon{xx, Word.and(qq, tt, uu)}, Bool.and(bb, cc), bb,
            mw.a1(bb, cc, qq, ff, uu, hm)), Equal.cong(Word(qq), Word(1n+qq), xx => WCon{bb, xx}, Word.and(qq, tt,
            uu), tt, ea))

# a U32 and a mask of e ones, below 2^e: the U32
def mask_u(
  +ii: U32,
  +mm: U32,
  +ee: Nat,
  +hm: {1n+U32.to_nat(mm) == Nat.pow(2n, ee) : Nat},
  +hi: {Nat.is_lt(U32.to_nat(ii), Nat.pow(2n, ee)) == True{} : Bool}
) -> {U32.and(ii, mm) == ii : U32}:
  match ii mm:
    case U32{+ww} U32{+mw}:
      Equal.cong(Word(32n), U32, xx => U32{xx}, Word.and(32n, ww, mw), ww, mask_w(32n, ee, ww, mw, hm, hi))

# an index below a size of 2^d, masked as Array.get and Array.set mask it: the index
def mask_id(
  +ii: U32,
  +nn: U32,
  +dd: Nat,
  +hn: {U32.to_nat(nn) == Nat.pow(2n, dd) : Nat},
  +hi: {Nat.is_lt(U32.to_nat(ii), Nat.pow(2n, dd)) == True{} : Bool}
) -> {mask(ii, nn) == ii : U32}:
  +pw = Nat.pow(2n, dd)
  +h1 = {R.le_rw_r(1n, pw, U32.to_nat(nn), Equal.sym(Nat, U32.to_nat(nn), pw, hn), Equal.trans(Bool, Nat.is_le(1n,
    pw), Nat.is_lt(0n, pw), True{}, Equal.sym(Bool, Nat.is_lt(0n, pw), Nat.is_le(1n, pw), R.lt_le_succ(0n, pw)),
    pow_pos(dd))) : {Nat.is_le(1n, U32.to_nat(nn)) == True{} : Bool}}
  +es = {R.u32_sub_nat(nn, 1, h1) : {U32.to_nat(U32.sub(nn, 1)) == Nat.sub(U32.to_nat(nn), 1n) : Nat}}
  +hm = {Equal.trans(Nat, 1n+U32.to_nat(U32.sub(nn, 1)), Nat.add(1n, Nat.sub(U32.to_nat(nn), 1n)), pw,
    Equal.cong(Nat, Nat, xx => 1n+xx, U32.to_nat(U32.sub(nn, 1)), Nat.sub(U32.to_nat(nn), 1n), es), Equal.trans(Nat,
    Nat.add(1n, Nat.sub(U32.to_nat(nn), 1n)), U32.to_nat(nn), pw, R.add_sub(1n, U32.to_nat(nn), h1), hn)) :
    {1n+U32.to_nat(U32.sub(nn, 1)) == pw : Nat}}
  mask_u(ii, U32.sub(nn, 1), dd, hm, hi)

# ---- Array.get after Array.set, on the tree ----

# the value Array.get finds in a tree's array
def at(+tt: Tr, +jj: U32) -> U32:
  get(tt, size(tt), mask(jj, size(tt)))

# a read after a write to a perfect tree of 2^d leaves, d below 32, both indices below 2^d: the written value
# when the indices are equal, else the value there before
def at_set(
  +dd: Nat,
  +tt: Tr,
  +ii: U32,
  +jj: U32,
  +vv: U32,
  +hp: {pf(dd, tt) == True{} : Bool},
  +hd: {Nat.is_lt(dd, 32n) == True{} : Bool},
  +hi: {Nat.is_lt(U32.to_nat(ii), Nat.pow(2n, dd)) == True{} : Bool},
  +hj: {Nat.is_lt(U32.to_nat(jj), Nat.pow(2n, dd)) == True{} : Bool}
) -> {at(set(tt, ii, vv), jj) == after(Nat.is_eq(U32.to_nat(ii), U32.to_nat(jj)), vv, at(tt, jj)) : U32}:
  +ss = size(tt)
  +mi = mask(ii, ss)
  +mj = mask(jj, ss)
  +pt = put(tt, ss, mi, vv)
  +hs = {size_nat(dd, tt, hp, hd) : {U32.to_nat(ss) == Nat.pow(2n, dd) : Nat}}
  +e1 = {Equal.cong(U32, U32, nn => get(pt, nn, mask(jj, nn)), size(pt), ss, size_put(tt, ss, mi, vv)) :
    {get(pt, size(pt), mask(jj, size(pt))) == get(pt, ss, mj) : U32}}
  +e2 = {get_put(dd, tt, ss, mi, mj, vv, hp) : {get(pt, ss, mj) == after(same(dd, ss, mi, mj), vv, get(tt, ss, mj)) :
    U32}}
  +e3 = {Equal.trans(Bool, same(dd, ss, mi, mj), same(dd, ss, ii, mj), same(dd, ss, ii, jj), Equal.cong(U32, Bool,
    xx => same(dd, ss, xx, mj), mi, ii, mask_id(ii, ss, dd, hs, hi)), Equal.cong(U32, Bool, xx => same(dd, ss, ii, xx),
    mj, jj, mask_id(jj, ss, dd, hs, hj))) : {same(dd, ss, mi, mj) == same(dd, ss, ii, jj) : Bool}}
  +e4 = {Equal.trans(Bool, same(dd, ss, mi, mj), same(dd, ss, ii, jj), Nat.is_eq(U32.to_nat(ii), U32.to_nat(jj)), e3,
    same_nat(dd, ss, ii, jj, hs, hi, hj)) : {same(dd, ss, mi, mj) == Nat.is_eq(U32.to_nat(ii), U32.to_nat(jj)) : Bool}}
  Equal.trans(U32, get(pt, size(pt), mask(jj, size(pt))), get(pt, ss, mj), after(Nat.is_eq(U32.to_nat(ii),
    U32.to_nat(jj)), vv, get(tt, ss, mj)), e1, Equal.trans(U32, get(pt, ss, mj), after(same(dd, ss, mi, mj), vv,
    get(tt, ss, mj)), after(Nat.is_eq(U32.to_nat(ii), U32.to_nat(jj)), vv, get(tt, ss, mj)), e2, Equal.cong(Bool, U32,
    bb => after(bb, vv, get(tt, ss, mj)), same(dd, ss, mi, mj), Nat.is_eq(U32.to_nat(ii), U32.to_nat(jj)), e4)))

# a write to a perfect tree leaves it perfect
def pf_set(
  +dd: Nat,
  +tt: Tr,
  +ii: U32,
  +vv: U32,
  +hp: {pf(dd, tt) == True{} : Bool}
) -> {pf(dd, set(tt, ii, vv)) == True{} : Bool}:
  Equal.trans(Bool, pf(dd, set(tt, ii, vv)), pf(dd, tt), True{}, pf_put(dd, tt, size(tt), mask(ii, size(tt)), vv), hp)

# a read at the index just written finds the value, in any tree
def at_set_same(+tt: Tr, +ii: U32, +vv: U32) -> {at(set(tt, ii, vv), ii) == vv : U32}:
  +ss = size(tt)
  +pt = put(tt, ss, mask(ii, ss), vv)
  Equal.trans(U32, get(pt, size(pt), mask(ii, size(pt))), get(pt, ss, mask(ii, ss)), vv, Equal.cong(U32, U32,
    nn => get(pt, nn, mask(ii, nn)), size(pt), ss, size_put(tt, ss, mask(ii, ss), vv)), get_put_same(tt, ss, mask(ii,
    ss), vv))

# ---- the laws on arrays ----

# a tree's array is perfect exactly when the tree is
def perfect_arr(+dd: Nat, +tt: Tr) -> {Laws.jpg.perfect(dd, arr(tt)) == pf(dd, tt) : Bool}:
  match dd tt:
    case 0n TLeaf{_xx}:
      {==}
    case 0n TNode{_lo, _hi}:
      {==}
    case 1n+_ee TLeaf{_xx}:
      {==}
    case 1n+ee TNode{lo, hi}:
      Equal.trans(Bool, Bool.and(Laws.jpg.perfect(ee, arr(lo)), Laws.jpg.perfect(ee, arr(hi))), Bool.and(pf(ee, lo),
        Laws.jpg.perfect(ee, arr(hi))), Bool.and(pf(ee, lo), pf(ee, hi)), Equal.cong(Bool, Bool, bb => Bool.and(bb,
        Laws.jpg.perfect(ee, arr(hi))), Laws.jpg.perfect(ee, arr(lo)), pf(ee, lo), perfect_arr(ee, lo)),
        Equal.cong(Bool, Bool, bb => Bool.and(pf(ee, lo), bb), Laws.jpg.perfect(ee, arr(hi)), pf(ee, hi),
        perfect_arr(ee, hi)))

# a perfect plane's tree is perfect
def pf_of(
  +dd: Nat,
  -aa: Array<U32>,
  +tt: Tr,
  +ea: {aa == arr(tt) : Array<U32>},
  +hp: {Laws.jpg.perfect(dd, aa) == True{} : Bool}
) -> {pf(dd, tt) == True{} : Bool}:
  Equal.trans(Bool, pf(dd, tt), Laws.jpg.perfect(dd, arr(tt)), True{}, Equal.sym(Bool, Laws.jpg.perfect(dd, arr(tt)),
    pf(dd, tt), perfect_arr(dd, tt)), Equal.trans(Bool, Laws.jpg.perfect(dd, arr(tt)), Laws.jpg.perfect(dd, aa), True{},
    Equal.sym(Bool, Laws.jpg.perfect(dd, aa), Laws.jpg.perfect(dd, arr(tt)), Equal.cong(Array<U32>, Bool,
    xx => Laws.jpg.perfect(dd, xx), aa, arr(tt), ea)), hp))

# the value Array.get finds in a tree's array after Array.set: at, after set
def val_set(
  +tt: Tr,
  +ii: U32,
  +vv: U32,
  +jj: U32
) -> {Laws.jpg.val(Array.get(U32, Array.set(U32, arr(tt), ii, vv), jj)) == at(set(tt, ii, vv), jj) : U32}:
  se = Equal.sym(Array<U32>, Array.set(U32, arr(tt), ii, vv), arr(set(tt, ii, vv)), set_arr(tt, ii, vv))
  %se : {Laws.jpg.val(Array.get(U32, _, jj)) == at(set(tt, ii, vv), jj) : U32}
  sg = Equal.sym(Array<U32> & U32, Array.get(U32, arr(set(tt, ii, vv)), jj), (arr(set(tt, ii, vv)), at(set(tt, ii,
    vv), jj)), get_arr(set(tt, ii, vv), jj))
  %sg : {Laws.jpg.val(_) == at(set(tt, ii, vv), jj) : U32}
  {==}

# the value Array.get finds in a tree's array: at
def val_at(+tt: Tr, +jj: U32) -> {Laws.jpg.val(Array.get(U32, arr(tt), jj)) == at(tt, jj) : U32}:
  sg = Equal.sym(Array<U32> & U32, Array.get(U32, arr(tt), jj), (arr(tt), at(tt, jj)), get_arr(tt, jj))
  %sg : {Laws.jpg.val(_) == at(tt, jj) : U32}
  {==}

# jpeg_get_set, from a tree the plane is the array of
def get_same_of(
  -plane: Array<U32>,
  +ii: U32,
  +vv: U32,
  oo: Of(plane)
) -> {Laws.jpg.val(Array.get(U32, Array.set(U32, plane, ii, vv), ii)) == vv : U32}:
  (+tt, ep) = oo
  sp = Equal.sym(Array<U32>, plane, arr(tt), ep)
  %sp : {Laws.jpg.val(Array.get(U32, Array.set(U32, _, ii, vv), ii)) == vv : U32}
  Equal.trans(U32, Laws.jpg.val(Array.get(U32, Array.set(U32, arr(tt), ii, vv), ii)), at(set(tt, ii, vv),
    ii), vv, val_set(tt, ii, vv, ii), at_set_same(tt, ii, vv))

# jpeg_get_set_other, from a tree the plane is the array of
def get_other_of(
  +dd: Nat,
  -plane: Array<U32>,
  +h_perfect: {Laws.jpg.perfect(dd, plane) == True{} : Bool},
  +h_dd: {Nat.is_lt(dd, 32n) == True{} : Bool},
  +ii: U32,
  +jj: U32,
  +vv: U32,
  +h_ii: {Nat.is_lt(U32.to_nat(ii), Nat.pow(2n, dd)) == True{} : Bool},
  +h_jj: {Nat.is_lt(U32.to_nat(jj), Nat.pow(2n, dd)) == True{} : Bool},
  +h_ne: {U32.is_eq(ii, jj) == False{} : Bool},
  oo: Of(plane)
) -> {Laws.jpg.val(Array.get(U32, Array.set(U32, plane, ii, vv), jj)) == Laws.jpg.val(Array.get(U32, plane, jj)) :
  U32}:
  (+tt, ep) = oo
  +sp = {Equal.sym(Array<U32>, plane, arr(tt), ep) : {arr(tt) == plane : Array<U32>}}
  +hp = pf_of(dd, plane, tt, Equal.sym(Array<U32>, arr(tt), plane, sp), h_perfect)
  %sp : {Laws.jpg.val(Array.get(U32, Array.set(U32, _, ii, vv), jj)) == Laws.jpg.val(Array.get(U32, _, jj)) : U32}
  +eq = {Equal.trans(Bool, Nat.is_eq(U32.to_nat(ii), U32.to_nat(jj)), U32.is_eq(ii, jj), False{}, Equal.sym(Bool,
    U32.is_eq(ii, jj), Nat.is_eq(U32.to_nat(ii), U32.to_nat(jj)), R.u32_eq(ii, jj)), h_ne) :
    {Nat.is_eq(U32.to_nat(ii), U32.to_nat(jj)) == False{} : Bool}}
  Equal.trans(U32, Laws.jpg.val(Array.get(U32, Array.set(U32, arr(tt), ii, vv), jj)), at(set(tt, ii, vv),
    jj), Laws.jpg.val(Array.get(U32, arr(tt), jj)), val_set(tt, ii, vv, jj), Equal.trans(U32,
    at(set(tt, ii, vv), jj), after(Nat.is_eq(U32.to_nat(ii), U32.to_nat(jj)), vv, at(tt, jj)),
    Laws.jpg.val(Array.get(U32, arr(tt), jj)), at_set(dd, tt, ii, jj, vv, hp, h_dd, h_ii, h_jj),
    Equal.trans(U32, after(Nat.is_eq(U32.to_nat(ii), U32.to_nat(jj)), vv, at(tt, jj)), at(tt, jj),
    Laws.jpg.val(Array.get(U32, arr(tt), jj)), Equal.cong(Bool, U32, bb => after(bb, vv, at(tt, jj)),
    Nat.is_eq(U32.to_nat(ii), U32.to_nat(jj)), False{}, eq), Equal.sym(U32, Laws.jpg.val(Array.get(U32, arr(tt),
    jj)), at(tt, jj), val_at(tt, jj)))))

# ---- painting a block, on the tree ----

# decode.splat.in on the tree
def inT(xin: Bool, yin: Bool, +tt: Tr, +xx: U32, +yy: U32, +ww: U32, +vv: U32) -> Tr:
  match xin yin:
    case True{} True{}:
      set(tt, (yy * ww + xx : U32), vv)
    case True{} False{}:
      tt
    case False{} _yin:
      tt

# decode.splat.px on the tree
def pxT(left: Nat, +tt: Tr, +x0: U32, +yy: U32, +px: U32, +ww: U32, +hh: U32, +vv: U32) -> Tr:
  match left:
    case 0n:
      tt
    case 1n+pp:
      pxT(pp, inT(U32.is_lt((x0 + px : U32), ww), U32.is_lt(yy, hh), tt, (x0 + px : U32), yy, ww, vv), x0, yy,
        (px + 1 : U32), ww, hh, vv)

# decode.splat.py on the tree
def pyT(left: Nat, +tt: Tr, +x0: U32, +y0: U32, +py: U32, +pw: U32, +ww: U32, +hh: U32, +vv: U32) -> Tr:
  match left:
    case 0n:
      tt
    case 1n+pp:
      pyT(pp, pxT(U32.to_nat(pw), tt, x0, (y0 + py : U32), 0, ww, hh, vv), x0, y0, (py + 1 : U32), pw, ww, hh, vv)

# decode.splat.col on the tree
def colT(
  left: Nat,
  +tt: Tr,
  +samples: List<&2, U32>,
  +row: U32,
  +col: U32,
  +ox: U32,
  +oy: U32,
  +pw: U32,
  +ph: U32,
  +ww: U32,
  +hh: U32
) -> Tr:
  match left:
    case 0n:
      tt
    case 1n+pp:
      colT(pp, pyT(U32.to_nat(ph), tt, (ox + col * pw : U32), (oy + row * ph : U32), 0, pw, ww, hh,
        Jpeg.decode.at(samples, (row * 8 + col : U32))), samples, row, (col + 1 : U32), ox, oy, pw, ph, ww, hh)

# decode.splat on the tree
def cvT(
  left: Nat,
  +tt: Tr,
  +samples: List<&2, U32>,
  +row: U32,
  +ox: U32,
  +oy: U32,
  +pw: U32,
  +ph: U32,
  +ww: U32,
  +hh: U32
) -> Tr:
  match left:
    case 0n:
      tt
    case 1n+pp:
      cvT(pp, colT(8n, tt, samples, row, 0, ox, oy, pw, ph, ww, hh), samples, (row + 1 : U32), ox, oy, pw, ph, ww, hh)

# the decoder's pixel write on a tree's array is the tree's
def arr_in(
  xin: Bool,
  yin: Bool,
  +tt: Tr,
  +xx: U32,
  +yy: U32,
  +ww: U32,
  +vv: U32
) -> {Jpeg.decode.splat.in(xin, yin, arr(tt), xx, yy, ww, vv) == arr(inT(xin, yin, tt, xx, yy, ww, vv)) : Array<U32>}:
  match xin yin:
    case True{} True{}:
      set_arr(tt, (yy * ww + xx : U32), vv)
    case True{} False{}:
      {==}
    case False{} _yin:
      {==}

# the decoder's pixel row on a tree's array is the tree's
def arr_px(
  left: Nat,
  +tt: Tr,
  +x0: U32,
  +yy: U32,
  +px: U32,
  +ww: U32,
  +hh: U32,
  +vv: U32
) -> {Jpeg.decode.splat.px(left, arr(tt), x0, yy, px, ww, hh, vv) == arr(pxT(left, tt, x0, yy, px, ww, hh, vv)) :
  Array<U32>}:
  match left:
    case 0n:
      {==}
    case 1n+pp:
      +xin = U32.is_lt((x0 + px : U32), ww)
      +yin = U32.is_lt(yy, hh)
      +t1 = inT(xin, yin, tt, (x0 + px : U32), yy, ww, vv)
      se = Equal.sym(Array<U32>, Jpeg.decode.splat.in(xin, yin, arr(tt), (x0 + px : U32), yy, ww, vv), arr(t1),
        arr_in(xin, yin, tt, (x0 + px : U32), yy, ww, vv))
      %se : {Jpeg.decode.splat.px(pp, _, x0, yy, (px + 1 : U32), ww, hh, vv) == arr(pxT(pp, t1, x0, yy, (px + 1 : U32),
        ww, hh, vv)) : Array<U32>}
      arr_px(pp, t1, x0, yy, (px + 1 : U32), ww, hh, vv)

# the decoder's cover of one sample on a tree's array is the tree's
def arr_py(
  left: Nat,
  +tt: Tr,
  +x0: U32,
  +y0: U32,
  +py: U32,
  +pw: U32,
  +ww: U32,
  +hh: U32,
  +vv: U32
) -> {Jpeg.decode.splat.py(left, arr(tt), x0, y0, py, pw, ww, hh, vv) == arr(pyT(left, tt, x0, y0, py, pw, ww, hh,
  vv)) :
  Array<U32>}:
  match left:
    case 0n:
      {==}
    case 1n+pp:
      +t1 = pxT(U32.to_nat(pw), tt, x0, (y0 + py : U32), 0, ww, hh, vv)
      se = Equal.sym(Array<U32>, Jpeg.decode.splat.px(U32.to_nat(pw), arr(tt), x0, (y0 + py : U32), 0, ww, hh, vv),
        arr(t1), arr_px(U32.to_nat(pw), tt, x0, (y0 + py : U32), 0, ww, hh, vv))
      %se : {Jpeg.decode.splat.py(pp, _, x0, y0, (py + 1 : U32), pw, ww, hh, vv) == arr(pyT(pp, t1, x0, y0,
        (py + 1 : U32), pw, ww, hh, vv)) : Array<U32>}
      arr_py(pp, t1, x0, y0, (py + 1 : U32), pw, ww, hh, vv)

# the decoder's block row on a tree's array is the tree's
def arr_col(
  left: Nat,
  +tt: Tr,
  +samples: List<&2, U32>,
  +row: U32,
  +col: U32,
  +ox: U32,
  +oy: U32,
  +pw: U32,
  +ph: U32,
  +ww: U32,
  +hh: U32
) -> {Jpeg.decode.splat.col(left, arr(tt), samples, row, col, ox, oy, pw, ph, ww, hh) == arr(colT(left, tt, samples,
  row, col, ox, oy, pw, ph, ww, hh)) : Array<U32>}:
  match left:
    case 0n:
      {==}
    case 1n+pp:
      +x0 = (ox + col * pw : U32)
      +y0 = (oy + row * ph : U32)
      +vv = Jpeg.decode.at(samples, (row * 8 + col : U32))
      +t1 = pyT(U32.to_nat(ph), tt, x0, y0, 0, pw, ww, hh, vv)
      se = Equal.sym(Array<U32>, Jpeg.decode.splat.py(U32.to_nat(ph), arr(tt), x0, y0, 0, pw, ww, hh, vv), arr(t1),
        arr_py(U32.to_nat(ph), tt, x0, y0, 0, pw, ww, hh, vv))
      %se : {Jpeg.decode.splat.col(pp, _, samples, row, (col + 1 : U32), ox, oy, pw, ph, ww, hh) == arr(colT(pp, t1,
        samples, row, (col + 1 : U32), ox, oy, pw, ph, ww, hh)) : Array<U32>}
      arr_col(pp, t1, samples, row, (col + 1 : U32), ox, oy, pw, ph, ww, hh)

# the decoder's block on a tree's array is the tree's
def arr_cv(
  left: Nat,
  +tt: Tr,
  +samples: List<&2, U32>,
  +row: U32,
  +ox: U32,
  +oy: U32,
  +pw: U32,
  +ph: U32,
  +ww: U32,
  +hh: U32
) -> {Jpeg.decode.splat(left, arr(tt), samples, row, ox, oy, pw, ph, ww, hh) == arr(cvT(left, tt, samples, row, ox, oy,
  pw, ph, ww, hh)) : Array<U32>}:
  match left:
    case 0n:
      {==}
    case 1n+pp:
      +t1 = colT(8n, tt, samples, row, 0, ox, oy, pw, ph, ww, hh)
      se = Equal.sym(Array<U32>, Jpeg.decode.splat.col(8n, arr(tt), samples, row, 0, ox, oy, pw, ph, ww, hh), arr(t1),
        arr_col(8n, tt, samples, row, 0, ox, oy, pw, ph, ww, hh))
      %se : {Jpeg.decode.splat(pp, _, samples, (row + 1 : U32), ox, oy, pw, ph, ww, hh) == arr(cvT(pp, t1, samples,
        (row + 1 : U32), ox, oy, pw, ph, ww, hh)) : Array<U32>}
      arr_cv(pp, t1, samples, (row + 1 : U32), ox, oy, pw, ph, ww, hh)

# a pixel write keeps a tree perfect
def pf_in(
  xin: Bool,
  yin: Bool,
  +dd: Nat,
  +tt: Tr,
  +xx: U32,
  +yy: U32,
  +ww: U32,
  +vv: U32,
  +hp: {pf(dd, tt) == True{} : Bool}
) -> {pf(dd, inT(xin, yin, tt, xx, yy, ww, vv)) == True{} : Bool}:
  match xin yin:
    case True{} True{}:
      pf_set(dd, tt, (yy * ww + xx : U32), vv, hp)
    case True{} False{}:
      hp
    case False{} _yin:
      hp

# a pixel row keeps a tree perfect
def pf_px(
  left: Nat,
  +dd: Nat,
  +tt: Tr,
  +x0: U32,
  +yy: U32,
  +px: U32,
  +ww: U32,
  +hh: U32,
  +vv: U32,
  +hp: {pf(dd, tt) == True{} : Bool}
) -> {pf(dd, pxT(left, tt, x0, yy, px, ww, hh, vv)) == True{} : Bool}:
  match left:
    case 0n:
      hp
    case 1n+pp:
      +xin = U32.is_lt((x0 + px : U32), ww)
      +yin = U32.is_lt(yy, hh)
      pf_px(pp, dd, inT(xin, yin, tt, (x0 + px : U32), yy, ww, vv), x0, yy, (px + 1 : U32), ww, hh, vv, pf_in(xin, yin,
        dd, tt, (x0 + px : U32), yy, ww, vv, hp))

# a sample's cover keeps a tree perfect
def pf_py(
  left: Nat,
  +dd: Nat,
  +tt: Tr,
  +x0: U32,
  +y0: U32,
  +py: U32,
  +pw: U32,
  +ww: U32,
  +hh: U32,
  +vv: U32,
  +hp: {pf(dd, tt) == True{} : Bool}
) -> {pf(dd, pyT(left, tt, x0, y0, py, pw, ww, hh, vv)) == True{} : Bool}:
  match left:
    case 0n:
      hp
    case 1n+pp:
      pf_py(pp, dd, pxT(U32.to_nat(pw), tt, x0, (y0 + py : U32), 0, ww, hh, vv), x0, y0, (py + 1 : U32), pw, ww, hh, vv,
        pf_px(U32.to_nat(pw), dd, tt, x0, (y0 + py : U32), 0, ww, hh, vv, hp))

# a block row keeps a tree perfect
def pf_col(
  left: Nat,
  +dd: Nat,
  +tt: Tr,
  +samples: List<&2, U32>,
  +row: U32,
  +col: U32,
  +ox: U32,
  +oy: U32,
  +pw: U32,
  +ph: U32,
  +ww: U32,
  +hh: U32,
  +hp: {pf(dd, tt) == True{} : Bool}
) -> {pf(dd, colT(left, tt, samples, row, col, ox, oy, pw, ph, ww, hh)) == True{} : Bool}:
  match left:
    case 0n:
      hp
    case 1n+pp:
      +x0 = (ox + col * pw : U32)
      +y0 = (oy + row * ph : U32)
      +vv = Jpeg.decode.at(samples, (row * 8 + col : U32))
      pf_col(pp, dd, pyT(U32.to_nat(ph), tt, x0, y0, 0, pw, ww, hh, vv), samples, row, (col + 1 : U32), ox, oy, pw, ph,
        ww, hh, pf_py(U32.to_nat(ph), dd, tt, x0, y0, 0, pw, ww, hh, vv, hp))

# a block keeps a tree perfect
def pf_cv(
  left: Nat,
  +dd: Nat,
  +tt: Tr,
  +samples: List<&2, U32>,
  +row: U32,
  +ox: U32,
  +oy: U32,
  +pw: U32,
  +ph: U32,
  +ww: U32,
  +hh: U32,
  +hp: {pf(dd, tt) == True{} : Bool}
) -> {pf(dd, cvT(left, tt, samples, row, ox, oy, pw, ph, ww, hh)) == True{} : Bool}:
  match left:
    case 0n:
      hp
    case 1n+pp:
      pf_cv(pp, dd, colT(8n, tt, samples, row, 0, ox, oy, pw, ph, ww, hh), samples, (row + 1 : U32), ox, oy, pw, ph, ww,
        hh, pf_col(8n, dd, tt, samples, row, 0, ox, oy, pw, ph, ww, hh, hp))

# ---- reading a painted pixel ----

# adding the same number on the left keeps whether two numbers are equal
def eq_add_l(+ww: Nat, +xx: Nat, +yy: Nat) -> {Nat.is_eq(Nat.add(ww, xx), Nat.add(ww, yy)) == Nat.is_eq(xx, yy) :
  Bool}:
  match ww:
    case 0n:
      {==}
    case 1n+vv:
      eq_add_l(vv, xx, yy)

# a number is at most itself plus more
def le_plus(+aa: Nat, +bb: Nat, +cc: Nat) -> {Nat.is_le(aa, Nat.add(Nat.add(aa, bb), cc)) == True{} : Bool}:
  R.le_add_more(aa, Nat.add(aa, bb), cc, R.le_add_more(aa, aa, bb, R.le_refl(aa)))

# row-major indices of in-row columns are equal exactly when both the columns and the rows are
def idx_eq(
  +aa: Nat,
  +bb: Nat,
  +cc: Nat,
  +dd: Nat,
  +ww: Nat,
  +hb: {Nat.is_lt(bb, ww) == True{} : Bool},
  +hd: {Nat.is_lt(dd, ww) == True{} : Bool}
) -> {Nat.is_eq(Nat.add(Nat.mul(aa, ww), bb), Nat.add(Nat.mul(cc, ww), dd)) == Bool.and(Nat.is_eq(bb, dd),
  Nat.is_eq(aa, cc)) : Bool}:
  match aa cc:
    case 0n 0n:
      Equal.sym(Bool, Bool.and(Nat.is_eq(bb, dd), True{}), Nat.is_eq(bb, dd), band_true(Nat.is_eq(bb, dd)))
    case 0n 1n+qq:
      +xx = Nat.add(Nat.mul(1n+qq, ww), dd)
      Equal.trans(Bool, Nat.is_eq(bb, xx), False{}, Bool.and(Nat.is_eq(bb, dd), False{}), lt_neq(bb, xx,
        R.lt_le_trans(bb, ww, xx, hb, le_plus(ww, Nat.mul(qq, ww), dd))), Equal.sym(Bool, Bool.and(Nat.is_eq(bb, dd),
        False{}), False{}, R.and_false_r(Nat.is_eq(bb, dd))))
    case 1n+pp 0n:
      +xx = Nat.add(Nat.mul(1n+pp, ww), bb)
      Equal.trans(Bool, Nat.is_eq(xx, dd), False{}, Bool.and(Nat.is_eq(bb, dd), False{}), gt_neq(xx, dd,
        R.lt_le_trans(dd, ww, xx, hd, le_plus(ww, Nat.mul(pp, ww), bb))), Equal.sym(Bool, Bool.and(Nat.is_eq(bb, dd),
        False{}), False{}, R.and_false_r(Nat.is_eq(bb, dd))))
    case 1n+pp 1n+qq:
      +xa = Nat.add(Nat.mul(pp, ww), bb)
      +xc = Nat.add(Nat.mul(qq, ww), dd)
      +e1 = {Equal.trans(Bool, Nat.is_eq(Nat.add(Nat.add(ww, Nat.mul(pp, ww)), bb), Nat.add(Nat.add(ww, Nat.mul(qq,
        ww)),
        dd)), Nat.is_eq(Nat.add(ww, xa), Nat.add(Nat.add(ww, Nat.mul(qq, ww)), dd)), Nat.is_eq(Nat.add(ww, xa),
        Nat.add(ww, xc)), Equal.cong(Nat, Bool, nn => Nat.is_eq(nn, Nat.add(Nat.add(ww, Nat.mul(qq, ww)), dd)),
        Nat.add(Nat.add(ww, Nat.mul(pp, ww)), bb), Nat.add(ww, xa), R.add_assoc(ww, Nat.mul(pp, ww), bb)),
        Equal.cong(Nat, Bool, nn => Nat.is_eq(Nat.add(ww, xa), nn), Nat.add(Nat.add(ww, Nat.mul(qq, ww)), dd),
        Nat.add(ww, xc), R.add_assoc(ww, Nat.mul(qq, ww), dd))) : {Nat.is_eq(Nat.add(Nat.add(ww, Nat.mul(pp, ww)), bb),
        Nat.add(Nat.add(ww, Nat.mul(qq, ww)), dd)) == Nat.is_eq(Nat.add(ww, xa), Nat.add(ww, xc)) : Bool}}
      Equal.trans(Bool, Nat.is_eq(Nat.add(Nat.add(ww, Nat.mul(pp, ww)), bb), Nat.add(Nat.add(ww, Nat.mul(qq, ww)), dd)),
        Nat.is_eq(Nat.add(ww, xa), Nat.add(ww, xc)), Bool.and(Nat.is_eq(bb, dd), Nat.is_eq(pp, qq)), e1,
        Equal.trans(Bool, Nat.is_eq(Nat.add(ww, xa), Nat.add(ww, xc)), Nat.is_eq(xa, xc), Bool.and(Nat.is_eq(bb, dd),
        Nat.is_eq(pp, qq)), eq_add_l(ww, xa, xc), idx_eq(pp, bb, qq, dd, ww, hb, hd)))

# the U32 below-test that holds as the Nat one
def lt_of(
  +aa: U32,
  +bb: U32,
  +hh: {U32.is_lt(aa, bb) == True{} : Bool}
) -> {Nat.is_lt(U32.to_nat(aa), U32.to_nat(bb)) == True{} : Bool}:
  lt_nat(aa, bb, True{}, hh)

# the frame's w * h fits the U32 of bit d
def area_nat(
  +ww: U32,
  +hh: U32,
  +dd: Nat,
  +hd: {Nat.is_lt(dd, 32n) == True{} : Bool},
  +hfit: {Nat.is_le(Nat.mul(U32.to_nat(ww), U32.to_nat(hh)), Nat.pow(2n, dd)) == True{} : Bool}
) -> {U32.to_nat((ww * hh : U32)) == Nat.mul(U32.to_nat(ww), U32.to_nat(hh)) : Nat}:
  R.u32_mul_below(ww, hh, U32{sbit(32n, dd)}, R.le_rw_r(Nat.mul(U32.to_nat(ww), U32.to_nat(hh)), Nat.pow(2n, dd),
    U32.to_nat(U32{sbit(32n, dd)}), Equal.sym(Nat, Word.to_nat(32n, sbit(32n, dd)), Nat.pow(2n, dd), sbit_nat(32n, dd,
    hd)), hfit))

# the point of pixel (x, y) of a frame w wide, as a number
def idx_nat(
  +ww: U32,
  +hh: U32,
  +xx: U32,
  +yy: U32,
  +dd: Nat,
  +hd: {Nat.is_lt(dd, 32n) == True{} : Bool},
  +hfit: {Nat.is_le(Nat.mul(U32.to_nat(ww), U32.to_nat(hh)), Nat.pow(2n, dd)) == True{} : Bool},
  +hx: {U32.is_lt(xx, ww) == True{} : Bool},
  +hy: {U32.is_lt(yy, hh) == True{} : Bool}
) -> {U32.to_nat((yy * ww + xx : U32)) == Nat.add(Nat.mul(U32.to_nat(yy), U32.to_nat(ww)), U32.to_nat(xx)) : Nat}:
  R.u32_index(ww, xx, yy, hh, (ww * hh : U32), area_nat(ww, hh, dd, hd, hfit), lt_of(xx, ww, hx), lt_of(yy, hh, hy))

# the point of pixel (x, y) of the frame is below 2^d
def idx_lt(
  +ww: U32,
  +hh: U32,
  +xx: U32,
  +yy: U32,
  +dd: Nat,
  +hd: {Nat.is_lt(dd, 32n) == True{} : Bool},
  +hfit: {Nat.is_le(Nat.mul(U32.to_nat(ww), U32.to_nat(hh)), Nat.pow(2n, dd)) == True{} : Bool},
  +hx: {U32.is_lt(xx, ww) == True{} : Bool},
  +hy: {U32.is_lt(yy, hh) == True{} : Bool}
) -> {Nat.is_lt(U32.to_nat((yy * ww + xx : U32)), Nat.pow(2n, dd)) == True{} : Bool}:
  +nx = Nat.add(Nat.mul(U32.to_nat(yy), U32.to_nat(ww)), U32.to_nat(xx))
  R.lt_rw_l(nx, U32.to_nat((yy * ww + xx : U32)), Nat.pow(2n, dd), Equal.sym(Nat, U32.to_nat((yy * ww + xx : U32)), nx,
    idx_nat(ww, hh, xx, yy, dd, hd, hfit, hx, hy)), R.lt_le_trans(nx, Nat.mul(U32.to_nat(ww), U32.to_nat(hh)),
    Nat.pow(2n, dd), R.index_lt(U32.to_nat(xx), U32.to_nat(yy), U32.to_nat(ww), U32.to_nat(hh), lt_of(xx, ww, hx),
    lt_of(yy, hh, hy)), hfit))

# the points of two pixels of the frame are equal exactly when the pixels are
def pix_eq(
  +ww: U32,
  +hh: U32,
  +ax: U32,
  +ay: U32,
  +xx: U32,
  +yy: U32,
  +dd: Nat,
  +hd: {Nat.is_lt(dd, 32n) == True{} : Bool},
  +hfit: {Nat.is_le(Nat.mul(U32.to_nat(ww), U32.to_nat(hh)), Nat.pow(2n, dd)) == True{} : Bool},
  +hax: {U32.is_lt(ax, ww) == True{} : Bool},
  +hay: {U32.is_lt(ay, hh) == True{} : Bool},
  +hx: {U32.is_lt(xx, ww) == True{} : Bool},
  +hy: {U32.is_lt(yy, hh) == True{} : Bool}
) -> {Nat.is_eq(U32.to_nat((ay * ww + ax : U32)), U32.to_nat((yy * ww + xx : U32))) == Bool.and(U32.is_eq(ax, xx),
  U32.is_eq(ay, yy)) : Bool}:
  +na = Nat.add(Nat.mul(U32.to_nat(ay), U32.to_nat(ww)), U32.to_nat(ax))
  +nb = Nat.add(Nat.mul(U32.to_nat(yy), U32.to_nat(ww)), U32.to_nat(xx))
  +e1 = {Equal.trans(Bool, Nat.is_eq(U32.to_nat((ay * ww + ax : U32)), U32.to_nat((yy * ww + xx : U32))), Nat.is_eq(na,
    U32.to_nat((yy * ww + xx : U32))), Nat.is_eq(na, nb), Equal.cong(Nat, Bool, nn => Nat.is_eq(nn, U32.to_nat((yy *
    ww + xx : U32))), U32.to_nat((ay * ww + ax : U32)), na, idx_nat(ww, hh, ax, ay, dd, hd, hfit, hax, hay)),
    Equal.cong(Nat, Bool, nn => Nat.is_eq(na, nn), U32.to_nat((yy * ww + xx : U32)), nb, idx_nat(ww, hh, xx, yy, dd,
    hd, hfit, hx, hy))) : {Nat.is_eq(U32.to_nat((ay * ww + ax : U32)), U32.to_nat((yy * ww + xx : U32))) ==
    Nat.is_eq(na, nb) : Bool}}
  +e2 = {idx_eq(U32.to_nat(ay), U32.to_nat(ax), U32.to_nat(yy), U32.to_nat(xx), U32.to_nat(ww), lt_of(ax, ww, hax),
    lt_of(xx, ww, hx)) : {Nat.is_eq(na, nb) == Bool.and(Nat.is_eq(U32.to_nat(ax), U32.to_nat(xx)),
    Nat.is_eq(U32.to_nat(ay), U32.to_nat(yy))) : Bool}}
  +e3 = {Equal.trans(Bool, Bool.and(Nat.is_eq(U32.to_nat(ax), U32.to_nat(xx)), Nat.is_eq(U32.to_nat(ay),
    U32.to_nat(yy))), Bool.and(U32.is_eq(ax, xx), Nat.is_eq(U32.to_nat(ay), U32.to_nat(yy))), Bool.and(U32.is_eq(ax,
    xx), U32.is_eq(ay, yy)), Equal.cong(Bool, Bool, bb => Bool.and(bb, Nat.is_eq(U32.to_nat(ay), U32.to_nat(yy))),
    Nat.is_eq(U32.to_nat(ax), U32.to_nat(xx)), U32.is_eq(ax, xx), Equal.sym(Bool, U32.is_eq(ax, xx),
    Nat.is_eq(U32.to_nat(ax), U32.to_nat(xx)), R.u32_eq(ax, xx))), Equal.cong(Bool, Bool, bb => Bool.and(U32.is_eq(ax,
    xx), bb), Nat.is_eq(U32.to_nat(ay), U32.to_nat(yy)), U32.is_eq(ay, yy), Equal.sym(Bool, U32.is_eq(ay, yy),
    Nat.is_eq(U32.to_nat(ay), U32.to_nat(yy)), R.u32_eq(ay, yy)))) : {Bool.and(Nat.is_eq(U32.to_nat(ax),
    U32.to_nat(xx)), Nat.is_eq(U32.to_nat(ay), U32.to_nat(yy))) == Bool.and(U32.is_eq(ax, xx), U32.is_eq(ay, yy)) :
    Bool}}
  Equal.trans(Bool, Nat.is_eq(U32.to_nat((ay * ww + ax : U32)), U32.to_nat((yy * ww + xx : U32))), Nat.is_eq(na, nb),
    Bool.and(U32.is_eq(ax, xx), U32.is_eq(ay, yy)), e1, Equal.trans(Bool, Nat.is_eq(na, nb),
    Bool.and(Nat.is_eq(U32.to_nat(ax), U32.to_nat(xx)), Nat.is_eq(U32.to_nat(ay), U32.to_nat(yy))),
    Bool.and(U32.is_eq(ax, xx), U32.is_eq(ay, yy)), e2, e3))

# a value is not one it differs from in a below-test
def nb_eq(
  zz: Bool,
  +aa: U32,
  +bb: U32,
  +ww: U32,
  +ez: {U32.is_eq(aa, bb) == zz : Bool},
  +ha: {U32.is_lt(aa, ww) == False{} : Bool},
  +hb: {U32.is_lt(bb, ww) == True{} : Bool}
) -> {zz == False{} : Bool}:
  match zz:
    case False{}:
      {==}
    case True{}:
      +ea = {U32L.ueq(aa, bb, ez) : {aa == bb : U32}}
      Empty.absurd({True{} == False{} : Bool}, U32L.false_true(Equal.trans(Bool, False{}, U32.is_lt(aa, ww), True{},
        Equal.sym(Bool, U32.is_lt(aa, ww), False{}, ha), Equal.trans(Bool, U32.is_lt(aa, ww), U32.is_lt(bb, ww),
        True{}, Equal.cong(U32, Bool, uu => U32.is_lt(uu, ww), aa, bb, ea), hb))))

# a coordinate outside the frame's side is not one inside
def neq_out(
  +aa: U32,
  +bb: U32,
  +ww: U32,
  +ha: {U32.is_lt(aa, ww) == False{} : Bool},
  +hb: {U32.is_lt(bb, ww) == True{} : Bool}
) -> {U32.is_eq(aa, bb) == False{} : Bool}:
  nb_eq(U32.is_eq(aa, bb), aa, bb, ww, {==}, ha, hb)

# a pixel write, read at pixel (x, y) of the frame: the written value when the write is at (x, y), else the old one
def rd_in(
  xin: Bool,
  yin: Bool,
  +dd: Nat,
  +tt: Tr,
  +ax: U32,
  +ay: U32,
  +ww: U32,
  +hh: U32,
  +xx: U32,
  +yy: U32,
  +vv: U32,
  +exin: {U32.is_lt(ax, ww) == xin : Bool},
  +eyin: {U32.is_lt(ay, hh) == yin : Bool},
  +hp: {pf(dd, tt) == True{} : Bool},
  +hd: {Nat.is_lt(dd, 32n) == True{} : Bool},
  +hfit: {Nat.is_le(Nat.mul(U32.to_nat(ww), U32.to_nat(hh)), Nat.pow(2n, dd)) == True{} : Bool},
  +hx: {U32.is_lt(xx, ww) == True{} : Bool},
  +hy: {U32.is_lt(yy, hh) == True{} : Bool}
) -> {at(inT(xin, yin, tt, ax, ay, ww, vv), (yy * ww + xx : U32)) == after(Bool.and(U32.is_eq(ax, xx), U32.is_eq(ay,
  yy)), vv, at(tt, (yy * ww + xx : U32))) : U32}:
  match xin yin:
    case True{} True{}:
      +ia = (ay * ww + ax : U32)
      +kk = (yy * ww + xx : U32)
      Equal.trans(U32, at(set(tt, ia, vv), kk), after(Nat.is_eq(U32.to_nat(ia), U32.to_nat(kk)), vv, at(tt, kk)),
        after(Bool.and(U32.is_eq(ax, xx), U32.is_eq(ay, yy)), vv, at(tt, kk)), at_set(dd, tt, ia, kk, vv, hp, hd,
        idx_lt(ww, hh, ax, ay, dd, hd, hfit, exin, eyin), idx_lt(ww, hh, xx, yy, dd, hd, hfit, hx, hy)),
        Equal.cong(Bool, U32, bb => after(bb, vv, at(tt, kk)), Nat.is_eq(U32.to_nat(ia), U32.to_nat(kk)),
        Bool.and(U32.is_eq(ax, xx), U32.is_eq(ay, yy)), pix_eq(ww, hh, ax, ay, xx, yy, dd, hd, hfit, exin, eyin, hx,
        hy)))
    case True{} False{}:
      +kk = (yy * ww + xx : U32)
      +ef = {Equal.trans(Bool, Bool.and(U32.is_eq(ax, xx), U32.is_eq(ay, yy)), Bool.and(U32.is_eq(ax, xx), False{}),
        False{}, Equal.cong(Bool, Bool, bb => Bool.and(U32.is_eq(ax, xx), bb), U32.is_eq(ay, yy), False{},
        neq_out(ay, yy, hh, eyin, hy)), R.and_false_r(U32.is_eq(ax, xx))) : {Bool.and(U32.is_eq(ax, xx), U32.is_eq(ay,
        yy)) == False{} : Bool}}
      Equal.sym(U32, after(Bool.and(U32.is_eq(ax, xx), U32.is_eq(ay, yy)), vv, at(tt, kk)), at(tt, kk),
        Equal.cong(Bool, U32, bb => after(bb, vv, at(tt, kk)), Bool.and(U32.is_eq(ax, xx), U32.is_eq(ay, yy)), False{},
        ef))
    case False{} _yin:
      +kk = (yy * ww + xx : U32)
      +ef = {Equal.cong(Bool, Bool, bb => Bool.and(bb, U32.is_eq(ay, yy)), U32.is_eq(ax, xx), False{}, neq_out(ax, xx,
        ww, exin, hx)) : {Bool.and(U32.is_eq(ax, xx), U32.is_eq(ay, yy)) == False{} : Bool}}
      Equal.sym(U32, after(Bool.and(U32.is_eq(ax, xx), U32.is_eq(ay, yy)), vv, at(tt, kk)), at(tt, kk),
        Equal.cong(Bool, U32, bb => after(bb, vv, at(tt, kk)), Bool.and(U32.is_eq(ax, xx), U32.is_eq(ay, yy)), False{},
        ef))

# a later hit of the same value over an earlier one: the value, when either hit
def ba1(
  hh: Bool,
  rr: Bool,
  ee: Bool,
  +vv: U32,
  +oo: U32
) -> {after(Bool.and(rr, ee), vv, after(Bool.and(hh, ee), vv, oo)) == after(Bool.and(Bool.or(hh, rr), ee), vv,
  oo) : U32}:
  match hh rr ee:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

# the same, the common test on the left
def ba2(
  ss: Bool,
  hh: Bool,
  rr: Bool,
  +vv: U32,
  +oo: U32
) -> {after(Bool.and(ss, rr), vv, after(Bool.and(ss, hh), vv, oo)) == after(Bool.and(ss, Bool.or(hh, rr)), vv,
  oo) : U32}:
  match ss hh rr:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

# a pixel row, read at pixel (x, y): the row's value when the row is y and one of its pixels is x, else the old one
def rd_px(
  left: Nat,
  +dd: Nat,
  +tt: Tr,
  +x0: U32,
  +ay: U32,
  +px: U32,
  +ww: U32,
  +hh: U32,
  +vv: U32,
  +xx: U32,
  +yy: U32,
  +hp: {pf(dd, tt) == True{} : Bool},
  +hd: {Nat.is_lt(dd, 32n) == True{} : Bool},
  +hfit: {Nat.is_le(Nat.mul(U32.to_nat(ww), U32.to_nat(hh)), Nat.pow(2n, dd)) == True{} : Bool},
  +hx: {U32.is_lt(xx, ww) == True{} : Bool},
  +hy: {U32.is_lt(yy, hh) == True{} : Bool}
) -> {at(pxT(left, tt, x0, ay, px, ww, hh, vv), (yy * ww + xx : U32)) == after(Bool.and(Laws.jpg.span(left, x0, px,
  xx), U32.is_eq(ay, yy)), vv, at(tt, (yy * ww + xx : U32))) : U32}:
  match left:
    case 0n:
      {==}
    case 1n+(+pp):
      +kk = (yy * ww + xx : U32)
      +ax = (x0 + px : U32)
      +xin = U32.is_lt(ax, ww)
      +yin = U32.is_lt(ay, hh)
      +t1 = inT(xin, yin, tt, ax, ay, ww, vv)
      +ey = U32.is_eq(ay, yy)
      +hr = U32.is_eq(ax, xx)
      +rr = Laws.jpg.span(pp, x0, (px + 1 : U32), xx)
      +ih = {rd_px(pp, dd, t1, x0, ay, (px + 1 : U32), ww, hh, vv, xx, yy, pf_in(xin, yin, dd, tt, ax, ay, ww, vv, hp),
        hd, hfit, hx, hy) : {at(pxT(pp, t1, x0, ay, (px + 1 : U32), ww, hh, vv), kk) == after(Bool.and(rr, ey), vv,
        at(t1, kk)) : U32}}
      +e1 = {rd_in(xin, yin, dd, tt, ax, ay, ww, hh, xx, yy, vv, {==}, {==}, hp, hd, hfit, hx, hy) : {at(t1, kk) ==
        after(Bool.and(hr, ey), vv, at(tt, kk)) : U32}}
      Equal.trans(U32, at(pxT(pp, t1, x0, ay, (px + 1 : U32), ww, hh, vv), kk), after(Bool.and(rr, ey), vv, at(t1, kk)),
        after(Bool.and(Bool.or(hr, rr), ey), vv, at(tt, kk)), ih, Equal.trans(U32, after(Bool.and(rr, ey), vv, at(t1,
        kk)), after(Bool.and(rr, ey), vv, after(Bool.and(hr, ey), vv, at(tt, kk))), after(Bool.and(Bool.or(hr, rr),
        ey), vv, at(tt, kk)), Equal.cong(U32, U32, oo => after(Bool.and(rr, ey), vv, oo), at(t1, kk),
        after(Bool.and(hr, ey), vv, at(tt, kk)), e1), ba1(hr, rr, ey, vv, at(tt, kk))))

# one sample's cover, read at pixel (x, y): the sample's value when its rows take in y and its columns x, else
# the old one
def rd_py(
  left: Nat,
  +dd: Nat,
  +tt: Tr,
  +x0: U32,
  +y0: U32,
  +py: U32,
  +pw: U32,
  +ww: U32,
  +hh: U32,
  +vv: U32,
  +xx: U32,
  +yy: U32,
  +hp: {pf(dd, tt) == True{} : Bool},
  +hd: {Nat.is_lt(dd, 32n) == True{} : Bool},
  +hfit: {Nat.is_le(Nat.mul(U32.to_nat(ww), U32.to_nat(hh)), Nat.pow(2n, dd)) == True{} : Bool},
  +hx: {U32.is_lt(xx, ww) == True{} : Bool},
  +hy: {U32.is_lt(yy, hh) == True{} : Bool}
) -> {at(pyT(left, tt, x0, y0, py, pw, ww, hh, vv),
  (yy * ww + xx : U32)) == after(Bool.and(Laws.jpg.span(U32.to_nat(pw),
  x0, 0, xx), Laws.jpg.span(left, y0, py, yy)), vv, at(tt, (yy * ww + xx : U32))) : U32}:
  match left:
    case 0n:
      +kk = (yy * ww + xx : U32)
      +sx = Laws.jpg.span(U32.to_nat(pw), x0, 0, xx)
      Equal.sym(U32, after(Bool.and(sx, False{}), vv, at(tt, kk)), at(tt, kk), Equal.cong(Bool, U32, bb => after(bb, vv,
        at(tt, kk)), Bool.and(sx, False{}), False{}, R.and_false_r(sx)))
    case 1n+(+pp):
      +kk = (yy * ww + xx : U32)
      +ay = (y0 + py : U32)
      +sx = Laws.jpg.span(U32.to_nat(pw), x0, 0, xx)
      +t1 = pxT(U32.to_nat(pw), tt, x0, ay, 0, ww, hh, vv)
      +hr = U32.is_eq(ay, yy)
      +rr = Laws.jpg.span(pp, y0, (py + 1 : U32), yy)
      +ih = {rd_py(pp, dd, t1, x0, y0, (py + 1 : U32), pw, ww, hh, vv, xx, yy, pf_px(U32.to_nat(pw), dd, tt, x0, ay, 0,
        ww, hh, vv, hp), hd, hfit, hx, hy) : {at(pyT(pp, t1, x0, y0, (py + 1 : U32), pw, ww, hh, vv), kk) ==
        after(Bool.and(sx, rr), vv, at(t1, kk)) : U32}}
      +e1 = {rd_px(U32.to_nat(pw), dd, tt, x0, ay, 0, ww, hh, vv, xx, yy, hp, hd, hfit, hx, hy) : {at(t1, kk) ==
        after(Bool.and(sx, hr), vv, at(tt, kk)) : U32}}
      Equal.trans(U32, at(pyT(pp, t1, x0, y0, (py + 1 : U32), pw, ww, hh, vv), kk), after(Bool.and(sx, rr), vv, at(t1,
        kk)), after(Bool.and(sx, Bool.or(hr, rr)), vv, at(tt, kk)), ih, Equal.trans(U32, after(Bool.and(sx, rr), vv,
        at(t1, kk)), after(Bool.and(sx, rr), vv, after(Bool.and(sx, hr), vv, at(tt, kk))), after(Bool.and(sx,
        Bool.or(hr, rr)), vv, at(tt, kk)), Equal.cong(U32, U32, oo => after(Bool.and(sx, rr), vv, oo), at(t1, kk),
        after(Bool.and(sx, hr), vv, at(tt, kk)), e1), ba2(sx, hr, rr, vv, at(tt, kk))))

# a block row, read at pixel (x, y): jpg.blk.col
def rd_col(
  left: Nat,
  +dd: Nat,
  +tt: Tr,
  +samples: List<&2, U32>,
  +row: U32,
  +col: U32,
  +ox: U32,
  +oy: U32,
  +pw: U32,
  +ph: U32,
  +ww: U32,
  +hh: U32,
  +xx: U32,
  +yy: U32,
  +hp: {pf(dd, tt) == True{} : Bool},
  +hd: {Nat.is_lt(dd, 32n) == True{} : Bool},
  +hfit: {Nat.is_le(Nat.mul(U32.to_nat(ww), U32.to_nat(hh)), Nat.pow(2n, dd)) == True{} : Bool},
  +hx: {U32.is_lt(xx, ww) == True{} : Bool},
  +hy: {U32.is_lt(yy, hh) == True{} : Bool}
) -> {at(colT(left, tt, samples, row, col, ox, oy, pw, ph, ww, hh), (yy * ww + xx : U32)) == Laws.jpg.blk.col(left,
  samples, row, col, ox, oy, pw, ph, xx, yy, at(tt, (yy * ww + xx : U32))) : U32}:
  match left:
    case 0n:
      {==}
    case 1n+(+pp):
      +kk = (yy * ww + xx : U32)
      +x0 = (ox + col * pw : U32)
      +y0 = (oy + row * ph : U32)
      +vv = Jpeg.decode.at(samples, (row * 8 + col : U32))
      +t1 = pyT(U32.to_nat(ph), tt, x0, y0, 0, pw, ww, hh, vv)
      +cv = Laws.jpg.covers(row, col, ox, oy, pw, ph, xx, yy)
      +ih = {rd_col(pp, dd, t1, samples, row, (col + 1 : U32), ox, oy, pw, ph, ww, hh, xx, yy, pf_py(U32.to_nat(ph), dd,
        tt, x0, y0, 0, pw, ww, hh, vv, hp), hd, hfit, hx, hy) : {at(colT(pp, t1, samples, row, (col + 1 : U32), ox,
        oy, pw, ph, ww, hh), kk) == Laws.jpg.blk.col(pp, samples, row, (col + 1 : U32), ox, oy, pw, ph, xx, yy, at(t1,
        kk)) : U32}}
      +e1 = {rd_py(U32.to_nat(ph), dd, tt, x0, y0, 0, pw, ww, hh, vv, xx, yy, hp, hd, hfit, hx, hy) : {at(t1, kk) ==
        after(cv, vv, at(tt, kk)) : U32}}
      Equal.trans(U32, at(colT(pp, t1, samples, row, (col + 1 : U32), ox, oy, pw, ph, ww, hh), kk),
        Laws.jpg.blk.col(pp, samples, row, (col + 1 : U32), ox, oy, pw, ph, xx, yy, at(t1, kk)),
        Laws.jpg.blk.col(pp, samples, row, (col + 1 : U32), ox, oy, pw, ph, xx, yy, after(cv, vv, at(tt, kk))), ih,
        Equal.cong(U32, U32, oo => Laws.jpg.blk.col(pp, samples, row, (col + 1 : U32), ox, oy, pw, ph, xx, yy, oo),
        at(t1, kk), after(cv, vv, at(tt, kk)), e1))

# a block, read at pixel (x, y): jpg.blk
def rd_cv(
  left: Nat,
  +dd: Nat,
  +tt: Tr,
  +samples: List<&2, U32>,
  +row: U32,
  +ox: U32,
  +oy: U32,
  +pw: U32,
  +ph: U32,
  +ww: U32,
  +hh: U32,
  +xx: U32,
  +yy: U32,
  +hp: {pf(dd, tt) == True{} : Bool},
  +hd: {Nat.is_lt(dd, 32n) == True{} : Bool},
  +hfit: {Nat.is_le(Nat.mul(U32.to_nat(ww), U32.to_nat(hh)), Nat.pow(2n, dd)) == True{} : Bool},
  +hx: {U32.is_lt(xx, ww) == True{} : Bool},
  +hy: {U32.is_lt(yy, hh) == True{} : Bool}
) -> {at(cvT(left, tt, samples, row, ox, oy, pw, ph, ww, hh), (yy * ww + xx : U32)) == Laws.jpg.blk(left, samples,
  row, ox, oy, pw, ph, xx, yy, at(tt, (yy * ww + xx : U32))) : U32}:
  match left:
    case 0n:
      {==}
    case 1n+(+pp):
      +kk = (yy * ww + xx : U32)
      +t1 = colT(8n, tt, samples, row, 0, ox, oy, pw, ph, ww, hh)
      +bc = Laws.jpg.blk.col(8n, samples, row, 0, ox, oy, pw, ph, xx, yy, at(tt, kk))
      +ih = {rd_cv(pp, dd, t1, samples, (row + 1 : U32), ox, oy, pw, ph, ww, hh, xx, yy, pf_col(8n, dd, tt, samples,
        row, 0, ox, oy, pw, ph, ww, hh, hp), hd, hfit, hx, hy) : {at(cvT(pp, t1, samples, (row + 1 : U32), ox, oy, pw,
        ph, ww, hh), kk) == Laws.jpg.blk(pp, samples, (row + 1 : U32), ox, oy, pw, ph, xx, yy, at(t1, kk)) : U32}}
      Equal.trans(U32, at(cvT(pp, t1, samples, (row + 1 : U32), ox, oy, pw, ph, ww, hh), kk), Laws.jpg.blk(pp, samples,
        (row + 1 : U32), ox, oy, pw, ph, xx, yy, at(t1, kk)), Laws.jpg.blk(pp, samples, (row + 1 : U32), ox, oy, pw, ph,
        xx, yy, bc), ih, Equal.cong(U32, U32, oo => Laws.jpg.blk(pp, samples, (row + 1 : U32), ox, oy, pw, ph, xx, yy,
        oo), at(t1, kk), bc, rd_col(8n, dd, tt, samples, row, 0, ox, oy, pw, ph, ww, hh, xx, yy, hp, hd, hfit, hx,
        hy)))

# jpeg_paint_at, from a tree the plane is the array of
def paint_at_of(
  +dd: Nat,
  -plane: Array<U32>,
  +h_perfect: {Laws.jpg.perfect(dd, plane) == True{} : Bool},
  +h_dd: {Nat.is_lt(dd, 32n) == True{} : Bool},
  +ox: U32,
  +oy: U32,
  +pw: U32,
  +ph: U32,
  +ww: U32,
  +hh: U32,
  +samples: List<&2, U32>,
  +h_fit: {Nat.is_le(Nat.mul(U32.to_nat(ww), U32.to_nat(hh)), Nat.pow(2n, dd)) == True{} : Bool},
  +xx: U32,
  +yy: U32,
  +h_xx: {U32.is_lt(xx, ww) == True{} : Bool},
  +h_yy: {U32.is_lt(yy, hh) == True{} : Bool},
  oo: Of(plane)
) -> {Laws.jpg.val(Array.get(U32, Jpeg.decode.paint.use(Jpeg.Geom{ox, oy, pw, ph, ww, hh}, True{}, samples, plane),
  (yy * ww + xx : U32))) == Laws.jpg.block.at(Jpeg.Geom{ox, oy, pw, ph, ww, hh}, samples, xx, yy,
  Laws.jpg.val(Array.get(U32, plane, (yy * ww + xx : U32)))) : U32}:
  (+tt, ep) = oo
  +sp = {Equal.sym(Array<U32>, plane, arr(tt), ep) : {arr(tt) == plane : Array<U32>}}
  +hp = pf_of(dd, plane, tt, Equal.sym(Array<U32>, arr(tt), plane, sp), h_perfect)
  +kk = (yy * ww + xx : U32)
  +cv = cvT(8n, tt, samples, 0, ox, oy, pw, ph, ww, hh)
  %sp : {Laws.jpg.val(Array.get(U32, Jpeg.decode.paint.use(Jpeg.Geom{ox, oy, pw, ph, ww, hh}, True{}, samples, _),
    kk)) == Laws.jpg.block.at(Jpeg.Geom{ox, oy, pw, ph, ww, hh}, samples, xx, yy, Laws.jpg.val(Array.get(U32, _, kk))) :
    U32}
  Equal.trans(U32, Laws.jpg.val(Array.get(U32, Jpeg.decode.splat(8n, arr(tt), samples, 0, ox, oy, pw, ph, ww, hh), kk)),
    Laws.jpg.val(Array.get(U32, arr(cv), kk)), Laws.jpg.blk(8n, samples, 0, ox, oy, pw, ph, xx, yy,
    Laws.jpg.val(Array.get(U32, arr(tt), kk))), Equal.cong(Array<U32>, U32, aa => Laws.jpg.val(Array.get(U32, aa, kk)),
    Jpeg.decode.splat(8n, arr(tt), samples, 0, ox, oy, pw, ph, ww, hh), arr(cv), arr_cv(8n, tt, samples, 0, ox, oy,
    pw, ph, ww, hh)), Equal.trans(U32, Laws.jpg.val(Array.get(U32, arr(cv), kk)), at(cv, kk), Laws.jpg.blk(8n,
    samples, 0, ox, oy, pw, ph, xx, yy, Laws.jpg.val(Array.get(U32, arr(tt), kk))), val_at(cv, kk), Equal.trans(U32,
    at(cv, kk), Laws.jpg.blk(8n, samples, 0, ox, oy, pw, ph, xx, yy, at(tt, kk)), Laws.jpg.blk(8n, samples, 0, ox, oy,
    pw, ph, xx, yy, Laws.jpg.val(Array.get(U32, arr(tt), kk))), rd_cv(8n, dd, tt, samples, 0, ox, oy, pw, ph, ww, hh,
    xx, yy, hp, h_dd, h_fit, h_xx, h_yy), Equal.cong(U32, U32, oo2 => Laws.jpg.blk(8n, samples, 0, ox, oy, pw, ph, xx,
    yy, oo2), at(tt, kk), Laws.jpg.val(Array.get(U32, arr(tt), kk)), Equal.sym(U32, Laws.jpg.val(Array.get(U32, arr(tt),
    kk)), at(tt, kk), val_at(tt, kk))))))

# ---- the plane's depth ----

# a U32's lowest bit
def lowb(uu: U32) -> Bool:
  match uu:
    case U32{ww}:
      match ww:
        case WCon{bb, _tt}:
          bb

# a U32 is its lowest bit plus twice its shr
def shr_split(+uu: U32) -> {U32.to_nat(uu) == Nat.add(R.bit(lowb(uu)), Nat.double(U32.to_nat(U32.shr(uu)))) : Nat}:
  match uu:
    case U32{+ww}:
      match ww:
        case WCon{+bb, +tt}:
          Equal.trans(Nat, Word.to_nat(32n, WCon{bb, tt}), Nat.add(R.bit(bb), Nat.double(Word.to_nat(31n, tt))),
            Nat.add(R.bit(bb), Nat.double(Word.to_nat(32n, Word.shr.pad(31n, tt)))), R.to_nat_con(31n, bb, tt),
            Equal.cong(Nat, Nat, nn => Nat.add(R.bit(bb), Nat.double(nn)), Word.to_nat(31n, tt), Word.to_nat(32n,
            Word.shr.pad(31n, tt)), Equal.sym(Nat, Word.to_nat(32n, Word.shr.pad(31n, tt)), Word.to_nat(31n, tt),
            pad_nat(31n, tt))))

# a bit plus a double is at least the halved number
def half_le(+bb: Bool, +xx: Nat) -> {Nat.is_le(xx, Nat.add(R.bit(bb), Nat.double(xx))) == True{} : Bool}:
  match bb:
    case False{}:
      R.le_rw_r(xx, Nat.add(xx, xx), Nat.double(xx), Equal.sym(Nat, Nat.double(xx), Nat.add(xx, xx), R.double_add(xx)),
        R.le_add_more(xx, xx, xx, R.le_refl(xx)))
    case True{}:
      R.le_trans(xx, Nat.double(xx), 1n+Nat.double(xx), R.le_rw_r(xx, Nat.add(xx, xx), Nat.double(xx), Equal.sym(Nat,
        Nat.double(xx), Nat.add(xx, xx), R.double_add(xx)), R.le_add_more(xx, xx, xx, R.le_refl(xx))),
        R.le_succ(Nat.double(xx)))

# a U32's shr is at most it
def shr_le(+uu: U32) -> {Nat.is_le(U32.to_nat(U32.shr(uu)), U32.to_nat(uu)) == True{} : Bool}:
  R.le_rw_r(U32.to_nat(U32.shr(uu)), Nat.add(R.bit(lowb(uu)), Nat.double(U32.to_nat(U32.shr(uu)))), U32.to_nat(uu),
    Equal.sym(Nat, U32.to_nat(uu), Nat.add(R.bit(lowb(uu)), Nat.double(U32.to_nat(U32.shr(uu)))), shr_split(uu)),
    half_le(lowb(uu), U32.to_nat(U32.shr(uu))))

# the log2 walk never takes its count down
def go_ge(+kk: Nat, +nn: U32, +dd: Nat) -> {Nat.is_le(dd, U32.log2.go(kk, nn, dd)) == True{} : Bool}:
  match kk:
    case 0n:
      R.le_refl(dd)
    case 1n+pp:
      +d1 = Nat.add(dd, U32.to_nat(Bool.to_u32(U32.is_lt(1, nn))))
      R.le_trans(dd, d1, U32.log2.go(pp, U32.shr(nn), d1), R.le_add_more(dd, dd, U32.to_nat(Bool.to_u32(U32.is_lt(1,
        nn))), R.le_refl(dd)), go_ge(pp, U32.shr(nn), d1))

# a number at least 2^(i+1) is above one
def two_le(
  +nn: U32,
  +ii: Nat,
  +hh: {Nat.is_le(Nat.pow(2n, 1n+ii), U32.to_nat(nn)) == True{} : Bool}
) -> {U32.is_lt(1, nn) == True{} : Bool}:
  +p2 = {R.lt_rw_r(1n, Nat.double(Nat.pow(2n, ii)), Nat.pow(2n, 1n+ii), Equal.sym(Nat, Nat.pow(2n, 1n+ii),
    Nat.double(Nat.pow(2n, ii)), R.pow2_succ(ii)), dbl_pos(Nat.pow(2n, ii), pow_pos(ii))) : {Nat.is_lt(1n,
    Nat.pow(2n, 1n+ii)) == True{} : Bool}}
  Equal.trans(Bool, U32.is_lt(1, nn), Nat.is_lt(1n, U32.to_nat(nn)), True{}, R.u32_lt(1, nn), R.lt_le_trans(1n,
    Nat.pow(2n, 1n+ii), U32.to_nat(nn), p2, hh))

# the log2 walk counts at least j halvings of a number at least 2^j, when it walks at least j steps
def le2(
  +kk: Nat,
  +jj: Nat,
  +nn: U32,
  +dd: Nat,
  +hk: {Nat.is_le(jj, kk) == True{} : Bool},
  +hn: {Nat.is_le(Nat.pow(2n, jj), U32.to_nat(nn)) == True{} : Bool}
) -> {Nat.is_le(Nat.add(dd, jj), U32.log2.go(kk, nn, dd)) == True{} : Bool}:
  match kk jj:
    case _kk 0n:
      R.le_rw_l(dd, Nat.add(dd, 0n), U32.log2.go(kk, nn, dd), Equal.sym(Nat, Nat.add(dd, 0n), dd, R.add_zero(dd)),
        go_ge(kk, nn, dd))
    case 0n 1n+ii:
      Empty.absurd({Nat.is_le(Nat.add(dd, 1n+ii), dd) == True{} : Bool}, U32L.false_true(hk))
    case 1n+pp 1n+ii:
      +sh = U32.shr(nn)
      +pw = Nat.pow(2n, ii)
      +el = {Equal.cong(Bool, Nat, bb => U32.log2.go(pp, sh, Nat.add(dd, U32.to_nat(Bool.to_u32(bb)))), U32.is_lt(1,
        nn), True{}, two_le(nn, ii, hn)) : {U32.log2.go(pp, sh, Nat.add(dd, U32.to_nat(Bool.to_u32(U32.is_lt(1, nn)))))
        == U32.log2.go(pp, sh, Nat.add(dd, 1n)) : Nat}}
      +h2 = {R.le_rw_r(Nat.double(pw), U32.to_nat(nn), Nat.add(R.bit(lowb(nn)), Nat.double(U32.to_nat(sh))),
        shr_split(nn), R.le_rw_l(Nat.pow(2n, 1n+ii), Nat.double(pw), U32.to_nat(nn), R.pow2_succ(ii), hn)) :
        {Nat.is_le(Nat.double(pw), Nat.add(R.bit(lowb(nn)), Nat.double(U32.to_nat(sh)))) == True{} : Bool}}
      +ih = {le2(pp, ii, sh, Nat.add(dd, 1n), hk, R.le_half(lowb(nn), pw, U32.to_nat(sh), h2)) :
        {Nat.is_le(Nat.add(Nat.add(dd, 1n), ii), U32.log2.go(pp, sh, Nat.add(dd, 1n))) == True{} : Bool}}
      +ea = {Equal.trans(Nat, Nat.add(Nat.add(dd, 1n), ii), Nat.add(dd, Nat.add(1n, ii)), Nat.add(dd, 1n+ii),
        R.add_assoc(dd, 1n, ii), {==}) : {Nat.add(Nat.add(dd, 1n), ii) == Nat.add(dd, 1n+ii) : Nat}}
      R.le_rw_l(Nat.add(Nat.add(dd, 1n), ii), Nat.add(dd, 1n+ii), U32.log2.go(1n+pp, nn, dd), ea,
        R.le_rw_r(Nat.add(Nat.add(dd,
        1n), ii), U32.log2.go(pp, sh, Nat.add(dd, 1n)), U32.log2.go(1n+pp, nn, dd), Equal.sym(Nat,
        U32.log2.go(1n+pp, nn, dd), U32.log2.go(pp, sh, Nat.add(dd, 1n)), el), ih))

# the bound the log2 walk's next step needs: halved below 2^(1+i) when not above one, below 2^i when above
def le1_hyp(
  zz: Bool,
  +ii: Nat,
  +nn: U32,
  +ez: {U32.is_lt(1, nn) == zz : Bool},
  +hn: {Nat.is_lt(U32.to_nat(nn), Nat.pow(2n, 1n+ii)) == True{} : Bool}
) -> {Nat.is_lt(U32.to_nat(U32.shr(nn)), Nat.pow(2n, 1n+Bool.pick(Nat, zz, pred(ii), ii))) == True{} : Bool}:
  match zz ii:
    case False{} _ii:
      R.le_lt_trans(U32.to_nat(U32.shr(nn)), U32.to_nat(nn), Nat.pow(2n, 1n+ii), shr_le(nn), hn)
    case True{} 0n:
      +h1 = {Equal.trans(Bool, Nat.is_lt(1n, U32.to_nat(nn)), U32.is_lt(1, nn), True{}, Equal.sym(Bool, U32.is_lt(1,
        nn),
        Nat.is_lt(1n, U32.to_nat(nn)), R.u32_lt(1, nn)), ez) : {Nat.is_lt(1n, U32.to_nat(nn)) == True{} : Bool}}
      +h2 = {Equal.trans(Bool, Nat.is_le(2n, U32.to_nat(nn)), Nat.is_lt(1n, U32.to_nat(nn)), True{}, Equal.sym(Bool,
        Nat.is_lt(1n, U32.to_nat(nn)), Nat.is_le(2n, U32.to_nat(nn)), R.lt_le_succ(1n, U32.to_nat(nn))), h1) :
        {Nat.is_le(2n, U32.to_nat(nn)) == True{} : Bool}}
      Empty.absurd({Nat.is_lt(U32.to_nat(U32.shr(nn)), Nat.pow(2n, 1n+Bool.pick(Nat, True{}, pred(0n), 0n))) == True{} :
        Bool}, U32L.false_true(Equal.trans(Bool, False{}, Nat.is_lt(2n, 2n), True{}, {==}, R.le_lt_trans(2n,
        U32.to_nat(nn), 2n, h2, hn))))
    case True{} 1n+jj:
      +sh = U32.to_nat(U32.shr(nn))
      +pw = Nat.pow(2n, 1n+jj)
      +h2 = {R.lt_rw_r(Nat.add(R.bit(lowb(nn)), Nat.double(sh)), Nat.pow(2n, 2n+jj), Nat.double(pw), R.pow2_succ(1n+jj),
        R.lt_rw_l(U32.to_nat(nn), Nat.add(R.bit(lowb(nn)), Nat.double(sh)), Nat.pow(2n, 2n+jj), shr_split(nn), hn)) :
        {Nat.is_lt(Nat.add(R.bit(lowb(nn)), Nat.double(sh)), Nat.double(pw)) == True{} : Bool}}
      R.lt_half(lowb(nn), sh, pw, h2)

# a number above one and below 2^(1+i): i is not zero
def two_pos(
  +nn: U32,
  +h1: {U32.is_lt(1, nn) == True{} : Bool},
  +hn: {Nat.is_lt(U32.to_nat(nn), 2n) == True{} : Bool}
) -> Empty:
  +h2 = {Equal.trans(Bool, Nat.is_le(2n, U32.to_nat(nn)), Nat.is_lt(1n, U32.to_nat(nn)), True{}, Equal.sym(Bool,
    Nat.is_lt(1n, U32.to_nat(nn)), Nat.is_le(2n, U32.to_nat(nn)), R.lt_le_succ(1n, U32.to_nat(nn))), Equal.trans(Bool,
    Nat.is_lt(1n, U32.to_nat(nn)), U32.is_lt(1, nn), True{}, Equal.sym(Bool, U32.is_lt(1, nn), Nat.is_lt(1n,
    U32.to_nat(nn)), R.u32_lt(1, nn)), h1)) : {Nat.is_le(2n, U32.to_nat(nn)) == True{} : Bool}}
  U32L.false_true(Equal.trans(Bool, False{}, Nat.is_lt(2n, 2n), True{}, {==}, R.le_lt_trans(2n, U32.to_nat(nn), 2n, h2,
    hn)))

# the count and bound after the log2 walk's step fit the bound before it
def le1_fin(
  zz: Bool,
  +ii: Nat,
  +dd: Nat,
  +nn: U32,
  +ez: {U32.is_lt(1, nn) == zz : Bool},
  +hn: {Nat.is_lt(U32.to_nat(nn), Nat.pow(2n, 1n+ii)) == True{} : Bool}
) -> {Nat.is_le(Nat.add(Nat.add(dd, U32.to_nat(Bool.to_u32(zz))), Bool.pick(Nat, zz, pred(ii), ii)), Nat.add(dd, ii)) ==
  True{} : Bool}:
  match zz ii:
    case False{} _ii:
      R.le_rw_l(Nat.add(dd, ii), Nat.add(Nat.add(dd, 0n), ii), Nat.add(dd, ii), Equal.cong(Nat, Nat, xx => Nat.add(xx,
        ii), dd, Nat.add(dd, 0n), Equal.sym(Nat, Nat.add(dd, 0n), dd, R.add_zero(dd))), R.le_refl(Nat.add(dd, ii)))
    case True{} 0n:
      Empty.absurd({Nat.is_le(Nat.add(Nat.add(dd, 1n), 0n), Nat.add(dd, 0n)) == True{} : Bool}, two_pos(nn, ez, hn))
    case True{} 1n+jj:
      R.le_rw_l(Nat.add(dd, 1n+jj), Nat.add(Nat.add(dd, 1n), jj), Nat.add(dd, 1n+jj), Equal.sym(Nat,
        Nat.add(Nat.add(dd, 1n), jj), Nat.add(dd, 1n+jj), R.add_assoc(dd, 1n, jj)), R.le_refl(Nat.add(dd, 1n+jj)))

# the log2 walk counts at most i halvings of a number below 2^(1+i)
def le1(
  +kk: Nat,
  +ii: Nat,
  +nn: U32,
  +dd: Nat,
  +hn: {Nat.is_lt(U32.to_nat(nn), Nat.pow(2n, 1n+ii)) == True{} : Bool}
) -> {Nat.is_le(U32.log2.go(kk, nn, dd), Nat.add(dd, ii)) == True{} : Bool}:
  match kk:
    case 0n:
      R.le_add_more(dd, dd, ii, R.le_refl(dd))
    case 1n+pp:
      +zz = U32.is_lt(1, nn)
      +d1 = Nat.add(dd, U32.to_nat(Bool.to_u32(zz)))
      +i1 = Bool.pick(Nat, zz, pred(ii), ii)
      R.le_trans(U32.log2.go(pp, U32.shr(nn), d1), Nat.add(d1, i1), Nat.add(dd, ii), le1(pp, i1, U32.shr(nn), d1,
        le1_hyp(zz, ii, nn, {==}, hn)), le1_fin(zz, ii, dd, nn, {==}, hn))

# doubling keeps an order, at most
def dbl_le(
  +xx: Nat,
  +yy: Nat,
  +hh: {Nat.is_le(xx, yy) == True{} : Bool}
) -> {Nat.is_le(Nat.double(xx), Nat.double(yy)) == True{} : Bool}:
  match xx yy:
    case 0n _yy:
      R.le_zero(Nat.double(yy))
    case 1n+_pp 0n:
      Empty.absurd({Nat.is_le(Nat.double(xx), 0n) == True{} : Bool}, U32L.false_true(hh))
    case 1n+pp 1n+qq:
      dbl_le(pp, qq, hh)

# two to a power at most another is at most two to it
def pow_le(
  +aa: Nat,
  +bb: Nat,
  +hh: {Nat.is_le(aa, bb) == True{} : Bool}
) -> {Nat.is_le(Nat.pow(2n, aa), Nat.pow(2n, bb)) == True{} : Bool}:
  match aa bb:
    case 0n _bb:
      Equal.trans(Bool, Nat.is_le(1n, Nat.pow(2n, bb)), Nat.is_lt(0n, Nat.pow(2n, bb)), True{}, Equal.sym(Bool,
        Nat.is_lt(0n, Nat.pow(2n, bb)), Nat.is_le(1n, Nat.pow(2n, bb)), R.lt_le_succ(0n, Nat.pow(2n, bb))), pow_pos(bb))
    case 1n+_pp 0n:
      Empty.absurd({Nat.is_le(Nat.pow(2n, aa), 1n) == True{} : Bool}, U32L.false_true(hh))
    case 1n+pp 1n+qq:
      R.le_rw_l(Nat.double(Nat.pow(2n, pp)), Nat.pow(2n, 1n+pp), Nat.pow(2n, 1n+qq), Equal.sym(Nat, Nat.pow(2n, 1n+pp),
        Nat.double(Nat.pow(2n, pp)), R.pow2_succ(pp)), R.le_rw_r(Nat.double(Nat.pow(2n, pp)), Nat.double(Nat.pow(2n,
        qq)), Nat.pow(2n, 1n+qq), Equal.sym(Nat, Nat.pow(2n, 1n+qq), Nat.double(Nat.pow(2n, qq)), R.pow2_succ(qq)),
        dbl_le(Nat.pow(2n, pp), Nat.pow(2n, qq), pow_le(pp, qq, hh))))

# shifting a word left doubles it, when it is below 2^e and e is at most p
def shl_ok(
  +pp: Nat,
  +ww: Word(1n+pp),
  +ee: Nat,
  +h1: {Nat.is_lt(Word.to_nat(1n+pp, ww), Nat.pow(2n, ee)) == True{} : Bool},
  +h2: {Nat.is_le(ee, pp) == True{} : Bool}
) -> {Word.to_nat(1n+pp, Word.shl(1n+pp, ww)) == Nat.double(Word.to_nat(1n+pp, ww)) : Nat}:
  match ww:
    case WCon{+bb, +tt}:
      +xn = Nat.add(R.bit(bb), Nat.double(Word.to_nat(pp, tt)))
      +hx = {R.lt_le_trans(xn, Nat.pow(2n, ee), Nat.pow(2n, pp), R.lt_rw_l(Word.to_nat(1n+pp, WCon{bb, tt}), xn,
        Nat.pow(2n, ee), R.to_nat_con(pp, bb, tt), h1), pow_le(ee, pp, h2)) : {Nat.is_lt(xn, Nat.pow(2n,
        pp)) == True{} :
        Bool}}
      Equal.trans(Nat, Nat.double(Word.to_nat(pp, Word.shl.put(pp, bb, tt))), Nat.double(xn),
        Nat.double(Word.to_nat(1n+pp, WCon{bb, tt})), Equal.cong(Nat, Nat, nn => Nat.double(nn), Word.to_nat(pp,
        Word.shl.put(pp, bb, tt)), xn, R.shl_put_nat(pp, bb, tt, hx)), Equal.cong(Nat, Nat, nn => Nat.double(nn), xn,
        Word.to_nat(1n+pp, WCon{bb, tt}), Equal.sym(Nat, Word.to_nat(1n+pp, WCon{bb, tt}), xn, R.to_nat_con(pp, bb,
        tt))))

# U32 shl doubles a number below 2^e, e at most 31
def shl_u(
  +uu: U32,
  +ee: Nat,
  +h1: {Nat.is_lt(U32.to_nat(uu), Nat.pow(2n, ee)) == True{} : Bool},
  +h2: {Nat.is_le(ee, 31n) == True{} : Bool}
) -> {U32.to_nat(U32.shl(uu)) == Nat.double(U32.to_nat(uu)) : Nat}:
  match uu:
    case U32{+ww}:
      shl_ok(31n, ww, ee, h1, h2)

# numbers each at most the other are equal
def le_anti(
  +xx: Nat,
  +yy: Nat,
  +h1: {Nat.is_le(xx, yy) == True{} : Bool},
  +h2: {Nat.is_le(yy, xx) == True{} : Bool}
) -> {xx == yy : Nat}:
  match xx yy:
    case 0n 0n:
      {==}
    case 0n 1n+_qq:
      Empty.absurd({0n == yy : Nat}, U32L.false_true(h2))
    case 1n+_pp 0n:
      Empty.absurd({xx == 0n : Nat}, U32L.false_true(h1))
    case 1n+pp 1n+qq:
      Equal.cong(Nat, Nat, nn => 1n+nn, pp, qq, le_anti(pp, qq, h1, h2))

# one more than a number is not at most it
def succ_nle(+xx: Nat) -> {Nat.is_le(1n+xx, xx) == False{} : Bool}:
  match xx:
    case 0n:
      {==}
    case 1n+pp:
      succ_nle(pp)

# not at most is above
def nle_lt(+aa: Nat, +bb: Nat, +hh: {Nat.is_le(aa, bb) == False{} : Bool}) -> {Nat.is_lt(bb, aa) == True{} : Bool}:
  match aa bb:
    case 0n _bb:
      Empty.absurd({Nat.is_lt(bb, 0n) == True{} : Bool}, U32L.false_true(Equal.trans(Bool, False{}, Nat.is_le(0n, bb),
        True{}, Equal.sym(Bool, Nat.is_le(0n, bb), False{}, hh), R.le_zero(bb))))
    case 1n+_pp 0n:
      {==}
    case 1n+pp 1n+qq:
      nle_lt(pp, qq, hh)

# a walk count at most 31 is below 32
def lt32(+dd: Nat, +hh: {Nat.is_le(dd, 31n) == True{} : Bool}) -> {Nat.is_lt(dd, 32n) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_lt(dd, 32n), Nat.is_le(1n+dd, 32n), True{}, R.lt_le_succ(dd, 32n), hh)

# a number is below 2^(1 + its log2), when the log2 is below 32
def dep_up(
  zz: Bool,
  +mm: U32,
  +ez: {Nat.is_le(Nat.pow(2n, 1n+U32.log2(mm)), U32.to_nat(mm)) == zz : Bool},
  +h32: {Nat.is_lt(U32.log2(mm), 32n) == True{} : Bool}
) -> {Nat.is_lt(U32.to_nat(mm), Nat.pow(2n, 1n+U32.log2(mm))) == True{} : Bool}:
  match zz:
    case False{}:
      nle_lt(Nat.pow(2n, 1n+U32.log2(mm)), U32.to_nat(mm), ez)
    case True{}:
      +dd = U32.log2(mm)
      +hk = {Equal.trans(Bool, Nat.is_le(1n+dd, 32n), Nat.is_lt(dd, 32n), True{}, Equal.sym(Bool, Nat.is_lt(dd, 32n),
        Nat.is_le(1n+dd, 32n), R.lt_le_succ(dd, 32n)), h32) : {Nat.is_le(1n+dd, 32n) == True{} : Bool}}
      Empty.absurd({Nat.is_lt(U32.to_nat(mm), Nat.pow(2n, 1n+dd)) == True{} : Bool}, U32L.false_true(Equal.trans(Bool,
        False{}, Nat.is_le(1n+dd, dd), True{}, Equal.sym(Bool, Nat.is_le(1n+dd, dd), False{}, succ_nle(dd)), le2(32n,
        1n+dd, mm, 0n, hk, ez))))

# the plane's depth, for nn from 1 below 2^e, e at most 31: at most e, and 2^depth at least nn
def dep_a(
  +nn: U32,
  +ee: Nat,
  +hpos: {Nat.is_lt(0n, U32.to_nat(nn)) == True{} : Bool},
  +he: {Nat.is_le(ee, 31n) == True{} : Bool},
  +hlt: {Nat.is_lt(U32.to_nat(nn), Nat.pow(2n, ee)) == True{} : Bool}
) -> {Bool.and(Nat.is_le(U32.log2((U32.shl(nn) - 1 : U32)), ee), Nat.is_le(U32.to_nat(nn), Nat.pow(2n,
  U32.log2((U32.shl(nn) - 1 : U32))))) == True{} : Bool}:
  +sh = U32.shl(nn)
  +mm = (sh - 1 : U32)
  +dd = U32.log2(mm)
  +n2 = Nat.double(U32.to_nat(nn))
  +es = {shl_u(nn, ee, hlt, he) : {U32.to_nat(sh) == n2 : Nat}}
  +h1 = {R.le_rw_r(1n, n2, U32.to_nat(sh), Equal.sym(Nat, U32.to_nat(sh), n2, es), R.le_trans(1n, U32.to_nat(nn), n2,
    Equal.trans(Bool, Nat.is_le(1n, U32.to_nat(nn)), Nat.is_lt(0n, U32.to_nat(nn)), True{}, Equal.sym(Bool,
    Nat.is_lt(0n, U32.to_nat(nn)), Nat.is_le(1n, U32.to_nat(nn)), R.lt_le_succ(0n, U32.to_nat(nn))), hpos),
    half_le(False{}, U32.to_nat(nn)))) : {Nat.is_le(1n, U32.to_nat(sh)) == True{} : Bool}}
  +em = {Equal.trans(Nat, U32.to_nat(mm), Nat.sub(U32.to_nat(sh), 1n), Nat.sub(n2, 1n), R.u32_sub_nat(sh, 1, h1),
    Equal.cong(Nat, Nat, xx => Nat.sub(xx, 1n), U32.to_nat(sh), n2, es)) : {U32.to_nat(mm) == Nat.sub(n2, 1n) : Nat}}
  +h1n = {R.le_rw_r(1n, U32.to_nat(sh), n2, es, h1) : {Nat.is_le(1n, n2) == True{} : Bool}}
  +hm = {R.lt_rw_l(Nat.sub(n2, 1n), U32.to_nat(mm), Nat.pow(2n, 1n+ee), Equal.sym(Nat, U32.to_nat(mm), Nat.sub(n2, 1n),
    em), R.le_lt_trans(Nat.sub(n2, 1n), n2, Nat.pow(2n, 1n+ee), R.sub_le(n2, 1n), R.lt_rw_r(n2,
    Nat.double(Nat.pow(2n, ee)), Nat.pow(2n, 1n+ee), Equal.sym(Nat, Nat.pow(2n, 1n+ee), Nat.double(Nat.pow(2n, ee)),
    R.pow2_succ(ee)), dbl_lt(U32.to_nat(nn), Nat.pow(2n, ee), hlt)))) : {Nat.is_lt(U32.to_nat(mm), Nat.pow(2n,
    1n+ee)) ==
    True{} : Bool}}
  +hd = {le1(32n, ee, mm, 0n, hm) : {Nat.is_le(dd, ee) == True{} : Bool}}
  +hup = {dep_up(Nat.is_le(Nat.pow(2n, 1n+dd), U32.to_nat(mm)), mm, {==}, lt32(dd, R.le_trans(dd, ee, 31n, hd,
    he))) : {Nat.is_lt(U32.to_nat(mm), Nat.pow(2n, 1n+dd)) == True{} : Bool}}
  +hup2 = {R.lt_rw_r(Nat.sub(n2, 1n), Nat.pow(2n, 1n+dd), Nat.double(Nat.pow(2n, dd)), R.pow2_succ(dd), R.lt_rw_l(
    U32.to_nat(mm), Nat.sub(n2, 1n), Nat.pow(2n, 1n+dd), em, hup)) : {Nat.is_lt(Nat.sub(n2, 1n), Nat.double(Nat.pow(2n,
    dd))) == True{} : Bool}}
  +h3 = {R.le_rw_l(Nat.add(1n, Nat.sub(n2, 1n)), n2, Nat.double(Nat.pow(2n, dd)), R.add_sub(1n, n2, h1n),
    Equal.trans(Bool, Nat.is_le(1n+Nat.sub(n2, 1n), Nat.double(Nat.pow(2n, dd))), Nat.is_lt(Nat.sub(n2, 1n),
    Nat.double(Nat.pow(2n, dd))), True{}, Equal.sym(Bool, Nat.is_lt(Nat.sub(n2, 1n), Nat.double(Nat.pow(2n, dd))),
    Nat.is_le(1n+Nat.sub(n2, 1n), Nat.double(Nat.pow(2n, dd))), R.lt_le_succ(Nat.sub(n2, 1n), Nat.double(Nat.pow(2n,
    dd)))), hup2)) : {Nat.is_le(n2, Nat.double(Nat.pow(2n, dd))) == True{} : Bool}}
  +hn = {R.le_half(False{}, U32.to_nat(nn), Nat.pow(2n, dd), h3) : {Nat.is_le(U32.to_nat(nn), Nat.pow(2n, dd)) ==
    True{} : Bool}}
  Equal.trans(Bool, Bool.and(Nat.is_le(dd, ee), Nat.is_le(U32.to_nat(nn), Nat.pow(2n, dd))), Bool.and(True{},
    Nat.is_le(U32.to_nat(nn), Nat.pow(2n, dd))), True{}, Equal.cong(Bool, Bool, bb => Bool.and(bb,
    Nat.is_le(U32.to_nat(nn), Nat.pow(2n, dd))), Nat.is_le(dd, ee), True{}, hd), hn)

# U32s of one number are one U32
def u32_nat_eq(+aa: U32, +bb: U32, +ee: {U32.to_nat(aa) == U32.to_nat(bb) : Nat}) -> {aa == bb : U32}:
  U32L.ueq(aa, bb, Equal.trans(Bool, U32.is_eq(aa, bb), Nat.is_eq(U32.to_nat(aa), U32.to_nat(bb)), True{},
    R.u32_eq(aa, bb), Equal.trans(Bool, Nat.is_eq(U32.to_nat(aa), U32.to_nat(bb)), Nat.is_eq(U32.to_nat(bb),
    U32.to_nat(bb)), True{}, Equal.cong(Nat, Bool, xx => Nat.is_eq(xx, U32.to_nat(bb)), U32.to_nat(aa), U32.to_nat(bb),
    ee), R.nat_eq_refl(U32.to_nat(bb)))))

# a number above zero is below its double
def lt_dbl(+xx: Nat, +hh: {Nat.is_lt(0n, xx) == True{} : Bool}) -> {Nat.is_lt(xx, Nat.double(xx)) == True{} : Bool}:
  R.lt_rw_l(Nat.add(xx, 0n), xx, Nat.double(xx), R.add_zero(xx), R.lt_rw_r(Nat.add(xx, 0n), Nat.add(xx, xx),
    Nat.double(xx), Equal.sym(Nat, Nat.double(xx), Nat.add(xx, xx), R.double_add(xx)), R.lt_add_mono(xx, 0n, xx, hh)))

# the plane's depth is below 32 when it is at most e and e at most 31, and 2^depth is at least nn
def dep_fin(
  +ll: Nat,
  +ee: Nat,
  +nn: U32,
  +he: {Nat.is_le(ee, 31n) == True{} : Bool},
  +hh: {Bool.and(Nat.is_le(ll, ee), Nat.is_le(U32.to_nat(nn), Nat.pow(2n, ll))) == True{} : Bool}
) -> {Bool.and(Nat.is_lt(ll, 32n), Nat.is_le(U32.to_nat(nn), Nat.pow(2n, ll))) == True{} : Bool}:
  +hl = {U32L.and_left(Nat.is_le(ll, ee), Nat.is_le(U32.to_nat(nn), Nat.pow(2n, ll)), hh) : {Nat.is_le(ll, ee) ==
    True{} : Bool}}
  +hn = {U32L.and_right(Nat.is_le(ll, ee), Nat.is_le(U32.to_nat(nn), Nat.pow(2n, ll)), hh) : {Nat.is_le(U32.to_nat(nn),
    Nat.pow(2n, ll)) == True{} : Bool}}
  Equal.trans(Bool, Bool.and(Nat.is_lt(ll, 32n), Nat.is_le(U32.to_nat(nn), Nat.pow(2n, ll))), Bool.and(True{},
    Nat.is_le(U32.to_nat(nn), Nat.pow(2n, ll))), True{}, Equal.cong(Bool, Bool, bb => Bool.and(bb,
    Nat.is_le(U32.to_nat(nn), Nat.pow(2n, ll))), Nat.is_lt(ll, 32n), True{}, lt32(ll, R.le_trans(ll, ee, 31n, hl, he))),
    hn)

# the plane's depth when nn is 2^d exactly: d below 31, or 31 itself, where U32 shl wraps and the depth is 31
def dep_top(
  zz: Bool,
  +nn: U32,
  +dd: Nat,
  +ez: {Nat.is_lt(dd, 31n) == zz : Bool},
  +hpos: {Nat.is_lt(0n, U32.to_nat(nn)) == True{} : Bool},
  +hdd: {Nat.is_le(dd, 31n) == True{} : Bool},
  +hq: {U32.to_nat(nn) == Nat.pow(2n, dd) : Nat}
) -> {Bool.and(Nat.is_lt(U32.log2((U32.shl(nn) - 1 : U32)), 32n), Nat.is_le(U32.to_nat(nn), Nat.pow(2n,
  U32.log2((U32.shl(nn) - 1 : U32))))) == True{} : Bool}:
  match zz:
    case True{}:
      +pw = Nat.pow(2n, dd)
      +h1 = {Equal.trans(Bool, Nat.is_le(1n+dd, 31n), Nat.is_lt(dd, 31n), True{}, Equal.sym(Bool, Nat.is_lt(dd, 31n),
        Nat.is_le(1n+dd, 31n), R.lt_le_succ(dd, 31n)), ez) : {Nat.is_le(1n+dd, 31n) == True{} : Bool}}
      +h2 = {R.lt_rw_l(pw, U32.to_nat(nn), Nat.pow(2n, 1n+dd), Equal.sym(Nat, U32.to_nat(nn), pw, hq), R.lt_rw_r(pw,
        Nat.double(pw), Nat.pow(2n, 1n+dd), Equal.sym(Nat, Nat.pow(2n, 1n+dd), Nat.double(pw), R.pow2_succ(dd)),
        lt_dbl(pw, pow_pos(dd)))) : {Nat.is_lt(U32.to_nat(nn), Nat.pow(2n, 1n+dd)) == True{} : Bool}}
      dep_fin(U32.log2((U32.shl(nn) - 1 : U32)), 1n+dd, nn, h1, dep_a(nn, 1n+dd, hpos, h1, h2))
    case False{}:
      +d31 = {le_anti(dd, 31n, hdd, R.not_lt_le(dd, 31n, ez)) : {dd == 31n : Nat}}
      +en = {u32_nat_eq(nn, U32{sbit(32n, dd)}, Equal.trans(Nat, U32.to_nat(nn), Nat.pow(2n, dd),
        U32.to_nat(U32{sbit(32n,
        dd)}), hq, Equal.sym(Nat, Word.to_nat(32n, sbit(32n, dd)), Nat.pow(2n, dd), sbit_nat(32n, dd, lt32(dd,
        hdd))))) :
        {nn == U32{sbit(32n, dd)} : U32}}
      +el = {Equal.trans(Nat, U32.log2((U32.shl(nn) - 1 : U32)), U32.log2((U32.shl(U32{sbit(32n, dd)}) - 1 : U32)), dd,
        Equal.cong(U32, Nat, uu => U32.log2((U32.shl(uu) - 1 : U32)), nn, U32{sbit(32n, dd)}, en), Equal.trans(Nat,
        U32.log2((U32.shl(U32{sbit(32n, dd)}) - 1 : U32)), U32.log2((U32.shl(U32{sbit(32n, 31n)}) - 1 : U32)), dd,
        Equal.cong(Nat, Nat, ee => U32.log2((U32.shl(U32{sbit(32n, ee)}) - 1 : U32)), dd, 31n, d31), Equal.sym(Nat, dd,
        31n, d31))) : {U32.log2((U32.shl(nn) - 1 : U32)) == dd : Nat}}
      +sl = Equal.sym(Nat, U32.log2((U32.shl(nn) - 1 : U32)), dd, el)
      %sl : {Bool.and(Nat.is_lt(_, 32n), Nat.is_le(U32.to_nat(nn), Nat.pow(2n, _))) == True{} : Bool}
      Equal.trans(Bool, Bool.and(Nat.is_lt(dd, 32n), Nat.is_le(U32.to_nat(nn), Nat.pow(2n, dd))), Bool.and(True{},
        Nat.is_le(U32.to_nat(nn), Nat.pow(2n, dd))), True{}, Equal.cong(Bool, Bool, bb => Bool.and(bb,
        Nat.is_le(U32.to_nat(nn), Nat.pow(2n, dd))), Nat.is_lt(dd, 32n), True{}, lt32(dd, hdd)), R.le_rw_l(Nat.pow(2n,
        dd), U32.to_nat(nn), Nat.pow(2n, dd), Equal.sym(Nat, U32.to_nat(nn), Nat.pow(2n, dd), hq), R.le_refl(Nat.pow(2n,
        dd))))

# the plane's depth for nn from 1 to 2^d, d at most 31, split on whether nn is below 2^d
def dep_lt(
  zz: Bool,
  +nn: U32,
  +dd: Nat,
  +ez: {Nat.is_lt(U32.to_nat(nn), Nat.pow(2n, dd)) == zz : Bool},
  +hpos: {Nat.is_lt(0n, U32.to_nat(nn)) == True{} : Bool},
  +hdd: {Nat.is_le(dd, 31n) == True{} : Bool},
  +hnn: {Nat.is_le(U32.to_nat(nn), Nat.pow(2n, dd)) == True{} : Bool}
) -> {Bool.and(Nat.is_lt(U32.log2((U32.shl(nn) - 1 : U32)), 32n), Nat.is_le(U32.to_nat(nn), Nat.pow(2n,
  U32.log2((U32.shl(nn) - 1 : U32))))) == True{} : Bool}:
  match zz:
    case True{}:
      dep_fin(U32.log2((U32.shl(nn) - 1 : U32)), dd, nn, hdd, dep_a(nn, dd, hpos, hdd, ez))
    case False{}:
      dep_top(Nat.is_lt(dd, 31n), nn, dd, {==}, hpos, hdd, le_anti(U32.to_nat(nn), Nat.pow(2n, dd), hnn,
        R.not_lt_le(U32.to_nat(nn), Nat.pow(2n, dd), ez)))

# the depth decode.plane takes for nn points, 1 to 2^d, d at most 31: below 32, and 2^depth at least nn
def dep(
  +nn: U32,
  +dd: Nat,
  +hpos: {Nat.is_lt(0n, U32.to_nat(nn)) == True{} : Bool},
  +hdd: {Nat.is_le(dd, 31n) == True{} : Bool},
  +hnn: {Nat.is_le(U32.to_nat(nn), Nat.pow(2n, dd)) == True{} : Bool}
) -> {Bool.and(Nat.is_lt(Jpeg.decode.depth(nn), 32n), Nat.is_le(U32.to_nat(nn), Nat.pow(2n, Jpeg.decode.depth(nn)))) ==
  True{} : Bool}:
  +e0 = {Equal.trans(Bool, U32.is_eq(nn, 0), Nat.is_eq(U32.to_nat(nn), 0n), False{}, R.u32_eq(nn, 0),
    gt_neq(U32.to_nat(nn),
    0n, hpos)) : {U32.is_eq(nn, 0) == False{} : Bool}}
  +se = Equal.sym(Bool, U32.is_eq(nn, 0), False{}, e0)
  %se : {Bool.and(Nat.is_lt(Jpeg.decode.depth.of(_, nn), 32n), Nat.is_le(U32.to_nat(nn), Nat.pow(2n,
    Jpeg.decode.depth.of(_, nn)))) == True{} : Bool}
  dep_lt(Nat.is_lt(U32.to_nat(nn), Nat.pow(2n, dd)), nn, dd, {==}, hpos, hdd, hnn)

# ---- a new plane ----

# the tree of 2^d leaves, every one v
def full(+dd: Nat, +vv: U32) -> Tr:
  match dd:
    case 0n:
      TLeaf{vv}
    case 1n+ee:
      TNode{full(ee, vv), full(ee, vv)}

# Array.new is the array of that tree
def new_arr(+dd: Nat, +vv: U32) -> {Array.new(U32, dd, vv) == arr(full(dd, vv)) : Array<U32>}:
  match dd:
    case 0n:
      {==}
    case 1n+ee:
      ee1 = Equal.sym(Array<U32>, Array.new(U32, ee, vv), arr(full(ee, vv)), new_arr(ee, vv))
      ee2 = Equal.sym(Array<U32>, Array.new(U32, ee, vv), arr(full(ee, vv)), new_arr(ee, vv))
      %ee1 : {ANode{_, Array.new(U32, ee, vv)} == ANode{arr(full(ee, vv)), arr(full(ee, vv))} : Array<U32>}
      %ee2 : {ANode{arr(full(ee, vv)), _} == ANode{arr(full(ee, vv)), arr(full(ee, vv))} : Array<U32>}
      {==}

# that tree is perfect
def pf_full(+dd: Nat, +vv: U32) -> {pf(dd, full(dd, vv)) == True{} : Bool}:
  match dd:
    case 0n:
      {==}
    case 1n+ee:
      +ih = pf_full(ee, vv)
      Equal.trans(Bool, Bool.and(pf(ee, full(ee, vv)), pf(ee, full(ee, vv))), Bool.and(True{}, pf(ee, full(ee, vv))),
        True{}, Equal.cong(Bool, Bool, bb => Bool.and(bb, pf(ee, full(ee, vv))), pf(ee, full(ee, vv)), True{}, ih), ih)

# a pick between one value and itself is the value
def pick_same(zz: Bool, +vv: U32) -> {Bool.pick(U32, zz, vv, vv) == vv : U32}:
  match zz:
    case True{}:
      {==}
    case False{}:
      {==}

# every read of that tree finds v
def get_full(+dd: Nat, +vv: U32, +nn: U32, +ii: U32) -> {get(full(dd, vv), nn, ii) == vv : U32}:
  match dd:
    case 0n:
      {==}
    case 1n+ee:
      +hh = U32.shr(nn)
      +el = get_full(ee, vv, hh, ii)
      +eh = get_full(ee, vv, hh, U32.sub(ii, hh))
      Equal.trans(U32, Bool.pick(U32, U32.is_lt(ii, hh), get(full(ee, vv), hh, ii), get(full(ee, vv), hh, U32.sub(ii,
        hh))), Bool.pick(U32, U32.is_lt(ii, hh), vv, get(full(ee, vv), hh, U32.sub(ii, hh))), vv, Equal.cong(U32, U32,
        xx => Bool.pick(U32, U32.is_lt(ii, hh), xx, get(full(ee, vv), hh, U32.sub(ii, hh))), get(full(ee, vv), hh, ii),
        vv, el), Equal.trans(U32, Bool.pick(U32, U32.is_lt(ii, hh), vv, get(full(ee, vv), hh, U32.sub(ii, hh))),
        Bool.pick(U32, U32.is_lt(ii, hh), vv, vv), vv, Equal.cong(U32, U32, xx => Bool.pick(U32, U32.is_lt(ii, hh), vv,
        xx), get(full(ee, vv), hh, U32.sub(ii, hh)), vv, eh), pick_same(U32.is_lt(ii, hh), vv)))

# a new plane is perfect
def plane_perfect(+nn: U32) -> {Laws.jpg.perfect(Jpeg.decode.depth(nn), Jpeg.decode.plane(nn)) == True{} : Bool}:
  +dd = Jpeg.decode.depth(nn)
  Equal.trans(Bool, Laws.jpg.perfect(dd, Array.new(U32, dd, 0)), Laws.jpg.perfect(dd, arr(full(dd, 0))), True{},
    Equal.cong(Array<U32>, Bool, aa => Laws.jpg.perfect(dd, aa), Array.new(U32, dd, 0), arr(full(dd, 0)), new_arr(dd,
    0)), Equal.trans(Bool, Laws.jpg.perfect(dd, arr(full(dd, 0))), pf(dd, full(dd, 0)), True{}, perfect_arr(dd, full(dd,
    0)), pf_full(dd, 0)))

# every point of a new plane is 0
def plane_zero(+nn: U32, +kk: U32) -> {Laws.jpg.val(Array.get(U32, Jpeg.decode.plane(nn), kk)) == 0 : U32}:
  +dd = Jpeg.decode.depth(nn)
  +tt = full(dd, 0)
  Equal.trans(U32, Laws.jpg.val(Array.get(U32, Array.new(U32, dd, 0), kk)), Laws.jpg.val(Array.get(U32, arr(tt), kk)),
    0, Equal.cong(Array<U32>, U32, aa => Laws.jpg.val(Array.get(U32, aa, kk)), Array.new(U32, dd, 0), arr(tt),
    new_arr(dd, 0)), Equal.trans(U32, Laws.jpg.val(Array.get(U32, arr(tt), kk)), at(tt, kk), 0, val_at(tt, kk),
    get_full(dd, 0, size(tt), mask(kk, size(tt)))))

# ---- the decoder's block run ----

# jpeg_blocks_paint: decode.blocks paints each unit it decodes where jpg.paint.all does
def blocks_paint(
  +left: Nat,
  +blk: Jpeg.Blk,
  +ctrl: Jpeg.Ctrl,
  +preds: Jpeg.Preds,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ri: U32,
  -yy: Array<U32>,
  -cb: Array<U32>,
  -cr: Array<U32>,
  +ok: U32
) -> {Jpeg.decode.blocks(left, blk, ctrl, preds, frame, scan, tabs, ri, yy, cb, cr, ok) ==
  Jpeg.decode.done(Laws.jpg.run.ok(left, blk, ctrl, preds, frame, scan, tabs, ri, ok), frame,
  Laws.jpg.paint.all(Laws.jpg.units.run(left, blk, ctrl, preds, frame, scan, tabs, ri), 0, frame, scan, yy),
  Laws.jpg.paint.all(Laws.jpg.units.run(left, blk, ctrl, preds, frame, scan, tabs, ri), 1, frame, scan, cb),
  Laws.jpg.paint.all(Laws.jpg.units.run(left, blk, ctrl, preds, frame, scan, tabs, ri), 2, frame, scan, cr)) :
  Maybe<&2, Jpeg.Pic>}:
  match left blk ctrl frame scan:
    case 0n Jpeg.Blk{+_samples, +_bits, +_pred, +_bok} Jpeg.Ctrl{+_comp, +_bi, +_mx, +_my, +_mcu, +_rst} Jpeg.Frame{+_w,
      +_h, +_nf, +_ids, +_hs, +_vs, +_tq, +_hmax, +_vmax} Jpeg.Scan{+_ns, +_sids, +_td, +_ta, +_ss, +_se, +_ah}:
      {==}
    case 1n+pp Jpeg.Blk{+samples, +bits, +pred, +bok} Jpeg.Ctrl{+comp, +bi, +mx, +my, +mcu, +rst} Jpeg.Frame{+w, +h,
      +nf,
      +ids, +hs, +vs, +tq, +hmax, +vmax} Jpeg.Scan{+ns, +sids, +td, +ta, +ss, +se, +ah}:
      +cc = {Jpeg.Ctrl{comp, bi, mx, my, mcu, rst} : Jpeg.Ctrl}
      +fr = {Jpeg.Frame{w, h, nf, ids, hs, vs, tq, hmax, vmax} : Jpeg.Frame}
      +sc = {Jpeg.Scan{ns, sids, td, ta, ss, se, ah} : Jpeg.Scan}
      +gg = Jpeg.decode.geom(cc, fr, sc)
      +av = Jpeg.decode.adv(cc, fr, sc, ri)
      blocks_paint(pp, Jpeg.decode.block.next(bits, preds, pred, cc, fr, sc, tabs, ri), Jpeg.decode.adv.ctrl(av),
        Jpeg.decode.preds.next(Jpeg.decode.adv.duef(av), preds, comp, pred), fr, sc, tabs, ri,
        Jpeg.decode.paint.use(gg, U32.is_eq(comp, 0), samples, yy), Jpeg.decode.paint.use(gg, U32.is_eq(comp, 1),
        samples, cb), Jpeg.decode.paint.use(gg, U32.is_eq(comp, 2), samples, cr), (ok * bok : U32))

# ---- a plane after the run ----

# a block's fields
def g.ox(gg: Jpeg.Geom) -> U32:
  match gg:
    case Jpeg.Geom{+ox, _oy, _pw, _ph, _ww, _hh}:
      ox

# a block's fields
def g.oy(gg: Jpeg.Geom) -> U32:
  match gg:
    case Jpeg.Geom{_ox, +oy, _pw, _ph, _ww, _hh}:
      oy

# a block's fields
def g.pw(gg: Jpeg.Geom) -> U32:
  match gg:
    case Jpeg.Geom{_ox, _oy, +pw, _ph, _ww, _hh}:
      pw

# a block's fields
def g.ph(gg: Jpeg.Geom) -> U32:
  match gg:
    case Jpeg.Geom{_ox, _oy, _pw, +ph, _ww, _hh}:
      ph

# a unit's block, as the frame's width and height and its own origin and sample size
def g.of(+gg: Jpeg.Geom, +ww: U32, +hh: U32) -> Jpeg.Geom:
  Jpeg.Geom{g.ox(gg), g.oy(gg), g.pw(gg), g.ph(gg), ww, hh}

# decode.geom's block carries the frame's width and height
def geom_eq(
  +ctrl: Jpeg.Ctrl,
  +ww: U32,
  +hh: U32,
  +nf: U32,
  +ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>,
  +tq: List<&2, U32>,
  +hmax: U32,
  +vmax: U32,
  +scan: Jpeg.Scan
) -> {Jpeg.decode.geom(ctrl, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan) ==
  g.of(Jpeg.decode.geom(ctrl, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan), ww, hh) : Jpeg.Geom}:
  match ctrl scan:
    case Jpeg.Ctrl{+_comp, +_bi, +_mx, +_my, +_mcu, +_rst} Jpeg.Scan{+_ns, +_sids, +_td, +_ta, +_ss, +_se, +_ah}:
      {==}

# decode.paint.use on the tree
def puT(which: Bool, +gg: Jpeg.Geom, +samples: List<&2, U32>, +tt: Tr) -> Tr:
  match which gg:
    case True{} Jpeg.Geom{+ox, +oy, +pw, +ph, +ww, +hh}:
      cvT(8n, tt, samples, 0, ox, oy, pw, ph, ww, hh)
    case False{} _gg:
      tt

# decode.paint.use on a tree's array is the tree's
def arr_pu(
  which: Bool,
  +gg: Jpeg.Geom,
  +samples: List<&2, U32>,
  +tt: Tr
) -> {Jpeg.decode.paint.use(gg, which, samples, arr(tt)) == arr(puT(which, gg, samples, tt)) : Array<U32>}:
  match which gg:
    case True{} Jpeg.Geom{+ox, +oy, +pw, +ph, +ww, +hh}:
      arr_cv(8n, tt, samples, 0, ox, oy, pw, ph, ww, hh)
    case False{} Jpeg.Geom{+_ox, +_oy, +_pw, +_ph, +_ww, +_hh}:
      {==}

# decode.paint.use keeps a tree perfect
def pf_pu(
  which: Bool,
  +gg: Jpeg.Geom,
  +samples: List<&2, U32>,
  +dd: Nat,
  +tt: Tr,
  +hp: {pf(dd, tt) == True{} : Bool}
) -> {pf(dd, puT(which, gg, samples, tt)) == True{} : Bool}:
  match which gg:
    case True{} Jpeg.Geom{+ox, +oy, +pw, +ph, +ww, +hh}:
      pf_cv(8n, dd, tt, samples, 0, ox, oy, pw, ph, ww, hh, hp)
    case False{} Jpeg.Geom{+_ox, +_oy, +_pw, +_ph, +_ww, +_hh}:
      hp

# decode.paint.use of a block in the frame, read at pixel (x, y): the block's value there when painted, else the old
def rd_pu(
  which: Bool,
  +ox: U32,
  +oy: U32,
  +pw: U32,
  +ph: U32,
  +ww: U32,
  +hh: U32,
  +samples: List<&2, U32>,
  +dd: Nat,
  +tt: Tr,
  +xx: U32,
  +yy: U32,
  +hp: {pf(dd, tt) == True{} : Bool},
  +hd: {Nat.is_lt(dd, 32n) == True{} : Bool},
  +hfit: {Nat.is_le(Nat.mul(U32.to_nat(ww), U32.to_nat(hh)), Nat.pow(2n, dd)) == True{} : Bool},
  +hx: {U32.is_lt(xx, ww) == True{} : Bool},
  +hy: {U32.is_lt(yy, hh) == True{} : Bool}
) -> {at(puT(which, Jpeg.Geom{ox, oy, pw, ph, ww, hh}, samples, tt), (yy * ww + xx : U32)) == Bool.pick(U32, which,
  Laws.jpg.block.at(Jpeg.Geom{ox, oy, pw, ph, ww, hh}, samples, xx, yy, at(tt, (yy * ww + xx : U32))), at(tt, (yy * ww +
  xx : U32))) : U32}:
  match which:
    case True{}:
      rd_cv(8n, dd, tt, samples, 0, ox, oy, pw, ph, ww, hh, xx, yy, hp, hd, hfit, hx, hy)
    case False{}:
      {==}

# a tree's plane with a scan component's units painted, read at pixel (x, y): jpg.point
def plane_at_t(
  +us: List<&2, Laws.JUnit>,
  +comp: U32,
  +dd: Nat,
  +tt: Tr,
  +ww: U32,
  +hh: U32,
  +nf: U32,
  +ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>,
  +tq: List<&2, U32>,
  +hmax: U32,
  +vmax: U32,
  +scan: Jpeg.Scan,
  +xx: U32,
  +yy: U32,
  +hp: {pf(dd, tt) == True{} : Bool},
  +hd: {Nat.is_lt(dd, 32n) == True{} : Bool},
  +hfit: {Nat.is_le(Nat.mul(U32.to_nat(ww), U32.to_nat(hh)), Nat.pow(2n, dd)) == True{} : Bool},
  +hx: {U32.is_lt(xx, ww) == True{} : Bool},
  +hy: {U32.is_lt(yy, hh) == True{} : Bool}
) -> {Laws.jpg.val(Array.get(U32, Laws.jpg.paint.all(us, comp, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax},
  scan,
  arr(tt)), (yy * ww + xx : U32))) == Laws.jpg.point(us, comp, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax},
  scan,
  xx, yy, at(tt, (yy * ww + xx : U32))) : U32}:
  match us:
    case Nil{}:
      val_at(tt, (yy * ww + xx : U32))
    case Laws.JUnit{+ctrl, +samples} <> rest:
      +fr = {Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax} : Jpeg.Frame}
      +kk = (yy * ww + xx : U32)
      +gg = Jpeg.decode.geom(ctrl, fr, scan)
      +g2 = g.of(gg, ww, hh)
      +wh = U32.is_eq(Jpeg.decode.ctrl.comp(ctrl), comp)
      +t1 = puT(wh, g2, samples, tt)
      +ac = at(tt, kk)
      +eg = {geom_eq(ctrl, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan) : {gg == g2 : Jpeg.Geom}}
      +e1 = {Equal.trans(Array<U32>, Jpeg.decode.paint.use(gg, wh, samples, arr(tt)), Jpeg.decode.paint.use(g2, wh,
        samples, arr(tt)), arr(t1), Equal.cong(Jpeg.Geom, Array<U32>, qq => Jpeg.decode.paint.use(qq, wh, samples,
        arr(tt)), gg, g2, eg), arr_pu(wh, g2, samples, tt)) : {Jpeg.decode.paint.use(gg, wh, samples, arr(tt)) ==
        arr(t1) : Array<U32>}}
      +e2 = {Equal.cong(Array<U32>, U32, aa => Laws.jpg.val(Array.get(U32, Laws.jpg.paint.all(rest, comp, fr, scan, aa),
        kk)), Jpeg.decode.paint.use(gg, wh, samples, arr(tt)), arr(t1), e1) : {Laws.jpg.val(Array.get(U32,
        Laws.jpg.paint.all(rest, comp, fr, scan, Jpeg.decode.paint.use(gg, wh, samples, arr(tt))), kk)) ==
        Laws.jpg.val(Array.get(U32, Laws.jpg.paint.all(rest, comp, fr, scan, arr(t1)), kk)) : U32}}
      +ih = {plane_at_t(rest, comp, dd, t1, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan, xx, yy, pf_pu(wh, g2,
        samples,
        dd, tt, hp), hd, hfit, hx, hy) : {Laws.jpg.val(Array.get(U32, Laws.jpg.paint.all(rest, comp, fr, scan, arr(t1)),
        kk)) == Laws.jpg.point(rest, comp, fr, scan, xx, yy, at(t1, kk)) : U32}}
      +e3 = {rd_pu(wh, g.ox(gg), g.oy(gg), g.pw(gg), g.ph(gg), ww, hh, samples, dd, tt, xx, yy, hp, hd, hfit, hx, hy) :
        {at(t1, kk) == Bool.pick(U32, wh, Laws.jpg.block.at(g2, samples, xx, yy, ac), ac) : U32}}
      +e4 = {Equal.cong(Jpeg.Geom, U32, qq => Bool.pick(U32, wh, Laws.jpg.block.at(qq, samples, xx, yy, ac), ac), g2,
        gg,
        Equal.sym(Jpeg.Geom, gg, g2, eg)) : {Bool.pick(U32, wh, Laws.jpg.block.at(g2, samples, xx, yy, ac), ac) ==
        Bool.pick(U32, wh, Laws.jpg.block.at(gg, samples, xx, yy, ac), ac) : U32}}
      Equal.trans(U32, Laws.jpg.val(Array.get(U32, Laws.jpg.paint.all(rest, comp, fr, scan, Jpeg.decode.paint.use(gg,
        wh,
        samples, arr(tt))), kk)), Laws.jpg.val(Array.get(U32, Laws.jpg.paint.all(rest, comp, fr, scan, arr(t1)), kk)),
        Laws.jpg.point(rest, comp, fr, scan, xx, yy, Bool.pick(U32, wh, Laws.jpg.block.at(gg, samples, xx, yy, ac),
        ac)),
        e2, Equal.trans(U32, Laws.jpg.val(Array.get(U32, Laws.jpg.paint.all(rest, comp, fr, scan, arr(t1)), kk)),
        Laws.jpg.point(rest, comp, fr, scan, xx, yy, at(t1, kk)), Laws.jpg.point(rest, comp, fr, scan, xx, yy,
        Bool.pick(U32, wh, Laws.jpg.block.at(gg, samples, xx, yy, ac), ac)), ih, Equal.cong(U32, U32,
        oo => Laws.jpg.point(rest, comp, fr, scan, xx, yy, oo), at(t1, kk), Bool.pick(U32, wh, Laws.jpg.block.at(gg,
        samples, xx, yy, ac), ac), Equal.trans(U32, at(t1, kk), Bool.pick(U32, wh, Laws.jpg.block.at(g2, samples, xx,
        yy, ac), ac), Bool.pick(U32, wh, Laws.jpg.block.at(gg, samples, xx, yy, ac), ac), e3, e4))))

# jpeg_plane_at, from a tree the plane is the array of
def plane_at_of(
  +dd: Nat,
  -plane: Array<U32>,
  +h_perfect: {Laws.jpg.perfect(dd, plane) == True{} : Bool},
  +h_dd: {Nat.is_lt(dd, 32n) == True{} : Bool},
  +us: List<&2, Laws.JUnit>,
  +comp: U32,
  +ww: U32,
  +hh: U32,
  +nf: U32,
  +ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>,
  +tq: List<&2, U32>,
  +hmax: U32,
  +vmax: U32,
  +scan: Jpeg.Scan,
  +h_fit: {Nat.is_le(Nat.mul(U32.to_nat(ww), U32.to_nat(hh)), Nat.pow(2n, dd)) == True{} : Bool},
  +xx: U32,
  +yy: U32,
  +h_xx: {U32.is_lt(xx, ww) == True{} : Bool},
  +h_yy: {U32.is_lt(yy, hh) == True{} : Bool},
  oo: Of(plane)
) -> {Laws.jpg.val(Array.get(U32, Laws.jpg.paint.all(us, comp, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax},
  scan,
  plane), (yy * ww + xx : U32))) == Laws.jpg.point(us, comp, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan,
  xx, yy, Laws.jpg.val(Array.get(U32, plane, (yy * ww + xx : U32)))) : U32}:
  (+tt, ep) = oo
  +sp = {Equal.sym(Array<U32>, plane, arr(tt), ep) : {arr(tt) == plane : Array<U32>}}
  +hp = pf_of(dd, plane, tt, Equal.sym(Array<U32>, arr(tt), plane, sp), h_perfect)
  +fr = {Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax} : Jpeg.Frame}
  +kk = (yy * ww + xx : U32)
  %sp : {Laws.jpg.val(Array.get(U32, Laws.jpg.paint.all(us, comp, fr, scan, _), kk)) == Laws.jpg.point(us, comp, fr,
    scan, xx, yy, Laws.jpg.val(Array.get(U32, _, kk))) : U32}
  Equal.trans(U32, Laws.jpg.val(Array.get(U32, Laws.jpg.paint.all(us, comp, fr, scan, arr(tt)), kk)),
    Laws.jpg.point(us, comp, fr, scan, xx, yy, at(tt, kk)), Laws.jpg.point(us, comp, fr, scan, xx, yy,
    Laws.jpg.val(Array.get(U32, arr(tt), kk))), plane_at_t(us, comp, dd, tt, ww, hh, nf, ids, hs, vs, tq, hmax, vmax,
    scan, xx, yy, hp, h_dd, h_fit, h_xx, h_yy), Equal.cong(U32, U32, oo2 => Laws.jpg.point(us, comp, fr, scan, xx, yy,
    oo2), at(tt, kk), Laws.jpg.val(Array.get(U32, arr(tt), kk)), Equal.sym(U32, Laws.jpg.val(Array.get(U32, arr(tt),
    kk)), at(tt, kk), val_at(tt, kk))))

# ---- the pixels ----

# a gray sample, if any
def mgray(mm: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match mm:
    case None{}:
      None{}
    case Some{+vv}:
      Some{Jpeg.gray(vv)}

# the gray pass is pointwise: sample k of decode.grays is gray of point k
def grays_at(
  +ys: List<&2, U32>,
  +kk: Nat
) -> {List.get(&2, U32, Jpeg.decode.grays(ys), kk) == mgray(List.get(&2, U32, ys, kk)) : Maybe<&2, U32>}:
  match ys kk:
    case Nil{} _kk:
      {==}
    case _yv <> _yt 0n:
      {==}
    case _yv <> yt 1n+pp:
      grays_at(yt, pp)
