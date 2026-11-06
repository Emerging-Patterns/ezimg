# JPEG entropy coding both ways: Huffman tables, DC and AC coding, blocks and
# MCUs
import Base
import ../../main.bend as Img
import ../../src/jpeg.bend as Jpeg
import ../../src/jpeg_enc.bend as Jenc
import ../../laws/JpegRoundTripKeepsSize.bend as L1
import ../../laws/defs/PointInside.bend as D1
import ./BasicFacts.bend as M1
import ./SubtractionAndHuffmanWalk.bend as M2
import ./WordAddition.bend as M3

# a - b <= a
law sub_le:
  for aa: Nat
  for bb: Nat
  {Nat.is_le(Nat.sub(aa, bb), aa) == True{} : Bool}

# the proof of sub_le
def sub_le(aa, bb):
  match aa bb:
    case 0n 0n:
      {==}
    case 0n 1n+_pb:
      {==}
    case 1n+pa 0n:
      M1.le_refl(pa)
    case 1n+(+pa) 1n+(+pb):
      M1.le_trans(Nat.sub(pa, pb), pa, 1n+pa, sub_le(pa, pb), M2.le_succ(pa))

# a payload the length announced is read whole, then handed to the segment's reader
def pay.go(
  tt: List<&2, U32>,
  +bb: U32,
  +mark: U32,
  +acc: List<&2, U32>,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> {Jpeg.decode.walk(bb <> tt, Jpeg.St{Jpeg.Pay{mark, 1n+List.length(&2, U32, tt), acc}, frame, scan, tabs, ent, ri,
  kind, bad}) == Jpeg.decode.dispatch(mark, List.reverse.go(&2, U32, acc, bb <> tt), frame, scan, tabs, ent, ri, kind,
  bad) : Jpeg.St}:
  match tt:
    case Nil{}:
      {==}
    case +cc <> rest:
      pay.go(rest, cc, mark, bb <> acc, frame, scan, tabs, ent, ri, kind, bad)

# a body whose length the segment announced is read whole, then handed to the segment's reader
def pay.all(
  +body: List<&2, U32>,
  +mark: U32,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> {Jpeg.decode.walk(body, Jpeg.decode.step.pay0(List.length(&2, U32, body), mark, frame, scan, tabs, ent, ri, kind,
  bad)) == Jpeg.decode.dispatch(mark, body, frame, scan, tabs, ent, ri, kind, bad) : Jpeg.St}:
  match body:
    case Nil{}:
      {==}
    case +bb <> +tt:
      pay.go(tt, bb, mark, [], frame, scan, tabs, ent, ri, kind, bad)

# a length field of at least 2 that counts the body plus two hands the body to the segment's reader
def seg.read(
  lt: Bool,
  +len: U32,
  +body: List<&2, U32>,
  +mark: U32,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32,
  e_lt: {lt == False{} : Bool},
  e_len: {U32.to_nat((len - 2 : U32)) == List.length(&2, U32, body) : Nat}
) -> {Jpeg.decode.walk(body, Jpeg.decode.step.len.b(lt, mark, len, frame, scan, tabs, ent, ri, kind, bad))
  == Jpeg.decode.dispatch(mark, body, frame, scan, tabs, ent, ri, kind, bad) : Jpeg.St}:
  match lt:
    case True{}:
      Empty.absurd({Jpeg.decode.walk(body, Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, 1})
        == Jpeg.decode.dispatch(mark, body, frame, scan, tabs, ent, ri, kind, bad) : Jpeg.St}, M1.jst.true_false(e_lt))
    case False{}:
      Equal.trans(Jpeg.St,
        Jpeg.decode.walk(body, Jpeg.decode.step.pay0(U32.to_nat((len - 2 : U32)), mark, frame, scan, tabs, ent, ri,
          kind, bad)),
        Jpeg.decode.walk(body, Jpeg.decode.step.pay0(List.length(&2, U32, body), mark, frame, scan, tabs, ent, ri, kind,
          bad)),
        Jpeg.decode.dispatch(mark, body, frame, scan, tabs, ent, ri, kind, bad),
        Equal.cong(Nat, Jpeg.St, nn => Jpeg.decode.walk(body, Jpeg.decode.step.pay0(nn, mark, frame, scan, tabs, ent,
          ri, kind, bad)), U32.to_nat((len - 2 : U32)), List.length(&2, U32, body), e_len),
        pay.all(body, mark, frame, scan, tabs, ent, ri, kind, bad))

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

# ---- reading a plane out (laws/JpegPlacesComponentSamples.bend) ----

# the size walk keeps the array
def size.eq(aa: Array<U32>) -> {Array.size(U32, aa) == (aa, D1.jpg.val(Array.size(U32, aa))) :
  Array<U32> & U32}:
  match aa:
    case ALeaf{_x}:
      {==}
    case ANode{xs, ys}:
      ee = Equal.sym(Array<U32> & U32, Array.size(U32, xs), (xs, D1.jpg.val(Array.size(U32, xs))), size.eq(xs))
      %ee : {Array.size.node(U32, ys, _) == (ANode{xs, ys}, D1.jpg.val(Array.size.node(U32, ys, _))) :
        Array<U32> & U32}
      {==}

# a node of equal halves is equal
def node.eq(
  -x1: Array<U32>,
  -y1: Array<U32>,
  -xs: Array<U32>,
  -ys: Array<U32>,
  ex: {x1 == xs : Array<U32>},
  ey: {y1 == ys : Array<U32>}
) -> {ANode{x1, y1} == ANode{xs, ys} : Array<U32>}:
  sx = Equal.sym(Array<U32>, x1, xs, ex)
  sy = Equal.sym(Array<U32>, y1, ys, ey)
  %sx : {ANode{_, y1} == ANode{xs, ys} : Array<U32>}
  %sy : {ANode{xs, _} == ANode{xs, ys} : Array<U32>}
  {==}

# two copies of an array, each equal to it
def Dup(-aa: Array<U32>) -> Type:
  &b1: Array<U32> -> &b2: Array<U32> -> {b1 == aa : Array<U32>} & {b2 == aa : Array<U32>}

# copies of an array known equal to another are copies of that one
def dup.tr(-bb: Array<U32>, -aa: Array<U32>, ee: {bb == aa : Array<U32>}, dd: Dup(bb)) -> Dup(aa):
  %ee : Dup(_)
  dd

# copies of a node from copies of its halves
def dup.node(-xs: Array<U32>, -ys: Array<U32>, dx: Dup(xs), dy: Dup(ys)) -> Dup(ANode{xs, ys}):
  (x1, x2, e1, e2) = dx
  (y1, y2, f1, f2) = dy
  (ANode{x1, y1}, ANode{x2, y2}, node.eq(x1, y1, xs, ys, e1, f1), node.eq(x2, y2, xs, ys, e2, f2))

# two copies of an array, each equal to it
def dup(aa: Array<U32>) -> Dup(aa):
  match aa:
    case ALeaf{+xx}:
      (ALeaf{xx}, ALeaf{xx}, {==}, {==})
    case ANode{xs, ys}:
      dup.node(xs, ys, dup(xs), dup(ys))

# the tree walk of a read hands the array back, whichever half zz sends it to
def getgo.eq(
  aa: Array<U32>,
  +nn: U32,
  +ii: U32,
  zz: Bool
) -> {Array.get.go(U32, aa, nn, ii, zz) == (aa, D1.jpg.val(Array.get.go(U32, aa, nn, ii, zz))) : Array<U32> & U32}:
  match aa zz:
    case ALeaf{+_xx} _:
      {==}
    case ANode{xs, ys} True{}:
      +hh = U32.shr(nn)
      +zx = U32.is_lt(ii, U32.shr(hh))
      sx = Equal.sym(Array<U32> & U32, Array.get.go(U32, xs, hh, ii, zx), (xs, D1.jpg.val(Array.get.go(U32, xs, hh,
        ii, zx))), getgo.eq(xs, hh, ii, zx))
      %sx : {Array.swap.lo(U32, ys, _) == (ANode{xs, ys}, D1.jpg.val(Array.swap.lo(U32, ys, _))) : Array<U32> & U32}
      {==}
    case ANode{xs, ys} False{}:
      +hh = U32.shr(nn)
      +jj = U32.sub(ii, hh)
      +zy = U32.is_lt(jj, U32.shr(hh))
      sy = Equal.sym(Array<U32> & U32, Array.get.go(U32, ys, hh, jj, zy), (ys, D1.jpg.val(Array.get.go(U32, ys, hh,
        jj, zy))), getgo.eq(ys, hh, jj, zy))
      %sy : {Array.swap.hi(U32, xs, _) == (ANode{xs, ys}, D1.jpg.val(Array.swap.hi(U32, xs, _))) : Array<U32> & U32}
      {==}

# the tree walk of a read of bb, at the size read from cc and the masked index, hands bb back
def GoAt2(-bb: Array<U32>, -cc: Array<U32>, +ii: U32) -> Type:
  {Array.get.go(U32, bb, D1.jpg.val(Array.size(U32, cc)), U32.and(ii, U32.sub(D1.jpg.val(Array.size(U32, cc)), 1)),
    U32.is_lt(U32.and(ii, U32.sub(D1.jpg.val(Array.size(U32, cc)), 1)), U32.shr(D1.jpg.val(Array.size(U32,
    cc))))) ==
    (bb, D1.jpg.val(Array.get.go(U32, bb, D1.jpg.val(Array.size(U32, cc)), U32.and(ii,
    U32.sub(D1.jpg.val(Array.size(U32, cc)), 1)), U32.is_lt(U32.and(ii, U32.sub(D1.jpg.val(Array.size(U32, cc)),
    1)), U32.shr(D1.jpg.val(Array.size(U32, cc))))))) : Array<U32> & U32}

# the tree walk of a read, at the array's own size and the masked index, hands the array back
def GoAt(-aa: Array<U32>, +ii: U32) -> Type:
  GoAt2(aa, aa, ii)

# the size walk's statement moved along an equality of arrays
def size.tr(
  -bb: Array<U32>,
  -aa: Array<U32>,
  ee: {bb == aa : Array<U32>},
  hh: {Array.size(U32, bb) == (bb, D1.jpg.val(Array.size(U32, bb))) : Array<U32> & U32}
) -> {Array.size(U32, aa) == (aa, D1.jpg.val(Array.size(U32, aa))) : Array<U32> & U32}:
  %ee : {Array.size(U32, _) == (_, D1.jpg.val(Array.size(U32, _))) : Array<U32> & U32}
  hh

# a read, once the size walk has handed the array back, hands it back too
def get.from(
  -aa: Array<U32>,
  +ii: U32,
  hs: {Array.size(U32, aa) == (aa, D1.jpg.val(Array.size(U32, aa))) : Array<U32> & U32},
  hg: GoAt(aa, ii)
) -> {Array.get(U32, aa, ii) == (aa, D1.jpg.val(Array.get(U32, aa, ii))) : Array<U32> & U32}:
  ss = Equal.sym(Array<U32> & U32, Array.size(U32, aa), (aa, D1.jpg.val(Array.size(U32, aa))), hs)
  %ss : {Array.get.at(U32, ii, _) == (aa, D1.jpg.val(Array.get.at(U32, ii, _))) : Array<U32> & U32}
  hg

# the tree walk's statement at a size read from another copy, moved along both equalities
def getgo.tr2(
  -bb: Array<U32>,
  -cc: Array<U32>,
  -aa: Array<U32>,
  +ii: U32,
  eb: {bb == aa : Array<U32>},
  ec: {cc == aa : Array<U32>},
  hh: GoAt2(bb, cc, ii)
) -> GoAt(aa, ii):
  %eb : GoAt2(_, aa, ii)
  %ec : GoAt2(bb, _, ii)
  hh

# the tree walk hands the array back, at the size read from a second copy
def getgo.at(
  -aa: Array<U32>,
  +ii: U32,
  dd: Dup(aa)
) -> GoAt(aa, ii):
  (c1, c2, e1, e2) = dd
  +nn = D1.jpg.val(Array.size(U32, c2))
  +jj = U32.and(ii, U32.sub(nn, 1))
  getgo.tr2(c1, c2, aa, ii, e1, e2, getgo.eq(c1, nn, jj, U32.is_lt(jj, U32.shr(nn))))

# a read hands the array back, from copies of it
def get.eq.d(
  -aa: Array<U32>,
  +ii: U32,
  dd: Dup(aa)
) -> {Array.get(U32, aa, ii) == (aa, D1.jpg.val(Array.get(U32, aa, ii))) : Array<U32> & U32}:
  (b1, b2, e1, e2) = dd
  get.from(aa, ii, size.tr(b1, aa, e1, size.eq(b1)), getgo.at(aa, ii, dup.tr(b2, aa, e2, dup(b2))))

# a read hands the array back
def get.eq(aa: Array<U32>, +ii: U32) -> {Array.get(U32, aa, ii) == (aa, D1.jpg.val(Array.get(U32, aa, ii))) :
  Array<U32> & U32}:
  get.eq.d(aa, ii, dup(aa))

# and with zeros on the right is zeros
def and_zero_r(nn: Nat, ww: Word(nn)) -> {Word.and(nn, ww, Word.zero(nn)) == Word.zero(nn) : Word(nn)}:
  match nn:
    case 0n:
      match ww:
        case WNil{}:
          {==}
    case 1n+pp:
      match ww:
        case WCon{bb, tt}:
          match bb:
            case True{}:
              Equal.cong(Word(pp), Word.Con<pp>, xx => WCon{False{}, xx}, Word.and(pp, tt, Word.zero(pp)),
                Word.zero(pp), and_zero_r(pp, tt))
            case False{}:
              Equal.cong(Word(pp), Word.Con<pp>, xx => WCon{False{}, xx}, Word.and(pp, tt, Word.zero(pp)),
                Word.zero(pp), and_zero_r(pp, tt))

# and with 1, by the low bit
def and_one.b(
  w0: Bool,
  +wt: Word(31n)
) -> {U32{WCon{Bool.and(w0, True{}), Word.and(31n, wt, Word.zero(31n))}} == U32{WCon{w0, Word.zero(31n)}} : U32}:
  match w0:
    case True{}:
      Equal.cong(Word(31n), U32, zz => U32{WCon{True{}, zz}}, Word.and(31n, wt, Word.zero(31n)), Word.zero(31n),
        and_zero_r(31n, wt))
    case False{}:
      Equal.cong(Word(31n), U32, zz => U32{WCon{False{}, zz}}, Word.and(31n, wt, Word.zero(31n)), Word.zero(31n),
        and_zero_r(31n, wt))

# and with 1 is the low bit
def and_one(xx: U32) -> {U32.and(xx, 1) == L1.jpg.ubit(L1.jpg.bit0(xx)) : U32}:
  match xx:
    case U32{ww}:
      match ww:
        case WCon{w0, wt}:
          and_one.b(w0, wt)

# the encoder's bit loop feeds the code's bits
def bits_go(
  kk: Nat,
  pp: Jenc.Put,
  +code: U32
) -> {Jenc.encode.bits.go(kk, pp, code) == L1.jpg.feed(L1.jpg.cb(kk, code), pp) : Jenc.Put}:
  match kk:
    case 0n:
      {==}
    case 1n+ +qq:
      +bt = U32.shrn(code, qq)
      Equal.trans(Jenc.Put, Jenc.encode.bits.go(qq, Jenc.encode.bit(pp, U32.and(bt, 1)), code),
        Jenc.encode.bits.go(qq, Jenc.encode.bit(pp, L1.jpg.ubit(L1.jpg.bit0(bt))), code),
          L1.jpg.feed(L1.jpg.cb(1n+qq, code), pp),
        Equal.cong(U32, Jenc.Put, xx => Jenc.encode.bits.go(qq, Jenc.encode.bit(pp, xx), code), U32.and(bt, 1),
        L1.jpg.ubit(L1.jpg.bit0(bt)), and_one(bt)), bits_go(qq, Jenc.encode.bit(pp,
          L1.jpg.ubit(L1.jpg.bit0(bt))), code))

# feeding two lists is feeding their join
def feed_app(
  xs: List<&2, Bool>,
  +ys: List<&2, Bool>,
  pp: Jenc.Put
) -> {L1.jpg.feed(List.append(&2, Bool, xs, ys), pp) == L1.jpg.feed(ys, L1.jpg.feed(xs, pp)) : Jenc.Put}:
  match xs:
    case Nil{}:
      {==}
    case bb <> rest:
      feed_app(rest, ys, Jenc.encode.bit(pp, L1.jpg.ubit(bb)))

# joining is associative
def huf.app_assoc(
  xs: List<&2, Bool>,
  +ys: List<&2, Bool>,
  +zs: List<&2, Bool>
) -> {List.append(&2, Bool, List.append(&2, Bool, xs, ys), zs) == List.append(&2, Bool, xs, List.append(&2, Bool, ys,
  zs)) : List<&2, Bool>}:
  match xs:
    case Nil{}:
      {==}
    case +hh <> tt:
      Equal.cong(List<&2, Bool>, List<&2, Bool>, ws => hh <> ws, List.append(&2, Bool, List.append(&2, Bool, tt, ys),
        zs), List.append(&2, Bool, tt, List.append(&2, Bool, ys, zs)), huf.app_assoc(tt, ys, zs))

# the left of a true and
def and_l(aa: Bool, -bb: Bool, hh: {Bool.and(aa, bb) == True{} : Bool}) -> {aa == True{} : Bool}:
  match aa:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, M1.huf.false_true(hh))

# the right of a true and
def and_r(aa: Bool, -bb: Bool, hh: {Bool.and(aa, bb) == True{} : Bool}) -> {bb == True{} : Bool}:
  match aa:
    case True{}:
      hh
    case False{}:
      Empty.absurd({bb == True{} : Bool}, M1.huf.false_true(hh))

# a list joined with nothing is the list
def huf.app_nil(xs: List<&2, Bool>) -> {List.append(&2, Bool, xs, []) == xs : List<&2, Bool>}:
  match xs:
    case Nil{}:
      {==}
    case +hh <> tt:
      Equal.cong(List<&2, Bool>, List<&2, Bool>, ws => hh <> ws, List.append(&2, Bool, tt, []), tt, huf.app_nil(tt))

# the dc book the encoder builds, written out
def dcbook.lit() -> Array<U32>:
  ANode{ANode{ANode{ANode{ANode{ANode{ANode{ANode{ALeaf{131072}, ALeaf{196610}}, ANode{ALeaf{196611},
    ALeaf{196612}}}, ANode{ANode{ALeaf{196613}, ALeaf{196614}}, ANode{ALeaf{262158}, ALeaf{327710}}}},
    ANode{ANode{ANode{ALeaf{393278}, ALeaf{458878}}, ANode{ALeaf{524542}, ALeaf{590334}}}, ANode{ANode{ALeaf{0},
    ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}},
    ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}, ANode{ANode{ANode{ALeaf{0}, ALeaf{0}},
    ANode{ALeaf{0}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}},
    ANode{ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}},
    ANode{ALeaf{0}, ALeaf{0}}}}, ANode{ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}},
    ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{0}},
    ANode{ALeaf{0}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}},
    ANode{ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}},
    ANode{ALeaf{0}, ALeaf{0}}}}}}}, ANode{ANode{ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0},
    ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}, ANode{ANode{ANode{ALeaf{0}, ALeaf{0}},
    ANode{ALeaf{0}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}},
    ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}},
    ANode{ALeaf{0}, ALeaf{0}}}}, ANode{ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}},
    ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}}, ANode{ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{0}},
    ANode{ALeaf{0}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}},
    ANode{ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}},
    ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}},
    ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}, ANode{ANode{ANode{ALeaf{0}, ALeaf{0}},
    ANode{ALeaf{0}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}}}},
    ANode{ANode{ANode{ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}, ANode{ANode{ALeaf{0},
    ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}, ANode{ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}},
    ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{0}},
    ANode{ALeaf{0}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}},
    ANode{ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}},
    ANode{ALeaf{0}, ALeaf{0}}}}}}, ANode{ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}},
    ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}, ANode{ANode{ANode{ALeaf{0}, ALeaf{0}},
    ANode{ALeaf{0}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}},
    ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}},
    ANode{ALeaf{0}, ALeaf{0}}}}, ANode{ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}},
    ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}}}, ANode{ANode{ANode{ANode{ANode{ANode{ALeaf{0},
    ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}},
    ANode{ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}},
    ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}},
    ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}, ANode{ANode{ANode{ALeaf{0}, ALeaf{0}},
    ANode{ALeaf{0}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}},
    ANode{ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}},
    ANode{ALeaf{0}, ALeaf{0}}}}, ANode{ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}},
    ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{0}},
    ANode{ALeaf{0}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}},
    ANode{ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}},
    ANode{ALeaf{0}, ALeaf{0}}}}}}}}}

# a symbol's code in the dc book
def code.dc(+sy: U32) -> List<&2, Bool>:
  L1.jpg.cbw(D1.jpg.val(Array.get(U32, dcbook.lit(), sy)))

# the ac book the encoder builds, written out
def acbook.lit() -> Array<U32>:
  ANode{ANode{ANode{ANode{ANode{ANode{ANode{ANode{ALeaf{262154}, ALeaf{131072}}, ANode{ALeaf{131073},
    ALeaf{196612}}}, ANode{ANode{ALeaf{262155}, ALeaf{327706}}, ANode{ALeaf{458872}, ALeaf{524536}}}},
    ANode{ANode{ANode{ALeaf{656374}, ALeaf{1113986}}, ANode{ALeaf{1113987}, ALeaf{0}}}, ANode{ANode{ALeaf{0},
    ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{262156}}, ANode{ALeaf{327707},
    ALeaf{458873}}}, ANode{ANode{ALeaf{590326}, ALeaf{722934}}, ANode{ALeaf{1113988}, ALeaf{1113989}}}},
    ANode{ANode{ANode{ALeaf{1113990}, ALeaf{1113991}}, ANode{ALeaf{1113992}, ALeaf{0}}}, ANode{ANode{ALeaf{0},
    ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}}, ANode{ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{327708}},
    ANode{ALeaf{524537}, ALeaf{656375}}}, ANode{ANode{ALeaf{790516}, ALeaf{1113993}}, ANode{ALeaf{1113994},
    ALeaf{1113995}}}}, ANode{ANode{ANode{ALeaf{1113996}, ALeaf{1113997}}, ANode{ALeaf{1113998}, ALeaf{0}}},
    ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{393274}},
    ANode{ALeaf{590327}, ALeaf{790517}}}, ANode{ANode{ALeaf{1113999}, ALeaf{1114000}}, ANode{ALeaf{1114001},
    ALeaf{1114002}}}}, ANode{ANode{ANode{ALeaf{1114003}, ALeaf{1114004}}, ANode{ALeaf{1114005}, ALeaf{0}}},
    ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}}}, ANode{ANode{ANode{ANode{ANode{ANode{ALeaf{0},
    ALeaf{393275}}, ANode{ALeaf{656376}, ALeaf{1114006}}}, ANode{ANode{ALeaf{1114007}, ALeaf{1114008}},
    ANode{ALeaf{1114009}, ALeaf{1114010}}}}, ANode{ANode{ANode{ALeaf{1114011}, ALeaf{1114012}}, ANode{ALeaf{1114013},
    ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{0},
    ALeaf{458874}}, ANode{ALeaf{722935}, ALeaf{1114014}}}, ANode{ANode{ALeaf{1114015}, ALeaf{1114016}},
    ANode{ALeaf{1114017}, ALeaf{1114018}}}}, ANode{ANode{ANode{ALeaf{1114019}, ALeaf{1114020}}, ANode{ALeaf{1114021},
    ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}},
    ANode{ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{458875}}, ANode{ALeaf{790518}, ALeaf{1114022}}},
    ANode{ANode{ALeaf{1114023}, ALeaf{1114024}}, ANode{ALeaf{1114025}, ALeaf{1114026}}}},
    ANode{ANode{ANode{ALeaf{1114027}, ALeaf{1114028}}, ANode{ALeaf{1114029}, ALeaf{0}}}, ANode{ANode{ALeaf{0},
    ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{524538}}, ANode{ALeaf{790519},
    ALeaf{1114030}}}, ANode{ANode{ALeaf{1114031}, ALeaf{1114032}}, ANode{ALeaf{1114033}, ALeaf{1114034}}}},
    ANode{ANode{ANode{ALeaf{1114035}, ALeaf{1114036}}, ANode{ALeaf{1114037}, ALeaf{0}}}, ANode{ANode{ALeaf{0},
    ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}}}}, ANode{ANode{ANode{ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{590328}},
    ANode{ALeaf{1015744}, ALeaf{1114038}}}, ANode{ANode{ALeaf{1114039}, ALeaf{1114040}}, ANode{ALeaf{1114041},
    ALeaf{1114042}}}}, ANode{ANode{ANode{ALeaf{1114043}, ALeaf{1114044}}, ANode{ALeaf{1114045}, ALeaf{0}}},
    ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{590329}},
    ANode{ALeaf{1114046}, ALeaf{1114047}}}, ANode{ANode{ALeaf{1114048}, ALeaf{1114049}}, ANode{ALeaf{1114050},
    ALeaf{1114051}}}}, ANode{ANode{ANode{ALeaf{1114052}, ALeaf{1114053}}, ANode{ALeaf{1114054}, ALeaf{0}}},
    ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}}, ANode{ANode{ANode{ANode{ANode{ALeaf{0},
    ALeaf{590330}}, ANode{ALeaf{1114055}, ALeaf{1114056}}}, ANode{ANode{ALeaf{1114057}, ALeaf{1114058}},
    ANode{ALeaf{1114059}, ALeaf{1114060}}}}, ANode{ANode{ANode{ALeaf{1114061}, ALeaf{1114062}}, ANode{ALeaf{1114063},
    ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{0},
    ALeaf{656377}}, ANode{ALeaf{1114064}, ALeaf{1114065}}}, ANode{ANode{ALeaf{1114066}, ALeaf{1114067}},
    ANode{ALeaf{1114068}, ALeaf{1114069}}}}, ANode{ANode{ANode{ALeaf{1114070}, ALeaf{1114071}}, ANode{ALeaf{1114072},
    ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}}},
    ANode{ANode{ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{656378}}, ANode{ALeaf{1114073}, ALeaf{1114074}}},
    ANode{ANode{ALeaf{1114075}, ALeaf{1114076}}, ANode{ALeaf{1114077}, ALeaf{1114078}}}},
    ANode{ANode{ANode{ALeaf{1114079}, ALeaf{1114080}}, ANode{ALeaf{1114081}, ALeaf{0}}}, ANode{ANode{ALeaf{0},
    ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{722936}}, ANode{ALeaf{1114082},
    ALeaf{1114083}}}, ANode{ANode{ALeaf{1114084}, ALeaf{1114085}}, ANode{ALeaf{1114086}, ALeaf{1114087}}}},
    ANode{ANode{ANode{ALeaf{1114088}, ALeaf{1114089}}, ANode{ALeaf{1114090}, ALeaf{0}}}, ANode{ANode{ALeaf{0},
    ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}}, ANode{ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{1114091}},
    ANode{ALeaf{1114092}, ALeaf{1114093}}}, ANode{ANode{ALeaf{1114094}, ALeaf{1114095}}, ANode{ALeaf{1114096},
    ALeaf{1114097}}}}, ANode{ANode{ANode{ALeaf{1114098}, ALeaf{1114099}}, ANode{ALeaf{1114100}, ALeaf{0}}},
    ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{722937},
    ALeaf{1114101}}, ANode{ALeaf{1114102}, ALeaf{1114103}}}, ANode{ANode{ALeaf{1114104}, ALeaf{1114105}},
    ANode{ALeaf{1114106}, ALeaf{1114107}}}}, ANode{ANode{ANode{ALeaf{1114108}, ALeaf{1114109}}, ANode{ALeaf{1114110},
    ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}}}}}

# a symbol's code in the ac book
def code.ac(+sy: U32) -> List<&2, Bool>:
  L1.jpg.cbw(D1.jpg.val(Array.get(U32, acbook.lit(), sy)))

# the bits of AC tokens: each symbol's code in the AC book, then its magnitude bits
def acbits(ts: List<&2, L1.JTok>) -> List<&2, Bool>:
  match ts:
    case Nil{}:
      []
    case L1.JTok{+sym, ex} <> rest:
      List.append(&2, Bool, code.ac(sym), List.append(&2, Bool, ex, acbits(rest)))

# a block's bits: the DC symbol's code in the DC book, its magnitude bits, and the AC tokens' bits
def blkbits(bt: L1.JBlkTok) -> List<&2, Bool>:
  match bt:
    case L1.JBlkTok{+dcs, dcx, acs}:
      List.append(&2, Bool, code.dc(dcs), List.append(&2, Bool, dcx, acbits(acs)))

# the encoder's AC book, written out
def acbk() -> Array<U32>:
  acbook.lit()

# the encoder's DC book, written out
def dcbk() -> Array<U32>:
  dcbook.lit()

# a symbol's code from the AC book: the book back, the code's bits fed to the writer
def emitp.ac(
  +sy: U32,
  +pp: Jenc.Put
) -> {Jenc.encode.emit(Jenc.encode.sym(acbk(), sy), pp) == (acbk(), L1.jpg.feed( code.ac(sy),
  pp)) : Array<U32> & Jenc.Put}:
  +vv = D1.jpg.val(Array.get(U32, acbk(), sy))
  Equal.trans(Array<U32> & Jenc.Put, Jenc.encode.emit(Jenc.encode.coded(Array.get(U32, acbk(), sy)), pp),
    Jenc.encode.emit(Jenc.encode.coded((acbk(), vv)), pp), (acbk(), L1.jpg.feed(code.ac(sy), pp)),
    Equal.cong(Array<U32> & U32, Array<U32> & Jenc.Put, gg => Jenc.encode.emit(Jenc.encode.coded(gg), pp),
    Array.get(U32, acbk(), sy), (acbk(), vv), get.eq(acbk(), sy)), Equal.cong(Jenc.Put, Array<U32> & Jenc.Put,
    qq => (acbk(), qq), Jenc.encode.bits.go(U32.to_nat(U32.shrn(vv, 16n)), pp, U32.and(vv, 65535)),
    L1.jpg.feed(code.ac(sy), pp), bits_go(U32.to_nat(U32.shrn(vv, 16n)), pp, U32.and(vv, 65535))))

# the AC tokens' bits, joined
def acbits_app(
  xs: List<&2, L1.JTok>,
  +ys: List<&2, L1.JTok>
) -> {acbits(List.append(&2, L1.JTok, xs, ys)) == List.append(&2, Bool, acbits(xs),
  acbits(ys)) : List<&2, Bool>}:
  match xs:
    case Nil{}:
      {==}
    case L1.JTok{+sym, +ex} <> +rest:
      Equal.trans(List<&2, Bool>, List.append(&2, Bool, code.ac(sym), List.append(&2, Bool, ex,
        acbits(List.append(&2, L1.JTok, rest, ys)))), List.append(&2, Bool, code.ac(sym), List.append(&2,
          Bool, ex,
        List.append(&2, Bool, acbits(rest), acbits(ys)))), List.append(&2, Bool, List.append(&2, Bool,
        code.ac(sym), List.append(&2, Bool, ex, acbits(rest))), acbits(ys)), Equal.cong(List<&2, Bool>,
        List<&2, Bool>, zs => List.append(&2, Bool, code.ac(sym), List.append(&2, Bool, ex, zs)),
        acbits(List.append(&2, L1.JTok, rest, ys)), List.append(&2, Bool, acbits(rest), acbits(ys)),
        acbits_app(rest, ys)), Equal.sym(List<&2, Bool>, List.append(&2, Bool, List.append(&2, Bool, code.ac(sym),
        List.append(&2, Bool, ex, acbits(rest))), acbits(ys)), List.append(&2, Bool, code.ac(sym),
        List.append(&2, Bool, ex, List.append(&2, Bool, acbits(rest), acbits(ys)))), Equal.trans(List<&2, Bool>,
        List.append(&2, Bool, List.append(&2, Bool, code.ac(sym), List.append(&2, Bool, ex, acbits(rest))),
        acbits(ys)), List.append(&2, Bool, code.ac(sym), List.append(&2, Bool, List.append(&2, Bool, ex,
        acbits(rest)), acbits(ys))), List.append(&2, Bool, code.ac(sym), List.append(&2, Bool, ex,
        List.append(&2, Bool, acbits(rest), acbits(ys)))), huf.app_assoc(code.ac(sym), List.append(&2, Bool,
        ex, acbits(rest)), acbits(ys)), Equal.cong(List<&2, Bool>, List<&2, Bool>, zs => List.append(&2, Bool,
        code.ac(sym), zs), List.append(&2, Bool, List.append(&2, Bool, ex, acbits(rest)), acbits(ys)),
        List.append(&2, Bool, ex, List.append(&2, Bool, acbits(rest), acbits(ys))), huf.app_assoc(ex,
        acbits(rest), acbits(ys))))))

# j ZRL tokens
def zrltoks(jj: Nat) -> List<&2, L1.JTok>:
  match jj:
    case 0n:
      []
    case 1n+kk:
      L1.JTok{240, []} <> zrltoks(kk)

# the encoder's run of ZRL codes is the ZRL tokens' bits fed to the writer
def zrls_eq(
  jj: Nat,
  +pp: Jenc.Put
) -> {Jenc.encode.zrls(jj, (acbk(), pp)) == (acbk(), L1.jpg.feed(acbits(zrltoks(jj)),
  pp)) : Array<U32> & Jenc.Put}:
  match jj:
    case 0n:
      {==}
    case 1n+ +kk:
      +cz = code.ac(240)
      Equal.trans(Array<U32> & Jenc.Put, Jenc.encode.zrls(kk, Jenc.encode.emit(Jenc.encode.sym(acbk(), 240), pp)),
        Jenc.encode.zrls(kk, (acbk(), L1.jpg.feed(cz, pp))), (acbk(), L1.jpg.feed(acbits(zrltoks(1n+kk)), pp)),
        Equal.cong(Array<U32> & Jenc.Put, Array<U32> & Jenc.Put, st => Jenc.encode.zrls(kk, st),
        Jenc.encode.emit(Jenc.encode.sym(acbk(), 240), pp), (acbk(), L1.jpg.feed(cz, pp)), emitp.ac(240, pp)),
        Equal.trans(Array<U32> & Jenc.Put, Jenc.encode.zrls(kk, (acbk(), L1.jpg.feed(cz, pp))), (acbk(),
          L1.jpg.feed(
        acbits(zrltoks(kk)), L1.jpg.feed(cz, pp))), (acbk(), L1.jpg.feed(acbits(zrltoks(1n+kk)), pp)),
          zrls_eq(kk,
        L1.jpg.feed(cz, pp)), Equal.cong(Jenc.Put, Array<U32> & Jenc.Put, qq => (acbk(), qq),
          L1.jpg.feed(acbits(
        zrltoks(kk)), L1.jpg.feed(cz, pp)), L1.jpg.feed(acbits(zrltoks(1n+kk)), pp), Equal.sym(Jenc.Put,
        L1.jpg.feed(List.append(&2, Bool, cz, acbits(zrltoks(kk))), pp), L1.jpg.feed(acbits(zrltoks(kk)),
          L1.jpg.feed(cz,
        pp)), feed_app(cz, acbits(zrltoks(kk)), pp)))))

# the magnitude bits of a size and value: none for size 0
def mz(zero: Bool, +cat: U32, +vv: U32) -> List<&2, Bool>:
  match zero:
    case True{}:
      +_u = (cat + vv : U32)
      []
    case False{}:
      L1.jpg.cb(U32.to_nat(cat), Jenc.encode.mag(cat, vv))

# the encoder's magnitude bits are mz's, fed to the writer
def magp_eq(
  zero: Bool,
  +pp: Jenc.Put,
  +cat: U32,
  +vv: U32
) -> {Jenc.encode.magp.z(zero, pp, cat, vv) == L1.jpg.feed(mz(zero, cat, vv), pp) : Jenc.Put}:
  match zero:
    case True{}:
      {==}
    case False{}:
      bits_go(U32.to_nat(cat), pp, Jenc.encode.mag(cat, vv))

# bits fed in three runs are their join fed at once
def feed3(
  +zz: List<&2, Bool>,
  +cc: List<&2, Bool>,
  +mm: List<&2, Bool>,
  +pp: Jenc.Put
) -> {L1.jpg.feed(mm, L1.jpg.feed(cc, L1.jpg.feed(zz, pp))) == L1.jpg.feed(List.append(&2, Bool, zz,
  List.append(&2, Bool, cc, List.append(&2, Bool, mm, []))), pp) : Jenc.Put}:
  Equal.sym(Jenc.Put, L1.jpg.feed(List.append(&2, Bool, zz, List.append(&2, Bool, cc, List.append(&2, Bool, mm,
    []))), pp),
    L1.jpg.feed(mm, L1.jpg.feed(cc, L1.jpg.feed(zz, pp))), Equal.trans(Jenc.Put, L1.jpg.feed(List.append(&2,
      Bool, zz,
    List.append(&2, Bool, cc, List.append(&2, Bool, mm, []))), pp), L1.jpg.feed(List.append(&2, Bool, cc,
      List.append(&2,
    Bool, mm, [])), L1.jpg.feed(zz, pp)), L1.jpg.feed(mm, L1.jpg.feed(cc, L1.jpg.feed(zz, pp))),
      feed_app(zz, List.append(&2, Bool,
    cc, List.append(&2, Bool, mm, [])), pp), Equal.trans(Jenc.Put, L1.jpg.feed(List.append(&2, Bool, cc,
      List.append(&2,
    Bool, mm, [])), L1.jpg.feed(zz, pp)), L1.jpg.feed(List.append(&2, Bool, mm, []), L1.jpg.feed(cc,
      L1.jpg.feed(zz, pp))),
    L1.jpg.feed(mm, L1.jpg.feed(cc, L1.jpg.feed(zz, pp))), feed_app(cc, List.append(&2, Bool, mm, []),
      L1.jpg.feed(zz, pp)),
    Equal.cong(List<&2, Bool>, Jenc.Put, xs => L1.jpg.feed(xs, L1.jpg.feed(cc, L1.jpg.feed(zz, pp))),
      List.append(&2, Bool, mm, []),
    mm, huf.app_nil(mm)))))

# the AC tokens one coefficient cc writes after a run of zeros: ZRL tokens for each 16 zeros, then its run and
# size symbol with its magnitude bits
def stoks(+zj: Nat, +sym: U32, +cat: U32, +clip: U32) -> List<&2, L1.JTok>:
  List.append(&2, L1.JTok, zrltoks(zj), [L1.JTok{sym, mz(U32.is_eq(cat, 0), cat, clip)}])

# the encoder's step for a coefficient, once its clipped value, size and symbol are named
def hit_eq(
  +zj: Nat,
  +sym: U32,
  +cat: U32,
  +clip: U32,
  +pp: Jenc.Put
) -> {Jenc.encode.ac.hit(Jenc.encode.zrls(zj, (acbk(), pp)), sym, cat, clip) == (acbk(),
  L1.jpg.feed(acbits(stoks(zj, sym, cat, clip)), pp)) : Array<U32> & Jenc.Put}:
  +zt = zrltoks(zj)
  +zb = acbits(zt)
  +cb = code.ac(sym)
  +mb = mz(U32.is_eq(cat, 0), cat, clip)
  +tk = {L1.JTok{sym, mb} : L1.JTok}
  Equal.trans(Array<U32> & Jenc.Put, Jenc.encode.ac.hit(Jenc.encode.zrls(zj, (acbk(), pp)), sym, cat, clip),
    Jenc.encode.ac.hit((acbk(), L1.jpg.feed(zb, pp)), sym, cat, clip), (acbk(), L1.jpg.feed(acbits(stoks(zj,
      sym, cat, clip)), pp)),
    Equal.cong(Array<U32> & Jenc.Put, Array<U32> & Jenc.Put, st => Jenc.encode.ac.hit(st, sym, cat, clip),
    Jenc.encode.zrls(zj, (acbk(), pp)), (acbk(), L1.jpg.feed(zb, pp)), zrls_eq(zj, pp)),
      Equal.trans(Array<U32> & Jenc.Put,
    Jenc.encode.ac.mag(Jenc.encode.emit(Jenc.encode.sym(acbk(), sym), L1.jpg.feed(zb, pp)), cat, clip),
    Jenc.encode.ac.mag((acbk(), L1.jpg.feed(cb, L1.jpg.feed(zb, pp))), cat, clip), (acbk(),
      L1.jpg.feed(acbits(stoks(zj, sym, cat, clip)), pp)), Equal.cong(Array<U32> & Jenc.Put,
      Array<U32> & Jenc.Put, st => Jenc.encode.ac.mag(st, cat, clip),
    Jenc.encode.emit(Jenc.encode.sym(acbk(), sym), L1.jpg.feed(zb, pp)), (acbk(), L1.jpg.feed(cb,
      L1.jpg.feed(zb, pp))),
    emitp.ac(sym, L1.jpg.feed(zb, pp))), Equal.cong(Jenc.Put, Array<U32> & Jenc.Put, qq => (acbk(), qq),
    Jenc.encode.magp.z(U32.is_eq(cat, 0), L1.jpg.feed(cb, L1.jpg.feed(zb, pp)), cat, clip),
      L1.jpg.feed(acbits(stoks(zj, sym, cat, clip)), pp), Equal.trans(Jenc.Put,
      Jenc.encode.magp.z(U32.is_eq(cat, 0), L1.jpg.feed(cb, L1.jpg.feed(zb, pp)), cat, clip),
    L1.jpg.feed(mb, L1.jpg.feed(cb, L1.jpg.feed(zb, pp))), L1.jpg.feed(acbits(stoks(zj, sym, cat, clip)),
      pp), magp_eq(U32.is_eq(cat, 0),
    L1.jpg.feed(cb, L1.jpg.feed(zb, pp)), cat, clip), Equal.trans(Jenc.Put, L1.jpg.feed(mb, L1.jpg.feed(cb,
      L1.jpg.feed(zb, pp))),
    L1.jpg.feed(List.append(&2, Bool, zb, List.append(&2, Bool, cb, List.append(&2, Bool, mb, []))), pp),
    L1.jpg.feed(acbits(stoks(zj, sym, cat, clip)), pp), feed3(zb, cb, mb, pp), Equal.cong(List<&2, Bool>,
      Jenc.Put, xs =>
    L1.jpg.feed(xs, pp), List.append(&2, Bool, zb, acbits([tk])), acbits(List.append(&2, L1.JTok, zt,
      [tk])),
    Equal.sym(List<&2, Bool>, acbits(List.append(&2, L1.JTok, zt, [tk])), List.append(&2, Bool, zb,
    acbits([tk])), acbits_app(zt, [tk]))))))))

# the encoder's step for a coefficient is its tokens' bits fed to the writer
def step_eq(
  +cc: U32,
  +run: U32,
  +pp: Jenc.Put
) -> {Jenc.encode.ac.step(cc, run, (acbk(), pp)) == (acbk(), L1.jpg.feed(acbits(stoks(U32.to_nat(U32.shrn(run,
  4n)), U32.or(Jenc.encode.cat(Jenc.encode.clip(cc, 1023)), U32.shln(U32.and(15, run), 4n)),
  Jenc.encode.cat(Jenc.encode.clip(cc, 1023)), Jenc.encode.clip(cc, 1023))), pp)) : Array<U32> & Jenc.Put}:
  hit_eq(U32.to_nat(U32.shrn(run, 4n)), U32.or(Jenc.encode.cat(Jenc.encode.clip(cc, 1023)), U32.shln(U32.and(15, run),
    4n)), Jenc.encode.cat(Jenc.encode.clip(cc, 1023)), Jenc.encode.clip(cc, 1023), pp)

# a word compare that sets the low bit against a clear one is never equal
def fin_ne(tt: Cmp) -> {Cmp.is_eq(Word.cmp.fin(True{}, False{}, tt)) == False{} : Bool}:
  match tt:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# a word compare over two clear low bits is the compare above them
def jenc.fin_ff(tt: Cmp) -> {Cmp.is_eq(Word.cmp.fin(False{}, False{}, tt)) == Cmp.is_eq(tt) : Bool}:
  match tt:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# one more than a word's complement is zero exactly when the word is zero
def neg_go(
  nn: Nat,
  ww: Word(nn)
) -> {Cmp.is_eq(Word.cmp(nn, Word.adc(nn, Word.not(nn, ww), Word.zero(nn), False{}, True{}),
  Word.zero(nn))) == Cmp.is_eq(Word.cmp(nn, ww, Word.zero(nn))) : Bool}:
  match nn:
    case 0n:
      match ww:
        case WNil{}:
          {==}
    case 1n+ +pp:
      match ww:
        case WCon{bb, +tt}:
          match bb:
            case True{}:
              Equal.trans(Bool, Cmp.is_eq(Word.cmp.fin(True{}, False{}, Word.cmp(pp, Word.adc(pp, Word.not(pp, tt),
                Word.zero(pp), False{}, False{}), Word.zero(pp)))), False{}, Cmp.is_eq(Word.cmp.fin(True{}, False{},
                Word.cmp(pp, tt, Word.zero(pp)))), fin_ne(Word.cmp(pp, Word.adc(pp, Word.not(pp, tt), Word.zero(pp),
                False{}, False{}), Word.zero(pp))), Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(True{}, False{}, Word.cmp(pp,
                tt, Word.zero(pp)))), False{}, fin_ne(Word.cmp(pp, tt, Word.zero(pp)))))
            case False{}:
              Equal.trans(Bool, Cmp.is_eq(Word.cmp.fin(False{}, False{}, Word.cmp(pp, Word.adc(pp, Word.not(pp, tt),
                Word.zero(pp), False{}, True{}), Word.zero(pp)))), Cmp.is_eq(Word.cmp(pp, Word.adc(pp, Word.not(pp,
                tt), Word.zero(pp), False{}, True{}), Word.zero(pp))), Cmp.is_eq(Word.cmp.fin(False{}, False{},
                Word.cmp(pp, tt, Word.zero(pp)))), jenc.fin_ff(Word.cmp(pp, Word.adc(pp, Word.not(pp, tt),
                    Word.zero(pp),
                False{}, True{}), Word.zero(pp))), Equal.trans(Bool, Cmp.is_eq(Word.cmp(pp, Word.adc(pp, Word.not(pp,
                tt), Word.zero(pp), False{}, True{}), Word.zero(pp))), Cmp.is_eq(Word.cmp(pp, tt, Word.zero(pp))),
                Cmp.is_eq(Word.cmp.fin(False{}, False{}, Word.cmp(pp, tt, Word.zero(pp)))), neg_go(pp, tt),
                Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(False{}, False{}, Word.cmp(pp, tt, Word.zero(pp)))),
                Cmp.is_eq(Word.cmp(pp, tt, Word.zero(pp))), jenc.fin_ff(Word.cmp(pp, tt, Word.zero(pp))))))

# the two's complement of a U32 is zero exactly when it is
def neg_nz(vv: U32) -> {U32.is_eq(Jpeg.decode.neg32(vv), 0) == U32.is_eq(vv, 0) : Bool}:
  match vv:
    case U32{ww}:
      match ww:
        case WCon{bb, +tt}:
          match bb:
            case True{}:
              Equal.trans(Bool, Cmp.is_eq(Word.cmp.fin(True{}, False{}, Word.cmp(31n, Word.adc(31n, Word.not(31n, tt),
                Word.zero(31n), False{}, False{}), Word.zero(31n)))), False{}, Cmp.is_eq(Word.cmp.fin(True{}, False{},
                Word.cmp(31n, tt, Word.zero(31n)))), fin_ne(Word.cmp(31n, Word.adc(31n, Word.not(31n, tt),
                Word.zero(31n), False{}, False{}), Word.zero(31n))), Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(True{},
                False{}, Word.cmp(31n, tt, Word.zero(31n)))), False{}, fin_ne(Word.cmp(31n, tt, Word.zero(31n)))))
            case False{}:
              Equal.trans(Bool, Cmp.is_eq(Word.cmp.fin(False{}, False{}, Word.cmp(31n, Word.adc(31n, Word.not(31n,
                tt), Word.zero(31n), False{}, True{}), Word.zero(31n)))), Cmp.is_eq(Word.cmp(31n, Word.adc(31n,
                Word.not(31n, tt), Word.zero(31n), False{}, True{}), Word.zero(31n))), Cmp.is_eq(Word.cmp.fin(False{},
                False{}, Word.cmp(31n, tt, Word.zero(31n)))), jenc.fin_ff(Word.cmp(31n, Word.adc(31n, Word.not(31n, tt),
                Word.zero(31n), False{}, True{}), Word.zero(31n))), Equal.trans(Bool, Cmp.is_eq(Word.cmp(31n,
                Word.adc(31n, Word.not(31n, tt), Word.zero(31n), False{}, True{}), Word.zero(31n))),
                Cmp.is_eq(Word.cmp(31n, tt, Word.zero(31n))), Cmp.is_eq(Word.cmp.fin(False{}, False{}, Word.cmp(31n,
                tt, Word.zero(31n)))), neg_go(31n, tt), Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(False{}, False{},
                Word.cmp(31n, tt, Word.zero(31n)))), Cmp.is_eq(Word.cmp(31n, tt, Word.zero(31n))),
                jenc.fin_ff(Word.cmp(31n, tt, Word.zero(31n))))))

# True is never False
def jenc.true_false(ee: {True{} == False{} : Bool}) -> Empty:
  M1.huf.false_true(Equal.sym(Bool, True{}, False{}, ee))

# the top bit of a word of nn + 1 bits
def wtop(nn: Nat, ww: Word(1n+nn)) -> Bool:
  match nn:
    case 0n:
      match ww:
        case WCon{bb, _t}:
          bb
    case 1n+pp:
      match ww:
        case WCon{_b, tt}:
          wtop(pp, tt)

# the word of a U32
def uw(vv: U32) -> Word(32n):
  match vv:
    case U32{ww}:
      ww

# the sign of a U32 is its top bit
def sign_top(vv: U32) -> {Jpeg.decode.sign(vv) == U32{WCon{wtop(31n, uw(vv)), Word.zero(31n)}} : U32}:
  match vv:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10,
      WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21,
      WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31,
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

# a sign read off its top bit that is not 0 is 1
def sign01.t(
  bb: Bool,
  hh: {U32.is_eq(U32{WCon{bb, Word.zero(31n)}}, 0) == False{} : Bool}
) -> {U32{WCon{bb, Word.zero(31n)}} == 1 : U32}:
  match bb:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({U32{WCon{False{}, Word.zero(31n)}} == 1 : U32}, jenc.true_false(hh))

# a U32's sign that is not 0 is 1, its top bit named
def sign01.w(
  +vv: U32,
  +bt: Bool,
  +es: {Jpeg.decode.sign(vv) == U32{WCon{bt, Word.zero(31n)}} : U32},
  hh: {U32.is_eq(Jpeg.decode.sign(vv), 0) == False{} : Bool}
) -> {Jpeg.decode.sign(vv) == 1 : U32}:
  Equal.trans(U32, Jpeg.decode.sign(vv), U32{WCon{bt, Word.zero(31n)}}, 1, es, sign01.t(bt, Equal.trans(Bool,
    U32.is_eq(U32{WCon{bt, Word.zero(31n)}}, 0), U32.is_eq(Jpeg.decode.sign(vv), 0), False{}, Equal.cong(U32, Bool,
    uu =>
    U32.is_eq(uu, 0), U32{WCon{bt, Word.zero(31n)}}, Jpeg.decode.sign(vv), Equal.sym(U32, Jpeg.decode.sign(vv),
    U32{WCon{bt, Word.zero(31n)}}, es)), hh)))

# a U32's sign that is not 0 is 1
def sign01(+vv: U32, hh: {U32.is_eq(Jpeg.decode.sign(vv), 0) == False{} : Bool}) -> {Jpeg.decode.sign(vv) == 1 : U32}:
  sign01.w(vv, wtop(31n, uw(vv)), sign_top(vv), hh)

# a U32 of sign 0 is its own magnitude
def abs_pos(+vv: U32, es: {Jpeg.decode.sign(vv) == 0 : U32}) -> {Jpeg.decode.abs(vv) == vv : U32}:
  ss = Equal.sym(U32, Jpeg.decode.sign(vv), 0, es)
  %ss : {Jpeg.decode.abs.s(_, vv) == vv : U32}
  {==}

# a U32 of sign 1 has its two's complement as its magnitude
def abs_neg(+vv: U32, es: {Jpeg.decode.sign(vv) == 1 : U32}) -> {Jpeg.decode.abs(vv) == Jpeg.decode.neg32(vv) : U32}:
  ss = Equal.sym(U32, Jpeg.decode.sign(vv), 1, es)
  %ss : {Jpeg.decode.abs.s(_, vv) == Jpeg.decode.neg32(vv) : U32}
  {==}

# U32 order is the order of the values
def jenc.u_cmp(aa: U32, bb: U32) -> {U32.cmp(aa, bb) == Nat.cmp(U32.to_nat(aa), U32.to_nat(bb)) : Cmp}:
  match aa bb:
    case U32{xw} U32{yw}:
      M1.ras.word_cmp_nat(32n, xw, yw)

# a value not above n is below n + 1
def ngt_lt(
  xx: Nat,
  nn: Nat,
  hh: {Cmp.is_gt(Nat.cmp(xx, nn)) == False{} : Bool}
) -> {Cmp.is_lt(Nat.cmp(xx, 1n+nn)) == True{} : Bool}:
  match xx nn:
    case 0n _:
      {==}
    case 1n+_p 0n:
      Empty.absurd({Cmp.is_lt(Nat.cmp(1n+_p, 1n)) == True{} : Bool}, jenc.true_false(hh))
    case 1n+pp 1n+qq:
      ngt_lt(pp, qq, hh)

# a value other than 0 is not below 1
def neq0_lt1(
  xx: Nat,
  hh: {Cmp.is_eq(Nat.cmp(xx, 0n)) == False{} : Bool}
) -> {Cmp.is_lt(Nat.cmp(xx, 1n)) == False{} : Bool}:
  match xx:
    case 0n:
      Empty.absurd({Cmp.is_lt(Nat.cmp(0n, 1n)) == False{} : Bool}, jenc.true_false(hh))
    case 1n+pp:
      Equal.sym(Bool, False{}, Nat.is_lt(pp, 0n), M1.lt_zero_false(pp))

# a U32 not above n is below n + 1
def u_ngt_lt(
  +xx: U32,
  +nn: U32,
  +n1: U32,
  e1: {U32.to_nat(n1) == 1n+U32.to_nat(nn) : Nat},
  hh: {U32.is_gt(xx, nn) == False{} : Bool}
) -> {U32.is_lt(xx, n1) == True{} : Bool}:
  +ex = U32.to_nat(xx)
  +en = U32.to_nat(nn)
  e2 = Equal.sym(Nat, U32.to_nat(n1), 1n+en, e1)
  ec1 = Equal.sym(Cmp, U32.cmp(xx, n1), Nat.cmp(ex, U32.to_nat(n1)), jenc.u_cmp(xx, n1))
  %ec1 : {Cmp.is_lt(_) == True{} : Bool}
  %e2 : {Cmp.is_lt(Nat.cmp(ex, _)) == True{} : Bool}
  ngt_lt(ex, en, Equal.trans(Bool, Cmp.is_gt(Nat.cmp(ex, en)), Cmp.is_gt(U32.cmp(xx, nn)), False{}, Equal.cong(Cmp,
    Bool, cc => Cmp.is_gt(cc), Nat.cmp(ex, en), U32.cmp(xx, nn), Equal.sym(Cmp, U32.cmp(xx, nn), Nat.cmp(ex, en),
    jenc.u_cmp(xx, nn))), hh))

# a U32 other than 0 is not below 1
def u_nz(+xx: U32, hh: {U32.is_eq(xx, 0) == False{} : Bool}) -> {U32.is_lt(xx, 1) == False{} : Bool}:
  +ex = U32.to_nat(xx)
  Equal.trans(Bool, U32.is_lt(xx, 1), Cmp.is_lt(Nat.cmp(ex, 1n)), False{}, Equal.cong(Cmp, Bool, cc => Cmp.is_lt(cc),
    U32.cmp(xx, 1), Nat.cmp(ex, 1n), jenc.u_cmp(xx, 1)), neq0_lt1(ex, Equal.trans(Bool, Cmp.is_eq(Nat.cmp(ex, 0n)),
    U32.is_eq(xx, 0), False{}, Equal.cong(Cmp, Bool, cc => Cmp.is_eq(cc), Nat.cmp(ex, 0n), U32.cmp(xx, 0),
    Equal.sym(Cmp, U32.cmp(xx, 0), Nat.cmp(ex, 0n), jenc.u_cmp(xx, 0))), hh)))

# a clipped value, by whether it was above the limit: under the limit plus 1
def clipb.hi(
  gg: Bool,
  +vv: U32,
  +lim: U32,
  +l1: U32,
  +e1: {U32.to_nat(l1) == 1n+U32.to_nat(lim) : Nat},
  +es: {Jpeg.decode.sign(vv) == 0 : U32},
  +hg: {U32.is_gt(vv, lim) == gg : Bool},
  +ha: {U32.is_lt(Jpeg.decode.abs(lim), l1) == True{} : Bool}
) -> {U32.is_lt(Jpeg.decode.abs(Jenc.encode.clip.hi(gg, vv, lim)), l1) == True{} : Bool}:
  match gg:
    case True{}:
      ha
    case False{}:
      ev = Equal.sym(U32, Jpeg.decode.abs(vv), vv, abs_pos(vv, es))
      %ev : {U32.is_lt(_, l1) == True{} : Bool}
      u_ngt_lt(vv, lim, l1, e1, hg)

# a clipped negative value, by whether its magnitude was above the limit
def clipb.lo(
  gg: Bool,
  +vv: U32,
  +lim: U32,
  +l1: U32,
  +e1: {U32.to_nat(l1) == 1n+U32.to_nat(lim) : Nat},
  +hg: {U32.is_gt(Jpeg.decode.abs(vv), lim) == gg : Bool},
  +hb: {U32.is_lt(Jpeg.decode.abs(Jpeg.decode.neg32(lim)), l1) == True{} : Bool}
) -> {U32.is_lt(Jpeg.decode.abs(Jenc.encode.clip.lo(gg, vv, lim)), l1) == True{} : Bool}:
  match gg:
    case True{}:
      hb
    case False{}:
      u_ngt_lt(Jpeg.decode.abs(vv), lim, l1, e1, hg)

# a clipped value, by its sign
def clipb.s(
  ss: Bool,
  +vv: U32,
  +lim: U32,
  +l1: U32,
  +e1: {U32.to_nat(l1) == 1n+U32.to_nat(lim) : Nat},
  +hs: {U32.is_eq(Jpeg.decode.sign(vv), 0) == ss : Bool},
  +ha: {U32.is_lt(Jpeg.decode.abs(lim), l1) == True{} : Bool},
  +hb: {U32.is_lt(Jpeg.decode.abs(Jpeg.decode.neg32(lim)), l1) == True{} : Bool}
) -> {U32.is_lt(Jpeg.decode.abs(Jenc.encode.clip.b(ss, vv, lim)), l1) == True{} : Bool}:
  match ss:
    case True{}:
      clipb.hi(U32.is_gt(vv, lim), vv, lim, l1, e1, M1.ueq(Jpeg.decode.sign(vv), 0, hs), {==}, ha)
    case False{}:
      clipb.lo(U32.is_gt(Jpeg.decode.abs(vv), lim), vv, lim, l1, e1, {==}, hb)

# the magnitude of a clipped value is at most the limit
def clipb(
  +vv: U32,
  +lim: U32,
  +l1: U32,
  +e1: {U32.to_nat(l1) == 1n+U32.to_nat(lim) : Nat},
  +ha: {U32.is_lt(Jpeg.decode.abs(lim), l1) == True{} : Bool},
  +hb: {U32.is_lt(Jpeg.decode.abs(Jpeg.decode.neg32(lim)), l1) == True{} : Bool}
) -> {U32.is_lt(Jpeg.decode.abs(Jenc.encode.clip(vv, lim)), l1) == True{} : Bool}:
  clipb.s(U32.is_eq(Jpeg.decode.sign(vv), 0), vv, lim, l1, e1, {==}, ha, hb)

# a clipped nonzero value, by whether it was above the limit, is not zero
def clipnz.hi(
  gg: Bool,
  +vv: U32,
  +lim: U32,
  +es: {Jpeg.decode.sign(vv) == 0 : U32},
  +hv: {U32.is_eq(vv, 0) == False{} : Bool},
  +ha: {U32.is_lt(Jpeg.decode.abs(lim), 1) == False{} : Bool}
) -> {U32.is_lt(Jpeg.decode.abs(Jenc.encode.clip.hi(gg, vv, lim)), 1) == False{} : Bool}:
  match gg:
    case True{}:
      ha
    case False{}:
      ev = Equal.sym(U32, Jpeg.decode.abs(vv), vv, abs_pos(vv, es))
      %ev : {U32.is_lt(_, 1) == False{} : Bool}
      u_nz(vv, hv)

# a clipped negative nonzero value, by whether its magnitude was above the limit, is not zero
def clipnz.lo(
  gg: Bool,
  +vv: U32,
  +lim: U32,
  +es: {Jpeg.decode.sign(vv) == 1 : U32},
  +hv: {U32.is_eq(vv, 0) == False{} : Bool},
  +hb: {U32.is_lt(Jpeg.decode.abs(Jpeg.decode.neg32(lim)), 1) == False{} : Bool}
) -> {U32.is_lt(Jpeg.decode.abs(Jenc.encode.clip.lo(gg, vv, lim)), 1) == False{} : Bool}:
  match gg:
    case True{}:
      hb
    case False{}:
      ev = Equal.sym(U32, Jpeg.decode.abs(vv), Jpeg.decode.neg32(vv), abs_neg(vv, es))
      %ev : {U32.is_lt(_, 1) == False{} : Bool}
      u_nz(Jpeg.decode.neg32(vv), Equal.trans(Bool, U32.is_eq(Jpeg.decode.neg32(vv), 0), U32.is_eq(vv, 0), False{},
        neg_nz(vv), hv))

# a clipped nonzero value, by its sign, is not zero
def clipnz.s(
  ss: Bool,
  +vv: U32,
  +lim: U32,
  +hs: {U32.is_eq(Jpeg.decode.sign(vv), 0) == ss : Bool},
  +hv: {U32.is_eq(vv, 0) == False{} : Bool},
  +ha: {U32.is_lt(Jpeg.decode.abs(lim), 1) == False{} : Bool},
  +hb: {U32.is_lt(Jpeg.decode.abs(Jpeg.decode.neg32(lim)), 1) == False{} : Bool}
) -> {U32.is_lt(Jpeg.decode.abs(Jenc.encode.clip.b(ss, vv, lim)), 1) == False{} : Bool}:
  match ss:
    case True{}:
      clipnz.hi(U32.is_gt(vv, lim), vv, lim, M1.ueq(Jpeg.decode.sign(vv), 0, hs), hv, ha)
    case False{}:
      clipnz.lo(U32.is_gt(Jpeg.decode.abs(vv), lim), vv, lim, sign01(vv, hs), hv, hb)

# the magnitude of a clipped nonzero value is not zero
def clipnz(
  +vv: U32,
  +lim: U32,
  +hv: {U32.is_eq(vv, 0) == False{} : Bool},
  +ha: {U32.is_lt(Jpeg.decode.abs(lim), 1) == False{} : Bool},
  +hb: {U32.is_lt(Jpeg.decode.abs(Jpeg.decode.neg32(lim)), 1) == False{} : Bool}
) -> {U32.is_lt(Jpeg.decode.abs(Jenc.encode.clip(vv, lim)), 1) == False{} : Bool}:
  clipnz.s(U32.is_eq(Jpeg.decode.sign(vv), 0), vv, lim, {==}, hv, ha, hb)

# an AC coefficient clipped to 1023 has a magnitude below 1024
def clip.ac(+vv: U32) -> {U32.is_lt(Jpeg.decode.abs(Jenc.encode.clip(vv, 1023)), 1024) == True{} : Bool}:
  clipb(vv, 1023, 1024, {==}, {==}, {==})

# a nonzero AC coefficient clipped to 1023 is not zero
def clipnz.ac(
  +vv: U32,
  +hv: {U32.is_eq(vv, 0) == False{} : Bool}
) -> {U32.is_lt(Jpeg.decode.abs(Jenc.encode.clip(vv, 1023)), 1) == False{} : Bool}:
  clipnz(vv, 1023, hv, {==}, {==})

# the size of a magnitude, as its chain of comparisons, is one of [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
def memcat.ac.b(
  b0: Bool,
  b1: Bool,
  b2: Bool,
  b3: Bool,
  b4: Bool,
  b5: Bool,
  b6: Bool,
  b7: Bool,
  b8: Bool,
  b9: Bool,
  b10: Bool,
  b11: Bool,
  h0: {b0 == False{} : Bool},
  hh: {b10 == True{} : Bool}
) -> {L1.jpg.memb(Jenc.encode.cat.pick(b0, 0, Jenc.encode.cat.pick(b1, 1, Jenc.encode.cat.pick(b2, 2,
  Jenc.encode.cat.pick(b3, 3, Jenc.encode.cat.pick(b4, 4, Jenc.encode.cat.pick(b5, 5, Jenc.encode.cat.pick(b6, 6,
  Jenc.encode.cat.pick(b7, 7, Jenc.encode.cat.pick(b8, 8, Jenc.encode.cat.pick(b9, 9, Jenc.encode.cat.pick(b10, 10,
  Jenc.encode.cat.pick(b11, 11, 12)))))))))))), [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]) == True{} : Bool}:
  match b0:
    case True{}:
      Empty.absurd({L1.jpg.memb(Jenc.encode.cat.pick(True{}, 0, Jenc.encode.cat.pick(b1, 1, Jenc.encode.cat.pick(b2,
        2, Jenc.encode.cat.pick(b3, 3, Jenc.encode.cat.pick(b4, 4, Jenc.encode.cat.pick(b5, 5,
        Jenc.encode.cat.pick(b6, 6, Jenc.encode.cat.pick(b7, 7, Jenc.encode.cat.pick(b8, 8, Jenc.encode.cat.pick(b9,
        9, Jenc.encode.cat.pick(b10, 10, Jenc.encode.cat.pick(b11, 11, 12)))))))))))), [1, 2, 3, 4, 5, 6, 7, 8, 9,
        10]) == True{} : Bool}, jenc.true_false(h0))
    case False{}:
      match b1:
        case True{}:
          {==}
        case False{}:
          match b2:
            case True{}:
              {==}
            case False{}:
              match b3:
                case True{}:
                  {==}
                case False{}:
                  match b4:
                    case True{}:
                      {==}
                    case False{}:
                      match b5:
                        case True{}:
                          {==}
                        case False{}:
                          match b6:
                            case True{}:
                              {==}
                            case False{}:
                              match b7:
                                case True{}:
                                  {==}
                                case False{}:
                                  match b8:
                                    case True{}:
                                      {==}
                                    case False{}:
                                      match b9:
                                        case True{}:
                                          {==}
                                        case False{}:
                                          match b10:
                                            case True{}:
                                              {==}
                                            case False{}:
                                              Empty.absurd({L1.jpg.memb(Jenc.encode.cat.pick(False{}, 0,
                                                Jenc.encode.cat.pick(False{}, 1, Jenc.encode.cat.pick(False{}, 2,
                                                Jenc.encode.cat.pick(False{}, 3, Jenc.encode.cat.pick(False{}, 4,
                                                Jenc.encode.cat.pick(False{}, 5, Jenc.encode.cat.pick(False{}, 6,
                                                Jenc.encode.cat.pick(False{}, 7, Jenc.encode.cat.pick(False{}, 8,
                                                Jenc.encode.cat.pick(False{}, 9, Jenc.encode.cat.pick(False{}, 10,
                                                Jenc.encode.cat.pick(b11, 11, 12)))))))))))), [1, 2, 3, 4, 5, 6, 7, 8,
                                                9, 10]) == True{} : Bool}, M1.huf.false_true(hh))

# the size of a magnitude, as its chain of comparisons, is one of Jenc.encode.dcsyms()
def memcat.dc.b(
  b0: Bool,
  b1: Bool,
  b2: Bool,
  b3: Bool,
  b4: Bool,
  b5: Bool,
  b6: Bool,
  b7: Bool,
  b8: Bool,
  b9: Bool,
  b10: Bool,
  b11: Bool,
  hh: {b11 == True{} : Bool}
) -> {L1.jpg.memb(Jenc.encode.cat.pick(b0, 0, Jenc.encode.cat.pick(b1, 1, Jenc.encode.cat.pick(b2, 2,
  Jenc.encode.cat.pick(b3, 3, Jenc.encode.cat.pick(b4, 4, Jenc.encode.cat.pick(b5, 5, Jenc.encode.cat.pick(b6, 6,
  Jenc.encode.cat.pick(b7, 7, Jenc.encode.cat.pick(b8, 8, Jenc.encode.cat.pick(b9, 9, Jenc.encode.cat.pick(b10, 10,
  Jenc.encode.cat.pick(b11, 11, 12)))))))))))), Jenc.encode.dcsyms()) == True{} : Bool}:
  match b0:
    case True{}:
      {==}
    case False{}:
      match b1:
        case True{}:
          {==}
        case False{}:
          match b2:
            case True{}:
              {==}
            case False{}:
              match b3:
                case True{}:
                  {==}
                case False{}:
                  match b4:
                    case True{}:
                      {==}
                    case False{}:
                      match b5:
                        case True{}:
                          {==}
                        case False{}:
                          match b6:
                            case True{}:
                              {==}
                            case False{}:
                              match b7:
                                case True{}:
                                  {==}
                                case False{}:
                                  match b8:
                                    case True{}:
                                      {==}
                                    case False{}:
                                      match b9:
                                        case True{}:
                                          {==}
                                        case False{}:
                                          match b10:
                                            case True{}:
                                              {==}
                                            case False{}:
                                              match b11:
                                                case True{}:
                                                  {==}
                                                case False{}:
                                                  Empty.absurd({L1.jpg.memb(Jenc.encode.cat.pick(False{}, 0,
                                                    Jenc.encode.cat.pick(False{}, 1, Jenc.encode.cat.pick(False{}, 2,
                                                    Jenc.encode.cat.pick(False{}, 3, Jenc.encode.cat.pick(False{}, 4,
                                                    Jenc.encode.cat.pick(False{}, 5, Jenc.encode.cat.pick(False{}, 6,
                                                    Jenc.encode.cat.pick(False{}, 7, Jenc.encode.cat.pick(False{}, 8,
                                                    Jenc.encode.cat.pick(False{}, 9, Jenc.encode.cat.pick(False{}, 10,
                                                    Jenc.encode.cat.pick(False{}, 11, 12)))))))))))),
                                                    Jenc.encode.dcsyms()) == True{} : Bool}, M1.huf.false_true(hh))

# the size of an AC magnitude from 1 to 1023 is one of 1 to 10
def memcat.ac(
  +xx: U32,
  h0: {U32.is_lt(Jpeg.decode.abs(xx), 1) == False{} : Bool},
  hh: {U32.is_lt(Jpeg.decode.abs(xx), 1024) == True{} : Bool}
) -> {L1.jpg.memb(Jenc.encode.cat(xx), [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]) == True{} : Bool}:
  memcat.ac.b(U32.is_lt(Jpeg.decode.abs(xx), 1), U32.is_lt(Jpeg.decode.abs(xx), 2), U32.is_lt(Jpeg.decode.abs(xx), 4),
    U32.is_lt(Jpeg.decode.abs(xx), 8), U32.is_lt(Jpeg.decode.abs(xx), 16), U32.is_lt(Jpeg.decode.abs(xx), 32),
    U32.is_lt(Jpeg.decode.abs(xx), 64), U32.is_lt(Jpeg.decode.abs(xx), 128), U32.is_lt(Jpeg.decode.abs(xx), 256),
    U32.is_lt(Jpeg.decode.abs(xx), 512), U32.is_lt(Jpeg.decode.abs(xx), 1024), U32.is_lt(Jpeg.decode.abs(xx), 2048),
    h0, hh)

# the size of a DC difference below 2048 in magnitude is one of the DC symbols
def memcat.dc(
  +xx: U32,
  hh: {U32.is_lt(Jpeg.decode.abs(xx), 2048) == True{} : Bool}
) -> {L1.jpg.memb(Jenc.encode.cat(xx), Jenc.encode.dcsyms()) == True{} : Bool}:
  memcat.dc.b(U32.is_lt(Jpeg.decode.abs(xx), 1), U32.is_lt(Jpeg.decode.abs(xx), 2), U32.is_lt(Jpeg.decode.abs(xx), 4),
    U32.is_lt(Jpeg.decode.abs(xx), 8), U32.is_lt(Jpeg.decode.abs(xx), 16), U32.is_lt(Jpeg.decode.abs(xx), 32),
    U32.is_lt(Jpeg.decode.abs(xx), 64), U32.is_lt(Jpeg.decode.abs(xx), 128), U32.is_lt(Jpeg.decode.abs(xx), 256),
    U32.is_lt(Jpeg.decode.abs(xx), 512), U32.is_lt(Jpeg.decode.abs(xx), 1024), U32.is_lt(Jpeg.decode.abs(xx), 2048), hh)

# a word of four bits over 28 zeros is one of 0 to 15
def nib.b(
  b0: Bool,
  b1: Bool,
  b2: Bool,
  b3: Bool
) -> {L1.jpg.memb(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, Word.zero(28n)}}}}}, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10,
  11, 12, 13, 14, 15]) == True{} : Bool}:
  match b0:
    case True{}:
      match b1:
        case True{}:
          match b2:
            case True{}:
              match b3:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match b3:
                case True{}:
                  {==}
                case False{}:
                  {==}
        case False{}:
          match b2:
            case True{}:
              match b3:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match b3:
                case True{}:
                  {==}
                case False{}:
                  {==}
    case False{}:
      match b1:
        case True{}:
          match b2:
            case True{}:
              match b3:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match b3:
                case True{}:
                  {==}
                case False{}:
                  {==}
        case False{}:
          match b2:
            case True{}:
              match b3:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match b3:
                case True{}:
                  {==}
                case False{}:
                  {==}

# the low four bits of a U32 are one of 0 to 15
def nib16(
  vv: U32
) -> {L1.jpg.memb(U32.and(15, vv), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]) == True{} : Bool}:
  match vv:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{_b4, WCon{_b5, WCon{_b6, WCon{_b7, WCon{_b8, WCon{_b9,
      WCon{_b10, WCon{_b11, WCon{_b12, WCon{_b13, WCon{_b14, WCon{_b15, WCon{_b16, WCon{_b17, WCon{_b18, WCon{_b19,
      WCon{_b20, WCon{_b21, WCon{_b22, WCon{_b23, WCon{_b24, WCon{_b25, WCon{_b26, WCon{_b27, WCon{_b28, WCon{_b29,
      WCon{_b30, WCon{_b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      nib.b(b0, b1, b2, b3)

# the facts for every nibble and size of two lists
def allq(qs: List<&2, U32>, +cs: List<&2, U32>) -> Bool:
  match qs:
    case Nil{}:
      True{}
    case +qq <> rest:
      L1.jpg.also(M1.allc(qq, cs), allq(rest, cs))

# every nibble from 0 to 15 and size from 1 to 10 has the facts, the answer
# bb being True. The statement is written out, not named (a named one would
# have the checker normalize both sides where symok.of hands this proof on,
# recomputing every fact twice); bb only lets the header span lines
def allq.ok(
  -bb: Bool,
  hb: {True{} == bb : Bool}
) -> {allq([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]) == bb : Bool}:
  %hb : {allq([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]) == _ : Bool}
  {==}

# the rest of the nibbles, as a nibble's membership step needs it
def InqIh(+_qq: U32, +_cc: U32, -rest: List<&2, U32>, -cs: List<&2, U32>) -> Type:
  @hr: {L1.jpg.memb(_qq, rest) == True{} : Bool} -> @ha: {allq(rest, cs) == True{} : Bool} -> {M1.symok(_qq,
    _cc) == True{} :
    Bool}

# a nibble of the list, by whether it is the list's first
def inq.b(
  eq: Bool,
  +qq: U32,
  +cc: U32,
  +xx: U32,
  +rest: List<&2, U32>,
  +cs: List<&2, U32>,
  he: {U32.is_eq(qq, xx) == eq : Bool},
  hin: {L1.jpg.eith(eq, L1.jpg.memb(qq, rest)) == True{} : Bool},
  hc: {L1.jpg.memb(cc, cs) == True{} : Bool},
  hall: {L1.jpg.also(M1.allc(xx, cs), allq(rest, cs)) == True{} : Bool},
  ih: InqIh(qq, cc, rest, cs)
) -> {M1.symok(qq, cc) == True{} : Bool}:
  match eq:
    case True{}:
      es = Equal.sym(U32, qq, xx, M1.ueq(qq, xx, he))
      %es : {M1.symok(_, cc) == True{} : Bool}
      M1.inc(cs, xx, cc, hc, M1.also_l(M1.allc(xx, cs), allq(rest, cs), hall))
    case False{}:
      ih(hin, M1.also_r(M1.allc(xx, cs), allq(rest, cs), hall))

# a nibble and a size of lists whose pairs all have the facts have them
def inq(
  qs: List<&2, U32>,
  +cs: List<&2, U32>,
  +qq: U32,
  +cc: U32,
  hin: {L1.jpg.memb(qq, qs) == True{} : Bool},
  +hc: {L1.jpg.memb(cc, cs) == True{} : Bool},
  hall: {allq(qs, cs) == True{} : Bool}
) -> {M1.symok(qq, cc) == True{} : Bool}:
  match qs:
    case Nil{}:
      Empty.absurd({M1.symok(qq, cc) == True{} : Bool}, M1.huf.false_true(hin))
    case +xx <> +rest:
      inq.b(U32.is_eq(qq, xx), qq, cc, xx, rest, cs, {==}, hin, hc, hall, hr => ha => inq(rest, cs, qq, cc, hr, hc, ha))

# the AC symbol of a run's nibble and an AC size has the facts
def symok.of(
  +run: U32,
  +cc: U32,
  hc: {L1.jpg.memb(cc, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]) == True{} : Bool}
) -> {M1.symok(U32.and(15, run), cc) == True{} : Bool}:
  inq([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10], U32.and(15, run), cc,
    nib16(run), hc, allq.ok(True{}, {==}))

# a word compare not above after its low bits is not above before them
def fin_ngt(
  aa: Bool,
  bb: Bool,
  tt: Cmp,
  hh: {Cmp.is_gt(Word.cmp.fin(aa, bb, tt)) == False{} : Bool}
) -> {Cmp.is_gt(tt) == False{} : Bool}:
  match tt:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({Cmp.is_gt(GT{}) == False{} : Bool}, jenc.true_false(hh))

# a one-bit word not above one whose bit is clear has a clear bit
def ngt_top0(
  aa: Bool,
  bb: Bool,
  tt: Word(0n),
  uu: Word(0n),
  hc: {wtop(0n, WCon{bb, uu}) == False{} : Bool},
  hh: {Cmp.is_gt(Word.cmp(1n, WCon{aa, tt}, WCon{bb, uu})) == False{} : Bool}
) -> {wtop(0n, WCon{aa, tt}) == False{} : Bool}:
  match aa bb:
    case True{} True{}:
      Empty.absurd({wtop(0n, WCon{True{}, tt}) == False{} : Bool}, jenc.true_false(hc))
    case False{} True{}:
      Empty.absurd({wtop(0n, WCon{False{}, tt}) == False{} : Bool}, jenc.true_false(hc))
    case True{} False{}:
      Empty.absurd({wtop(0n, WCon{True{}, tt}) == False{} : Bool}, jenc.true_false(hh))
    case False{} False{}:
      {==}

# a word not above one whose top bit is clear has a clear top bit
def ngt_top(
  nn: Nat,
  ww: Word(1n+nn),
  cw: Word(1n+nn),
  hc: {wtop(nn, cw) == False{} : Bool},
  hh: {Cmp.is_gt(Word.cmp(1n+nn, ww, cw)) == False{} : Bool}
) -> {wtop(nn, ww) == False{} : Bool}:
  match nn:
    case 0n:
      match ww cw:
        case WCon{aa, tt} WCon{bb, uu}:
          ngt_top0(aa, bb, tt, uu, hc, hh)
    case 1n+ +pp:
      match ww cw:
        case WCon{+aa, +tt} WCon{+bb, +uu}:
          ngt_top(pp, tt, uu, hc, fin_ngt(aa, bb, Word.cmp(1n+pp, tt, uu), hh))

# a compare that is below is not above
def lt_ngt(tt: Cmp, hh: {Cmp.is_lt(tt) == True{} : Bool}) -> {Cmp.is_gt(tt) == False{} : Bool}:
  match tt:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({Cmp.is_gt(EQ{}) == False{} : Bool}, M1.huf.false_true(hh))
    case GT{}:
      Empty.absurd({Cmp.is_gt(GT{}) == False{} : Bool}, M1.huf.false_true(hh))

# a U32 below one whose top bit is clear has sign 0
def small_sign(
  +xx: U32,
  +cc: U32,
  hc: {wtop(31n, uw(cc)) == False{} : Bool},
  hh: {U32.is_lt(xx, cc) == True{} : Bool}
) -> {Jpeg.decode.sign(xx) == 0 : U32}:
  match xx cc:
    case U32{+xw} U32{+cw}:
      Equal.trans(U32, Jpeg.decode.sign(U32{xw}), U32{WCon{wtop(31n, xw), Word.zero(31n)}}, 0, sign_top(U32{xw}),
        Equal.cong(Bool, U32, bb => U32{WCon{bb, Word.zero(31n)}}, wtop(31n, xw), False{}, ngt_top(31n, xw, cw, hc,
        lt_ngt(Word.cmp(32n, xw, cw), hh))))

# a U32 below 2048 is its own magnitude
def abs_small(+xx: U32, hh: {U32.is_lt(xx, 2048) == True{} : Bool}) -> {Jpeg.decode.abs(xx) == xx : U32}:
  abs_pos(xx, small_sign(xx, 2048, {==}, hh))

# below n + 1 is at most n
def lt_s_le(xx: Nat, zz: Nat) -> {Nat.is_lt(xx, 1n+zz) == Nat.is_le(xx, zz) : Bool}:
  match xx zz:
    case 0n 0n:
      {==}
    case 0n 1n+_q:
      {==}
    case 1n+pp 0n:
      Equal.sym(Bool, False{}, Nat.is_lt(pp, 0n), M1.lt_zero_false(pp))
    case 1n+pp 1n+qq:
      lt_s_le(pp, qq)

# at least, read the other way, is at most
def ge_le(xx: Nat, yy: Nat) -> {Cmp.is_ge(Nat.cmp(xx, yy)) == Nat.is_le(yy, xx) : Bool}:
  match xx yy:
    case 0n 0n:
      {==}
    case 0n 1n+_q:
      {==}
    case 1n+_p 0n:
      {==}
    case 1n+pp 1n+qq:
      ge_le(pp, qq)

# not at most is above, read the other way
def nle_lt(xx: Nat, yy: Nat, hh: {Nat.is_le(xx, yy) == False{} : Bool}) -> {Nat.is_lt(yy, xx) == True{} : Bool}:
  match xx yy:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, jenc.true_false(hh))
    case 0n 1n+_q:
      Empty.absurd({Nat.is_lt(1n+_q, 0n) == True{} : Bool}, jenc.true_false(hh))
    case 1n+_p 0n:
      {==}
    case 1n+pp 1n+qq:
      nle_lt(pp, qq, hh)

# a U32 compare below, as Nat
def ult_n(
  +xx: U32,
  +yy: U32,
  hh: {U32.is_lt(xx, yy) == True{} : Bool}
) -> {Nat.is_lt(U32.to_nat(xx), U32.to_nat(yy)) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_lt(U32.to_nat(xx), U32.to_nat(yy)), U32.is_lt(xx, yy), True{}, Equal.sym(Bool, U32.is_lt(xx,
    yy), Nat.is_lt(U32.to_nat(xx), U32.to_nat(yy)), M3.u32_lt(xx, yy)), hh)

# a Nat compare below, as U32
def n_ult(
  +xx: U32,
  +yy: U32,
  hh: {Nat.is_lt(U32.to_nat(xx), U32.to_nat(yy)) == True{} : Bool}
) -> {U32.is_lt(xx, yy) == True{} : Bool}:
  Equal.trans(Bool, U32.is_lt(xx, yy), Nat.is_lt(U32.to_nat(xx), U32.to_nat(yy)), True{}, M3.u32_lt(xx, yy), hh)

# a clipped value is below the limit plus 1
def hi_lt(
  gg: Bool,
  +vv: U32,
  +lim: U32,
  +l1: U32,
  e1: {U32.to_nat(l1) == 1n+U32.to_nat(lim) : Nat},
  hg: {U32.is_gt(vv, lim) == gg : Bool},
  hl: {U32.is_lt(lim, l1) == True{} : Bool}
) -> {U32.is_lt(Jenc.encode.clip.hi(gg, vv, lim), l1) == True{} : Bool}:
  match gg:
    case True{}:
      hl
    case False{}:
      u_ngt_lt(vv, lim, l1, e1, hg)

# a value below 1024, plus 1024, is below 2048
def add1024(
  +cc: U32,
  hc: {U32.is_lt(cc, 1024) == True{} : Bool}
) -> {U32.is_lt((cc + 1024 : U32), 2048) == True{} : Bool}:
  +cn = U32.to_nat(cc)
  h1 = M1.lt_add_mono(1024n, cn, 1024n, ult_n(cc, 1024, hc))
  +h2 = {Equal.trans(Bool, Nat.is_lt(Nat.add(cn, 1024n), 2048n), Nat.is_lt(Nat.add(1024n, cn), 2048n), True{},
    Equal.cong(Nat, Bool, nn => Nat.is_lt(nn, 2048n), Nat.add(cn, 1024n), Nat.add(1024n, cn), M1.ras.add_comm(cn,
        1024n)),
    h1) : {Nat.is_lt(Nat.add(cn, 1024n), 2048n) == True{} : Bool}}
  n_ult((cc + 1024 : U32), 2048, Equal.trans(Bool, Nat.is_lt(U32.to_nat((cc + 1024 : U32)), 2048n),
    Nat.is_lt(Nat.add(cn, 1024n), 2048n), True{}, Equal.cong(Nat, Bool, nn => Nat.is_lt(nn, 2048n),
    U32.to_nat((cc + 1024 : U32)), Nat.add(cn, 1024n), M3.u32_add_below(cc, 1024, 2048, M1.lt_le(Nat.add(cn, 1024n),
    2048n, h2))), h2))

# 1024 less a value at most 1024 is below 2048
def sub1024(
  +mm: U32,
  hm: {U32.is_lt(mm, 1025) == True{} : Bool}
) -> {U32.is_lt((1024 - mm : U32), 2048) == True{} : Bool}:
  +mn = U32.to_nat(mm)
  hl = Equal.trans(Bool, Nat.is_le(mn, 1024n), Nat.is_lt(mn, 1025n), True{}, Equal.sym(Bool, Nat.is_lt(mn, 1025n),
    Nat.is_le(mn, 1024n), lt_s_le(mn, 1024n)), ult_n(mm, 1025, hm))
  n_ult((1024 - mm : U32), 2048, Equal.trans(Bool, Nat.is_lt(U32.to_nat((1024 - mm : U32)), 2048n),
    Nat.is_lt(Nat.sub(1024n, mn), 2048n), True{}, Equal.cong(Nat, Bool, nn => Nat.is_lt(nn, 2048n),
    U32.to_nat((1024 - mm : U32)), Nat.sub(1024n, mn), M2.ras.u32_sub_nat(1024, mm, hl)), M1.le_lt_trans(Nat.sub(1024n,
    mn), 1024n, 2048n, sub_le(1024n, mn), {==})))

# a DC clipped and biased, by its sign, is below 2048
def bias.b(pos: Bool, +vv: U32) -> {U32.is_lt(Jenc.encode.dcbias.b(pos, vv), 2048) == True{} : Bool}:
  match pos:
    case True{}:
      add1024(Jenc.encode.clip.hi(U32.is_gt(vv, 1023), vv, 1023), hi_lt(U32.is_gt(vv, 1023), vv, 1023, 1024, {==},
        {==}, {==}))
    case False{}:
      +av = Jpeg.decode.abs(vv)
      sub1024(Jenc.encode.clip.hi(U32.is_gt(av, 1024), av, 1024), hi_lt(U32.is_gt(av, 1024), av, 1024, 1025, {==},
        {==}, {==}))

# a DC clipped and biased is below 2048
def bias_lt(+vv: U32) -> {U32.is_lt(Jenc.encode.dcbias(vv), 2048) == True{} : Bool}:
  bias.b(U32.is_eq(Jpeg.decode.sign(vv), 0), vv)

# the difference of two biased DCs, the first at least the second, is below 2048
def up_lt(
  +bb: U32,
  +pb: U32,
  hb: {U32.is_lt(bb, 2048) == True{} : Bool},
  hg: {U32.is_ge(bb, pb) == True{} : Bool}
) -> {U32.is_lt((bb - pb : U32), 2048) == True{} : Bool}:
  +bn = U32.to_nat(bb)
  +pn = U32.to_nat(pb)
  hl = Equal.trans(Bool, Nat.is_le(pn, bn), Cmp.is_ge(Nat.cmp(bn, pn)), True{}, Equal.sym(Bool, Cmp.is_ge(Nat.cmp(bn,
    pn)), Nat.is_le(pn, bn), ge_le(bn, pn)), Equal.trans(Bool, Cmp.is_ge(Nat.cmp(bn, pn)), U32.is_ge(bb, pb), True{},
    Equal.cong(Cmp, Bool, cc => Cmp.is_ge(cc), Nat.cmp(bn, pn), U32.cmp(bb, pb), Equal.sym(Cmp, U32.cmp(bb, pb),
    Nat.cmp(bn, pn), jenc.u_cmp(bb, pb))), hg))
  n_ult((bb - pb : U32), 2048, Equal.trans(Bool, Nat.is_lt(U32.to_nat((bb - pb : U32)), 2048n), Nat.is_lt(Nat.sub(bn,
    pn), 2048n), True{}, Equal.cong(Nat, Bool, nn => Nat.is_lt(nn, 2048n), U32.to_nat((bb - pb : U32)), Nat.sub(bn,
    pn), M2.ras.u32_sub_nat(bb, pb, hl)), M1.le_lt_trans(Nat.sub(bn, pn), bn, 2048n, sub_le(bn, pn), ult_n(bb, 2048,
    hb))))

# the difference of two biased DCs, the first below the second, taken the other way, is below 2048
def down_lt(
  +bb: U32,
  +pb: U32,
  hp: {U32.is_lt(pb, 2048) == True{} : Bool},
  hg: {U32.is_ge(bb, pb) == False{} : Bool}
) -> {U32.is_lt((pb - bb : U32), 2048) == True{} : Bool}:
  +bn = U32.to_nat(bb)
  +pn = U32.to_nat(pb)
  hn = Equal.trans(Bool, Nat.is_le(pn, bn), Cmp.is_ge(Nat.cmp(bn, pn)), False{}, Equal.sym(Bool, Cmp.is_ge(Nat.cmp(bn,
    pn)), Nat.is_le(pn, bn), ge_le(bn, pn)), Equal.trans(Bool, Cmp.is_ge(Nat.cmp(bn, pn)), U32.is_ge(bb, pb), False{},
    Equal.cong(Cmp, Bool, cc => Cmp.is_ge(cc), Nat.cmp(bn, pn), U32.cmp(bb, pb), Equal.sym(Cmp, U32.cmp(bb, pb),
    Nat.cmp(bn, pn), jenc.u_cmp(bb, pb))), hg))
  hl = M1.lt_le(bn, pn, nle_lt(pn, bn, hn))
  n_ult((pb - bb : U32), 2048, Equal.trans(Bool, Nat.is_lt(U32.to_nat((pb - bb : U32)), 2048n), Nat.is_lt(Nat.sub(pn,
    bn), 2048n), True{}, Equal.cong(Nat, Bool, nn => Nat.is_lt(nn, 2048n), U32.to_nat((pb - bb : U32)), Nat.sub(pn,
    bn), M2.ras.u32_sub_nat(pb, bb, hl)), M1.le_lt_trans(Nat.sub(pn, bn), pn, 2048n, sub_le(pn, bn), ult_n(pb, 2048,
    hp))))

# the writer's bits of a code of kk bits are kk bits
def len_cb(kk: Nat, +code: U32) -> {List.length(&2, Bool, L1.jpg.cb(kk, code)) == kk : Nat}:
  match kk:
    case 0n:
      {==}
    case 1n+ +pp:
      Equal.cong(Nat, Nat, nn => 1n+nn, List.length(&2, Bool, L1.jpg.cb(pp, code)), pp, len_cb(pp, code))

# the magnitude bits of a negative DC difference -mm: none for size 0
def mzn(zero: Bool, +cat: U32, +mm: U32) -> List<&2, Bool>:
  match zero:
    case True{}:
      +_u = (cat + mm : U32)
      []
    case False{}:
      L1.jpg.cb(U32.to_nat(cat), ((U32.shln(1, U32.to_nat(cat)) - 1 : U32) - mm : U32))

# the encoder's magnitude bits of a negative DC difference are mzn's, fed to the writer
def magn_eq(
  zero: Bool,
  +pp: Jenc.Put,
  +cat: U32,
  +mm: U32
) -> {Jenc.encode.magp.n(zero, pp, cat, mm) == L1.jpg.feed(mzn(zero, cat, mm), pp) : Jenc.Put}:
  match zero:
    case True{}:
      {==}
    case False{}:
      bits_go(U32.to_nat(cat), pp, ((U32.shln(1, U32.to_nat(cat)) - 1 : U32) - mm : U32))

# as many magnitude bits as the size, by whether the size is 0
def mzlen(
  zero: Bool,
  +cat: U32,
  +vv: U32,
  hz: {U32.is_eq(cat, 0) == zero : Bool}
) -> {Nat.is_eq(List.length(&2, Bool, mz(zero, cat, vv)), U32.to_nat(cat)) == True{} : Bool}:
  match zero:
    case True{}:
      ec = Equal.sym(U32, cat, 0, M1.ueq(cat, 0, hz))
      %ec : {Nat.is_eq(0n, U32.to_nat(_)) == True{} : Bool}
      {==}
    case False{}:
      +kn = U32.to_nat(cat)
      el = Equal.sym(Nat, List.length(&2, Bool, L1.jpg.cb(kn, Jenc.encode.mag(cat, vv))), kn, len_cb(kn,
        Jenc.encode.mag(cat,
        vv)))
      %el : {Nat.is_eq(_, kn) == True{} : Bool}
      M1.nat_eq_refl(kn)

# as many magnitude bits of a negative difference as the size, by whether the size is 0
def mznlen(
  zero: Bool,
  +cat: U32,
  +mm: U32,
  hz: {U32.is_eq(cat, 0) == zero : Bool}
) -> {Nat.is_eq(List.length(&2, Bool, mzn(zero, cat, mm)), U32.to_nat(cat)) == True{} : Bool}:
  match zero:
    case True{}:
      ec = Equal.sym(U32, cat, 0, M1.ueq(cat, 0, hz))
      %ec : {Nat.is_eq(0n, U32.to_nat(_)) == True{} : Bool}
      {==}
    case False{}:
      +kn = U32.to_nat(cat)
      +mg = ((U32.shln(1, kn) - 1 : U32) - mm : U32)
      el = Equal.sym(Nat, List.length(&2, Bool, L1.jpg.cb(kn, mg)), kn, len_cb(kn, mg))
      %el : {Nat.is_eq(_, kn) == True{} : Bool}
      M1.nat_eq_refl(kn)

# the DC book's code for a size, then the magnitude bits of a difference
def dcuse_eq(
  +cat: U32,
  +pp: Jenc.Put,
  +xx: U32
) -> {Jenc.encode.dc.use(Jenc.encode.sym(dcbk(), cat), pp, cat, xx) == (dcbk(), L1.jpg.feed(List.append(&2, Bool,
  code.dc(cat), mz(U32.is_eq(cat, 0), cat, xx)), pp)) : Array<U32> & Jenc.Put}:
  +vv = D1.jpg.val(Array.get(U32, dcbk(), cat))
  +cd = code.dc(cat)
  +mb = mz(U32.is_eq(cat, 0), cat, xx)
  Equal.trans(Array<U32> & Jenc.Put, Jenc.encode.dc.use(Jenc.encode.coded(Array.get(U32, dcbk(), cat)), pp, cat, xx),
    Jenc.encode.dc.use(Jenc.encode.coded((dcbk(), vv)), pp, cat, xx), (dcbk(), L1.jpg.feed(List.append(&2, Bool, cd,
    mb), pp)), Equal.cong(Array<U32> & U32, Array<U32> & Jenc.Put, gg => Jenc.encode.dc.use(Jenc.encode.coded(gg), pp,
    cat, xx), Array.get(U32, dcbk(), cat), (dcbk(), vv), get.eq(dcbk(), cat)), Equal.cong(Jenc.Put,
    Array<U32> & Jenc.Put, qq => (dcbk(), qq), Jenc.encode.magp.z(U32.is_eq(cat, 0), Jenc.encode.bits.go(
    U32.to_nat(U32.shrn(vv, 16n)), pp, U32.and(vv, 65535)), cat, xx), L1.jpg.feed(List.append(&2, Bool, cd, mb), pp),
    Equal.trans(Jenc.Put, Jenc.encode.magp.z(U32.is_eq(cat, 0), Jenc.encode.bits.go(U32.to_nat(U32.shrn(vv, 16n)), pp,
    U32.and(vv, 65535)), cat, xx), Jenc.encode.magp.z(U32.is_eq(cat, 0), L1.jpg.feed(cd, pp), cat, xx), L1.jpg.feed(
    List.append(&2, Bool, cd, mb), pp), Equal.cong(Jenc.Put, Jenc.Put, qq => Jenc.encode.magp.z(U32.is_eq(cat, 0), qq,
    cat, xx), Jenc.encode.bits.go(U32.to_nat(U32.shrn(vv, 16n)), pp, U32.and(vv, 65535)), L1.jpg.feed(cd, pp),
    bits_go(U32.to_nat(U32.shrn(vv, 16n)), pp, U32.and(vv, 65535))), Equal.trans(Jenc.Put, Jenc.encode.magp.z(
    U32.is_eq(cat, 0), L1.jpg.feed(cd, pp), cat, xx), L1.jpg.feed(mb, L1.jpg.feed(cd, pp)),
      L1.jpg.feed(List.append(&2, Bool, cd, mb),
    pp), magp_eq(U32.is_eq(cat, 0), L1.jpg.feed(cd, pp), cat, xx), Equal.sym(Jenc.Put, L1.jpg.feed(List.append(&2,
      Bool, cd,
    mb), pp), L1.jpg.feed(mb, L1.jpg.feed(cd, pp)), feed_app(cd, mb, pp))))))

# the DC book's code for a size, then the magnitude bits of a negative difference
def dcneg_eq(
  +cat: U32,
  +pp: Jenc.Put,
  +mm: U32
) -> {Jenc.encode.dc.use.neg(Jenc.encode.sym(dcbk(), cat), pp, cat, mm) == (dcbk(), L1.jpg.feed(List.append(&2,
  Bool, code.dc(cat), mzn(U32.is_eq(cat, 0), cat, mm)), pp)) : Array<U32> & Jenc.Put}:
  +vv = D1.jpg.val(Array.get(U32, dcbk(), cat))
  +cd = code.dc(cat)
  +mb = mzn(U32.is_eq(cat, 0), cat, mm)
  Equal.trans(Array<U32> & Jenc.Put, Jenc.encode.dc.use.neg(Jenc.encode.coded(Array.get(U32, dcbk(), cat)), pp, cat,
    mm), Jenc.encode.dc.use.neg(Jenc.encode.coded((dcbk(), vv)), pp, cat, mm), (dcbk(), L1.jpg.feed(List.append(&2,
    Bool, cd, mb), pp)), Equal.cong(Array<U32> & U32, Array<U32> & Jenc.Put, gg => Jenc.encode.dc.use.neg(
    Jenc.encode.coded(gg), pp, cat, mm), Array.get(U32, dcbk(), cat), (dcbk(), vv), get.eq(dcbk(), cat)),
    Equal.cong(Jenc.Put, Array<U32> & Jenc.Put, qq => (dcbk(), qq), Jenc.encode.magp.n(U32.is_eq(cat, 0),
    Jenc.encode.bits.go(U32.to_nat(U32.shrn(vv, 16n)), pp, U32.and(vv, 65535)), cat, mm),
      L1.jpg.feed(List.append(&2, Bool,
    cd, mb), pp), Equal.trans(Jenc.Put, Jenc.encode.magp.n(U32.is_eq(cat, 0), Jenc.encode.bits.go(U32.to_nat(
    U32.shrn(vv, 16n)), pp, U32.and(vv, 65535)), cat, mm), Jenc.encode.magp.n(U32.is_eq(cat, 0), L1.jpg.feed(cd,
      pp), cat,
    mm), L1.jpg.feed(List.append(&2, Bool, cd, mb), pp), Equal.cong(Jenc.Put, Jenc.Put, qq => Jenc.encode.magp.n(
    U32.is_eq(cat, 0), qq, cat, mm), Jenc.encode.bits.go(U32.to_nat(U32.shrn(vv, 16n)), pp, U32.and(vv, 65535)),
    L1.jpg.feed(cd, pp), bits_go(U32.to_nat(U32.shrn(vv, 16n)), pp, U32.and(vv, 65535))), Equal.trans(Jenc.Put,
    Jenc.encode.magp.n(U32.is_eq(cat, 0), L1.jpg.feed(cd, pp), cat, mm), L1.jpg.feed(mb, L1.jpg.feed(cd, pp)),
      L1.jpg.feed(
    List.append(&2, Bool, cd, mb), pp), magn_eq(U32.is_eq(cat, 0), L1.jpg.feed(cd, pp), cat, mm), Equal.sym(Jenc.Put,
    L1.jpg.feed(List.append(&2, Bool, cd, mb), pp), L1.jpg.feed(mb, L1.jpg.feed(cd, pp)), feed_app(cd, mb,
      pp))))))

# the DC part of a block: a size of the DC table, its code and as many magnitude bits, fed to the writer
def DcRes(+bb: U32, +pb: U32, +pp: Jenc.Put) -> Type:
  &dcs: U32 -> &dcx: List<&2, Bool> -> &_e: {Jenc.encode.dcdiff(dcbk(), pp, bb, pb) == (dcbk(), L1.jpg.feed(
    List.append(&2, Bool, code.dc(dcs), dcx), pp)) : Array<U32> & Jenc.Put} -> &_h: {L1.jpg.memb(dcs,
    Jenc.encode.dcsyms()) == True{} : Bool} -> {Nat.is_eq(List.length(&2, Bool, dcx), U32.to_nat(dcs)) == True{} :
    Bool}

# the DC part of a block, by the difference's sign
def dcres.b(
  up: Bool,
  +bb: U32,
  +pb: U32,
  +pp: Jenc.Put,
  hb: {U32.is_lt(bb, 2048) == True{} : Bool},
  hp: {U32.is_lt(pb, 2048) == True{} : Bool},
  hg: {U32.is_ge(bb, pb) == up : Bool}
) -> {Jenc.encode.dcdiff.b(up, dcbk(), pp, bb, pb) == Jenc.encode.dcdiff(dcbk(), pp, bb,
  pb) : Array<U32> & Jenc.Put} -> DcRes(bb, pb, pp):
  match up:
    case True{}:
      +xx = (bb - pb : U32)
      +cat = Jenc.encode.cat(xx)
      +hx = {up_lt(bb, pb, hb, hg) : {U32.is_lt(xx, 2048) == True{} : Bool}}
      ed => (cat, mz(U32.is_eq(cat, 0), cat, xx), Equal.trans(Array<U32> & Jenc.Put, Jenc.encode.dcdiff(dcbk(),
        pp, bb, pb), Jenc.encode.dc.use(Jenc.encode.sym(dcbk(), cat), pp, cat, xx), (dcbk(), L1.jpg.feed(
        List.append(&2, Bool, code.dc(cat), mz(U32.is_eq(cat, 0), cat, xx)), pp)), Equal.sym(Array<U32> &
        Jenc.Put, Jenc.encode.dcdiff.b(True{}, dcbk(), pp, bb, pb), Jenc.encode.dcdiff(dcbk(), pp, bb, pb), ed),
        dcuse_eq(cat, pp, xx)), memcat.dc(xx, Equal.trans(Bool, U32.is_lt(Jpeg.decode.abs(xx), 2048),
        U32.is_lt(xx, 2048), True{}, Equal.cong(U32, Bool, uu => U32.is_lt(uu, 2048), Jpeg.decode.abs(xx), xx,
        abs_small(xx, hx)), hx)), mzlen(U32.is_eq(cat, 0), cat, xx, {==}))
    case False{}:
      +mm = (pb - bb : U32)
      +cat = Jenc.encode.cat(mm)
      +hm = {down_lt(bb, pb, hp, hg) : {U32.is_lt(mm, 2048) == True{} : Bool}}
      ed => (cat, mzn(U32.is_eq(cat, 0), cat, mm), Equal.trans(Array<U32> & Jenc.Put, Jenc.encode.dcdiff(dcbk(), pp,
        bb, pb), Jenc.encode.dc.use.neg(Jenc.encode.sym(dcbk(), cat), pp, cat, mm), (dcbk(), L1.jpg.feed(
        List.append(&2, Bool, code.dc(cat), mzn(U32.is_eq(cat, 0), cat, mm)), pp)), Equal.sym(Array<U32> &
        Jenc.Put, Jenc.encode.dcdiff.b(False{}, dcbk(), pp, bb, pb), Jenc.encode.dcdiff(dcbk(), pp, bb, pb), ed),
        dcneg_eq(cat, pp, mm)), memcat.dc(mm, Equal.trans(Bool, U32.is_lt(Jpeg.decode.abs(mm), 2048),
        U32.is_lt(mm, 2048), True{}, Equal.cong(U32, Bool, uu => U32.is_lt(uu, 2048), Jpeg.decode.abs(mm), mm,
        abs_small(mm, hm)), hm)), mznlen(U32.is_eq(cat, 0), cat, mm, {==}))

# the DC part of a block from two biased DCs below 2048
def dcres(
  +bb: U32,
  +pb: U32,
  +pp: Jenc.Put,
  hb: {U32.is_lt(bb, 2048) == True{} : Bool},
  hp: {U32.is_lt(pb, 2048) == True{} : Bool}
) -> DcRes(bb, pb, pp):
  dcres.b(U32.is_ge(bb, pb), bb, pb, pp, hb, hp, {==}, {==})

# both answers when the first holds are the second
def also_t(ok: Bool, -rest: Bool, hh: {ok == True{} : Bool}) -> {L1.jpg.also(ok, rest) == rest : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({L1.jpg.also(False{}, rest) == rest : Bool}, M1.huf.false_true(hh))

# two that hold
def and_tt(
  aa: Bool,
  -bb: Bool,
  ha: {aa == True{} : Bool},
  hb: {bb == True{} : Bool}
) -> {Bool.and(aa, bb) == True{} : Bool}:
  match aa:
    case True{}:
      hb
    case False{}:
      Empty.absurd({Bool.and(False{}, bb) == True{} : Bool}, M1.huf.false_true(ha))

# either, when the first holds
def or_tl(aa: Bool, -bb: Bool, ha: {aa == True{} : Bool}) -> {Bool.or(aa, bb) == True{} : Bool}:
  match aa:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Bool.or(False{}, bb) == True{} : Bool}, M1.huf.false_true(ha))

# not of one that fails
def not_f(aa: Bool, ha: {aa == False{} : Bool}) -> {Bool.not(aa) == True{} : Bool}:
  match aa:
    case True{}:
      Empty.absurd({Bool.not(True{}) == True{} : Bool}, jenc.true_false(ha))
    case False{}:
      {==}

# below is not equal
def lt_ne(xx: Nat, nn: Nat, hh: {Nat.is_lt(xx, nn) == True{} : Bool}) -> {Nat.is_eq(xx, nn) == False{} : Bool}:
  match xx nn:
    case 0n 0n:
      Empty.absurd({Nat.is_eq(0n, 0n) == False{} : Bool}, M1.huf.false_true(hh))
    case 0n 1n+_q:
      {==}
    case 1n+_p 0n:
      {==}
    case 1n+ +pp 1n+ +qq:
      lt_ne(pp, qq, hh)

# below is not at least
def lt_nle(xx: Nat, nn: Nat, hh: {Nat.is_lt(xx, nn) == True{} : Bool}) -> {Nat.is_le(nn, xx) == False{} : Bool}:
  match xx nn:
    case 0n 0n:
      Empty.absurd({Nat.is_le(0n, 0n) == False{} : Bool}, M1.huf.false_true(hh))
    case 0n 1n+_q:
      {==}
    case 1n+_p 0n:
      Empty.absurd({Nat.is_le(0n, 1n+_p) == False{} : Bool}, M1.huf.false_true(hh))
    case 1n+ +pp 1n+ +qq:
      lt_nle(pp, qq, hh)

# adding a positive number makes more
def lt_add_pos(
  xx: Nat,
  +rr: Nat,
  hh: {Nat.is_lt(0n, rr) == True{} : Bool}
) -> {Nat.is_lt(xx, Nat.add(xx, rr)) == True{} : Bool}:
  match xx:
    case 0n:
      hh
    case 1n+ +pp:
      lt_add_pos(pp, rr, hh)

# above 0 is at least 1
def gt0(rr: Nat, hh: {Cmp.is_gt(Nat.cmp(rr, 0n)) == True{} : Bool}) -> {Nat.is_lt(0n, rr) == True{} : Bool}:
  match rr:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, M1.huf.false_true(hh))
    case 1n+_p:
      {==}

# not above 0 is 0
def ngt0(rr: Nat, hh: {Cmp.is_gt(Nat.cmp(rr, 0n)) == False{} : Bool}) -> {rr == 0n : Nat}:
  match rr:
    case 0n:
      {==}
    case 1n+_p:
      Empty.absurd({1n+_p == 0n : Nat}, jenc.true_false(hh))

# a number is at most its double
def le_double(nn: Nat) -> {Nat.is_le(nn, Nat.double(nn)) == True{} : Bool}:
  match nn:
    case 0n:
      {==}
    case 1n+ +pp:
      M1.le_trans(pp, Nat.double(pp), 1n+Nat.double(pp), le_double(pp), M2.le_succ(Nat.double(pp)))

# a number is at most sixteen times it
def le_sixteen(+nn: Nat) -> {Nat.is_le(nn, M1.sixteen(nn)) == True{} : Bool}:
  +d1 = Nat.double(nn)
  +d2 = Nat.double(d1)
  +d3 = Nat.double(d2)
  M1.le_trans(nn, d1, M1.sixteen(nn), le_double(nn), M1.le_trans(d1, d2, M1.sixteen(nn), le_double(d1), M1.le_trans(d2,
      d3,
    M1.sixteen(nn), le_double(d2), le_double(d3))))

# one less than a bound above j is a bound for j
def le_npred(
  jj: Nat,
  ll: Nat,
  hh: {Nat.is_le(1n+jj, ll) == True{} : Bool}
) -> {Nat.is_le(jj, L1.jpg.npred(ll)) == True{} : Bool}:
  match ll:
    case 0n:
      Empty.absurd({Nat.is_le(jj, 0n) == True{} : Bool}, M1.huf.false_true(hh))
    case 1n+_q:
      hh

# a bound above j is above 0
def pos_of_le(jj: Nat, ll: Nat, hh: {Nat.is_le(1n+jj, ll) == True{} : Bool}) -> {Nat.is_lt(0n, ll) == True{} : Bool}:
  match ll:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, M1.huf.false_true(hh))
    case 1n+_q:
      {==}

# the lookups left after j tokens
def npreds(jj: Nat, ll: Nat) -> Nat:
  match jj:
    case 0n:
      ll
    case 1n+ +pp:
      npreds(pp, L1.jpg.npred(ll))

# a bound of j + m leaves m after j tokens
def npl(
  jj: Nat,
  +mm: Nat,
  +ll: Nat,
  hh: {Nat.is_le(Nat.add(jj, mm), ll) == True{} : Bool}
) -> {Nat.is_le(mm, npreds(jj, ll)) == True{} : Bool}:
  match jj:
    case 0n:
      hh
    case 1n+ +pp:
      npl(pp, mm, L1.jpg.npred(ll), le_npred(Nat.add(pp, mm), ll, hh))

# a U32 sum whose Nat sum is at most 64 is the Nat sum
def uadd(
  +aa: U32,
  +bb: U32,
  hh: {Nat.is_le(Nat.add(U32.to_nat(aa), U32.to_nat(bb)), 64n) == True{} : Bool}
) -> {U32.to_nat((aa + bb : U32)) == Nat.add(U32.to_nat(aa), U32.to_nat(bb)) : Nat}:
  M3.u32_add_below(aa, bb, 64, hh)

# the index after j ZRLs, as a Nat, while it stays below 64
def kz_nat(
  jj: Nat,
  +kk: U32,
  hh: {Nat.is_lt(Nat.add(U32.to_nat(kk), M1.sixteen(jj)), 64n) == True{} : Bool}
) -> {U32.to_nat(M2.kz(jj, kk)) == Nat.add(U32.to_nat(kk), M1.sixteen(jj)) : Nat}:
  match jj:
    case 0n:
      Equal.sym(Nat, Nat.add(U32.to_nat(kk), 0n), U32.to_nat(kk), M1.ras.add_zero(U32.to_nat(kk)))
    case 1n+ +pp:
      +kn = U32.to_nat(kk)
      +sp = M1.sixteen(pp)
      +ea = {M1.ras.add_assoc(kn, 16n, sp) : {Nat.add(Nat.add(kn, 16n), sp) == Nat.add(kn, 16n+sp) : Nat}}
      +hs = {Equal.trans(Bool, Nat.is_lt(Nat.add(Nat.add(kn, 16n), sp), 64n), Nat.is_lt(Nat.add(kn, 16n+sp), 64n),
        True{},
        Equal.cong(Nat, Bool, nn => Nat.is_lt(nn, 64n), Nat.add(Nat.add(kn, 16n), sp), Nat.add(kn, 16n+sp), ea), hh) :
        {Nat.is_lt(Nat.add(Nat.add(kn, 16n), sp), 64n) == True{} : Bool}}
      +e16 = {uadd(kk, 16, M3.le_add_r(Nat.add(kn, 16n), sp, 64n, M1.lt_le(Nat.add(Nat.add(kn, 16n), sp), 64n, hs))) :
        {U32.to_nat((kk + 16 : U32)) == Nat.add(kn, 16n) : Nat}}
      +h2 = {Equal.trans(Bool, Nat.is_lt(Nat.add(U32.to_nat((kk + 16 : U32)), sp), 64n), Nat.is_lt(Nat.add(Nat.add(kn,
        16n), sp), 64n), True{}, Equal.cong(Nat, Bool, nn => Nat.is_lt(Nat.add(nn, sp), 64n), U32.to_nat((kk + 16 :
        U32)), Nat.add(kn, 16n), e16), hs) : {Nat.is_lt(Nat.add(U32.to_nat((kk + 16 : U32)), sp), 64n) == True{} :
        Bool}}
      Equal.trans(Nat, U32.to_nat(M2.kz(pp, (kk + 16 : U32))), Nat.add(U32.to_nat((kk + 16 : U32)), sp), Nat.add(kn,
        16n+sp), kz_nat(pp, (kk + 16 : U32), h2), Equal.trans(Nat, Nat.add(U32.to_nat((kk + 16 : U32)), sp),
        Nat.add(Nat.add(kn, 16n), sp), Nat.add(kn, 16n+sp), Equal.cong(Nat, Nat, nn => Nat.add(nn, sp), U32.to_nat((kk +
        16 : U32)), Nat.add(kn, 16n), e16), ea))

# a ZRL token is read at an index at most 48 with a lookup left, and moves the index on by 16
def zrl_ok(
  +kk: U32,
  +left: Nat,
  hz: {Nat.is_lt(0n, left) == True{} : Bool},
  hq: {U32.is_lt((kk + 16 : U32), 64) == True{} : Bool}
) -> {L1.jpg.acok(L1.JTok{240, []}, L1.JAcSt{kk, left, False{}}) == True{} : Bool}:
  and_tt(Nat.is_lt(0n, left), Bool.or(U32.is_lt((kk + 16 : U32), 64), U32.is_eq((kk + 16 : U32), 64)), hz,
    or_tl(U32.is_lt((kk + 16 : U32), 64), U32.is_eq((kk + 16 : U32), 64), hq))

# j ZRL tokens before more are read in full as the more are from the index 16j on
def zrlwf(
  jj: Nat,
  +kk: U32,
  +left: Nat,
  +rest: List<&2, L1.JTok>,
  hk: {Nat.is_lt(Nat.add(U32.to_nat(kk), M1.sixteen(jj)), 64n) == True{} : Bool},
  +hl: {Nat.is_le(jj, left) == True{} : Bool}
) -> {L1.jpg.acwf(List.append(&2, L1.JTok, zrltoks(jj), rest), L1.JAcSt{kk, left,
  False{}}) == L1.jpg.acwf(rest, L1.JAcSt{M2.kz(jj, kk), npreds(jj, left), False{}}) : Bool}:
  match jj:
    case 0n:
      {==}
    case 1n+ +pp:
      +kn = U32.to_nat(kk)
      +sp = M1.sixteen(pp)
      +tl = List.append(&2, L1.JTok, zrltoks(pp), rest)
      +ea = {M1.ras.add_assoc(kn, 16n, sp) : {Nat.add(Nat.add(kn, 16n), sp) == Nat.add(kn, 16n+sp) : Nat}}
      +hs = {Equal.trans(Bool, Nat.is_lt(Nat.add(Nat.add(kn, 16n), sp), 64n), Nat.is_lt(Nat.add(kn, 16n+sp), 64n),
        True{},
        Equal.cong(Nat, Bool, nn => Nat.is_lt(nn, 64n), Nat.add(Nat.add(kn, 16n), sp), Nat.add(kn, 16n+sp), ea), hk) :
        {Nat.is_lt(Nat.add(Nat.add(kn, 16n), sp), 64n) == True{} : Bool}}
      +e16 = {uadd(kk, 16, M3.le_add_r(Nat.add(kn, 16n), sp, 64n, M1.lt_le(Nat.add(Nat.add(kn, 16n), sp), 64n, hs))) :
        {U32.to_nat((kk + 16 : U32)) == Nat.add(kn, 16n) : Nat}}
      +h2 = {Equal.trans(Bool, Nat.is_lt(Nat.add(U32.to_nat((kk + 16 : U32)), sp), 64n), Nat.is_lt(Nat.add(Nat.add(kn,
        16n), sp), 64n), True{}, Equal.cong(Nat, Bool, nn => Nat.is_lt(Nat.add(nn, sp), 64n), U32.to_nat((kk + 16 :
        U32)), Nat.add(kn, 16n), e16), hs) : {Nat.is_lt(Nat.add(U32.to_nat((kk + 16 : U32)), sp), 64n) == True{} :
        Bool}}
      +hq = {n_ult((kk + 16 : U32), 64, M1.le_lt_trans(U32.to_nat((kk + 16 : U32)), Nat.add(U32.to_nat((kk + 16 :
        U32)), sp), 64n, M2.le_add_more(U32.to_nat((kk + 16 : U32)), U32.to_nat((kk + 16 : U32)), sp, M1.le_refl(
        U32.to_nat((kk + 16 : U32)))), h2)) : {U32.is_lt((kk + 16 : U32), 64) == True{} : Bool}}
      +tk = {L1.JTok{240, []} : L1.JTok}
      +st = {L1.JAcSt{kk, left, False{}} : L1.JAcSt}
      +en = {Equal.cong(Bool, L1.JAcSt, bb => L1.JAcSt{(kk + 16 : U32), L1.jpg.npred(left), Bool.not(bb)},
        U32.is_lt((kk + 16 :
        U32), 64), True{}, hq) : {L1.jpg.acnx(tk, st) == L1.JAcSt{(kk + 16 : U32), L1.jpg.npred(left),
          False{}} : L1.JAcSt}}
      Equal.trans(Bool, L1.jpg.also(L1.jpg.acok(tk, st), L1.jpg.acwf(tl, L1.jpg.acnx(tk, st))),
        L1.jpg.acwf(tl, L1.jpg.acnx(tk, st)),
        L1.jpg.acwf(rest, L1.JAcSt{M2.kz(pp, (kk + 16 : U32)), npreds(pp, L1.jpg.npred(left)), False{}}),
          also_t(L1.jpg.acok(tk, st),
        L1.jpg.acwf(tl, L1.jpg.acnx(tk, st)), zrl_ok(kk, left, pos_of_le(pp, left, hl), hq)), Equal.trans(Bool,
          L1.jpg.acwf(tl,
        L1.jpg.acnx(tk, st)), L1.jpg.acwf(tl, L1.JAcSt{(kk + 16 : U32), L1.jpg.npred(left), False{}}),
          L1.jpg.acwf(rest, L1.JAcSt{M2.kz(pp, (kk +
        16 : U32)), npreds(pp, L1.jpg.npred(left)), False{}}), Equal.cong(L1.JAcSt, Bool, ss => L1.jpg.acwf(tl,
          ss), L1.jpg.acnx(tk,
        st), L1.JAcSt{(kk + 16 : U32), L1.jpg.npred(left), False{}}, en), zrlwf(pp, (kk + 16 : U32),
          L1.jpg.npred(left), rest, h2,
        le_npred(pp, left, hl))))

# c is at most y + c
def le_add_left(yy: Nat, +cc: Nat) -> {Nat.is_le(cc, Nat.add(yy, cc)) == True{} : Bool}:
  match yy:
    case 0n:
      M1.le_refl(cc)
    case 1n+ +pp:
      M1.le_trans(cc, Nat.add(pp, cc), 1n+Nat.add(pp, cc), le_add_left(pp, cc), M2.le_succ(Nat.add(pp, cc)))

# adding the same on the right keeps at most
def le_addr(
  xx: Nat,
  yy: Nat,
  +cc: Nat,
  hh: {Nat.is_le(xx, yy) == True{} : Bool}
) -> {Nat.is_le(Nat.add(xx, cc), Nat.add(yy, cc)) == True{} : Bool}:
  match xx yy:
    case 0n _y:
      le_add_left(_y, cc)
    case 1n+_p 0n:
      Empty.absurd({Nat.is_le(Nat.add(1n+_p, cc), Nat.add(0n, cc)) == True{} : Bool}, M1.huf.false_true(hh))
    case 1n+pp 1n+qq:
      le_addr(pp, qq, cc, hh)

# not of one that holds fails
def not_t(aa: Bool, ha: {Bool.not(aa) == True{} : Bool}) -> {aa == False{} : Bool}:
  match aa:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, M1.huf.false_true(ha))
    case False{}:
      {==}

# an AC size, by whether it is 0
def memb_nz.b(
  zz: Bool,
  +xx: U32,
  hz: {U32.is_eq(xx, 0) == zz : Bool},
  hm: {L1.jpg.memb(xx, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]) == True{} : Bool}
) -> {U32.is_eq(xx, 0) == False{} : Bool}:
  match zz:
    case True{}:
      ex = Equal.sym(U32, xx, 0, M1.ueq(xx, 0, hz))
      Empty.absurd({U32.is_eq(xx, 0) == False{} : Bool}, M1.huf.false_true(Equal.trans(Bool, L1.jpg.memb(0, [1, 2, 3,
        4, 5, 6,
        7, 8, 9, 10]), L1.jpg.memb(xx, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]), True{}, Equal.cong(U32, Bool,
          uu => L1.jpg.memb(uu, [1,
        2, 3, 4, 5, 6, 7, 8, 9, 10]), 0, xx, ex), hm)))
    case False{}:
      hz

# a size from 1 to 10 is not 0
def memb_nz(
  +xx: U32,
  hm: {L1.jpg.memb(xx, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]) == True{} : Bool}
) -> {U32.is_eq(xx, 0) == False{} : Bool}:
  memb_nz.b(U32.is_eq(xx, 0), xx, {==}, hm)

# a run and size token's own check, when its symbol is neither EOB nor ZRL
def acokk(
  eob: Bool,
  zrl: Bool,
  +sym: U32,
  ex: List<&2, Bool>,
  +kk: U32,
  he: {eob == False{} : Bool},
  hz: {zrl == False{} : Bool},
  h1: {U32.is_eq(U32.and(15, sym), 0) == False{} : Bool},
  h2: {U32.is_ge((kk + U32.shrn(sym, 4n) : U32), 64) == False{} : Bool},
  h3: {Nat.is_eq(List.length(&2, Bool, ex), U32.to_nat(U32.and(15, sym))) == True{} : Bool}
) -> {L1.jpg.acok.k(eob, zrl, sym, ex, kk) == True{} : Bool}:
  match eob zrl:
    case True{} _z:
      Empty.absurd({L1.jpg.acok.k(True{}, _z, sym, ex, kk) == True{} : Bool}, jenc.true_false(he))
    case False{} True{}:
      Empty.absurd({L1.jpg.acok.k(False{}, True{}, sym, ex, kk) == True{} : Bool}, jenc.true_false(hz))
    case False{} False{}:
      and_tt(Bool.not(U32.is_eq(U32.and(15, sym), 0)), Bool.and(Bool.not(U32.is_ge((kk + U32.shrn(sym, 4n) : U32), 64)),
        Nat.is_eq(List.length(&2, Bool, ex), U32.to_nat(U32.and(15, sym)))), not_f(U32.is_eq(U32.and(15, sym), 0), h1),
        and_tt(Bool.not(U32.is_ge((kk + U32.shrn(sym, 4n) : U32), 64)), Nat.is_eq(List.length(&2, Bool, ex),
        U32.to_nat(U32.and(15, sym))), not_f(U32.is_ge((kk + U32.shrn(sym, 4n) : U32), 64), h2), h3))

# the state after a run and size token
def acnxk(
  eob: Bool,
  zrl: Bool,
  +sym: U32,
  +kk: U32,
  +left: Nat,
  he: {eob == False{} : Bool},
  hz: {zrl == False{} : Bool}
) -> {L1.jpg.acnx.k(eob, zrl, sym, kk, left) == L1.JAcSt{((kk + U32.shrn(sym, 4n) : U32) + 1 : U32),
  L1.jpg.npred(left), U32.is_eq(((kk + U32.shrn(sym, 4n) : U32) + 1 : U32), 64)} : L1.JAcSt}:
  match eob zrl:
    case True{} _z:
      Empty.absurd({L1.jpg.acnx.k(True{}, _z, sym, kk, left) == L1.JAcSt{((kk + U32.shrn(sym, 4n) : U32) + 1 : U32),
        L1.jpg.npred(left), U32.is_eq(((kk + U32.shrn(sym, 4n) : U32) + 1 : U32), 64)} : L1.JAcSt}, jenc.true_false(he))
    case False{} True{}:
      Empty.absurd({L1.jpg.acnx.k(False{}, True{}, sym, kk, left) == L1.JAcSt{((kk + U32.shrn(sym,
        4n) : U32) + 1 : U32),
        L1.jpg.npred(left), U32.is_eq(((kk + U32.shrn(sym, 4n) : U32) + 1 : U32), 64)} : L1.JAcSt}, jenc.true_false(hz))
    case False{} False{}:
      {==}

# a run and size token, then more, read from a state that has not ended
def symwf(
  +sym: U32,
  +ex: List<&2, Bool>,
  +kk: U32,
  +left: Nat,
  +ts: List<&2, L1.JTok>,
  +he: {U32.is_eq(sym, 0) == False{} : Bool},
  +hz: {U32.is_eq(sym, 240) == False{} : Bool},
  hm: {L1.jpg.memb(sym, Jenc.encode.acsyms()) == True{} : Bool},
  hp: {Nat.is_lt(0n, left) == True{} : Bool},
  h1: {U32.is_eq(U32.and(15, sym), 0) == False{} : Bool},
  h2: {U32.is_ge((kk + U32.shrn(sym, 4n) : U32), 64) == False{} : Bool},
  h3: {Nat.is_eq(List.length(&2, Bool, ex), U32.to_nat(U32.and(15, sym))) == True{} : Bool}
) -> {L1.jpg.acwf(L1.JTok{sym, ex} <> ts, L1.JAcSt{kk, left, False{}}) == L1.jpg.acwf(ts,
  L1.JAcSt{((kk + U32.shrn(sym, 4n) : U32) + 1 : U32), L1.jpg.npred(left), U32.is_eq(((kk + U32.shrn(sym,
  4n) : U32) + 1 : U32), 64)}) : Bool}:
  +tk = {L1.JTok{sym, ex} : L1.JTok}
  +st = {L1.JAcSt{kk, left, False{}} : L1.JAcSt}
  +n2 = ((kk + U32.shrn(sym, 4n) : U32) + 1 : U32)
  +ok = {and_tt(Nat.is_lt(0n, left), Bool.and(L1.jpg.memb(sym, Jenc.encode.acsyms()), L1.jpg.acok.k(U32.is_eq(sym,
    0),
    U32.is_eq(sym, 240), sym, ex, kk)), hp, and_tt(L1.jpg.memb(sym, Jenc.encode.acsyms()),
      L1.jpg.acok.k(U32.is_eq(sym, 0),
    U32.is_eq(sym, 240), sym, ex, kk), hm, acokk(U32.is_eq(sym, 0), U32.is_eq(sym, 240), sym, ex, kk, he, hz, h1, h2,
    h3))) : {L1.jpg.acok(tk, st) == True{} : Bool}}
  Equal.trans(Bool, L1.jpg.also(L1.jpg.acok(tk, st), L1.jpg.acwf(ts, L1.jpg.acnx(tk, st))), L1.jpg.acwf(ts,
    L1.jpg.acnx(tk, st)), L1.jpg.acwf(ts,
    L1.JAcSt{n2, L1.jpg.npred(left), U32.is_eq(n2, 64)}), also_t(L1.jpg.acok(tk, st), L1.jpg.acwf(ts,
      L1.jpg.acnx(tk, st)), ok),
    Equal.cong(L1.JAcSt, Bool, ss => L1.jpg.acwf(ts, ss), L1.jpg.acnx(tk, st), L1.JAcSt{n2,
      L1.jpg.npred(left), U32.is_eq(n2, 64)},
    acnxk(U32.is_eq(sym, 0), U32.is_eq(sym, 240), sym, kk, left, he, hz)))

# below n is n at most after adding 1
def lt_add1(
  aa: Nat,
  nn: Nat,
  hh: {Nat.is_lt(aa, nn) == True{} : Bool}
) -> {Nat.is_le(Nat.add(aa, 1n), nn) == True{} : Bool}:
  match aa nn:
    case 0n 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, M1.huf.false_true(hh))
    case 0n 1n+qq:
      M1.le_zero(qq)
    case 1n+_p 0n:
      Empty.absurd({Nat.is_le(Nat.add(1n+_p, 1n), 0n) == True{} : Bool}, M1.huf.false_true(hh))
    case 1n+pp 1n+qq:
      lt_add1(pp, qq, hh)

# AC tokens joined, their lists regrouped
def app_t(
  xs: List<&2, L1.JTok>,
  +ys: List<&2, L1.JTok>,
  +zs: List<&2, L1.JTok>
) -> {List.append(&2, L1.JTok, List.append(&2, L1.JTok, xs, ys), zs) == List.append(&2, L1.JTok, xs,
  List.append(&2, L1.JTok, ys, zs)) : List<&2, L1.JTok>}:
  match xs:
    case Nil{}:
      {==}
    case +hh <> tt:
      Equal.cong(List<&2, L1.JTok>, List<&2, L1.JTok>, ws => hh <> ws, List.append(&2, L1.JTok, List.append(&2,
        L1.JTok, tt,
        ys), zs), List.append(&2, L1.JTok, tt, List.append(&2, L1.JTok, ys, zs)), app_t(tt, ys, zs))

# the AC coder from a state: tokens it writes to the writer, read in full by the decoder's loop from the matching
# state
def AclRes(-zz: List<&2, U32>, +run: U32, +kk: U32, +left: Nat, +pp: Jenc.Put) -> Type:
  &ts: List<&2, L1.JTok> -> &_e: {Jenc.encode.ac(zz, run, (acbk(), pp)) == (acbk(), L1.jpg.feed(acbits(ts),
    pp)) :
    Array<U32> & Jenc.Put} -> {L1.jpg.acwf(ts, L1.JAcSt{kk, left, U32.is_eq(kk, 64)}) == True{} : Bool}

# the AC coder's positions: the decoder's index, the zero run, and the coefficients left make 64
def AclPos(+kk: U32, +run: U32, -zz: List<&2, U32>) -> Type:
  {Nat.add(U32.to_nat(kk), Nat.add(U32.to_nat(run), List.length(&2, U32, zz))) == 64n : Nat}

# the lookups left cover the zero run and the coefficients left
def AclLeft(+run: U32, -zz: List<&2, U32>, +left: Nat) -> Type:
  {Nat.is_le(Nat.add(U32.to_nat(run), List.length(&2, U32, zz)), left) == True{} : Bool}

# the AC coder on the rest of the coefficients, from any state that keeps the invariant
def AclIh(-ct: List<&2, U32>) -> Type:
  @r2: U32 -> @k2: U32 -> @l2: Nat -> @p2: Jenc.Put -> @e2: AclPos(k2, r2, ct) -> @h2: AclLeft(r2, ct, l2) ->
    AclRes(ct, r2, k2, l2, p2)

# a U32 above 0, as a Nat compare
def ugt0(
  +run: U32,
  gz: Bool,
  hg: {U32.is_gt(run, 0) == gz : Bool}
) -> {Cmp.is_gt(Nat.cmp(U32.to_nat(run), 0n)) == gz : Bool}:
  Equal.trans(Bool, Cmp.is_gt(Nat.cmp(U32.to_nat(run), 0n)), U32.is_gt(run, 0), gz, Equal.cong(Cmp, Bool, cc =>
    Cmp.is_gt(cc), Nat.cmp(U32.to_nat(run), 0n), U32.cmp(run, 0), Equal.sym(Cmp, U32.cmp(run, 0), Nat.cmp(U32.to_nat(
    run), 0n), jenc.u_cmp(run, 0))), hg)

# the AC coder at the end of the coefficients, by whether a zero run is open
def acl_nil(
  gz: Bool,
  +run: U32,
  +kk: U32,
  +left: Nat,
  +pp: Jenc.Put,
  +hg: {U32.is_gt(run, 0) == gz : Bool},
  ee: AclPos(kk, run, []),
  hl: AclLeft(run, [], left)
) -> AclRes([], run, kk, left, pp):
  match gz:
    case True{}:
      +rn = U32.to_nat(run)
      +kn = U32.to_nat(kk)
      +hr = {gt0(rn, ugt0(run, True{}, hg)) : {Nat.is_lt(0n, rn) == True{} : Bool}}
      +ez = {M1.ras.add_zero(rn) : {Nat.add(rn, 0n) == rn : Nat}}
      +e1 = {Equal.trans(Nat, Nat.add(kn, rn), Nat.add(kn, Nat.add(rn, 0n)), 64n, Equal.cong(Nat, Nat, nn => Nat.add(kn,
        nn), rn, Nat.add(rn, 0n), Equal.sym(Nat, Nat.add(rn, 0n), rn, ez)), ee) : {Nat.add(kn, rn) == 64n : Nat}}
      +hk = {Equal.trans(Bool, Nat.is_lt(kn, 64n), Nat.is_lt(kn, Nat.add(kn, rn)), True{}, Equal.cong(Nat, Bool, nn =>
        Nat.is_lt(kn, nn), 64n, Nat.add(kn, rn), Equal.sym(Nat, Nat.add(kn, rn), 64n, e1)), lt_add_pos(kn, rn, hr)) :
        {Nat.is_lt(kn, 64n) == True{} : Bool}}
      +he = {Equal.trans(Bool, U32.is_eq(kk, 64), Nat.is_eq(kn, 64n), False{}, M1.u32_eq(kk, 64), lt_ne(kn, 64n, hk)) :
        {U32.is_eq(kk, 64) == False{} : Bool}}
      +hp = {M1.lt_le_trans(0n, rn, left, hr, Equal.trans(Bool, Nat.is_le(rn, left), Nat.is_le(Nat.add(rn, 0n), left),
        True{}, Equal.cong(Nat, Bool, nn => Nat.is_le(nn, left), rn, Nat.add(rn, 0n), Equal.sym(Nat, Nat.add(rn, 0n),
          rn,
        ez)), hl)) : {Nat.is_lt(0n, left) == True{} : Bool}}
      +tk = {L1.JTok{0, []} : L1.JTok}
      +st = {L1.JAcSt{kk, left, U32.is_eq(kk, 64)} : L1.JAcSt}
      +c0 = code.ac(0)
      +ok = {and_tt(Bool.not(U32.is_eq(kk, 64)), Bool.and(Nat.is_lt(0n, left), Bool.and(L1.jpg.memb(0,
        Jenc.encode.acsyms()), L1.jpg.acok.k(True{}, False{}, 0, [], kk))), not_f(U32.is_eq(kk, 64), he), and_tt(
        Nat.is_lt(0n, left), Bool.and(L1.jpg.memb(0, Jenc.encode.acsyms()), L1.jpg.acok.k(True{}, False{}, 0, [],
          kk)), hp,
        {==})) : {L1.jpg.acok(tk, st) == True{} : Bool}}
      ([tk], Equal.trans(Array<U32> & Jenc.Put, Jenc.encode.eob.on(U32.is_gt(run, 0), (acbk(), pp)),
        Jenc.encode.eob.on(True{}, (acbk(), pp)), (acbk(), L1.jpg.feed(acbits([tk]), pp)), Equal.cong(Bool,
        Array<U32> & Jenc.Put, gg => Jenc.encode.eob.on(gg, (acbk(), pp)), U32.is_gt(run, 0), True{}, hg),
        Equal.trans(Array<U32> & Jenc.Put, Jenc.encode.emit(Jenc.encode.sym(acbk(), 0), pp), (acbk(), L1.jpg.feed(c0,
        pp)), (acbk(), L1.jpg.feed(acbits([tk]), pp)), emitp.ac(0, pp), Equal.cong(List<&2, Bool>,
        Array<U32> & Jenc.Put, xs => (acbk(), L1.jpg.feed(xs, pp)), c0, List.append(&2, Bool, c0, []), Equal.sym(
        List<&2, Bool>, List.append(&2, Bool, c0, []), c0, huf.app_nil(c0))))), Equal.trans(Bool,
          L1.jpg.also(L1.jpg.acok(tk,
        st), L1.jpg.acwf([], L1.jpg.acnx(tk, st))), L1.jpg.acwf([], L1.jpg.acnx(tk, st)), True{},
          also_t(L1.jpg.acok(tk, st), L1.jpg.acwf([],
        L1.jpg.acnx(tk, st)), ok), {==}))
    case False{}:
      +rn = U32.to_nat(run)
      +kn = U32.to_nat(kk)
      +hr = {ngt0(rn, ugt0(run, False{}, hg)) : {rn == 0n : Nat}}
      +ek = {Equal.trans(Nat, kn, Nat.add(kn, 0n), 64n, Equal.sym(Nat, Nat.add(kn, 0n), kn, M1.ras.add_zero(kn)),
        Equal.trans(
        Nat, Nat.add(kn, 0n), Nat.add(kn, Nat.add(rn, 0n)), 64n, Equal.cong(Nat, Nat, nn => Nat.add(kn, Nat.add(nn,
          0n)),
        0n, rn, Equal.sym(Nat, rn, 0n, hr)), ee)) : {kn == 64n : Nat}}
      +he = {Equal.trans(Bool, U32.is_eq(kk, 64), Nat.is_eq(kn, 64n), True{}, M1.u32_eq(kk, 64), Equal.trans(Bool,
        Nat.is_eq(kn, 64n), Nat.is_eq(64n, 64n), True{}, Equal.cong(Nat, Bool, nn => Nat.is_eq(nn, 64n), kn, 64n, ek),
        {==})) : {U32.is_eq(kk, 64) == True{} : Bool}}
      ([], Equal.cong(Bool, Array<U32> & Jenc.Put, gg => Jenc.encode.eob.on(gg, (acbk(), pp)), U32.is_gt(run, 0),
        False{}, hg), he)

# the AC coder past a zero coefficient, from its run one longer
def acl_zero(
  +cc: U32,
  +ct: List<&2, U32>,
  +run: U32,
  +kk: U32,
  +left: Nat,
  +pp: Jenc.Put,
  hz: {U32.is_eq(cc, 0) == True{} : Bool},
  res: AclRes(ct, (run + 1 : U32), kk, left, pp)
) -> AclRes(cc <> ct, run, kk, left, pp):
  (ts, eq, wf) = res
  (ts, Equal.trans(Array<U32> & Jenc.Put, Jenc.encode.ac(ct, Jenc.encode.ac.run(U32.is_eq(cc, 0), run),
    Jenc.encode.ac.at(U32.is_eq(cc, 0), cc, run, (acbk(), pp))), Jenc.encode.ac(ct, (run + 1 : U32), (acbk(),
    pp)), (acbk(), L1.jpg.feed(acbits(ts), pp)), Equal.cong(Bool, Array<U32> & Jenc.Put, zz => Jenc.encode.ac(ct,
    Jenc.encode.ac.run(zz, run), Jenc.encode.ac.at(zz, cc, run, (acbk(), pp))), U32.is_eq(cc, 0), True{}, hz), eq),
    wf)

# the invariant one coefficient on, past a zero
def acl_zero_pos(
  +ct: List<&2, U32>,
  +run: U32,
  +kk: U32,
  +left: Nat,
  +ee: {Nat.add(U32.to_nat(kk), Nat.add(U32.to_nat(run), 1n+List.length(&2, U32, ct))) == 64n : Nat},
  _hl: {Nat.is_le(Nat.add(U32.to_nat(run), 1n+List.length(&2, U32, ct)), left) == True{} : Bool}
) -> AclPos(kk, (run + 1 : U32), ct):
  +kn = U32.to_nat(kk)
  +rn = U32.to_nat(run)
  +ll = List.length(&2, U32, ct)
  +a2 = {Equal.trans(Bool, Nat.is_le(Nat.add(rn, 1n+ll), 64n), Nat.is_le(Nat.add(rn, 1n+ll), Nat.add(kn, Nat.add(rn,
    1n+ll))), True{}, Equal.cong(Nat, Bool, nn => Nat.is_le(Nat.add(rn, 1n+ll), nn), 64n, Nat.add(kn, Nat.add(rn,
    1n+ll)), Equal.sym(Nat, Nat.add(kn, Nat.add(rn, 1n+ll)), 64n, ee)), le_add_left(kn, Nat.add(rn, 1n+ll))) :
    {Nat.is_le(Nat.add(rn, 1n+ll), 64n) == True{} : Bool}}
  +er = {uadd(run, 1, M1.le_trans(Nat.add(rn, 1n), Nat.add(rn, 1n+ll), 64n, M1.le_add_mono(rn, 1n, 1n+ll,
      M1.le_zero(ll)),
    a2)) : {U32.to_nat((run + 1 : U32)) == Nat.add(rn, 1n) : Nat}}
  +ea = {Equal.trans(Nat, Nat.add(U32.to_nat((run + 1 : U32)), ll), Nat.add(Nat.add(rn, 1n), ll), Nat.add(rn, 1n+ll),
    Equal.cong(Nat, Nat, nn => Nat.add(nn, ll), U32.to_nat((run + 1 : U32)), Nat.add(rn, 1n), er), M1.ras.add_assoc(rn,
        1n,
    ll)) : {Nat.add(U32.to_nat((run + 1 : U32)), ll) == Nat.add(rn, 1n+ll) : Nat}}
  Equal.trans(Nat, Nat.add(kn, Nat.add(U32.to_nat((run + 1 : U32)), ll)), Nat.add(kn, Nat.add(rn, 1n+ll)), 64n,
    Equal.cong(Nat, Nat, nn => Nat.add(kn, nn), Nat.add(U32.to_nat((run + 1 : U32)), ll), Nat.add(rn, 1n+ll), ea), ee)

# the lookups left one coefficient on, past a zero
def acl_zero_left(
  +ct: List<&2, U32>,
  +run: U32,
  +kk: U32,
  +left: Nat,
  +ee: {Nat.add(U32.to_nat(kk), Nat.add(U32.to_nat(run), 1n+List.length(&2, U32, ct))) == 64n : Nat},
  hl: {Nat.is_le(Nat.add(U32.to_nat(run), 1n+List.length(&2, U32, ct)), left) == True{} : Bool}
) -> AclLeft((run + 1 : U32), ct, left):
  +kn = U32.to_nat(kk)
  +rn = U32.to_nat(run)
  +ll = List.length(&2, U32, ct)
  +a2 = {Equal.trans(Bool, Nat.is_le(Nat.add(rn, 1n+ll), 64n), Nat.is_le(Nat.add(rn, 1n+ll), Nat.add(kn, Nat.add(rn,
    1n+ll))), True{}, Equal.cong(Nat, Bool, nn => Nat.is_le(Nat.add(rn, 1n+ll), nn), 64n, Nat.add(kn, Nat.add(rn,
    1n+ll)), Equal.sym(Nat, Nat.add(kn, Nat.add(rn, 1n+ll)), 64n, ee)), le_add_left(kn, Nat.add(rn, 1n+ll))) :
    {Nat.is_le(Nat.add(rn, 1n+ll), 64n) == True{} : Bool}}
  +er = {uadd(run, 1, M1.le_trans(Nat.add(rn, 1n), Nat.add(rn, 1n+ll), 64n, M1.le_add_mono(rn, 1n, 1n+ll,
      M1.le_zero(ll)),
    a2)) : {U32.to_nat((run + 1 : U32)) == Nat.add(rn, 1n) : Nat}}
  +ea = {Equal.trans(Nat, Nat.add(U32.to_nat((run + 1 : U32)), ll), Nat.add(Nat.add(rn, 1n), ll), Nat.add(rn, 1n+ll),
    Equal.cong(Nat, Nat, nn => Nat.add(nn, ll), U32.to_nat((run + 1 : U32)), Nat.add(rn, 1n), er), M1.ras.add_assoc(rn,
        1n,
    ll)) : {Nat.add(U32.to_nat((run + 1 : U32)), ll) == Nat.add(rn, 1n+ll) : Nat}}
  Equal.trans(Bool, Nat.is_le(Nat.add(U32.to_nat((run + 1 : U32)), ll), left), Nat.is_le(Nat.add(rn, 1n+ll), left),
    True{}, Equal.cong(Nat, Bool, nn => Nat.is_le(nn, left), Nat.add(U32.to_nat((run + 1 : U32)), ll), Nat.add(rn,
    1n+ll), ea), hl)

# the type of acl_join's parameter hs
def acl_join.hs.ty(+_cc: U32, +_ct: List<&2, U32>, +_run: U32, +_pp: Jenc.Put, +_stk: List<&2, L1.JTok>) -> Type:
  {Jenc.encode.ac(_cc <> _ct, _run, (acbk(), _pp)) == Jenc.encode.ac(_ct, 0, (acbk(), L1.jpg.feed(acbits(_stk),
    _pp))) : Array<U32> & Jenc.Put}

# the type of acl_join's parameter hw
def acl_join.hw.ty(+_kk: U32, +_left: Nat, +_stk: List<&2, L1.JTok>, +_k2: U32, +_l2: Nat) -> Type:
  @ts: List<&2, L1.JTok> -> {L1.jpg.acwf(List.append(&2, L1.JTok, _stk, ts), L1.JAcSt{_kk, _left,
    U32.is_eq(_kk, 64)}) == L1.jpg.acwf(ts, L1.JAcSt{_k2, _l2, U32.is_eq(_k2, 64)}) : Bool}

# the tokens after a nonzero coefficient, joined to the AC coder's tokens after it
def acl_join(
  +cc: U32,
  +ct: List<&2, U32>,
  +run: U32,
  +kk: U32,
  +left: Nat,
  +pp: Jenc.Put,
  +stk: List<&2, L1.JTok>,
  +k2: U32,
  +l2: Nat,
  hs: acl_join.hs.ty(cc, ct, run, pp, stk),
  hw: acl_join.hw.ty(kk, left, stk, k2, l2),
  res: AclRes(ct, 0, k2, l2, L1.jpg.feed(acbits(stk), pp))
) -> AclRes(cc <> ct, run, kk, left, pp):
  (+ts, eq, wf) = res
  +sb = acbits(stk)
  (List.append(&2, L1.JTok, stk, ts), Equal.trans(Array<U32> & Jenc.Put, Jenc.encode.ac(cc <> ct, run, (acbk(), pp)),
    Jenc.encode.ac(ct, 0, (acbk(), L1.jpg.feed(sb, pp))), (acbk(), L1.jpg.feed(acbits(List.append(&2,
      L1.JTok, stk,
    ts)), pp)), hs, Equal.trans(Array<U32> & Jenc.Put, Jenc.encode.ac(ct, 0, (acbk(), L1.jpg.feed(sb, pp))), (acbk(),
    L1.jpg.feed(acbits(ts), L1.jpg.feed(sb, pp))), (acbk(), L1.jpg.feed(acbits(List.append(&2,
      L1.JTok, stk, ts)), pp)), eq,
    Equal.cong(Jenc.Put, Array<U32> & Jenc.Put, qq => (acbk(), qq), L1.jpg.feed(acbits(ts), L1.jpg.feed(sb,
      pp)),
    L1.jpg.feed(acbits(List.append(&2, L1.JTok, stk, ts)), pp), Equal.trans(Jenc.Put,
      L1.jpg.feed(acbits(ts), L1.jpg.feed(sb,
    pp)), L1.jpg.feed(List.append(&2, Bool, sb, acbits(ts)), pp), L1.jpg.feed(acbits(List.append(&2,
      L1.JTok, stk, ts)),
    pp), Equal.sym(Jenc.Put, L1.jpg.feed(List.append(&2, Bool, sb, acbits(ts)), pp),
      L1.jpg.feed(acbits(ts), L1.jpg.feed(sb,
    pp)), feed_app(sb, acbits(ts), pp)), Equal.cong(List<&2, Bool>, Jenc.Put, xs => L1.jpg.feed(xs, pp),
    List.append(&2, Bool, sb, acbits(ts)), acbits(List.append(&2, L1.JTok, stk, ts)), Equal.sym(List<&2,
      Bool>,
    acbits(List.append(&2, L1.JTok, stk, ts)), List.append(&2, Bool, sb, acbits(ts)), acbits_app(stk,
    ts))))))), Equal.trans(Bool, L1.jpg.acwf(List.append(&2, L1.JTok, stk, ts), L1.JAcSt{kk, left, U32.is_eq(kk,
      64)}),
    L1.jpg.acwf(ts, L1.JAcSt{k2, l2, U32.is_eq(k2, 64)}), True{}, hw(ts), wf))

# a U32 compare at least 64, as Nat, fails below 64
def uge64_f(+xx: U32, hh: {Nat.is_lt(U32.to_nat(xx), 64n) == True{} : Bool}) -> {U32.is_ge(xx, 64) == False{} : Bool}:
  +xn = U32.to_nat(xx)
  Equal.trans(Bool, U32.is_ge(xx, 64), Cmp.is_ge(Nat.cmp(xn, 64n)), False{}, Equal.cong(Cmp, Bool, cc => Cmp.is_ge(cc),
    U32.cmp(xx, 64), Nat.cmp(xn, 64n), jenc.u_cmp(xx, 64)), Equal.trans(Bool, Cmp.is_ge(Nat.cmp(xn, 64n)),
        Nat.is_le(64n,
    xn), False{}, ge_le(xn, 64n), lt_nle(xn, 64n, hh)))

# the AC coder at a nonzero coefficient: ZRLs and its run and size token, then the rest
def acl_nz(
  +cc: U32,
  +ct: List<&2, U32>,
  +run: U32,
  +kk: U32,
  +left: Nat,
  +pp: Jenc.Put,
  +hz: {U32.is_eq(cc, 0) == False{} : Bool},
  +ee: {Nat.add(U32.to_nat(kk), Nat.add(U32.to_nat(run), 1n+List.length(&2, U32, ct))) == 64n : Nat},
  +hl: {Nat.is_le(Nat.add(U32.to_nat(run), 1n+List.length(&2, U32, ct)), left) == True{} : Bool},
  ih: AclIh(ct)
) -> AclRes(cc <> ct, run, kk, left, pp):
  +clip = Jenc.encode.clip(cc, 1023)
  +cat = Jenc.encode.cat(clip)
  +qq = U32.and(15, run)
  +sym = U32.or(cat, U32.shln(qq, 4n))
  +zj = U32.to_nat(U32.shrn(run, 4n))
  +ex = mz(U32.is_eq(cat, 0), cat, clip)
  +stk = stoks(zj, sym, cat, clip)
  +tk = {L1.JTok{sym, ex} : L1.JTok}
  +hcat = {memcat.ac(clip, clipnz.ac(cc, hz), clip.ac(cc)) : {L1.jpg.memb(cat, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]) ==
    True{} : Bool}}
  +r0 = {symok.of(run, cat, hcat) : {M1.symok(qq, cat) == True{} : Bool}}
  +a1 = Bool.not(U32.is_eq(sym, 0))
  +a2 = Bool.not(U32.is_eq(sym, 240))
  +a3 = U32.is_eq(U32.and(15, sym), cat)
  +a4 = U32.is_eq(U32.shrn(sym, 4n), qq)
  +hm = {and_l(L1.jpg.memb(sym, Jenc.encode.acsyms()), Bool.and(a1, Bool.and(a2, Bool.and(a3, a4))),
    r0) : {L1.jpg.memb(sym,
    Jenc.encode.acsyms()) == True{} : Bool}}
  +r1 = {and_r(L1.jpg.memb(sym, Jenc.encode.acsyms()), Bool.and(a1, Bool.and(a2, Bool.and(a3, a4))),
    r0) : {Bool.and(a1,
    Bool.and(a2, Bool.and(a3, a4))) == True{} : Bool}}
  +he = {not_t(U32.is_eq(sym, 0), and_l(a1, Bool.and(a2, Bool.and(a3, a4)), r1)) : {U32.is_eq(sym, 0) == False{} :
    Bool}}
  +r2 = {and_r(a1, Bool.and(a2, Bool.and(a3, a4)), r1) : {Bool.and(a2, Bool.and(a3, a4)) == True{} : Bool}}
  +h240 = {not_t(U32.is_eq(sym, 240), and_l(a2, Bool.and(a3, a4), r2)) : {U32.is_eq(sym, 240) == False{} : Bool}}
  +r3 = {and_r(a2, Bool.and(a3, a4), r2) : {Bool.and(a3, a4) == True{} : Bool}}
  +ec = {M1.ueq(U32.and(15, sym), cat, and_l(a3, a4, r3)) : {U32.and(15, sym) == cat : U32}}
  +eq4 = {M1.ueq(U32.shrn(sym, 4n), qq, and_r(a3, a4, r3)) : {U32.shrn(sym, 4n) == qq : U32}}
  +kn = U32.to_nat(kk)
  +rn = U32.to_nat(run)
  +qn = U32.to_nat(qq)
  +sn = M1.sixteen(zj)
  +ll = List.length(&2, U32, ct)
  +en1 = {M1.n1(run) : {rn == Nat.add(qn, sn) : Nat}}
  +eas = {M1.ras.add_assoc(kn, rn, 1n+ll) : {Nat.add(Nat.add(kn, rn), 1n+ll) == Nat.add(kn, Nat.add(rn, 1n+ll)) : Nat}}
  +d1 = {Equal.trans(Bool, Nat.is_lt(Nat.add(kn, rn), 64n), Nat.is_lt(Nat.add(kn, rn), Nat.add(Nat.add(kn, rn), 1n+ll)),
    True{}, Equal.cong(Nat, Bool, nn => Nat.is_lt(Nat.add(kn, rn), nn), 64n, Nat.add(Nat.add(kn, rn), 1n+ll),
    Equal.sym(Nat, Nat.add(Nat.add(kn, rn), 1n+ll), 64n, Equal.trans(Nat, Nat.add(Nat.add(kn, rn), 1n+ll), Nat.add(kn,
    Nat.add(rn, 1n+ll)), 64n, eas, ee))), lt_add_pos(Nat.add(kn, rn), 1n+ll, {==})) : {Nat.is_lt(Nat.add(kn, rn), 64n)
    == True{} : Bool}}
  +slr = {Equal.trans(Bool, Nat.is_le(sn, rn), Nat.is_le(sn, Nat.add(qn, sn)), True{}, Equal.cong(Nat, Bool, nn =>
    Nat.is_le(sn, nn), rn, Nat.add(qn, sn), en1), le_add_left(qn, sn)) : {Nat.is_le(sn, rn) == True{} : Bool}}
  +d2 = {M1.le_lt_trans(Nat.add(kn, sn), Nat.add(kn, rn), 64n, M1.le_add_mono(kn, sn, rn, slr), d1) :
    {Nat.is_lt(Nat.add(kn, sn), 64n) == True{} : Bool}}
  +zlr = {M1.le_trans(zj, sn, rn, le_sixteen(zj), slr) : {Nat.is_le(zj, rn) == True{} : Bool}}
  +d3 = {M1.le_trans(Nat.add(zj, 1n+ll), Nat.add(rn, 1n+ll), left, le_addr(zj, rn, 1n+ll, zlr), hl) :
    {Nat.is_le(Nat.add(zj, 1n+ll), left) == True{} : Bool}}
  +hz3 = {M3.le_add_r(zj, 1n+ll, left, d3) : {Nat.is_le(zj, left) == True{} : Bool}}
  +lz = npreds(zj, left)
  +hlz = {npl(zj, 1n+ll, left, d3) : {Nat.is_le(1n+ll, lz) == True{} : Bool}}
  +hp = {pos_of_le(ll, lz, hlz) : {Nat.is_lt(0n, lz) == True{} : Bool}}
  +h2 = {le_npred(ll, lz, hlz) : {Nat.is_le(ll, L1.jpg.npred(lz)) == True{} : Bool}}
  +kzz = M2.kz(zj, kk)
  +ekz = {kz_nat(zj, kk, d2) : {U32.to_nat(kzz) == Nat.add(kn, sn) : Nat}}
  +esum = {Equal.trans(Nat, Nat.add(U32.to_nat(kzz), qn), Nat.add(Nat.add(kn, sn), qn), Nat.add(kn, rn), Equal.cong(Nat,
    Nat, nn => Nat.add(nn, qn), U32.to_nat(kzz), Nat.add(kn, sn), ekz), Equal.trans(Nat, Nat.add(Nat.add(kn, sn), qn),
    Nat.add(kn, Nat.add(sn, qn)), Nat.add(kn, rn), M1.ras.add_assoc(kn, sn, qn), Equal.cong(Nat, Nat, nn => Nat.add(kn,
        nn),
    Nat.add(sn, qn), rn, Equal.trans(Nat, Nat.add(sn, qn), Nat.add(qn, sn), rn, M1.ras.add_comm(sn, qn), Equal.sym(Nat,
        rn,
    Nat.add(qn, sn), en1))))) : {Nat.add(U32.to_nat(kzz), qn) == Nat.add(kn, rn) : Nat}}
  +x1 = (kzz + qq : U32)
  +ex1 = {Equal.trans(Nat, U32.to_nat(x1), Nat.add(U32.to_nat(kzz), qn), Nat.add(kn, rn), uadd(kzz, qq,
    Equal.trans(Bool, Nat.is_le(Nat.add(U32.to_nat(kzz), qn), 64n), Nat.is_le(Nat.add(kn, rn), 64n), True{},
    Equal.cong(Nat, Bool, nn => Nat.is_le(nn, 64n), Nat.add(U32.to_nat(kzz), qn), Nat.add(kn, rn), esum), M1.lt_le(
    Nat.add(kn, rn), 64n, d1))), esum) : {U32.to_nat(x1) == Nat.add(kn, rn) : Nat}}
  +xlt = {Equal.trans(Bool, Nat.is_lt(U32.to_nat(x1), 64n), Nat.is_lt(Nat.add(kn, rn), 64n), True{}, Equal.cong(Nat,
    Bool, nn => Nat.is_lt(nn, 64n), U32.to_nat(x1), Nat.add(kn, rn), ex1), d1) : {Nat.is_lt(U32.to_nat(x1), 64n) ==
    True{} : Bool}}
  +ex4 = {Equal.cong(U32, U32, uu => (kzz + uu : U32), U32.shrn(sym, 4n), qq, eq4) : {(kzz + U32.shrn(sym, 4n) : U32) ==
    x1 : U32}}
  +hge = {Equal.trans(Bool, U32.is_ge((kzz + U32.shrn(sym, 4n) : U32), 64), U32.is_ge(x1, 64), False{}, Equal.cong(U32,
    Bool, uu => U32.is_ge(uu, 64), (kzz + U32.shrn(sym, 4n) : U32), x1, ex4), uge64_f(x1, xlt)) : {U32.is_ge((kzz +
    U32.shrn(sym, 4n) : U32), 64) == False{} : Bool}}
  +h1 = {Equal.trans(Bool, U32.is_eq(U32.and(15, sym), 0), U32.is_eq(cat, 0), False{}, Equal.cong(U32, Bool, uu =>
    U32.is_eq(uu, 0), U32.and(15, sym), cat, ec), memb_nz(cat, hcat)) : {U32.is_eq(U32.and(15, sym), 0) == False{} :
    Bool}}
  +h3 = {Equal.trans(Bool, Nat.is_eq(List.length(&2, Bool, ex), U32.to_nat(U32.and(15, sym))), Nat.is_eq(List.length(&2,
    Bool, ex), U32.to_nat(cat)), True{}, Equal.cong(U32, Bool, uu => Nat.is_eq(List.length(&2, Bool, ex),
      U32.to_nat(uu)),
    U32.and(15, sym), cat, ec), mzlen(U32.is_eq(cat, 0), cat, clip, {==})) : {Nat.is_eq(List.length(&2, Bool, ex),
    U32.to_nat(U32.and(15, sym))) == True{} : Bool}}
  +k2 = ((kzz + U32.shrn(sym, 4n) : U32) + 1 : U32)
  +y1 = (kzz + U32.shrn(sym, 4n) : U32)
  +ey1 = {Equal.trans(Nat, U32.to_nat(y1), U32.to_nat(x1), Nat.add(kn, rn), Equal.cong(U32, Nat, uu => U32.to_nat(uu),
    y1, x1, ex4), ex1) : {U32.to_nat(y1) == Nat.add(kn, rn) : Nat}}
  +ek2 = {Equal.trans(Nat, U32.to_nat(k2), Nat.add(U32.to_nat(y1), 1n), Nat.add(Nat.add(kn, rn), 1n), uadd(y1, 1,
    Equal.trans(Bool, Nat.is_le(Nat.add(U32.to_nat(y1), 1n), 64n), Nat.is_le(Nat.add(Nat.add(kn, rn), 1n), 64n), True{},
    Equal.cong(Nat, Bool, nn => Nat.is_le(Nat.add(nn, 1n), 64n), U32.to_nat(y1), Nat.add(kn, rn), ey1), lt_add1(
    Nat.add(kn, rn), 64n, d1))), Equal.cong(Nat, Nat, nn => Nat.add(nn, 1n), U32.to_nat(y1), Nat.add(kn, rn), ey1)) :
    {U32.to_nat(k2) == Nat.add(Nat.add(kn, rn), 1n) : Nat}}
  +e2 = {Equal.trans(Nat, Nat.add(U32.to_nat(k2), ll), Nat.add(Nat.add(Nat.add(kn, rn), 1n), ll), 64n, Equal.cong(Nat,
    Nat, nn => Nat.add(nn, ll), U32.to_nat(k2), Nat.add(Nat.add(kn, rn), 1n), ek2), Equal.trans(Nat, Nat.add(Nat.add(
    Nat.add(kn, rn), 1n), ll), Nat.add(Nat.add(kn, rn), 1n+ll), 64n, M1.ras.add_assoc(Nat.add(kn, rn), 1n, ll),
    Equal.trans(Nat, Nat.add(Nat.add(kn, rn), 1n+ll), Nat.add(kn, Nat.add(rn, 1n+ll)), 64n, eas, ee))) :
    {Nat.add(U32.to_nat(k2), ll) == 64n : Nat}}
  +hk = {M1.le_lt_trans(kn, Nat.add(kn, rn), 64n, M2.le_add_more(kn, kn, rn, M1.le_refl(kn)), d1) : {Nat.is_lt(kn,
      64n) ==
    True{} : Bool}}
  +hE = {Equal.trans(Bool, U32.is_eq(kk, 64), Nat.is_eq(kn, 64n), False{}, M1.u32_eq(kk, 64), lt_ne(kn, 64n, hk)) :
    {U32.is_eq(kk, 64) == False{} : Bool}}
  +hs = {Equal.trans(Array<U32> & Jenc.Put, Jenc.encode.ac(ct, Jenc.encode.ac.run(U32.is_eq(cc, 0), run),
    Jenc.encode.ac.at(U32.is_eq(cc, 0), cc, run, (acbk(), pp))), Jenc.encode.ac(ct, 0, Jenc.encode.ac.step(cc, run,
    (acbk(), pp))), Jenc.encode.ac(ct, 0, (acbk(), L1.jpg.feed(acbits(stk), pp))), Equal.cong(Bool,
    Array<U32> & Jenc.Put, zz => Jenc.encode.ac(ct, Jenc.encode.ac.run(zz, run), Jenc.encode.ac.at(zz, cc, run,
    (acbk(), pp))), U32.is_eq(cc, 0), False{}, hz), Equal.cong(Array<U32> & Jenc.Put, Array<U32> & Jenc.Put, st =>
    Jenc.encode.ac(ct, 0, st), Jenc.encode.ac.step(cc, run, (acbk(), pp)), (acbk(), L1.jpg.feed(acbits(stk), pp)),
    step_eq(cc, run, pp))) : {Jenc.encode.ac(cc <> ct, run, (acbk(), pp)) == Jenc.encode.ac(ct, 0, (acbk(),
    L1.jpg.feed(acbits(stk), pp))) : Array<U32> & Jenc.Put}}
  +zt = zrltoks(zj)
  acl_join(cc, ct, run, kk, left, pp, stk, k2, L1.jpg.npred(lz), hs, +ts => Equal.trans(Bool,
    L1.jpg.acwf(List.append(&2, L1.JTok,
    stk, ts), L1.JAcSt{kk, left, U32.is_eq(kk, 64)}), L1.jpg.acwf(List.append(&2, L1.JTok, stk, ts),
      L1.JAcSt{kk, left, False{}}),
    L1.jpg.acwf(ts, L1.JAcSt{k2, L1.jpg.npred(lz), U32.is_eq(k2, 64)}), Equal.cong(Bool, Bool,
      bb => L1.jpg.acwf(List.append(&2, L1.JTok,
    stk, ts), L1.JAcSt{kk, left, bb}), U32.is_eq(kk, 64), False{}, hE), Equal.trans(Bool,
      L1.jpg.acwf(List.append(&2, L1.JTok,
    stk, ts), L1.JAcSt{kk, left, False{}}), L1.jpg.acwf(List.append(&2, L1.JTok, zt, tk <> ts), L1.JAcSt{kk,
      left, False{}}),
    L1.jpg.acwf(ts, L1.JAcSt{k2, L1.jpg.npred(lz), U32.is_eq(k2, 64)}), Equal.cong(List<&2, L1.JTok>, Bool,
      xs => L1.jpg.acwf(xs,
    L1.JAcSt{kk, left, False{}}), List.append(&2, L1.JTok, stk, ts), List.append(&2, L1.JTok, zt, tk <> ts),
      app_t(zt, [tk],
    ts)), Equal.trans(Bool, L1.jpg.acwf(List.append(&2, L1.JTok, zt, tk <> ts), L1.JAcSt{kk, left, False{}}),
      L1.jpg.acwf(tk <> ts,
    L1.JAcSt{kzz, lz, False{}}), L1.jpg.acwf(ts, L1.JAcSt{k2, L1.jpg.npred(lz), U32.is_eq(k2, 64)}), zrlwf(zj,
      kk, left, tk <> ts, d2,
    hz3), symwf(sym, ex, kzz, lz, ts, he, h240, hm, hp, h1, hge, h3)))), ih(0, k2, L1.jpg.npred(lz),
      L1.jpg.feed(acbits(stk),
    pp), e2, h2))

# the AC coder at a coefficient, by whether it is zero
def acl_cons(
  zero: Bool,
  +cc: U32,
  +ct: List<&2, U32>,
  +run: U32,
  +kk: U32,
  +left: Nat,
  +pp: Jenc.Put,
  +hz: {U32.is_eq(cc, 0) == zero : Bool},
  +ee: {Nat.add(U32.to_nat(kk), Nat.add(U32.to_nat(run), 1n+List.length(&2, U32, ct))) == 64n : Nat},
  +hl: {Nat.is_le(Nat.add(U32.to_nat(run), 1n+List.length(&2, U32, ct)), left) == True{} : Bool},
  ih: AclIh(ct)
) -> AclRes(cc <> ct, run, kk, left, pp):
  match zero:
    case True{}:
      acl_zero(cc, ct, run, kk, left, pp, hz, ih((run + 1 : U32), kk, left, pp, acl_zero_pos(ct, run, kk, left, ee, hl),
        acl_zero_left(ct, run, kk, left, ee, hl)))
    case False{}:
      acl_nz(cc, ct, run, kk, left, pp, hz, ee, hl, ih)

# the AC coder over coefficients from a state that keeps the invariant writes tokens the decoder's loop reads in full
def acl(
  zz: List<&2, U32>,
  +run: U32,
  +kk: U32,
  +left: Nat,
  +pp: Jenc.Put,
  ee: AclPos(kk, run, zz),
  hl: AclLeft(run, zz, left)
) -> AclRes(zz, run, kk, left, pp):
  match zz:
    case Nil{}:
      acl_nil(U32.is_gt(run, 0), run, kk, left, pp, {==}, ee, hl)
    case +cc <> +ct:
      acl_cons(U32.is_eq(cc, 0), cc, ct, run, kk, left, pp, {==}, ee, hl, r2 => k2 => l2 => p2 => e2 => h2 => acl(ct,
        r2,
        k2, l2, p2, e2, h2))

# the encoder's books, written out
def book() -> Jenc.Book:
  Jenc.Book{dcbk(), acbk()}

# one block the encoder codes: a token the decoder reads whole, fed to the writer, the books back, and the next
# predictor below 2048
def BlkOut(+pred: U32, +pp: Jenc.Put, -zz: List<&2, U32>) -> Type:
  &bt: L1.JBlkTok -> &dd: U32 -> &_e: {Jenc.encode.block.go(book(), pp, pred, zz) == (book(), dd,
    L1.jpg.feed(blkbits(bt),
    pp)) : Jenc.Book & U32 & Jenc.Put} -> &_h: {U32.is_lt(dd, 2048) == True{} : Bool} -> {L1.jpg.blkwf(bt) == True{} :
    Bool}

# the type of blk_fin's parameter edc
def blk_fin.edc.ty(+_dc0: U32, +_pred: U32, +_pp: Jenc.Put, +_dcs: U32, +_dcx: List<&2, Bool>) -> Type:
  {Jenc.encode.dcdiff(dcbk(), _pp, Jenc.encode.dcbias(_dc0), _pred) == (dcbk(), L1.jpg.feed(List.append(&2, Bool,
    code.dc(_dcs), _dcx), _pp)) : Array<U32> & Jenc.Put}

# the block's AC part coded after its DC token
def blk_fin(
  +dc0: U32,
  +rest: List<&2, U32>,
  +pred: U32,
  +pp: Jenc.Put,
  +dcs: U32,
  +dcx: List<&2, Bool>,
  edc: blk_fin.edc.ty(dc0, pred, pp, dcs, dcx),
  hm: {L1.jpg.memb(dcs, Jenc.encode.dcsyms()) == True{} : Bool},
  hl: {Nat.is_eq(List.length(&2, Bool, dcx), U32.to_nat(dcs)) == True{} : Bool},
  ares: AclRes(rest, 0, 1, 63n, L1.jpg.feed(List.append(&2, Bool, code.dc(dcs), dcx), pp))
) -> BlkOut(pred, pp, dc0 <> rest):
  (+ts, eac, wf) = ares
  +dd = Jenc.encode.dcbias(dc0)
  +cd = List.append(&2, Bool, code.dc(dcs), dcx)
  +p1 = L1.jpg.feed(cd, pp)
  +ab = acbits(ts)
  +bt = {L1.JBlkTok{dcs, dcx, ts} : L1.JBlkTok}
  (bt, dd, Equal.trans(Jenc.Book & U32 & Jenc.Put, Jenc.encode.block.dc(Jenc.encode.dcdiff(dcbk(), pp, dd, pred),
    acbk(), dd, rest), Jenc.encode.block.dc((dcbk(), p1), acbk(), dd, rest), (book(), dd, L1.jpg.feed(
    blkbits(bt), pp)), Equal.cong(Array<U32> & Jenc.Put, Jenc.Book & U32 & Jenc.Put, gg => Jenc.encode.block.dc(gg,
    acbk(), dd, rest), Jenc.encode.dcdiff(dcbk(), pp, dd, pred), (dcbk(), p1), edc), Equal.trans(Jenc.Book &
    U32 & Jenc.Put, Jenc.encode.block.join(Jenc.encode.ac(rest, 0, (acbk(), p1)), dcbk(), dd),
    Jenc.encode.block.join((acbk(), L1.jpg.feed(ab, p1)), dcbk(), dd), (book(), dd, L1.jpg.feed(blkbits(bt),
      pp)),
    Equal.cong(Array<U32> & Jenc.Put, Jenc.Book & U32 & Jenc.Put, gg => Jenc.encode.block.join(gg, dcbk(), dd),
    Jenc.encode.ac(rest, 0, (acbk(), p1)), (acbk(), L1.jpg.feed(ab, p1)), eac), Equal.cong(Jenc.Put, Jenc.Book & U32 &
    Jenc.Put, qq => (book(), dd, qq), L1.jpg.feed(ab, p1), L1.jpg.feed(blkbits(bt), pp), Equal.trans(Jenc.Put,
      L1.jpg.feed(ab,
    p1), L1.jpg.feed(List.append(&2, Bool, cd, ab), pp), L1.jpg.feed(blkbits(bt), pp), Equal.sym(Jenc.Put,
      L1.jpg.feed(
    List.append(&2, Bool, cd, ab), pp), L1.jpg.feed(ab, p1), feed_app(cd, ab, pp)), Equal.cong(List<&2, Bool>,
      Jenc.Put,
    xs => L1.jpg.feed(xs, pp), List.append(&2, Bool, cd, ab), blkbits(bt), huf.app_assoc(code.dc(dcs), dcx,
      ab)))))),
    bias_lt(dc0), and_tt(L1.jpg.memb(dcs, Jenc.encode.dcsyms()), Bool.and(Nat.is_eq(List.length(&2, Bool, dcx),
    U32.to_nat(dcs)), L1.jpg.acwf(ts, L1.JAcSt{1, 63n, False{}})), hm, and_tt(Nat.is_eq(List.length(&2, Bool, dcx),
    U32.to_nat(dcs)), L1.jpg.acwf(ts, L1.JAcSt{1, 63n, False{}}), hl, wf)))

# the block after its DC token is named
def blk_dc(
  +dc0: U32,
  +rest: List<&2, U32>,
  +pred: U32,
  +pp: Jenc.Put,
  +hr: {List.length(&2, U32, rest) == 63n : Nat},
  dres: DcRes(Jenc.encode.dcbias(dc0), pred, pp)
) -> BlkOut(pred, pp, dc0 <> rest):
  (+dcs, +dcx, edc, hm, hl) = dres
  +p1 = L1.jpg.feed(List.append(&2, Bool, code.dc(dcs), dcx), pp)
  blk_fin(dc0, rest, pred, pp, dcs, dcx, edc, hm, hl, acl(rest, 0, 1, 63n, p1, Equal.cong(Nat, Nat, nn => Nat.add(1n,
    Nat.add(0n, nn)), List.length(&2, U32, rest), 63n, hr), Equal.trans(Bool, Nat.is_le(List.length(&2, U32, rest),
      63n),
    Nat.is_le(63n, 63n), True{}, Equal.cong(Nat, Bool, nn => Nat.is_le(nn, 63n), List.length(&2, U32, rest), 63n, hr),
    {==})))

# 0 is not a successor
def zero_ne(+nn: Nat, ee: {0n == 1n+nn : Nat}) -> Empty:
  jenc.true_false(Equal.cong(Nat, Bool, xx => Nat.is_eq(xx, 0n), 0n, 1n+nn, ee))

# a block of 64 coefficients the encoder codes, from a predictor below 2048
def jenc.blk(
  zz: List<&2, U32>,
  +pred: U32,
  +pp: Jenc.Put,
  hl: {List.length(&2, U32, zz) == 64n : Nat},
  hp: {U32.is_lt(pred, 2048) == True{} : Bool}
) -> BlkOut(pred, pp, zz):
  match zz:
    case Nil{}:
      Empty.absurd(BlkOut(pred, pp, []), zero_ne(63n, hl))
    case +dc0 <> +rest:
      blk_dc(dc0, rest, pred, pp, Equal.cong(Nat, Nat, nn => L1.jpg.npred(nn), 1n+List.length(&2, U32, rest), 64n,
        hl),
        dcres(Jenc.encode.dcbias(dc0), pred, pp, bias_lt(dc0), hp))

# one value read at an index joins the values read so far, the array handed on
def vals.put(got: Array<U32> & U32, acc: List<&2, U32>) -> Array<U32> & List<&2, U32>:
  (aa, +vv) = got
  (aa, List.append(&2, U32, acc, [vv]))

# the read at one index
def vals.step(st: Array<U32> & List<&2, U32>, +gg: U32) -> Array<U32> & List<&2, U32>:
  (aa, acc) = st
  vals.put(Array.get(U32, aa, gg), acc)

# the values read, the array dropped
def vals.end(st: Array<U32> & List<&2, U32>) -> List<&2, U32>:
  (aa, acc) = st
  +_s = Jenc.encode.pix.sink(aa)
  acc

# the values an array holds at indexes, in order, after acc
def vals(gs: List<&2, U32>, st: Array<U32> & List<&2, U32>) -> List<&2, U32>:
  match gs:
    case Nil{}:
      vals.end(st)
    case +gg <> gt:
      vals(gt, vals.step(st, gg))

# U32 lists regrouped
def app_u(
  xs: List<&2, U32>,
  +ys: List<&2, U32>,
  +zs: List<&2, U32>
) -> {List.append(&2, U32, List.append(&2, U32, xs, ys), zs) == List.append(&2, U32, xs, List.append(&2, U32, ys,
  zs)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case +hh <> tt:
      Equal.cong(List<&2, U32>, List<&2, U32>, ws => hh <> ws, List.append(&2, U32, List.append(&2, U32, tt, ys), zs),
        List.append(&2, U32, tt, List.append(&2, U32, ys, zs)), app_u(tt, ys, zs))

# a U32 list with nothing after it
def app_nil_u(xs: List<&2, U32>) -> {List.append(&2, U32, xs, []) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case +hh <> tt:
      Equal.cong(List<&2, U32>, List<&2, U32>, ws => hh <> ws, List.append(&2, U32, tt, []), tt, app_nil_u(tt))

# the values after acc and pre, for the rest of the indexes
def VaccIh(-gt: List<&2, U32>, +_acc: List<&2, U32>) -> Type:
  @a2: Array<U32> -> @p2: List<&2, U32> -> {vals(gt, (a2, List.append(&2, U32, _acc, p2))) == List.append(&2, U32, _acc,
    vals(gt, (a2, p2))) : List<&2, U32>}

# one read joins acc and pre, whatever it returned
def vacc.got(
  got: Array<U32> & U32,
  +gt: List<&2, U32>,
  +acc: List<&2, U32>,
  +pre: List<&2, U32>,
  ih: VaccIh(gt, acc)
) -> {vals(gt, vals.put(got, List.append(&2, U32, acc, pre))) == List.append(&2, U32, acc, vals(gt, vals.put(got,
  pre))) : List<&2, U32>}:
  match got:
    case (a2, +vv):
      Equal.trans(List<&2, U32>, vals(gt, (a2, List.append(&2, U32, List.append(&2, U32, acc, pre), [vv]))), vals(gt,
        (a2, List.append(&2, U32, acc, List.append(&2, U32, pre, [vv])))), List.append(&2, U32, acc, vals(gt, (a2,
        List.append(&2, U32, pre, [vv])))), Equal.cong(List<&2, U32>, List<&2, U32>, ws => vals(gt, (a2, ws)),
        List.append(&2, U32, List.append(&2, U32, acc, pre), [vv]), List.append(&2, U32, acc, List.append(&2, U32, pre,
        [vv])), app_u(acc, pre, [vv])), ih(a2, List.append(&2, U32, pre, [vv])))

# the values an array holds at indexes, after acc and pre, are acc and then the values after pre
def vacc2(
  gs: List<&2, U32>,
  aa: Array<U32>,
  +acc: List<&2, U32>,
  +pre: List<&2, U32>
) -> {vals(gs, (aa, List.append(&2, U32, acc, pre))) == List.append(&2, U32, acc, vals(gs, (aa, pre))) : List<&2, U32>}:
  match gs:
    case Nil{}:
      {==}
    case +gg <> +gt:
      vacc.got(Array.get(U32, aa, gg), gt, acc, pre, a2 => p2 => vacc2(gt, a2, acc, p2))

# the values an array holds at indexes, after acc, are acc and then the values
def vacc(
  gs: List<&2, U32>,
  aa: Array<U32>,
  +acc: List<&2, U32>
) -> {vals(gs, (aa, acc)) == List.append(&2, U32, acc, vals(gs, (aa, []))) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, vals(gs, (aa, acc)), vals(gs, (aa, List.append(&2, U32, acc, []))), List.append(&2, U32,
    acc, vals(gs, (aa, []))), Equal.cong(List<&2, U32>, List<&2, U32>, ws => vals(gs, (aa, ws)), acc, List.append(&2,
    U32, acc, []), Equal.sym(List<&2, U32>, List.append(&2, U32, acc, []), acc, app_nil_u(acc))), vacc2(gs, aa, acc,
      []))

# the rest of the scan, from any state, is the AC coder over the values it reads
def SacIh(-gt: List<&2, U32>) -> Type:
  @a2: Array<U32> -> @r2: U32 -> @c2: Array<U32> -> @b2: Jenc.Put -> {Jenc.encode.scan.ac(gt, Jenc.Scan{a2, r2, c2, b2})
    == Jenc.encode.ac(vals(gt, (a2, [])), r2, (c2, b2)) : Array<U32> & Jenc.Put}

# the scan after a nonzero coefficient, whatever the AC coder handed back
def sac.hit(
  st: Array<U32> & Jenc.Put,
  a2: Array<U32>,
  +gt: List<&2, U32>,
  ih: SacIh(gt)
) -> {Jenc.encode.scan.ac(gt, Jenc.encode.scan.hit(st, a2)) == Jenc.encode.ac(vals(gt, (a2, [])), 0,
  st) : Array<U32> & Jenc.Put}:
  match st:
    case (c3, b3):
      ih(a2, 0, c3, b3)

# the scan at a coefficient, by whether it is zero
def sac.z(
  zz: Bool,
  +vv: U32,
  a2: Array<U32>,
  +gt: List<&2, U32>,
  +run: U32,
  ac: Array<U32>,
  +bit: Jenc.Put,
  ih: SacIh(gt)
) -> {Jenc.encode.scan.ac(gt, Jenc.encode.scan.bump(zz, Jenc.Scan{a2, run, ac, bit}, vv)) == Jenc.encode.ac(vals(gt,
  (a2, [])), Jenc.encode.ac.run(zz, run), Jenc.encode.ac.at(zz, vv, run, (ac, bit))) : Array<U32> & Jenc.Put}:
  match zz:
    case True{}:
      ih(a2, (run + 1 : U32), ac, bit)
    case False{}:
      sac.hit(Jenc.encode.ac.step(vv, run, (ac, bit)), a2, gt, ih)

# the values after one read, for an array known equal to another
def vacc_tr(
  -a2: Array<U32>,
  bb: Array<U32>,
  ee: {bb == a2 : Array<U32>},
  +gt: List<&2, U32>,
  +vv: U32
) -> {vals(gt, (a2, [vv])) == vv <> vals(gt, (a2, [])) : List<&2, U32>}:
  %ee : {vals(gt, (_, [vv])) == vv <> vals(gt, (_, [])) : List<&2, U32>}
  vacc(gt, bb, [vv])

# the scan at a coefficient, for an array known equal to another
def sacz_tr(
  zz: Bool,
  +vv: U32,
  -a2: Array<U32>,
  bb: Array<U32>,
  ee: {bb == a2 : Array<U32>},
  +gt: List<&2, U32>,
  +run: U32,
  ac: Array<U32>,
  +bit: Jenc.Put,
  ih: SacIh(gt)
) -> {Jenc.encode.scan.ac(gt, Jenc.encode.scan.bump(zz, Jenc.Scan{a2, run, ac, bit}, vv)) == Jenc.encode.ac(vals(gt,
  (a2, [])), Jenc.encode.ac.run(zz, run), Jenc.encode.ac.at(zz, vv, run, (ac, bit))) : Array<U32> & Jenc.Put}:
  %ee : {Jenc.encode.scan.ac(gt, Jenc.encode.scan.bump(zz, Jenc.Scan{_, run, ac, bit}, vv)) == Jenc.encode.ac(vals(gt,
    (_, [])), Jenc.encode.ac.run(zz, run), Jenc.encode.ac.at(zz, vv, run, (ac, bit))) : Array<U32> & Jenc.Put}
  sac.z(zz, vv, bb, gt, run, ac, bit, ih)

# the scan at an index, from two copies of the array read
def sac.d(
  -a2: Array<U32>,
  +vv: U32,
  +gt: List<&2, U32>,
  +run: U32,
  ac: Array<U32>,
  +bit: Jenc.Put,
  ih: SacIh(gt),
  dd: Dup(a2)
) -> {Jenc.encode.scan.ac(gt, Jenc.encode.scan.bump(U32.is_eq(vv, 0), Jenc.Scan{a2, run, ac, bit},
  vv)) == Jenc.encode.ac(vals(gt, (a2, [vv])), run, (ac, bit)) : Array<U32> & Jenc.Put}:
  (b1, b2, e1, e2) = dd
  Equal.trans(Array<U32> & Jenc.Put, Jenc.encode.scan.ac(gt, Jenc.encode.scan.bump(U32.is_eq(vv, 0), Jenc.Scan{a2, run,
    ac, bit}, vv)), Jenc.encode.ac(vv <> vals(gt, (a2, [])), run, (ac, bit)), Jenc.encode.ac(vals(gt, (a2, [vv])), run,
    (ac, bit)), sacz_tr(U32.is_eq(vv, 0), vv, a2, b1, e1, gt, run, ac, bit, ih), Equal.cong(List<&2, U32>, Array<U32> &
    Jenc.Put, ws => Jenc.encode.ac(ws, run, (ac, bit)), vv <> vals(gt, (a2, [])), vals(gt, (a2, [vv])), Equal.sym(
    List<&2, U32>, vals(gt, (a2, [vv])), vv <> vals(gt, (a2, [])), vacc_tr(a2, b2, e2, gt, vv))))

# the scan at an index, whatever the read returned
def sac.got(
  got: Array<U32> & U32,
  +gt: List<&2, U32>,
  +run: U32,
  ac: Array<U32>,
  +bit: Jenc.Put,
  ih: SacIh(gt)
) -> {Jenc.encode.scan.ac(gt, Jenc.encode.scan.val(got, run, (ac, bit))) == Jenc.encode.ac(vals(gt, vals.put(got,
  [])), run, (ac, bit)) : Array<U32> & Jenc.Put}:
  match got:
    case (a2, +vv):
      sac.d(a2, vv, gt, run, ac, bit, ih, dup(a2))

# the scan's AC part is the AC coder over the values it reads
def sac(
  gs: List<&2, U32>,
  aa: Array<U32>,
  +run: U32,
  ac: Array<U32>,
  +bit: Jenc.Put
) -> {Jenc.encode.scan.ac(gs, Jenc.Scan{aa, run, ac, bit}) == Jenc.encode.ac(vals(gs, (aa, [])), run, (ac,
  bit)) : Array<U32> & Jenc.Put}:
  match gs:
    case Nil{}:
      {==}
    case +gg <> +gt:
      sac.got(Array.get(U32, aa, gg), gt, run, ac, bit, a2 => r2 => c2 => b2 => sac(gt, a2, r2, c2, b2))

# the scan's and the block coder's last step build the same books, whatever the AC coder handed back
def book_join(
  got: Array<U32> & Jenc.Put,
  dc: Array<U32>,
  +dd: U32
) -> {Jenc.encode.scan.book(got, dc, dd) == Jenc.encode.block.join(got, dc, dd) : Jenc.Book & U32 & Jenc.Put}:
  match got:
    case (_a, _p):
      {==}

# the scan's AC part, for arrays known equal to others
def sac_tr(
  +gt: List<&2, U32>,
  -a2: Array<U32>,
  -ac: Array<U32>,
  bb: Array<U32>,
  cc: Array<U32>,
  eb: {bb == a2 : Array<U32>},
  ec: {cc == ac : Array<U32>},
  +p2: Jenc.Put
) -> {Jenc.encode.scan.ac(gt, Jenc.Scan{a2, 0, ac, p2}) == Jenc.encode.ac(vals(gt, (a2, [])), 0, (ac,
  p2)) : Array<U32> & Jenc.Put}:
  %eb : {Jenc.encode.scan.ac(gt, Jenc.Scan{_, 0, ac, p2}) == Jenc.encode.ac(vals(gt, (_, [])), 0, (ac, p2)) : Array<U32>
    & Jenc.Put}
  %ec : {Jenc.encode.scan.ac(gt, Jenc.Scan{bb, 0, _, p2}) == Jenc.encode.ac(vals(gt, (bb, [])), 0, (_, p2)) : Array<U32>
    & Jenc.Put}
  sac(gt, bb, 0, cc, p2)

# the last step's books, for arrays known equal to others
def bj_tr(
  +gt: List<&2, U32>,
  -a2: Array<U32>,
  -ac: Array<U32>,
  bb: Array<U32>,
  cc: Array<U32>,
  eb: {bb == a2 : Array<U32>},
  ec: {cc == ac : Array<U32>},
  +p2: Jenc.Put,
  dc2: Array<U32>,
  +dd: U32
) -> {Jenc.encode.scan.book(Jenc.encode.ac(vals(gt, (a2, [])), 0, (ac, p2)), dc2,
  dd) == Jenc.encode.block.join( Jenc.encode.ac(vals(gt, (a2, [])), 0, (ac, p2)), dc2,
  dd) : Jenc.Book & U32 & Jenc.Put}:
  %eb : {Jenc.encode.scan.book(Jenc.encode.ac(vals(gt, (_, [])), 0, (ac, p2)), dc2, dd) == Jenc.encode.block.join(
    Jenc.encode.ac(vals(gt, (_, [])), 0, (ac, p2)), dc2, dd) : Jenc.Book & U32 & Jenc.Put}
  %ec : {Jenc.encode.scan.book(Jenc.encode.ac(vals(gt, (bb, [])), 0, (_, p2)), dc2, dd) == Jenc.encode.block.join(
    Jenc.encode.ac(vals(gt, (bb, [])), 0, (_, p2)), dc2, dd) : Jenc.Book & U32 & Jenc.Put}
  book_join(Jenc.encode.ac(vals(gt, (bb, [])), 0, (cc, p2)), dc2, dd)

# the scan after its DC token, from copies of the arrays
def sjoin.d(
  -a2: Array<U32>,
  -ac: Array<U32>,
  +p2: Jenc.Put,
  dc2: Array<U32>,
  +dd: U32,
  +gt: List<&2, U32>,
  da: Dup(a2),
  dk: Dup(ac)
) -> {Jenc.encode.scan.book(Jenc.encode.scan.ac(gt, Jenc.Scan{a2, 0, ac, p2}), dc2,
  dd) == Jenc.encode.block.join( Jenc.encode.ac(vals(gt, (a2, [])), 0, (ac, p2)), dc2,
  dd) : Jenc.Book & U32 & Jenc.Put}:
  (x1, x2, ea1, ea2) = da
  (y1, y2, ec1, ec2) = dk
  Equal.trans(Jenc.Book & U32 & Jenc.Put, Jenc.encode.scan.book(Jenc.encode.scan.ac(gt, Jenc.Scan{a2, 0, ac, p2}), dc2,
    dd), Jenc.encode.scan.book(Jenc.encode.ac(vals(gt, (a2, [])), 0, (ac, p2)), dc2, dd), Jenc.encode.block.join(
    Jenc.encode.ac(vals(gt, (a2, [])), 0, (ac, p2)), dc2, dd), Equal.cong(Array<U32> & Jenc.Put, Jenc.Book & U32 &
    Jenc.Put, xx => Jenc.encode.scan.book(xx, dc2, dd), Jenc.encode.scan.ac(gt, Jenc.Scan{a2, 0, ac, p2}),
    Jenc.encode.ac(vals(gt, (a2, [])), 0, (ac, p2)), sac_tr(gt, a2, ac, x1, y1, ea1, ec1, p2)), bj_tr(gt, a2, ac, x2,
      y2,
    ea2, ec2, p2, dc2, dd))

# the scan after its DC token, whatever the DC coder handed back, is the block coder's
def sjoin(
  got: Array<U32> & Jenc.Put,
  ac: Array<U32>,
  +dd: U32,
  +gt: List<&2, U32>,
  a2: Array<U32>
) -> {Jenc.encode.scan.join(got, ac, dd, gt, a2) == Jenc.encode.block.dc(got, ac, dd, vals(gt, (a2,
  []))) : Jenc.Book & U32 & Jenc.Put}:
  match got:
    case (dc2, +p2):
      sjoin.d(a2, ac, p2, dc2, dd, gt, dup(a2), dup(ac))

# the scan with its DC value named, over any books
def sdc(
  book: Jenc.Book,
  +pp: Jenc.Put,
  +pred: U32,
  +vv: U32,
  +gt: List<&2, U32>,
  a2: Array<U32>
) -> {Jenc.encode.scan.dc(book, pp, pred, vv, gt, a2) == Jenc.encode.block.ac(book, pp, pred, vv, vals(gt, (a2,
  []))) : Jenc.Book & U32 & Jenc.Put}:
  match book:
    case Jenc.Book{dc, ac}:
      sjoin(Jenc.encode.dcdiff(dc, pp, Jenc.encode.dcbias(vv), pred), ac, Jenc.encode.dcbias(vv), gt, a2)

# the scan's DC value named, for an array known equal to another
def sdc_tr(
  book: Jenc.Book,
  +pp: Jenc.Put,
  +pred: U32,
  +vv: U32,
  +gt: List<&2, U32>,
  -a2: Array<U32>,
  bb: Array<U32>,
  ee: {bb == a2 : Array<U32>}
) -> {Jenc.encode.scan.dc(book, pp, pred, vv, gt, a2) == Jenc.encode.block.ac(book, pp, pred, vv, vals(gt, (a2,
  []))) : Jenc.Book & U32 & Jenc.Put}:
  %ee : {Jenc.encode.scan.dc(book, pp, pred, vv, gt, _) == Jenc.encode.block.ac(book, pp, pred, vv, vals(gt, (_, []))) :
    Jenc.Book & U32 & Jenc.Put}
  sdc(book, pp, pred, vv, gt, bb)

# the scan at its first index, from two copies of the array read
def sopen.d(
  -a2: Array<U32>,
  +vv: U32,
  +gt: List<&2, U32>,
  book: Jenc.Book,
  +pp: Jenc.Put,
  +pred: U32,
  dd: Dup(a2)
) -> {Jenc.encode.scan.dc(book, pp, pred, vv, gt, a2) == Jenc.encode.block.go(book, pp, pred, vals(gt, (a2,
  [vv]))) : Jenc.Book & U32 & Jenc.Put}:
  (b1, b2, e1, e2) = dd
  Equal.trans(Jenc.Book & U32 & Jenc.Put, Jenc.encode.scan.dc(book, pp, pred, vv, gt, a2), Jenc.encode.block.go(book,
    pp,
    pred, vv <> vals(gt, (a2, []))), Jenc.encode.block.go(book, pp, pred, vals(gt, (a2, [vv]))), sdc_tr(book, pp, pred,
    vv, gt, a2, b1, e1), Equal.cong(List<&2, U32>, Jenc.Book & U32 & Jenc.Put, ws => Jenc.encode.block.go(book, pp,
      pred,
    ws), vv <> vals(gt, (a2, [])), vals(gt, (a2, [vv])), Equal.sym(List<&2, U32>, vals(gt, (a2, [vv])), vv <> vals(gt,
    (a2, [])), vacc_tr(a2, b2, e2, gt, vv))))

# the scan at its first index, whatever the read returned
def sopen(
  got: Array<U32> & U32,
  +gt: List<&2, U32>,
  book: Jenc.Book,
  +pp: Jenc.Put,
  +pred: U32
) -> {Jenc.encode.scan.open(gt, got, book, pp, pred) == Jenc.encode.block.go(book, pp, pred, vals(gt, vals.put(got,
  []))) : Jenc.Book & U32 & Jenc.Put}:
  match got:
    case (a2, +vv):
      sopen.d(a2, vv, gt, book, pp, pred, dup(a2))

# the encoder's scan of a frequency plane is its block coder over the values the zigzag reads
def scan_blk(
  book: Jenc.Book,
  +pp: Jenc.Put,
  +pred: U32,
  aa: Array<U32>,
  +gg: U32,
  +gt: List<&2, U32>
) -> {Jenc.encode.scan(book, pp, pred, aa, gg <> gt) == Jenc.encode.block.go(book, pp, pred, vals(gg <> gt, (aa,
  []))) : Jenc.Book & U32 & Jenc.Put}:
  sopen(Array.get(U32, aa, gg), gt, book, pp, pred)

# the number of values read, after acc, whatever the read returned
def LenIh(-gt: List<&2, U32>) -> Type:
  @a2: Array<U32> -> {List.length(&2, U32, vals(gt, (a2, []))) == List.length(&2, U32, gt) : Nat}

# the count of values read, for an array known equal to another
def vlen_tr(
  -a2: Array<U32>,
  bb: Array<U32>,
  ee: {bb == a2 : Array<U32>},
  +gt: List<&2, U32>,
  ih: LenIh(gt)
) -> {List.length(&2, U32, vals(gt, (a2, []))) == List.length(&2, U32, gt) : Nat}:
  %ee : {List.length(&2, U32, vals(gt, (_, []))) == List.length(&2, U32, gt) : Nat}
  ih(bb)

# one read, then the rest, from two copies of the array read
def vlen.d(
  -a2: Array<U32>,
  +vv: U32,
  +gt: List<&2, U32>,
  ih: LenIh(gt),
  dd: Dup(a2)
) -> {List.length(&2, U32, vals(gt, (a2, [vv]))) == 1n+List.length(&2, U32, gt) : Nat}:
  (b1, b2, e1, e2) = dd
  Equal.trans(Nat, List.length(&2, U32, vals(gt, (a2, [vv]))), List.length(&2, U32, vv <> vals(gt, (a2, []))),
    1n+List.length(&2, U32, gt), Equal.cong(List<&2, U32>, Nat, ws => List.length(&2, U32, ws), vals(gt, (a2, [vv])),
    vv <> vals(gt, (a2, [])), vacc_tr(a2, b1, e1, gt, vv)), Equal.cong(Nat, Nat, nn => 1n+nn, List.length(&2, U32,
    vals(gt, (a2, []))), List.length(&2, U32, gt), vlen_tr(a2, b2, e2, gt, ih)))

# one read, then the rest
def vlen.got(
  got: Array<U32> & U32,
  +gt: List<&2, U32>,
  ih: LenIh(gt)
) -> {List.length(&2, U32, vals(gt, vals.put(got, []))) == 1n+List.length(&2, U32, gt) : Nat}:
  match got:
    case (a2, +vv):
      vlen.d(a2, vv, gt, ih, dup(a2))

# as many values as indexes
def vlen(
  gs: List<&2, U32>,
  aa: Array<U32>
) -> {List.length(&2, U32, vals(gs, (aa, []))) == List.length(&2, U32, gs) : Nat}:
  match gs:
    case Nil{}:
      {==}
    case +gg <> +gt:
      vlen.got(Array.get(U32, aa, gg), gt, a2 => vlen(gt, a2))

# the scan of an empty zigzag is the block coder of no values
def scan_nil(
  book: Jenc.Book,
  +pp: Jenc.Put,
  +pred: U32,
  aa: Array<U32>
) -> {Jenc.encode.scan(book, pp, pred, aa, []) == Jenc.encode.block.go(book, pp, pred, vals([], (aa,
  []))) : Jenc.Book & U32 & Jenc.Put}:
  {==}

# the encoder's scan of a frequency plane is its block coder over the values the zigzag reads
def scan_eq(
  book: Jenc.Book,
  +pp: Jenc.Put,
  +pred: U32,
  aa: Array<U32>,
  zig: List<&2, U32>
) -> {Jenc.encode.scan(book, pp, pred, aa, zig) == Jenc.encode.block.go(book, pp, pred, vals(zig, (aa,
  []))) : Jenc.Book & U32 & Jenc.Put}:
  match zig:
    case Nil{}:
      scan_nil(book, pp, pred, aa)
    case +gg <> +gt:
      scan_blk(book, pp, pred, aa, gg, gt)

# the count of values an array holds at the zigzag, from a copy of it
def lenz(
  -aa: Array<U32>,
  bb: Array<U32>,
  ee: {bb == aa : Array<U32>}
) -> {List.length(&2, U32, vals(Jpeg.decode.zig(), (aa, []))) == 64n : Nat}:
  %ee : {List.length(&2, U32, vals(Jpeg.decode.zig(), (_, []))) == 64n : Nat}
  vlen(Jpeg.decode.zig(), bb)

# a block of values, once they are known to be 64
def Blk64(+_pred: U32, +_pp: Jenc.Put, +_xs: List<&2, U32>) -> Type:
  @hl: {List.length(&2, U32, _xs) == 64n : Nat} -> BlkOut(_pred, _pp, _xs)

# the block of the values an array holds at the zigzag, once they are known to be 64, from a copy of it
def blkh(
  -aa: Array<U32>,
  bb: Array<U32>,
  ee: {bb == aa : Array<U32>},
  +pp: Jenc.Put,
  +pred: U32,
  hp: {U32.is_lt(pred, 2048) == True{} : Bool}
) -> Blk64(pred, pp, vals(Jpeg.decode.zig(), (aa, []))):
  %ee : Blk64(pred, pp, vals(Jpeg.decode.zig(), (_, [])))
  hl => jenc.blk(vals(Jpeg.decode.zig(), (bb, [])), pred, pp, hl, hp)

# the block of the values an array holds at the zigzag, the array one of two copies
def blkv(
  -aa: Array<U32>,
  +pp: Jenc.Put,
  +pred: U32,
  hp: {U32.is_lt(pred, 2048) == True{} : Bool},
  dd: Dup(aa)
) -> BlkOut(pred, pp, vals(Jpeg.decode.zig(), (aa, []))):
  (b1, b2, e1, e2) = dd
  blkh(aa, b1, e1, pp, pred, hp)(lenz(aa, b2, e2))

# the encoder's scan of any frequency plane codes a block the decoder reads whole
def ScanOut(-aa: Array<U32>, +pp: Jenc.Put, +pred: U32) -> Type:
  &bt: L1.JBlkTok -> &dd: U32 -> &_e: {Jenc.encode.scan(book(), pp, pred, aa, Jpeg.decode.zig()) == (book(), dd,
    L1.jpg.feed(blkbits(bt), pp)) : Jenc.Book & U32 & Jenc.Put} -> &_h: {U32.is_lt(dd, 2048) == True{} : Bool} ->
    {L1.jpg.blkwf(bt) == True{} : Bool}

# the type of scan_fin's parameter es
def scan_fin.es.ty(_aa: Array<U32>, +_pp: Jenc.Put, +_pred: U32) -> Type:
  {Jenc.encode.scan(book(), _pp, _pred, _aa, Jpeg.decode.zig()) == Jenc.encode.block.go(book(), _pp, _pred,
    vals(Jpeg.decode.zig(), (_aa, []))) : Jenc.Book & U32 & Jenc.Put}

# the scan's block, moved along the scan's equation
def scan_fin(
  -aa: Array<U32>,
  +pp: Jenc.Put,
  +pred: U32,
  es: scan_fin.es.ty(aa, pp, pred),
  bo: BlkOut(pred, pp, vals(Jpeg.decode.zig(), (aa, [])))
) -> ScanOut(aa, pp, pred):
  (bt, +dd, eb, hd, hw) = bo
  (bt, dd, Equal.trans(Jenc.Book & U32 & Jenc.Put, Jenc.encode.scan(book(), pp, pred, aa, Jpeg.decode.zig()),
    Jenc.encode.block.go(book(), pp, pred, vals(Jpeg.decode.zig(), (aa, []))), (book(), dd, L1.jpg.feed(
    blkbits(bt), pp)), es, eb), hd, hw)

# the scan's equation for an array known equal to another
def scan_tr(
  -aa: Array<U32>,
  bb: Array<U32>,
  ee: {bb == aa : Array<U32>},
  +pp: Jenc.Put,
  +pred: U32
) -> {Jenc.encode.scan(book(), pp, pred, aa, Jpeg.decode.zig()) == Jenc.encode.block.go(book(), pp, pred,
  vals( Jpeg.decode.zig(), (aa, []))) : Jenc.Book & U32 & Jenc.Put}:
  %ee : {Jenc.encode.scan(book(), pp, pred, _, Jpeg.decode.zig()) == Jenc.encode.block.go(book(), pp, pred,
    vals(Jpeg.decode.zig(), (_, []))) : Jenc.Book & U32 & Jenc.Put}
  scan_eq(book(), pp, pred, bb, Jpeg.decode.zig())

# the scan of a plane, from copies of it
def scan_d(
  -aa: Array<U32>,
  +pp: Jenc.Put,
  +pred: U32,
  hp: {U32.is_lt(pred, 2048) == True{} : Bool},
  dd: Dup(aa)
) -> ScanOut(aa, pp, pred):
  (b1, b2, e1, e2) = dd
  scan_fin(aa, pp, pred, scan_tr(aa, b1, e1, pp, pred), blkv(aa, pp, pred, hp, dup.tr(b2, aa, e2, dup(b2))))

# the scan of any plane
def scan_ok(
  aa: Array<U32>,
  +pp: Jenc.Put,
  +pred: U32,
  hp: {U32.is_lt(pred, 2048) == True{} : Bool}
) -> ScanOut(aa, pp, pred):
  scan_d(aa, pp, pred, hp, dup(aa))

# one component's block of an MCU, flat or not
def ChOut(+flat: Bool, -plane: Array<U32>, +pp: Jenc.Put, +pred: U32, +kern: Jenc.Kern, +qs: List<&2, U32>) -> Type:
  &bt: L1.JBlkTok -> &dd: U32 -> &_e: {Jenc.encode.chan.go(flat, plane, book(), pp, pred, kern, Jpeg.decode.zig(),
    qs) ==
    (book(), dd, L1.jpg.feed(blkbits(bt), pp)) : Jenc.Book & U32 & Jenc.Put} -> &_h: {U32.is_lt(dd,
      2048) == True{} :
    Bool} -> {L1.jpg.blkwf(bt) == True{} : Bool}

# one component's block, by whether it is flat
def chan_ok(
  flat: Bool,
  plane: Array<U32>,
  +pp: Jenc.Put,
  +pred: U32,
  +kern: Jenc.Kern,
  +qs: List<&2, U32>,
  hp: {U32.is_lt(pred, 2048) == True{} : Bool}
) -> ChOut(flat, plane, pp, pred, kern, qs):
  match flat:
    case True{}:
      jenc.blk(List.replicate(U32, 64n, 0), pred, pp, {==}, hp)
    case False{}:
      scan_ok(Jenc.encode.freq(plane, kern), pp, pred, hp)

# the encoder's cosine kernel
def kern() -> Jenc.Kern:
  Jenc.encode.kern(Jpeg.decode.cos())

# three blocks' bits fed after bits already fed
def feed3b(+b1: L1.JBlkTok, +b2: L1.JBlkTok, +b3: L1.JBlkTok, +bit: Jenc.Put) -> Jenc.Put:
  L1.jpg.feed(blkbits(b3), L1.jpg.feed(blkbits(b2), L1.jpg.feed(blkbits(b1), bit)))

# one MCU the encoder codes: three blocks the decoder reads whole, fed to the writer, the books back, and the next
# predictors below 2048
def McuOut(-tt: Jenc.Tile, +bit: Jenc.Put, +py: U32, +pb: U32, +pr: U32) -> Type:
  &t1: L1.JBlkTok -> &t2: L1.JBlkTok -> &t3: L1.JBlkTok -> &aa: Array<U32> -> &d1: U32 -> &d2: U32 -> &d3: U32 ->
    &_e:
    {Jenc.encode.step.tile(tt, book(), bit, py, pb, pr, kern(), Jpeg.decode.zig(), Jenc.encode.quant()) == (aa,
    book(), d1, d2, d3, feed3b(t1, t2, t3, bit)) : Array<U32> & Jenc.Book & U32 & U32 & U32 & Jenc.Put} -> &_h1:
    {U32.is_lt(d1, 2048) == True{} : Bool} -> &_h2: {U32.is_lt(d2, 2048) == True{} : Bool} -> &_h3: {U32.is_lt(d3,
    2048) == True{} : Bool} -> &_w1: {L1.jpg.blkwf(t1) == True{} : Bool} -> &_w2: {L1.jpg.blkwf(t2) == True{} :
      Bool} ->
    {L1.jpg.blkwf(t3) == True{} : Bool}

# the type of mcu3's parameter e1
def mcu3.e1.ty(_ys: Array<U32>, +_fy: Bool, +_bit: Jenc.Put, +_py: U32, +_t1: L1.JBlkTok, +_d1: U32) -> Type:
  {Jenc.encode.chan.go(_fy, _ys, book(), _bit, _py, kern(), Jpeg.decode.zig(), Jenc.encode.quant()) == (book(), _d1,
    L1.jpg.feed(blkbits(_t1), _bit)) : Jenc.Book & U32 & Jenc.Put}

# the type of mcu3's parameter e2
def mcu3.e2.ty(
  _bs: Array<U32>,
  +_fb: Bool,
  +_bit: Jenc.Put,
  +_pb: U32,
  +_t1: L1.JBlkTok,
  +_t2: L1.JBlkTok,
  +_d2: U32
) -> Type:
  {Jenc.encode.chan.go(_fb, _bs, book(), L1.jpg.feed(blkbits(_t1), _bit), _pb, kern(), Jpeg.decode.zig(),
    Jenc.encode.quant()) == (book(), _d2, L1.jpg.feed(blkbits(_t2), L1.jpg.feed(blkbits(_t1),
    _bit))) : Jenc.Book & U32 & Jenc.Put}

# the type of mcu3's parameter c3
def mcu3.c3.ty(_rs: Array<U32>, +_fr: Bool, +_bit: Jenc.Put, +_pr: U32, +_t1: L1.JBlkTok, +_t2: L1.JBlkTok) -> Type:
  ChOut(_fr, _rs, L1.jpg.feed(blkbits(_t2), L1.jpg.feed(blkbits(_t1), _bit)), _pr, kern(),
    Jenc.encode.quant())

# the MCU's Cr block, after its Y and Cb blocks
def mcu3(
  pix: Array<U32>,
  -ys: Array<U32>,
  -bs: Array<U32>,
  -rs: Array<U32>,
  -fy: Bool,
  -fb: Bool,
  -fr: Bool,
  +bit: Jenc.Put,
  +py: U32,
  +pb: U32,
  +pr: U32,
  +t1: L1.JBlkTok,
  +d1: U32,
  e1: mcu3.e1.ty(ys, fy, bit, py, t1, d1),
  h1: {U32.is_lt(d1, 2048) == True{} : Bool},
  w1: {L1.jpg.blkwf(t1) == True{} : Bool},
  +t2: L1.JBlkTok,
  +d2: U32,
  e2: mcu3.e2.ty(bs, fb, bit, pb, t1, t2, d2),
  h2: {U32.is_lt(d2, 2048) == True{} : Bool},
  w2: {L1.jpg.blkwf(t2) == True{} : Bool},
  c3: mcu3.c3.ty(rs, fr, bit, pr, t1, t2)
) -> McuOut(Jenc.Tile{pix, ys, bs, rs, fy, fb, fr}, bit, py, pb, pr):
  (+t3, +d3, e3, h3, w3) = c3
  +kn = kern()
  +zg = Jpeg.decode.zig()
  +qs = Jenc.encode.quant()
  +p1 = L1.jpg.feed(blkbits(t1), bit)
  +p2 = L1.jpg.feed(blkbits(t2), p1)
  +p3 = L1.jpg.feed(blkbits(t3), p2)
  (t1, t2, t3, pix, d1, d2, d3, Equal.trans(Array<U32> & Jenc.Book & U32 & U32 & U32 & Jenc.Put, Jenc.encode.step.cb(
    Jenc.encode.chan.go(fy, ys, book(), bit, py, kn, zg, qs), pix, bs, rs, fb, fr, pb, pr, kn, zg, qs),
    Jenc.encode.step.cb((book(), d1, p1), pix, bs, rs, fb, fr, pb, pr, kn, zg, qs), (pix, book(), d1, d2, d3, p3),
    Equal.cong(Jenc.Book & U32 & Jenc.Put, Array<U32> & Jenc.Book & U32 & U32 & U32 & Jenc.Put, gg =>
    Jenc.encode.step.cb(gg, pix, bs, rs, fb, fr, pb, pr, kn, zg, qs), Jenc.encode.chan.go(fy, ys, book(), bit, py, kn,
    zg, qs), (book(), d1, p1), e1), Equal.trans(Array<U32> & Jenc.Book & U32 & U32 & U32 & Jenc.Put,
    Jenc.encode.step.cr(Jenc.encode.chan.go(fb, bs, book(), p1, pb, kn, zg, qs), pix, rs, fr, d1, pr, kn, zg, qs),
    Jenc.encode.step.cr((book(), d2, p2), pix, rs, fr, d1, pr, kn, zg, qs), (pix, book(), d1, d2, d3, p3),
    Equal.cong(Jenc.Book & U32 & Jenc.Put, Array<U32> & Jenc.Book & U32 & U32 & U32 & Jenc.Put, gg =>
    Jenc.encode.step.cr(gg, pix, rs, fr, d1, pr, kn, zg, qs), Jenc.encode.chan.go(fb, bs, book(), p1, pb, kn, zg, qs),
    (book(), d2, p2), e2), Equal.cong(Jenc.Book & U32 & Jenc.Put, Array<U32> & Jenc.Book & U32 & U32 & U32 &
    Jenc.Put, gg => Jenc.encode.step.end(Jenc.encode.chan.pair(gg, pix), d1, d2), Jenc.encode.chan.go(fr, rs, book(),
    p2, pr, kn, zg, qs), (book(), d3, p3), e3))), h1, h2, h3, w1, w2, w3)

# the type of mcu2's parameter e1
def mcu2.e1.ty(_ys: Array<U32>, +_fy: Bool, +_bit: Jenc.Put, +_py: U32, +_t1: L1.JBlkTok, +_d1: U32) -> Type:
  {Jenc.encode.chan.go(_fy, _ys, book(), _bit, _py, kern(), Jpeg.decode.zig(), Jenc.encode.quant()) == (book(), _d1,
    L1.jpg.feed(blkbits(_t1), _bit)) : Jenc.Book & U32 & Jenc.Put}

# the MCU's Cb and Cr blocks, after its Y block
def mcu2(
  pix: Array<U32>,
  -ys: Array<U32>,
  -bs: Array<U32>,
  rs: Array<U32>,
  -fy: Bool,
  -fb: Bool,
  +fr: Bool,
  +bit: Jenc.Put,
  +py: U32,
  +pb: U32,
  +pr: U32,
  hr: {U32.is_lt(pr, 2048) == True{} : Bool},
  +t1: L1.JBlkTok,
  +d1: U32,
  e1: mcu2.e1.ty(ys, fy, bit, py, t1, d1),
  h1: {U32.is_lt(d1, 2048) == True{} : Bool},
  w1: {L1.jpg.blkwf(t1) == True{} : Bool},
  c2: ChOut(fb, bs, L1.jpg.feed(blkbits(t1), bit), pb, kern(), Jenc.encode.quant())
) -> McuOut(Jenc.Tile{pix, ys, bs, rs, fy, fb, fr}, bit, py, pb, pr):
  (+t2, +d2, e2, h2, w2) = c2
  mcu3(pix, ys, bs, rs, fy, fb, fr, bit, py, pb, pr, t1, d1, e1, h1, w1, t2, d2, e2, h2, w2, chan_ok(fr, rs,
    L1.jpg.feed(
    blkbits(t2), L1.jpg.feed(blkbits(t1), bit)), pr, kern(), Jenc.encode.quant(), hr))

# the MCU's blocks, after its Y block
def mcu1(
  pix: Array<U32>,
  -ys: Array<U32>,
  bs: Array<U32>,
  rs: Array<U32>,
  -fy: Bool,
  +fb: Bool,
  +fr: Bool,
  +bit: Jenc.Put,
  +py: U32,
  +pb: U32,
  +pr: U32,
  hb: {U32.is_lt(pb, 2048) == True{} : Bool},
  hr: {U32.is_lt(pr, 2048) == True{} : Bool},
  c1: ChOut(fy, ys, bit, py, kern(), Jenc.encode.quant())
) -> McuOut(Jenc.Tile{pix, ys, bs, rs, fy, fb, fr}, bit, py, pb, pr):
  (+t1, +d1, e1, h1, w1) = c1
  mcu2(pix, ys, bs, rs, fy, fb, fr, bit, py, pb, pr, hr, t1, d1, e1, h1, w1, chan_ok(fb, bs,
    L1.jpg.feed(blkbits(t1),
    bit), pb, kern(), Jenc.encode.quant(), hb))

# every MCU's tile, whatever it holds, codes three blocks the decoder reads whole
def mcu(
  tt: Jenc.Tile,
  +bit: Jenc.Put,
  +py: U32,
  +pb: U32,
  +pr: U32,
  hy: {U32.is_lt(py, 2048) == True{} : Bool},
  hb: {U32.is_lt(pb, 2048) == True{} : Bool},
  hr: {U32.is_lt(pr, 2048) == True{} : Bool}
) -> McuOut(tt, bit, py, pb, pr):
  match tt:
    case Jenc.Tile{pix, ys, bs, rs, +fy, +fb, +fr}:
      mcu1(pix, ys, bs, rs, fy, fb, fr, bit, py, pb, pr, hb, hr, chan_ok(fy, ys, bit, py, kern(), Jenc.encode.quant(),
        hy))

# decode_jpeg of the state a walk ends in
def w8.out(st: Jpeg.St, +facts: U32) -> Maybe<&2, Img.Raster>:
  Img.decode_jpeg.out(Jpeg.decode.finish(st, facts))
