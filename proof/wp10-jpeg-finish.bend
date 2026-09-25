# proof/wp10-jpeg-finish: lemmas for IMG-JPG-2's last parts (block painting, component placement, the
# SOF0 refusals, the MCU walk over the frame, reading the planes out) and IMG-JPG-3's intermediate laws
# (the encoder's header walked by the decoder, the entropy-coded data unstuffed). PROOF.bend imports this
# file as W10, so the gate checks it.
import Base
import ../LAWS.bend as Laws
import ../main.bend as Img
import ../src/jpeg.bend as Jpeg
import ../src/jpeg_enc.bend as Jenc
import ./u32.bend as U32L
import ./wp6-raster.bend as R
import ./wp7-jpeg-struct.bend as W7
import ./wp8-jpeg-numeric.bend as W8

# ---- block painting (IMG-JPG-2) ----

# the decoder's pixel row of one sample's cover is jpg.cover.px's, write for write
def cv.px(
  left: Nat,
  -plane: Array<U32>,
  +x0: U32,
  +yy: U32,
  +px: U32,
  +ww: U32,
  +hh: U32,
  +vv: U32
) -> {Jpeg.decode.splat.px(left, plane, x0, yy, px, ww, hh, vv) == Laws.jpg.cover.px(left, plane, x0, yy, px, ww, hh,
  vv) : Array<U32>}:
  match left:
    case 0n:
      {==}
    case 1n+pp:
      cv.px(pp, Jpeg.decode.splat.in(U32.is_lt((x0 + px : U32), ww), U32.is_lt(yy, hh), plane, (x0 + px : U32), yy,
        ww, vv), x0, yy, (px + 1 : U32), ww, hh, vv)

# the decoder's cover of one sample is jpg.cover.py's, row for row
def cv.py(
  left: Nat,
  -plane: Array<U32>,
  +x0: U32,
  +y0: U32,
  +py: U32,
  +pw: U32,
  +ww: U32,
  +hh: U32,
  +vv: U32
) -> {Jpeg.decode.splat.py(left, plane, x0, y0, py, pw, ww, hh, vv) == Laws.jpg.cover.py(left, plane, x0, y0, py, pw,
  ww, hh, vv) : Array<U32>}:
  match left:
    case 0n:
      {==}
    case 1n+pp:
      ee = cv.px(U32.to_nat(pw), plane, x0, (y0 + py : U32), 0, ww, hh, vv)
      %ee : {Jpeg.decode.splat.py(pp, Jpeg.decode.splat.px(U32.to_nat(pw), plane, x0, (y0 + py : U32), 0, ww, hh, vv),
        x0, y0, (py + 1 : U32), pw, ww, hh, vv) == Laws.jpg.cover.py(pp, _, x0, y0, (py + 1 : U32), pw, ww, hh, vv) :
        Array<U32>}
      cv.py(pp, Jpeg.decode.splat.px(U32.to_nat(pw), plane, x0, (y0 + py : U32), 0, ww, hh, vv), x0, y0,
        (py + 1 : U32), pw, ww, hh, vv)

# the decoder's block row is jpg.cover.col's, sample for sample
def cv.col(
  left: Nat,
  -plane: Array<U32>,
  +samples: List<&2, U32>,
  +row: U32,
  +col: U32,
  +ox: U32,
  +oy: U32,
  +pw: U32,
  +ph: U32,
  +ww: U32,
  +hh: U32
) -> {Jpeg.decode.splat.col(left, plane, samples, row, col, ox, oy, pw, ph, ww, hh) ==
  Laws.jpg.cover.col(left, plane, samples, row, col, ox, oy, pw, ph, ww, hh) : Array<U32>}:
  match left:
    case 0n:
      {==}
    case 1n+pp:
      ee = cv.py(U32.to_nat(ph), plane, (ox + col * pw : U32), (oy + row * ph : U32), 0, pw, ww, hh,
        Jpeg.decode.at(samples, (row * 8 + col : U32)))
      %ee : {Jpeg.decode.splat.col(pp, Jpeg.decode.splat.py(U32.to_nat(ph), plane, (ox + col * pw : U32),
        (oy + row * ph : U32), 0, pw, ww, hh, Jpeg.decode.at(samples, (row * 8 + col : U32))), samples, row,
        (col + 1 : U32), ox, oy, pw, ph, ww, hh) == Laws.jpg.cover.col(pp, _, samples, row, (col + 1 : U32), ox, oy,
        pw, ph, ww, hh) : Array<U32>}
      cv.col(pp, Jpeg.decode.splat.py(U32.to_nat(ph), plane, (ox + col * pw : U32), (oy + row * ph : U32), 0, pw,
        ww, hh, Jpeg.decode.at(samples, (row * 8 + col : U32))), samples, row, (col + 1 : U32), ox, oy, pw, ph, ww, hh)

# the decoder's block is jpg.cover's, row for row
def cv.all(
  left: Nat,
  -plane: Array<U32>,
  +samples: List<&2, U32>,
  +row: U32,
  +ox: U32,
  +oy: U32,
  +pw: U32,
  +ph: U32,
  +ww: U32,
  +hh: U32
) -> {Jpeg.decode.splat(left, plane, samples, row, ox, oy, pw, ph, ww, hh) ==
  Laws.jpg.cover(left, plane, samples, row, ox, oy, pw, ph, ww, hh) : Array<U32>}:
  match left:
    case 0n:
      {==}
    case 1n+pp:
      ee = cv.col(8n, plane, samples, row, 0, ox, oy, pw, ph, ww, hh)
      %ee : {Jpeg.decode.splat(pp, Jpeg.decode.splat.col(8n, plane, samples, row, 0, ox, oy, pw, ph, ww, hh), samples,
        (row + 1 : U32), ox, oy, pw, ph, ww, hh) == Laws.jpg.cover(pp, _, samples, (row + 1 : U32), ox, oy, pw, ph, ww,
        hh) : Array<U32>}
      cv.all(pp, Jpeg.decode.splat.col(8n, plane, samples, row, 0, ox, oy, pw, ph, ww, hh), samples,
        (row + 1 : U32), ox, oy, pw, ph, ww, hh)

# ---- placement of any scan component (IMG-JPG-2) ----

# a scan component's placement is the placement of a one-component scan with its frame component's factors
def grid.of(
  left: Nat,
  +bi: U32,
  +comp: U32,
  +sids: List<&2, U32>,
  +ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>,
  +mx: U32,
  +my: U32,
  +hmax: U32,
  +vmax: U32,
  +ww: U32,
  +hh: U32
) -> {Laws.jpg.blocks.of(left, bi, comp, sids, ids, hs, vs, mx, my, hmax, vmax, ww, hh) == Laws.jpg.blocks(left, bi,
  Laws.jpg.fac.of(comp, sids, ids, hs), Laws.jpg.fac.of(comp, sids, ids, vs), mx, my, hmax, vmax, ww, hh) :
  List<&2, Jpeg.Geom>}:
  match left:
    case 0n:
      {==}
    case 1n+pp:
      ee = grid.of(pp, (bi + 1 : U32), comp, sids, ids, hs, vs, mx, my, hmax, vmax, ww, hh)
      %ee : {Jpeg.decode.geom.go(comp, bi, mx, my, ww, hh, hmax, vmax, sids, ids, hs, vs) <>
        Laws.jpg.blocks.of(pp, (bi + 1 : U32), comp, sids, ids, hs, vs, mx, my, hmax, vmax, ww, hh) ==
        Jpeg.decode.geom.go(0, bi, mx, my, ww, hh, hmax, vmax, [0], [0], [Laws.jpg.fac.of(comp, sids, ids, hs)],
        [Laws.jpg.fac.of(comp, sids, ids, vs)]) <> _ : List<&2, Jpeg.Geom>}
      {==}

# ---- the SOF0 refusals (IMG-JPG-2) ----

# the state a refused frame header leaves the walk in (the same state as PROOF.bend's w8.stop)
def stop(+sc: Jpeg.Scan, +tb: Jpeg.Tabs, +en: List<&2, U32>, +ri: U32, +kd: U32) -> Jpeg.St:
  Jpeg.St{Jpeg.Stop{}, Jpeg.decode.frame0(), sc, tb, en, ri, kd, 1}

# the frame reader refuses a SOF0 body
def sof.Disp(
  +body: List<&2, U32>,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> Type:
  {Jpeg.decode.dispatch(192, body, frame, scan, tabs, ent, ri, kind, bad) == stop(scan, tabs, ent, ri, kind) :
    Jpeg.St}

# a SOF0 segment read from just after its marker: when its body makes the frame reader refuse, the
# walk goes on stopped from the end of the body, whatever the body's length
def sof.seg(
  +lh: U32,
  +ll: U32,
  +body: List<&2, U32>,
  +rest: List<&2, U32>,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32,
  h_len: {U32.is_lt(Jpeg.decode.u16(lh, ll), 2) == False{} : Bool},
  h_body: {U32.to_nat((Jpeg.decode.u16(lh, ll) - 2 : U32)) == List.length(&2, U32, body) : Nat},
  h_disp: sof.Disp(body, frame, scan, tabs, ent, ri, kind, bad)
) -> {Jpeg.decode.walk(lh <> ll <> List.append(&2, U32, body, rest), Jpeg.St{Jpeg.LenHi{192}, frame, scan, tabs, ent,
  ri, kind, bad}) == Jpeg.decode.walk(rest, stop(scan, tabs, ent, ri, kind)) : Jpeg.St}:
  +slb = {Jpeg.decode.step.len.b(U32.is_lt(Jpeg.decode.u16(lh, ll), 2), 192, Jpeg.decode.u16(lh, ll), frame, scan, tabs,
    ent, ri, kind, bad) : Jpeg.St}
  Equal.trans(Jpeg.St, Jpeg.decode.walk(List.append(&2, U32, body, rest), slb),
    Jpeg.decode.walk(rest, Jpeg.decode.walk(body, slb)), Jpeg.decode.walk(rest, stop(scan, tabs, ent, ri, kind)),
    W8.walk_app(body, rest, slb),
    Equal.trans(Jpeg.St, Jpeg.decode.walk(rest, Jpeg.decode.walk(body, slb)),
      Jpeg.decode.walk(rest, Jpeg.decode.dispatch(192, body, frame, scan, tabs, ent, ri, kind, bad)),
      Jpeg.decode.walk(rest, stop(scan, tabs, ent, ri, kind)),
      Equal.cong(Jpeg.St, Jpeg.St, st => Jpeg.decode.walk(rest, st), Jpeg.decode.walk(body, slb),
        Jpeg.decode.dispatch(192, body, frame, scan, tabs, ent, ri, kind, bad),
        W7.seg.read(U32.is_lt(Jpeg.decode.u16(lh, ll), 2), Jpeg.decode.u16(lh, ll), body, 192, frame, scan, tabs, ent,
          ri, kind, bad, h_len, h_body)),
      Equal.cong(Jpeg.St, Jpeg.St, st => Jpeg.decode.walk(rest, st),
        Jpeg.decode.dispatch(192, body, frame, scan, tabs, ent, ri, kind, bad), stop(scan, tabs, ent, ri, kind),
        h_disp)))

# a frame header of a component count the decoder does not read: refused, whatever the components
def sof.cok(
  cok: Bool,
  +ww: U32,
  +hh: U32,
  +nf: U32,
  +ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>,
  +tq: List<&2, U32>,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32
) -> {Jpeg.decode.read.sof.c(cok, False{}, U32.is_eq(Jpeg.decode.vmax(hs, 0), 0), ww, hh, nf, ids, hs, vs, tq, scan,
  tabs, ent, ri, kind) == stop(scan, tabs, ent, ri, kind) : Jpeg.St}:
  match cok:
    case True{}:
      {==}
    case False{}:
      {==}

# the components read, whatever they are, then a count the decoder does not read: refused
def sof.cnt(
  cc: Jpeg.Comps,
  +ww: U32,
  +hh: U32,
  +nf: U32,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32,
  h_nf: {Bool.or(U32.is_eq(nf, 1), U32.is_eq(nf, 3)) == False{} : Bool}
) -> {Jpeg.decode.read.sof.f(cc, ww, hh, nf, scan, tabs, ent, ri, kind, bad) == stop(scan, tabs, ent, ri, kind) :
  Jpeg.St}:
  match cc:
    case Jpeg.Comps{+ids, +hs, +vs, +tq, cok}:
      es = Equal.sym(Bool, Bool.or(U32.is_eq(nf, 1), U32.is_eq(nf, 3)), False{}, h_nf)
      %es : {Jpeg.decode.read.sof.c(cok, Bool.and(_, U32.is_eq(bad, 0)), U32.is_eq(Jpeg.decode.vmax(hs, 0), 0), ww,
        hh, nf, ids, hs, vs, tq, scan, tabs, ent, ri, kind) == stop(scan, tabs, ent, ri, kind) : Jpeg.St}
      sof.cok(cok, ww, hh, nf, ids, hs, vs, tq, scan, tabs, ent, ri, kind)

# ---- words and bytes ----

# Bool.and commutes
def band_comm(aa: Bool, bb: Bool) -> {Bool.and(aa, bb) == Bool.and(bb, aa) : Bool}:
  match aa bb:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# Word.and commutes
def wand_comm(nn: Nat, aw: Word(nn), bw: Word(nn)) -> {Word.and(nn, aw, bw) == Word.and(nn, bw, aw) : Word(nn)}:
  match nn:
    case 0n:
      {==}
    case 1n+pp:
      match aw bw:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          e1 = band_comm(ab, bb)
          e2 = wand_comm(pp, at, bt)
          %e1 : {WCon{Bool.and(ab, bb), Word.and(pp, at, bt)} == WCon{_, Word.and(pp, bt, at)} : Word(1n+pp)}
          %e2 : {WCon{Bool.and(ab, bb), Word.and(pp, at, bt)} == WCon{Bool.and(ab, bb), _} : Word(1n+pp)}
          {==}

# U32.and commutes
def uand_comm(au: U32, bu: U32) -> {U32.and(au, bu) == U32.and(bu, au) : U32}:
  match au bu:
    case U32{aw} U32{bw}:
      Equal.cong(Word(32n), U32, ww => U32{ww}, Word.and(32n, aw, bw), Word.and(32n, bw, aw), wand_comm(32n, aw, bw))

# or with False on the right is the bit
def bor_false(bb: Bool) -> {Bool.or(bb, False{}) == bb : Bool}:
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# or with the zero word on the right is the word
def wor_zero(nn: Nat, aw: Word(nn)) -> {Word.or(nn, aw, Word.zero(nn)) == aw : Word(nn)}:
  match nn:
    case 0n:
      match aw:
        case WNil{}:
          {==}
    case 1n+pp:
      match aw:
        case WCon{+ab, +at}:
          e1 = bor_false(ab)
          e2 = wor_zero(pp, at)
          es1 = Equal.sym(Bool, Bool.or(ab, False{}), ab, e1)
          es2 = Equal.sym(Word(pp), Word.or(pp, at, Word.zero(pp)), at, e2)
          %es1 : {WCon{_, Word.or(pp, at, Word.zero(pp))} == WCon{ab, at} : Word(1n+pp)}
          %es2 : {WCon{ab, _} == WCon{ab, at} : Word(1n+pp)}
          {==}

# the decoder's u16 of a U32's bits 8 and up and its low byte (the mask first) is the U32, for every U32
def u16_bits(ww: U32) -> {Jpeg.decode.u16(U32.shrn(ww, 8n), U32.and(255, ww)) == ww : U32}:
  match ww:
    case U32{WCon{+b0, WCon{+b1, WCon{+b2, WCon{+b3, WCon{+b4, WCon{+b5, WCon{+b6, WCon{+b7, WCon{+b8, WCon{+b9,
      WCon{+b10, WCon{+b11, WCon{+b12, WCon{+b13, WCon{+b14, WCon{+b15, WCon{+b16, WCon{+b17, WCon{+b18, WCon{+b19,
      WCon{+b20, WCon{+b21, WCon{+b22, WCon{+b23, WCon{+b24, WCon{+b25, WCon{+b26, WCon{+b27, WCon{+b28, WCon{+b29,
      WCon{+b30, WCon{+b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      +tt = {WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18,
        WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29,
        WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}} : Word(24n)}
      ee = Equal.sym(Word(24n), Word.or(24n, tt, Word.zero(24n)), tt, wor_zero(24n, tt))
      %ee : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, _}}}}}}}}} == U32{WCon{b0,
        WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12,
        WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23,
        WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31,
        WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
      {==}

# ---- reading a plane out (IMG-JPG-2) ----

# the size walk keeps the array
def size.eq(aa: Array<U32>) -> {Array.size(U32, aa) == (aa, Laws.jpg.val(Array.size(U32, aa))) :
  Array<U32> & U32}:
  match aa:
    case ALeaf{_x}:
      {==}
    case ANode{xs, ys}:
      ee = Equal.sym(Array<U32> & U32, Array.size(U32, xs), (xs, Laws.jpg.val(Array.size(U32, xs))), size.eq(xs))
      %ee : {Array.size.node(U32, ys, _) == (ANode{xs, ys}, Laws.jpg.val(Array.size.node(U32, ys, _))) :
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

# the result of a read of the tree walk keeps the array: the reads below a node hand the node back
def getif.eq(
  -xs: Array<U32>,
  -ys: Array<U32>,
  +hh: U32,
  +ii: U32,
  zz: Bool,
  ihx: {Array.get.go(U32, xs, hh, ii) == (xs, Laws.jpg.val(Array.get.go(U32, xs, hh, ii))) : Array<U32> & U32},
  ihy: {Array.get.go(U32, ys, hh, U32.sub(ii, hh)) == (ys, Laws.jpg.val(Array.get.go(U32, ys, hh, U32.sub(ii, hh)))) :
    Array<U32> & U32}
) -> {Array.get.if(U32, xs, ys, hh, ii, zz) == (ANode{xs, ys}, Laws.jpg.val(Array.get.if(U32, xs, ys, hh, ii, zz))) :
  Array<U32> & U32}:
  match zz:
    case True{}:
      sx = Equal.sym(Array<U32> & U32, Array.get.go(U32, xs, hh, ii), (xs, Laws.jpg.val(Array.get.go(U32, xs, hh,
        ii))), ihx)
      %sx : {Array.swap.lo(U32, ys, _) == (ANode{xs, ys}, Laws.jpg.val(Array.swap.lo(U32, ys, _))) : Array<U32> & U32}
      {==}
    case False{}:
      sy = Equal.sym(Array<U32> & U32, Array.get.go(U32, ys, hh, U32.sub(ii, hh)),
        (ys, Laws.jpg.val(Array.get.go(U32, ys, hh, U32.sub(ii, hh)))), ihy)
      %sy : {Array.swap.hi(U32, xs, _) == (ANode{xs, ys}, Laws.jpg.val(Array.swap.hi(U32, xs, _))) : Array<U32> & U32}
      {==}

# the tree walk of a read hands the array back
def getgo.eq(
  aa: Array<U32>,
  +nn: U32,
  +ii: U32
) -> {Array.get.go(U32, aa, nn, ii) == (aa, Laws.jpg.val(Array.get.go(U32, aa, nn, ii))) : Array<U32> & U32}:
  match aa:
    case ALeaf{+_xx}:
      {==}
    case ANode{xs, ys}:
      getif.eq(xs, ys, U32.shr(nn), ii, U32.is_lt(ii, U32.shr(nn)), getgo.eq(xs, U32.shr(nn), ii),
        getgo.eq(ys, U32.shr(nn), U32.sub(ii, U32.shr(nn))))

# the tree walk of a read, at the array's own size and the masked index, hands the array back
def GoAt(-aa: Array<U32>, +ii: U32) -> Type:
  {Array.get.go(U32, aa, Laws.jpg.val(Array.size(U32, aa)), U32.and(ii, U32.sub(Laws.jpg.val(Array.size(U32, aa)),
    1))) == (aa, Laws.jpg.val(Array.get.go(U32, aa, Laws.jpg.val(Array.size(U32, aa)), U32.and(ii,
    U32.sub(Laws.jpg.val(Array.size(U32, aa)), 1))))) : Array<U32> & U32}

# the tree walk of a read of bb, at the size read from cc, hands bb back
def GoAt2(-bb: Array<U32>, -cc: Array<U32>, +ii: U32) -> Type:
  {Array.get.go(U32, bb, Laws.jpg.val(Array.size(U32, cc)), U32.and(ii, U32.sub(Laws.jpg.val(Array.size(U32, cc)),
    1))) == (bb, Laws.jpg.val(Array.get.go(U32, bb, Laws.jpg.val(Array.size(U32, cc)), U32.and(ii,
    U32.sub(Laws.jpg.val(Array.size(U32, cc)), 1))))) : Array<U32> & U32}

# the size walk's statement moved along an equality of arrays
def size.tr(
  -bb: Array<U32>,
  -aa: Array<U32>,
  ee: {bb == aa : Array<U32>},
  hh: {Array.size(U32, bb) == (bb, Laws.jpg.val(Array.size(U32, bb))) : Array<U32> & U32}
) -> {Array.size(U32, aa) == (aa, Laws.jpg.val(Array.size(U32, aa))) : Array<U32> & U32}:
  %ee : {Array.size(U32, _) == (_, Laws.jpg.val(Array.size(U32, _))) : Array<U32> & U32}
  hh

# the tree walk's statement moved along an equality of arrays
def getgo.tr(
  -bb: Array<U32>,
  -aa: Array<U32>,
  +nn: U32,
  +ii: U32,
  ee: {bb == aa : Array<U32>},
  hh: {Array.get.go(U32, bb, nn, ii) == (bb, Laws.jpg.val(Array.get.go(U32, bb, nn, ii))) : Array<U32> & U32}
) -> {Array.get.go(U32, aa, nn, ii) == (aa, Laws.jpg.val(Array.get.go(U32, aa, nn, ii))) : Array<U32> & U32}:
  %ee : {Array.get.go(U32, _, nn, ii) == (_, Laws.jpg.val(Array.get.go(U32, _, nn, ii))) : Array<U32> & U32}
  hh

# a read, once the size walk has handed the array back, hands it back too
def get.from(
  -aa: Array<U32>,
  +ii: U32,
  hs: {Array.size(U32, aa) == (aa, Laws.jpg.val(Array.size(U32, aa))) : Array<U32> & U32},
  hg: GoAt(aa, ii)
) -> {Array.get(U32, aa, ii) == (aa, Laws.jpg.val(Array.get(U32, aa, ii))) : Array<U32> & U32}:
  ss = Equal.sym(Array<U32> & U32, Array.size(U32, aa), (aa, Laws.jpg.val(Array.size(U32, aa))), hs)
  %ss : {Array.get.at(U32, ii, _) == (aa, Laws.jpg.val(Array.get.at(U32, ii, _))) : Array<U32> & U32}
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
  %eb : {Array.get.go(U32, _, Laws.jpg.val(Array.size(U32, aa)), U32.and(ii, U32.sub(Laws.jpg.val(Array.size(U32,
    aa)), 1))) ==
    (_, Laws.jpg.val(Array.get.go(U32, _, Laws.jpg.val(Array.size(U32, aa)), U32.and(ii,
      U32.sub(Laws.jpg.val(Array.size(U32, aa)),
    1))))) : Array<U32> & U32}
  %ec : {Array.get.go(U32, bb, Laws.jpg.val(Array.size(U32, _)), U32.and(ii, U32.sub(Laws.jpg.val(Array.size(U32,
    _)), 1))) ==
    (bb, Laws.jpg.val(Array.get.go(U32, bb, Laws.jpg.val(Array.size(U32, _)), U32.and(ii,
      U32.sub(Laws.jpg.val(Array.size(U32, _)),
    1))))) : Array<U32> & U32}
  hh

# the tree walk hands the array back, at the size read from a second copy
def getgo.at(
  -aa: Array<U32>,
  +ii: U32,
  dd: Dup(aa)
) -> GoAt(aa, ii):
  (c1, c2, e1, e2) = dd
  +nn = Laws.jpg.val(Array.size(U32, c2))
  getgo.tr2(c1, c2, aa, ii, e1, e2, getgo.eq(c1, nn, U32.and(ii, U32.sub(nn, 1))))

# a read hands the array back, from copies of it
def get.eq.d(
  -aa: Array<U32>,
  +ii: U32,
  dd: Dup(aa)
) -> {Array.get(U32, aa, ii) == (aa, Laws.jpg.val(Array.get(U32, aa, ii))) : Array<U32> & U32}:
  (b1, b2, e1, e2) = dd
  get.from(aa, ii, size.tr(b1, aa, e1, size.eq(b1)), getgo.at(aa, ii, dup.tr(b2, aa, e2, dup(b2))))

# a read hands the array back
def get.eq(aa: Array<U32>, +ii: U32) -> {Array.get(U32, aa, ii) == (aa, Laws.jpg.val(Array.get(U32, aa, ii))) :
  Array<U32> & U32}:
  get.eq.d(aa, ii, dup(aa))

# the read statement moved along an equality of arrays
def get.tr(
  -bb: Array<U32>,
  -aa: Array<U32>,
  +ii: U32,
  ee: {bb == aa : Array<U32>},
  hh: {Array.get(U32, bb, ii) == (bb, Laws.jpg.val(Array.get(U32, bb, ii))) : Array<U32> & U32}
) -> {Array.get(U32, aa, ii) == (aa, Laws.jpg.val(Array.get(U32, aa, ii))) : Array<U32> & U32}:
  %ee : {Array.get(U32, _, ii) == (_, Laws.jpg.val(Array.get(U32, _, ii))) : Array<U32> & U32}
  hh

# a plane read out from point jj on: element mm is the plane's point jj + mm
def emit.at(
  nn: Nat,
  mm: Nat,
  -aa: Array<U32>,
  +jj: U32,
  dd: Dup(aa),
  hm: {Nat.is_lt(mm, nn) == True{} : Bool}
) -> {List.get(&2, U32, Jpeg.decode.emit(nn, Array.get(U32, aa, jj), (jj + 1 : U32)), mm) ==
  Some{Laws.jpg.val(Array.get(U32, aa, Laws.jpg.idx(mm, jj)))} : Maybe<&2, U32>}:
  match nn:
    case 0n:
      -_d = dd
      Empty.absurd({List.get(&2, U32, Jpeg.decode.emit(0n, Array.get(U32, aa, jj), (jj + 1 : U32)), mm) ==
        Some{Laws.jpg.val(Array.get(U32, aa, Laws.jpg.idx(mm,
          jj)))} : Maybe<&2, U32>}, U32L.false_true(Equal.trans(Bool, False{},
        Nat.is_lt(mm, 0n), True{}, R.lt_zero_false(mm), hm)))
    case 1n+pp:
      match mm:
        case 0n:
          (b1, _b2, e1, _e2) = dd
          se = Equal.sym(Array<U32> & U32, Array.get(U32, aa, jj), (aa, Laws.jpg.val(Array.get(U32, aa, jj))),
            get.tr(b1, aa, jj, e1, get.eq(b1, jj)))
          %se : {List.get(&2, U32, Jpeg.decode.emit(1n+pp, _, (jj + 1 : U32)), 0n) ==
            Some{Laws.jpg.val(Array.get(U32, aa, jj))} : Maybe<&2, U32>}
          {==}
        case 1n+qq:
          (b1, b2, e1, e2) = dd
          se = Equal.sym(Array<U32> & U32, Array.get(U32, aa, jj), (aa, Laws.jpg.val(Array.get(U32, aa, jj))),
            get.tr(b1, aa, jj, e1, get.eq(b1, jj)))
          %se : {List.get(&2, U32, Jpeg.decode.emit(1n+pp, _, (jj + 1 : U32)), 1n+qq) ==
            Some{Laws.jpg.val(Array.get(U32, aa, Laws.jpg.idx(1n+qq, jj)))} : Maybe<&2, U32>}
          emit.at(pp, qq, aa, (jj + 1 : U32), dup.tr(b2, aa, e2, dup(b2)), hm)

# jj advanced one step at a time, mm times, is jj + mm when that stays within the U32 tt
def idx.nat(
  +mm: Nat,
  +jj: U32,
  +tt: U32,
  +hh: {Nat.is_le(Nat.add(U32.to_nat(jj), mm), U32.to_nat(tt)) == True{} : Bool}
) -> {U32.to_nat(Laws.jpg.idx(mm, jj)) == Nat.add(U32.to_nat(jj), mm) : Nat}:
  match mm:
    case 0n:
      Equal.sym(Nat, Nat.add(U32.to_nat(jj), 0n), U32.to_nat(jj), R.add_zero(U32.to_nat(jj)))
    case 1n+(+pp):
      +jn = U32.to_nat(jj)
      +h1 = {R.le_trans(Nat.add(jn, 1n), Nat.add(jn, 1n+pp), U32.to_nat(tt), R.le_add_mono(jn, 1n, 1n+pp,
        R.le_zero(pp)), hh) : {Nat.is_le(Nat.add(jn, 1n), U32.to_nat(tt)) == True{} : Bool}}
      +e1 = {R.u32_add_below(jj, 1, tt, h1) : {U32.to_nat((jj + 1 : U32)) == Nat.add(jn, 1n) : Nat}}
      +ea = {Equal.trans(Nat, Nat.add(U32.to_nat((jj + 1 : U32)), pp), Nat.add(Nat.add(jn, 1n), pp), Nat.add(jn, 1n+pp),
        Equal.cong(Nat, Nat, xx => Nat.add(xx, pp), U32.to_nat((jj + 1 : U32)), Nat.add(jn, 1n), e1),
        R.add_assoc(jn, 1n, pp)) : {Nat.add(U32.to_nat((jj + 1 : U32)), pp) == Nat.add(jn, 1n+pp) : Nat}}
      h2 = Equal.trans(Bool, Nat.is_le(Nat.add(U32.to_nat((jj + 1 : U32)), pp), U32.to_nat(tt)),
        Nat.is_le(Nat.add(jn, 1n+pp), U32.to_nat(tt)), True{}, Equal.cong(Nat, Bool, xx => Nat.is_le(xx,
        U32.to_nat(tt)), Nat.add(U32.to_nat((jj + 1 : U32)), pp), Nat.add(jn, 1n+pp), ea), hh)
      Equal.trans(Nat, U32.to_nat(Laws.jpg.idx(pp, (jj + 1 : U32))), Nat.add(U32.to_nat((jj + 1 : U32)), pp),
        Nat.add(jn, 1n+pp), idx.nat(pp, (jj + 1 : U32), tt, h2), ea)

# the index reached by counting kk steps from 0 is kk
def idx.of(+kk: U32) -> {Laws.jpg.idx(U32.to_nat(kk), 0) == kk : U32}:
  +kn = U32.to_nat(kk)
  +ix = Laws.jpg.idx(kn, 0)
  U32L.ueq(ix, kk, Equal.trans(Bool, U32.is_eq(ix, kk), Nat.is_eq(U32.to_nat(ix), kn), True{}, R.u32_eq(ix, kk),
    Equal.trans(Bool, Nat.is_eq(U32.to_nat(ix), kn), Nat.is_eq(kn, kn), True{}, Equal.cong(Nat, Bool,
    xx => Nat.is_eq(xx, kn), U32.to_nat(ix), kn, idx.nat(kn, 0, kk, R.le_refl(kn))), R.nat_eq_refl(kn))))

# ---- the MCU walk over the frame (IMG-JPG-2) ----

# the walk's next position, the restart count dropped
def nxt(+ctrl: Jpeg.Ctrl, +fr: Jpeg.Frame, +sc: Jpeg.Scan, +ri: U32) -> Jpeg.Ctrl:
  Laws.jpg.pos(Jpeg.decode.adv.ctrl(Jpeg.decode.adv(ctrl, fr, sc, ri)))

# the positions of the next left blocks, the restart count dropped at every step
def tr(left: Nat, +ctrl: Jpeg.Ctrl, +fr: Jpeg.Frame, +sc: Jpeg.Scan, +ri: U32) -> List<&2, Jpeg.Ctrl>:
  match left:
    case 0n:
      []
    case 1n+pp:
      Laws.jpg.pos(ctrl) <> tr(pp, nxt(ctrl, fr, sc, ri), fr, sc, ri)

# the first MCU of the next MCU row, or the next MCU of this row
def mx.res(inb: Bool, +mcu: U32, +mx: U32, +my: U32) -> Jpeg.Ctrl:
  match inb:
    case True{}:
      Jpeg.Ctrl{0, 0, mx, my, mcu, 0}
    case False{}:
      Jpeg.Ctrl{0, 0, 0, (my + 1 : U32), mcu, 0}

# where the walk goes from data unit bi of scan component comp: the next unit, the next component,
# or the next MCU, by whether the component and then the scan have more
def bi.res(more: Bool, next: Bool, inb: Bool, +comp: U32, +bi: U32, +mx: U32, +my: U32, +mcu: U32) -> Jpeg.Ctrl:
  match more:
    case True{}:
      Jpeg.Ctrl{comp, (bi + 1 : U32), mx, my, mcu, 0}
    case False{}:
      match next:
        case True{}:
          Jpeg.Ctrl{(comp + 1 : U32), 0, mx, my, mcu, 0}
        case False{}:
          mx.res(inb, (mcu + 1 : U32), (mx + 1 : U32), my)

# a new MCU starts at unit 0 of component 0, restart or not
def due.pos(
  zero: Bool,
  hit: Bool,
  +mcu: U32,
  +mx: U32,
  +my: U32,
  +rst: U32
) -> {Laws.jpg.pos(Jpeg.decode.adv.ctrl(Jpeg.decode.adv.due.b(zero, hit, mcu, mx, my, rst))) ==
  Jpeg.Ctrl{0, 0, mx, my, mcu, 0} : Jpeg.Ctrl}:
  match zero hit:
    case True{} _hit:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# the next MCU in this row, or the first of the next row
def mx.pos(
  inb: Bool,
  +mcu: U32,
  +mx: U32,
  +my: U32,
  +rst: U32,
  +ri: U32
) -> {Laws.jpg.pos(Jpeg.decode.adv.ctrl(Jpeg.decode.adv.mx(inb, mcu, mx, my, rst, ri))) == mx.res(inb, mcu, mx, my) :
  Jpeg.Ctrl}:
  match inb:
    case True{}:
      due.pos(U32.is_eq(ri, 0), U32.is_eq(U32.mod(mcu, Jpeg.decode.ri.nz(ri)), 0), mcu, mx, my, rst)
    case False{}:
      due.pos(U32.is_eq(ri, 0), U32.is_eq(U32.mod(mcu, Jpeg.decode.ri.nz(ri)), 0), mcu, 0, (my + 1 : U32), rst)

# after a component's last unit: the next component, or the next MCU
def comp.pos(
  next: Bool,
  +comp: U32,
  +bi: U32,
  +mx: U32,
  +my: U32,
  +mcu: U32,
  +rst: U32,
  +ww: U32,
  +hmax: U32,
  +ri: U32
) -> {Laws.jpg.pos(Jpeg.decode.adv.ctrl(Jpeg.decode.adv.comp(next, comp, mx, my, mcu, rst, ww, hmax, ri))) ==
  bi.res(False{}, next, U32.is_lt((mx + 1 : U32), Jpeg.decode.ceil(ww, (hmax * 8 : U32))), comp, bi, mx, my, mcu) :
  Jpeg.Ctrl}:
  match next:
    case True{}:
      {==}
    case False{}:
      mx.pos(U32.is_lt((mx + 1 : U32), Jpeg.decode.ceil(ww, (hmax * 8 : U32))), (mcu + 1 : U32), (mx + 1 : U32), my,
        rst,
        ri)

# one step of the walk from data unit bi
def bi.pos(
  more: Bool,
  +comp: U32,
  +bi: U32,
  +mx: U32,
  +my: U32,
  +mcu: U32,
  +rst: U32,
  +ww: U32,
  +hmax: U32,
  +ns: U32,
  +ri: U32
) -> {Laws.jpg.pos(Jpeg.decode.adv.ctrl(Jpeg.decode.adv.bi(more, comp, bi, mx, my, mcu, rst, ww, hmax, ns, ri))) ==
  bi.res(more, U32.is_lt((comp + 1 : U32), ns), U32.is_lt((mx + 1 : U32), Jpeg.decode.ceil(ww, (hmax * 8 : U32))),
  comp, bi, mx, my, mcu) : Jpeg.Ctrl}:
  match more:
    case True{}:
      {==}
    case False{}:
      comp.pos(U32.is_lt((comp + 1 : U32), ns), comp, bi, mx, my, mcu, rst, ww, hmax, ri)

# one step of the walk, whatever the restart count: the next unit, component or MCU
def nxt.eq(
  +comp: U32,
  +bi: U32,
  +mx: U32,
  +my: U32,
  +mcu: U32,
  +rst: U32,
  +ww: U32,
  +hh: U32,
  +nf: U32,
  +ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>,
  +tq: List<&2, U32>,
  +hmax: U32,
  +vmax: U32,
  +ns: U32,
  +sids: List<&2, U32>,
  +td: List<&2, U32>,
  +ta: List<&2, U32>,
  +ss: U32,
  +se: U32,
  +ah: U32,
  +ri: U32
) -> {nxt(Jpeg.Ctrl{comp, bi, mx, my, mcu, rst}, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax},
  Jpeg.Scan{ns, sids, td, ta, ss, se, ah}, ri) == bi.res(U32.is_lt((bi + 1 : U32), Laws.jpg.units(comp, sids, ids, hs,
  vs)), U32.is_lt((comp + 1 : U32), ns), U32.is_lt((mx + 1 : U32), Jpeg.decode.ceil(ww, (hmax * 8 : U32))), comp, bi,
  mx, my, mcu) : Jpeg.Ctrl}:
  bi.pos(U32.is_lt((bi + 1 : U32), Laws.jpg.units(comp, sids, ids, hs, vs)), comp, bi, mx, my, mcu, rst, ww, hmax, ns,
    ri)

# the walk from a position does not depend on the restart count it holds
def tr.pos(
  left: Nat,
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
  +ns: U32,
  +sids: List<&2, U32>,
  +td: List<&2, U32>,
  +ta: List<&2, U32>,
  +ss: U32,
  +se: U32,
  +ah: U32,
  +ri: U32
) -> {tr(left, ctrl, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, Jpeg.Scan{ns, sids, td, ta, ss, se, ah},
  ri) ==
  tr(left, Laws.jpg.pos(ctrl), Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, Jpeg.Scan{ns, sids, td, ta, ss, se,
  ah}, ri) : List<&2, Jpeg.Ctrl>}:
  match left:
    case 0n:
      {==}
    case 1n+pp:
      match ctrl:
        case Jpeg.Ctrl{+comp, +bi, +mx, +my, +mcu, +rst}:
          +fr = {Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax} : Jpeg.Frame}
          +sc = {Jpeg.Scan{ns, sids, td, ta, ss, se, ah} : Jpeg.Scan}
          +res = {bi.res(U32.is_lt((bi + 1 : U32), Laws.jpg.units(comp, sids, ids, hs, vs)), U32.is_lt((comp + 1 : U32),
            ns), U32.is_lt((mx + 1 : U32), Jpeg.decode.ceil(ww, (hmax * 8 : U32))), comp, bi, mx, my, mcu) : Jpeg.Ctrl}
          e1 = nxt.eq(comp, bi, mx, my, mcu, rst, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, ns, sids, td, ta, ss, se, ah,
            ri)
          e0 = nxt.eq(comp, bi, mx, my, mcu, 0, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, ns, sids, td, ta, ss, se, ah,
            ri)
          Equal.cong(Jpeg.Ctrl, List<&2, Jpeg.Ctrl>, cc => {Jpeg.Ctrl{comp, bi, mx, my, mcu, 0} <> tr(pp, cc, fr, sc,
            ri) :
            List<&2, Jpeg.Ctrl>}, nxt(Jpeg.Ctrl{comp, bi, mx, my, mcu, rst}, fr, sc, ri),
            nxt(Jpeg.Ctrl{comp, bi, mx, my, mcu, 0}, fr, sc, ri),
            Equal.trans(Jpeg.Ctrl, nxt(Jpeg.Ctrl{comp, bi, mx, my, mcu, rst}, fr, sc, ri), res,
              nxt(Jpeg.Ctrl{comp, bi, mx, my, mcu, 0}, fr, sc, ri), e1, Equal.sym(Jpeg.Ctrl,
              nxt(Jpeg.Ctrl{comp, bi, mx, my, mcu, 0}, fr, sc, ri), res, e0)))

# the decoder's trace is the walk with the restart count dropped
def trace.tr(
  +left: Nat,
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
  +ns: U32,
  +sids: List<&2, U32>,
  +td: List<&2, U32>,
  +ta: List<&2, U32>,
  +ss: U32,
  +se: U32,
  +ah: U32,
  +ri: U32
) -> {Laws.jpg.trace(left, ctrl, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, Jpeg.Scan{ns, sids, td, ta, ss,
  se, ah}, ri) == tr(left, ctrl, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, Jpeg.Scan{ns, sids, td, ta, ss,
  se, ah}, ri) : List<&2, Jpeg.Ctrl>}:
  match left:
    case 0n:
      {==}
    case 1n+(+pp):
      +fr = {Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax} : Jpeg.Frame}
      +sc = {Jpeg.Scan{ns, sids, td, ta, ss, se, ah} : Jpeg.Scan}
      +nc = {Jpeg.decode.adv.ctrl(Jpeg.decode.adv(ctrl, fr, sc, ri)) : Jpeg.Ctrl}
      Equal.cong(List<&2, Jpeg.Ctrl>, List<&2, Jpeg.Ctrl>, ll => {Laws.jpg.pos(ctrl) <> ll : List<&2, Jpeg.Ctrl>},
        Laws.jpg.trace(pp, nc, fr, sc, ri), tr(pp, Laws.jpg.pos(nc), fr, sc, ri),
        Equal.trans(List<&2, Jpeg.Ctrl>, Laws.jpg.trace(pp, nc, fr, sc, ri), tr(pp, nc, fr, sc, ri),
          tr(pp, Laws.jpg.pos(nc), fr, sc, ri),
          trace.tr(pp, nc, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, ns, sids, td, ta, ss, se, ah, ri),
          tr.pos(pp, nc, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, ns, sids, td, ta, ss, se, ah, ri)))

# n is below n + 1
def lt.succ(+nn: Nat) -> {Nat.is_lt(nn, 1n+nn) == True{} : Bool}:
  match nn:
    case 0n:
      {==}
    case 1n+pp:
      lt.succ(pp)

# n is not below n
def lt.irr(+nn: Nat) -> {Nat.is_lt(nn, nn) == False{} : Bool}:
  match nn:
    case 0n:
      {==}
    case 1n+pp:
      lt.irr(pp)

# one less than a number above 0
def npred(nn: Nat) -> Nat:
  match nn:
    case 0n:
      0n
    case 1n+pp:
      pp

# a number above 0 is one more than its predecessor
def succ.of(+nn: Nat, hh: {Nat.is_lt(0n, nn) == True{} : Bool}) -> {1n+npred(nn) == nn : Nat}:
  match nn:
    case 0n:
      Empty.absurd({1n == 0n : Nat}, U32L.false_true(hh))
    case 1n+_pp:
      {==}

# a U32 above 0 is one more than its predecessor, as a number
def pos.nat(+uu: U32, hh: {U32.is_lt(0, uu) == True{} : Bool}) -> {1n+npred(U32.to_nat(uu)) == U32.to_nat(uu) : Nat}:
  succ.of(U32.to_nat(uu), Equal.trans(Bool, Nat.is_lt(0n, U32.to_nat(uu)), U32.is_lt(0, uu), True{},
    Equal.sym(Bool, U32.is_lt(0, uu), Nat.is_lt(0n, U32.to_nat(uu)), R.u32_lt(0, uu)), hh))

# xx + 1 does not wrap while xx + 1 + qq is some U32's value
def inc.nat(
  +xx: U32,
  +uu: U32,
  +qq: Nat,
  +hb: {Nat.add(U32.to_nat(xx), 1n+qq) == U32.to_nat(uu) : Nat}
) -> {U32.to_nat((xx + 1 : U32)) == Nat.add(U32.to_nat(xx), 1n) : Nat}:
  +bn = U32.to_nat(xx)
  R.u32_add_below(xx, 1, uu, Equal.trans(Bool, Nat.is_le(Nat.add(bn, 1n), U32.to_nat(uu)),
    Nat.is_le(Nat.add(bn, 1n), Nat.add(bn, 1n+qq)), True{}, Equal.cong(Nat, Bool, zz => Nat.is_le(Nat.add(bn, 1n), zz),
    U32.to_nat(uu), Nat.add(bn, 1n+qq), Equal.sym(Nat, Nat.add(bn, 1n+qq), U32.to_nat(uu), hb)),
    R.le_add_mono(bn, 1n, 1n+qq, R.le_zero(qq))))

# a counter two or more below its bound: the next is still below it
def lt.more(
  +xx: U32,
  +uu: U32,
  +pp: Nat,
  +hb: {Nat.add(U32.to_nat(xx), 1n+(1n+pp)) == U32.to_nat(uu) : Nat}
) -> {U32.is_lt((xx + 1 : U32), uu) == True{} : Bool}:
  +bn = U32.to_nat(xx)
  +e1 = {inc.nat(xx, uu, 1n+pp, hb) : {U32.to_nat((xx + 1 : U32)) == Nat.add(bn, 1n) : Nat}}
  Equal.trans(Bool, U32.is_lt((xx + 1 : U32), uu), Nat.is_lt(U32.to_nat((xx + 1 : U32)), U32.to_nat(uu)), True{},
    R.u32_lt((xx + 1 : U32), uu), Equal.trans(Bool, Nat.is_lt(U32.to_nat((xx + 1 : U32)), U32.to_nat(uu)),
    Nat.is_lt(Nat.add(bn, 1n), Nat.add(bn, 1n+(1n+pp))), True{}, Equal.trans(Bool,
    Nat.is_lt(U32.to_nat((xx + 1 : U32)), U32.to_nat(uu)), Nat.is_lt(Nat.add(bn, 1n), U32.to_nat(uu)),
    Nat.is_lt(Nat.add(bn, 1n), Nat.add(bn, 1n+(1n+pp))), Equal.cong(Nat, Bool, zz => Nat.is_lt(zz, U32.to_nat(uu)),
    U32.to_nat((xx + 1 : U32)), Nat.add(bn, 1n), e1), Equal.cong(Nat, Bool, zz => Nat.is_lt(Nat.add(bn, 1n), zz),
    U32.to_nat(uu), Nat.add(bn, 1n+(1n+pp)), Equal.sym(Nat, Nat.add(bn, 1n+(1n+pp)), U32.to_nat(uu), hb))),
    R.lt_add_mono(bn, 1n, 1n+(1n+pp), {==})))

# a counter one below its bound: the next is not below it
def lt.last(
  +xx: U32,
  +uu: U32,
  +hb: {Nat.add(U32.to_nat(xx), 1n) == U32.to_nat(uu) : Nat}
) -> {U32.is_lt((xx + 1 : U32), uu) == False{} : Bool}:
  +bn = U32.to_nat(xx)
  +e1 = {inc.nat(xx, uu, 0n, hb) : {U32.to_nat((xx + 1 : U32)) == Nat.add(bn, 1n) : Nat}}
  Equal.trans(Bool, U32.is_lt((xx + 1 : U32), uu), Nat.is_lt(U32.to_nat((xx + 1 : U32)), U32.to_nat(uu)), False{},
    R.u32_lt((xx + 1 : U32), uu), Equal.trans(Bool, Nat.is_lt(U32.to_nat((xx + 1 : U32)), U32.to_nat(uu)),
    Nat.is_lt(U32.to_nat(uu), U32.to_nat(uu)), False{}, Equal.cong(Nat, Bool, zz => Nat.is_lt(zz, U32.to_nat(uu)),
    U32.to_nat((xx + 1 : U32)), U32.to_nat(uu), Equal.trans(Nat, U32.to_nat((xx + 1 : U32)), Nat.add(bn, 1n),
    U32.to_nat(uu), e1, hb)), lt.irr(U32.to_nat(uu))))

# a counter two or more below its bound: the next is one or more below it
def lt.next(
  +xx: U32,
  +uu: U32,
  +pp: Nat,
  +hb: {Nat.add(U32.to_nat(xx), 1n+(1n+pp)) == U32.to_nat(uu) : Nat}
) -> {Nat.add(U32.to_nat((xx + 1 : U32)), 1n+pp) == U32.to_nat(uu) : Nat}:
  +bn = U32.to_nat(xx)
  Equal.trans(Nat, Nat.add(U32.to_nat((xx + 1 : U32)), 1n+pp), Nat.add(Nat.add(bn, 1n), 1n+pp), U32.to_nat(uu),
    Equal.cong(Nat, Nat, zz => Nat.add(zz, 1n+pp), U32.to_nat((xx + 1 : U32)), Nat.add(bn, 1n), inc.nat(xx, uu, 1n+pp,
    hb)), Equal.trans(Nat, Nat.add(Nat.add(bn, 1n), 1n+pp), Nat.add(bn, 1n+(1n+pp)), U32.to_nat(uu),
    R.add_assoc(bn, 1n, 1n+pp), hb))

# the last of kk + 1 data units counted from 0 is one below their count
def last.nat(
  +kk: Nat,
  +uu: U32,
  +hs: {1n+kk == U32.to_nat(uu) : Nat}
) -> {Nat.add(U32.to_nat(Laws.jpg.idx(kk, 0)), 1n) == U32.to_nat(uu) : Nat}:
  +hle = {Equal.trans(Bool, Nat.is_le(kk, U32.to_nat(uu)), Nat.is_le(kk, 1n+kk), True{}, Equal.cong(Nat, Bool,
    zz => Nat.is_le(kk, zz), U32.to_nat(uu), 1n+kk, Equal.sym(Nat, 1n+kk, U32.to_nat(uu), hs)), R.lt_le(kk, 1n+kk,
    lt.succ(kk))) : {Nat.is_le(kk, U32.to_nat(uu)) == True{} : Bool}}
  +ei = {idx.nat(kk, 0, uu, hle) : {U32.to_nat(Laws.jpg.idx(kk, 0)) == kk : Nat}}
  Equal.trans(Nat, Nat.add(U32.to_nat(Laws.jpg.idx(kk, 0)), 1n), Nat.add(kk, 1n), U32.to_nat(uu),
    Equal.cong(Nat, Nat, zz => Nat.add(zz, 1n), U32.to_nat(Laws.jpg.idx(kk, 0)), kk, ei), Equal.trans(Nat,
    Nat.add(kk, 1n), 1n+Nat.add(kk, 0n), U32.to_nat(uu), R.add_succ(kk, 0n), Equal.trans(Nat, 1n+Nat.add(kk, 0n),
    1n+kk, U32.to_nat(uu), Equal.cong(Nat, Nat, zz => 1n+zz, Nat.add(kk, 0n), kk, R.add_zero(kk)), hs)))

# a false accumulator stays false
def uok.false(
  ll: Nat,
  +comp: U32,
  +sids: List<&2, U32>,
  +ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>
) -> {Laws.jpg.units.ok(ll, comp, sids, ids, hs, vs, False{}) == False{} : Bool}:
  match ll:
    case 0n:
      {==}
    case 1n+pp:
      uok.false(pp, (comp + 1 : U32), sids, ids, hs, vs)

# a true answer had a true accumulator
def uok.acc(
  ll: Nat,
  +comp: U32,
  +sids: List<&2, U32>,
  +ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>,
  ok: Bool,
  hh: {Laws.jpg.units.ok(ll, comp, sids, ids, hs, vs, ok) == True{} : Bool}
) -> {ok == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, U32L.false_true(Equal.trans(Bool, False{}, Laws.jpg.units.ok(ll, comp,
        sids, ids, hs, vs, False{}), True{}, Equal.sym(Bool, Laws.jpg.units.ok(ll, comp, sids, ids, hs, vs, False{}),
        False{}, uok.false(ll, comp, sids, ids, hs, vs)), hh)))

# the length of two lists of positions
def len.app(
  xs: List<&2, Jpeg.Ctrl>,
  -ys: List<&2, Jpeg.Ctrl>
) -> {List.length(&2, Jpeg.Ctrl, List.append(&2, Jpeg.Ctrl, xs, ys)) == Nat.add(List.length(&2, Jpeg.Ctrl, xs),
  List.length(&2, Jpeg.Ctrl, ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case _hd <> tl:
      Equal.cong(Nat, Nat, zz => 1n+zz, List.length(&2, Jpeg.Ctrl, List.append(&2, Jpeg.Ctrl, tl, ys)),
        Nat.add(List.length(&2, Jpeg.Ctrl, tl), List.length(&2, Jpeg.Ctrl, ys)), len.app(tl, ys))

# appending positions is associative
def app.assoc(
  xs: List<&2, Jpeg.Ctrl>,
  -ys: List<&2, Jpeg.Ctrl>,
  -zs: List<&2, Jpeg.Ctrl>
) -> {List.append(&2, Jpeg.Ctrl, List.append(&2, Jpeg.Ctrl, xs, ys), zs) == List.append(&2, Jpeg.Ctrl, xs,
  List.append(&2, Jpeg.Ctrl, ys, zs)) : List<&2, Jpeg.Ctrl>}:
  match xs:
    case Nil{}:
      {==}
    case +hd <> tl:
      Equal.cong(List<&2, Jpeg.Ctrl>, List<&2, Jpeg.Ctrl>, ll => {hd <> ll : List<&2, Jpeg.Ctrl>},
        List.append(&2, Jpeg.Ctrl, List.append(&2, Jpeg.Ctrl, tl, ys), zs), List.append(&2, Jpeg.Ctrl, tl,
        List.append(&2, Jpeg.Ctrl, ys, zs)), app.assoc(tl, ys, zs))

# no positions appended
def app.nil(xs: List<&2, Jpeg.Ctrl>) -> {List.append(&2, Jpeg.Ctrl, xs, []) == xs : List<&2, Jpeg.Ctrl>}:
  match xs:
    case Nil{}:
      {==}
    case +hd <> tl:
      Equal.cong(List<&2, Jpeg.Ctrl>, List<&2, Jpeg.Ctrl>, ll => {hd <> ll : List<&2, Jpeg.Ctrl>},
        List.append(&2, Jpeg.Ctrl, tl, []), tl, app.nil(tl))

# the walk from cc visits the positions ll, then goes on from ee: kk blocks after them are the walk from ee
def Run(
  -ll: List<&2, Jpeg.Ctrl>,
  +cc: Jpeg.Ctrl,
  +ee: Jpeg.Ctrl,
  +fr: Jpeg.Frame,
  +sc: Jpeg.Scan,
  +ri: U32,
  +kk: Nat
) -> Type:
  {tr(Nat.add(List.length(&2, Jpeg.Ctrl, ll), kk), cc, fr, sc, ri) == List.append(&2, Jpeg.Ctrl, ll, tr(kk, ee, fr, sc,
    ri)) : List<&2, Jpeg.Ctrl>}

# two runs, one after the other
def run.cat(
  +l1: List<&2, Jpeg.Ctrl>,
  +l2: List<&2, Jpeg.Ctrl>,
  +c0: Jpeg.Ctrl,
  +c1: Jpeg.Ctrl,
  +c2: Jpeg.Ctrl,
  +fr: Jpeg.Frame,
  +sc: Jpeg.Scan,
  +ri: U32,
  +kk: Nat,
  h1: Run(l1, c0, c1, fr, sc, ri, Nat.add(List.length(&2, Jpeg.Ctrl, l2), kk)),
  h2: Run(l2, c1, c2, fr, sc, ri, kk)
) -> Run(List.append(&2, Jpeg.Ctrl, l1, l2), c0, c2, fr, sc, ri, kk):
  +n1 = List.length(&2, Jpeg.Ctrl, l1)
  +n2 = List.length(&2, Jpeg.Ctrl, l2)
  +t2 = {tr(kk, c2, fr, sc, ri) : List<&2, Jpeg.Ctrl>}
  Equal.trans(List<&2, Jpeg.Ctrl>, tr(Nat.add(List.length(&2, Jpeg.Ctrl, List.append(&2, Jpeg.Ctrl, l1, l2)), kk), c0,
    fr, sc, ri), tr(Nat.add(n1, Nat.add(n2, kk)), c0, fr, sc, ri), List.append(&2, Jpeg.Ctrl, List.append(&2,
    Jpeg.Ctrl, l1, l2), t2), Equal.cong(Nat, List<&2, Jpeg.Ctrl>, zz => tr(zz, c0, fr, sc, ri),
    Nat.add(List.length(&2, Jpeg.Ctrl, List.append(&2, Jpeg.Ctrl, l1, l2)), kk), Nat.add(n1, Nat.add(n2, kk)),
    Equal.trans(Nat, Nat.add(List.length(&2, Jpeg.Ctrl, List.append(&2, Jpeg.Ctrl, l1, l2)), kk),
    Nat.add(Nat.add(n1, n2), kk), Nat.add(n1, Nat.add(n2, kk)), Equal.cong(Nat, Nat, zz => Nat.add(zz, kk),
    List.length(&2, Jpeg.Ctrl, List.append(&2, Jpeg.Ctrl, l1, l2)), Nat.add(n1, n2), len.app(l1, l2)),
    R.add_assoc(n1, n2, kk))), Equal.trans(List<&2, Jpeg.Ctrl>, tr(Nat.add(n1, Nat.add(n2, kk)), c0, fr, sc, ri),
    List.append(&2, Jpeg.Ctrl, l1, tr(Nat.add(n2, kk), c1, fr, sc, ri)), List.append(&2, Jpeg.Ctrl, List.append(&2,
    Jpeg.Ctrl, l1, l2), t2), h1, Equal.trans(List<&2, Jpeg.Ctrl>, List.append(&2, Jpeg.Ctrl, l1, tr(Nat.add(n2, kk), c1,
    fr, sc, ri)), List.append(&2, Jpeg.Ctrl, l1, List.append(&2, Jpeg.Ctrl, l2, t2)), List.append(&2, Jpeg.Ctrl,
    List.append(&2, Jpeg.Ctrl, l1, l2), t2), Equal.cong(List<&2, Jpeg.Ctrl>, List<&2, Jpeg.Ctrl>,
    zz => List.append(&2, Jpeg.Ctrl, l1, zz), tr(Nat.add(n2, kk), c1, fr, sc, ri), List.append(&2, Jpeg.Ctrl, l2, t2),
    h2), Equal.sym(List<&2, Jpeg.Ctrl>, List.append(&2, Jpeg.Ctrl, List.append(&2, Jpeg.Ctrl, l1, l2), t2),
    List.append(&2, Jpeg.Ctrl, l1, List.append(&2, Jpeg.Ctrl, l2, t2)), app.assoc(l1, l2, t2)))))

# a run followed by no positions
def run.nil(
  +ll: List<&2, Jpeg.Ctrl>,
  +cc: Jpeg.Ctrl,
  +ee: Jpeg.Ctrl,
  +fr: Jpeg.Frame,
  +sc: Jpeg.Scan,
  +ri: U32,
  +kk: Nat,
  hh: Run(ll, cc, ee, fr, sc, ri, kk)
) -> Run(List.append(&2, Jpeg.Ctrl, ll, []), cc, ee, fr, sc, ri, kk):
  es = Equal.sym(List<&2, Jpeg.Ctrl>, List.append(&2, Jpeg.Ctrl, ll, []), ll, app.nil(ll))
  %es : Run(_, cc, ee, fr, sc, ri, kk)
  hh

# a run whose end is known by another name
def run.end(
  -ll: List<&2, Jpeg.Ctrl>,
  +cc: Jpeg.Ctrl,
  +e1: Jpeg.Ctrl,
  +e2: Jpeg.Ctrl,
  +fr: Jpeg.Frame,
  +sc: Jpeg.Scan,
  +ri: U32,
  +kk: Nat,
  hh: Run(ll, cc, e1, fr, sc, ri, kk),
  ee: {e1 == e2 : Jpeg.Ctrl}
) -> Run(ll, cc, e2, fr, sc, ri, kk):
  %ee : Run(ll, cc, _, fr, sc, ri, kk)
  hh

# the data units bi onward of a scan component, the last of them ll units on: the walk visits each, then
# goes where the decoder goes from the last
def run.units(
  +ll: Nat,
  +comp: U32,
  +bi: U32,
  +mx: U32,
  +my: U32,
  +mcu: U32,
  +ww: U32,
  +hh: U32,
  +nf: U32,
  +ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>,
  +tq: List<&2, U32>,
  +hmax: U32,
  +vmax: U32,
  +ns: U32,
  +sids: List<&2, U32>,
  +td: List<&2, U32>,
  +ta: List<&2, U32>,
  +ss: U32,
  +se: U32,
  +ah: U32,
  +ri: U32,
  +kk: Nat,
  +hb: {Nat.add(U32.to_nat(bi), 1n+ll) == U32.to_nat(Laws.jpg.units(comp, sids, ids, hs, vs)) : Nat}
) -> Run(Laws.jpg.o.units(1n+ll, comp, bi, mx, my, mcu), Jpeg.Ctrl{comp, bi, mx, my, mcu, 0},
  nxt(Jpeg.Ctrl{comp, Laws.jpg.idx(ll, bi), mx, my, mcu, 0}, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax},
    Jpeg.Scan{ns, sids, td, ta, ss, se,
      ah}, ri), Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, Jpeg.Scan{ns, sids, td, ta, ss, se, ah}, ri, kk):
  match ll:
    case 0n:
      {==}
    case 1n+(+pp):
      +fr = {Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax} : Jpeg.Frame}
      +sc = {Jpeg.Scan{ns, sids, td, ta, ss, se, ah} : Jpeg.Scan}
      +cc = {Jpeg.Ctrl{comp, bi, mx, my, mcu, 0} : Jpeg.Ctrl}
      +c1 = {Jpeg.Ctrl{comp, (bi + 1 : U32), mx, my, mcu, 0} : Jpeg.Ctrl}
      +nn = {Nat.add(List.length(&2, Jpeg.Ctrl, Laws.jpg.o.units(1n+pp, comp, (bi + 1 : U32), mx, my, mcu)), kk) : Nat}
      +en = {Equal.trans(Jpeg.Ctrl, nxt(cc, fr, sc, ri), bi.res(U32.is_lt((bi + 1 : U32), Laws.jpg.units(comp, sids,
        ids, hs, vs)),
        U32.is_lt((comp + 1 : U32), ns), U32.is_lt((mx + 1 : U32), Jpeg.decode.ceil(ww,
          (hmax * 8 : U32))), comp, bi, mx, my, mcu), c1,
        nxt.eq(comp, bi, mx, my, mcu, 0, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, ns, sids, td, ta, ss, se, ah,
          ri), Equal.cong(Bool, Jpeg.Ctrl, mb => bi.res(mb,
        U32.is_lt((comp + 1 : U32), ns), U32.is_lt((mx + 1 : U32), Jpeg.decode.ceil(ww,
          (hmax * 8 : U32))), comp, bi, mx, my, mcu),
        U32.is_lt((bi + 1 : U32), Laws.jpg.units(comp, sids, ids, hs, vs)), True{}, lt.more(bi, Laws.jpg.units(comp,
          sids, ids, hs, vs), pp, hb))) : {nxt(cc, fr, sc, ri) == c1 : Jpeg.Ctrl}}
      Equal.trans(List<&2, Jpeg.Ctrl>, cc <> tr(nn, nxt(cc, fr, sc, ri), fr, sc, ri), cc <> tr(nn, c1, fr, sc, ri),
        cc <> List.append(&2, Jpeg.Ctrl, Laws.jpg.o.units(1n+pp, comp, (bi + 1 : U32), mx, my, mcu), tr(kk,
        nxt(Jpeg.Ctrl{comp, Laws.jpg.idx(pp, (bi + 1 : U32)), mx, my, mcu, 0}, fr, sc, ri), fr, sc, ri)),
        Equal.cong(Jpeg.Ctrl, List<&2, Jpeg.Ctrl>, dd => {cc <> tr(nn, dd, fr, sc, ri) : List<&2, Jpeg.Ctrl>},
          nxt(cc, fr, sc, ri), c1, en),
        Equal.cong(List<&2, Jpeg.Ctrl>, List<&2, Jpeg.Ctrl>, zz => {cc <> zz : List<&2, Jpeg.Ctrl>}, tr(nn, c1, fr,
          sc, ri), List.append(&2, Jpeg.Ctrl,
        Laws.jpg.o.units(1n+pp, comp, (bi + 1 : U32), mx, my, mcu), tr(kk, nxt(Jpeg.Ctrl{comp, Laws.jpg.idx(pp,
        (bi + 1 : U32)), mx, my, mcu, 0}, fr, sc, ri), fr, sc, ri)), run.units(pp, comp, (bi + 1 : U32), mx, my, mcu,
        ww, hh, nf, ids, hs, vs, tq, hmax, vmax, ns, sids, td, ta, ss, se, ah, ri, kk, lt.next(bi,
          Laws.jpg.units(comp, sids, ids, hs, vs), pp, hb))))

# where the walk goes after a component's last unit, when the scan has more components
def comp.end.more(
  +kk: Nat,
  +comp: U32,
  +mx: U32,
  +my: U32,
  +mcu: U32,
  +ww: U32,
  +hh: U32,
  +nf: U32,
  +ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>,
  +tq: List<&2, U32>,
  +hmax: U32,
  +vmax: U32,
  +ns: U32,
  +sids: List<&2, U32>,
  +td: List<&2, U32>,
  +ta: List<&2, U32>,
  +ss: U32,
  +se: U32,
  +ah: U32,
  +ri: U32,
  +hs1: {1n+kk == U32.to_nat(Laws.jpg.units(comp, sids, ids, hs, vs)) : Nat},
  +hnext: {U32.is_lt((comp + 1 : U32), ns) == True{} : Bool}
) -> {nxt(Jpeg.Ctrl{comp, Laws.jpg.idx(kk, 0), mx, my, mcu, 0}, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax},
  Jpeg.Scan{ns, sids, td, ta, ss, se, ah}, ri) ==
  Jpeg.Ctrl{(comp + 1 : U32), 0, mx, my, mcu, 0} : Jpeg.Ctrl}:
  +bl = Laws.jpg.idx(kk, 0)
  Equal.trans(Jpeg.Ctrl, nxt(Jpeg.Ctrl{comp, bl, mx, my, mcu, 0}, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax,
    vmax}, Jpeg.Scan{ns, sids, td, ta, ss, se, ah}, ri),
    bi.res(U32.is_lt((bl + 1 : U32), Laws.jpg.units(comp, sids, ids, hs, vs)), U32.is_lt((comp + 1 : U32), ns),
      U32.is_lt((mx + 1 : U32), Jpeg.decode.ceil(ww, (hmax * 8 : U32))), comp,
    bl, mx, my, mcu), Jpeg.Ctrl{(comp + 1 : U32), 0, mx, my, mcu, 0}, nxt.eq(comp, bl, mx, my, mcu, 0, ww, hh, nf,
      ids, hs, vs, tq, hmax, vmax, ns, sids, td, ta, ss, se, ah, ri),
    Equal.trans(Jpeg.Ctrl, bi.res(U32.is_lt((bl + 1 : U32), Laws.jpg.units(comp, sids, ids, hs, vs)),
      U32.is_lt((comp + 1 : U32), ns),
    U32.is_lt((mx + 1 : U32), Jpeg.decode.ceil(ww,
      (hmax * 8 : U32))), comp, bl, mx, my, mcu), bi.res(False{}, U32.is_lt((comp + 1 : U32), ns),
    U32.is_lt((mx + 1 : U32), Jpeg.decode.ceil(ww,
      (hmax * 8 : U32))), comp, bl, mx, my, mcu), Jpeg.Ctrl{(comp + 1 : U32), 0, mx, my, mcu, 0},
    Equal.cong(Bool, Jpeg.Ctrl, mb => bi.res(mb, U32.is_lt((comp + 1 : U32), ns), U32.is_lt((mx + 1 : U32),
      Jpeg.decode.ceil(ww, (hmax * 8 : U32))),
    comp, bl, mx, my, mcu), U32.is_lt((bl + 1 : U32), Laws.jpg.units(comp, sids, ids, hs,
      vs)), False{}, lt.last(bl, Laws.jpg.units(comp, sids, ids, hs, vs), last.nat(kk, Laws.jpg.units(comp, sids,
        ids, hs, vs), hs1))),
    Equal.cong(Bool, Jpeg.Ctrl, nb => bi.res(False{}, nb, U32.is_lt((mx + 1 : U32), Jpeg.decode.ceil(ww,
      (hmax * 8 : U32))), comp, bl, mx, my, mcu),
    U32.is_lt((comp + 1 : U32), ns), True{}, hnext)))

# where the walk goes after the last component's last unit: the next MCU
def comp.end.last(
  +kk: Nat,
  +comp: U32,
  +mx: U32,
  +my: U32,
  +mcu: U32,
  +ww: U32,
  +hh: U32,
  +nf: U32,
  +ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>,
  +tq: List<&2, U32>,
  +hmax: U32,
  +vmax: U32,
  +ns: U32,
  +sids: List<&2, U32>,
  +td: List<&2, U32>,
  +ta: List<&2, U32>,
  +ss: U32,
  +se: U32,
  +ah: U32,
  +ri: U32,
  +hs1: {1n+kk == U32.to_nat(Laws.jpg.units(comp, sids, ids, hs, vs)) : Nat},
  +hnext: {U32.is_lt((comp + 1 : U32), ns) == False{} : Bool}
) -> {nxt(Jpeg.Ctrl{comp, Laws.jpg.idx(kk, 0), mx, my, mcu, 0}, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax},
  Jpeg.Scan{ns, sids, td, ta, ss, se, ah}, ri) ==
  mx.res(U32.is_lt((mx + 1 : U32), Jpeg.decode.ceil(ww, (hmax * 8 : U32))), (mcu + 1 : U32), (mx + 1 : U32),
    my) : Jpeg.Ctrl}:
  +bl = Laws.jpg.idx(kk, 0)
  Equal.trans(Jpeg.Ctrl, nxt(Jpeg.Ctrl{comp, bl, mx, my, mcu, 0}, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax,
    vmax}, Jpeg.Scan{ns, sids, td, ta, ss, se, ah}, ri),
    bi.res(U32.is_lt((bl + 1 : U32), Laws.jpg.units(comp, sids, ids, hs, vs)), U32.is_lt((comp + 1 : U32), ns),
      U32.is_lt((mx + 1 : U32), Jpeg.decode.ceil(ww, (hmax * 8 : U32))), comp,
    bl, mx, my, mcu), mx.res(U32.is_lt((mx + 1 : U32), Jpeg.decode.ceil(ww,
      (hmax * 8 : U32))), (mcu + 1 : U32), (mx + 1 : U32), my),
    nxt.eq(comp, bl, mx, my, mcu, 0, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, ns, sids, td, ta, ss, se, ah,
      ri), Equal.trans(Jpeg.Ctrl, bi.res(U32.is_lt((bl + 1 : U32), Laws.jpg.units(comp, sids, ids, hs, vs)),
    U32.is_lt((comp + 1 : U32), ns), U32.is_lt((mx + 1 : U32), Jpeg.decode.ceil(ww,
      (hmax * 8 : U32))), comp, bl, mx, my, mcu), bi.res(False{},
    U32.is_lt((comp + 1 : U32), ns), U32.is_lt((mx + 1 : U32), Jpeg.decode.ceil(ww,
      (hmax * 8 : U32))), comp, bl, mx, my, mcu),
    mx.res(U32.is_lt((mx + 1 : U32), Jpeg.decode.ceil(ww, (hmax * 8 : U32))), (mcu + 1 : U32), (mx + 1 : U32),
      my), Equal.cong(Bool, Jpeg.Ctrl,
    mb => bi.res(mb, U32.is_lt((comp + 1 : U32), ns), U32.is_lt((mx + 1 : U32), Jpeg.decode.ceil(ww,
      (hmax * 8 : U32))), comp, bl, mx, my, mcu),
    U32.is_lt((bl + 1 : U32), Laws.jpg.units(comp, sids, ids, hs, vs)), False{}, lt.last(bl, Laws.jpg.units(comp,
      sids, ids, hs, vs), last.nat(kk, Laws.jpg.units(comp, sids, ids, hs, vs), hs1))), Equal.cong(Bool,
    Jpeg.Ctrl, nb => bi.res(False{}, nb, U32.is_lt((mx + 1 : U32), Jpeg.decode.ceil(ww, (hmax * 8 : U32))), comp, bl,
      mx, my, mcu),
    U32.is_lt((comp + 1 : U32), ns), False{}, hnext)))

# where the walk goes after the last of a component's units in an MCU
def units.End(
  +comp: U32,
  +mx: U32,
  +my: U32,
  +mcu: U32,
  +ww: U32,
  +hh: U32,
  +nf: U32,
  +ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>,
  +tq: List<&2, U32>,
  +hmax: U32,
  +vmax: U32,
  +ns: U32,
  +sids: List<&2, U32>,
  +td: List<&2, U32>,
  +ta: List<&2, U32>,
  +ss: U32,
  +se: U32,
  +ah: U32,
  +ri: U32,
  +ee: Jpeg.Ctrl
) -> Type:
  {nxt(Jpeg.Ctrl{comp, Laws.jpg.idx(npred(U32.to_nat(Laws.jpg.units(comp, sids, ids, hs, vs))), 0), mx, my, mcu, 0},
    Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, Jpeg.Scan{ns, sids, td, ta, ss, se, ah}, ri) == ee :
    Jpeg.Ctrl}

# a scan component's units, counted as the decoder counts them: all of them, from unit 0
def run.comp.units(
  +comp: U32,
  +mx: U32,
  +my: U32,
  +mcu: U32,
  +ww: U32,
  +hh: U32,
  +nf: U32,
  +ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>,
  +tq: List<&2, U32>,
  +hmax: U32,
  +vmax: U32,
  +ns: U32,
  +sids: List<&2, U32>,
  +td: List<&2, U32>,
  +ta: List<&2, U32>,
  +ss: U32,
  +se: U32,
  +ah: U32,
  +ri: U32,
  +kk: Nat,
  +ee: Jpeg.Ctrl,
  +hpos: {U32.is_lt(0, Laws.jpg.units(comp, sids, ids, hs, vs)) == True{} : Bool},
  hend: units.End(comp, mx, my, mcu, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, ns, sids, td, ta, ss, se, ah, ri, ee)
) -> Run(Laws.jpg.o.units(U32.to_nat(Laws.jpg.units(comp, sids, ids, hs, vs)), comp, 0, mx, my, mcu), Jpeg.Ctrl{comp,
  0, mx, my, mcu, 0}, ee, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, Jpeg.Scan{ns, sids, td, ta, ss, se,
    ah}, ri, kk):
  +k1 = npred(U32.to_nat(Laws.jpg.units(comp, sids, ids, hs, vs)))
  +es = {pos.nat(Laws.jpg.units(comp, sids, ids, hs, vs), hpos) : {1n+k1 == U32.to_nat(Laws.jpg.units(comp, sids,
    ids, hs, vs)) : Nat}}
  %es : Run(Laws.jpg.o.units(_, comp, 0, mx, my, mcu), Jpeg.Ctrl{comp, 0, mx, my, mcu, 0}, ee, Jpeg.Frame{ww, hh, nf,
    ids, hs, vs, tq, hmax, vmax}, Jpeg.Scan{ns, sids, td, ta, ss, se, ah}, ri,
    kk)
  run.end(Laws.jpg.o.units(1n+k1, comp, 0, mx, my, mcu), Jpeg.Ctrl{comp, 0, mx, my, mcu, 0},
    nxt(Jpeg.Ctrl{comp, Laws.jpg.idx(k1, 0), mx, my, mcu, 0}, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax},
      Jpeg.Scan{ns, sids, td, ta, ss, se,
        ah}, ri), ee, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, Jpeg.Scan{ns, sids, td, ta, ss, se, ah},
          ri, kk,
    run.units(k1, comp, 0, mx, my, mcu, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, ns, sids, td, ta, ss, se, ah, ri,
      kk, es), hend)

# the scan's components comp onward of one MCU, the last ll components on: the walk visits their units in
# order, then goes to the next MCU
def run.comps(
  +ll: Nat,
  +comp: U32,
  +mx: U32,
  +my: U32,
  +mcu: U32,
  +ww: U32,
  +hh: U32,
  +nf: U32,
  +ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>,
  +tq: List<&2, U32>,
  +hmax: U32,
  +vmax: U32,
  +ns: U32,
  +sids: List<&2, U32>,
  +td: List<&2, U32>,
  +ta: List<&2, U32>,
  +ss: U32,
  +se: U32,
  +ah: U32,
  +ri: U32,
  +kk: Nat,
  +ok: Bool,
  +hc: {Nat.add(U32.to_nat(comp), 1n+ll) == U32.to_nat(ns) : Nat},
  +hu: {Laws.jpg.units.ok(1n+ll, comp, sids, ids, hs, vs, ok) == True{} : Bool}
) -> Run(Laws.jpg.o.comps(1n+ll, comp, mx, my, mcu, sids, ids, hs, vs), Jpeg.Ctrl{comp, 0, mx, my, mcu, 0},
  mx.res(U32.is_lt((mx + 1 : U32), Jpeg.decode.ceil(ww, (hmax * 8 : U32))), (mcu + 1 : U32), (mx + 1 : U32),
    my), Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, Jpeg.Scan{ns, sids, td, ta, ss, se, ah}, ri, kk):
  match ll:
    case 0n:
      +hpos = {U32L.and_right(ok, U32.is_lt(0, Laws.jpg.units(comp, sids, ids, hs, vs)), uok.acc(0n,
        (comp + 1 : U32), sids, ids, hs, vs, Bool.and(ok,
        U32.is_lt(0, Laws.jpg.units(comp, sids, ids, hs,
          vs))), hu)) : {U32.is_lt(0, Laws.jpg.units(comp, sids, ids, hs, vs)) == True{} : Bool}}
      +k1 = npred(U32.to_nat(Laws.jpg.units(comp, sids, ids, hs, vs)))
      +em = {mx.res(U32.is_lt((mx + 1 : U32), Jpeg.decode.ceil(ww, (hmax * 8 : U32))), (mcu + 1 : U32),
        (mx + 1 : U32), my) : Jpeg.Ctrl}
      run.nil(Laws.jpg.o.units(U32.to_nat(Laws.jpg.units(comp, sids, ids, hs, vs)), comp, 0, mx, my, mcu),
        Jpeg.Ctrl{comp, 0, mx, my, mcu, 0}, em,
        Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, Jpeg.Scan{ns, sids, td, ta, ss, se,
          ah}, ri, kk, run.comp.units(comp, mx, my, mcu, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, ns, sids, td, ta,
            ss, se, ah, ri, kk, em, hpos, comp.end.last(k1, comp, mx, my,
        mcu, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, ns, sids, td, ta, ss, se, ah, ri, pos.nat(Laws.jpg.units(comp,
          sids, ids, hs, vs), hpos), lt.last(comp, ns, hc))))
    case 1n+(+pp):
      +hpos = {U32L.and_right(ok, U32.is_lt(0, Laws.jpg.units(comp, sids, ids, hs, vs)), uok.acc(1n+pp,
        (comp + 1 : U32), sids, ids, hs, vs, Bool.and(ok,
        U32.is_lt(0, Laws.jpg.units(comp, sids, ids, hs,
          vs))), hu)) : {U32.is_lt(0, Laws.jpg.units(comp, sids, ids, hs, vs)) == True{} : Bool}}
      +k1 = npred(U32.to_nat(Laws.jpg.units(comp, sids, ids, hs, vs)))
      +em = {mx.res(U32.is_lt((mx + 1 : U32), Jpeg.decode.ceil(ww, (hmax * 8 : U32))), (mcu + 1 : U32),
        (mx + 1 : U32), my) : Jpeg.Ctrl}
      +c1 = {Jpeg.Ctrl{(comp + 1 : U32), 0, mx, my, mcu, 0} : Jpeg.Ctrl}
      +l2 = {Laws.jpg.o.comps(1n+pp, (comp + 1 : U32), mx, my, mcu, sids, ids, hs, vs) : List<&2, Jpeg.Ctrl>}
      run.cat(Laws.jpg.o.units(U32.to_nat(Laws.jpg.units(comp, sids, ids, hs, vs)), comp, 0, mx, my, mcu), l2,
        Jpeg.Ctrl{comp, 0, mx, my, mcu, 0}, c1,
        em, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, Jpeg.Scan{ns, sids, td, ta, ss, se,
          ah}, ri, kk, run.comp.units(comp, mx, my, mcu, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, ns, sids, td, ta,
            ss, se, ah, ri, Nat.add(List.length(&2, Jpeg.Ctrl, l2),
        kk), c1, hpos, comp.end.more(k1, comp, mx, my, mcu, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, ns, sids, td,
          ta, ss, se, ah, ri, pos.nat(Laws.jpg.units(comp, sids, ids, hs, vs), hpos), lt.more(comp, ns, pp, hc))),
        run.comps(pp, (comp + 1 : U32), mx, my, mcu, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, ns, sids, td, ta, ss,
          se, ah, ri, kk, Bool.and(ok, U32.is_lt(0, Laws.jpg.units(comp, sids, ids, hs, vs))), lt.next(comp, ns,
        pp, hc), hu))

# the MCUs mx onward of MCU row my, the last ll MCUs on: the walk visits each MCU's units in order, then
# goes to the first MCU of the next row
def run.row(
  +ll: Nat,
  +mx: U32,
  +my: U32,
  +mcu: U32,
  +ww: U32,
  +hh: U32,
  +nf: U32,
  +ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>,
  +tq: List<&2, U32>,
  +hmax: U32,
  +vmax: U32,
  +ns: U32,
  +sids: List<&2, U32>,
  +td: List<&2, U32>,
  +ta: List<&2, U32>,
  +ss: U32,
  +se: U32,
  +ah: U32,
  +ri: U32,
  +kk: Nat,
  +n1: Nat,
  +hn: {1n+n1 == U32.to_nat(ns) : Nat},
  +hu: {Laws.jpg.units.ok(1n+n1, 0, sids, ids, hs, vs, True{}) == True{} : Bool},
  +hx: {Nat.add(U32.to_nat(mx), 1n+ll) == U32.to_nat(Jpeg.decode.ceil(ww, (hmax * 8 : U32))) : Nat}
) -> Run(Laws.jpg.o.row(1n+ll, mx, my, mcu, ns, sids, ids, hs, vs), Jpeg.Ctrl{0, 0, mx, my, mcu, 0},
  Jpeg.Ctrl{0, 0, 0, (my + 1 : U32), Laws.jpg.idx(1n+ll, mcu), 0}, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax,
    vmax}, Jpeg.Scan{ns, sids, td, ta, ss, se, ah}, ri, kk):
  match ll:
    case 0n:
      +em = {mx.res(U32.is_lt((mx + 1 : U32), Jpeg.decode.ceil(ww, (hmax * 8 : U32))), (mcu + 1 : U32),
        (mx + 1 : U32), my) : Jpeg.Ctrl}
      +et = {Jpeg.Ctrl{0, 0, 0, (my + 1 : U32), (mcu + 1 : U32), 0} : Jpeg.Ctrl}
      %hn : Run(List.append(&2, Jpeg.Ctrl, Laws.jpg.o.comps(_, 0, mx, my, mcu, sids, ids, hs, vs), []),
        Jpeg.Ctrl{0, 0, mx, my, mcu, 0}, et, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, Jpeg.Scan{ns, sids,
          td, ta, ss, se, ah}, ri, kk)
      run.nil(Laws.jpg.o.comps(1n+n1, 0, mx, my, mcu, sids, ids, hs, vs), Jpeg.Ctrl{0, 0, mx, my, mcu, 0}, et,
        Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax},
        Jpeg.Scan{ns, sids, td, ta, ss, se, ah}, ri, kk, run.end(Laws.jpg.o.comps(1n+n1, 0, mx, my, mcu, sids, ids,
          hs, vs), Jpeg.Ctrl{0, 0, mx, my, mcu,
        0}, em, et, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, Jpeg.Scan{ns, sids, td, ta, ss, se, ah}, ri,
          kk, run.comps(n1, 0, mx, my, mcu, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, ns, sids, td, ta, ss, se, ah,
            ri, kk, True{}, hn, hu),
        Equal.cong(Bool, Jpeg.Ctrl, ib => mx.res(ib, (mcu + 1 : U32), (mx + 1 : U32), my),
        U32.is_lt((mx + 1 : U32), Jpeg.decode.ceil(ww, (hmax * 8 : U32))), False{}, lt.last(mx, Jpeg.decode.ceil(ww,
          (hmax * 8 : U32)), hx))))
    case 1n+(+pp):
      +em = {mx.res(U32.is_lt((mx + 1 : U32), Jpeg.decode.ceil(ww, (hmax * 8 : U32))), (mcu + 1 : U32),
        (mx + 1 : U32), my) : Jpeg.Ctrl}
      +c1 = {Jpeg.Ctrl{0, 0, (mx + 1 : U32), my, (mcu + 1 : U32), 0} : Jpeg.Ctrl}
      +et = {Jpeg.Ctrl{0, 0, 0, (my + 1 : U32), Laws.jpg.idx(1n+(1n+pp), mcu), 0} : Jpeg.Ctrl}
      +l2 = {Laws.jpg.o.row(1n+pp, (mx + 1 : U32), my, (mcu + 1 : U32), ns, sids, ids, hs, vs) : List<&2, Jpeg.Ctrl>}
      %hn : Run(List.append(&2, Jpeg.Ctrl, Laws.jpg.o.comps(_, 0, mx, my, mcu, sids, ids, hs, vs), l2),
        Jpeg.Ctrl{0, 0, mx, my, mcu, 0}, et, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, Jpeg.Scan{ns, sids,
          td, ta, ss, se, ah}, ri, kk)
      run.cat(Laws.jpg.o.comps(1n+n1, 0, mx, my, mcu, sids, ids, hs, vs), l2, Jpeg.Ctrl{0, 0, mx, my, mcu, 0}, c1, et,
        Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, Jpeg.Scan{ns, sids, td, ta, ss, se,
          ah}, ri, kk, run.end(Laws.jpg.o.comps(1n+n1, 0, mx, my, mcu, sids, ids, hs, vs), Jpeg.Ctrl{0, 0, mx,
        my, mcu, 0}, em, c1, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, Jpeg.Scan{ns, sids, td, ta, ss, se,
          ah}, ri, Nat.add(List.length(&2, Jpeg.Ctrl, l2), kk), run.comps(n1, 0, mx, my,
        mcu, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, ns, sids, td, ta, ss, se, ah, ri, Nat.add(List.length(&2,
          Jpeg.Ctrl, l2), kk), True{}, hn, hu), Equal.cong(Bool, Jpeg.Ctrl,
        ib => mx.res(ib, (mcu + 1 : U32), (mx + 1 : U32), my), U32.is_lt((mx + 1 : U32), Jpeg.decode.ceil(ww,
          (hmax * 8 : U32))), True{}, lt.more(mx,
        Jpeg.decode.ceil(ww,
          (hmax * 8 : U32)), pp, hx))), run.row(pp, (mx + 1 : U32), my, (mcu + 1 : U32), ww, hh, nf, ids, hs, vs, tq,
            hmax, vmax, ns, sids, td, ta, ss, se, ah, ri, kk, n1, hn, hu, lt.next(mx,
        Jpeg.decode.ceil(ww, (hmax * 8 : U32)), pp, hx)))

# where the walk is after mm MCU rows from row my, MCU number mcu, mw MCUs to a row
def rows.end(mm: Nat, +my: U32, +mcu: U32, +mw: U32) -> Jpeg.Ctrl:
  match mm:
    case 0n:
      Jpeg.Ctrl{0, 0, 0, my, mcu, 0}
    case 1n+pp:
      rows.end(pp, (my + 1 : U32), Laws.jpg.idx(U32.to_nat(mw), mcu), mw)

# MCU rows my onward, mm of them: the walk visits each row's MCUs in order
def run.rows(
  +mm: Nat,
  +my: U32,
  +mcu: U32,
  +ww: U32,
  +hh: U32,
  +nf: U32,
  +ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>,
  +tq: List<&2, U32>,
  +hmax: U32,
  +vmax: U32,
  +ns: U32,
  +sids: List<&2, U32>,
  +td: List<&2, U32>,
  +ta: List<&2, U32>,
  +ss: U32,
  +se: U32,
  +ah: U32,
  +ri: U32,
  +kk: Nat,
  +n1: Nat,
  +hn: {1n+n1 == U32.to_nat(ns) : Nat},
  +hu: {Laws.jpg.units.ok(1n+n1, 0, sids, ids, hs, vs, True{}) == True{} : Bool},
  +w1: Nat,
  +hw: {1n+w1 == U32.to_nat(Jpeg.decode.ceil(ww, (hmax * 8 : U32))) : Nat}
) -> Run(Laws.jpg.o.rows(mm, my, mcu, Jpeg.decode.ceil(ww, (hmax * 8 : U32)), ns, sids, ids, hs, vs), Jpeg.Ctrl{0, 0,
  0, my, mcu, 0},
  rows.end(mm, my, mcu, Jpeg.decode.ceil(ww, (hmax * 8 : U32))), Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax,
    vmax}, Jpeg.Scan{ns, sids, td, ta, ss, se, ah}, ri, kk):
  match mm:
    case 0n:
      {==}
    case 1n+(+pp):
      +m2 = {Laws.jpg.idx(U32.to_nat(Jpeg.decode.ceil(ww, (hmax * 8 : U32))), mcu) : U32}
      +c1 = {Jpeg.Ctrl{0, 0, 0, (my + 1 : U32), m2, 0} : Jpeg.Ctrl}
      +l2 = {Laws.jpg.o.rows(pp, (my + 1 : U32), m2, Jpeg.decode.ceil(ww, (hmax * 8 : U32)), ns, sids, ids, hs,
        vs) : List<&2, Jpeg.Ctrl>}
      +et = {rows.end(pp, (my + 1 : U32), m2, Jpeg.decode.ceil(ww, (hmax * 8 : U32))) : Jpeg.Ctrl}
      %hw : Run(List.append(&2, Jpeg.Ctrl, Laws.jpg.o.row(_, 0, my, mcu, ns, sids, ids, hs, vs), l2),
        Jpeg.Ctrl{0, 0, 0, my, mcu, 0}, et, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, Jpeg.Scan{ns, sids,
          td, ta, ss, se, ah}, ri, kk)
      run.cat(Laws.jpg.o.row(1n+w1, 0, my, mcu, ns, sids, ids, hs, vs), l2, Jpeg.Ctrl{0, 0, 0, my, mcu, 0}, c1, et,
        Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, Jpeg.Scan{ns, sids, td, ta, ss, se,
          ah}, ri, kk, run.end(Laws.jpg.o.row(1n+w1, 0, my, mcu, ns, sids, ids, hs, vs), Jpeg.Ctrl{0, 0, 0, my,
        mcu, 0}, Jpeg.Ctrl{0, 0, 0, (my + 1 : U32), Laws.jpg.idx(1n+w1,
          mcu), 0}, c1, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, Jpeg.Scan{ns, sids, td, ta, ss, se, ah},
            ri,
        Nat.add(List.length(&2, Jpeg.Ctrl, l2), kk), run.row(w1, 0, my, mcu, ww, hh, nf, ids, hs, vs, tq, hmax, vmax,
          ns, sids, td, ta, ss, se, ah, ri, Nat.add(List.length(&2, Jpeg.Ctrl,
        l2), kk), n1, hn, hu, hw), Equal.cong(Nat, Jpeg.Ctrl, nn => {Jpeg.Ctrl{0, 0, 0, (my + 1 : U32),
        Laws.jpg.idx(nn,
          mcu), 0} : Jpeg.Ctrl}, 1n+w1, U32.to_nat(Jpeg.decode.ceil(ww, (hmax * 8 : U32))), hw)), run.rows(pp,
            (my + 1 : U32), m2,
        ww, hh, nf, ids, hs, vs, tq, hmax, vmax, ns, sids, td, ta, ss, se, ah, ri, kk, n1, hn, hu, w1, hw))

# jpeg_walk_frame: the decoder's trace from the scan's first block is the T.81 order
def walk.frame(
  +ww: U32,
  +hh: U32,
  +nf: U32,
  +ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>,
  +tq: List<&2, U32>,
  +hmax: U32,
  +vmax: U32,
  +ns: U32,
  +sids: List<&2, U32>,
  +td: List<&2, U32>,
  +ta: List<&2, U32>,
  +ss: U32,
  +se: U32,
  +ah: U32,
  +ri: U32,
  +rst: U32,
  +mh: U32,
  +h_ns: {U32.is_lt(0, ns) == True{} : Bool},
  +h_mw: {U32.is_lt(0, Jpeg.decode.ceil(ww, (hmax * 8 : U32))) == True{} : Bool},
  +h_units: {Laws.jpg.units.ok(U32.to_nat(ns), 0, sids, ids, hs, vs, True{}) == True{} : Bool}
) -> {Laws.jpg.trace(List.length(&2, Jpeg.Ctrl, Laws.jpg.o.rows(U32.to_nat(mh), 0, 0, Jpeg.decode.ceil(ww,
  (hmax * 8 : U32)), ns, sids, ids, hs, vs)),
  Jpeg.Ctrl{0, 0, 0, 0, 0, rst}, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, Jpeg.Scan{ns, sids, td, ta, ss,
    se, ah}, ri) == Laws.jpg.o.rows(U32.to_nat(mh), 0, 0, Jpeg.decode.ceil(ww, (hmax * 8 : U32)), ns, sids, ids,
  hs, vs) : List<&2, Jpeg.Ctrl>}:
  +fr = {Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax} : Jpeg.Frame}
  +sc = {Jpeg.Scan{ns, sids, td, ta, ss, se, ah} : Jpeg.Scan}
  +ll = {Laws.jpg.o.rows(U32.to_nat(mh), 0, 0, Jpeg.decode.ceil(ww, (hmax * 8 : U32)), ns, sids, ids, hs,
    vs) : List<&2, Jpeg.Ctrl>}
  +ln = List.length(&2, Jpeg.Ctrl, ll)
  +n1 = npred(U32.to_nat(ns))
  +hn = {pos.nat(ns, h_ns) : {1n+n1 == U32.to_nat(ns) : Nat}}
  +c0 = {Jpeg.Ctrl{0, 0, 0, 0, 0, 0} : Jpeg.Ctrl}
  +hu = {Equal.trans(Bool, Laws.jpg.units.ok(1n+n1, 0, sids, ids, hs, vs, True{}), Laws.jpg.units.ok(U32.to_nat(ns),
    0, sids, ids, hs, vs, True{}), True{}, Equal.cong(Nat, Bool, nn => Laws.jpg.units.ok(nn, 0, sids, ids, hs, vs,
    True{}), 1n+n1, U32.to_nat(ns), hn), h_units) : {Laws.jpg.units.ok(1n+n1, 0, sids, ids, hs, vs, True{}) == True{} :
    Bool}}
  Equal.trans(List<&2, Jpeg.Ctrl>, Laws.jpg.trace(ln, Jpeg.Ctrl{0, 0, 0, 0, 0, rst}, fr, sc, ri), tr(ln,
    Jpeg.Ctrl{0, 0, 0, 0, 0, rst}, fr, sc, ri), ll, trace.tr(ln, Jpeg.Ctrl{0, 0, 0, 0, 0,
      rst}, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, ns, sids, td, ta, ss, se, ah, ri),
    Equal.trans(List<&2, Jpeg.Ctrl>, tr(ln, Jpeg.Ctrl{0, 0, 0, 0, 0, rst}, fr, sc, ri), tr(ln, c0, fr, sc, ri), ll,
    tr.pos(ln, Jpeg.Ctrl{0, 0, 0, 0, 0, rst}, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, ns, sids, td, ta, ss, se, ah,
      ri), Equal.trans(List<&2, Jpeg.Ctrl>, tr(ln, c0, fr, sc, ri),
    tr(Nat.add(ln, 0n), c0, fr, sc, ri), ll, Equal.cong(Nat, List<&2, Jpeg.Ctrl>, nn => tr(nn, c0, fr, sc, ri), ln,
    Nat.add(ln, 0n), Equal.sym(Nat, Nat.add(ln, 0n), ln, R.add_zero(ln))), Equal.trans(List<&2, Jpeg.Ctrl>,
    tr(Nat.add(ln, 0n), c0, fr, sc, ri), List.append(&2, Jpeg.Ctrl, ll, []), ll, run.rows(U32.to_nat(mh), 0, 0, ww,
      hh, nf, ids, hs, vs, tq, hmax, vmax, ns, sids, td, ta, ss, se, ah, ri,
    0n, n1, hn, hu, npred(U32.to_nat(Jpeg.decode.ceil(ww, (hmax * 8 : U32)))), pos.nat(Jpeg.decode.ceil(ww,
      (hmax * 8 : U32)), h_mw)), app.nil(ll)))))

# ---- IMG-JPG-3: stuffing, the header walk, the entropy walk, the frame size ----

# a stuffed list stays refused once a 255 was not followed by a 0
def st.false(xs: List<&2, U32>, ff: Bool) -> {Laws.jpg.stuffed(xs, ff, False{}) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +bb <> rest:
      match ff:
        case True{}:
          st.false(rest, False{})
        case False{}:
          st.false(rest, U32.is_eq(bb, 255))

# one byte stuffed in front of stuffed bytes keeps them stuffed
def st.put(
  ff: Bool,
  +bb: U32,
  +acc: List<&2, U32>,
  +ee: {U32.is_eq(bb, 255) == ff : Bool},
  hh: {Laws.jpg.stuffed(acc, False{}, True{}) == True{} : Bool}
) -> {Laws.jpg.stuffed(Jenc.encode.stuff.put(ff, bb, acc), False{}, True{}) == True{} : Bool}:
  match ff:
    case True{}:
      es = Equal.sym(Bool, U32.is_eq(bb, 255), True{}, ee)
      %es : {Laws.jpg.stuffed(0 <> acc, _, True{}) == True{} : Bool}
      hh
    case False{}:
      es = Equal.sym(Bool, U32.is_eq(bb, 255), False{}, ee)
      %es : {Laws.jpg.stuffed(acc, _, True{}) == True{} : Bool}
      hh

# every byte of a written list stuffed onto stuffed bytes gives stuffed bytes
def st.all(
  out: List<&2, U32>,
  +acc: List<&2, U32>,
  hh: {Laws.jpg.stuffed(acc, False{}, True{}) == True{} : Bool}
) -> {Laws.jpg.stuffed(Jenc.encode.stuff.all(out, acc), False{}, True{}) == True{} : Bool}:
  match out:
    case Nil{}:
      hh
    case +bb <> rest:
      st.all(rest, Jenc.encode.stuff.put(U32.is_eq(bb, 255), bb, acc), st.put(U32.is_eq(bb, 255), bb, acc, {==}, hh))

# the entropy-coded bytes the encoder flushes are stuffed, whatever it wrote
def st.pad(pp: Jenc.Put) -> {Laws.jpg.stuffed(Jenc.encode.pad(pp), False{}, True{}) == True{} : Bool}:
  match pp:
    case Jenc.Put{out, +buf, +nn}:
      st.all(Jenc.encode.pad.n(U32.is_eq(nn, 0), out, buf, nn), [], {==})

# each of the encoder's three paths ends in a flush
def st.disp(
  neu: Bool,
  sol: Bool,
  +color: U32,
  px: List<&2, U32>,
  +ww: U32,
  +hh: U32
) -> {Laws.jpg.stuffed(Jenc.encode.dispatch.b(neu, sol, color, px, ww, hh), False{}, True{}) == True{} : Bool}:
  match neu:
    case True{}:
      st.pad(Jenc.encode.neutral.mcus(U32.to_nat((U32.div((ww + 7 : U32), 8) * U32.div((hh + 7 : U32), 8) : U32)),
        Jenc.encode.put0()))
    case False{}:
      match sol:
        case True{}:
          st.pad(Jenc.encode.neutral.mcus(U32.to_nat(((U32.div((ww + 7 : U32), 8) * U32.div((hh + 7 : U32), 8) : U32) -
            1 : U32)), Jenc.encode.solid.y(Array.set(U32, Jpeg.decode.plane(1), 0, color),
            Jenc.encode.book(Jenc.encode.dccounts(), Jenc.encode.dcsyms(), Jenc.encode.accounts(),
            Jenc.encode.acsyms()), Jenc.encode.put0(), Jenc.encode.ctx())))
        case False{}:
          st.pad(Jenc.encode.mcus(U32.to_nat((U32.div((ww + 7 : U32), 8) * U32.div((hh + 7 : U32), 8) : U32)),
            (Jenc.encode.pix.load(U32.to_nat((ww * hh : U32)), px, Jpeg.decode.plane((ww * hh : U32)), 0),
            Jenc.encode.book(Jenc.encode.dccounts(), Jenc.encode.dcsyms(), Jenc.encode.accounts(),
            Jenc.encode.acsyms()), 0, 0, 0, Jenc.encode.put0()), 0, 0, U32.div((ww + 7 : U32), 8), ww, hh,
            Jenc.encode.ctx()))

# the watch's answer, whatever it is, dispatches to stuffed bytes
def st.use(
  got: U32 & U32 & List<&2, U32>,
  +ww: U32,
  +hh: U32
) -> {Laws.jpg.stuffed(Jenc.encode.arm.use(got, ww, hh), False{}, True{}) == True{} : Bool}:
  match got:
    case (+tag, +color, px):
      st.disp(U32.is_eq(tag, 0), U32.is_eq(tag, 1), color, px, ww, hh)

# the phase the entropy walk is in: after a 255, or not
def ent.ph(ff: Bool) -> Jpeg.Phase:
  match ff:
    case True{}:
      Jpeg.EntFF{}
    case False{}:
      Jpeg.Ent{}

# the bytes the entropy walk holds: a 255 just read is not yet among them
def ent.acc(ff: Bool, +en: List<&2, U32>) -> List<&2, U32>:
  match ff:
    case True{}:
      255 <> en
    case False{}:
      en

# what the entropy walk holds after one byte: a 255 is held back until its pair is read
def ent.hold(ff: Bool, +bb: U32, +en: List<&2, U32>) -> List<&2, U32>:
  match ff:
    case True{}:
      +_b = (bb - bb : U32)
      en
    case False{}:
      bb <> en

# the entropy walk from after one byte, as ent.go gives it
def ent.Ih(
  ff: Bool,
  +bb: U32,
  +rest: List<&2, U32>,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +en: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> Type:
  {Jpeg.decode.walk(List.append(&2, U32, rest, [255, 217]), Jpeg.St{ent.ph(ff), frame, scan, tabs, ent.hold(ff, bb,
    en), ri, kind, bad}) == Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, List.reverse.go(&2, U32, rest, ent.acc(ff,
    ent.hold(ff, bb, en))), ri, kind, bad} : Jpeg.St}

# the entropy walk over one byte that is not after a 255: 255 opens a pair, any other is kept
def ent.one(
  ff: Bool,
  +bb: U32,
  +rest: List<&2, U32>,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +en: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32,
  +ee: {U32.is_eq(bb, 255) == ff : Bool},
  ih: ent.Ih(ff, bb, rest, frame, scan, tabs, en, ri, kind, bad)
) -> {Jpeg.decode.walk(List.append(&2, U32, bb <> rest, [255, 217]), Jpeg.St{Jpeg.Ent{}, frame, scan, tabs, en, ri,
  kind, bad}) == Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, List.reverse.go(&2, U32, bb <> rest, en), ri, kind, bad} :
  Jpeg.St}:
  match ff:
    case True{}:
      es = Equal.sym(Bool, U32.is_eq(bb, 255), True{}, ee)
      eb = Equal.sym(U32, bb, 255, U32L.ueq(bb, 255, ee))
      %es : {Jpeg.decode.walk(List.append(&2, U32, rest, [255, 217]), Jpeg.decode.step.ent(_, bb, frame, scan, tabs,
        en, ri, kind, bad)) == Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, List.reverse.go(&2, U32, rest, bb <> en), ri,
        kind, bad} : Jpeg.St}
      %eb : {Jpeg.decode.walk(List.append(&2, U32, rest, [255, 217]), Jpeg.decode.step.ent(True{}, bb, frame, scan,
        tabs, en, ri, kind, bad)) == Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, List.reverse.go(&2, U32, rest, _ <> en),
          ri,
        kind, bad} : Jpeg.St}
      ih
    case False{}:
      es = Equal.sym(Bool, U32.is_eq(bb, 255), False{}, ee)
      %es : {Jpeg.decode.walk(List.append(&2, U32, rest, [255, 217]), Jpeg.decode.step.ent(_, bb, frame, scan, tabs,
        en, ri, kind, bad)) == Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, List.reverse.go(&2, U32, rest, bb <> en), ri,
        kind, bad} : Jpeg.St}
      ih

# after a 255 the next byte of stuffed bytes is 0
def ent.zero(
  zb: Bool,
  rest: List<&2, U32>,
  +hh: {Laws.jpg.stuffed(rest, False{}, zb) == True{} : Bool}
) -> {zb == True{} : Bool}:
  match zb:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, U32L.false_true(Equal.trans(Bool, False{}, Laws.jpg.stuffed(rest,
        False{}, False{}), True{}, Equal.sym(Bool, Laws.jpg.stuffed(rest, False{}, False{}), False{}, st.false(rest,
        False{})), hh)))

# the entropy walk over stuffed bytes, then EOI: every byte kept, in reverse, onto what it held, and a 255
# it had just read put back in front of them
def ent.go(
  +xs: List<&2, U32>,
  ff: Bool,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +en: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32,
  +hh: {Laws.jpg.stuffed(xs, ff, True{}) == True{} : Bool}
) -> {Jpeg.decode.walk(List.append(&2, U32, xs, [255, 217]), Jpeg.St{ent.ph(ff), frame, scan, tabs, en, ri, kind,
  bad}) == Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, List.reverse.go(&2, U32, xs, ent.acc(ff, en)), ri, kind, bad} :
  Jpeg.St}:
  match xs:
    case Nil{}:
      match ff:
        case False{}:
          {==}
        case True{}:
          Empty.absurd({Jpeg.decode.walk([255, 217], Jpeg.St{Jpeg.EntFF{}, frame, scan, tabs, en, ri, kind, bad}) ==
            Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, 255 <> en, ri, kind, bad} : Jpeg.St}, U32L.false_true(hh))
    case +bb <> +rest:
      match ff:
        case False{}:
          ent.one(U32.is_eq(bb, 255), bb, rest, frame, scan, tabs, en, ri, kind, bad, {==}, ent.go(rest,
            U32.is_eq(bb, 255), frame, scan, tabs, ent.hold(U32.is_eq(bb, 255), bb, en), ri, kind, bad, hh))
        case True{}:
          +ez = {ent.zero(U32.is_eq(bb, 0), rest, hh) : {U32.is_eq(bb, 0) == True{} : Bool}}
          eb = Equal.sym(U32, bb, 0, U32L.ueq(bb, 0, ez))
          %eb : {Jpeg.decode.walk(List.append(&2, U32, _ <> rest, [255, 217]), Jpeg.St{Jpeg.EntFF{}, frame, scan, tabs,
            en, ri, kind, bad}) == Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, List.reverse.go(&2, U32, _ <> rest,
            255 <> en), ri, kind, bad} : Jpeg.St}
          h2 = Equal.trans(Bool, Laws.jpg.stuffed(rest, False{}, True{}), Laws.jpg.stuffed(rest, False{},
            U32.is_eq(bb, 0)), True{}, Equal.cong(Bool, Bool, zb => Laws.jpg.stuffed(rest, False{}, zb), True{},
            U32.is_eq(bb, 0), Equal.sym(Bool, U32.is_eq(bb, 0), True{}, ez)), hh)
          ent.go(rest, False{}, frame, scan, tabs, 0 <> (255 <> en), ri, kind, bad, h2)

# the decoder's u16 of the high and low bytes the encoder writes for a size is the size
def u16.eq(+ww: U32) -> {Jpeg.decode.u16(U32.shrn(ww, 8n), U32.and(ww, 255)) == ww : U32}:
  Equal.trans(U32, Jpeg.decode.u16(U32.shrn(ww, 8n), U32.and(ww, 255)), Jpeg.decode.u16(U32.shrn(ww, 8n),
    U32.and(255, ww)), ww, Equal.cong(U32, U32, xx => Jpeg.decode.u16(U32.shrn(ww, 8n), xx), U32.and(ww, 255),
    U32.and(255, ww), uand_comm(ww, 255)), u16_bits(ww))

# a raster of width ww and height hh has that size
def sized.pic(
  +ww: U32,
  +hh: U32,
  px: List<&2, U32>
) -> {Laws.jpg.sized(Some{Img.Raster{ww, hh, px}}, ww, hh) == True{} : Bool}:
  Equal.trans(Bool, Bool.and(U32.is_eq(ww, ww), U32.is_eq(hh, hh)), Bool.and(True{}, U32.is_eq(hh, hh)), True{},
    Equal.cong(Bool, Bool, bb => Bool.and(bb, U32.is_eq(hh, hh)), U32.is_eq(ww, ww), True{}, U32L.u32_eq_refl(ww)),
    U32L.u32_eq_refl(hh))

# three components: a colour picture of the frame's size, or none
def nf3.sized(
  three: Bool,
  +ww: U32,
  +hh: U32,
  yy: Array<U32>,
  cb: Array<U32>,
  cr: Array<U32>
) -> {Laws.jpg.sized(Img.decode_jpeg.out(Jpeg.decode.done.nf3(three, ww, hh, yy, cb, cr)), ww, hh) == True{} : Bool}:
  match three:
    case True{}:
      +nn = U32.to_nat((ww * hh : U32))
      sized.pic(ww, hh, Jpeg.decode.rgbs(Jpeg.decode.points(nn, yy), Jpeg.decode.points(nn, cb),
        Jpeg.decode.points(nn, cr)))
    case False{}:
      -_y = yy
      -_b = cb
      -_r = cr
      {==}

# one component: a gray picture of the frame's size; any other count as above
def nf1.sized(
  one: Bool,
  +nf: U32,
  +ww: U32,
  +hh: U32,
  yy: Array<U32>,
  cb: Array<U32>,
  cr: Array<U32>
) -> {Laws.jpg.sized(Img.decode_jpeg.out(Jpeg.decode.done.nf1(one, nf, ww, hh, yy, cb, cr)), ww, hh) == True{} :
  Bool}:
  match one:
    case True{}:
      -_b = cb
      -_r = cr
      sized.pic(ww, hh, Jpeg.decode.grays(Jpeg.decode.points(U32.to_nat((ww * hh : U32)), yy)))
    case False{}:
      nf3.sized(U32.is_eq(nf, 3), ww, hh, yy, cb, cr)

# the planes of a finished scan as a picture of the frame's size, or none
def dok.sized(
  bad: Bool,
  +ww: U32,
  +hh: U32,
  +nf: U32,
  +ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>,
  +tq: List<&2, U32>,
  +hmax: U32,
  +vmax: U32,
  yy: Array<U32>,
  cb: Array<U32>,
  cr: Array<U32>
) -> {Laws.jpg.sized(Img.decode_jpeg.out(Jpeg.decode.done.ok(bad, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax},
  yy, cb, cr)), ww, hh) == True{} : Bool}:
  match bad:
    case True{}:
      -_y = yy
      -_b = cb
      -_r = cr
      {==}
    case False{}:
      nf1.sized(U32.is_eq(nf, 1), nf, ww, hh, yy, cb, cr)

# the block loop ends in a picture of the frame's size, or none
def blocks.sized(
  left: Nat,
  blk: Jpeg.Blk,
  +ctrl: Jpeg.Ctrl,
  +preds: Jpeg.Preds,
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
  +tabs: Jpeg.Tabs,
  +ri: U32,
  yy: Array<U32>,
  cb: Array<U32>,
  cr: Array<U32>,
  +ok: U32
) -> {Laws.jpg.sized(Img.decode_jpeg.out(Jpeg.decode.blocks(left, blk, ctrl, preds, Jpeg.Frame{ww, hh, nf, ids, hs, vs,
  tq, hmax, vmax}, scan, tabs, ri, yy, cb, cr, ok)), ww, hh) == True{} : Bool}:
  match left:
    case 0n:
      match blk:
        case Jpeg.Blk{+samples, _bits, _pred, +bok}:
          +fr = {Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax} : Jpeg.Frame}
          dok.sized(U32.is_eq((ok * bok : U32), 0), ww, hh, nf, ids, hs, vs, tq, hmax, vmax,
            Jpeg.decode.paint.use(Jpeg.decode.geom(ctrl, fr, scan), U32.is_eq(Jpeg.decode.ctrl.comp(ctrl), 0), samples,
            yy), Jpeg.decode.paint.use(Jpeg.decode.geom(ctrl, fr, scan), U32.is_eq(Jpeg.decode.ctrl.comp(ctrl), 1),
            samples, cb), Jpeg.decode.paint.use(Jpeg.decode.geom(ctrl, fr, scan), U32.is_eq(Jpeg.decode.ctrl.comp(ctrl),
            2), samples, cr))
    case 1n+pp:
      match blk:
        case Jpeg.Blk{+samples, +bits, +pred, +bok}:
          match ctrl:
            case Jpeg.Ctrl{+comp, _bi, _mx, _my, _mcu, _rst}:
              +fr = {Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax} : Jpeg.Frame}
              blocks.sized(pp, Jpeg.decode.block.next(bits, preds, pred, ctrl, fr, scan, tabs, ri),
                Jpeg.decode.adv.ctrl(Jpeg.decode.adv(ctrl, fr, scan, ri)),
                Jpeg.decode.preds.next(Jpeg.decode.adv.duef(Jpeg.decode.adv(ctrl, fr, scan, ri)), preds, comp,
                  pred), ww,
                hh, nf, ids, hs, vs, tq, hmax, vmax, scan, tabs, ri, Jpeg.decode.paint.use(Jpeg.decode.geom(ctrl, fr,
                scan), U32.is_eq(comp, 0), samples, yy), Jpeg.decode.paint.use(Jpeg.decode.geom(ctrl, fr, scan),
                U32.is_eq(comp, 1), samples, cb), Jpeg.decode.paint.use(Jpeg.decode.geom(ctrl, fr, scan),
                U32.is_eq(comp, 2), samples, cr), (ok * bok : U32))

# the scan decode from its first block: a picture of the frame's size, or none
def start.sized(
  nn: Nat,
  bits: Jpeg.Bits,
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
  +tabs: Jpeg.Tabs,
  +ri: U32,
  yy: Array<U32>,
  cb: Array<U32>,
  cr: Array<U32>
) -> {Laws.jpg.sized(Img.decode_jpeg.out(Jpeg.decode.start(nn, bits, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax,
  vmax}, scan, tabs, ri, yy, cb, cr)), ww, hh) == True{} : Bool}:
  match nn:
    case 0n:
      -_s = bits
      -_y = yy
      -_b = cb
      -_r = cr
      {==}
    case 1n+pp:
      +fr = {Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax} : Jpeg.Frame}
      blocks.sized(pp, Jpeg.decode.block.of(bits, 0, Jpeg.decode.pred.zero(), fr, scan, tabs), Jpeg.Ctrl{0, 0, 0, 0, 0,
        0}, Jpeg.decode.pred.zero(), ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan, tabs, ri, yy, cb, cr, 1)

# a frame with a side of 0 is none; any other is decoded from its first block
def runn.sized(
  empty: Bool,
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
  +tabs: Jpeg.Tabs,
  ent: List<&2, U32>,
  +ri: U32
) -> {Laws.jpg.sized(Img.decode_jpeg.out(Jpeg.decode.run.n(empty, ww, hh, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax,
  vmax}, scan, tabs, ent, ri)), ww, hh) == True{} : Bool}:
  match empty:
    case True{}:
      -_e = ent
      {==}
    case False{}:
      start.sized(U32.to_nat(Jpeg.decode.nblocks(ww, hh, hs, vs, hmax, vmax)), Jpeg.Bits{0, 1, 0, ent}, ww, hh, nf,
        ids, hs, vs, tq, hmax, vmax, scan,
        tabs, ri, Jpeg.decode.plane((ww * hh : U32)), Jpeg.decode.plane((ww * hh : U32)),
        Jpeg.decode.plane((ww * hh : U32)))

# jpeg_run_sized: the scan decode is none or a picture of the frame's size
def run.sized(
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
  +tabs: Jpeg.Tabs,
  ent: List<&2, U32>,
  +ri: U32
) -> {Laws.jpg.sized(Img.decode_jpeg.out(Jpeg.decode.run(Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan,
  tabs, ent, ri)), ww, hh) == True{} : Bool}:
  runn.sized(Bool.or(U32.is_eq(ww, 0), U32.is_eq(hh, 0)), ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan, tabs, ent, ri)

# ---- the decoder's block count (IMG-JPG-2) ----

# the length of a component's units in the order
def len.units(
  +kk: Nat,
  +comp: U32,
  +bi: U32,
  +mx: U32,
  +my: U32,
  +mcu: U32
) -> {List.length(&2, Jpeg.Ctrl, Laws.jpg.o.units(kk, comp, bi, mx, my, mcu)) == kk : Nat}:
  match kk:
    case 0n:
      {==}
    case 1n+(+pp):
      Equal.cong(Nat, Nat, nn => 1n+nn, List.length(&2, Jpeg.Ctrl, Laws.jpg.o.units(pp, comp, (bi + 1 : U32), mx, my,
        mcu)), pp, len.units(pp, comp, (bi + 1 : U32), mx, my, mcu))

# the length of an MCU's components in the order: their data units summed
def len.comps(
  +nn: Nat,
  +comp: U32,
  +mx: U32,
  +my: U32,
  +mcu: U32,
  +sids: List<&2, U32>,
  +ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>
) -> {List.length(&2, Jpeg.Ctrl, Laws.jpg.o.comps(nn, comp, mx, my, mcu, sids, ids, hs, vs)) == Laws.jpg.usum(nn,
  comp, sids, ids, hs, vs) : Nat}:
  match nn:
    case 0n:
      {==}
    case 1n+(+pp):
      +un = U32.to_nat(Laws.jpg.units(comp, sids, ids, hs, vs))
      +l1 = {Laws.jpg.o.units(un, comp, 0, mx, my, mcu) : List<&2, Jpeg.Ctrl>}
      +l2 = {Laws.jpg.o.comps(pp, (comp + 1 : U32), mx, my, mcu, sids, ids, hs, vs) : List<&2, Jpeg.Ctrl>}
      +s2 = Laws.jpg.usum(pp, (comp + 1 : U32), sids, ids, hs, vs)
      Equal.trans(Nat, List.length(&2, Jpeg.Ctrl, List.append(&2, Jpeg.Ctrl, l1, l2)), Nat.add(List.length(&2,
        Jpeg.Ctrl, l1), List.length(&2, Jpeg.Ctrl, l2)), Nat.add(un, s2), len.app(l1, l2), Equal.trans(Nat,
        Nat.add(List.length(&2, Jpeg.Ctrl, l1), List.length(&2, Jpeg.Ctrl, l2)), Nat.add(un, List.length(&2,
        Jpeg.Ctrl, l2)), Nat.add(un, s2), Equal.cong(Nat, Nat, xx => Nat.add(xx, List.length(&2, Jpeg.Ctrl, l2)),
        List.length(&2, Jpeg.Ctrl, l1), un, len.units(un, comp, 0, mx, my, mcu)), Equal.cong(Nat, Nat,
        xx => Nat.add(un, xx), List.length(&2, Jpeg.Ctrl, l2), s2, len.comps(pp, (comp + 1 : U32), mx, my, mcu, sids,
        ids, hs, vs))))

# the length of an MCU row in the order: its MCUs times the data units of one
def len.row(
  +kk: Nat,
  +mx: U32,
  +my: U32,
  +mcu: U32,
  +ns: U32,
  +sids: List<&2, U32>,
  +ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>
) -> {List.length(&2, Jpeg.Ctrl, Laws.jpg.o.row(kk, mx, my, mcu, ns, sids, ids, hs, vs)) == Nat.mul(kk,
  Laws.jpg.usum(U32.to_nat(ns), 0, sids, ids, hs, vs)) : Nat}:
  match kk:
    case 0n:
      {==}
    case 1n+(+pp):
      +uu = Laws.jpg.usum(U32.to_nat(ns), 0, sids, ids, hs, vs)
      +l1 = {Laws.jpg.o.comps(U32.to_nat(ns), 0, mx, my, mcu, sids, ids, hs, vs) : List<&2, Jpeg.Ctrl>}
      +l2 = {Laws.jpg.o.row(pp, (mx + 1 : U32), my, (mcu + 1 : U32), ns, sids, ids, hs, vs) : List<&2, Jpeg.Ctrl>}
      Equal.trans(Nat, List.length(&2, Jpeg.Ctrl, List.append(&2, Jpeg.Ctrl, l1, l2)), Nat.add(List.length(&2,
        Jpeg.Ctrl, l1), List.length(&2, Jpeg.Ctrl, l2)), Nat.add(uu, Nat.mul(pp, uu)), len.app(l1, l2),
        Equal.trans(Nat, Nat.add(List.length(&2, Jpeg.Ctrl, l1), List.length(&2, Jpeg.Ctrl, l2)), Nat.add(uu,
        List.length(&2, Jpeg.Ctrl, l2)), Nat.add(uu, Nat.mul(pp, uu)), Equal.cong(Nat, Nat, xx => Nat.add(xx,
        List.length(&2, Jpeg.Ctrl, l2)), List.length(&2, Jpeg.Ctrl, l1), uu, len.comps(U32.to_nat(ns), 0, mx, my, mcu,
        sids, ids, hs, vs)), Equal.cong(Nat, Nat, xx => Nat.add(uu, xx), List.length(&2, Jpeg.Ctrl, l2), Nat.mul(pp,
        uu), len.row(pp, (mx + 1 : U32), my, (mcu + 1 : U32), ns, sids, ids, hs, vs))))

# the length of the order over mm MCU rows
def len.rows(
  +mm: Nat,
  +my: U32,
  +mcu: U32,
  +mw: U32,
  +ns: U32,
  +sids: List<&2, U32>,
  +ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>
) -> {List.length(&2, Jpeg.Ctrl, Laws.jpg.o.rows(mm, my, mcu, mw, ns, sids, ids, hs, vs)) == Nat.mul(mm,
  Nat.mul(U32.to_nat(mw), Laws.jpg.usum(U32.to_nat(ns), 0, sids, ids, hs, vs))) : Nat}:
  match mm:
    case 0n:
      {==}
    case 1n+(+pp):
      +ru = Nat.mul(U32.to_nat(mw), Laws.jpg.usum(U32.to_nat(ns), 0, sids, ids, hs, vs))
      +l1 = {Laws.jpg.o.row(U32.to_nat(mw), 0, my, mcu, ns, sids, ids, hs, vs) : List<&2, Jpeg.Ctrl>}
      +l2 = {Laws.jpg.o.rows(pp, (my + 1 : U32), Laws.jpg.idx(U32.to_nat(mw), mcu), mw, ns, sids, ids, hs, vs) :
        List<&2, Jpeg.Ctrl>}
      Equal.trans(Nat, List.length(&2, Jpeg.Ctrl, List.append(&2, Jpeg.Ctrl, l1, l2)), Nat.add(List.length(&2,
        Jpeg.Ctrl, l1), List.length(&2, Jpeg.Ctrl, l2)), Nat.add(ru, Nat.mul(pp, ru)), len.app(l1, l2),
        Equal.trans(Nat, Nat.add(List.length(&2, Jpeg.Ctrl, l1), List.length(&2, Jpeg.Ctrl, l2)), Nat.add(ru,
        List.length(&2, Jpeg.Ctrl, l2)), Nat.add(ru, Nat.mul(pp, ru)), Equal.cong(Nat, Nat, xx => Nat.add(xx,
        List.length(&2, Jpeg.Ctrl, l2)), List.length(&2, Jpeg.Ctrl, l1), ru, len.row(U32.to_nat(mw), 0, my, mcu, ns,
        sids, ids, hs, vs)), Equal.cong(Nat, Nat, xx => Nat.add(ru, xx), List.length(&2, Jpeg.Ctrl, l2), Nat.mul(pp,
        ru), len.rows(pp, (my + 1 : U32), Laws.jpg.idx(U32.to_nat(mw), mcu), mw, ns, sids, ids, hs, vs))))

# multiplication is associative
def mul.assoc(+aa: Nat, +bb: Nat, +cc: Nat) -> {Nat.mul(Nat.mul(aa, bb), cc) == Nat.mul(aa, Nat.mul(bb, cc)) : Nat}:
  match aa:
    case 0n:
      {==}
    case 1n+(+pp):
      Equal.trans(Nat, Nat.mul(Nat.add(bb, Nat.mul(pp, bb)), cc), Nat.add(Nat.mul(bb, cc), Nat.mul(Nat.mul(pp, bb),
        cc)), Nat.add(Nat.mul(bb, cc), Nat.mul(pp, Nat.mul(bb, cc))), R.mul_add(bb, Nat.mul(pp, bb), cc),
        Equal.cong(Nat, Nat, xx => Nat.add(Nat.mul(bb, cc), xx), Nat.mul(Nat.mul(pp, bb), cc), Nat.mul(pp,
        Nat.mul(bb, cc)), mul.assoc(pp, bb, cc)))

# x is at most x times a positive number
def le.mulr(+xx: Nat, +uu: Nat, +hu: {1n+npred(uu) == uu : Nat}) -> {Nat.is_le(xx, Nat.mul(xx, uu)) == True{} : Bool}:
  +u1 = npred(uu)
  Equal.trans(Bool, Nat.is_le(xx, Nat.mul(xx, uu)), Nat.is_le(xx, Nat.add(xx, Nat.mul(xx, u1))), True{},
    Equal.cong(Nat, Bool, nn => Nat.is_le(xx, nn), Nat.mul(xx, uu), Nat.add(xx, Nat.mul(xx, u1)), Equal.trans(Nat,
    Nat.mul(xx, uu), Nat.mul(xx, 1n+u1), Nat.add(xx, Nat.mul(xx, u1)), Equal.cong(Nat, Nat, nn => Nat.mul(xx, nn), uu,
    1n+u1, Equal.sym(Nat, 1n+u1, uu, hu)), R.mul_succ(xx, u1))), R.le_add_more(xx, xx, Nat.mul(xx, u1),
    R.le_refl(xx)))

# the scan has at least one data unit per MCU
def usum.pos(
  +ns: U32,
  +sids: List<&2, U32>,
  +ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>,
  +h_ns: {U32.is_lt(0, ns) == True{} : Bool},
  +h_units: {Laws.jpg.units.ok(U32.to_nat(ns), 0, sids, ids, hs, vs, True{}) == True{} : Bool}
) -> {1n+npred(Laws.jpg.usum(U32.to_nat(ns), 0, sids, ids, hs, vs)) == Laws.jpg.usum(U32.to_nat(ns), 0, sids, ids,
  hs, vs) : Nat}:
  +n1 = npred(U32.to_nat(ns))
  +hn = {pos.nat(ns, h_ns) : {1n+n1 == U32.to_nat(ns) : Nat}}
  +u0 = Laws.jpg.units(0, sids, ids, hs, vs)
  +hu = {Equal.trans(Bool, Laws.jpg.units.ok(1n+n1, 0, sids, ids, hs, vs, True{}), Laws.jpg.units.ok(U32.to_nat(ns),
    0, sids, ids, hs, vs, True{}), True{}, Equal.cong(Nat, Bool, nn => Laws.jpg.units.ok(nn, 0, sids, ids, hs, vs,
    True{}), 1n+n1, U32.to_nat(ns), hn), h_units) : {Laws.jpg.units.ok(1n+n1, 0, sids, ids, hs, vs, True{}) == True{} :
    Bool}}
  +hp = {uok.acc(n1, 1, sids, ids, hs, vs, U32.is_lt(0, u0), hu) : {U32.is_lt(0, u0) == True{} : Bool}}
  +k0 = npred(U32.to_nat(u0))
  +rest = Laws.jpg.usum(n1, 1, sids, ids, hs, vs)
  succ.of(Laws.jpg.usum(U32.to_nat(ns), 0, sids, ids, hs, vs), Equal.trans(Bool, Nat.is_lt(0n,
    Laws.jpg.usum(U32.to_nat(ns), 0, sids, ids, hs, vs)), Nat.is_lt(0n, Nat.add(U32.to_nat(u0), rest)), True{},
    Equal.cong(Nat, Bool, nn => Nat.is_lt(0n, Laws.jpg.usum(nn, 0, sids, ids, hs, vs)), U32.to_nat(ns), 1n+n1,
    Equal.sym(Nat, 1n+n1, U32.to_nat(ns), hn)), Equal.cong(Nat, Bool, nn => Nat.is_lt(0n, Nat.add(nn, rest)),
    U32.to_nat(u0), 1n+k0, Equal.sym(Nat, 1n+k0, U32.to_nat(u0), pos.nat(u0, hp)))))

# the scan's data units per MCU are one more than their predecessor
def usum.Pos(+ns: U32, +sids: List<&2, U32>, +ids: List<&2, U32>, +hs: List<&2, U32>, +vs: List<&2, U32>) -> Type:
  {1n+npred(Laws.jpg.usum(U32.to_nat(ns), 0, sids, ids, hs, vs)) == Laws.jpg.usum(U32.to_nat(ns), 0, sids, ids, hs, vs)
    : Nat}

# the blocks of a frame of mw by mh MCUs, as a number
def fit.n(
  +mw: U32,
  +mh: U32,
  +ns: U32,
  +sids: List<&2, U32>,
  +ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>
) -> Nat:
  Nat.mul(Nat.mul(U32.to_nat(mw), U32.to_nat(mh)), Laws.jpg.usum(U32.to_nat(ns), 0, sids, ids, hs, vs))

# jpeg_walk_count: the decoder's U32 block count is the order's length
def walk.count(
  +mw: U32,
  +mh: U32,
  +bs: U32,
  +ns: U32,
  +sids: List<&2, U32>,
  +ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>,
  +top: U32,
  h_pos: usum.Pos(ns, sids, ids, hs, vs),
  +h_sum: {U32.to_nat(bs) == Laws.jpg.usum(U32.to_nat(ns), 0, sids, ids, hs, vs) : Nat},
  +h_fit: {Nat.is_le(fit.n(mw, mh, ns, sids, ids, hs, vs), U32.to_nat(top)) == True{} : Bool}
) -> {U32.to_nat((mw * mh * bs : U32)) == List.length(&2, Jpeg.Ctrl, Laws.jpg.o.rows(U32.to_nat(mh), 0, 0, mw, ns,
  sids, ids, hs, vs)) : Nat}:
  +uu = Laws.jpg.usum(U32.to_nat(ns), 0, sids, ids, hs, vs)
  +wn = U32.to_nat(mw)
  +hn = U32.to_nat(mh)
  +in = {R.u32_mul_below(mw, mh, top, R.le_trans(Nat.mul(wn, hn), Nat.mul(Nat.mul(wn, hn), uu), U32.to_nat(top),
    le.mulr(Nat.mul(wn, hn), uu, h_pos), h_fit)) : {U32.to_nat((mw * mh : U32)) == Nat.mul(wn, hn) : Nat}}
  +eo = {Equal.trans(Nat, Nat.mul(U32.to_nat((mw * mh : U32)), U32.to_nat(bs)), Nat.mul(Nat.mul(wn, hn),
    U32.to_nat(bs)), Nat.mul(Nat.mul(wn, hn), uu), Equal.cong(Nat, Nat, nn => Nat.mul(nn, U32.to_nat(bs)),
    U32.to_nat((mw * mh : U32)), Nat.mul(wn, hn), in), Equal.cong(Nat, Nat, nn => Nat.mul(Nat.mul(wn, hn), nn),
    U32.to_nat(bs), uu, h_sum)) : {Nat.mul(U32.to_nat((mw * mh : U32)), U32.to_nat(bs)) == Nat.mul(Nat.mul(wn, hn), uu)
    : Nat}}
  +out = {R.u32_mul_below((mw * mh : U32), bs, top, Equal.trans(Bool, Nat.is_le(Nat.mul(U32.to_nat((mw * mh : U32)),
    U32.to_nat(bs)), U32.to_nat(top)), Nat.is_le(Nat.mul(Nat.mul(wn, hn), uu), U32.to_nat(top)), True{},
    Equal.cong(Nat, Bool, nn => Nat.is_le(nn, U32.to_nat(top)), Nat.mul(U32.to_nat((mw * mh : U32)), U32.to_nat(bs)),
    Nat.mul(Nat.mul(wn, hn), uu), eo), h_fit)) : {U32.to_nat((mw * mh * bs : U32)) == Nat.mul(U32.to_nat((mw * mh :
    U32)), U32.to_nat(bs)) : Nat}}
  Equal.trans(Nat, U32.to_nat((mw * mh * bs : U32)), Nat.mul(Nat.mul(wn, hn), uu), List.length(&2, Jpeg.Ctrl,
    Laws.jpg.o.rows(hn, 0, 0, mw, ns, sids, ids, hs, vs)), Equal.trans(Nat, U32.to_nat((mw * mh * bs : U32)),
    Nat.mul(U32.to_nat((mw * mh : U32)), U32.to_nat(bs)), Nat.mul(Nat.mul(wn, hn), uu), out, eo), Equal.trans(Nat,
    Nat.mul(Nat.mul(wn, hn), uu), Nat.mul(Nat.mul(hn, wn), uu), List.length(&2, Jpeg.Ctrl, Laws.jpg.o.rows(hn, 0, 0,
    mw, ns, sids, ids, hs, vs)), Equal.cong(Nat, Nat, nn => Nat.mul(nn, uu), Nat.mul(wn, hn), Nat.mul(hn, wn),
    R.mul_comm(wn, hn)), Equal.trans(Nat, Nat.mul(Nat.mul(hn, wn), uu), Nat.mul(hn, Nat.mul(wn, uu)), List.length(&2,
    Jpeg.Ctrl, Laws.jpg.o.rows(hn, 0, 0, mw, ns, sids, ids, hs, vs)), mul.assoc(hn, wn, uu), Equal.sym(Nat,
    List.length(&2, Jpeg.Ctrl, Laws.jpg.o.rows(hn, 0, 0, mw, ns, sids, ids, hs, vs)), Nat.mul(hn, Nat.mul(wn, uu)),
    len.rows(hn, 0, 0, mw, ns, sids, ids, hs, vs)))))

# ---- stuffing and unstuffing (IMG-JPG-3) ----

# bytes stuffed in order onto acc, the first byte first
def stf(xs: List<&2, U32>, +acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case +bb <> rest:
      Jenc.encode.stuff.put(U32.is_eq(bb, 255), bb, stf(rest, acc))

# the encoder stuffing written bytes, newest first, is stuffing them in order
def stall.rev(
  xs: List<&2, U32>,
  +rr: List<&2, U32>,
  +acc: List<&2, U32>
) -> {Jenc.encode.stuff.all(List.reverse.go(&2, U32, xs, rr), acc) == Jenc.encode.stuff.all(rr, stf(xs, acc)) :
  List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case +bb <> rest:
      stall.rev(rest, bb <> rr, acc)

# a byte that is not 255, read by the bit reader: its eight bits, top first, each or-ed with False
def rd.plain(
  h0: Bool,
  +c0: Bool,
  +c1: Bool,
  +c2: Bool,
  +c3: Bool,
  +c4: Bool,
  +c5: Bool,
  +c6: Bool,
  +c7: Bool,
  +rest: List<&2, U32>,
  +ok: U32
) -> {Jpeg.decode.nbits(8n, True{}, W7.byte.w(c0, c1, c2, c3, c4, c5, c6, c7) <> rest, False{}, False{}, h0, 0, 0, ok,
  0) == (Jpeg.Bits{0, ok, 0, rest}, W7.byte.w(Bool.or(c0, False{}), Bool.or(c1, False{}), Bool.or(c2, False{}),
  Bool.or(c3, False{}), Bool.or(c4, False{}), Bool.or(c5, False{}), Bool.or(c6, False{}), Bool.or(c7, False{}))) :
  Jpeg.Bits & U32}:
  {==}

# one stuffed byte, read by the bit reader: the byte back, the reader at the bytes after it
def rd.z(
  zz: Bool,
  +c0: Bool,
  +c1: Bool,
  +c2: Bool,
  +c3: Bool,
  +c4: Bool,
  +c5: Bool,
  +c6: Bool,
  +c7: Bool,
  +rest: List<&2, U32>,
  +ok: U32,
  +ee: {U32.is_eq(W7.byte.w(c0, c1, c2, c3, c4, c5, c6, c7), 255) == zz : Bool}
) -> {Jpeg.decode.read.n(8, Jpeg.Bits{0, ok, 0, Jenc.encode.stuff.put(zz, W7.byte.w(c0, c1, c2, c3, c4, c5, c6, c7),
  rest)}) == (Jpeg.Bits{0, ok, 0, rest}, W7.byte.w(c0, c1, c2, c3, c4, c5, c6, c7)) : Jpeg.Bits & U32}:
  match zz:
    case False{}:
      +bw = W7.byte.w(c0, c1, c2, c3, c4, c5, c6, c7)
      +h0 = U32.is_eq(bw, 0)
      Equal.trans(Jpeg.Bits & U32, Jpeg.decode.nbits(8n, True{}, bw <> rest, False{}, U32.is_eq(bw, 255), h0, 0, 0,
        ok, 0),
        Jpeg.decode.nbits(8n, True{}, bw <> rest, False{}, False{}, h0, 0, 0, ok, 0), (Jpeg.Bits{0, ok, 0, rest}, bw),
        Equal.cong(Bool, Jpeg.Bits & U32, hb => Jpeg.decode.nbits(8n, True{}, bw <> rest, False{}, hb, h0, 0, 0, ok, 0),
        U32.is_eq(bw, 255), False{}, ee), Equal.trans(Jpeg.Bits & U32, Jpeg.decode.nbits(8n, True{}, bw <> rest,
          False{},
        False{}, h0, 0, 0, ok, 0), (Jpeg.Bits{0, ok, 0, rest}, W7.byte.w(Bool.or(c0, False{}), Bool.or(c1, False{}),
        Bool.or(c2, False{}), Bool.or(c3, False{}), Bool.or(c4, False{}), Bool.or(c5, False{}), Bool.or(c6, False{}),
        Bool.or(c7, False{}))), (Jpeg.Bits{0, ok, 0, rest}, bw), rd.plain(h0, c0, c1, c2, c3, c4, c5, c6, c7, rest, ok),
        Equal.cong(U32, Jpeg.Bits & U32, vv => {(Jpeg.Bits{0, ok, 0, rest}, vv) : Jpeg.Bits & U32},
        W7.byte.w(Bool.or(c0, False{}), Bool.or(c1, False{}), Bool.or(c2, False{}), Bool.or(c3, False{}),
        Bool.or(c4, False{}), Bool.or(c5, False{}), Bool.or(c6, False{}), Bool.or(c7, False{})), bw,
        W7.or_byte(c0, c1, c2, c3, c4, c5, c6, c7))))
    case True{}:
      +bw = W7.byte.w(c0, c1, c2, c3, c4, c5, c6, c7)
      eb = Equal.sym(U32, bw, 255, U32L.ueq(bw, 255, ee))
      %eb : {Jpeg.decode.read.n(8, Jpeg.Bits{0, ok, 0, _ <> (0 <> rest)}) == (Jpeg.Bits{0, ok, 0, rest}, _) :
        Jpeg.Bits & U32}
      {==}

# the bit reader reads stuffed bytes back, eight bits at a time
def rd.list(
  +bs: List<&2, Laws.JByte>,
  +ok: U32,
  +rest: List<&2, U32>
) -> {Laws.jpg.read8(List.length(&2, Laws.JByte, bs), Jpeg.decode.read.n(8, Jpeg.Bits{0, ok, 0,
  stf(Laws.jpg.bytes(bs), rest)})) == Laws.jpg.bytes(bs) : List<&2, U32>}:
  match bs:
    case Nil{}:
      {==}
    case +bb <> +tl:
      match bb:
        case Laws.JByte{+c0, +c1, +c2, +c3, +c4, +c5, +c6, +c7}:
          +bw = W7.byte.w(c0, c1, c2, c3, c4, c5, c6, c7)
          +st = stf(Laws.jpg.bytes(tl), rest)
          Equal.trans(List<&2, U32>, Laws.jpg.read8(1n+List.length(&2, Laws.JByte, tl), Jpeg.decode.read.n(8,
            Jpeg.Bits{0, ok, 0, Jenc.encode.stuff.put(U32.is_eq(bw, 255), bw, st)})), Laws.jpg.read8(1n+List.length(&2,
            Laws.JByte, tl), (Jpeg.Bits{0, ok, 0, st}, bw)), bw <> Laws.jpg.bytes(tl), Equal.cong(Jpeg.Bits & U32,
            List<&2, U32>, gg => Laws.jpg.read8(1n+List.length(&2, Laws.JByte, tl), gg), Jpeg.decode.read.n(8,
            Jpeg.Bits{0, ok, 0, Jenc.encode.stuff.put(U32.is_eq(bw, 255), bw, st)}), (Jpeg.Bits{0, ok, 0, st}, bw),
            rd.z(U32.is_eq(bw, 255), c0, c1, c2, c3, c4, c5, c6, c7, st, ok, {==})), Equal.cong(List<&2, U32>,
            List<&2, U32>, ll => {bw <> ll : List<&2, U32>}, Laws.jpg.read8(List.length(&2, Laws.JByte, tl),
            Jpeg.decode.read.n(8, Jpeg.Bits{0, ok, 0, st})), Laws.jpg.bytes(tl), rd.list(tl, ok, rest)))
