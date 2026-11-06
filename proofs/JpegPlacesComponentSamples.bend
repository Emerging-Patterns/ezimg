# proofs of laws/JpegPlacesComponentSamples.bend
import Base
import ../main.bend as Img
import ../src/jpeg.bend as Jpeg
import ../laws/JpegPlacesComponentSamples.bend as Laws
import ../laws/defs/PointInside.bend as D1
import ./lemmas/BasicFacts.bend as M1
import ./lemmas/JpegHuffmanCoding.bend as M2
import ./lemmas/RowMajorIndex.bend as M3
import ./lemmas/SubtractionAndHuffmanWalk.bend as M4
import ./lemmas/WordAddition.bend as M5
import ./lemmas/PngEncoderArithmetic.bend as M6

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

# a factor of 1, 2 or 4 (the or laws/JpegPlacesComponentSamples.bend's allowed factors unfold to): a
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
      es = Equal.sym(U32, ff, 4, M1.ueq(ff, 4, e4))
      %es : pp(_)
      p4
    case False{}:
      Empty.absurd(pp(ff), M1.false_true(h_ok))

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
      es = Equal.sym(U32, ff, 2, M1.ueq(ff, 2, e2))
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
      es = Equal.sym(U32, ff, 1, M1.ueq(ff, 1, e1))
      %es : pp(_)
      p1
    case False{}:
      fac_elim2(pp, ff, U32.is_eq(ff, 2), {==}, h_ok, p2, p4)

# ---- block painting (laws/JpegPlacesComponentSamples.bend) ----

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

# ---- placement of any scan component (laws/JpegPlacesComponentSamples.bend) ----

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
  {Jpeg.decode.dispatch(192, body, frame, scan, tabs, ent, ri, kind, bad) == M1.stop(scan, tabs, ent, ri, kind) :
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
  ri, kind, bad}) == Jpeg.decode.walk(rest, M1.stop(scan, tabs, ent, ri, kind)) : Jpeg.St}:
  +slb = {Jpeg.decode.step.len.b(U32.is_lt(Jpeg.decode.u16(lh, ll), 2), 192, Jpeg.decode.u16(lh, ll), frame, scan, tabs,
    ent, ri, kind, bad) : Jpeg.St}
  Equal.trans(Jpeg.St, Jpeg.decode.walk(List.append(&2, U32, body, rest), slb),
    Jpeg.decode.walk(rest, Jpeg.decode.walk(body, slb)), Jpeg.decode.walk(rest, M1.stop(scan, tabs, ent, ri, kind)),
    M2.walk_app(body, rest, slb),
    Equal.trans(Jpeg.St, Jpeg.decode.walk(rest, Jpeg.decode.walk(body, slb)),
      Jpeg.decode.walk(rest, Jpeg.decode.dispatch(192, body, frame, scan, tabs, ent, ri, kind, bad)),
      Jpeg.decode.walk(rest, M1.stop(scan, tabs, ent, ri, kind)),
      Equal.cong(Jpeg.St, Jpeg.St, st => Jpeg.decode.walk(rest, st), Jpeg.decode.walk(body, slb),
        Jpeg.decode.dispatch(192, body, frame, scan, tabs, ent, ri, kind, bad),
        M2.seg.read(U32.is_lt(Jpeg.decode.u16(lh, ll), 2), Jpeg.decode.u16(lh, ll), body, 192, frame, scan, tabs, ent,
          ri, kind, bad, h_len, h_body)),
      Equal.cong(Jpeg.St, Jpeg.St, st => Jpeg.decode.walk(rest, st),
        Jpeg.decode.dispatch(192, body, frame, scan, tabs, ent, ri, kind, bad), M1.stop(scan, tabs, ent, ri, kind),
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
  tabs, ent, ri, kind) == M1.stop(scan, tabs, ent, ri, kind) : Jpeg.St}:
  match cok:
    case True{}:
      {==}
    case False{}:
      {==}

# a count the decoder does not read is not 1, so the frame is read as the many-component frame it is not
def sof.cnt.n1(
  one: Bool,
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
  +kind: U32,
  +bad: U32,
  h1: {U32.is_eq(nf, 1) == one : Bool},
  h_nf: {Bool.or(U32.is_eq(nf, 1), U32.is_eq(nf, 3)) == False{} : Bool}
) -> {Jpeg.decode.read.sof.n1(one, cok, ww, hh, nf, ids, hs, vs, tq, scan, tabs, ent, ri, kind, bad) ==
  M1.stop(scan, tabs, ent, ri, kind) : Jpeg.St}:
  match one:
    case True{}:
      Empty.absurd({Jpeg.decode.read.sof.n1(True{}, cok, ww, hh, nf, ids, hs, vs, tq, scan, tabs, ent, ri, kind, bad) ==
        M1.stop(scan, tabs, ent, ri, kind) : Jpeg.St}, M1.jst.true_false(Equal.trans(Bool, True{}, Bool.or(U32.is_eq(nf,
        1), U32.is_eq(nf, 3)), False{}, Equal.cong(Bool, Bool, bb => Bool.or(bb, U32.is_eq(nf, 3)), True{},
        U32.is_eq(nf, 1), Equal.sym(Bool, U32.is_eq(nf, 1), True{}, h1)), h_nf)))
    case False{}:
      es = Equal.sym(Bool, Bool.or(U32.is_eq(nf, 1), U32.is_eq(nf, 3)), False{}, h_nf)
      %es : {Jpeg.decode.read.sof.c(cok, Bool.and(_, U32.is_eq(bad, 0)), U32.is_eq(Jpeg.decode.vmax(hs, 0), 0), ww,
        hh, nf, ids, hs, vs, tq, scan, tabs, ent, ri, kind) == M1.stop(scan, tabs, ent, ri, kind) : Jpeg.St}
      sof.cok(cok, ww, hh, nf, ids, hs, vs, tq, scan, tabs, ent, ri, kind)

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
) -> {Jpeg.decode.read.sof.f(cc, ww, hh, nf, scan, tabs, ent, ri, kind, bad) == M1.stop(scan, tabs, ent, ri, kind) :
  Jpeg.St}:
  match cc:
    case Jpeg.Comps{+ids, +hs, +vs, +tq, cok}:
      sof.cnt.n1(U32.is_eq(nf, 1), cok, ww, hh, nf, ids, hs, vs, tq, scan, tabs, ent, ri, kind, bad, {==}, h_nf)

# the read statement moved along an equality of arrays
def get.tr(
  -bb: Array<U32>,
  -aa: Array<U32>,
  +ii: U32,
  ee: {bb == aa : Array<U32>},
  hh: {Array.get(U32, bb, ii) == (bb, D1.jpg.val(Array.get(U32, bb, ii))) : Array<U32> & U32}
) -> {Array.get(U32, aa, ii) == (aa, D1.jpg.val(Array.get(U32, aa, ii))) : Array<U32> & U32}:
  %ee : {Array.get(U32, _, ii) == (_, D1.jpg.val(Array.get(U32, _, ii))) : Array<U32> & U32}
  hh

# a plane read out from point jj on: element mm is the plane's point jj + mm
def emit.at(
  nn: Nat,
  mm: Nat,
  -aa: Array<U32>,
  +jj: U32,
  dd: M2.Dup(aa),
  hm: {Nat.is_lt(mm, nn) == True{} : Bool}
) -> {List.get(&2, U32, Jpeg.decode.emit(nn, Array.get(U32, aa, jj), (jj + 1 : U32)), mm) ==
  Some{D1.jpg.val(Array.get(U32, aa, Laws.jpg.idx(mm, jj)))} : Maybe<&2, U32>}:
  match nn:
    case 0n:
      -_d = dd
      Empty.absurd({List.get(&2, U32, Jpeg.decode.emit(0n, Array.get(U32, aa, jj), (jj + 1 : U32)), mm) ==
        Some{D1.jpg.val(Array.get(U32, aa, Laws.jpg.idx(mm,
          jj)))} : Maybe<&2, U32>}, M1.false_true(Equal.trans(Bool, False{},
        Nat.is_lt(mm, 0n), True{}, M1.lt_zero_false(mm), hm)))
    case 1n+pp:
      match mm:
        case 0n:
          (b1, _b2, e1, _e2) = dd
          se = Equal.sym(Array<U32> & U32, Array.get(U32, aa, jj), (aa, D1.jpg.val(Array.get(U32, aa, jj))),
            get.tr(b1, aa, jj, e1, M2.get.eq(b1, jj)))
          %se : {List.get(&2, U32, Jpeg.decode.emit(1n+pp, _, (jj + 1 : U32)), 0n) ==
            Some{D1.jpg.val(Array.get(U32, aa, jj))} : Maybe<&2, U32>}
          {==}
        case 1n+qq:
          (b1, b2, e1, e2) = dd
          se = Equal.sym(Array<U32> & U32, Array.get(U32, aa, jj), (aa, D1.jpg.val(Array.get(U32, aa, jj))),
            get.tr(b1, aa, jj, e1, M2.get.eq(b1, jj)))
          %se : {List.get(&2, U32, Jpeg.decode.emit(1n+pp, _, (jj + 1 : U32)), 1n+qq) ==
            Some{D1.jpg.val(Array.get(U32, aa, Laws.jpg.idx(1n+qq, jj)))} : Maybe<&2, U32>}
          emit.at(pp, qq, aa, (jj + 1 : U32), M2.dup.tr(b2, aa, e2, M2.dup(b2)), hm)

# jj advanced one step at a time, mm times, is jj + mm when that stays within the U32 tt
def idx.nat(
  +mm: Nat,
  +jj: U32,
  +tt: U32,
  +hh: {Nat.is_le(Nat.add(U32.to_nat(jj), mm), U32.to_nat(tt)) == True{} : Bool}
) -> {U32.to_nat(Laws.jpg.idx(mm, jj)) == Nat.add(U32.to_nat(jj), mm) : Nat}:
  match mm:
    case 0n:
      Equal.sym(Nat, Nat.add(U32.to_nat(jj), 0n), U32.to_nat(jj), M1.ras.add_zero(U32.to_nat(jj)))
    case 1n+(+pp):
      +jn = U32.to_nat(jj)
      +h1 = {M1.le_trans(Nat.add(jn, 1n), Nat.add(jn, 1n+pp), U32.to_nat(tt), M1.le_add_mono(jn, 1n, 1n+pp,
        M1.le_zero(pp)), hh) : {Nat.is_le(Nat.add(jn, 1n), U32.to_nat(tt)) == True{} : Bool}}
      +e1 = {M5.u32_add_below(jj, 1, tt, h1) : {U32.to_nat((jj + 1 : U32)) == Nat.add(jn, 1n) : Nat}}
      +ea = {Equal.trans(Nat, Nat.add(U32.to_nat((jj + 1 : U32)), pp), Nat.add(Nat.add(jn, 1n), pp), Nat.add(jn, 1n+pp),
        Equal.cong(Nat, Nat, xx => Nat.add(xx, pp), U32.to_nat((jj + 1 : U32)), Nat.add(jn, 1n), e1),
        M1.ras.add_assoc(jn, 1n, pp)) : {Nat.add(U32.to_nat((jj + 1 : U32)), pp) == Nat.add(jn, 1n+pp) : Nat}}
      h2 = Equal.trans(Bool, Nat.is_le(Nat.add(U32.to_nat((jj + 1 : U32)), pp), U32.to_nat(tt)),
        Nat.is_le(Nat.add(jn, 1n+pp), U32.to_nat(tt)), True{}, Equal.cong(Nat, Bool, xx => Nat.is_le(xx,
        U32.to_nat(tt)), Nat.add(U32.to_nat((jj + 1 : U32)), pp), Nat.add(jn, 1n+pp), ea), hh)
      Equal.trans(Nat, U32.to_nat(Laws.jpg.idx(pp, (jj + 1 : U32))), Nat.add(U32.to_nat((jj + 1 : U32)), pp),
        Nat.add(jn, 1n+pp), idx.nat(pp, (jj + 1 : U32), tt, h2), ea)

# the index reached by counting kk steps from 0 is kk
def idx.of(+kk: U32) -> {Laws.jpg.idx(U32.to_nat(kk), 0) == kk : U32}:
  +kn = U32.to_nat(kk)
  +ix = Laws.jpg.idx(kn, 0)
  M1.ueq(ix, kk, Equal.trans(Bool, U32.is_eq(ix, kk), Nat.is_eq(U32.to_nat(ix), kn), True{}, M1.u32_eq(ix, kk),
    Equal.trans(Bool, Nat.is_eq(U32.to_nat(ix), kn), Nat.is_eq(kn, kn), True{}, Equal.cong(Nat, Bool,
    xx => Nat.is_eq(xx, kn), U32.to_nat(ix), kn, idx.nat(kn, 0, kk, M1.le_refl(kn))), M1.nat_eq_refl(kn))))

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
) -> {M1.nxt(Jpeg.Ctrl{comp, bi, mx, my, mcu, rst}, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax},
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
) -> {M1.tr(left, ctrl, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, Jpeg.Scan{ns, sids, td, ta, ss, se, ah},
  ri) ==
  M1.tr(left, Laws.jpg.pos(ctrl), Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, Jpeg.Scan{ns, sids, td, ta, ss, se,  # noqa: S002
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
          Equal.cong(Jpeg.Ctrl, List<&2, Jpeg.Ctrl>, cc => {Jpeg.Ctrl{comp, bi, mx, my, mcu, 0} <> M1.tr(pp, cc, fr, sc,
            ri) :
            List<&2, Jpeg.Ctrl>}, M1.nxt(Jpeg.Ctrl{comp, bi, mx, my, mcu, rst}, fr, sc, ri),
            M1.nxt(Jpeg.Ctrl{comp, bi, mx, my, mcu, 0}, fr, sc, ri),
            Equal.trans(Jpeg.Ctrl, M1.nxt(Jpeg.Ctrl{comp, bi, mx, my, mcu, rst}, fr, sc, ri), res,
              M1.nxt(Jpeg.Ctrl{comp, bi, mx, my, mcu, 0}, fr, sc, ri), e1, Equal.sym(Jpeg.Ctrl,
              M1.nxt(Jpeg.Ctrl{comp, bi, mx, my, mcu, 0}, fr, sc, ri), res, e0)))

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
  se, ah}, ri) == M1.tr(left, ctrl, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, Jpeg.Scan{ns, sids, td, ta, ss,
  se, ah}, ri) : List<&2, Jpeg.Ctrl>}:
  match left:
    case 0n:
      {==}
    case 1n+(+pp):
      +fr = {Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax} : Jpeg.Frame}
      +sc = {Jpeg.Scan{ns, sids, td, ta, ss, se, ah} : Jpeg.Scan}
      +nc = {Jpeg.decode.adv.ctrl(Jpeg.decode.adv(ctrl, fr, sc, ri)) : Jpeg.Ctrl}
      Equal.cong(List<&2, Jpeg.Ctrl>, List<&2, Jpeg.Ctrl>, ll => {Laws.jpg.pos(ctrl) <> ll : List<&2, Jpeg.Ctrl>},
        Laws.jpg.trace(pp, nc, fr, sc, ri), M1.tr(pp, Laws.jpg.pos(nc), fr, sc, ri),
        Equal.trans(List<&2, Jpeg.Ctrl>, Laws.jpg.trace(pp, nc, fr, sc, ri), M1.tr(pp, nc, fr, sc, ri),
          M1.tr(pp, Laws.jpg.pos(nc), fr, sc, ri),
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
def jfin.npred(nn: Nat) -> Nat:
  match nn:
    case 0n:
      0n
    case 1n+pp:
      pp

# a number above 0 is one more than its predecessor
def succ.of(+nn: Nat, hh: {Nat.is_lt(0n, nn) == True{} : Bool}) -> {1n+jfin.npred(nn) == nn : Nat}:
  match nn:
    case 0n:
      Empty.absurd({1n == 0n : Nat}, M1.false_true(hh))
    case 1n+_pp:
      {==}

# a U32 above 0 is one more than its predecessor, as a number
def pos.nat(
  +uu: U32,
  hh: {U32.is_lt(0, uu) == True{} : Bool}
) -> {1n+jfin.npred(U32.to_nat(uu)) == U32.to_nat(uu) : Nat}:
  succ.of(U32.to_nat(uu), Equal.trans(Bool, Nat.is_lt(0n, U32.to_nat(uu)), U32.is_lt(0, uu), True{},
    Equal.sym(Bool, U32.is_lt(0, uu), Nat.is_lt(0n, U32.to_nat(uu)), M5.u32_lt(0, uu)), hh))

# xx + 1 does not wrap while xx + 1 + qq is some U32's value
def inc.nat(
  +xx: U32,
  +uu: U32,
  +qq: Nat,
  +hb: {Nat.add(U32.to_nat(xx), 1n+qq) == U32.to_nat(uu) : Nat}
) -> {U32.to_nat((xx + 1 : U32)) == Nat.add(U32.to_nat(xx), 1n) : Nat}:
  +bn = U32.to_nat(xx)
  M5.u32_add_below(xx, 1, uu, Equal.trans(Bool, Nat.is_le(Nat.add(bn, 1n), U32.to_nat(uu)),
    Nat.is_le(Nat.add(bn, 1n), Nat.add(bn, 1n+qq)), True{}, Equal.cong(Nat, Bool, zz => Nat.is_le(Nat.add(bn, 1n), zz),
    U32.to_nat(uu), Nat.add(bn, 1n+qq), Equal.sym(Nat, Nat.add(bn, 1n+qq), U32.to_nat(uu), hb)),
    M1.le_add_mono(bn, 1n, 1n+qq, M1.le_zero(qq))))

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
    M5.u32_lt((xx + 1 : U32), uu), Equal.trans(Bool, Nat.is_lt(U32.to_nat((xx + 1 : U32)), U32.to_nat(uu)),
    Nat.is_lt(Nat.add(bn, 1n), Nat.add(bn, 1n+(1n+pp))), True{}, Equal.trans(Bool,
    Nat.is_lt(U32.to_nat((xx + 1 : U32)), U32.to_nat(uu)), Nat.is_lt(Nat.add(bn, 1n), U32.to_nat(uu)),
    Nat.is_lt(Nat.add(bn, 1n), Nat.add(bn, 1n+(1n+pp))), Equal.cong(Nat, Bool, zz => Nat.is_lt(zz, U32.to_nat(uu)),
    U32.to_nat((xx + 1 : U32)), Nat.add(bn, 1n), e1), Equal.cong(Nat, Bool, zz => Nat.is_lt(Nat.add(bn, 1n), zz),
    U32.to_nat(uu), Nat.add(bn, 1n+(1n+pp)), Equal.sym(Nat, Nat.add(bn, 1n+(1n+pp)), U32.to_nat(uu), hb))),
    M1.lt_add_mono(bn, 1n, 1n+(1n+pp), {==})))

# a counter one below its bound: the next is not below it
def lt.last(
  +xx: U32,
  +uu: U32,
  +hb: {Nat.add(U32.to_nat(xx), 1n) == U32.to_nat(uu) : Nat}
) -> {U32.is_lt((xx + 1 : U32), uu) == False{} : Bool}:
  +bn = U32.to_nat(xx)
  +e1 = {inc.nat(xx, uu, 0n, hb) : {U32.to_nat((xx + 1 : U32)) == Nat.add(bn, 1n) : Nat}}
  Equal.trans(Bool, U32.is_lt((xx + 1 : U32), uu), Nat.is_lt(U32.to_nat((xx + 1 : U32)), U32.to_nat(uu)), False{},
    M5.u32_lt((xx + 1 : U32), uu), Equal.trans(Bool, Nat.is_lt(U32.to_nat((xx + 1 : U32)), U32.to_nat(uu)),
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
    M1.ras.add_assoc(bn, 1n, 1n+pp), hb))

# the last of kk + 1 data units counted from 0 is one below their count
def last.nat(
  +kk: Nat,
  +uu: U32,
  +hs: {1n+kk == U32.to_nat(uu) : Nat}
) -> {Nat.add(U32.to_nat(Laws.jpg.idx(kk, 0)), 1n) == U32.to_nat(uu) : Nat}:
  +hle = {Equal.trans(Bool, Nat.is_le(kk, U32.to_nat(uu)), Nat.is_le(kk, 1n+kk), True{}, Equal.cong(Nat, Bool,
    zz => Nat.is_le(kk, zz), U32.to_nat(uu), 1n+kk, Equal.sym(Nat, 1n+kk, U32.to_nat(uu), hs)), M1.lt_le(kk, 1n+kk,
    lt.succ(kk))) : {Nat.is_le(kk, U32.to_nat(uu)) == True{} : Bool}}
  +ei = {idx.nat(kk, 0, uu, hle) : {U32.to_nat(Laws.jpg.idx(kk, 0)) == kk : Nat}}
  Equal.trans(Nat, Nat.add(U32.to_nat(Laws.jpg.idx(kk, 0)), 1n), Nat.add(kk, 1n), U32.to_nat(uu),
    Equal.cong(Nat, Nat, zz => Nat.add(zz, 1n), U32.to_nat(Laws.jpg.idx(kk, 0)), kk, ei), Equal.trans(Nat,
    Nat.add(kk, 1n), 1n+Nat.add(kk, 0n), U32.to_nat(uu), M1.ras.add_succ(kk, 0n), Equal.trans(Nat, 1n+Nat.add(kk, 0n),
    1n+kk, U32.to_nat(uu), Equal.cong(Nat, Nat, zz => 1n+zz, Nat.add(kk, 0n), kk, M1.ras.add_zero(kk)), hs)))

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
      Empty.absurd({False{} == True{} : Bool}, M1.false_true(Equal.trans(Bool, False{}, Laws.jpg.units.ok(ll, comp,
        sids, ids, hs, vs, False{}), True{}, Equal.sym(Bool, Laws.jpg.units.ok(ll, comp, sids, ids, hs, vs, False{}),
        False{}, uok.false(ll, comp, sids, ids, hs, vs)), hh)))

# the length of two lists of positions
def jfin.len.app(
  xs: List<&2, Jpeg.Ctrl>,
  -ys: List<&2, Jpeg.Ctrl>
) -> {List.length(&2, Jpeg.Ctrl, List.append(&2, Jpeg.Ctrl, xs, ys)) == Nat.add(List.length(&2, Jpeg.Ctrl, xs),
  List.length(&2, Jpeg.Ctrl, ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case _hd <> tl:
      Equal.cong(Nat, Nat, zz => 1n+zz, List.length(&2, Jpeg.Ctrl, List.append(&2, Jpeg.Ctrl, tl, ys)),
        Nat.add(List.length(&2, Jpeg.Ctrl, tl), List.length(&2, Jpeg.Ctrl, ys)), jfin.len.app(tl, ys))

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
  {M1.tr(Nat.add(List.length(&2, Jpeg.Ctrl, ll), kk), cc, fr, sc, ri) == List.append(&2, Jpeg.Ctrl, ll, M1.tr(kk, ee,
      fr, sc,
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
  +t2 = {M1.tr(kk, c2, fr, sc, ri) : List<&2, Jpeg.Ctrl>}
  Equal.trans(List<&2, Jpeg.Ctrl>, M1.tr(Nat.add(List.length(&2, Jpeg.Ctrl, List.append(&2, Jpeg.Ctrl, l1, l2)), kk),
      c0,
    fr, sc, ri), M1.tr(Nat.add(n1, Nat.add(n2, kk)), c0, fr, sc, ri), List.append(&2, Jpeg.Ctrl, List.append(&2,
    Jpeg.Ctrl, l1, l2), t2), Equal.cong(Nat, List<&2, Jpeg.Ctrl>, zz => M1.tr(zz, c0, fr, sc, ri),
    Nat.add(List.length(&2, Jpeg.Ctrl, List.append(&2, Jpeg.Ctrl, l1, l2)), kk), Nat.add(n1, Nat.add(n2, kk)),
    Equal.trans(Nat, Nat.add(List.length(&2, Jpeg.Ctrl, List.append(&2, Jpeg.Ctrl, l1, l2)), kk),
    Nat.add(Nat.add(n1, n2), kk), Nat.add(n1, Nat.add(n2, kk)), Equal.cong(Nat, Nat, zz => Nat.add(zz, kk),
    List.length(&2, Jpeg.Ctrl, List.append(&2, Jpeg.Ctrl, l1, l2)), Nat.add(n1, n2), jfin.len.app(l1, l2)),
    M1.ras.add_assoc(n1, n2, kk))), Equal.trans(List<&2, Jpeg.Ctrl>, M1.tr(Nat.add(n1, Nat.add(n2, kk)), c0, fr, sc,
        ri),
    List.append(&2, Jpeg.Ctrl, l1, M1.tr(Nat.add(n2, kk), c1, fr, sc, ri)), List.append(&2, Jpeg.Ctrl, List.append(&2,
    Jpeg.Ctrl, l1, l2), t2), h1, Equal.trans(List<&2, Jpeg.Ctrl>, List.append(&2, Jpeg.Ctrl, l1, M1.tr(Nat.add(n2, kk),
        c1,
    fr, sc, ri)), List.append(&2, Jpeg.Ctrl, l1, List.append(&2, Jpeg.Ctrl, l2, t2)), List.append(&2, Jpeg.Ctrl,
    List.append(&2, Jpeg.Ctrl, l1, l2), t2), Equal.cong(List<&2, Jpeg.Ctrl>, List<&2, Jpeg.Ctrl>,
    zz => List.append(&2, Jpeg.Ctrl, l1, zz), M1.tr(Nat.add(n2, kk), c1, fr, sc, ri), List.append(&2, Jpeg.Ctrl, l2,
        t2),
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
  M1.nxt(Jpeg.Ctrl{comp, Laws.jpg.idx(ll, bi), mx, my, mcu, 0}, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax},
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
      +en = {Equal.trans(Jpeg.Ctrl, M1.nxt(cc, fr, sc, ri), bi.res(U32.is_lt((bi + 1 : U32), Laws.jpg.units(comp, sids,
        ids, hs, vs)),
        U32.is_lt((comp + 1 : U32), ns), U32.is_lt((mx + 1 : U32), Jpeg.decode.ceil(ww,
          (hmax * 8 : U32))), comp, bi, mx, my, mcu), c1,
        nxt.eq(comp, bi, mx, my, mcu, 0, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, ns, sids, td, ta, ss, se, ah,
          ri), Equal.cong(Bool, Jpeg.Ctrl, mb => bi.res(mb,
        U32.is_lt((comp + 1 : U32), ns), U32.is_lt((mx + 1 : U32), Jpeg.decode.ceil(ww,
          (hmax * 8 : U32))), comp, bi, mx, my, mcu),
        U32.is_lt((bi + 1 : U32), Laws.jpg.units(comp, sids, ids, hs, vs)), True{}, lt.more(bi, Laws.jpg.units(comp,
          sids, ids, hs, vs), pp, hb))) : {M1.nxt(cc, fr, sc, ri) == c1 : Jpeg.Ctrl}}
      Equal.trans(List<&2, Jpeg.Ctrl>, cc <> M1.tr(nn, M1.nxt(cc, fr, sc, ri), fr, sc, ri), cc <> M1.tr(nn, c1, fr, sc,
          ri),
        cc <> List.append(&2, Jpeg.Ctrl, Laws.jpg.o.units(1n+pp, comp, (bi + 1 : U32), mx, my, mcu), M1.tr(kk,
        M1.nxt(Jpeg.Ctrl{comp, Laws.jpg.idx(pp, (bi + 1 : U32)), mx, my, mcu, 0}, fr, sc, ri), fr, sc, ri)),
        Equal.cong(Jpeg.Ctrl, List<&2, Jpeg.Ctrl>, dd => {cc <> M1.tr(nn, dd, fr, sc, ri) : List<&2, Jpeg.Ctrl>},
          M1.nxt(cc, fr, sc, ri), c1, en),
        Equal.cong(List<&2, Jpeg.Ctrl>, List<&2, Jpeg.Ctrl>, zz => {cc <> zz : List<&2, Jpeg.Ctrl>}, M1.tr(nn, c1, fr,
          sc, ri), List.append(&2, Jpeg.Ctrl,
        Laws.jpg.o.units(1n+pp, comp, (bi + 1 : U32), mx, my, mcu), M1.tr(kk, M1.nxt(Jpeg.Ctrl{comp, Laws.jpg.idx(pp,
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
) -> {M1.nxt(Jpeg.Ctrl{comp, Laws.jpg.idx(kk, 0), mx, my, mcu, 0}, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax},
  Jpeg.Scan{ns, sids, td, ta, ss, se, ah}, ri) ==
  Jpeg.Ctrl{(comp + 1 : U32), 0, mx, my, mcu, 0} : Jpeg.Ctrl}:
  +bl = Laws.jpg.idx(kk, 0)
  Equal.trans(Jpeg.Ctrl, M1.nxt(Jpeg.Ctrl{comp, bl, mx, my, mcu, 0}, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax,
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
) -> {M1.nxt(Jpeg.Ctrl{comp, Laws.jpg.idx(kk, 0), mx, my, mcu, 0}, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax},
  Jpeg.Scan{ns, sids, td, ta, ss, se, ah}, ri) ==
  mx.res(U32.is_lt((mx + 1 : U32), Jpeg.decode.ceil(ww, (hmax * 8 : U32))), (mcu + 1 : U32), (mx + 1 : U32),
    my) : Jpeg.Ctrl}:
  +bl = Laws.jpg.idx(kk, 0)
  Equal.trans(Jpeg.Ctrl, M1.nxt(Jpeg.Ctrl{comp, bl, mx, my, mcu, 0}, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax,
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
  {M1.nxt(Jpeg.Ctrl{comp, Laws.jpg.idx(jfin.npred(U32.to_nat(Laws.jpg.units(comp, sids, ids, hs, vs))), 0), mx, my,
      mcu, 0},
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
  +k1 = jfin.npred(U32.to_nat(Laws.jpg.units(comp, sids, ids, hs, vs)))
  +es = {pos.nat(Laws.jpg.units(comp, sids, ids, hs, vs), hpos) : {1n+k1 == U32.to_nat(Laws.jpg.units(comp, sids,
    ids, hs, vs)) : Nat}}
  %es : Run(Laws.jpg.o.units(_, comp, 0, mx, my, mcu), Jpeg.Ctrl{comp, 0, mx, my, mcu, 0}, ee, Jpeg.Frame{ww, hh, nf,
    ids, hs, vs, tq, hmax, vmax}, Jpeg.Scan{ns, sids, td, ta, ss, se, ah}, ri,
    kk)
  run.end(Laws.jpg.o.units(1n+k1, comp, 0, mx, my, mcu), Jpeg.Ctrl{comp, 0, mx, my, mcu, 0},
    M1.nxt(Jpeg.Ctrl{comp, Laws.jpg.idx(k1, 0), mx, my, mcu, 0}, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax},
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
      +hpos = {M1.and_right(ok, U32.is_lt(0, Laws.jpg.units(comp, sids, ids, hs, vs)), uok.acc(0n,
        (comp + 1 : U32), sids, ids, hs, vs, Bool.and(ok,
        U32.is_lt(0, Laws.jpg.units(comp, sids, ids, hs,
          vs))), hu)) : {U32.is_lt(0, Laws.jpg.units(comp, sids, ids, hs, vs)) == True{} : Bool}}
      +k1 = jfin.npred(U32.to_nat(Laws.jpg.units(comp, sids, ids, hs, vs)))
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
      +hpos = {M1.and_right(ok, U32.is_lt(0, Laws.jpg.units(comp, sids, ids, hs, vs)), uok.acc(1n+pp,
        (comp + 1 : U32), sids, ids, hs, vs, Bool.and(ok,
        U32.is_lt(0, Laws.jpg.units(comp, sids, ids, hs,
          vs))), hu)) : {U32.is_lt(0, Laws.jpg.units(comp, sids, ids, hs, vs)) == True{} : Bool}}
      +k1 = jfin.npred(U32.to_nat(Laws.jpg.units(comp, sids, ids, hs, vs)))
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
  +n1 = jfin.npred(U32.to_nat(ns))
  +hn = {pos.nat(ns, h_ns) : {1n+n1 == U32.to_nat(ns) : Nat}}
  +c0 = {Jpeg.Ctrl{0, 0, 0, 0, 0, 0} : Jpeg.Ctrl}
  +hu = {Equal.trans(Bool, Laws.jpg.units.ok(1n+n1, 0, sids, ids, hs, vs, True{}), Laws.jpg.units.ok(U32.to_nat(ns),
    0, sids, ids, hs, vs, True{}), True{}, Equal.cong(Nat, Bool, nn => Laws.jpg.units.ok(nn, 0, sids, ids, hs, vs,
    True{}), 1n+n1, U32.to_nat(ns), hn), h_units) : {Laws.jpg.units.ok(1n+n1, 0, sids, ids, hs, vs, True{}) == True{} :
    Bool}}
  Equal.trans(List<&2, Jpeg.Ctrl>, Laws.jpg.trace(ln, Jpeg.Ctrl{0, 0, 0, 0, 0, rst}, fr, sc, ri), M1.tr(ln,
    Jpeg.Ctrl{0, 0, 0, 0, 0, rst}, fr, sc, ri), ll, trace.tr(ln, Jpeg.Ctrl{0, 0, 0, 0, 0,
      rst}, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, ns, sids, td, ta, ss, se, ah, ri),
    Equal.trans(List<&2, Jpeg.Ctrl>, M1.tr(ln, Jpeg.Ctrl{0, 0, 0, 0, 0, rst}, fr, sc, ri), M1.tr(ln, c0, fr, sc, ri),
        ll,
    tr.pos(ln, Jpeg.Ctrl{0, 0, 0, 0, 0, rst}, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, ns, sids, td, ta, ss, se, ah,
      ri), Equal.trans(List<&2, Jpeg.Ctrl>, M1.tr(ln, c0, fr, sc, ri),
    M1.tr(Nat.add(ln, 0n), c0, fr, sc, ri), ll, Equal.cong(Nat, List<&2, Jpeg.Ctrl>, nn => M1.tr(nn, c0, fr, sc, ri),
        ln,
    Nat.add(ln, 0n), Equal.sym(Nat, Nat.add(ln, 0n), ln, M1.ras.add_zero(ln))), Equal.trans(List<&2, Jpeg.Ctrl>,
    M1.tr(Nat.add(ln, 0n), c0, fr, sc, ri), List.append(&2, Jpeg.Ctrl, ll, []), ll, run.rows(U32.to_nat(mh), 0, 0, ww,
      hh, nf, ids, hs, vs, tq, hmax, vmax, ns, sids, td, ta, ss, se, ah, ri,
    0n, n1, hn, hu, jfin.npred(U32.to_nat(Jpeg.decode.ceil(ww, (hmax * 8 : U32)))), pos.nat(Jpeg.decode.ceil(ww,
      (hmax * 8 : U32)), h_mw)), app.nil(ll)))))

# ---- the decoder's block count (laws/JpegPlacesComponentSamples.bend) ----

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
        Jpeg.Ctrl, l1), List.length(&2, Jpeg.Ctrl, l2)), Nat.add(un, s2), jfin.len.app(l1, l2), Equal.trans(Nat,
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
        Jpeg.Ctrl, l1), List.length(&2, Jpeg.Ctrl, l2)), Nat.add(uu, Nat.mul(pp, uu)), jfin.len.app(l1, l2),
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
        Jpeg.Ctrl, l1), List.length(&2, Jpeg.Ctrl, l2)), Nat.add(ru, Nat.mul(pp, ru)), jfin.len.app(l1, l2),
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
        cc)), Nat.add(Nat.mul(bb, cc), Nat.mul(pp, Nat.mul(bb, cc))), M1.mul_add(bb, Nat.mul(pp, bb), cc),
        Equal.cong(Nat, Nat, xx => Nat.add(Nat.mul(bb, cc), xx), Nat.mul(Nat.mul(pp, bb), cc), Nat.mul(pp,
        Nat.mul(bb, cc)), mul.assoc(pp, bb, cc)))

# x is at most x times a positive number
def le.mulr(
  +xx: Nat,
  +uu: Nat,
  +hu: {1n+jfin.npred(uu) == uu : Nat}
) -> {Nat.is_le(xx, Nat.mul(xx, uu)) == True{} : Bool}:
  +u1 = jfin.npred(uu)
  Equal.trans(Bool, Nat.is_le(xx, Nat.mul(xx, uu)), Nat.is_le(xx, Nat.add(xx, Nat.mul(xx, u1))), True{},
    Equal.cong(Nat, Bool, nn => Nat.is_le(xx, nn), Nat.mul(xx, uu), Nat.add(xx, Nat.mul(xx, u1)), Equal.trans(Nat,
    Nat.mul(xx, uu), Nat.mul(xx, 1n+u1), Nat.add(xx, Nat.mul(xx, u1)), Equal.cong(Nat, Nat, nn => Nat.mul(xx, nn), uu,
    1n+u1, Equal.sym(Nat, 1n+u1, uu, hu)), M1.mul_succ(xx, u1))), M4.le_add_more(xx, xx, Nat.mul(xx, u1),
    M1.le_refl(xx)))

# the scan has at least one data unit per MCU
def usum.pos(
  +ns: U32,
  +sids: List<&2, U32>,
  +ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>,
  +h_ns: {U32.is_lt(0, ns) == True{} : Bool},
  +h_units: {Laws.jpg.units.ok(U32.to_nat(ns), 0, sids, ids, hs, vs, True{}) == True{} : Bool}
) -> {1n+jfin.npred(Laws.jpg.usum(U32.to_nat(ns), 0, sids, ids, hs, vs)) == Laws.jpg.usum(U32.to_nat(ns), 0, sids, ids,
  hs, vs) : Nat}:
  +n1 = jfin.npred(U32.to_nat(ns))
  +hn = {pos.nat(ns, h_ns) : {1n+n1 == U32.to_nat(ns) : Nat}}
  +u0 = Laws.jpg.units(0, sids, ids, hs, vs)
  +hu = {Equal.trans(Bool, Laws.jpg.units.ok(1n+n1, 0, sids, ids, hs, vs, True{}), Laws.jpg.units.ok(U32.to_nat(ns),
    0, sids, ids, hs, vs, True{}), True{}, Equal.cong(Nat, Bool, nn => Laws.jpg.units.ok(nn, 0, sids, ids, hs, vs,
    True{}), 1n+n1, U32.to_nat(ns), hn), h_units) : {Laws.jpg.units.ok(1n+n1, 0, sids, ids, hs, vs, True{}) == True{} :
    Bool}}
  +hp = {uok.acc(n1, 1, sids, ids, hs, vs, U32.is_lt(0, u0), hu) : {U32.is_lt(0, u0) == True{} : Bool}}
  +k0 = jfin.npred(U32.to_nat(u0))
  +rest = Laws.jpg.usum(n1, 1, sids, ids, hs, vs)
  succ.of(Laws.jpg.usum(U32.to_nat(ns), 0, sids, ids, hs, vs), Equal.trans(Bool, Nat.is_lt(0n,
    Laws.jpg.usum(U32.to_nat(ns), 0, sids, ids, hs, vs)), Nat.is_lt(0n, Nat.add(U32.to_nat(u0), rest)), True{},
    Equal.cong(Nat, Bool, nn => Nat.is_lt(0n, Laws.jpg.usum(nn, 0, sids, ids, hs, vs)), U32.to_nat(ns), 1n+n1,
    Equal.sym(Nat, 1n+n1, U32.to_nat(ns), hn)), Equal.cong(Nat, Bool, nn => Nat.is_lt(0n, Nat.add(nn, rest)),
    U32.to_nat(u0), 1n+k0, Equal.sym(Nat, 1n+k0, U32.to_nat(u0), pos.nat(u0, hp)))))

# the scan's data units per MCU are one more than their predecessor
def usum.Pos(+ns: U32, +sids: List<&2, U32>, +ids: List<&2, U32>, +hs: List<&2, U32>, +vs: List<&2, U32>) -> Type:
  {1n+jfin.npred(Laws.jpg.usum(U32.to_nat(ns), 0, sids, ids, hs, vs)) == Laws.jpg.usum(U32.to_nat(ns), 0, sids, ids,
      hs, vs)
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
  +in = {M3.u32_mul_below(mw, mh, top, M1.le_trans(Nat.mul(wn, hn), Nat.mul(Nat.mul(wn, hn), uu), U32.to_nat(top),
    le.mulr(Nat.mul(wn, hn), uu, h_pos), h_fit)) : {U32.to_nat((mw * mh : U32)) == Nat.mul(wn, hn) : Nat}}
  +eo = {Equal.trans(Nat, Nat.mul(U32.to_nat((mw * mh : U32)), U32.to_nat(bs)), Nat.mul(Nat.mul(wn, hn),
    U32.to_nat(bs)), Nat.mul(Nat.mul(wn, hn), uu), Equal.cong(Nat, Nat, nn => Nat.mul(nn, U32.to_nat(bs)),
    U32.to_nat((mw * mh : U32)), Nat.mul(wn, hn), in), Equal.cong(Nat, Nat, nn => Nat.mul(Nat.mul(wn, hn), nn),
    U32.to_nat(bs), uu, h_sum)) : {Nat.mul(U32.to_nat((mw * mh : U32)), U32.to_nat(bs)) == Nat.mul(Nat.mul(wn, hn), uu)
    : Nat}}
  +out = {M3.u32_mul_below((mw * mh : U32), bs, top, Equal.trans(Bool, Nat.is_le(Nat.mul(U32.to_nat((mw * mh : U32)),
    U32.to_nat(bs)), U32.to_nat(top)), Nat.is_le(Nat.mul(Nat.mul(wn, hn), uu), U32.to_nat(top)), True{},
    Equal.cong(Nat, Bool, nn => Nat.is_le(nn, U32.to_nat(top)), Nat.mul(U32.to_nat((mw * mh : U32)), U32.to_nat(bs)),
    Nat.mul(Nat.mul(wn, hn), uu), eo), h_fit)) : {U32.to_nat((mw * mh * bs : U32)) == Nat.mul(U32.to_nat((mw * mh :
    U32)), U32.to_nat(bs)) : Nat}}
  Equal.trans(Nat, U32.to_nat((mw * mh * bs : U32)), Nat.mul(Nat.mul(wn, hn), uu), List.length(&2, Jpeg.Ctrl,
    Laws.jpg.o.rows(hn, 0, 0, mw, ns, sids, ids, hs, vs)), Equal.trans(Nat, U32.to_nat((mw * mh * bs : U32)),
    Nat.mul(U32.to_nat((mw * mh : U32)), U32.to_nat(bs)), Nat.mul(Nat.mul(wn, hn), uu), out, eo), Equal.trans(Nat,
    Nat.mul(Nat.mul(wn, hn), uu), Nat.mul(Nat.mul(hn, wn), uu), List.length(&2, Jpeg.Ctrl, Laws.jpg.o.rows(hn, 0, 0,
    mw, ns, sids, ids, hs, vs)), Equal.cong(Nat, Nat, nn => Nat.mul(nn, uu), Nat.mul(wn, hn), Nat.mul(hn, wn),
    M1.mul_comm(wn, hn)), Equal.trans(Nat, Nat.mul(Nat.mul(hn, wn), uu), Nat.mul(hn, Nat.mul(wn, uu)), List.length(&2,
    Jpeg.Ctrl, Laws.jpg.o.rows(hn, 0, 0, mw, ns, sids, ids, hs, vs)), mul.assoc(hn, wn, uu), Equal.sym(Nat,
    List.length(&2, Jpeg.Ctrl, Laws.jpg.o.rows(hn, 0, 0, mw, ns, sids, ids, hs, vs)), Nat.mul(hn, Nat.mul(wn, uu)),
    len.rows(hn, 0, 0, mw, ns, sids, ids, hs, vs)))))

# ---- the array walks, on the tree ----

# the size walk of a tree's array hands the array back with the tree's size
def size_eq(tt: M1.Tr) -> {Array.size(U32, M1.arr(tt)) == (M1.arr(tt), M1.size(tt)) : Array<U32> & U32}:
  match tt:
    case M1.TLeaf{_xx}:
      {==}
    case M1.TNode{lo, hi}:
      ee = Equal.sym(Array<U32> & U32, Array.size(U32, M1.arr(lo)), (M1.arr(lo), M1.size(lo)), size_eq(lo))
      %ee : {Array.size.node(U32, M1.arr(hi), _) == (ANode{M1.arr(lo), M1.arr(hi)},
          U32.shl(M1.size(lo))) : Array<U32> & U32}
      {==}

# a read's tree walk, as get_eq says it: the half is the one the index falls in
def GetHalf(+tt: M1.Tr, +nn: U32, +ii: U32) -> Type:
  {Array.get.go(U32, M1.arr(tt), nn, ii, U32.is_lt(ii, U32.shr(nn))) == (M1.arr(tt), M1.get(tt, nn,
      ii)) : Array<U32> & U32}

# a read's step at a node: the half zz picks read, the other half kept
def get_if(
  +lo: M1.Tr,
  +hi: M1.Tr,
  +nn: U32,
  +ii: U32,
  zz: Bool,
  el: GetHalf(lo, U32.shr(nn), ii),
  eh: GetHalf(hi, U32.shr(nn), U32.sub(ii, U32.shr(nn)))
) -> {Array.get.go(U32, ANode{M1.arr(lo), M1.arr(hi)}, nn, ii, zz) == (ANode{M1.arr(lo), M1.arr(hi)}, Bool.pick(U32,
    zz, M1.get(lo,
  U32.shr(nn), ii), M1.get(hi, U32.shr(nn), U32.sub(ii, U32.shr(nn))))) : Array<U32> & U32}:
  match zz:
    case True{}:
      +hh = U32.shr(nn)
      sl = Equal.sym(Array<U32> & U32, Array.get.go(U32, M1.arr(lo), hh, ii, U32.is_lt(ii, U32.shr(hh))), (M1.arr(lo),
        M1.get(lo, hh, ii)), el)
      %sl : {Array.swap.lo(U32, M1.arr(hi), _) == (ANode{M1.arr(lo), M1.arr(hi)}, M1.get(lo, hh,
          ii)) : Array<U32> & U32}
      {==}
    case False{}:
      +hh = U32.shr(nn)
      +jj = U32.sub(ii, hh)
      sh = Equal.sym(Array<U32> & U32, Array.get.go(U32, M1.arr(hi), hh, jj, U32.is_lt(jj, U32.shr(hh))), (M1.arr(hi),
        M1.get(hi, hh, jj)), eh)
      %sh : {Array.swap.hi(U32, M1.arr(lo), _) == (ANode{M1.arr(lo), M1.arr(hi)}, M1.get(hi, hh,
          jj)) : Array<U32> & U32}
      {==}

# a read's tree walk hands the array back with the value the tree walk finds
def get_eq(+tt: M1.Tr, +nn: U32, +ii: U32) -> GetHalf(tt, nn, ii):
  match tt:
    case M1.TLeaf{_xx}:
      {==}
    case M1.TNode{lo, hi}:
      +hh = U32.shr(nn)
      get_if(lo, hi, nn, ii, U32.is_lt(ii, hh), get_eq(lo, hh, ii), get_eq(hi, hh, U32.sub(ii, hh)))

# a write's tree walk, as swap_eq says it: the half is the one the index falls in
def SwapHalf(+tt: M1.Tr, +nn: U32, +ii: U32, +vv: U32) -> Type:
  {Array.swap.go(U32, M1.arr(tt), nn, ii, vv, U32.is_lt(ii, U32.shr(nn))) == (M1.arr(M1.put(tt, nn, ii, vv)),
      M1.get(tt, nn, ii)) :
    Array<U32> & U32}

# a write's step at a node: the half zz picks written, the other half kept
def swap_if(
  +lo: M1.Tr,
  +hi: M1.Tr,
  +nn: U32,
  +ii: U32,
  +vv: U32,
  zz: Bool,
  el: SwapHalf(lo, U32.shr(nn), ii, vv),
  eh: SwapHalf(hi, U32.shr(nn), U32.sub(ii, U32.shr(nn)), vv)
) -> {Array.swap.go(U32, ANode{M1.arr(lo), M1.arr(hi)}, nn, ii, vv, zz) == (M1.arr(M1.put.if(zz, lo, hi, M1.put(lo,
    U32.shr(nn), ii,
  vv), M1.put(hi, U32.shr(nn), U32.sub(ii, U32.shr(nn)), vv))), Bool.pick(U32, zz, M1.get(lo, U32.shr(nn), ii), M1.get(hi,  # noqa: S002
  U32.shr(nn), U32.sub(ii, U32.shr(nn))))) : Array<U32> & U32}:
  match zz:
    case True{}:
      +hh = U32.shr(nn)
      sl = Equal.sym(Array<U32> & U32, Array.swap.go(U32, M1.arr(lo), hh, ii, vv, U32.is_lt(ii, U32.shr(hh))),
        (M1.arr(M1.put(lo, hh, ii, vv)), M1.get(lo, hh, ii)), el)
      %sl : {Array.swap.lo(U32, M1.arr(hi), _) == (ANode{M1.arr(M1.put(lo, hh, ii, vv)), M1.arr(hi)}, M1.get(lo, hh,
          ii)) :
        Array<U32> & U32}
      {==}
    case False{}:
      +hh = U32.shr(nn)
      +jj = U32.sub(ii, hh)
      sh = Equal.sym(Array<U32> & U32, Array.swap.go(U32, M1.arr(hi), hh, jj, vv, U32.is_lt(jj, U32.shr(hh))),
        (M1.arr(M1.put(hi, hh, jj, vv)), M1.get(hi, hh, jj)), eh)
      %sh : {Array.swap.hi(U32, M1.arr(lo), _) == (ANode{M1.arr(lo), M1.arr(M1.put(hi, hh, jj, vv))}, M1.get(hi, hh,
          jj)) :
        Array<U32> & U32}
      {==}

# a write's tree walk leaves the array of the tree put leaves, and hands back the value get finds
def swap_eq(+tt: M1.Tr, +nn: U32, +ii: U32, +vv: U32) -> SwapHalf(tt, nn, ii, vv):
  match tt:
    case M1.TLeaf{_xx}:
      {==}
    case M1.TNode{lo, hi}:
      +hh = U32.shr(nn)
      swap_if(lo, hi, nn, ii, vv, U32.is_lt(ii, hh), swap_eq(lo, hh, ii, vv), swap_eq(hi, hh, U32.sub(ii, hh), vv))

# Array.get of a tree's array: the array back, and the value get finds at the masked index
def get_arr(
  +tt: M1.Tr,
  +ii: U32
) -> {Array.get(U32, M1.arr(tt), ii) == (M1.arr(tt), M1.get(tt, M1.size(tt), M1.mask(ii, M1.size(tt)))) :
  Array<U32> & U32}:
  ss = Equal.sym(Array<U32> & U32, Array.size(U32, M1.arr(tt)), (M1.arr(tt), M1.size(tt)), size_eq(tt))
  %ss : {Array.get.at(U32, ii, _) == (M1.arr(tt), M1.get(tt, M1.size(tt), M1.mask(ii, M1.size(tt)))) : Array<U32> & U32}
  get_eq(tt, M1.size(tt), M1.mask(ii, M1.size(tt)))

# Array.set of a tree's array is the array of the tree set leaves
def set_arr(
  +tt: M1.Tr,
  +ii: U32,
  +vv: U32
) -> {Array.set(U32, M1.arr(tt), ii, vv) == M1.arr(M1.set(tt, ii, vv)) : Array<U32>}:
  ss = Equal.sym(Array<U32> & U32, Array.size(U32, M1.arr(tt)), (M1.arr(tt), M1.size(tt)), size_eq(tt))
  +mm = M1.mask(ii, M1.size(tt))
  sw = Equal.sym(Array<U32> & U32, Array.swap.go(U32, M1.arr(tt), M1.size(tt), mm, vv, U32.is_lt(mm,
      U32.shr(M1.size(tt)))),
    (M1.arr(M1.set(tt, ii, vv)), M1.get(tt, M1.size(tt), mm)), swap_eq(tt, M1.size(tt), mm, vv))
  %ss : {Array.set.fin(U32, Array.swap.at(U32, ii, vv, _)) == M1.arr(M1.set(tt, ii, vv)) : Array<U32>}
  %sw : {Array.set.fin(U32, _) == M1.arr(M1.set(tt, ii, vv)) : Array<U32>}
  {==}

# a write at a node keeps the size, given that a write to the low half does
def size_put.if(
  zz: Bool,
  +lo: M1.Tr,
  +hi: M1.Tr,
  +pl: M1.Tr,
  +ph: M1.Tr,
  +el: {M1.size(pl) == M1.size(lo) : U32}
) -> {M1.size(M1.put.if(zz, lo, hi, pl, ph)) == U32.shl(M1.size(lo)) : U32}:
  match zz:
    case True{}:
      Equal.cong(U32, U32, xx => U32.shl(xx), M1.size(pl), M1.size(lo), el)
    case False{}:
      {==}

# a write keeps the size
def size_put(+tt: M1.Tr, +nn: U32, +ii: U32, +vv: U32) -> {M1.size(M1.put(tt, nn, ii, vv)) == M1.size(tt) : U32}:
  match tt:
    case M1.TLeaf{_xx}:
      {==}
    case M1.TNode{lo, hi}:
      +hh = U32.shr(nn)
      size_put.if(U32.is_lt(ii, hh), lo, hi, M1.put(lo, hh, ii, vv), M1.put(hi, hh, U32.sub(ii, hh), vv),
        size_put(lo, hh, ii, vv))

# ---- a read after a write ----

# at a node: a read at the index just written finds the value, given that it does in each half
def gps_if(
  zz: Bool,
  +lo: M1.Tr,
  +hi: M1.Tr,
  +nn: U32,
  +ii: U32,
  +vv: U32,
  +ez: {U32.is_lt(ii, U32.shr(nn)) == zz : Bool},
  +el: {M1.get(M1.put(lo, U32.shr(nn), ii, vv), U32.shr(nn), ii) == vv : U32},
  +eh: {M1.get(M1.put(hi, U32.shr(nn), U32.sub(ii, U32.shr(nn)), vv), U32.shr(nn), U32.sub(ii, U32.shr(nn))) == vv : U32}  # noqa: S002
) -> {M1.get(M1.put.if(zz, lo, hi, M1.put(lo, U32.shr(nn), ii, vv), M1.put(hi, U32.shr(nn), U32.sub(ii, U32.shr(nn)),
    vv)), nn,
  ii) == vv : U32}:
  match zz:
    case True{}:
      +hh = U32.shr(nn)
      +ih = U32.sub(ii, hh)
      se = Equal.sym(Bool, U32.is_lt(ii, hh), True{}, ez)
      %se : {Bool.pick(U32, _, M1.get(M1.put(lo, hh, ii, vv), hh, ii), M1.get(hi, hh, ih)) == vv : U32}
      el
    case False{}:
      +hh = U32.shr(nn)
      +ih = U32.sub(ii, hh)
      se = Equal.sym(Bool, U32.is_lt(ii, hh), False{}, ez)
      %se : {Bool.pick(U32, _, M1.get(lo, hh, ii), M1.get(M1.put(hi, hh, ih, vv), hh, ih)) == vv : U32}
      eh

# a read at the index just written finds the value, in any tree
def get_put_same(+tt: M1.Tr, +nn: U32, +ii: U32, +vv: U32) -> {M1.get(M1.put(tt, nn, ii, vv), nn, ii) == vv : U32}:
  match tt:
    case M1.TLeaf{_xx}:
      {==}
    case M1.TNode{lo, hi}:
      +hh = U32.shr(nn)
      gps_if(U32.is_lt(ii, hh), lo, hi, nn, ii, vv, {==}, get_put_same(lo, hh, ii, vv), get_put_same(hi, hh,
        U32.sub(ii, hh), vv))

# a perfect binary tree of 2^d leaves
def pf(+dd: Nat, +tt: M1.Tr) -> Bool:
  match dd tt:
    case 0n M1.TLeaf{_xx}:
      True{}
    case 0n M1.TNode{_lo, _hi}:
      False{}
    case 1n+_ee M1.TLeaf{_xx}:
      False{}
    case 1n+ee M1.TNode{lo, hi}:
      +pl = pf(ee, lo)
      +ph = pf(ee, hi)
      Bool.and(pl, ph)

# the right-hand side of get_put at a node, for walks going a and b at the root
def gp.rhs(
  +aa: Bool,
  +bb: Bool,
  +ee: Nat,
  +lo: M1.Tr,
  +hi: M1.Tr,
  +hh: U32,
  +ii: U32,
  +jj: U32,
  +vv: U32
) -> U32:
  +gl = M1.get(lo, hh, jj)
  +gh = M1.get(hi, hh, U32.sub(jj, hh))
  M1.after(M1.same.if(aa, bb, M1.same(ee, hh, Bool.pick(U32, aa, ii, U32.sub(ii, hh)), Bool.pick(U32, bb, jj,
      U32.sub(jj,
    hh)))), vv, Bool.pick(U32, bb, gl, gh))

# a read after a write in a half, as get_put says it
def GpHalf(+tt: M1.Tr, +ee: Nat, +hh: U32, +ii: U32, +jj: U32, +vv: U32) -> Type:
  {M1.get(M1.put(tt, hh, ii, vv), hh, jj) == M1.after(M1.same(ee, hh, ii, jj), vv, M1.get(tt, hh, jj)) : U32}

# at a node of a perfect tree: a read after a write, given the halves
def gp_if(
  zi: Bool,
  zj: Bool,
  +ee: Nat,
  +lo: M1.Tr,
  +hi: M1.Tr,
  +nn: U32,
  +ii: U32,
  +jj: U32,
  +vv: U32,
  +ezi: {U32.is_lt(ii, U32.shr(nn)) == zi : Bool},
  +ezj: {U32.is_lt(jj, U32.shr(nn)) == zj : Bool},
  el: GpHalf(lo, ee, U32.shr(nn), ii, jj, vv),
  eh: GpHalf(hi, ee, U32.shr(nn), U32.sub(ii, U32.shr(nn)), U32.sub(jj, U32.shr(nn)), vv)
) -> {M1.get(M1.put.if(zi, lo, hi, M1.put(lo, U32.shr(nn), ii, vv), M1.put(hi, U32.shr(nn), U32.sub(ii, U32.shr(nn)),
    vv)), nn,
  jj) == gp.rhs(U32.is_lt(ii, U32.shr(nn)), U32.is_lt(jj, U32.shr(nn)), ee, lo, hi, U32.shr(nn), ii, jj, vv) : U32}:
  match zi zj:
    case True{} True{}:
      +hh = U32.shr(nn)
      +sj = U32.sub(jj, hh)
      +pl = M1.put(lo, hh, ii, vv)
      si1 = Equal.sym(Bool, U32.is_lt(ii, hh), True{}, ezi)
      sj1 = Equal.sym(Bool, U32.is_lt(jj, hh), True{}, ezj)
      %si1 : {M1.get(M1.TNode{pl, hi}, nn, jj) == gp.rhs(_, U32.is_lt(jj, hh), ee, lo, hi, hh, ii, jj, vv) : U32}
      %sj1 : {Bool.pick(U32, _, M1.get(pl, hh, jj), M1.get(hi, hh, sj)) == gp.rhs(True{}, _, ee, lo, hi, hh,
        ii, jj, vv) : U32}
      el
    case True{} False{}:
      +hh = U32.shr(nn)
      +sj = U32.sub(jj, hh)
      +pl = M1.put(lo, hh, ii, vv)
      si1 = Equal.sym(Bool, U32.is_lt(ii, hh), True{}, ezi)
      sj1 = Equal.sym(Bool, U32.is_lt(jj, hh), False{}, ezj)
      %si1 : {M1.get(M1.TNode{pl, hi}, nn, jj) == gp.rhs(_, U32.is_lt(jj, hh), ee, lo, hi, hh, ii, jj, vv) : U32}
      %sj1 : {Bool.pick(U32, _, M1.get(pl, hh, jj), M1.get(hi, hh, sj)) == gp.rhs(True{}, _, ee, lo, hi, hh,
        ii, jj, vv) : U32}
      {==}
    case False{} True{}:
      +hh = U32.shr(nn)
      +si = U32.sub(ii, hh)
      +sj = U32.sub(jj, hh)
      +ph = M1.put(hi, hh, si, vv)
      si1 = Equal.sym(Bool, U32.is_lt(ii, hh), False{}, ezi)
      sj1 = Equal.sym(Bool, U32.is_lt(jj, hh), True{}, ezj)
      %si1 : {M1.get(M1.TNode{lo, ph}, nn, jj) == gp.rhs(_, U32.is_lt(jj, hh), ee, lo, hi, hh, ii, jj, vv) : U32}
      %sj1 : {Bool.pick(U32, _, M1.get(lo, hh, jj), M1.get(ph, hh, sj)) == gp.rhs(False{}, _, ee, lo, hi, hh,
        ii, jj, vv) : U32}
      {==}
    case False{} False{}:
      +hh = U32.shr(nn)
      +si = U32.sub(ii, hh)
      +sj = U32.sub(jj, hh)
      +ph = M1.put(hi, hh, si, vv)
      si1 = Equal.sym(Bool, U32.is_lt(ii, hh), False{}, ezi)
      sj1 = Equal.sym(Bool, U32.is_lt(jj, hh), False{}, ezj)
      %si1 : {M1.get(M1.TNode{lo, ph}, nn, jj) == gp.rhs(_, U32.is_lt(jj, hh), ee, lo, hi, hh, ii, jj, vv) : U32}
      %sj1 : {Bool.pick(U32, _, M1.get(lo, hh, jj), M1.get(ph, hh, sj)) == gp.rhs(False{}, _, ee, lo, hi, hh,
        ii, jj, vv) : U32}
      eh

# a read after a write to a perfect tree finds the written value when both walks end at one leaf, and what it
# found before otherwise
def get_put(
  +dd: Nat,
  +tt: M1.Tr,
  +nn: U32,
  +ii: U32,
  +jj: U32,
  +vv: U32,
  +hp: {pf(dd, tt) == True{} : Bool}
) -> {M1.get(M1.put(tt, nn, ii, vv), nn, jj) == M1.after(M1.same(dd, nn, ii, jj), vv, M1.get(tt, nn, jj)) : U32}:
  match dd tt:
    case 0n M1.TLeaf{_xx}:
      {==}
    case 1n+ee M1.TLeaf{+xx}:
      Empty.absurd({M1.get(M1.put(M1.TLeaf{xx}, nn, ii, vv), nn, jj) == M1.after(M1.same(1n+ee, nn, ii, jj), vv,
          xx) : U32},
        M1.false_true(hp))
    case 0n M1.TNode{lo, hi}:
      Empty.absurd({M1.get(M1.put(M1.TNode{lo, hi}, nn, ii, vv), nn, jj) == M1.after(True{}, vv, M1.get(M1.TNode{lo,
          hi}, nn, jj)) :
        U32}, M1.false_true(hp))
    case 1n+ee M1.TNode{lo, hi}:
      +hh = U32.shr(nn)
      +ha = M1.and_left(pf(ee, lo), pf(ee, hi), hp)
      +hb = M1.and_right(pf(ee, lo), pf(ee, hi), hp)
      gp_if(U32.is_lt(ii, hh), U32.is_lt(jj, hh), ee, lo, hi, nn, ii, jj, vv, {==}, {==}, get_put(ee, lo, hh, ii, jj,
        vv, ha), get_put(ee, hi, hh, U32.sub(ii, hh), U32.sub(jj, hh), vv, hb))

# at a node of depth one more than ee: a write keeps the tree perfect, given that a write to the low half does
def pfp_if(
  zz: Bool,
  +ee: Nat,
  +lo: M1.Tr,
  +hi: M1.Tr,
  +pl: M1.Tr,
  +ph: M1.Tr,
  +el: {pf(ee, pl) == pf(ee, lo) : Bool},
  +eh: {pf(ee, ph) == pf(ee, hi) : Bool}
) -> {pf(1n+ee, M1.put.if(zz, lo, hi, pl, ph)) == pf(1n+ee, M1.TNode{lo, hi}) : Bool}:
  match zz:
    case True{}:
      Equal.cong(Bool, Bool, bb => Bool.and(bb, pf(ee, hi)), pf(ee, pl), pf(ee, lo), el)
    case False{}:
      Equal.cong(Bool, Bool, bb => Bool.and(pf(ee, lo), bb), pf(ee, ph), pf(ee, hi), eh)

# at a node of depth zero: a write leaves it not perfect, as it was
def pfp_zero(
  zz: Bool,
  +lo: M1.Tr,
  +hi: M1.Tr,
  +pl: M1.Tr,
  +ph: M1.Tr
) -> {pf(0n, M1.put.if(zz, lo, hi, pl, ph)) == False{} : Bool}:
  match zz:
    case True{}:
      {==}
    case False{}:
      {==}

# a write keeps a tree perfect, and a tree that is not stays not
def pf_put(+dd: Nat, +tt: M1.Tr, +nn: U32, +ii: U32, +vv: U32) -> {pf(dd, M1.put(tt, nn, ii, vv)) == pf(dd, tt) : Bool}:
  match dd tt:
    case 0n M1.TLeaf{_xx}:
      {==}
    case 1n+_ee M1.TLeaf{_xx}:
      {==}
    case 0n M1.TNode{lo, hi}:
      +hh = U32.shr(nn)
      pfp_zero(U32.is_lt(ii, hh), lo, hi, M1.put(lo, hh, ii, vv), M1.put(hi, hh, U32.sub(ii, hh), vv))
    case 1n+ee M1.TNode{lo, hi}:
      +hh = U32.shr(nn)
      pfp_if(U32.is_lt(ii, hh), ee, lo, hi, M1.put(lo, hh, ii, vv), M1.put(hi, hh, U32.sub(ii, hh), vv), pf_put(ee, lo,
          hh,
        ii, vv), pf_put(ee, hi, hh, U32.sub(ii, hh), vv))

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
      Empty.absurd({WNil{} == WNil{} : Word(0n)}, M1.false_true(hh))
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
      Empty.absurd({WNil{} == WNil{} : Word(0n)}, M1.false_true(hh))
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
      Empty.absurd({WNil{} == WNil{} : Word(0n)}, M1.false_true(hh))
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
      Empty.absurd({0n == Nat.pow(2n, ee) : Nat}, M1.false_true(Equal.trans(Bool, False{}, Nat.is_lt(ee, 0n),
        True{}, M1.lt_zero_false(ee), hh)))
    case 1n+qq:
      match ee:
        case 0n:
          Equal.cong(Nat, Nat, xx => 1n+Nat.double(xx), Word.to_nat(qq, Word.zero(qq)), 0n, M3.word_zero_nat(qq))
        case 1n+ff:
          Equal.trans(Nat, Nat.double(Word.to_nat(qq, sbit(qq, ff))), Nat.double(Nat.pow(2n, ff)), Nat.pow(2n, 1n+ff),
            Equal.cong(Nat, Nat, xx => Nat.double(xx), Word.to_nat(qq, sbit(qq, ff)), Nat.pow(2n, ff), sbit_nat(qq,
            ff, hh)), Equal.sym(Nat, Nat.pow(2n, 1n+ff), Nat.double(Nat.pow(2n, ff)), M1.pow2_succ(ff)))

# the size of a perfect tree of 2^d leaves, d below 32, is the U32 of bit d
def size_bits(
  +dd: Nat,
  +tt: M1.Tr,
  +hp: {pf(dd, tt) == True{} : Bool},
  +hd: {Nat.is_lt(dd, 32n) == True{} : Bool}
) -> {M1.size(tt) == U32{sbit(32n, dd)} : U32}:
  match dd tt:
    case 0n M1.TLeaf{_xx}:
      {==}
    case 1n+ee M1.TLeaf{+xx}:
      Empty.absurd({M1.size(M1.TLeaf{xx}) == U32{sbit(32n, 1n+ee)} : U32}, M1.false_true(hp))
    case 0n M1.TNode{lo, hi}:
      Empty.absurd({M1.size(M1.TNode{lo, hi}) == U32{sbit(32n, 0n)} : U32}, M1.false_true(hp))
    case 1n+ee M1.TNode{lo, _hi}:
      +he = {M1.lt_le_trans(ee, 31n, 32n, hd, M4.le_succ(31n)) : {Nat.is_lt(ee, 32n) == True{} : Bool}}
      +ih = size_bits(ee, lo, M1.and_left(pf(ee, lo), pf(ee, _hi), hp), he)
      Equal.trans(U32, U32.shl(M1.size(lo)), U32.shl(U32{sbit(32n, ee)}), U32{sbit(32n, 1n+ee)}, Equal.cong(U32, U32,
        uu => U32.shl(uu), M1.size(lo), U32{sbit(32n, ee)}, ih), Equal.cong(Word(32n), U32, ww => U32{ww},
        Word.shl(32n, sbit(32n, ee)), sbit(32n, 1n+ee), shl_sbit(32n, ee, hd)))

# the size of a perfect tree of 2^d leaves, d below 32, is 2^d
def size_nat(
  +dd: Nat,
  +tt: M1.Tr,
  +hp: {pf(dd, tt) == True{} : Bool},
  +hd: {Nat.is_lt(dd, 32n) == True{} : Bool}
) -> {U32.to_nat(M1.size(tt)) == Nat.pow(2n, dd) : Nat}:
  Equal.trans(Nat, U32.to_nat(M1.size(tt)), U32.to_nat(U32{sbit(32n, dd)}), Nat.pow(2n, dd), Equal.cong(U32, Nat,
    uu => U32.to_nat(uu), M1.size(tt), U32{sbit(32n, dd)}, size_bits(dd, tt, hp, hd)), sbit_nat(32n, dd, hd))

# a successor is not zero
def succ_ne(-xx: Nat, ee: {1n+xx == 0n : Nat}) -> Empty:
  M1.false_true(Equal.cong(Nat, Bool, nn => Nat.is_eq(nn, 0n), 1n+xx, 0n, ee))

# successors equal have equal predecessors
def pln.succ_inj(-xx: Nat, -yy: Nat, ee: {1n+xx == 1n+yy : Nat}) -> {xx == yy : Nat}:
  Equal.cong(Nat, Nat, nn => M1.pred(nn), 1n+xx, 1n+yy, ee)

# an odd number is not an even one
def odd_even(+xx: Nat, +yy: Nat, ee: {1n+Nat.double(xx) == Nat.double(yy) : Nat}) -> Empty:
  match xx yy:
    case 0n 0n:
      succ_ne(0n, ee)
    case 0n 1n+qq:
      succ_ne(Nat.double(qq), Equal.sym(Nat, 0n, 1n+Nat.double(qq), pln.succ_inj(0n, 1n+Nat.double(qq), ee)))
    case 1n+pp 0n:
      succ_ne(2n+Nat.double(pp), ee)
    case 1n+pp 1n+qq:
      odd_even(pp, qq, pln.succ_inj(1n+Nat.double(pp), Nat.double(qq), pln.succ_inj(2n+Nat.double(pp),
          1n+Nat.double(qq), ee)))

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
      Equal.cong(Nat, Nat, nn => 1n+nn, pp, qq, dbl_inj(pp, qq, pln.succ_inj(Nat.double(pp), Nat.double(qq),
        pln.succ_inj(1n+Nat.double(pp), 1n+Nat.double(qq), ee))))

# a number below one is zero
def lt1_zero(+xx: Nat, hh: {Nat.is_lt(xx, 1n) == True{} : Bool}) -> {xx == 0n : Nat}:
  match xx:
    case 0n:
      {==}
    case 1n+pp:
      Empty.absurd({1n+pp == 0n : Nat}, M1.false_true(Equal.trans(Bool, False{}, Nat.is_lt(pp, 0n), True{},
        M1.lt_zero_false(pp), hh)))

# a number below another is not it
def lt_neq(+xx: Nat, +yy: Nat, hh: {Nat.is_lt(xx, yy) == True{} : Bool}) -> {Nat.is_eq(xx, yy) == False{} : Bool}:
  match xx yy:
    case _xx 0n:
      Empty.absurd({Nat.is_eq(xx, 0n) == False{} : Bool}, M1.false_true(Equal.trans(Bool, False{}, Nat.is_lt(xx,
        0n), True{}, M1.lt_zero_false(xx), hh)))
    case 0n 1n+_qq:
      {==}
    case 1n+pp 1n+qq:
      lt_neq(pp, qq, hh)

# a number above another is not it
def gt_neq(+xx: Nat, +yy: Nat, hh: {Nat.is_lt(yy, xx) == True{} : Bool}) -> {Nat.is_eq(xx, yy) == False{} : Bool}:
  match xx yy:
    case 0n _yy:
      Empty.absurd({Nat.is_eq(0n, yy) == False{} : Bool}, M1.false_true(Equal.trans(Bool, False{}, Nat.is_lt(yy,
        0n), True{}, M1.lt_zero_false(yy), hh)))
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
      +ex = Equal.sym(Nat, Nat.sub(xx, 0n), xx, M4.sub_zero(xx))
      +ey = Equal.sym(Nat, Nat.sub(yy, 0n), yy, M4.sub_zero(yy))
      %ex : {Nat.is_eq(_, Nat.sub(yy, 0n)) == Nat.is_eq(xx, yy) : Bool}
      %ey : {Nat.is_eq(xx, _) == Nat.is_eq(xx, yy) : Bool}
      {==}
    case 1n+cc 0n _yy:
      Empty.absurd({Nat.is_eq(0n, Nat.sub(yy, 1n+cc)) == Nat.is_eq(0n, yy) : Bool}, M1.false_true(hx))
    case 1n+cc 1n+_pp 0n:
      Empty.absurd({Nat.is_eq(Nat.sub(1n+_pp, 1n+cc), 0n) == Nat.is_eq(1n+_pp, 0n) : Bool}, M1.false_true(hy))
    case 1n+cc 1n+pp 1n+qq:
      eq_sub(cc, pp, qq, hx, hy)

# U32 shr of the double of m is m
def shr_half(uu: U32, +mm: Nat, ee: {U32.to_nat(uu) == Nat.double(mm) : Nat}) -> {U32.to_nat(U32.shr(uu)) == mm :
  Nat}:
  match uu:
    case U32{+ww}:
      match ww:
        case WCon{+bb, +rest}:
          match bb:
            case False{}:
              Equal.trans(Nat, Word.to_nat(32n, Word.shr.pad(31n, rest)), Word.to_nat(31n, rest), mm, M1.pad_nat(31n,
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
      M1.lt_rw_r(U32.to_nat(ii), U32.to_nat(hh), Nat.pow(2n, ee), eh, Equal.trans(Bool, Nat.is_lt(U32.to_nat(ii),
        U32.to_nat(hh)), U32.is_lt(ii, hh), True{}, Equal.sym(Bool, U32.is_lt(ii, hh), Nat.is_lt(U32.to_nat(ii),
        U32.to_nat(hh)), M5.u32_lt(ii, hh)), ez))
    case False{}:
      +pw = Nat.pow(2n, ee)
      +ni = U32.to_nat(ii)
      +hle = {M3.not_lt_le(ni, U32.to_nat(hh), Equal.trans(Bool, Nat.is_lt(ni, U32.to_nat(hh)), U32.is_lt(ii, hh),
        False{}, Equal.sym(Bool, U32.is_lt(ii, hh), Nat.is_lt(ni, U32.to_nat(hh)), M5.u32_lt(ii, hh)), ez)) :
        {Nat.is_le(U32.to_nat(hh), ni) == True{} : Bool}}
      +es = {M4.ras.u32_sub_nat(ii, hh, hle) : {U32.to_nat(U32.sub(ii, hh)) == Nat.sub(ni, U32.to_nat(hh)) : Nat}}
      +hle2 = {M1.le_rw_l(U32.to_nat(hh), pw, ni, eh, hle) : {Nat.is_le(pw, ni) == True{} : Bool}}
      +hlt = {M1.lt_rw_r(ni, Nat.double(pw), Nat.add(pw, pw), M1.double_add(pw), hi) :
        {Nat.is_lt(ni, Nat.add(pw, pw)) == True{} : Bool}}
      +hs = {M4.sub_lt(pw, ni, pw, hle2, hlt) : {Nat.is_lt(Nat.sub(ni, pw), pw) == True{} : Bool}}
      +e2 = {Equal.trans(Nat, U32.to_nat(U32.sub(ii, hh)), Nat.sub(ni, U32.to_nat(hh)), Nat.sub(ni, pw), es,
        Equal.cong(Nat, Nat, xx => Nat.sub(ni, xx), U32.to_nat(hh), pw, eh)) :
        {U32.to_nat(U32.sub(ii, hh)) == Nat.sub(ni, pw) : Nat}}
      M1.lt_rw_l(Nat.sub(ni, pw), U32.to_nat(U32.sub(ii, hh)), pw, Equal.sym(Nat, U32.to_nat(U32.sub(ii, hh)),
        Nat.sub(ni, pw), e2), hs)

# the U32 below-test as the Nat one
def lt_nat(
  +aa: U32,
  +bb: U32,
  +zz: Bool,
  ez: {U32.is_lt(aa, bb) == zz : Bool}
) -> {Nat.is_lt(U32.to_nat(aa), U32.to_nat(bb)) == zz : Bool}:
  Equal.trans(Bool, Nat.is_lt(U32.to_nat(aa), U32.to_nat(bb)), U32.is_lt(aa, bb), zz, Equal.sym(Bool, U32.is_lt(aa,
    bb), Nat.is_lt(U32.to_nat(aa), U32.to_nat(bb)), M5.u32_lt(aa, bb)), ez)

# two walks end at one leaf exactly when the indices are equal, as same_nat says it
def SameNat(+ee: Nat, +hh: U32, +ii: U32, +jj: U32) -> Type:
  {M1.same(ee, hh, ii, jj) == Nat.is_eq(U32.to_nat(ii), U32.to_nat(jj)) : Bool}

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
) -> {M1.same.if(zi, zj, M1.same(ee, hh, Bool.pick(U32, zi, ii, U32.sub(ii, hh)), Bool.pick(U32, zj, jj, U32.sub(jj,
  hh)))) == Nat.is_eq(U32.to_nat(ii), U32.to_nat(jj)) : Bool}:
  match zi zj:
    case True{} True{}:
      ih
    case False{} False{}:
      +ni = U32.to_nat(ii)
      +nj = U32.to_nat(jj)
      +nh = U32.to_nat(hh)
      +hi = {M3.not_lt_le(ni, nh, lt_nat(ii, hh, False{}, ezi)) : {Nat.is_le(nh, ni) == True{} : Bool}}
      +hj = {M3.not_lt_le(nj, nh, lt_nat(jj, hh, False{}, ezj)) : {Nat.is_le(nh, nj) == True{} : Bool}}
      +es = {Equal.trans(Bool, Nat.is_eq(U32.to_nat(U32.sub(ii, hh)), U32.to_nat(U32.sub(jj, hh))),
        Nat.is_eq(Nat.sub(ni,
        nh), U32.to_nat(U32.sub(jj, hh))), Nat.is_eq(Nat.sub(ni, nh), Nat.sub(nj, nh)), Equal.cong(Nat, Bool,
        xx => Nat.is_eq(xx, U32.to_nat(U32.sub(jj, hh))), U32.to_nat(U32.sub(ii, hh)), Nat.sub(ni, nh),
        M4.ras.u32_sub_nat(ii, hh, hi)), Equal.cong(Nat, Bool, xx => Nat.is_eq(Nat.sub(ni, nh), xx),
            U32.to_nat(U32.sub(jj,
        hh)), Nat.sub(nj, nh), M4.ras.u32_sub_nat(jj, hh, hj))) : {Nat.is_eq(U32.to_nat(U32.sub(ii, hh)),
        U32.to_nat(U32.sub(jj, hh))) == Nat.is_eq(Nat.sub(ni, nh), Nat.sub(nj, nh)) : Bool}}
      Equal.trans(Bool, M1.same(ee, hh, U32.sub(ii, hh), U32.sub(jj, hh)), Nat.is_eq(U32.to_nat(U32.sub(ii, hh)),
        U32.to_nat(U32.sub(jj, hh))), Nat.is_eq(ni, nj), ih, Equal.trans(Bool, Nat.is_eq(U32.to_nat(U32.sub(ii, hh)),
        U32.to_nat(U32.sub(jj, hh))), Nat.is_eq(Nat.sub(ni, nh), Nat.sub(nj, nh)), Nat.is_eq(ni, nj), es, eq_sub(nh,
        ni, nj, hi, hj)))
    case True{} False{}:
      +ni = U32.to_nat(ii)
      +nj = U32.to_nat(jj)
      +nh = U32.to_nat(hh)
      +hj = {M3.not_lt_le(nj, nh, lt_nat(jj, hh, False{}, ezj)) : {Nat.is_le(nh, nj) == True{} : Bool}}
      Equal.sym(Bool, Nat.is_eq(ni, nj), False{}, lt_neq(ni, nj, M1.lt_le_trans(ni, nh, nj, lt_nat(ii, hh, True{}, ezi),
        hj)))
    case False{} True{}:
      +ni = U32.to_nat(ii)
      +nj = U32.to_nat(jj)
      +nh = U32.to_nat(hh)
      +hi = {M3.not_lt_le(ni, nh, lt_nat(ii, hh, False{}, ezi)) : {Nat.is_le(nh, ni) == True{} : Bool}}
      Equal.sym(Bool, Nat.is_eq(ni, nj), False{}, gt_neq(ni, nj, M1.lt_le_trans(nj, nh, ni, lt_nat(jj, hh, True{}, ezj),
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
) -> {M1.same(dd, nn, ii, jj) == Nat.is_eq(U32.to_nat(ii), U32.to_nat(jj)) : Bool}:
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
      +sp = {M1.pow2_succ(ee) : {Nat.pow(2n, 1n+ee) == Nat.double(pw) : Nat}}
      +eh = {shr_half(nn, pw, Equal.trans(Nat, U32.to_nat(nn), Nat.pow(2n, 1n+ee), Nat.double(pw), hn, sp)) :
        {U32.to_nat(hh) == pw : Nat}}
      +hi2 = {M1.lt_rw_r(U32.to_nat(ii), Nat.pow(2n, 1n+ee), Nat.double(pw), sp, hi) :
        {Nat.is_lt(U32.to_nat(ii), Nat.double(pw)) == True{} : Bool}}
      +hj2 = {M1.lt_rw_r(U32.to_nat(jj), Nat.pow(2n, 1n+ee), Nat.double(pw), sp, hj) :
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
      Empty.absurd({Nat.is_lt(1n+pp, 1n) == True{} : Bool}, M1.false_true(hh))

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
        pln.succ_inj(1n+Nat.double(Word.to_nat(qq, uu)), 0n, hm)))
    case False{}:
      +un = Word.to_nat(qq, uu)
      Equal.cong(Nat, Nat, xx => 1n+xx, un, 0n, dbl_inj(un, 0n, pln.succ_inj(Nat.double(un), 0n, hm)))

# a word below one: its bit is clear, and the rest is below one
def mw.t0(
  +qq: Nat,
  bb: Bool,
  +tt: Word(qq),
  +hw: {Nat.is_lt(Word.to_nat(1n+qq, WCon{bb, tt}), 1n) == True{} : Bool}
) -> {Nat.is_lt(Word.to_nat(qq, tt), 1n) == True{} : Bool}:
  match bb:
    case True{}:
      Empty.absurd({Nat.is_lt(Word.to_nat(qq, tt), 1n) == True{} : Bool}, M1.false_true(Equal.trans(Bool, False{},
        Nat.is_lt(Nat.double(Word.to_nat(qq, tt)), 0n), True{}, M1.lt_zero_false(Nat.double(Word.to_nat(qq, tt))), hw)))
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
      Empty.absurd({False{} == True{} : Bool}, M1.false_true(Equal.trans(Bool, False{},
        Nat.is_lt(Nat.double(Word.to_nat(qq, tt)), 0n), True{}, M1.lt_zero_false(Nat.double(Word.to_nat(qq, tt))), hw)))

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
        M1.pow2_succ(ff))))
    case True{}:
      +un = Word.to_nat(qq, uu)
      dbl_inj(1n+un, Nat.pow(2n, ff), Equal.trans(Nat, 2n+Nat.double(un), Nat.pow(2n, 1n+ff), Nat.double(Nat.pow(2n,
        ff)), hm, M1.pow2_succ(ff)))

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
        M1.pow2_succ(ff))))
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
          +hx = {M1.lt_rw_l(Word.to_nat(1n+qq, WCon{bb, tt}), Nat.add(M1.bit(bb), Nat.double(tn)), Nat.double(pw),
            M1.to_nat_con(qq, bb, tt), M1.lt_rw_r(Word.to_nat(1n+qq, WCon{bb, tt}), Nat.pow(2n, 1n+ff),
            Nat.double(pw), M1.pow2_succ(ff), hw)) : {Nat.is_lt(Nat.add(M1.bit(bb), Nat.double(tn)),
            Nat.double(pw)) == True{} : Bool}}
          +ea = {mask_w(qq, ff, tt, uu, mw.u1(qq, ff, cc, uu, hm), M1.lt_half(bb, tn, pw, hx)) : {Word.and(qq, tt,
              uu) ==
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
) -> {M1.mask(ii, nn) == ii : U32}:
  +pw = Nat.pow(2n, dd)
  +h1 = {M1.le_rw_r(1n, pw, U32.to_nat(nn), Equal.sym(Nat, U32.to_nat(nn), pw, hn), Equal.trans(Bool, Nat.is_le(1n,
    pw), Nat.is_lt(0n, pw), True{}, Equal.sym(Bool, Nat.is_lt(0n, pw), Nat.is_le(1n, pw), M1.lt_le_succ(0n, pw)),
    M1.pow_pos(dd))) : {Nat.is_le(1n, U32.to_nat(nn)) == True{} : Bool}}
  +es = {M4.ras.u32_sub_nat(nn, 1, h1) : {U32.to_nat(U32.sub(nn, 1)) == Nat.sub(U32.to_nat(nn), 1n) : Nat}}
  +hm = {Equal.trans(Nat, 1n+U32.to_nat(U32.sub(nn, 1)), Nat.add(1n, Nat.sub(U32.to_nat(nn), 1n)), pw,
    Equal.cong(Nat, Nat, xx => 1n+xx, U32.to_nat(U32.sub(nn, 1)), Nat.sub(U32.to_nat(nn), 1n), es), Equal.trans(Nat,
    Nat.add(1n, Nat.sub(U32.to_nat(nn), 1n)), U32.to_nat(nn), pw, M4.add_sub(1n, U32.to_nat(nn), h1), hn)) :
    {1n+U32.to_nat(U32.sub(nn, 1)) == pw : Nat}}
  mask_u(ii, U32.sub(nn, 1), dd, hm, hi)

# a read after a write to a perfect tree of 2^d leaves, d below 32, both indices below 2^d: the written value
# when the indices are equal, else the value there before
def at_set(
  +dd: Nat,
  +tt: M1.Tr,
  +ii: U32,
  +jj: U32,
  +vv: U32,
  +hp: {pf(dd, tt) == True{} : Bool},
  +hd: {Nat.is_lt(dd, 32n) == True{} : Bool},
  +hi: {Nat.is_lt(U32.to_nat(ii), Nat.pow(2n, dd)) == True{} : Bool},
  +hj: {Nat.is_lt(U32.to_nat(jj), Nat.pow(2n, dd)) == True{} : Bool}
) -> {M1.at(M1.set(tt, ii, vv), jj) == M1.after(Nat.is_eq(U32.to_nat(ii), U32.to_nat(jj)), vv, M1.at(tt, jj)) : U32}:
  +ss = M1.size(tt)
  +mi = M1.mask(ii, ss)
  +mj = M1.mask(jj, ss)
  +pt = M1.put(tt, ss, mi, vv)
  +hs = {size_nat(dd, tt, hp, hd) : {U32.to_nat(ss) == Nat.pow(2n, dd) : Nat}}
  +e1 = {Equal.cong(U32, U32, nn => M1.get(pt, nn, M1.mask(jj, nn)), M1.size(pt), ss, size_put(tt, ss, mi, vv)) :
    {M1.get(pt, M1.size(pt), M1.mask(jj, M1.size(pt))) == M1.get(pt, ss, mj) : U32}}
  +e2 = {get_put(dd, tt, ss, mi, mj, vv, hp) : {M1.get(pt, ss, mj) == M1.after(M1.same(dd, ss, mi, mj), vv, M1.get(tt,
      ss, mj)) :
    U32}}
  +e3 = {Equal.trans(Bool, M1.same(dd, ss, mi, mj), M1.same(dd, ss, ii, mj), M1.same(dd, ss, ii, jj), Equal.cong(U32,
      Bool,
    xx => M1.same(dd, ss, xx, mj), mi, ii, mask_id(ii, ss, dd, hs, hi)), Equal.cong(U32, Bool, xx => M1.same(dd, ss,
        ii, xx),
    mj, jj, mask_id(jj, ss, dd, hs, hj))) : {M1.same(dd, ss, mi, mj) == M1.same(dd, ss, ii, jj) : Bool}}
  +e4 = {Equal.trans(Bool, M1.same(dd, ss, mi, mj), M1.same(dd, ss, ii, jj), Nat.is_eq(U32.to_nat(ii), U32.to_nat(jj)),
      e3,
    same_nat(dd, ss, ii, jj, hs, hi, hj)) : {M1.same(dd, ss, mi, mj) == Nat.is_eq(U32.to_nat(ii),
        U32.to_nat(jj)) : Bool}}
  Equal.trans(U32, M1.get(pt, M1.size(pt), M1.mask(jj, M1.size(pt))), M1.get(pt, ss, mj),
      M1.after(Nat.is_eq(U32.to_nat(ii),
    U32.to_nat(jj)), vv, M1.get(tt, ss, mj)), e1, Equal.trans(U32, M1.get(pt, ss, mj), M1.after(M1.same(dd, ss, mi,
        mj), vv,
    M1.get(tt, ss, mj)), M1.after(Nat.is_eq(U32.to_nat(ii), U32.to_nat(jj)), vv, M1.get(tt, ss, mj)), e2,
        Equal.cong(Bool, U32,
    bb => M1.after(bb, vv, M1.get(tt, ss, mj)), M1.same(dd, ss, mi, mj), Nat.is_eq(U32.to_nat(ii), U32.to_nat(jj)),
        e4)))

# a write to a perfect tree leaves it perfect
def pf_set(
  +dd: Nat,
  +tt: M1.Tr,
  +ii: U32,
  +vv: U32,
  +hp: {pf(dd, tt) == True{} : Bool}
) -> {pf(dd, M1.set(tt, ii, vv)) == True{} : Bool}:
  Equal.trans(Bool, pf(dd, M1.set(tt, ii, vv)), pf(dd, tt), True{}, pf_put(dd, tt, M1.size(tt), M1.mask(ii,
      M1.size(tt)), vv), hp)

# a read at the index just written finds the value, in any tree
def at_set_same(+tt: M1.Tr, +ii: U32, +vv: U32) -> {M1.at(M1.set(tt, ii, vv), ii) == vv : U32}:
  +ss = M1.size(tt)
  +pt = M1.put(tt, ss, M1.mask(ii, ss), vv)
  Equal.trans(U32, M1.get(pt, M1.size(pt), M1.mask(ii, M1.size(pt))), M1.get(pt, ss, M1.mask(ii, ss)), vv,
      Equal.cong(U32, U32,
    nn => M1.get(pt, nn, M1.mask(ii, nn)), M1.size(pt), ss, size_put(tt, ss, M1.mask(ii, ss), vv)), get_put_same(tt,
        ss, M1.mask(ii,
    ss), vv))

# ---- the laws on arrays ----

# a tree's array is perfect exactly when the tree is
def perfect_arr(+dd: Nat, +tt: M1.Tr) -> {Laws.jpg.perfect(dd, M1.arr(tt)) == pf(dd, tt) : Bool}:
  match dd tt:
    case 0n M1.TLeaf{_xx}:
      {==}
    case 0n M1.TNode{_lo, _hi}:
      {==}
    case 1n+_ee M1.TLeaf{_xx}:
      {==}
    case 1n+ee M1.TNode{lo, hi}:
      Equal.trans(Bool, Bool.and(Laws.jpg.perfect(ee, M1.arr(lo)), Laws.jpg.perfect(ee, M1.arr(hi))), Bool.and(pf(ee,
          lo),
        Laws.jpg.perfect(ee, M1.arr(hi))), Bool.and(pf(ee, lo), pf(ee, hi)), Equal.cong(Bool, Bool, bb => Bool.and(bb,
        Laws.jpg.perfect(ee, M1.arr(hi))), Laws.jpg.perfect(ee, M1.arr(lo)), pf(ee, lo), perfect_arr(ee, lo)),
        Equal.cong(Bool, Bool, bb => Bool.and(pf(ee, lo), bb), Laws.jpg.perfect(ee, M1.arr(hi)), pf(ee, hi),
        perfect_arr(ee, hi)))

# a perfect plane's tree is perfect
def pf_of(
  +dd: Nat,
  -aa: Array<U32>,
  +tt: M1.Tr,
  +ea: {aa == M1.arr(tt) : Array<U32>},
  +hp: {Laws.jpg.perfect(dd, aa) == True{} : Bool}
) -> {pf(dd, tt) == True{} : Bool}:
  Equal.trans(Bool, pf(dd, tt), Laws.jpg.perfect(dd, M1.arr(tt)), True{}, Equal.sym(Bool, Laws.jpg.perfect(dd,
      M1.arr(tt)),
    pf(dd, tt), perfect_arr(dd, tt)), Equal.trans(Bool, Laws.jpg.perfect(dd, M1.arr(tt)), Laws.jpg.perfect(dd, aa),
        True{},
    Equal.sym(Bool, Laws.jpg.perfect(dd, aa), Laws.jpg.perfect(dd, M1.arr(tt)), Equal.cong(Array<U32>, Bool,
    xx => Laws.jpg.perfect(dd, xx), aa, M1.arr(tt), ea)), hp))

# the value Array.get finds in a tree's array after Array.set: at, after set
def val_set(
  +tt: M1.Tr,
  +ii: U32,
  +vv: U32,
  +jj: U32
) -> {D1.jpg.val(Array.get(U32, Array.set(U32, M1.arr(tt), ii, vv), jj)) == M1.at(M1.set(tt, ii, vv), jj) : U32}:
  se = Equal.sym(Array<U32>, Array.set(U32, M1.arr(tt), ii, vv), M1.arr(M1.set(tt, ii, vv)), set_arr(tt, ii, vv))
  %se : {D1.jpg.val(Array.get(U32, _, jj)) == M1.at(M1.set(tt, ii, vv), jj) : U32}
  sg = Equal.sym(Array<U32> & U32, Array.get(U32, M1.arr(M1.set(tt, ii, vv)), jj), (M1.arr(M1.set(tt, ii, vv)),
      M1.at(M1.set(tt, ii,
    vv), jj)), get_arr(M1.set(tt, ii, vv), jj))
  %sg : {D1.jpg.val(_) == M1.at(M1.set(tt, ii, vv), jj) : U32}
  {==}

# the value Array.get finds in a tree's array: at
def val_at(+tt: M1.Tr, +jj: U32) -> {D1.jpg.val(Array.get(U32, M1.arr(tt), jj)) == M1.at(tt, jj) : U32}:
  sg = Equal.sym(Array<U32> & U32, Array.get(U32, M1.arr(tt), jj), (M1.arr(tt), M1.at(tt, jj)), get_arr(tt, jj))
  %sg : {D1.jpg.val(_) == M1.at(tt, jj) : U32}
  {==}

# jpeg_get_set, from a tree the plane is the array of
def get_same_of(
  -plane: Array<U32>,
  +ii: U32,
  +vv: U32,
  oo: M1.Of(plane)
) -> {D1.jpg.val(Array.get(U32, Array.set(U32, plane, ii, vv), ii)) == vv : U32}:
  (+tt, ep) = oo
  sp = Equal.sym(Array<U32>, plane, M1.arr(tt), ep)
  %sp : {D1.jpg.val(Array.get(U32, Array.set(U32, _, ii, vv), ii)) == vv : U32}
  Equal.trans(U32, D1.jpg.val(Array.get(U32, Array.set(U32, M1.arr(tt), ii, vv), ii)), M1.at(M1.set(tt, ii, vv),
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
  oo: M1.Of(plane)
) -> {D1.jpg.val(Array.get(U32, Array.set(U32, plane, ii, vv), jj)) == D1.jpg.val(Array.get(U32, plane, jj)) :
  U32}:
  (+tt, ep) = oo
  +sp = {Equal.sym(Array<U32>, plane, M1.arr(tt), ep) : {M1.arr(tt) == plane : Array<U32>}}
  +hp = pf_of(dd, plane, tt, Equal.sym(Array<U32>, M1.arr(tt), plane, sp), h_perfect)
  %sp : {D1.jpg.val(Array.get(U32, Array.set(U32, _, ii, vv), jj)) == D1.jpg.val(Array.get(U32, _, jj)) : U32}
  +eq = {Equal.trans(Bool, Nat.is_eq(U32.to_nat(ii), U32.to_nat(jj)), U32.is_eq(ii, jj), False{}, Equal.sym(Bool,
    U32.is_eq(ii, jj), Nat.is_eq(U32.to_nat(ii), U32.to_nat(jj)), M1.u32_eq(ii, jj)), h_ne) :
    {Nat.is_eq(U32.to_nat(ii), U32.to_nat(jj)) == False{} : Bool}}
  Equal.trans(U32, D1.jpg.val(Array.get(U32, Array.set(U32, M1.arr(tt), ii, vv), jj)), M1.at(M1.set(tt, ii, vv),
    jj), D1.jpg.val(Array.get(U32, M1.arr(tt), jj)), val_set(tt, ii, vv, jj), Equal.trans(U32,
    M1.at(M1.set(tt, ii, vv), jj), M1.after(Nat.is_eq(U32.to_nat(ii), U32.to_nat(jj)), vv, M1.at(tt, jj)),
    D1.jpg.val(Array.get(U32, M1.arr(tt), jj)), at_set(dd, tt, ii, jj, vv, hp, h_dd, h_ii, h_jj),
    Equal.trans(U32, M1.after(Nat.is_eq(U32.to_nat(ii), U32.to_nat(jj)), vv, M1.at(tt, jj)), M1.at(tt, jj),
    D1.jpg.val(Array.get(U32, M1.arr(tt), jj)), Equal.cong(Bool, U32, bb => M1.after(bb, vv, M1.at(tt, jj)),
    Nat.is_eq(U32.to_nat(ii), U32.to_nat(jj)), False{}, eq), Equal.sym(U32, D1.jpg.val(Array.get(U32, M1.arr(tt),
    jj)), M1.at(tt, jj), val_at(tt, jj)))))

# ---- painting a block, on the tree ----

# decode.splat.in on the tree
def inT(xin: Bool, yin: Bool, +tt: M1.Tr, +xx: U32, +yy: U32, +ww: U32, +vv: U32) -> M1.Tr:
  match xin yin:
    case True{} True{}:
      M1.set(tt, (yy * ww + xx : U32), vv)
    case True{} False{}:
      tt
    case False{} _yin:
      tt

# decode.splat.px on the tree
def pxT(left: Nat, +tt: M1.Tr, +x0: U32, +yy: U32, +px: U32, +ww: U32, +hh: U32, +vv: U32) -> M1.Tr:
  match left:
    case 0n:
      tt
    case 1n+pp:
      pxT(pp, inT(U32.is_lt((x0 + px : U32), ww), U32.is_lt(yy, hh), tt, (x0 + px : U32), yy, ww, vv), x0, yy,
        (px + 1 : U32), ww, hh, vv)

# decode.splat.py on the tree
def pyT(left: Nat, +tt: M1.Tr, +x0: U32, +y0: U32, +py: U32, +pw: U32, +ww: U32, +hh: U32, +vv: U32) -> M1.Tr:
  match left:
    case 0n:
      tt
    case 1n+pp:
      pyT(pp, pxT(U32.to_nat(pw), tt, x0, (y0 + py : U32), 0, ww, hh, vv), x0, y0, (py + 1 : U32), pw, ww, hh, vv)

# decode.splat.col on the tree
def colT(
  left: Nat,
  +tt: M1.Tr,
  +samples: List<&2, U32>,
  +row: U32,
  +col: U32,
  +ox: U32,
  +oy: U32,
  +pw: U32,
  +ph: U32,
  +ww: U32,
  +hh: U32
) -> M1.Tr:
  match left:
    case 0n:
      tt
    case 1n+pp:
      colT(pp, pyT(U32.to_nat(ph), tt, (ox + col * pw : U32), (oy + row * ph : U32), 0, pw, ww, hh,
        Jpeg.decode.at(samples, (row * 8 + col : U32))), samples, row, (col + 1 : U32), ox, oy, pw, ph, ww, hh)

# decode.splat on the tree
def cvT(
  left: Nat,
  +tt: M1.Tr,
  +samples: List<&2, U32>,
  +row: U32,
  +ox: U32,
  +oy: U32,
  +pw: U32,
  +ph: U32,
  +ww: U32,
  +hh: U32
) -> M1.Tr:
  match left:
    case 0n:
      tt
    case 1n+pp:
      cvT(pp, colT(8n, tt, samples, row, 0, ox, oy, pw, ph, ww, hh), samples, (row + 1 : U32), ox, oy, pw, ph, ww, hh)

# the decoder's pixel write on a tree's array is the tree's
def arr_in(
  xin: Bool,
  yin: Bool,
  +tt: M1.Tr,
  +xx: U32,
  +yy: U32,
  +ww: U32,
  +vv: U32
) -> {Jpeg.decode.splat.in(xin, yin, M1.arr(tt), xx, yy, ww, vv) == M1.arr(inT(xin, yin, tt, xx, yy, ww,
    vv)) : Array<U32>}:
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
  +tt: M1.Tr,
  +x0: U32,
  +yy: U32,
  +px: U32,
  +ww: U32,
  +hh: U32,
  +vv: U32
) -> {Jpeg.decode.splat.px(left, M1.arr(tt), x0, yy, px, ww, hh, vv) == M1.arr(pxT(left, tt, x0, yy, px, ww, hh, vv)) :
  Array<U32>}:
  match left:
    case 0n:
      {==}
    case 1n+pp:
      +xin = U32.is_lt((x0 + px : U32), ww)
      +yin = U32.is_lt(yy, hh)
      +t1 = inT(xin, yin, tt, (x0 + px : U32), yy, ww, vv)
      se = Equal.sym(Array<U32>, Jpeg.decode.splat.in(xin, yin, M1.arr(tt), (x0 + px : U32), yy, ww, vv), M1.arr(t1),
        arr_in(xin, yin, tt, (x0 + px : U32), yy, ww, vv))
      %se : {Jpeg.decode.splat.px(pp, _, x0, yy, (px + 1 : U32), ww, hh, vv) == M1.arr(pxT(pp, t1, x0, yy,
          (px + 1 : U32),
        ww, hh, vv)) : Array<U32>}
      arr_px(pp, t1, x0, yy, (px + 1 : U32), ww, hh, vv)

# the decoder's cover of one sample on a tree's array is the tree's
def arr_py(
  left: Nat,
  +tt: M1.Tr,
  +x0: U32,
  +y0: U32,
  +py: U32,
  +pw: U32,
  +ww: U32,
  +hh: U32,
  +vv: U32
) -> {Jpeg.decode.splat.py(left, M1.arr(tt), x0, y0, py, pw, ww, hh, vv) == M1.arr(pyT(left, tt, x0, y0, py, pw, ww, hh,
  vv)) :
  Array<U32>}:
  match left:
    case 0n:
      {==}
    case 1n+pp:
      +t1 = pxT(U32.to_nat(pw), tt, x0, (y0 + py : U32), 0, ww, hh, vv)
      se = Equal.sym(Array<U32>, Jpeg.decode.splat.px(U32.to_nat(pw), M1.arr(tt), x0, (y0 + py : U32), 0, ww, hh, vv),
        M1.arr(t1), arr_px(U32.to_nat(pw), tt, x0, (y0 + py : U32), 0, ww, hh, vv))
      %se : {Jpeg.decode.splat.py(pp, _, x0, y0, (py + 1 : U32), pw, ww, hh, vv) == M1.arr(pyT(pp, t1, x0, y0,
        (py + 1 : U32), pw, ww, hh, vv)) : Array<U32>}
      arr_py(pp, t1, x0, y0, (py + 1 : U32), pw, ww, hh, vv)

# the decoder's block row on a tree's array is the tree's
def arr_col(
  left: Nat,
  +tt: M1.Tr,
  +samples: List<&2, U32>,
  +row: U32,
  +col: U32,
  +ox: U32,
  +oy: U32,
  +pw: U32,
  +ph: U32,
  +ww: U32,
  +hh: U32
) -> {Jpeg.decode.splat.col(left, M1.arr(tt), samples, row, col, ox, oy, pw, ph, ww, hh) == M1.arr(colT(left, tt,
    samples,
  row, col, ox, oy, pw, ph, ww, hh)) : Array<U32>}:
  match left:
    case 0n:
      {==}
    case 1n+pp:
      +x0 = (ox + col * pw : U32)
      +y0 = (oy + row * ph : U32)
      +vv = Jpeg.decode.at(samples, (row * 8 + col : U32))
      +t1 = pyT(U32.to_nat(ph), tt, x0, y0, 0, pw, ww, hh, vv)
      se = Equal.sym(Array<U32>, Jpeg.decode.splat.py(U32.to_nat(ph), M1.arr(tt), x0, y0, 0, pw, ww, hh, vv),
          M1.arr(t1),
        arr_py(U32.to_nat(ph), tt, x0, y0, 0, pw, ww, hh, vv))
      %se : {Jpeg.decode.splat.col(pp, _, samples, row, (col + 1 : U32), ox, oy, pw, ph, ww, hh) == M1.arr(colT(pp, t1,
        samples, row, (col + 1 : U32), ox, oy, pw, ph, ww, hh)) : Array<U32>}
      arr_col(pp, t1, samples, row, (col + 1 : U32), ox, oy, pw, ph, ww, hh)

# the decoder's block on a tree's array is the tree's
def arr_cv(
  left: Nat,
  +tt: M1.Tr,
  +samples: List<&2, U32>,
  +row: U32,
  +ox: U32,
  +oy: U32,
  +pw: U32,
  +ph: U32,
  +ww: U32,
  +hh: U32
) -> {Jpeg.decode.splat(left, M1.arr(tt), samples, row, ox, oy, pw, ph, ww, hh) == M1.arr(cvT(left, tt, samples, row,
    ox, oy,
  pw, ph, ww, hh)) : Array<U32>}:
  match left:
    case 0n:
      {==}
    case 1n+pp:
      +t1 = colT(8n, tt, samples, row, 0, ox, oy, pw, ph, ww, hh)
      se = Equal.sym(Array<U32>, Jpeg.decode.splat.col(8n, M1.arr(tt), samples, row, 0, ox, oy, pw, ph, ww, hh),
          M1.arr(t1),
        arr_col(8n, tt, samples, row, 0, ox, oy, pw, ph, ww, hh))
      %se : {Jpeg.decode.splat(pp, _, samples, (row + 1 : U32), ox, oy, pw, ph, ww, hh) == M1.arr(cvT(pp, t1, samples,
        (row + 1 : U32), ox, oy, pw, ph, ww, hh)) : Array<U32>}
      arr_cv(pp, t1, samples, (row + 1 : U32), ox, oy, pw, ph, ww, hh)

# a pixel write keeps a tree perfect
def pf_in(
  xin: Bool,
  yin: Bool,
  +dd: Nat,
  +tt: M1.Tr,
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
  +tt: M1.Tr,
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
  +tt: M1.Tr,
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
  +tt: M1.Tr,
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
  +tt: M1.Tr,
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
  M4.le_add_more(aa, Nat.add(aa, bb), cc, M4.le_add_more(aa, aa, bb, M1.le_refl(aa)))

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
        M1.lt_le_trans(bb, ww, xx, hb, le_plus(ww, Nat.mul(qq, ww), dd))), Equal.sym(Bool, Bool.and(Nat.is_eq(bb, dd),
        False{}), False{}, M4.and_false_r(Nat.is_eq(bb, dd))))
    case 1n+pp 0n:
      +xx = Nat.add(Nat.mul(1n+pp, ww), bb)
      Equal.trans(Bool, Nat.is_eq(xx, dd), False{}, Bool.and(Nat.is_eq(bb, dd), False{}), gt_neq(xx, dd,
        M1.lt_le_trans(dd, ww, xx, hd, le_plus(ww, Nat.mul(pp, ww), bb))), Equal.sym(Bool, Bool.and(Nat.is_eq(bb, dd),
        False{}), False{}, M4.and_false_r(Nat.is_eq(bb, dd))))
    case 1n+pp 1n+qq:
      +xa = Nat.add(Nat.mul(pp, ww), bb)
      +xc = Nat.add(Nat.mul(qq, ww), dd)
      +e1 = {Equal.trans(Bool, Nat.is_eq(Nat.add(Nat.add(ww, Nat.mul(pp, ww)), bb), Nat.add(Nat.add(ww, Nat.mul(qq,
        ww)),
        dd)), Nat.is_eq(Nat.add(ww, xa), Nat.add(Nat.add(ww, Nat.mul(qq, ww)), dd)), Nat.is_eq(Nat.add(ww, xa),
        Nat.add(ww, xc)), Equal.cong(Nat, Bool, nn => Nat.is_eq(nn, Nat.add(Nat.add(ww, Nat.mul(qq, ww)), dd)),
        Nat.add(Nat.add(ww, Nat.mul(pp, ww)), bb), Nat.add(ww, xa), M1.ras.add_assoc(ww, Nat.mul(pp, ww), bb)),
        Equal.cong(Nat, Bool, nn => Nat.is_eq(Nat.add(ww, xa), nn), Nat.add(Nat.add(ww, Nat.mul(qq, ww)), dd),
        Nat.add(ww, xc), M1.ras.add_assoc(ww, Nat.mul(qq, ww), dd))) : {Nat.is_eq(Nat.add(Nat.add(ww, Nat.mul(pp, ww)),
            bb),
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
  M3.u32_mul_below(ww, hh, U32{sbit(32n, dd)}, M1.le_rw_r(Nat.mul(U32.to_nat(ww), U32.to_nat(hh)), Nat.pow(2n, dd),
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
  M3.u32_index(ww, xx, yy, hh, (ww * hh : U32), area_nat(ww, hh, dd, hd, hfit), lt_of(xx, ww, hx), lt_of(yy, hh, hy))

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
  M1.lt_rw_l(nx, U32.to_nat((yy * ww + xx : U32)), Nat.pow(2n, dd), Equal.sym(Nat, U32.to_nat((yy * ww + xx : U32)), nx,
    idx_nat(ww, hh, xx, yy, dd, hd, hfit, hx, hy)), M1.lt_le_trans(nx, Nat.mul(U32.to_nat(ww), U32.to_nat(hh)),
    Nat.pow(2n, dd), M3.index_lt(U32.to_nat(xx), U32.to_nat(yy), U32.to_nat(ww), U32.to_nat(hh), lt_of(xx, ww, hx),
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
    Nat.is_eq(U32.to_nat(ax), U32.to_nat(xx)), M1.u32_eq(ax, xx))), Equal.cong(Bool, Bool, bb => Bool.and(U32.is_eq(ax,
    xx), bb), Nat.is_eq(U32.to_nat(ay), U32.to_nat(yy)), U32.is_eq(ay, yy), Equal.sym(Bool, U32.is_eq(ay, yy),
    Nat.is_eq(U32.to_nat(ay), U32.to_nat(yy)), M1.u32_eq(ay, yy)))) : {Bool.and(Nat.is_eq(U32.to_nat(ax),
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
      +ea = {M1.ueq(aa, bb, ez) : {aa == bb : U32}}
      Empty.absurd({True{} == False{} : Bool}, M1.false_true(Equal.trans(Bool, False{}, U32.is_lt(aa, ww), True{},
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
  +tt: M1.Tr,
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
) -> {M1.at(inT(xin, yin, tt, ax, ay, ww, vv), (yy * ww + xx : U32)) == M1.after(Bool.and(U32.is_eq(ax, xx),
    U32.is_eq(ay,
  yy)), vv, M1.at(tt, (yy * ww + xx : U32))) : U32}:
  match xin yin:
    case True{} True{}:
      +ia = (ay * ww + ax : U32)
      +kk = (yy * ww + xx : U32)
      Equal.trans(U32, M1.at(M1.set(tt, ia, vv), kk), M1.after(Nat.is_eq(U32.to_nat(ia), U32.to_nat(kk)), vv, M1.at(tt,
          kk)),
        M1.after(Bool.and(U32.is_eq(ax, xx), U32.is_eq(ay, yy)), vv, M1.at(tt, kk)), at_set(dd, tt, ia, kk, vv, hp, hd,
        idx_lt(ww, hh, ax, ay, dd, hd, hfit, exin, eyin), idx_lt(ww, hh, xx, yy, dd, hd, hfit, hx, hy)),
        Equal.cong(Bool, U32, bb => M1.after(bb, vv, M1.at(tt, kk)), Nat.is_eq(U32.to_nat(ia), U32.to_nat(kk)),
        Bool.and(U32.is_eq(ax, xx), U32.is_eq(ay, yy)), pix_eq(ww, hh, ax, ay, xx, yy, dd, hd, hfit, exin, eyin, hx,
        hy)))
    case True{} False{}:
      +kk = (yy * ww + xx : U32)
      +ef = {Equal.trans(Bool, Bool.and(U32.is_eq(ax, xx), U32.is_eq(ay, yy)), Bool.and(U32.is_eq(ax, xx), False{}),
        False{}, Equal.cong(Bool, Bool, bb => Bool.and(U32.is_eq(ax, xx), bb), U32.is_eq(ay, yy), False{},
        neq_out(ay, yy, hh, eyin, hy)), M4.and_false_r(U32.is_eq(ax, xx))) : {Bool.and(U32.is_eq(ax, xx), U32.is_eq(ay,
        yy)) == False{} : Bool}}
      Equal.sym(U32, M1.after(Bool.and(U32.is_eq(ax, xx), U32.is_eq(ay, yy)), vv, M1.at(tt, kk)), M1.at(tt, kk),
        Equal.cong(Bool, U32, bb => M1.after(bb, vv, M1.at(tt, kk)), Bool.and(U32.is_eq(ax, xx), U32.is_eq(ay, yy)),
            False{},
        ef))
    case False{} _yin:
      +kk = (yy * ww + xx : U32)
      +ef = {Equal.cong(Bool, Bool, bb => Bool.and(bb, U32.is_eq(ay, yy)), U32.is_eq(ax, xx), False{}, neq_out(ax, xx,
        ww, exin, hx)) : {Bool.and(U32.is_eq(ax, xx), U32.is_eq(ay, yy)) == False{} : Bool}}
      Equal.sym(U32, M1.after(Bool.and(U32.is_eq(ax, xx), U32.is_eq(ay, yy)), vv, M1.at(tt, kk)), M1.at(tt, kk),
        Equal.cong(Bool, U32, bb => M1.after(bb, vv, M1.at(tt, kk)), Bool.and(U32.is_eq(ax, xx), U32.is_eq(ay, yy)),
            False{},
        ef))

# a later hit of the same value over an earlier one: the value, when either hit
def ba1(
  hh: Bool,
  rr: Bool,
  ee: Bool,
  +vv: U32,
  +oo: U32
) -> {M1.after(Bool.and(rr, ee), vv, M1.after(Bool.and(hh, ee), vv, oo)) == M1.after(Bool.and(Bool.or(hh, rr), ee), vv,
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
) -> {M1.after(Bool.and(ss, rr), vv, M1.after(Bool.and(ss, hh), vv, oo)) == M1.after(Bool.and(ss, Bool.or(hh, rr)), vv,
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
  +tt: M1.Tr,
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
) -> {M1.at(pxT(left, tt, x0, ay, px, ww, hh, vv), (yy * ww + xx : U32)) == M1.after(Bool.and(Laws.jpg.span(left, x0,
    px,
  xx), U32.is_eq(ay, yy)), vv, M1.at(tt, (yy * ww + xx : U32))) : U32}:
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
        hd, hfit, hx, hy) : {M1.at(pxT(pp, t1, x0, ay, (px + 1 : U32), ww, hh, vv), kk) == M1.after(Bool.and(rr, ey),
            vv,
        M1.at(t1, kk)) : U32}}
      +e1 = {rd_in(xin, yin, dd, tt, ax, ay, ww, hh, xx, yy, vv, {==}, {==}, hp, hd, hfit, hx, hy) : {M1.at(t1, kk) ==
        M1.after(Bool.and(hr, ey), vv, M1.at(tt, kk)) : U32}}
      Equal.trans(U32, M1.at(pxT(pp, t1, x0, ay, (px + 1 : U32), ww, hh, vv), kk), M1.after(Bool.and(rr, ey), vv,
          M1.at(t1, kk)),
        M1.after(Bool.and(Bool.or(hr, rr), ey), vv, M1.at(tt, kk)), ih, Equal.trans(U32, M1.after(Bool.and(rr, ey), vv,
            M1.at(t1,
        kk)), M1.after(Bool.and(rr, ey), vv, M1.after(Bool.and(hr, ey), vv, M1.at(tt, kk))),
            M1.after(Bool.and(Bool.or(hr, rr),
        ey), vv, M1.at(tt, kk)), Equal.cong(U32, U32, oo => M1.after(Bool.and(rr, ey), vv, oo), M1.at(t1, kk),
        M1.after(Bool.and(hr, ey), vv, M1.at(tt, kk)), e1), ba1(hr, rr, ey, vv, M1.at(tt, kk))))

# one sample's cover, read at pixel (x, y): the sample's value when its rows take in y and its columns x, else
# the old one
def rd_py(
  left: Nat,
  +dd: Nat,
  +tt: M1.Tr,
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
) -> {M1.at(pyT(left, tt, x0, y0, py, pw, ww, hh, vv),
  (yy * ww + xx : U32)) == M1.after(Bool.and(Laws.jpg.span(U32.to_nat(pw),
  x0, 0, xx), Laws.jpg.span(left, y0, py, yy)), vv, M1.at(tt, (yy * ww + xx : U32))) : U32}:
  match left:
    case 0n:
      +kk = (yy * ww + xx : U32)
      +sx = Laws.jpg.span(U32.to_nat(pw), x0, 0, xx)
      Equal.sym(U32, M1.after(Bool.and(sx, False{}), vv, M1.at(tt, kk)), M1.at(tt, kk), Equal.cong(Bool, U32,
          bb => M1.after(bb, vv,
        M1.at(tt, kk)), Bool.and(sx, False{}), False{}, M4.and_false_r(sx)))
    case 1n+(+pp):
      +kk = (yy * ww + xx : U32)
      +ay = (y0 + py : U32)
      +sx = Laws.jpg.span(U32.to_nat(pw), x0, 0, xx)
      +t1 = pxT(U32.to_nat(pw), tt, x0, ay, 0, ww, hh, vv)
      +hr = U32.is_eq(ay, yy)
      +rr = Laws.jpg.span(pp, y0, (py + 1 : U32), yy)
      +ih = {rd_py(pp, dd, t1, x0, y0, (py + 1 : U32), pw, ww, hh, vv, xx, yy, pf_px(U32.to_nat(pw), dd, tt, x0, ay, 0,
        ww, hh, vv, hp), hd, hfit, hx, hy) : {M1.at(pyT(pp, t1, x0, y0, (py + 1 : U32), pw, ww, hh, vv), kk) ==
        M1.after(Bool.and(sx, rr), vv, M1.at(t1, kk)) : U32}}
      +e1 = {rd_px(U32.to_nat(pw), dd, tt, x0, ay, 0, ww, hh, vv, xx, yy, hp, hd, hfit, hx, hy) : {M1.at(t1, kk) ==
        M1.after(Bool.and(sx, hr), vv, M1.at(tt, kk)) : U32}}
      Equal.trans(U32, M1.at(pyT(pp, t1, x0, y0, (py + 1 : U32), pw, ww, hh, vv), kk), M1.after(Bool.and(sx, rr), vv,
          M1.at(t1,
        kk)), M1.after(Bool.and(sx, Bool.or(hr, rr)), vv, M1.at(tt, kk)), ih, Equal.trans(U32, M1.after(Bool.and(sx,
            rr), vv,
        M1.at(t1, kk)), M1.after(Bool.and(sx, rr), vv, M1.after(Bool.and(sx, hr), vv, M1.at(tt, kk))),
            M1.after(Bool.and(sx,
        Bool.or(hr, rr)), vv, M1.at(tt, kk)), Equal.cong(U32, U32, oo => M1.after(Bool.and(sx, rr), vv, oo), M1.at(t1,
            kk),
        M1.after(Bool.and(sx, hr), vv, M1.at(tt, kk)), e1), ba2(sx, hr, rr, vv, M1.at(tt, kk))))

# a block row, read at pixel (x, y): jpg.blk.col
def rd_col(
  left: Nat,
  +dd: Nat,
  +tt: M1.Tr,
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
) -> {M1.at(colT(left, tt, samples, row, col, ox, oy, pw, ph, ww, hh), (yy * ww + xx : U32)) == Laws.jpg.blk.col(left,
  samples, row, col, ox, oy, pw, ph, xx, yy, M1.at(tt, (yy * ww + xx : U32))) : U32}:
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
        tt, x0, y0, 0, pw, ww, hh, vv, hp), hd, hfit, hx, hy) : {M1.at(colT(pp, t1, samples, row, (col + 1 : U32), ox,
        oy, pw, ph, ww, hh), kk) == Laws.jpg.blk.col(pp, samples, row, (col + 1 : U32), ox, oy, pw, ph, xx, yy,
            M1.at(t1,
        kk)) : U32}}
      +e1 = {rd_py(U32.to_nat(ph), dd, tt, x0, y0, 0, pw, ww, hh, vv, xx, yy, hp, hd, hfit, hx, hy) : {M1.at(t1, kk) ==
        M1.after(cv, vv, M1.at(tt, kk)) : U32}}
      Equal.trans(U32, M1.at(colT(pp, t1, samples, row, (col + 1 : U32), ox, oy, pw, ph, ww, hh), kk),
        Laws.jpg.blk.col(pp, samples, row, (col + 1 : U32), ox, oy, pw, ph, xx, yy, M1.at(t1, kk)),
        Laws.jpg.blk.col(pp, samples, row, (col + 1 : U32), ox, oy, pw, ph, xx, yy, M1.after(cv, vv, M1.at(tt, kk))),
            ih,
        Equal.cong(U32, U32, oo => Laws.jpg.blk.col(pp, samples, row, (col + 1 : U32), ox, oy, pw, ph, xx, yy, oo),
        M1.at(t1, kk), M1.after(cv, vv, M1.at(tt, kk)), e1))

# a block, read at pixel (x, y): jpg.blk
def rd_cv(
  left: Nat,
  +dd: Nat,
  +tt: M1.Tr,
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
) -> {M1.at(cvT(left, tt, samples, row, ox, oy, pw, ph, ww, hh), (yy * ww + xx : U32)) == Laws.jpg.blk(left, samples,
  row, ox, oy, pw, ph, xx, yy, M1.at(tt, (yy * ww + xx : U32))) : U32}:
  match left:
    case 0n:
      {==}
    case 1n+(+pp):
      +kk = (yy * ww + xx : U32)
      +t1 = colT(8n, tt, samples, row, 0, ox, oy, pw, ph, ww, hh)
      +bc = Laws.jpg.blk.col(8n, samples, row, 0, ox, oy, pw, ph, xx, yy, M1.at(tt, kk))
      +ih = {rd_cv(pp, dd, t1, samples, (row + 1 : U32), ox, oy, pw, ph, ww, hh, xx, yy, pf_col(8n, dd, tt, samples,
        row, 0, ox, oy, pw, ph, ww, hh, hp), hd, hfit, hx, hy) : {M1.at(cvT(pp, t1, samples, (row + 1 : U32), ox, oy,
            pw,
        ph, ww, hh), kk) == Laws.jpg.blk(pp, samples, (row + 1 : U32), ox, oy, pw, ph, xx, yy, M1.at(t1, kk)) : U32}}
      Equal.trans(U32, M1.at(cvT(pp, t1, samples, (row + 1 : U32), ox, oy, pw, ph, ww, hh), kk), Laws.jpg.blk(pp,
          samples,
        (row + 1 : U32), ox, oy, pw, ph, xx, yy, M1.at(t1, kk)), Laws.jpg.blk(pp, samples, (row + 1 : U32), ox, oy, pw,
            ph,
        xx, yy, bc), ih, Equal.cong(U32, U32, oo => Laws.jpg.blk(pp, samples, (row + 1 : U32), ox, oy, pw, ph, xx, yy,
        oo), M1.at(t1, kk), bc, rd_col(8n, dd, tt, samples, row, 0, ox, oy, pw, ph, ww, hh, xx, yy, hp, hd, hfit, hx,
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
  oo: M1.Of(plane)
) -> {D1.jpg.val(Array.get(U32, Jpeg.decode.paint.use(Jpeg.Geom{ox, oy, pw, ph, ww, hh}, True{}, samples, plane),
  (yy * ww + xx : U32))) == Laws.jpg.block.at(Jpeg.Geom{ox, oy, pw, ph, ww, hh}, samples, xx, yy,
  D1.jpg.val(Array.get(U32, plane, (yy * ww + xx : U32)))) : U32}:
  (+tt, ep) = oo
  +sp = {Equal.sym(Array<U32>, plane, M1.arr(tt), ep) : {M1.arr(tt) == plane : Array<U32>}}
  +hp = pf_of(dd, plane, tt, Equal.sym(Array<U32>, M1.arr(tt), plane, sp), h_perfect)
  +kk = (yy * ww + xx : U32)
  +cv = cvT(8n, tt, samples, 0, ox, oy, pw, ph, ww, hh)
  %sp : {D1.jpg.val(Array.get(U32, Jpeg.decode.paint.use(Jpeg.Geom{ox, oy, pw, ph, ww, hh}, True{}, samples, _),
    kk)) == Laws.jpg.block.at(Jpeg.Geom{ox, oy, pw, ph, ww, hh}, samples, xx, yy, D1.jpg.val(Array.get(U32, _, kk))) :
    U32}
  Equal.trans(U32, D1.jpg.val(Array.get(U32, Jpeg.decode.splat(8n, M1.arr(tt), samples, 0, ox, oy, pw, ph, ww, hh),
      kk)),
    D1.jpg.val(Array.get(U32, M1.arr(cv), kk)), Laws.jpg.blk(8n, samples, 0, ox, oy, pw, ph, xx, yy,
    D1.jpg.val(Array.get(U32, M1.arr(tt), kk))), Equal.cong(Array<U32>, U32, aa => D1.jpg.val(Array.get(U32, aa, kk)),
    Jpeg.decode.splat(8n, M1.arr(tt), samples, 0, ox, oy, pw, ph, ww, hh), M1.arr(cv), arr_cv(8n, tt, samples, 0, ox,
        oy,
    pw, ph, ww, hh)), Equal.trans(U32, D1.jpg.val(Array.get(U32, M1.arr(cv), kk)), M1.at(cv, kk), Laws.jpg.blk(8n,
    samples, 0, ox, oy, pw, ph, xx, yy, D1.jpg.val(Array.get(U32, M1.arr(tt), kk))), val_at(cv, kk), Equal.trans(U32,
    M1.at(cv, kk), Laws.jpg.blk(8n, samples, 0, ox, oy, pw, ph, xx, yy, M1.at(tt, kk)), Laws.jpg.blk(8n, samples, 0,
        ox, oy,
    pw, ph, xx, yy, D1.jpg.val(Array.get(U32, M1.arr(tt), kk))), rd_cv(8n, dd, tt, samples, 0, ox, oy, pw, ph, ww, hh,
    xx, yy, hp, h_dd, h_fit, h_xx, h_yy), Equal.cong(U32, U32, oo2 => Laws.jpg.blk(8n, samples, 0, ox, oy, pw, ph, xx,
    yy, oo2), M1.at(tt, kk), D1.jpg.val(Array.get(U32, M1.arr(tt), kk)), Equal.sym(U32, D1.jpg.val(Array.get(U32,
        M1.arr(tt),
    kk)), M1.at(tt, kk), val_at(tt, kk))))))

# a bit plus a double is at least the halved number
def half_le(+bb: Bool, +xx: Nat) -> {Nat.is_le(xx, Nat.add(M1.bit(bb), Nat.double(xx))) == True{} : Bool}:
  match bb:
    case False{}:
      M1.le_rw_r(xx, Nat.add(xx, xx), Nat.double(xx), Equal.sym(Nat, Nat.double(xx), Nat.add(xx, xx),
          M1.double_add(xx)),
        M4.le_add_more(xx, xx, xx, M1.le_refl(xx)))
    case True{}:
      M1.le_trans(xx, Nat.double(xx), 1n+Nat.double(xx), M1.le_rw_r(xx, Nat.add(xx, xx), Nat.double(xx), Equal.sym(Nat,
        Nat.double(xx), Nat.add(xx, xx), M1.double_add(xx)), M4.le_add_more(xx, xx, xx, M1.le_refl(xx))),
        M4.le_succ(Nat.double(xx)))

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
      Empty.absurd({0n == yy : Nat}, M1.false_true(h2))
    case 1n+_pp 0n:
      Empty.absurd({xx == 0n : Nat}, M1.false_true(h1))
    case 1n+pp 1n+qq:
      Equal.cong(Nat, Nat, nn => 1n+nn, pp, qq, le_anti(pp, qq, h1, h2))

# one more than a number is not at most it
def succ_nle(+xx: Nat) -> {Nat.is_le(1n+xx, xx) == False{} : Bool}:
  match xx:
    case 0n:
      {==}
    case 1n+pp:
      succ_nle(pp)

# a walk count at most 31 is below 32
def lt32(+dd: Nat, +hh: {Nat.is_le(dd, 31n) == True{} : Bool}) -> {Nat.is_lt(dd, 32n) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_lt(dd, 32n), Nat.is_le(1n+dd, 32n), True{}, M1.lt_le_succ(dd, 32n), hh)

# a number not equal to zero is above zero
def nz_lt(+nn: Nat, +hh: {Bool.not(Nat.is_eq(nn, 0n)) == True{} : Bool}) -> {Nat.is_lt(0n, nn) == True{} : Bool}:
  match nn:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, M1.false_true(hh))
    case 1n+_pp:
      {==}

# a U32 not equal to zero is above zero
def ne_pos(+xx: U32, +hh: {U32.is_ne(xx, 0) == True{} : Bool}) -> {Nat.is_lt(0n, U32.to_nat(xx)) == True{} : Bool}:
  nz_lt(U32.to_nat(xx), Equal.trans(Bool, Bool.not(Nat.is_eq(U32.to_nat(xx), 0n)), Bool.not(U32.is_eq(xx, 0)), True{},
    Equal.cong(Bool, Bool, bb => Bool.not(bb), Nat.is_eq(U32.to_nat(xx), 0n), U32.is_eq(xx, 0), Equal.sym(Bool,
    U32.is_eq(xx, 0), Nat.is_eq(U32.to_nat(xx), 0n), M1.u32_eq(xx, 0))), hh))

# a U32 whose s-fold shift right is not zero is at least 2^s, split on whether it is below 2^s
def ge_case(
  ww: Bool,
  +ss: Nat,
  +nn: U32,
  +ew: {Nat.is_lt(U32.to_nat(nn), Nat.pow(2n, ss)) == ww : Bool},
  +ez: {U32.is_ne(U32.shrn(nn, ss), 0) == True{} : Bool}
) -> {Nat.is_le(Nat.pow(2n, ss), U32.to_nat(nn)) == True{} : Bool}:
  match ww:
    case False{}:
      M3.not_lt_le(U32.to_nat(nn), Nat.pow(2n, ss), ew)
    case True{}:
      +h0 = {M1.shrn_dn(ss, nn, 0n, M1.lt_rw_r(U32.to_nat(nn), Nat.pow(2n, ss), Nat.pow(2n, Nat.add(ss, 0n)),
        Equal.cong(Nat, Nat, xx => Nat.pow(2n, xx), ss, Nat.add(ss, 0n), Equal.sym(Nat, Nat.add(ss, 0n), ss,
        M1.ras.add_zero(ss))), ew)) : {Nat.is_lt(U32.to_nat(U32.shrn(nn, ss)), 1n) == True{} : Bool}}
      +h1 = {Equal.trans(Bool, Nat.is_le(1n, U32.to_nat(U32.shrn(nn, ss))), Nat.is_lt(0n, U32.to_nat(U32.shrn(nn,
        ss))), True{}, Equal.sym(Bool, Nat.is_lt(0n, U32.to_nat(U32.shrn(nn, ss))), Nat.is_le(1n,
        U32.to_nat(U32.shrn(nn, ss))), M1.lt_le_succ(0n, U32.to_nat(U32.shrn(nn, ss)))), ne_pos(U32.shrn(nn, ss), ez)) :
        {Nat.is_le(1n, U32.to_nat(U32.shrn(nn, ss))) == True{} : Bool}}
      Empty.absurd({Nat.is_le(Nat.pow(2n, ss), U32.to_nat(nn)) == True{} : Bool}, M1.false_true(Equal.trans(Bool,
        False{}, Nat.is_lt(1n, 1n), True{}, {==}, M1.le_lt_trans(1n, U32.to_nat(U32.shrn(nn, ss)), 1n, h1, h0))))

# two to a power below two to another: the power is below the other
def pow_lt_rev(
  ww: Bool,
  +aa: Nat,
  +bb: Nat,
  +ew: {Nat.is_lt(aa, bb) == ww : Bool},
  +hh: {Nat.is_lt(Nat.pow(2n, aa), Nat.pow(2n, bb)) == True{} : Bool}
) -> {Nat.is_lt(aa, bb) == True{} : Bool}:
  match ww:
    case True{}:
      ew
    case False{}:
      +hb = {M1.le_lt_trans(Nat.pow(2n, bb), Nat.pow(2n, aa), Nat.pow(2n, bb), M1.pow_le(bb, aa, M3.not_lt_le(aa, bb,
          ew)),
        hh) : {Nat.is_lt(Nat.pow(2n, bb), Nat.pow(2n, bb)) == True{} : Bool}}
      Empty.absurd({Nat.is_lt(aa, bb) == True{} : Bool}, M1.false_true(Equal.trans(Bool, False{},
        Nat.is_lt(Nat.pow(2n, bb), Nat.pow(2n, bb)), True{}, Equal.trans(Bool, False{}, Nat.is_le(1n+Nat.pow(2n, bb),
        Nat.pow(2n, bb)), Nat.is_lt(Nat.pow(2n, bb), Nat.pow(2n, bb)), Equal.sym(Bool, Nat.is_le(1n+Nat.pow(2n, bb),
        Nat.pow(2n, bb)), False{}, succ_nle(Nat.pow(2n, bb))), Equal.sym(Bool, Nat.is_lt(Nat.pow(2n, bb), Nat.pow(2n,
        bb)), Nat.is_le(1n+Nat.pow(2n, bb), Nat.pow(2n, bb)), M1.lt_le_succ(Nat.pow(2n, bb), Nat.pow(2n, bb)))), hb)))

# a U32 below 2^(1+e) whose shift right by the step width is not zero: the width is at most e
def sw_le(
  +pp: Nat,
  +ee: Nat,
  +nn: U32,
  +ez: {U32.is_ne(U32.shrn(nn, M1.sw(pp)), 0) == True{} : Bool},
  +hn: {Nat.is_lt(U32.to_nat(nn), Nat.pow(2n, 1n+ee)) == True{} : Bool}
) -> {Nat.is_le(M1.sw(pp), ee) == True{} : Bool}:
  +hp = {M1.le_lt_trans(Nat.pow(2n, M1.sw(pp)), U32.to_nat(nn), Nat.pow(2n, 1n+ee), ge_case(Nat.is_lt(U32.to_nat(nn),
    Nat.pow(2n, M1.sw(pp))), M1.sw(pp), nn, {==}, ez), hn) : {Nat.is_lt(Nat.pow(2n, M1.sw(pp)), Nat.pow(2n,
        1n+ee)) == True{} :
    Bool}}
  Equal.trans(Bool, Nat.is_le(1n+M1.sw(pp), 1n+ee), Nat.is_lt(M1.sw(pp), 1n+ee), True{}, Equal.sym(Bool,
      Nat.is_lt(M1.sw(pp),
    1n+ee), Nat.is_le(1n+M1.sw(pp), 1n+ee), M1.lt_le_succ(M1.sw(pp), 1n+ee)), pow_lt_rev(Nat.is_lt(M1.sw(pp), 1n+ee),
        M1.sw(pp),
    1n+ee, {==}, hp))

# the bound the log2 walk's next step needs, for the upper bound: below 2^(1+e) less the shift
def up_hyp(
  zz: Bool,
  +pp: Nat,
  +ee: Nat,
  +nn: U32,
  +ez: {U32.is_ne(U32.shrn(nn, M1.sw(pp)), 0) == zz : Bool},
  +hn: {Nat.is_lt(U32.to_nat(nn), Nat.pow(2n, 1n+ee)) == True{} : Bool}
) -> {Nat.is_lt(U32.to_nat(U32.shrn(nn, Bool.pick(Nat, zz, M1.sw(pp), 0n))), Nat.pow(2n, 1n+Bool.pick(Nat, zz,
  Nat.sub(ee, M1.sw(pp)), ee))) == True{} : Bool}:
  match zz:
    case False{}:
      hn
    case True{}:
      +ss = M1.sw(pp)
      +dd = Nat.sub(ee, ss)
      +ea = {M4.add_sub(ss, ee, sw_le(pp, ee, nn, ez, hn)) : {Nat.add(ss, dd) == ee : Nat}}
      +eb = {Equal.trans(Nat, 1n+ee, 1n+Nat.add(ss, dd), Nat.add(ss, 1n+dd), Equal.cong(Nat, Nat, xx => 1n+xx, ee,
        Nat.add(ss, dd), Equal.sym(Nat, Nat.add(ss, dd), ee, ea)), Equal.sym(Nat, Nat.add(ss, 1n+dd), 1n+Nat.add(ss,
        dd), M1.ras.add_succ(ss, dd))) : {1n+ee == Nat.add(ss, 1n+dd) : Nat}}
      M1.shrn_dn(ss, nn, 1n+dd, M1.lt_rw_r(U32.to_nat(nn), Nat.pow(2n, 1n+ee), Nat.pow(2n, Nat.add(ss, 1n+dd)),
        Equal.cong(Nat, Nat, xx => Nat.pow(2n, xx), 1n+ee, Nat.add(ss, 1n+dd), eb), hn))

# the count and bound after the log2 walk's step fit the bound before it
def up_fin(
  zz: Bool,
  +pp: Nat,
  +ee: Nat,
  +nn: U32,
  +bb: Nat,
  +ez: {U32.is_ne(U32.shrn(nn, M1.sw(pp)), 0) == zz : Bool},
  +hn: {Nat.is_lt(U32.to_nat(nn), Nat.pow(2n, 1n+ee)) == True{} : Bool}
) -> {Nat.is_le(Nat.add(Nat.add(bb, Bool.pick(Nat, zz, M1.sw(pp), 0n)), Bool.pick(Nat, zz, Nat.sub(ee, M1.sw(pp)), ee)),
  Nat.add(bb, ee)) == True{} : Bool}:
  match zz:
    case False{}:
      M1.le_rw_l(Nat.add(bb, ee), Nat.add(Nat.add(bb, 0n), ee), Nat.add(bb, ee), Equal.cong(Nat, Nat, xx => Nat.add(xx,
        ee), bb, Nat.add(bb, 0n), Equal.sym(Nat, Nat.add(bb, 0n), bb, M1.ras.add_zero(bb))), M1.le_refl(Nat.add(bb,
            ee)))
    case True{}:
      +ss = M1.sw(pp)
      +dd = Nat.sub(ee, ss)
      +ea = {Equal.trans(Nat, Nat.add(Nat.add(bb, ss), dd), Nat.add(bb, Nat.add(ss, dd)), Nat.add(bb, ee),
        M1.ras.add_assoc(bb, ss, dd), Equal.cong(Nat, Nat, xx => Nat.add(bb, xx), Nat.add(ss, dd), ee, M4.add_sub(ss,
            ee,
        sw_le(pp, ee, nn, ez, hn)))) : {Nat.add(Nat.add(bb, ss), dd) == Nat.add(bb, ee) : Nat}}
      M1.le_rw_l(Nat.add(bb, ee), Nat.add(Nat.add(bb, ss), dd), Nat.add(bb, ee), Equal.sym(Nat, Nat.add(Nat.add(bb, ss),
        dd), Nat.add(bb, ee), ea), M1.le_refl(Nat.add(bb, ee)))

# the log2 walk counts at most e more of a number below 2^(1+e)
def pln.up(
  +kk: Nat,
  +ee: Nat,
  +nn: U32,
  +bb: Nat,
  +hn: {Nat.is_lt(U32.to_nat(nn), Nat.pow(2n, 1n+ee)) == True{} : Bool}
) -> {Nat.is_le(U32.log2.go(kk, nn, bb), Nat.add(bb, ee)) == True{} : Bool}:
  match kk:
    case 0n:
      M4.le_add_more(bb, bb, ee, M1.le_refl(bb))
    case 1n+pp:
      +zz = U32.is_ne(U32.shrn(nn, M1.sw(pp)), 0)
      +tt = M1.sp(pp, nn)
      +e1 = Bool.pick(Nat, zz, Nat.sub(ee, M1.sw(pp)), ee)
      +ih = {pln.up(pp, e1, U32.shrn(nn, tt), Nat.add(bb, tt), up_hyp(zz, pp, ee, nn, {==}, hn)) :
        {Nat.is_le(U32.log2.go(pp, U32.shrn(nn, tt), Nat.add(bb, tt)), Nat.add(Nat.add(bb, tt), e1)) == True{} : Bool}}
      M1.le_rw_l(U32.log2.go(pp, U32.shrn(nn, tt), Nat.add(bb, tt)), U32.log2.go(1n+pp, nn, bb), Nat.add(bb, ee),
        Equal.sym(Nat, U32.log2.go(1n+pp, nn, bb), U32.log2.go(pp, U32.shrn(nn, tt), Nat.add(bb, tt)), M1.go_z(pp, nn,
        bb)), M1.le_trans(U32.log2.go(pp, U32.shrn(nn, tt), Nat.add(bb, tt)), Nat.add(Nat.add(bb, tt), e1),
        Nat.add(bb, ee), ih, up_fin(zz, pp, ee, nn, bb, {==}, hn)))

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
  +es = {M1.shl_u(nn, ee, hlt, he) : {U32.to_nat(sh) == n2 : Nat}}
  +h1 = {M1.le_rw_r(1n, n2, U32.to_nat(sh), Equal.sym(Nat, U32.to_nat(sh), n2, es), M1.le_trans(1n, U32.to_nat(nn), n2,
    Equal.trans(Bool, Nat.is_le(1n, U32.to_nat(nn)), Nat.is_lt(0n, U32.to_nat(nn)), True{}, Equal.sym(Bool,
    Nat.is_lt(0n, U32.to_nat(nn)), Nat.is_le(1n, U32.to_nat(nn)), M1.lt_le_succ(0n, U32.to_nat(nn))), hpos),
    half_le(False{}, U32.to_nat(nn)))) : {Nat.is_le(1n, U32.to_nat(sh)) == True{} : Bool}}
  +em = {Equal.trans(Nat, U32.to_nat(mm), Nat.sub(U32.to_nat(sh), 1n), Nat.sub(n2, 1n), M4.ras.u32_sub_nat(sh, 1, h1),
    Equal.cong(Nat, Nat, xx => Nat.sub(xx, 1n), U32.to_nat(sh), n2, es)) : {U32.to_nat(mm) == Nat.sub(n2, 1n) : Nat}}
  +h1n = {M1.le_rw_r(1n, U32.to_nat(sh), n2, es, h1) : {Nat.is_le(1n, n2) == True{} : Bool}}
  +hm = {M1.lt_rw_l(Nat.sub(n2, 1n), U32.to_nat(mm), Nat.pow(2n, 1n+ee), Equal.sym(Nat, U32.to_nat(mm), Nat.sub(n2, 1n),
    em), M1.le_lt_trans(Nat.sub(n2, 1n), n2, Nat.pow(2n, 1n+ee), M2.sub_le(n2, 1n), M1.lt_rw_r(n2,
    Nat.double(Nat.pow(2n, ee)), Nat.pow(2n, 1n+ee), Equal.sym(Nat, Nat.pow(2n, 1n+ee), Nat.double(Nat.pow(2n, ee)),
    M1.pow2_succ(ee)), M1.dbl_lt(U32.to_nat(nn), Nat.pow(2n, ee), hlt)))) : {Nat.is_lt(U32.to_nat(mm), Nat.pow(2n,
    1n+ee)) ==
    True{} : Bool}}
  +hd = {pln.up(5n, ee, mm, 0n, hm) : {Nat.is_le(dd, ee) == True{} : Bool}}
  +hup = {M1.lo(5n, 1n+ee, mm, {==}, he, hm) : {Nat.is_lt(U32.to_nat(mm), Nat.pow(2n, 1n+dd)) == True{} : Bool}}
  +hup2 = {M1.lt_rw_r(Nat.sub(n2, 1n), Nat.pow(2n, 1n+dd), Nat.double(Nat.pow(2n, dd)), M1.pow2_succ(dd), M1.lt_rw_l(
    U32.to_nat(mm), Nat.sub(n2, 1n), Nat.pow(2n, 1n+dd), em, hup)) : {Nat.is_lt(Nat.sub(n2, 1n), Nat.double(Nat.pow(2n,
    dd))) == True{} : Bool}}
  +h3 = {M1.le_rw_l(Nat.add(1n, Nat.sub(n2, 1n)), n2, Nat.double(Nat.pow(2n, dd)), M4.add_sub(1n, n2, h1n),
    Equal.trans(Bool, Nat.is_le(1n+Nat.sub(n2, 1n), Nat.double(Nat.pow(2n, dd))), Nat.is_lt(Nat.sub(n2, 1n),
    Nat.double(Nat.pow(2n, dd))), True{}, Equal.sym(Bool, Nat.is_lt(Nat.sub(n2, 1n), Nat.double(Nat.pow(2n, dd))),
    Nat.is_le(1n+Nat.sub(n2, 1n), Nat.double(Nat.pow(2n, dd))), M1.lt_le_succ(Nat.sub(n2, 1n), Nat.double(Nat.pow(2n,
    dd)))), hup2)) : {Nat.is_le(n2, Nat.double(Nat.pow(2n, dd))) == True{} : Bool}}
  +hn = {M4.le_half(False{}, U32.to_nat(nn), Nat.pow(2n, dd), h3) : {Nat.is_le(U32.to_nat(nn), Nat.pow(2n, dd)) ==
    True{} : Bool}}
  Equal.trans(Bool, Bool.and(Nat.is_le(dd, ee), Nat.is_le(U32.to_nat(nn), Nat.pow(2n, dd))), Bool.and(True{},
    Nat.is_le(U32.to_nat(nn), Nat.pow(2n, dd))), True{}, Equal.cong(Bool, Bool, bb => Bool.and(bb,
    Nat.is_le(U32.to_nat(nn), Nat.pow(2n, dd))), Nat.is_le(dd, ee), True{}, hd), hn)

# U32s of one number are one U32
def u32_nat_eq(+aa: U32, +bb: U32, +ee: {U32.to_nat(aa) == U32.to_nat(bb) : Nat}) -> {aa == bb : U32}:
  M1.ueq(aa, bb, Equal.trans(Bool, U32.is_eq(aa, bb), Nat.is_eq(U32.to_nat(aa), U32.to_nat(bb)), True{},
    M1.u32_eq(aa, bb), Equal.trans(Bool, Nat.is_eq(U32.to_nat(aa), U32.to_nat(bb)), Nat.is_eq(U32.to_nat(bb),
    U32.to_nat(bb)), True{}, Equal.cong(Nat, Bool, xx => Nat.is_eq(xx, U32.to_nat(bb)), U32.to_nat(aa), U32.to_nat(bb),
    ee), M1.nat_eq_refl(U32.to_nat(bb)))))

# the plane's depth is below 32 when it is at most e and e at most 31, and 2^depth is at least nn
def dep_fin(
  +ll: Nat,
  +ee: Nat,
  +nn: U32,
  +he: {Nat.is_le(ee, 31n) == True{} : Bool},
  +hh: {Bool.and(Nat.is_le(ll, ee), Nat.is_le(U32.to_nat(nn), Nat.pow(2n, ll))) == True{} : Bool}
) -> {Bool.and(Nat.is_lt(ll, 32n), Nat.is_le(U32.to_nat(nn), Nat.pow(2n, ll))) == True{} : Bool}:
  +hl = {M1.and_left(Nat.is_le(ll, ee), Nat.is_le(U32.to_nat(nn), Nat.pow(2n, ll)), hh) : {Nat.is_le(ll, ee) ==
    True{} : Bool}}
  +hn = {M1.and_right(Nat.is_le(ll, ee), Nat.is_le(U32.to_nat(nn), Nat.pow(2n, ll)), hh) : {Nat.is_le(U32.to_nat(nn),
    Nat.pow(2n, ll)) == True{} : Bool}}
  Equal.trans(Bool, Bool.and(Nat.is_lt(ll, 32n), Nat.is_le(U32.to_nat(nn), Nat.pow(2n, ll))), Bool.and(True{},
    Nat.is_le(U32.to_nat(nn), Nat.pow(2n, ll))), True{}, Equal.cong(Bool, Bool, bb => Bool.and(bb,
    Nat.is_le(U32.to_nat(nn), Nat.pow(2n, ll))), Nat.is_lt(ll, 32n), True{}, lt32(ll, M1.le_trans(ll, ee, 31n, hl,
        he))),
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
        Nat.is_le(1n+dd, 31n), M1.lt_le_succ(dd, 31n)), ez) : {Nat.is_le(1n+dd, 31n) == True{} : Bool}}
      +h2 = {M1.lt_rw_l(pw, U32.to_nat(nn), Nat.pow(2n, 1n+dd), Equal.sym(Nat, U32.to_nat(nn), pw, hq), M1.lt_rw_r(pw,
        Nat.double(pw), Nat.pow(2n, 1n+dd), Equal.sym(Nat, Nat.pow(2n, 1n+dd), Nat.double(pw), M1.pow2_succ(dd)),
        M1.lt_dbl(pw, M1.pow_pos(dd)))) : {Nat.is_lt(U32.to_nat(nn), Nat.pow(2n, 1n+dd)) == True{} : Bool}}
      dep_fin(U32.log2((U32.shl(nn) - 1 : U32)), 1n+dd, nn, h1, dep_a(nn, 1n+dd, hpos, h1, h2))
    case False{}:
      +d31 = {le_anti(dd, 31n, hdd, M3.not_lt_le(dd, 31n, ez)) : {dd == 31n : Nat}}
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
        Nat.is_le(U32.to_nat(nn), Nat.pow(2n, dd))), Nat.is_lt(dd, 32n), True{}, lt32(dd, hdd)), M1.le_rw_l(Nat.pow(2n,
        dd), U32.to_nat(nn), Nat.pow(2n, dd), Equal.sym(Nat, U32.to_nat(nn), Nat.pow(2n, dd), hq),
            M1.le_refl(Nat.pow(2n,
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
        M3.not_lt_le(U32.to_nat(nn), Nat.pow(2n, dd), ez)))

# the depth decode.plane takes for nn points, 1 to 2^d, d at most 31: below 32, and 2^depth at least nn
def dep(
  +nn: U32,
  +dd: Nat,
  +hpos: {Nat.is_lt(0n, U32.to_nat(nn)) == True{} : Bool},
  +hdd: {Nat.is_le(dd, 31n) == True{} : Bool},
  +hnn: {Nat.is_le(U32.to_nat(nn), Nat.pow(2n, dd)) == True{} : Bool}
) -> {Bool.and(Nat.is_lt(Jpeg.decode.depth(nn), 32n), Nat.is_le(U32.to_nat(nn), Nat.pow(2n, Jpeg.decode.depth(nn)))) ==
  True{} : Bool}:
  +e0 = {Equal.trans(Bool, U32.is_eq(nn, 0), Nat.is_eq(U32.to_nat(nn), 0n), False{}, M1.u32_eq(nn, 0),
    gt_neq(U32.to_nat(nn),
    0n, hpos)) : {U32.is_eq(nn, 0) == False{} : Bool}}
  +se = Equal.sym(Bool, U32.is_eq(nn, 0), False{}, e0)
  %se : {Bool.and(Nat.is_lt(Jpeg.decode.depth.of(_, nn), 32n), Nat.is_le(U32.to_nat(nn), Nat.pow(2n,
    Jpeg.decode.depth.of(_, nn)))) == True{} : Bool}
  dep_lt(Nat.is_lt(U32.to_nat(nn), Nat.pow(2n, dd)), nn, dd, {==}, hpos, hdd, hnn)

# Array.new is the array of that tree
def new_arr(+dd: Nat, +vv: U32) -> {Array.new(U32, dd, vv) == M1.arr(M1.full(dd, vv)) : Array<U32>}:
  match dd:
    case 0n:
      {==}
    case 1n+ee:
      ee1 = Equal.sym(Array<U32>, Array.new(U32, ee, vv), M1.arr(M1.full(ee, vv)), new_arr(ee, vv))
      ee2 = Equal.sym(Array<U32>, Array.new(U32, ee, vv), M1.arr(M1.full(ee, vv)), new_arr(ee, vv))
      %ee1 : {ANode{_, Array.new(U32, ee, vv)} == ANode{M1.arr(M1.full(ee, vv)), M1.arr(M1.full(ee, vv))} : Array<U32>}
      %ee2 : {ANode{M1.arr(M1.full(ee, vv)), _} == ANode{M1.arr(M1.full(ee, vv)), M1.arr(M1.full(ee, vv))} : Array<U32>}
      {==}

# that tree is perfect
def pf_full(+dd: Nat, +vv: U32) -> {pf(dd, M1.full(dd, vv)) == True{} : Bool}:
  match dd:
    case 0n:
      {==}
    case 1n+ee:
      +ih = pf_full(ee, vv)
      Equal.trans(Bool, Bool.and(pf(ee, M1.full(ee, vv)), pf(ee, M1.full(ee, vv))), Bool.and(True{}, pf(ee, M1.full(ee,
          vv))),
        True{}, Equal.cong(Bool, Bool, bb => Bool.and(bb, pf(ee, M1.full(ee, vv))), pf(ee, M1.full(ee, vv)), True{},
            ih), ih)

# a pick between one value and itself is the value
def pick_same(zz: Bool, +vv: U32) -> {Bool.pick(U32, zz, vv, vv) == vv : U32}:
  match zz:
    case True{}:
      {==}
    case False{}:
      {==}

# every read of that tree finds v
def get_full(+dd: Nat, +vv: U32, +nn: U32, +ii: U32) -> {M1.get(M1.full(dd, vv), nn, ii) == vv : U32}:
  match dd:
    case 0n:
      {==}
    case 1n+ee:
      +hh = U32.shr(nn)
      +el = get_full(ee, vv, hh, ii)
      +eh = get_full(ee, vv, hh, U32.sub(ii, hh))
      Equal.trans(U32, Bool.pick(U32, U32.is_lt(ii, hh), M1.get(M1.full(ee, vv), hh, ii), M1.get(M1.full(ee, vv), hh,
          U32.sub(ii,
        hh))), Bool.pick(U32, U32.is_lt(ii, hh), vv, M1.get(M1.full(ee, vv), hh, U32.sub(ii, hh))), vv, Equal.cong(U32,
            U32,
        xx => Bool.pick(U32, U32.is_lt(ii, hh), xx, M1.get(M1.full(ee, vv), hh, U32.sub(ii, hh))), M1.get(M1.full(ee,
            vv), hh, ii),
        vv, el), Equal.trans(U32, Bool.pick(U32, U32.is_lt(ii, hh), vv, M1.get(M1.full(ee, vv), hh, U32.sub(ii, hh))),
        Bool.pick(U32, U32.is_lt(ii, hh), vv, vv), vv, Equal.cong(U32, U32, xx => Bool.pick(U32, U32.is_lt(ii, hh), vv,
        xx), M1.get(M1.full(ee, vv), hh, U32.sub(ii, hh)), vv, eh), pick_same(U32.is_lt(ii, hh), vv)))

# a new plane is perfect
def plane_perfect(+nn: U32) -> {Laws.jpg.perfect(Jpeg.decode.depth(nn), Jpeg.decode.plane(nn)) == True{} : Bool}:
  +dd = Jpeg.decode.depth(nn)
  Equal.trans(Bool, Laws.jpg.perfect(dd, Array.new(U32, dd, 0)), Laws.jpg.perfect(dd, M1.arr(M1.full(dd, 0))), True{},
    Equal.cong(Array<U32>, Bool, aa => Laws.jpg.perfect(dd, aa), Array.new(U32, dd, 0), M1.arr(M1.full(dd, 0)),
        new_arr(dd,
    0)), Equal.trans(Bool, Laws.jpg.perfect(dd, M1.arr(M1.full(dd, 0))), pf(dd, M1.full(dd, 0)), True{},
        perfect_arr(dd, M1.full(dd,
    0)), pf_full(dd, 0)))

# every point of a new plane is 0
def plane_zero(+nn: U32, +kk: U32) -> {D1.jpg.val(Array.get(U32, Jpeg.decode.plane(nn), kk)) == 0 : U32}:
  +dd = Jpeg.decode.depth(nn)
  +tt = M1.full(dd, 0)
  Equal.trans(U32, D1.jpg.val(Array.get(U32, Array.new(U32, dd, 0), kk)), D1.jpg.val(Array.get(U32, M1.arr(tt), kk)),
    0, Equal.cong(Array<U32>, U32, aa => D1.jpg.val(Array.get(U32, aa, kk)), Array.new(U32, dd, 0), M1.arr(tt),
    new_arr(dd, 0)), Equal.trans(U32, D1.jpg.val(Array.get(U32, M1.arr(tt), kk)), M1.at(tt, kk), 0, val_at(tt, kk),
    get_full(dd, 0, M1.size(tt), M1.mask(kk, M1.size(tt)))))

# ---- the decoder's block run ----

# jpeg_blocks_paint: decode.blocks paints each unit it decodes where jpg.paint.all does, for any flag live the run is
# handed with blk
def blocks_paint(
  +left: Nat,
  +live: Bool,
  +blk: Jpeg.Blk,
  +ctrl: Jpeg.Ctrl,
  +preds: Jpeg.Preds,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ri: U32,
  +rgb: Bool,
  -yy: Array<U32>,
  -cb: Array<U32>,
  -cr: Array<U32>,
  +ok: U32
) -> {Jpeg.decode.blocks(left, live, blk, ctrl, preds, frame, scan, tabs, ri, rgb, yy, cb, cr, ok) ==
  Jpeg.decode.done(Laws.jpg.run.ok(left, live, blk, ctrl, preds, frame, scan, tabs, ri, ok), frame, rgb,
  Laws.jpg.paint.all(Laws.jpg.units.run(left, blk, ctrl, preds, frame, scan, tabs, ri), 0, frame, scan, yy),
  Laws.jpg.paint.all(Laws.jpg.units.run(left, blk, ctrl, preds, frame, scan, tabs, ri), 1, frame, scan, cb),
  Laws.jpg.paint.all(Laws.jpg.units.run(left, blk, ctrl, preds, frame, scan, tabs, ri), 2, frame, scan, cr)) :
  Maybe<&2, Jpeg.Pic>}:
  match left live blk ctrl frame scan:
    case 0n _live Jpeg.Blk{+_samples, +_bits, +_pred, +_bok} Jpeg.Ctrl{+_comp, +_bi, +_mx, +_my, +_mcu, +_rst}
      Jpeg.Frame{+_w, +_h, +_nf, +_ids, +_hs, +_vs, +_tq, +_hmax, +_vmax} Jpeg.Scan{+_ns, +_sids, +_td, +_ta, +_ss,
      +_se, +_ah}:
      {==}
    case 1n+_pp False{} _blk _ctrl _frame _scan:
      {==}
    case 1n+pp True{} Jpeg.Blk{+samples, +bits, +pred, +bok} Jpeg.Ctrl{+comp, +bi, +mx, +my, +mcu, +rst} Jpeg.Frame{+w,
      +h, +nf, +ids, +hs, +vs, +tq, +hmax, +vmax} Jpeg.Scan{+ns, +sids, +td, +ta, +ss, +se, +ah}:
      +cc = {Jpeg.Ctrl{comp, bi, mx, my, mcu, rst} : Jpeg.Ctrl}
      +fr = {Jpeg.Frame{w, h, nf, ids, hs, vs, tq, hmax, vmax} : Jpeg.Frame}
      +sc = {Jpeg.Scan{ns, sids, td, ta, ss, se, ah} : Jpeg.Scan}
      +gg = Jpeg.decode.geom(cc, fr, sc)
      +av = Jpeg.decode.adv(cc, fr, sc, ri)
      +nx = Jpeg.decode.block.next(bits, preds, pred, cc, fr, sc, tabs, ri)
      blocks_paint(pp, Jpeg.decode.blk.live(nx), nx, Jpeg.decode.adv.ctrl(av),
        Jpeg.decode.preds.next(Jpeg.decode.adv.duef(av), preds, comp, pred), fr, sc, tabs, ri, rgb,
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
def puT(which: Bool, +gg: Jpeg.Geom, +samples: List<&2, U32>, +tt: M1.Tr) -> M1.Tr:
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
  +tt: M1.Tr
) -> {Jpeg.decode.paint.use(gg, which, samples, M1.arr(tt)) == M1.arr(puT(which, gg, samples, tt)) : Array<U32>}:
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
  +tt: M1.Tr,
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
  +tt: M1.Tr,
  +xx: U32,
  +yy: U32,
  +hp: {pf(dd, tt) == True{} : Bool},
  +hd: {Nat.is_lt(dd, 32n) == True{} : Bool},
  +hfit: {Nat.is_le(Nat.mul(U32.to_nat(ww), U32.to_nat(hh)), Nat.pow(2n, dd)) == True{} : Bool},
  +hx: {U32.is_lt(xx, ww) == True{} : Bool},
  +hy: {U32.is_lt(yy, hh) == True{} : Bool}
) -> {M1.at(puT(which, Jpeg.Geom{ox, oy, pw, ph, ww, hh}, samples, tt), (yy * ww + xx : U32)) == Bool.pick(U32, which,
  Laws.jpg.block.at(Jpeg.Geom{ox, oy, pw, ph, ww, hh}, samples, xx, yy, M1.at(tt, (yy * ww + xx : U32))), M1.at(tt, (yy * ww +  # noqa: S002
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
  +tt: M1.Tr,
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
) -> {D1.jpg.val(Array.get(U32, Laws.jpg.paint.all(us, comp, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax},
  scan,
  M1.arr(tt)), (yy * ww + xx : U32))) == Laws.jpg.point(us, comp, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax},
  scan,
  xx, yy, M1.at(tt, (yy * ww + xx : U32))) : U32}:
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
      +ac = M1.at(tt, kk)
      +eg = {geom_eq(ctrl, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan) : {gg == g2 : Jpeg.Geom}}
      +e1 = {Equal.trans(Array<U32>, Jpeg.decode.paint.use(gg, wh, samples, M1.arr(tt)), Jpeg.decode.paint.use(g2, wh,
        samples, M1.arr(tt)), M1.arr(t1), Equal.cong(Jpeg.Geom, Array<U32>, qq => Jpeg.decode.paint.use(qq, wh, samples,
        M1.arr(tt)), gg, g2, eg), arr_pu(wh, g2, samples, tt)) : {Jpeg.decode.paint.use(gg, wh, samples, M1.arr(tt)) ==
        M1.arr(t1) : Array<U32>}}
      +e2 = {Equal.cong(Array<U32>, U32, aa => D1.jpg.val(Array.get(U32, Laws.jpg.paint.all(rest, comp, fr, scan, aa),
        kk)), Jpeg.decode.paint.use(gg, wh, samples, M1.arr(tt)), M1.arr(t1), e1) : {D1.jpg.val(Array.get(U32,
        Laws.jpg.paint.all(rest, comp, fr, scan, Jpeg.decode.paint.use(gg, wh, samples, M1.arr(tt))), kk)) ==
        D1.jpg.val(Array.get(U32, Laws.jpg.paint.all(rest, comp, fr, scan, M1.arr(t1)), kk)) : U32}}
      +ih = {plane_at_t(rest, comp, dd, t1, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan, xx, yy, pf_pu(wh, g2,
        samples,
        dd, tt, hp), hd, hfit, hx, hy) : {D1.jpg.val(Array.get(U32, Laws.jpg.paint.all(rest, comp, fr, scan,
            M1.arr(t1)),
        kk)) == Laws.jpg.point(rest, comp, fr, scan, xx, yy, M1.at(t1, kk)) : U32}}
      +e3 = {rd_pu(wh, g.ox(gg), g.oy(gg), g.pw(gg), g.ph(gg), ww, hh, samples, dd, tt, xx, yy, hp, hd, hfit, hx, hy) :
        {M1.at(t1, kk) == Bool.pick(U32, wh, Laws.jpg.block.at(g2, samples, xx, yy, ac), ac) : U32}}
      +e4 = {Equal.cong(Jpeg.Geom, U32, qq => Bool.pick(U32, wh, Laws.jpg.block.at(qq, samples, xx, yy, ac), ac), g2,
        gg,
        Equal.sym(Jpeg.Geom, gg, g2, eg)) : {Bool.pick(U32, wh, Laws.jpg.block.at(g2, samples, xx, yy, ac), ac) ==
        Bool.pick(U32, wh, Laws.jpg.block.at(gg, samples, xx, yy, ac), ac) : U32}}
      Equal.trans(U32, D1.jpg.val(Array.get(U32, Laws.jpg.paint.all(rest, comp, fr, scan, Jpeg.decode.paint.use(gg,
        wh,
        samples, M1.arr(tt))), kk)), D1.jpg.val(Array.get(U32, Laws.jpg.paint.all(rest, comp, fr, scan, M1.arr(t1)),
            kk)),
        Laws.jpg.point(rest, comp, fr, scan, xx, yy, Bool.pick(U32, wh, Laws.jpg.block.at(gg, samples, xx, yy, ac),
        ac)),
        e2, Equal.trans(U32, D1.jpg.val(Array.get(U32, Laws.jpg.paint.all(rest, comp, fr, scan, M1.arr(t1)), kk)),
        Laws.jpg.point(rest, comp, fr, scan, xx, yy, M1.at(t1, kk)), Laws.jpg.point(rest, comp, fr, scan, xx, yy,
        Bool.pick(U32, wh, Laws.jpg.block.at(gg, samples, xx, yy, ac), ac)), ih, Equal.cong(U32, U32,
        oo => Laws.jpg.point(rest, comp, fr, scan, xx, yy, oo), M1.at(t1, kk), Bool.pick(U32, wh, Laws.jpg.block.at(gg,
        samples, xx, yy, ac), ac), Equal.trans(U32, M1.at(t1, kk), Bool.pick(U32, wh, Laws.jpg.block.at(g2, samples, xx,
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
  oo: M1.Of(plane)
) -> {D1.jpg.val(Array.get(U32, Laws.jpg.paint.all(us, comp, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax},
  scan,
  plane), (yy * ww + xx : U32))) == Laws.jpg.point(us, comp, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan,
  xx, yy, D1.jpg.val(Array.get(U32, plane, (yy * ww + xx : U32)))) : U32}:
  (+tt, ep) = oo
  +sp = {Equal.sym(Array<U32>, plane, M1.arr(tt), ep) : {M1.arr(tt) == plane : Array<U32>}}
  +hp = pf_of(dd, plane, tt, Equal.sym(Array<U32>, M1.arr(tt), plane, sp), h_perfect)
  +fr = {Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax} : Jpeg.Frame}
  +kk = (yy * ww + xx : U32)
  %sp : {D1.jpg.val(Array.get(U32, Laws.jpg.paint.all(us, comp, fr, scan, _), kk)) == Laws.jpg.point(us, comp, fr,
    scan, xx, yy, D1.jpg.val(Array.get(U32, _, kk))) : U32}
  Equal.trans(U32, D1.jpg.val(Array.get(U32, Laws.jpg.paint.all(us, comp, fr, scan, M1.arr(tt)), kk)),
    Laws.jpg.point(us, comp, fr, scan, xx, yy, M1.at(tt, kk)), Laws.jpg.point(us, comp, fr, scan, xx, yy,
    D1.jpg.val(Array.get(U32, M1.arr(tt), kk))), plane_at_t(us, comp, dd, tt, ww, hh, nf, ids, hs, vs, tq, hmax, vmax,
    scan, xx, yy, hp, h_dd, h_fit, h_xx, h_yy), Equal.cong(U32, U32, oo2 => Laws.jpg.point(us, comp, fr, scan, xx, yy,
    oo2), M1.at(tt, kk), D1.jpg.val(Array.get(U32, M1.arr(tt), kk)), Equal.sym(U32, D1.jpg.val(Array.get(U32,
        M1.arr(tt),
    kk)), M1.at(tt, kk), val_at(tt, kk))))

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

# a refused frame is none whether or not a frame was read before it
def w8.none(
  ok1: Bool,
  +sc: Jpeg.Scan,
  +tb: Jpeg.Tabs,
  +en: List<&2, U32>,
  +ri: U32,
  +rgb: Bool
) -> {Img.decode_jpeg.out(Jpeg.decode.finish.ok(ok1, False{}, Jpeg.decode.frame0(), sc, tb, en, ri, rgb)) ==
  None{} : Maybe<&2, Img.Raster>}:
  match ok1:
    case False{}:
      {==}
    case True{}:
      {==}

# from where the prefix leaves the walk: a segment that stops the walk with
# the refusal flag set gives none, whatever follows it
def w8.tail(
  +pre: List<&2, U32>,
  +seg: List<&2, U32>,
  +mid: Jpeg.St,
  +rest: List<&2, U32>,
  +sc: Jpeg.Scan,
  +tb: Jpeg.Tabs,
  +en: List<&2, U32>,
  +ri: U32,
  +kd: U32,
  h_walk: {Jpeg.decode.walk(pre, Jpeg.decode.st0()) == mid : Jpeg.St},
  h_seg: {Jpeg.decode.walk(seg, mid) == Jpeg.decode.walk(rest, M1.w8.stop(sc, tb, en, ri, kd)) : Jpeg.St}
) -> {Img.decode_jpeg(List.append(&2, U32, pre, seg)) == None{} : Maybe<&2, Img.Raster>}:
  +stop = {M1.w8.stop(sc, tb, en, ri, kd) : Jpeg.St}
  +fx = Jpeg.decode.facts(List.append(&2, U32, pre, seg))
  Equal.trans(Maybe<&2, Img.Raster>, M2.w8.out(Jpeg.decode.walk(List.append(&2, U32, pre, seg), Jpeg.decode.st0()), fx),
    M2.w8.out(Jpeg.decode.walk(seg, Jpeg.decode.walk(pre, Jpeg.decode.st0())), fx), None{},
    Equal.cong(Jpeg.St, Maybe<&2, Img.Raster>, st => M2.w8.out(st, fx),
      Jpeg.decode.walk(List.append(&2, U32, pre, seg), Jpeg.decode.st0()),
      Jpeg.decode.walk(seg, Jpeg.decode.walk(pre, Jpeg.decode.st0())), M2.walk_app(pre, seg, Jpeg.decode.st0())),
    Equal.trans(Maybe<&2, Img.Raster>, M2.w8.out(Jpeg.decode.walk(seg, Jpeg.decode.walk(pre, Jpeg.decode.st0())), fx),
      M2.w8.out(Jpeg.decode.walk(seg, mid), fx), None{},
      Equal.cong(Jpeg.St, Maybe<&2, Img.Raster>, st => M2.w8.out(Jpeg.decode.walk(seg, st), fx),
        Jpeg.decode.walk(pre, Jpeg.decode.st0()), mid, h_walk),
      Equal.trans(Maybe<&2, Img.Raster>, M2.w8.out(Jpeg.decode.walk(seg, mid), fx), M2.w8.out(Jpeg.decode.walk(rest,
        stop), fx),
        None{},
        Equal.cong(Jpeg.St, Maybe<&2, Img.Raster>, st => M2.w8.out(st, fx), Jpeg.decode.walk(seg, mid),
          Jpeg.decode.walk(rest, stop), h_seg),
        Equal.trans(Maybe<&2, Img.Raster>, M2.w8.out(Jpeg.decode.walk(rest, stop), fx), M2.w8.out(stop, fx), None{},
          Equal.cong(Jpeg.St, Maybe<&2, Img.Raster>, st => M2.w8.out(st, fx), Jpeg.decode.walk(rest, stop), stop,
            walk_stop(rest, Jpeg.decode.frame0(), sc, tb, en, ri, kd, 1)),
          w8.none(Bool.and(U32.is_eq(kd, 1), Jpeg.decode.facts.soi(fx)), sc, tb, en, ri,
            Jpeg.decode.rgb.of(fx, Jpeg.decode.frame0()))))))

def Laws.jpeg_refuse_factor1(
  pre,
  frame,
  scan,
  tabs,
  ent,
  ri,
  kind,
  bad,
  h_walk,
  yh,
  yl,
  xh,
  xl,
  c1,
  f1,
  q1,
  h_fac,
  rest
):
  w8.tail(pre, 255 <> 192 <> 0 <> 11 <> 8 <> yh <> yl <> xh <> xl <> 1 <> c1 <> f1 <> q1 <> rest,
    Jpeg.St{Jpeg.Seek{}, frame, scan, tabs, ent, ri, kind, bad}, rest, scan, tabs, ent, ri, kind, h_walk,
    Equal.cong(Bool, Jpeg.St, ok => Jpeg.decode.walk(rest, Jpeg.decode.read.sof.c(ok, U32.is_eq(bad, 0), False{},
      Jpeg.decode.u16(xh, xl), Jpeg.decode.u16(yh, yl), 1, [c1], [1], [1], [q1], scan, tabs, ent, ri, kind)),
      Laws.jpg.facs4(f1), False{}, h_fac))

def Laws.jpeg_refuse_factor3(
  pre,
  frame,
  scan,
  tabs,
  ent,
  ri,
  kind,
  bad,
  h_walk,
  yh,
  yl,
  xh,
  xl,
  c1,
  f1,
  q1,
  c2,
  f2,
  q2,
  c3,
  f3,
  q3,
  h_fac,
  rest
):
  w8.tail(pre, 255 <> 192 <> 0 <> 17 <> 8 <> yh <> yl <> xh <> xl <> 3 <> c1 <> f1 <> q1 <> c2 <> f2 <> q2 <> c3 <>
    f3 <> q3 <> rest, Jpeg.St{Jpeg.Seek{}, frame, scan, tabs, ent, ri, kind, bad}, rest, scan, tabs, ent, ri, kind,
    h_walk,
    Equal.cong(Bool, Jpeg.St, ok => Jpeg.decode.walk(rest, Jpeg.decode.read.sof.c(ok,
      Bool.and(Jpeg.decode.nf.ok(3), U32.is_eq(bad, 0)),
      U32.is_eq(Jpeg.decode.vmax([U32.shrn(f1, 4n), U32.shrn(f2, 4n), U32.shrn(f3, 4n)], 0), 0),
      Jpeg.decode.u16(xh, xl), Jpeg.decode.u16(yh, yl), 3, [c1, c2, c3],
      [U32.shrn(f1, 4n), U32.shrn(f2, 4n), U32.shrn(f3, 4n)], [U32.and(f1, 15), U32.and(f2, 15), U32.and(f3, 15)],
      [q1, q2, q3], scan, tabs, ent, ri, kind)),
      Bool.and(Bool.and(Laws.jpg.facs(f1), Laws.jpg.facs(f2)), Laws.jpg.facs(f3)), False{}, h_fac))

# what jpeg_mcu_grid says for factors hi and vi
def w8.grid.ty(
  +hi: U32,
  +vi: U32,
  +mx: U32,
  +my: U32,
  +hmax: U32,
  +vmax: U32,
  +ww: U32,
  +hh: U32
) -> Type:
  {Laws.jpg.blocks(U32.to_nat((hi * vi : U32)), 0, hi, vi, mx, my, hmax, vmax, ww, hh) ==
    Laws.jpg.grid(U32.to_nat(vi), 0, hi, mx, my, hmax, vmax, U32.div(hmax, hi), U32.div(vmax, vi), ww, hh) :
    List<&2, Jpeg.Geom>}

# for one factor hi of 1, 2 or 4: every allowed vi, one concrete case each
def w8.grid.vi(
  +hi: U32,
  +vi: U32,
  +h_vi: {Laws.jpg.fac(vi) == True{} : Bool},
  +mx: U32,
  +my: U32,
  +hmax: U32,
  +vmax: U32,
  +ww: U32,
  +hh: U32,
  p1: w8.grid.ty(hi, 1, mx, my, hmax, vmax, ww, hh),
  p2: w8.grid.ty(hi, 2, mx, my, hmax, vmax, ww, hh),
  p4: w8.grid.ty(hi, 4, mx, my, hmax, vmax, ww, hh)
) -> w8.grid.ty(hi, vi, mx, my, hmax, vmax, ww, hh):
  fac_elim(vv => w8.grid.ty(hi, vv, mx, my, hmax, vmax, ww, hh), vi, U32.is_eq(vi, 1), {==}, h_vi, p1, p2, p4)

def Laws.jpeg_mcu_grid(hi, vi, h_hi, h_vi, mx, my, hmax, vmax, ww, hh):
  fac_elim(hv => w8.grid.ty(hv, vi, mx, my, hmax, vmax, ww, hh), hi, U32.is_eq(hi, 1), {==}, h_hi,
    w8.grid.vi(1, vi, h_vi, mx, my, hmax, vmax, ww, hh, {==}, {==}, {==}),
    w8.grid.vi(2, vi, h_vi, mx, my, hmax, vmax, ww, hh, {==}, {==}, {==}),
    w8.grid.vi(4, vi, h_vi, mx, my, hmax, vmax, ww, hh, {==}, {==}, {==}))

# no Cb sample: no colour, whatever the Y and Cr samples
def w8.rgb3.nb(aa: Maybe<&2, U32>, cc: Maybe<&2, U32>) -> {None{} == Laws.jpg.rgb3(aa, None{}, cc) : Maybe<&2, U32>}:
  match aa:
    case None{}:
      {==}
    case Some{_av}:
      {==}

# no Cr sample: no colour, whatever the Y and Cb samples
def w8.rgb3.nr(aa: Maybe<&2, U32>, bb: Maybe<&2, U32>) -> {None{} == Laws.jpg.rgb3(aa, bb, None{}) : Maybe<&2, U32>}:
  match aa bb:
    case None{} _bb:
      {==}
    case Some{_av} None{}:
      {==}
    case Some{_av} Some{_bv}:
      {==}

# jpeg_rgbs_at by induction on the three planes together
def w8.rgbs.at(
  +ys: List<&2, U32>,
  +bs: List<&2, U32>,
  +rs: List<&2, U32>,
  +kk: Nat
) -> {List.get(&2, U32, Jpeg.decode.rgbs(ys, bs, rs), kk) ==
  Laws.jpg.rgb3(List.get(&2, U32, ys, kk), List.get(&2, U32, bs, kk), List.get(&2, U32, rs, kk)) : Maybe<&2, U32>}:
  match ys bs rs kk:
    case Nil{} _bs _rs _kk:
      {==}
    case _yv <> _yt Nil{} _rs 0n:
      {==}
    case _yv <> yt Nil{} rs 1n+pp:
      w8.rgb3.nb(List.get(&2, U32, yt, pp), List.get(&2, U32, rs, 1n+pp))
    case _yv <> _yt _bv <> _bt Nil{} 0n:
      {==}
    case _yv <> yt _bv <> bt Nil{} 1n+pp:
      w8.rgb3.nr(List.get(&2, U32, yt, pp), List.get(&2, U32, bt, pp))
    case _yv <> _yt _bv <> _bt _rv <> _rt 0n:
      {==}
    case _yv <> yt _bv <> bt _rv <> rt 1n+pp:
      w8.rgbs.at(yt, bt, rt, pp)

def Laws.jpeg_rgbs_at(ys, bs, rs, kk):
  w8.rgbs.at(ys, bs, rs, kk)

# the absent test's first conjunct: this element is not want
def w8.idx.ne(
  bb: Bool,
  +rest: Bool,
  h_new: {Bool.and(Bool.not(bb), rest) == True{} : Bool}
) -> {bb == False{} : Bool}:
  match bb:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, M1.false_true(h_new))

# the absent test's second conjunct: no later element is want
def w8.idx.rest(
  bb: Bool,
  +rest: Bool,
  h_new: {Bool.and(Bool.not(bb), rest) == True{} : Bool}
) -> {rest == True{} : Bool}:
  match bb:
    case False{}:
      h_new
    case True{}:
      Empty.absurd({rest == True{} : Bool}, M1.false_true(h_new))

# decode.index after the element that was want is the count so far
def w8.idx.seen(
  xs: List<&2, U32>,
  +want: U32,
  +ii: U32
) -> {Jpeg.decode.index(xs, True{}, want, ii) == ii : U32}:
  match xs:
    case Nil{}:
      {==}
    case _xx <> _rest:
      {==}

# decode.index from ii over pre, then want: ii plus pre's length
def w8.idx.go(
  +pre: List<&2, U32>,
  +want: U32,
  +post: List<&2, U32>,
  +ii: U32,
  +h_new: {Laws.jpg.absent(pre, want) == True{} : Bool}
) -> {Jpeg.decode.index(List.append(&2, U32, pre, want <> post), False{}, want, ii) == Laws.jpg.count(pre, ii) : U32}:
  match pre:
    case Nil{}:
      Equal.trans(U32, Jpeg.decode.index(post, U32.is_eq(want, want), want,
        Jpeg.decode.index.add(U32.is_eq(want, want), ii)), Jpeg.decode.index(post, True{}, want,
        Jpeg.decode.index.add(True{}, ii)), ii,
        Equal.cong(Bool, U32, bb => Jpeg.decode.index(post, bb, want, Jpeg.decode.index.add(bb, ii)),
          U32.is_eq(want, want), True{}, M1.u32_eq_refl(want)),
        w8.idx.seen(post, want, ii))
    case +xx <> rest:
      Equal.trans(U32, Jpeg.decode.index(List.append(&2, U32, rest, want <> post), U32.is_eq(xx, want), want,
        Jpeg.decode.index.add(U32.is_eq(xx, want), ii)), Jpeg.decode.index(List.append(&2, U32, rest, want <> post),
        False{}, want, Jpeg.decode.index.add(False{}, ii)), Laws.jpg.count(rest, (ii + 1 : U32)),
        Equal.cong(Bool, U32, bb => Jpeg.decode.index(List.append(&2, U32, rest, want <> post), bb, want,
          Jpeg.decode.index.add(bb, ii)), U32.is_eq(xx, want), False{},
          w8.idx.ne(U32.is_eq(xx, want), Laws.jpg.absent(rest, want), h_new)),
        w8.idx.go(rest, want, post, (ii + 1 : U32),
          w8.idx.rest(U32.is_eq(xx, want), Laws.jpg.absent(rest, want), h_new)))

def Laws.jpeg_comp_index(pre, want, post, h_new):
  w8.idx.go(pre, want, post, 0, h_new)

# one step of the walk, from where it tests for more data units
def w8.walk.more(
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
  +ri: U32,
  h_more: {more == True{} : Bool}
) -> {Jpeg.decode.adv.bi(more, comp, bi, mx, my, mcu, rst, ww, hmax, ns, ri) ==
  Jpeg.Adv{Jpeg.Ctrl{comp, (bi + 1 : U32), mx, my, mcu, rst}, 0, rst} : Jpeg.Adv}:
  match more:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Jpeg.decode.adv.bi(False{}, comp, bi, mx, my, mcu, rst, ww, hmax, ns, ri) ==
        Jpeg.Adv{Jpeg.Ctrl{comp, (bi + 1 : U32), mx, my, mcu, rst}, 0, rst} : Jpeg.Adv}, M1.false_true(h_more))

def Laws.jpeg_walk_unit(
  comp,
  bi,
  mx,
  my,
  mcu,
  rst,
  ww,
  _hh,
  _nf,
  ids,
  hs,
  vs,
  _tq,
  hmax,
  _vmax,
  ns,
  sids,
  _td,
  _ta,
  _ss,
  _se,
  _ah,
  ri,
  h_more
):
  w8.walk.more(U32.is_lt((bi + 1 : U32), Laws.jpg.units(comp, sids, ids, hs, vs)), comp, bi, mx, my, mcu, rst, ww,
    hmax, ns, ri, h_more)

# the step after a component's last unit, once it has found more components: unit 0 of the next one
def w8.walk.next(
  next: Bool,
  +comp: U32,
  +mx: U32,
  +my: U32,
  +mcu: U32,
  +rst: U32,
  +ww: U32,
  +hmax: U32,
  +ri: U32,
  h_next: {next == True{} : Bool}
) -> {Jpeg.decode.adv.comp(next, comp, mx, my, mcu, rst, ww, hmax, ri) ==
  Jpeg.Adv{Jpeg.Ctrl{(comp + 1 : U32), 0, mx, my, mcu, rst}, 0, rst} : Jpeg.Adv}:
  match next:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Jpeg.decode.adv.comp(False{}, comp, mx, my, mcu, rst, ww, hmax, ri) ==
        Jpeg.Adv{Jpeg.Ctrl{(comp + 1 : U32), 0, mx, my, mcu, rst}, 0, rst} : Jpeg.Adv}, M1.false_true(h_next))

# the step after a component's last unit, from where it tests for more units
def w8.walk.comp(
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
  +ri: U32,
  h_last: {more == False{} : Bool},
  h_next: {U32.is_lt((comp + 1 : U32), ns) == True{} : Bool}
) -> {Jpeg.decode.adv.bi(more, comp, bi, mx, my, mcu, rst, ww, hmax, ns, ri) ==
  Jpeg.Adv{Jpeg.Ctrl{(comp + 1 : U32), 0, mx, my, mcu, rst}, 0, rst} : Jpeg.Adv}:
  match more:
    case True{}:
      Empty.absurd({Jpeg.decode.adv.bi(True{}, comp, bi, mx, my, mcu, rst, ww, hmax, ns, ri) ==
        Jpeg.Adv{Jpeg.Ctrl{(comp + 1 : U32), 0, mx, my, mcu, rst}, 0, rst} : Jpeg.Adv},
        M1.false_true(Equal.sym(Bool, True{}, False{}, h_last)))
    case False{}:
      w8.walk.next(U32.is_lt((comp + 1 : U32), ns), comp, mx, my, mcu, rst, ww, hmax, ri, h_next)

def Laws.jpeg_walk_comp(
  comp,
  bi,
  mx,
  my,
  mcu,
  rst,
  ww,
  _hh,
  _nf,
  ids,
  hs,
  vs,
  _tq,
  hmax,
  _vmax,
  ns,
  sids,
  _td,
  _ta,
  _ss,
  _se,
  _ah,
  ri,
  h_last,
  h_next
):
  w8.walk.comp(U32.is_lt((bi + 1 : U32), Laws.jpg.units(comp, sids, ids, hs, vs)), comp, bi, mx, my, mcu, rst, ww,
    hmax, ns, ri, h_last, h_next)

# a new MCU starts at unit 0 of component 0, restart or not
def w8.walk.due(
  zero: Bool,
  hit: Bool,
  +mcu: U32,
  +mx: U32,
  +my: U32,
  +rst: U32
) -> {Laws.jpg.adv.at(Jpeg.decode.adv.due.b(zero, hit, mcu, mx, my, rst)) == (0, 0, mcu) : U32 & U32 & U32}:
  match zero hit:
    case True{} _hit:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# a new MCU starts at unit 0 of component 0, in this MCU row or the next
def w8.walk.mx(
  inb: Bool,
  +mcu: U32,
  +mx: U32,
  +my: U32,
  +rst: U32,
  +ri: U32
) -> {Laws.jpg.adv.at(Jpeg.decode.adv.mx(inb, mcu, mx, my, rst, ri)) == (0, 0, mcu) : U32 & U32 & U32}:
  match inb:
    case True{}:
      w8.walk.due(U32.is_eq(ri, 0), U32.is_eq(U32.mod(mcu, Jpeg.decode.ri.nz(ri)), 0), mcu, mx, my, rst)
    case False{}:
      w8.walk.due(U32.is_eq(ri, 0), U32.is_eq(U32.mod(mcu, Jpeg.decode.ri.nz(ri)), 0), mcu, 0, (my + 1 : U32), rst)

# after the last component's last unit: the next MCU
def w8.walk.end(
  next: Bool,
  +comp: U32,
  +mx: U32,
  +my: U32,
  +mcu: U32,
  +rst: U32,
  +ww: U32,
  +hmax: U32,
  +ri: U32,
  h_end: {next == False{} : Bool}
) -> {Laws.jpg.adv.at(Jpeg.decode.adv.comp(next, comp, mx, my, mcu, rst, ww, hmax, ri)) == (0, 0, (mcu + 1 : U32)) :
  U32 & U32 & U32}:
  match next:
    case False{}:
      w8.walk.mx(U32.is_lt((mx + 1 : U32), Jpeg.decode.ceil(ww, (hmax * 8 : U32))), (mcu + 1 : U32), (mx + 1 : U32),
        my, rst, ri)
    case True{}:
      Empty.absurd({Laws.jpg.adv.at(Jpeg.decode.adv.comp(True{}, comp, mx, my, mcu, rst, ww, hmax, ri)) ==
        (0, 0, (mcu + 1 : U32)) : U32 & U32 & U32}, M1.false_true(Equal.sym(Bool, True{}, False{}, h_end)))

# the step after the last unit of a component, when no component follows
def w8.walk.last(
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
  +ri: U32,
  h_last: {more == False{} : Bool},
  h_end: {U32.is_lt((comp + 1 : U32), ns) == False{} : Bool}
) -> {Laws.jpg.adv.at(Jpeg.decode.adv.bi(more, comp, bi, mx, my, mcu, rst, ww, hmax, ns, ri)) ==
  (0, 0, (mcu + 1 : U32)) : U32 & U32 & U32}:
  match more:
    case True{}:
      Empty.absurd({Laws.jpg.adv.at(Jpeg.decode.adv.bi(True{}, comp, bi, mx, my, mcu, rst, ww, hmax, ns, ri)) ==
        (0, 0, (mcu + 1 : U32)) : U32 & U32 & U32}, M1.false_true(Equal.sym(Bool, True{}, False{}, h_last)))
    case False{}:
      w8.walk.end(U32.is_lt((comp + 1 : U32), ns), comp, mx, my, mcu, rst, ww, hmax, ri, h_end)

def Laws.jpeg_walk_mcu(
  comp,
  bi,
  mx,
  my,
  mcu,
  rst,
  ww,
  _hh,
  _nf,
  ids,
  hs,
  vs,
  _tq,
  hmax,
  _vmax,
  ns,
  sids,
  _td,
  _ta,
  _ss,
  _se,
  _ah,
  ri,
  h_last,
  h_end
):
  w8.walk.last(U32.is_lt((bi + 1 : U32), Laws.jpg.units(comp, sids, ids, hs, vs)), comp, bi, mx, my, mcu, rst, ww,
    hmax, ns, ri, h_last, h_end)

def Laws.jpeg_block_cover_all(pw, ph, ox, oy, ww, hh, samples, plane):
  cv.all(8n, plane, samples, 0, ox, oy, pw, ph, ww, hh)

def Laws.jpeg_block_cover(pw, ph, _h_pw, _h_ph, _h_44, ox, oy, ww, hh, samples, nn):
  cv.all(8n, Jpeg.decode.plane(nn), samples, 0, ox, oy, pw, ph, ww, hh)

def Laws.jpeg_mcu_grid_comp(comp, sids, ids, hs, vs, h_hi, h_vi, mx, my, hmax, vmax, ww, hh):
  +hi = Laws.jpg.fac.of(comp, sids, ids, hs)
  +vi = Laws.jpg.fac.of(comp, sids, ids, vs)
  Equal.trans(List<&2, Jpeg.Geom>, Laws.jpg.blocks.of(U32.to_nat((hi * vi : U32)), 0, comp, sids, ids, hs, vs, mx, my,
    hmax, vmax, ww, hh), Laws.jpg.blocks(U32.to_nat((hi * vi : U32)), 0, hi, vi, mx, my, hmax, vmax, ww, hh),
    Laws.jpg.grid(U32.to_nat(vi), 0, hi, mx, my, hmax, vmax, U32.div(hmax, hi), U32.div(vmax, vi), ww, hh),
    grid.of(U32.to_nat((hi * vi : U32)), 0, comp, sids, ids, hs, vs, mx, my, hmax, vmax, ww, hh),
    Laws.jpeg_mcu_grid(hi, vi, h_hi, h_vi, mx, my, hmax, vmax, ww, hh))

def Laws.jpeg_refuse_factor1_any(
  pre,
  frame,
  scan,
  tabs,
  ent,
  ri,
  kind,
  bad,
  h_walk,
  lh,
  ll,
  yh,
  yl,
  xh,
  xl,
  c1,
  f1,
  q1,
  extra,
  h_len,
  h_body,
  h_fac,
  rest
):
  +body = {List.append(&2, U32, [8, yh, yl, xh, xl, 1, c1, f1, q1], extra) : List<&2, U32>}
  w8.tail(pre, lh <> ll <> List.append(&2, U32, body, rest), Jpeg.St{Jpeg.LenHi{192}, frame, scan, tabs, ent, ri,
    kind, bad}, rest, scan, tabs, ent, ri, kind, h_walk,
    sof.seg(lh, ll, body, rest, frame, scan, tabs, ent, ri, kind, bad, h_len, h_body,
      Equal.cong(Bool, Jpeg.St, ok => Jpeg.decode.read.sof.c(ok, U32.is_eq(bad, 0), False{}, Jpeg.decode.u16(xh, xl),
        Jpeg.decode.u16(yh, yl), 1, [c1], [1], [1], [q1], scan, tabs, ent, ri, kind), Laws.jpg.facs4(f1), False{},
        h_fac)))

def Laws.jpeg_refuse_factor3_any(
  pre,
  frame,
  scan,
  tabs,
  ent,
  ri,
  kind,
  bad,
  h_walk,
  lh,
  ll,
  yh,
  yl,
  xh,
  xl,
  c1,
  f1,
  q1,
  c2,
  f2,
  q2,
  c3,
  f3,
  q3,
  extra,
  h_len,
  h_body,
  h_fac,
  rest
):
  +body = {List.append(&2, U32, [8, yh, yl, xh, xl, 3, c1, f1, q1, c2, f2, q2, c3, f3, q3], extra) : List<&2, U32>}
  w8.tail(pre, lh <> ll <> List.append(&2, U32, body, rest), Jpeg.St{Jpeg.LenHi{192}, frame, scan, tabs, ent, ri,
    kind, bad}, rest, scan, tabs, ent, ri, kind, h_walk,
    sof.seg(lh, ll, body, rest, frame, scan, tabs, ent, ri, kind, bad, h_len, h_body,
      Equal.cong(Bool, Jpeg.St, ok => Jpeg.decode.read.sof.c(ok, Bool.and(Jpeg.decode.nf.ok(3), U32.is_eq(bad, 0)),
        U32.is_eq(Jpeg.decode.vmax([U32.shrn(f1, 4n), U32.shrn(f2, 4n), U32.shrn(f3, 4n)], 0), 0),
        Jpeg.decode.u16(xh, xl), Jpeg.decode.u16(yh, yl), 3, [c1, c2, c3],
        [U32.shrn(f1, 4n), U32.shrn(f2, 4n), U32.shrn(f3, 4n)], [U32.and(f1, 15), U32.and(f2, 15), U32.and(f3, 15)],
        [q1, q2, q3], scan, tabs, ent, ri, kind),
        Bool.and(Bool.and(Laws.jpg.facs(f1), Laws.jpg.facs(f2)), Laws.jpg.facs(f3)), False{}, h_fac)))

def Laws.jpeg_refuse_count(
  pre,
  frame,
  scan,
  tabs,
  ent,
  ri,
  kind,
  bad,
  h_walk,
  lh,
  ll,
  yh,
  yl,
  xh,
  xl,
  nf,
  h_nf,
  comps,
  h_len,
  h_body,
  rest
):
  +body = {8 <> yh <> yl <> xh <> xl <> nf <> comps : List<&2, U32>}
  w8.tail(pre, lh <> ll <> List.append(&2, U32, body, rest), Jpeg.St{Jpeg.LenHi{192}, frame, scan, tabs, ent, ri,
    kind, bad}, rest, scan, tabs, ent, ri, kind, h_walk,
    sof.seg(lh, ll, body, rest, frame, scan, tabs, ent, ri, kind, bad, h_len, h_body,
      sof.cnt(Jpeg.decode.read.cs(U32.to_nat(nf), comps, [], [], [], [], True{}), Jpeg.decode.u16(xh, xl),
        Jpeg.decode.u16(yh, yl), nf, scan, tabs, ent, ri, kind, bad, h_nf)))

def Laws.jpeg_points_at(nn, plane, kk, h_kk):
  ee = idx.of(kk)
  %ee : {List.get(&2, U32, Jpeg.decode.points(nn, plane), U32.to_nat(kk)) ==
    Some{D1.jpg.val(Array.get(U32, plane, _))} : Maybe<&2, U32>}
  emit.at(nn, U32.to_nat(kk), plane, 0, M2.dup(plane), h_kk)

def Laws.jpeg_walk_frame(
  ww,
  hh,
  nf,
  ids,
  hs,
  vs,
  tq,
  hmax,
  vmax,
  ns,
  sids,
  td,
  ta,
  ss,
  se,
  ah,
  ri,
  rst,
  mh,
  h_ns,
  h_mw,
  h_units
):
  walk.frame(ww, hh, nf, ids, hs, vs, tq, hmax, vmax, ns, sids, td, ta, ss, se, ah, ri, rst, mh, h_ns, h_mw,
    h_units)

def Laws.jpeg_walk_count(ww, hh, ids, hs, vs, hmax, vmax, ns, sids, top, h_ns, h_units, h_sum, h_fit):
  walk.count(Jpeg.decode.ceil(ww, (hmax * 8 : U32)), Jpeg.decode.ceil(hh, (vmax * 8 : U32)),
    Jpeg.decode.blocks.sum(hs, vs, 0), ns, sids, ids, hs, vs, top, usum.pos(ns, sids, ids, hs, vs, h_ns, h_units),
    h_sum, h_fit)

def Laws.jpeg_get_set(plane, ii, vv):
  get_same_of(plane, ii, vv, M1.of(plane))

def Laws.jpeg_get_set_other(dd, plane, h_perfect, h_dd, ii, jj, vv, h_ii, h_jj, h_ne):
  get_other_of(dd, plane, h_perfect, h_dd, ii, jj, vv, h_ii, h_jj, h_ne, M1.of(plane))

def Laws.jpeg_paint_at(dd, plane, h_perfect, h_dd, ox, oy, pw, ph, ww, hh, samples, h_fit, xx, yy, h_xx, h_yy):
  paint_at_of(dd, plane, h_perfect, h_dd, ox, oy, pw, ph, ww, hh, samples, h_fit, xx, yy, h_xx, h_yy,
    M1.of(plane))

def Laws.jpeg_plane_depth(nn, dd, h_pos, h_dd, h_nn):
  dep(nn, dd, h_pos, h_dd, h_nn)

def Laws.jpeg_blocks_paint(left, blk, ctrl, preds, frame, scan, tabs, ri, rgb, yy, cb, cr, ok):
  blocks_paint(left, Jpeg.decode.blk.live(blk), blk, ctrl, preds, frame, scan, tabs, ri, rgb, yy, cb, cr, ok)

def Laws.jpeg_plane_at(
  dd,
  plane,
  h_perfect,
  h_dd,
  us,
  comp,
  ww,
  hh,
  nf,
  ids,
  hs,
  vs,
  tq,
  hmax,
  vmax,
  scan,
  h_fit,
  xx,
  yy,
  h_xx,
  h_yy
):
  plane_at_of(dd, plane, h_perfect, h_dd, us, comp, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan, h_fit, xx, yy,
    h_xx, h_yy, M1.of(plane))

# ---- decode_jpeg's pixels (jpeg_place) ----

# a decoded picture's sample kn is cc, when there is a picture
def w13.Q(-mm: Maybe<&2, Jpeg.Pic>, +kn: Nat, +cc: U32) -> Type:
  {Laws.jpg.px.at(Img.decode_jpeg.out(mm), kn) == Laws.jpg.px.want(Img.decode_jpeg.out(mm), cc) : Maybe<&2, U32>}

# a component's plane read out: point k is jpg.point over the component's units
def w13.pt(
  +cc: U32,
  +us: List<&2, Laws.JUnit>,
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
  +hD: {Nat.is_lt(Jpeg.decode.depth((ww * hh : U32)), 32n) == True{} : Bool},
  +hfD: {Nat.is_le(Nat.mul(U32.to_nat(ww), U32.to_nat(hh)), Nat.pow(2n, Jpeg.decode.depth((ww * hh : U32)))) == True{} :
    Bool},
  +hK: {Nat.is_lt(U32.to_nat((yy * ww + xx : U32)), U32.to_nat((ww * hh : U32))) == True{} : Bool},
  +h_xx: {U32.is_lt(xx, ww) == True{} : Bool},
  +h_yy: {U32.is_lt(yy, hh) == True{} : Bool}
) -> {List.get(&2, U32, Jpeg.decode.points(U32.to_nat((ww * hh : U32)), Laws.jpg.paint.all(us, cc, Jpeg.Frame{ww, hh,
  nf, ids, hs, vs, tq, hmax, vmax}, scan, Jpeg.decode.plane((ww * hh : U32)))),
  U32.to_nat((yy * ww + xx : U32))) == Some{Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax},
  scan, xx, yy, 0)} :
  Maybe<&2, U32>}:
  +kk = (yy * ww + xx : U32)
  +e1 = Laws.jpeg_points_at(U32.to_nat((ww * hh : U32)), Laws.jpg.paint.all(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs,
    tq, hmax, vmax}, scan, Jpeg.decode.plane((ww * hh : U32))), kk, hK)
  +e2 = Laws.jpeg_plane_at(Jpeg.decode.depth((ww * hh : U32)), Jpeg.decode.plane((ww * hh : U32)),
    plane_perfect((ww * hh : U32)), hD, us, cc,
    ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan, hfD, xx, yy, h_xx, h_yy)
  +e3 = plane_zero((ww * hh : U32), kk)
  Equal.trans(Maybe<&2, U32>, List.get(&2, U32, Jpeg.decode.points(U32.to_nat((ww * hh : U32)), Laws.jpg.paint.all(us,
    cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, Jpeg.decode.plane((ww * hh : U32)))),
    U32.to_nat((yy * ww + xx : U32))),
    Some{D1.jpg.val(Array.get(U32, Laws.jpg.paint.all(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax},
    scan, Jpeg.decode.plane((ww * hh : U32))), kk))}, Some{Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs,
    tq, hmax, vmax}, scan, xx, yy, 0)}, e1, Equal.cong(U32, Maybe<&2, U32>,
    vv => {Some{vv} : Maybe<&2, U32>}, D1.jpg.val(Array.get(U32, Laws.jpg.paint.all(us, cc, Jpeg.Frame{ww, hh, nf,
    ids, hs, vs, tq, hmax, vmax}, scan, Jpeg.decode.plane((ww * hh : U32))), kk)), Laws.jpg.point(us, cc, Jpeg.Frame{ww,
    hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy, 0), Equal.trans(U32,
    D1.jpg.val(Array.get(U32, Laws.jpg.paint.all(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan,
    Jpeg.decode.plane((ww * hh : U32))), kk)), Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax,
    vmax}, scan, xx, yy, D1.jpg.val(Array.get(U32,
    Jpeg.decode.plane((ww * hh : U32)), kk))), Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax,
    vmax}, scan, xx, yy, 0), e2, Equal.cong(U32, U32, aa => Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs,
    tq, hmax, vmax}, scan, xx, yy, aa),
    D1.jpg.val(Array.get(U32, Jpeg.decode.plane((ww * hh : U32)), kk)), 0, e3))))

# ---- libjpeg's upsampling (jpg.up.value) ----

# a U32 above 0 less one stays below what it was below
def sub1.nat(
  nx: Nat,
  +xx: U32,
  +nn: U32,
  +ee: {U32.to_nat(xx) == nx : Nat},
  hz: {Nat.is_eq(nx, 0n) == False{} : Bool},
  hl: {Nat.is_lt(nx, U32.to_nat(nn)) == True{} : Bool}
) -> {Nat.is_lt(U32.to_nat((xx - 1 : U32)), U32.to_nat(nn)) == True{} : Bool}:
  match nx:
    case 0n:
      Empty.absurd({Nat.is_lt(U32.to_nat((xx - 1 : U32)), U32.to_nat(nn)) == True{} : Bool}, M1.jst.true_false(hz))
    case 1n+(+dd):
      +es = {M6.u32_sub_nat(xx, 1, dd, ee) : {U32.to_nat((xx - 1 : U32)) == dd : Nat}}
      +hs = {Equal.trans(Bool, Nat.is_lt(dd, 1n+dd), Nat.is_le(1n+dd, 1n+dd), True{}, M1.lt_le_succ(dd, 1n+dd),
        M1.le_refl(dd)) : {Nat.is_lt(dd, 1n+dd) == True{} : Bool}}
      +hd = {M1.lt_le_trans(dd, 1n+dd, U32.to_nat(nn), hs, M1.lt_le(1n+dd, U32.to_nat(nn), hl)) :
        {Nat.is_lt(dd, U32.to_nat(nn)) == True{} : Bool}}
      Equal.trans(Bool, Nat.is_lt(U32.to_nat((xx - 1 : U32)), U32.to_nat(nn)), Nat.is_lt(dd, U32.to_nat(nn)), True{},
        Equal.cong(Nat, Bool, zz => Nat.is_lt(zz, U32.to_nat(nn)), U32.to_nat((xx - 1 : U32)), dd, es), hd)

# a U32 other than 0 less one stays below what it was below
def sub1.lt(
  +xx: U32,
  +nn: U32,
  hz: {U32.is_eq(xx, 0) == False{} : Bool},
  hl: {U32.is_lt(xx, nn) == True{} : Bool}
) -> {U32.is_lt((xx - 1 : U32), nn) == True{} : Bool}:
  +hzn = {Equal.trans(Bool, Nat.is_eq(U32.to_nat(xx), 0n), U32.is_eq(xx, 0), False{}, Equal.sym(Bool, U32.is_eq(xx, 0),
    Nat.is_eq(U32.to_nat(xx), 0n), M1.u32_eq(xx, 0)), hz) : {Nat.is_eq(U32.to_nat(xx), 0n) == False{} : Bool}}
  Equal.trans(Bool, U32.is_lt((xx - 1 : U32), nn), Nat.is_lt(U32.to_nat((xx - 1 : U32)), U32.to_nat(nn)), True{},
    M5.u32_lt((xx - 1 : U32), nn), sub1.nat(U32.to_nat(xx), xx, nn, {==}, hzn, lt_of(xx, nn, hl)))

# the farther pixel of an odd pixel is below the side
def far.lt.odd(
  lt: Bool,
  +xx: U32,
  +nn: U32,
  he: {U32.is_lt((xx + 1 : U32), nn) == lt : Bool},
  hl: {U32.is_lt(xx, nn) == True{} : Bool}
) -> {U32.is_lt(Bool.pick(U32, lt, (xx + 1 : U32), xx), nn) == True{} : Bool}:
  match lt:
    case True{}:
      he
    case False{}:
      hl

# the farther pixel of an even pixel is below the side
def far.lt.even(
  zz: Bool,
  +xx: U32,
  +nn: U32,
  he: {U32.is_eq(xx, 0) == zz : Bool},
  hl: {U32.is_lt(xx, nn) == True{} : Bool}
) -> {U32.is_lt(Bool.pick(U32, zz, xx, (xx - 1 : U32)), nn) == True{} : Bool}:
  match zz:
    case True{}:
      hl
    case False{}:
      sub1.lt(xx, nn, he, hl)

def far.lt.p(
  ev: Bool,
  +xx: U32,
  +nn: U32,
  hl: {U32.is_lt(xx, nn) == True{} : Bool}
) -> {U32.is_lt(Bool.pick(U32, ev, Bool.pick(U32, U32.is_eq(xx, 0), xx, (xx - 1 : U32)), Bool.pick(U32,
  U32.is_lt((xx + 1 : U32), nn), (xx + 1 : U32), xx)), nn) == True{} : Bool}:
  match ev:
    case True{}:
      far.lt.even(U32.is_eq(xx, 0), xx, nn, {==}, hl)
    case False{}:
      far.lt.odd(U32.is_lt((xx + 1 : U32), nn), xx, nn, {==}, hl)

# the farther pixel the filter reads is inside the frame
def far.lt(
  +xx: U32,
  +nn: U32,
  +hl: {U32.is_lt(xx, nn) == True{} : Bool}
) -> {U32.is_lt(Jpeg.decode.up.far(xx, nn), nn) == True{} : Bool}:
  far.lt.p(U32.is_eq(U32.and(xx, 1), 0), xx, nn, hl)

# a filtered pixel's four reads each hand the plane back: the pixel is the filter of the plane's values
def CellEq(+mode: U32, +xx: U32, +yy: U32, +ww: U32, +hh: U32, -aa: Array<U32>) -> Type:
  {Jpeg.decode.up.cell(mode, xx, yy, ww, hh, aa) == (aa, Jpeg.decode.up.mix(mode, xx, yy, D1.jpg.val(Array.get(U32, aa,
    (yy * ww + xx : U32))), D1.jpg.val(Array.get(U32, aa, (yy * ww + Jpeg.decode.up.far(xx, ww) : U32))),
    D1.jpg.val(Array.get(U32, aa, (Jpeg.decode.up.far(yy, hh) * ww + xx : U32))), D1.jpg.val(Array.get(U32, aa,
    (Jpeg.decode.up.far(yy, hh) * ww + Jpeg.decode.up.far(xx, ww) : U32))))) : Array<U32> & U32}

def cell.eq(
  +mode: U32,
  +xx: U32,
  +yy: U32,
  +ww: U32,
  +hh: U32,
  -aa: Array<U32>,
  d0: M2.Dup(aa),
  d1: M2.Dup(aa),
  d2: M2.Dup(aa),
  d3: M2.Dup(aa)
) -> CellEq(mode, xx, yy, ww, hh, aa):
  +xf = Jpeg.decode.up.far(xx, ww)
  +yf = Jpeg.decode.up.far(yy, hh)
  -mx = Jpeg.decode.up.mix(mode, xx, yy, D1.jpg.val(Array.get(U32, aa, (yy * ww + xx : U32))),
    D1.jpg.val(Array.get(U32, aa, (yy * ww + Jpeg.decode.up.far(xx, ww) : U32))), D1.jpg.val(Array.get(U32, aa,
    (Jpeg.decode.up.far(yy, hh) * ww + xx : U32))), D1.jpg.val(Array.get(U32, aa, (Jpeg.decode.up.far(yy, hh) * ww +
    Jpeg.decode.up.far(xx, ww) : U32))))
  -v0 = D1.jpg.val(Array.get(U32, aa, (yy * ww + xx : U32)))
  -vh = D1.jpg.val(Array.get(U32, aa, (yy * ww + xf : U32)))
  -vv = D1.jpg.val(Array.get(U32, aa, (yf * ww + xx : U32)))
  e0 = Equal.sym(Array<U32> & U32, Array.get(U32, aa, (yy * ww + xx : U32)), (aa, v0), M2.get.eq.d(aa,
    (yy * ww + xx : U32), d0))
  %e0 : {Jpeg.decode.up.cell.a(_, mode, xx, yy, xf, yf, ww) == (aa, mx) : Array<U32> & U32}
  e1 = Equal.sym(Array<U32> & U32, Array.get(U32, aa, (yy * ww + xf : U32)), (aa, vh), M2.get.eq.d(aa,
    (yy * ww + xf : U32), d1))
  %e1 : {Jpeg.decode.up.cell.b(_, mode, xx, yy, xf, yf, ww, v0) == (aa, mx) : Array<U32> & U32}
  e2 = Equal.sym(Array<U32> & U32, Array.get(U32, aa, (yf * ww + xx : U32)), (aa, vv), M2.get.eq.d(aa,
    (yf * ww + xx : U32), d2))
  %e2 : {Jpeg.decode.up.cell.c(_, mode, xx, yy, xf, yf, ww, v0, vh) == (aa, mx) : Array<U32> & U32}
  e3 = Equal.sym(Array<U32> & U32, Array.get(U32, aa, (yf * ww + xf : U32)), (aa, D1.jpg.val(Array.get(U32, aa, (yf *
    ww + xf : U32)))),
    M2.get.eq.d(aa, (yf * ww + xf : U32), d3))
  %e3 : {Jpeg.decode.up.cell.d(_, mode, xx, yy, v0, vh, vv) == (aa, mx) : Array<U32> & U32}
  {==}

# five copies' worth of reads of a plane
def Dups(-aa: Array<U32>) -> Type:
  M2.Dup(aa) & M2.Dup(aa) & M2.Dup(aa) & M2.Dup(aa) & M2.Dup(aa)

def dsplit(-aa: Array<U32>, dd: M2.Dup(aa)) -> M2.Dup(aa) & M2.Dup(aa):
  (b1, b2, e1, e2) = dd
  (M2.dup.tr(b1, aa, e1, M2.dup(b1)), M2.dup.tr(b2, aa, e2, M2.dup(b2)))

def mk5.c(-aa: Array<U32>, ef: M2.Dup(aa) & M2.Dup(aa), a1: M2.Dup(aa), a2: M2.Dup(aa), c1: M2.Dup(aa)) -> Dups(aa):
  (e5, f5) = ef
  (a1, a2, c1, e5, f5)

def mk5.b(-aa: Array<U32>, ab: M2.Dup(aa) & M2.Dup(aa), cd: M2.Dup(aa) & M2.Dup(aa)) -> Dups(aa):
  (a1, a2) = ab
  (c1, c2) = cd
  mk5.c(aa, dsplit(aa, c2), a1, a2, c1)

def mk5.a(-aa: Array<U32>, pq: M2.Dup(aa) & M2.Dup(aa)) -> Dups(aa):
  (pp, qq) = pq
  mk5.b(aa, dsplit(aa, pp), dsplit(aa, qq))

def mk5(-aa: Array<U32>, dd: M2.Dup(aa)) -> Dups(aa):
  mk5.a(aa, dsplit(aa, dd))

# the filtered pixel at m is the filter at (X, Y)
def AtIs(-lst: List<&2, U32>, +mm: Nat, +mode: U32, +xx: U32, +yy: U32, +ww: U32, +hh: U32, -aa: Array<U32>) -> Type:
  {List.get(&2, U32, lst, mm) == Some{Jpeg.decode.up.mix(mode, xx, yy, D1.jpg.val(Array.get(U32, aa, (yy * ww + xx :
    U32))), D1.jpg.val(Array.get(U32, aa, (yy * ww + Jpeg.decode.up.far(xx, ww) : U32))), D1.jpg.val(Array.get(U32, aa,
    (Jpeg.decode.up.far(yy, hh) * ww + xx : U32))), D1.jpg.val(Array.get(U32, aa, (Jpeg.decode.up.far(yy, hh) * ww +
    Jpeg.decode.up.far(xx, ww) : U32))))} : Maybe<&2, U32>}

# within a row: the walk's pixel m, at most lx on, is pixel xx + m of the row
def walk.at(
  ly: Nat,
  lx: Nat,
  mm: Nat,
  +xx: U32,
  +yy: U32,
  +mode: U32,
  +ww: U32,
  +hh: U32,
  +wn: Nat,
  -aa: Array<U32>,
  dd: Dups(aa),
  hm: {Nat.is_le(mm, lx) == True{} : Bool}
) -> AtIs(Jpeg.decode.up.walk(ly, lx, Jpeg.decode.up.cell(mode, xx, yy, ww, hh, aa), xx, yy, mode, ww, hh, wn), mm,
  mode, Laws.jpg.idx(mm, xx), yy, ww, hh, aa):
  match ly:
    case 0n:
      match lx:
        case 0n:
          match mm:
            case 0n:
              (d0, d1, d2, d3, _d4) = dd
              es = Equal.sym(Array<U32> & U32, Jpeg.decode.up.cell(mode, xx, yy, ww, hh, aa), (aa,
                Jpeg.decode.up.mix(mode, xx, yy, D1.jpg.val(Array.get(U32, aa, (yy * ww + xx : U32))),
                D1.jpg.val(Array.get(U32, aa, (yy * ww + Jpeg.decode.up.far(xx, ww) : U32))), D1.jpg.val(Array.get(U32,
                aa, (Jpeg.decode.up.far(yy, hh) * ww + xx : U32))), D1.jpg.val(Array.get(U32, aa,
                (Jpeg.decode.up.far(yy, hh) * ww + Jpeg.decode.up.far(xx, ww) : U32))))),
                cell.eq(mode, xx, yy, ww, hh, aa, d0, d1, d2, d3))
              %es : AtIs(Jpeg.decode.up.walk(0n, 0n, _, xx, yy, mode, ww, hh, wn), 0n, mode, xx, yy, ww, hh, aa)
              {==}
            case 1n+rr:
              Empty.absurd(AtIs(Jpeg.decode.up.walk(0n, 0n, Jpeg.decode.up.cell(mode, xx, yy, ww, hh, aa), xx, yy,
                mode, ww, hh, wn), 1n+rr, mode, Laws.jpg.idx(1n+rr, xx), yy, ww, hh, aa),
                M1.false_true(hm))
        case 1n+pp:
          match mm:
            case 0n:
              (d0, d1, d2, d3, _d4) = dd
              es = Equal.sym(Array<U32> & U32, Jpeg.decode.up.cell(mode, xx, yy, ww, hh, aa), (aa,
                Jpeg.decode.up.mix(mode, xx, yy, D1.jpg.val(Array.get(U32, aa, (yy * ww + xx : U32))),
                D1.jpg.val(Array.get(U32, aa, (yy * ww + Jpeg.decode.up.far(xx, ww) : U32))), D1.jpg.val(Array.get(U32,
                aa, (Jpeg.decode.up.far(yy, hh) * ww + xx : U32))), D1.jpg.val(Array.get(U32, aa,
                (Jpeg.decode.up.far(yy, hh) * ww + Jpeg.decode.up.far(xx, ww) : U32))))),
                cell.eq(mode, xx, yy, ww, hh, aa, d0, d1, d2, d3))
              %es : AtIs(Jpeg.decode.up.walk(0n, 1n+pp, _, xx, yy, mode, ww, hh, wn), 0n, mode, xx, yy, ww, hh, aa)
              {==}
            case 1n+rr:
              (d0, d1, d2, d3, d4) = dd
              es = Equal.sym(Array<U32> & U32, Jpeg.decode.up.cell(mode, xx, yy, ww, hh, aa), (aa,
                Jpeg.decode.up.mix(mode, xx, yy, D1.jpg.val(Array.get(U32, aa, (yy * ww + xx : U32))),
                D1.jpg.val(Array.get(U32, aa, (yy * ww + Jpeg.decode.up.far(xx, ww) : U32))), D1.jpg.val(Array.get(U32,
                aa, (Jpeg.decode.up.far(yy, hh) * ww + xx : U32))), D1.jpg.val(Array.get(U32, aa,
                (Jpeg.decode.up.far(yy, hh) * ww + Jpeg.decode.up.far(xx, ww) : U32))))),
                cell.eq(mode, xx, yy, ww, hh, aa, d0, d1, d2, d3))
              %es : AtIs(Jpeg.decode.up.walk(0n, 1n+pp, _, xx, yy, mode, ww, hh, wn), 1n+rr, mode, Laws.jpg.idx(rr,
                (xx + 1 : U32)), yy, ww, hh, aa)
              walk.at(0n, pp, rr, (xx + 1 : U32), yy, mode, ww, hh, wn, aa, mk5(aa, d4), hm)
    case 1n+qq:
      match lx:
        case 0n:
          match mm:
            case 0n:
              (d0, d1, d2, d3, _d4) = dd
              es = Equal.sym(Array<U32> & U32, Jpeg.decode.up.cell(mode, xx, yy, ww, hh, aa), (aa,
                Jpeg.decode.up.mix(mode, xx, yy, D1.jpg.val(Array.get(U32, aa, (yy * ww + xx : U32))),
                D1.jpg.val(Array.get(U32, aa, (yy * ww + Jpeg.decode.up.far(xx, ww) : U32))), D1.jpg.val(Array.get(U32,
                aa, (Jpeg.decode.up.far(yy, hh) * ww + xx : U32))), D1.jpg.val(Array.get(U32, aa,
                (Jpeg.decode.up.far(yy, hh) * ww + Jpeg.decode.up.far(xx, ww) : U32))))),
                cell.eq(mode, xx, yy, ww, hh, aa, d0, d1, d2, d3))
              %es : AtIs(Jpeg.decode.up.walk(1n+qq, 0n, _, xx, yy, mode, ww, hh, wn), 0n, mode, xx, yy, ww, hh, aa)
              {==}
            case 1n+rr:
              Empty.absurd(AtIs(Jpeg.decode.up.walk(1n+qq, 0n, Jpeg.decode.up.cell(mode, xx, yy, ww, hh, aa), xx, yy,
                mode, ww, hh, wn), 1n+rr, mode, Laws.jpg.idx(1n+rr, xx), yy, ww, hh,
                aa),
                M1.false_true(hm))
        case 1n+pp:
          match mm:
            case 0n:
              (d0, d1, d2, d3, _d4) = dd
              es = Equal.sym(Array<U32> & U32, Jpeg.decode.up.cell(mode, xx, yy, ww, hh, aa), (aa,
                Jpeg.decode.up.mix(mode, xx, yy, D1.jpg.val(Array.get(U32, aa, (yy * ww + xx : U32))),
                D1.jpg.val(Array.get(U32, aa, (yy * ww + Jpeg.decode.up.far(xx, ww) : U32))), D1.jpg.val(Array.get(U32,
                aa, (Jpeg.decode.up.far(yy, hh) * ww + xx : U32))), D1.jpg.val(Array.get(U32, aa,
                (Jpeg.decode.up.far(yy, hh) * ww + Jpeg.decode.up.far(xx, ww) : U32))))),
                cell.eq(mode, xx, yy, ww, hh, aa, d0, d1, d2, d3))
              %es : AtIs(Jpeg.decode.up.walk(1n+qq, 1n+pp, _, xx, yy, mode, ww, hh, wn), 0n, mode, xx, yy, ww, hh, aa)
              {==}
            case 1n+rr:
              (d0, d1, d2, d3, d4) = dd
              es = Equal.sym(Array<U32> & U32, Jpeg.decode.up.cell(mode, xx, yy, ww, hh, aa), (aa,
                Jpeg.decode.up.mix(mode, xx, yy, D1.jpg.val(Array.get(U32, aa, (yy * ww + xx : U32))),
                D1.jpg.val(Array.get(U32, aa, (yy * ww + Jpeg.decode.up.far(xx, ww) : U32))), D1.jpg.val(Array.get(U32,
                aa, (Jpeg.decode.up.far(yy, hh) * ww + xx : U32))), D1.jpg.val(Array.get(U32, aa,
                (Jpeg.decode.up.far(yy, hh) * ww + Jpeg.decode.up.far(xx, ww) : U32))))),
                cell.eq(mode, xx, yy, ww, hh, aa, d0, d1, d2, d3))
              %es : AtIs(Jpeg.decode.up.walk(1n+qq, 1n+pp, _, xx, yy, mode, ww, hh, wn), 1n+rr, mode,
                Laws.jpg.idx(rr, (xx + 1 : U32)), yy, ww, hh, aa)
              walk.at(1n+qq, pp, rr, (xx + 1 : U32), yy, mode, ww, hh, wn, aa, mk5(aa, d4), hm)

# past a row: the walk's pixel 1 + lx + m on is pixel m of the next rows
def walk.skip(
  lx: Nat,
  +qq: Nat,
  +mm: Nat,
  +xx: U32,
  +yy: U32,
  +mode: U32,
  +ww: U32,
  +hh: U32,
  +wn: Nat,
  -aa: Array<U32>,
  dd: Dups(aa)
) -> {List.get(&2, U32, Jpeg.decode.up.walk(1n+qq, lx, Jpeg.decode.up.cell(mode, xx, yy, ww, hh, aa), xx, yy, mode, ww,
  hh, wn), Nat.add(1n+lx, mm)) ==
  List.get(&2, U32, Jpeg.decode.up.walk(qq, wn, Jpeg.decode.up.cell(mode, 0, (yy + 1 : U32), ww, hh, aa), 0, (yy + 1 :
    U32), mode, ww, hh, wn), mm) : Maybe<&2, U32>}:
  match lx:
    case 0n:
      (d0, d1, d2, d3, _d4) = dd
      es = Equal.sym(Array<U32> & U32, Jpeg.decode.up.cell(mode, xx, yy, ww, hh, aa), (aa, Jpeg.decode.up.mix(mode, xx,
        yy, D1.jpg.val(Array.get(U32, aa, (yy * ww + xx : U32))), D1.jpg.val(Array.get(U32, aa, (yy * ww +
        Jpeg.decode.up.far(xx, ww) : U32))), D1.jpg.val(Array.get(U32, aa, (Jpeg.decode.up.far(yy, hh) * ww + xx :
        U32))), D1.jpg.val(Array.get(U32, aa, (Jpeg.decode.up.far(yy, hh) * ww + Jpeg.decode.up.far(xx, ww) : U32))))),
        cell.eq(mode, xx, yy, ww, hh, aa, d0, d1, d2, d3))
      %es : {List.get(&2, U32, Jpeg.decode.up.walk(1n+qq, 0n, _, xx, yy, mode, ww, hh, wn), 1n+mm) ==
        List.get(&2, U32, Jpeg.decode.up.walk(qq, wn, Jpeg.decode.up.cell(mode, 0, (yy + 1 : U32), ww, hh, aa), 0, (yy
          + 1 : U32), mode, ww, hh, wn), mm) : Maybe<&2, U32>}
      {==}
    case 1n+pp:
      (d0, d1, d2, d3, d4) = dd
      es = Equal.sym(Array<U32> & U32, Jpeg.decode.up.cell(mode, xx, yy, ww, hh, aa), (aa, Jpeg.decode.up.mix(mode, xx,
        yy, D1.jpg.val(Array.get(U32, aa, (yy * ww + xx : U32))), D1.jpg.val(Array.get(U32, aa, (yy * ww +
        Jpeg.decode.up.far(xx, ww) : U32))), D1.jpg.val(Array.get(U32, aa, (Jpeg.decode.up.far(yy, hh) * ww + xx :
        U32))), D1.jpg.val(Array.get(U32, aa, (Jpeg.decode.up.far(yy, hh) * ww + Jpeg.decode.up.far(xx, ww) : U32))))),
        cell.eq(mode, xx, yy, ww, hh, aa, d0, d1, d2, d3))
      %es : {List.get(&2, U32, Jpeg.decode.up.walk(1n+qq, 1n+pp, _, xx, yy, mode, ww, hh, wn), 1n+Nat.add(1n+pp, mm)) ==
        List.get(&2, U32, Jpeg.decode.up.walk(qq, wn, Jpeg.decode.up.cell(mode, 0, (yy + 1 : U32), ww, hh, aa), 0, (yy
          + 1 : U32), mode, ww, hh, wn), mm) : Maybe<&2, U32>}
      walk.skip(pp, qq, mm, (xx + 1 : U32), yy, mode, ww, hh, wn, aa, mk5(aa, d4))

# over rows: the walk's pixel yn * (1 + wn) + xn, from the start of row y0, is pixel xn of row y0 + yn
def rows.at(
  yn: Nat,
  ly: Nat,
  +xn: Nat,
  +y0: U32,
  +mode: U32,
  +ww: U32,
  +hh: U32,
  +wn: Nat,
  -aa: Array<U32>,
  dd: Dups(aa),
  hy: {Nat.is_le(yn, ly) == True{} : Bool},
  +hx: {Nat.is_le(xn, wn) == True{} : Bool}
) -> AtIs(Jpeg.decode.up.walk(ly, wn, Jpeg.decode.up.cell(mode, 0, y0, ww, hh, aa), 0, y0, mode, ww, hh, wn),
  Nat.add(Nat.mul(yn, 1n+wn), xn), mode, Laws.jpg.idx(xn, 0), Laws.jpg.idx(yn, y0),
  ww, hh, aa):
  match yn:
    case 0n:
      walk.at(ly, wn, xn, 0, y0, mode, ww, hh, wn, aa, dd, hx)
    case 1n+(+rr):
      match ly:
        case 0n:
          Empty.absurd(AtIs(Jpeg.decode.up.walk(0n, wn, Jpeg.decode.up.cell(mode, 0, y0, ww, hh, aa), 0, y0, mode, ww,
            hh, wn), Nat.add(Nat.mul(1n+rr, 1n+wn), xn), mode, Laws.jpg.idx(xn, 0),
            Laws.jpg.idx(1n+rr, y0), ww, hh, aa), M1.false_true(hy))
        case 1n+(+qq):
          (d0, d1, _d2, _d3, _d4) = dd
          +mr = Nat.mul(rr, 1n+wn)
          +y1 = (y0 + 1 : U32)
          +ea = {M1.ras.add_assoc(1n+wn, mr, xn) : {Nat.add(Nat.add(1n+wn, mr), xn) == Nat.add(1n+wn, Nat.add(mr, xn)) :
            Nat}}
          Equal.trans(Maybe<&2, U32>, List.get(&2, U32, Jpeg.decode.up.walk(1n+qq, wn, Jpeg.decode.up.cell(mode, 0, y0,
            ww, hh, aa), 0, y0, mode, ww, hh, wn), Nat.add(Nat.add(1n+wn, mr), xn)),
            List.get(&2, U32, Jpeg.decode.up.walk(1n+qq, wn, Jpeg.decode.up.cell(mode, 0, y0, ww, hh, aa), 0, y0, mode,
              ww, hh, wn), Nat.add(1n+wn, Nat.add(mr, xn))),
            Some{Jpeg.decode.up.mix(mode, Laws.jpg.idx(xn, 0), Laws.jpg.idx(rr, y1), D1.jpg.val(Array.get(U32, aa,
              (Laws.jpg.idx(rr, y1) * ww + Laws.jpg.idx(xn, 0) : U32))), D1.jpg.val(Array.get(U32, aa,
              (Laws.jpg.idx(rr, y1) * ww + Jpeg.decode.up.far(Laws.jpg.idx(xn, 0), ww) : U32))),
              D1.jpg.val(Array.get(U32, aa, (Jpeg.decode.up.far(Laws.jpg.idx(rr, y1), hh) * ww + Laws.jpg.idx(xn, 0) :
              U32))), D1.jpg.val(Array.get(U32, aa, (Jpeg.decode.up.far(Laws.jpg.idx(rr, y1), hh) * ww +
              Jpeg.decode.up.far(Laws.jpg.idx(xn, 0), ww) : U32))))},
            Equal.cong(Nat, Maybe<&2, U32>, nn => List.get(&2, U32, Jpeg.decode.up.walk(1n+qq, wn,
              Jpeg.decode.up.cell(mode, 0, y0, ww, hh, aa), 0, y0, mode, ww, hh, wn), nn),
            Nat.add(Nat.add(1n+wn, mr), xn), Nat.add(1n+wn, Nat.add(mr, xn)), ea),
            Equal.trans(Maybe<&2, U32>, List.get(&2, U32, Jpeg.decode.up.walk(1n+qq, wn, Jpeg.decode.up.cell(mode, 0,
              y0, ww, hh, aa), 0, y0, mode, ww, hh, wn), Nat.add(1n+wn, Nat.add(mr, xn))),
            List.get(&2, U32, Jpeg.decode.up.walk(qq, wn, Jpeg.decode.up.cell(mode, 0, y1, ww, hh, aa), 0, y1, mode,
              ww, hh, wn), Nat.add(mr, xn)),
            Some{Jpeg.decode.up.mix(mode, Laws.jpg.idx(xn, 0), Laws.jpg.idx(rr, y1), D1.jpg.val(Array.get(U32, aa,
              (Laws.jpg.idx(rr, y1) * ww + Laws.jpg.idx(xn, 0) : U32))), D1.jpg.val(Array.get(U32, aa,
              (Laws.jpg.idx(rr, y1) * ww + Jpeg.decode.up.far(Laws.jpg.idx(xn, 0), ww) : U32))),
              D1.jpg.val(Array.get(U32, aa, (Jpeg.decode.up.far(Laws.jpg.idx(rr, y1), hh) * ww + Laws.jpg.idx(xn, 0) :
              U32))), D1.jpg.val(Array.get(U32, aa, (Jpeg.decode.up.far(Laws.jpg.idx(rr, y1), hh) * ww +
              Jpeg.decode.up.far(Laws.jpg.idx(xn, 0), ww) : U32))))},
            walk.skip(wn, qq, Nat.add(mr, xn), 0, y0, mode, ww, hh, wn, aa, mk5(aa, d0)),
            rows.at(rr, qq, xn, y1, mode, ww, hh, wn, aa, mk5(aa, d1), hy, hx)))

# a plane's filtered rows: pixel yn * wn + xn is the filter at (xn, yn)
def rows.top(
  hn: Nat,
  wn: Nat,
  +xn: Nat,
  +yn: Nat,
  +mode: U32,
  +ww: U32,
  +hh: U32,
  aa: Array<U32>,
  hyn: {Nat.is_lt(yn, hn) == True{} : Bool},
  hxn: {Nat.is_lt(xn, wn) == True{} : Bool}
) -> AtIs(Jpeg.decode.up.rows(hn, wn, mode, ww, hh, aa), Nat.add(Nat.mul(yn, wn), xn), mode, Laws.jpg.idx(xn, 0),
  Laws.jpg.idx(yn, 0), ww, hh, aa):
  match hn:
    case 0n:
      Empty.absurd(AtIs(Jpeg.decode.up.rows(0n, wn, mode, ww, hh, aa), Nat.add(Nat.mul(yn, wn), xn), mode,
        Laws.jpg.idx(xn, 0), Laws.jpg.idx(yn, 0), ww, hh, aa), M1.false_true(Equal.trans(Bool, False{},
        Nat.is_lt(yn, 0n), True{}, M1.lt_zero_false(yn), hyn)))
    case 1n+(+qq):
      match wn:
        case 0n:
          Empty.absurd(AtIs(Jpeg.decode.up.rows(1n+qq, 0n, mode, ww, hh, aa), Nat.add(Nat.mul(yn, 0n), xn), mode,
            Laws.jpg.idx(xn, 0), Laws.jpg.idx(yn, 0), ww, hh, aa), M1.false_true(Equal.trans(Bool,
            False{}, Nat.is_lt(xn, 0n), True{}, M1.lt_zero_false(xn), hxn)))
        case 1n+(+pp):
          +hy = {Equal.trans(Bool, Nat.is_le(1n+yn, 1n+qq), Nat.is_lt(yn, 1n+qq), True{}, Equal.sym(Bool,
            Nat.is_lt(yn, 1n+qq), Nat.is_le(1n+yn, 1n+qq), M1.lt_le_succ(yn, 1n+qq)), hyn) : {Nat.is_le(yn, qq) ==
            True{} : Bool}}
          +hx = {Equal.trans(Bool, Nat.is_le(1n+xn, 1n+pp), Nat.is_lt(xn, 1n+pp), True{}, Equal.sym(Bool,
            Nat.is_lt(xn, 1n+pp), Nat.is_le(1n+xn, 1n+pp), M1.lt_le_succ(xn, 1n+pp)), hxn) : {Nat.is_le(xn, pp) ==
            True{} : Bool}}
          rows.at(yn, qq, xn, 0, mode, ww, hh, pp, aa, mk5(aa, M2.dup(aa)), hy, hx)

# a component's painted plane at a pixel inside the frame is jpg.point over its units
def up.pv(
  +cc: U32,
  +us: List<&2, Laws.JUnit>,
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
  +aa: U32,
  +bb: U32,
  +hD: {Nat.is_lt(Jpeg.decode.depth((ww * hh : U32)), 32n) == True{} : Bool},
  +hfD: {Nat.is_le(Nat.mul(U32.to_nat(ww), U32.to_nat(hh)), Nat.pow(2n, Jpeg.decode.depth((ww * hh : U32)))) == True{} :
    Bool},
  +ha: {U32.is_lt(aa, ww) == True{} : Bool},
  +hb: {U32.is_lt(bb, hh) == True{} : Bool}
) -> {D1.jpg.val(Array.get(U32, Laws.jpg.paint.all(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan,
  Jpeg.decode.plane((ww * hh : U32))), (bb * ww + aa : U32))) == Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs,
  vs, tq, hmax, vmax}, scan, aa, bb, 0) : U32}:
  Equal.trans(U32, D1.jpg.val(Array.get(U32, Laws.jpg.paint.all(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax,
    vmax}, scan, Jpeg.decode.plane((ww * hh : U32))), (bb * ww + aa : U32))), Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh,
    nf, ids, hs, vs, tq, hmax, vmax}, scan, aa, bb, D1.jpg.val(Array.get(U32, Jpeg.decode.plane((ww * hh : U32)), (bb *
    ww + aa : U32)))),
    Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, aa, bb, 0),
      Laws.jpeg_plane_at(Jpeg.decode.depth((ww * hh : U32)), Jpeg.decode.plane((ww * hh : U32)),
    plane_perfect((ww * hh : U32)), hD, us, cc, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan, hfD, aa, bb, ha, hb),
    Equal.cong(U32, U32, vv => Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, aa,
      bb, vv), D1.jpg.val(Array.get(U32, Jpeg.decode.plane((ww * hh : U32)), (bb * ww + aa : U32))), 0,
    plane_zero((ww * hh : U32), (bb * ww + aa : U32))))

# a component's point at (aa, bb), as its painted plane holds it
def PtEq(
  +cc: U32,
  +us: List<&2, Laws.JUnit>,
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
  +aa: U32,
  +bb: U32
) -> Type:
  {Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, aa, bb, 0) ==
    D1.jpg.val(Array.get(U32, Laws.jpg.paint.all(us, cc,
    Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, Jpeg.decode.plane((ww * hh : U32))), (bb * ww + aa :
      U32))) : U32}

# PtEq at the farther pixel across and the farther row down
def PtEqD(
  +cc: U32,
  +us: List<&2, Laws.JUnit>,
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
  +yy: U32
) -> Type:
  PtEq(cc, us, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan, Jpeg.decode.up.far(xx, ww), Jpeg.decode.up.far(yy, hh))

# the filter of the painted plane's values, at the counted pixel, is the filter of the component's points
def up.fin(
  +cc: U32,
  +us: List<&2, Laws.JUnit>,
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
  ex: {xx == Laws.jpg.idx(U32.to_nat(xx), 0) : U32},
  ey: {yy == Laws.jpg.idx(U32.to_nat(yy), 0) : U32},
  e0: PtEq(cc, us, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan, xx, yy),
  e1: PtEq(cc, us, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan, Jpeg.decode.up.far(xx, ww), yy),
  e2: PtEq(cc, us, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan, xx, Jpeg.decode.up.far(yy, hh)),
  e3: PtEqD(cc, us, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan, xx, yy)
) -> {Some{Jpeg.decode.up.mix(Jpeg.decode.up.mode(Jpeg.decode.at(hs, cc), Jpeg.decode.at(vs, cc), hmax, vmax, ww),
  Laws.jpg.idx(U32.to_nat(xx), 0), Laws.jpg.idx(U32.to_nat(yy), 0), D1.jpg.val(Array.get(U32, Laws.jpg.paint.all(us,
  cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, Jpeg.decode.plane((ww * hh : U32))),
  (Laws.jpg.idx(U32.to_nat(yy), 0) * ww + Laws.jpg.idx(U32.to_nat(xx), 0) : U32))), D1.jpg.val(Array.get(U32,
  Laws.jpg.paint.all(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, Jpeg.decode.plane((ww * hh :
  U32))), (Laws.jpg.idx(U32.to_nat(yy), 0) * ww + Jpeg.decode.up.far(Laws.jpg.idx(U32.to_nat(xx), 0), ww) : U32))),
  D1.jpg.val(Array.get(U32, Laws.jpg.paint.all(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan,
  Jpeg.decode.plane((ww * hh : U32))), (Jpeg.decode.up.far(Laws.jpg.idx(U32.to_nat(yy), 0), hh) * ww +
  Laws.jpg.idx(U32.to_nat(xx), 0) : U32))), D1.jpg.val(Array.get(U32, Laws.jpg.paint.all(us, cc, Jpeg.Frame{ww, hh, nf,
  ids, hs, vs, tq, hmax, vmax}, scan, Jpeg.decode.plane((ww * hh : U32))),
  (Jpeg.decode.up.far(Laws.jpg.idx(U32.to_nat(yy), 0), hh) * ww + Jpeg.decode.up.far(Laws.jpg.idx(U32.to_nat(xx), 0),
  ww) : U32))))} == Some{Laws.jpg.up.mix(Jpeg.decode.up.mode(Jpeg.decode.at(hs, cc), Jpeg.decode.at(vs, cc), hmax,
  vmax, ww), xx, yy, Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy, 0),
  Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, Laws.jpg.up.far(xx, ww), yy, 0),
  Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, Laws.jpg.up.far(yy, hh), 0),
  Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, Laws.jpg.up.far(xx, ww),
  Laws.jpg.up.far(yy, hh), 0))} :
  Maybe<&2, U32>}:
  +m = Jpeg.decode.up.mode(Jpeg.decode.at(hs, cc), Jpeg.decode.at(vs, cc), hmax, vmax, ww)
  %ex : {Some{Jpeg.decode.up.mix(m, _, Laws.jpg.idx(U32.to_nat(yy), 0), D1.jpg.val(Array.get(U32,
    Laws.jpg.paint.all(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, Jpeg.decode.plane((ww * hh :
    U32))), (Laws.jpg.idx(U32.to_nat(yy), 0) * ww + _ : U32))), D1.jpg.val(Array.get(U32, Laws.jpg.paint.all(us, cc,
    Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, Jpeg.decode.plane((ww * hh : U32))),
    (Laws.jpg.idx(U32.to_nat(yy), 0) * ww + Jpeg.decode.up.far(_, ww) : U32))), D1.jpg.val(Array.get(U32,
    Laws.jpg.paint.all(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, Jpeg.decode.plane((ww * hh :
    U32))), (Jpeg.decode.up.far(Laws.jpg.idx(U32.to_nat(yy), 0), hh) * ww + _ : U32))), D1.jpg.val(Array.get(U32,
    Laws.jpg.paint.all(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, Jpeg.decode.plane((ww * hh :
    U32))), (Jpeg.decode.up.far(Laws.jpg.idx(U32.to_nat(yy), 0), hh) * ww + Jpeg.decode.up.far(_, ww) : U32))))} ==
    Some{Laws.jpg.up.mix(Jpeg.decode.up.mode(Jpeg.decode.at(hs, cc), Jpeg.decode.at(vs, cc), hmax, vmax, ww), xx, yy,
    Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy, 0), Laws.jpg.point(us,
    cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, Laws.jpg.up.far(xx, ww), yy, 0), Laws.jpg.point(us,
    cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, Laws.jpg.up.far(yy, hh), 0), Laws.jpg.point(us,
    cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, Laws.jpg.up.far(xx, ww), Laws.jpg.up.far(yy, hh),
    0))} : Maybe<&2, U32>}
  %ey : {Some{Jpeg.decode.up.mix(m, xx, _, D1.jpg.val(Array.get(U32, Laws.jpg.paint.all(us, cc, Jpeg.Frame{ww, hh, nf,
    ids, hs, vs, tq, hmax, vmax}, scan, Jpeg.decode.plane((ww * hh : U32))), (_ * ww + xx : U32))),
    D1.jpg.val(Array.get(U32, Laws.jpg.paint.all(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan,
    Jpeg.decode.plane((ww * hh : U32))), (_ * ww + Jpeg.decode.up.far(xx, ww) : U32))), D1.jpg.val(Array.get(U32,
    Laws.jpg.paint.all(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, Jpeg.decode.plane((ww * hh :
    U32))), (Jpeg.decode.up.far(_, hh) * ww + xx : U32))), D1.jpg.val(Array.get(U32, Laws.jpg.paint.all(us, cc,
    Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, Jpeg.decode.plane((ww * hh : U32))),
    (Jpeg.decode.up.far(_, hh) * ww + Jpeg.decode.up.far(xx, ww) : U32))))} ==
    Some{Laws.jpg.up.mix(Jpeg.decode.up.mode(Jpeg.decode.at(hs, cc), Jpeg.decode.at(vs, cc), hmax, vmax, ww), xx, yy,
    Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy, 0), Laws.jpg.point(us,
    cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, Laws.jpg.up.far(xx, ww), yy, 0), Laws.jpg.point(us,
    cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, Laws.jpg.up.far(yy, hh), 0), Laws.jpg.point(us,
    cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, Laws.jpg.up.far(xx, ww), Laws.jpg.up.far(yy, hh),
    0))} : Maybe<&2, U32>}
  %e0 : {Some{Jpeg.decode.up.mix(m, xx, yy, _, D1.jpg.val(Array.get(U32, Laws.jpg.paint.all(us, cc, Jpeg.Frame{ww, hh,
    nf, ids, hs, vs, tq, hmax, vmax}, scan, Jpeg.decode.plane((ww * hh : U32))), (yy * ww + Jpeg.decode.up.far(xx, ww)
    : U32))), D1.jpg.val(Array.get(U32, Laws.jpg.paint.all(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax},
    scan, Jpeg.decode.plane((ww * hh : U32))), (Jpeg.decode.up.far(yy, hh) * ww + xx : U32))),
    D1.jpg.val(Array.get(U32, Laws.jpg.paint.all(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan,
    Jpeg.decode.plane((ww * hh : U32))), (Jpeg.decode.up.far(yy, hh) * ww + Jpeg.decode.up.far(xx, ww) : U32))))} ==
    Some{Laws.jpg.up.mix(Jpeg.decode.up.mode(Jpeg.decode.at(hs, cc), Jpeg.decode.at(vs, cc), hmax, vmax, ww), xx, yy,
    Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy, 0), Laws.jpg.point(us,
    cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, Laws.jpg.up.far(xx, ww), yy, 0), Laws.jpg.point(us,
    cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, Laws.jpg.up.far(yy, hh), 0), Laws.jpg.point(us,
    cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, Laws.jpg.up.far(xx, ww), Laws.jpg.up.far(yy, hh),
    0))} :
    Maybe<&2, U32>}
  %e1 : {Some{Jpeg.decode.up.mix(m, xx, yy, Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax},
    scan, xx, yy, 0), _, D1.jpg.val(Array.get(U32, Laws.jpg.paint.all(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq,
    hmax, vmax}, scan, Jpeg.decode.plane((ww * hh : U32))), (Jpeg.decode.up.far(yy, hh) * ww + xx : U32))),
    D1.jpg.val(Array.get(U32, Laws.jpg.paint.all(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan,
    Jpeg.decode.plane((ww * hh : U32))), (Jpeg.decode.up.far(yy, hh) * ww + Jpeg.decode.up.far(xx, ww) : U32))))} ==
    Some{Laws.jpg.up.mix(Jpeg.decode.up.mode(Jpeg.decode.at(hs, cc), Jpeg.decode.at(vs, cc), hmax, vmax, ww), xx, yy,
    Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy, 0), Laws.jpg.point(us,
    cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, Laws.jpg.up.far(xx, ww), yy, 0), Laws.jpg.point(us,
    cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, Laws.jpg.up.far(yy, hh), 0), Laws.jpg.point(us,
    cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, Laws.jpg.up.far(xx, ww), Laws.jpg.up.far(yy, hh),
    0))} :
    Maybe<&2, U32>}
  %e2 : {Some{Jpeg.decode.up.mix(m, xx, yy, Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax},
    scan, xx, yy, 0), Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan,
    Jpeg.decode.up.far(xx, ww), yy, 0), _, D1.jpg.val(Array.get(U32, Laws.jpg.paint.all(us, cc, Jpeg.Frame{ww, hh, nf,
    ids, hs, vs, tq, hmax, vmax}, scan, Jpeg.decode.plane((ww * hh : U32))), (Jpeg.decode.up.far(yy, hh) * ww +
    Jpeg.decode.up.far(xx, ww) : U32))))} == Some{Laws.jpg.up.mix(Jpeg.decode.up.mode(Jpeg.decode.at(hs, cc),
    Jpeg.decode.at(vs, cc), hmax, vmax, ww), xx, yy, Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq,
    hmax, vmax}, scan, xx, yy, 0), Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan,
    Laws.jpg.up.far(xx, ww), yy, 0), Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan,
    xx, Laws.jpg.up.far(yy, hh), 0), Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan,
    Laws.jpg.up.far(xx, ww), Laws.jpg.up.far(yy, hh), 0))} :
    Maybe<&2, U32>}
  %e3 : {Some{Jpeg.decode.up.mix(m, xx, yy, Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax},
    scan, xx, yy, 0), Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan,
    Jpeg.decode.up.far(xx, ww), yy, 0), Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax},
    scan, xx, Jpeg.decode.up.far(yy, hh), 0), _)} == Some{Laws.jpg.up.mix(Jpeg.decode.up.mode(Jpeg.decode.at(hs, cc),
    Jpeg.decode.at(vs, cc), hmax, vmax, ww), xx, yy, Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq,
    hmax, vmax}, scan, xx, yy, 0), Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan,
    Laws.jpg.up.far(xx, ww), yy, 0), Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan,
    xx, Laws.jpg.up.far(yy, hh), 0), Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan,
    Laws.jpg.up.far(xx, ww), Laws.jpg.up.far(yy, hh), 0))} :
    Maybe<&2, U32>}
  {==}

# the statement of w13.up.z: the plane read out, as painted or filtered by zero, is the component's value
def UpGoal(
  zero: Bool,
  +cc: U32,
  +us: List<&2, Laws.JUnit>,
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
  +yy: U32
) -> Type:
  {List.get(&2, U32, Jpeg.decode.up.out.z(zero, Jpeg.decode.up.mode(Jpeg.decode.at(hs, cc), Jpeg.decode.at(vs, cc),
    hmax, vmax, ww), U32.to_nat((ww * hh : U32)), ww, hh, Laws.jpg.paint.all(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs,
    vs, tq, hmax, vmax}, scan, Jpeg.decode.plane((ww * hh : U32)))), U32.to_nat((yy * ww + xx : U32))) ==
    Some{Bool.pick(U32, zero, Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy,
      0), Laws.jpg.up.mix(Jpeg.decode.up.mode(Jpeg.decode.at(hs, cc), Jpeg.decode.at(vs, cc), hmax, vmax, ww), xx, yy,
      Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy, 0), Laws.jpg.point(us,
      cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, Laws.jpg.up.far(xx, ww), yy, 0),
      Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, Laws.jpg.up.far(yy, hh),
      0), Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, Laws.jpg.up.far(xx, ww),
      Laws.jpg.up.far(yy, hh), 0)))} : Maybe<&2, U32>}

# a component's plane read out, as painted (w13.pt) or filtered (rows.top, then up.pv at the four pixels)
def w13.up.z(
  zero: Bool,
  +cc: U32,
  +us: List<&2, Laws.JUnit>,
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
  +hD: {Nat.is_lt(Jpeg.decode.depth((ww * hh : U32)), 32n) == True{} : Bool},
  +hfD: {Nat.is_le(Nat.mul(U32.to_nat(ww), U32.to_nat(hh)), Nat.pow(2n, Jpeg.decode.depth((ww * hh : U32)))) == True{} :
    Bool},
  +hK: {Nat.is_lt(U32.to_nat((yy * ww + xx : U32)), U32.to_nat((ww * hh : U32))) == True{} : Bool},
  +h_xx: {U32.is_lt(xx, ww) == True{} : Bool},
  +h_yy: {U32.is_lt(yy, hh) == True{} : Bool}
) -> UpGoal(zero, cc, us, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan, xx, yy):
  match zero:
    case True{}:
      w13.pt(cc, us, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan, xx, yy, hD, hfD, hK, h_xx, h_yy)
    case False{}:
      +xn = U32.to_nat(xx)
      +yn = U32.to_nat(yy)
      +hxf = far.lt(xx, ww, h_xx)
      +hyf = far.lt(yy, hh, h_yy)
      +ei = {idx_nat(ww, hh, xx, yy, Jpeg.decode.depth((ww * hh : U32)), hD, hfD, h_xx, h_yy) : {U32.to_nat((yy * ww +
        xx : U32)) ==
        Nat.add(Nat.mul(yn, U32.to_nat(ww)), xn) : Nat}}
      ek = Equal.sym(Nat, U32.to_nat((yy * ww + xx : U32)), Nat.add(Nat.mul(yn, U32.to_nat(ww)), xn), ei)
      %ek : {List.get(&2, U32, Jpeg.decode.up.rows(U32.to_nat(hh), U32.to_nat(ww),
        Jpeg.decode.up.mode(Jpeg.decode.at(hs, cc), Jpeg.decode.at(vs, cc), hmax, vmax, ww), ww, hh,
        Laws.jpg.paint.all(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, Jpeg.decode.plane((ww *
        hh : U32)))), _) ==
        Some{Laws.jpg.up.mix(Jpeg.decode.up.mode(Jpeg.decode.at(hs, cc), Jpeg.decode.at(vs, cc), hmax, vmax, ww), xx,
          yy, Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy, 0),
          Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, Laws.jpg.up.far(xx, ww),
          yy, 0), Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx,
          Laws.jpg.up.far(yy, hh), 0), Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax},
          scan, Laws.jpg.up.far(xx, ww), Laws.jpg.up.far(yy, hh), 0))} : Maybe<&2, U32>}
      ex = Equal.sym(U32, Laws.jpg.idx(xn, 0), xx, idx.of(xx))
      ey = Equal.sym(U32, Laws.jpg.idx(yn, 0), yy, idx.of(yy))
      e0 = Equal.sym(U32, D1.jpg.val(Array.get(U32, Laws.jpg.paint.all(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq,
        hmax, vmax}, scan, Jpeg.decode.plane((ww * hh : U32))), (yy * ww + xx : U32))), Laws.jpg.point(us, cc,
        Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy, 0), up.pv(cc, us, ww, hh, nf, ids, hs, vs,
        tq, hmax, vmax, scan,
        xx, yy, hD, hfD, h_xx, h_yy))
      e1 = Equal.sym(U32, D1.jpg.val(Array.get(U32, Laws.jpg.paint.all(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq,
        hmax, vmax}, scan, Jpeg.decode.plane((ww * hh : U32))), (yy * ww + Jpeg.decode.up.far(xx, ww) : U32))),
        Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, Jpeg.decode.up.far(xx, ww),
        yy, 0), up.pv(cc, us, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan,
        Jpeg.decode.up.far(xx, ww), yy, hD, hfD, hxf, h_yy))
      e2 = Equal.sym(U32, D1.jpg.val(Array.get(U32, Laws.jpg.paint.all(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq,
        hmax, vmax}, scan, Jpeg.decode.plane((ww * hh : U32))), (Jpeg.decode.up.far(yy, hh) * ww + xx : U32))),
        Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, Jpeg.decode.up.far(yy,
        hh), 0), up.pv(cc, us, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan,
        xx, Jpeg.decode.up.far(yy, hh), hD, hfD, h_xx, hyf))
      e3 = Equal.sym(U32, D1.jpg.val(Array.get(U32, Laws.jpg.paint.all(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq,
        hmax, vmax}, scan, Jpeg.decode.plane((ww * hh : U32))), (Jpeg.decode.up.far(yy, hh) * ww +
        Jpeg.decode.up.far(xx, ww) : U32))), Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax,
        vmax}, scan, Jpeg.decode.up.far(xx, ww), Jpeg.decode.up.far(yy, hh), 0), up.pv(cc, us, ww, hh, nf, ids, hs, vs,
        tq, hmax, vmax, scan,
        Jpeg.decode.up.far(xx, ww), Jpeg.decode.up.far(yy, hh), hD, hfD, hxf, hyf))
      Equal.trans(Maybe<&2, U32>, List.get(&2, U32, Jpeg.decode.up.rows(U32.to_nat(hh), U32.to_nat(ww),
        Jpeg.decode.up.mode(Jpeg.decode.at(hs, cc), Jpeg.decode.at(vs, cc), hmax, vmax, ww), ww, hh,
        Laws.jpg.paint.all(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, Jpeg.decode.plane((ww *
          hh : U32)))), Nat.add(Nat.mul(yn, U32.to_nat(ww)), xn)),
          Some{Jpeg.decode.up.mix(Jpeg.decode.up.mode(Jpeg.decode.at(hs, cc), Jpeg.decode.at(vs, cc), hmax, vmax, ww),
          Laws.jpg.idx(xn, 0), Laws.jpg.idx(yn, 0), D1.jpg.val(Array.get(U32, Laws.jpg.paint.all(us, cc, Jpeg.Frame{ww,
          hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, Jpeg.decode.plane((ww * hh : U32))), (Laws.jpg.idx(yn, 0) * ww +
          Laws.jpg.idx(xn, 0) : U32))), D1.jpg.val(Array.get(U32, Laws.jpg.paint.all(us, cc, Jpeg.Frame{ww, hh, nf,
          ids, hs, vs, tq, hmax, vmax}, scan, Jpeg.decode.plane((ww * hh : U32))), (Laws.jpg.idx(yn, 0) * ww +
          Jpeg.decode.up.far(Laws.jpg.idx(xn, 0), ww) : U32))), D1.jpg.val(Array.get(U32, Laws.jpg.paint.all(us, cc,
          Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, Jpeg.decode.plane((ww * hh : U32))),
          (Jpeg.decode.up.far(Laws.jpg.idx(yn, 0), hh) * ww + Laws.jpg.idx(xn, 0) : U32))), D1.jpg.val(Array.get(U32,
          Laws.jpg.paint.all(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, Jpeg.decode.plane((ww *
          hh : U32))), (Jpeg.decode.up.far(Laws.jpg.idx(yn, 0), hh) * ww + Jpeg.decode.up.far(Laws.jpg.idx(xn, 0), ww)
          : U32))))},
        Some{Laws.jpg.up.mix(Jpeg.decode.up.mode(Jpeg.decode.at(hs, cc), Jpeg.decode.at(vs, cc), hmax, vmax, ww), xx,
          yy, Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy, 0),
          Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, Laws.jpg.up.far(xx, ww),
          yy, 0), Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx,
          Laws.jpg.up.far(yy, hh), 0), Laws.jpg.point(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax},
          scan, Laws.jpg.up.far(xx, ww), Laws.jpg.up.far(yy, hh), 0))}, rows.top(U32.to_nat(hh), U32.to_nat(ww), xn,
          yn, Jpeg.decode.up.mode(Jpeg.decode.at(hs, cc), Jpeg.decode.at(vs, cc), hmax, vmax, ww), ww, hh,
          Laws.jpg.paint.all(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, Jpeg.decode.plane((ww *
          hh : U32))), lt_of(yy, hh, h_yy),
        lt_of(xx, ww, h_xx)), up.fin(cc, us, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan, xx, yy, ex, ey, e0, e1, e2,
        e3))

# a component's plane read out as libjpeg upsamples it: point k is jpg.up.value over the component's units
def w13.up(
  +cc: U32,
  +us: List<&2, Laws.JUnit>,
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
  +hD: {Nat.is_lt(Jpeg.decode.depth((ww * hh : U32)), 32n) == True{} : Bool},
  +hfD: {Nat.is_le(Nat.mul(U32.to_nat(ww), U32.to_nat(hh)), Nat.pow(2n, Jpeg.decode.depth((ww * hh : U32)))) == True{} :
    Bool},
  +hK: {Nat.is_lt(U32.to_nat((yy * ww + xx : U32)), U32.to_nat((ww * hh : U32))) == True{} : Bool},
  +h_xx: {U32.is_lt(xx, ww) == True{} : Bool},
  +h_yy: {U32.is_lt(yy, hh) == True{} : Bool}
) -> {List.get(&2, U32, Jpeg.decode.up.out(Jpeg.decode.up.mode(Jpeg.decode.at(hs, cc), Jpeg.decode.at(vs, cc), hmax,
  vmax, ww), U32.to_nat((ww * hh : U32)), ww, hh, Laws.jpg.paint.all(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq,
  hmax, vmax}, scan, Jpeg.decode.plane((ww * hh : U32)))), U32.to_nat((yy * ww + xx : U32))) ==
  Some{Laws.jpg.up.value(us, cc, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy)} : Maybe<&2, U32>}:
  w13.up.z(U32.is_eq(Jpeg.decode.up.mode(Jpeg.decode.at(hs, cc), Jpeg.decode.at(vs, cc), hmax, vmax, ww), 0), cc, us,
    ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan, xx, yy, hD, hfD, hK, h_xx,
    h_yy)

# three samples coded as R, G and B, when all three are there
def dir3(rr: Maybe<&2, U32>, gg: Maybe<&2, U32>, bb: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match rr:
    case None{}:
      None{}
    case Some{rv}:
      match gg:
        case None{}:
          None{}
        case Some{gv}:
          match bb:
            case None{}:
              None{}
            case Some{bv}:
              Some{Jpeg.direct(rv, gv, bv)}

# no G sample: no sample, whatever the R and B samples
def dir3.ng(aa: Maybe<&2, U32>, cc: Maybe<&2, U32>) -> {None{} == dir3(aa, None{}, cc) : Maybe<&2, U32>}:
  match aa:
    case None{}:
      {==}
    case Some{_av}:
      {==}

# no B sample: no sample, whatever the R and G samples
def dir3.nb(aa: Maybe<&2, U32>, bb: Maybe<&2, U32>) -> {None{} == dir3(aa, bb, None{}) : Maybe<&2, U32>}:
  match aa bb:
    case None{} _bb:
      {==}
    case Some{_av} None{}:
      {==}
    case Some{_av} Some{_bv}:
      {==}

# the pass for samples coded as R, G and B is pointwise: sample k of decode.directs is Jpeg.direct of point k's samples
def dirs.at(
  +rs: List<&2, U32>,
  +gs: List<&2, U32>,
  +bs: List<&2, U32>,
  +kk: Nat
) -> {List.get(&2, U32, Jpeg.decode.directs(rs, gs, bs), kk) ==
  dir3(List.get(&2, U32, rs, kk), List.get(&2, U32, gs, kk), List.get(&2, U32, bs, kk)) : Maybe<&2, U32>}:
  match rs gs bs kk:
    case Nil{} _gs _bs _kk:
      {==}
    case _rv <> _rt Nil{} _bs 0n:
      {==}
    case _rv <> rt Nil{} bs 1n+pp:
      dir3.ng(List.get(&2, U32, rt, pp), List.get(&2, U32, bs, 1n+pp))
    case _rv <> _rt _gv <> _gt Nil{} 0n:
      {==}
    case _rv <> rt _gv <> gt Nil{} 1n+pp:
      dir3.nb(List.get(&2, U32, rt, pp), List.get(&2, U32, gt, pp))
    case _rv <> _rt _gv <> _gt _bv <> _bt 0n:
      {==}
    case _rv <> rt _gv <> gt _bv <> bt 1n+pp:
      dirs.at(rt, gt, bt, pp)

# three components' points read out, each its jpg.point: the sample the pass of the picture's coding (R, G and B as
# coded, or T.871) makes of them
def w13.pack(
  rgb: Bool,
  +us: List<&2, Laws.JUnit>,
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
  +eb1: {U32.is_eq(nf, 1) == False{} : Bool},
  +hD: {Nat.is_lt(Jpeg.decode.depth((ww * hh : U32)), 32n) == True{} : Bool},
  +hfD: {Nat.is_le(Nat.mul(U32.to_nat(ww), U32.to_nat(hh)), Nat.pow(2n, Jpeg.decode.depth((ww * hh : U32)))) == True{} :
    Bool},
  +hK: {Nat.is_lt(U32.to_nat((yy * ww + xx : U32)), U32.to_nat((ww * hh : U32))) == True{} : Bool},
  +h_xx: {U32.is_lt(xx, ww) == True{} : Bool},
  +h_yy: {U32.is_lt(yy, hh) == True{} : Bool}
) -> {List.get(&2, U32, Jpeg.decode.done.pack(rgb, U32.to_nat((ww * hh : U32)), ww, hh, Jpeg.decode.ups(hs, vs, hmax,
  vmax, ww), Laws.jpg.paint.all(us, 0,
  Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, Jpeg.decode.plane((ww * hh : U32))),
  Laws.jpg.paint.all(us, 1, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, Jpeg.decode.plane((ww * hh :
  U32))), Laws.jpg.paint.all(us, 2, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, Jpeg.decode.plane((ww *
  hh : U32)))), U32.to_nat((yy * ww + xx : U32))) ==
  Some{Laws.jpg.colour(nf, rgb, Laws.jpg.up.value(us, 0, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx,
    yy), Laws.jpg.up.value(us, 1, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy),
    Laws.jpg.up.value(us, 2, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy))} : Maybe<&2, U32>}:
  match rgb:
    case True{}:
      +py = Jpeg.decode.up.out(Jpeg.decode.up.mode(Jpeg.decode.at(hs, 0), Jpeg.decode.at(vs, 0), hmax, vmax, ww),
        U32.to_nat((ww * hh : U32)), ww, hh, Laws.jpg.paint.all(us, 0, Jpeg.Frame{ww, hh, nf, ids, hs,
        vs,
        tq, hmax, vmax}, scan, Jpeg.decode.plane((ww * hh : U32))))
      +pb = Jpeg.decode.up.out(Jpeg.decode.up.mode(Jpeg.decode.at(hs, 1), Jpeg.decode.at(vs, 1), hmax, vmax, ww),
        U32.to_nat((ww * hh : U32)), ww, hh, Laws.jpg.paint.all(us, 1, Jpeg.Frame{ww, hh, nf, ids, hs,
        vs,
        tq, hmax, vmax}, scan, Jpeg.decode.plane((ww * hh : U32))))
      +pr = Jpeg.decode.up.out(Jpeg.decode.up.mode(Jpeg.decode.at(hs, 2), Jpeg.decode.at(vs, 2), hmax, vmax, ww),
        U32.to_nat((ww * hh : U32)), ww, hh, Laws.jpg.paint.all(us, 2, Jpeg.Frame{ww, hh, nf, ids, hs,
        vs,
        tq, hmax, vmax}, scan, Jpeg.decode.plane((ww * hh : U32))))
      +v0 = Laws.jpg.up.value(us, 0, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy)
      +v1 = Laws.jpg.up.value(us, 1, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy)
      +v2 = Laws.jpg.up.value(us, 2, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy)
      +ey = w13.up(0, us, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan, xx, yy, hD, hfD, hK, h_xx, h_yy)
      +eb = w13.up(1, us, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan, xx, yy, hD, hfD, hK, h_xx, h_yy)
      +er = w13.up(2, us, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan, xx, yy, hD, hfD, hK, h_xx, h_yy)
      +gy = List.get(&2, U32, py, U32.to_nat((yy * ww + xx : U32)))
      +gb = List.get(&2, U32, pb, U32.to_nat((yy * ww + xx : U32)))
      +gr = List.get(&2, U32, pr, U32.to_nat((yy * ww + xx : U32)))
      +e3 = {Equal.trans(Maybe<&2, U32>, dir3(gy, gb, gr), dir3(Some{v0}, gb, gr), Some{Jpeg.direct(v0, v1, v2)},
        Equal.cong(Maybe<&2, U32>, Maybe<&2, U32>, mm => dir3(mm, gb, gr), gy, Some{v0}, ey), Equal.trans(Maybe<&2,
        U32>, dir3(Some{v0}, gb, gr), dir3(Some{v0}, Some{v1}, gr), Some{Jpeg.direct(v0, v1, v2)},
        Equal.cong(Maybe<&2, U32>, Maybe<&2, U32>, mm => dir3(Some{v0}, mm, gr), gb, Some{v1}, eb),
        Equal.cong(Maybe<&2, U32>, Maybe<&2, U32>, mm => dir3(Some{v0}, Some{v1}, mm), gr, Some{v2}, er))) :
        {dir3(gy, gb, gr) == Some{Jpeg.direct(v0, v1, v2)} : Maybe<&2, U32>}}
      +ec = {Equal.cong(Bool, Maybe<&2, U32>, zz => {Some{Bool.pick(U32, zz, Jpeg.gray(v0), Jpeg.direct(v0, v1, v2))} :
        Maybe<&2, U32>}, U32.is_eq(nf, 1), False{}, eb1) : {Some{Laws.jpg.colour(nf, True{}, v0, v1, v2)} ==
        Some{Jpeg.direct(v0, v1, v2)} : Maybe<&2, U32>}}
      Equal.trans(Maybe<&2, U32>, List.get(&2, U32, Jpeg.decode.directs(py, pb, pr), U32.to_nat((yy * ww + xx : U32))),
        dir3(gy, gb, gr),
        Some{Laws.jpg.colour(nf, True{}, v0, v1, v2)}, dirs.at(py, pb, pr, U32.to_nat((yy * ww + xx : U32))),
          Equal.trans(Maybe<&2, U32>,
        dir3(gy, gb, gr), Some{Jpeg.direct(v0, v1, v2)}, Some{Laws.jpg.colour(nf, True{}, v0, v1, v2)}, e3,
        Equal.sym(Maybe<&2, U32>, Some{Laws.jpg.colour(nf, True{}, v0, v1, v2)}, Some{Jpeg.direct(v0, v1, v2)},
        ec)))
    case False{}:
      +py = Jpeg.decode.up.out(Jpeg.decode.up.mode(Jpeg.decode.at(hs, 0), Jpeg.decode.at(vs, 0), hmax, vmax, ww),
        U32.to_nat((ww * hh : U32)), ww, hh, Laws.jpg.paint.all(us, 0, Jpeg.Frame{ww, hh, nf, ids, hs,
        vs,
        tq, hmax, vmax}, scan, Jpeg.decode.plane((ww * hh : U32))))
      +pb = Jpeg.decode.up.out(Jpeg.decode.up.mode(Jpeg.decode.at(hs, 1), Jpeg.decode.at(vs, 1), hmax, vmax, ww),
        U32.to_nat((ww * hh : U32)), ww, hh, Laws.jpg.paint.all(us, 1, Jpeg.Frame{ww, hh, nf, ids, hs,
        vs,
        tq, hmax, vmax}, scan, Jpeg.decode.plane((ww * hh : U32))))
      +pr = Jpeg.decode.up.out(Jpeg.decode.up.mode(Jpeg.decode.at(hs, 2), Jpeg.decode.at(vs, 2), hmax, vmax, ww),
        U32.to_nat((ww * hh : U32)), ww, hh, Laws.jpg.paint.all(us, 2, Jpeg.Frame{ww, hh, nf, ids, hs,
        vs,
        tq, hmax, vmax}, scan, Jpeg.decode.plane((ww * hh : U32))))
      +v0 = Laws.jpg.up.value(us, 0, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy)
      +v1 = Laws.jpg.up.value(us, 1, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy)
      +v2 = Laws.jpg.up.value(us, 2, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy)
      +ey = w13.up(0, us, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan, xx, yy, hD, hfD, hK, h_xx, h_yy)
      +eb = w13.up(1, us, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan, xx, yy, hD, hfD, hK, h_xx, h_yy)
      +er = w13.up(2, us, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan, xx, yy, hD, hfD, hK, h_xx, h_yy)
      +gy = List.get(&2, U32, py, U32.to_nat((yy * ww + xx : U32)))
      +gb = List.get(&2, U32, pb, U32.to_nat((yy * ww + xx : U32)))
      +gr = List.get(&2, U32, pr, U32.to_nat((yy * ww + xx : U32)))
      +e3 = {Equal.trans(Maybe<&2, U32>, Laws.jpg.rgb3(gy, gb, gr), Laws.jpg.rgb3(Some{v0}, gb, gr),
        Some{Jpeg.rgb(v0, v1, v2)}, Equal.cong(Maybe<&2, U32>, Maybe<&2, U32>, mm => Laws.jpg.rgb3(mm, gb, gr), gy,
        Some{v0}, ey), Equal.trans(Maybe<&2, U32>, Laws.jpg.rgb3(Some{v0}, gb, gr), Laws.jpg.rgb3(Some{v0}, Some{v1},
        gr), Some{Jpeg.rgb(v0, v1, v2)}, Equal.cong(Maybe<&2, U32>, Maybe<&2, U32>, mm => Laws.jpg.rgb3(Some{v0}, mm,
        gr), gb, Some{v1}, eb), Equal.cong(Maybe<&2, U32>, Maybe<&2, U32>, mm => Laws.jpg.rgb3(Some{v0}, Some{v1},
        mm), gr, Some{v2}, er))) : {Laws.jpg.rgb3(gy, gb, gr) == Some{Jpeg.rgb(v0, v1, v2)} : Maybe<&2, U32>}}
      +ec = {Equal.cong(Bool, Maybe<&2, U32>, zz => {Some{Bool.pick(U32, zz, Jpeg.gray(v0), Jpeg.rgb(v0, v1, v2))} :
        Maybe<&2, U32>}, U32.is_eq(nf, 1), False{}, eb1) : {Some{Laws.jpg.colour(nf, False{}, v0, v1, v2)} ==
        Some{Jpeg.rgb(v0, v1, v2)} : Maybe<&2, U32>}}
      Equal.trans(Maybe<&2, U32>, List.get(&2, U32, Jpeg.decode.rgbs(py, pb, pr), U32.to_nat((yy * ww + xx : U32))),
        Laws.jpg.rgb3(gy, gb, gr),
        Some{Laws.jpg.colour(nf, False{}, v0, v1, v2)}, Laws.jpeg_rgbs_at(py, pb, pr, U32.to_nat((yy * ww + xx :
          U32))), Equal.trans(Maybe<&2,
        U32>, Laws.jpg.rgb3(gy, gb, gr), Some{Jpeg.rgb(v0, v1, v2)}, Some{Laws.jpg.colour(nf, False{}, v0, v1, v2)},
        e3, Equal.sym(Maybe<&2, U32>, Some{Laws.jpg.colour(nf, False{}, v0, v1, v2)}, Some{Jpeg.rgb(v0, v1, v2)},
        ec)))

# three components: the colour pass
def w13.nf3(
  bb: Bool,
  rgb: Bool,
  +us: List<&2, Laws.JUnit>,
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
  +eb1: {U32.is_eq(nf, 1) == False{} : Bool},
  +hD: {Nat.is_lt(Jpeg.decode.depth((ww * hh : U32)), 32n) == True{} : Bool},
  +hfD: {Nat.is_le(Nat.mul(U32.to_nat(ww), U32.to_nat(hh)), Nat.pow(2n, Jpeg.decode.depth((ww * hh : U32)))) == True{} :
    Bool},
  +hK: {Nat.is_lt(U32.to_nat((yy * ww + xx : U32)), U32.to_nat((ww * hh : U32))) == True{} : Bool},
  +h_xx: {U32.is_lt(xx, ww) == True{} : Bool},
  +h_yy: {U32.is_lt(yy, hh) == True{} : Bool}
) -> w13.Q(Jpeg.decode.done.nf3(bb, rgb, ww, hh, Jpeg.decode.ups(hs, vs, hmax, vmax, ww), Laws.jpg.paint.all(us, 0,
  Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq,
  hmax, vmax}, scan, Jpeg.decode.plane((ww * hh : U32))), Laws.jpg.paint.all(us, 1, Jpeg.Frame{ww, hh, nf, ids, hs, vs,
  tq, hmax, vmax}, scan, Jpeg.decode.plane((ww * hh : U32))), Laws.jpg.paint.all(us, 2, Jpeg.Frame{ww, hh, nf, ids, hs,
  vs, tq, hmax, vmax}, scan, Jpeg.decode.plane((ww * hh : U32)))), U32.to_nat((yy * ww + xx : U32)),
  Laws.jpg.colour(nf, rgb, Laws.jpg.up.value(us, 0, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy),
  Laws.jpg.up.value(us, 1, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy), Laws.jpg.up.value(us, 2,
  Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy))):
  match bb:
    case True{}:
      w13.pack(rgb, us, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan, xx, yy, eb1, hD, hfD, hK, h_xx, h_yy)
    case False{}:
      {==}

# one component: the gray pass; any other count: the colour pass or none
def w13.nf1(
  bb: Bool,
  +rgb: Bool,
  +us: List<&2, Laws.JUnit>,
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
  +eb1: {U32.is_eq(nf, 1) == bb : Bool},
  +hD: {Nat.is_lt(Jpeg.decode.depth((ww * hh : U32)), 32n) == True{} : Bool},
  +hfD: {Nat.is_le(Nat.mul(U32.to_nat(ww), U32.to_nat(hh)), Nat.pow(2n, Jpeg.decode.depth((ww * hh : U32)))) == True{} :
    Bool},
  +hK: {Nat.is_lt(U32.to_nat((yy * ww + xx : U32)), U32.to_nat((ww * hh : U32))) == True{} : Bool},
  +h_xx: {U32.is_lt(xx, ww) == True{} : Bool},
  +h_yy: {U32.is_lt(yy, hh) == True{} : Bool}
) -> w13.Q(Jpeg.decode.done.nf1(bb, nf, rgb, ww, hh, Jpeg.decode.ups(hs, vs, hmax, vmax, ww), Laws.jpg.paint.all(us, 0,
  Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq,
  hmax, vmax}, scan, Jpeg.decode.plane((ww * hh : U32))), Laws.jpg.paint.all(us, 1, Jpeg.Frame{ww, hh, nf, ids, hs, vs,
  tq, hmax, vmax}, scan, Jpeg.decode.plane((ww * hh : U32))), Laws.jpg.paint.all(us, 2, Jpeg.Frame{ww, hh, nf, ids, hs,
  vs, tq, hmax, vmax}, scan, Jpeg.decode.plane((ww * hh : U32)))), U32.to_nat((yy * ww + xx : U32)),
  Laws.jpg.colour(nf, rgb, Laws.jpg.up.value(us, 0, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy),
  Laws.jpg.up.value(us, 1, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy), Laws.jpg.up.value(us, 2,
  Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy))):
  match bb:
    case True{}:
      +py = Jpeg.decode.up.out(Jpeg.decode.up.mode(Jpeg.decode.at(hs, 0), Jpeg.decode.at(vs, 0), hmax, vmax, ww),
        U32.to_nat((ww * hh : U32)), ww, hh, Laws.jpg.paint.all(us, 0, Jpeg.Frame{ww, hh, nf, ids, hs,
        vs, tq, hmax, vmax}, scan, Jpeg.decode.plane((ww * hh : U32))))
      +v0 = Laws.jpg.up.value(us, 0, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy)
      +v1 = Laws.jpg.up.value(us, 1, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy)
      +v2 = Laws.jpg.up.value(us, 2, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy)
      +ec = {Equal.cong(Bool, Maybe<&2, U32>, zz => {Some{Bool.pick(U32, zz, Jpeg.gray(v0), Bool.pick(U32, rgb,
        Jpeg.direct(v0, v1, v2), Jpeg.rgb(v0, v1, v2)))} : Maybe<&2, U32>}, U32.is_eq(nf, 1), True{}, eb1) :
        {Some{Laws.jpg.colour(nf, rgb, v0, v1, v2)} == Some{Jpeg.gray(v0)} : Maybe<&2, U32>}}
      Equal.trans(Maybe<&2, U32>, List.get(&2, U32, Jpeg.decode.grays(py), U32.to_nat((yy * ww + xx : U32))),
        mgray(List.get(&2, U32, py, U32.to_nat((yy * ww + xx : U32)))),
        Some{Laws.jpg.colour(nf, rgb, v0, v1, v2)}, grays_at(py, U32.to_nat((yy * ww + xx : U32))),
          Equal.trans(Maybe<&2, U32>,
        mgray(List.get(&2, U32, py, U32.to_nat((yy * ww + xx : U32)))), Some{Jpeg.gray(v0)}, Some{Laws.jpg.colour(nf,
          rgb, v0, v1, v2)},
        Equal.cong(Maybe<&2, U32>, Maybe<&2, U32>, mm => mgray(mm), List.get(&2, U32, py, U32.to_nat((yy * ww + xx :
          U32))), Some{v0},
        w13.up(0, us, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan, xx, yy, hD, hfD, hK, h_xx, h_yy)),
        Equal.sym(Maybe<&2, U32>, Some{Laws.jpg.colour(nf, rgb, v0, v1, v2)}, Some{Jpeg.gray(v0)}, ec)))
    case False{}:
      w13.nf3(U32.is_eq(nf, 3), rgb, us, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan, xx, yy, eb1, hD, hfD, hK,
        h_xx, h_yy)

# the scan's ok flag: none, or the picture by the component count
def w13.dn(
  bb: Bool,
  +rgb: Bool,
  +us: List<&2, Laws.JUnit>,
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
  +hD: {Nat.is_lt(Jpeg.decode.depth((ww * hh : U32)), 32n) == True{} : Bool},
  +hfD: {Nat.is_le(Nat.mul(U32.to_nat(ww), U32.to_nat(hh)), Nat.pow(2n, Jpeg.decode.depth((ww * hh : U32)))) == True{} :
    Bool},
  +hK: {Nat.is_lt(U32.to_nat((yy * ww + xx : U32)), U32.to_nat((ww * hh : U32))) == True{} : Bool},
  +h_xx: {U32.is_lt(xx, ww) == True{} : Bool},
  +h_yy: {U32.is_lt(yy, hh) == True{} : Bool}
) -> w13.Q(Jpeg.decode.done.ok(bb, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, rgb, Laws.jpg.paint.all(us, 0,
  Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, Jpeg.decode.plane((ww * hh : U32))),
  Laws.jpg.paint.all(us, 1, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, Jpeg.decode.plane((ww * hh :
  U32))), Laws.jpg.paint.all(us, 2, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, Jpeg.decode.plane((ww *
  hh : U32)))), U32.to_nat((yy * ww + xx : U32)), Laws.jpg.colour(nf, rgb, Laws.jpg.up.value(us, 0, Jpeg.Frame{ww, hh,
    nf,
  ids, hs, vs, tq, hmax, vmax}, scan, xx, yy), Laws.jpg.up.value(us, 1, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax,
  vmax}, scan, xx, yy), Laws.jpg.up.value(us, 2, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy))):
  match bb:
    case True{}:
      {==}
    case False{}:
      w13.nf1(U32.is_eq(nf, 1), rgb, us, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan, xx, yy, {==}, hD, hfD, hK,
        h_xx, h_yy)

# the scan decode of nb blocks: none for no blocks, else jpeg_blocks_paint and then decode.done
def w13.st(
  nb: Nat,
  +ent: List<&2, U32>,
  +tabs: Jpeg.Tabs,
  +ri: U32,
  +rgb: Bool,
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
  +hD: {Nat.is_lt(Jpeg.decode.depth((ww * hh : U32)), 32n) == True{} : Bool},
  +hfD: {Nat.is_le(Nat.mul(U32.to_nat(ww), U32.to_nat(hh)), Nat.pow(2n, Jpeg.decode.depth((ww * hh : U32)))) == True{} :
    Bool},
  +hK: {Nat.is_lt(U32.to_nat((yy * ww + xx : U32)), U32.to_nat((ww * hh : U32))) == True{} : Bool},
  +h_xx: {U32.is_lt(xx, ww) == True{} : Bool},
  +h_yy: {U32.is_lt(yy, hh) == True{} : Bool}
) -> w13.Q(Jpeg.decode.start(nb, Jpeg.Bits{0, 1, 0, ent}, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan,
  tabs, ri, rgb, Jpeg.decode.plane((ww * hh : U32)), Jpeg.decode.plane((ww * hh : U32)), Jpeg.decode.plane((ww * hh :
  U32))), U32.to_nat((yy * ww + xx : U32)),
  Laws.jpg.colour(nf, rgb, Laws.jpg.up.value(Laws.jpg.decoded.n(nb, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax},
    scan, tabs, ent, ri), 0, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy),
    Laws.jpg.up.value(Laws.jpg.decoded.n(nb, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, tabs, ent, ri),
      1,
    Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy), Laws.jpg.up.value(Laws.jpg.decoded.n(nb,
    Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, tabs, ent, ri), 2, Jpeg.Frame{ww, hh, nf, ids, hs, vs,
    tq, hmax, vmax}, scan, xx, yy))):
  match nb:
    case 0n:
      {==}
    case 1n+(+pp):
      +fr = {Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax} : Jpeg.Frame}
      +b0 = Jpeg.decode.block.of(Jpeg.Bits{0, 1, 0, ent}, 0, Jpeg.decode.pred.zero(), fr, scan, tabs)
      +lv = Jpeg.decode.blk.live(b0)
      +c0 = {Jpeg.Ctrl{0, 0, 0, 0, 0, 0} : Jpeg.Ctrl}
      +us = Laws.jpg.units.run(pp, b0, c0, Jpeg.decode.pred.zero(), fr, scan, tabs, ri)
      +ok = Laws.jpg.run.ok(pp, lv, b0, c0, Jpeg.decode.pred.zero(), fr, scan, tabs, ri, 1)
      +sl = Equal.sym(Maybe<&2, Jpeg.Pic>, Jpeg.decode.blocks(pp, lv, b0, c0, Jpeg.decode.pred.zero(), fr, scan, tabs,
        ri, rgb, Jpeg.decode.plane((ww * hh : U32)), Jpeg.decode.plane((ww * hh : U32)), Jpeg.decode.plane((ww * hh :
        U32)), 1), Jpeg.decode.done(ok, fr, rgb, Laws.jpg.paint.all(us, 0, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq,
        hmax, vmax}, scan, Jpeg.decode.plane((ww * hh : U32))), Laws.jpg.paint.all(us, 1, Jpeg.Frame{ww, hh, nf, ids,
        hs, vs, tq, hmax, vmax}, scan, Jpeg.decode.plane((ww * hh : U32))), Laws.jpg.paint.all(us, 2, Jpeg.Frame{ww,
        hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, Jpeg.decode.plane((ww * hh : U32)))), Laws.jpeg_blocks_paint(pp,
        b0, c0, Jpeg.decode.pred.zero(), fr, scan, tabs, ri, rgb, Jpeg.decode.plane((ww * hh : U32)),
        Jpeg.decode.plane((ww * hh : U32)), Jpeg.decode.plane((ww * hh : U32)), 1))
      %sl : w13.Q(_, U32.to_nat((yy * ww + xx : U32)), Laws.jpg.colour(nf, rgb, Laws.jpg.up.value(us, 0, Jpeg.Frame{ww,
        hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy), Laws.jpg.up.value(us, 1, Jpeg.Frame{ww, hh, nf, ids, hs,
        vs, tq, hmax, vmax}, scan, xx, yy), Laws.jpg.up.value(us, 2, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax,
        vmax}, scan, xx, yy)))
      w13.dn(U32.is_eq(ok, 0), rgb, us, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan, xx, yy, hD, hfD, hK, h_xx, h_yy)

# a scan the decoder does not run is none; one it runs is the scan decode of its blocks
def w13.fit(
  fit: Bool,
  +ent: List<&2, U32>,
  +tabs: Jpeg.Tabs,
  +ri: U32,
  +rgb: Bool,
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
  +hD: {Nat.is_lt(Jpeg.decode.depth((ww * hh : U32)), 32n) == True{} : Bool},
  +hfD: {Nat.is_le(Nat.mul(U32.to_nat(ww), U32.to_nat(hh)), Nat.pow(2n, Jpeg.decode.depth((ww * hh : U32)))) == True{} :
    Bool},
  +hK: {Nat.is_lt(U32.to_nat((yy * ww + xx : U32)), U32.to_nat((ww * hh : U32))) == True{} : Bool},
  +h_xx: {U32.is_lt(xx, ww) == True{} : Bool},
  +h_yy: {U32.is_lt(yy, hh) == True{} : Bool}
) -> w13.Q(Jpeg.decode.run.fit(fit, Jpeg.decode.nblocks(ww, hh, hs, vs, hmax, vmax), ww, hh, Jpeg.Frame{ww, hh, nf,
  ids, hs, vs, tq, hmax, vmax}, scan, tabs, ent, ri, rgb), U32.to_nat((yy * ww + xx : U32)), Laws.jpg.colour(nf, rgb,
  Laws.jpg.up.value(Laws.jpg.decoded.n(U32.to_nat(Jpeg.decode.nblocks(ww, hh, hs, vs, hmax, vmax)), Jpeg.Frame{ww, hh,
    nf,
  ids, hs, vs, tq, hmax, vmax}, scan, tabs, ent, ri), 0, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx,
    yy), Laws.jpg.up.value(Laws.jpg.decoded.n(U32.to_nat(Jpeg.decode.nblocks(ww, hh, hs, vs, hmax, vmax)),
    Jpeg.Frame{ww,
  hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, tabs, ent, ri), 1, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax},
  scan, xx, yy), Laws.jpg.up.value(Laws.jpg.decoded.n(U32.to_nat(Jpeg.decode.nblocks(ww, hh, hs, vs, hmax, vmax)),
  Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, tabs, ent, ri), 2, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq,
  hmax, vmax}, scan, xx, yy))):
  match fit:
    case False{}:
      {==}
    case True{}:
      w13.st(U32.to_nat(Jpeg.decode.nblocks(ww, hh, hs, vs, hmax, vmax)), ent, tabs, ri, rgb, ww, hh, nf, ids, hs, vs,
        tq, hmax, vmax, scan, xx, yy, hD, hfD, hK, h_xx, h_yy)

# a finished walk: none unless a baseline frame was read and nothing refused, else the scan decode
def w13.fin(
  k1: Bool,
  b0: Bool,
  +ent: List<&2, U32>,
  +tabs: Jpeg.Tabs,
  +ri: U32,
  +rgb: Bool,
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
  +ew: {Bool.or(U32.is_eq(ww, 0), U32.is_eq(hh, 0)) == False{} : Bool},
  +hD: {Nat.is_lt(Jpeg.decode.depth((ww * hh : U32)), 32n) == True{} : Bool},
  +hfD: {Nat.is_le(Nat.mul(U32.to_nat(ww), U32.to_nat(hh)), Nat.pow(2n, Jpeg.decode.depth((ww * hh : U32)))) == True{} :
    Bool},
  +hK: {Nat.is_lt(U32.to_nat((yy * ww + xx : U32)), U32.to_nat((ww * hh : U32))) == True{} : Bool},
  +h_xx: {U32.is_lt(xx, ww) == True{} : Bool},
  +h_yy: {U32.is_lt(yy, hh) == True{} : Bool}
) -> w13.Q(Jpeg.decode.finish.ok(k1, b0, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, tabs, ent, ri,
  rgb), U32.to_nat((yy * ww + xx : U32)), Laws.jpg.colour(nf, rgb, Laws.jpg.up.value(Laws.jpg.decoded(ww, hh, nf, ids,
    hs,
  vs, tq, hmax, vmax, scan, tabs, List.reverse(&2, U32, ent), ri), 0, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax,
  vmax}, scan, xx, yy), Laws.jpg.up.value(Laws.jpg.decoded(ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan, tabs,
  List.reverse(&2, U32, ent), ri), 1, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy),
  Laws.jpg.up.value(Laws.jpg.decoded(ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan, tabs, List.reverse(&2, U32, ent),
    ri),
  2, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy))):
  match k1 b0:
    case True{} True{}:
      +en = List.reverse(&2, U32, ent)
      +se = Equal.sym(Bool, Bool.or(U32.is_eq(ww, 0), U32.is_eq(hh, 0)), False{}, ew)
      %se : w13.Q(Jpeg.decode.run.n(_, ww, hh, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, tabs, en, ri,
        rgb), U32.to_nat((yy * ww + xx : U32)), Laws.jpg.colour(nf, rgb, Laws.jpg.up.value(Laws.jpg.decoded(ww, hh, nf,
        ids, hs, vs, tq, hmax, vmax, scan, tabs, en, ri), 0, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan,
          xx, yy), Laws.jpg.up.value(Laws.jpg.decoded(ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan, tabs, en, ri), 1,
        Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy), Laws.jpg.up.value(Laws.jpg.decoded(ww, hh,
        nf, ids, hs, vs, tq, hmax, vmax, scan, tabs, en, ri), 2, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax},
        scan, xx, yy)))
      w13.fit(Jpeg.decode.fits(ww, hh, Jpeg.decode.nblocks(ww, hh, hs, vs, hmax, vmax), en, nf, ids, scan), en, tabs,
        ri,
        rgb, ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan, xx, yy, hD, hfD, hK, h_xx, h_yy)
    case True{} False{}:
      {==}
    case False{} _b0:
      {==}

def Laws.jpeg_place(
  bytes,
  ww,
  hh,
  nf,
  ids,
  hs,
  vs,
  tq,
  hmax,
  vmax,
  scan,
  tabs,
  ent,
  ri,
  kind,
  bad,
  h_walk,
  dd,
  h_dd,
  h_fit,
  xx,
  yy,
  h_xx,
  h_yy
):
  +nn = (ww * hh : U32)
  +kk = (yy * ww + xx : U32)
  +wn = U32.to_nat(ww)
  +hn = U32.to_nat(hh)
  +hd32 = lt32(dd, h_dd)
  +hx = lt_of(xx, ww, h_xx)
  +hy = lt_of(yy, hh, h_yy)
  +ea = {area_nat(ww, hh, dd, hd32, h_fit) : {U32.to_nat(nn) == Nat.mul(wn, hn) : Nat}}
  +ei = {idx_nat(ww, hh, xx, yy, dd, hd32, h_fit, h_xx, h_yy) : {U32.to_nat(kk) ==
    Nat.add(Nat.mul(U32.to_nat(yy), wn), U32.to_nat(xx)) : Nat}}
  +hK = {M1.lt_rw_r(U32.to_nat(kk), Nat.mul(wn, hn), U32.to_nat(nn), Equal.sym(Nat, U32.to_nat(nn), Nat.mul(wn, hn),
      ea),
    M1.lt_rw_l(Nat.add(Nat.mul(U32.to_nat(yy), wn), U32.to_nat(xx)), U32.to_nat(kk), Nat.mul(wn, hn), Equal.sym(Nat,
    U32.to_nat(kk), Nat.add(Nat.mul(U32.to_nat(yy), wn), U32.to_nat(xx)), ei), M3.index_lt(U32.to_nat(xx),
    U32.to_nat(yy),
    wn, hn, hx, hy))) : {Nat.is_lt(U32.to_nat(kk), U32.to_nat(nn)) == True{} : Bool}}
  +hpos = {M3.lt_pos(U32.to_nat(kk), U32.to_nat(nn), hK) : {Nat.is_lt(0n, U32.to_nat(nn)) == True{} : Bool}}
  +hnn = {M1.le_rw_l(Nat.mul(wn, hn), U32.to_nat(nn), Nat.pow(2n, dd), Equal.sym(Nat, U32.to_nat(nn), Nat.mul(wn, hn),
    ea), h_fit) : {Nat.is_le(U32.to_nat(nn), Nat.pow(2n, dd)) == True{} : Bool}}
  +dp = Laws.jpeg_plane_depth(nn, dd, hpos, h_dd, hnn)
  +dn = Jpeg.decode.depth(nn)
  +hD = {M1.and_left(Nat.is_lt(dn, 32n), Nat.is_le(U32.to_nat(nn), Nat.pow(2n, dn)), dp) : {Nat.is_lt(dn, 32n) ==
    True{} : Bool}}
  +hfD = {M1.le_rw_l(U32.to_nat(nn), Nat.mul(wn, hn), Nat.pow(2n, dn), ea, M1.and_right(Nat.is_lt(dn, 32n),
    Nat.is_le(U32.to_nat(nn), Nat.pow(2n, dn)), dp)) : {Nat.is_le(Nat.mul(wn, hn), Nat.pow(2n, dn)) == True{} : Bool}}
  +e0w = {Equal.trans(Bool, U32.is_eq(ww, 0), Nat.is_eq(wn, 0n), False{}, M1.u32_eq(ww, 0), gt_neq(wn, 0n,
    M3.lt_pos(U32.to_nat(xx), wn, hx))) : {U32.is_eq(ww, 0) == False{} : Bool}}
  +e0h = {Equal.trans(Bool, U32.is_eq(hh, 0), Nat.is_eq(hn, 0n), False{}, M1.u32_eq(hh, 0), gt_neq(hn, 0n,
    M3.lt_pos(U32.to_nat(yy), hn, hy))) : {U32.is_eq(hh, 0) == False{} : Bool}}
  +ew = {Equal.trans(Bool, Bool.or(U32.is_eq(ww, 0), U32.is_eq(hh, 0)), Bool.or(False{}, U32.is_eq(hh, 0)), False{},
    Equal.cong(Bool, Bool, bb => Bool.or(bb, U32.is_eq(hh, 0)), U32.is_eq(ww, 0), False{}, e0w), e0h) :
    {Bool.or(U32.is_eq(ww, 0), U32.is_eq(hh, 0)) == False{} : Bool}}
  +sh = Equal.sym(Jpeg.St, Jpeg.decode.walk(bytes, Jpeg.decode.st0()), Jpeg.St{Jpeg.Stop{}, Jpeg.Frame{ww, hh, nf, ids,
    hs, vs, tq, hmax, vmax}, scan, tabs, ent, ri,
    kind, bad}, h_walk)
  %sh : w13.Q(Jpeg.decode.finish(_, Jpeg.decode.facts(bytes)), U32.to_nat((yy * ww + xx : U32)), Laws.jpg.colour(nf,
    Jpeg.decode.rgb.of(Jpeg.decode.facts(bytes), Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}),
    Laws.jpg.up.value(Laws.jpg.decoded(ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan, tabs, List.reverse(&2, U32, ent),
    ri), 0, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy), Laws.jpg.up.value(Laws.jpg.decoded(ww,
    hh, nf, ids, hs, vs, tq, hmax, vmax, scan, tabs, List.reverse(&2, U32, ent), ri), 1, Jpeg.Frame{ww, hh, nf, ids, hs,
    vs, tq, hmax, vmax}, scan, xx, yy), Laws.jpg.up.value(Laws.jpg.decoded(ww, hh, nf, ids, hs, vs, tq, hmax, vmax,
    scan, tabs, List.reverse(&2, U32, ent), ri), 2, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, scan, xx, yy)))
  w13.fin(Bool.and(U32.is_eq(kind, 1), Jpeg.decode.facts.soi(Jpeg.decode.facts(bytes))), U32.is_eq(bad, 0), ent, tabs,
    ri, Jpeg.decode.rgb.of(Jpeg.decode.facts(bytes), Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}), ww, hh, nf,
    ids, hs, vs, tq, hmax, vmax, scan, xx, yy, ew, hD, hfD, hK, h_xx, h_yy)
