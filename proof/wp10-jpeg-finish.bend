# proof/wp10-jpeg-finish: lemmas for IMG-JPG-2's last parts (block painting, component placement, the
# SOF0 refusals, the MCU walk over the frame, reading the planes out) and IMG-JPG-3's intermediate laws
# (the encoder's header walked by the decoder, the entropy-coded data unstuffed). PROOF.bend imports this
# file as W10, so the gate checks it.
import Base
import ../LAWS.bend as Laws
import ../src/jpeg.bend as Jpeg
import ../src/jpeg_enc.bend as Jenc
import ./u32.bend as U32L
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
  h_disp: {Jpeg.decode.dispatch(192, body, frame, scan, tabs, ent, ri, kind, bad) == stop(scan, tabs, ent, ri, kind)
    : Jpeg.St}
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
