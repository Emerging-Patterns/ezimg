# proofs of laws/JpegReadsScansInTurn.bend
import Base
import ../main.bend as Img
import ../src/jpeg.bend as Jpeg
import ../laws/JpegReadsScansInTurn.bend as Laws
import ../laws/JpegRefusesNonBaselineFrames.bend as LR
import ../laws/JpegRoundTripKeepsSize.bend as LT
import ./JpegRoundTripKeepsSize.bend as PT
import ./lemmas/BasicFacts.bend as M1
import ./lemmas/JpegHuffmanCoding.bend as M2

# ---- jpeg_scan_ends_at_segment ----

# the entropy walk from after one byte, as sw.go gives it
def sw.Ih(
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
  {Jpeg.decode.walk(rest, Jpeg.St{PT.ent.ph(ff), frame, scan, tabs, PT.ent.hold(ff, bb, en), ri, kind, bad}) ==
    Jpeg.St{Jpeg.Ent{}, frame, scan, tabs, List.reverse.go(&2, U32, rest, PT.ent.acc(ff, PT.ent.hold(ff, bb, en))),
    ri, kind, bad} : Jpeg.St}

# the entropy walk over one byte that is not after a 255: 255 opens a pair, any other is kept
def sw.one(
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
  ih: sw.Ih(ff, bb, rest, frame, scan, tabs, en, ri, kind, bad)
) -> {Jpeg.decode.walk(bb <> rest, Jpeg.St{Jpeg.Ent{}, frame, scan, tabs, en, ri, kind, bad}) == Jpeg.St{Jpeg.Ent{},
  frame, scan, tabs, List.reverse.go(&2, U32, bb <> rest, en), ri, kind, bad} : Jpeg.St}:
  match ff:
    case True{}:
      es = Equal.sym(Bool, U32.is_eq(bb, 255), True{}, ee)
      eb = Equal.sym(U32, bb, 255, M1.ueq(bb, 255, ee))
      %es : {Jpeg.decode.walk(rest, Jpeg.decode.step.ent(_, bb, frame, scan, tabs, en, ri, kind, bad)) ==
        Jpeg.St{Jpeg.Ent{}, frame, scan, tabs, List.reverse.go(&2, U32, rest, bb <> en), ri, kind, bad} : Jpeg.St}
      %eb : {Jpeg.decode.walk(rest, Jpeg.decode.step.ent(True{}, bb, frame, scan, tabs, en, ri, kind, bad)) ==
        Jpeg.St{Jpeg.Ent{}, frame, scan, tabs, List.reverse.go(&2, U32, rest, _ <> en), ri, kind, bad} : Jpeg.St}
      ih
    case False{}:
      es = Equal.sym(Bool, U32.is_eq(bb, 255), False{}, ee)
      %es : {Jpeg.decode.walk(rest, Jpeg.decode.step.ent(_, bb, frame, scan, tabs, en, ri, kind, bad)) ==
        Jpeg.St{Jpeg.Ent{}, frame, scan, tabs, List.reverse.go(&2, U32, rest, bb <> en), ri, kind, bad} : Jpeg.St}
      ih

# the entropy walk over stuffed bytes stays in the scan, keeping every byte in reverse onto what it held, and a 255
# it had just read put back in front of them
def sw.go(
  +xs: List<&2, U32>,
  ff: Bool,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +en: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32,
  +hh: {LT.jpg.stuffed(xs, ff, True{}) == True{} : Bool}
) -> {Jpeg.decode.walk(xs, Jpeg.St{PT.ent.ph(ff), frame, scan, tabs, en, ri, kind, bad}) == Jpeg.St{Jpeg.Ent{}, frame,
  scan, tabs, List.reverse.go(&2, U32, xs, PT.ent.acc(ff, en)), ri, kind, bad} : Jpeg.St}:
  match xs:
    case Nil{}:
      match ff:
        case False{}:
          {==}
        case True{}:
          Empty.absurd({Jpeg.St{Jpeg.EntFF{}, frame, scan, tabs, en, ri, kind, bad} == Jpeg.St{Jpeg.Ent{}, frame, scan,
            tabs, 255 <> en, ri, kind, bad} : Jpeg.St}, M1.false_true(hh))
    case +bb <> +rest:
      match ff:
        case False{}:
          sw.one(U32.is_eq(bb, 255), bb, rest, frame, scan, tabs, en, ri, kind, bad, {==}, sw.go(rest,
            U32.is_eq(bb, 255), frame, scan, tabs, PT.ent.hold(U32.is_eq(bb, 255), bb, en), ri, kind, bad, hh))
        case True{}:
          +ez = {PT.ent.zero(U32.is_eq(bb, 0), rest, hh) : {U32.is_eq(bb, 0) == True{} : Bool}}
          eb = Equal.sym(U32, bb, 0, M1.ueq(bb, 0, ez))
          %eb : {Jpeg.decode.walk(_ <> rest, Jpeg.St{Jpeg.EntFF{}, frame, scan, tabs, en, ri, kind, bad}) ==
            Jpeg.St{Jpeg.Ent{}, frame, scan, tabs, List.reverse.go(&2, U32, _ <> rest, 255 <> en), ri, kind, bad} :
            Jpeg.St}
          h2 = Equal.trans(Bool, LT.jpg.stuffed(rest, False{}, True{}), LT.jpg.stuffed(rest, False{},
            U32.is_eq(bb, 0)), True{}, Equal.cong(Bool, Bool, zb => LT.jpg.stuffed(rest, False{}, zb), True{},
            U32.is_eq(bb, 0), Equal.sym(Bool, U32.is_eq(bb, 0), True{}, ez)), hh)
          sw.go(rest, False{}, frame, scan, tabs, 0 <> (255 <> en), ri, kind, bad, h2)

# a walk that ended a scan at a marker keeps every byte after it, in reverse onto what it held
def rw.go(
  xs: List<&2, U32>,
  +mark: U32,
  +acc: List<&2, U32>,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +en: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> {Jpeg.decode.walk(xs, Jpeg.St{Jpeg.Rest{mark, acc}, frame, scan, tabs, en, ri, kind, bad}) ==
  Jpeg.St{Jpeg.Rest{mark, List.reverse.go(&2, U32, xs, acc)}, frame, scan, tabs, en, ri, kind, bad} : Jpeg.St}:
  match xs:
    case Nil{}:
      {==}
    case bb <> tl:
      rw.go(tl, mark, bb <> acc, frame, scan, tabs, en, ri, kind, bad)

# after a frame header, a 255 and a segment marker inside a scan end it at that marker
def mk.rest(
  mk: LR.Mk,
  +rest: List<&2, U32>,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +en: List<&2, U32>,
  +ri: U32,
  +bad: U32
) -> {Jpeg.decode.walk(255 <> (LR.mk.byte(mk) <> rest), Jpeg.St{Jpeg.Ent{}, frame, scan, tabs, en, ri, 1, bad}) ==
  Jpeg.St{Jpeg.Rest{LR.mk.byte(mk), List.reverse.go(&2, U32, rest, [])}, frame, scan, tabs, en, ri, 1, bad} :
  Jpeg.St}:
  match mk:
    case LR.MDht{}:
      rw.go(rest, 196, [], frame, scan, tabs, en, ri, 1, bad)
    case LR.MDqt{}:
      rw.go(rest, 219, [], frame, scan, tabs, en, ri, 1, bad)
    case LR.MSos{}:
      rw.go(rest, 218, [], frame, scan, tabs, en, ri, 1, bad)
    case LR.MDri{}:
      rw.go(rest, 221, [], frame, scan, tabs, en, ri, 1, bad)
    case LR.MCom{}:
      rw.go(rest, 254, [], frame, scan, tabs, en, ri, 1, bad)
    case LR.MApp0{}:
      rw.go(rest, 224, [], frame, scan, tabs, en, ri, 1, bad)
    case LR.MApp1{}:
      rw.go(rest, 225, [], frame, scan, tabs, en, ri, 1, bad)
    case LR.MApp2{}:
      rw.go(rest, 226, [], frame, scan, tabs, en, ri, 1, bad)
    case LR.MApp3{}:
      rw.go(rest, 227, [], frame, scan, tabs, en, ri, 1, bad)
    case LR.MApp4{}:
      rw.go(rest, 228, [], frame, scan, tabs, en, ri, 1, bad)
    case LR.MApp5{}:
      rw.go(rest, 229, [], frame, scan, tabs, en, ri, 1, bad)
    case LR.MApp6{}:
      rw.go(rest, 230, [], frame, scan, tabs, en, ri, 1, bad)
    case LR.MApp7{}:
      rw.go(rest, 231, [], frame, scan, tabs, en, ri, 1, bad)
    case LR.MApp8{}:
      rw.go(rest, 232, [], frame, scan, tabs, en, ri, 1, bad)
    case LR.MApp9{}:
      rw.go(rest, 233, [], frame, scan, tabs, en, ri, 1, bad)
    case LR.MApp10{}:
      rw.go(rest, 234, [], frame, scan, tabs, en, ri, 1, bad)
    case LR.MApp11{}:
      rw.go(rest, 235, [], frame, scan, tabs, en, ri, 1, bad)
    case LR.MApp12{}:
      rw.go(rest, 236, [], frame, scan, tabs, en, ri, 1, bad)
    case LR.MApp13{}:
      rw.go(rest, 237, [], frame, scan, tabs, en, ri, 1, bad)
    case LR.MApp14{}:
      rw.go(rest, 238, [], frame, scan, tabs, en, ri, 1, bad)
    case LR.MApp15{}:
      rw.go(rest, 239, [], frame, scan, tabs, en, ri, 1, bad)

def Laws.jpeg_scan_ends_at_segment(xs, h_stuffed, mk, rest, frame, scan, tabs, ent, ri, bad):
  +tail = {255 <> (LR.mk.byte(mk) <> rest) : List<&2, U32>}
  +st = {Jpeg.St{Jpeg.Ent{}, frame, scan, tabs, ent, ri, 1, bad} : Jpeg.St}
  +mid = {Jpeg.St{Jpeg.Ent{}, frame, scan, tabs, List.reverse.go(&2, U32, xs, ent), ri, 1, bad} : Jpeg.St}
  +fin = {Jpeg.St{Jpeg.Rest{LR.mk.byte(mk), List.reverse.go(&2, U32, rest, [])}, frame, scan, tabs,
    List.reverse.go(&2, U32, xs, ent), ri, 1, bad} : Jpeg.St}
  Equal.trans(Jpeg.St, Jpeg.decode.walk(List.append(&2, U32, xs, tail), st), Jpeg.decode.walk(tail,
    Jpeg.decode.walk(xs, st)), fin, M2.walk_app(xs, tail, st),
    Equal.trans(Jpeg.St, Jpeg.decode.walk(tail, Jpeg.decode.walk(xs, st)), Jpeg.decode.walk(tail, mid), fin,
      Equal.cong(Jpeg.St, Jpeg.St, ss => Jpeg.decode.walk(tail, ss), Jpeg.decode.walk(xs, st), mid,
        sw.go(xs, False{}, frame, scan, tabs, ent, ri, 1, bad, h_stuffed)),
      mk.rest(mk, rest, frame, scan, tabs, List.reverse.go(&2, U32, xs, ent), ri, bad)))

# ---- jpeg_scans_in_turn ----

def Laws.jpeg_scans_in_turn(
  bytes,
  h_soi,
  mark,
  acc,
  frame,
  scan,
  tabs,
  ent,
  ri,
  h_walk,
  ns,
  sids,
  td,
  ta,
  ss,
  se,
  ah,
  h_ns,
  tabs2,
  ent2,
  ri2,
  h_next
):
  +facts = Jpeg.decode.facts(bytes)
  +rgb = Jpeg.decode.rgb.of(facts, frame)
  +s1 = {Jpeg.St{Jpeg.Rest{mark, acc}, frame, scan, tabs, ent, ri, 1, 0} : Jpeg.St}
  +sc2 = {Jpeg.Scan{ns, sids, td, ta, ss, se, ah} : Jpeg.Scan}
  +s2 = {Jpeg.St{Jpeg.Stop{}, frame, sc2, tabs2, ent2, ri2, 1, 0} : Jpeg.St}
  +nx = Jpeg.decode.walk(List.reverse(&2, U32, acc), Jpeg.decode.mark(mark, frame, Jpeg.decode.scan0(), tabs, [], ri,
    1, 0))
  +p1 = {Jpeg.Pass{scan, tabs, List.reverse(&2, U32, ent), ri} : Jpeg.Pass}
  +p2 = {Jpeg.Pass{sc2, tabs2, List.reverse(&2, U32, ent2), ri2} : Jpeg.Pass}
  +left = {1n+List.length(&2, U32, acc) : Nat}
  +want = Img.decode_jpeg.out(Jpeg.decode.passes(frame, [p1, p2], rgb))
  Equal.trans(Maybe<&2, Img.Raster>, Img.decode_jpeg(bytes), Img.decode_jpeg.out(Jpeg.decode.finish(s1, facts)), want,
    Equal.cong(Jpeg.St, Maybe<&2, Img.Raster>, ww => Img.decode_jpeg.out(Jpeg.decode.finish(ww, facts)),
      Jpeg.decode.walk(bytes, Jpeg.decode.st0()), s1, h_walk),
    Equal.trans(Maybe<&2, Img.Raster>, Img.decode_jpeg.out(Jpeg.decode.finish(s1, facts)),
      Img.decode_jpeg.out(Jpeg.decode.multi(Jpeg.decode.chain(left, Jpeg.decode.st.good(s2), s2, [p1]), frame,
      facts)), want,
      Equal.cong(Jpeg.St, Maybe<&2, Img.Raster>, ww => Img.decode_jpeg.out(Jpeg.decode.multi(Jpeg.decode.chain(left,
        Jpeg.decode.st.good(ww), ww, [p1]), frame, facts)), nx, s2, h_next),
      Equal.trans(Maybe<&2, Img.Raster>, Img.decode_jpeg.out(Jpeg.decode.multi(Jpeg.decode.chain(left,
        Jpeg.decode.st.good(s2), s2, [p1]), frame, facts)), Img.decode_jpeg.out(Jpeg.decode.multi.go(
        Jpeg.decode.facts.soi(facts), [p2, p1], frame, rgb)), want,
        Equal.cong(Bool, Maybe<&2, Img.Raster>, bb => Img.decode_jpeg.out(Jpeg.decode.multi.go(
          Jpeg.decode.facts.soi(facts), Jpeg.decode.chain.last(bb, sc2, tabs2, ent2, ri2, [p1]), frame, rgb)),
          U32.is_eq(ns, 0), False{}, h_ns),
        Equal.cong(Bool, Maybe<&2, Img.Raster>, bb => Img.decode_jpeg.out(Jpeg.decode.multi.go(bb, [p2, p1], frame,
          rgb)), Jpeg.decode.facts.soi(facts), True{}, h_soi))))

# ---- jpeg_passes_sized ----

# the passes end in decode.done, a picture of the frame's size or none
def pdone.sized(
  got: U32 & Array<U32> & Array<U32> & Array<U32>,
  +ww: U32,
  +hh: U32,
  +nf: U32,
  +ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>,
  +tq: List<&2, U32>,
  +hmax: U32,
  +vmax: U32,
  rgb: Bool
) -> {LT.jpg.sized(Img.decode_jpeg.out(Jpeg.decode.passes.done(got, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax,
  vmax}, rgb)), ww, hh) == True{} : Bool}:
  (ok, yy, cb, cr) = got
  PT.dok.sized(U32.is_eq(ok, 0), ww, hh, nf, ids, hs, vs, tq, hmax, vmax, rgb, yy, cb, cr)

# scans the passes refuse have no picture; others end in decode.done
def pfit.sized(
  fit: Bool,
  +ww: U32,
  +hh: U32,
  +nf: U32,
  +ids: List<&2, U32>,
  +hs: List<&2, U32>,
  +vs: List<&2, U32>,
  +tq: List<&2, U32>,
  +hmax: U32,
  +vmax: U32,
  passes: List<&2, Jpeg.Pass>,
  rgb: Bool
) -> {LT.jpg.sized(Img.decode_jpeg.out(Jpeg.decode.passes.fit(fit, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax,
  vmax}, passes, ww, hh, rgb)), ww, hh) == True{} : Bool}:
  match fit:
    case False{}:
      {==}
    case True{}:
      +fr = {Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax} : Jpeg.Frame}
      pdone.sized(Jpeg.decode.passes.go(passes, fr, (1, Jpeg.decode.plane((ww * hh : U32)),
        Jpeg.decode.plane((ww * hh : U32)), Jpeg.decode.plane((ww * hh : U32)))), ww, hh, nf, ids, hs, vs, tq, hmax,
        vmax, rgb)

def Laws.jpeg_passes_sized(ww, hh, nf, ids, hs, vs, tq, hmax, vmax, passes, rgb):
  +fr = {Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax} : Jpeg.Frame}
  pfit.sized(Bool.and(Bool.not(Bool.or(U32.is_eq(ww, 0), U32.is_eq(hh, 0))), Bool.and(Jpeg.decode.area.ok(ww, hh),
    Jpeg.decode.passes.ok(passes, fr, 0, True{}))), ww, hh, nf, ids, hs, vs, tq, hmax, vmax, passes, rgb)
