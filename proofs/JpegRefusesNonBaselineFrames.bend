# proofs of laws/JpegRefusesNonBaselineFrames.bend
import Base
import ../main.bend as Img
import ../src/jpeg.bend as Jpeg
import ../laws/JpegRefusesNonBaselineFrames.bend as Laws
import ./lemmas/BasicFacts.bend as M1
import ./lemmas/JpegHuffmanCoding.bend as M2

# a stopped walk stays stopped, and keeps everything it holds
def stop.walk(
  xs: List<&2, U32>,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> {Jpeg.decode.walk(xs, Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad})
  == Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad} : Jpeg.St}:
  match xs:
    case Nil{}:
      {==}
    case _bb <> rest:
      stop.walk(rest, frame, scan, tabs, ent, ri, kind, bad)

# walking two lists is walking the first, then the second
def walk.app(
  xs: List<&2, U32>,
  +ys: List<&2, U32>,
  st: Jpeg.St
) -> {Jpeg.decode.walk(List.append(&2, U32, xs, ys), st) == Jpeg.decode.walk(ys, Jpeg.decode.walk(xs, st)) : Jpeg.St}:
  match xs:
    case Nil{}:
      {==}
    case +bb <> rest:
      walk.app(rest, ys, Jpeg.decode.step(bb, st))

# a DHT body leaves kind as it found it, and the walk seeking or stopped
def dht.inv(
  xs: List<&2, U32>,
  ok: Bool,
  sym: Bool,
  phase: Nat,
  +cls: U32,
  +id: U32,
  +counts: List<&2, U32>,
  +syms: List<&2, U32>,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> {M1.inv(Jpeg.decode.read.dht(xs, ok, sym, phase, cls, id, counts, syms, frame, scan, tabs, ent, ri, kind, bad))
  == U32.is_eq(kind, 0) : Bool}:
  match xs:
    case Nil{}:
      match ok:
        case False{}:
          {==}
        case True{}:
          match sym:
            case False{}:
              match phase:
                case 0n:
                  {==}
                case 1n+_pp:
                  {==}
            case True{}:
              match phase:
                case 0n:
                  {==}
                case 1n+_pp:
                  {==}
    case +bb <> rest:
      match ok:
        case False{}:
          {==}
        case True{}:
          match sym:
            case False{}:
              match phase:
                case 0n:
                  dht.inv(rest, Bool.and(U32.is_le(U32.shrn(bb, 4n), 1), U32.is_le(U32.and(bb, 15), 3)), False{}, 16n,
                    U32.shrn(bb, 4n), U32.and(bb, 15), [], [], frame, scan, tabs, ent, ri, kind, bad)
                case 1n+pp:
                  match pp:
                    case 0n:
                      +cs = List.reverse(&2, U32, bb <> counts)
                      dht.inv(rest, Jpeg.decode.huff.counts.ok(cs), True{}, U32.to_nat(Jpeg.decode.sum.counts(cs, 0)),
                        cls, id, cs, [], frame, scan, tabs, ent, ri, kind, bad)
                    case 1n+qq:
                      dht.inv(rest, True{}, False{}, 1n+qq, cls, id, bb <> counts, [], frame, scan, tabs, ent, ri, kind,
                        bad)
            case True{}:
              match phase:
                case 0n:
                  dht.inv(rest, Bool.and(U32.is_le(U32.shrn(bb, 4n), 1), U32.is_le(U32.and(bb, 15), 3)), False{}, 16n,
                    U32.shrn(bb, 4n), U32.and(bb, 15), [], [], frame, scan, Jpeg.decode.huff.put(tabs, cls, id,
                    Jpeg.decode.canon(272n, 0n, counts, [], 0, 0, [], [], [])), ent, ri, kind, bad)
                case 1n+pp:
                  match pp:
                    case 0n:
                      dht.inv(rest, Jpeg.decode.huff.sym.ok(cls, bb), False{}, 0n, 0, 0, [], [], frame, scan,
                        Jpeg.decode.huff.put(tabs, cls, id, Jpeg.decode.canon(272n, 0n, counts, List.reverse(&2, U32,
                        bb <> syms), 0, 0, [], [], [])), ent, ri, kind, bad)
                    case 1n+qq:
                      dht.inv(rest, Jpeg.decode.huff.sym.ok(cls, bb), True{}, 1n+qq, cls, id, counts, bb <> syms, frame,
                        scan, tabs, ent, ri, kind, bad)

# a DQT body leaves kind as it found it, and the walk seeking or stopped
def dqt.inv(
  xs: List<&2, U32>,
  ok: Bool,
  phase: Nat,
  +id: U32,
  +wide: Bool,
  +acc: List<&2, U32>,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> {M1.inv(Jpeg.decode.read.dqt(xs, ok, phase, id, wide, acc, frame, scan, tabs, ent, ri, kind, bad))
  == U32.is_eq(kind, 0) : Bool}:
  match xs:
    case Nil{}:
      match ok:
        case False{}:
          {==}
        case True{}:
          match phase:
            case 0n:
              {==}
            case 1n+_pp:
              {==}
    case +bb <> rest:
      match ok:
        case False{}:
          {==}
        case True{}:
          match phase:
            case 0n:
              +pq = U32.shrn(bb, 4n)
              dqt.inv(rest, Bool.and(U32.is_le(pq, 1), U32.is_le(U32.and(bb, 15), 3)), Bool.pick(Nat, U32.is_eq(pq, 1),
                128n, 64n), U32.and(bb, 15), U32.is_eq(pq, 1), [], frame, scan, tabs, ent, ri, kind, bad)
            case 1n+pp:
              match pp:
                case 0n:
                  dqt.inv(rest, True{}, 0n, 0, False{}, [], frame, scan, Jpeg.decode.q.put(tabs, id,
                    Jpeg.decode.q.vals(wide, List.reverse(&2, U32, bb <> acc))), ent, ri, kind, bad)
                case 1n+qq:
                  dqt.inv(rest, True{}, 1n+qq, id, wide, bb <> acc, frame, scan, tabs, ent, ri, kind, bad)

# the end of an SOS header leaves kind as it found it, and the walk in the scan or stopped
def sos.ok.inv(
  ss0: Bool,
  se63: Bool,
  ah0: Bool,
  +sids: List<&2, U32>,
  +td: List<&2, U32>,
  +ta: List<&2, U32>,
  +ns: U32,
  +frame: Jpeg.Frame,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> {M1.inv(Jpeg.decode.read.sos.ok(ss0, se63, ah0, sids, td, ta, ns, frame, tabs, ent, ri, kind, bad))
  == U32.is_eq(kind, 0) : Bool}:
  match ss0 se63 ah0:
    case False{} _se _ah:
      {==}
    case True{} False{} _ah:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} True{} True{}:
      {==}

# the components of an SOS header leave kind as they found it, and the walk in the scan or stopped
def sos.cs.inv(
  left: Nat,
  xs: List<&2, U32>,
  +tok: Bool,
  +sids: List<&2, U32>,
  +td: List<&2, U32>,
  +ta: List<&2, U32>,
  +ns: U32,
  +frame: Jpeg.Frame,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> {M1.inv(Jpeg.decode.read.sos.cs(left, xs, tok, sids, td, ta, ns, frame, tabs, ent, ri, kind, bad))
  == U32.is_eq(kind, 0) : Bool}:
  match left:
    case 0n:
      match xs:
        case Nil{}:
          {==}
        case _ss <> Nil{}:
          {==}
        case _ss <> _se <> Nil{}:
          {==}
        case +ss <> +se <> +ah <> _rest:
          sos.ok.inv(Bool.and(tok, U32.is_eq(ss, 0)), U32.is_eq(se, 63), U32.is_eq(ah, 0), sids, td, ta, ns, frame,
            tabs, ent, ri, kind, bad)
    case 1n+pp:
      match xs:
        case Nil{}:
          {==}
        case _id <> Nil{}:
          {==}
        case +id <> +tdta <> rest:
          sos.cs.inv(pp, rest, Bool.and(tok, Bool.and(U32.is_le(U32.shrn(tdta, 4n), 3), U32.is_le(U32.and(tdta, 15),
            3))), id <> sids, U32.shrn(tdta, 4n) <> td, U32.and(tdta, 15) <> ta, ns, frame, tabs, ent, ri, kind, bad)

# an SOS body leaves kind as it found it, and the walk in the scan or stopped
def sos.inv(
  xs: List<&2, U32>,
  +frame: Jpeg.Frame,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> {M1.inv(Jpeg.decode.read.sos(xs, frame, tabs, ent, ri, kind, bad)) == U32.is_eq(kind, 0) : Bool}:
  match xs:
    case +ns <> rest:
      sos.cs.inv(U32.to_nat(ns), rest, True{}, [], [], [], ns, frame, tabs, ent, ri, kind, bad)
    case Nil{}:
      {==}

# a DRI body leaves kind as it found it, and the walk seeking or stopped
def dri.inv(
  xs: List<&2, U32>,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +kind: U32,
  +bad: U32
) -> {M1.inv(Jpeg.decode.read.dri(xs, frame, scan, tabs, ent, kind, bad)) == U32.is_eq(kind, 0) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case _hi <> Nil{}:
      {==}
    case _hi <> _lo <> _rest:
      {==}

# a stopped walk that read no frame header decodes to none, whatever the file's facts
def fin.none(
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32,
  +facts: U32,
  hk: {U32.is_eq(kind, 0) == True{} : Bool}
) -> {Jpeg.decode.finish(Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad}, facts) == None{} :
  Maybe<&2, Jpeg.Pic>}:
  Equal.cong(U32, Maybe<&2, Jpeg.Pic>, kk => Jpeg.decode.finish(Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kk,
    bad}, facts), kind, 0, M1.ueq(kind, 0, hk))

# a walk that stopped on an error decodes to none
def fin.bad.go(
  ok1: Bool,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +rgb: Bool
) -> {Jpeg.decode.finish.ok(ok1, False{}, frame, scan, tabs, ent, ri, rgb) == None{} : Maybe<&2, Jpeg.Pic>}:
  match ok1:
    case True{}:
      {==}
    case False{}:
      {==}

# a walk that stopped on an error decodes to none, whatever kind it read and the file's facts
def fin.bad(
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +facts: U32
) -> {Jpeg.decode.finish(Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, 1}, facts) == None{} :
  Maybe<&2, Jpeg.Pic>}:
  fin.bad.go(Bool.and(U32.is_eq(kind, 1), Jpeg.decode.facts.soi(facts)), frame, scan, tabs, ent, ri,
    Jpeg.decode.rgb.of(facts, frame))

# the state st decodes to none
def fin.Nil(st: Jpeg.St, facts: U32) -> Type:
  {Jpeg.decode.finish(st, facts) == None{} : Maybe<&2, Jpeg.Pic>}

# a walk that reaches a stopped state that decodes to none decodes to none, whatever follows
def fin.after(
  rest: List<&2, U32>,
  +st: Jpeg.St,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32,
  +facts: U32,
  e_st: {st == Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad} : Jpeg.St},
  e_none: fin.Nil(Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad}, facts)
) -> {Jpeg.decode.finish(Jpeg.decode.walk(rest, st), facts) == None{} : Maybe<&2, Jpeg.Pic>}:
  +stop = {Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad} : Jpeg.St}
  Equal.trans(Maybe<&2, Jpeg.Pic>, Jpeg.decode.finish(Jpeg.decode.walk(rest, st), facts),
    Jpeg.decode.finish(Jpeg.decode.walk(rest, stop), facts), None{},
    Equal.cong(Jpeg.St, Maybe<&2, Jpeg.Pic>, ss => Jpeg.decode.finish(Jpeg.decode.walk(rest, ss), facts), st, stop,
      e_st),
    Equal.trans(Maybe<&2, Jpeg.Pic>, Jpeg.decode.finish(Jpeg.decode.walk(rest, stop), facts),
      Jpeg.decode.finish(stop, facts), None{},
      Equal.cong(Jpeg.St, Maybe<&2, Jpeg.Pic>, ss => Jpeg.decode.finish(ss, facts), Jpeg.decode.walk(rest, stop), stop,
        stop.walk(rest, frame, scan, tabs, ent, ri, kind, bad)), e_none))

# a phase between segments is itself; any other phase is taken as stopped
def ph.norm(ph: Jpeg.Phase) -> Jpeg.Phase:
  match ph:
    case Jpeg.Seek{}:
      Jpeg.Seek{}
    case Jpeg.Ent{}:
      Jpeg.Ent{}
    case Jpeg.Stop{}:
      Jpeg.Stop{}
    case Jpeg.Mark{}:
      Jpeg.Stop{}
    case Jpeg.LenHi{_mark}:
      Jpeg.Stop{}
    case Jpeg.LenLo{_mark, _hi}:
      Jpeg.Stop{}
    case Jpeg.Pay{_mark, _left, _acc}:
      Jpeg.Stop{}
    case Jpeg.EntFF{}:
      Jpeg.Stop{}

# a phase between segments is its own ph.norm
def ph.norm.eq(ph: Jpeg.Phase, h_ok: {M1.ph.ok(ph) == True{} : Bool}) -> {ph == ph.norm(ph) : Jpeg.Phase}:
  match ph:
    case Jpeg.Seek{}:
      {==}
    case Jpeg.Ent{}:
      {==}
    case Jpeg.Stop{}:
      {==}
    case Jpeg.Mark{}:
      Empty.absurd({Jpeg.Mark{} == Jpeg.Stop{} : Jpeg.Phase}, M1.false_true(h_ok))
    case Jpeg.LenHi{mark}:
      Empty.absurd({Jpeg.LenHi{mark} == Jpeg.Stop{} : Jpeg.Phase}, M1.false_true(h_ok))
    case Jpeg.LenLo{mark, hi}:
      Empty.absurd({Jpeg.LenLo{mark, hi} == Jpeg.Stop{} : Jpeg.Phase}, M1.false_true(h_ok))
    case Jpeg.Pay{mark, left, acc}:
      Empty.absurd({Jpeg.Pay{mark, left, acc} == Jpeg.Stop{} : Jpeg.Phase}, M1.false_true(h_ok))
    case Jpeg.EntFF{}:
      Empty.absurd({Jpeg.EntFF{} == Jpeg.Stop{} : Jpeg.Phase}, M1.false_true(h_ok))

# a segment marker starts its length field
def mk.mark(
  mk: Laws.Mk,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> {Jpeg.decode.mark(Laws.mk.byte(mk), frame, scan, tabs, ent, ri, kind, bad)
  == Jpeg.St{Jpeg.LenHi{Laws.mk.byte(mk)}, frame, scan, tabs, ent, ri, kind, bad} : Jpeg.St}:
  match mk:
    case Laws.MDht{}:
      {==}
    case Laws.MDqt{}:
      {==}
    case Laws.MSos{}:
      {==}
    case Laws.MDri{}:
      {==}
    case Laws.MCom{}:
      {==}
    case Laws.MApp0{}:
      {==}
    case Laws.MApp1{}:
      {==}
    case Laws.MApp2{}:
      {==}
    case Laws.MApp3{}:
      {==}
    case Laws.MApp4{}:
      {==}
    case Laws.MApp5{}:
      {==}
    case Laws.MApp6{}:
      {==}
    case Laws.MApp7{}:
      {==}
    case Laws.MApp8{}:
      {==}
    case Laws.MApp9{}:
      {==}
    case Laws.MApp10{}:
      {==}
    case Laws.MApp11{}:
      {==}
    case Laws.MApp12{}:
      {==}
    case Laws.MApp13{}:
      {==}
    case Laws.MApp14{}:
      {==}
    case Laws.MApp15{}:
      {==}

# a segment marker inside a scan stops the walk on an error
def mk.ent(
  mk: Laws.Mk,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> {Jpeg.decode.step.ph(Jpeg.EntFF{}, Laws.mk.byte(mk), frame, scan, tabs, ent, ri, kind, bad)
  == Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, 1} : Jpeg.St}:
  match mk:
    case Laws.MDht{}:
      {==}
    case Laws.MDqt{}:
      {==}
    case Laws.MSos{}:
      {==}
    case Laws.MDri{}:
      {==}
    case Laws.MCom{}:
      {==}
    case Laws.MApp0{}:
      {==}
    case Laws.MApp1{}:
      {==}
    case Laws.MApp2{}:
      {==}
    case Laws.MApp3{}:
      {==}
    case Laws.MApp4{}:
      {==}
    case Laws.MApp5{}:
      {==}
    case Laws.MApp6{}:
      {==}
    case Laws.MApp7{}:
      {==}
    case Laws.MApp8{}:
      {==}
    case Laws.MApp9{}:
      {==}
    case Laws.MApp10{}:
      {==}
    case Laws.MApp11{}:
      {==}
    case Laws.MApp12{}:
      {==}
    case Laws.MApp13{}:
      {==}
    case Laws.MApp14{}:
      {==}
    case Laws.MApp15{}:
      {==}

# a segment's reader leaves kind as it found it, and the walk seeking, in a scan, or stopped
def mk.disp(
  mk: Laws.Mk,
  body: List<&2, U32>,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> {M1.inv(Jpeg.decode.dispatch(Laws.mk.byte(mk), body, frame, scan, tabs, ent, ri, kind, bad))
  == U32.is_eq(kind, 0) : Bool}:
  match mk:
    case Laws.MDht{}:
      dht.inv(body, True{}, False{}, 0n, 0, 0, [], [], frame, scan, tabs, ent, ri, kind, bad)
    case Laws.MDqt{}:
      dqt.inv(body, True{}, 0n, 0, False{}, [], frame, scan, tabs, ent, ri, kind, bad)
    case Laws.MSos{}:
      sos.inv(body, frame, tabs, ent, ri, kind, bad)
    case Laws.MDri{}:
      dri.inv(body, frame, scan, tabs, ent, kind, bad)
    case Laws.MCom{}:
      {==}
    case Laws.MApp0{}:
      {==}
    case Laws.MApp1{}:
      {==}
    case Laws.MApp2{}:
      {==}
    case Laws.MApp3{}:
      {==}
    case Laws.MApp4{}:
      {==}
    case Laws.MApp5{}:
      {==}
    case Laws.MApp6{}:
      {==}
    case Laws.MApp7{}:
      {==}
    case Laws.MApp8{}:
      {==}
    case Laws.MApp9{}:
      {==}
    case Laws.MApp10{}:
      {==}
    case Laws.MApp11{}:
      {==}
    case Laws.MApp12{}:
      {==}
    case Laws.MApp13{}:
      {==}
    case Laws.MApp14{}:
      {==}
    case Laws.MApp15{}:
      {==}

# a frame header other than SOF0 stops the walk on an error
def sofn.mark(
  sn: Laws.Sofn,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> {Jpeg.decode.mark(Laws.sofn.byte(sn), frame, scan, tabs, ent, ri, kind, bad)
  == Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, 2, 1} : Jpeg.St}:
  match sn:
    case Laws.Sof2{}:
      {==}
    case Laws.Sof3{}:
      {==}
    case Laws.Sof5{}:
      {==}
    case Laws.Sof6{}:
      {==}
    case Laws.Sof7{}:
      {==}
    case Laws.Sof9{}:
      {==}
    case Laws.Sof10{}:
      {==}
    case Laws.Sof11{}:
      {==}
    case Laws.Sof13{}:
      {==}
    case Laws.Sof14{}:
      {==}
    case Laws.Sof15{}:
      {==}

# a frame header's marker inside a scan stops the walk on an error
def sofn.ent(
  sn: Laws.Sofn,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> {Jpeg.decode.step.ph(Jpeg.EntFF{}, Laws.sofn.byte(sn), frame, scan, tabs, ent, ri, kind, bad)
  == Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, 1} : Jpeg.St}:
  match sn:
    case Laws.Sof2{}:
      {==}
    case Laws.Sof3{}:
      {==}
    case Laws.Sof5{}:
      {==}
    case Laws.Sof6{}:
      {==}
    case Laws.Sof7{}:
      {==}
    case Laws.Sof9{}:
      {==}
    case Laws.Sof10{}:
      {==}
    case Laws.Sof11{}:
      {==}
    case Laws.Sof13{}:
      {==}
    case Laws.Sof14{}:
      {==}
    case Laws.Sof15{}:
      {==}

# what a segment's walk leaves: the kind it found and a phase between segments
def seg.Goal(
  ph: Jpeg.Phase,
  mk: Laws.Mk,
  hi: U32,
  lo: U32,
  body: List<&2, U32>,
  frame: Jpeg.Frame,
  scan: Jpeg.Scan,
  tabs: Jpeg.Tabs,
  ent: List<&2, U32>,
  ri: U32,
  kind: U32,
  bad: U32
) -> Type:
  {M1.inv(Jpeg.decode.walk(Laws.seg.bytes(Laws.Seg{mk, hi, lo, body}), Jpeg.St{ph, frame, scan, tabs, ent, ri, kind,
    bad})) == True{} : Bool}

# a segment walked from a state between segments that read no frame header ends in one
def seg.ph(
  ph: Jpeg.Phase,
  +mk: Laws.Mk,
  +hi: U32,
  +lo: U32,
  +body: List<&2, U32>,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32,
  h_fit: Laws.seg.Fits(hi, lo, body),
  h_inv: {M1.inv(Jpeg.St{ph, frame, scan, tabs, ent, ri, kind, bad}) == True{} : Bool}
) -> seg.Goal(ph, mk, hi, lo, body, frame, scan, tabs, ent, ri, kind, bad):
  match ph:
    case Jpeg.Seek{}:
      (e_lt, e_len) = h_fit
      +tail = {hi <> (lo <> body) : List<&2, U32>}
      +mm = Laws.mk.byte(mk)
      +lenhi = {Jpeg.St{Jpeg.LenHi{mm}, frame, scan, tabs, ent, ri, kind, bad} : Jpeg.St}
      +disp = Jpeg.decode.dispatch(mm, body, frame, scan, tabs, ent, ri, kind, bad)
      Equal.trans(Bool, M1.inv(Jpeg.decode.walk(tail, Jpeg.decode.mark(mm, frame, scan, tabs, ent, ri, kind, bad))),
        M1.inv(disp), True{},
        Equal.cong(Jpeg.St, Bool, ss => M1.inv(ss),
          Jpeg.decode.walk(tail, Jpeg.decode.mark(mm, frame, scan, tabs, ent, ri, kind, bad)), disp,
          Equal.trans(Jpeg.St, Jpeg.decode.walk(tail, Jpeg.decode.mark(mm, frame, scan, tabs, ent, ri, kind, bad)),
            Jpeg.decode.walk(tail, lenhi), disp,
            Equal.cong(Jpeg.St, Jpeg.St, ss => Jpeg.decode.walk(tail, ss),
              Jpeg.decode.mark(mm, frame, scan, tabs, ent, ri, kind, bad), lenhi,
              mk.mark(mk, frame, scan, tabs, ent, ri, kind, bad)),
            M2.seg.read(U32.is_lt(Laws.seg.len(hi, lo), 2), Laws.seg.len(hi, lo), body, mm, frame, scan, tabs, ent, ri,
              kind, bad, e_lt, e_len))),
        Equal.trans(Bool, M1.inv(disp), U32.is_eq(kind, 0), True{}, mk.disp(mk, body, frame, scan, tabs, ent, ri, kind,
          bad), h_inv))
    case Jpeg.Stop{}:
      +tail = {hi <> (lo <> body) : List<&2, U32>}
      +stop = {Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad} : Jpeg.St}
      Equal.trans(Bool, M1.inv(Jpeg.decode.walk(255 <> (Laws.mk.byte(mk) <> tail), stop)), U32.is_eq(kind, 0), True{},
        Equal.cong(Jpeg.St, Bool, ss => M1.inv(ss), Jpeg.decode.walk(255 <> (Laws.mk.byte(mk) <> tail), stop), stop,
          stop.walk(255 <> (Laws.mk.byte(mk) <> tail), frame, scan, tabs, ent, ri, kind, bad)), h_inv)
    case Jpeg.Ent{}:
      +tail = {hi <> (lo <> body) : List<&2, U32>}
      +mm = Laws.mk.byte(mk)
      +stop = {Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, 1} : Jpeg.St}
      +ff = {Jpeg.St{Jpeg.EntFF{}, frame, scan, tabs, ent, ri, kind, bad} : Jpeg.St}
      Equal.trans(Bool, M1.inv(Jpeg.decode.walk(tail, Jpeg.decode.step(mm, ff))), U32.is_eq(kind, 0), True{},
        Equal.cong(Jpeg.St, Bool, ss => M1.inv(ss), Jpeg.decode.walk(tail, Jpeg.decode.step(mm, ff)), stop,
          Equal.trans(Jpeg.St, Jpeg.decode.walk(tail, Jpeg.decode.step(mm, ff)), Jpeg.decode.walk(tail, stop), stop,
            Equal.cong(Jpeg.St, Jpeg.St, ss => Jpeg.decode.walk(tail, ss), Jpeg.decode.step(mm, ff), stop,
              mk.ent(mk, frame, scan, tabs, ent, ri, kind, bad)),
            stop.walk(tail, frame, scan, tabs, ent, ri, kind, 1))), h_inv)
    case Jpeg.Mark{}:
      Empty.absurd(seg.Goal(Jpeg.Mark{}, mk, hi, lo, body, frame, scan, tabs, ent, ri, kind, bad),
        M1.false_true(h_inv))
    case Jpeg.LenHi{mark}:
      Empty.absurd(seg.Goal(Jpeg.LenHi{mark}, mk, hi, lo, body, frame, scan, tabs, ent, ri, kind, bad),
        M1.false_true(h_inv))
    case Jpeg.LenLo{mark, mhi}:
      Empty.absurd(seg.Goal(Jpeg.LenLo{mark, mhi}, mk, hi, lo, body, frame, scan, tabs, ent, ri, kind, bad),
        M1.false_true(h_inv))
    case Jpeg.Pay{mark, left, acc}:
      Empty.absurd(seg.Goal(Jpeg.Pay{mark, left, acc}, mk, hi, lo, body, frame, scan, tabs, ent, ri, kind, bad),
        M1.false_true(h_inv))
    case Jpeg.EntFF{}:
      Empty.absurd(seg.Goal(Jpeg.EntFF{}, mk, hi, lo, body, frame, scan, tabs, ent, ri, kind, bad),
        M1.false_true(h_inv))

# a segment walked from a state between segments that read no frame header ends in one
def seg.inv(
  +mk: Laws.Mk,
  +hi: U32,
  +lo: U32,
  +body: List<&2, U32>,
  st: Jpeg.St,
  h_fit: Laws.seg.Fits(hi, lo, body),
  h_inv: {M1.inv(st) == True{} : Bool}
) -> {M1.inv(Jpeg.decode.walk(Laws.seg.bytes(Laws.Seg{mk, hi, lo, body}), st)) == True{} : Bool}:
  match st:
    case Jpeg.St{ph, +frame, +scan, +tabs, +ent, +ri, +kind, +bad}:
      seg.ph(ph, mk, hi, lo, body, frame, scan, tabs, ent, ri, kind, bad, h_fit, h_inv)

# segments walked from a state between segments that read no frame header end in one
def segs.inv(
  ss: List<&2, Laws.Seg>,
  +st: Jpeg.St,
  h_fit: Laws.segs.Fit(ss),
  h_inv: {M1.inv(st) == True{} : Bool}
) -> {M1.inv(Jpeg.decode.walk(Laws.segs.bytes(ss), st)) == True{} : Bool}:
  match ss:
    case Nil{}:
      h_inv
    case Laws.Seg{+mk, +hi, +lo, +body} <> +rest:
      (h_one, h_rest) = h_fit
      +sb = Laws.seg.bytes(Laws.Seg{mk, hi, lo, body})
      +rb = Laws.segs.bytes(rest)
      Equal.trans(Bool, M1.inv(Jpeg.decode.walk(List.append(&2, U32, sb, rb), st)),
        M1.inv(Jpeg.decode.walk(rb, Jpeg.decode.walk(sb, st))), True{},
        Equal.cong(Jpeg.St, Bool, xx => M1.inv(xx), Jpeg.decode.walk(List.append(&2, U32, sb, rb), st),
          Jpeg.decode.walk(rb, Jpeg.decode.walk(sb, st)), walk.app(sb, rb, st)),
        segs.inv(rest, Jpeg.decode.walk(sb, st), h_rest, seg.inv(mk, hi, lo, body, st, h_one, h_inv)))

# a walk from st over xs decodes to none, whatever the file's facts
def fin.Goal(xs: List<&2, U32>, st: Jpeg.St, facts: U32) -> Type:
  {Jpeg.decode.finish(Jpeg.decode.walk(xs, st), facts) == None{} : Maybe<&2, Jpeg.Pic>}

# after the segments, a frame header other than SOF0 and SOF1 decodes to none
def sofn.ph(
  ph: Jpeg.Phase,
  +sn: Laws.Sofn,
  +rest: List<&2, U32>,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32,
  +facts: U32,
  h_inv: {M1.inv(Jpeg.St{ph, frame, scan, tabs, ent, ri, kind, bad}) == True{} : Bool}
) -> fin.Goal(255 <> (Laws.sofn.byte(sn) <> rest), Jpeg.St{ph, frame, scan, tabs, ent, ri, kind, bad}, facts):
  match ph:
    case Jpeg.Seek{}:
      fin.after(rest, Jpeg.decode.mark(Laws.sofn.byte(sn), frame, scan, tabs, ent, ri, kind, bad), frame, scan, tabs,
        ent, ri, 2, 1, facts, sofn.mark(sn, frame, scan, tabs, ent, ri, kind, bad), fin.bad(frame, scan, tabs, ent, ri,
        2, facts))
    case Jpeg.Ent{}:
      fin.after(rest, Jpeg.decode.step.ph(Jpeg.EntFF{}, Laws.sofn.byte(sn), frame, scan, tabs, ent, ri, kind, bad),
        frame, scan, tabs, ent, ri, kind, 1, facts, sofn.ent(sn, frame, scan, tabs, ent, ri, kind, bad),
        fin.bad(frame, scan, tabs, ent, ri, kind, facts))
    case Jpeg.Stop{}:
      fin.after(255 <> (Laws.sofn.byte(sn) <> rest), Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad},
        frame, scan, tabs, ent, ri, kind, bad, facts, {==}, fin.none(frame, scan, tabs, ent, ri, kind, bad, facts,
        h_inv))
    case Jpeg.Mark{}:
      Empty.absurd(fin.Goal(255 <> (Laws.sofn.byte(sn) <> rest), Jpeg.St{Jpeg.Mark{}, frame, scan, tabs, ent, ri,
        kind, bad}, facts),
        M1.false_true(h_inv))
    case Jpeg.LenHi{mark}:
      Empty.absurd(fin.Goal(255 <> (Laws.sofn.byte(sn) <> rest), Jpeg.St{Jpeg.LenHi{mark}, frame, scan, tabs, ent, ri,
        kind, bad}, facts),
        M1.false_true(h_inv))
    case Jpeg.LenLo{mark, mhi}:
      Empty.absurd(fin.Goal(255 <> (Laws.sofn.byte(sn) <> rest), Jpeg.St{Jpeg.LenLo{mark, mhi}, frame, scan, tabs, ent,
        ri, kind, bad}, facts),
        M1.false_true(h_inv))
    case Jpeg.Pay{mark, left, acc}:
      Empty.absurd(fin.Goal(255 <> (Laws.sofn.byte(sn) <> rest), Jpeg.St{Jpeg.Pay{mark, left, acc}, frame, scan, tabs,
        ent, ri, kind, bad}, facts),
        M1.false_true(h_inv))
    case Jpeg.EntFF{}:
      Empty.absurd(fin.Goal(255 <> (Laws.sofn.byte(sn) <> rest), Jpeg.St{Jpeg.EntFF{}, frame, scan, tabs, ent, ri,
        kind, bad}, facts),
        M1.false_true(h_inv))

# after the segments, a frame header other than SOF0 and SOF1 decodes to none, whatever the state's phase
def sofn.st(
  +sn: Laws.Sofn,
  +rest: List<&2, U32>,
  st: Jpeg.St,
  +facts: U32,
  h_inv: {M1.inv(st) == True{} : Bool}
) -> fin.Goal(255 <> (Laws.sofn.byte(sn) <> rest), st, facts):
  match st:
    case Jpeg.St{ph, +frame, +scan, +tabs, +ent, +ri, +kind, +bad}:
      sofn.ph(ph, sn, rest, frame, scan, tabs, ent, ri, kind, bad, facts, h_inv)

# the walk of SOI and the segments decodes to none when a walk from where they leave it does, whatever the file's
# lead.none's parameter h_tail: the tail ends none from any state the walk keeps, with the whole file's facts
def LeadTail(-ss: List<&2, Laws.Seg>, -tail: List<&2, U32>) -> Type:
  @st: Jpeg.St -> {M1.inv(st) == True{} : Bool} -> fin.Goal(tail, st, Jpeg.decode.facts(Laws.jpeg.lead(ss, tail)))

# facts
def lead.none(
  +ss: List<&2, Laws.Seg>,
  +tail: List<&2, U32>,
  h_fit: Laws.segs.Fit(ss),
  h_tail: LeadTail(ss, tail)
) -> {Img.decode_jpeg(Laws.jpeg.lead(ss, tail)) == None{} : Maybe<&2, Img.Raster>}:
  +s1 = {Jpeg.St{Jpeg.Seek{}, Jpeg.decode.frame0(), Jpeg.decode.scan0(), Jpeg.decode.tabs0(), [], 0, 0, 0} : Jpeg.St}
  +sb = Laws.segs.bytes(ss)
  +s2 = Jpeg.decode.walk(sb, s1)
  +fx = Jpeg.decode.facts(Laws.jpeg.lead(ss, tail))
  Equal.cong(Maybe<&2, Jpeg.Pic>, Maybe<&2, Img.Raster>, mm => Img.decode_jpeg.out(mm),
    Jpeg.decode.finish(Jpeg.decode.walk(List.append(&2, U32, sb, tail), s1), fx), None{},
    Equal.trans(Maybe<&2, Jpeg.Pic>, Jpeg.decode.finish(Jpeg.decode.walk(List.append(&2, U32, sb, tail), s1), fx),
      Jpeg.decode.finish(Jpeg.decode.walk(tail, s2), fx), None{},
      Equal.cong(Jpeg.St, Maybe<&2, Jpeg.Pic>, xx => Jpeg.decode.finish(xx, fx),
        Jpeg.decode.walk(List.append(&2, U32, sb, tail), s1), Jpeg.decode.walk(tail, s2), walk.app(sb, tail, s1)),
      h_tail(s2, segs.inv(ss, s1, h_fit, {==}))))

def Laws.jpeg_refuse_sofn(segs, h_fit, sn, rest):
  lead.none(segs, 255 <> (Laws.sofn.byte(sn) <> rest), h_fit, st => hi => sofn.st(sn, rest, st,
    Jpeg.decode.facts(Laws.jpeg.lead(segs, 255 <> (Laws.sofn.byte(sn) <> rest))), hi))

# an SOF0 or SOF1 segment (marker mm) whose precision is not 8, and what follows, as bytes
def prec.bytes(+mm: U32, +hi: U32, +lo: U32, +pp: U32, +body: List<&2, U32>, +rest: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, 255 <> (mm <> (hi <> (lo <> (pp <> body)))), rest)

# what the walk does with a frame header marker mm it reads: between segments it opens a length field, inside a scan
# it stops the walk on an error, and its segment's body is read as an SOF0 body
def PrecMk(
  +mm: U32,
  +body: List<&2, U32>,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> Type:
  {Jpeg.decode.mark(mm, frame, scan, tabs, ent, ri, kind, bad) == Jpeg.St{Jpeg.LenHi{mm}, frame, scan, tabs, ent, ri,
    kind, bad} : Jpeg.St} & {Jpeg.decode.dispatch(mm, body, frame, scan, tabs, ent, ri, kind, bad) ==
    Jpeg.decode.read.sof(body, scan, tabs, ent, ri, kind, bad) : Jpeg.St} & {Jpeg.decode.step.ph(Jpeg.EntFF{}, mm,
    frame, scan, tabs, ent, ri, kind, bad) == Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, 1} : Jpeg.St}

# SOF0 and SOF1 are such markers
def prec.mk(
  +ext: Bool,
  +body: List<&2, U32>,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> PrecMk(Laws.sof.byte(ext), body, frame, scan, tabs, ent, ri, kind, bad):
  match ext:
    case True{}:
      ({==}, ({==}, {==}))
    case False{}:
      ({==}, ({==}, {==}))

# after the segments, an SOF0 or SOF1 segment whose precision is not 8 decodes to none
def prec.ph(
  ph: Jpeg.Phase,
  +mm: U32,
  +hi: U32,
  +lo: U32,
  +pp: U32,
  +body: List<&2, U32>,
  +rest: List<&2, U32>,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32,
  +facts: U32,
  h_len: Laws.seg.Fits(hi, lo, pp <> body),
  h_pp: {U32.is_eq(pp, 8) == False{} : Bool},
  h_mk: PrecMk(mm, pp <> body, frame, scan, tabs, ent, ri, kind, bad),
  h_inv: {M1.inv(Jpeg.St{ph, frame, scan, tabs, ent, ri, kind, bad}) == True{} : Bool}
) -> fin.Goal(prec.bytes(mm, hi, lo, pp, body, rest), Jpeg.St{ph.norm(ph), frame, scan, tabs, ent, ri, kind, bad},
  facts):
  match ph:
    case Jpeg.Seek{}:
      (e_lt, e_len) = h_len
      (e_mark, e_disp, _e_ent) = h_mk
      +sof = {255 <> (mm <> (hi <> (lo <> (pp <> body)))) : List<&2, U32>}
      +st = {Jpeg.St{Jpeg.Seek{}, frame, scan, tabs, ent, ri, kind, bad} : Jpeg.St}
      +lenhi = {Jpeg.St{Jpeg.LenHi{mm}, frame, scan, tabs, ent, ri, kind, bad} : Jpeg.St}
      +tail = {hi <> (lo <> (pp <> body)) : List<&2, U32>}
      Equal.trans(Maybe<&2, Jpeg.Pic>, Jpeg.decode.finish(Jpeg.decode.walk(List.append(&2, U32, sof, rest), st),
        facts), Jpeg.decode.finish(Jpeg.decode.walk(rest, Jpeg.decode.walk(sof, st)), facts), None{},
        Equal.cong(Jpeg.St, Maybe<&2, Jpeg.Pic>, xx => Jpeg.decode.finish(xx, facts),
          Jpeg.decode.walk(List.append(&2, U32, sof, rest), st), Jpeg.decode.walk(rest, Jpeg.decode.walk(sof, st)),
          walk.app(sof, rest, st)),
        fin.after(rest, Jpeg.decode.walk(sof, st), Jpeg.decode.frame0(), scan, tabs, ent, ri, kind, 1, facts,
          Equal.trans(Jpeg.St, Jpeg.decode.walk(tail, Jpeg.decode.mark(mm, frame, scan, tabs, ent, ri, kind, bad)),
            Jpeg.decode.walk(tail, lenhi), Jpeg.St{Jpeg.Stop{}, Jpeg.decode.frame0(), scan, tabs, ent, ri, kind, 1},
            Equal.cong(Jpeg.St, Jpeg.St, ss => Jpeg.decode.walk(tail, ss), Jpeg.decode.mark(mm, frame, scan, tabs, ent,
              ri, kind, bad), lenhi, e_mark),
            Equal.trans(Jpeg.St, Jpeg.decode.walk(tail, lenhi), Jpeg.decode.dispatch(mm, pp <> body, frame, scan, tabs,
              ent, ri, kind, bad), Jpeg.St{Jpeg.Stop{}, Jpeg.decode.frame0(), scan, tabs, ent, ri, kind, 1},
              M2.seg.read(U32.is_lt(Laws.seg.len(hi, lo), 2), Laws.seg.len(hi, lo), pp <> body, mm, frame, scan, tabs,
                ent, ri, kind, bad, e_lt, e_len),
              Equal.trans(Jpeg.St, Jpeg.decode.dispatch(mm, pp <> body, frame, scan, tabs, ent, ri, kind, bad),
                Jpeg.decode.read.sof.p(U32.is_eq(pp, 8), body, scan, tabs, ent, ri, kind, bad),
                Jpeg.St{Jpeg.Stop{}, Jpeg.decode.frame0(), scan, tabs, ent, ri, kind, 1}, e_disp,
                Equal.cong(Bool, Jpeg.St, bb => Jpeg.decode.read.sof.p(bb, body, scan, tabs, ent, ri, kind, bad),
                  U32.is_eq(pp, 8), False{}, h_pp)))),
          fin.bad(Jpeg.decode.frame0(), scan, tabs, ent, ri, kind, facts)))
    case Jpeg.Ent{}:
      (_e_mark, _e_disp, e_ent) = h_mk
      +sof = {255 <> (mm <> (hi <> (lo <> (pp <> body)))) : List<&2, U32>}
      +st = {Jpeg.St{Jpeg.Ent{}, frame, scan, tabs, ent, ri, kind, bad} : Jpeg.St}
      +tail = {hi <> (lo <> (pp <> body)) : List<&2, U32>}
      +stop = {Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, 1} : Jpeg.St}
      Equal.trans(Maybe<&2, Jpeg.Pic>, Jpeg.decode.finish(Jpeg.decode.walk(List.append(&2, U32, sof, rest), st),
        facts), Jpeg.decode.finish(Jpeg.decode.walk(rest, Jpeg.decode.walk(sof, st)), facts), None{},
        Equal.cong(Jpeg.St, Maybe<&2, Jpeg.Pic>, xx => Jpeg.decode.finish(xx, facts),
          Jpeg.decode.walk(List.append(&2, U32, sof, rest), st), Jpeg.decode.walk(rest, Jpeg.decode.walk(sof, st)),
          walk.app(sof, rest, st)),
        fin.after(rest, Jpeg.decode.walk(sof, st), frame, scan, tabs, ent, ri, kind, 1, facts,
          Equal.trans(Jpeg.St, Jpeg.decode.walk(tail, Jpeg.decode.step.ph(Jpeg.EntFF{}, mm, frame, scan, tabs, ent, ri,
            kind, bad)), Jpeg.decode.walk(tail, stop), stop, Equal.cong(Jpeg.St, Jpeg.St, ss => Jpeg.decode.walk(tail,
            ss), Jpeg.decode.step.ph(Jpeg.EntFF{}, mm, frame, scan, tabs, ent, ri, kind, bad), stop, e_ent),
            stop.walk(tail, frame, scan, tabs, ent, ri, kind, 1)),
          fin.bad(frame, scan, tabs, ent, ri, kind, facts)))
    case Jpeg.Stop{}:
      fin.after(prec.bytes(mm, hi, lo, pp, body, rest), Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad},
        frame, scan, tabs, ent, ri, kind, bad, facts, {==}, fin.none(frame, scan, tabs, ent, ri, kind, bad, facts,
        h_inv))
    case Jpeg.Mark{}:
      fin.after(prec.bytes(mm, hi, lo, pp, body, rest), Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad},
        frame, scan, tabs, ent, ri, kind, bad, facts, {==}, fin.none(frame, scan, tabs, ent, ri, kind, bad, facts,
          Empty.absurd({U32.is_eq(kind, 0) == True{} : Bool}, M1.false_true(h_inv))))
    case Jpeg.LenHi{_mark}:
      fin.after(prec.bytes(mm, hi, lo, pp, body, rest), Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad},
        frame, scan, tabs, ent, ri, kind, bad, facts, {==}, fin.none(frame, scan, tabs, ent, ri, kind, bad, facts,
          Empty.absurd({U32.is_eq(kind, 0) == True{} : Bool}, M1.false_true(h_inv))))
    case Jpeg.LenLo{_mark, _mhi}:
      fin.after(prec.bytes(mm, hi, lo, pp, body, rest), Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad},
        frame, scan, tabs, ent, ri, kind, bad, facts, {==}, fin.none(frame, scan, tabs, ent, ri, kind, bad, facts,
          Empty.absurd({U32.is_eq(kind, 0) == True{} : Bool}, M1.false_true(h_inv))))
    case Jpeg.Pay{_mark, _left, _acc}:
      fin.after(prec.bytes(mm, hi, lo, pp, body, rest), Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad},
        frame, scan, tabs, ent, ri, kind, bad, facts, {==}, fin.none(frame, scan, tabs, ent, ri, kind, bad, facts,
          Empty.absurd({U32.is_eq(kind, 0) == True{} : Bool}, M1.false_true(h_inv))))
    case Jpeg.EntFF{}:
      fin.after(prec.bytes(mm, hi, lo, pp, body, rest), Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad},
        frame, scan, tabs, ent, ri, kind, bad, facts, {==}, fin.none(frame, scan, tabs, ent, ri, kind, bad, facts,
          Empty.absurd({U32.is_eq(kind, 0) == True{} : Bool}, M1.false_true(h_inv))))

# after the segments, an SOF0 or SOF1 segment whose precision is not 8 decodes to none, whatever the state's phase
def prec.st(
  +ext: Bool,
  +hi: U32,
  +lo: U32,
  +pp: U32,
  +body: List<&2, U32>,
  +rest: List<&2, U32>,
  st: Jpeg.St,
  +facts: U32,
  h_len: Laws.seg.Fits(hi, lo, pp <> body),
  h_pp: {U32.is_eq(pp, 8) == False{} : Bool},
  h_inv: {M1.inv(st) == True{} : Bool}
) -> fin.Goal(prec.bytes(Laws.sof.byte(ext), hi, lo, pp, body, rest), st, facts):
  match st:
    case Jpeg.St{+ph, +frame, +scan, +tabs, +ent, +ri, +kind, +bad}:
      +mm = Laws.sof.byte(ext)
      +xs = prec.bytes(mm, hi, lo, pp, body, rest)
      +h_st = {h_inv : {M1.inv(Jpeg.St{ph, frame, scan, tabs, ent, ri, kind, bad}) == True{} : Bool}}
      Equal.trans(Maybe<&2, Jpeg.Pic>,
        Jpeg.decode.finish(Jpeg.decode.walk(xs, Jpeg.St{ph, frame, scan, tabs, ent, ri, kind, bad}), facts),
        Jpeg.decode.finish(Jpeg.decode.walk(xs, Jpeg.St{ph.norm(ph), frame, scan, tabs, ent, ri, kind, bad}), facts),
        None{},
        Equal.cong(Jpeg.Phase, Maybe<&2, Jpeg.Pic>, qq => Jpeg.decode.finish(Jpeg.decode.walk(xs, Jpeg.St{qq, frame,
          scan, tabs, ent, ri, kind, bad}), facts), ph, ph.norm(ph), ph.norm.eq(ph, M1.and_left(M1.ph.ok(ph),
          U32.is_eq(kind, 0), h_st))),
        prec.ph(ph, mm, hi, lo, pp, body, rest, frame, scan, tabs, ent, ri, kind, bad, facts, h_len, h_pp,
          prec.mk(ext, pp <> body, frame, scan, tabs, ent, ri, kind, bad), h_st))

def Laws.jpeg_refuse_precision(segs, h_fit, ext, hi, lo, pp, body, h_len, h_pp, rest):
  lead.none(segs, prec.bytes(Laws.sof.byte(ext), hi, lo, pp, body, rest), h_fit,
    st => hs => prec.st(ext, hi, lo, pp, body, rest, st, Jpeg.decode.facts(Laws.jpeg.lead(segs,
      prec.bytes(Laws.sof.byte(ext), hi, lo, pp, body, rest))), h_len, h_pp, hs))
