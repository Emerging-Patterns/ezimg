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
                      dht.inv(rest, True{}, True{}, U32.to_nat(Jpeg.decode.sum.counts(List.reverse(&2, U32,
                        bb <> counts), 0)), cls, id, List.reverse(&2, U32, bb <> counts), [], frame, scan, tabs, ent,
                        ri, kind, bad)
                    case 1n+qq:
                      dht.inv(rest, True{}, False{}, 1n+qq, cls, id, bb <> counts, [], frame, scan, tabs, ent, ri, kind,
                        bad)
            case True{}:
              match phase:
                case 0n:
                  {==}
                case 1n+pp:
                  match pp:
                    case 0n:
                      dht.inv(rest, True{}, False{}, 0n, 0, 0, [], [], frame, scan, Jpeg.decode.huff.put(tabs, cls, id,
                        Jpeg.decode.canon(272n, 0n, counts, List.reverse(&2, U32, bb <> syms), 0, 0, [], [], [])), ent,
                        ri, kind, bad)
                    case 1n+qq:
                      dht.inv(rest, True{}, True{}, 1n+qq, cls, id, counts, bb <> syms, frame, scan, tabs, ent, ri,
                        kind, bad)

# a DQT body leaves kind as it found it, and the walk seeking or stopped
def dqt.inv(
  xs: List<&2, U32>,
  ok: Bool,
  phase: Nat,
  +id: U32,
  +acc: List<&2, U32>,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> {M1.inv(Jpeg.decode.read.dqt(xs, ok, phase, id, acc, frame, scan, tabs, ent, ri, kind, bad))
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
              dqt.inv(rest, U32.is_eq(U32.shrn(bb, 4n), 0), 64n, U32.and(bb, 15), [], frame, scan, tabs, ent, ri, kind,
                bad)
            case 1n+pp:
              match pp:
                case 0n:
                  dqt.inv(rest, True{}, 0n, 0, [], frame, scan, Jpeg.decode.q.put(tabs, id, List.reverse(&2, U32,
                    bb <> acc)), ent, ri, kind, bad)
                case 1n+qq:
                  dqt.inv(rest, True{}, 1n+qq, id, bb <> acc, frame, scan, tabs, ent, ri, kind, bad)

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
) -> {M1.inv(Jpeg.decode.read.sos.cs(left, xs, sids, td, ta, ns, frame, tabs, ent, ri, kind, bad))
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
          sos.ok.inv(U32.is_eq(ss, 0), U32.is_eq(se, 63), U32.is_eq(ah, 0), sids, td, ta, ns, frame, tabs, ent, ri,
            kind, bad)
    case 1n+pp:
      match xs:
        case Nil{}:
          {==}
        case _id <> Nil{}:
          {==}
        case +id <> +tdta <> rest:
          sos.cs.inv(pp, rest, id <> sids, U32.shrn(tdta, 4n) <> td, U32.and(tdta, 15) <> ta, ns, frame, tabs, ent, ri,
            kind, bad)

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
      sos.cs.inv(U32.to_nat(ns), rest, [], [], [], ns, frame, tabs, ent, ri, kind, bad)
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

# the density check of an APP0 body leaves kind as it found it, and the walk seeking or stopped
def den.inv(
  xz: Bool,
  yz: Bool,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> {M1.inv(Jpeg.decode.read.app0.den(xz, yz, frame, scan, tabs, ent, ri, kind, bad)) == U32.is_eq(kind, 0) : Bool}:
  match xz yz:
    case True{} _yz:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# an APP0 body, JFIF or not, leaves kind as it found it, and the walk seeking or stopped
def app0.id.inv(
  jfif: Bool,
  +xh: U32,
  +xl: U32,
  +yh: U32,
  +yl: U32,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> {M1.inv(Jpeg.decode.read.app0.id(jfif, xh, xl, yh, yl, frame, scan, tabs, ent, ri, kind, bad))
  == U32.is_eq(kind, 0) : Bool}:
  match jfif:
    case True{}:
      den.inv(U32.is_eq(Jpeg.decode.u16(xh, xl), 0), U32.is_eq(Jpeg.decode.u16(yh, yl), 0), frame, scan, tabs, ent, ri,
        kind, bad)
    case False{}:
      {==}

# an APP0 body leaves kind as it found it, and the walk seeking or stopped
def app0.inv(
  xs: List<&2, U32>,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> {M1.inv(Jpeg.decode.read.app0(xs, frame, scan, tabs, ent, ri, kind, bad)) == U32.is_eq(kind, 0) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case _c0 <> Nil{}:
      {==}
    case _c0 <> _c1 <> Nil{}:
      {==}
    case _c0 <> _c1 <> _c2 <> Nil{}:
      {==}
    case _c0 <> _c1 <> _c2 <> _c3 <> Nil{}:
      {==}
    case _c0 <> _c1 <> _c2 <> _c3 <> _c4 <> Nil{}:
      {==}
    case _c0 <> _c1 <> _c2 <> _c3 <> _c4 <> _maj <> Nil{}:
      {==}
    case _c0 <> _c1 <> _c2 <> _c3 <> _c4 <> _maj <> _min <> Nil{}:
      {==}
    case _c0 <> _c1 <> _c2 <> _c3 <> _c4 <> _maj <> _min <> _u <> Nil{}:
      {==}
    case _c0 <> _c1 <> _c2 <> _c3 <> _c4 <> _maj <> _min <> _u <> _xh <> Nil{}:
      {==}
    case _c0 <> _c1 <> _c2 <> _c3 <> _c4 <> _maj <> _min <> _u <> _xh <> _xl <> Nil{}:
      {==}
    case _c0 <> _c1 <> _c2 <> _c3 <> _c4 <> _maj <> _min <> _u <> _xh <> _xl <> _yh <> Nil{}:
      {==}
    case _c0 <> _c1 <> _c2 <> _c3 <> _c4 <> _maj <> _min <> _u <> _xh <> _xl <> _yh <> _yl <> Nil{}:
      {==}
    case _c0 <> _c1 <> _c2 <> _c3 <> _c4 <> _maj <> _min <> _u <> _xh <> _xl <> _yh <> _yl <> _xt <> Nil{}:
      {==}
    case +c0 <> +c1 <> +c2 <> +c3 <> +c4 <> _maj <> _min <> _u <> +xh <> +xl <> +yh <> +yl <> _xt <> _yt <> _rest:
      app0.id.inv(Bool.and(U32.is_eq(c0, 74), Bool.and(U32.is_eq(c1, 70), Bool.and(U32.is_eq(c2, 73),
        Bool.and(U32.is_eq(c3, 70), U32.is_eq(c4, 0))))), xh, xl, yh, yl, frame, scan, tabs, ent, ri, kind, bad)

# a stopped walk that read no frame header decodes to none
def fin.none(
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32,
  hk: {U32.is_eq(kind, 0) == True{} : Bool}
) -> {Jpeg.decode.finish(Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad}) == None{} : Maybe<&2, Jpeg.Pic>}:
  Equal.cong(U32, Maybe<&2, Jpeg.Pic>, kk => Jpeg.decode.finish(Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kk,
    bad}), kind, 0, M1.ueq(kind, 0, hk))

# a walk that stopped on an error decodes to none
def fin.bad.go(
  ok1: Bool,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32
) -> {Jpeg.decode.finish.ok(ok1, False{}, frame, scan, tabs, ent, ri) == None{} : Maybe<&2, Jpeg.Pic>}:
  match ok1:
    case True{}:
      {==}
    case False{}:
      {==}

# a walk that stopped on an error decodes to none, whatever kind it read
def fin.bad(
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32
) -> {Jpeg.decode.finish(Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, 1}) == None{} : Maybe<&2, Jpeg.Pic>}:
  fin.bad.go(U32.is_eq(kind, 1), frame, scan, tabs, ent, ri)

# the state st decodes to none
def fin.Nil(st: Jpeg.St) -> Type:
  {Jpeg.decode.finish(st) == None{} : Maybe<&2, Jpeg.Pic>}

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
  e_st: {st == Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad} : Jpeg.St},
  e_none: fin.Nil(Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad})
) -> {Jpeg.decode.finish(Jpeg.decode.walk(rest, st)) == None{} : Maybe<&2, Jpeg.Pic>}:
  +stop = {Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad} : Jpeg.St}
  Equal.trans(Maybe<&2, Jpeg.Pic>, Jpeg.decode.finish(Jpeg.decode.walk(rest, st)),
    Jpeg.decode.finish(Jpeg.decode.walk(rest, stop)), None{},
    Equal.cong(Jpeg.St, Maybe<&2, Jpeg.Pic>, ss => Jpeg.decode.finish(Jpeg.decode.walk(rest, ss)), st, stop, e_st),
    Equal.trans(Maybe<&2, Jpeg.Pic>, Jpeg.decode.finish(Jpeg.decode.walk(rest, stop)), Jpeg.decode.finish(stop), None{},
      Equal.cong(Jpeg.St, Maybe<&2, Jpeg.Pic>, ss => Jpeg.decode.finish(ss), Jpeg.decode.walk(rest, stop), stop,
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
      dqt.inv(body, True{}, 0n, 0, [], frame, scan, tabs, ent, ri, kind, bad)
    case Laws.MSos{}:
      sos.inv(body, frame, tabs, ent, ri, kind, bad)
    case Laws.MDri{}:
      dri.inv(body, frame, scan, tabs, ent, kind, bad)
    case Laws.MCom{}:
      {==}
    case Laws.MApp0{}:
      app0.inv(body, frame, scan, tabs, ent, ri, kind, bad)
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
    case Laws.Sof1{}:
      {==}
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
    case Laws.Sof1{}:
      {==}
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

# a walk from st over xs decodes to none
def fin.Goal(xs: List<&2, U32>, st: Jpeg.St) -> Type:
  {Jpeg.decode.finish(Jpeg.decode.walk(xs, st)) == None{} : Maybe<&2, Jpeg.Pic>}

# after the segments, a frame header other than SOF0 decodes to none
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
  h_inv: {M1.inv(Jpeg.St{ph, frame, scan, tabs, ent, ri, kind, bad}) == True{} : Bool}
) -> fin.Goal(255 <> (Laws.sofn.byte(sn) <> rest), Jpeg.St{ph, frame, scan, tabs, ent, ri, kind, bad}):
  match ph:
    case Jpeg.Seek{}:
      fin.after(rest, Jpeg.decode.mark(Laws.sofn.byte(sn), frame, scan, tabs, ent, ri, kind, bad), frame, scan, tabs,
        ent, ri, 2, 1, sofn.mark(sn, frame, scan, tabs, ent, ri, kind, bad), fin.bad(frame, scan, tabs, ent, ri, 2))
    case Jpeg.Ent{}:
      fin.after(rest, Jpeg.decode.step.ph(Jpeg.EntFF{}, Laws.sofn.byte(sn), frame, scan, tabs, ent, ri, kind, bad),
        frame, scan, tabs, ent, ri, kind, 1, sofn.ent(sn, frame, scan, tabs, ent, ri, kind, bad),
        fin.bad(frame, scan, tabs, ent, ri, kind))
    case Jpeg.Stop{}:
      fin.after(255 <> (Laws.sofn.byte(sn) <> rest), Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad},
        frame, scan, tabs, ent, ri, kind, bad, {==}, fin.none(frame, scan, tabs, ent, ri, kind, bad, h_inv))
    case Jpeg.Mark{}:
      Empty.absurd(fin.Goal(255 <> (Laws.sofn.byte(sn) <> rest), Jpeg.St{Jpeg.Mark{}, frame, scan, tabs, ent, ri,
        kind, bad}),
        M1.false_true(h_inv))
    case Jpeg.LenHi{mark}:
      Empty.absurd(fin.Goal(255 <> (Laws.sofn.byte(sn) <> rest), Jpeg.St{Jpeg.LenHi{mark}, frame, scan, tabs, ent, ri,
        kind, bad}),
        M1.false_true(h_inv))
    case Jpeg.LenLo{mark, mhi}:
      Empty.absurd(fin.Goal(255 <> (Laws.sofn.byte(sn) <> rest), Jpeg.St{Jpeg.LenLo{mark, mhi}, frame, scan, tabs, ent,
        ri, kind, bad}),
        M1.false_true(h_inv))
    case Jpeg.Pay{mark, left, acc}:
      Empty.absurd(fin.Goal(255 <> (Laws.sofn.byte(sn) <> rest), Jpeg.St{Jpeg.Pay{mark, left, acc}, frame, scan, tabs,
        ent, ri, kind, bad}),
        M1.false_true(h_inv))
    case Jpeg.EntFF{}:
      Empty.absurd(fin.Goal(255 <> (Laws.sofn.byte(sn) <> rest), Jpeg.St{Jpeg.EntFF{}, frame, scan, tabs, ent, ri,
        kind, bad}),
        M1.false_true(h_inv))

# after the segments, a frame header other than SOF0 decodes to none, whatever the state's phase
def sofn.st(
  +sn: Laws.Sofn,
  +rest: List<&2, U32>,
  st: Jpeg.St,
  h_inv: {M1.inv(st) == True{} : Bool}
) -> fin.Goal(255 <> (Laws.sofn.byte(sn) <> rest), st):
  match st:
    case Jpeg.St{ph, +frame, +scan, +tabs, +ent, +ri, +kind, +bad}:
      sofn.ph(ph, sn, rest, frame, scan, tabs, ent, ri, kind, bad, h_inv)

# the walk of SOI and the segments decodes to none when a walk from where they leave it does
def lead.none(
  +ss: List<&2, Laws.Seg>,
  +tail: List<&2, U32>,
  h_fit: Laws.segs.Fit(ss),
  h_tail: @st: Jpeg.St -> {M1.inv(st) == True{} : Bool} -> fin.Goal(tail, st)
) -> {Img.decode_jpeg(Laws.jpeg.lead(ss, tail)) == None{} : Maybe<&2, Img.Raster>}:
  +s1 = {Jpeg.St{Jpeg.Seek{}, Jpeg.decode.frame0(), Jpeg.decode.scan0(), Jpeg.decode.tabs0(), [], 0, 0, 0} : Jpeg.St}
  +sb = Laws.segs.bytes(ss)
  +s2 = Jpeg.decode.walk(sb, s1)
  Equal.cong(Maybe<&2, Jpeg.Pic>, Maybe<&2, Img.Raster>, mm => Img.decode_jpeg.out(mm),
    Jpeg.decode.finish(Jpeg.decode.walk(List.append(&2, U32, sb, tail), s1)), None{},
    Equal.trans(Maybe<&2, Jpeg.Pic>, Jpeg.decode.finish(Jpeg.decode.walk(List.append(&2, U32, sb, tail), s1)),
      Jpeg.decode.finish(Jpeg.decode.walk(tail, s2)), None{},
      Equal.cong(Jpeg.St, Maybe<&2, Jpeg.Pic>, xx => Jpeg.decode.finish(xx),
        Jpeg.decode.walk(List.append(&2, U32, sb, tail), s1), Jpeg.decode.walk(tail, s2), walk.app(sb, tail, s1)),
      h_tail(s2, segs.inv(ss, s1, h_fit, {==}))))

def Laws.jpeg_refuse_sofn(segs, h_fit, sn, rest):
  lead.none(segs, 255 <> (Laws.sofn.byte(sn) <> rest), h_fit, st => hi => sofn.st(sn, rest, st, hi))

# an SOF0 segment whose precision is not 8, and what follows, as bytes
def prec.bytes(+hi: U32, +lo: U32, +pp: U32, +body: List<&2, U32>, +rest: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, 255 <> (192 <> (hi <> (lo <> (pp <> body)))), rest)

# after the segments, an SOF0 segment whose precision is not 8 decodes to none
def prec.ph(
  ph: Jpeg.Phase,
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
  h_len: Laws.seg.Fits(hi, lo, pp <> body),
  h_pp: {U32.is_eq(pp, 8) == False{} : Bool},
  h_inv: {M1.inv(Jpeg.St{ph, frame, scan, tabs, ent, ri, kind, bad}) == True{} : Bool}
) -> fin.Goal(prec.bytes(hi, lo, pp, body, rest), Jpeg.St{ph.norm(ph), frame, scan, tabs, ent, ri, kind, bad}):
  match ph:
    case Jpeg.Seek{}:
      (e_lt, e_len) = h_len
      +sof = {255 <> (192 <> (hi <> (lo <> (pp <> body)))) : List<&2, U32>}
      +st = {Jpeg.St{Jpeg.Seek{}, frame, scan, tabs, ent, ri, kind, bad} : Jpeg.St}
      Equal.trans(Maybe<&2, Jpeg.Pic>, Jpeg.decode.finish(Jpeg.decode.walk(List.append(&2, U32, sof, rest), st)),
        Jpeg.decode.finish(Jpeg.decode.walk(rest, Jpeg.decode.walk(sof, st))), None{},
        Equal.cong(Jpeg.St, Maybe<&2, Jpeg.Pic>, xx => Jpeg.decode.finish(xx),
          Jpeg.decode.walk(List.append(&2, U32, sof, rest), st), Jpeg.decode.walk(rest, Jpeg.decode.walk(sof, st)),
          walk.app(sof, rest, st)),
        fin.after(rest, Jpeg.decode.walk(sof, st), Jpeg.decode.frame0(), scan, tabs, ent, ri, kind, 1,
          Equal.trans(Jpeg.St, Jpeg.decode.walk(sof, st),
            Jpeg.decode.read.sof.p(U32.is_eq(pp, 8), body, scan, tabs, ent, ri, kind, bad),
            Jpeg.St{Jpeg.Stop{}, Jpeg.decode.frame0(), scan, tabs, ent, ri, kind, 1},
            M2.seg.read(U32.is_lt(Laws.seg.len(hi, lo), 2), Laws.seg.len(hi, lo), pp <> body, 192, frame, scan, tabs,
              ent, ri, kind, bad, e_lt, e_len),
            Equal.cong(Bool, Jpeg.St, bb => Jpeg.decode.read.sof.p(bb, body, scan, tabs, ent, ri, kind, bad),
              U32.is_eq(pp, 8), False{}, h_pp)),
          fin.bad(Jpeg.decode.frame0(), scan, tabs, ent, ri, kind)))
    case Jpeg.Ent{}:
      +sof = {255 <> (192 <> (hi <> (lo <> (pp <> body)))) : List<&2, U32>}
      +st = {Jpeg.St{Jpeg.Ent{}, frame, scan, tabs, ent, ri, kind, bad} : Jpeg.St}
      Equal.trans(Maybe<&2, Jpeg.Pic>, Jpeg.decode.finish(Jpeg.decode.walk(List.append(&2, U32, sof, rest), st)),
        Jpeg.decode.finish(Jpeg.decode.walk(rest, Jpeg.decode.walk(sof, st))), None{},
        Equal.cong(Jpeg.St, Maybe<&2, Jpeg.Pic>, xx => Jpeg.decode.finish(xx),
          Jpeg.decode.walk(List.append(&2, U32, sof, rest), st), Jpeg.decode.walk(rest, Jpeg.decode.walk(sof, st)),
          walk.app(sof, rest, st)),
        fin.after(rest, Jpeg.decode.walk(sof, st), frame, scan, tabs, ent, ri, kind, 1,
          stop.walk(hi <> (lo <> (pp <> body)), frame, scan, tabs, ent, ri, kind, 1),
          fin.bad(frame, scan, tabs, ent, ri, kind)))
    case Jpeg.Stop{}:
      fin.after(prec.bytes(hi, lo, pp, body, rest), Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad},
        frame, scan, tabs, ent, ri, kind, bad, {==}, fin.none(frame, scan, tabs, ent, ri, kind, bad, h_inv))
    case Jpeg.Mark{}:
      fin.after(prec.bytes(hi, lo, pp, body, rest), Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad},
        frame, scan, tabs, ent, ri, kind, bad, {==}, fin.none(frame, scan, tabs, ent, ri, kind, bad,
          Empty.absurd({U32.is_eq(kind, 0) == True{} : Bool}, M1.false_true(h_inv))))
    case Jpeg.LenHi{_mark}:
      fin.after(prec.bytes(hi, lo, pp, body, rest), Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad},
        frame, scan, tabs, ent, ri, kind, bad, {==}, fin.none(frame, scan, tabs, ent, ri, kind, bad,
          Empty.absurd({U32.is_eq(kind, 0) == True{} : Bool}, M1.false_true(h_inv))))
    case Jpeg.LenLo{_mark, _mhi}:
      fin.after(prec.bytes(hi, lo, pp, body, rest), Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad},
        frame, scan, tabs, ent, ri, kind, bad, {==}, fin.none(frame, scan, tabs, ent, ri, kind, bad,
          Empty.absurd({U32.is_eq(kind, 0) == True{} : Bool}, M1.false_true(h_inv))))
    case Jpeg.Pay{_mark, _left, _acc}:
      fin.after(prec.bytes(hi, lo, pp, body, rest), Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad},
        frame, scan, tabs, ent, ri, kind, bad, {==}, fin.none(frame, scan, tabs, ent, ri, kind, bad,
          Empty.absurd({U32.is_eq(kind, 0) == True{} : Bool}, M1.false_true(h_inv))))
    case Jpeg.EntFF{}:
      fin.after(prec.bytes(hi, lo, pp, body, rest), Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad},
        frame, scan, tabs, ent, ri, kind, bad, {==}, fin.none(frame, scan, tabs, ent, ri, kind, bad,
          Empty.absurd({U32.is_eq(kind, 0) == True{} : Bool}, M1.false_true(h_inv))))

# after the segments, an SOF0 segment whose precision is not 8 decodes to none, whatever the state's phase
def prec.st(
  +hi: U32,
  +lo: U32,
  +pp: U32,
  +body: List<&2, U32>,
  +rest: List<&2, U32>,
  st: Jpeg.St,
  h_len: Laws.seg.Fits(hi, lo, pp <> body),
  h_pp: {U32.is_eq(pp, 8) == False{} : Bool},
  h_inv: {M1.inv(st) == True{} : Bool}
) -> fin.Goal(prec.bytes(hi, lo, pp, body, rest), st):
  match st:
    case Jpeg.St{+ph, +frame, +scan, +tabs, +ent, +ri, +kind, +bad}:
      +xs = prec.bytes(hi, lo, pp, body, rest)
      +h_st = {h_inv : {M1.inv(Jpeg.St{ph, frame, scan, tabs, ent, ri, kind, bad}) == True{} : Bool}}
      Equal.trans(Maybe<&2, Jpeg.Pic>,
        Jpeg.decode.finish(Jpeg.decode.walk(xs, Jpeg.St{ph, frame, scan, tabs, ent, ri, kind, bad})),
        Jpeg.decode.finish(Jpeg.decode.walk(xs, Jpeg.St{ph.norm(ph), frame, scan, tabs, ent, ri, kind, bad})),
        None{},
        Equal.cong(Jpeg.Phase, Maybe<&2, Jpeg.Pic>, qq => Jpeg.decode.finish(Jpeg.decode.walk(xs, Jpeg.St{qq, frame,
          scan, tabs, ent, ri, kind, bad})), ph, ph.norm(ph), ph.norm.eq(ph, M1.and_left(M1.ph.ok(ph),
          U32.is_eq(kind, 0), h_st))),
        prec.ph(ph, hi, lo, pp, body, rest, frame, scan, tabs, ent, ri, kind, bad, h_len, h_pp, h_st))

def Laws.jpeg_refuse_precision(segs, h_fit, hi, lo, pp, body, h_len, h_pp, rest):
  lead.none(segs, prec.bytes(hi, lo, pp, body, rest), h_fit,
    st => hs => prec.st(hi, lo, pp, body, rest, st, h_len, h_pp, hs))
