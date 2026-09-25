# proof/wp7-jpeg-struct: lemmas for the JPEG structure rows (IMG-JPG-1, IMG-JPG-5, IMG-PIX-1's JPEG
# side). PROOF.bend imports this file, so the gate checks it.
import Base
import ../main.bend as Img
import ../src/jpeg.bend as Jpeg
import ../src/jpeg_enc.bend as Jenc
import ../src/png.bend as Png
import ./u32.bend as U32L

# True is never False
def true_false(ee: {True{} == False{} : Bool}) -> Empty:
  U32L.false_true(Equal.sym(Bool, True{}, False{}, ee))

# a comparison that is greater is not equal
def gt_ne(cc: Cmp, hh: {Cmp.is_gt(cc) == True{} : Bool}) -> {Cmp.is_eq(cc) == False{} : Bool}:
  match cc:
    case LT{}:
      Empty.absurd({False{} == False{} : Bool}, U32L.false_true(hh))
    case EQ{}:
      Empty.absurd({True{} == False{} : Bool}, U32L.false_true(hh))
    case GT{}:
      {==}

# a comparison that is at most is not greater
def le_ngt(cc: Cmp, hh: {Cmp.is_le(cc) == True{} : Bool}) -> {Cmp.is_gt(cc) == False{} : Bool}:
  match cc:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({True{} == False{} : Bool}, U32L.false_true(hh))

# the encoder's size test is false when no side is zero and none passes 65535
def bad_no(
  zw: Bool,
  zh: Bool,
  bw: Bool,
  bh: Bool,
  ew: {zw == False{} : Bool},
  eh: {zh == False{} : Bool},
  gw: {bw == False{} : Bool},
  gh: {bh == False{} : Bool}
) -> {Jenc.encode.bad.w(zw, zh, bw, bh) == False{} : Bool}:
  match zw zh bw bh:
    case False{} False{} False{} False{}:
      {==}
    case True{} _zh _bw _bh:
      Empty.absurd({True{} == False{} : Bool}, true_false(ew))
    case False{} True{} _bw _bh:
      Empty.absurd({True{} == False{} : Bool}, true_false(eh))
    case False{} False{} True{} _bh:
      Empty.absurd({True{} == False{} : Bool}, true_false(gw))
    case False{} False{} False{} True{}:
      Empty.absurd({True{} == False{} : Bool}, true_false(gh))

# a size encode_png accepts and whose sides are at most 65535 passes the JPEG encoder's size test
def bad_of_good(
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  e_good: {Png.enc.good(ww, hh, px) == True{} : Bool},
  h_w: {U32.is_le(ww, 65535) == True{} : Bool},
  h_h: {U32.is_le(hh, 65535) == True{} : Bool}
) -> {Jenc.encode.bad(ww, hh) == False{} : Bool}:
  +e_gt = {U32L.and_left(Bool.and(U32.is_gt(ww, 0), U32.is_gt(hh, 0)),
    Png.enc.rows(px, U32.is_zero(hh), U32.is_lt(Png.enc.len(px, 0), ww), ww, hh, Png.enc.len(px, 0)), e_good)
    : {Bool.and(U32.is_gt(ww, 0), U32.is_gt(hh, 0)) == True{} : Bool}}
  bad_no(U32.is_eq(ww, 0), U32.is_eq(hh, 0), U32.is_gt(ww, 65535), U32.is_gt(hh, 65535),
    gt_ne(U32.cmp(ww, 0), U32L.and_left(U32.is_gt(ww, 0), U32.is_gt(hh, 0), e_gt)),
    gt_ne(U32.cmp(hh, 0), U32L.and_right(U32.is_gt(ww, 0), U32.is_gt(hh, 0), e_gt)),
    le_ngt(U32.cmp(ww, 65535), h_w), le_ngt(U32.cmp(hh, 65535), h_h))

# 24 zero bits
def byte.zero24() -> Word(24n):
  Word.zero(24n)

# eight bits over 24 zero bits
def byte.w(
  c0: Bool,
  c1: Bool,
  c2: Bool,
  c3: Bool,
  c4: Bool,
  c5: Bool,
  c6: Bool,
  c7: Bool
) -> U32:
  U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, byte.zero24()}}}}}}}}}

# or with False on the right is the bit
def or_f(bb: Bool) -> {bb == Bool.or(bb, False{}) : Bool}:
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# a byte whose bits were each or-ed with False is the byte
def or_byte(
  +b0: Bool,
  +b1: Bool,
  +b2: Bool,
  +b3: Bool,
  +b4: Bool,
  +b5: Bool,
  +b6: Bool,
  +b7: Bool
) -> {byte.w(Bool.or(b0, False{}), Bool.or(b1, False{}), Bool.or(b2, False{}), Bool.or(b3, False{}),
  Bool.or(b4, False{}), Bool.or(b5, False{}), Bool.or(b6, False{}), Bool.or(b7, False{}))
  == byte.w(b0, b1, b2, b3, b4, b5, b6, b7) : U32}:
  e0 = or_f(b0)
  %e0 : {byte.w(_, Bool.or(b1, False{}), Bool.or(b2, False{}), Bool.or(b3, False{}),
    Bool.or(b4, False{}), Bool.or(b5, False{}), Bool.or(b6, False{}), Bool.or(b7, False{}))
    == byte.w(b0, b1, b2, b3, b4, b5, b6, b7) : U32}
  e1 = or_f(b1)
  %e1 : {byte.w(b0, _, Bool.or(b2, False{}), Bool.or(b3, False{}),
    Bool.or(b4, False{}), Bool.or(b5, False{}), Bool.or(b6, False{}), Bool.or(b7, False{}))
    == byte.w(b0, b1, b2, b3, b4, b5, b6, b7) : U32}
  e2 = or_f(b2)
  %e2 : {byte.w(b0, b1, _, Bool.or(b3, False{}),
    Bool.or(b4, False{}), Bool.or(b5, False{}), Bool.or(b6, False{}), Bool.or(b7, False{}))
    == byte.w(b0, b1, b2, b3, b4, b5, b6, b7) : U32}
  e3 = or_f(b3)
  %e3 : {byte.w(b0, b1, b2, _, Bool.or(b4, False{}), Bool.or(b5, False{}), Bool.or(b6, False{}), Bool.or(b7, False{}))
    == byte.w(b0, b1, b2, b3, b4, b5, b6, b7) : U32}
  e4 = or_f(b4)
  %e4 : {byte.w(b0, b1, b2, b3, _, Bool.or(b5, False{}), Bool.or(b6, False{}), Bool.or(b7, False{}))
    == byte.w(b0, b1, b2, b3, b4, b5, b6, b7) : U32}
  e5 = or_f(b5)
  %e5 : {byte.w(b0, b1, b2, b3, b4, _, Bool.or(b6, False{}), Bool.or(b7, False{}))
    == byte.w(b0, b1, b2, b3, b4, b5, b6, b7) : U32}
  e6 = or_f(b6)
  %e6 : {byte.w(b0, b1, b2, b3, b4, b5, _, Bool.or(b7, False{}))
    == byte.w(b0, b1, b2, b3, b4, b5, b6, b7) : U32}
  e7 = or_f(b7)
  %e7 : {byte.w(b0, b1, b2, b3, b4, b5, b6, _)
    == byte.w(b0, b1, b2, b3, b4, b5, b6, b7) : U32}
  {==}

# the type a Maybe names: Unit for None, Empty for Some
def none_ty(-T: Data, mm: Maybe<&2, T>) -> Type:
  match mm:
    case None{}:
      Unit
    case Some{_vv}:
      Empty

# None is never Some
def none_some(-T: Data, vv: T, ee: {None{} == Some{vv} : Maybe<&2, T>}) -> Empty:
  %ee : none_ty(T, _)
  Unit{}

# ---- the marker walk (IMG-JPG-1) ----

# the phases the walk may be in between two segments: seeking a marker, inside a scan, or stopped
def ph.ok(ph: Jpeg.Phase) -> Bool:
  match ph:
    case Jpeg.Seek{}:
      True{}
    case Jpeg.Ent{}:
      True{}
    case Jpeg.Stop{}:
      True{}
    case Jpeg.Mark{}:
      False{}
    case Jpeg.LenHi{_mark}:
      False{}
    case Jpeg.LenLo{_mark, _hi}:
      False{}
    case Jpeg.Pay{_mark, _left, _acc}:
      False{}
    case Jpeg.EntFF{}:
      False{}

# a walk state between two segments that has read no frame header: kind is still 0
def inv(st: Jpeg.St) -> Bool:
  match st:
    case Jpeg.St{ph, _fr, _sc, _tb, _en, _ri, kind, _bad}:
      Bool.and(ph.ok(ph), U32.is_eq(kind, 0))

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
        == Jpeg.decode.dispatch(mark, body, frame, scan, tabs, ent, ri, kind, bad) : Jpeg.St}, true_false(e_lt))
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
) -> {inv(Jpeg.decode.read.dht(xs, ok, sym, phase, cls, id, counts, syms, frame, scan, tabs, ent, ri, kind, bad))
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
) -> {inv(Jpeg.decode.read.dqt(xs, ok, phase, id, acc, frame, scan, tabs, ent, ri, kind, bad))
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
) -> {inv(Jpeg.decode.read.sos.ok(ss0, se63, ah0, sids, td, ta, ns, frame, tabs, ent, ri, kind, bad))
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
) -> {inv(Jpeg.decode.read.sos.cs(left, xs, sids, td, ta, ns, frame, tabs, ent, ri, kind, bad))
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
) -> {inv(Jpeg.decode.read.sos(xs, frame, tabs, ent, ri, kind, bad)) == U32.is_eq(kind, 0) : Bool}:
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
) -> {inv(Jpeg.decode.read.dri(xs, frame, scan, tabs, ent, kind, bad)) == U32.is_eq(kind, 0) : Bool}:
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
) -> {inv(Jpeg.decode.read.app0.den(xz, yz, frame, scan, tabs, ent, ri, kind, bad)) == U32.is_eq(kind, 0) : Bool}:
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
) -> {inv(Jpeg.decode.read.app0.id(jfif, xh, xl, yh, yl, frame, scan, tabs, ent, ri, kind, bad))
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
) -> {inv(Jpeg.decode.read.app0(xs, frame, scan, tabs, ent, ri, kind, bad)) == U32.is_eq(kind, 0) : Bool}:
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
    bad}), kind, 0, U32L.ueq(kind, 0, hk))

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
def ph.norm.eq(ph: Jpeg.Phase, h_ok: {ph.ok(ph) == True{} : Bool}) -> {ph == ph.norm(ph) : Jpeg.Phase}:
  match ph:
    case Jpeg.Seek{}:
      {==}
    case Jpeg.Ent{}:
      {==}
    case Jpeg.Stop{}:
      {==}
    case Jpeg.Mark{}:
      Empty.absurd({Jpeg.Mark{} == Jpeg.Stop{} : Jpeg.Phase}, U32L.false_true(h_ok))
    case Jpeg.LenHi{mark}:
      Empty.absurd({Jpeg.LenHi{mark} == Jpeg.Stop{} : Jpeg.Phase}, U32L.false_true(h_ok))
    case Jpeg.LenLo{mark, hi}:
      Empty.absurd({Jpeg.LenLo{mark, hi} == Jpeg.Stop{} : Jpeg.Phase}, U32L.false_true(h_ok))
    case Jpeg.Pay{mark, left, acc}:
      Empty.absurd({Jpeg.Pay{mark, left, acc} == Jpeg.Stop{} : Jpeg.Phase}, U32L.false_true(h_ok))
    case Jpeg.EntFF{}:
      Empty.absurd({Jpeg.EntFF{} == Jpeg.Stop{} : Jpeg.Phase}, U32L.false_true(h_ok))
