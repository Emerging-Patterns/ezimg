# every sample the JPEG decoder returns is packed and opaque
import Base
import ../../main.bend as Img
import ../../src/jpeg.bend as Jpeg
import ../../laws/DecodedSamplesPackArgb.bend as L1
import ../../laws/defs/PngSpecification.bend as D1

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

# U32.or with 0xFF000000 first has alpha 255, whatever the other operand:
# the 32 bits are taken apart four at a time, and Bool.or(True, b) is True.
def alpha.first(xx: U32) -> {U32.shrn(U32.or(4278190080, xx), 24n) == 255 : U32}:
  match xx:
    case U32{w0}:
      match w0:
        case WCon{_b0, WCon{_b1, WCon{_b2, WCon{_b3, w4}}}}:
          match w4:
            case WCon{_b4, WCon{_b5, WCon{_b6, WCon{_b7, w8}}}}:
              match w8:
                case WCon{_b8, WCon{_b9, WCon{_b10, WCon{_b11, w12}}}}:
                  match w12:
                    case WCon{_b12, WCon{_b13, WCon{_b14, WCon{_b15, w16}}}}:
                      match w16:
                        case WCon{_b16, WCon{_b17, WCon{_b18, WCon{_b19, w20}}}}:
                          match w20:
                            case WCon{_b20, WCon{_b21, WCon{_b22, WCon{_b23, w24}}}}:
                              match w24:
                                case WCon{_b24, WCon{_b25, WCon{_b26, WCon{_b27, w28}}}}:
                                  match w28:
                                    case WCon{_b28, WCon{_b29, WCon{_b30, WCon{_b31, w32}}}}:
                                      match w32:
                                        case WNil{}:
                                          {==}

def L1.jpeg_rgb_opaque(yy, cb, cr):
  alpha.first(Jpeg.rgb.bits(yy, cb, cr))

def L1.jpeg_gray_opaque(yy):
  alpha.first(Jpeg.gray.bits(yy))

def L1.jpeg_direct_opaque(rr, gg, bb):
  alpha.first(U32.or(U32.or(U32.shln(U32.and(255, rr), 16n), U32.shln(U32.and(255, gg), 8n)), U32.and(255, bb)))

# the samples of a decoded picture, or none
def pic.px(mm: Maybe<&2, Jpeg.Pic>) -> List<&2, U32>:
  match mm:
    case None{}:
      []
    case Some{Jpeg.Pic{_ww, _hh, px}}:
      px

# what jpeg_decode_packed says of samples px
def pk.Ty(px: List<&2, U32>) -> Type:
  &gray: Bool -> &coded: Bool -> &ys: List<&2, U32> -> &bs: List<&2, U32> -> &rs: List<&2, U32>
    -> {px == L1.jpeg.pack(gray, coded, ys, bs, rs) : List<&2, U32>}

# the code's gray packing is the law's
def grays.eq(+ys: List<&2, U32>) -> {Jpeg.decode.grays(ys) == L1.jpeg.grays(ys) : List<&2, U32>}:
  match ys:
    case Nil{}:
      {==}
    case +yv <> rest:
      Equal.cong(List<&2, U32>, List<&2, U32>, tl => {Jpeg.gray(yv) <> tl : List<&2, U32>}, Jpeg.decode.grays(rest),
        L1.jpeg.grays(rest), grays.eq(rest))

# the code's colour packing is the law's
def rgbs.eq(
  +ys: List<&2, U32>,
  +bs: List<&2, U32>,
  +rs: List<&2, U32>
) -> {Jpeg.decode.rgbs(ys, bs, rs) == L1.jpeg.rgbs(ys, bs, rs) : List<&2, U32>}:
  match ys bs rs:
    case Nil{} _bs _rs:
      {==}
    case _yv <> _yt Nil{} _rs:
      {==}
    case _yv <> _yt _bv <> _bt Nil{}:
      {==}
    case +yv <> yt +bv <> bt +rv <> rt:
      Equal.cong(List<&2, U32>, List<&2, U32>, tl => {Jpeg.rgb(yv, bv, rv) <> tl : List<&2, U32>},
        Jpeg.decode.rgbs(yt, bt, rt), L1.jpeg.rgbs(yt, bt, rt), rgbs.eq(yt, bt, rt))

# the code's packing of samples coded as R, G and B is the law's
def directs.eq(
  +rs: List<&2, U32>,
  +gs: List<&2, U32>,
  +bs: List<&2, U32>
) -> {Jpeg.decode.directs(rs, gs, bs) == L1.jpeg.directs(rs, gs, bs) : List<&2, U32>}:
  match rs gs bs:
    case Nil{} _gs _bs:
      {==}
    case _rv <> _rt Nil{} _bs:
      {==}
    case _rv <> _rt _gv <> _gt Nil{}:
      {==}
    case +rv <> rt +gv <> gt +bv <> bt:
      Equal.cong(List<&2, U32>, List<&2, U32>, tl => {Jpeg.direct(rv, gv, bv) <> tl : List<&2, U32>},
        Jpeg.decode.directs(rt, gt, bt), L1.jpeg.directs(rt, gt, bt), directs.eq(rt, gt, bt))

# no picture has no samples
def none.pk() -> pk.Ty([]):
  (True{}, (False{}, ([], ([], ([], {==})))))

# three components' samples, coded as R, G and B or as Y, Cb and Cr
def pack.pk(
  rgb: Bool,
  +nn: Nat,
  +ww: U32,
  +hh: U32,
  ups: Jpeg.Ups,
  yy: Array<U32>,
  cb: Array<U32>,
  cr: Array<U32>
) -> pk.Ty(Jpeg.decode.done.pack(rgb, nn, ww, hh, ups, yy, cb, cr)):
  match rgb:
    case True{}:
      match ups:
        case Jpeg.Ups{+m0, +m1, +m2}:
          +ey = Jpeg.decode.up.out(m0, nn, ww, hh, yy)
          +eb = Jpeg.decode.up.out(m1, nn, ww, hh, cb)
          +er = Jpeg.decode.up.out(m2, nn, ww, hh, cr)
          (False{}, (True{}, (ey, (eb, (er, directs.eq(ey, eb, er))))))
    case False{}:
      match ups:
        case Jpeg.Ups{+m0, +m1, +m2}:
          +ey = Jpeg.decode.up.out(m0, nn, ww, hh, yy)
          +eb = Jpeg.decode.up.out(m1, nn, ww, hh, cb)
          +er = Jpeg.decode.up.out(m2, nn, ww, hh, cr)
          (False{}, (False{}, (ey, (eb, (er, rgbs.eq(ey, eb, er))))))

# gray or colour, by the component count
def nf3.pk(
  three: Bool,
  rgb: Bool,
  +ww: U32,
  +hh: U32,
  ups: Jpeg.Ups,
  yy: Array<U32>,
  cb: Array<U32>,
  cr: Array<U32>
) -> pk.Ty(pic.px(Jpeg.decode.done.nf3(three, rgb, ww, hh, ups, yy, cb, cr))):
  match three:
    case True{}:
      pack.pk(rgb, U32.to_nat((ww * hh : U32)), ww, hh, ups, yy, cb, cr)
    case False{}:
      none.pk()

# one component is gray
def nf1.pk(
  one: Bool,
  +nf: U32,
  rgb: Bool,
  +ww: U32,
  +hh: U32,
  ups: Jpeg.Ups,
  yy: Array<U32>,
  cb: Array<U32>,
  cr: Array<U32>
) -> pk.Ty(pic.px(Jpeg.decode.done.nf1(one, nf, rgb, ww, hh, ups, yy, cb, cr))):
  match one:
    case True{}:
      match ups:
        case Jpeg.Ups{+m0, _m1, _m2}:
          +ey = Jpeg.decode.up.out(m0, U32.to_nat((ww * hh : U32)), ww, hh, yy)
          (True{}, (False{}, (ey, ([], ([], grays.eq(ey))))))
    case False{}:
      nf3.pk(U32.is_eq(nf, 3), rgb, ww, hh, ups, yy, cb, cr)

# a failed scan has no samples, and a finished one is packed by its component count
def dok.pk(
  bad: Bool,
  frame: Jpeg.Frame,
  rgb: Bool,
  yy: Array<U32>,
  cb: Array<U32>,
  cr: Array<U32>
) -> pk.Ty(pic.px(Jpeg.decode.done.ok(bad, frame, rgb, yy, cb, cr))):
  match bad:
    case True{}:
      none.pk()
    case False{}:
      match frame:
        case Jpeg.Frame{+ww, +hh, +nf, _ids, +hs, +vs, _tq, +hmax, +vmax}:
          nf1.pk(U32.is_eq(nf, 1), nf, rgb, ww, hh, Jpeg.decode.ups(hs, vs, hmax, vmax, ww), yy, cb, cr)

# the blocks' walk ends in decode.done, whose samples are packed
def blocks.pk(
  left: Nat,
  live: Bool,
  blk: Jpeg.Blk,
  +ctrl: Jpeg.Ctrl,
  +preds: Jpeg.Preds,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ri: U32,
  +rgb: Bool,
  yy: Array<U32>,
  cb: Array<U32>,
  cr: Array<U32>,
  +ok: U32
) -> pk.Ty(pic.px(Jpeg.decode.blocks(left, live, blk, ctrl, preds, frame, scan, tabs, ri, rgb, yy, cb, cr, ok))):
  match left:
    case 0n:
      match live:
        case _live:
          match blk:
            case Jpeg.Blk{+samples, _bits, _pred, +bok}:
              +gg = Jpeg.decode.geom(ctrl, frame, scan)
              +cc = Jpeg.decode.ctrl.comp(ctrl)
              dok.pk(U32.is_eq((ok * bok : U32), 0), frame, rgb, Jpeg.decode.paint.use(gg, U32.is_eq(cc, 0), samples,
                yy), Jpeg.decode.paint.use(gg, U32.is_eq(cc, 1), samples, cb), Jpeg.decode.paint.use(gg, U32.is_eq(cc,
                2), samples, cr))
    case 1n+pp:
      match live:
        case False{}:
          dok.pk(U32.is_eq(0, 0), frame, rgb, yy, cb, cr)
        case True{}:
          match blk:
            case Jpeg.Blk{+samples, +bits, +pred, +bok}:
              match ctrl:
                case Jpeg.Ctrl{+comp, +bi, +mx, +my, +mcu, +rst}:
                  +ct = {Jpeg.Ctrl{comp, bi, mx, my, mcu, rst} : Jpeg.Ctrl}
                  +av = Jpeg.decode.adv(ct, frame, scan, ri)
                  +gg = Jpeg.decode.geom(ct, frame, scan)
                  +nx = Jpeg.decode.block.next(bits, preds, pred, ct, frame, scan, tabs, ri)
                  blocks.pk(pp, Jpeg.decode.blk.live(nx), nx, Jpeg.decode.adv.ctrl(av),
                    Jpeg.decode.preds.next(Jpeg.decode.adv.duef(av), preds, comp, pred), frame, scan, tabs, ri, rgb,
                    Jpeg.decode.paint.use(gg, U32.is_eq(comp, 0), samples, yy), Jpeg.decode.paint.use(gg,
                    U32.is_eq(comp, 1), samples, cb), Jpeg.decode.paint.use(gg, U32.is_eq(comp, 2), samples, cr),
                    (ok * bok : U32))

# the scan starts the blocks' walk, or has no blocks
def start.pk(
  nn: Nat,
  bits: Jpeg.Bits,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ri: U32,
  +rgb: Bool,
  yy: Array<U32>,
  cb: Array<U32>,
  cr: Array<U32>
) -> pk.Ty(pic.px(Jpeg.decode.start(nn, bits, frame, scan, tabs, ri, rgb, yy, cb, cr))):
  match nn:
    case 0n:
      none.pk()
    case 1n+pp:
      +b0 = Jpeg.decode.block.of(bits, 0, Jpeg.decode.pred.zero(), frame, scan, tabs)
      blocks.pk(pp, Jpeg.decode.blk.live(b0), b0, Jpeg.Ctrl{0, 0, 0, 0, 0, 0}, Jpeg.decode.pred.zero(), frame, scan,
        tabs, ri, rgb, yy, cb, cr, 1)

# a scan the decoder does not run has no samples; one it runs starts
def runf.pk(
  fit: Bool,
  +nb: U32,
  +ww: U32,
  +hh: U32,
  frame: Jpeg.Frame,
  scan: Jpeg.Scan,
  tabs: Jpeg.Tabs,
  ent: List<&2, U32>,
  +ri: U32,
  +rgb: Bool
) -> pk.Ty(pic.px(Jpeg.decode.run.fit(fit, nb, ww, hh, frame, scan, tabs, ent, ri, rgb))):
  match fit:
    case False{}:
      none.pk()
    case True{}:
      start.pk(U32.to_nat(nb), Jpeg.Bits{0, 1, 0, ent}, frame, scan, tabs, ri, rgb, Jpeg.decode.plane((ww * hh :
        U32)), Jpeg.decode.plane((ww * hh : U32)), Jpeg.decode.plane((ww * hh : U32)))

# an empty frame has no samples; any other starts the scan
def runn.pk(
  empty: Bool,
  +ww: U32,
  +hh: U32,
  frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +rgb: Bool
) -> pk.Ty(pic.px(Jpeg.decode.run.n(empty, ww, hh, frame, scan, tabs, ent, ri, rgb))):
  match empty:
    case True{}:
      none.pk()
    case False{}:
      match frame:
        case Jpeg.Frame{+w, +h, +nf, +ids, +hs, +vs, +tq, +hmax, +vmax}:
          +nb = Jpeg.decode.nblocks(ww, hh, hs, vs, hmax, vmax)
          runf.pk(Jpeg.decode.fits(ww, hh, nb, ent, nf, ids, scan), nb, ww, hh, Jpeg.Frame{w, h, nf, ids, hs, vs, tq,
            hmax, vmax}, scan, tabs, ent, ri, rgb)

# a run's samples are packed
def run.pk(
  frame: Jpeg.Frame,
  scan: Jpeg.Scan,
  tabs: Jpeg.Tabs,
  ent: List<&2, U32>,
  +ri: U32,
  +rgb: Bool
) -> pk.Ty(pic.px(Jpeg.decode.run(frame, scan, tabs, ent, ri, rgb))):
  match frame:
    case Jpeg.Frame{+ww, +hh, +nf, +ids, +hs, +vs, +tq, +hmax, +vmax}:
      runn.pk(Bool.or(U32.is_eq(ww, 0), U32.is_eq(hh, 0)), ww, hh, Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax,
        vmax}, scan, tabs, ent, ri, rgb)

# a walk that did not reach a baseline frame cleanly has no samples; one that did runs
def fok.pk(
  ok1: Bool,
  ok2: Bool,
  frame: Jpeg.Frame,
  scan: Jpeg.Scan,
  tabs: Jpeg.Tabs,
  ent: List<&2, U32>,
  +ri: U32,
  +rgb: Bool
) -> pk.Ty(pic.px(Jpeg.decode.finish.ok(ok1, ok2, frame, scan, tabs, ent, ri, rgb))):
  match ok1 ok2:
    case False{} _ok2:
      none.pk()
    case True{} False{}:
      none.pk()
    case True{} True{}:
      run.pk(frame, scan, tabs, List.reverse(&2, U32, ent), ri, rgb)

# a walk that did not end where a scan may end has no samples
def fph.pk(
  done: Bool,
  +frame: Jpeg.Frame,
  scan: Jpeg.Scan,
  tabs: Jpeg.Tabs,
  ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32,
  +facts: U32
) -> pk.Ty(pic.px(Jpeg.decode.finish.ph(done, frame, scan, tabs, ent, ri, kind, bad, facts))):
  match done:
    case True{}:
      fok.pk(Bool.and(U32.is_eq(kind, 1), Jpeg.decode.facts.soi(facts)), U32.is_eq(bad, 0), frame, scan, tabs, ent,
        ri, Jpeg.decode.rgb.of(facts, frame))
    case False{}:
      none.pk()

# the passes end in decode.done, whose samples are packed
def pdone.pk(
  got: U32 & Array<U32> & Array<U32> & Array<U32>,
  frame: Jpeg.Frame,
  rgb: Bool
) -> pk.Ty(pic.px(Jpeg.decode.passes.done(got, frame, rgb))):
  (ok, yy, cb, cr) = got
  dok.pk(U32.is_eq(ok, 0), frame, rgb, yy, cb, cr)

# scans the passes refuse have no samples; others are painted and packed
def pfit.pk(
  fit: Bool,
  +frame: Jpeg.Frame,
  passes: List<&2, Jpeg.Pass>,
  +ww: U32,
  +hh: U32,
  rgb: Bool
) -> pk.Ty(pic.px(Jpeg.decode.passes.fit(fit, frame, passes, ww, hh, rgb))):
  match fit:
    case False{}:
      none.pk()
    case True{}:
      pdone.pk(Jpeg.decode.passes.go(passes, frame, (1, Jpeg.decode.plane((ww * hh : U32)),
        Jpeg.decode.plane((ww * hh : U32)), Jpeg.decode.plane((ww * hh : U32)))), frame, rgb)

# the picture of a frame's passes is packed
def passes.pk(
  frame: Jpeg.Frame,
  +passes: List<&2, Jpeg.Pass>,
  rgb: Bool
) -> pk.Ty(pic.px(Jpeg.decode.passes(frame, passes, rgb))):
  match frame:
    case Jpeg.Frame{+w, +h, +nf, +ids, +hs, +vs, +tq, +hmax, +vmax}:
      +fr = {Jpeg.Frame{w, h, nf, ids, hs, vs, tq, hmax, vmax} : Jpeg.Frame}
      pfit.pk(Bool.and(Bool.not(Bool.or(U32.is_eq(w, 0), U32.is_eq(h, 0))), Bool.and(Jpeg.decode.area.ok(w, h),
        Jpeg.decode.passes.ok(passes, fr, 0, True{}))), fr, passes, w, h, rgb)

def multigo.pk(
  ok: Bool,
  passes: List<&2, Jpeg.Pass>,
  frame: Jpeg.Frame,
  rgb: Bool
) -> pk.Ty(pic.px(Jpeg.decode.multi.go(ok, passes, frame, rgb))):
  match ok:
    case False{}:
      none.pk()
    case True{}:
      passes.pk(frame, List.reverse(&2, Jpeg.Pass, passes), rgb)

# the picture of a file of several scans is packed
def multi.pk(
  chain: Jpeg.Chain,
  +frame: Jpeg.Frame,
  +facts: U32
) -> pk.Ty(pic.px(Jpeg.decode.multi(chain, frame, facts))):
  match chain:
    case Jpeg.Chain{+ok, +passes}:
      multigo.pk(Bool.and(ok, Jpeg.decode.facts.soi(facts)), passes, frame, Jpeg.decode.rgb.of(facts, frame))

# whatever the phase a walk ends in, the picture is packed
def fat.pk(
  phase: Jpeg.Phase,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32,
  +facts: U32
) -> pk.Ty(pic.px(Jpeg.decode.finish.at(phase, frame, scan, tabs, ent, ri, kind, bad, facts))):
  match phase:
    case Jpeg.Rest{+mark, +acc}:
      +st = {Jpeg.St{Jpeg.Rest{mark, acc}, frame, scan, tabs, ent, ri, kind, bad} : Jpeg.St}
      multi.pk(Jpeg.decode.chain(1n+1n+List.length(&2, U32, acc), Jpeg.decode.st.good(st), st, []), frame,
        facts)
    case Jpeg.Stop{}:
      fph.pk(True{}, frame, scan, tabs, ent, ri, kind, bad, facts)
    case Jpeg.Ent{}:
      fph.pk(True{}, frame, scan, tabs, ent, ri, kind, bad, facts)
    case Jpeg.EntFF{}:
      fph.pk(True{}, frame, scan, tabs, ent, ri, kind, bad, facts)
    case Jpeg.Seek{}:
      fph.pk(False{}, frame, scan, tabs, ent, ri, kind, bad, facts)
    case Jpeg.Mark{}:
      fph.pk(False{}, frame, scan, tabs, ent, ri, kind, bad, facts)
    case Jpeg.LenHi{_m}:
      fph.pk(False{}, frame, scan, tabs, ent, ri, kind, bad, facts)
    case Jpeg.LenLo{_m, _h}:
      fph.pk(False{}, frame, scan, tabs, ent, ri, kind, bad, facts)
    case Jpeg.Pay{_m, _l, _a}:
      fph.pk(False{}, frame, scan, tabs, ent, ri, kind, bad, facts)

# whatever the walk's state and the facts, the picture decode finishes with is packed
def finish.pk(st: Jpeg.St, +facts: U32) -> pk.Ty(pic.px(Jpeg.decode.finish(st, facts))):
  match st:
    case Jpeg.St{+phase, +frame, +scan, +tabs, +ent, +ri, +kind, +bad}:
      fat.pk(phase, frame, scan, tabs, ent, ri, kind, bad, facts)

# the samples of a raster, or none
def raster.px(mr: Maybe<&2, Img.Raster>) -> List<&2, U32>:
  match mr:
    case None{}:
      []
    case Some{rr}:
      Img.pixels(rr)

# a raster decode_jpeg returns has the samples of the picture decode returns
def out.px(
  mm: Maybe<&2, Jpeg.Pic>,
  +img: Img.Raster,
  h_dec: {Img.decode_jpeg.out(mm) == Some{img} : Maybe<&2, Img.Raster>}
) -> {Img.pixels(img) == pic.px(mm) : List<&2, U32>}:
  match mm:
    case None{}:
      Empty.absurd({Img.pixels(img) == [] : List<&2, U32>}, none_some(Img.Raster, img, h_dec))
    case Some{Jpeg.Pic{ww, hh, px}}:
      Equal.sym(List<&2, U32>, px, Img.pixels(img), Equal.cong(Maybe<&2, Img.Raster>, List<&2, U32>,
        mr => raster.px(mr), Some{Img.Raster{ww, hh, px}}, Some{img}, h_dec))

# samples equal to packed samples are packed
def pk.move(
  +aa: List<&2, U32>,
  +bb: List<&2, U32>,
  eab: {aa == bb : List<&2, U32>},
  pr: pk.Ty(bb)
) -> pk.Ty(aa):
  (gray, (coded, (ys, (bs, (rs, eb))))) = pr
  (gray, (coded, (ys, (bs, (rs, Equal.trans(List<&2, U32>, aa, bb, L1.jpeg.pack(gray, coded, ys, bs, rs), eab,
    eb))))))

def L1.jpeg_decode_packed(bytes, img, h_dec):
  pk.move(Img.pixels(img), pic.px(Jpeg.decode(bytes)), out.px(Jpeg.decode(bytes), img, h_dec),
    finish.pk(Jpeg.decode.walk(bytes, Jpeg.decode.st0()), Jpeg.decode.facts(bytes)))

# a sample with alpha 255 passes the alpha test
def op.one(+pp: U32, ea: {U32.shrn(pp, 24n) == 255 : U32}) -> {U32.is_eq(U32.shrn(pp, 24n), 255) == True{} : Bool}:
  Equal.cong(U32, Bool, xx => U32.is_eq(xx, 255), U32.shrn(pp, 24n), 255, ea)

# one opaque sample in front leaves the answer as it was
def op.step(
  +pp: U32,
  +rest: List<&2, U32>,
  +ok: Bool,
  ea: {U32.shrn(pp, 24n) == 255 : U32},
  ih: {D1.all.opaque(rest, ok) == ok : Bool}
) -> {D1.all.opaque(pp <> rest, ok) == ok : Bool}:
  Equal.trans(Bool, D1.all.opaque(rest, Bool.and(U32.is_eq(U32.shrn(pp, 24n), 255), ok)),
    D1.all.opaque(rest, ok), ok,
    Equal.cong(Bool, Bool, bb => D1.all.opaque(rest, Bool.and(bb, ok)), U32.is_eq(U32.shrn(pp, 24n), 255), True{},
      op.one(pp, ea)), ih)

# gray samples are all opaque
def op.grays(+ys: List<&2, U32>, +ok: Bool) -> {D1.all.opaque(L1.jpeg.grays(ys), ok) == ok : Bool}:
  match ys:
    case Nil{}:
      {==}
    case +yv <> +rest:
      op.step(Jpeg.gray(yv), L1.jpeg.grays(rest), ok, L1.jpeg_gray_opaque(yv), op.grays(rest, ok))

# colour samples are all opaque
def op.rgbs(
  +ys: List<&2, U32>,
  +bs: List<&2, U32>,
  +rs: List<&2, U32>,
  +ok: Bool
) -> {D1.all.opaque(L1.jpeg.rgbs(ys, bs, rs), ok) == ok : Bool}:
  match ys bs rs:
    case Nil{} _bs _rs:
      {==}
    case _yv <> _yt Nil{} _rs:
      {==}
    case _yv <> _yt _bv <> _bt Nil{}:
      {==}
    case +yv <> +yt +bv <> +bt +rv <> +rt:
      op.step(Jpeg.rgb(yv, bv, rv), L1.jpeg.rgbs(yt, bt, rt), ok, L1.jpeg_rgb_opaque(yv, bv, rv),
        op.rgbs(yt, bt, rt, ok))

# samples coded as R, G and B are all opaque
def op.directs(
  +rs: List<&2, U32>,
  +gs: List<&2, U32>,
  +bs: List<&2, U32>,
  +ok: Bool
) -> {D1.all.opaque(L1.jpeg.directs(rs, gs, bs), ok) == ok : Bool}:
  match rs gs bs:
    case Nil{} _gs _bs:
      {==}
    case _rv <> _rt Nil{} _bs:
      {==}
    case _rv <> _rt _gv <> _gt Nil{}:
      {==}
    case +rv <> +rt +gv <> +gt +bv <> +bt:
      op.step(Jpeg.direct(rv, gv, bv), L1.jpeg.directs(rt, gt, bt), ok, L1.jpeg_direct_opaque(rv, gv, bv),
        op.directs(rt, gt, bt, ok))

# packed samples are all opaque
def op.pack(
  gray: Bool,
  coded: Bool,
  +ys: List<&2, U32>,
  +bs: List<&2, U32>,
  +rs: List<&2, U32>
) -> {D1.all.opaque(L1.jpeg.pack(gray, coded, ys, bs, rs), True{}) == True{} : Bool}:
  match gray:
    case True{}:
      op.grays(ys, True{})
    case False{}:
      match coded:
        case True{}:
          op.directs(ys, bs, rs, True{})
        case False{}:
          op.rgbs(ys, bs, rs, True{})

# samples that are packed are all opaque
def op.of(+px: List<&2, U32>, pr: pk.Ty(px)) -> {D1.all.opaque(px, True{}) == True{} : Bool}:
  (gray, (coded, (ys, (bs, (rs, ep))))) = pr
  Equal.trans(Bool, D1.all.opaque(px, True{}), D1.all.opaque(L1.jpeg.pack(gray, coded, ys, bs, rs), True{}), True{},
    Equal.cong(List<&2, U32>, Bool, ll => D1.all.opaque(ll, True{}), px, L1.jpeg.pack(gray, coded, ys, bs, rs), ep),
    op.pack(gray, coded, ys, bs, rs))

def L1.jpeg_decode_opaque(bytes, img, h_dec):
  op.of(Img.pixels(img), L1.jpeg_decode_packed(bytes, img, h_dec))
