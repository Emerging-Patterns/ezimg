# proofs of laws/JpegRoundTripKeepsSize.bend
import Base
import ../main.bend as Img
import ../src/jpeg.bend as Jpeg
import ../src/jpeg_enc.bend as Jenc
import ../laws/DecodedSamplesPackArgb.bend as L1
import ../laws/JpegRoundTripKeepsSize.bend as Laws
import ../laws/defs/PngSpecification.bend as D1
import ../laws/defs/PointInside.bend as D2
import ./lemmas/BasicFacts.bend as M1
import ./lemmas/JpegEncoderScan.bend as M2
import ./lemmas/JpegHuffmanCoding.bend as M3
import ./lemmas/JpegSamplesPacked.bend as M4
import ./lemmas/RowMajorIndex.bend as M5
import ./lemmas/SubtractionAndHuffmanWalk.bend as M6
import ./lemmas/WordAddition.bend as M7
import ./lemmas/JpegEncoderGuard.bend as M8

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

# ---- laws/JpegRoundTripKeepsSize.bend: stuffing, the header walk, the entropy walk, the frame size ----

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
            Jenc.encode.acsyms()), 1024, 1024, 1024, Jenc.encode.put0()), 0, 0, U32.div((ww + 7 : U32), 8), ww,
            hh,
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
      eb = Equal.sym(U32, bb, 255, M1.ueq(bb, 255, ee))
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
      Empty.absurd({False{} == True{} : Bool}, M1.false_true(Equal.trans(Bool, False{}, Laws.jpg.stuffed(rest,
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
            Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, 255 <> en, ri, kind, bad} : Jpeg.St}, M1.false_true(hh))
    case +bb <> +rest:
      match ff:
        case False{}:
          ent.one(U32.is_eq(bb, 255), bb, rest, frame, scan, tabs, en, ri, kind, bad, {==}, ent.go(rest,
            U32.is_eq(bb, 255), frame, scan, tabs, ent.hold(U32.is_eq(bb, 255), bb, en), ri, kind, bad, hh))
        case True{}:
          +ez = {ent.zero(U32.is_eq(bb, 0), rest, hh) : {U32.is_eq(bb, 0) == True{} : Bool}}
          eb = Equal.sym(U32, bb, 0, M1.ueq(bb, 0, ez))
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
    Equal.cong(Bool, Bool, bb => Bool.and(bb, U32.is_eq(hh, hh)), U32.is_eq(ww, ww), True{}, M1.u32_eq_refl(ww)),
    M1.u32_eq_refl(hh))

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

# ---- stuffing and unstuffing (laws/JpegRoundTripKeepsSize.bend) ----

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
) -> {Jpeg.decode.nbits(8n, True{}, M4.byte.w(c0, c1, c2, c3, c4, c5, c6, c7) <> rest, False{}, False{}, h0, 0, 0, ok,
  0) == (Jpeg.Bits{0, ok, 0, rest}, M4.byte.w(Bool.or(c0, False{}), Bool.or(c1, False{}), Bool.or(c2, False{}),
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
  +ee: {U32.is_eq(M4.byte.w(c0, c1, c2, c3, c4, c5, c6, c7), 255) == zz : Bool}
) -> {Jpeg.decode.read.n(8, Jpeg.Bits{0, ok, 0, Jenc.encode.stuff.put(zz, M4.byte.w(c0, c1, c2, c3, c4, c5, c6, c7),
  rest)}) == (Jpeg.Bits{0, ok, 0, rest}, M4.byte.w(c0, c1, c2, c3, c4, c5, c6, c7)) : Jpeg.Bits & U32}:
  match zz:
    case False{}:
      +bw = M4.byte.w(c0, c1, c2, c3, c4, c5, c6, c7)
      +h0 = U32.is_eq(bw, 0)
      Equal.trans(Jpeg.Bits & U32, Jpeg.decode.nbits(8n, True{}, bw <> rest, False{}, U32.is_eq(bw, 255), h0, 0, 0,
        ok, 0),
        Jpeg.decode.nbits(8n, True{}, bw <> rest, False{}, False{}, h0, 0, 0, ok, 0), (Jpeg.Bits{0, ok, 0, rest}, bw),
        Equal.cong(Bool, Jpeg.Bits & U32, hb => Jpeg.decode.nbits(8n, True{}, bw <> rest, False{}, hb, h0, 0, 0, ok, 0),
        U32.is_eq(bw, 255), False{}, ee), Equal.trans(Jpeg.Bits & U32, Jpeg.decode.nbits(8n, True{}, bw <> rest,
          False{},
        False{}, h0, 0, 0, ok, 0), (Jpeg.Bits{0, ok, 0, rest}, M4.byte.w(Bool.or(c0, False{}), Bool.or(c1, False{}),
        Bool.or(c2, False{}), Bool.or(c3, False{}), Bool.or(c4, False{}), Bool.or(c5, False{}), Bool.or(c6, False{}),
        Bool.or(c7, False{}))), (Jpeg.Bits{0, ok, 0, rest}, bw), rd.plain(h0, c0, c1, c2, c3, c4, c5, c6, c7, rest, ok),
        Equal.cong(U32, Jpeg.Bits & U32, vv => {(Jpeg.Bits{0, ok, 0, rest}, vv) : Jpeg.Bits & U32},
        M4.byte.w(Bool.or(c0, False{}), Bool.or(c1, False{}), Bool.or(c2, False{}), Bool.or(c3, False{}),
        Bool.or(c4, False{}), Bool.or(c5, False{}), Bool.or(c6, False{}), Bool.or(c7, False{})), bw,
        M4.or_byte(c0, c1, c2, c3, c4, c5, c6, c7))))
    case True{}:
      +bw = M4.byte.w(c0, c1, c2, c3, c4, c5, c6, c7)
      eb = Equal.sym(U32, bw, 255, M1.ueq(bw, 255, ee))
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
          +bw = M4.byte.w(c0, c1, c2, c3, c4, c5, c6, c7)
          +st = stf(Laws.jpg.bytes(tl), rest)
          Equal.trans(List<&2, U32>, Laws.jpg.read8(1n+List.length(&2, Laws.JByte, tl), Jpeg.decode.read.n(8,
            Jpeg.Bits{0, ok, 0, Jenc.encode.stuff.put(U32.is_eq(bw, 255), bw, st)})), Laws.jpg.read8(1n+List.length(&2,
            Laws.JByte, tl), (Jpeg.Bits{0, ok, 0, st}, bw)), bw <> Laws.jpg.bytes(tl), Equal.cong(Jpeg.Bits & U32,
            List<&2, U32>, gg => Laws.jpg.read8(1n+List.length(&2, Laws.JByte, tl), gg), Jpeg.decode.read.n(8,
            Jpeg.Bits{0, ok, 0, Jenc.encode.stuff.put(U32.is_eq(bw, 255), bw, st)}), (Jpeg.Bits{0, ok, 0, st}, bw),
            rd.z(U32.is_eq(bw, 255), c0, c1, c2, c3, c4, c5, c6, c7, st, ok, {==})), Equal.cong(List<&2, U32>,
            List<&2, U32>, ll => {bw <> ll : List<&2, U32>}, Laws.jpg.read8(List.length(&2, Laws.JByte, tl),
            Jpeg.decode.read.n(8, Jpeg.Bits{0, ok, 0, st})), Laws.jpg.bytes(tl), rd.list(tl, ok, rest)))

# or with zeros on the left is the word
def or_zero_l(nn: Nat, ww: Word(nn)) -> {Word.or(nn, Word.zero(nn), ww) == ww : Word(nn)}:
  match nn:
    case 0n:
      match ww:
        case WNil{}:
          {==}
    case 1n+pp:
      match ww:
        case WCon{bb, tt}:
          Equal.cong(Word(pp), Word.Con<pp>, xx => WCon{bb, xx}, Word.or(pp, Word.zero(pp), tt), tt, or_zero_l(pp, tt))

# the reader's step, by the bit
def or_u_shl.b(
  bb: Bool,
  +sp: Word(31n)
) -> {U32{WCon{Bool.or(bb, False{}), Word.or(31n, Word.zero(31n), sp)}} == U32{WCon{bb, sp}} : U32}:
  match bb:
    case True{}:
      Equal.cong(Word(31n), U32, zz => U32{WCon{True{}, zz}}, Word.or(31n, Word.zero(31n), sp), sp, or_zero_l(31n, sp))
    case False{}:
      Equal.cong(Word(31n), U32, zz => U32{WCon{False{}, zz}}, Word.or(31n, Word.zero(31n), sp), sp, or_zero_l(31n, sp))

# the reader's step: the bit or-ed onto the shifted value
def or_u_shl(xx: U32, bb: Bool) -> {U32.or(Laws.jpg.ubit(bb), U32.shl(xx)) == M6.vstep(xx, bb) : U32}:
  match xx:
    case U32{ww}:
      match ww:
        case WCon{w0, wt}:
          or_u_shl.b(bb, Word.shl.put(31n, w0, wt))

# a code of at most 16 bits, written with its length and value, is its bits fed to the writer
def bits_code(
  +cc: List<&2, Bool>,
  pp: Jenc.Put,
  hh: {Nat.is_le(List.length(&2, Bool, cc), 16n) == True{} : Bool}
) -> {Jenc.encode.bits(pp, U32.from_nat(List.length(&2, Bool, cc)), M2.vfold(cc, 0)) == Laws.jpg.feed(cc,
    pp) : Jenc.Put}:
  match cc:
    case Nil{}:
      M3.bits_go(0n, pp, M2.vfold([], 0))
    case +h0 <> t0:
      match t0:
        case Nil{}:
          M3.bits_go(1n, pp, M2.vfold(h0 <> [], 0))
        case +h1 <> t1:
          match t1:
            case Nil{}:
              M3.bits_go(2n, pp, M2.vfold(h0 <> h1 <> [], 0))
            case +h2 <> t2:
              match t2:
                case Nil{}:
                  M3.bits_go(3n, pp, M2.vfold(h0 <> h1 <> h2 <> [], 0))
                case +h3 <> t3:
                  match t3:
                    case Nil{}:
                      M3.bits_go(4n, pp, M2.vfold(h0 <> h1 <> h2 <> h3 <> [], 0))
                    case +h4 <> t4:
                      match t4:
                        case Nil{}:
                          M3.bits_go(5n, pp, M2.vfold(h0 <> h1 <> h2 <> h3 <> h4 <> [], 0))
                        case +h5 <> t5:
                          match t5:
                            case Nil{}:
                              M3.bits_go(6n, pp, M2.vfold(h0 <> h1 <> h2 <> h3 <> h4 <> h5 <> [], 0))
                            case +h6 <> t6:
                              match t6:
                                case Nil{}:
                                  M3.bits_go(7n, pp, M2.vfold(h0 <> h1 <> h2 <> h3 <> h4 <> h5 <> h6 <> [], 0))
                                case +h7 <> t7:
                                  match t7:
                                    case Nil{}:
                                      M3.bits_go(8n, pp, M2.vfold(h0 <> h1 <> h2 <> h3 <> h4 <> h5 <> h6 <> h7 <> [],
                                          0))
                                    case +h8 <> t8:
                                      match t8:
                                        case Nil{}:
                                          M3.bits_go(9n, pp,
                                            M2.vfold(h0 <> h1 <> h2 <> h3 <> h4 <> h5 <> h6 <> h7 <> h8 <> [], 0))
                                        case +h9 <> t9:
                                          match t9:
                                            case Nil{}:
                                              M3.bits_go(10n, pp,
                                                M2.vfold(h0 <> h1 <> h2 <> h3 <> h4 <> h5 <> h6 <> h7 <> h8 <> h9 <> [],
                                                0))
                                            case +h10 <> t10:
                                              match t10:
                                                case Nil{}:
                                                  M3.bits_go(11n, pp,
                                                    M2.vfold(h0 <> h1 <> h2 <> h3 <> h4 <> h5 <> h6 <> h7 <> h8 <> h9 <>
                                                    h10 <> [], 0))
                                                case +h11 <> t11:
                                                  match t11:
                                                    case Nil{}:
                                                      M3.bits_go(12n, pp,
                                                        M2.vfold(h0 <> h1 <> h2 <> h3 <> h4 <> h5 <> h6 <> h7 <> h8 <>
                                                          h9
                                                        <> h10 <> h11 <> [], 0))
                                                    case +h12 <> t12:
                                                      match t12:
                                                        case Nil{}:
                                                          M3.bits_go(13n, pp,
                                                            M2.vfold(h0 <> h1 <> h2 <> h3 <> h4 <> h5 <> h6 <> h7 <>
                                                              h8 <>
                                                            h9 <> h10 <> h11 <> h12 <> [], 0))
                                                        case +h13 <> t13:
                                                          match t13:
                                                            case Nil{}:
                                                              M3.bits_go(14n, pp,
                                                                M2.vfold(h0 <> h1 <> h2 <> h3 <> h4 <> h5 <> h6 <> h7 <>
                                                                h8 <> h9 <> h10 <> h11 <> h12 <> h13 <> [], 0))
                                                            case +h14 <> t14:
                                                              match t14:
                                                                case Nil{}:
                                                                  M3.bits_go(15n, pp,
                                                                    M2.vfold(h0 <> h1 <> h2 <> h3 <> h4 <> h5 <> h6 <>
                                                                      h7
                                                                    <> h8 <> h9 <> h10 <> h11 <> h12 <> h13 <> h14 <>
                                                                    [], 0))
                                                                case +h15 <> t15:
                                                                  match t15:
                                                                    case Nil{}:
                                                                      M3.bits_go(16n, pp,
                                                                        M2.vfold(h0 <> h1 <> h2 <> h3 <> h4 <> h5 <>
                                                                          h6 <>
                                                                        h7 <> h8 <> h9 <> h10 <> h11 <> h12 <> h13 <>
                                                                        h14 <> h15 <> [], 0))
                                                                    case _h16 <> _t16:
                                                                      Empty.absurd({Jenc.encode.bits(pp,
                                                                        U32.from_nat(List.length(&2, Bool,
                                                                        h0 <> h1 <> h2 <> h3 <> h4 <> h5 <> h6 <> h7 <>
                                                                        h8 <> h9 <> h10 <> h11 <> h12 <> h13 <> h14 <>
                                                                        h15 <> _h16 <> _t16)),
                                                                        M2.vfold(h0 <> h1 <> h2 <> h3 <> h4 <> h5 <>
                                                                          h6 <>
                                                                          h7 <> h8 <> h9 <> h10 <> h11 <> h12 <> h13 <>
                                                                          h14 <> h15 <> _h16 <> _t16,
                                                                          0)) == Laws.jpg.feed(h0 <> h1 <> h2 <> h3 <>
                                                                          h4 <> h5 <> h6 <> h7 <> h8 <> h9 <> h10 <>
                                                                          h11 <> h12 <> h13 <> h14 <> h15 <> _h16 <>
                                                                          _t16, pp) : Jenc.Put}, M1.huf.false_true(hh))

# 1 or 0 is the bit as a U32
def bitu_u(bb: Bool) -> {Laws.jpg.bitu(bb) == Laws.jpg.ubit(bb) : U32}:
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# a code's value is the model's fold of its bits
def num_v(bs: List<&2, Bool>, +acc: U32) -> {Laws.jpg.num(bs, acc) == M2.vfold(bs, acc) : U32}:
  match bs:
    case Nil{}:
      {==}
    case +bb <> rest:
      Equal.trans(U32, Laws.jpg.num(rest, U32.or(U32.shl(acc), Laws.jpg.bitu(bb))), Laws.jpg.num(rest, M6.vstep(acc,
        bb)), M2.vfold(rest, M6.vstep(acc, bb)),
        Equal.cong(U32, U32, xx => Laws.jpg.num(rest, xx), U32.or(U32.shl(acc), Laws.jpg.bitu(bb)), M6.vstep(acc, bb),
        Equal.trans(U32, U32.or(U32.shl(acc), Laws.jpg.bitu(bb)), U32.or(U32.shl(acc), Laws.jpg.ubit(bb)), M6.vstep(acc,
          bb),
        Equal.cong(U32, U32, xx => U32.or(U32.shl(acc), xx), Laws.jpg.bitu(bb), Laws.jpg.ubit(bb), bitu_u(bb)),
          M2.or_shl_u(acc, bb))),
        num_v(rest, M6.vstep(acc, bb)))

# codes written one after another are their bits fed in order
def wcodes_feed(
  cs: List<&2, List<&2, Bool>>,
  +pp: Jenc.Put,
  +hh: {Laws.jpg.codes16(cs) == True{} : Bool}
) -> {Laws.jpg.write(cs, pp) == Laws.jpg.feed(List.concat(&2, Bool, cs), pp) : Jenc.Put}:
  match cs:
    case Nil{}:
      {==}
    case +cc <> +rest:
      +h1 = {M1.also_l(Nat.is_le(List.length(&2, Bool, cc), 16n), Laws.jpg.codes16(rest), hh) :
        {Nat.is_le(List.length(&2, Bool, cc), 16n) == True{} : Bool}}
      +nn = U32.from_nat(List.length(&2, Bool, cc))
      Equal.trans(Jenc.Put, Laws.jpg.write(rest, Jenc.encode.bits(pp, nn, Laws.jpg.num(cc, 0))), Laws.jpg.write(rest,
        Laws.jpg.feed(cc, pp)),
        Laws.jpg.feed(List.concat(&2, Bool, cc <> rest), pp), Equal.cong(Jenc.Put, Jenc.Put,
          qq => Laws.jpg.write(rest, qq),
        Jenc.encode.bits(pp, nn, Laws.jpg.num(cc, 0)), Laws.jpg.feed(cc, pp), Equal.trans(Jenc.Put,
          Jenc.encode.bits(pp, nn, Laws.jpg.num(cc, 0)),
        Jenc.encode.bits(pp, nn, M2.vfold(cc, 0)), Laws.jpg.feed(cc, pp), Equal.cong(U32, Jenc.Put,
          vv => Jenc.encode.bits(pp, nn,
        vv), Laws.jpg.num(cc, 0), M2.vfold(cc, 0), num_v(cc, 0)), bits_code(cc, pp, h1))),
        Equal.trans(Jenc.Put, Laws.jpg.write(rest, Laws.jpg.feed(cc, pp)), Laws.jpg.feed(List.concat(&2, Bool, rest),
          Laws.jpg.feed(cc, pp)),
        Laws.jpg.feed(List.concat(&2, Bool, cc <> rest), pp), wcodes_feed(rest, Laws.jpg.feed(cc, pp),
          M1.also_r(Nat.is_le(List.length(&2,
        Bool, cc), 16n), Laws.jpg.codes16(rest), hh)), Equal.sym(Jenc.Put, Laws.jpg.feed(List.concat(&2, Bool,
          cc <> rest), pp),
        Laws.jpg.feed(List.concat(&2, Bool, rest), Laws.jpg.feed(cc, pp)), M3.feed_app(cc, List.concat(&2, Bool, rest),
          pp))))

# the last byte's bits: the pending bits, then 1 bits to fill the byte; none when nothing is pending
def pendo(pp: List<&2, Bool>) -> List<&2, List<&2, Bool>>:
  match pp:
    case Nil{}:
      []
    case +hh <> +tt:
      [List.append(&2, Bool, hh <> tt, List.replicate(Bool, Nat.sub(8n, List.length(&2, Bool, hh <> tt)), True{}))]

# the pending bits after one more bit
def mo.next(full: Bool, pp: List<&2, Bool>, bb: Bool) -> List<&2, Bool>:
  match full:
    case True{}:
      +_d = pp
      +_b = bb
      []
    case False{}:
      List.append(&2, Bool, pp, [bb])

# the byte one more bit finishes, if it does, before the bytes after it
def mo.join(full: Bool, pp: List<&2, Bool>, bb: Bool, rest: List<&2, List<&2, Bool>>) -> List<&2, List<&2, Bool>>:
  match full:
    case True{}:
      List.append(&2, Bool, pp, [bb]) <> rest
    case False{}:
      +_d = pp
      +_b = bb
      rest

# the bytes, as their bits and in order, the writer finishes from pending bits pp and then bits bs, padded
def moct(bs: List<&2, Bool>, +pp: List<&2, Bool>) -> List<&2, List<&2, Bool>>:
  match bs:
    case Nil{}:
      pendo(pp)
    case +bb <> rest:
      mo.join(M2.is7(pp), pp, bb, moct(rest, mo.next(M2.is7(pp), pp, bb)))

# the encoder's pad of a model writer is the finished bytes, then the last byte's, stuffed
def pad_base(
  +out: List<&2, List<&2, Bool>>,
  pp: List<&2, Bool>,
  hh: {M2.short(pp) == True{} : Bool}
) -> {Jenc.encode.pad(M2.wst(M2.obytes(out), pp)) == Jenc.encode.stuff.all(M2.obytes(out), stf(M2.obytes(pendo(pp)),
  [])) : List<&2, U32>}:
  match pp:
    case Nil{}:
      {==}
    case +p0 <> t0:
      match t0:
        case Nil{}:
          {==}
        case +p1 <> t1:
          match t1:
            case Nil{}:
              {==}
            case +p2 <> t2:
              match t2:
                case Nil{}:
                  {==}
                case +p3 <> t3:
                  match t3:
                    case Nil{}:
                      {==}
                    case +p4 <> t4:
                      match t4:
                        case Nil{}:
                          {==}
                        case +p5 <> t5:
                          match t5:
                            case Nil{}:
                              {==}
                            case +p6 <> t6:
                              match t6:
                                case Nil{}:
                                  {==}
                                case +p7 <> t7:
                                  Empty.absurd({Jenc.encode.pad(M2.wst(M2.obytes(out),
                                    p0 <> p1 <> p2 <> p3 <> p4 <> p5 <> p6 <> p7 <> t7)) ==
                                    Jenc.encode.stuff.all(M2.obytes(out),
                                    stf(M2.obytes(pendo(p0 <> p1 <> p2 <> p3 <> p4 <> p5 <> p6 <> p7 <> t7)),
                                      [])) : List<&2, U32>}, M2.long8(t7, hh))

# after one more bit the pending bits are still fewer than 8
def next_short(
  pp: List<&2, Bool>,
  bb: Bool,
  hh: {M2.short(pp) == True{} : Bool}
) -> {M2.short(mo.next(M2.is7(pp), pp, bb)) == True{} : Bool}:
  match pp:
    case Nil{}:
      {==}
    case p0 <> t0:
      match t0:
        case Nil{}:
          {==}
        case p1 <> t1:
          match t1:
            case Nil{}:
              {==}
            case p2 <> t2:
              match t2:
                case Nil{}:
                  {==}
                case p3 <> t3:
                  match t3:
                    case Nil{}:
                      {==}
                    case p4 <> t4:
                      match t4:
                        case Nil{}:
                          {==}
                        case p5 <> t5:
                          match t5:
                            case Nil{}:
                              {==}
                            case p6 <> t6:
                              match t6:
                                case Nil{}:
                                  {==}
                                case p7 <> t7:
                                  Empty.absurd({M2.short(mo.next(M2.is7(p0 <> p1 <> p2 <> p3 <> p4 <> p5 <> p6 <> p7 <>
                                    t7),
                                    p0 <> p1 <> p2 <> p3 <> p4 <> p5 <> p6 <> p7 <> t7, bb)) == True{} : Bool},
                                    M2.long8(t7, hh))

# the finished bytes after one more bit
def wo(full: Bool, out: List<&2, List<&2, Bool>>, pp: List<&2, Bool>, bb: Bool) -> List<&2, List<&2, Bool>>:
  match full:
    case True{}:
      List.append(&2, Bool, pp, [bb]) <> out
    case False{}:
      +_d = pp
      +_b = bb
      out

# one model step, as its bytes and pending bits
def wstep.parts(
  full: Bool,
  +out: List<&2, List<&2, Bool>>,
  +pp: List<&2, Bool>,
  +bb: Bool
) -> {M2.wstep.b(full, out, pp, bb) == M2.WS{wo(full, out, pp, bb), mo.next(full, pp, bb)} : M2.WS}:
  match full:
    case True{}:
      {==}
    case False{}:
      {==}

# a finished byte moves from the writer's bytes to the stuffed ones after them
def join.stuff(
  full: Bool,
  +out: List<&2, List<&2, Bool>>,
  +pp: List<&2, Bool>,
  +bb: Bool,
  +rest: List<&2, List<&2, Bool>>
) -> {Jenc.encode.stuff.all(M2.obytes(wo(full, out, pp, bb)), stf(M2.obytes(rest),
  [])) == Jenc.encode.stuff.all(M2.obytes(out), stf(M2.obytes(mo.join(full, pp, bb, rest)), [])) : List<&2, U32>}:
  match full:
    case True{}:
      {==}
    case False{}:
      {==}

# the encoder's pad of the model writer after bits bs is the model's bytes, stuffed
def pad_m(
  bs: List<&2, Bool>,
  +out: List<&2, List<&2, Bool>>,
  +pp: List<&2, Bool>,
  +hh: {M2.short(pp) == True{} : Bool}
) -> {Jenc.encode.pad(M2.wput(M2.wm(bs, M2.WS{out, pp}))) == Jenc.encode.stuff.all(M2.obytes(out),
    stf(M2.obytes(moct(bs, pp)),
  [])) : List<&2, U32>}:
  match bs:
    case Nil{}:
      pad_base(out, pp, hh)
    case +bb <> +rest:
      +fl = M2.is7(pp)
      +o2 = wo(fl, out, pp, bb)
      +p2 = mo.next(fl, pp, bb)
      Equal.trans(List<&2, U32>, Jenc.encode.pad(M2.wput(M2.wm(rest, M2.wstep.b(fl, out, pp, bb)))),
        Jenc.encode.pad(M2.wput(M2.wm(rest, M2.WS{o2, p2}))), Jenc.encode.stuff.all(M2.obytes(out),
            stf(M2.obytes(moct(bb <> rest,
        pp)), [])), Equal.cong(M2.WS, List<&2, U32>, ws => Jenc.encode.pad(M2.wput(M2.wm(rest, ws))), M2.wstep.b(fl,
            out, pp, bb),
        M2.WS{o2, p2}, wstep.parts(fl, out, pp, bb)),
        Equal.trans(List<&2, U32>, Jenc.encode.pad(M2.wput(M2.wm(rest, M2.WS{o2, p2}))),
            Jenc.encode.stuff.all(M2.obytes(o2),
        stf(M2.obytes(moct(rest, p2)), [])), Jenc.encode.stuff.all(M2.obytes(out), stf(M2.obytes(moct(bb <> rest, pp)),
          [])),
        pad_m(rest, o2, p2, next_short(pp, bb, hh)), join.stuff(fl, out, pp, bb, moct(rest, p2))))

# the reader after taking the first bit of a fresh byte bo: seven bits left, the bit shifted into acc
def rfresh(left: Nat, +bo: U32, +rest: List<&2, U32>, +ok: U32, +acc: U32) -> Jpeg.Bits & U32:
  Jpeg.decode.nbits(left, False{}, rest, False{}, Jpeg.decode.head.is(rest, 255), Jpeg.decode.head.is(rest, 0), 7,
    U32.and(255, U32.shl(bo)), ok, U32.or(U32.shrn(bo, 7n), U32.shl(acc)))

# the bit reader with an empty buffer takes the next byte, stuffed or not
def rbyte(
  zz: Bool,
  +left: Nat,
  +bo: U32,
  +rest: List<&2, U32>,
  +ok: U32,
  +acc: U32,
  +ee: {U32.is_eq(bo, 255) == zz : Bool}
) -> {Jpeg.decode.nbits(1n+left, True{}, Jenc.encode.stuff.put(zz, bo, rest), False{},
  Jpeg.decode.head.is(Jenc.encode.stuff.put(zz, bo, rest), 255), Jpeg.decode.head.is(Jenc.encode.stuff.put(zz, bo,
  rest), 0), 0, 0, ok, acc) == rfresh(left, bo, rest, ok, acc) : Jpeg.Bits & U32}:
  match zz:
    case False{}:
      Equal.cong(Bool, Jpeg.Bits & U32, hb => Jpeg.decode.nbits(1n+left, True{}, bo <> rest, False{}, hb,
        U32.is_eq(bo, 0), 0, 0, ok, acc), U32.is_eq(bo, 255), False{}, ee)
    case True{}:
      eb = Equal.sym(U32, bo, 255, M1.ueq(bo, 255, ee))
      %eb : {Jpeg.decode.nbits(1n+left, True{}, _ <> (0 <> rest), False{}, Jpeg.decode.head.is(_ <> (0 <> rest), 255),
        Jpeg.decode.head.is(_ <> (0 <> rest), 0), 0, 0, ok, acc) == rfresh(left, _, rest, ok, acc) : Jpeg.Bits & U32}
      {==}

# the reader's model: the bits left in its buffer, and the bytes after them as their bits
type RS is Data:
  RS{qq: List<&2, Bool>, os: List<&2, List<&2, Bool>>}

# the reader's buffer holding bits qq: the first at bit 7, the rest below it, zeros under them
def rbuf(+qq: List<&2, Bool>) -> U32:
  U32.shln(M2.vfold(qq, 0), Nat.sub(8n, List.length(&2, Bool, qq)))

# the stuffed bytes of a model reader
def rxs(os: List<&2, List<&2, Bool>>) -> List<&2, U32>:
  stf(M2.obytes(os), [])

# the decoder's bit reader the model stands for
def rbits(ss: RS, +ok: U32) -> Jpeg.Bits:
  match ss:
    case RS{+qq, os}:
      Jpeg.Bits{U32.from_nat(List.length(&2, Bool, qq)), ok, rbuf(qq), rxs(os)}

# the bit reader's loop reading left more bits onto acc from the model's reader
def canon(left: Nat, ss: RS, +ok: U32, +acc: U32) -> Jpeg.Bits & U32:
  match ss:
    case RS{+qq, +os}:
      +nn = U32.from_nat(List.length(&2, Bool, qq))
      Jpeg.decode.nbits(left, U32.is_eq(nn, 0), rxs(os), False{}, Jpeg.decode.head.is(rxs(os), 255),
        Jpeg.decode.head.is(rxs(os), 0), nn, rbuf(qq), ok, acc)

# the bits the model reader has left, in order
def rem(ss: RS) -> List<&2, Bool>:
  match ss:
    case RS{qq, os}:
      List.append(&2, Bool, qq, List.concat(&2, Bool, os))

# the next bit a model reader reads (False when it has none)
def rhead(ss: RS) -> Bool:
  match ss:
    case RS{qq, os}:
      match qq:
        case q0 <> _qt:
          +_o = os
          q0
        case Nil{}:
          match os:
            case oo <> _ot:
              match oo:
                case o0 <> _t:
                  o0
                case Nil{}:
                  False{}
            case Nil{}:
              False{}

# the model reader after one bit
def rnext(ss: RS) -> RS:
  match ss:
    case RS{qq, os}:
      match qq:
        case _q0 <> qt:
          RS{qt, os}
        case Nil{}:
          match os:
            case oo <> ot:
              match oo:
                case _o0 <> tt:
                  RS{tt, ot}
                case Nil{}:
                  RS{[], ot}
            case Nil{}:
              RS{[], []}

# every byte of a model reader has 8 bits
def oct8(os: List<&2, List<&2, Bool>>) -> Bool:
  match os:
    case Nil{}:
      True{}
    case oo <> rest:
      Laws.jpg.also(Nat.is_eq(List.length(&2, Bool, oo), 8n), oct8(rest))

# one bit read from a buffer holding bits
def rstep.q(
  +left: Nat,
  +q0: Bool,
  t0: List<&2, Bool>,
  +os: List<&2, List<&2, Bool>>,
  +ok: U32,
  +acc: U32,
  hs: {M2.short(q0 <> t0) == True{} : Bool}
) -> {canon(1n+left, RS{q0 <> t0, os}, ok, acc) == canon(left, rnext(RS{q0 <> t0, os}), ok, M6.vstep(acc,
  rhead(RS{q0 <> t0, os}))) : Jpeg.Bits & U32}:
  match t0:
    case Nil{}:
      Equal.cong(U32, Jpeg.Bits & U32, xx => Jpeg.decode.nbits(left, U32.is_eq(U32.from_nat(List.length(&2, Bool,
        [])), 0), rxs(os), False{}, Jpeg.decode.head.is(rxs(os), 255), Jpeg.decode.head.is(rxs(os), 0),
        U32.from_nat(List.length(&2, Bool, [])), rbuf([]), ok, xx), U32.or(Laws.jpg.ubit(q0), U32.shl(acc)),
        M6.vstep(acc, q0), or_u_shl(acc, q0))
    case +q1 <> t1:
      match t1:
        case Nil{}:
          Equal.cong(U32, Jpeg.Bits & U32, xx => Jpeg.decode.nbits(left, U32.is_eq(U32.from_nat(List.length(&2, Bool,
            q1 <> [])), 0), rxs(os), False{}, Jpeg.decode.head.is(rxs(os), 255), Jpeg.decode.head.is(rxs(os), 0),
            U32.from_nat(List.length(&2, Bool, q1 <> [])), rbuf(q1 <> []), ok, xx), U32.or(Laws.jpg.ubit(q0),
              U32.shl(acc)),
            M6.vstep(acc, q0), or_u_shl(acc, q0))
        case +q2 <> t2:
          match t2:
            case Nil{}:
              Equal.cong(U32, Jpeg.Bits & U32, xx => Jpeg.decode.nbits(left, U32.is_eq(U32.from_nat(List.length(&2,
                Bool,
                q1 <> q2 <> [])), 0), rxs(os), False{}, Jpeg.decode.head.is(rxs(os), 255),
                  Jpeg.decode.head.is(rxs(os), 0),
                U32.from_nat(List.length(&2, Bool, q1 <> q2 <> [])), rbuf(q1 <> q2 <> []), ok, xx),
                  U32.or(Laws.jpg.ubit(q0), U32.shl(acc)),
                M6.vstep(acc, q0), or_u_shl(acc, q0))
            case +q3 <> t3:
              match t3:
                case Nil{}:
                  Equal.cong(U32, Jpeg.Bits & U32, xx => Jpeg.decode.nbits(left,
                    U32.is_eq(U32.from_nat(List.length(&2, Bool,
                    q1 <> q2 <> q3 <> [])), 0), rxs(os), False{}, Jpeg.decode.head.is(rxs(os), 255),
                      Jpeg.decode.head.is(rxs(os), 0),
                    U32.from_nat(List.length(&2, Bool, q1 <> q2 <> q3 <> [])), rbuf(q1 <> q2 <> q3 <> []), ok, xx),
                      U32.or(Laws.jpg.ubit(q0), U32.shl(acc)),
                    M6.vstep(acc, q0), or_u_shl(acc, q0))
                case +q4 <> t4:
                  match t4:
                    case Nil{}:
                      Equal.cong(U32, Jpeg.Bits & U32, xx => Jpeg.decode.nbits(left,
                        U32.is_eq(U32.from_nat(List.length(&2, Bool,
                        q1 <> q2 <> q3 <> q4 <> [])), 0), rxs(os), False{}, Jpeg.decode.head.is(rxs(os), 255),
                          Jpeg.decode.head.is(rxs(os), 0),
                        U32.from_nat(List.length(&2, Bool, q1 <> q2 <> q3 <> q4 <> [])),
                          rbuf(q1 <> q2 <> q3 <> q4 <> []), ok, xx), U32.or(Laws.jpg.ubit(q0), U32.shl(acc)),
                        M6.vstep(acc, q0), or_u_shl(acc, q0))
                    case +q5 <> t5:
                      match t5:
                        case Nil{}:
                          Equal.cong(U32, Jpeg.Bits & U32, xx => Jpeg.decode.nbits(left,
                            U32.is_eq(U32.from_nat(List.length(&2, Bool,
                            q1 <> q2 <> q3 <> q4 <> q5 <> [])), 0), rxs(os), False{}, Jpeg.decode.head.is(rxs(os),
                              255), Jpeg.decode.head.is(rxs(os), 0),
                            U32.from_nat(List.length(&2, Bool, q1 <> q2 <> q3 <> q4 <> q5 <> [])),
                              rbuf(q1 <> q2 <> q3 <> q4 <> q5 <> []), ok, xx), U32.or(Laws.jpg.ubit(q0), U32.shl(acc)),
                            M6.vstep(acc, q0), or_u_shl(acc, q0))
                        case +q6 <> t6:
                          match t6:
                            case Nil{}:
                              Equal.cong(U32, Jpeg.Bits & U32, xx => Jpeg.decode.nbits(left,
                                U32.is_eq(U32.from_nat(List.length(&2, Bool,
                                q1 <> q2 <> q3 <> q4 <> q5 <> q6 <> [])), 0), rxs(os), False{},
                                  Jpeg.decode.head.is(rxs(os), 255), Jpeg.decode.head.is(rxs(os), 0),
                                U32.from_nat(List.length(&2, Bool, q1 <> q2 <> q3 <> q4 <> q5 <> q6 <> [])),
                                  rbuf(q1 <> q2 <> q3 <> q4 <> q5 <> q6 <> []), ok, xx), U32.or(Laws.jpg.ubit(q0),
                                  U32.shl(acc)),
                                M6.vstep(acc, q0), or_u_shl(acc, q0))
                            case _q7 <> t7:
                              Empty.absurd({canon(1n+left, RS{q0 <> q1 <> q2 <> q3 <> q4 <> q5 <> q6 <> _q7 <> t7,
                                os}, ok, acc) == canon(left,
                                rnext(RS{q0 <> q1 <> q2 <> q3 <> q4 <> q5 <> q6 <> _q7 <> t7, os}), ok, M6.vstep(acc,
                                rhead(RS{q0 <> q1 <> q2 <> q3 <> q4 <> q5 <> q6 <> _q7 <> t7,
                                os}))) : Jpeg.Bits & U32}, M2.long8(t7, hs))

# one bit read with the buffer empty: the next byte's first bit
def rstep.o(
  +left: Nat,
  oo: List<&2, Bool>,
  +ot: List<&2, List<&2, Bool>>,
  +ok: U32,
  +acc: U32,
  h8: {Nat.is_eq(List.length(&2, Bool, oo), 8n) == True{} : Bool}
) -> {canon(1n+left, RS{[], oo <> ot}, ok, acc) == canon(left, rnext(RS{[], oo <> ot}), ok, M6.vstep(acc, rhead(RS{[],
  oo <> ot}))) : Jpeg.Bits & U32}:
  match oo:
    case Nil{}:
      Empty.absurd({canon(1n+left, RS{[], ([]) <> ot}, ok, acc) == canon(left, rnext(RS{[], ([]) <> ot}), ok,
        M6.vstep(acc, rhead(RS{[], ([]) <> ot}))) : Jpeg.Bits & U32}, M1.huf.false_true(h8))
    case +o0 <> t0:
      match t0:
        case Nil{}:
          Empty.absurd({canon(1n+left, RS{[], (o0 <> []) <> ot}, ok, acc) == canon(left, rnext(RS{[],
            (o0 <> []) <> ot}), ok, M6.vstep(acc, rhead(RS{[], (o0 <> []) <> ot}))) : Jpeg.Bits & U32},
                M1.huf.false_true(h8))
        case +o1 <> t1:
          match t1:
            case Nil{}:
              Empty.absurd({canon(1n+left, RS{[], (o0 <> o1 <> []) <> ot}, ok, acc) == canon(left, rnext(RS{[],
                (o0 <> o1 <> []) <> ot}), ok, M6.vstep(acc, rhead(RS{[], (o0 <> o1 <> []) <> ot}))) : Jpeg.Bits & U32},
                M1.huf.false_true(h8))
            case +o2 <> t2:
              match t2:
                case Nil{}:
                  Empty.absurd({canon(1n+left, RS{[], (o0 <> o1 <> o2 <> []) <> ot}, ok, acc) == canon(left,
                    rnext(RS{[], (o0 <> o1 <> o2 <> []) <> ot}), ok, M6.vstep(acc, rhead(RS{[],
                    (o0 <> o1 <> o2 <> []) <> ot}))) : Jpeg.Bits & U32}, M1.huf.false_true(h8))
                case +o3 <> t3:
                  match t3:
                    case Nil{}:
                      Empty.absurd({canon(1n+left, RS{[], (o0 <> o1 <> o2 <> o3 <> []) <> ot}, ok, acc) == canon(left,
                        rnext(RS{[], (o0 <> o1 <> o2 <> o3 <> []) <> ot}), ok, M6.vstep(acc, rhead(RS{[],
                        (o0 <> o1 <> o2 <> o3 <> []) <> ot}))) : Jpeg.Bits & U32}, M1.huf.false_true(h8))
                    case +o4 <> t4:
                      match t4:
                        case Nil{}:
                          Empty.absurd({canon(1n+left, RS{[], (o0 <> o1 <> o2 <> o3 <> o4 <> []) <> ot}, ok,
                            acc) == canon(left, rnext(RS{[], (o0 <> o1 <> o2 <> o3 <> o4 <> []) <> ot}), ok,
                            M6.vstep(acc, rhead(RS{[], (o0 <> o1 <> o2 <> o3 <> o4 <> []) <> ot}))) : Jpeg.Bits & U32},
                            M1.huf.false_true(h8))
                        case +o5 <> t5:
                          match t5:
                            case Nil{}:
                              Empty.absurd({canon(1n+left, RS{[], (o0 <> o1 <> o2 <> o3 <> o4 <> o5 <> []) <> ot}, ok,
                                acc) == canon(left, rnext(RS{[], (o0 <> o1 <> o2 <> o3 <> o4 <> o5 <> []) <> ot}), ok,
                                M6.vstep(acc, rhead(RS{[],
                                (o0 <> o1 <> o2 <> o3 <> o4 <> o5 <> []) <> ot}))) : Jpeg.Bits & U32},
                                    M1.huf.false_true(h8))
                            case +o6 <> t6:
                              match t6:
                                case Nil{}:
                                  Empty.absurd({canon(1n+left, RS{[],
                                    (o0 <> o1 <> o2 <> o3 <> o4 <> o5 <> o6 <> []) <> ot}, ok, acc) == canon(left,
                                    rnext(RS{[], (o0 <> o1 <> o2 <> o3 <> o4 <> o5 <> o6 <> []) <> ot}), ok,
                                    M6.vstep(acc, rhead(RS{[],
                                    (o0 <> o1 <> o2 <> o3 <> o4 <> o5 <> o6 <> []) <> ot}))) : Jpeg.Bits & U32},
                                    M1.huf.false_true(h8))
                                case +o7 <> t7:
                                  match t7:
                                    case Nil{}:
                                      Equal.trans(Jpeg.Bits & U32, canon(1n+left, RS{[],
                                        (o0 <> o1 <> o2 <> o3 <> o4 <> o5 <> o6 <> o7 <> []) <> ot}, ok, acc),
                                        rfresh(left, M2.vfold(o0 <> o1 <> o2 <> o3 <> o4 <> o5 <> o6 <> o7 <> [], 0),
                                        rxs(ot), ok, acc),
                                        canon(left, rnext(RS{[],
                                          (o0 <> o1 <> o2 <> o3 <> o4 <> o5 <> o6 <> o7 <> []) <> ot}), ok,
                                              M6.vstep(acc,
                                          rhead(RS{[], (o0 <> o1 <> o2 <> o3 <> o4 <> o5 <> o6 <> o7 <> []) <> ot}))),
                                          rbyte(U32.is_eq(M2.vfold(o0 <> o1 <> o2 <> o3 <> o4 <> o5 <> o6 <> o7 <> [],
                                          0), 255), left, M2.vfold(o0 <> o1 <> o2 <> o3 <> o4 <> o5 <> o6 <> o7 <> [],
                                              0),
                                        rxs(ot), ok, acc, {==}), Equal.cong(U32, Jpeg.Bits & U32,
                                          xx => Jpeg.decode.nbits(left, False{}, rxs(ot),
                                        False{}, Jpeg.decode.head.is(rxs(ot), 255), Jpeg.decode.head.is(rxs(ot), 0),
                                          7, rbuf(o1 <> o2 <> o3 <> o4 <> o5 <> o6 <> o7 <> []), ok, xx),
                                        U32.or(Laws.jpg.ubit(o0), U32.shl(acc)), M6.vstep(acc, o0), or_u_shl(acc, o0)))
                                    case _o8 <> t8:
                                      Empty.absurd({canon(1n+left, RS{[],
                                        (o0 <> o1 <> o2 <> o3 <> o4 <> o5 <> o6 <> o7 <> _o8 <> t8) <> ot}, ok,
                                        acc) == canon(left, rnext(RS{[],
                                        (o0 <> o1 <> o2 <> o3 <> o4 <> o5 <> o6 <> o7 <> _o8 <> t8) <> ot}), ok,
                                        M6.vstep(acc, rhead(RS{[],
                                        (o0 <> o1 <> o2 <> o3 <> o4 <> o5 <> o6 <> o7 <> _o8 <> t8) <> ot}))) :
                                        Jpeg.Bits & U32}, M1.huf.false_true(h8))

# a model reader's buffer holds fewer than 8 bits
def rshort(ss: RS) -> Bool:
  match ss:
    case RS{qq, _os}:
      M2.short(qq)

# every byte after a model reader's buffer has 8 bits
def roct8(ss: RS) -> Bool:
  match ss:
    case RS{_qq, os}:
      oct8(os)

# a model reader with a bit left
def rsome(ss: RS) -> Bool:
  Nat.is_lt(0n, List.length(&2, Bool, rem(ss)))

# one bit read from the model reader: its next bit shifted into acc, the reader after it
def rstep(
  +left: Nat,
  ss: RS,
  +ok: U32,
  +acc: U32,
  hs: {rshort(ss) == True{} : Bool},
  h8: {roct8(ss) == True{} : Bool},
  hn: {rsome(ss) == True{} : Bool}
) -> {canon(1n+left, ss, ok, acc) == canon(left, rnext(ss), ok, M6.vstep(acc, rhead(ss))) : Jpeg.Bits & U32}:
  match ss:
    case RS{qq, os}:
      match qq:
        case +q0 <> t0:
          rstep.q(left, q0, t0, os, ok, acc, hs)
        case Nil{}:
          match os:
            case Nil{}:
              Empty.absurd({canon(1n+left, RS{[], []}, ok, acc) == canon(left, rnext(RS{[], []}), ok, M6.vstep(acc,
                rhead(RS{[], []}))) : Jpeg.Bits & U32}, M1.huf.false_true(hn))
            case +oo <> +ot:
              rstep.o(left, oo, ot, ok, acc, M1.also_l(Nat.is_eq(List.length(&2, Bool, oo), 8n), oct8(ot), h8))

# below b after one more is below b
def lt_succ_l(aa: Nat, bb: Nat, hh: {Nat.is_lt(1n+aa, bb) == True{} : Bool}) -> {Nat.is_lt(aa, bb) == True{} : Bool}:
  match aa bb:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, M1.huf.false_true(hh))
    case 0n 1n+_q:
      {==}
    case 1n+_p 0n:
      Empty.absurd({Nat.is_lt(1n+_p, 0n) == True{} : Bool}, M1.huf.false_true(hh))
    case 1n+pp 1n+qq:
      lt_succ_l(pp, qq, hh)

# a number equal to b + 1 less one is below b + 1
def eq_lt_succ(aa: Nat, bb: Nat, hh: {Nat.is_eq(1n+aa, bb) == True{} : Bool}) -> {Nat.is_lt(aa, bb) == True{} : Bool}:
  match aa bb:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, M1.huf.false_true(hh))
    case 0n 1n+_q:
      {==}
    case 1n+_p 0n:
      Empty.absurd({Nat.is_lt(1n+_p, 0n) == True{} : Bool}, M1.huf.false_true(hh))
    case 1n+pp 1n+qq:
      eq_lt_succ(pp, qq, hh)

# m + 1 at most l says l is above 0
def le_pos(mm: Nat, ll: Nat, hh: {Nat.is_le(1n+mm, ll) == True{} : Bool}) -> {Nat.is_lt(0n, ll) == True{} : Bool}:
  match ll:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, M1.huf.false_true(hh))
    case 1n+_q:
      {==}

# the model reader after a bit still holds fewer than 8 bits
def rnext_short(
  ss: RS,
  hs: {rshort(ss) == True{} : Bool},
  h8: {roct8(ss) == True{} : Bool}
) -> {rshort(rnext(ss)) == True{} : Bool}:
  match ss:
    case RS{qq, os}:
      match qq:
        case _q0 <> +qt:
          lt_succ_l(List.length(&2, Bool, qt), 8n, hs)
        case Nil{}:
          match os:
            case Nil{}:
              {==}
            case oo <> +ot:
              match oo:
                case Nil{}:
                  {==}
                case _o0 <> +tt:
                  eq_lt_succ(List.length(&2, Bool, tt), 8n, M1.also_l(Nat.is_eq(1n+List.length(&2, Bool, tt), 8n),
                    oct8(ot), h8))

# the model reader's bytes after a bit still have 8 bits each
def rnext_oct8(ss: RS, h8: {roct8(ss) == True{} : Bool}) -> {roct8(rnext(ss)) == True{} : Bool}:
  match ss:
    case RS{qq, os}:
      match qq:
        case _q0 <> _qt:
          h8
        case Nil{}:
          match os:
            case Nil{}:
              {==}
            case oo <> +ot:
              match oo:
                case Nil{}:
                  M1.also_r(Nat.is_eq(0n, 8n), oct8(ot), h8)
                case _o0 <> +tt:
                  M1.also_r(Nat.is_eq(1n+List.length(&2, Bool, tt), 8n), oct8(ot), h8)

# the model reader's bits: the next bit, then the bits after it
def rem_cons(
  ss: RS,
  h8: {roct8(ss) == True{} : Bool},
  hn: {rsome(ss) == True{} : Bool}
) -> {rem(ss) == rhead(ss) <> rem(rnext(ss)) : List<&2, Bool>}:
  match ss:
    case RS{qq, os}:
      match qq:
        case _q0 <> _qt:
          {==}
        case Nil{}:
          match os:
            case Nil{}:
              Empty.absurd({rem(RS{[], []}) == rhead(RS{[], []}) <> rem(rnext(RS{[], []})) : List<&2, Bool>},
                M1.huf.false_true(hn))
            case oo <> +ot:
              match oo:
                case Nil{}:
                  Empty.absurd({rem(RS{[], [] <> ot}) == rhead(RS{[], [] <> ot}) <> rem(rnext(RS{[], [] <> ot})) :
                    List<&2, Bool>}, M1.huf.false_true(M1.also_l(Nat.is_eq(0n, 8n), oct8(ot), h8)))
                case _o0 <> _tt:
                  {==}

# the model reader after m bits
def radv(mm: Nat, ss: RS) -> RS:
  match mm:
    case 0n:
      ss
    case 1n+pp:
      radv(pp, rnext(ss))

# nothing taken is nothing
def take0(xs: List<&2, Bool>) -> {List.take(&2, Bool, xs, 0n) == [] : List<&2, Bool>}:
  match xs:
    case Nil{}:
      {==}
    case _h <> _t:
      {==}

# nothing dropped is the list
def drop0(xs: List<&2, Bool>) -> {List.drop(&2, Bool, xs, 0n) == xs : List<&2, Bool>}:
  match xs:
    case Nil{}:
      {==}
    case _h <> _t:
      {==}

# the bit reader's loop, m bits from a model reader: the reader m bits on, and those bits folded onto acc
def rread(
  mm: Nat,
  +ss: RS,
  +ok: U32,
  +acc: U32,
  +hs: {rshort(ss) == True{} : Bool},
  +h8: {roct8(ss) == True{} : Bool},
  +hl: {Nat.is_le(mm, List.length(&2, Bool, rem(ss))) == True{} : Bool}
) -> {canon(mm, ss, ok, acc) == (rbits(radv(mm, ss), ok), M2.vfold(List.take(&2, Bool, rem(ss), mm),
  acc)) : Jpeg.Bits & U32}:
  match mm:
    case 0n:
      match ss:
        case RS{+qq, +os}:
          Equal.cong(List<&2, Bool>, Jpeg.Bits & U32, tk => (rbits(RS{qq, os}, ok), M2.vfold(tk, acc)), [],
            List.take(&2, Bool, rem(RS{qq, os}), 0n), Equal.sym(List<&2, Bool>, List.take(&2, Bool, rem(RS{qq, os}),
            0n), [], take0(rem(RS{qq, os}))))
    case 1n+ +pp:
      +hn = {le_pos(pp, List.length(&2, Bool, rem(ss)), hl) : {rsome(ss) == True{} : Bool}}
      +nx = rnext(ss)
      +er = {rem_cons(ss, h8, hn) : {rem(ss) == rhead(ss) <> rem(nx) : List<&2, Bool>}}
      +h2 = {Equal.cong(List<&2, Bool>, Bool, xs => Nat.is_le(1n+pp, List.length(&2, Bool, xs)), rem(ss),
        rhead(ss) <> rem(nx), er) : {Nat.is_le(1n+pp, List.length(&2, Bool, rem(ss))) == Nat.is_le(pp,
        List.length(&2, Bool, rem(nx))) : Bool}}
      Equal.trans(Jpeg.Bits & U32, canon(1n+pp, ss, ok, acc), canon(pp, nx, ok, M6.vstep(acc, rhead(ss))),
        (rbits(radv(1n+pp, ss), ok), M2.vfold(List.take(&2, Bool, rem(ss), 1n+pp), acc)),
        rstep(pp, ss, ok, acc, hs, h8, hn),
        Equal.trans(Jpeg.Bits & U32, canon(pp, nx, ok, M6.vstep(acc, rhead(ss))), (rbits(radv(pp, nx), ok),
        M2.vfold(List.take(&2, Bool, rem(nx), pp), M6.vstep(acc, rhead(ss)))), (rbits(radv(1n+pp, ss), ok),
        M2.vfold(List.take(&2, Bool, rem(ss), 1n+pp), acc)),
        rread(pp, nx, ok, M6.vstep(acc, rhead(ss)), rnext_short(ss, hs, h8), rnext_oct8(ss, h8),
        Equal.trans(Bool, Nat.is_le(pp, List.length(&2, Bool, rem(nx))), Nat.is_le(1n+pp, List.length(&2, Bool,
        rem(ss))), True{}, Equal.sym(Bool, Nat.is_le(1n+pp, List.length(&2, Bool, rem(ss))), Nat.is_le(pp,
        List.length(&2, Bool, rem(nx))), h2), hl)),
        Equal.cong(List<&2, Bool>, Jpeg.Bits & U32, xs => (rbits(radv(pp, nx), ok), M2.vfold(List.take(&2, Bool, xs,
        1n+pp), acc)), rhead(ss) <> rem(nx), rem(ss), Equal.sym(List<&2, Bool>, rem(ss), rhead(ss) <> rem(nx), er))))

# the model reader m bits on still holds fewer than 8 bits and its bytes have 8 bits each
def radv_ok(
  mm: Nat,
  +ss: RS,
  +hs: {rshort(ss) == True{} : Bool},
  +h8: {roct8(ss) == True{} : Bool}
) -> {Bool.and(rshort(radv(mm, ss)), roct8(radv(mm, ss))) == True{} : Bool}:
  match mm:
    case 0n:
      es = Equal.sym(Bool, rshort(ss), True{}, hs)
      %es : {Bool.and(_, roct8(ss)) == True{} : Bool}
      h8
    case 1n+pp:
      radv_ok(pp, rnext(ss), rnext_short(ss, hs, h8), rnext_oct8(ss, h8))

# the model reader's bits m bits on are its bits with m dropped
def rem_radv(
  mm: Nat,
  +ss: RS,
  +hs: {rshort(ss) == True{} : Bool},
  +h8: {roct8(ss) == True{} : Bool},
  +hl: {Nat.is_le(mm, List.length(&2, Bool, rem(ss))) == True{} : Bool}
) -> {rem(radv(mm, ss)) == List.drop(&2, Bool, rem(ss), mm) : List<&2, Bool>}:
  match mm:
    case 0n:
      match ss:
        case RS{+qq, +os}:
          Equal.sym(List<&2, Bool>, List.drop(&2, Bool, rem(RS{qq, os}), 0n), rem(RS{qq, os}), drop0(rem(RS{qq, os})))
    case 1n+ +pp:
      +hn = {le_pos(pp, List.length(&2, Bool, rem(ss)), hl) : {rsome(ss) == True{} : Bool}}
      +nx = rnext(ss)
      +er = {rem_cons(ss, h8, hn) : {rem(ss) == rhead(ss) <> rem(nx) : List<&2, Bool>}}
      +h2 = {Equal.cong(List<&2, Bool>, Bool, xs => Nat.is_le(1n+pp, List.length(&2, Bool, xs)), rem(ss),
        rhead(ss) <> rem(nx), er) : {Nat.is_le(1n+pp, List.length(&2, Bool, rem(ss))) == Nat.is_le(pp,
        List.length(&2, Bool, rem(nx))) : Bool}}
      Equal.trans(List<&2, Bool>, rem(radv(pp, nx)), List.drop(&2, Bool, rem(nx), pp), List.drop(&2, Bool, rem(ss),
        1n+pp), rem_radv(pp, nx, rnext_short(ss, hs, h8), rnext_oct8(ss, h8), Equal.trans(Bool, Nat.is_le(pp,
        List.length(&2, Bool, rem(nx))), Nat.is_le(1n+pp, List.length(&2, Bool, rem(ss))), True{}, Equal.sym(Bool,
        Nat.is_le(1n+pp, List.length(&2, Bool, rem(ss))), Nat.is_le(pp, List.length(&2, Bool, rem(nx))), h2), hl)),
        Equal.cong(List<&2, Bool>, List<&2, Bool>, xs => List.drop(&2, Bool, xs, 1n+pp), rhead(ss) <> rem(nx), rem(ss),
        Equal.sym(List<&2, Bool>, rem(ss), rhead(ss) <> rem(nx), er)))

# zero is at most every number
def le0(nn: Nat) -> {Nat.is_le(0n, nn) == True{} : Bool}:
  match nn:
    case 0n:
      {==}
    case 1n+_p:
      {==}

# a length up to 16 is its own U32
def tn16(nn: Nat, hh: {Nat.is_le(nn, 16n) == True{} : Bool}) -> {U32.to_nat(U32.from_nat(nn)) == nn : Nat}:
  match nn:
    case 0n:
      {==}
    case 1n+n0:
      match n0:
        case 0n:
          {==}
        case 1n+n1:
          match n1:
            case 0n:
              {==}
            case 1n+n2:
              match n2:
                case 0n:
                  {==}
                case 1n+n3:
                  match n3:
                    case 0n:
                      {==}
                    case 1n+n4:
                      match n4:
                        case 0n:
                          {==}
                        case 1n+n5:
                          match n5:
                            case 0n:
                              {==}
                            case 1n+n6:
                              match n6:
                                case 0n:
                                  {==}
                                case 1n+n7:
                                  match n7:
                                    case 0n:
                                      {==}
                                    case 1n+n8:
                                      match n8:
                                        case 0n:
                                          {==}
                                        case 1n+n9:
                                          match n9:
                                            case 0n:
                                              {==}
                                            case 1n+n10:
                                              match n10:
                                                case 0n:
                                                  {==}
                                                case 1n+n11:
                                                  match n11:
                                                    case 0n:
                                                      {==}
                                                    case 1n+n12:
                                                      match n12:
                                                        case 0n:
                                                          {==}
                                                        case 1n+n13:
                                                          match n13:
                                                            case 0n:
                                                              {==}
                                                            case 1n+n14:
                                                              match n14:
                                                                case 0n:
                                                                  {==}
                                                                case 1n+n15:
                                                                  match n15:
                                                                    case 0n:
                                                                      {==}
                                                                    case 1n+_n16:
                                                                      Empty.absurd({U32.to_nat(U32.from_nat(nn)) == nn
                                                                        : Nat}, M1.huf.false_true(hh))

# a code's own bits are what taking its length from it and more gives
def take_app(
  cc: List<&2, Bool>,
  +xs: List<&2, Bool>
) -> {List.take(&2, Bool, List.append(&2, Bool, cc, xs), List.length(&2, Bool, cc)) == cc : List<&2, Bool>}:
  match cc:
    case Nil{}:
      take0(xs)
    case +hh <> tt:
      Equal.cong(List<&2, Bool>, List<&2, Bool>, ys => hh <> ys, List.take(&2, Bool, List.append(&2, Bool, tt, xs),
        List.length(&2, Bool, tt)), tt, take_app(tt, xs))

# dropping a code's length from it and more leaves the more
def drop_app(
  cc: List<&2, Bool>,
  +xs: List<&2, Bool>
) -> {List.drop(&2, Bool, List.append(&2, Bool, cc, xs), List.length(&2, Bool, cc)) == xs : List<&2, Bool>}:
  match cc:
    case Nil{}:
      drop0(xs)
    case _hh <> tt:
      drop_app(tt, xs)

# a code is no longer than it and more
def len_app(
  cc: List<&2, Bool>,
  xs: List<&2, Bool>
) -> {Nat.is_le(List.length(&2, Bool, cc), List.length(&2, Bool, List.append(&2, Bool, cc, xs))) == True{} : Bool}:
  match cc:
    case Nil{}:
      le0(List.length(&2, Bool, xs))
    case _hh <> tt:
      len_app(tt, xs)

# a read of n bits from the model's reader is the bit reader's loop
def read_canon(
  +nn: U32,
  ss: RS,
  +ok: U32
) -> {Jpeg.decode.read.n(nn, rbits(ss, ok)) == canon(U32.to_nat(nn), ss, ok, 0) : Jpeg.Bits & U32}:
  match ss:
    case RS{_qq, _os}:
      {==}

# the model reader over codes then more bits reads each code's value back, its ok flag kept
def reads_m(
  cs: List<&2, List<&2, Bool>>,
  +ss: RS,
  +ok: U32,
  +tl: List<&2, Bool>,
  +hs: {rshort(ss) == True{} : Bool},
  +h8: {roct8(ss) == True{} : Bool},
  +hc: {Laws.jpg.codes16(cs) == True{} : Bool},
  +he: {rem(ss) == List.append(&2, Bool, List.concat(&2, Bool, cs), tl) : List<&2, Bool>}
) -> {Laws.jpg.reads(cs, rbits(ss, ok)) == (Laws.jpg.nums(cs), ok) : List<&2, U32> & U32}:
  match cs:
    case Nil{}:
      match ss:
        case RS{_qq, _os}:
          {==}
    case +cc <> +rest:
      +ln = List.length(&2, Bool, cc)
      +nn = U32.from_nat(ln)
      +mr = List.append(&2, Bool, List.concat(&2, Bool, rest), tl)
      +h16 = {M1.also_l(Nat.is_le(ln, 16n), Laws.jpg.codes16(rest), hc) : {Nat.is_le(ln, 16n) == True{} : Bool}}
      +ea = {Equal.trans(List<&2, Bool>, rem(ss), List.append(&2, Bool, List.concat(&2, Bool, cc <> rest), tl),
        List.append(&2, Bool, cc, mr), he, M3.huf.app_assoc(cc, List.concat(&2, Bool, rest), tl)) :
        {rem(ss) == List.append(&2, Bool, cc, mr) : List<&2, Bool>}}
      +hl = {Equal.trans(Bool, Nat.is_le(ln, List.length(&2, Bool, rem(ss))), Nat.is_le(ln, List.length(&2, Bool,
        List.append(&2, Bool, cc, mr))), True{}, Equal.cong(List<&2, Bool>, Bool, xs => Nat.is_le(ln, List.length(&2,
        Bool, xs)), rem(ss), List.append(&2, Bool, cc, mr), ea), len_app(cc, mr)) :
        {Nat.is_le(ln, List.length(&2, Bool, rem(ss))) == True{} : Bool}}
      +s2 = radv(ln, ss)
      +ok2 = {radv_ok(ln, ss, hs, h8) : {Bool.and(rshort(s2), roct8(s2)) == True{} : Bool}}
      +e2 = {Equal.trans(List<&2, Bool>, rem(s2), List.drop(&2, Bool, rem(ss), ln), mr, rem_radv(ln, ss, hs, h8, hl),
        Equal.trans(List<&2, Bool>, List.drop(&2, Bool, rem(ss), ln), List.drop(&2, Bool, List.append(&2, Bool, cc, mr),
        ln), mr, Equal.cong(List<&2, Bool>, List<&2, Bool>, xs => List.drop(&2, Bool, xs, ln), rem(ss),
        List.append(&2, Bool, cc, mr), ea), drop_app(cc, mr))) : {rem(s2) == mr : List<&2, Bool>}}
      +vr = {Equal.trans(U32, M2.vfold(List.take(&2, Bool, rem(ss), ln), 0), M2.vfold(List.take(&2, Bool,
          List.append(&2,
        Bool, cc, mr), ln), 0), Laws.jpg.num(cc, 0), Equal.cong(List<&2, Bool>, U32, xs => M2.vfold(List.take(&2, Bool,
          xs, ln), 0),
        rem(ss), List.append(&2, Bool, cc, mr), ea), Equal.trans(U32, M2.vfold(List.take(&2, Bool, List.append(&2, Bool,
        cc, mr), ln), 0), M2.vfold(cc, 0), Laws.jpg.num(cc, 0), Equal.cong(List<&2, Bool>, U32, xs => M2.vfold(xs, 0),
        List.take(&2, Bool, List.append(&2, Bool, cc, mr), ln), cc, take_app(cc, mr)), Equal.sym(U32, Laws.jpg.num(cc,
          0),
        M2.vfold(cc, 0), num_v(cc, 0)))) : {M2.vfold(List.take(&2, Bool, rem(ss), ln), 0) == Laws.jpg.num(cc, 0) : U32}}
      +er = {Equal.trans(Jpeg.Bits & U32, Jpeg.decode.read.n(nn, rbits(ss, ok)), canon(U32.to_nat(nn), ss, ok, 0),
        (rbits(s2, ok), Laws.jpg.num(cc, 0)), read_canon(nn, ss, ok), Equal.trans(Jpeg.Bits & U32,
          canon(U32.to_nat(nn), ss,
        ok, 0), canon(ln, ss, ok, 0), (rbits(s2, ok), Laws.jpg.num(cc, 0)), Equal.cong(Nat, Jpeg.Bits & U32,
          kk => canon(kk, ss,
        ok, 0), U32.to_nat(nn), ln, tn16(ln, h16)), Equal.trans(Jpeg.Bits & U32, canon(ln, ss, ok, 0), (rbits(s2, ok),
        M2.vfold(List.take(&2, Bool, rem(ss), ln), 0)), (rbits(s2, ok), Laws.jpg.num(cc, 0)), rread(ln, ss, ok, 0, hs,
          h8, hl),
        Equal.cong(U32, Jpeg.Bits & U32, vv => (rbits(s2, ok), vv), M2.vfold(List.take(&2, Bool, rem(ss), ln), 0),
        Laws.jpg.num(cc, 0), vr)))) : {Jpeg.decode.read.n(nn, rbits(ss, ok)) == (rbits(s2, ok), Laws.jpg.num(cc,
          0)) : Jpeg.Bits & U32}}
      Equal.trans(List<&2, U32> & U32, Laws.jpg.rcons(Laws.jpg.got.val(Jpeg.decode.read.n(nn, rbits(ss, ok))),
        Laws.jpg.reads(rest,
        Laws.jpg.got.bits(Jpeg.decode.read.n(nn, rbits(ss, ok))))), Laws.jpg.rcons(Laws.jpg.num(cc, 0),
          Laws.jpg.reads(rest, rbits(s2, ok))),
        (Laws.jpg.nums(cc <> rest), ok), Equal.cong(Jpeg.Bits & U32, List<&2, U32> & U32,
          rr => Laws.jpg.rcons(Laws.jpg.got.val(rr), Laws.jpg.reads(rest,
        Laws.jpg.got.bits(rr))), Jpeg.decode.read.n(nn, rbits(ss, ok)), (rbits(s2, ok), Laws.jpg.num(cc, 0)), er),
        Equal.cong(List<&2, U32> & U32, List<&2, U32> & U32, gg => Laws.jpg.rcons(Laws.jpg.num(cc, 0), gg),
          Laws.jpg.reads(rest, rbits(s2, ok)),
        (Laws.jpg.nums(rest), ok), reads_m(rest, s2, ok, tl, M3.and_l(rshort(s2), roct8(s2), ok2), M3.and_r(rshort(s2),
          roct8(s2),
        ok2), M1.also_r(Nat.is_le(ln, 16n), Laws.jpg.codes16(rest), hc), e2)))

# the 1 bits that pad the last byte after pending bits pp
def padbits(pp: List<&2, Bool>) -> List<&2, Bool>:
  match pp:
    case Nil{}:
      []
    case +hh <> +tt:
      List.replicate(Bool, Nat.sub(8n, List.length(&2, Bool, hh <> tt)), True{})

# the pad after pending bits pp and then bits bs
def mpad(bs: List<&2, Bool>, +pp: List<&2, Bool>) -> List<&2, Bool>:
  match bs:
    case Nil{}:
      padbits(pp)
    case +bb <> rest:
      mpad(rest, mo.next(M2.is7(pp), pp, bb))

# the last byte's bits are the pending bits and the pad
def pendo_concat(
  +pp: List<&2, Bool>
) -> {List.concat(&2, Bool, pendo(pp)) == List.append(&2, Bool, pp, padbits(pp)) : List<&2, Bool>}:
  match pp:
    case Nil{}:
      {==}
    case +hh <> +tt:
      M3.huf.app_nil(List.append(&2, Bool, hh <> tt, List.replicate(Bool, Nat.sub(8n, List.length(&2, Bool, hh <> tt)),
        True{})))

# a byte one more bit may finish goes before the bytes after it, bit for bit
def join_concat(
  full: Bool,
  +pp: List<&2, Bool>,
  +bb: Bool,
  +mm: List<&2, List<&2, Bool>>,
  +xs: List<&2, Bool>,
  +hm: {List.concat(&2, Bool, mm) == List.append(&2, Bool, mo.next(full, pp, bb), xs) : List<&2, Bool>}
) -> {List.concat(&2, Bool, mo.join(full, pp, bb, mm)) == List.append(&2, Bool, pp, bb <> xs) : List<&2, Bool>}:
  match full:
    case True{}:
      Equal.trans(List<&2, Bool>, List.append(&2, Bool, List.append(&2, Bool, pp, [bb]), List.concat(&2, Bool, mm)),
        List.append(&2, Bool, List.append(&2, Bool, pp, [bb]), xs), List.append(&2, Bool, pp, bb <> xs),
        Equal.cong(List<&2, Bool>, List<&2, Bool>, ws => List.append(&2, Bool, List.append(&2, Bool, pp, [bb]), ws),
        List.concat(&2, Bool, mm), xs, hm), M3.huf.app_assoc(pp, [bb], xs))
    case False{}:
      Equal.trans(List<&2, Bool>, List.concat(&2, Bool, mm), List.append(&2, Bool, List.append(&2, Bool, pp, [bb]), xs),
        List.append(&2, Bool, pp, bb <> xs), hm, M3.huf.app_assoc(pp, [bb], xs))

# the model's bytes, bit for bit, are the pending bits, the bits, and the pad
def concat_moct(
  bs: List<&2, Bool>,
  +pp: List<&2, Bool>
) -> {List.concat(&2, Bool, moct(bs, pp)) == List.append(&2, Bool, pp, List.append(&2, Bool, bs, mpad(bs,
  pp))) : List<&2, Bool>}:
  match bs:
    case Nil{}:
      pendo_concat(pp)
    case +bb <> +rest:
      +fl = M2.is7(pp)
      +p2 = mo.next(fl, pp, bb)
      join_concat(fl, pp, bb, moct(rest, p2), List.append(&2, Bool, rest, mpad(rest, p2)), concat_moct(rest, p2))

# a byte one more bit finishes has 8 bits
def join_oct8(
  pp: List<&2, Bool>,
  bb: Bool,
  mm: List<&2, List<&2, Bool>>,
  hs: {M2.short(pp) == True{} : Bool},
  hm: {oct8(mm) == True{} : Bool}
) -> {oct8(mo.join(M2.is7(pp), pp, bb, mm)) == True{} : Bool}:
  match pp:
    case Nil{}:
      hm
    case +p0 <> t0:
      match t0:
        case Nil{}:
          hm
        case +p1 <> t1:
          match t1:
            case Nil{}:
              hm
            case +p2 <> t2:
              match t2:
                case Nil{}:
                  hm
                case +p3 <> t3:
                  match t3:
                    case Nil{}:
                      hm
                    case +p4 <> t4:
                      match t4:
                        case Nil{}:
                          hm
                        case +p5 <> t5:
                          match t5:
                            case Nil{}:
                              hm
                            case +p6 <> t6:
                              match t6:
                                case Nil{}:
                                  hm
                                case +p7 <> t7:
                                  Empty.absurd({oct8(mo.join(M2.is7(p0 <> p1 <> p2 <> p3 <> p4 <> p5 <> p6 <> p7 <> t7),
                                    p0 <> p1 <> p2 <> p3 <> p4 <> p5 <> p6 <> p7 <> t7, bb, mm)) == True{} : Bool},
                                    M2.long8(t7, hs))

# the last byte has 8 bits
def pendo_oct8(pp: List<&2, Bool>, hs: {M2.short(pp) == True{} : Bool}) -> {oct8(pendo(pp)) == True{} : Bool}:
  match pp:
    case Nil{}:
      {==}
    case +p0 <> t0:
      match t0:
        case Nil{}:
          {==}
        case +p1 <> t1:
          match t1:
            case Nil{}:
              {==}
            case +p2 <> t2:
              match t2:
                case Nil{}:
                  {==}
                case +p3 <> t3:
                  match t3:
                    case Nil{}:
                      {==}
                    case +p4 <> t4:
                      match t4:
                        case Nil{}:
                          {==}
                        case +p5 <> t5:
                          match t5:
                            case Nil{}:
                              {==}
                            case +p6 <> t6:
                              match t6:
                                case Nil{}:
                                  {==}
                                case +p7 <> t7:
                                  Empty.absurd({oct8(pendo(p0 <> p1 <> p2 <> p3 <> p4 <> p5 <> p6 <> p7 <> t7)) ==
                                    True{} : Bool}, M2.long8(t7, hs))

# every byte of the model has 8 bits
def oct8_moct(
  bs: List<&2, Bool>,
  +pp: List<&2, Bool>,
  +hs: {M2.short(pp) == True{} : Bool}
) -> {oct8(moct(bs, pp)) == True{} : Bool}:
  match bs:
    case Nil{}:
      pendo_oct8(pp, hs)
    case +bb <> +rest:
      +fl = M2.is7(pp)
      +p2 = mo.next(fl, pp, bb)
      join_oct8(pp, bb, moct(rest, p2), hs, oct8_moct(rest, p2, next_short(pp, bb, hs)))

# the bit round trip: codes of at most 16 bits written and padded, then read back one length at a time
def round_trip(
  +cs: List<&2, List<&2, Bool>>,
  +hc: {Laws.jpg.codes16(cs) == True{} : Bool}
) -> {Laws.jpg.reads(cs, Jpeg.Bits{0, 1, 0, Jenc.encode.pad(Laws.jpg.write(cs,
  Jenc.encode.put0()))}) == (Laws.jpg.nums(cs), 1) : List<&2, U32> & U32}:
  +bs = List.concat(&2, Bool, cs)
  +os = moct(bs, [])
  +ep = {Equal.trans(List<&2, U32>, Jenc.encode.pad(Laws.jpg.write(cs, Jenc.encode.put0())),
    Jenc.encode.pad(Laws.jpg.feed(bs,
    Jenc.encode.put0())), rxs(os), Equal.cong(Jenc.Put, List<&2, U32>, qq => Jenc.encode.pad(qq), Laws.jpg.write(cs,
    Jenc.encode.put0()), Laws.jpg.feed(bs, Jenc.encode.put0()), wcodes_feed(cs, Jenc.encode.put0(), hc)),
    Equal.trans(List<&2, U32>, Jenc.encode.pad(Laws.jpg.feed(bs, M2.wput(M2.WS{[], []}))),
        Jenc.encode.pad(M2.wput(M2.wm(bs,
      M2.WS{[], []}))),
    rxs(os), Equal.cong(Jenc.Put, List<&2, U32>, qq => Jenc.encode.pad(qq), Laws.jpg.feed(bs, M2.wput(M2.WS{[], []})),
    M2.wput(M2.wm(bs, M2.WS{[], []})), M2.wfeed(bs, M2.WS{[], []}, {==})), pad_m(bs, [], [], {==}))) :
    {Jenc.encode.pad(Laws.jpg.write(cs, Jenc.encode.put0())) == rxs(os) : List<&2, U32>}}
  Equal.trans(List<&2, U32> & U32, Laws.jpg.reads(cs, Jpeg.Bits{0, 1, 0, Jenc.encode.pad(Laws.jpg.write(cs,
    Jenc.encode.put0()))}),
    Laws.jpg.reads(cs, rbits(RS{[], os}, 1)), (Laws.jpg.nums(cs), 1), Equal.cong(List<&2, U32>, List<&2, U32> & U32,
      xs => Laws.jpg.reads(cs,
    Jpeg.Bits{0, 1, 0, xs}), Jenc.encode.pad(Laws.jpg.write(cs, Jenc.encode.put0())), rxs(os), ep),
    reads_m(cs, RS{[], os}, 1, mpad(bs, []), {==}, oct8_moct(bs, [], {==}), hc, concat_moct(bs, [])))

# the bit reader's loop with nothing left to read hands back the model's reader
def canon0(ss: RS, +ok: U32, +acc: U32) -> {canon(0n, ss, ok, acc) == (rbits(ss, ok), acc) : Jpeg.Bits & U32}:
  match ss:
    case RS{_qq, _os}:
      {==}

# one bit read from the model's reader is the bit reader's loop for one bit
def one_canon(ss: RS, +ok: U32) -> {Jpeg.decode.one(rbits(ss, ok)) == canon(1n, ss, ok, 0) : Jpeg.Bits & U32}:
  match ss:
    case RS{_qq, _os}:
      {==}

# the ask of one bit, once the bit is read
def ask.of(
  +cs: List<&2, U32>,
  +ls: List<&2, U32>,
  +ys: List<&2, U32>,
  +code: U32,
  +len: U32,
  bits: Jpeg.Bits,
  +bb: Bool
) -> {Jpeg.decode.ask.bit(Jpeg.Huff{cs, ls, ys}, (bits, M6.vstep(0, bb)), code, len) == Jpeg.Ask{Jpeg.decode.look(cs,
    ls,
  ys, M6.vstep(code, bb), (len + 1 : U32)), M6.vstep(code, bb), (len + 1 : U32), bits} : Jpeg.Ask}:
  Equal.cong(U32, Jpeg.Ask, xx => Jpeg.Ask{Jpeg.decode.look(cs, ls, ys, xx, (len + 1 : U32)), xx, (len + 1 : U32),
    bits}, U32.or(U32.shl(code), Laws.jpg.ubit(bb)), M6.vstep(code, bb), M2.or_shl_u(code, bb))

# one bit asked of the table from the model reader
def ask_step(
  +ss: RS,
  +ok: U32,
  +code: U32,
  +len: U32,
  +cs: List<&2, U32>,
  +ls: List<&2, U32>,
  +ys: List<&2, U32>,
  hs: {rshort(ss) == True{} : Bool},
  h8: {roct8(ss) == True{} : Bool},
  hn: {rsome(ss) == True{} : Bool}
) -> {Jpeg.decode.ask(rbits(ss, ok), code, len, Jpeg.Huff{cs, ls, ys}) == Jpeg.Ask{Jpeg.decode.look(cs, ls, ys,
  M6.vstep(code, rhead(ss)), (len + 1 : U32)), M6.vstep(code, rhead(ss)), (len + 1 : U32), rbits(rnext(ss), ok)} : Jpeg.Ask}:  # noqa: S002
  +hh = {Jpeg.Huff{cs, ls, ys} : Jpeg.Huff}
  +nx = rnext(ss)
  +bb = rhead(ss)
  Equal.trans(Jpeg.Ask, Jpeg.decode.ask.bit(hh, Jpeg.decode.one(rbits(ss, ok)), code, len),
    Jpeg.decode.ask.bit(hh, (rbits(nx, ok), M6.vstep(0, bb)), code, len), Jpeg.Ask{Jpeg.decode.look(cs, ls, ys,
    M6.vstep(code, bb), (len + 1 : U32)), M6.vstep(code, bb), (len + 1 : U32), rbits(nx, ok)},
    Equal.cong(Jpeg.Bits & U32, Jpeg.Ask, gg => Jpeg.decode.ask.bit(hh, gg, code, len), Jpeg.decode.one(rbits(ss,
    ok)), (rbits(nx, ok), M6.vstep(0, bb)), Equal.trans(Jpeg.Bits & U32, Jpeg.decode.one(rbits(ss, ok)),
    canon(1n, ss, ok, 0), (rbits(nx, ok), M6.vstep(0, bb)), one_canon(ss, ok), Equal.trans(Jpeg.Bits & U32,
    canon(1n, ss, ok, 0), canon(0n, nx, ok, M6.vstep(0, bb)), (rbits(nx, ok), M6.vstep(0, bb)),
    rstep(0n, ss, ok, 0, hs, h8, hn), canon0(nx, ok, M6.vstep(0, bb))))),
    ask.of(cs, ls, ys, code, len, rbits(nx, ok), bb))

# the head of a list of bits, False when empty
def lhead(xs: List<&2, Bool>) -> Bool:
  match xs:
    case hh <> _t:
      hh
    case Nil{}:
      False{}

# the tail of a list of bits
def ltail(xs: List<&2, Bool>) -> List<&2, Bool>:
  match xs:
    case _h <> tt:
      tt
    case Nil{}:
      []

# the decoder's answer a walk stands for: the symbol and the reader past its bits, or a miss
def hwres(rr: M6.HW, ss: RS, +ok: U32) -> Jpeg.Hit:
  match rr:
    case M6.HWHit{+sym, +nn}:
      Jpeg.Hit{sym, rbits(radv(nn, ss), ok), ok}
    case M6.HWMiss{}:
      Jpeg.Hit{0, rbits(ss, ok), 0}

# a walk that hits within left asks
def hw.fits(rr: M6.HW, +left: Nat) -> Bool:
  match rr:
    case M6.HWHit{_s, +nn}:
      Nat.is_le(nn, left)
    case M6.HWMiss{}:
      False{}

# a hit's symbol handed on with the model's reader
def use_some(
  +sym: U32,
  ss: RS,
  +ok: U32
) -> {Jpeg.decode.huff.use(Some{sym}, rbits(ss, ok)) == Jpeg.Hit{sym, rbits(ss, ok), ok} : Jpeg.Hit}:
  match ss:
    case RS{_qq, _os}:
      {==}

# no walk fits in zero asks
def pick_pos(look: Maybe<&2, U32>, rest: M6.HW, hf: {hw.fits(M6.hw.pick(look, rest), 0n) == True{} : Bool}) -> Empty:
  match look:
    case Some{_s}:
      M1.huf.false_true(hf)
    case None{}:
      match rest:
        case M6.HWHit{_s, _n}:
          M1.huf.false_true(hf)
        case M6.HWMiss{}:
          M1.huf.false_true(hf)

# the walk over the bits after the first, as the lookup after one bit needs it
def HwIh(-rest: M6.HW, +_lf: Nat, -s0: RS, +_ok: U32, +_cd: U32, +_ln: U32, -tab: Jpeg.Huff) -> Type:
  @hr: {hw.fits(rest, _lf) == True{} : Bool} -> {Jpeg.decode.huff(_lf, Jpeg.Ask{None{}, _cd, _ln,
    rbits(rnext(s0), _ok)}, tab) == hwres(rest, rnext(s0), _ok) : Jpeg.Hit}

# the decoder's lookup after one bit, by the table's answer at that length
def hw.case(
  look: Maybe<&2, U32>,
  rest: M6.HW,
  left: Nat,
  +s0: RS,
  +ok: U32,
  +code: U32,
  +len: U32,
  +tab: Jpeg.Huff,
  hf: {hw.fits(M6.hw.pick(look, rest), 1n+left) == True{} : Bool},
  ih: HwIh(rest, left, s0, ok, code, len, tab)
) -> {Jpeg.decode.huff(left, Jpeg.Ask{look, code, len, rbits(rnext(s0), ok)}, tab) == hwres(M6.hw.pick(look, rest), s0,
  ok) : Jpeg.Hit}:
  match look:
    case Some{+sym}:
      match left:
        case 0n:
          use_some(sym, rnext(s0), ok)
        case 1n+_q:
          use_some(sym, rnext(s0), ok)
    case None{}:
      match rest:
        case M6.HWHit{+s2, +nn}:
          ih(hf)
        case M6.HWMiss{}:
          Empty.absurd({Jpeg.decode.huff(left, Jpeg.Ask{None{}, code, len, rbits(rnext(s0), ok)}, tab) ==
            hwres(M6.HWMiss{}, s0, ok) : Jpeg.Hit}, M1.huf.false_true(hf))

# the decoder's Huffman lookup from the model's reader holding bits bs and more is the walk over bs
def hwalk(
  bs: List<&2, Bool>,
  left: Nat,
  +ss: RS,
  +ok: U32,
  +code: U32,
  +len: U32,
  +cs: List<&2, U32>,
  +ls: List<&2, U32>,
  +ys: List<&2, U32>,
  +tl: List<&2, Bool>,
  +hs: {rshort(ss) == True{} : Bool},
  +h8: {roct8(ss) == True{} : Bool},
  +he: {rem(ss) == List.append(&2, Bool, bs, tl) : List<&2, Bool>},
  hf: {hw.fits(M6.hw(bs, Jpeg.Huff{cs, ls, ys}, code, len), left) == True{} : Bool}
) -> {Jpeg.decode.huff(left, Jpeg.Ask{None{}, code, len, rbits(ss, ok)}, Jpeg.Huff{cs, ls, ys}) == hwres(M6.hw(bs,
  Jpeg.Huff{cs, ls, ys}, code, len), ss, ok) : Jpeg.Hit}:
  match bs:
    case Nil{}:
      Empty.absurd({Jpeg.decode.huff(left, Jpeg.Ask{None{}, code, len, rbits(ss, ok)}, Jpeg.Huff{cs, ls, ys}) ==
        hwres(M6.HWMiss{}, ss, ok) : Jpeg.Hit}, M1.huf.false_true(hf))
    case +bb <> +rest:
      match left:
        case 0n:
          +tab = {Jpeg.Huff{cs, ls, ys} : Jpeg.Huff}
          +c2 = M6.vstep(code, bb)
          +l2 = (len + 1 : U32)
          Empty.absurd({Jpeg.decode.huff(0n, Jpeg.Ask{None{}, code, len, rbits(ss, ok)}, tab) ==
            hwres(M6.hw(bb <> rest, tab, code, len), ss, ok) : Jpeg.Hit}, pick_pos(Jpeg.decode.look(cs, ls, ys, c2, l2),
            M6.hw(rest, tab, c2, l2), hf))
        case 1n+ +pp:
          +tab = {Jpeg.Huff{cs, ls, ys} : Jpeg.Huff}
          +c2 = M6.vstep(code, bb)
          +l2 = (len + 1 : U32)
          +lk = Jpeg.decode.look(cs, ls, ys, c2, l2)
          +nx = rnext(ss)
          +hn = {Equal.cong(List<&2, Bool>, Bool, xs => Nat.is_lt(0n, List.length(&2, Bool, xs)), rem(ss),
            bb <> List.append(&2, Bool, rest, tl), he) : {rsome(ss) == True{} : Bool}}
          +ec = {Equal.trans(List<&2, Bool>, rhead(ss) <> rem(nx), rem(ss), bb <> List.append(&2, Bool, rest,
            tl), Equal.sym(List<&2, Bool>, rem(ss), rhead(ss) <> rem(nx), rem_cons(ss, h8, hn)), he) :
            {rhead(ss) <> rem(nx) == bb <> List.append(&2, Bool, rest, tl) : List<&2, Bool>}}
          +eh = {Equal.cong(List<&2, Bool>, Bool, xs => lhead(xs), rhead(ss) <> rem(nx), bb <> List.append(&2,
            Bool, rest, tl), ec) : {rhead(ss) == bb : Bool}}
          +et = {Equal.cong(List<&2, Bool>, List<&2, Bool>, xs => ltail(xs), rhead(ss) <> rem(nx), bb <>
            List.append(&2, Bool, rest, tl), ec) : {rem(nx) == List.append(&2, Bool, rest, tl) : List<&2, Bool>}}
          Equal.trans(Jpeg.Hit, Jpeg.decode.huff(pp, Jpeg.decode.ask(rbits(ss, ok), code, len, tab), tab),
            Jpeg.decode.huff(pp, Jpeg.Ask{lk, c2, l2, rbits(nx, ok)}, tab), hwres(M6.hw(bb <> rest, tab, code, len), ss,
            ok), Equal.cong(Jpeg.Ask, Jpeg.Hit, aa => Jpeg.decode.huff(pp, aa, tab), Jpeg.decode.ask(rbits(ss, ok),
            code, len, tab), Jpeg.Ask{lk, c2, l2, rbits(nx, ok)}, Equal.trans(Jpeg.Ask, Jpeg.decode.ask(rbits(ss,
            ok), code, len, tab), Jpeg.Ask{Jpeg.decode.look(cs, ls, ys, M6.vstep(code, rhead(ss)), l2),
            M6.vstep(code, rhead(ss)), l2, rbits(nx, ok)}, Jpeg.Ask{lk, c2, l2, rbits(nx, ok)},
            ask_step(ss, ok, code, len, cs, ls, ys, hs, h8, hn), Equal.cong(Bool, Jpeg.Ask, xb =>
            Jpeg.Ask{Jpeg.decode.look(cs, ls, ys, M6.vstep(code, xb), l2), M6.vstep(code, xb), l2, rbits(nx, ok)},
            rhead(ss), bb, eh))),
            hw.case(lk, M6.hw(rest, tab, c2, l2), pp, ss, ok, c2, l2, tab, hf, hr => hwalk(rest, pp, nx, ok, c2, l2, cs,
            ls, ys, tl, rnext_short(ss, hs, h8), rnext_oct8(ss, h8), et, hr)))

# the first answer, else the second
def orelse(aa: Maybe<&2, U32>, bb: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match aa:
    case Some{+vv}:
      match bb:
        case _b:
          Some{vv}
    case None{}:
      bb

# three lists of one length
def sm3(cs: List<&2, U32>, ls: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match cs ls ys:
    case Nil{} Nil{} Nil{}:
      True{}
    case _c <> ct _l <> lt _y <> yt:
      sm3(ct, lt, yt)
    case _ _ _:
      False{}

# none second is the first
def orelse_none(aa: Maybe<&2, U32>) -> {aa == orelse(aa, None{}) : Maybe<&2, U32>}:
  match aa:
    case Some{_v}:
      {==}
    case None{}:
      {==}

# a lookup's answer before one more entry, over a join
def pref_orelse(
  aa: Maybe<&2, U32>,
  bb: Maybe<&2, U32>,
  eqc: Bool,
  eql: Bool,
  +ss: U32
) -> {Jpeg.decode.look.pref(orelse(aa, bb), eqc, eql, ss) == orelse(aa, Jpeg.decode.look.pref(bb, eqc, eql,
  ss)) : Maybe<&2, U32>}:
  match aa:
    case Some{_v}:
      match bb:
        case Some{_w}:
          match eqc:
            case True{}:
              match eql:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match eql:
                case True{}:
                  {==}
                case False{}:
                  {==}
        case None{}:
          match eqc:
            case True{}:
              match eql:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match eql:
                case True{}:
                  {==}
                case False{}:
                  {==}
    case None{}:
      {==}

# the decoder's lookup over joined lists: the later lists' answer, else the earlier ones'
def look_app(
  c1: List<&2, U32>,
  l1: List<&2, U32>,
  s1: List<&2, U32>,
  +c2: List<&2, U32>,
  +l2: List<&2, U32>,
  +s2: List<&2, U32>,
  +code: U32,
  +len: U32,
  hh: {sm3(c1, l1, s1) == True{} : Bool}
) -> {Jpeg.decode.look(List.append(&2, U32, c1, c2), List.append(&2, U32, l1, l2), List.append(&2, U32, s1, s2), code,
  len) == orelse(Jpeg.decode.look(c2, l2, s2, code, len), Jpeg.decode.look(c1, l1, s1, code, len)) : Maybe<&2, U32>}:
  match c1:
    case Nil{}:
      match l1:
        case Nil{}:
          match s1:
            case Nil{}:
              orelse_none(Jpeg.decode.look(c2, l2, s2, code, len))
            case _y <> _yt:
              Empty.absurd({Jpeg.decode.look(c2, l2, List.append(&2, U32, _y <> _yt, s2), code, len) ==
                orelse(Jpeg.decode.look(c2, l2, s2, code, len), None{}) : Maybe<&2, U32>}, M1.huf.false_true(hh))
        case _l <> _lt:
          Empty.absurd({Jpeg.decode.look(c2, List.append(&2, U32, _l <> _lt, l2), List.append(&2, U32, s1, s2), code,
            len) == orelse(Jpeg.decode.look(c2, l2, s2, code, len), Jpeg.decode.look([], _l <> _lt, s1, code, len)) :
            Maybe<&2, U32>}, M1.huf.false_true(hh))
    case +cc <> +ct:
      match l1:
        case Nil{}:
          Empty.absurd({Jpeg.decode.look(cc <> List.append(&2, U32, ct, c2), l2, List.append(&2, U32, s1, s2), code,
            len) == orelse(Jpeg.decode.look(c2, l2, s2, code, len), Jpeg.decode.look(cc <> ct, [], s1, code, len)) :
            Maybe<&2, U32>}, M1.huf.false_true(hh))
        case +ll <> +lt:
          match s1:
            case Nil{}:
              Empty.absurd({Jpeg.decode.look(cc <> List.append(&2, U32, ct, c2), ll <> List.append(&2, U32, lt, l2),
                s2, code, len) == orelse(Jpeg.decode.look(c2, l2, s2, code, len), Jpeg.decode.look(cc <> ct, ll <> lt,
                [], code, len)) : Maybe<&2, U32>}, M1.huf.false_true(hh))
            case +sy <> +st:
              +eqc = U32.is_eq(cc, code)
              +eql = U32.is_eq(ll, len)
              +aa = Jpeg.decode.look(c2, l2, s2, code, len)
              +bb = Jpeg.decode.look(ct, lt, st, code, len)
              Equal.trans(Maybe<&2, U32>, Jpeg.decode.look.pref(Jpeg.decode.look(List.append(&2, U32, ct, c2),
                List.append(&2, U32, lt, l2), List.append(&2, U32, st, s2), code, len), eqc, eql, sy),
                Jpeg.decode.look.pref(orelse(aa, bb), eqc, eql, sy), orelse(aa, Jpeg.decode.look.pref(bb, eqc, eql,
                sy)), Equal.cong(Maybe<&2, U32>, Maybe<&2, U32>, mm => Jpeg.decode.look.pref(mm, eqc, eql, sy),
                Jpeg.decode.look(List.append(&2, U32, ct, c2), List.append(&2, U32, lt, l2), List.append(&2, U32, st,
                s2), code, len), orelse(aa, bb), look_app(ct, lt, st, c2, l2, s2, code, len, hh)),
                pref_orelse(aa, bb, eqc, eql, sy))

# the groups' codes
def gc(gs: List<&2, M1.HG>) -> List<&2, U32>:
  match gs:
    case Nil{}:
      []
    case M1.HG{_l, cs, _y} <> rest:
      List.append(&2, U32, cs, gc(rest))

# the groups' symbols
def gsy(gs: List<&2, M1.HG>) -> List<&2, U32>:
  match gs:
    case Nil{}:
      []
    case M1.HG{_l, _c, ys} <> rest:
      List.append(&2, U32, ys, gsy(rest))

# every group has as many symbols as codes
def wfg(gs: List<&2, M1.HG>) -> Bool:
  match gs:
    case Nil{}:
      True{}
    case M1.HG{+ln, +cs, ys} <> rest:
      Laws.jpg.also(sm3(cs, List.replicate(U32, List.length(&2, U32, cs), ln), ys), wfg(rest))

# one group's answer: asked only when its length is the one sought
def lookgrp(eq: Bool, +ln: U32, cs: List<&2, U32>, ys: List<&2, U32>, +code: U32, +len: U32) -> Maybe<&2, U32>:
  match eq:
    case True{}:
      +cc = cs
      Jpeg.decode.look(cc, List.replicate(U32, List.length(&2, U32, cc), ln), ys, code, len)
    case False{}:
      match cs:
        case _c:
          match ys:
            case _y:
              None{}

# the lookup over groups: the later groups' answer, else this group's
def lookg(gs: List<&2, M1.HG>, +code: U32, +len: U32) -> Maybe<&2, U32>:
  match gs:
    case Nil{}:
      None{}
    case M1.HG{+ln, cs, ys} <> rest:
      orelse(lookg(rest, code, len), lookgrp(U32.is_eq(ln, len), ln, cs, ys, code, len))

# no entry of another length answers
def pref_nf(eqc: Bool, +ss: U32) -> {Jpeg.decode.look.pref(None{}, eqc, False{}, ss) == None{} : Maybe<&2, U32>}:
  match eqc:
    case True{}:
      {==}
    case False{}:
      {==}

# a lookup over codes all of another length finds nothing
def look_rep_none(
  cs: List<&2, U32>,
  ys: List<&2, U32>,
  +ln: U32,
  +code: U32,
  +len: U32,
  +hh: {U32.is_eq(ln, len) == False{} : Bool}
) -> {Jpeg.decode.look(cs, List.replicate(U32, List.length(&2, U32, cs), ln), ys, code, len) == None{} : Maybe<&2,
  U32>}:
  match cs:
    case Nil{}:
      match ys:
        case Nil{}:
          {==}
        case _y <> _t:
          {==}
    case +cc <> ct:
      match ys:
        case Nil{}:
          +_c = ct
          {==}
        case +sy <> st:
          +ih = look_rep_none(ct, st, ln, code, len, hh)
          Equal.trans(Maybe<&2, U32>, Jpeg.decode.look.pref(Jpeg.decode.look(ct, List.replicate(U32, List.length(&2,
            U32, ct), ln), st, code, len), U32.is_eq(cc, code), U32.is_eq(ln, len), sy),
            Jpeg.decode.look.pref(None{}, U32.is_eq(cc, code), False{}, sy), None{},
            Equal.trans(Maybe<&2, U32>, Jpeg.decode.look.pref(Jpeg.decode.look(ct, List.replicate(U32,
            List.length(&2, U32, ct), ln), st, code, len), U32.is_eq(cc, code), U32.is_eq(ln, len), sy),
            Jpeg.decode.look.pref(None{}, U32.is_eq(cc, code), U32.is_eq(ln, len), sy),
            Jpeg.decode.look.pref(None{}, U32.is_eq(cc, code), False{}, sy), Equal.cong(Maybe<&2, U32>,
            Maybe<&2, U32>, mm => Jpeg.decode.look.pref(mm, U32.is_eq(cc, code), U32.is_eq(ln, len), sy),
            Jpeg.decode.look(ct, List.replicate(U32, List.length(&2, U32, ct), ln), st, code, len), None{}, ih),
            Equal.cong(Bool, Maybe<&2, U32>, bb => Jpeg.decode.look.pref(None{}, U32.is_eq(cc, code), bb, sy),
            U32.is_eq(ln, len), False{}, hh)), pref_nf(U32.is_eq(cc, code), sy))

# one group's answer is the lookup over its codes
def lookgrp_eq(
  eq: Bool,
  +ln: U32,
  +cs: List<&2, U32>,
  +ys: List<&2, U32>,
  +code: U32,
  +len: U32,
  +he: {U32.is_eq(ln, len) == eq : Bool}
) -> {Jpeg.decode.look(cs, List.replicate(U32, List.length(&2, U32, cs), ln), ys, code, len) == lookgrp(eq, ln, cs,
  ys, code, len) : Maybe<&2, U32>}:
  match eq:
    case True{}:
      {==}
    case False{}:
      look_rep_none(cs, ys, ln, code, len, he)

# the decoder's lookup over a table in groups is the lookup over groups
def look_g(
  gs: List<&2, M1.HG>,
  +code: U32,
  +len: U32,
  +hh: {wfg(gs) == True{} : Bool}
) -> {Jpeg.decode.look(gc(gs), M1.gl(gs), gsy(gs), code, len) == lookg(gs, code, len) : Maybe<&2, U32>}:
  match gs:
    case Nil{}:
      {==}
    case M1.HG{+ln, +cs, +ys} <> +rest:
      +rp = List.replicate(U32, List.length(&2, U32, cs), ln)
      Equal.trans(Maybe<&2, U32>, Jpeg.decode.look(List.append(&2, U32, cs, gc(rest)), List.append(&2, U32, rp,
        M1.gl(rest)),
        List.append(&2, U32, ys, gsy(rest)), code, len), orelse(Jpeg.decode.look(gc(rest), M1.gl(rest), gsy(rest), code,
          len),
        Jpeg.decode.look(cs, rp, ys, code, len)), lookg(M1.HG{ln, cs, ys} <> rest, code, len),
        look_app(cs, rp, ys, gc(rest), M1.gl(rest), gsy(rest), code, len, M1.also_l(sm3(cs, rp, ys), wfg(rest), hh)),
        Equal.trans(Maybe<&2, U32>, orelse(Jpeg.decode.look(gc(rest), M1.gl(rest), gsy(rest), code, len),
        Jpeg.decode.look(cs, rp, ys, code, len)), orelse(lookg(rest, code, len), Jpeg.decode.look(cs, rp, ys, code,
          len)),
        lookg(M1.HG{ln, cs, ys} <> rest, code, len), Equal.cong(Maybe<&2, U32>, Maybe<&2, U32>, mm => orelse(mm,
        Jpeg.decode.look(cs, rp, ys, code, len)), Jpeg.decode.look(gc(rest), M1.gl(rest), gsy(rest), code, len),
        lookg(rest, code, len), look_g(rest, code, len, M1.also_r(sm3(cs, rp, ys), wfg(rest), hh))),
        Equal.cong(Maybe<&2, U32>, Maybe<&2, U32>, mm => orelse(lookg(rest, code, len), mm), Jpeg.decode.look(cs, rp,
        ys, code, len), lookgrp(U32.is_eq(ln, len), ln, cs, ys, code, len), lookgrp_eq(U32.is_eq(ln, len), ln, cs, ys,
        code, len, {==}))))

# the walk with the lookup over groups
def hwg(bs: List<&2, Bool>, +gs: List<&2, M1.HG>, +code: U32, +len: U32) -> M6.HW:
  match bs:
    case Nil{}:
      M6.HWMiss{}
    case +bb <> rest:
      M6.hw.pick(lookg(gs, M6.vstep(code, bb), (len + 1 : U32)), hwg(rest, gs, M6.vstep(code, bb), (len + 1 : U32)))

# the walk over a table in groups is the walk with the lookup over groups
def hw_g(
  bs: List<&2, Bool>,
  +gs: List<&2, M1.HG>,
  +code: U32,
  +len: U32,
  +hh: {wfg(gs) == True{} : Bool}
) -> {M6.hw(bs, Jpeg.Huff{gc(gs), M1.gl(gs), gsy(gs)}, code, len) == hwg(bs, gs, code, len) : M6.HW}:
  match bs:
    case Nil{}:
      {==}
    case +bb <> rest:
      +c2 = M6.vstep(code, bb)
      +l2 = (len + 1 : U32)
      Equal.trans(M6.HW, M6.hw.pick(Jpeg.decode.look(gc(gs), M1.gl(gs), gsy(gs), c2, l2), M6.hw(rest, Jpeg.Huff{gc(gs),
          M1.gl(gs),
        gsy(gs)}, c2, l2)), M6.hw.pick(lookg(gs, c2, l2), M6.hw(rest, Jpeg.Huff{gc(gs), M1.gl(gs), gsy(gs)}, c2, l2)),
        hwg(bb <> rest, gs, code, len), Equal.cong(Maybe<&2, U32>, M6.HW, mm => M6.hw.pick(mm, M6.hw(rest,
            Jpeg.Huff{gc(gs),
        M1.gl(gs), gsy(gs)}, c2, l2)), Jpeg.decode.look(gc(gs), M1.gl(gs), gsy(gs), c2, l2), lookg(gs, c2, l2),
            look_g(gs,
        c2, l2, hh)), Equal.cong(M6.HW, M6.HW, rr => M6.hw.pick(lookg(gs, c2, l2), rr), M6.hw(rest, Jpeg.Huff{gc(gs),
            M1.gl(gs),
        gsy(gs)}, c2, l2), hwg(rest, gs, c2, l2), hw_g(rest, gs, c2, l2, hh)))

# a walk that hit symbol ss after nn bits
def hw.is(rr: M6.HW, +ss: U32, +nn: Nat) -> Bool:
  match rr:
    case M6.HWHit{+tt, +jj}:
      Bool.and(U32.is_eq(tt, ss), Nat.is_eq(jj, nn))
    case M6.HWMiss{}:
      False{}

# a symbol's code, at most 16 bits, walked over the table in groups, hits the symbol at its last bit
def hwchk(+cc: List<&2, Bool>, +gs: List<&2, M1.HG>, +ss: U32) -> Bool:
  Bool.and(Nat.is_le(List.length(&2, Bool, cc), 16n), hw.is(hwg(cc, gs, 0, 0), ss, List.length(&2, Bool, cc)))

# a walk known to hit symbol ss after nn bits
def hwis(rr: M6.HW, +ss: U32, +nn: Nat, +hh: {hw.is(rr, ss, nn) == True{} : Bool}) -> {rr == M6.HWHit{ss, nn} : M6.HW}:
  match rr:
    case M6.HWHit{+tt, +jj}:
      +et = {M1.ueq(tt, ss, M3.and_l(U32.is_eq(tt, ss), Nat.is_eq(jj, nn), hh)) : {tt == ss : U32}}
      +ej = {M1.ras.nat_eq_true(jj, nn, M3.and_r(U32.is_eq(tt, ss), Nat.is_eq(jj, nn), hh)) : {jj == nn : Nat}}
      Equal.trans(M6.HW, M6.HWHit{tt, jj}, M6.HWHit{ss, jj}, M6.HWHit{ss, nn}, Equal.cong(U32, M6.HW, xx =>
        M6.HWHit{xx, jj}, tt, ss, et), Equal.cong(Nat, M6.HW, xx => M6.HWHit{ss, xx}, jj, nn, ej))
    case M6.HWMiss{}:
      Empty.absurd({M6.HWMiss{} == M6.HWHit{ss, nn} : M6.HW}, M1.huf.false_true(hh))

# the dc table the decoder builds, in groups of one code length
def dcgrp() -> List<&2, M1.HG>:
  [M1.HG{2, [0], [0]}, M1.HG{3, [2, 3, 4, 5, 6], [1, 2, 3, 4, 5]}, M1.HG{4, [14], [6]}, M1.HG{5, [30], [7]},
    M1.HG{6, [62], [8]}, M1.HG{7, [126], [9]}, M1.HG{8, [254], [10]}, M1.HG{9, [510], [11]}]

# the statement of dctab.eq
def dctab.eq.ty() -> Type:
  {Jpeg.decode.canon(272n, 0n, Jenc.encode.dccounts(), Jenc.encode.dcsyms(), 0, 0, [], [],
    []) == Jpeg.Huff{gc(dcgrp()), M1.gl(dcgrp()), gsy(dcgrp())} : Jpeg.Huff}

# the decoder's table is the groups'
def dctab.eq() -> dctab.eq.ty():
  {==}

# the dc table in groups, as the decoder holds it
def dctab() -> Jpeg.Huff:
  Jpeg.Huff{gc(dcgrp()), M1.gl(dcgrp()), gsy(dcgrp())}

# every group has as many symbols as codes
def dcgrp.wf() -> {wfg(dcgrp()) == True{} : Bool}:
  {==}

# the check for one symbol: its book code hits it
def chk.dc(+ss: U32) -> Bool:
  hwchk(M3.code.dc(ss), dcgrp(), ss)

# the check for every symbol of a list
def all.dc(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +xx <> rest:
      Laws.jpg.also(chk.dc(xx), all.dc(rest))

# every symbol of the table passes
def all.dc.ok() -> {all.dc(Jenc.encode.dcsyms()) == True{} : Bool}:
  {==}

# the rest of the list, as the membership step needs it
def MembIh.dc(+_sy: U32, -rest: List<&2, U32>) -> Type:
  @hr: {Laws.jpg.memb(_sy,
    rest) == True{} : Bool} -> @ha: {all.dc(rest) == True{} : Bool} -> {chk.dc(_sy) == True{} : Bool}

# one of the symbols passes, by whether it is the list's first
def memb.dc.b(
  eq: Bool,
  +ss: U32,
  +xx: U32,
  +rest: List<&2, U32>,
  he: {U32.is_eq(ss, xx) == eq : Bool},
  hin: {Laws.jpg.eith(eq, Laws.jpg.memb(ss, rest)) == True{} : Bool},
  hall: {Laws.jpg.also(chk.dc(xx), all.dc(rest)) == True{} : Bool},
  ih: MembIh.dc(ss, rest)
) -> {chk.dc(ss) == True{} : Bool}:
  match eq:
    case True{}:
      es = Equal.sym(U32, ss, xx, M1.ueq(ss, xx, he))
      %es : {chk.dc(_) == True{} : Bool}
      M1.also_l(chk.dc(xx), all.dc(rest), hall)
    case False{}:
      ih(hin, M1.also_r(chk.dc(xx), all.dc(rest), hall))

# a symbol of a list whose symbols all pass passes
def memb.dc(
  xs: List<&2, U32>,
  +ss: U32,
  hin: {Laws.jpg.memb(ss, xs) == True{} : Bool},
  hall: {all.dc(xs) == True{} : Bool}
) -> {chk.dc(ss) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({chk.dc(ss) == True{} : Bool}, M1.huf.false_true(hin))
    case +xx <> +rest:
      memb.dc.b(U32.is_eq(ss, xx), ss, xx, rest, {==}, hin, hall, hr => ha => memb.dc(rest, ss, hr, ha))

# the decoder's Huffman lookup, over the dc table in groups, from a model reader holding a symbol's book code and
# more, finds the symbol and leaves the reader after the code
def huff.dc(
  +ss: RS,
  +ok: U32,
  +sy: U32,
  +tl: List<&2, Bool>,
  +hs: {rshort(ss) == True{} : Bool},
  +h8: {roct8(ss) == True{} : Bool},
  +he: {rem(ss) == List.append(&2, Bool, M3.code.dc(sy), tl) : List<&2, Bool>},
  +hc: {chk.dc(sy) == True{} : Bool}
) -> {Jpeg.decode.huff(16n, Jpeg.Ask{None{}, 0, 0, rbits(ss, ok)}, Jpeg.Huff{gc(dcgrp()), M1.gl(dcgrp()),
  gsy(dcgrp())}) == Jpeg.Hit{sy, rbits(radv(List.length(&2, Bool, M3.code.dc(sy)), ss), ok), ok} : Jpeg.Hit}:
  +cc = M3.code.dc(sy)
  +nn = List.length(&2, Bool, cc)
  +gs = dcgrp()
  +tab = {Jpeg.Huff{gc(gs), M1.gl(gs), gsy(gs)} : Jpeg.Huff}
  +eh = {hwis(hwg(cc, gs, 0, 0), sy, nn, M3.and_r(Nat.is_le(nn, 16n), hw.is(hwg(cc, gs, 0, 0), sy, nn), hc)) :
    {hwg(cc, gs, 0, 0) == M6.HWHit{sy, nn} : M6.HW}}
  +ew = {Equal.trans(M6.HW, M6.hw(cc, tab, 0, 0), hwg(cc, gs, 0, 0), M6.HWHit{sy, nn}, hw_g(cc, gs, 0, 0,
    dcgrp.wf()), eh) : {M6.hw(cc, tab, 0, 0) == M6.HWHit{sy, nn} : M6.HW}}
  +hf = {Equal.trans(Bool, hw.fits(M6.hw(cc, tab, 0, 0), 16n), hw.fits(M6.HWHit{sy, nn}, 16n), True{},
    Equal.cong(M6.HW, Bool, rr => hw.fits(rr, 16n), M6.hw(cc, tab, 0, 0), M6.HWHit{sy, nn}, ew),
    M3.and_l(Nat.is_le(nn, 16n), hw.is(hwg(cc, gs, 0, 0), sy, nn), hc)) :
    {hw.fits(M6.hw(cc, tab, 0, 0), 16n) == True{} : Bool}}
  Equal.trans(Jpeg.Hit, Jpeg.decode.huff(16n, Jpeg.Ask{None{}, 0, 0, rbits(ss, ok)}, tab), hwres(M6.hw(cc, tab,
    0, 0), ss, ok), Jpeg.Hit{sy, rbits(radv(nn, ss), ok), ok}, hwalk(cc, 16n, ss, ok, 0, 0, gc(gs),
    M1.gl(gs), gsy(gs), tl, hs, h8, he, hf), Equal.cong(M6.HW, Jpeg.Hit, rr => hwres(rr, ss, ok), M6.hw(cc, tab,
    0, 0), M6.HWHit{sy, nn}, ew))

# the ac table the decoder builds, in groups of one code length
def acgrp() -> List<&2, M1.HG>:
  [M1.HG{2, [0, 1], [1, 2]}, M1.HG{3, [4], [3]}, M1.HG{4, [10, 11, 12], [0, 4, 17]}, M1.HG{5, [26, 27, 28], [5, 18,
    33]}, M1.HG{6, [58, 59], [49, 65]}, M1.HG{7, [120, 121, 122, 123], [6, 19, 81, 97]}, M1.HG{8, [248, 249, 250], [7,
    34, 113]}, M1.HG{9, [502, 503, 504, 505, 506], [20, 50, 129, 145, 161]}, M1.HG{10, [1014, 1015, 1016, 1017, 1018],
    [8, 35, 66, 177, 193]}, M1.HG{11, [2038, 2039, 2040, 2041], [21, 82, 209, 240]}, M1.HG{12, [4084, 4085, 4086,
    4087], [36, 51, 98, 114]}, M1.HG{15, [32704], [130]}, M1.HG{16, [65410, 65411, 65412, 65413, 65414, 65415, 65416,
    65417, 65418, 65419, 65420, 65421, 65422, 65423, 65424, 65425, 65426, 65427, 65428, 65429, 65430, 65431, 65432,
    65433, 65434, 65435, 65436, 65437, 65438, 65439, 65440, 65441, 65442, 65443, 65444, 65445, 65446, 65447, 65448,
    65449, 65450, 65451, 65452, 65453, 65454, 65455, 65456, 65457, 65458, 65459, 65460, 65461, 65462, 65463, 65464,
    65465, 65466, 65467, 65468, 65469, 65470, 65471, 65472, 65473, 65474, 65475, 65476, 65477, 65478, 65479, 65480,
    65481, 65482, 65483, 65484, 65485, 65486, 65487, 65488, 65489, 65490, 65491, 65492, 65493, 65494, 65495, 65496,
    65497, 65498, 65499, 65500, 65501, 65502, 65503, 65504, 65505, 65506, 65507, 65508, 65509, 65510, 65511, 65512,
    65513, 65514, 65515, 65516, 65517, 65518, 65519, 65520, 65521, 65522, 65523, 65524, 65525, 65526, 65527, 65528,
    65529, 65530, 65531, 65532, 65533, 65534], [9, 10, 22, 23, 24, 25, 26, 37, 38, 39, 40, 41, 42, 52, 53, 54, 55, 56,
    57, 58, 67, 68, 69, 70, 71, 72, 73, 74, 83, 84, 85, 86, 87, 88, 89, 90, 99, 100, 101, 102, 103, 104, 105, 106,
    115, 116, 117, 118, 119, 120, 121, 122, 131, 132, 133, 134, 135, 136, 137, 138, 146, 147, 148, 149, 150, 151, 152,
    153, 154, 162, 163, 164, 165, 166, 167, 168, 169, 170, 178, 179, 180, 181, 182, 183, 184, 185, 186, 194, 195, 196,
    197, 198, 199, 200, 201, 202, 210, 211, 212, 213, 214, 215, 216, 217, 218, 225, 226, 227, 228, 229, 230, 231, 232,
    233, 234, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250]}]

# the statement of actab.eq
def actab.eq.ty() -> Type:
  {Jpeg.decode.canon(272n, 0n, Jenc.encode.accounts(), Jenc.encode.acsyms(), 0, 0, [], [],
    []) == Jpeg.Huff{gc(acgrp()), M1.gl(acgrp()), gsy(acgrp())} : Jpeg.Huff}

# the decoder's table is the groups'
def actab.eq() -> actab.eq.ty():
  {==}

# the ac table in groups, as the decoder holds it
def actab() -> Jpeg.Huff:
  Jpeg.Huff{gc(acgrp()), M1.gl(acgrp()), gsy(acgrp())}

# every group has as many symbols as codes
def acgrp.wf() -> {wfg(acgrp()) == True{} : Bool}:
  {==}

# the check for one symbol: its book code hits it
def chk.ac(+ss: U32) -> Bool:
  hwchk(M3.code.ac(ss), acgrp(), ss)

# the check for every symbol of a list
def all.ac(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +xx <> rest:
      Laws.jpg.also(chk.ac(xx), all.ac(rest))

# every symbol of the table passes
def all.ac.ok() -> {all.ac(Jenc.encode.acsyms()) == True{} : Bool}:
  {==}

# the rest of the list, as the membership step needs it
def MembIh.ac(+_sy: U32, -rest: List<&2, U32>) -> Type:
  @hr: {Laws.jpg.memb(_sy,
    rest) == True{} : Bool} -> @ha: {all.ac(rest) == True{} : Bool} -> {chk.ac(_sy) == True{} : Bool}

# one of the symbols passes, by whether it is the list's first
def memb.ac.b(
  eq: Bool,
  +ss: U32,
  +xx: U32,
  +rest: List<&2, U32>,
  he: {U32.is_eq(ss, xx) == eq : Bool},
  hin: {Laws.jpg.eith(eq, Laws.jpg.memb(ss, rest)) == True{} : Bool},
  hall: {Laws.jpg.also(chk.ac(xx), all.ac(rest)) == True{} : Bool},
  ih: MembIh.ac(ss, rest)
) -> {chk.ac(ss) == True{} : Bool}:
  match eq:
    case True{}:
      es = Equal.sym(U32, ss, xx, M1.ueq(ss, xx, he))
      %es : {chk.ac(_) == True{} : Bool}
      M1.also_l(chk.ac(xx), all.ac(rest), hall)
    case False{}:
      ih(hin, M1.also_r(chk.ac(xx), all.ac(rest), hall))

# a symbol of a list whose symbols all pass passes
def memb.ac(
  xs: List<&2, U32>,
  +ss: U32,
  hin: {Laws.jpg.memb(ss, xs) == True{} : Bool},
  hall: {all.ac(xs) == True{} : Bool}
) -> {chk.ac(ss) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({chk.ac(ss) == True{} : Bool}, M1.huf.false_true(hin))
    case +xx <> +rest:
      memb.ac.b(U32.is_eq(ss, xx), ss, xx, rest, {==}, hin, hall, hr => ha => memb.ac(rest, ss, hr, ha))

# the decoder's Huffman lookup, over the ac table in groups, from a model reader holding a symbol's book code and
# more, finds the symbol and leaves the reader after the code
def huff.ac(
  +ss: RS,
  +ok: U32,
  +sy: U32,
  +tl: List<&2, Bool>,
  +hs: {rshort(ss) == True{} : Bool},
  +h8: {roct8(ss) == True{} : Bool},
  +he: {rem(ss) == List.append(&2, Bool, M3.code.ac(sy), tl) : List<&2, Bool>},
  +hc: {chk.ac(sy) == True{} : Bool}
) -> {Jpeg.decode.huff(16n, Jpeg.Ask{None{}, 0, 0, rbits(ss, ok)}, Jpeg.Huff{gc(acgrp()), M1.gl(acgrp()),
  gsy(acgrp())}) == Jpeg.Hit{sy, rbits(radv(List.length(&2, Bool, M3.code.ac(sy)), ss), ok), ok} : Jpeg.Hit}:
  +cc = M3.code.ac(sy)
  +nn = List.length(&2, Bool, cc)
  +gs = acgrp()
  +tab = {Jpeg.Huff{gc(gs), M1.gl(gs), gsy(gs)} : Jpeg.Huff}
  +eh = {hwis(hwg(cc, gs, 0, 0), sy, nn, M3.and_r(Nat.is_le(nn, 16n), hw.is(hwg(cc, gs, 0, 0), sy, nn), hc)) :
    {hwg(cc, gs, 0, 0) == M6.HWHit{sy, nn} : M6.HW}}
  +ew = {Equal.trans(M6.HW, M6.hw(cc, tab, 0, 0), hwg(cc, gs, 0, 0), M6.HWHit{sy, nn}, hw_g(cc, gs, 0, 0,
    acgrp.wf()), eh) : {M6.hw(cc, tab, 0, 0) == M6.HWHit{sy, nn} : M6.HW}}
  +hf = {Equal.trans(Bool, hw.fits(M6.hw(cc, tab, 0, 0), 16n), hw.fits(M6.HWHit{sy, nn}, 16n), True{},
    Equal.cong(M6.HW, Bool, rr => hw.fits(rr, 16n), M6.hw(cc, tab, 0, 0), M6.HWHit{sy, nn}, ew),
    M3.and_l(Nat.is_le(nn, 16n), hw.is(hwg(cc, gs, 0, 0), sy, nn), hc)) :
    {hw.fits(M6.hw(cc, tab, 0, 0), 16n) == True{} : Bool}}
  Equal.trans(Jpeg.Hit, Jpeg.decode.huff(16n, Jpeg.Ask{None{}, 0, 0, rbits(ss, ok)}, tab), hwres(M6.hw(cc, tab,
    0, 0), ss, ok), Jpeg.Hit{sy, rbits(radv(nn, ss), ok), ok}, hwalk(cc, 16n, ss, ok, 0, 0, gc(gs),
    M1.gl(gs), gsy(gs), tl, hs, h8, he, hf), Equal.cong(M6.HW, Jpeg.Hit, rr => hwres(rr, ss, ok), M6.hw(cc, tab,
    0, 0), M6.HWHit{sy, nn}, ew))

# one code read from a model reader holding it and more: the reader after it, and its value
def read1(
  +cc: List<&2, Bool>,
  +ss: RS,
  +ok: U32,
  +mr: List<&2, Bool>,
  +hs: {rshort(ss) == True{} : Bool},
  +h8: {roct8(ss) == True{} : Bool},
  +h16: {Nat.is_le(List.length(&2, Bool, cc), 16n) == True{} : Bool},
  +ea: {rem(ss) == List.append(&2, Bool, cc, mr) : List<&2, Bool>}
) -> {Jpeg.decode.read.n(U32.from_nat(List.length(&2, Bool, cc)), rbits(ss, ok)) == (rbits(radv(List.length(&2, Bool,
  cc), ss), ok), Laws.jpg.num(cc, 0)) : Jpeg.Bits & U32}:
  +ln = List.length(&2, Bool, cc)
  +nn = U32.from_nat(ln)
  +s2 = radv(ln, ss)
  +hl = {Equal.trans(Bool, Nat.is_le(ln, List.length(&2, Bool, rem(ss))), Nat.is_le(ln, List.length(&2, Bool,
    List.append(&2, Bool, cc, mr))), True{}, Equal.cong(List<&2, Bool>, Bool, xs => Nat.is_le(ln, List.length(&2,
    Bool, xs)), rem(ss), List.append(&2, Bool, cc, mr), ea), len_app(cc, mr)) :
    {Nat.is_le(ln, List.length(&2, Bool, rem(ss))) == True{} : Bool}}
  +vr = {Equal.trans(U32, M2.vfold(List.take(&2, Bool, rem(ss), ln), 0), M2.vfold(List.take(&2, Bool, List.append(&2,
    Bool, cc, mr), ln), 0), Laws.jpg.num(cc, 0), Equal.cong(List<&2, Bool>, U32, xs => M2.vfold(List.take(&2, Bool, xs,
    ln), 0), rem(ss), List.append(&2, Bool, cc, mr), ea), Equal.trans(U32, M2.vfold(List.take(&2, Bool, List.append(&2,
    Bool, cc, mr), ln), 0), M2.vfold(cc, 0), Laws.jpg.num(cc, 0), Equal.cong(List<&2, Bool>, U32, xs => M2.vfold(xs, 0),
    List.take(&2, Bool, List.append(&2, Bool, cc, mr), ln), cc, take_app(cc, mr)), Equal.sym(U32,
    Laws.jpg.num(cc, 0), M2.vfold(cc, 0), num_v(cc, 0)))) : {M2.vfold(List.take(&2, Bool, rem(ss), ln), 0) ==
    Laws.jpg.num(cc, 0) : U32}}
  Equal.trans(Jpeg.Bits & U32, Jpeg.decode.read.n(nn, rbits(ss, ok)), canon(U32.to_nat(nn), ss, ok, 0),
    (rbits(s2, ok), Laws.jpg.num(cc, 0)), read_canon(nn, ss, ok), Equal.trans(Jpeg.Bits & U32, canon(U32.to_nat(nn),
    ss, ok, 0), canon(ln, ss, ok, 0), (rbits(s2, ok), Laws.jpg.num(cc, 0)), Equal.cong(Nat, Jpeg.Bits & U32, kk =>
    canon(kk, ss, ok, 0), U32.to_nat(nn), ln, tn16(ln, h16)), Equal.trans(Jpeg.Bits & U32, canon(ln, ss, ok, 0),
    (rbits(s2, ok), M2.vfold(List.take(&2, Bool, rem(ss), ln), 0)), (rbits(s2, ok), Laws.jpg.num(cc, 0)), rread(ln, ss,
    ok, 0, hs, h8, hl), Equal.cong(U32, Jpeg.Bits & U32, vv => (rbits(s2, ok), vv), M2.vfold(List.take(&2, Bool,
        rem(ss),
    ln), 0), Laws.jpg.num(cc, 0), vr))))

# the bits a model reader holds after n bits of bits cc and more are the more
def rem_after(
  +cc: List<&2, Bool>,
  +ss: RS,
  +mr: List<&2, Bool>,
  +hs: {rshort(ss) == True{} : Bool},
  +h8: {roct8(ss) == True{} : Bool},
  +ea: {rem(ss) == List.append(&2, Bool, cc, mr) : List<&2, Bool>}
) -> {rem(radv(List.length(&2, Bool, cc), ss)) == mr : List<&2, Bool>}:
  +ln = List.length(&2, Bool, cc)
  +hl = {Equal.trans(Bool, Nat.is_le(ln, List.length(&2, Bool, rem(ss))), Nat.is_le(ln, List.length(&2, Bool,
    List.append(&2, Bool, cc, mr))), True{}, Equal.cong(List<&2, Bool>, Bool, xs => Nat.is_le(ln, List.length(&2,
    Bool, xs)), rem(ss), List.append(&2, Bool, cc, mr), ea), len_app(cc, mr)) :
    {Nat.is_le(ln, List.length(&2, Bool, rem(ss))) == True{} : Bool}}
  Equal.trans(List<&2, Bool>, rem(radv(ln, ss)), List.drop(&2, Bool, rem(ss), ln), mr, rem_radv(ln, ss, hs, h8, hl),
    Equal.trans(List<&2, Bool>, List.drop(&2, Bool, rem(ss), ln), List.drop(&2, Bool, List.append(&2, Bool, cc, mr),
    ln), mr, Equal.cong(List<&2, Bool>, List<&2, Bool>, xs => List.drop(&2, Bool, xs, ln), rem(ss),
    List.append(&2, Bool, cc, mr), ea), drop_app(cc, mr)))

# the model reader after codes, one length at a time
def skm(cs: List<&2, List<&2, Bool>>, ss: RS) -> RS:
  match cs:
    case Nil{}:
      ss
    case cc <> rest:
      skm(rest, radv(List.length(&2, Bool, cc), ss))

# the decoder's reader after codes is the model's, with the rest of the bits, the model still a reader
def Skip(+cs: List<&2, List<&2, Bool>>, +ss: RS, +ok: U32, +tl: List<&2, Bool>) -> Type:
  &e1: {Laws.jpg.skip(cs, rbits(ss, ok)) == rbits(skm(cs, ss), ok) : Jpeg.Bits} ->
  &e2: {rem(skm(cs, ss)) == tl : List<&2, Bool>} ->
  {Bool.and(rshort(skm(cs, ss)), roct8(skm(cs, ss))) == True{} : Bool}

# one code read: the reader after it and its value
def ReadOne(+cc: List<&2, Bool>, -ss: RS, +ok: U32) -> Type:
  {Jpeg.decode.read.n(U32.from_nat(List.length(&2, Bool, cc)), rbits(ss, ok)) == (rbits(radv(List.length(&2, Bool,
    cc), ss), ok), Laws.jpg.num(cc, 0)) : Jpeg.Bits & U32}

# the reader after one code, then the rest of the codes
def skip.join(
  +cc: List<&2, Bool>,
  +rest: List<&2, List<&2, Bool>>,
  +ss: RS,
  +ok: U32,
  +tl: List<&2, Bool>,
  er: ReadOne(cc, ss, ok),
  ih: Skip(rest, radv(List.length(&2, Bool, cc), ss), ok, tl)
) -> Skip(cc <> rest, ss, ok, tl):
  (e1, e2, e3) = ih
  +ln = List.length(&2, Bool, cc)
  +s2 = radv(ln, ss)
  (Equal.trans(Jpeg.Bits, Laws.jpg.skip(rest, Laws.jpg.got.bits(Jpeg.decode.read.n(U32.from_nat(ln), rbits(ss,
    ok)))), Laws.jpg.skip(rest, rbits(s2, ok)), rbits(skm(rest, s2), ok), Equal.cong(Jpeg.Bits & U32, Jpeg.Bits,
    gg => Laws.jpg.skip(rest, Laws.jpg.got.bits(gg)), Jpeg.decode.read.n(U32.from_nat(ln), rbits(ss, ok)),
    (rbits(s2, ok), Laws.jpg.num(cc, 0)), er), e1), e2, e3)

# the decoder's reader after codes held by a model reader, and more bits
def skip_m(
  cs: List<&2, List<&2, Bool>>,
  +ss: RS,
  +ok: U32,
  +tl: List<&2, Bool>,
  +hs: {rshort(ss) == True{} : Bool},
  +h8: {roct8(ss) == True{} : Bool},
  +hc: {Laws.jpg.codes16(cs) == True{} : Bool},
  +he: {rem(ss) == List.append(&2, Bool, List.concat(&2, Bool, cs), tl) : List<&2, Bool>}
) -> Skip(cs, ss, ok, tl):
  match cs:
    case Nil{}:
      ({==}, he, radv_ok(0n, ss, hs, h8))
    case +cc <> +rest:
      +ln = List.length(&2, Bool, cc)
      +mr = List.append(&2, Bool, List.concat(&2, Bool, rest), tl)
      +h16 = {M1.also_l(Nat.is_le(ln, 16n), Laws.jpg.codes16(rest), hc) : {Nat.is_le(ln, 16n) == True{} : Bool}}
      +ea = {Equal.trans(List<&2, Bool>, rem(ss), List.append(&2, Bool, List.concat(&2, Bool, cc <> rest), tl),
        List.append(&2, Bool, cc, mr), he, M3.huf.app_assoc(cc, List.concat(&2, Bool, rest), tl)) :
        {rem(ss) == List.append(&2, Bool, cc, mr) : List<&2, Bool>}}
      +s2 = radv(ln, ss)
      +ok2 = {radv_ok(ln, ss, hs, h8) : {Bool.and(rshort(s2), roct8(s2)) == True{} : Bool}}
      skip.join(cc, rest, ss, ok, tl, read1(cc, ss, ok, mr, hs, h8, h16, ea), skip_m(rest, s2, ok, tl,
          M3.and_l(rshort(s2),
        roct8(s2), ok2), M3.and_r(rshort(s2), roct8(s2), ok2), M1.also_r(Nat.is_le(ln, 16n), Laws.jpg.codes16(rest),
            hc),
        rem_after(cc, ss, mr, hs, h8, ea)))

# the encoder's code for a symbol from its dc book is the code's bits fed to the writer
def emit_feed.dc(
  +sy: U32,
  +pp: Jenc.Put
) -> {Laws.jpg.emit(Jenc.encode.emit(Jenc.encode.sym(M3.dcbook.lit(), sy), pp)) == Laws.jpg.feed(M3.code.dc(sy),
  pp) : Jenc.Put}:
  +vv = D2.jpg.val(Array.get(U32, M3.dcbook.lit(), sy))
  Equal.trans(Jenc.Put, Laws.jpg.emit(Jenc.encode.emit(Jenc.encode.coded(Array.get(U32, M3.dcbook.lit(), sy)), pp)),
    Laws.jpg.emit(Jenc.encode.emit(Jenc.encode.coded((M3.dcbook.lit(), vv)), pp)), Laws.jpg.feed(M3.code.dc(sy), pp),
    Equal.cong(Array<U32> & U32, Jenc.Put, gg => Laws.jpg.emit(Jenc.encode.emit(Jenc.encode.coded(gg), pp)),
    Array.get(U32, M3.dcbook.lit(), sy), (M3.dcbook.lit(), vv), M3.get.eq(M3.dcbook.lit(), sy)), M3.bits_go(U32.to_nat(
    U32.shrn(vv, 16n)), pp, U32.and(vv, 65535)))

# the model's bits for codes pre, a symbol's code from the dc book, and codes post
def symbits.dc(+pre: List<&2, List<&2, Bool>>, +sy: U32, +post: List<&2, List<&2, Bool>>) -> List<&2, Bool>:
  List.append(&2, Bool, List.concat(&2, Bool, pre), List.append(&2, Bool, M3.code.dc(sy), List.concat(&2, Bool, post)))

# the bytes the writer makes of them
def SymBytes.dc(+pre: List<&2, List<&2, Bool>>, +sy: U32, +post: List<&2, List<&2, Bool>>) -> Type:
  {Laws.jpg.sym.bytes(pre, M3.dcbook.lit(), sy, post) == rxs(moct(symbits.dc(pre, sy, post), [])) : List<&2, U32>}

# the reader after codes pre back
def SymSkip.dc(+pre: List<&2, List<&2, Bool>>, +sy: U32, +post: List<&2, List<&2, Bool>>) -> Type:
  Skip(pre, RS{[], moct(symbits.dc(pre, sy, post), [])}, 1, List.append(&2, Bool, List.append(&2, Bool, M3.code.dc(sy),
    List.concat(&2, Bool, post)), mpad(symbits.dc(pre, sy, post), [])))

# the round trip once the reader has read codes pre back
def sym_rt2.dc(
  +pre: List<&2, List<&2, Bool>>,
  +sy: U32,
  +hy: {Laws.jpg.memb(sy, Jenc.encode.dcsyms()) == True{} : Bool},
  +post: List<&2, List<&2, Bool>>,
  +hq: {Laws.jpg.codes16(post) == True{} : Bool},
  eb: SymBytes.dc(pre, sy, post),
  sk: SymSkip.dc(pre, sy, post)
) -> {Laws.jpg.sym.back(pre, M3.dcbook.lit(), dctab(), sy, post) == (sy, (Laws.jpg.nums(post), 1), 1) : U32 & (List<&2,
  U32> & U32) & U32}:
  (k1, k2, k3) = sk
  +cc = M3.code.dc(sy)
  +cp = List.concat(&2, Bool, pre)
  +cq = List.concat(&2, Bool, post)
  +bs = List.append(&2, Bool, cp, List.append(&2, Bool, cc, cq))
  +os = moct(bs, [])
  +mp = mpad(bs, [])
  +s0 = {RS{[], os} : RS}
  +mr = List.append(&2, Bool, List.append(&2, Bool, cc, cq), mp)
  +s1 = skm(pre, s0)
  +tl = List.append(&2, Bool, cq, mp)
  +e1 = {Equal.trans(List<&2, Bool>, rem(s1), mr, List.append(&2, Bool, cc, tl), k2, M3.huf.app_assoc(cc, cq, mp)) :
    {rem(s1) == List.append(&2, Bool, cc, tl) : List<&2, Bool>}}
  +f1 = {k3 : {Bool.and(rshort(s1), roct8(s1)) == True{} : Bool}}
  +hs1 = {M3.and_l(rshort(s1), roct8(s1), f1) : {rshort(s1) == True{} : Bool}}
  +h81 = {M3.and_r(rshort(s1), roct8(s1), f1) : {roct8(s1) == True{} : Bool}}
  +s2 = radv(List.length(&2, Bool, cc), s1)
  +f2 = {radv_ok(List.length(&2, Bool, cc), s1, hs1, h81) : {Bool.and(rshort(s2), roct8(s2)) == True{} : Bool}}
  +eh = {huff.dc(s1, 1, sy, tl, hs1, h81, e1, memb.dc(Jenc.encode.dcsyms(), sy, hy, all.dc.ok())) :
    {Jpeg.decode.huff(16n, Jpeg.Ask{None{}, 0, 0, rbits(s1, 1)}, dctab()) == Jpeg.Hit{sy, rbits(s2, 1), 1} : Jpeg.Hit}}
  Equal.trans(U32 & (List<&2, U32> & U32) & U32, Laws.jpg.sym.back(pre, M3.dcbook.lit(), dctab(), sy, post),
    Laws.jpg.hit(Jpeg.decode.huff(16n, Jpeg.Ask{None{}, 0, 0, rbits(s1, 1)}, dctab()), post), (sy,
    (Laws.jpg.nums(post), 1), 1),
    Equal.cong(Jpeg.Bits, U32 & (List<&2, U32> & U32) & U32, bb => Laws.jpg.hit(Jpeg.decode.huff(16n,
    Jpeg.Ask{None{}, 0, 0, bb}, dctab()), post), Laws.jpg.skip(pre, Jpeg.Bits{0, 1, 0, Laws.jpg.sym.bytes(pre,
      M3.dcbook.lit(), sy, post)}), rbits(s1, 1), Equal.trans(Jpeg.Bits, Laws.jpg.skip(pre, Jpeg.Bits{0, 1, 0,
    Laws.jpg.sym.bytes(pre, M3.dcbook.lit(), sy, post)}), Laws.jpg.skip(pre, rbits(s0,
    1)), rbits(s1, 1), Equal.cong(List<&2, U32>, Jpeg.Bits, xs => Laws.jpg.skip(pre, Jpeg.Bits{0, 1, 0, xs}),
    Laws.jpg.sym.bytes(pre, M3.dcbook.lit(), sy, post), rxs(os), eb), k1)),
    Equal.trans(U32 & (List<&2, U32> & U32) & U32, Laws.jpg.hit(Jpeg.decode.huff(16n, Jpeg.Ask{None{}, 0, 0, rbits(s1,
    1)}, dctab()), post),
    Laws.jpg.hit(Jpeg.Hit{sy, rbits(s2, 1), 1}, post), (sy, (Laws.jpg.nums(post), 1), 1), Equal.cong(Jpeg.Hit,
    U32 & (List<&2, U32> & U32) & U32, hh => Laws.jpg.hit(hh, post), Jpeg.decode.huff(16n, Jpeg.Ask{None{}, 0, 0,
    rbits(s1, 1)}, dctab()),
    Jpeg.Hit{sy, rbits(s2, 1), 1}, eh), Equal.cong(List<&2, U32> & U32, U32 & (List<&2, U32> & U32) & U32, rr => (sy,
    rr, 1), Laws.jpg.reads(post, rbits(s2, 1)), (Laws.jpg.nums(post), 1), reads_m(post, s2, 1, mp, M3.and_l(rshort(s2),
    roct8(s2), f2), M3.and_r(rshort(s2), roct8(s2), f2), hq, rem_after(cc, s1, tl, hs1, h81, e1)))))

# codes pre, a symbol's code from the dc book and codes post, round trip through the writer and the reader
def sym_rt.dc(
  +pre: List<&2, List<&2, Bool>>,
  +hp: {Laws.jpg.codes16(pre) == True{} : Bool},
  +sy: U32,
  +hy: {Laws.jpg.memb(sy, Jenc.encode.dcsyms()) == True{} : Bool},
  +post: List<&2, List<&2, Bool>>,
  +hq: {Laws.jpg.codes16(post) == True{} : Bool}
) -> {Laws.jpg.sym.back(pre, M3.dcbook.lit(), dctab(), sy, post) == (sy, (Laws.jpg.nums(post), 1), 1) : U32 & (List<&2,
  U32> & U32) & U32}:
  +cc = M3.code.dc(sy)
  +cp = List.concat(&2, Bool, pre)
  +cq = List.concat(&2, Bool, post)
  +bs = List.append(&2, Bool, cp, List.append(&2, Bool, cc, cq))
  +os = moct(bs, [])
  +mp = mpad(bs, [])
  +p0 = Jenc.encode.put0()
  +ew = {Equal.trans(Jenc.Put, Laws.jpg.write(post, Laws.jpg.emit(Jenc.encode.emit(Jenc.encode.sym(M3.dcbook.lit(), sy),
    Laws.jpg.write(pre, p0)))), Laws.jpg.write(post, Laws.jpg.feed(cc,
    Laws.jpg.write(pre, p0))), Laws.jpg.feed(bs, p0), Equal.cong(Jenc.Put, Jenc.Put, qq => Laws.jpg.write(post, qq),
    Laws.jpg.emit(Jenc.encode.emit(Jenc.encode.sym(M3.dcbook.lit(), sy), Laws.jpg.write(pre, p0))), Laws.jpg.feed(cc,
      Laws.jpg.write(pre, p0)), emit_feed.dc(sy, Laws.jpg.write(pre, p0))),
    Equal.trans(Jenc.Put, Laws.jpg.write(post, Laws.jpg.feed(cc, Laws.jpg.write(pre, p0))), Laws.jpg.feed(cq,
      Laws.jpg.feed(cc,
    Laws.jpg.write(pre, p0))), Laws.jpg.feed(bs, p0), wcodes_feed(post, Laws.jpg.feed(cc, Laws.jpg.write(pre, p0)), hq),
    Equal.trans(Jenc.Put, Laws.jpg.feed(cq, Laws.jpg.feed(cc, Laws.jpg.write(pre, p0))), Laws.jpg.feed(cq,
      Laws.jpg.feed(cc, Laws.jpg.feed(cp, p0))), Laws.jpg.feed(bs, p0),
    Equal.cong(Jenc.Put, Jenc.Put, qq => Laws.jpg.feed(cq, Laws.jpg.feed(cc, qq)), Laws.jpg.write(pre, p0),
      Laws.jpg.feed(cp, p0),
    wcodes_feed(pre, p0, hp)), Equal.trans(Jenc.Put, Laws.jpg.feed(cq, Laws.jpg.feed(cc, Laws.jpg.feed(cp, p0))),
      Laws.jpg.feed(List.append(&2, Bool, cc,
    cq), Laws.jpg.feed(cp, p0)), Laws.jpg.feed(bs, p0), Equal.sym(Jenc.Put, Laws.jpg.feed(List.append(&2, Bool, cc,
      cq), Laws.jpg.feed(cp, p0)), Laws.jpg.feed(cq,
    Laws.jpg.feed(cc, Laws.jpg.feed(cp, p0))), M3.feed_app(cc, cq, Laws.jpg.feed(cp, p0))), Equal.sym(Jenc.Put,
      Laws.jpg.feed(bs, p0),
    Laws.jpg.feed(List.append(&2, Bool, cc, cq), Laws.jpg.feed(cp, p0)), M3.feed_app(cp, List.append(&2, Bool, cc, cq),
      p0)))))) :
    {Laws.jpg.write(post, Laws.jpg.emit(Jenc.encode.emit(Jenc.encode.sym(M3.dcbook.lit(), sy), Laws.jpg.write(pre,
      p0)))) == Laws.jpg.feed(bs, p0) : Jenc.Put}}
  +eb = {Equal.trans(List<&2, U32>, Laws.jpg.sym.bytes(pre, M3.dcbook.lit(), sy, post),
    Jenc.encode.pad(Laws.jpg.feed(bs, M2.wput(M2.WS{[], []}))), rxs(os), Equal.cong(Jenc.Put, List<&2, U32>, qq =>
    Jenc.encode.pad(qq), Laws.jpg.write(post, Laws.jpg.emit(Jenc.encode.emit(Jenc.encode.sym(M3.dcbook.lit(), sy),
      Laws.jpg.write(pre, p0)))), Laws.jpg.feed(bs, p0), ew),
    Equal.trans(List<&2, U32>, Jenc.encode.pad(Laws.jpg.feed(bs, M2.wput(M2.WS{[], []}))),
        Jenc.encode.pad(M2.wput(M2.wm(bs, M2.WS{[],
    []}))), rxs(os), Equal.cong(Jenc.Put, List<&2, U32>, qq => Jenc.encode.pad(qq), Laws.jpg.feed(bs, M2.wput(M2.WS{[],
        []})),
    M2.wput(M2.wm(bs, M2.WS{[], []})), M2.wfeed(bs, M2.WS{[], []}, {==})), pad_m(bs, [], [], {==}))) :
    {Laws.jpg.sym.bytes(pre, M3.dcbook.lit(), sy, post) == rxs(os) : List<&2, U32>}}
  +s0 = {RS{[], os} : RS}
  +mr = List.append(&2, Bool, List.append(&2, Bool, cc, cq), mp)
  +e0 = {Equal.trans(List<&2, Bool>, rem(s0), List.append(&2, Bool, bs, mp), List.append(&2, Bool, cp, mr),
    concat_moct(bs, []), M3.huf.app_assoc(cp, List.append(&2, Bool, cc, cq), mp)) : {rem(s0) == List.append(&2, Bool,
        cp,
    mr) : List<&2, Bool>}}
  sym_rt2.dc(pre, sy, hy, post, hq, eb, skip_m(pre, s0, 1, mr, {==}, oct8_moct(bs, [], {==}), hp, e0))

# the dc table law: the real book and table are the ones written out
def huff_law.dc(
  +pre: List<&2, List<&2, Bool>>,
  +hp: {Laws.jpg.codes16(pre) == True{} : Bool},
  +sy: U32,
  +hy: {Laws.jpg.memb(sy, Jenc.encode.dcsyms()) == True{} : Bool},
  +post: List<&2, List<&2, Bool>>,
  +hq: {Laws.jpg.codes16(post) == True{} : Bool}
) -> {Laws.jpg.sym.back(pre, Jenc.encode.huff(Jenc.encode.dccounts(), Jenc.encode.dcsyms()), Jpeg.decode.canon(272n,
  0n, Jenc.encode.dccounts(), Jenc.encode.dcsyms(), 0, 0, [], [], []), sy, post) == (sy, (Laws.jpg.nums(post), 1),
  1) : U32 & (List<&2, U32> & U32) & U32}:
  +cn = Jpeg.decode.canon(272n, 0n, Jenc.encode.dccounts(), Jenc.encode.dcsyms(), 0, 0, [], [], [])
  Equal.trans(U32 & (List<&2, U32> & U32) & U32, Laws.jpg.sym.back(pre, Jenc.encode.huff(Jenc.encode.dccounts(),
    Jenc.encode.dcsyms()), cn, sy, post), Laws.jpg.sym.back(pre, M3.dcbook.lit(), cn, sy, post), (sy,
        (Laws.jpg.nums(post),
    1), 1), Equal.cong(Array<U32>, U32 & (List<&2, U32> & U32) & U32, bk => Laws.jpg.sym.back(pre, bk, cn, sy, post),
    Jenc.encode.huff(Jenc.encode.dccounts(), Jenc.encode.dcsyms()), M3.dcbook.lit(), M2.dcbook.eq()),
    Equal.trans(U32 & (List<&2, U32> & U32) & U32, Laws.jpg.sym.back(pre, M3.dcbook.lit(), cn, sy, post),
    Laws.jpg.sym.back(pre, M3.dcbook.lit(), dctab(), sy, post), (sy, (Laws.jpg.nums(post), 1), 1), Equal.cong(Jpeg.Huff,
    U32 & (List<&2, U32> & U32) & U32, tb => Laws.jpg.sym.back(pre, M3.dcbook.lit(), tb, sy, post), cn, dctab(),
    dctab.eq()), sym_rt.dc(pre, hp, sy, hy, post, hq)))

# the encoder's code for a symbol from its ac book is the code's bits fed to the writer
def emit_feed.ac(
  +sy: U32,
  +pp: Jenc.Put
) -> {Laws.jpg.emit(Jenc.encode.emit(Jenc.encode.sym(M3.acbook.lit(), sy), pp)) == Laws.jpg.feed(M3.code.ac(sy),
  pp) : Jenc.Put}:
  +vv = D2.jpg.val(Array.get(U32, M3.acbook.lit(), sy))
  Equal.trans(Jenc.Put, Laws.jpg.emit(Jenc.encode.emit(Jenc.encode.coded(Array.get(U32, M3.acbook.lit(), sy)), pp)),
    Laws.jpg.emit(Jenc.encode.emit(Jenc.encode.coded((M3.acbook.lit(), vv)), pp)), Laws.jpg.feed(M3.code.ac(sy), pp),
    Equal.cong(Array<U32> & U32, Jenc.Put, gg => Laws.jpg.emit(Jenc.encode.emit(Jenc.encode.coded(gg), pp)),
    Array.get(U32, M3.acbook.lit(), sy), (M3.acbook.lit(), vv), M3.get.eq(M3.acbook.lit(), sy)), M3.bits_go(U32.to_nat(
    U32.shrn(vv, 16n)), pp, U32.and(vv, 65535)))

# the model's bits for codes pre, a symbol's code from the ac book, and codes post
def symbits.ac(+pre: List<&2, List<&2, Bool>>, +sy: U32, +post: List<&2, List<&2, Bool>>) -> List<&2, Bool>:
  List.append(&2, Bool, List.concat(&2, Bool, pre), List.append(&2, Bool, M3.code.ac(sy), List.concat(&2, Bool, post)))

# the bytes the writer makes of them
def SymBytes.ac(+pre: List<&2, List<&2, Bool>>, +sy: U32, +post: List<&2, List<&2, Bool>>) -> Type:
  {Laws.jpg.sym.bytes(pre, M3.acbook.lit(), sy, post) == rxs(moct(symbits.ac(pre, sy, post), [])) : List<&2, U32>}

# the reader after codes pre back
def SymSkip.ac(+pre: List<&2, List<&2, Bool>>, +sy: U32, +post: List<&2, List<&2, Bool>>) -> Type:
  Skip(pre, RS{[], moct(symbits.ac(pre, sy, post), [])}, 1, List.append(&2, Bool, List.append(&2, Bool, M3.code.ac(sy),
    List.concat(&2, Bool, post)), mpad(symbits.ac(pre, sy, post), [])))

# the round trip once the reader has read codes pre back
def sym_rt2.ac(
  +pre: List<&2, List<&2, Bool>>,
  +sy: U32,
  +hy: {Laws.jpg.memb(sy, Jenc.encode.acsyms()) == True{} : Bool},
  +post: List<&2, List<&2, Bool>>,
  +hq: {Laws.jpg.codes16(post) == True{} : Bool},
  eb: SymBytes.ac(pre, sy, post),
  sk: SymSkip.ac(pre, sy, post)
) -> {Laws.jpg.sym.back(pre, M3.acbook.lit(), actab(), sy, post) == (sy, (Laws.jpg.nums(post), 1), 1) : U32 & (List<&2,
  U32> & U32) & U32}:
  (k1, k2, k3) = sk
  +cc = M3.code.ac(sy)
  +cp = List.concat(&2, Bool, pre)
  +cq = List.concat(&2, Bool, post)
  +bs = List.append(&2, Bool, cp, List.append(&2, Bool, cc, cq))
  +os = moct(bs, [])
  +mp = mpad(bs, [])
  +s0 = {RS{[], os} : RS}
  +mr = List.append(&2, Bool, List.append(&2, Bool, cc, cq), mp)
  +s1 = skm(pre, s0)
  +tl = List.append(&2, Bool, cq, mp)
  +e1 = {Equal.trans(List<&2, Bool>, rem(s1), mr, List.append(&2, Bool, cc, tl), k2, M3.huf.app_assoc(cc, cq, mp)) :
    {rem(s1) == List.append(&2, Bool, cc, tl) : List<&2, Bool>}}
  +f1 = {k3 : {Bool.and(rshort(s1), roct8(s1)) == True{} : Bool}}
  +hs1 = {M3.and_l(rshort(s1), roct8(s1), f1) : {rshort(s1) == True{} : Bool}}
  +h81 = {M3.and_r(rshort(s1), roct8(s1), f1) : {roct8(s1) == True{} : Bool}}
  +s2 = radv(List.length(&2, Bool, cc), s1)
  +f2 = {radv_ok(List.length(&2, Bool, cc), s1, hs1, h81) : {Bool.and(rshort(s2), roct8(s2)) == True{} : Bool}}
  +eh = {huff.ac(s1, 1, sy, tl, hs1, h81, e1, memb.ac(Jenc.encode.acsyms(), sy, hy, all.ac.ok())) :
    {Jpeg.decode.huff(16n, Jpeg.Ask{None{}, 0, 0, rbits(s1, 1)}, actab()) == Jpeg.Hit{sy, rbits(s2, 1), 1} : Jpeg.Hit}}
  Equal.trans(U32 & (List<&2, U32> & U32) & U32, Laws.jpg.sym.back(pre, M3.acbook.lit(), actab(), sy, post),
    Laws.jpg.hit(Jpeg.decode.huff(16n, Jpeg.Ask{None{}, 0, 0, rbits(s1, 1)}, actab()), post), (sy,
    (Laws.jpg.nums(post), 1), 1),
    Equal.cong(Jpeg.Bits, U32 & (List<&2, U32> & U32) & U32, bb => Laws.jpg.hit(Jpeg.decode.huff(16n,
    Jpeg.Ask{None{}, 0, 0, bb}, actab()), post), Laws.jpg.skip(pre, Jpeg.Bits{0, 1, 0, Laws.jpg.sym.bytes(pre,
      M3.acbook.lit(), sy, post)}), rbits(s1, 1), Equal.trans(Jpeg.Bits, Laws.jpg.skip(pre, Jpeg.Bits{0, 1, 0,
    Laws.jpg.sym.bytes(pre, M3.acbook.lit(), sy, post)}), Laws.jpg.skip(pre, rbits(s0,
    1)), rbits(s1, 1), Equal.cong(List<&2, U32>, Jpeg.Bits, xs => Laws.jpg.skip(pre, Jpeg.Bits{0, 1, 0, xs}),
    Laws.jpg.sym.bytes(pre, M3.acbook.lit(), sy, post), rxs(os), eb), k1)),
    Equal.trans(U32 & (List<&2, U32> & U32) & U32, Laws.jpg.hit(Jpeg.decode.huff(16n, Jpeg.Ask{None{}, 0, 0, rbits(s1,
    1)}, actab()), post),
    Laws.jpg.hit(Jpeg.Hit{sy, rbits(s2, 1), 1}, post), (sy, (Laws.jpg.nums(post), 1), 1), Equal.cong(Jpeg.Hit,
    U32 & (List<&2, U32> & U32) & U32, hh => Laws.jpg.hit(hh, post), Jpeg.decode.huff(16n, Jpeg.Ask{None{}, 0, 0,
    rbits(s1, 1)}, actab()),
    Jpeg.Hit{sy, rbits(s2, 1), 1}, eh), Equal.cong(List<&2, U32> & U32, U32 & (List<&2, U32> & U32) & U32, rr => (sy,
    rr, 1), Laws.jpg.reads(post, rbits(s2, 1)), (Laws.jpg.nums(post), 1), reads_m(post, s2, 1, mp, M3.and_l(rshort(s2),
    roct8(s2), f2), M3.and_r(rshort(s2), roct8(s2), f2), hq, rem_after(cc, s1, tl, hs1, h81, e1)))))

# codes pre, a symbol's code from the ac book and codes post, round trip through the writer and the reader
def sym_rt.ac(
  +pre: List<&2, List<&2, Bool>>,
  +hp: {Laws.jpg.codes16(pre) == True{} : Bool},
  +sy: U32,
  +hy: {Laws.jpg.memb(sy, Jenc.encode.acsyms()) == True{} : Bool},
  +post: List<&2, List<&2, Bool>>,
  +hq: {Laws.jpg.codes16(post) == True{} : Bool}
) -> {Laws.jpg.sym.back(pre, M3.acbook.lit(), actab(), sy, post) == (sy, (Laws.jpg.nums(post), 1), 1) : U32 & (List<&2,
  U32> & U32) & U32}:
  +cc = M3.code.ac(sy)
  +cp = List.concat(&2, Bool, pre)
  +cq = List.concat(&2, Bool, post)
  +bs = List.append(&2, Bool, cp, List.append(&2, Bool, cc, cq))
  +os = moct(bs, [])
  +mp = mpad(bs, [])
  +p0 = Jenc.encode.put0()
  +ew = {Equal.trans(Jenc.Put, Laws.jpg.write(post, Laws.jpg.emit(Jenc.encode.emit(Jenc.encode.sym(M3.acbook.lit(), sy),
    Laws.jpg.write(pre, p0)))), Laws.jpg.write(post, Laws.jpg.feed(cc,
    Laws.jpg.write(pre, p0))), Laws.jpg.feed(bs, p0), Equal.cong(Jenc.Put, Jenc.Put, qq => Laws.jpg.write(post, qq),
    Laws.jpg.emit(Jenc.encode.emit(Jenc.encode.sym(M3.acbook.lit(), sy), Laws.jpg.write(pre, p0))), Laws.jpg.feed(cc,
      Laws.jpg.write(pre, p0)), emit_feed.ac(sy, Laws.jpg.write(pre, p0))),
    Equal.trans(Jenc.Put, Laws.jpg.write(post, Laws.jpg.feed(cc, Laws.jpg.write(pre, p0))), Laws.jpg.feed(cq,
      Laws.jpg.feed(cc,
    Laws.jpg.write(pre, p0))), Laws.jpg.feed(bs, p0), wcodes_feed(post, Laws.jpg.feed(cc, Laws.jpg.write(pre, p0)), hq),
    Equal.trans(Jenc.Put, Laws.jpg.feed(cq, Laws.jpg.feed(cc, Laws.jpg.write(pre, p0))), Laws.jpg.feed(cq,
      Laws.jpg.feed(cc, Laws.jpg.feed(cp, p0))), Laws.jpg.feed(bs, p0),
    Equal.cong(Jenc.Put, Jenc.Put, qq => Laws.jpg.feed(cq, Laws.jpg.feed(cc, qq)), Laws.jpg.write(pre, p0),
      Laws.jpg.feed(cp, p0),
    wcodes_feed(pre, p0, hp)), Equal.trans(Jenc.Put, Laws.jpg.feed(cq, Laws.jpg.feed(cc, Laws.jpg.feed(cp, p0))),
      Laws.jpg.feed(List.append(&2, Bool, cc,
    cq), Laws.jpg.feed(cp, p0)), Laws.jpg.feed(bs, p0), Equal.sym(Jenc.Put, Laws.jpg.feed(List.append(&2, Bool, cc,
      cq), Laws.jpg.feed(cp, p0)), Laws.jpg.feed(cq,
    Laws.jpg.feed(cc, Laws.jpg.feed(cp, p0))), M3.feed_app(cc, cq, Laws.jpg.feed(cp, p0))), Equal.sym(Jenc.Put,
      Laws.jpg.feed(bs, p0),
    Laws.jpg.feed(List.append(&2, Bool, cc, cq), Laws.jpg.feed(cp, p0)), M3.feed_app(cp, List.append(&2, Bool, cc, cq),
      p0)))))) :
    {Laws.jpg.write(post, Laws.jpg.emit(Jenc.encode.emit(Jenc.encode.sym(M3.acbook.lit(), sy), Laws.jpg.write(pre,
      p0)))) == Laws.jpg.feed(bs, p0) : Jenc.Put}}
  +eb = {Equal.trans(List<&2, U32>, Laws.jpg.sym.bytes(pre, M3.acbook.lit(), sy, post),
    Jenc.encode.pad(Laws.jpg.feed(bs, M2.wput(M2.WS{[], []}))), rxs(os), Equal.cong(Jenc.Put, List<&2, U32>, qq =>
    Jenc.encode.pad(qq), Laws.jpg.write(post, Laws.jpg.emit(Jenc.encode.emit(Jenc.encode.sym(M3.acbook.lit(), sy),
      Laws.jpg.write(pre, p0)))), Laws.jpg.feed(bs, p0), ew),
    Equal.trans(List<&2, U32>, Jenc.encode.pad(Laws.jpg.feed(bs, M2.wput(M2.WS{[], []}))),
        Jenc.encode.pad(M2.wput(M2.wm(bs, M2.WS{[],
    []}))), rxs(os), Equal.cong(Jenc.Put, List<&2, U32>, qq => Jenc.encode.pad(qq), Laws.jpg.feed(bs, M2.wput(M2.WS{[],
        []})),
    M2.wput(M2.wm(bs, M2.WS{[], []})), M2.wfeed(bs, M2.WS{[], []}, {==})), pad_m(bs, [], [], {==}))) :
    {Laws.jpg.sym.bytes(pre, M3.acbook.lit(), sy, post) == rxs(os) : List<&2, U32>}}
  +s0 = {RS{[], os} : RS}
  +mr = List.append(&2, Bool, List.append(&2, Bool, cc, cq), mp)
  +e0 = {Equal.trans(List<&2, Bool>, rem(s0), List.append(&2, Bool, bs, mp), List.append(&2, Bool, cp, mr),
    concat_moct(bs, []), M3.huf.app_assoc(cp, List.append(&2, Bool, cc, cq), mp)) : {rem(s0) == List.append(&2, Bool,
        cp,
    mr) : List<&2, Bool>}}
  sym_rt2.ac(pre, sy, hy, post, hq, eb, skip_m(pre, s0, 1, mr, {==}, oct8_moct(bs, [], {==}), hp, e0))

# the ac table law: the real book and table are the ones written out
def huff_law.ac(
  +pre: List<&2, List<&2, Bool>>,
  +hp: {Laws.jpg.codes16(pre) == True{} : Bool},
  +sy: U32,
  +hy: {Laws.jpg.memb(sy, Jenc.encode.acsyms()) == True{} : Bool},
  +post: List<&2, List<&2, Bool>>,
  +hq: {Laws.jpg.codes16(post) == True{} : Bool}
) -> {Laws.jpg.sym.back(pre, Jenc.encode.huff(Jenc.encode.accounts(), Jenc.encode.acsyms()), Jpeg.decode.canon(272n,
  0n, Jenc.encode.accounts(), Jenc.encode.acsyms(), 0, 0, [], [], []), sy, post) == (sy, (Laws.jpg.nums(post), 1),
  1) : U32 & (List<&2, U32> & U32) & U32}:
  +cn = Jpeg.decode.canon(272n, 0n, Jenc.encode.accounts(), Jenc.encode.acsyms(), 0, 0, [], [], [])
  Equal.trans(U32 & (List<&2, U32> & U32) & U32, Laws.jpg.sym.back(pre, Jenc.encode.huff(Jenc.encode.accounts(),
    Jenc.encode.acsyms()), cn, sy, post), Laws.jpg.sym.back(pre, M3.acbook.lit(), cn, sy, post), (sy,
        (Laws.jpg.nums(post),
    1), 1), Equal.cong(Array<U32>, U32 & (List<&2, U32> & U32) & U32, bk => Laws.jpg.sym.back(pre, bk, cn, sy, post),
    Jenc.encode.huff(Jenc.encode.accounts(), Jenc.encode.acsyms()), M3.acbook.lit(), M2.acbook.eq()),
    Equal.trans(U32 & (List<&2, U32> & U32) & U32, Laws.jpg.sym.back(pre, M3.acbook.lit(), cn, sy, post),
    Laws.jpg.sym.back(pre, M3.acbook.lit(), actab(), sy, post), (sy, (Laws.jpg.nums(post), 1), 1), Equal.cong(Jpeg.Huff,
    U32 & (List<&2, U32> & U32) & U32, tb => Laws.jpg.sym.back(pre, M3.acbook.lit(), tb, sy, post), cn, actab(),
    actab.eq()), sym_rt.ac(pre, hp, sy, hy, post, hq)))

# the AC table the decoder holds, in groups
def actb() -> Jpeg.Huff:
  actab()

# the reader and the ok flag of the decoder's AC state
def acbo(xx: Jpeg.Ac) -> Jpeg.Bits & U32:
  match xx:
    case Jpeg.Ac{_k, _zz, bits, _d, +ok}:
      (bits, ok)

# the decoder's AC loop ended with a model reader holding tail bits rr, its ok flag 1
def AcRes(-xx: Jpeg.Ac, +rr: List<&2, Bool>) -> Type:
  &se: RS -> &e1: {acbo(xx) == (rbits(se, 1), 1) : Jpeg.Bits & U32} -> &e2: {rem(se) == rr : List<&2, Bool>} ->
    {Bool.and(rshort(se), roct8(se)) == True{} : Bool}

# an ended AC loop stays as it is
def acdone(
  pp: Nat,
  +kk: U32,
  +zz: List<&2, U32>,
  +bits: Jpeg.Bits,
  +ok: U32
) -> {Jpeg.decode.ac(pp, Jpeg.Ac{kk, zz, bits, 1, ok}, actb()) == Jpeg.Ac{kk, zz, bits, 1, ok} : Jpeg.Ac}:
  match pp:
    case 0n:
      {==}
    case 1n+_q:
      {==}

# an ended AC loop with the model's reader is a result
def acres.done(
  +pp: Nat,
  +kk: U32,
  +zz: List<&2, U32>,
  +se: RS,
  +rr: List<&2, Bool>,
  e2: {rem(se) == rr : List<&2, Bool>},
  e3: {Bool.and(rshort(se), roct8(se)) == True{} : Bool}
) -> AcRes(Jpeg.decode.ac(pp, Jpeg.Ac{kk, zz, rbits(se, 1), 1, 1}, actb()), rr):
  ea = Equal.sym(Jpeg.Ac, Jpeg.decode.ac(pp, Jpeg.Ac{kk, zz, rbits(se, 1), 1, 1}, actb()), Jpeg.Ac{kk, zz,
    rbits(se, 1), 1, 1}, acdone(pp, kk, zz, rbits(se, 1), 1))
  %ea : AcRes(_, rr)
  (se, {==}, e2, e3)

# no token can follow the end of a block
def acwf.fin(
  ts: List<&2, Laws.JTok>,
  +kk: U32,
  +left: Nat,
  hw: {Laws.jpg.acwf(ts, Laws.JAcSt{kk, left, True{}}) == True{} : Bool}
) -> {ts == [] : List<&2, Laws.JTok>}:
  match ts:
    case Nil{}:
      {==}
    case tt <> _rest:
      match tt:
        case Laws.JTok{_s, _e}:
          Empty.absurd({Laws.JTok{_s, _e} <> _rest == [] : List<&2, Laws.JTok>}, M1.huf.false_true(hw))

# an empty list of bits
def isnil.eq(xs: List<&2, Bool>, hh: {Laws.jpg.isnil(xs) == True{} : Bool}) -> {xs == [] : List<&2, Bool>}:
  match xs:
    case Nil{}:
      {==}
    case _h <> _t:
      Empty.absurd({_h <> _t == [] : List<&2, Bool>}, M1.huf.false_true(hh))

# the rest of the AC loop, as a token's step needs it
def IhAc(-rest: List<&2, Laws.JTok>, +pp: Nat, +rr: List<&2, Bool>) -> Type:
  @kk: U32 -> @zz: List<&2, U32> -> @ss: RS -> @hs: {rshort(ss) == True{} : Bool} ->
    @h8: {roct8(ss) == True{} : Bool} -> @he: {rem(ss) == List.append(&2, Bool, M3.acbits(rest), rr) :
    List<&2, Bool>} -> @hw: {Laws.jpg.acwf(rest, Laws.JAcSt{kk, pp, False{}}) == True{} : Bool} ->
    AcRes(Jpeg.decode.ac(pp, Jpeg.Ac{kk, zz, rbits(ss, 1), 0, 1}, actb()), rr)

# the tail after an empty list of magnitude bits and no tokens is the tail
def tail.nil(
  +ex: List<&2, Bool>,
  +rest: List<&2, Laws.JTok>,
  +rr: List<&2, Bool>,
  xe: {ex == [] : List<&2, Bool>},
  re: {rest == [] : List<&2, Laws.JTok>}
) -> {List.append(&2, Bool, ex, List.append(&2, Bool, M3.acbits(rest), rr)) == rr : List<&2, Bool>}:
  Equal.trans(List<&2, Bool>, List.append(&2, Bool, ex, List.append(&2, Bool, M3.acbits(rest), rr)), List.append(&2,
      Bool,
    M3.acbits(rest), rr), rr, Equal.cong(List<&2, Bool>, List<&2, Bool>, xs => List.append(&2, Bool, xs,
    List.append(&2, Bool, M3.acbits(rest), rr)), ex, [], xe), Equal.cong(List<&2, Laws.JTok>, List<&2, Bool>, ts =>
    List.append(&2, Bool, M3.acbits(ts), rr), rest, [], re))

# the tail after an empty list of magnitude bits
def tail.ex(
  +ex: List<&2, Bool>,
  +rest: List<&2, Laws.JTok>,
  +rr: List<&2, Bool>,
  xe: {ex == [] : List<&2, Bool>}
) -> {List.append(&2, Bool, ex, List.append(&2, Bool, M3.acbits(rest), rr)) == List.append(&2, Bool, M3.acbits(rest),
  rr) : List<&2, Bool>}:
  Equal.cong(List<&2, Bool>, List<&2, Bool>, xs => List.append(&2, Bool, xs, List.append(&2, Bool, M3.acbits(rest),
      rr)),
    ex, [], xe)

# an EOB token ends the block
def sim.eob(
  +pp: Nat,
  +kk: U32,
  +zz: List<&2, U32>,
  +s1: RS,
  +ex: List<&2, Bool>,
  +rest: List<&2, Laws.JTok>,
  +rr: List<&2, Bool>,
  f1: {Bool.and(rshort(s1), roct8(s1)) == True{} : Bool},
  er: {rem(s1) == List.append(&2, Bool, ex, List.append(&2, Bool, M3.acbits(rest), rr)) : List<&2, Bool>},
  hk: {Laws.jpg.isnil(ex) == True{} : Bool},
  hr: {Laws.jpg.acwf(rest, Laws.JAcSt{kk, pp, True{}}) == True{} : Bool}
) -> AcRes(Jpeg.decode.ac(pp, Jpeg.Ac{kk, zz, rbits(s1, 1), 1, 1}, actb()), rr):
  acres.done(pp, kk, zz, s1, rr, Equal.trans(List<&2, Bool>, rem(s1), List.append(&2, Bool, ex, List.append(&2,
    Bool, M3.acbits(rest), rr)), rr, er, tail.nil(ex, rest, rr, isnil.eq(ex, hk), acwf.fin(rest, kk, pp, hr))), f1)

# a ZRL token that reaches index 64 ends the block
def sim.zrl2(
  c2: Bool,
  +pp: Nat,
  +kk: U32,
  +zz: List<&2, U32>,
  +s1: RS,
  +ex: List<&2, Bool>,
  +rest: List<&2, Laws.JTok>,
  +rr: List<&2, Bool>,
  f1: {Bool.and(rshort(s1), roct8(s1)) == True{} : Bool},
  er: {rem(s1) == List.append(&2, Bool, ex, List.append(&2, Bool, M3.acbits(rest), rr)) : List<&2, Bool>},
  +hk: {Bool.and(Laws.jpg.isnil(ex), Bool.or(False{}, c2)) == True{} : Bool},
  hr: {Laws.jpg.acwf(rest, Laws.JAcSt{(kk + 16 : U32), pp, True{}}) == True{} : Bool}
) -> AcRes(Jpeg.decode.ac(pp, Jpeg.decode.ac.zrl.eq(c2, zz, rbits(s1, 1), 1), actb()), rr):
  match c2:
    case True{}:
      acres.done(pp, 64, zz, s1, rr, Equal.trans(List<&2, Bool>, rem(s1), List.append(&2, Bool, ex,
        List.append(&2, Bool, M3.acbits(rest), rr)), rr, er, tail.nil(ex, rest, rr, isnil.eq(ex,
            M3.and_l(Laws.jpg.isnil(ex),
        True{}, hk)), acwf.fin(rest, (kk + 16 : U32), pp, hr))), f1)
    case False{}:
      Empty.absurd(AcRes(Jpeg.decode.ac(pp, Jpeg.decode.ac.zrl.eq(False{}, zz, rbits(s1, 1), 1), actb()), rr),
        M1.huf.false_true(Equal.trans(Bool, False{}, Bool.and(Laws.jpg.isnil(ex), False{}), True{}, Equal.sym(Bool,
        Bool.and(Laws.jpg.isnil(ex), False{}), False{}, M6.and_false_r(Laws.jpg.isnil(ex))), hk)))

# a ZRL token: sixteen zeros, then the loop goes on or the block ends at index 64
def sim.zrl(
  c1: Bool,
  c2: Bool,
  +pp: Nat,
  +kk: U32,
  +zz: List<&2, U32>,
  +s1: RS,
  +ex: List<&2, Bool>,
  +rest: List<&2, Laws.JTok>,
  +rr: List<&2, Bool>,
  +f1: {Bool.and(rshort(s1), roct8(s1)) == True{} : Bool},
  +er: {rem(s1) == List.append(&2, Bool, ex, List.append(&2, Bool, M3.acbits(rest), rr)) : List<&2, Bool>},
  h2: {U32.is_eq((kk + 16 : U32), 64) == c2 : Bool},
  +hk: {Bool.and(Laws.jpg.isnil(ex), Bool.or(c1, c2)) == True{} : Bool},
  hr: {Laws.jpg.acwf(rest, Laws.JAcSt{(kk + 16 : U32), pp, Bool.not(c1)}) == True{} : Bool},
  ih: IhAc(rest, pp, rr)
) -> AcRes(Jpeg.decode.ac(pp, Jpeg.decode.ac.zrl.k(c1, (kk + 16 : U32), zz, rbits(s1, 1), 1), actb()), rr):
  match c1:
    case True{}:
      ih((kk + 16 : U32), zz, s1, M3.and_l(rshort(s1), roct8(s1), f1), M3.and_r(rshort(s1), roct8(s1), f1),
        Equal.trans(List<&2, Bool>, rem(s1), List.append(&2, Bool, ex, List.append(&2, Bool, M3.acbits(rest), rr)),
        List.append(&2, Bool, M3.acbits(rest), rr), er, tail.ex(ex, rest, rr, isnil.eq(ex, M3.and_l(Laws.jpg.isnil(ex),
          True{},
        hk)))), hr)
    case False{}:
      sh = Equal.sym(Bool, U32.is_eq((kk + 16 : U32), 64), c2, h2)
      %sh : AcRes(Jpeg.decode.ac(pp, Jpeg.decode.ac.zrl.eq(_, zz, rbits(s1, 1), 1), actb()), rr)
      sim.zrl2(c2, pp, kk, zz, s1, ex, rest, rr, f1, er, hk, hr)

# a stored coefficient: the loop goes on, or the block ends at index 64
def sim.st(
  c3: Bool,
  +pp: Nat,
  +n2: U32,
  +zz: List<&2, U32>,
  +s2: RS,
  +rest: List<&2, Laws.JTok>,
  +rr: List<&2, Bool>,
  +f2: {Bool.and(rshort(s2), roct8(s2)) == True{} : Bool},
  +e2: {rem(s2) == List.append(&2, Bool, M3.acbits(rest), rr) : List<&2, Bool>},
  hr: {Laws.jpg.acwf(rest, Laws.JAcSt{n2, pp, c3}) == True{} : Bool},
  ih: IhAc(rest, pp, rr)
) -> AcRes(Jpeg.decode.ac(pp, Jpeg.decode.ac.stored(c3, n2, zz, rbits(s2, 1), 1), actb()), rr):
  match c3:
    case True{}:
      acres.done(pp, n2, zz, s2, rr, Equal.trans(List<&2, Bool>, rem(s2), List.append(&2, Bool, M3.acbits(rest), rr),
        rr, e2, Equal.cong(List<&2, Laws.JTok>, List<&2, Bool>, ts => List.append(&2, Bool, M3.acbits(ts), rr), rest,
            [],
        acwf.fin(rest, n2, pp, hr))), f2)
    case False{}:
      ih(n2, zz, s2, M3.and_l(rshort(s2), roct8(s2), f2), M3.and_r(rshort(s2), roct8(s2), f2), e2, hr)

# a run and size token's own check, by the two kinds it is not
def RunOk(-c1: Bool, -c2: Bool, +sym: U32, -ex: List<&2, Bool>) -> Type:
  {Bool.and(Bool.not(c1), Bool.and(Bool.not(c2), Nat.is_eq(List.length(&2, Bool, ex), U32.to_nat(U32.and(15,
    sym))))) == True{} : Bool}

# the tokens after a run and size token, read in full from the index after it
def RunRest(-rest: List<&2, Laws.JTok>, +kk: U32, +sym: U32, +pp: Nat) -> Type:
  {Laws.jpg.acwf(rest, Laws.JAcSt{((kk + U32.shrn(sym, 4n) : U32) + 1 : U32), pp, U32.is_eq(((kk + U32.shrn(sym,
    4n) : U32) + 1 :
    U32), 64)}) == True{} : Bool}

# a run and size token: its magnitude bits read, the coefficient stored at its index
def sim.run(
  c1: Bool,
  c2: Bool,
  +pp: Nat,
  +sym: U32,
  +kk: U32,
  +zz: List<&2, U32>,
  +s1: RS,
  +ex: List<&2, Bool>,
  +rest: List<&2, Laws.JTok>,
  +rr: List<&2, Bool>,
  +f1: {Bool.and(rshort(s1), roct8(s1)) == True{} : Bool},
  +er: {rem(s1) == List.append(&2, Bool, ex, List.append(&2, Bool, M3.acbits(rest), rr)) : List<&2, Bool>},
  hk: RunOk(c1, c2, sym, ex),
  hr: RunRest(rest, kk, sym, pp),
  ih: IhAc(rest, pp, rr)
) -> AcRes(Jpeg.decode.ac(pp, Jpeg.decode.ac.run.b(c1, c2, U32.and(15, sym), (kk + U32.shrn(sym, 4n) : U32), rbits(s1,
  1), zz, 1), actb()), rr):
  match c1:
    case True{}:
      Empty.absurd(AcRes(Jpeg.decode.ac(pp, Jpeg.decode.ac.run.b(True{}, c2, U32.and(15, sym), (kk + U32.shrn(sym,
        4n) : U32), rbits(s1, 1), zz, 1), actb()), rr), M1.huf.false_true(hk))
    case False{}:
      match c2:
        case True{}:
          Empty.absurd(AcRes(Jpeg.decode.ac(pp, Jpeg.decode.ac.run.b(False{}, True{}, U32.and(15, sym), (kk +
            U32.shrn(sym, 4n) : U32), rbits(s1, 1), zz, 1), actb()), rr), M1.huf.false_true(hk))
        case False{}:
          +sz = U32.and(15, sym)
          +nk = (kk + U32.shrn(sym, 4n) : U32)
          +ln = List.length(&2, Bool, ex)
          +mr = List.append(&2, Bool, M3.acbits(rest), rr)
          +s2 = radv(ln, s1)
          +hs1 = {M3.and_l(rshort(s1), roct8(s1), f1) : {rshort(s1) == True{} : Bool}}
          +h81 = {M3.and_r(rshort(s1), roct8(s1), f1) : {roct8(s1) == True{} : Bool}}
          +el = {M1.ras.nat_eq_true(ln, U32.to_nat(sz), hk) : {ln == U32.to_nat(sz) : Nat}}
          +hl = {Equal.trans(Bool, Nat.is_le(ln, List.length(&2, Bool, rem(s1))), Nat.is_le(ln, List.length(&2,
            Bool, List.append(&2, Bool, ex, mr))), True{}, Equal.cong(List<&2, Bool>, Bool, xs => Nat.is_le(ln,
            List.length(&2, Bool, xs)), rem(s1), List.append(&2, Bool, ex, mr), er), len_app(ex, mr)) :
            {Nat.is_le(ln, List.length(&2, Bool, rem(s1))) == True{} : Bool}}
          +vv = M2.vfold(List.take(&2, Bool, rem(s1), ln), 0)
          +erd = {Equal.trans(Jpeg.Bits & U32, Jpeg.decode.read.n(sz, rbits(s1, 1)), canon(U32.to_nat(sz), s1,
            1, 0), (rbits(s2, 1), vv), read_canon(sz, s1, 1), Equal.trans(Jpeg.Bits & U32,
            canon(U32.to_nat(sz), s1, 1, 0), canon(ln, s1, 1, 0), (rbits(s2, 1), vv), Equal.cong(Nat,
            Jpeg.Bits & U32, mm => canon(mm, s1, 1, 0), U32.to_nat(sz), ln, Equal.sym(Nat, ln, U32.to_nat(sz),
            el)), rread(ln, s1, 1, 0, hs1, h81, hl))) : {Jpeg.decode.read.n(sz, rbits(s1, 1)) ==
            (rbits(s2, 1), vv) : Jpeg.Bits & U32}}
          sr = Equal.sym(Jpeg.Bits & U32, Jpeg.decode.read.n(sz, rbits(s1, 1)), (rbits(s2, 1), vv), erd)
          %sr : AcRes(Jpeg.decode.ac(pp, Jpeg.decode.ac.store(_, sz, nk, zz, 1), actb()), rr)
          sim.st(U32.is_eq((nk + 1 : U32), 64), pp, (nk + 1 : U32), List.set(&2, U32, zz, U32.to_nat(nk),
            Jpeg.decode.extend(sz, vv)), s2, rest, rr, radv_ok(ln, s1, hs1, h81), rem_after(ex, s1, mr, hs1, h81,
            er), hr, ih)

# one token's step, by its kind
def sim.k(
  e0: Bool,
  e2: Bool,
  +pp: Nat,
  +sym: U32,
  +kk: U32,
  +zz: List<&2, U32>,
  +s1: RS,
  +ex: List<&2, Bool>,
  +rest: List<&2, Laws.JTok>,
  +rr: List<&2, Bool>,
  +f1: {Bool.and(rshort(s1), roct8(s1)) == True{} : Bool},
  +er: {rem(s1) == List.append(&2, Bool, ex, List.append(&2, Bool, M3.acbits(rest), rr)) : List<&2, Bool>},
  +hk: {Laws.jpg.acok.k(e0, e2, sym, ex, kk) == True{} : Bool},
  +hr: {Laws.jpg.acwf(rest, Laws.jpg.acnx.k(e0, e2, sym, kk, 1n+pp)) == True{} : Bool},
  ih: IhAc(rest, pp, rr)
) -> AcRes(Jpeg.decode.ac(pp, Jpeg.decode.ac.sym.b(e0, e2, sym, rbits(s1, 1), kk, zz, 1), actb()), rr):
  match e0:
    case True{}:
      sim.eob(pp, kk, zz, s1, ex, rest, rr, f1, er, hk, hr)
    case False{}:
      match e2:
        case True{}:
          sim.zrl(U32.is_lt((kk + 16 : U32), 64), U32.is_eq((kk + 16 : U32), 64), pp, kk, zz, s1, ex, rest, rr, f1, er,
            {==}, hk, hr, ih)
        case False{}:
          sim.run(U32.is_eq(U32.and(15, sym), 0), U32.is_ge((kk + U32.shrn(sym, 4n) : U32), 64), pp, sym, kk, zz, s1,
            ex, rest, rr, f1, er, hk, hr, ih)

# the decoder's AC loop over AC tokens' bits: every token read, the reader left at the tail, ok still 1
def huf.sim(
  ts: List<&2, Laws.JTok>,
  +left: Nat,
  +kk: U32,
  +zz: List<&2, U32>,
  +ss: RS,
  +rr: List<&2, Bool>,
  +hs: {rshort(ss) == True{} : Bool},
  +h8: {roct8(ss) == True{} : Bool},
  +he: {rem(ss) == List.append(&2, Bool, M3.acbits(ts), rr) : List<&2, Bool>},
  +hw: {Laws.jpg.acwf(ts, Laws.JAcSt{kk, left, False{}}) == True{} : Bool}
) -> AcRes(Jpeg.decode.ac(left, Jpeg.Ac{kk, zz, rbits(ss, 1), 0, 1}, actb()), rr):
  match ts:
    case Nil{}:
      Empty.absurd(AcRes(Jpeg.decode.ac(left, Jpeg.Ac{kk, zz, rbits(ss, 1), 0, 1}, actb()), rr), M1.huf.false_true(hw))
    case +tt <> +rest:
      match tt:
        case Laws.JTok{+sym, +ex}:
          match left:
            case 0n:
              Empty.absurd(AcRes(Jpeg.decode.ac(0n, Jpeg.Ac{kk, zz, rbits(ss, 1), 0, 1}, actb()), rr),
                M1.huf.false_true(hw))
            case 1n+ +pp:
              +e0 = U32.is_eq(sym, 0)
              +e2 = U32.is_eq(sym, 240)
              +ha = {M1.also_l(Laws.jpg.acok(Laws.JTok{sym, ex}, Laws.JAcSt{kk, 1n+pp, False{}}), Laws.jpg.acwf(rest,
                Laws.jpg.acnx(Laws.JTok{sym, ex}, Laws.JAcSt{kk, 1n+pp,
                False{}})), hw) : {Bool.and(Laws.jpg.memb(sym, Jenc.encode.acsyms()), Laws.jpg.acok.k(e0, e2, sym, ex,
                  kk)) ==
                True{} : Bool}}
              +hr = {M1.also_r(Laws.jpg.acok(Laws.JTok{sym, ex}, Laws.JAcSt{kk, 1n+pp, False{}}), Laws.jpg.acwf(rest,
                Laws.jpg.acnx(Laws.JTok{sym, ex}, Laws.JAcSt{kk, 1n+pp,
                False{}})), hw) : {Laws.jpg.acwf(rest, Laws.jpg.acnx.k(e0, e2, sym, kk, 1n+pp)) == True{} : Bool}}
              +cc = M3.code.ac(sym)
              +tl = List.append(&2, Bool, ex, List.append(&2, Bool, M3.acbits(rest), rr))
              +he1 = {Equal.trans(List<&2, Bool>, rem(ss), List.append(&2, Bool, List.append(&2, Bool, cc,
                List.append(&2, Bool, ex, M3.acbits(rest))), rr), List.append(&2, Bool, cc, tl), he,
                Equal.trans(List<&2, Bool>, List.append(&2, Bool, List.append(&2, Bool, cc, List.append(&2, Bool, ex,
                M3.acbits(rest))), rr), List.append(&2, Bool, cc, List.append(&2, Bool, List.append(&2, Bool, ex,
                M3.acbits(rest)), rr)), List.append(&2, Bool, cc, tl), M3.huf.app_assoc(cc, List.append(&2, Bool, ex,
                M3.acbits(rest)), rr), Equal.cong(List<&2, Bool>, List<&2, Bool>, xs => List.append(&2, Bool, cc, xs),
                List.append(&2, Bool, List.append(&2, Bool, ex, M3.acbits(rest)), rr), tl, M3.huf.app_assoc(ex,
                    M3.acbits(rest),
                rr)))) : {rem(ss) == List.append(&2, Bool, cc, tl) : List<&2, Bool>}}
              +s1 = radv(List.length(&2, Bool, cc), ss)
              +eh = {huff.ac(ss, 1, sym, tl, hs, h8, he1, memb.ac(Jenc.encode.acsyms(), sym, M3.and_l(Laws.jpg.memb(sym,
                Jenc.encode.acsyms()), Laws.jpg.acok.k(e0, e2, sym, ex, kk), ha), all.ac.ok())) : {Jpeg.decode.huff(16n,
                Jpeg.Ask{None{}, 0, 0, rbits(ss, 1)}, actb()) == Jpeg.Hit{sym, rbits(s1, 1), 1} : Jpeg.Hit}}
              sh = Equal.sym(Jpeg.Hit, Jpeg.decode.huff(16n, Jpeg.Ask{None{}, 0, 0, rbits(ss, 1)}, actb()),
                Jpeg.Hit{sym, rbits(s1, 1), 1}, eh)
              %sh : AcRes(Jpeg.decode.ac(pp, Jpeg.decode.ac.step(_, kk, zz, 1), actb()), rr)
              sim.k(e0, e2, pp, sym, kk, zz, s1, ex, rest, rr, radv_ok(List.length(&2, Bool, cc), ss, hs, h8),
                rem_after(cc, ss, tl, hs, h8, he1), M3.and_r(Laws.jpg.memb(sym, Jenc.encode.acsyms()),
                  Laws.jpg.acok.k(e0, e2,
                sym, ex, kk), ha), hr, k2 => z2 => s2 => a2 => b2 => c2 => d2 => huf.sim(rest, pp, k2, z2, s2, rr, a2,
                    b2,
                c2, d2))

# the DC table the decoder holds, in groups
def dctb() -> Jpeg.Huff:
  dctab()

# the quantisation table the decoder holds for the encoder's frame: 64 ones
def ones64() -> List<&2, U32>:
  List.replicate(U32, 64n, 1)

# the reader and the ok flag of a decoded block
def blkbo(bk: Jpeg.Blk) -> Jpeg.Bits & U32:
  match bk:
    case Jpeg.Blk{_s, bits, _p, +ok}:
      (bits, ok)

# a reader and a flag, the flag times qo
def bomul(bo: Jpeg.Bits & U32, +qo: U32) -> Jpeg.Bits & U32:
  match bo:
    case (bits, +ok):
      (bits, (ok * qo : U32))

# a decoded block ended with a model reader holding tail bits rr, its ok flag 1
def BlkRes(-bk: Jpeg.Blk, +rr: List<&2, Bool>) -> Type:
  &se: RS -> &e1: {blkbo(bk) == (rbits(se, 1), 1) : Jpeg.Bits & U32} -> &e2: {rem(se) == rr : List<&2, Bool>}
    -> {Bool.and(rshort(se), roct8(se)) == True{} : Bool}

# the block from its AC loop keeps the loop's reader, its flag times the quantisation flag
def blk.ac.eq(
  xx: Jpeg.Ac,
  +pred: U32,
  +qq: List<&2, U32>,
  +qo: U32
) -> {blkbo(Jpeg.decode.block.ac(xx, pred, qq, qo)) == bomul(acbo(xx), qo) : Jpeg.Bits & U32}:
  match xx:
    case Jpeg.Ac{_k, _zz, _bits, _d, _ok}:
      {==}

# a block from an AC loop that ended well
def blk.from.ac(
  xx: Jpeg.Ac,
  +pred: U32,
  +rr: List<&2, Bool>,
  res: AcRes(xx, rr)
) -> BlkRes(Jpeg.decode.block.ac(xx, pred, ones64(), Jpeg.decode.qok(ones64())), rr):
  (se, e1, e2, e3) = res
  +qo = Jpeg.decode.qok(ones64())
  (se, Equal.trans(Jpeg.Bits & U32, blkbo(Jpeg.decode.block.ac(xx, pred, ones64(), qo)), bomul(acbo(xx), qo),
    (rbits(se, 1), 1), blk.ac.eq(xx, pred, ones64(), qo), Equal.cong(Jpeg.Bits & U32, Jpeg.Bits & U32, bo =>
    bomul(bo, qo), acbo(xx), (rbits(se, 1), 1), e1)), e2, e3)

# a list of length zero is empty
def len0(
  xs: List<&2, Bool>,
  hh: {Nat.is_eq(List.length(&2, Bool, xs), 0n) == True{} : Bool}
) -> {xs == [] : List<&2, Bool>}:
  match xs:
    case Nil{}:
      {==}
    case _h <> _t:
      Empty.absurd({_h <> _t == [] : List<&2, Bool>}, M1.huf.false_true(hh))

# the DC magnitude, none for size 0, then the AC loop
def bsim.z(
  zz: Bool,
  +dcs: U32,
  +dcx: List<&2, Bool>,
  +acs: List<&2, Laws.JTok>,
  +pred: U32,
  +s1: RS,
  +rr: List<&2, Bool>,
  +f1: {Bool.and(rshort(s1), roct8(s1)) == True{} : Bool},
  +er: {rem(s1) == List.append(&2, Bool, dcx, List.append(&2, Bool, M3.acbits(acs), rr)) : List<&2, Bool>},
  +hz: {U32.is_eq(dcs, 0) == zz : Bool},
  +hl: {Nat.is_eq(List.length(&2, Bool, dcx), U32.to_nat(dcs)) == True{} : Bool},
  +hw: {Laws.jpg.acwf(acs, Laws.JAcSt{1, 63n, False{}}) == True{} : Bool}
) -> BlkRes(Jpeg.decode.block.cat(zz, dcs, rbits(s1, 1), pred, 1, actb(), ones64(), Jpeg.decode.qok(ones64())), rr):
  match zz:
    case True{}:
      +hs1 = {M3.and_l(rshort(s1), roct8(s1), f1) : {rshort(s1) == True{} : Bool}}
      +h81 = {M3.and_r(rshort(s1), roct8(s1), f1) : {roct8(s1) == True{} : Bool}}
      +mr = List.append(&2, Bool, M3.acbits(acs), rr)
      +dz = {M1.ueq(dcs, 0, hz) : {dcs == 0 : U32}}
      +hl0 = {Equal.trans(Bool, Nat.is_eq(List.length(&2, Bool, dcx), U32.to_nat(0)), Nat.is_eq(List.length(&2, Bool,
        dcx), U32.to_nat(dcs)), True{}, Equal.cong(U32, Bool, xx => Nat.is_eq(List.length(&2, Bool, dcx),
        U32.to_nat(xx)), 0, dcs, Equal.sym(U32, dcs, 0, dz)), hl) : {Nat.is_eq(List.length(&2, Bool, dcx), 0n) ==
        True{} : Bool}}
      +e1 = {Equal.trans(List<&2, Bool>, rem(s1), List.append(&2, Bool, dcx, mr), mr, er, Equal.cong(List<&2, Bool>,
        List<&2, Bool>, xs => List.append(&2, Bool, xs, mr), dcx, [], len0(dcx, hl0))) : {rem(s1) == mr :
        List<&2, Bool>}}
      +dc = (pred + Jpeg.decode.extend(0, 0) : U32)
      blk.from.ac(Jpeg.decode.ac(63n, Jpeg.Ac{1, dc <> Jpeg.decode.zeros(63n, []), rbits(s1, 1), 0, 1}, actb()),
        dc, rr, huf.sim(acs, 63n, 1, dc <> Jpeg.decode.zeros(63n, []), s1, rr, hs1, h81, e1, hw))
    case False{}:
      +hs1 = {M3.and_l(rshort(s1), roct8(s1), f1) : {rshort(s1) == True{} : Bool}}
      +h81 = {M3.and_r(rshort(s1), roct8(s1), f1) : {roct8(s1) == True{} : Bool}}
      +mr = List.append(&2, Bool, M3.acbits(acs), rr)
      +ln = List.length(&2, Bool, dcx)
      +s2 = radv(ln, s1)
      +el = {M1.ras.nat_eq_true(ln, U32.to_nat(dcs), hl) : {ln == U32.to_nat(dcs) : Nat}}
      +hl2 = {Equal.trans(Bool, Nat.is_le(ln, List.length(&2, Bool, rem(s1))), Nat.is_le(ln, List.length(&2,
        Bool, List.append(&2, Bool, dcx, mr))), True{}, Equal.cong(List<&2, Bool>, Bool, xs => Nat.is_le(ln,
        List.length(&2, Bool, xs)), rem(s1), List.append(&2, Bool, dcx, mr), er), len_app(dcx, mr)) :
        {Nat.is_le(ln, List.length(&2, Bool, rem(s1))) == True{} : Bool}}
      +vv = M2.vfold(List.take(&2, Bool, rem(s1), ln), 0)
      +erd = {Equal.trans(Jpeg.Bits & U32, Jpeg.decode.read.n(dcs, rbits(s1, 1)), canon(U32.to_nat(dcs), s1, 1,
        0), (rbits(s2, 1), vv), read_canon(dcs, s1, 1), Equal.trans(Jpeg.Bits & U32, canon(U32.to_nat(dcs),
        s1, 1, 0), canon(ln, s1, 1, 0), (rbits(s2, 1), vv), Equal.cong(Nat, Jpeg.Bits & U32, mm =>
        canon(mm, s1, 1, 0), U32.to_nat(dcs), ln, Equal.sym(Nat, ln, U32.to_nat(dcs), el)), rread(ln, s1, 1, 0,
        hs1, h81, hl2))) : {Jpeg.decode.read.n(dcs, rbits(s1, 1)) == (rbits(s2, 1), vv) : Jpeg.Bits & U32}}
      +dc = (pred + Jpeg.decode.extend(dcs, vv) : U32)
      sr = Equal.sym(Jpeg.Bits & U32, Jpeg.decode.read.n(dcs, rbits(s1, 1)), (rbits(s2, 1), vv), erd)
      %sr : BlkRes(Jpeg.decode.block.diff(_, dcs, pred, 1, actb(), ones64(), Jpeg.decode.qok(ones64())), rr)
      blk.from.ac(Jpeg.decode.ac(63n, Jpeg.Ac{1, dc <> Jpeg.decode.zeros(63n, []), rbits(s2, 1), 0, 1}, actb()),
        dc, rr, huf.sim(acs, 63n, 1, dc <> Jpeg.decode.zeros(63n, []), s2, rr, M3.and_l(rshort(s2), roct8(s2),
        radv_ok(ln, s1, hs1, h81)), M3.and_r(rshort(s2), roct8(s2), radv_ok(ln, s1, hs1, h81)),
        rem_after(dcx, s1, mr, hs1, h81, er), hw))

# the decoder reads one block's bits whole: the reader left at the tail, ok still 1
def bsim(
  bt: Laws.JBlkTok,
  +pred: U32,
  +ss: RS,
  +rr: List<&2, Bool>,
  +hs: {rshort(ss) == True{} : Bool},
  +h8: {roct8(ss) == True{} : Bool},
  +he: {rem(ss) == List.append(&2, Bool, M3.blkbits(bt), rr) : List<&2, Bool>},
  +hw: {Laws.jpg.blkwf(bt) == True{} : Bool}
) -> BlkRes(Jpeg.decode.block.go(rbits(ss, 1), pred, dctb(), actb(), ones64()), rr):
  match bt:
    case Laws.JBlkTok{+dcs, +dcx, +acs}:
      +cc = M3.code.dc(dcs)
      +tl = List.append(&2, Bool, dcx, List.append(&2, Bool, M3.acbits(acs), rr))
      +he1 = {Equal.trans(List<&2, Bool>, rem(ss), List.append(&2, Bool, List.append(&2, Bool, cc, List.append(&2,
        Bool, dcx, M3.acbits(acs))), rr), List.append(&2, Bool, cc, tl), he, Equal.trans(List<&2, Bool>,
        List.append(&2, Bool, List.append(&2, Bool, cc, List.append(&2, Bool, dcx, M3.acbits(acs))), rr),
        List.append(&2, Bool, cc, List.append(&2, Bool, List.append(&2, Bool, dcx, M3.acbits(acs)), rr)),
        List.append(&2, Bool, cc, tl), M3.huf.app_assoc(cc, List.append(&2, Bool, dcx, M3.acbits(acs)), rr),
        Equal.cong(List<&2, Bool>, List<&2, Bool>, xs => List.append(&2, Bool, cc, xs), List.append(&2, Bool,
        List.append(&2, Bool, dcx, M3.acbits(acs)), rr), tl, M3.huf.app_assoc(dcx, M3.acbits(acs), rr)))) : {rem(ss) ==
        List.append(&2, Bool, cc, tl) : List<&2, Bool>}}
      +ha = {M3.and_r(Laws.jpg.memb(dcs, Jenc.encode.dcsyms()), Bool.and(Nat.is_eq(List.length(&2, Bool, dcx),
        U32.to_nat(dcs)), Laws.jpg.acwf(acs, Laws.JAcSt{1, 63n, False{}})), hw) : {Bool.and(Nat.is_eq(List.length(&2,
          Bool, dcx),
        U32.to_nat(dcs)), Laws.jpg.acwf(acs, Laws.JAcSt{1, 63n, False{}})) == True{} : Bool}}
      +s1 = radv(List.length(&2, Bool, cc), ss)
      +eh = {huff.dc(ss, 1, dcs, tl, hs, h8, he1, memb.dc(Jenc.encode.dcsyms(), dcs, M3.and_l(Laws.jpg.memb(dcs,
        Jenc.encode.dcsyms()), Bool.and(Nat.is_eq(List.length(&2, Bool, dcx), U32.to_nat(dcs)), Laws.jpg.acwf(acs,
          Laws.JAcSt{1,
        63n, False{}})), hw), all.dc.ok())) : {Jpeg.decode.huff(16n, Jpeg.Ask{None{}, 0, 0, rbits(ss, 1)},
        dctb()) == Jpeg.Hit{dcs, rbits(s1, 1), 1} : Jpeg.Hit}}
      sh = Equal.sym(Jpeg.Hit, Jpeg.decode.huff(16n, Jpeg.Ask{None{}, 0, 0, rbits(ss, 1)}, dctb()), Jpeg.Hit{dcs,
        rbits(s1, 1), 1}, eh)
      %sh : BlkRes(Jpeg.decode.block.dc(_, pred, actb(), ones64(), Jpeg.decode.qok(ones64())), rr)
      bsim.z(U32.is_eq(dcs, 0), dcs, dcx, acs, pred, s1, rr, radv_ok(List.length(&2, Bool, cc), ss, hs, h8),
        rem_after(cc, ss, tl, hs, h8, he1), {==}, M3.and_l(Nat.is_eq(List.length(&2, Bool, dcx), U32.to_nat(dcs)),
        Laws.jpg.acwf(acs, Laws.JAcSt{1, 63n, False{}}), ha), M3.and_r(Nat.is_eq(List.length(&2, Bool, dcx),
          U32.to_nat(dcs)),
        Laws.jpg.acwf(acs, Laws.JAcSt{1, 63n, False{}}), ha))

# the tables the decoder holds after the encoder's header, the Huffman tables in groups
def tabsg() -> Jpeg.Tabs:
  Jpeg.Tabs{List.replicate(U32, 64n, 1), [], [], [], dctb(), Jpeg.decode.huff0(), Jpeg.decode.huff0(),
    Jpeg.decode.huff0(), actb(), Jpeg.decode.huff0(), Jpeg.decode.huff0(), Jpeg.decode.huff0()}

# the decoder's tables after the encoder's header are the ones in groups
def tabs.eq() -> {Laws.jpg.enc.tabs() == tabsg() : Jpeg.Tabs}:
  Equal.trans(Jpeg.Tabs, Laws.jpg.enc.tabs(), Jpeg.Tabs{List.replicate(U32, 64n, 1), [], [], [], dctb(),
    Jpeg.decode.huff0(), Jpeg.decode.huff0(), Jpeg.decode.huff0(), Jpeg.decode.canon(272n, 0n,
    Jenc.encode.accounts(), Jenc.encode.acsyms(), 0, 0, [], [], []), Jpeg.decode.huff0(), Jpeg.decode.huff0(),
    Jpeg.decode.huff0()}, tabsg(), Equal.cong(Jpeg.Huff, Jpeg.Tabs, hh => Jpeg.Tabs{List.replicate(U32, 64n, 1), [],
    [], [], hh, Jpeg.decode.huff0(), Jpeg.decode.huff0(), Jpeg.decode.huff0(), Jpeg.decode.canon(272n, 0n,
    Jenc.encode.accounts(), Jenc.encode.acsyms(), 0, 0, [], [], []), Jpeg.decode.huff0(), Jpeg.decode.huff0(),
    Jpeg.decode.huff0()}, Jpeg.decode.canon(272n, 0n, Jenc.encode.dccounts(), Jenc.encode.dcsyms(), 0, 0, [], [], []),
    dctb(), dctab.eq()), Equal.cong(Jpeg.Huff, Jpeg.Tabs, hh => Jpeg.Tabs{List.replicate(U32, 64n, 1), [], [],
    [], dctb(), Jpeg.decode.huff0(), Jpeg.decode.huff0(), Jpeg.decode.huff0(), hh, Jpeg.decode.huff0(),
    Jpeg.decode.huff0(), Jpeg.decode.huff0()}, Jpeg.decode.canon(272n, 0n, Jenc.encode.accounts(),
    Jenc.encode.acsyms(), 0, 0, [], [], []), actb(), actab.eq()))

# an entry of [0, 0, 0] at a natural index, or its default
def at000.n(nn: Nat) -> {Jpeg.decode.at.m(List.get(&2, U32, [0, 0, 0], nn)) == 0 : U32}:
  match nn:
    case 0n:
      {==}
    case 1n+0n:
      {==}
    case 1n+1n+0n:
      {==}
    case 1n+1n+1n+_m:
      {==}

# every entry of [0, 0, 0] is 0, and so is its default
def at000(+cc: U32) -> {Jpeg.decode.at([0, 0, 0], cc) == 0 : U32}:
  at000.n(U32.to_nat(cc))

# a block of the encoder's frame and scan reads with the tables in groups and the quantisation table of ones
def bof(
  +bits: Jpeg.Bits,
  +cc: U32,
  +preds: Jpeg.Preds,
  +ww: U32,
  +hh: U32
) -> {Jpeg.decode.block.of(bits, cc, preds, Laws.jpg.enc.frame(ww, hh), Laws.jpg.enc.scan(),
  tabsg()) == Jpeg.decode.block.go(bits, Jpeg.decode.pred.get(preds, cc), dctb(), actb(), ones64()) : Jpeg.Blk}:
  +ez = at000(cc)
  +ei = at000(Jpeg.decode.index([1, 2, 3], False{}, Jpeg.decode.at([1, 2, 3], cc), 0))
  ez1 = Equal.sym(U32, Jpeg.decode.at([0, 0, 0], cc), 0, ez)
  ei1 = Equal.sym(U32, Jpeg.decode.at([0, 0, 0], Jpeg.decode.index([1, 2, 3], False{}, Jpeg.decode.at([1, 2, 3], cc),
    0)), 0, ei)
  %ez1 : {Jpeg.decode.block.go(bits, Jpeg.decode.pred.get(preds, cc), Jpeg.decode.dc.get(tabsg(), _),
    Jpeg.decode.ac.get(tabsg(), _), Jpeg.decode.q.get(tabsg(), Jpeg.decode.at([0, 0, 0], Jpeg.decode.index([1, 2, 3],
    False{}, Jpeg.decode.at([1, 2, 3], cc), 0)))) == Jpeg.decode.block.go(bits, Jpeg.decode.pred.get(preds, cc),
    dctb(), actb(), ones64()) : Jpeg.Blk}
  %ei1 : {Jpeg.decode.block.go(bits, Jpeg.decode.pred.get(preds, cc), Jpeg.decode.dc.get(tabsg(), 0),
    Jpeg.decode.ac.get(tabsg(), 0), Jpeg.decode.q.get(tabsg(), _)) == Jpeg.decode.block.go(bits,
    Jpeg.decode.pred.get(preds, cc), dctb(), actb(), ones64()) : Jpeg.Blk}
  {==}

# the next block after a step of the walk: the component the step names, read with the tables in groups
def NextBlk(-aa: Jpeg.Adv, +bits: Jpeg.Bits, +preds: Jpeg.Preds, +pred: U32, +cc: U32, +ww: U32, +hh: U32) -> Type:
  {Jpeg.decode.block.next.go(aa, bits, preds, pred, cc, Laws.jpg.enc.frame(ww, hh), Laws.jpg.enc.scan(), tabsg()) ==
    Jpeg.decode.block.go(bits, Jpeg.decode.pred.get(Jpeg.decode.preds.next(0, preds, cc, pred),
    Jpeg.decode.ctrl.comp(Jpeg.decode.adv.ctrl(aa))), dctb(), actb(), ones64()) : Jpeg.Blk}

# the walk to the next MCU, in its row or the next: component 0, no restart marker
def nx.mx(
  inb: Bool,
  +mcu: U32,
  +mx: U32,
  +my: U32,
  +rst: U32,
  +bits: Jpeg.Bits,
  +preds: Jpeg.Preds,
  +pred: U32,
  +cc: U32,
  +ww: U32,
  +hh: U32
) -> NextBlk(Jpeg.decode.adv.mx(inb, mcu, mx, my, rst, 0), bits, preds, pred, cc, ww, hh):
  match inb:
    case True{}:
      bof(bits, 0, Jpeg.decode.preds.next(0, preds, cc, pred), ww, hh)
    case False{}:
      bof(bits, 0, Jpeg.decode.preds.next(0, preds, cc, pred), ww, hh)

# the walk to the next component, or to the next MCU
def nx.comp(
  more: Bool,
  +cc: U32,
  +mx: U32,
  +my: U32,
  +mcu: U32,
  +rst: U32,
  +bits: Jpeg.Bits,
  +preds: Jpeg.Preds,
  +pred: U32,
  +ww: U32,
  +hh: U32
) -> NextBlk(Jpeg.decode.adv.comp(more, cc, mx, my, mcu, rst, ww, 1, 0), bits, preds, pred, cc, ww, hh):
  match more:
    case True{}:
      bof(bits, (cc + 1 : U32), Jpeg.decode.preds.next(0, preds, cc, pred), ww, hh)
    case False{}:
      nx.mx(U32.is_lt((mx + 1 : U32), Jpeg.decode.ceil(ww, (1 * 8 : U32))), (mcu + 1 : U32), (mx + 1 : U32), my, rst,
        bits, preds, pred, cc, ww, hh)

# the walk to the next data unit, or to the next component
def nx.bi(
  more: Bool,
  +cc: U32,
  +bi: U32,
  +mx: U32,
  +my: U32,
  +mcu: U32,
  +rst: U32,
  +bits: Jpeg.Bits,
  +preds: Jpeg.Preds,
  +pred: U32,
  +ww: U32,
  +hh: U32
) -> NextBlk(Jpeg.decode.adv.bi(more, cc, bi, mx, my, mcu, rst, ww, 1, 3, 0), bits, preds, pred, cc, ww, hh):
  match more:
    case True{}:
      bof(bits, cc, Jpeg.decode.preds.next(0, preds, cc, pred), ww, hh)
    case False{}:
      nx.comp(U32.is_lt((cc + 1 : U32), 3), cc, mx, my, mcu, rst, bits, preds, pred, ww, hh)

# with no restart interval, the decoder's next block is the next component's, read with the tables in groups
def bnext(
  +bits: Jpeg.Bits,
  +preds: Jpeg.Preds,
  +pred: U32,
  ctrl: Jpeg.Ctrl,
  +ww: U32,
  +hh: U32
) -> {Jpeg.decode.block.next(bits, preds, pred, ctrl, Laws.jpg.enc.frame(ww, hh), Laws.jpg.enc.scan(), tabsg(),
  0) == Jpeg.decode.block.go(bits, Jpeg.decode.pred.get(Jpeg.decode.preds.next(0, preds, Jpeg.decode.ctrl.comp(ctrl),
  pred), Jpeg.decode.ctrl.comp(Jpeg.decode.adv.ctrl(Jpeg.decode.adv(ctrl, Laws.jpg.enc.frame(ww, hh),
  Laws.jpg.enc.scan(), 0)))), dctb(), actb(), ones64()) : Jpeg.Blk}:
  match ctrl:
    case Jpeg.Ctrl{+cc, +bi, +mx, +my, +mcu, +rst}:
      +fi = Jpeg.decode.index([1, 2, 3], False{}, Jpeg.decode.at([1, 2, 3], cc), 0)
      +hi = Jpeg.decode.at([1, 1, 1], fi)
      +vi = Jpeg.decode.at([1, 1, 1], fi)
      nx.bi(U32.is_lt((bi + 1 : U32), (hi * vi : U32)), cc, bi, mx, my, mcu, rst, bits, preds, pred, ww, hh)

# the flag of a reader and a flag
def bo.ok(bo: Jpeg.Bits & U32) -> U32:
  match bo:
    case (_b, +ok):
      ok

# the reader of a reader and a flag
def bo.bits(bo: Jpeg.Bits & U32) -> Jpeg.Bits:
  match bo:
    case (bits, _o):
      bits

# a block result moved along an equality of blocks
def blkres.tr(
  -aa: Jpeg.Blk,
  -bb: Jpeg.Blk,
  +rr: List<&2, Bool>,
  ee: {aa == bb : Jpeg.Blk},
  res: BlkRes(aa, rr)
) -> BlkRes(bb, rr):
  %ee : BlkRes(_, rr)
  res

# the decoder's block loop over blocks that each read whole returns a picture
def huf.fl(
  ts: List<&2, Laws.JBlkTok>,
  blk: Jpeg.Blk,
  ctrl: Jpeg.Ctrl,
  +preds: Jpeg.Preds,
  +ww: U32,
  +hh: U32,
  yy: Array<U32>,
  cb: Array<U32>,
  cr: Array<U32>,
  +tl: List<&2, Bool>,
  res: BlkRes(blk, List.append(&2, Bool, M2.tbits(ts), tl)),
  +hw: {Laws.jpg.allwf(ts) == True{} : Bool}
) -> {Laws.jpg.psome(Jpeg.decode.blocks(List.length(&2, Laws.JBlkTok, ts), blk, ctrl, preds, Laws.jpg.enc.frame(ww,
  hh), Laws.jpg.enc.scan(), tabsg(), 0, yy, cb, cr, 1)) == True{} : Bool}:
  match ts:
    case Nil{}:
      match blk:
        case Jpeg.Blk{+ss, +bb, +pd, +oo}:
          (+se, e1, _e2, _e3) = res
          eo = Equal.sym(U32, oo, 1, Equal.cong(Jpeg.Bits & U32, U32, xx => bo.ok(xx), (bb, oo), (rbits(se, 1), 1),
            e1))
          %eo : {Laws.jpg.psome(Jpeg.decode.blocks(0n, Jpeg.Blk{ss, bb, pd, _}, ctrl, preds, Laws.jpg.enc.frame(ww, hh),
            Laws.jpg.enc.scan(), tabsg(), 0, yy, cb, cr, 1)) == True{} : Bool}
          {==}
    case +tt <> +rest:
      match blk:
        case Jpeg.Blk{+ss, +bb, +pd, +oo}:
          match ctrl:
            case Jpeg.Ctrl{+cc, +bi, +mx, +my, +mcu, +rst}:
              (+se, e1x, e2, e3x) = res
              +e1 = {e1x : {(bb, oo) == (rbits(se, 1), 1) : Jpeg.Bits & U32}}
              +e3 = {e3x : {Bool.and(rshort(se), roct8(se)) == True{} : Bool}}
              +ct = {Jpeg.Ctrl{cc, bi, mx, my, mcu, rst} : Jpeg.Ctrl}
              +fr = Laws.jpg.enc.frame(ww, hh)
              +sc = Laws.jpg.enc.scan()
              eo = Equal.sym(U32, oo, 1, Equal.cong(Jpeg.Bits & U32, U32, xx => bo.ok(xx), (bb, oo), (rbits(se, 1),
                1), e1))
              eb = Equal.sym(Jpeg.Bits, bb, rbits(se, 1), Equal.cong(Jpeg.Bits & U32, Jpeg.Bits, xx => bo.bits(xx),
                (bb, oo), (rbits(se, 1), 1), e1))
              +hs = {M3.and_l(rshort(se), roct8(se), e3) : {rshort(se) == True{} : Bool}}
              +h8 = {M3.and_r(rshort(se), roct8(se), e3) : {roct8(se) == True{} : Bool}}
              +mr = List.append(&2, Bool, M2.tbits(rest), tl)
              +he = {Equal.trans(List<&2, Bool>, rem(se), List.append(&2, Bool, List.append(&2, Bool,
                M3.blkbits(tt), M2.tbits(rest)), tl), List.append(&2, Bool, M3.blkbits(tt), mr), e2,
                M3.huf.app_assoc(M3.blkbits(tt), M2.tbits(rest), tl)) : {rem(se) == List.append(&2, Bool,
                    M3.blkbits(tt),
                mr) : List<&2, Bool>}}
              +pn = Jpeg.decode.pred.get(Jpeg.decode.preds.next(0, preds, cc, pd), Jpeg.decode.ctrl.comp(
                Jpeg.decode.adv.ctrl(Jpeg.decode.adv(ct, fr, sc, 0))))
              +nb = Jpeg.decode.block.next(rbits(se, 1), preds, pd, ct, fr, sc, tabsg(), 0)
              +gb = Jpeg.decode.block.go(rbits(se, 1), pn, dctb(), actb(), ones64())
              +en = {bnext(rbits(se, 1), preds, pd, ct, ww, hh) : {nb == gb : Jpeg.Blk}}
              %eo : {Laws.jpg.psome(Jpeg.decode.blocks(1n+List.length(&2, Laws.JBlkTok, rest), Jpeg.Blk{ss, bb, pd,
                _}, ct, preds, fr,
                sc, tabsg(), 0, yy, cb, cr, 1)) == True{} : Bool}
              %eb : {Laws.jpg.psome(Jpeg.decode.blocks(1n+List.length(&2, Laws.JBlkTok, rest), Jpeg.Blk{ss, _, pd, 1},
                ct, preds, fr,
                sc, tabsg(), 0, yy, cb, cr, 1)) == True{} : Bool}
              huf.fl(rest, nb, Jpeg.decode.adv.ctrl(Jpeg.decode.adv(ct, fr, sc, 0)), Jpeg.decode.preds.next(
                Jpeg.decode.adv.duef(Jpeg.decode.adv(ct, fr, sc, 0)), preds, cc, pd), ww, hh,
                Jpeg.decode.paint.use(Jpeg.decode.geom(ct, fr, sc), U32.is_eq(cc, 0), ss, yy),
                Jpeg.decode.paint.use(Jpeg.decode.geom(ct, fr, sc), U32.is_eq(cc, 1), ss, cb),
                Jpeg.decode.paint.use(Jpeg.decode.geom(ct, fr, sc), U32.is_eq(cc, 2), ss, cr), tl,
                blkres.tr(gb, nb, mr, Equal.sym(Jpeg.Blk, nb, gb, en), bsim(tt, pn, se, mr, hs, h8, he,
                M1.also_l(Laws.jpg.blkwf(tt), Laws.jpg.allwf(rest), hw))), M1.also_r(Laws.jpg.blkwf(tt),
                  Laws.jpg.allwf(rest), hw))

# the frame's block count is the number of blocks
def NBlk(+ww: U32, +hh: U32, -rest: List<&2, Laws.JBlkTok>) -> Type:
  {U32.to_nat(Jpeg.decode.nblocks(ww, hh, [1, 1, 1], [1, 1, 1], 1, 1)) == 1n+List.length(&2, Laws.JBlkTok, rest) : Nat}

# the decoder's scan decode, in the encoder's frame, of bytes holding blocks that each read whole, as many as the
# frame's block count, returns a picture
def dec(
  +tt: Laws.JBlkTok,
  +rest: List<&2, Laws.JBlkTok>,
  +tl: List<&2, Bool>,
  +ww: U32,
  +hh: U32,
  +os: List<&2, List<&2, Bool>>,
  hw0: {U32.is_eq(ww, 0) == False{} : Bool},
  hh0: {U32.is_eq(hh, 0) == False{} : Bool},
  +h8: {oct8(os) == True{} : Bool},
  +he: {rem(RS{[], os}) == List.append(&2, Bool, M2.tbits(tt <> rest), tl) : List<&2, Bool>},
  +hw: {Laws.jpg.allwf(tt <> rest) == True{} : Bool},
  hn: NBlk(ww, hh, rest)
) -> {Laws.jpg.psome(Jpeg.decode.run(Laws.jpg.enc.frame(ww, hh), Laws.jpg.enc.scan(), tabsg(), rxs(os),
  0)) == True{} : Bool}:
  +fr = Laws.jpg.enc.frame(ww, hh)
  +sc = Laws.jpg.enc.scan()
  +s0 = {RS{[], os} : RS}
  +mr = List.append(&2, Bool, M2.tbits(rest), tl)
  +he1 = {Equal.trans(List<&2, Bool>, rem(s0), List.append(&2, Bool, List.append(&2, Bool, M3.blkbits(tt),
    M2.tbits(rest)), tl), List.append(&2, Bool, M3.blkbits(tt), mr), he, M3.huf.app_assoc(M3.blkbits(tt),
        M2.tbits(rest), tl)) :
    {rem(s0) == List.append(&2, Bool, M3.blkbits(tt), mr) : List<&2, Bool>}}
  +bo = Jpeg.decode.block.of(rbits(s0, 1), 0, Jpeg.decode.pred.zero(), fr, sc, tabsg())
  +bg = Jpeg.decode.block.go(rbits(s0, 1), Jpeg.decode.pred.get(Jpeg.decode.pred.zero(), 0), dctb(), actb(),
    ones64())
  s1 = Equal.sym(Bool, U32.is_eq(ww, 0), False{}, hw0)
  s2 = Equal.sym(Bool, U32.is_eq(hh, 0), False{}, hh0)
  s3 = Equal.sym(Nat, U32.to_nat(Jpeg.decode.nblocks(ww, hh, [1, 1, 1], [1, 1, 1], 1, 1)), 1n+List.length(&2,
    Laws.JBlkTok,
    rest), hn)
  %s1 : {Laws.jpg.psome(Jpeg.decode.run.n(Bool.or(_, U32.is_eq(hh, 0)), ww, hh, fr, sc, tabsg(), rxs(os),
    0)) == True{} :
    Bool}
  %s2 : {Laws.jpg.psome(Jpeg.decode.run.n(Bool.or(False{}, _), ww, hh, fr, sc, tabsg(), rxs(os), 0)) == True{} : Bool}
  %s3 : {Laws.jpg.psome(Jpeg.decode.start(_, Jpeg.Bits{0, 1, 0, rxs(os)}, fr, sc, tabsg(), 0,
    Jpeg.decode.plane((ww * hh : U32)), Jpeg.decode.plane((ww * hh : U32)), Jpeg.decode.plane((ww * hh : U32)))) ==
    True{} : Bool}
  huf.fl(rest, bo, Jpeg.Ctrl{0, 0, 0, 0, 0, 0}, Jpeg.decode.pred.zero(), ww, hh, Jpeg.decode.plane((ww * hh : U32)),
    Jpeg.decode.plane((ww * hh : U32)), Jpeg.decode.plane((ww * hh : U32)), tl, blkres.tr(bg, bo, mr,
    Equal.sym(Jpeg.Blk, bo, bg, bof(rbits(s0, 1), 0, Jpeg.decode.pred.zero(), ww, hh)), bsim(tt,
    Jpeg.decode.pred.get(Jpeg.decode.pred.zero(), 0), s0, mr, {==}, h8, he1, M1.also_l(Laws.jpg.blkwf(tt),
      Laws.jpg.allwf(rest),
    hw))), M1.also_r(Laws.jpg.blkwf(tt), Laws.jpg.allwf(rest), hw))

# the code the encoder's AC book holds for a symbol is the literal book's
def acode.eq(+sy: U32) -> {Laws.jpg.acode(sy) == M3.code.ac(sy) : List<&2, Bool>}:
  Equal.cong(Array<U32>, List<&2, Bool>, bk => Laws.jpg.cbw(D2.jpg.val(Array.get(U32, bk, sy))),
    Jenc.encode.huff(Jenc.encode.accounts(), Jenc.encode.acsyms()), M3.acbook.lit(), M2.acbook.eq())

# the code the encoder's DC book holds for a symbol is the literal book's
def dcode.eq(+sy: U32) -> {Laws.jpg.dcode(sy) == M3.code.dc(sy) : List<&2, Bool>}:
  Equal.cong(Array<U32>, List<&2, Bool>, bk => Laws.jpg.cbw(D2.jpg.val(Array.get(U32, bk, sy))),
    Jenc.encode.huff(Jenc.encode.dccounts(), Jenc.encode.dcsyms()), M3.dcbook.lit(), M2.dcbook.eq())

# AC tokens' bits over the encoder's book are their bits over the literal book
def acbits.eq(ts: List<&2, Laws.JTok>) -> {Laws.jpg.acbits(ts) == M3.acbits(ts) : List<&2, Bool>}:
  match ts:
    case Nil{}:
      {==}
    case Laws.JTok{+sym, +ex} <> +rest:
      Equal.trans(List<&2, Bool>, List.append(&2, Bool, Laws.jpg.acode(sym), List.append(&2, Bool, ex,
        Laws.jpg.acbits(rest))), List.append(&2, Bool, M3.code.ac(sym), List.append(&2, Bool, ex,
        Laws.jpg.acbits(rest))), List.append(&2, Bool, M3.code.ac(sym), List.append(&2, Bool, ex, M3.acbits(rest))),
        Equal.cong(List<&2, Bool>, List<&2, Bool>, xs => List.append(&2, Bool, xs, List.append(&2, Bool, ex,
        Laws.jpg.acbits(rest))), Laws.jpg.acode(sym), M3.code.ac(sym), acode.eq(sym)), Equal.cong(List<&2, Bool>,
        List<&2, Bool>, ys => List.append(&2, Bool, M3.code.ac(sym), List.append(&2, Bool, ex, ys)),
        Laws.jpg.acbits(rest), M3.acbits(rest), acbits.eq(rest)))

# a block's bits over the encoder's books are its bits over the literal books
def blkbits.eq(bt: Laws.JBlkTok) -> {Laws.jpg.blkbits(bt) == M3.blkbits(bt) : List<&2, Bool>}:
  match bt:
    case Laws.JBlkTok{+dcs, +dcx, +acs}:
      Equal.trans(List<&2, Bool>, List.append(&2, Bool, Laws.jpg.dcode(dcs), List.append(&2, Bool, dcx,
        Laws.jpg.acbits(acs))), List.append(&2, Bool, M3.code.dc(dcs), List.append(&2, Bool, dcx,
            Laws.jpg.acbits(acs))),
        List.append(&2, Bool, M3.code.dc(dcs), List.append(&2, Bool, dcx, M3.acbits(acs))), Equal.cong(List<&2, Bool>,
        List<&2, Bool>, xs => List.append(&2, Bool, xs, List.append(&2, Bool, dcx, Laws.jpg.acbits(acs))),
        Laws.jpg.dcode(dcs), M3.code.dc(dcs), dcode.eq(dcs)), Equal.cong(List<&2, Bool>, List<&2, Bool>,
        ys => List.append(&2, Bool, M3.code.dc(dcs), List.append(&2, Bool, dcx, ys)), Laws.jpg.acbits(acs),
            M3.acbits(acs),
        acbits.eq(acs)))

# blocks' bits over the encoder's books are their bits over the literal books
def tbits.eq(ts: List<&2, Laws.JBlkTok>) -> {Laws.jpg.tbits(ts) == M2.tbits(ts) : List<&2, Bool>}:
  match ts:
    case Nil{}:
      {==}
    case +tt <> +rest:
      Equal.trans(List<&2, Bool>, List.append(&2, Bool, Laws.jpg.blkbits(tt), Laws.jpg.tbits(rest)), List.append(&2,
        Bool, M3.blkbits(tt), Laws.jpg.tbits(rest)), List.append(&2, Bool, M3.blkbits(tt), M2.tbits(rest)),
            Equal.cong(List<&2,
        Bool>, List<&2, Bool>, xs => List.append(&2, Bool, xs, Laws.jpg.tbits(rest)), Laws.jpg.blkbits(tt),
        M3.blkbits(tt), blkbits.eq(tt)), Equal.cong(List<&2, Bool>, List<&2, Bool>, ys => List.append(&2, Bool,
        M3.blkbits(tt), ys), Laws.jpg.tbits(rest), M2.tbits(rest), tbits.eq(rest)))

# the scan side of the round trip: blocks the decoder reads whole, as many as the frame has, written by the
# encoder's bit writer, decode to a picture
def scan_some(
  +tt: Laws.JBlkTok,
  +rest: List<&2, Laws.JBlkTok>,
  +ww: U32,
  +hh: U32,
  hw0: {U32.is_eq(ww, 0) == False{} : Bool},
  hh0: {U32.is_eq(hh, 0) == False{} : Bool},
  hw: {Laws.jpg.allwf(tt <> rest) == True{} : Bool},
  hn: NBlk(ww, hh, rest)
) -> {Laws.jpg.psome(Jpeg.decode.run(Laws.jpg.enc.frame(ww, hh), Laws.jpg.enc.scan(), Laws.jpg.enc.tabs(),
  Jenc.encode.pad(Laws.jpg.feed(Laws.jpg.tbits(tt <> rest), Jenc.encode.put0())), 0)) == True{} : Bool}:
  +bs = M2.tbits(tt <> rest)
  +os = moct(bs, [])
  +fr = Laws.jpg.enc.frame(ww, hh)
  +sc = Laws.jpg.enc.scan()
  eb = Equal.sym(List<&2, Bool>, Laws.jpg.tbits(tt <> rest), bs, tbits.eq(tt <> rest))
  et = Equal.sym(Jpeg.Tabs, Laws.jpg.enc.tabs(), tabsg(), tabs.eq())
  ep = Equal.sym(List<&2, U32>, Jenc.encode.pad(Laws.jpg.feed(bs, Jenc.encode.put0())), rxs(os), Equal.trans(List<&2,
    U32>, Jenc.encode.pad(Laws.jpg.feed(bs, M2.wput(M2.WS{[], []}))), Jenc.encode.pad(M2.wput(M2.wm(bs, M2.WS{[],
        []}))), rxs(os),
    Equal.cong(Jenc.Put, List<&2, U32>, qq => Jenc.encode.pad(qq), Laws.jpg.feed(bs, M2.wput(M2.WS{[], []})),
        M2.wput(M2.wm(bs,
    M2.WS{[], []})), M2.wfeed(bs, M2.WS{[], []}, {==})), pad_m(bs, [], [], {==})))
  %eb : {Laws.jpg.psome(Jpeg.decode.run(fr, sc, Laws.jpg.enc.tabs(), Jenc.encode.pad(Laws.jpg.feed(_,
    Jenc.encode.put0())), 0)) == True{} : Bool}
  %et : {Laws.jpg.psome(Jpeg.decode.run(fr, sc, _, Jenc.encode.pad(Laws.jpg.feed(bs, Jenc.encode.put0())),
    0)) == True{} : Bool}
  %ep : {Laws.jpg.psome(Jpeg.decode.run(fr, sc, tabsg(), _, 0)) == True{} : Bool}
  dec(tt, rest, mpad(bs, []), ww, hh, os, hw0, hh0, oct8_moct(bs, [], {==}), concat_moct(bs, []), hw, hn)

# whatever the watch finds, its colour and samples together
def arm_use2(
  +tag: U32,
  rest: U32 & List<&2, U32>,
  +ww: U32,
  +hh: U32,
  hn: {1n+U32.to_nat((M2.mcun(ww, hh) - 1 : U32)) == U32.to_nat(M2.mcun(ww, hh)) : Nat}
) -> M2.PathOut(Jenc.encode.arm.use((tag, rest), ww, hh), U32.to_nat(M2.mcun(ww, hh))):
  match rest:
    case (+color, +px):
      M2.disp(U32.is_eq(tag, 0), U32.is_eq(tag, 1), color, px, ww, hh, hn)

# whatever the watch finds
def arm_use(
  got: U32 & U32 & List<&2, U32>,
  +ww: U32,
  +hh: U32,
  hn: {1n+U32.to_nat((M2.mcun(ww, hh) - 1 : U32)) == U32.to_nat(M2.mcun(ww, hh)) : Nat}
) -> M2.PathOut(Jenc.encode.arm.use(got, ww, hh), U32.to_nat(M2.mcun(ww, hh))):
  match got:
    case (+tag, rest):
      arm_use2(tag, rest, ww, hh, hn)

# the encoder's entropy-coded bytes are blocks the decoder reads whole, three per MCU, fed to the writer and padded
def arm_ok(
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  hn: {1n+U32.to_nat((M2.mcun(ww, hh) - 1 : U32)) == U32.to_nat(M2.mcun(ww, hh)) : Nat}
) -> M2.PathOut(Jenc.encode.arm(ww, hh, px), U32.to_nat(M2.mcun(ww, hh))):
  arm_use(Jenc.encode.watch(U32.to_nat((ww * hh : U32)), px), ww, hh, hn)

# the first of a pair
def fst.bw(+pp: Nat, pr: Bool & Word(pp)) -> Bool:
  match pr:
    case (bb, _w):
      bb

# the second of a pair
def snd.bw(+pp: Nat, pr: Bool & Word(pp)) -> Word(pp):
  match pr:
    case (_b, ww):
      ww

# the shift-out step puts c below the rest's shifted word and hands on its top bit
def con_eta(
  +pp: Nat,
  +cc: Bool,
  pr: Bool & Word(pp)
) -> {Word.shl.out.con(pp, cc, pr) == (fst.bw(pp, pr), WCon{cc, snd.bw(pp, pr)}) : Bool & Word(1n+pp)}:
  match pr:
    case (_b, _w):
      {==}

# the bit a shift out drops is the top bit
def shl_top(
  nn: Nat,
  +cc: Bool,
  ww: Word(1n+nn)
) -> {fst.bw(1n+nn, Word.shl.out(1n+nn, cc, ww)) == M3.wtop(nn, ww) : Bool}:
  match nn:
    case 0n:
      match ww:
        case WCon{_b, _t}:
          {==}
    case 1n+ +pp:
      match ww:
        case WCon{+bb, +tt}:
          Equal.trans(Bool, fst.bw(2n+pp, Word.shl.out.con(1n+pp, cc, Word.shl.out(1n+pp, bb, tt))), fst.bw(1n+pp,
            Word.shl.out(1n+pp, bb, tt)), M3.wtop(pp, tt), Equal.cong(Bool & Word(2n+pp), Bool, xx => fst.bw(2n+pp, xx),
            Word.shl.out.con(1n+pp, cc, Word.shl.out(1n+pp, bb, tt)), (fst.bw(1n+pp, Word.shl.out(1n+pp, bb, tt)),
            WCon{cc, snd.bw(1n+pp, Word.shl.out(1n+pp, bb, tt))}), con_eta(1n+pp, cc, Word.shl.out(1n+pp, bb, tt))),
            shl_top(pp, bb, tt))

# the word a shift out leaves, when the top bit is clear, is c plus twice the word
def jenc.shl_nat(
  nn: Nat,
  +cc: Bool,
  ww: Word(1n+nn),
  hh: {M3.wtop(nn, ww) == False{} : Bool}
) -> {Word.to_nat(1n+nn, snd.bw(1n+nn, Word.shl.out(1n+nn, cc, ww))) == Nat.add(M1.bit(cc),
  Nat.double(Word.to_nat(1n+nn, ww))) : Nat}:
  match nn:
    case 0n:
      match ww:
        case WCon{False{}, WNil{}}:
          M1.to_nat_con(0n, cc, WNil{})
        case WCon{True{}, WNil{}}:
          Empty.absurd({Word.to_nat(1n, snd.bw(1n, Word.shl.out(1n, cc, WCon{True{}, WNil{}}))) == Nat.add(M1.bit(cc),
            Nat.double(Word.to_nat(1n, WCon{True{}, WNil{}}))) : Nat}, M3.jenc.true_false(hh))
    case 1n+ +pp:
      match ww:
        case WCon{+bb, +tt}:
          +sx = snd.bw(1n+pp, Word.shl.out(1n+pp, bb, tt))
          +tn = Word.to_nat(1n+pp, tt)
          Equal.trans(Nat, Word.to_nat(2n+pp, snd.bw(2n+pp, Word.shl.out.con(1n+pp, cc, Word.shl.out(1n+pp, bb, tt)))),
            Word.to_nat(2n+pp, WCon{cc, sx}), Nat.add(M1.bit(cc), Nat.double(Word.to_nat(2n+pp, WCon{bb, tt}))),
            Equal.cong(Bool & Word(2n+pp), Nat, xx => Word.to_nat(2n+pp, snd.bw(2n+pp, xx)), Word.shl.out.con(1n+pp, cc,
            Word.shl.out(1n+pp, bb, tt)), (fst.bw(1n+pp, Word.shl.out(1n+pp, bb, tt)), WCon{cc, sx}), con_eta(1n+pp, cc,
            Word.shl.out(1n+pp, bb, tt))), Equal.trans(Nat, Word.to_nat(2n+pp, WCon{cc, sx}), Nat.add(M1.bit(cc),
            Nat.double(Word.to_nat(1n+pp, sx))), Nat.add(M1.bit(cc), Nat.double(Word.to_nat(2n+pp, WCon{bb, tt}))),
            M1.to_nat_con(1n+pp, cc, sx), Equal.cong(Nat, Nat, xx => Nat.add(M1.bit(cc), Nat.double(xx)),
              Word.to_nat(1n+pp,
            sx), Word.to_nat(2n+pp, WCon{bb, tt}), Equal.trans(Nat, Word.to_nat(1n+pp, sx), Nat.add(M1.bit(bb),
            Nat.double(tn)), Word.to_nat(2n+pp, WCon{bb, tt}), jenc.shl_nat(pp, bb, tt, hh), Equal.sym(Nat,
            Word.to_nat(2n+pp, WCon{bb, tt}), Nat.add(M1.bit(bb), Nat.double(tn)), M1.to_nat_con(1n+pp, bb, tt))))))

# the quotient of a long division
def jenc.dq(+pp: Nat, pr: Word(pp) & U32) -> Word(pp):
  match pr:
    case (qq, _r):
      qq

# the remainder of a long division
def jenc.dr(+pp: Nat, pr: Word(pp) & U32) -> U32:
  match pr:
    case (_q, rr):
      rr

# a long division by 8 of a word of m bits: the word is the remainder and eight times the quotient, the remainder
# below 8
def DivInv(+mm: Nat, -aa: Word(mm)) -> Type:
  &_e: {Word.to_nat(mm, aa) == Nat.add(U32.to_nat(jenc.dr(mm, U32.divmod.go(mm, aa, 8))), M1.eight(Word.to_nat(mm,
      jenc.dq(mm,
    U32.divmod.go(mm, aa, 8))))) : Nat} -> {U32.is_lt(jenc.dr(mm, U32.divmod.go(mm, aa, 8)), 8) == True{} : Bool}

# a pair of a bit and a word is its parts
def bw_eta(+pp: Nat, pr: Bool & Word(pp)) -> {pr == (fst.bw(pp, pr), snd.bw(pp, pr)) : Bool & Word(pp)}:
  match pr:
    case (_b, _w):
      {==}

# a compare not at least is below
def nge_lt(tt: Cmp, hh: {Cmp.is_ge(tt) == False{} : Bool}) -> {Cmp.is_lt(tt) == True{} : Bool}:
  match tt:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({Cmp.is_lt(EQ{}) == True{} : Bool}, M3.jenc.true_false(hh))
    case GT{}:
      Empty.absurd({Cmp.is_lt(GT{}) == True{} : Bool}, M3.jenc.true_false(hh))

# twice a number below n is below twice n
def lt_dbl0(
  rr: Nat,
  nn: Nat,
  hh: {Nat.is_lt(rr, nn) == True{} : Bool}
) -> {Nat.is_lt(Nat.double(rr), Nat.double(nn)) == True{} : Bool}:
  match rr nn:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, M1.huf.false_true(hh))
    case 0n 1n+_m:
      {==}
    case 1n+_r 0n:
      Empty.absurd({Nat.is_lt(Nat.double(1n+_r), 0n) == True{} : Bool}, M1.huf.false_true(hh))
    case 1n+rp 1n+mp:
      lt_dbl0(rp, mp, hh)

# one and twice a number below n is below twice n
def lt_dbl1(
  rr: Nat,
  nn: Nat,
  hh: {Nat.is_lt(rr, nn) == True{} : Bool}
) -> {Nat.is_lt(1n+Nat.double(rr), Nat.double(nn)) == True{} : Bool}:
  match rr nn:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(1n, 0n) == True{} : Bool}, M1.huf.false_true(hh))
    case 0n 1n+_m:
      {==}
    case 1n+_r 0n:
      Empty.absurd({Nat.is_lt(1n+Nat.double(1n+_r), 0n) == True{} : Bool}, M1.huf.false_true(hh))
    case 1n+rp 1n+mp:
      lt_dbl1(rp, mp, hh)

# a bit and twice a number below n are below twice n
def jenc.lt_dbl(
  bb: Bool,
  rr: Nat,
  nn: Nat,
  hh: {Nat.is_lt(rr, nn) == True{} : Bool}
) -> {Nat.is_lt(Nat.add(M1.bit(bb), Nat.double(rr)), Nat.double(nn)) == True{} : Bool}:
  match bb:
    case False{}:
      lt_dbl0(rr, nn, hh)
    case True{}:
      lt_dbl1(rr, nn, hh)

# the type of divg's parameter eh
def divg.eh.ty(+_pp: Nat, +_a0: Bool, +_hi: Word(_pp), +_qq: Word(_pp), +_rn: Nat) -> Type:
  {Word.to_nat(1n+_pp, WCon{_a0, _hi}) == Nat.add(Nat.add(M1.bit(_a0), Nat.double(_rn)),
    Nat.double(M1.eight(Word.to_nat(_pp, _qq)))) : Nat}

# the long division's shifted remainder, the new quotient bit decided by g
def divg(
  gg: Bool,
  +pp: Nat,
  +a0: Bool,
  -hi: Word(pp),
  +qq: Word(pp),
  +ss: Word(32n),
  +rn: Nat,
  +hg: {U32.is_ge(U32{ss}, 8) == gg : Bool},
  +es: {Word.to_nat(32n, ss) == Nat.add(M1.bit(a0), Nat.double(rn)) : Nat},
  eh0: divg.eh.ty(pp, a0, hi, qq, rn),
  +hr: {Nat.is_lt(rn, 8n) == True{} : Bool}
) -> &_e: {Word.to_nat(1n+pp, WCon{a0, hi}) == Nat.add(U32.to_nat(jenc.dr(1n+pp, U32.divmod.go.fin(pp, qq, U32{ss}, 8,
  gg))), M1.eight(Word.to_nat(1n+pp, jenc.dq(1n+pp, U32.divmod.go.fin(pp, qq, U32{ss}, 8,
  gg))))) : Nat} -> {U32.is_lt(jenc.dr(1n+pp, U32.divmod.go.fin(pp, qq, U32{ss}, 8, gg)), 8) == True{} : Bool}:
  match gg:
    case False{}:
      +eh = {eh0 : {Word.to_nat(1n+pp, WCon{a0, hi}) == Nat.add(Nat.add(M1.bit(a0), Nat.double(rn)),
        Nat.double(M1.eight(Word.to_nat(pp, qq)))) : Nat}}
      +sn = Word.to_nat(32n, ss)
      (Equal.trans(Nat, Word.to_nat(1n+pp, WCon{a0, hi}), Nat.add(Nat.add(M1.bit(a0), Nat.double(rn)),
          Nat.double(M1.eight(
        Word.to_nat(pp, qq)))), Nat.add(sn, Nat.double(M1.eight(Word.to_nat(pp, qq)))), eh, Equal.cong(Nat, Nat, xx =>
        Nat.add(xx, Nat.double(M1.eight(Word.to_nat(pp, qq)))), Nat.add(M1.bit(a0), Nat.double(rn)), sn, Equal.sym(Nat,
            sn,
        Nat.add(M1.bit(a0), Nat.double(rn)), es))), nge_lt(U32.cmp(U32{ss}, 8), hg))
    case True{}:
      +eh = {eh0 : {Word.to_nat(1n+pp, WCon{a0, hi}) == Nat.add(Nat.add(M1.bit(a0), Nat.double(rn)),
        Nat.double(M1.eight(Word.to_nat(pp, qq)))) : Nat}}
      +sn = Word.to_nat(32n, ss)
      +dd = Nat.double(M1.eight(Word.to_nat(pp, qq)))
      +h8 = {Equal.trans(Bool, Nat.is_le(8n, sn), Cmp.is_ge(Nat.cmp(sn, 8n)), True{}, Equal.sym(Bool,
        Cmp.is_ge(Nat.cmp(sn,
        8n)), Nat.is_le(8n, sn), M3.ge_le(sn, 8n)), Equal.trans(Bool, Cmp.is_ge(Nat.cmp(sn, 8n)), U32.is_ge(U32{ss}, 8),
        True{}, Equal.cong(Cmp, Bool, cc => Cmp.is_ge(cc), Nat.cmp(sn, 8n), U32.cmp(U32{ss}, 8), Equal.sym(Cmp,
        U32.cmp(U32{ss}, 8), Nat.cmp(sn, 8n), M3.jenc.u_cmp(U32{ss}, 8))), hg)) : {Nat.is_le(8n, sn) == True{} : Bool}}
      +er = {M6.ras.u32_sub_nat(U32{ss}, 8, h8) : {U32.to_nat((U32{ss} - 8 : U32)) == Nat.sub(sn, 8n) : Nat}}
      +h16 = {Equal.trans(Bool, Nat.is_lt(sn, 16n), Nat.is_lt(Nat.add(M1.bit(a0), Nat.double(rn)), 16n), True{},
        Equal.cong(Nat, Bool, xx => Nat.is_lt(xx, 16n), sn, Nat.add(M1.bit(a0), Nat.double(rn)), es), jenc.lt_dbl(a0,
            rn, 8n,
        hr)) : {Nat.is_lt(sn, 16n) == True{} : Bool}}
      (Equal.trans(Nat, Word.to_nat(1n+pp, WCon{a0, hi}), Nat.add(sn, dd), Nat.add(U32.to_nat((U32{ss} - 8 : U32)),
        8n+dd), Equal.trans(Nat, Word.to_nat(1n+pp, WCon{a0, hi}), Nat.add(Nat.add(M1.bit(a0), Nat.double(rn)), dd),
        Nat.add(sn, dd), eh, Equal.cong(Nat, Nat, xx => Nat.add(xx, dd), Nat.add(M1.bit(a0), Nat.double(rn)), sn,
        Equal.sym(Nat, sn, Nat.add(M1.bit(a0), Nat.double(rn)), es))), Equal.sym(Nat, Nat.add(U32.to_nat((U32{ss} - 8 :
        U32)), 8n+dd), Nat.add(sn, dd), Equal.trans(Nat, Nat.add(U32.to_nat((U32{ss} - 8 : U32)), 8n+dd), Nat.add(
        Nat.sub(sn, 8n), 8n+dd), Nat.add(sn, dd), Equal.cong(Nat, Nat, xx => Nat.add(xx, 8n+dd), U32.to_nat((U32{ss} - 8
        : U32)), Nat.sub(sn, 8n), er), Equal.trans(Nat, Nat.add(Nat.sub(sn, 8n), Nat.add(8n, dd)), Nat.add(8n, Nat.add(
        Nat.sub(sn, 8n), dd)), Nat.add(sn, dd), M1.add_swap(Nat.sub(sn, 8n), 8n, dd), Equal.trans(Nat, Nat.add(8n,
        Nat.add(Nat.sub(sn, 8n), dd)), Nat.add(Nat.add(8n, Nat.sub(sn, 8n)), dd), Nat.add(sn, dd), Equal.sym(Nat,
        Nat.add(Nat.add(8n, Nat.sub(sn, 8n)), dd), Nat.add(8n, Nat.add(Nat.sub(sn, 8n), dd)), M1.ras.add_assoc(8n,
        Nat.sub(sn, 8n), dd)), Equal.cong(Nat, Nat, xx => Nat.add(xx, dd), Nat.add(8n, Nat.sub(sn, 8n)), sn,
          M6.add_sub(8n,
        sn, h8))))))), M3.n_ult((U32{ss} - 8 : U32), 8, Equal.trans(Bool, Nat.is_lt(U32.to_nat((U32{ss} - 8 : U32)),
            8n),
        Nat.is_lt(Nat.sub(sn, 8n), 8n), True{}, Equal.cong(Nat, Bool, xx => Nat.is_lt(xx, 8n), U32.to_nat((U32{ss} - 8 :
        U32)), Nat.sub(sn, 8n), er), M6.sub_lt(8n, sn, 8n, h8, h16))))

# the division by 8 invariant for a long division's result x of a word of p + 1 bits
def DivR(+pp: Nat, -aa: Word(1n+pp), xx: Word(1n+pp) & U32) -> Type:
  &_e: {Word.to_nat(1n+pp, aa) == Nat.add(U32.to_nat(jenc.dr(1n+pp, xx)), M1.eight(Word.to_nat(1n+pp, jenc.dq(1n+pp,
      xx)))) : Nat} ->
    {U32.is_lt(jenc.dr(1n+pp, xx), 8) == True{} : Bool}

# the invariant moved along an equality of results
def divr_tr(
  +pp: Nat,
  -aa: Word(1n+pp),
  xx: Word(1n+pp) & U32,
  yy: Word(1n+pp) & U32,
  ee: {xx == yy : Word(1n+pp) & U32},
  hh: DivR(pp, aa, yy)
) -> DivR(pp, aa, xx):
  es = Equal.sym(Word(1n+pp) & U32, xx, yy, ee)
  %es : DivR(pp, aa, _)
  hh

# one step of the long division by 8, the remainder a word
def divstep.r(
  +pp: Nat,
  +a0: Bool,
  -hi: Word(pp),
  +qq: Word(pp),
  +rw: Word(32n),
  ee: {Word.to_nat(pp, hi) == Nat.add(Word.to_nat(32n, rw), M1.eight(Word.to_nat(pp, qq))) : Nat},
  +hl: {U32.is_lt(U32{rw}, 8) == True{} : Bool}
) -> DivR(pp, WCon{a0, hi}, U32.divmod.go.rec(pp, a0, 8, (qq, U32{rw}))):
  +ss = snd.bw(32n, Word.shl.out(32n, a0, rw))
  +rn = Word.to_nat(32n, rw)
  +qn = Word.to_nat(pp, qq)
  +ht = {M3.ngt_top(31n, rw, M3.uw(8), {==}, M3.lt_ngt(Word.cmp(32n, rw, M3.uw(8)), hl)) : {M3.wtop(31n,
      rw) == False{} :
    Bool}}
  +hf = {Equal.trans(Bool, fst.bw(32n, Word.shl.out(32n, a0, rw)), M3.wtop(31n, rw), False{}, shl_top(31n, a0, rw),
    ht) : {fst.bw(32n, Word.shl.out(32n, a0, rw)) ==
    False{} : Bool}}
  +es = {jenc.shl_nat(31n, a0, rw, ht) : {Word.to_nat(32n, ss) == Nat.add(M1.bit(a0), Nat.double(rn)) : Nat}}
  +eh = {Equal.trans(Nat, Word.to_nat(1n+pp, WCon{a0, hi}), Nat.add(M1.bit(a0), Nat.double(Word.to_nat(pp, hi))),
    Nat.add(Nat.add(M1.bit(a0), Nat.double(rn)), Nat.double(M1.eight(qn))), M1.to_nat_con(pp, a0, hi), Equal.trans(Nat,
    Nat.add(M1.bit(a0), Nat.double(Word.to_nat(pp, hi))), Nat.add(M1.bit(a0), Nat.double(Nat.add(rn, M1.eight(qn)))),
    Nat.add(Nat.add(M1.bit(a0), Nat.double(rn)), Nat.double(M1.eight(qn))), Equal.cong(Nat, Nat,
        xx => Nat.add(M1.bit(a0),
    Nat.double(xx)), Word.to_nat(pp, hi), Nat.add(rn, M1.eight(qn)), ee), Equal.trans(Nat, Nat.add(M1.bit(a0),
    Nat.double(Nat.add(rn, M1.eight(qn)))), Nat.add(M1.bit(a0), Nat.add(Nat.double(rn), Nat.double(M1.eight(qn)))),
    Nat.add(Nat.add(M1.bit(a0), Nat.double(rn)), Nat.double(M1.eight(qn))), Equal.cong(Nat, Nat,
        xx => Nat.add(M1.bit(a0),
    xx), Nat.double(Nat.add(rn, M1.eight(qn))), Nat.add(Nat.double(rn), Nat.double(M1.eight(qn))), M1.double_dist(rn,
    M1.eight(qn))), Equal.sym(Nat, Nat.add(Nat.add(M1.bit(a0), Nat.double(rn)), Nat.double(M1.eight(qn))),
        Nat.add(M1.bit(a0),
    Nat.add(Nat.double(rn), Nat.double(M1.eight(qn)))), M1.ras.add_assoc(M1.bit(a0), Nat.double(rn),
        Nat.double(M1.eight(qn))))))) :
    {Word.to_nat(1n+pp, WCon{a0, hi}) == Nat.add(Nat.add(M1.bit(a0), Nat.double(rn)), Nat.double(M1.eight(qn))) : Nat}}
  +gg = U32.is_ge(U32{ss}, 8)
  divr_tr(pp, WCon{a0, hi}, U32.divmod.go.rec(pp, a0, 8, (qq, U32{rw})), U32.divmod.go.fin(pp, qq, U32{ss}, 8, gg),
    Equal.trans(Word(1n+pp) & U32, U32.divmod.go.shl(pp, qq, 8, Word.shl.out(32n, a0, rw)), U32.divmod.go.shl(pp, qq,
      8, (fst.bw(32n, Word.shl.out(32n, a0, rw)), ss)),
    U32.divmod.go.fin(pp, qq, U32{ss}, 8, gg), Equal.cong(Bool & Word(32n), Word(1n+pp) & U32, tt =>
    U32.divmod.go.shl(pp, qq, 8, tt), Word.shl.out(32n, a0, rw), (fst.bw(32n, Word.shl.out(32n, a0, rw)), ss),
      bw_eta(32n, Word.shl.out(32n, a0, rw))), Equal.cong(Bool, Word(1n+pp) & U32,
    bb => U32.divmod.go.fin(pp, qq, U32{ss}, 8, Bool.or(bb, gg)), fst.bw(32n, Word.shl.out(32n, a0, rw)), False{},
      hf)), divg(gg, pp, a0, hi,
    qq, ss, rn, {==}, es, eh, M3.ult_n(U32{rw}, 8, hl)))

# the type of divstep's parameter inv
def divstep.inv.ty(+_pp: Nat, +_hi: Word(_pp), _qr: Word(_pp) & U32) -> Type:
  &_e: {Word.to_nat(_pp, _hi) == Nat.add(U32.to_nat(jenc.dr(_pp, _qr)), M1.eight(Word.to_nat(_pp, jenc.dq(_pp,
    _qr)))) : Nat} -> {U32.is_lt(jenc.dr(_pp, _qr), 8) == True{} : Bool}

# one step of the long division by 8, whatever the division of the higher bits returned
def divstep(
  +pp: Nat,
  +a0: Bool,
  -hi: Word(pp),
  qr: Word(pp) & U32,
  inv: divstep.inv.ty(pp, hi, qr)
) -> DivR(pp, WCon{a0, hi}, U32.divmod.go.rec(pp, a0, 8, qr)):
  match qr:
    case (+qq, rr):
      match rr:
        case U32{+rw}:
          (e, hl) = inv
          divstep.r(pp, a0, hi, qq, rw, e, hl)

# the long division by 8: the word is the remainder and eight times the quotient, the remainder below 8
def divinv(mm: Nat, aa: Word(mm)) -> DivInv(mm, aa):
  match mm aa:
    case 0n WNil{}:
      ({==}, {==})
    case 1n+ +pp WCon{+a0, +hi}:
      divstep(pp, a0, hi, U32.divmod.go(pp, hi, 8), divinv(pp, hi))

# the division's last step keeps the quotient
def divfin_eta(qr: Word(32n) & U32) -> {U32.div.fin(qr) == U32{jenc.dq(32n, qr)} : U32}:
  match qr:
    case (_q, _r):
      {==}

# the division of a word by 8, its invariant named
def udiv8.fin(
  +xw: Word(32n),
  inv: DivInv(32n, xw)
) -> &rr: U32 -> &_e: {U32.to_nat(U32{xw}) == Nat.add(U32.to_nat(rr), M1.eight(U32.to_nat(U32.div(U32{xw},
  8)))) : Nat} -> {U32.is_lt(rr, 8) == True{} : Bool}:
  (e, hl) = inv
  (jenc.dr(32n, U32.divmod.go(32n, xw, 8)), Equal.trans(Nat, Word.to_nat(32n, xw), Nat.add(U32.to_nat(jenc.dr(32n,
    U32.divmod.go(32n, xw, 8))), M1.eight(Word.to_nat(32n, jenc.dq(32n,
    U32.divmod.go(32n, xw, 8))))), Nat.add(U32.to_nat(jenc.dr(32n, U32.divmod.go(32n, xw, 8))),
      M1.eight(U32.to_nat(U32.div(U32{xw}, 8)))), e, Equal.cong(U32, Nat, uu =>
    Nat.add(U32.to_nat(jenc.dr(32n, U32.divmod.go(32n, xw, 8))), M1.eight(U32.to_nat(uu))), U32{jenc.dq(32n,
        U32.divmod.go(32n, xw,
      8))}, U32.div(U32{xw}, 8), Equal.sym(U32,
    U32.div(U32{xw}, 8), U32{jenc.dq(32n, U32.divmod.go(32n, xw, 8))}, divfin_eta(U32.divmod.go(32n, xw, 8))))), hl)

# a U32 is a remainder below 8 and eight times its quotient by 8
def udiv8(
  xx: U32
) -> &rr: U32 -> &_e: {U32.to_nat(xx) == Nat.add(U32.to_nat(rr), M1.eight(U32.to_nat(U32.div(xx,
  8)))) : Nat} -> {U32.is_lt(rr, 8) == True{} : Bool}:
  match xx:
    case U32{+xw}:
      udiv8.fin(xw, divinv(32n, xw))

# the multiplier, when the product is below 2^n, is the product
def word_mul_pow(
  +nn: Nat,
  +aw: Word(nn),
  +bw: Word(nn),
  hh: {Nat.is_lt(Nat.mul(Word.to_nat(nn, aw), Word.to_nat(nn, bw)), Nat.pow(2n, nn)) == True{} : Bool}
) -> {Word.to_nat(nn, Word.mul(nn, aw, bw)) == Nat.mul(Word.to_nat(nn, aw), Word.to_nat(nn, bw)) : Nat}:
  +pr = Nat.mul(Word.to_nat(nn, aw), Word.to_nat(nn, bw))
  +top = Nat.pow(2n, nn)
  +zn = Word.to_nat(nn, Word.zero(nn))
  +ez = {M5.word_zero_nat(nn) : {Word.to_nat(nn, Word.zero(nn)) == 0n : Nat}}
  +h1 = {M1.lt_rw_l(pr, Nat.add(zn, pr), top, Equal.cong(Nat, Nat, xx => Nat.add(xx, pr), 0n, zn, Equal.sym(Nat, zn, 0n,
    ez)), hh) : {Nat.is_lt(Nat.add(zn, pr), top) == True{} : Bool}}
  Equal.trans(Nat, Word.to_nat(nn, Word.mul.go(nn, nn, aw, bw, Word.zero(nn))), Nat.add(zn, pr), pr, M5.mulgo_nat(nn,
      nn,
    aw, bw, Word.zero(nn), h1), Equal.cong(Nat, Nat, xx => Nat.add(xx, pr), zn, 0n, ez))

# two to a sum is the product of the two powers
def pow_add(+aa: Nat, +bb: Nat) -> {Nat.pow(2n, Nat.add(aa, bb)) == Nat.mul(Nat.pow(2n, aa), Nat.pow(2n, bb)) : Nat}:
  match aa:
    case 0n:
      Equal.sym(Nat, Nat.add(Nat.pow(2n, bb), 0n), Nat.pow(2n, bb), M1.ras.add_zero(Nat.pow(2n, bb)))
    case 1n+ +pp:
      +pa = Nat.pow(2n, pp)
      +pb = Nat.pow(2n, bb)
      Equal.trans(Nat, Nat.pow(2n, 1n+Nat.add(pp, bb)), Nat.double(Nat.pow(2n, Nat.add(pp, bb))), Nat.mul(Nat.pow(2n,
        1n+pp), pb), M1.pow2_succ(Nat.add(pp, bb)), Equal.trans(Nat, Nat.double(Nat.pow(2n, Nat.add(pp, bb))),
        Nat.double(Nat.mul(pa, pb)), Nat.mul(Nat.pow(2n, 1n+pp), pb), Equal.cong(Nat, Nat, xx => Nat.double(xx),
        Nat.pow(2n, Nat.add(pp, bb)), Nat.mul(pa, pb), pow_add(pp, bb)), Equal.trans(Nat, Nat.double(Nat.mul(pa, pb)),
        Nat.mul(Nat.double(pa), pb), Nat.mul(Nat.pow(2n, 1n+pp), pb), Equal.sym(Nat, Nat.mul(Nat.double(pa), pb),
        Nat.double(Nat.mul(pa, pb)), M5.mul_double(pa, pb)), Equal.cong(Nat, Nat, xx => Nat.mul(xx, pb), Nat.double(pa),
        Nat.pow(2n, 1n+pp), Equal.sym(Nat, Nat.pow(2n, 1n+pp), Nat.double(pa), M1.pow2_succ(pp))))))

# at most b is at most b + 1
def le_s(+aa: Nat, +bb: Nat, hh: {Nat.is_le(aa, bb) == True{} : Bool}) -> {Nat.is_le(aa, 1n+bb) == True{} : Bool}:
  M1.le_trans(aa, bb, 1n+bb, hh, M6.le_succ(bb))

# a number is at most its double
def le_dbl(nn: Nat) -> {Nat.is_le(nn, Nat.double(nn)) == True{} : Bool}:
  match nn:
    case 0n:
      {==}
    case 1n+ +pp:
      le_s(pp, Nat.double(pp), le_dbl(pp))

# two to a larger power is at least as large
def jenc.pow_le(+aa: Nat, +kk: Nat) -> {Nat.is_le(Nat.pow(2n, aa), Nat.pow(2n, Nat.add(kk, aa))) == True{} : Bool}:
  match kk:
    case 0n:
      M1.le_refl(Nat.pow(2n, aa))
    case 1n+ +qq:
      M1.le_trans(Nat.pow(2n, aa), Nat.pow(2n, Nat.add(qq, aa)), Nat.pow(2n, 1n+Nat.add(qq, aa)), jenc.pow_le(aa, qq),
        M1.le_rw_r(Nat.pow(2n, Nat.add(qq, aa)), Nat.double(Nat.pow(2n, Nat.add(qq, aa))), Nat.pow(2n, 1n+Nat.add(qq,
          aa)),
        Equal.sym(Nat, Nat.pow(2n, 1n+Nat.add(qq, aa)), Nat.double(Nat.pow(2n, Nat.add(qq, aa))),
          M1.pow2_succ(Nat.add(qq,
        aa))), le_dbl(Nat.pow(2n, Nat.add(qq, aa)))))

# a product with a larger right factor is at least as large
def mul_le_r(
  +pp: Nat,
  +bb: Nat,
  +qq: Nat,
  hh: {Nat.is_le(bb, qq) == True{} : Bool}
) -> {Nat.is_le(Nat.mul(pp, bb), Nat.mul(pp, qq)) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_le(Nat.mul(pp, bb), Nat.mul(pp, qq)), Nat.is_le(Nat.mul(bb, pp), Nat.mul(qq, pp)), True{},
    Equal.trans(Bool, Nat.is_le(Nat.mul(pp, bb), Nat.mul(pp, qq)), Nat.is_le(Nat.mul(bb, pp), Nat.mul(pp, qq)),
    Nat.is_le(Nat.mul(bb, pp), Nat.mul(qq, pp)), Equal.cong(Nat, Bool, xx => Nat.is_le(xx, Nat.mul(pp, qq)), Nat.mul(pp,
    bb), Nat.mul(bb, pp), M1.mul_comm(pp, bb)), Equal.cong(Nat, Bool, xx => Nat.is_le(Nat.mul(bb, pp), xx), Nat.mul(pp,
    qq), Nat.mul(qq, pp), M1.mul_comm(pp, qq))), M7.le_mul_mono(bb, qq, pp, hh))

# a number is below it plus a positive number, added on the left
def lt_addq(
  +xx: Nat,
  +qq: Nat,
  hq: {Nat.is_lt(0n, qq) == True{} : Bool}
) -> {Nat.is_lt(xx, Nat.add(qq, xx)) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_lt(xx, Nat.add(qq, xx)), Nat.is_lt(xx, Nat.add(xx, qq)), True{}, Equal.cong(Nat, Bool, nn =>
    Nat.is_lt(xx, nn), Nat.add(qq, xx), Nat.add(xx, qq), M1.ras.add_comm(qq, xx)), M3.lt_add_pos(xx, qq, hq))

# a product of two numbers below p and q is below p q
def mul_lt(
  +aa: Nat,
  +bb: Nat,
  pp: Nat,
  +qq: Nat,
  ha: {Nat.is_lt(aa, pp) == True{} : Bool},
  +hb: {Nat.is_lt(bb, qq) == True{} : Bool}
) -> {Nat.is_lt(Nat.mul(aa, bb), Nat.mul(pp, qq)) == True{} : Bool}:
  match pp:
    case 0n:
      Empty.absurd({Nat.is_lt(Nat.mul(aa, bb), 0n) == True{} : Bool}, M1.huf.false_true(Equal.trans(Bool, False{},
        Nat.is_lt(aa, 0n), True{}, M1.lt_zero_false(aa), ha)))
    case 1n+ +p1:
      M1.le_lt_trans(Nat.mul(aa, bb), Nat.mul(p1, qq), Nat.add(qq, Nat.mul(p1, qq)), M1.le_trans(Nat.mul(aa, bb),
        Nat.mul(p1,
        bb), Nat.mul(p1, qq), M7.le_mul_mono(aa, p1, bb, Equal.trans(Bool, Nat.is_le(aa, p1), Nat.is_lt(aa, 1n+p1),
        True{}, Equal.sym(Bool, Nat.is_lt(aa, 1n+p1), Nat.is_le(aa, p1), M3.lt_s_le(aa, p1)), ha)), mul_le_r(p1, bb, qq,
        M1.lt_le(bb, qq, hb))), lt_addq(Nat.mul(p1, qq), qq, M1.le_lt_trans(0n, bb, qq, M1.le_zero(bb), hb)))

# two to a larger power is at least as large, by the exponents' order
def pow_mono(
  +aa: Nat,
  +bb: Nat,
  hh: {Nat.is_le(aa, bb) == True{} : Bool}
) -> {Nat.is_le(Nat.pow(2n, aa), Nat.pow(2n, bb)) == True{} : Bool}:
  +dd = Nat.sub(bb, aa)
  M1.le_rw_r(Nat.pow(2n, aa), Nat.pow(2n, Nat.add(dd, aa)), Nat.pow(2n, bb), Equal.cong(Nat, Nat, xx => Nat.pow(2n, xx),
    Nat.add(dd, aa), bb, Equal.trans(Nat, Nat.add(dd, aa), Nat.add(aa, dd), bb, M1.ras.add_comm(dd, aa), M6.add_sub(aa,
        bb,
    hh))), jenc.pow_le(aa, dd))

# a product of numbers below 2^i and 2^j is below 2^(i + j)
def mul_pow(
  +aa: Nat,
  +bb: Nat,
  +ii: Nat,
  +jj: Nat,
  ha: {Nat.is_lt(aa, Nat.pow(2n, ii)) == True{} : Bool},
  +hb: {Nat.is_lt(bb, Nat.pow(2n, jj)) == True{} : Bool}
) -> {Nat.is_lt(Nat.mul(aa, bb), Nat.pow(2n, Nat.add(ii, jj))) == True{} : Bool}:
  M1.lt_rw_r(Nat.mul(aa, bb), Nat.mul(Nat.pow(2n, ii), Nat.pow(2n, jj)), Nat.pow(2n, Nat.add(ii, jj)), Equal.sym(Nat,
    Nat.pow(2n, Nat.add(ii, jj)), Nat.mul(Nat.pow(2n, ii), Nat.pow(2n, jj)), pow_add(ii, jj)), mul_lt(aa, bb,
      Nat.pow(2n,
    ii), Nat.pow(2n, jj), ha, hb))

# twice numbers keep their order
def dbl_iff(aa: Nat, bb: Nat) -> {Nat.is_lt(Nat.double(aa), Nat.double(bb)) == Nat.is_lt(aa, bb) : Bool}:
  match aa bb:
    case 0n 0n:
      {==}
    case 0n 1n+_q:
      {==}
    case 1n+_p 0n:
      {==}
    case 1n+pp 1n+qq:
      dbl_iff(pp, qq)

# eight times numbers keep their order
def eight_iff(+aa: Nat, +bb: Nat) -> {Nat.is_lt(M1.eight(aa), M1.eight(bb)) == Nat.is_lt(aa, bb) : Bool}:
  Equal.trans(Bool, Nat.is_lt(M1.eight(aa), M1.eight(bb)), Nat.is_lt(Nat.double(Nat.double(aa)), Nat.double(
    Nat.double(bb))), Nat.is_lt(aa, bb), dbl_iff(Nat.double(Nat.double(aa)), Nat.double(Nat.double(bb))), Equal.trans(
    Bool, Nat.is_lt(Nat.double(Nat.double(aa)), Nat.double(Nat.double(bb))), Nat.is_lt(Nat.double(aa), Nat.double(bb)),
    Nat.is_lt(aa, bb), dbl_iff(Nat.double(aa), Nat.double(bb)), dbl_iff(aa, bb)))

# a quotient by 8 of a number at least 8 is above 0
def q_pos(
  qq: Nat,
  +xx: Nat,
  +rr: Nat,
  ee: {xx == Nat.add(rr, M1.eight(qq)) : Nat},
  hr: {Nat.is_lt(rr, 8n) == True{} : Bool},
  hx: {Nat.is_le(8n, xx) == True{} : Bool}
) -> {Nat.is_lt(0n, qq) == True{} : Bool}:
  match qq:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, M3.jenc.true_false(Equal.trans(Bool, True{}, Nat.is_le(8n, rr),
        False{}, Equal.sym(Bool, Nat.is_le(8n, rr), True{}, Equal.trans(Bool, Nat.is_le(8n, rr), Nat.is_le(8n, xx),
          True{},
        Equal.cong(Nat, Bool, nn => Nat.is_le(8n, nn), rr, xx, Equal.sym(Nat, xx, rr, Equal.trans(Nat, xx, Nat.add(rr,
        0n), rr, ee, M1.ras.add_zero(rr)))), hx)), M3.lt_nle(rr, 8n, hr))))
    case 1n+_p:
      {==}

# a number an n-bit word holds
def Fits(+nn: Nat, +xx: Nat) -> Type:
  &ww: Word(nn) -> {Word.to_nat(nn, ww) == xx : Nat}

# a number is twice its half and its parity
def halfeq(nn: Nat) -> {nn == Nat.add(Nat.double(M1.half(nn)), M1.bit(M1.odd(nn))) : Nat}:
  match nn:
    case 0n:
      {==}
    case 1n+0n:
      {==}
    case 1n+1n+ +pp:
      Equal.cong(Nat, Nat, xx => 2n+xx, pp, Nat.add(Nat.double(M1.half(pp)), M1.bit(M1.odd(pp))), halfeq(pp))

# the low n bits of a number, as a word
def wof(nn: Nat, +xx: Nat) -> Word(nn):
  match nn:
    case 0n:
      WNil{}
    case 1n+pp:
      WCon{M1.odd(xx), wof(pp, M1.half(xx))}

# a number below 2^n is held by its low n bits
def lt_fits(
  nn: Nat,
  +xx: Nat,
  hh: {Nat.is_lt(xx, Nat.pow(2n, nn)) == True{} : Bool}
) -> {Word.to_nat(nn, wof(nn, xx)) == xx : Nat}:
  match nn:
    case 0n:
      M1.lt1(xx, hh)
    case 1n+ +pp:
      +hf = M1.half(xx)
      +ob = M1.bit(M1.odd(xx))
      +ex = {Equal.trans(Nat, xx, Nat.add(Nat.double(hf), ob), Nat.add(ob, Nat.double(hf)), halfeq(xx), M1.ras.add_comm(
        Nat.double(hf), ob)) : {xx == Nat.add(ob, Nat.double(hf)) : Nat}}
      +hl = {M1.lt_half(M1.odd(xx), hf, Nat.pow(2n, pp), M1.lt_rw_l(xx, Nat.add(ob, Nat.double(hf)),
          Nat.double(Nat.pow(2n,
        pp)), ex, M1.lt_rw_r(xx, Nat.pow(2n, 1n+pp), Nat.double(Nat.pow(2n, pp)), M1.pow2_succ(pp),
            hh))) : {Nat.is_lt(hf,
        Nat.pow(2n, pp)) == True{} : Bool}}
      Equal.trans(Nat, Word.to_nat(1n+pp, WCon{M1.odd(xx), wof(pp, hf)}), Nat.add(ob, Nat.double(Word.to_nat(pp, wof(pp,
        hf)))), xx, M1.to_nat_con(pp, M1.odd(xx), wof(pp, hf)), Equal.trans(Nat, Nat.add(ob, Nat.double(Word.to_nat(pp,
          wof(pp,
        hf)))), Nat.add(ob, Nat.double(hf)), xx, Equal.cong(Nat, Nat, yy => Nat.add(ob, Nat.double(yy)), Word.to_nat(pp,
        wof(pp, hf)), hf, lt_fits(pp, hf, hl)), Equal.sym(Nat, xx, Nat.add(ob, Nat.double(hf)), ex)))

# a number below 2^n fits n bits
def mkfits(+nn: Nat, +xx: Nat, hh: {Nat.is_lt(xx, Nat.pow(2n, nn)) == True{} : Bool}) -> Fits(nn, xx):
  (wof(nn, xx), lt_fits(nn, xx, hh))

# a number n bits hold is below 2^n
def fits_lt(+nn: Nat, +xx: Nat, ff: Fits(nn, xx)) -> {Nat.is_lt(xx, Nat.pow(2n, nn)) == True{} : Bool}:
  (+ww, ee) = ff
  M1.lt_rw_l(Word.to_nat(nn, ww), xx, Nat.pow(2n, nn), ee, M7.word_lt_pow(nn, ww))

# a sum of two numbers of n bits fits n + 1 bits
def fits_add(+ii: Nat, +aa: Nat, +bb: Nat, fa: Fits(ii, aa), fb: Fits(ii, bb)) -> Fits(1n+ii, Nat.add(aa, bb)):
  +pw = Nat.pow(2n, ii)
  +ha = {fits_lt(ii, aa, fa) : {Nat.is_lt(aa, pw) == True{} : Bool}}
  +hb = {fits_lt(ii, bb, fb) : {Nat.is_lt(bb, pw) == True{} : Bool}}
  mkfits(1n+ii, Nat.add(aa, bb), M1.lt_rw_r(Nat.add(aa, bb), Nat.double(pw), Nat.pow(2n, 1n+ii), Equal.sym(Nat,
    Nat.pow(2n, 1n+ii), Nat.double(pw), M1.pow2_succ(ii)), M1.lt_le_trans(Nat.add(aa, bb), Nat.add(aa, pw),
      Nat.double(pw),
    M1.lt_add_mono(aa, bb, pw, hb), M1.le_rw_r(Nat.add(aa, pw), Nat.add(pw, pw), Nat.double(pw), Equal.sym(Nat,
    Nat.double(pw), Nat.add(pw, pw), M1.double_add(pw)), M3.le_addr(aa, pw, pw, M1.lt_le(aa, pw, ha))))))

# a number of i bits fits k + i bits
def fits_up(+ii: Nat, +kk: Nat, +aa: Nat, fa: Fits(ii, aa)) -> Fits(Nat.add(kk, ii), aa):
  mkfits(Nat.add(kk, ii), aa, M1.lt_le_trans(aa, Nat.pow(2n, ii), Nat.pow(2n, Nat.add(kk, ii)), fits_lt(ii, aa, fa),
    jenc.pow_le(ii, kk)))

# U32 add, when the sum fits 32 bits, is Nat add
def uadd_fits(
  +au: U32,
  +bu: U32,
  ff: Fits(32n, Nat.add(U32.to_nat(au), U32.to_nat(bu)))
) -> {U32.to_nat((au + bu : U32)) == Nat.add(U32.to_nat(au), U32.to_nat(bu)) : Nat}:
  (+ww, ee) = ff
  +sm = Nat.add(U32.to_nat(au), U32.to_nat(bu))
  M7.u32_add_below(au, bu, U32{ww}, M1.le_rw_r(sm, sm, Word.to_nat(32n, ww), Equal.sym(Nat, Word.to_nat(32n, ww), sm,
      ee),
    M1.le_refl(sm)))

# a word of k bits, then a word of m bits above it
def wapp(kk: Nat, +mm: Nat, aa: Word(kk), bb: Word(mm)) -> Word(Nat.add(kk, mm)):
  match kk:
    case 0n:
      match aa:
        case WNil{}:
          bb
    case 1n+pp:
      match aa:
        case WCon{a0, at}:
          WCon{a0, wapp(pp, mm, at, bb)}

# the low k bits of a word of k + m bits
def wlo(kk: Nat, +mm: Nat, xx: Word(Nat.add(kk, mm))) -> Word(kk):
  match kk:
    case 0n:
      WNil{}
    case 1n+pp:
      match xx:
        case WCon{x0, xt}:
          WCon{x0, wlo(pp, mm, xt)}

# the high m bits of a word of k + m bits
def whi(kk: Nat, +mm: Nat, xx: Word(Nat.add(kk, mm))) -> Word(mm):
  match kk:
    case 0n:
      xx
    case 1n+pp:
      match xx:
        case WCon{_x, xt}:
          whi(pp, mm, xt)

# a word is its low bits and its high bits
def split_eq(
  kk: Nat,
  +mm: Nat,
  xx: Word(Nat.add(kk, mm))
) -> {wapp(kk, mm, wlo(kk, mm, xx), whi(kk, mm, xx)) == xx : Word(Nat.add(kk, mm))}:
  match kk:
    case 0n:
      {==}
    case 1n+ +pp:
      match xx:
        case WCon{+x0, +xt}:
          Equal.cong(Word(Nat.add(pp, mm)), Word.Con<Nat.add(pp, mm)>, ww => WCon{x0, ww}, wapp(pp, mm, wlo(pp, mm, xt),
            whi(pp, mm, xt)), xt, split_eq(pp, mm, xt))

# a word with zero high bits is its low bits' number
def zapp_nat(
  kk: Nat,
  +mm: Nat,
  aa: Word(kk)
) -> {Word.to_nat(Nat.add(kk, mm), wapp(kk, mm, aa, Word.zero(mm))) == Word.to_nat(kk, aa) : Nat}:
  match kk:
    case 0n:
      match aa:
        case WNil{}:
          M5.word_zero_nat(mm)
    case 1n+ +pp:
      match aa:
        case WCon{+a0, +at}:
          Equal.trans(Nat, Word.to_nat(1n+Nat.add(pp, mm), WCon{a0, wapp(pp, mm, at, Word.zero(mm))}),
            Nat.add(M1.bit(a0),
            Nat.double(Word.to_nat(Nat.add(pp, mm), wapp(pp, mm, at, Word.zero(mm))))), Word.to_nat(1n+pp, WCon{a0,
              at}),
            M1.to_nat_con(Nat.add(pp, mm), a0, wapp(pp, mm, at, Word.zero(mm))), Equal.trans(Nat, Nat.add(M1.bit(a0),
            Nat.double(Word.to_nat(Nat.add(pp, mm), wapp(pp, mm, at, Word.zero(mm))))), Nat.add(M1.bit(a0), Nat.double(
            Word.to_nat(pp, at))), Word.to_nat(1n+pp, WCon{a0, at}), Equal.cong(Nat, Nat, xx => Nat.add(M1.bit(a0),
            Nat.double(xx)), Word.to_nat(Nat.add(pp, mm), wapp(pp, mm, at, Word.zero(mm))), Word.to_nat(pp, at),
              zapp_nat(pp,
            mm, at)), Equal.sym(Nat, Word.to_nat(1n+pp, WCon{a0, at}), Nat.add(M1.bit(a0), Nat.double(Word.to_nat(pp,
              at))),
            M1.to_nat_con(pp, a0, at))))

# a one-bit compare against 0, when it is not above, is of 0
def nz0.b(
  aa: Bool,
  tt: Cmp,
  ht: {tt == EQ{} : Cmp},
  hh: {Cmp.is_gt(Word.cmp.fin(aa, False{}, tt)) == False{} : Bool}
) -> {aa == False{} : Bool}:
  match aa:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, M3.jenc.true_false(Equal.trans(Bool, True{},
          Cmp.is_gt(Word.cmp.fin(True{},
        False{}, tt)), False{}, Equal.cong(Cmp, Bool, cc => Cmp.is_gt(Word.cmp.fin(True{}, False{}, cc)), EQ{}, tt,
        Equal.sym(Cmp, tt, EQ{}, ht)), hh)))

# a word compares equal to itself
def cmp_refl(mm: Nat, xx: Word(mm)) -> {Word.cmp(mm, xx, xx) == EQ{} : Cmp}:
  match mm:
    case 0n:
      {==}
    case 1n+ +pp:
      match xx:
        case WCon{False{}, +xt}:
          Equal.cong(Cmp, Cmp, cc => Word.cmp.fin(False{}, False{}, cc), Word.cmp(pp, xt, xt), EQ{}, cmp_refl(pp, xt))
        case WCon{True{}, +xt}:
          Equal.cong(Cmp, Cmp, cc => Word.cmp.fin(True{}, True{}, cc), Word.cmp(pp, xt, xt), EQ{}, cmp_refl(pp, xt))

# a word not above 0 is 0
def nz0(
  mm: Nat,
  xx: Word(mm),
  +hh: {Cmp.is_gt(Word.cmp(mm, xx, Word.zero(mm))) == False{} : Bool}
) -> {xx == Word.zero(mm) : Word(mm)}:
  match mm:
    case 0n:
      match xx:
        case WNil{}:
          {==}
    case 1n+ +pp:
      match xx:
        case WCon{+a0, +xt}:
          +et = {nz0(pp, xt, M3.fin_ngt(a0, False{}, Word.cmp(pp, xt, Word.zero(pp)), hh)) : {xt == Word.zero(pp) :
            Word(pp)}}
          +ht = {Equal.trans(Cmp, Word.cmp(pp, xt, Word.zero(pp)), Word.cmp(pp, Word.zero(pp), Word.zero(pp)), EQ{},
            Equal.cong(Word(pp), Cmp, ww => Word.cmp(pp, ww, Word.zero(pp)), xt, Word.zero(pp), et), cmp_refl(pp,
            Word.zero(pp))) : {Word.cmp(pp, xt, Word.zero(pp)) == EQ{} : Cmp}}
          +e0 = {nz0.b(a0, Word.cmp(pp, xt, Word.zero(pp)), ht, hh) : {a0 == False{} : Bool}}
          Equal.trans(Word(1n+pp), WCon{a0, xt}, WCon{False{}, xt}, WCon{False{}, Word.zero(pp)}, Equal.cong(Bool,
            Word(1n+pp), bb => WCon{bb, xt}, a0, False{}, e0), Equal.cong(Word(pp), Word(1n+pp), ww => WCon{False{},
              ww}, xt,
            Word.zero(pp), et))

# a word not above one with zero high bits has zero high bits
def hi_zero(
  kk: Nat,
  +mm: Nat,
  xl: Word(kk),
  +xh: Word(mm),
  cl: Word(kk),
  hh: {Cmp.is_gt(Word.cmp(Nat.add(kk, mm), wapp(kk, mm, xl, xh), wapp(kk, mm, cl, Word.zero(mm)))) == False{} : Bool}
) -> {xh == Word.zero(mm) : Word(mm)}:
  match kk:
    case 0n:
      match xl cl:
        case WNil{} WNil{}:
          nz0(mm, xh, hh)
    case 1n+ +pp:
      match xl cl:
        case WCon{+x0, +xt} WCon{+c0, +ct}:
          hi_zero(pp, mm, xt, xh, ct, M3.fin_ngt(x0, c0, Word.cmp(Nat.add(pp, mm), wapp(pp, mm, xt, xh), wapp(pp, mm,
              ct,
            Word.zero(mm))), hh))

# at most is not above
def jenc.le_ngt(tt: Cmp, hh: {Cmp.is_le(tt) == True{} : Bool}) -> {Cmp.is_gt(tt) == False{} : Bool}:
  match tt:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({Cmp.is_gt(GT{}) == False{} : Bool}, M1.huf.false_true(hh))

# a side at most 65535 fits 16 bits
def fits16(+ww: U32, hh: {U32.is_le(ww, 65535) == True{} : Bool}) -> Fits(16n, U32.to_nat(ww)):
  match ww:
    case U32{+xw}:
      +lo = wlo(16n, 16n, xw)
      +hi = whi(16n, 16n, xw)
      +cl = wlo(16n, 16n, M3.uw(65535))
      +es = {split_eq(16n, 16n, xw) : {wapp(16n, 16n, lo, hi) == xw : Word(32n)}}
      +hg = {Equal.trans(Bool, Cmp.is_gt(Word.cmp(32n, wapp(16n, 16n, lo, hi), wapp(16n, 16n, cl, Word.zero(16n)))),
        Cmp.is_gt(Word.cmp(32n, xw, M3.uw(65535))), False{}, Equal.cong(Word(32n), Bool, ww2 => Cmp.is_gt(Word.cmp(32n,
          ww2,
        M3.uw(65535))), wapp(16n, 16n, lo, hi), xw, es), jenc.le_ngt(Word.cmp(32n, xw, M3.uw(65535)), hh)) :
        {Cmp.is_gt(Word.cmp(32n, wapp(16n, 16n, lo, hi), wapp(16n, 16n, cl, Word.zero(16n)))) == False{} : Bool}}
      +ez = {hi_zero(16n, 16n, lo, hi, cl, hg) : {hi == Word.zero(16n) : Word(16n)}}
      (lo, Equal.sym(Nat, Word.to_nat(32n, xw), Word.to_nat(16n, lo), Equal.trans(Nat, Word.to_nat(32n, xw),
        Word.to_nat(32n, wapp(16n, 16n, lo, hi)), Word.to_nat(16n, lo), Equal.cong(Word(32n), Nat,
          ww2 => Word.to_nat(32n,
        ww2), xw, wapp(16n, 16n, lo, hi), Equal.sym(Word(32n), wapp(16n, 16n, lo, hi), xw, es)), Equal.trans(Nat,
        Word.to_nat(32n, wapp(16n, 16n, lo, hi)), Word.to_nat(32n, wapp(16n, 16n, lo, Word.zero(16n))), Word.to_nat(16n,
        lo), Equal.cong(Word(16n), Nat, ww2 => Word.to_nat(32n, wapp(16n, 16n, lo, ww2)), hi, Word.zero(16n), ez),
        zapp_nat(16n, 16n, lo)))))

# two to 3 + k is eight times two to k
def pow3(+kk: Nat) -> {Nat.pow(2n, 3n+kk) == M1.eight(Nat.pow(2n, kk)) : Nat}:
  +p0 = Nat.pow(2n, kk)
  Equal.trans(Nat, Nat.pow(2n, 3n+kk), Nat.double(Nat.pow(2n, 2n+kk)), M1.eight(p0), M1.pow2_succ(2n+kk),
    Equal.cong(Nat, Nat, xx => Nat.double(xx), Nat.pow(2n, 2n+kk), Nat.double(Nat.double(p0)), Equal.trans(Nat,
      Nat.pow(2n,
    2n+kk), Nat.double(Nat.pow(2n, 1n+kk)), Nat.double(Nat.double(p0)), M1.pow2_succ(1n+kk), Equal.cong(Nat, Nat, xx =>
    Nat.double(xx), Nat.pow(2n, 1n+kk), Nat.double(p0), M1.pow2_succ(kk)))))

# a quotient by 8 of a number of k + 3 bits fits k bits
def qfits(
  +kk: Nat,
  +xx: Nat,
  +rr: Nat,
  +qq: Nat,
  ee: {xx == Nat.add(rr, M1.eight(qq)) : Nat},
  ff: Fits(3n+kk, xx)
) -> Fits(kk, qq):
  +pk = Nat.pow(2n, kk)
  +hx = {fits_lt(3n+kk, xx, ff) : {Nat.is_lt(xx, Nat.pow(2n, 3n+kk)) == True{} : Bool}}
  +h8 = {M1.le_lt_trans(M1.eight(qq), xx, M1.eight(pk), M1.le_rw_r(M1.eight(qq), Nat.add(rr, M1.eight(qq)), xx,
    Equal.sym(Nat, xx, Nat.add(rr, M1.eight(qq)), ee), M3.le_add_left(rr, M1.eight(qq))), M1.lt_rw_r(xx, Nat.pow(2n,
    3n+kk), M1.eight(pk), pow3(kk), hx)) : {Nat.is_lt(M1.eight(qq), M1.eight(pk)) == True{} : Bool}}
  mkfits(kk, qq, Equal.trans(Bool, Nat.is_lt(qq, pk), Nat.is_lt(M1.eight(qq), M1.eight(pk)), True{}, Equal.sym(
    Bool, Nat.is_lt(M1.eight(qq), M1.eight(pk)), Nat.is_lt(qq, pk), eight_iff(qq, pk)), h8))

# a fit moved along an equality
def fits_tr(+nn: Nat, +aa: Nat, +bb: Nat, ee: {aa == bb : Nat}, ff: Fits(nn, aa)) -> Fits(nn, bb):
  %ee : Fits(nn, _)
  ff

# a side of 1 to 65535, plus 7, as a Nat, and the side's MCU count: fits 14 bits and is at least 1
def MwOut(+ww: U32) -> Type:
  &_e: {U32.to_nat((ww + 7 : U32)) == Nat.add(U32.to_nat(ww), 7n) : Nat} -> &_f: Fits(14n, U32.to_nat(U32.div((ww +
    7 : U32), 8))) -> {Nat.is_lt(0n, U32.to_nat(U32.div((ww + 7 : U32), 8))) == True{} : Bool}

# the type of mw_fin's parameter dv
def mw_fin.dv.ty(+_ww: U32) -> Type:
  &rr: U32 -> &_e: {U32.to_nat((_ww + 7 : U32)) == Nat.add(U32.to_nat(rr), M1.eight(U32.to_nat(U32.div((_ww + 7 : U32),
    8)))) : Nat} -> {U32.is_lt(rr, 8) == True{} : Bool}

# a side's MCU count, its division named
def mw_fin(
  +ww: U32,
  fw: Fits(16n, U32.to_nat(ww)),
  +e7: {U32.to_nat((ww + 7 : U32)) == Nat.add(U32.to_nat(ww), 7n) : Nat},
  +h8: {Nat.is_le(8n, Nat.add(U32.to_nat(ww), 7n)) == True{} : Bool},
  dv: mw_fin.dv.ty(ww)
) -> MwOut(ww):
  (+rr, +ed, hr) = dv
  +xx = U32.to_nat((ww + 7 : U32))
  +qn = U32.to_nat(U32.div((ww + 7 : U32), 8))
  (e7, qfits(14n, xx, U32.to_nat(rr), qn, ed, fits_tr(17n, Nat.add(U32.to_nat(ww), 7n), xx, Equal.sym(Nat, xx,
    Nat.add(U32.to_nat(ww), 7n), e7), fits_add(16n, U32.to_nat(ww), 7n, fw, (wof(16n, 7n), {==})))), q_pos(qn, xx,
      U32.to_nat(rr), ed, M3.ult_n(rr, 8, hr),
    M1.le_rw_r(8n, Nat.add(U32.to_nat(ww), 7n), xx, Equal.sym(Nat, xx, Nat.add(U32.to_nat(ww), 7n), e7), h8)))

# at most 0 is 0
def ngt_le0(nn: Nat) -> {Nat.is_le(nn, 0n) == Nat.is_eq(nn, 0n) : Bool}:
  match nn:
    case 0n:
      {==}
    case 1n+_p:
      {==}

# a nonzero side at most 65535: its MCU count fits 14 bits and is at least 1
def mw_ok(
  +ww: U32,
  h0: {U32.is_eq(ww, 0) == False{} : Bool},
  +hl: {U32.is_le(ww, 65535) == True{} : Bool}
) -> MwOut( ww):
  +wn = U32.to_nat(ww)
  +e7 = {uadd_fits(ww, 7, fits_up(17n, 15n, Nat.add(wn, 7n), fits_add(16n, wn, 7n, fits16(ww, hl), (wof(16n, 7n),
    {==})))) : {U32.to_nat((ww + 7 : U32)) == Nat.add(wn, 7n) : Nat}}
  +hw = {M3.nle_lt(wn, 0n, Equal.trans(Bool, Nat.is_le(wn, 0n), Nat.is_eq(wn, 0n), False{}, ngt_le0(wn),
      Equal.trans(Bool,
    Nat.is_eq(wn, 0n), U32.is_eq(ww, 0), False{}, Equal.sym(Bool, U32.is_eq(ww, 0), Nat.is_eq(wn, 0n), M1.u32_eq(ww,
        0)),
    h0))) : {Nat.is_lt(0n, wn) == True{} : Bool}}
  mw_fin(ww, fits16(ww, hl), e7, M3.le_addr(1n, wn, 7n, Equal.trans(Bool, Nat.is_le(1n, wn), Nat.is_lt(0n, wn), True{},
    Equal.sym(Bool,
    Nat.is_lt(0n, wn), Nat.is_le(1n, wn), M1.lt_le_succ(0n, wn)), hw)), udiv8((ww + 7 : U32)))

# a product of three words of i, j and k bits, i + j + k at most n, never wraps
def word_triple(
  +nn: Nat,
  +ii: Nat,
  +jj: Nat,
  +kk: Nat,
  +aw: Word(nn),
  +bw: Word(nn),
  +cw: Word(nn),
  fa: Fits(ii, Word.to_nat(nn, aw)),
  fb: Fits(jj, Word.to_nat(nn, bw)),
  fc: Fits(kk, Word.to_nat(nn, cw)),
  +hs: {Nat.is_le(Nat.add(Nat.add(ii, jj), kk), nn) == True{} : Bool}
) -> &_p: {Word.to_nat(nn, Word.mul(nn, aw, bw)) == Nat.mul(Word.to_nat(nn, aw), Word.to_nat(nn,
  bw)) : Nat} -> {Word.to_nat(nn, Word.mul(nn, Word.mul(nn, aw, bw), cw)) == Nat.mul(Nat.mul(Word.to_nat(nn, aw),
  Word.to_nat(nn, bw)), Word.to_nat(nn, cw)) : Nat}:
  +an = Word.to_nat(nn, aw)
  +bn = Word.to_nat(nn, bw)
  +cn = Word.to_nat(nn, cw)
  +ij = Nat.add(ii, jj)
  +hab = {mul_pow(an, bn, ii, jj, fits_lt(ii, an, fa), fits_lt(jj, bn, fb)) : {Nat.is_lt(Nat.mul(an, bn),
    Nat.pow(2n, ij)) == True{} : Bool}}
  +habc = {mul_pow(Nat.mul(an, bn), cn, ij, kk, hab, fits_lt(kk, cn, fc)) : {Nat.is_lt(Nat.mul(Nat.mul(an, bn),
    cn), Nat.pow(2n, Nat.add(ij, kk))) == True{} : Bool}}
  +pn = {pow_mono(Nat.add(ij, kk), nn, hs) : {Nat.is_le(Nat.pow(2n, Nat.add(ij, kk)), Nat.pow(2n, nn)) == True{} :
    Bool}}
  +pij = {pow_mono(ij, nn, M1.le_trans(ij, Nat.add(ij, kk), nn, M6.le_add_more(ij, ij, kk, M1.le_refl(ij)), hs)) :
    {Nat.is_le(Nat.pow(2n, ij), Nat.pow(2n, nn)) == True{} : Bool}}
  +e1 = {word_mul_pow(nn, aw, bw, M1.lt_le_trans(Nat.mul(an, bn), Nat.pow(2n, ij), Nat.pow(2n, nn), hab, pij)) :
    {Word.to_nat(nn, Word.mul(nn, aw, bw)) == Nat.mul(an, bn) : Nat}}
  +xw = Word.mul(nn, aw, bw)
  (e1, Equal.trans(Nat, Word.to_nat(nn, Word.mul(nn, xw, cw)), Nat.mul(Word.to_nat(nn, xw), cn), Nat.mul(Nat.mul(an,
    bn),
    cn), word_mul_pow(nn, xw, cw, Equal.trans(Bool, Nat.is_lt(Nat.mul(Word.to_nat(nn, xw), cn), Nat.pow(2n, nn)),
    Nat.is_lt(Nat.mul(Nat.mul(an, bn), cn), Nat.pow(2n, nn)), True{}, Equal.cong(Nat, Bool, xx => Nat.is_lt(Nat.mul(xx,
    cn), Nat.pow(2n, nn)), Word.to_nat(nn, xw), Nat.mul(an, bn), e1), M1.lt_le_trans(Nat.mul(Nat.mul(an, bn), cn),
    Nat.pow(2n, Nat.add(ij, kk)), Nat.pow(2n, nn), habc, pn))), Equal.cong(Nat, Nat, xx => Nat.mul(xx, cn),
    Word.to_nat(nn, xw), Nat.mul(an, bn), e1)))

# the MCU counts' product, and it times 3, never wrap
def u32_triple(
  +au: U32,
  +bu: U32,
  +cu: U32,
  fa: Fits(14n, U32.to_nat(au)),
  fb: Fits(14n, U32.to_nat(bu)),
  fc: Fits(2n, U32.to_nat(cu))
) -> &_p: {U32.to_nat((au * bu : U32)) == Nat.mul(U32.to_nat(au),
  U32.to_nat(bu)) : Nat} -> {U32.to_nat(((au * bu : U32) * cu : U32)) == Nat.mul(Nat.mul(U32.to_nat(au),
  U32.to_nat(bu)), U32.to_nat(cu)) : Nat}:
  match au bu cu:
    case U32{+aw} U32{+bw} U32{+cw}:
      word_triple(32n, 14n, 14n, 2n, aw, bw, cw, fa, fb, fc, {==})

# three for each is three times
def tri_mul(nn: Nat) -> {M2.tri(nn) == Nat.mul(nn, 3n) : Nat}:
  match nn:
    case 0n:
      {==}
    case 1n+ +pp:
      Equal.cong(Nat, Nat, xx => 3n+xx, M2.tri(pp), Nat.mul(pp, 3n), tri_mul(pp))

# U32s of the same number are the same
def unat_eq(+aa: U32, +bb: U32, ee: {U32.to_nat(aa) == U32.to_nat(bb) : Nat}) -> {aa == bb : U32}:
  M1.ueq(aa, bb, Equal.trans(Bool, U32.is_eq(aa, bb), Nat.is_eq(U32.to_nat(aa), U32.to_nat(bb)), True{}, M1.u32_eq(aa,
    bb), Equal.trans(Bool, Nat.is_eq(U32.to_nat(aa), U32.to_nat(bb)), Nat.is_eq(U32.to_nat(bb), U32.to_nat(bb)), True{},
    Equal.cong(Nat, Bool, nn => Nat.is_eq(nn, U32.to_nat(bb)), U32.to_nat(aa), U32.to_nat(bb), ee), M1.nat_eq_refl(
    U32.to_nat(bb)))))

# the decoder's rounding up, w + 8 - 1, is the encoder's, w + 7, for a side at most 65535
def ceil_eq(
  +ww: U32,
  +hl: {U32.is_le(ww, 65535) == True{} : Bool},
  +e7: {U32.to_nat((ww + 7 : U32)) == Nat.add(U32.to_nat(ww), 7n) : Nat}
) -> {((ww + 8 : U32) - 1 : U32) == (ww + 7 : U32) : U32}:
  +wn = U32.to_nat(ww)
  +e8 = {uadd_fits(ww, 8, fits_up(17n, 15n, Nat.add(wn, 8n), fits_add(16n, wn, 8n, fits16(ww, hl), (wof(16n,
    8n), {==})))) : {U32.to_nat((ww + 8 : U32)) == Nat.add(wn, 8n) : Nat}}
  +h1 = {M1.le_rw_r(1n, Nat.add(wn, 8n), U32.to_nat((ww + 8 : U32)), Equal.sym(Nat, U32.to_nat((ww + 8 : U32)),
    Nat.add(wn,
    8n), e8), M1.le_trans(1n, 8n, Nat.add(wn, 8n), {==}, M3.le_add_left(wn, 8n))) : {Nat.is_le(1n, U32.to_nat((ww + 8 :
    U32))) == True{} : Bool}}
  unat_eq(((ww + 8 : U32) - 1 : U32), (ww + 7 : U32), Equal.trans(Nat, U32.to_nat(((ww + 8 : U32) - 1 : U32)), Nat.sub(
    U32.to_nat((ww + 8 : U32)), 1n), U32.to_nat((ww + 7 : U32)), M6.ras.u32_sub_nat((ww + 8 : U32), 1, h1),
        Equal.trans(Nat,
    Nat.sub(U32.to_nat((ww + 8 : U32)), 1n), Nat.sub(1n+Nat.add(wn, 7n), 1n), U32.to_nat((ww + 7 : U32)),
      Equal.cong(Nat,
    Nat, nn => Nat.sub(nn, 1n), U32.to_nat((ww + 8 : U32)), 1n+Nat.add(wn, 7n), Equal.trans(Nat, U32.to_nat((ww + 8 :
    U32)), Nat.add(wn, 8n), 1n+Nat.add(wn, 7n), e8, M1.ras.add_succ(wn, 7n))), Equal.trans(Nat, Nat.sub(Nat.add(wn,
        7n), 0n),
    Nat.add(wn, 7n), U32.to_nat((ww + 7 : U32)), M6.sub_zero(Nat.add(wn, 7n)), Equal.sym(Nat,
        U32.to_nat((ww + 7 : U32)),
    Nat.add(wn, 7n), e7)))))

# the encoder's MCU count and the decoder's block count, for sides of 1 to 65535: three blocks per MCU, at least one
# MCU
def CountOut(+ww: U32, +hh: U32) -> Type:
  &_n: {U32.to_nat(Jpeg.decode.nblocks(ww, hh, [1, 1, 1], [1, 1, 1], 1, 1)) == M2.tri(U32.to_nat(M2.mcun(ww,
      hh))) : Nat} ->
    &_p: {Nat.is_lt(0n, U32.to_nat(M2.mcun(ww, hh))) == True{} : Bool} -> {1n+U32.to_nat((M2.mcun(ww, hh) - 1 : U32)) ==
    U32.to_nat(M2.mcun(ww, hh)) : Nat}

# a product of two numbers above 0 is above 0
def pos_mul(
  aa: Nat,
  +bb: Nat,
  ha: {Nat.is_lt(0n, aa) == True{} : Bool},
  hb: {Nat.is_lt(0n, bb) == True{} : Bool}
) -> {Nat.is_lt(0n, Nat.mul(aa, bb)) == True{} : Bool}:
  match aa:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, M1.huf.false_true(ha))
    case 1n+ +pp:
      M1.lt_le_trans(0n, bb, Nat.add(bb, Nat.mul(pp, bb)), hb, M6.le_add_more(bb, bb, Nat.mul(pp, bb), M1.le_refl(bb)))

# the type of count_fin's parameter pr
def count_fin.pr.ty(+_ww: U32, +_hh: U32) -> Type:
  &_p: {U32.to_nat(M2.mcun(_ww, _hh)) == Nat.mul(U32.to_nat(U32.div((_ww + 7 : U32), 8)),
    U32.to_nat(U32.div((_hh + 7 : U32), 8))) : Nat} -> {U32.to_nat((M2.mcun(_ww,
    _hh) * 3 : U32)) == Nat.mul(Nat.mul(U32.to_nat(U32.div((_ww + 7 : U32), 8)), U32.to_nat(U32.div((_hh + 7 : U32),
    8))), 3n) : Nat}

# the counts, the products named
def count_fin(
  +ww: U32,
  +hh: U32,
  +cw: {((ww + 8 : U32) - 1 : U32) == (ww + 7 : U32) : U32},
  +ch: {((hh + 8 : U32) - 1 : U32) == (hh + 7 : U32) : U32},
  +pw: {Nat.is_lt(0n, U32.to_nat(U32.div((ww + 7 : U32), 8))) == True{} : Bool},
  +ph: {Nat.is_lt(0n, U32.to_nat(U32.div((hh + 7 : U32), 8))) == True{} : Bool},
  pr: count_fin.pr.ty(ww, hh)
) -> CountOut(ww, hh):
  (em0, e30) = pr
  +mw = U32.div((ww + 7 : U32), 8)
  +mh = U32.div((hh + 7 : U32), 8)
  +mm = M2.mcun(ww, hh)
  +mn = U32.to_nat(mm)
  +pn = Nat.mul(U32.to_nat(mw), U32.to_nat(mh))
  +em = {em0 : {mn == pn : Nat}}
  +e3 = {e30 : {U32.to_nat((mm * 3 : U32)) == Nat.mul(pn, 3n) : Nat}}
  +hp = {M1.lt_rw_r(0n, pn, mn, Equal.sym(Nat, mn, pn, em), pos_mul(U32.to_nat(mw), U32.to_nat(mh), pw, ph)) :
    {Nat.is_lt(0n, mn) == True{} : Bool}}
  +h1 = {Equal.trans(Bool, Nat.is_le(1n, mn), Nat.is_lt(0n, mn), True{}, Equal.sym(Bool, Nat.is_lt(0n, mn),
    Nat.is_le(1n,
    mn), M1.lt_le_succ(0n, mn)), hp) : {Nat.is_le(1n, mn) == True{} : Bool}}
  +nb = {Equal.cong(U32, U32, uu => (uu * 3 : U32), (U32.div(((ww + 8 : U32) - 1 : U32),
    8) * U32.div(((hh + 8 : U32) - 1 :
    U32), 8) : U32), mm, Equal.trans(U32, (U32.div(((ww + 8 : U32) - 1 : U32),
      8) * U32.div(((hh + 8 : U32) - 1 : U32), 8)
    : U32), (mw * U32.div(((hh + 8 : U32) - 1 : U32), 8) : U32), mm, Equal.cong(U32, U32, uu => (U32.div(uu, 8) *
    U32.div(((hh + 8 : U32) - 1 : U32), 8) : U32), ((ww + 8 : U32) - 1 : U32), (ww + 7 : U32), cw), Equal.cong(U32, U32,
    uu => (mw * U32.div(uu, 8) : U32), ((hh + 8 : U32) - 1 : U32), (hh + 7 : U32), ch))) :
    {Jpeg.decode.nblocks(ww, hh, [1, 1, 1], [1, 1, 1], 1, 1) == (mm * 3 : U32) : U32}}
  (Equal.trans(Nat, U32.to_nat(Jpeg.decode.nblocks(ww, hh, [1, 1, 1], [1, 1, 1], 1, 1)), U32.to_nat((mm * 3 : U32)),
    M2.tri(mn), Equal.cong(U32, Nat, uu => U32.to_nat(uu), Jpeg.decode.nblocks(ww, hh, [1, 1, 1], [1, 1, 1], 1, 1),
        (mm *
    3 : U32), nb), Equal.trans(Nat, U32.to_nat((mm * 3 : U32)), Nat.mul(pn, 3n), M2.tri(mn), e3, Equal.trans(Nat,
    Nat.mul(pn, 3n), Nat.mul(mn, 3n), M2.tri(mn), Equal.cong(Nat, Nat, xx => Nat.mul(xx, 3n), pn, mn, Equal.sym(Nat, mn,
    pn, em)), Equal.sym(Nat, M2.tri(mn), Nat.mul(mn, 3n), tri_mul(mn))))), hp, Equal.trans(Nat, 1n+U32.to_nat((mm - 1 :
    U32)), Nat.add(1n, Nat.sub(mn, 1n)), mn, Equal.cong(Nat, Nat, xx => 1n+xx, U32.to_nat((mm - 1 : U32)), Nat.sub(mn,
      1n),
    M6.ras.u32_sub_nat(mm, 1, h1)), M6.add_sub(1n, mn, h1)))

# the counts, each side's MCU count named
def count_mw(
  +ww: U32,
  +hh: U32,
  +hwl: {U32.is_le(ww, 65535) == True{} : Bool},
  +hhl: {U32.is_le(hh, 65535) == True{} : Bool},
  ow: MwOut(ww),
  oh: MwOut(hh)
) -> CountOut(ww, hh):
  (e7w, fw, pw) = ow
  (e7h, fh, ph) = oh
  count_fin(ww, hh, ceil_eq(ww, hwl, e7w), ceil_eq(hh, hhl, e7h), pw, ph, u32_triple(U32.div((ww + 7 : U32), 8),
    U32.div((hh + 7 : U32), 8), 3, fw, fh, (wof(2n, 3n), {==})))

# the counts, for sides of 1 to 65535
def count_ok(
  +ww: U32,
  +hh: U32,
  +hw0: {U32.is_eq(ww, 0) == False{} : Bool},
  +hh0: {U32.is_eq(hh, 0) == False{} : Bool},
  +hwl: {U32.is_le(ww, 65535) == True{} : Bool},
  +hhl: {U32.is_le(hh, 65535) == True{} : Bool}
) -> CountOut(ww, hh):
  count_mw(ww, hh, hwl, hhl, mw_ok(ww, hw0, hwl), mw_ok(hh, hh0, hhl))

# a number above 0 is not 0
def ne0(nn: Nat, hh: {Nat.is_lt(0n, nn) == True{} : Bool}) -> {Nat.is_eq(nn, 0n) == False{} : Bool}:
  match nn:
    case 0n:
      Empty.absurd({Nat.is_eq(0n, 0n) == False{} : Bool}, M1.huf.false_true(hh))
    case 1n+_p:
      {==}

# above 0 as a U32 is not 0
def gt0_ne(+ww: U32, hh: {U32.is_gt(ww, 0) == True{} : Bool}) -> {U32.is_eq(ww, 0) == False{} : Bool}:
  +wn = U32.to_nat(ww)
  Equal.trans(Bool, U32.is_eq(ww, 0), Nat.is_eq(wn, 0n), False{}, M1.u32_eq(ww, 0), ne0(wn, M3.gt0(wn, M3.ugt0(ww,
      True{},
    hh))))

# a decode that returned a picture gives a raster
def psome_some(
  mm: Maybe<&2, Jpeg.Pic>,
  hh: {Laws.jpg.psome(mm) == True{} : Bool}
) -> {Maybe.is_some(&2, Img.Raster, Img.decode_jpeg.out(mm)) == True{} : Bool}:
  match mm:
    case Some{pc}:
      match pc:
        case Jpeg.Pic{_w, _h, _p}:
          {==}
    case None{}:
      Empty.absurd({Maybe.is_some(&2, Img.Raster, Img.decode_jpeg.out(None{})) == True{} : Bool}, M1.huf.false_true(hh))

# three per MCU, at least one MCU, is not no blocks
def tri_pos(nn: Nat, hp: {Nat.is_lt(0n, nn) == True{} : Bool}, ee: {0n == M2.tri(nn) : Nat}) -> Empty:
  match nn:
    case 0n:
      M1.huf.false_true(hp)
    case 1n+pp:
      M3.zero_ne(1n+(1n+M2.tri(pp)), ee)

# the type of some_ts's parameter ea
def some_ts.ea.ty(+_ts: List<&2, Laws.JBlkTok>, +_ww: U32, +_hh: U32, +_px: List<&2, U32>) -> Type:
  {Jenc.encode.arm(_ww, _hh, _px) == Jenc.encode.pad(Laws.jpg.feed(M2.tbits(_ts), Jenc.encode.put0())) : List<&2, U32>}

# the entropy-coded bytes' blocks, at least one, decode to a picture
def some_ts(
  ts: List<&2, Laws.JBlkTok>,
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  +hw0: {U32.is_eq(ww, 0) == False{} : Bool},
  +hh0: {U32.is_eq(hh, 0) == False{} : Bool},
  +mn: Nat,
  ea: some_ts.ea.ty(ts, ww, hh, px),
  el: {List.length(&2, Laws.JBlkTok, ts) == M2.tri(mn) : Nat},
  ew: {Laws.jpg.allwf(ts) == True{} : Bool},
  en: {U32.to_nat(Jpeg.decode.nblocks(ww, hh, [1, 1, 1], [1, 1, 1], 1, 1)) == M2.tri(mn) : Nat},
  hp: {Nat.is_lt(0n, mn) == True{} : Bool}
) -> {Laws.jpg.psome(Jpeg.decode.run(Laws.jpg.enc.frame(ww, hh), Laws.jpg.enc.scan(), Laws.jpg.enc.tabs(),
  Jenc.encode.arm(ww, hh, px), 0)) == True{} : Bool}:
  match ts:
    case Nil{}:
      Empty.absurd({Laws.jpg.psome(Jpeg.decode.run(Laws.jpg.enc.frame(ww, hh), Laws.jpg.enc.scan(), Laws.jpg.enc.tabs(),
        Jenc.encode.arm(ww, hh, px), 0)) == True{} : Bool}, tri_pos(mn, hp, el))
    case +tt <> +rest:
      +fr = Laws.jpg.enc.frame(ww, hh)
      +sc = Laws.jpg.enc.scan()
      +tb = Laws.jpg.enc.tabs()
      +p0 = Jenc.encode.put0()
      eb = Equal.trans(List<&2, U32>, Jenc.encode.arm(ww, hh, px),
        Jenc.encode.pad(Laws.jpg.feed(M2.tbits(tt <> rest), p0)),
        Jenc.encode.pad(Laws.jpg.feed(Laws.jpg.tbits(tt <> rest), p0)), ea, Equal.cong(List<&2, Bool>, List<&2, U32>,
          bs =>
        Jenc.encode.pad(Laws.jpg.feed(bs, p0)), M2.tbits(tt <> rest), Laws.jpg.tbits(tt <> rest), Equal.sym(List<&2,
        Bool>, Laws.jpg.tbits(tt <> rest), M2.tbits(tt <> rest), tbits.eq(tt <> rest))))
      es = Equal.sym(List<&2, U32>, Jenc.encode.arm(ww, hh, px),
        Jenc.encode.pad(Laws.jpg.feed(Laws.jpg.tbits(tt <> rest),
        p0)), eb)
      %es : {Laws.jpg.psome(Jpeg.decode.run(fr, sc, tb, _, 0)) == True{} : Bool}
      scan_some(tt, rest, ww, hh, hw0, hh0, ew, Equal.trans(Nat, U32.to_nat(Jpeg.decode.nblocks(ww, hh, [1, 1, 1],
        [1, 1,
        1], 1, 1)), M2.tri(mn), 1n+List.length(&2, Laws.JBlkTok, rest), en, Equal.sym(Nat, 1n+List.length(&2,
            Laws.JBlkTok,
        rest), M2.tri(mn), el)))

# the entropy-coded bytes' blocks named
def some_path(
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  +hw0: {U32.is_eq(ww, 0) == False{} : Bool},
  +hh0: {U32.is_eq(hh, 0) == False{} : Bool},
  en: {U32.to_nat(Jpeg.decode.nblocks(ww, hh, [1, 1, 1], [1, 1, 1], 1, 1)) == M2.tri(U32.to_nat(M2.mcun(ww, hh))) : Nat},  # noqa: S002
  hp: {Nat.is_lt(0n, U32.to_nat(M2.mcun(ww, hh))) == True{} : Bool},
  po: M2.PathOut(Jenc.encode.arm(ww, hh, px), U32.to_nat(M2.mcun(ww, hh)))
) -> {Laws.jpg.psome(Jpeg.decode.run(Laws.jpg.enc.frame(ww, hh), Laws.jpg.enc.scan(), Laws.jpg.enc.tabs(),
  Jenc.encode.arm(ww, hh, px), 0)) == True{} : Bool}:
  (ts, ea, el, ew) = po
  some_ts(ts, ww, hh, px, hw0, hh0, U32.to_nat(M2.mcun(ww, hh)), ea, el, ew, en, hp)

# the block counts named
def some_cnt(
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  +hw0: {U32.is_eq(ww, 0) == False{} : Bool},
  +hh0: {U32.is_eq(hh, 0) == False{} : Bool},
  co: CountOut(ww, hh)
) -> {Laws.jpg.psome(Jpeg.decode.run(Laws.jpg.enc.frame(ww, hh), Laws.jpg.enc.scan(), Laws.jpg.enc.tabs(),
  Jenc.encode.arm(ww, hh, px), 0)) == True{} : Bool}:
  (en, hp, hn) = co
  some_path(ww, hh, px, hw0, hh0, en, hp, arm_ok(ww, hh, px, hn))

# the type of some_ok's parameter ers
def some_ok.ers.ty(+_ww: U32, +_hh: U32, +_px: List<&2, U32>) -> Type:
  {Laws.jpg.back(Img.encode_jpeg(Img.Raster{_ww, _hh,
    _px})) == Img.decode_jpeg.out(Jpeg.decode.run(Laws.jpg.enc.frame(_ww, _hh), Laws.jpg.enc.scan(),
    Laws.jpg.enc.tabs(), Jenc.encode.arm(_ww, _hh, Img.colours(_px)), 0)) : Maybe<&2, Img.Raster>}

# decode_jpeg of encode_jpeg's bytes, for a well-formed raster with both sides from 1 to 65535, is some raster
def some_ok(
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  +h_good: {Img.encode_jpeg.good(ww, hh, px) == True{} : Bool},
  ers: some_ok.ers.ty(ww, hh, px)
) -> {Maybe.is_some(&2, Img.Raster, Laws.jpg.back(Img.encode_jpeg(Img.Raster{ww, hh, px}))) == True{} : Bool}:
  +hw0 = {gt0_ne(ww, M8.w_pos(ww, hh, px, h_good)) : {U32.is_eq(ww, 0) == False{} : Bool}}
  +hh0 = {gt0_ne(hh, M8.h_pos(ww, hh, px, h_good)) : {U32.is_eq(hh, 0) == False{} : Bool}}
  +h_w = M8.w_le(ww, hh, px, h_good)
  +h_h = M8.h_le(ww, hh, px, h_good)
  +cp = Img.colours(px)
  es = Equal.sym(Maybe<&2, Img.Raster>, Laws.jpg.back(Img.encode_jpeg(Img.Raster{ww, hh, px})), Img.decode_jpeg.out(
    Jpeg.decode.run(Laws.jpg.enc.frame(ww, hh), Laws.jpg.enc.scan(), Laws.jpg.enc.tabs(), Jenc.encode.arm(ww, hh, cp),
      0)),
    ers)
  %es : {Maybe.is_some(&2, Img.Raster, _) == True{} : Bool}
  psome_some(Jpeg.decode.run(Laws.jpg.enc.frame(ww, hh), Laws.jpg.enc.scan(), Laws.jpg.enc.tabs(), Jenc.encode.arm(ww,
    hh, cp), 0), some_cnt(ww, hh, cp, hw0, hh0, count_ok(ww, hh, hw0, hh0, h_w, h_h)))

# the opacity of decode_jpeg's samples, for any bytes
def OpqFact() -> Type:
  @bytes: List<&2, U32> -> @img: Img.Raster -> @hd: {Img.decode_jpeg(bytes) == Some{img} : Maybe<&2, Img.Raster>} ->
    {D1.all.opaque(Img.pixels(img), True{}) == True{} : Bool}

# a decode's samples all have alpha 255, whatever it returned
def opq_dec(
  +bytes: List<&2, U32>,
  mr: Maybe<&2, Img.Raster>,
  ee: {Img.decode_jpeg(bytes) == mr : Maybe<&2, Img.Raster>},
  op: OpqFact()
) -> {Laws.jpg.opq(mr) == True{} : Bool}:
  match mr:
    case None{}:
      {==}
    case Some{img}:
      op(bytes, img, ee)

# the samples of the decode of encode_jpeg's bytes all have alpha 255, whatever encode_jpeg returned
def opq_back(eb: Maybe<&2, List<&2, U32>>, op: OpqFact()) -> {Laws.jpg.opq(Laws.jpg.back(eb)) == True{} : Bool}:
  match eb:
    case None{}:
      {==}
    case Some{+bytes}:
      opq_dec(bytes, Img.decode_jpeg(bytes), {==}, op)

# some raster of width w and height h, every sample of it with alpha 255, from the three facts
def round_ok(
  +mm: Maybe<&2, Img.Raster>,
  +ww: U32,
  +hh: U32,
  hs: {Maybe.is_some(&2, Img.Raster, mm) == True{} : Bool},
  hz: {Laws.jpg.sized(mm, ww, hh) == True{} : Bool},
  ho: {Laws.jpg.opq(mm) == True{} : Bool}
) -> {Laws.jpg.round(mm, ww, hh) == True{} : Bool}:
  M3.and_tt(Bool.and(Maybe.is_some(&2, Img.Raster, mm), Laws.jpg.sized(mm, ww, hh)), Laws.jpg.opq(mm),
    M3.and_tt(Maybe.is_some(&2, Img.Raster, mm), Laws.jpg.sized(mm, ww, hh), hs, hz), ho)

def Laws.jpeg_enc_stuffed(ww, hh, px):
  st.use(Jenc.encode.watch(U32.to_nat((ww * hh : U32)), px), ww, hh)

# the decoder's state after the encoder's header, with the sizes as it reads them back
def w10.hdr.st(+ww: U32, +hh: U32) -> Jpeg.St:
  Jpeg.St{Jpeg.Ent{}, Jpeg.Frame{ww, hh, 3, [1, 2, 3], [1, 1, 1], [1, 1, 1], [0, 0, 0], 1, 1}, Laws.jpg.enc.scan(),
    Laws.jpg.enc.tabs(), [], 0, 1, 0}

def Laws.jpeg_enc_header_walk(ww, hh):
  +wr = Jpeg.decode.u16(U32.shrn(ww, 8n), U32.and(ww, 255))
  +hr = Jpeg.decode.u16(U32.shrn(hh, 8n), U32.and(hh, 255))
  Equal.trans(Jpeg.St, Jpeg.decode.walk(Jenc.encode.header(ww, hh, Jenc.encode.dccounts(), Jenc.encode.dcsyms(),
    Jenc.encode.accounts(), Jenc.encode.acsyms()), Jpeg.decode.st0()), w10.hdr.st(wr, hr), w10.hdr.st(ww, hh), {==},
    Equal.trans(Jpeg.St, w10.hdr.st(wr, hr), w10.hdr.st(ww, hr), w10.hdr.st(ww, hh), Equal.cong(U32, Jpeg.St,
    xx => w10.hdr.st(xx, hr), wr, ww, u16.eq(ww)), Equal.cong(U32, Jpeg.St, xx => w10.hdr.st(ww, xx), hr, hh,
    u16.eq(hh))))

def Laws.jpeg_ent_walk(xs, h_stuffed, frame, scan, tabs, ent, ri, kind, bad):
  ent.go(xs, False{}, frame, scan, tabs, ent, ri, kind, bad, h_stuffed)

def Laws.jpeg_round_trip_scan(ww, hh, px, h_good):
  +cp = Img.colours(px)
  +ee = Jenc.encode.arm(ww, hh, cp)
  +hd = Jenc.encode.header(ww, hh, Jenc.encode.dccounts(), Jenc.encode.dcsyms(), Jenc.encode.accounts(),
    Jenc.encode.acsyms())
  +rr = List.append(&2, U32, ee, [255, 217])
  +fr = Laws.jpg.enc.frame(ww, hh)
  +sc = Laws.jpg.enc.scan()
  +tb = Laws.jpg.enc.tabs()
  +ent = {Jpeg.St{Jpeg.Ent{}, fr, sc, tb, [], 0, 1, 0} : Jpeg.St}
  +stop = {Jpeg.St{Jpeg.Stop{}, fr, sc, tb, List.reverse.go(&2, U32, ee, []), 0, 1, 0} : Jpeg.St}
  Equal.trans(Maybe<&2, Img.Raster>, Laws.jpg.back(Img.encode_jpeg(Img.Raster{ww, hh, px})),
    Laws.jpg.back(Img.encode_jpeg.pick(True{}, ww, hh, cp)), Img.decode_jpeg.out(Jpeg.decode.run(fr, sc, tb, ee, 0)),
    Equal.cong(Bool, Maybe<&2, Img.Raster>, bb => Laws.jpg.back(Img.encode_jpeg.pick(bb, ww, hh, cp)),
    Img.encode_jpeg.good(ww, hh, px), True{}, h_good),
    Equal.trans(Maybe<&2, Img.Raster>, Img.decode_jpeg(Jenc.encode.pick(Jenc.encode.bad(ww, hh), ww, hh, cp)),
    Img.decode_jpeg(Jenc.encode.pick(False{}, ww, hh, cp)), Img.decode_jpeg.out(Jpeg.decode.run(fr, sc, tb, ee, 0)),
    Equal.cong(Bool, Maybe<&2, Img.Raster>, bb => Img.decode_jpeg(Jenc.encode.pick(bb, ww, hh, cp)),
    Jenc.encode.bad(ww, hh), False{}, M8.bad(ww, hh, px, h_good)),
    Equal.trans(Maybe<&2, Img.Raster>, M3.w8.out(Jpeg.decode.walk(List.append(&2, U32, hd, rr), Jpeg.decode.st0())),
    M3.w8.out(Jpeg.decode.walk(rr, Jpeg.decode.walk(hd, Jpeg.decode.st0()))),
    Img.decode_jpeg.out(Jpeg.decode.run(fr, sc, tb, ee, 0)), Equal.cong(Jpeg.St, Maybe<&2, Img.Raster>,
    st => M3.w8.out(st), Jpeg.decode.walk(List.append(&2, U32, hd, rr), Jpeg.decode.st0()), Jpeg.decode.walk(rr,
    Jpeg.decode.walk(hd, Jpeg.decode.st0())), M3.walk_app(hd, rr, Jpeg.decode.st0())),
    Equal.trans(Maybe<&2, Img.Raster>, M3.w8.out(Jpeg.decode.walk(rr, Jpeg.decode.walk(hd, Jpeg.decode.st0()))),
    M3.w8.out(Jpeg.decode.walk(rr, ent)), Img.decode_jpeg.out(Jpeg.decode.run(fr, sc, tb, ee, 0)),
    Equal.cong(Jpeg.St, Maybe<&2, Img.Raster>, st => M3.w8.out(Jpeg.decode.walk(rr, st)), Jpeg.decode.walk(hd,
    Jpeg.decode.st0()), ent, Laws.jpeg_enc_header_walk(ww, hh)),
    Equal.trans(Maybe<&2, Img.Raster>, M3.w8.out(Jpeg.decode.walk(rr, ent)), M3.w8.out(stop),
    Img.decode_jpeg.out(Jpeg.decode.run(fr, sc, tb, ee, 0)), Equal.cong(Jpeg.St, Maybe<&2, Img.Raster>,
    st => M3.w8.out(st), Jpeg.decode.walk(rr, ent), stop, Laws.jpeg_ent_walk(ee, Laws.jpeg_enc_stuffed(ww, hh, cp), fr,
    sc, tb, [], 0, 1, 0)), Equal.cong(List<&2, U32>, Maybe<&2, Img.Raster>, xs => Img.decode_jpeg.out(
    Jpeg.decode.run(fr, sc, tb, xs, 0)), List.reverse(&2, U32, List.reverse.go(&2, U32, ee, [])), ee,
    M1.flt.rev_rev(ee)))))))

def Laws.jpeg_run_sized(ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan, tabs, ent, ri):
  run.sized(ww, hh, nf, ids, hs, vs, tq, hmax, vmax, scan, tabs, ent, ri)

def Laws.jpeg_round_trip_sized(ww, hh, px, h_good):
  +ee = Jenc.encode.arm(ww, hh, Img.colours(px))
  Equal.trans(Bool, Laws.jpg.sized(Laws.jpg.back(Img.encode_jpeg(Img.Raster{ww, hh, px})), ww, hh),
    Laws.jpg.sized(Img.decode_jpeg.out(Jpeg.decode.run(Laws.jpg.enc.frame(ww, hh), Laws.jpg.enc.scan(),
    Laws.jpg.enc.tabs(), ee, 0)), ww, hh), True{}, Equal.cong(Maybe<&2, Img.Raster>, Bool, mm => Laws.jpg.sized(mm, ww,
    hh), Laws.jpg.back(Img.encode_jpeg(Img.Raster{ww, hh, px})), Img.decode_jpeg.out(Jpeg.decode.run(
    Laws.jpg.enc.frame(ww, hh), Laws.jpg.enc.scan(), Laws.jpg.enc.tabs(), ee, 0)), Laws.jpeg_round_trip_scan(ww, hh,
    px, h_good)), Laws.jpeg_run_sized(ww, hh, 3, [1, 2, 3], [1, 1, 1], [1, 1, 1], [0, 0, 0], 1, 1,
    Laws.jpg.enc.scan(), Laws.jpg.enc.tabs(), ee, 0))

def Laws.jpeg_unstuff(bs, ok):
  +xs = Laws.jpg.bytes(bs)
  +nn = List.length(&2, Laws.JByte, bs)
  Equal.trans(List<&2, U32>, Laws.jpg.read8(nn, Jpeg.decode.read.n(8, Jpeg.Bits{0, ok, 0,
    Jenc.encode.stuff.all(List.reverse(&2, U32, xs), [])})), Laws.jpg.read8(nn, Jpeg.decode.read.n(8, Jpeg.Bits{0, ok,
    0, stf(xs, [])})), xs, Equal.cong(List<&2, U32>, List<&2, U32>, zs => Laws.jpg.read8(nn, Jpeg.decode.read.n(8,
    Jpeg.Bits{0, ok, 0, zs})), Jenc.encode.stuff.all(List.reverse(&2, U32, xs), []), stf(xs, []),
    stall.rev(xs, [], [])), rd.list(bs, ok, []))

def Laws.jpeg_bits_round_trip(cs, h_len):
  round_trip(cs, h_len)

def Laws.jpeg_huff_dc(pre, h_pre, sy, h_sy, post, h_post):
  huff_law.dc(pre, h_pre, sy, h_sy, post, h_post)

def Laws.jpeg_huff_ac(pre, h_pre, sy, h_sy, post, h_post):
  huff_law.ac(pre, h_pre, sy, h_sy, post, h_post)

def Laws.jpeg_scan_some(tt, rest, ww, hh, h_w, h_h, h_wf, h_n):
  scan_some(tt, rest, ww, hh, h_w, h_h, h_wf, h_n)

def Laws.jpeg_round_trip_some(ww, hh, px, h_good):
  some_ok(ww, hh, px, h_good, Laws.jpeg_round_trip_scan(ww, hh, px, h_good))

def Laws.jpeg_round_trip(ww, hh, px, h_good):
  round_ok(Laws.jpg.back(Img.encode_jpeg(Img.Raster{ww, hh, px})), ww, hh, Laws.jpeg_round_trip_some(ww, hh, px,
    h_good), Laws.jpeg_round_trip_sized(ww, hh, px, h_good), opq_back(Img.encode_jpeg(
    Img.Raster{ww, hh, px}), bb => ii => ee => L1.jpeg_decode_opaque(bb, ii, ee)))
