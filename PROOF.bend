# ezimg: the proofs. `bend PROOF.bend` is the gate: its first line must be
# exactly `All terms check.`
import Base
import ./LAWS.bend as Laws
import ./proof/u32.bend as U32L
import ./proof/wp2-inflate.bend as Wp2
import ./proof/wp3-filter.bend as Flt
import ./proof/wp1-crc.bend as Wp1
import ./main.bend as Img
import ./src/png.bend as Png
import ./src/jpeg.bend as Jpeg
import ./src/crc.bend as Crc
import ./proof/wp5-png-decode.bend as W5
import ./proof/wp7-jpeg-struct.bend as W7
import ./src/jpeg_enc.bend as Jenc

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

def Laws.jpeg_rgb_opaque(yy, cb, cr):
  alpha.first(Jpeg.rgb.bits(yy, cb, cr))

def Laws.jpeg_gray_opaque(yy):
  alpha.first(Jpeg.gray.bits(yy))

# encode_jpeg and encode_png branch on the same guard, so they are none together
def refuse.alike(
  ok: Bool,
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  +qx: List<&2, U32>
) -> {Maybe.is_none(&2, List<&2, U32>, Img.encode_jpeg.pick(ok, ww, hh, qx)) ==
  Maybe.is_none(&2, List<&2, U32>, Png.enc.open(ok, ww, hh, px)) : Bool}:
  match ok:
    case False{}:
      {==}
    case True{}:
      {==}

def Laws.jpeg_png_refuse_alike(img):
  match img:
    case Img.Raster{+ww, +hh, +px}:
      refuse.alike(Png.enc.good(ww, hh, px), ww, hh, px, Img.colours(px))

# the code's colours is the specification's alpha.drop
def colours.drop(+px: List<&2, U32>) -> {Img.colours(px) == Laws.alpha.drop(px) : List<&2, U32>}:
  match px:
    case Nil{}:
      {==}
    case +pp <> rest:
      Equal.cong(List<&2, U32>, List<&2, U32>, tl => {U32.and(16777215, pp) <> tl : List<&2, U32>}, Img.colours(rest),
        Laws.alpha.drop(rest), colours.drop(rest))

# clearing alpha keeps the count Png.enc.len takes
def len.drop(
  +px: List<&2, U32>,
  +nn: U32
) -> {Png.enc.len(Laws.alpha.drop(px), nn) == Png.enc.len(px, nn) : U32}:
  match px:
    case Nil{}:
      {==}
    case _pp <> rest:
      len.drop(rest, (nn + 1 : U32))

# so the guard answers the same for a list and its colours
def good.drop(
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>
) -> {Png.enc.good(ww, hh, Laws.alpha.drop(px)) == Png.enc.good(ww, hh, px) : Bool}:
  Equal.cong(U32, Bool, nn => Bool.and(Bool.and(U32.is_gt(ww, 0), U32.is_gt(hh, 0)), Bool.and(Png.enc.area(ww, hh),
    U32.is_eq(nn, (ww * hh : U32)))), Png.enc.len(Laws.alpha.drop(px), 0), Png.enc.len(px, 0), len.drop(px, 0))

def Laws.jpeg_alpha_blind(ww, hh, pa, pb, same):
  +gab = Equal.trans(Bool, Png.enc.good(ww, hh, pa), Png.enc.good(ww, hh, Laws.alpha.drop(pa)),
    Png.enc.good(ww, hh, pb),
    Equal.sym(Bool, Png.enc.good(ww, hh, Laws.alpha.drop(pa)), Png.enc.good(ww, hh, pa), good.drop(ww, hh, pa)),
    Equal.trans(Bool, Png.enc.good(ww, hh, Laws.alpha.drop(pa)), Png.enc.good(ww, hh, Laws.alpha.drop(pb)),
      Png.enc.good(ww, hh, pb),
      Equal.cong(List<&2, U32>, Bool, ll => Png.enc.good(ww, hh, ll), Laws.alpha.drop(pa), Laws.alpha.drop(pb), same),
      good.drop(ww, hh, pb)))
  +cab = Equal.trans(List<&2, U32>, Img.colours(pa), Laws.alpha.drop(pa), Img.colours(pb), colours.drop(pa),
    Equal.trans(List<&2, U32>, Laws.alpha.drop(pa), Laws.alpha.drop(pb), Img.colours(pb), same,
      Equal.sym(List<&2, U32>, Img.colours(pb), Laws.alpha.drop(pb), colours.drop(pb))))
  Equal.trans(Maybe<&2, List<&2, U32>>,
    Img.encode_jpeg.pick(Png.enc.good(ww, hh, pa), ww, hh, Img.colours(pa)),
    Img.encode_jpeg.pick(Png.enc.good(ww, hh, pb), ww, hh, Img.colours(pa)),
    Img.encode_jpeg.pick(Png.enc.good(ww, hh, pb), ww, hh, Img.colours(pb)),
    Equal.cong(Bool, Maybe<&2, List<&2, U32>>, bb => Img.encode_jpeg.pick(bb, ww, hh, Img.colours(pa)),
      Png.enc.good(ww, hh, pa), Png.enc.good(ww, hh, pb), gab),
    Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>,
      ll => Img.encode_jpeg.pick(Png.enc.good(ww, hh, pb), ww, hh, ll), Img.colours(pa), Img.colours(pb), cab))

def Laws.map_size(_ff, img):
  match img:
    case Img.Raster{_ww, _hh, _px}:
      {==}

# sample k of map.go is f of sample k
def map.go.at(
  ~ff: U32 -> U32,
  px: List<&2, U32>,
  kk: Nat
) -> {List.get(&2, U32, Img.map.go(~ff, px), kk) == Laws.opt.map(~ff, List.get(&2, U32, px, kk)) : Maybe<&2, U32>}:
  match px kk:
    case Nil{} _kk:
      {==}
    case _hd <> _tl 0n:
      {==}
    case _hd <> tl 1n+pp:
      map.go.at(~ff, tl, pp)

def Laws.map_at(ff, img, kk):
  match img:
    case Img.Raster{_ww, _hh, px}:
      map.go.at(~ff, px, kk)

def Laws.sig_opens(_rest):
  {==}

# dropping nothing is the list
def drop.zero(+xs: List<&2, U32>) -> {xs == List.drop(&2, U32, xs, 0n) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case _hd <> _tl:
      {==}

# two lists with equal heads and equal tails are equal
def cons.eq(
  +aa: U32,
  +bb: U32,
  +ta: List<&2, U32>,
  +tb: List<&2, U32>,
  eh: {aa == bb : U32},
  et: {ta == tb : List<&2, U32>}
) -> {aa <> ta == bb <> tb : List<&2, U32>}:
  Equal.trans(List<&2, U32>, aa <> ta, bb <> ta, bb <> tb,
    Equal.cong(U32, List<&2, U32>, xx => {xx <> ta : List<&2, U32>}, aa, bb, eh),
    Equal.cong(List<&2, U32>, List<&2, U32>, ll => {bb <> ll : List<&2, U32>}, ta, tb, et))

# what sig.match says of want and xs, when it answers true: the answer it
# started from was true, and xs is want followed by the rest
def prefix.only.ty(+want: List<&2, U32>, +xs: List<&2, U32>, +ok: Bool) -> Type:
  {ok == True{} : Bool} &
    {xs == List.append(&2, U32, want, List.drop(&2, U32, xs, List.length(&2, U32, want))) : List<&2, U32>}

# one byte further: what the rest proves gives the answer so far and this byte
def prefix.only.cons(
  +ok: Bool,
  +wh: U32,
  +wt: List<&2, U32>,
  +bh: U32,
  +bt: List<&2, U32>,
  pr: prefix.only.ty(wt, bt, Bool.and(ok, U32.is_eq(bh, wh)))
) -> prefix.only.ty(wh <> wt, bh <> bt, ok):
  (e_and, e_tail) = pr
  +e_and2 = {e_and : {Bool.and(ok, U32.is_eq(bh, wh)) == True{} : Bool}}
  (U32L.and_left(ok, U32.is_eq(bh, wh), e_and2),
    cons.eq(bh, wh, bt, List.append(&2, U32, wt, List.drop(&2, U32, bt, List.length(&2, U32, wt))),
      U32L.ueq(bh, wh, U32L.and_right(ok, U32.is_eq(bh, wh), e_and2)), e_tail))

# bytes that sig.match finds open with want are want followed by the rest
def prefix.only(
  +want: List<&2, U32>,
  +xs: List<&2, U32>,
  +ok: Bool,
  +h_match: {Img.sig.match(want, xs, ok) == True{} : Bool}
) -> prefix.only.ty(want, xs, ok):
  match want xs:
    case Nil{} _xs:
      (h_match, drop.zero(_xs))
    case +wh <> +wt Nil{}:
      Empty.absurd(prefix.only.ty(wh <> wt, Nil{}, ok), U32L.false_true(h_match))
    case +wh <> +wt +bh <> +bt:
      prefix.only.cons(ok, wh, wt, bh, bt, prefix.only(wt, bt, Bool.and(ok, U32.is_eq(bh, wh)), h_match))

# the second half of what prefix.only proves
def prefix.only.rest(
  +want: List<&2, U32>,
  +xs: List<&2, U32>,
  +ok: Bool,
  pr: prefix.only.ty(want, xs, ok)
) -> {xs == List.append(&2, U32, want, List.drop(&2, U32, xs, List.length(&2, U32, want))) : List<&2, U32>}:
  (_e_ok, e_xs) = pr
  e_xs

# split on what sig.match answers: false gives none, which h_some rules out
def sig.only.go(
  ok: Bool,
  +xs: List<&2, U32>,
  e_ok: {Img.sig.match(Img.png_sig(), xs, True{}) == ok : Bool},
  h_some: {Maybe.is_some(&2, List<&2, U32>, Img.sig.pick(ok)) == True{} : Bool}
) -> {xs == List.append(&2, U32, Img.png_sig(), List.drop(&2, U32, xs, 8n)) : List<&2, U32>}:
  match ok:
    case False{}:
      Empty.absurd({xs == List.append(&2, U32, Img.png_sig(), List.drop(&2, U32, xs, 8n)) : List<&2, U32>},
        U32L.false_true(h_some))
    case True{}:
      prefix.only.rest(Img.png_sig(), xs, True{}, prefix.only(Img.png_sig(), xs, True{}, e_ok))

def Laws.sig_only(xs, h_some):
  sig.only.go(Img.sig.match(Img.png_sig(), xs, True{}), xs, {==}, h_some)

# ---- wp7-jpeg-struct ----

# what jpeg_enc_layout says of an encoding mm of a raster of width ww and height hh
def lay.Ty(mm: Maybe<&2, List<&2, U32>>, ww: U32, hh: U32) -> Type:
  &app: List<&2, U32> -> &dq: List<&2, U32> -> &sof: List<&2, U32> -> &dc: List<&2, U32>
    -> &ac: List<&2, U32> -> &sos: List<&2, U32> -> &ent: List<&2, U32>
    -> {mm == Some{Laws.jfif.file(ww, hh, app, dq, sof, dc, ac, sos, ent)} : Maybe<&2, List<&2, U32>>}

# an accepted raster's encoding is the header, the entropy-coded bytes and EOI
def lay.pick(
  ok: Bool,
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  e_ok: {Png.enc.good(ww, hh, px) == ok : Bool},
  h_some: {Maybe.is_some(&2, List<&2, U32>, Img.encode_jpeg.pick(ok, ww, hh, Img.colours(px))) == True{} : Bool},
  h_w: {U32.is_le(ww, 65535) == True{} : Bool},
  h_h: {U32.is_le(hh, 65535) == True{} : Bool}
) -> lay.Ty(Img.encode_jpeg.pick(ok, ww, hh, Img.colours(px)), ww, hh):
  match ok:
    case False{}:
      Empty.absurd(lay.Ty(None{}, ww, hh), U32L.false_true(h_some))
    case True{}:
      +cp = Img.colours(px)
      ([1, 1, 0, 0, 1, 0, 1, 0, 0], (0 <> Jenc.encode.quant(), ([3, 1, 17, 0, 2, 17, 0, 3, 17, 0],
        (0 <> Jenc.encode.join(Jenc.encode.dccounts(), Jenc.encode.dcsyms()),
        (16 <> Jenc.encode.join(Jenc.encode.accounts(), Jenc.encode.acsyms()), ([3, 1, 0, 2, 0, 3, 0, 0, 63, 0],
        (Jenc.encode.arm(ww, hh, cp),
        Equal.cong(Bool, Maybe<&2, List<&2, U32>>, bb => Some{Jenc.encode.pick(bb, ww, hh, cp)},
          Jenc.encode.bad(ww, hh), False{}, W7.bad_of_good(ww, hh, px, e_ok, h_w, h_h)))))))))

def Laws.jpeg_enc_layout(img, h_some, h_w, h_h):
  match img:
    case Img.Raster{+ww, +hh, +px}:
      lay.pick(Png.enc.good(ww, hh, px), ww, hh, px, {==}, h_some, h_w, h_h)

# what jpeg_enc_ends says of an encoding mm
def ends.Ty(mm: Maybe<&2, List<&2, U32>>) -> Type:
  &mid: List<&2, U32>
    -> {mm == Some{List.append(&2, U32, [255, 216], List.append(&2, U32, mid, [255, 217]))} : Maybe<&2, List<&2, U32>>}

# the encoder's output opens with SOI and closes with EOI, whichever way its size test goes
def ends.bad(bad: Bool, +ww: U32, +hh: U32, +cp: List<&2, U32>) -> ends.Ty(Some{Jenc.encode.pick(bad, ww, hh, cp)}):
  match bad:
    case True{}:
      ([], {==})
    case False{}:
      (List.append(&2, U32, Jenc.encode.join(Jenc.encode.app0(), Jenc.encode.join(Jenc.encode.dqt(),
        Jenc.encode.join(Jenc.encode.sof(ww, hh), Jenc.encode.join(Jenc.encode.dht(0, Jenc.encode.dccounts(),
        Jenc.encode.dcsyms()), Jenc.encode.join(Jenc.encode.dht(16, Jenc.encode.accounts(), Jenc.encode.acsyms()),
        Jenc.encode.sos()))))), Jenc.encode.arm(ww, hh, cp)), {==})

# an accepted raster's encoding opens with SOI and closes with EOI
def ends.pick(
  ok: Bool,
  +ww: U32,
  +hh: U32,
  +cp: List<&2, U32>,
  h_some: {Maybe.is_some(&2, List<&2, U32>, Img.encode_jpeg.pick(ok, ww, hh, cp)) == True{} : Bool}
) -> ends.Ty(Img.encode_jpeg.pick(ok, ww, hh, cp)):
  match ok:
    case False{}:
      Empty.absurd(ends.Ty(None{}), U32L.false_true(h_some))
    case True{}:
      ends.bad(Jenc.encode.bad(ww, hh), ww, hh, cp)

def Laws.jpeg_enc_ends(img, h_some):
  match img:
    case Img.Raster{+ww, +hh, +px}:
      ends.pick(Png.enc.good(ww, hh, px), ww, hh, Img.colours(px), h_some)

def Laws.jpeg_gray_level(yy):
  match yy:
    case U32{w0}:
      match w0:
        case WCon{b0, WCon{b1, WCon{b2, WCon{b3, w4}}}}:
          match w4:
            case WCon{b4, WCon{b5, WCon{b6, WCon{b7, w8}}}}:
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
                                          (W7.or_byte(b0, b1, b2, b3, b4, b5, b6, b7),
                                            (W7.or_byte(b0, b1, b2, b3, b4, b5, b6, b7), {==}))

# the samples of a decoded picture, or none
def pic.px(mm: Maybe<&2, Jpeg.Pic>) -> List<&2, U32>:
  match mm:
    case None{}:
      []
    case Some{Jpeg.Pic{_ww, _hh, px}}:
      px

# what jpeg_decode_packed says of samples px
def pk.Ty(px: List<&2, U32>) -> Type:
  &gray: Bool -> &ys: List<&2, U32> -> &bs: List<&2, U32> -> &rs: List<&2, U32>
    -> {px == Laws.jpeg.pack(gray, ys, bs, rs) : List<&2, U32>}

# the code's gray packing is the law's
def grays.eq(+ys: List<&2, U32>) -> {Jpeg.decode.grays(ys) == Laws.jpeg.grays(ys) : List<&2, U32>}:
  match ys:
    case Nil{}:
      {==}
    case +yv <> rest:
      Equal.cong(List<&2, U32>, List<&2, U32>, tl => {Jpeg.gray(yv) <> tl : List<&2, U32>}, Jpeg.decode.grays(rest),
        Laws.jpeg.grays(rest), grays.eq(rest))

# the code's colour packing is the law's
def rgbs.eq(
  +ys: List<&2, U32>,
  +bs: List<&2, U32>,
  +rs: List<&2, U32>
) -> {Jpeg.decode.rgbs(ys, bs, rs) == Laws.jpeg.rgbs(ys, bs, rs) : List<&2, U32>}:
  match ys bs rs:
    case Nil{} _bs _rs:
      {==}
    case _yv <> _yt Nil{} _rs:
      {==}
    case _yv <> _yt _bv <> _bt Nil{}:
      {==}
    case +yv <> yt +bv <> bt +rv <> rt:
      Equal.cong(List<&2, U32>, List<&2, U32>, tl => {Jpeg.rgb(yv, bv, rv) <> tl : List<&2, U32>},
        Jpeg.decode.rgbs(yt, bt, rt), Laws.jpeg.rgbs(yt, bt, rt), rgbs.eq(yt, bt, rt))

# no picture has no samples
def none.pk() -> pk.Ty([]):
  (True{}, ([], ([], ([], {==}))))

# gray or colour, by the component count
def nf3.pk(
  three: Bool,
  +ww: U32,
  +hh: U32,
  yy: Array<U32>,
  cb: Array<U32>,
  cr: Array<U32>
) -> pk.Ty(pic.px(Jpeg.decode.done.nf3(three, ww, hh, yy, cb, cr))):
  match three:
    case True{}:
      +nn = U32.to_nat((ww * hh : U32))
      +ey = Jpeg.decode.emit(nn, (yy, 0), 0, [], False{})
      +eb = Jpeg.decode.emit(nn, (cb, 0), 0, [], False{})
      +er = Jpeg.decode.emit(nn, (cr, 0), 0, [], False{})
      (False{}, (ey, (eb, (er, rgbs.eq(ey, eb, er)))))
    case False{}:
      none.pk()

# one component is gray
def nf1.pk(
  one: Bool,
  +nf: U32,
  +ww: U32,
  +hh: U32,
  yy: Array<U32>,
  cb: Array<U32>,
  cr: Array<U32>
) -> pk.Ty(pic.px(Jpeg.decode.done.nf1(one, nf, ww, hh, yy, cb, cr))):
  match one:
    case True{}:
      +ey = Jpeg.decode.emit(U32.to_nat((ww * hh : U32)), (yy, 0), 0, [], False{})
      (True{}, (ey, ([], ([], grays.eq(ey)))))
    case False{}:
      nf3.pk(U32.is_eq(nf, 3), ww, hh, yy, cb, cr)

# a failed scan has no samples, and a finished one is packed by its component count
def dok.pk(
  bad: Bool,
  frame: Jpeg.Frame,
  yy: Array<U32>,
  cb: Array<U32>,
  cr: Array<U32>
) -> pk.Ty(pic.px(Jpeg.decode.done.ok(bad, frame, yy, cb, cr))):
  match bad:
    case True{}:
      none.pk()
    case False{}:
      match frame:
        case Jpeg.Frame{+ww, +hh, +nf, _ids, _hs, _vs, _tq, _hmax, _vmax}:
          nf1.pk(U32.is_eq(nf, 1), nf, ww, hh, yy, cb, cr)

# the blocks' walk ends in decode.done, whose samples are packed
def blocks.pk(
  left: Nat,
  blk: Jpeg.Blk,
  +ctrl: Jpeg.Ctrl,
  +preds: Jpeg.Preds,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ri: U32,
  yy: Array<U32>,
  cb: Array<U32>,
  cr: Array<U32>,
  +ok: U32
) -> pk.Ty(pic.px(Jpeg.decode.blocks(left, blk, ctrl, preds, frame, scan, tabs, ri, yy, cb, cr, ok))):
  match left:
    case 0n:
      match blk:
        case Jpeg.Blk{+samples, _bits, _pred, +bok}:
          dok.pk(U32.is_eq((ok * bok : U32), 0), frame,
            Jpeg.decode.paint.use(Jpeg.decode.geom(ctrl, frame, scan), U32.is_eq(Jpeg.decode.ctrl.comp(ctrl), 0),
              samples, yy),
            Jpeg.decode.paint.use(Jpeg.decode.geom(ctrl, frame, scan), U32.is_eq(Jpeg.decode.ctrl.comp(ctrl), 1),
              samples, cb),
            Jpeg.decode.paint.use(Jpeg.decode.geom(ctrl, frame, scan), U32.is_eq(Jpeg.decode.ctrl.comp(ctrl), 2),
              samples, cr))
    case 1n+pp:
      match blk:
        case Jpeg.Blk{+samples, +bits, +pred, +bok}:
          match ctrl:
            case Jpeg.Ctrl{+comp, _bi, _mx, _my, _mcu, _rst}:
              blocks.pk(pp, Jpeg.decode.block.next(bits, preds, pred, ctrl, frame, scan, tabs, ri),
                Jpeg.decode.adv.ctrl(Jpeg.decode.adv(ctrl, frame, scan, ri)),
                Jpeg.decode.preds.next(Jpeg.decode.adv.duef(Jpeg.decode.adv(ctrl, frame, scan, ri)), preds, comp, pred),
                frame, scan, tabs, ri,
                Jpeg.decode.paint.use(Jpeg.decode.geom(ctrl, frame, scan), U32.is_eq(comp, 0), samples, yy),
                Jpeg.decode.paint.use(Jpeg.decode.geom(ctrl, frame, scan), U32.is_eq(comp, 1), samples, cb),
                Jpeg.decode.paint.use(Jpeg.decode.geom(ctrl, frame, scan), U32.is_eq(comp, 2), samples, cr),
                (ok * bok : U32))

# the scan starts the blocks' walk, or has no blocks
def start.pk(
  nn: Nat,
  bits: Jpeg.Bits,
  +frame: Jpeg.Frame,
  +scan: Jpeg.Scan,
  +tabs: Jpeg.Tabs,
  +ri: U32,
  yy: Array<U32>,
  cb: Array<U32>,
  cr: Array<U32>
) -> pk.Ty(pic.px(Jpeg.decode.start(nn, bits, frame, scan, tabs, ri, yy, cb, cr))):
  match nn:
    case 0n:
      none.pk()
    case 1n+pp:
      blocks.pk(pp, Jpeg.decode.block.of(bits, 0, Jpeg.decode.pred.zero(), frame, scan, tabs),
        Jpeg.Ctrl{0, 0, 0, 0, 0, 0}, Jpeg.decode.pred.zero(), frame, scan, tabs, ri, yy, cb, cr, 1)

# an empty frame has no samples; any other starts the scan
def runn.pk(
  empty: Bool,
  +ww: U32,
  +hh: U32,
  frame: Jpeg.Frame,
  scan: Jpeg.Scan,
  tabs: Jpeg.Tabs,
  ent: List<&2, U32>,
  +ri: U32
) -> pk.Ty(pic.px(Jpeg.decode.run.n(empty, ww, hh, frame, scan, tabs, ent, ri))):
  match empty:
    case True{}:
      none.pk()
    case False{}:
      match frame:
        case Jpeg.Frame{_w, _h, _nf, _ids, +hs, +vs, _tq, +hmax, +vmax}:
          start.pk(U32.to_nat((Jpeg.decode.ceil(ww, (hmax * 8 : U32)) * Jpeg.decode.ceil(hh, (vmax * 8 : U32))
            * Jpeg.decode.blocks.sum(hs, vs, 0) : U32)), Jpeg.Bits{0, 1, 0, ent}, frame, scan, tabs, ri,
            Jpeg.decode.plane((ww * hh : U32)), Jpeg.decode.plane((ww * hh : U32)), Jpeg.decode.plane((ww * hh : U32)))

# a run's samples are packed
def run.pk(
  frame: Jpeg.Frame,
  scan: Jpeg.Scan,
  tabs: Jpeg.Tabs,
  ent: List<&2, U32>,
  +ri: U32
) -> pk.Ty(pic.px(Jpeg.decode.run(frame, scan, tabs, ent, ri))):
  match frame:
    case Jpeg.Frame{+ww, +hh, _nf, _ids, _hs, _vs, _tq, _hmax, _vmax}:
      runn.pk(Bool.or(U32.is_eq(ww, 0), U32.is_eq(hh, 0)), ww, hh, frame, scan, tabs, ent, ri)

# a walk that did not reach a baseline frame cleanly has no samples; one that did runs
def fok.pk(
  ok1: Bool,
  ok2: Bool,
  frame: Jpeg.Frame,
  scan: Jpeg.Scan,
  tabs: Jpeg.Tabs,
  ent: List<&2, U32>,
  +ri: U32
) -> pk.Ty(pic.px(Jpeg.decode.finish.ok(ok1, ok2, frame, scan, tabs, ent, ri))):
  match ok1 ok2:
    case False{} _ok2:
      none.pk()
    case True{} False{}:
      none.pk()
    case True{} True{}:
      run.pk(frame, scan, tabs, List.reverse(&2, U32, ent), ri)

# a walk that did not stop has no samples
def fph.pk(
  phase: Jpeg.Phase,
  frame: Jpeg.Frame,
  scan: Jpeg.Scan,
  tabs: Jpeg.Tabs,
  ent: List<&2, U32>,
  +ri: U32,
  +kind: U32,
  +bad: U32
) -> pk.Ty(pic.px(Jpeg.decode.finish.ph(phase, frame, scan, tabs, ent, ri, kind, bad))):
  match phase:
    case Jpeg.Stop{}:
      fok.pk(U32.is_eq(kind, 1), U32.is_eq(bad, 0), frame, scan, tabs, ent, ri)
    case Jpeg.Seek{}:
      none.pk()
    case Jpeg.Mark{}:
      none.pk()
    case Jpeg.LenHi{_mark}:
      none.pk()
    case Jpeg.LenLo{_mark, _hi}:
      none.pk()
    case Jpeg.Pay{_mark, _left, _acc}:
      none.pk()
    case Jpeg.Ent{}:
      none.pk()
    case Jpeg.EntFF{}:
      none.pk()

# whatever the walk's state, the picture decode finishes with is packed
def finish.pk(st: Jpeg.St) -> pk.Ty(pic.px(Jpeg.decode.finish(st))):
  match st:
    case Jpeg.St{+phase, +frame, +scan, +tabs, +ent, +ri, +kind, +bad}:
      fph.pk(phase, frame, scan, tabs, ent, ri, kind, bad)

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
      Empty.absurd({Img.pixels(img) == [] : List<&2, U32>}, W7.none_some(Img.Raster, img, h_dec))
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
  (gray, (ys, (bs, (rs, eb)))) = pr
  (gray, (ys, (bs, (rs, Equal.trans(List<&2, U32>, aa, bb, Laws.jpeg.pack(gray, ys, bs, rs), eab, eb)))))

def Laws.jpeg_decode_packed(bytes, img, h_dec):
  pk.move(Img.pixels(img), pic.px(Jpeg.decode(bytes)), out.px(Jpeg.decode(bytes), img, h_dec),
    finish.pk(Jpeg.decode.walk(bytes, Jpeg.decode.st0())))

# a sample with alpha 255 passes the alpha test
def op.one(+pp: U32, ea: {U32.shrn(pp, 24n) == 255 : U32}) -> {U32.is_eq(U32.shrn(pp, 24n), 255) == True{} : Bool}:
  Equal.cong(U32, Bool, xx => U32.is_eq(xx, 255), U32.shrn(pp, 24n), 255, ea)

# one opaque sample in front leaves the answer as it was
def op.step(
  +pp: U32,
  +rest: List<&2, U32>,
  +ok: Bool,
  ea: {U32.shrn(pp, 24n) == 255 : U32},
  ih: {Laws.all.opaque(rest, ok) == ok : Bool}
) -> {Laws.all.opaque(pp <> rest, ok) == ok : Bool}:
  Equal.trans(Bool, Laws.all.opaque(rest, Bool.and(U32.is_eq(U32.shrn(pp, 24n), 255), ok)),
    Laws.all.opaque(rest, ok), ok,
    Equal.cong(Bool, Bool, bb => Laws.all.opaque(rest, Bool.and(bb, ok)), U32.is_eq(U32.shrn(pp, 24n), 255), True{},
      op.one(pp, ea)), ih)

# gray samples are all opaque
def op.grays(+ys: List<&2, U32>, +ok: Bool) -> {Laws.all.opaque(Laws.jpeg.grays(ys), ok) == ok : Bool}:
  match ys:
    case Nil{}:
      {==}
    case +yv <> +rest:
      op.step(Jpeg.gray(yv), Laws.jpeg.grays(rest), ok, Laws.jpeg_gray_opaque(yv), op.grays(rest, ok))

# colour samples are all opaque
def op.rgbs(
  +ys: List<&2, U32>,
  +bs: List<&2, U32>,
  +rs: List<&2, U32>,
  +ok: Bool
) -> {Laws.all.opaque(Laws.jpeg.rgbs(ys, bs, rs), ok) == ok : Bool}:
  match ys bs rs:
    case Nil{} _bs _rs:
      {==}
    case _yv <> _yt Nil{} _rs:
      {==}
    case _yv <> _yt _bv <> _bt Nil{}:
      {==}
    case +yv <> +yt +bv <> +bt +rv <> +rt:
      op.step(Jpeg.rgb(yv, bv, rv), Laws.jpeg.rgbs(yt, bt, rt), ok, Laws.jpeg_rgb_opaque(yv, bv, rv),
        op.rgbs(yt, bt, rt, ok))

# packed samples are all opaque
def op.pack(
  gray: Bool,
  +ys: List<&2, U32>,
  +bs: List<&2, U32>,
  +rs: List<&2, U32>
) -> {Laws.all.opaque(Laws.jpeg.pack(gray, ys, bs, rs), True{}) == True{} : Bool}:
  match gray:
    case True{}:
      op.grays(ys, True{})
    case False{}:
      op.rgbs(ys, bs, rs, True{})

# samples that are packed are all opaque
def op.of(+px: List<&2, U32>, pr: pk.Ty(px)) -> {Laws.all.opaque(px, True{}) == True{} : Bool}:
  (gray, (ys, (bs, (rs, ep)))) = pr
  Equal.trans(Bool, Laws.all.opaque(px, True{}), Laws.all.opaque(Laws.jpeg.pack(gray, ys, bs, rs), True{}), True{},
    Equal.cong(List<&2, U32>, Bool, ll => Laws.all.opaque(ll, True{}), px, Laws.jpeg.pack(gray, ys, bs, rs), ep),
    op.pack(gray, ys, bs, rs))

def Laws.jpeg_decode_opaque(bytes, img, h_dec):
  op.of(Img.pixels(img), Laws.jpeg_decode_packed(bytes, img, h_dec))

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
) -> {W7.inv(Jpeg.decode.dispatch(Laws.mk.byte(mk), body, frame, scan, tabs, ent, ri, kind, bad))
  == U32.is_eq(kind, 0) : Bool}:
  match mk:
    case Laws.MDht{}:
      W7.dht.inv(body, True{}, False{}, 0n, 0, 0, [], [], frame, scan, tabs, ent, ri, kind, bad)
    case Laws.MDqt{}:
      W7.dqt.inv(body, True{}, 0n, 0, [], frame, scan, tabs, ent, ri, kind, bad)
    case Laws.MSos{}:
      W7.sos.inv(body, frame, tabs, ent, ri, kind, bad)
    case Laws.MDri{}:
      W7.dri.inv(body, frame, scan, tabs, ent, kind, bad)
    case Laws.MCom{}:
      {==}
    case Laws.MApp0{}:
      W7.app0.inv(body, frame, scan, tabs, ent, ri, kind, bad)
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
  {W7.inv(Jpeg.decode.walk(Laws.seg.bytes(Laws.Seg{mk, hi, lo, body}), Jpeg.St{ph, frame, scan, tabs, ent, ri, kind,
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
  h_inv: {W7.inv(Jpeg.St{ph, frame, scan, tabs, ent, ri, kind, bad}) == True{} : Bool}
) -> seg.Goal(ph, mk, hi, lo, body, frame, scan, tabs, ent, ri, kind, bad):
  match ph:
    case Jpeg.Seek{}:
      (e_lt, e_len) = h_fit
      +tail = {hi <> (lo <> body) : List<&2, U32>}
      +mm = Laws.mk.byte(mk)
      +lenhi = {Jpeg.St{Jpeg.LenHi{mm}, frame, scan, tabs, ent, ri, kind, bad} : Jpeg.St}
      +disp = Jpeg.decode.dispatch(mm, body, frame, scan, tabs, ent, ri, kind, bad)
      Equal.trans(Bool, W7.inv(Jpeg.decode.walk(tail, Jpeg.decode.mark(mm, frame, scan, tabs, ent, ri, kind, bad))),
        W7.inv(disp), True{},
        Equal.cong(Jpeg.St, Bool, ss => W7.inv(ss),
          Jpeg.decode.walk(tail, Jpeg.decode.mark(mm, frame, scan, tabs, ent, ri, kind, bad)), disp,
          Equal.trans(Jpeg.St, Jpeg.decode.walk(tail, Jpeg.decode.mark(mm, frame, scan, tabs, ent, ri, kind, bad)),
            Jpeg.decode.walk(tail, lenhi), disp,
            Equal.cong(Jpeg.St, Jpeg.St, ss => Jpeg.decode.walk(tail, ss),
              Jpeg.decode.mark(mm, frame, scan, tabs, ent, ri, kind, bad), lenhi,
              mk.mark(mk, frame, scan, tabs, ent, ri, kind, bad)),
            W7.seg.read(U32.is_lt(Laws.seg.len(hi, lo), 2), Laws.seg.len(hi, lo), body, mm, frame, scan, tabs, ent, ri,
              kind, bad, e_lt, e_len))),
        Equal.trans(Bool, W7.inv(disp), U32.is_eq(kind, 0), True{}, mk.disp(mk, body, frame, scan, tabs, ent, ri, kind,
          bad), h_inv))
    case Jpeg.Stop{}:
      +tail = {hi <> (lo <> body) : List<&2, U32>}
      +stop = {Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad} : Jpeg.St}
      Equal.trans(Bool, W7.inv(Jpeg.decode.walk(255 <> (Laws.mk.byte(mk) <> tail), stop)), U32.is_eq(kind, 0), True{},
        Equal.cong(Jpeg.St, Bool, ss => W7.inv(ss), Jpeg.decode.walk(255 <> (Laws.mk.byte(mk) <> tail), stop), stop,
          W7.stop.walk(255 <> (Laws.mk.byte(mk) <> tail), frame, scan, tabs, ent, ri, kind, bad)), h_inv)
    case Jpeg.Ent{}:
      +tail = {hi <> (lo <> body) : List<&2, U32>}
      +mm = Laws.mk.byte(mk)
      +stop = {Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, 1} : Jpeg.St}
      +ff = {Jpeg.St{Jpeg.EntFF{}, frame, scan, tabs, ent, ri, kind, bad} : Jpeg.St}
      Equal.trans(Bool, W7.inv(Jpeg.decode.walk(tail, Jpeg.decode.step(mm, ff))), U32.is_eq(kind, 0), True{},
        Equal.cong(Jpeg.St, Bool, ss => W7.inv(ss), Jpeg.decode.walk(tail, Jpeg.decode.step(mm, ff)), stop,
          Equal.trans(Jpeg.St, Jpeg.decode.walk(tail, Jpeg.decode.step(mm, ff)), Jpeg.decode.walk(tail, stop), stop,
            Equal.cong(Jpeg.St, Jpeg.St, ss => Jpeg.decode.walk(tail, ss), Jpeg.decode.step(mm, ff), stop,
              mk.ent(mk, frame, scan, tabs, ent, ri, kind, bad)),
            W7.stop.walk(tail, frame, scan, tabs, ent, ri, kind, 1))), h_inv)
    case Jpeg.Mark{}:
      Empty.absurd(seg.Goal(Jpeg.Mark{}, mk, hi, lo, body, frame, scan, tabs, ent, ri, kind, bad),
        U32L.false_true(h_inv))
    case Jpeg.LenHi{mark}:
      Empty.absurd(seg.Goal(Jpeg.LenHi{mark}, mk, hi, lo, body, frame, scan, tabs, ent, ri, kind, bad),
        U32L.false_true(h_inv))
    case Jpeg.LenLo{mark, mhi}:
      Empty.absurd(seg.Goal(Jpeg.LenLo{mark, mhi}, mk, hi, lo, body, frame, scan, tabs, ent, ri, kind, bad),
        U32L.false_true(h_inv))
    case Jpeg.Pay{mark, left, acc}:
      Empty.absurd(seg.Goal(Jpeg.Pay{mark, left, acc}, mk, hi, lo, body, frame, scan, tabs, ent, ri, kind, bad),
        U32L.false_true(h_inv))
    case Jpeg.EntFF{}:
      Empty.absurd(seg.Goal(Jpeg.EntFF{}, mk, hi, lo, body, frame, scan, tabs, ent, ri, kind, bad),
        U32L.false_true(h_inv))

# a segment walked from a state between segments that read no frame header ends in one
def seg.inv(
  +mk: Laws.Mk,
  +hi: U32,
  +lo: U32,
  +body: List<&2, U32>,
  st: Jpeg.St,
  h_fit: Laws.seg.Fits(hi, lo, body),
  h_inv: {W7.inv(st) == True{} : Bool}
) -> {W7.inv(Jpeg.decode.walk(Laws.seg.bytes(Laws.Seg{mk, hi, lo, body}), st)) == True{} : Bool}:
  match st:
    case Jpeg.St{ph, +frame, +scan, +tabs, +ent, +ri, +kind, +bad}:
      seg.ph(ph, mk, hi, lo, body, frame, scan, tabs, ent, ri, kind, bad, h_fit, h_inv)

# segments walked from a state between segments that read no frame header end in one
def segs.inv(
  ss: List<&2, Laws.Seg>,
  +st: Jpeg.St,
  h_fit: Laws.segs.Fit(ss),
  h_inv: {W7.inv(st) == True{} : Bool}
) -> {W7.inv(Jpeg.decode.walk(Laws.segs.bytes(ss), st)) == True{} : Bool}:
  match ss:
    case Nil{}:
      h_inv
    case Laws.Seg{+mk, +hi, +lo, +body} <> +rest:
      (h_one, h_rest) = h_fit
      +sb = Laws.seg.bytes(Laws.Seg{mk, hi, lo, body})
      +rb = Laws.segs.bytes(rest)
      Equal.trans(Bool, W7.inv(Jpeg.decode.walk(List.append(&2, U32, sb, rb), st)),
        W7.inv(Jpeg.decode.walk(rb, Jpeg.decode.walk(sb, st))), True{},
        Equal.cong(Jpeg.St, Bool, xx => W7.inv(xx), Jpeg.decode.walk(List.append(&2, U32, sb, rb), st),
          Jpeg.decode.walk(rb, Jpeg.decode.walk(sb, st)), W7.walk.app(sb, rb, st)),
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
  h_inv: {W7.inv(Jpeg.St{ph, frame, scan, tabs, ent, ri, kind, bad}) == True{} : Bool}
) -> fin.Goal(255 <> (Laws.sofn.byte(sn) <> rest), Jpeg.St{ph, frame, scan, tabs, ent, ri, kind, bad}):
  match ph:
    case Jpeg.Seek{}:
      W7.fin.after(rest, Jpeg.decode.mark(Laws.sofn.byte(sn), frame, scan, tabs, ent, ri, kind, bad), frame, scan, tabs,
        ent, ri, 2, 1, sofn.mark(sn, frame, scan, tabs, ent, ri, kind, bad), W7.fin.bad(frame, scan, tabs, ent, ri, 2))
    case Jpeg.Ent{}:
      W7.fin.after(rest, Jpeg.decode.step.ph(Jpeg.EntFF{}, Laws.sofn.byte(sn), frame, scan, tabs, ent, ri, kind, bad),
        frame, scan, tabs, ent, ri, kind, 1, sofn.ent(sn, frame, scan, tabs, ent, ri, kind, bad),
        W7.fin.bad(frame, scan, tabs, ent, ri, kind))
    case Jpeg.Stop{}:
      W7.fin.after(255 <> (Laws.sofn.byte(sn) <> rest), Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad},
        frame, scan, tabs, ent, ri, kind, bad, {==}, W7.fin.none(frame, scan, tabs, ent, ri, kind, bad, h_inv))
    case Jpeg.Mark{}:
      Empty.absurd(fin.Goal(255 <> (Laws.sofn.byte(sn) <> rest), Jpeg.St{Jpeg.Mark{}, frame, scan, tabs, ent, ri,
        kind, bad}),
        U32L.false_true(h_inv))
    case Jpeg.LenHi{mark}:
      Empty.absurd(fin.Goal(255 <> (Laws.sofn.byte(sn) <> rest), Jpeg.St{Jpeg.LenHi{mark}, frame, scan, tabs, ent, ri,
        kind, bad}),
        U32L.false_true(h_inv))
    case Jpeg.LenLo{mark, mhi}:
      Empty.absurd(fin.Goal(255 <> (Laws.sofn.byte(sn) <> rest), Jpeg.St{Jpeg.LenLo{mark, mhi}, frame, scan, tabs, ent,
        ri, kind, bad}),
        U32L.false_true(h_inv))
    case Jpeg.Pay{mark, left, acc}:
      Empty.absurd(fin.Goal(255 <> (Laws.sofn.byte(sn) <> rest), Jpeg.St{Jpeg.Pay{mark, left, acc}, frame, scan, tabs,
        ent, ri, kind, bad}),
        U32L.false_true(h_inv))
    case Jpeg.EntFF{}:
      Empty.absurd(fin.Goal(255 <> (Laws.sofn.byte(sn) <> rest), Jpeg.St{Jpeg.EntFF{}, frame, scan, tabs, ent, ri,
        kind, bad}),
        U32L.false_true(h_inv))

# after the segments, a frame header other than SOF0 decodes to none, whatever the state's phase
def sofn.st(
  +sn: Laws.Sofn,
  +rest: List<&2, U32>,
  st: Jpeg.St,
  h_inv: {W7.inv(st) == True{} : Bool}
) -> fin.Goal(255 <> (Laws.sofn.byte(sn) <> rest), st):
  match st:
    case Jpeg.St{ph, +frame, +scan, +tabs, +ent, +ri, +kind, +bad}:
      sofn.ph(ph, sn, rest, frame, scan, tabs, ent, ri, kind, bad, h_inv)

# the walk of SOI and the segments decodes to none when a walk from where they leave it does
def lead.none(
  +ss: List<&2, Laws.Seg>,
  +tail: List<&2, U32>,
  h_fit: Laws.segs.Fit(ss),
  h_tail: @st: Jpeg.St -> {W7.inv(st) == True{} : Bool} -> fin.Goal(tail, st)
) -> {Img.decode_jpeg(Laws.jpeg.lead(ss, tail)) == None{} : Maybe<&2, Img.Raster>}:
  +s1 = {Jpeg.St{Jpeg.Seek{}, Jpeg.decode.frame0(), Jpeg.decode.scan0(), Jpeg.decode.tabs0(), [], 0, 0, 0} : Jpeg.St}
  +sb = Laws.segs.bytes(ss)
  +s2 = Jpeg.decode.walk(sb, s1)
  Equal.cong(Maybe<&2, Jpeg.Pic>, Maybe<&2, Img.Raster>, mm => Img.decode_jpeg.out(mm),
    Jpeg.decode.finish(Jpeg.decode.walk(List.append(&2, U32, sb, tail), s1)), None{},
    Equal.trans(Maybe<&2, Jpeg.Pic>, Jpeg.decode.finish(Jpeg.decode.walk(List.append(&2, U32, sb, tail), s1)),
      Jpeg.decode.finish(Jpeg.decode.walk(tail, s2)), None{},
      Equal.cong(Jpeg.St, Maybe<&2, Jpeg.Pic>, xx => Jpeg.decode.finish(xx),
        Jpeg.decode.walk(List.append(&2, U32, sb, tail), s1), Jpeg.decode.walk(tail, s2), W7.walk.app(sb, tail, s1)),
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
  h_inv: {W7.inv(Jpeg.St{ph, frame, scan, tabs, ent, ri, kind, bad}) == True{} : Bool}
) -> fin.Goal(prec.bytes(hi, lo, pp, body, rest), Jpeg.St{W7.ph.norm(ph), frame, scan, tabs, ent, ri, kind, bad}):
  match ph:
    case Jpeg.Seek{}:
      (e_lt, e_len) = h_len
      +sof = {255 <> (192 <> (hi <> (lo <> (pp <> body)))) : List<&2, U32>}
      +st = {Jpeg.St{Jpeg.Seek{}, frame, scan, tabs, ent, ri, kind, bad} : Jpeg.St}
      Equal.trans(Maybe<&2, Jpeg.Pic>, Jpeg.decode.finish(Jpeg.decode.walk(List.append(&2, U32, sof, rest), st)),
        Jpeg.decode.finish(Jpeg.decode.walk(rest, Jpeg.decode.walk(sof, st))), None{},
        Equal.cong(Jpeg.St, Maybe<&2, Jpeg.Pic>, xx => Jpeg.decode.finish(xx),
          Jpeg.decode.walk(List.append(&2, U32, sof, rest), st), Jpeg.decode.walk(rest, Jpeg.decode.walk(sof, st)),
          W7.walk.app(sof, rest, st)),
        W7.fin.after(rest, Jpeg.decode.walk(sof, st), Jpeg.decode.frame0(), scan, tabs, ent, ri, kind, 1,
          Equal.trans(Jpeg.St, Jpeg.decode.walk(sof, st),
            Jpeg.decode.read.sof.p(U32.is_eq(pp, 8), body, scan, tabs, ent, ri, kind, bad),
            Jpeg.St{Jpeg.Stop{}, Jpeg.decode.frame0(), scan, tabs, ent, ri, kind, 1},
            W7.seg.read(U32.is_lt(Laws.seg.len(hi, lo), 2), Laws.seg.len(hi, lo), pp <> body, 192, frame, scan, tabs,
              ent, ri, kind, bad, e_lt, e_len),
            Equal.cong(Bool, Jpeg.St, bb => Jpeg.decode.read.sof.p(bb, body, scan, tabs, ent, ri, kind, bad),
              U32.is_eq(pp, 8), False{}, h_pp)),
          W7.fin.bad(Jpeg.decode.frame0(), scan, tabs, ent, ri, kind)))
    case Jpeg.Ent{}:
      +sof = {255 <> (192 <> (hi <> (lo <> (pp <> body)))) : List<&2, U32>}
      +st = {Jpeg.St{Jpeg.Ent{}, frame, scan, tabs, ent, ri, kind, bad} : Jpeg.St}
      Equal.trans(Maybe<&2, Jpeg.Pic>, Jpeg.decode.finish(Jpeg.decode.walk(List.append(&2, U32, sof, rest), st)),
        Jpeg.decode.finish(Jpeg.decode.walk(rest, Jpeg.decode.walk(sof, st))), None{},
        Equal.cong(Jpeg.St, Maybe<&2, Jpeg.Pic>, xx => Jpeg.decode.finish(xx),
          Jpeg.decode.walk(List.append(&2, U32, sof, rest), st), Jpeg.decode.walk(rest, Jpeg.decode.walk(sof, st)),
          W7.walk.app(sof, rest, st)),
        W7.fin.after(rest, Jpeg.decode.walk(sof, st), frame, scan, tabs, ent, ri, kind, 1,
          W7.stop.walk(hi <> (lo <> (pp <> body)), frame, scan, tabs, ent, ri, kind, 1),
          W7.fin.bad(frame, scan, tabs, ent, ri, kind)))
    case Jpeg.Stop{}:
      W7.fin.after(prec.bytes(hi, lo, pp, body, rest), Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad},
        frame, scan, tabs, ent, ri, kind, bad, {==}, W7.fin.none(frame, scan, tabs, ent, ri, kind, bad, h_inv))
    case Jpeg.Mark{}:
      W7.fin.after(prec.bytes(hi, lo, pp, body, rest), Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad},
        frame, scan, tabs, ent, ri, kind, bad, {==}, W7.fin.none(frame, scan, tabs, ent, ri, kind, bad,
          Empty.absurd({U32.is_eq(kind, 0) == True{} : Bool}, U32L.false_true(h_inv))))
    case Jpeg.LenHi{_mark}:
      W7.fin.after(prec.bytes(hi, lo, pp, body, rest), Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad},
        frame, scan, tabs, ent, ri, kind, bad, {==}, W7.fin.none(frame, scan, tabs, ent, ri, kind, bad,
          Empty.absurd({U32.is_eq(kind, 0) == True{} : Bool}, U32L.false_true(h_inv))))
    case Jpeg.LenLo{_mark, _mhi}:
      W7.fin.after(prec.bytes(hi, lo, pp, body, rest), Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad},
        frame, scan, tabs, ent, ri, kind, bad, {==}, W7.fin.none(frame, scan, tabs, ent, ri, kind, bad,
          Empty.absurd({U32.is_eq(kind, 0) == True{} : Bool}, U32L.false_true(h_inv))))
    case Jpeg.Pay{_mark, _left, _acc}:
      W7.fin.after(prec.bytes(hi, lo, pp, body, rest), Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad},
        frame, scan, tabs, ent, ri, kind, bad, {==}, W7.fin.none(frame, scan, tabs, ent, ri, kind, bad,
          Empty.absurd({U32.is_eq(kind, 0) == True{} : Bool}, U32L.false_true(h_inv))))
    case Jpeg.EntFF{}:
      W7.fin.after(prec.bytes(hi, lo, pp, body, rest), Jpeg.St{Jpeg.Stop{}, frame, scan, tabs, ent, ri, kind, bad},
        frame, scan, tabs, ent, ri, kind, bad, {==}, W7.fin.none(frame, scan, tabs, ent, ri, kind, bad,
          Empty.absurd({U32.is_eq(kind, 0) == True{} : Bool}, U32L.false_true(h_inv))))

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
  h_inv: {W7.inv(st) == True{} : Bool}
) -> fin.Goal(prec.bytes(hi, lo, pp, body, rest), st):
  match st:
    case Jpeg.St{+ph, +frame, +scan, +tabs, +ent, +ri, +kind, +bad}:
      +xs = prec.bytes(hi, lo, pp, body, rest)
      +h_st = {h_inv : {W7.inv(Jpeg.St{ph, frame, scan, tabs, ent, ri, kind, bad}) == True{} : Bool}}
      Equal.trans(Maybe<&2, Jpeg.Pic>,
        Jpeg.decode.finish(Jpeg.decode.walk(xs, Jpeg.St{ph, frame, scan, tabs, ent, ri, kind, bad})),
        Jpeg.decode.finish(Jpeg.decode.walk(xs, Jpeg.St{W7.ph.norm(ph), frame, scan, tabs, ent, ri, kind, bad})),
        None{},
        Equal.cong(Jpeg.Phase, Maybe<&2, Jpeg.Pic>, qq => Jpeg.decode.finish(Jpeg.decode.walk(xs, Jpeg.St{qq, frame,
          scan, tabs, ent, ri, kind, bad})), ph, W7.ph.norm(ph), W7.ph.norm.eq(ph, U32L.and_left(W7.ph.ok(ph),
          U32.is_eq(kind, 0), h_st))),
        prec.ph(ph, hi, lo, pp, body, rest, frame, scan, tabs, ent, ri, kind, bad, h_len, h_pp, h_st))

def Laws.jpeg_refuse_precision(segs, h_fit, hi, lo, pp, body, h_len, h_pp, rest):
  lead.none(segs, prec.bytes(hi, lo, pp, body, rest), h_fit,
    st => hs => prec.st(hi, lo, pp, body, rest, st, h_len, h_pp, hs))

# ---- wp2-inflate ----

def Laws.inflate_stored(sz, xs, h_sz, h_by, h_n):
  Wp2.inflate_stored(sz, xs, h_sz, h_by, h_n)

def Laws.inflate_enc_zlib(xs, h_by, h_n):
  Wp2.inflate_stored(65535, xs, {==}, h_by, h_n)

# ---- wp3-filter ----

# rows_go from the law's hypotheses: the stride is not zero, and the fit is
# stated at the stride
def Laws.unfilter_filter(ft, ww, hh, bpp, rows, h_dims, h_wrap, h_rows, h_fit):
  +d_ww = U32L.and_left(U32.is_gt(ww, 0), Bool.and(U32.is_gt(hh, 0), Bool.and(U32.is_gt(bpp, 0), U32.is_le(bpp, 4))),
    h_dims)
  +d_rest = U32L.and_right(U32.is_gt(ww, 0), Bool.and(U32.is_gt(hh, 0), Bool.and(U32.is_gt(bpp, 0), U32.is_le(bpp, 4))),
    h_dims)
  +d_bpp = U32L.and_left(U32.is_gt(bpp, 0), U32.is_le(bpp, 4),
    U32L.and_right(U32.is_gt(hh, 0), Bool.and(U32.is_gt(bpp, 0), U32.is_le(bpp, 4)), d_rest))
  +en = Flt.stride_nz(ww, bpp, d_ww, d_bpp, h_wrap)
  +fit = Equal.trans(Bool, Laws.flt.fit(rows, U32.to_nat(U32.mul(ww, bpp)), True{}),
    Laws.flt.fit(rows, Nat.mul(U32.to_nat(ww), U32.to_nat(bpp)), True{}), True{},
    Equal.cong(Nat, Bool, nn => Laws.flt.fit(rows, nn, True{}), U32.to_nat(U32.mul(ww, bpp)),
      Nat.mul(U32.to_nat(ww), U32.to_nat(bpp)), h_wrap),
    h_fit)
  Flt.top.go(Png.uf.ok(ww, hh, bpp), h_dims, ft, ww, hh, bpp, rows,
    Flt.rows_go(rows, U32.to_nat(hh), h_rows, ft, bpp, U32.mul(ww, bpp), en, True{}, fit, [], []))

# ---- wp1-crc ----

def Laws.crc32_bitwise(xs):
  Wp1.crc32_ref(xs)

def Laws.png_crc_refused(pre, bad, rest, h_pre, h_bad, h_crc):
  Equal.cong(Maybe<&2, Png.Pic>, Maybe<&2, Img.Raster>, mm => Img.decode_png.pic(mm),
    Png.png.go(Laws.chunks.onto(pre, Laws.chunk.onto(bad, rest)), Png.ZLen{}, False{}, 0, 0, [], [], Png.pg.empty()),
    None{}, Wp1.walk_all(pre, bad, rest, Png.pg.empty(), h_pre, h_bad, h_crc))

# ---- wp5-png-decode ----

# byte 3, 2, 1 and 0 of a U32, as spec.be4 writes them
def by3(+nn: U32) -> U32:
  U32.and(255, U32.shrn(nn, 24n))

def by2(+nn: U32) -> U32:
  U32.and(255, U32.shrn(nn, 16n))

def by1(+nn: U32) -> U32:
  U32.and(255, U32.shrn(nn, 8n))

def by0(+nn: U32) -> U32:
  U32.and(255, nn)

# the width or height the decoder reads back from spec.be4's bytes
def be.back(+nn: U32) -> U32:
  Png.be.u32(by3(nn), by2(nn), by1(nn), by0(nn))

# the IHDR data as the walker holds it, last byte first
def ihdr.held(+ww: U32, +hh: U32, +dd: U32, +cc: U32, +comp: U32, +ff: U32, +ii: U32) -> List<&2, U32>:
  [ii, ff, comp, cc, dd, by0(hh), by1(hh), by2(hh), by3(hh), by0(ww), by1(ww), by2(ww), by3(ww)]

# the IHDR chunk judged, CRC right or wrong: png.good refuses the fields, so the chunk is refused
def ihdr.judged(
  zz: Bool,
  +ww: U32,
  +hh: U32,
  +dd: U32,
  +cc: U32,
  +comp: U32,
  +ff: U32,
  +ii: U32,
  empty: Bool,
  more: Maybe<&2, Png.Pic>,
  hg: {Png.png.good(be.back(ww), be.back(hh), dd, cc, comp, ff, ii) == False{} : Bool}
) -> {Img.decode_png.pic(Png.png.crc(Png.png.judge.at(zz, Png.tag.ihdr(), ihdr.held(ww, hh, dd, cc, comp, ff, ii),
  Png.pg.empty()), empty, more)) == None{} : Maybe<&2, Img.Raster>}:
  match zz:
    case False{}:
      {==}
    case True{}:
      Equal.cong(Bool, Maybe<&2, Img.Raster>,
        gg => Img.decode_png.pic(Png.png.crc(Png.png.ihdr.ok(gg, be.back(ww), be.back(hh), dd, cc, comp, ff, ii),
          empty, more)),
        Png.png.good(be.back(ww), be.back(hh), dd, cc, comp, ff, ii), False{}, hg)

# the walker at the CRC of that IHDR chunk, whatever the CRC bytes, the bytes after and the CRC register so far
def ihdr.at.crc(
  +c3: U32,
  +c2: U32,
  +c1: U32,
  +c0: U32,
  +rest: List<&2, U32>,
  +crc: List<&2, U32>,
  +ww: U32,
  +hh: U32,
  +dd: U32,
  +cc: U32,
  +comp: U32,
  +ff: U32,
  +ii: U32,
  hg: {Png.png.good(be.back(ww), be.back(hh), dd, cc, comp, ff, ii) == False{} : Bool}
) -> {Img.decode_png.pic(Png.png.go(c3 <> c2 <> c1 <> c0 <> rest, Png.ZCrc{}, False{}, 0, Png.tag.ihdr(), crc,
  ihdr.held(ww, hh, dd, cc, comp, ff, ii), Png.pg.empty())) == None{} : Maybe<&2, Img.Raster>}:
  ihdr.judged(U32.is_eq(Png.be.u32(c3, c2, c1, c0), Crc.crc32(List.reverse(&2, U32, crc))), ww, hh, dd, cc, comp, ff,
    ii, List.is_empty(&2, U32, rest),
    Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], Png.png.pgof(Png.png.judge(Png.be.u32(c3, c2, c1, c0), crc,
      Png.tag.ihdr(), ihdr.held(ww, hh, dd, cc, comp, ff, ii), Png.pg.empty()))),
    hg)

# a file whose IHDR png.good refuses decodes to none
def ihdr.refused(
  +ww: U32,
  +hh: U32,
  +dd: U32,
  +cc: U32,
  +comp: U32,
  +ff: U32,
  +ii: U32,
  +crc: U32,
  +rest: List<&2, U32>,
  hg: {Png.png.good(be.back(ww), be.back(hh), dd, cc, comp, ff, ii) == False{} : Bool}
) -> {Img.decode_png(Laws.spec.ihdr.file(ww, hh, dd, cc, comp, ff, ii, crc, rest)) == None{} : Maybe<&2, Img.Raster>}:
  ihdr.at.crc(by3(crc), by2(crc), by1(crc), by0(crc), rest,
    List.append(&2, U32, ihdr.held(ww, hh, dd, cc, comp, ff, ii), [82, 68, 72, 73]), ww, hh, dd, cc, comp, ff, ii, hg)

# png.good refuses a bit depth other than 8
def good.depth(
  +ww: U32,
  +hh: U32,
  +dd: U32,
  +cc: U32,
  +comp: U32,
  +ff: U32,
  +ii: U32,
  h_dd: {U32.is_eq(dd, 8) == False{} : Bool}
) -> {Png.png.good(ww, hh, dd, cc, comp, ff, ii) == False{} : Bool}:
  W5.shape_second(Bool.and(U32.is_gt(ww, 0), U32.is_gt(hh, 0)), U32.is_eq(dd, 8), Png.png.col(cc), U32.is_zero(comp),
    U32.is_zero(ff), U32.is_zero(ii), h_dd)

# png.good refuses an interlace method other than 0
def good.interlace(
  +ww: U32,
  +hh: U32,
  +dd: U32,
  +cc: U32,
  +comp: U32,
  +ff: U32,
  +ii: U32,
  h_ii: {U32.is_eq(ii, 0) == False{} : Bool}
) -> {Png.png.good(ww, hh, dd, cc, comp, ff, ii) == False{} : Bool}:
  W5.shape_sixth(Bool.and(U32.is_gt(ww, 0), U32.is_gt(hh, 0)), U32.is_eq(dd, 8), Png.png.col(cc), U32.is_zero(comp),
    U32.is_zero(ff), U32.is_zero(ii), h_ii)

# png.good refuses a colour type outside 0, 2, 3, 4 and 6
def good.colour(
  +ww: U32,
  +hh: U32,
  +dd: U32,
  +cc: U32,
  +comp: U32,
  +ff: U32,
  +ii: U32,
  h_cc: {Laws.spec.colour.ok(cc) == False{} : Bool}
) -> {Png.png.good(ww, hh, dd, cc, comp, ff, ii) == False{} : Bool}:
  W5.shape_third(Bool.and(U32.is_gt(ww, 0), U32.is_gt(hh, 0)), U32.is_eq(dd, 8), Png.png.col(cc), U32.is_zero(comp),
    U32.is_zero(ff), U32.is_zero(ii),
    W5.or_regroup(U32.is_eq(cc, 0), U32.is_eq(cc, 2), Bool.or(U32.is_eq(cc, 3), Bool.or(U32.is_eq(cc, 4),
      U32.is_eq(cc, 6))), h_cc))

def Laws.png_depth_refused(ww, hh, dd, cc, comp, ff, ii, crc, rest, h_dd):
  ihdr.refused(ww, hh, dd, cc, comp, ff, ii, crc, rest,
    good.depth(be.back(ww), be.back(hh), dd, cc, comp, ff, ii, h_dd))

def Laws.png_interlace_refused(ww, hh, dd, cc, comp, ff, ii, crc, rest, h_ii):
  ihdr.refused(ww, hh, dd, cc, comp, ff, ii, crc, rest,
    good.interlace(be.back(ww), be.back(hh), dd, cc, comp, ff, ii, h_ii))

def Laws.png_colour_refused(ww, hh, dd, cc, comp, ff, ii, crc, rest, h_cc):
  ihdr.refused(ww, hh, dd, cc, comp, ff, ii, crc, rest,
    good.colour(be.back(ww), be.back(hh), dd, cc, comp, ff, ii, h_cc))

# samples built onto an accumulator: the accumulator reversed, then the list, or none
def onto(acc: List<&2, U32>, mm: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match mm:
    case None{}:
      None{}
    case Some{ll}:
      Some{List.reverse.go(&2, U32, acc, ll)}

# one sample more on the accumulator is one sample more in front of the list
def onto.cons(
  +hd: U32,
  +acc: List<&2, U32>,
  mm: Maybe<&2, List<&2, U32>>
) -> {onto(hd <> acc, mm) == onto(acc, Laws.spec.cons(hd, mm)) : Maybe<&2, List<&2, U32>>}:
  match mm:
    case None{}:
      {==}
    case Some{_ll}:
      {==}

# onto an empty accumulator is the list itself
def onto.nil(mm: Maybe<&2, List<&2, U32>>) -> {onto([], mm) == mm : Maybe<&2, List<&2, U32>>}:
  match mm:
    case None{}:
      {==}
    case Some{_ll}:
      {==}

# px.grey without a key packs each byte as spec.grey does
def grey.acc(
  xs: List<&2, U32>,
  +acc: List<&2, U32>
) -> {Png.px.grey(xs, Png.KNone{}, acc) == Some{List.reverse.go(&2, U32, acc, Laws.spec.grey(xs))}
  : Maybe<&2, List<&2, U32>>}:
  match xs:
    case Nil{}:
      {==}
    case +gg <> tl:
      grey.acc(tl, Png.px.pack(255, gg, gg, gg) <> acc)

def Laws.png_px_grey(xs):
  grey.acc(xs, [])

# the code's key alpha is the specification's
def hit.alpha(zz: Bool) -> {Png.px.hit.at(zz) == Laws.spec.key.alpha(zz) : U32}:
  match zz:
    case True{}:
      {==}
    case False{}:
      {==}

# px.grey with a key packs each byte as spec.grey.key does
def grey.key.acc(
  xs: List<&2, U32>,
  +kk: U32,
  +acc: List<&2, U32>
) -> {Png.px.grey(xs, Png.KGrey{kk}, acc) == Some{List.reverse.go(&2, U32, acc, Laws.spec.grey.key(xs, kk))}
  : Maybe<&2, List<&2, U32>>}:
  match xs:
    case Nil{}:
      {==}
    case +gg <> +tl:
      Equal.trans(Maybe<&2, List<&2, U32>>,
        Png.px.grey(tl, Png.KGrey{kk}, Png.px.pack(Png.px.hit(gg, kk), gg, gg, gg) <> acc),
        Some{List.reverse.go(&2, U32, acc, Png.px.pack(Png.px.hit(gg, kk), gg, gg, gg) <> Laws.spec.grey.key(tl, kk))},
        Some{List.reverse.go(&2, U32, acc, Laws.spec.argb(Laws.spec.key.alpha(U32.is_eq(gg, kk)), gg, gg, gg) <>
          Laws.spec.grey.key(tl, kk))},
        grey.key.acc(tl, kk, Png.px.pack(Png.px.hit(gg, kk), gg, gg, gg) <> acc),
        Equal.cong(U32, Maybe<&2, List<&2, U32>>,
          aa => Some{List.reverse.go(&2, U32, acc, Laws.spec.argb(aa, gg, gg, gg) <> Laws.spec.grey.key(tl, kk))},
          Png.px.hit.at(U32.is_eq(gg, kk)), Laws.spec.key.alpha(U32.is_eq(gg, kk)), hit.alpha(U32.is_eq(gg, kk))))

def Laws.png_px_grey_key(xs, kk):
  grey.key.acc(xs, kk, [])

# px.ga packs each pair as spec.ga does
def ga.acc(
  xs: List<&2, U32>,
  +acc: List<&2, U32>
) -> {Png.px.ga(xs, acc) == onto(acc, Laws.spec.ga(xs)) : Maybe<&2, List<&2, U32>>}:
  match xs:
    case Nil{}:
      {==}
    case +gg <> t1:
      match t1:
        case Nil{}:
          {==}
        case +aa <> +tl:
          Equal.trans(Maybe<&2, List<&2, U32>>,
            Png.px.ga(tl, Png.px.pack(aa, gg, gg, gg) <> acc),
            onto(Png.px.pack(aa, gg, gg, gg) <> acc, Laws.spec.ga(tl)),
            onto(acc, Laws.spec.cons(Png.px.pack(aa, gg, gg, gg), Laws.spec.ga(tl))),
            ga.acc(tl, Png.px.pack(aa, gg, gg, gg) <> acc),
            onto.cons(Png.px.pack(aa, gg, gg, gg), acc, Laws.spec.ga(tl)))

def Laws.png_px_ga(xs):
  Equal.trans(Maybe<&2, List<&2, U32>>, Png.px.ga(xs, []), onto([], Laws.spec.ga(xs)), Laws.spec.ga(xs),
    ga.acc(xs, []), onto.nil(Laws.spec.ga(xs)))

# px.rgb without a key packs each triple as spec.rgb does
def rgb.acc(
  xs: List<&2, U32>,
  +acc: List<&2, U32>
) -> {Png.px.rgb(xs, Png.KNone{}, acc) == onto(acc, Laws.spec.rgb(xs)) : Maybe<&2, List<&2, U32>>}:
  match xs:
    case Nil{}:
      {==}
    case +rr <> t1:
      match t1:
        case Nil{}:
          {==}
        case +gg <> t2:
          match t2:
            case Nil{}:
              {==}
            case +bb <> +tl:
              Equal.trans(Maybe<&2, List<&2, U32>>,
                Png.px.rgb(tl, Png.KNone{}, Png.px.pack(255, rr, gg, bb) <> acc),
                onto(Png.px.pack(255, rr, gg, bb) <> acc, Laws.spec.rgb(tl)),
                onto(acc, Laws.spec.cons(Png.px.pack(255, rr, gg, bb), Laws.spec.rgb(tl))),
                rgb.acc(tl, Png.px.pack(255, rr, gg, bb) <> acc),
                onto.cons(Png.px.pack(255, rr, gg, bb), acc, Laws.spec.rgb(tl)))

def Laws.png_px_rgb(xs, _plte):
  Equal.trans(Maybe<&2, List<&2, U32>>, Png.px.rgb(xs, Png.KNone{}, []), onto([], Laws.spec.rgb(xs)),
    Laws.spec.rgb(xs), rgb.acc(xs, []), onto.nil(Laws.spec.rgb(xs)))

# the key alpha of one triple
def rgb.hit(+rr: U32, +gg: U32, +bb: U32, +kr: U32, +kg: U32, +kb: U32) -> Bool:
  Bool.and(U32.is_eq(rr, kr), Bool.and(U32.is_eq(gg, kg), U32.is_eq(bb, kb)))

# px.rgb with a key packs each triple as spec.rgb.key does
def rgb.key.acc(
  xs: List<&2, U32>,
  +kr: U32,
  +kg: U32,
  +kb: U32,
  +acc: List<&2, U32>
) -> {Png.px.rgb(xs, Png.KRgb{kr, kg, kb}, acc) == onto(acc, Laws.spec.rgb.key(xs, kr, kg, kb))
  : Maybe<&2, List<&2, U32>>}:
  match xs:
    case Nil{}:
      {==}
    case +rr <> t1:
      match t1:
        case Nil{}:
          {==}
        case +gg <> t2:
          match t2:
            case Nil{}:
              {==}
            case +bb <> +tl:
              Equal.trans(Maybe<&2, List<&2, U32>>,
                Png.px.rgb(tl, Png.KRgb{kr, kg, kb}, Png.px.pack(Png.px.rgb.hit(rr, gg, bb, kr, kg, kb), rr, gg, bb) <>
                  acc),
                onto(Png.px.pack(Png.px.rgb.hit(rr, gg, bb, kr, kg, kb), rr, gg, bb) <> acc,
                  Laws.spec.rgb.key(tl, kr, kg, kb)),
                onto(acc, Laws.spec.cons(Laws.spec.argb(Laws.spec.key.alpha(rgb.hit(rr, gg, bb, kr, kg, kb)), rr, gg,
                  bb), Laws.spec.rgb.key(tl, kr, kg, kb))),
                rgb.key.acc(tl, kr, kg, kb, Png.px.pack(Png.px.rgb.hit(rr, gg, bb, kr, kg, kb), rr, gg, bb) <> acc),
                Equal.trans(Maybe<&2, List<&2, U32>>,
                  onto(Png.px.pack(Png.px.rgb.hit(rr, gg, bb, kr, kg, kb), rr, gg, bb) <> acc,
                    Laws.spec.rgb.key(tl, kr, kg, kb)),
                  onto(Laws.spec.argb(Laws.spec.key.alpha(rgb.hit(rr, gg, bb, kr, kg, kb)), rr, gg, bb) <> acc,
                    Laws.spec.rgb.key(tl, kr, kg, kb)),
                  onto(acc, Laws.spec.cons(Laws.spec.argb(Laws.spec.key.alpha(rgb.hit(rr, gg, bb, kr, kg, kb)), rr,
                    gg, bb), Laws.spec.rgb.key(tl, kr, kg, kb))),
                  Equal.cong(U32, Maybe<&2, List<&2, U32>>,
                    aa => onto(Laws.spec.argb(aa, rr, gg, bb) <> acc, Laws.spec.rgb.key(tl, kr, kg, kb)),
                    Png.px.hit.at(rgb.hit(rr, gg, bb, kr, kg, kb)),
                    Laws.spec.key.alpha(rgb.hit(rr, gg, bb, kr, kg, kb)),
                    hit.alpha(rgb.hit(rr, gg, bb, kr, kg, kb))),
                  onto.cons(Laws.spec.argb(Laws.spec.key.alpha(rgb.hit(rr, gg, bb, kr, kg, kb)), rr, gg, bb), acc,
                    Laws.spec.rgb.key(tl, kr, kg, kb))))

def Laws.png_px_rgb_key(xs, _plte, kr, kg, kb):
  Equal.trans(Maybe<&2, List<&2, U32>>, Png.px.rgb(xs, Png.KRgb{kr, kg, kb}, []),
    onto([], Laws.spec.rgb.key(xs, kr, kg, kb)), Laws.spec.rgb.key(xs, kr, kg, kb), rgb.key.acc(xs, kr, kg, kb, []),
    onto.nil(Laws.spec.rgb.key(xs, kr, kg, kb)))

# px.rgba packs each quadruple as spec.rgba does
def rgba.acc(
  xs: List<&2, U32>,
  +acc: List<&2, U32>
) -> {Png.px.rgba(xs, acc) == onto(acc, Laws.spec.rgba(xs)) : Maybe<&2, List<&2, U32>>}:
  match xs:
    case Nil{}:
      {==}
    case +rr <> t1:
      match t1:
        case Nil{}:
          {==}
        case +gg <> t2:
          match t2:
            case Nil{}:
              {==}
            case +bb <> t3:
              match t3:
                case Nil{}:
                  {==}
                case +aa <> +tl:
                  Equal.trans(Maybe<&2, List<&2, U32>>,
                    Png.px.rgba(tl, Png.px.pack(aa, rr, gg, bb) <> acc),
                    onto(Png.px.pack(aa, rr, gg, bb) <> acc, Laws.spec.rgba(tl)),
                    onto(acc, Laws.spec.cons(Png.px.pack(aa, rr, gg, bb), Laws.spec.rgba(tl))),
                    rgba.acc(tl, Png.px.pack(aa, rr, gg, bb) <> acc),
                    onto.cons(Png.px.pack(aa, rr, gg, bb), acc, Laws.spec.rgba(tl)))

def Laws.png_px_rgba(xs, _plte):
  Equal.trans(Maybe<&2, List<&2, U32>>, Png.px.rgba(xs, []), onto([], Laws.spec.rgba(xs)), Laws.spec.rgba(xs),
    rgba.acc(xs, []), onto.nil(Laws.spec.rgba(xs)))

# PLTE holds whole entries
def triples(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case _rr <> _gg <> _bb <> tl:
      triples(tl)
    case _xs:
      False{}

# a list when the answer is true, none otherwise
def gate(zz: Bool, ll: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match zz:
    case False{}:
      None{}
    case True{}:
      Some{ll}

# pal.make builds spec.pal's entries, when PLTE holds whole entries
def pal.acc(
  xs: List<&2, U32>,
  +als: List<&2, U32>,
  +acc: List<&2, U32>
) -> {Png.pal.make(xs, als, acc) == gate(triples(xs), List.reverse.go(&2, U32, acc, Laws.spec.pal(xs, als)))
  : Maybe<&2, List<&2, U32>>}:
  match xs:
    case Nil{}:
      {==}
    case +rr <> t1:
      match t1:
        case Nil{}:
          {==}
        case +gg <> t2:
          match t2:
            case Nil{}:
              {==}
            case +bb <> tl:
              match als:
                case Nil{}:
                  pal.acc(tl, [], Png.px.pack(255, rr, gg, bb) <> acc)
                case +aa <> at:
                  pal.acc(tl, at, Png.px.pack(aa, rr, gg, bb) <> acc)

# px.at one entry further on, at the index less one
def at.prev(tl: List<&2, U32>, +ix: U32) -> Maybe<&2, U32>:
  Png.px.at(tl, U32.is_zero(U32.sub(ix, 1)), U32.sub(ix, 1))

# one step of px.at, once whether the index is zero is known
def at.step(
  +hd: U32,
  +tl: List<&2, U32>,
  +ix: U32,
  bz: Bool,
  ez: {U32.is_zero(ix) == bz : Bool},
  ih: {at.prev(tl, ix) == List.get(&2, U32, tl, U32.to_nat(U32.sub(ix, 1))) : Maybe<&2, U32>}
) -> {Png.px.at(hd <> tl, bz, ix) == List.get(&2, U32, hd <> tl, U32.to_nat(ix)) : Maybe<&2, U32>}:
  match bz:
    case True{}:
      e0 = Equal.sym(U32, ix, 0, U32L.ueq(ix, 0, ez))
      %e0 : {Some{hd} == List.get(&2, U32, hd <> tl, U32.to_nat(_)) : Maybe<&2, U32>}
      {==}
    case False{}:
      en = Equal.sym(Nat, U32.to_nat(ix), 1n+U32.to_nat(U32.sub(ix, 1)), W5.u32_dec(ix, ez))
      %en : {Png.px.at(tl, U32.is_zero(U32.sub(ix, 1)), U32.sub(ix, 1)) == List.get(&2, U32, hd <> tl, _)
        : Maybe<&2, U32>}
      ih

# px.at is the palette's entry at the index, as a Nat
def at.get(
  pal: List<&2, U32>,
  +ix: U32
) -> {Png.px.at(pal, U32.is_zero(ix), ix) == List.get(&2, U32, pal, U32.to_nat(ix)) : Maybe<&2, U32>}:
  match pal:
    case Nil{}:
      {==}
    case +hd <> +tl:
      at.step(hd, tl, ix, U32.is_zero(ix), {==}, at.get(tl, U32.sub(ix, 1)))

# what idx.acc says of the rest, with one entry more on the accumulator
def idx.ih(+tl: List<&2, U32>, +pal: List<&2, U32>, +acc: List<&2, U32>, +cc: U32) -> Type:
  {Png.px.idx(tl, pal, cc <> acc) == onto(cc <> acc, Laws.spec.idx(tl, pal)) : Maybe<&2, List<&2, U32>>}

# one index of px.idx, once its entry is known
def idx.step(
  mm: Maybe<&2, U32>,
  +tl: List<&2, U32>,
  +pal: List<&2, U32>,
  +acc: List<&2, U32>,
  ih: @cc: U32 -> idx.ih(tl, pal, acc, cc)
) -> {Png.px.use(mm, cc => Png.px.idx(tl, pal, {cc <> acc : List<&2, U32>})) ==
  onto(acc, Laws.spec.idx.at(mm, Laws.spec.idx(tl, pal))) : Maybe<&2, List<&2, U32>>}:
  match mm:
    case None{}:
      {==}
    case Some{+cc}:
      Equal.trans(Maybe<&2, List<&2, U32>>, Png.px.idx(tl, pal, cc <> acc), onto(cc <> acc, Laws.spec.idx(tl, pal)),
        onto(acc, Laws.spec.cons(cc, Laws.spec.idx(tl, pal))), ih(cc), onto.cons(cc, acc, Laws.spec.idx(tl, pal)))

# px.idx looks each index up as spec.idx does
def idx.acc(
  xs: List<&2, U32>,
  +pal: List<&2, U32>,
  +acc: List<&2, U32>
) -> {Png.px.idx(xs, pal, acc) == onto(acc, Laws.spec.idx(xs, pal)) : Maybe<&2, List<&2, U32>>}:
  match xs:
    case Nil{}:
      {==}
    case +ix <> +tl:
      Equal.trans(Maybe<&2, List<&2, U32>>,
        Png.px.use(Png.px.at(pal, U32.is_zero(ix), ix), cc => Png.px.idx(tl, pal, {cc <> acc : List<&2, U32>})),
        Png.px.use(List.get(&2, U32, pal, U32.to_nat(ix)), cc => Png.px.idx(tl, pal, {cc <> acc : List<&2, U32>})),
        onto(acc, Laws.spec.idx.at(List.get(&2, U32, pal, U32.to_nat(ix)), Laws.spec.idx(tl, pal))),
        Equal.cong(Maybe<&2, U32>, Maybe<&2, List<&2, U32>>,
          mm => Png.px.use(mm, cc => Png.px.idx(tl, pal, {cc <> acc : List<&2, U32>})),
          Png.px.at(pal, U32.is_zero(ix), ix), List.get(&2, U32, pal, U32.to_nat(ix)), at.get(pal, ix)),
        idx.step(List.get(&2, U32, pal, U32.to_nat(ix)), tl, pal, acc, cc => idx.acc(tl, pal, cc <> acc)))

# the palette passed the length check: the indices look up spec.idx
def indexed.le(
  zz: Bool,
  +xs: List<&2, U32>,
  +pal: List<&2, U32>,
  h_some: {Maybe.is_some(&2, List<&2, U32>, Png.px.indexed.at(Png.pal.gate(zz, pal), xs)) == True{} : Bool}
) -> {Png.px.indexed.at(Png.pal.gate(zz, pal), xs) == Laws.spec.idx(xs, pal) : Maybe<&2, List<&2, U32>>}:
  match zz:
    case False{}:
      Empty.absurd({None{} == Laws.spec.idx(xs, pal) : Maybe<&2, List<&2, U32>>}, U32L.false_true(h_some))
    case True{}:
      Equal.trans(Maybe<&2, List<&2, U32>>, Png.px.idx(xs, pal, []), onto([], Laws.spec.idx(xs, pal)),
        Laws.spec.idx(xs, pal), idx.acc(xs, pal, []), onto.nil(Laws.spec.idx(xs, pal)))

# the indexed samples of a palette that is some or none
def ixd(tr: Bool, xs: List<&2, U32>, trns: List<&2, U32>, pal: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  Png.px.indexed.at(Png.pal.ready(gate(tr, pal), trns), xs)

# PLTE held whole entries or not: none is ruled out, and the rest is indexed.le
def indexed.tr(
  tr: Bool,
  +xs: List<&2, U32>,
  +trns: List<&2, U32>,
  +pal: List<&2, U32>,
  h_some: {Maybe.is_some(&2, List<&2, U32>, ixd(tr, xs, trns, pal)) == True{} : Bool}
) -> {ixd(tr, xs, trns, pal) == Laws.spec.idx(xs, pal) : Maybe<&2, List<&2, U32>>}:
  match tr:
    case False{}:
      Empty.absurd({None{} == Laws.spec.idx(xs, pal) : Maybe<&2, List<&2, U32>>}, U32L.false_true(h_some))
    case True{}:
      indexed.le(Png.png.le(trns, pal), xs, pal, h_some)

def Laws.png_px_indexed(xs, plte, trns, h_some):
  +ep = {pal.acc(plte, trns, []) : {Png.pal.make(plte, trns, []) == gate(triples(plte), Laws.spec.pal(plte, trns))
    : Maybe<&2, List<&2, U32>>}}
  +hs = Equal.trans(Bool,
    Maybe.is_some(&2, List<&2, U32>, Png.px.indexed.at(Png.pal.ready(gate(triples(plte), Laws.spec.pal(plte, trns)),
      trns), xs)),
    Maybe.is_some(&2, List<&2, U32>, Png.px.indexed.at(Png.pal.ready(Png.pal.make(plte, trns, []), trns), xs)),
    True{},
    Equal.sym(Bool,
      Maybe.is_some(&2, List<&2, U32>, Png.px.indexed.at(Png.pal.ready(Png.pal.make(plte, trns, []), trns), xs)),
      Maybe.is_some(&2, List<&2, U32>, Png.px.indexed.at(Png.pal.ready(gate(triples(plte), Laws.spec.pal(plte,
        trns)), trns), xs)),
      Equal.cong(Maybe<&2, List<&2, U32>>, Bool,
        mm => Maybe.is_some(&2, List<&2, U32>, Png.px.indexed.at(Png.pal.ready(mm, trns), xs)),
        Png.pal.make(plte, trns, []), gate(triples(plte), Laws.spec.pal(plte, trns)), ep)),
    h_some)
  Equal.trans(Maybe<&2, List<&2, U32>>,
    Png.px.indexed.at(Png.pal.ready(Png.pal.make(plte, trns, []), trns), xs),
    Png.px.indexed.at(Png.pal.ready(gate(triples(plte), Laws.spec.pal(plte, trns)), trns), xs),
    Laws.spec.idx(xs, Laws.spec.pal(plte, trns)),
    Equal.cong(Maybe<&2, List<&2, U32>>, Maybe<&2, List<&2, U32>>,
      mm => Png.px.indexed.at(Png.pal.ready(mm, trns), xs),
      Png.pal.make(plte, trns, []), gate(triples(plte), Laws.spec.pal(plte, trns)), ep),
    indexed.tr(triples(plte), xs, trns, Laws.spec.pal(plte, trns), hs))

# png.pic is spec.pic
def pic.frame(
  mm: Maybe<&2, List<&2, U32>>,
  +ww: U32,
  +hh: U32
) -> {Png.png.pic(mm, ww, hh) == Laws.spec.pic(mm, ww, hh) : Maybe<&2, Png.Pic>}:
  match mm:
    case None{}:
      {==}
    case Some{_px}:
      {==}

# png.pack is px.of of the unfiltered bytes, whatever unfilter answered
def pack.frame(
  mm: Maybe<&2, List<&2, U32>>,
  +ww: U32,
  +hh: U32,
  +colour: U32,
  +plte: List<&2, U32>,
  +trns: List<&2, U32>
) -> {Png.png.pack(mm, ww, hh, colour, plte, trns) == Laws.spec.pic(Laws.spec.px.then(mm, colour, plte, trns), ww, hh)
  : Maybe<&2, Png.Pic>}:
  match mm:
    case None{}:
      {==}
    case Some{raw}:
      pic.frame(Png.px.of(colour, raw, plte, trns), ww, hh)

def Laws.png_samples_frame(raw, ww, hh, colour, plte, trns):
  pack.frame(Png.unfilter(raw, ww, hh, Png.png.bpp(colour)), ww, hh, colour, plte, trns)
