# proof/wp14-jpeg-encoder: lemmas for IMG-JPG-3's encoder side: every path of encode.arm (neutral, solid, encode.go)
# writes blocks the decoder reads whole, three per MCU, through the encoder's bit writer, and the MCU count times 3
# is decode.nblocks of the encoder's frame, with no U32 wrap, for sides from 1 to 65535. With the scan side
# (proof/wp12-jpeg-huffman) decode_jpeg(encode_jpeg(r)) is some raster. PROOF.bend imports this file as W14.
import Base
import ../LAWS.bend as Laws
import ../main.bend as Img
import ../src/jpeg.bend as Jpeg
import ../src/jpeg_enc.bend as Jenc
import ../src/png.bend as Png
import ./u32.bend as U32L
import ./wp6-raster.bend as R
import ./wp10-jpeg-finish.bend as W10
import ./wp12-jpeg-huffman.bend as W12

# the encoder's AC book, written out
def acbk() -> Array<U32>:
  W12.acbook.lit()

# the encoder's DC book, written out
def dcbk() -> Array<U32>:
  W12.dcbook.lit()

# a symbol's code from the AC book: the book back, the code's bits fed to the writer
def emitp.ac(
  +sy: U32,
  +pp: Jenc.Put
) -> {Jenc.encode.emit(Jenc.encode.sym(acbk(), sy), pp) == (acbk(), Laws.jpg.feed( W12.code.ac(sy),
  pp)) : Array<U32> & Jenc.Put}:
  +vv = Laws.jpg.val(Array.get(U32, acbk(), sy))
  Equal.trans(Array<U32> & Jenc.Put, Jenc.encode.emit(Jenc.encode.coded(Array.get(U32, acbk(), sy)), pp),
    Jenc.encode.emit(Jenc.encode.coded((acbk(), vv)), pp), (acbk(), Laws.jpg.feed(W12.code.ac(sy), pp)),
    Equal.cong(Array<U32> & U32, Array<U32> & Jenc.Put, gg => Jenc.encode.emit(Jenc.encode.coded(gg), pp),
    Array.get(U32, acbk(), sy), (acbk(), vv), W10.get.eq(acbk(), sy)), Equal.cong(Jenc.Put, Array<U32> & Jenc.Put,
    qq => (acbk(), qq), Jenc.encode.bits.go(U32.to_nat(U32.shrn(vv, 16n)), pp, U32.and(vv, 65535)),
    Laws.jpg.feed(W12.code.ac(sy), pp), W12.bits_go(U32.to_nat(U32.shrn(vv, 16n)), pp, U32.and(vv, 65535))))

# a symbol's code from the DC book: the book back, the code's bits fed to the writer
def emitp.dc(
  +sy: U32,
  +pp: Jenc.Put
) -> {Jenc.encode.emit(Jenc.encode.sym(dcbk(), sy), pp) == (dcbk(), Laws.jpg.feed( W12.code.dc(sy),
  pp)) : Array<U32> & Jenc.Put}:
  +vv = Laws.jpg.val(Array.get(U32, dcbk(), sy))
  Equal.trans(Array<U32> & Jenc.Put, Jenc.encode.emit(Jenc.encode.coded(Array.get(U32, dcbk(), sy)), pp),
    Jenc.encode.emit(Jenc.encode.coded((dcbk(), vv)), pp), (dcbk(), Laws.jpg.feed(W12.code.dc(sy), pp)),
    Equal.cong(Array<U32> & U32, Array<U32> & Jenc.Put, gg => Jenc.encode.emit(Jenc.encode.coded(gg), pp),
    Array.get(U32, dcbk(), sy), (dcbk(), vv), W10.get.eq(dcbk(), sy)), Equal.cong(Jenc.Put, Array<U32> & Jenc.Put,
    qq => (dcbk(), qq), Jenc.encode.bits.go(U32.to_nat(U32.shrn(vv, 16n)), pp, U32.and(vv, 65535)),
    Laws.jpg.feed(W12.code.dc(sy), pp), W12.bits_go(U32.to_nat(U32.shrn(vv, 16n)), pp, U32.and(vv, 65535))))

# the AC tokens' bits, joined
def acbits_app(
  xs: List<&2, Laws.JTok>,
  +ys: List<&2, Laws.JTok>
) -> {W12.acbits(List.append(&2, Laws.JTok, xs, ys)) == List.append(&2, Bool, W12.acbits(xs),
  W12.acbits(ys)) : List<&2, Bool>}:
  match xs:
    case Nil{}:
      {==}
    case Laws.JTok{+sym, +ex} <> +rest:
      Equal.trans(List<&2, Bool>, List.append(&2, Bool, W12.code.ac(sym), List.append(&2, Bool, ex,
        W12.acbits(List.append(&2, Laws.JTok, rest, ys)))), List.append(&2, Bool, W12.code.ac(sym), List.append(&2,
          Bool, ex,
        List.append(&2, Bool, W12.acbits(rest), W12.acbits(ys)))), List.append(&2, Bool, List.append(&2, Bool,
        W12.code.ac(sym), List.append(&2, Bool, ex, W12.acbits(rest))), W12.acbits(ys)), Equal.cong(List<&2, Bool>,
        List<&2, Bool>, zs => List.append(&2, Bool, W12.code.ac(sym), List.append(&2, Bool, ex, zs)),
        W12.acbits(List.append(&2, Laws.JTok, rest, ys)), List.append(&2, Bool, W12.acbits(rest), W12.acbits(ys)),
        acbits_app(rest, ys)), Equal.sym(List<&2, Bool>, List.append(&2, Bool, List.append(&2, Bool, W12.code.ac(sym),
        List.append(&2, Bool, ex, W12.acbits(rest))), W12.acbits(ys)), List.append(&2, Bool, W12.code.ac(sym),
        List.append(&2, Bool, ex, List.append(&2, Bool, W12.acbits(rest), W12.acbits(ys)))), Equal.trans(List<&2, Bool>,
        List.append(&2, Bool, List.append(&2, Bool, W12.code.ac(sym), List.append(&2, Bool, ex, W12.acbits(rest))),
        W12.acbits(ys)), List.append(&2, Bool, W12.code.ac(sym), List.append(&2, Bool, List.append(&2, Bool, ex,
        W12.acbits(rest)), W12.acbits(ys))), List.append(&2, Bool, W12.code.ac(sym), List.append(&2, Bool, ex,
        List.append(&2, Bool, W12.acbits(rest), W12.acbits(ys)))), W12.app_assoc(W12.code.ac(sym), List.append(&2, Bool,
        ex, W12.acbits(rest)), W12.acbits(ys)), Equal.cong(List<&2, Bool>, List<&2, Bool>, zs => List.append(&2, Bool,
        W12.code.ac(sym), zs), List.append(&2, Bool, List.append(&2, Bool, ex, W12.acbits(rest)), W12.acbits(ys)),
        List.append(&2, Bool, ex, List.append(&2, Bool, W12.acbits(rest), W12.acbits(ys))), W12.app_assoc(ex,
        W12.acbits(rest), W12.acbits(ys))))))

# j ZRL tokens
def zrltoks(jj: Nat) -> List<&2, Laws.JTok>:
  match jj:
    case 0n:
      []
    case 1n+kk:
      Laws.JTok{240, []} <> zrltoks(kk)

# the encoder's run of ZRL codes is the ZRL tokens' bits fed to the writer
def zrls_eq(
  jj: Nat,
  +pp: Jenc.Put
) -> {Jenc.encode.zrls(jj, (acbk(), pp)) == (acbk(), Laws.jpg.feed(W12.acbits(zrltoks(jj)),
  pp)) : Array<U32> & Jenc.Put}:
  match jj:
    case 0n:
      {==}
    case 1n+ +kk:
      +cz = W12.code.ac(240)
      Equal.trans(Array<U32> & Jenc.Put, Jenc.encode.zrls(kk, Jenc.encode.emit(Jenc.encode.sym(acbk(), 240), pp)),
        Jenc.encode.zrls(kk, (acbk(), Laws.jpg.feed(cz, pp))), (acbk(), Laws.jpg.feed(W12.acbits(zrltoks(1n+kk)), pp)),
        Equal.cong(Array<U32> & Jenc.Put, Array<U32> & Jenc.Put, st => Jenc.encode.zrls(kk, st),
        Jenc.encode.emit(Jenc.encode.sym(acbk(), 240), pp), (acbk(), Laws.jpg.feed(cz, pp)), emitp.ac(240, pp)),
        Equal.trans(Array<U32> & Jenc.Put, Jenc.encode.zrls(kk, (acbk(), Laws.jpg.feed(cz, pp))), (acbk(),
          Laws.jpg.feed(
        W12.acbits(zrltoks(kk)), Laws.jpg.feed(cz, pp))), (acbk(), Laws.jpg.feed(W12.acbits(zrltoks(1n+kk)), pp)),
          zrls_eq(kk,
        Laws.jpg.feed(cz, pp)), Equal.cong(Jenc.Put, Array<U32> & Jenc.Put, qq => (acbk(), qq),
          Laws.jpg.feed(W12.acbits(
        zrltoks(kk)), Laws.jpg.feed(cz, pp)), Laws.jpg.feed(W12.acbits(zrltoks(1n+kk)), pp), Equal.sym(Jenc.Put,
        Laws.jpg.feed(List.append(&2, Bool, cz, W12.acbits(zrltoks(kk))), pp), Laws.jpg.feed(W12.acbits(zrltoks(kk)),
          Laws.jpg.feed(cz,
        pp)), W12.feed_app(cz, W12.acbits(zrltoks(kk)), pp)))))

# the magnitude bits of a size and value: none for size 0
def mz(zero: Bool, +cat: U32, +vv: U32) -> List<&2, Bool>:
  match zero:
    case True{}:
      +_u = (cat + vv : U32)
      []
    case False{}:
      Laws.jpg.cb(U32.to_nat(cat), Jenc.encode.mag(cat, vv))

# the encoder's magnitude bits are mz's, fed to the writer
def magp_eq(
  zero: Bool,
  +pp: Jenc.Put,
  +cat: U32,
  +vv: U32
) -> {Jenc.encode.magp.z(zero, pp, cat, vv) == Laws.jpg.feed(mz(zero, cat, vv), pp) : Jenc.Put}:
  match zero:
    case True{}:
      {==}
    case False{}:
      W12.bits_go(U32.to_nat(cat), pp, Jenc.encode.mag(cat, vv))

# bits fed in three runs are their join fed at once
def feed3(
  +zz: List<&2, Bool>,
  +cc: List<&2, Bool>,
  +mm: List<&2, Bool>,
  +pp: Jenc.Put
) -> {Laws.jpg.feed(mm, Laws.jpg.feed(cc, Laws.jpg.feed(zz, pp))) == Laws.jpg.feed(List.append(&2, Bool, zz,
  List.append(&2, Bool, cc, List.append(&2, Bool, mm, []))), pp) : Jenc.Put}:
  Equal.sym(Jenc.Put, Laws.jpg.feed(List.append(&2, Bool, zz, List.append(&2, Bool, cc, List.append(&2, Bool, mm,
    []))), pp),
    Laws.jpg.feed(mm, Laws.jpg.feed(cc, Laws.jpg.feed(zz, pp))), Equal.trans(Jenc.Put, Laws.jpg.feed(List.append(&2,
      Bool, zz,
    List.append(&2, Bool, cc, List.append(&2, Bool, mm, []))), pp), Laws.jpg.feed(List.append(&2, Bool, cc,
      List.append(&2,
    Bool, mm, [])), Laws.jpg.feed(zz, pp)), Laws.jpg.feed(mm, Laws.jpg.feed(cc, Laws.jpg.feed(zz, pp))),
      W12.feed_app(zz, List.append(&2, Bool,
    cc, List.append(&2, Bool, mm, [])), pp), Equal.trans(Jenc.Put, Laws.jpg.feed(List.append(&2, Bool, cc,
      List.append(&2,
    Bool, mm, [])), Laws.jpg.feed(zz, pp)), Laws.jpg.feed(List.append(&2, Bool, mm, []), Laws.jpg.feed(cc,
      Laws.jpg.feed(zz, pp))),
    Laws.jpg.feed(mm, Laws.jpg.feed(cc, Laws.jpg.feed(zz, pp))), W12.feed_app(cc, List.append(&2, Bool, mm, []),
      Laws.jpg.feed(zz, pp)),
    Equal.cong(List<&2, Bool>, Jenc.Put, xs => Laws.jpg.feed(xs, Laws.jpg.feed(cc, Laws.jpg.feed(zz, pp))),
      List.append(&2, Bool, mm, []),
    mm, W12.app_nil(mm)))))

# the AC tokens one coefficient cc writes after a run of zeros: ZRL tokens for each 16 zeros, then its run and
# size symbol with its magnitude bits
def stoks(+zj: Nat, +sym: U32, +cat: U32, +clip: U32) -> List<&2, Laws.JTok>:
  List.append(&2, Laws.JTok, zrltoks(zj), [Laws.JTok{sym, mz(U32.is_eq(cat, 0), cat, clip)}])

# the encoder's step for a coefficient, once its clipped value, size and symbol are named
def hit_eq(
  +zj: Nat,
  +sym: U32,
  +cat: U32,
  +clip: U32,
  +pp: Jenc.Put
) -> {Jenc.encode.ac.hit(Jenc.encode.zrls(zj, (acbk(), pp)), sym, cat, clip) == (acbk(),
  Laws.jpg.feed(W12.acbits(stoks(zj, sym, cat, clip)), pp)) : Array<U32> & Jenc.Put}:
  +zt = zrltoks(zj)
  +zb = W12.acbits(zt)
  +cb = W12.code.ac(sym)
  +mb = mz(U32.is_eq(cat, 0), cat, clip)
  +tk = {Laws.JTok{sym, mb} : Laws.JTok}
  Equal.trans(Array<U32> & Jenc.Put, Jenc.encode.ac.hit(Jenc.encode.zrls(zj, (acbk(), pp)), sym, cat, clip),
    Jenc.encode.ac.hit((acbk(), Laws.jpg.feed(zb, pp)), sym, cat, clip), (acbk(), Laws.jpg.feed(W12.acbits(stoks(zj,
      sym, cat, clip)), pp)),
    Equal.cong(Array<U32> & Jenc.Put, Array<U32> & Jenc.Put, st => Jenc.encode.ac.hit(st, sym, cat, clip),
    Jenc.encode.zrls(zj, (acbk(), pp)), (acbk(), Laws.jpg.feed(zb, pp)), zrls_eq(zj, pp)),
      Equal.trans(Array<U32> & Jenc.Put,
    Jenc.encode.ac.mag(Jenc.encode.emit(Jenc.encode.sym(acbk(), sym), Laws.jpg.feed(zb, pp)), cat, clip),
    Jenc.encode.ac.mag((acbk(), Laws.jpg.feed(cb, Laws.jpg.feed(zb, pp))), cat, clip), (acbk(),
      Laws.jpg.feed(W12.acbits(stoks(zj, sym, cat, clip)), pp)), Equal.cong(Array<U32> & Jenc.Put,
      Array<U32> & Jenc.Put, st => Jenc.encode.ac.mag(st, cat, clip),
    Jenc.encode.emit(Jenc.encode.sym(acbk(), sym), Laws.jpg.feed(zb, pp)), (acbk(), Laws.jpg.feed(cb,
      Laws.jpg.feed(zb, pp))),
    emitp.ac(sym, Laws.jpg.feed(zb, pp))), Equal.cong(Jenc.Put, Array<U32> & Jenc.Put, qq => (acbk(), qq),
    Jenc.encode.magp.z(U32.is_eq(cat, 0), Laws.jpg.feed(cb, Laws.jpg.feed(zb, pp)), cat, clip),
      Laws.jpg.feed(W12.acbits(stoks(zj, sym, cat, clip)), pp), Equal.trans(Jenc.Put,
      Jenc.encode.magp.z(U32.is_eq(cat, 0), Laws.jpg.feed(cb, Laws.jpg.feed(zb, pp)), cat, clip),
    Laws.jpg.feed(mb, Laws.jpg.feed(cb, Laws.jpg.feed(zb, pp))), Laws.jpg.feed(W12.acbits(stoks(zj, sym, cat, clip)),
      pp), magp_eq(U32.is_eq(cat, 0),
    Laws.jpg.feed(cb, Laws.jpg.feed(zb, pp)), cat, clip), Equal.trans(Jenc.Put, Laws.jpg.feed(mb, Laws.jpg.feed(cb,
      Laws.jpg.feed(zb, pp))),
    Laws.jpg.feed(List.append(&2, Bool, zb, List.append(&2, Bool, cb, List.append(&2, Bool, mb, []))), pp),
    Laws.jpg.feed(W12.acbits(stoks(zj, sym, cat, clip)), pp), feed3(zb, cb, mb, pp), Equal.cong(List<&2, Bool>,
      Jenc.Put, xs =>
    Laws.jpg.feed(xs, pp), List.append(&2, Bool, zb, W12.acbits([tk])), W12.acbits(List.append(&2, Laws.JTok, zt,
      [tk])),
    Equal.sym(List<&2, Bool>, W12.acbits(List.append(&2, Laws.JTok, zt, [tk])), List.append(&2, Bool, zb,
    W12.acbits([tk])), acbits_app(zt, [tk]))))))))

# the encoder's step for a coefficient is its tokens' bits fed to the writer
def step_eq(
  +cc: U32,
  +run: U32,
  +pp: Jenc.Put
) -> {Jenc.encode.ac.step(cc, run, (acbk(), pp)) == (acbk(), Laws.jpg.feed(W12.acbits(stoks(U32.to_nat(U32.shrn(run,
  4n)), U32.or(Jenc.encode.cat(Jenc.encode.clip(cc, 1023)), U32.shln(U32.and(15, run), 4n)),
  Jenc.encode.cat(Jenc.encode.clip(cc, 1023)), Jenc.encode.clip(cc, 1023))), pp)) : Array<U32> & Jenc.Put}:
  hit_eq(U32.to_nat(U32.shrn(run, 4n)), U32.or(Jenc.encode.cat(Jenc.encode.clip(cc, 1023)), U32.shln(U32.and(15, run),
    4n)), Jenc.encode.cat(Jenc.encode.clip(cc, 1023)), Jenc.encode.clip(cc, 1023), pp)

# a word compare that sets the low bit against a clear one is never equal
def fin_ne(tt: Cmp) -> {Cmp.is_eq(Word.cmp.fin(True{}, False{}, tt)) == False{} : Bool}:
  match tt:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# a word compare over two clear low bits is the compare above them
def fin_ff(tt: Cmp) -> {Cmp.is_eq(Word.cmp.fin(False{}, False{}, tt)) == Cmp.is_eq(tt) : Bool}:
  match tt:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# one more than a word's complement is zero exactly when the word is zero
def neg_go(
  nn: Nat,
  ww: Word(nn)
) -> {Cmp.is_eq(Word.cmp(nn, Word.adc(nn, Word.not(nn, ww), Word.zero(nn), False{}, True{}),
  Word.zero(nn))) == Cmp.is_eq(Word.cmp(nn, ww, Word.zero(nn))) : Bool}:
  match nn:
    case 0n:
      match ww:
        case WNil{}:
          {==}
    case 1n+ +pp:
      match ww:
        case WCon{bb, +tt}:
          match bb:
            case True{}:
              Equal.trans(Bool, Cmp.is_eq(Word.cmp.fin(True{}, False{}, Word.cmp(pp, Word.adc(pp, Word.not(pp, tt),
                Word.zero(pp), False{}, False{}), Word.zero(pp)))), False{}, Cmp.is_eq(Word.cmp.fin(True{}, False{},
                Word.cmp(pp, tt, Word.zero(pp)))), fin_ne(Word.cmp(pp, Word.adc(pp, Word.not(pp, tt), Word.zero(pp),
                False{}, False{}), Word.zero(pp))), Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(True{}, False{}, Word.cmp(pp,
                tt, Word.zero(pp)))), False{}, fin_ne(Word.cmp(pp, tt, Word.zero(pp)))))
            case False{}:
              Equal.trans(Bool, Cmp.is_eq(Word.cmp.fin(False{}, False{}, Word.cmp(pp, Word.adc(pp, Word.not(pp, tt),
                Word.zero(pp), False{}, True{}), Word.zero(pp)))), Cmp.is_eq(Word.cmp(pp, Word.adc(pp, Word.not(pp,
                tt), Word.zero(pp), False{}, True{}), Word.zero(pp))), Cmp.is_eq(Word.cmp.fin(False{}, False{},
                Word.cmp(pp, tt, Word.zero(pp)))), fin_ff(Word.cmp(pp, Word.adc(pp, Word.not(pp, tt), Word.zero(pp),
                False{}, True{}), Word.zero(pp))), Equal.trans(Bool, Cmp.is_eq(Word.cmp(pp, Word.adc(pp, Word.not(pp,
                tt), Word.zero(pp), False{}, True{}), Word.zero(pp))), Cmp.is_eq(Word.cmp(pp, tt, Word.zero(pp))),
                Cmp.is_eq(Word.cmp.fin(False{}, False{}, Word.cmp(pp, tt, Word.zero(pp)))), neg_go(pp, tt),
                Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(False{}, False{}, Word.cmp(pp, tt, Word.zero(pp)))),
                Cmp.is_eq(Word.cmp(pp, tt, Word.zero(pp))), fin_ff(Word.cmp(pp, tt, Word.zero(pp))))))

# the two's complement of a U32 is zero exactly when it is
def neg_nz(vv: U32) -> {U32.is_eq(Jpeg.decode.neg32(vv), 0) == U32.is_eq(vv, 0) : Bool}:
  match vv:
    case U32{ww}:
      match ww:
        case WCon{bb, +tt}:
          match bb:
            case True{}:
              Equal.trans(Bool, Cmp.is_eq(Word.cmp.fin(True{}, False{}, Word.cmp(31n, Word.adc(31n, Word.not(31n, tt),
                Word.zero(31n), False{}, False{}), Word.zero(31n)))), False{}, Cmp.is_eq(Word.cmp.fin(True{}, False{},
                Word.cmp(31n, tt, Word.zero(31n)))), fin_ne(Word.cmp(31n, Word.adc(31n, Word.not(31n, tt),
                Word.zero(31n), False{}, False{}), Word.zero(31n))), Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(True{},
                False{}, Word.cmp(31n, tt, Word.zero(31n)))), False{}, fin_ne(Word.cmp(31n, tt, Word.zero(31n)))))
            case False{}:
              Equal.trans(Bool, Cmp.is_eq(Word.cmp.fin(False{}, False{}, Word.cmp(31n, Word.adc(31n, Word.not(31n,
                tt), Word.zero(31n), False{}, True{}), Word.zero(31n)))), Cmp.is_eq(Word.cmp(31n, Word.adc(31n,
                Word.not(31n, tt), Word.zero(31n), False{}, True{}), Word.zero(31n))), Cmp.is_eq(Word.cmp.fin(False{},
                False{}, Word.cmp(31n, tt, Word.zero(31n)))), fin_ff(Word.cmp(31n, Word.adc(31n, Word.not(31n, tt),
                Word.zero(31n), False{}, True{}), Word.zero(31n))), Equal.trans(Bool, Cmp.is_eq(Word.cmp(31n,
                Word.adc(31n, Word.not(31n, tt), Word.zero(31n), False{}, True{}), Word.zero(31n))),
                Cmp.is_eq(Word.cmp(31n, tt, Word.zero(31n))), Cmp.is_eq(Word.cmp.fin(False{}, False{}, Word.cmp(31n,
                tt, Word.zero(31n)))), neg_go(31n, tt), Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(False{}, False{},
                Word.cmp(31n, tt, Word.zero(31n)))), Cmp.is_eq(Word.cmp(31n, tt, Word.zero(31n))),
                fin_ff(Word.cmp(31n, tt, Word.zero(31n))))))

# True is never False
def true_false(ee: {True{} == False{} : Bool}) -> Empty:
  W12.false_true(Equal.sym(Bool, True{}, False{}, ee))

# the top bit of a word of nn + 1 bits
def wtop(nn: Nat, ww: Word(1n+nn)) -> Bool:
  match nn:
    case 0n:
      match ww:
        case WCon{bb, _t}:
          bb
    case 1n+pp:
      match ww:
        case WCon{_b, tt}:
          wtop(pp, tt)

# the word of a U32
def uw(vv: U32) -> Word(32n):
  match vv:
    case U32{ww}:
      ww

# the sign of a U32 is its top bit
def sign_top(vv: U32) -> {Jpeg.decode.sign(vv) == U32{WCon{wtop(31n, uw(vv)), Word.zero(31n)}} : U32}:
  match vv:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10,
      WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21,
      WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31,
      WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

# a sign read off its top bit that is not 0 is 1
def sign01.t(
  bb: Bool,
  hh: {U32.is_eq(U32{WCon{bb, Word.zero(31n)}}, 0) == False{} : Bool}
) -> {U32{WCon{bb, Word.zero(31n)}} == 1 : U32}:
  match bb:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({U32{WCon{False{}, Word.zero(31n)}} == 1 : U32}, true_false(hh))

# a U32's sign that is not 0 is 1, its top bit named
def sign01.w(
  +vv: U32,
  +bt: Bool,
  +es: {Jpeg.decode.sign(vv) == U32{WCon{bt, Word.zero(31n)}} : U32},
  hh: {U32.is_eq(Jpeg.decode.sign(vv), 0) == False{} : Bool}
) -> {Jpeg.decode.sign(vv) == 1 : U32}:
  Equal.trans(U32, Jpeg.decode.sign(vv), U32{WCon{bt, Word.zero(31n)}}, 1, es, sign01.t(bt, Equal.trans(Bool,
    U32.is_eq(U32{WCon{bt, Word.zero(31n)}}, 0), U32.is_eq(Jpeg.decode.sign(vv), 0), False{}, Equal.cong(U32, Bool,
    uu =>
    U32.is_eq(uu, 0), U32{WCon{bt, Word.zero(31n)}}, Jpeg.decode.sign(vv), Equal.sym(U32, Jpeg.decode.sign(vv),
    U32{WCon{bt, Word.zero(31n)}}, es)), hh)))

# a U32's sign that is not 0 is 1
def sign01(+vv: U32, hh: {U32.is_eq(Jpeg.decode.sign(vv), 0) == False{} : Bool}) -> {Jpeg.decode.sign(vv) == 1 : U32}:
  sign01.w(vv, wtop(31n, uw(vv)), sign_top(vv), hh)

# a U32 of sign 0 is its own magnitude
def abs_pos(+vv: U32, es: {Jpeg.decode.sign(vv) == 0 : U32}) -> {Jpeg.decode.abs(vv) == vv : U32}:
  ss = Equal.sym(U32, Jpeg.decode.sign(vv), 0, es)
  %ss : {Jpeg.decode.abs.s(_, vv) == vv : U32}
  {==}

# a U32 of sign 1 has its two's complement as its magnitude
def abs_neg(+vv: U32, es: {Jpeg.decode.sign(vv) == 1 : U32}) -> {Jpeg.decode.abs(vv) == Jpeg.decode.neg32(vv) : U32}:
  ss = Equal.sym(U32, Jpeg.decode.sign(vv), 1, es)
  %ss : {Jpeg.decode.abs.s(_, vv) == Jpeg.decode.neg32(vv) : U32}
  {==}

# U32 order is the order of the values
def u_cmp(aa: U32, bb: U32) -> {U32.cmp(aa, bb) == Nat.cmp(U32.to_nat(aa), U32.to_nat(bb)) : Cmp}:
  match aa bb:
    case U32{xw} U32{yw}:
      R.word_cmp_nat(32n, xw, yw)

# a value not above n is below n + 1
def ngt_lt(
  xx: Nat,
  nn: Nat,
  hh: {Cmp.is_gt(Nat.cmp(xx, nn)) == False{} : Bool}
) -> {Cmp.is_lt(Nat.cmp(xx, 1n+nn)) == True{} : Bool}:
  match xx nn:
    case 0n _:
      {==}
    case 1n+_p 0n:
      Empty.absurd({Cmp.is_lt(Nat.cmp(1n+_p, 1n)) == True{} : Bool}, true_false(hh))
    case 1n+pp 1n+qq:
      ngt_lt(pp, qq, hh)

# a value other than 0 is not below 1
def neq0_lt1(
  xx: Nat,
  hh: {Cmp.is_eq(Nat.cmp(xx, 0n)) == False{} : Bool}
) -> {Cmp.is_lt(Nat.cmp(xx, 1n)) == False{} : Bool}:
  match xx:
    case 0n:
      Empty.absurd({Cmp.is_lt(Nat.cmp(0n, 1n)) == False{} : Bool}, true_false(hh))
    case 1n+pp:
      Equal.sym(Bool, False{}, Nat.is_lt(pp, 0n), R.lt_zero_false(pp))

# a U32 not above n is below n + 1
def u_ngt_lt(
  +xx: U32,
  +nn: U32,
  +n1: U32,
  e1: {U32.to_nat(n1) == 1n+U32.to_nat(nn) : Nat},
  hh: {U32.is_gt(xx, nn) == False{} : Bool}
) -> {U32.is_lt(xx, n1) == True{} : Bool}:
  +ex = U32.to_nat(xx)
  +en = U32.to_nat(nn)
  e2 = Equal.sym(Nat, U32.to_nat(n1), 1n+en, e1)
  ec1 = Equal.sym(Cmp, U32.cmp(xx, n1), Nat.cmp(ex, U32.to_nat(n1)), u_cmp(xx, n1))
  %ec1 : {Cmp.is_lt(_) == True{} : Bool}
  %e2 : {Cmp.is_lt(Nat.cmp(ex, _)) == True{} : Bool}
  ngt_lt(ex, en, Equal.trans(Bool, Cmp.is_gt(Nat.cmp(ex, en)), Cmp.is_gt(U32.cmp(xx, nn)), False{}, Equal.cong(Cmp,
    Bool, cc => Cmp.is_gt(cc), Nat.cmp(ex, en), U32.cmp(xx, nn), Equal.sym(Cmp, U32.cmp(xx, nn), Nat.cmp(ex, en),
    u_cmp(xx, nn))), hh))

# a U32 other than 0 is not below 1
def u_nz(+xx: U32, hh: {U32.is_eq(xx, 0) == False{} : Bool}) -> {U32.is_lt(xx, 1) == False{} : Bool}:
  +ex = U32.to_nat(xx)
  Equal.trans(Bool, U32.is_lt(xx, 1), Cmp.is_lt(Nat.cmp(ex, 1n)), False{}, Equal.cong(Cmp, Bool, cc => Cmp.is_lt(cc),
    U32.cmp(xx, 1), Nat.cmp(ex, 1n), u_cmp(xx, 1)), neq0_lt1(ex, Equal.trans(Bool, Cmp.is_eq(Nat.cmp(ex, 0n)),
    U32.is_eq(xx, 0), False{}, Equal.cong(Cmp, Bool, cc => Cmp.is_eq(cc), Nat.cmp(ex, 0n), U32.cmp(xx, 0),
    Equal.sym(Cmp, U32.cmp(xx, 0), Nat.cmp(ex, 0n), u_cmp(xx, 0))), hh)))

# a clipped value, by whether it was above the limit: under the limit plus 1
def clipb.hi(
  gg: Bool,
  +vv: U32,
  +lim: U32,
  +l1: U32,
  +e1: {U32.to_nat(l1) == 1n+U32.to_nat(lim) : Nat},
  +es: {Jpeg.decode.sign(vv) == 0 : U32},
  +hg: {U32.is_gt(vv, lim) == gg : Bool},
  +ha: {U32.is_lt(Jpeg.decode.abs(lim), l1) == True{} : Bool}
) -> {U32.is_lt(Jpeg.decode.abs(Jenc.encode.clip.hi(gg, vv, lim)), l1) == True{} : Bool}:
  match gg:
    case True{}:
      ha
    case False{}:
      ev = Equal.sym(U32, Jpeg.decode.abs(vv), vv, abs_pos(vv, es))
      %ev : {U32.is_lt(_, l1) == True{} : Bool}
      u_ngt_lt(vv, lim, l1, e1, hg)

# a clipped negative value, by whether its magnitude was above the limit
def clipb.lo(
  gg: Bool,
  +vv: U32,
  +lim: U32,
  +l1: U32,
  +e1: {U32.to_nat(l1) == 1n+U32.to_nat(lim) : Nat},
  +hg: {U32.is_gt(Jpeg.decode.abs(vv), lim) == gg : Bool},
  +hb: {U32.is_lt(Jpeg.decode.abs(Jpeg.decode.neg32(lim)), l1) == True{} : Bool}
) -> {U32.is_lt(Jpeg.decode.abs(Jenc.encode.clip.lo(gg, vv, lim)), l1) == True{} : Bool}:
  match gg:
    case True{}:
      hb
    case False{}:
      u_ngt_lt(Jpeg.decode.abs(vv), lim, l1, e1, hg)

# a clipped value, by its sign
def clipb.s(
  ss: Bool,
  +vv: U32,
  +lim: U32,
  +l1: U32,
  +e1: {U32.to_nat(l1) == 1n+U32.to_nat(lim) : Nat},
  +hs: {U32.is_eq(Jpeg.decode.sign(vv), 0) == ss : Bool},
  +ha: {U32.is_lt(Jpeg.decode.abs(lim), l1) == True{} : Bool},
  +hb: {U32.is_lt(Jpeg.decode.abs(Jpeg.decode.neg32(lim)), l1) == True{} : Bool}
) -> {U32.is_lt(Jpeg.decode.abs(Jenc.encode.clip.b(ss, vv, lim)), l1) == True{} : Bool}:
  match ss:
    case True{}:
      clipb.hi(U32.is_gt(vv, lim), vv, lim, l1, e1, U32L.ueq(Jpeg.decode.sign(vv), 0, hs), {==}, ha)
    case False{}:
      clipb.lo(U32.is_gt(Jpeg.decode.abs(vv), lim), vv, lim, l1, e1, {==}, hb)

# the magnitude of a clipped value is at most the limit
def clipb(
  +vv: U32,
  +lim: U32,
  +l1: U32,
  +e1: {U32.to_nat(l1) == 1n+U32.to_nat(lim) : Nat},
  +ha: {U32.is_lt(Jpeg.decode.abs(lim), l1) == True{} : Bool},
  +hb: {U32.is_lt(Jpeg.decode.abs(Jpeg.decode.neg32(lim)), l1) == True{} : Bool}
) -> {U32.is_lt(Jpeg.decode.abs(Jenc.encode.clip(vv, lim)), l1) == True{} : Bool}:
  clipb.s(U32.is_eq(Jpeg.decode.sign(vv), 0), vv, lim, l1, e1, {==}, ha, hb)

# a clipped nonzero value, by whether it was above the limit, is not zero
def clipnz.hi(
  gg: Bool,
  +vv: U32,
  +lim: U32,
  +es: {Jpeg.decode.sign(vv) == 0 : U32},
  +hv: {U32.is_eq(vv, 0) == False{} : Bool},
  +ha: {U32.is_lt(Jpeg.decode.abs(lim), 1) == False{} : Bool}
) -> {U32.is_lt(Jpeg.decode.abs(Jenc.encode.clip.hi(gg, vv, lim)), 1) == False{} : Bool}:
  match gg:
    case True{}:
      ha
    case False{}:
      ev = Equal.sym(U32, Jpeg.decode.abs(vv), vv, abs_pos(vv, es))
      %ev : {U32.is_lt(_, 1) == False{} : Bool}
      u_nz(vv, hv)

# a clipped negative nonzero value, by whether its magnitude was above the limit, is not zero
def clipnz.lo(
  gg: Bool,
  +vv: U32,
  +lim: U32,
  +es: {Jpeg.decode.sign(vv) == 1 : U32},
  +hv: {U32.is_eq(vv, 0) == False{} : Bool},
  +hb: {U32.is_lt(Jpeg.decode.abs(Jpeg.decode.neg32(lim)), 1) == False{} : Bool}
) -> {U32.is_lt(Jpeg.decode.abs(Jenc.encode.clip.lo(gg, vv, lim)), 1) == False{} : Bool}:
  match gg:
    case True{}:
      hb
    case False{}:
      ev = Equal.sym(U32, Jpeg.decode.abs(vv), Jpeg.decode.neg32(vv), abs_neg(vv, es))
      %ev : {U32.is_lt(_, 1) == False{} : Bool}
      u_nz(Jpeg.decode.neg32(vv), Equal.trans(Bool, U32.is_eq(Jpeg.decode.neg32(vv), 0), U32.is_eq(vv, 0), False{},
        neg_nz(vv), hv))

# a clipped nonzero value, by its sign, is not zero
def clipnz.s(
  ss: Bool,
  +vv: U32,
  +lim: U32,
  +hs: {U32.is_eq(Jpeg.decode.sign(vv), 0) == ss : Bool},
  +hv: {U32.is_eq(vv, 0) == False{} : Bool},
  +ha: {U32.is_lt(Jpeg.decode.abs(lim), 1) == False{} : Bool},
  +hb: {U32.is_lt(Jpeg.decode.abs(Jpeg.decode.neg32(lim)), 1) == False{} : Bool}
) -> {U32.is_lt(Jpeg.decode.abs(Jenc.encode.clip.b(ss, vv, lim)), 1) == False{} : Bool}:
  match ss:
    case True{}:
      clipnz.hi(U32.is_gt(vv, lim), vv, lim, U32L.ueq(Jpeg.decode.sign(vv), 0, hs), hv, ha)
    case False{}:
      clipnz.lo(U32.is_gt(Jpeg.decode.abs(vv), lim), vv, lim, sign01(vv, hs), hv, hb)

# the magnitude of a clipped nonzero value is not zero
def clipnz(
  +vv: U32,
  +lim: U32,
  +hv: {U32.is_eq(vv, 0) == False{} : Bool},
  +ha: {U32.is_lt(Jpeg.decode.abs(lim), 1) == False{} : Bool},
  +hb: {U32.is_lt(Jpeg.decode.abs(Jpeg.decode.neg32(lim)), 1) == False{} : Bool}
) -> {U32.is_lt(Jpeg.decode.abs(Jenc.encode.clip(vv, lim)), 1) == False{} : Bool}:
  clipnz.s(U32.is_eq(Jpeg.decode.sign(vv), 0), vv, lim, {==}, hv, ha, hb)

# an AC coefficient clipped to 1023 has a magnitude below 1024
def clip.ac(+vv: U32) -> {U32.is_lt(Jpeg.decode.abs(Jenc.encode.clip(vv, 1023)), 1024) == True{} : Bool}:
  clipb(vv, 1023, 1024, {==}, {==}, {==})

# a DC difference clipped to 2047 has a magnitude below 2048
def clip.dc(+vv: U32) -> {U32.is_lt(Jpeg.decode.abs(Jenc.encode.clip(vv, 2047)), 2048) == True{} : Bool}:
  clipb(vv, 2047, 2048, {==}, {==}, {==})

# a nonzero AC coefficient clipped to 1023 is not zero
def clipnz.ac(
  +vv: U32,
  +hv: {U32.is_eq(vv, 0) == False{} : Bool}
) -> {U32.is_lt(Jpeg.decode.abs(Jenc.encode.clip(vv, 1023)), 1) == False{} : Bool}:
  clipnz(vv, 1023, hv, {==}, {==})

# the size of a magnitude, as its chain of comparisons, is one of [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
def memcat.ac.b(
  b0: Bool,
  b1: Bool,
  b2: Bool,
  b3: Bool,
  b4: Bool,
  b5: Bool,
  b6: Bool,
  b7: Bool,
  b8: Bool,
  b9: Bool,
  b10: Bool,
  b11: Bool,
  h0: {b0 == False{} : Bool},
  hh: {b10 == True{} : Bool}
) -> {Laws.jpg.memb(Jenc.encode.cat.pick(b0, 0, Jenc.encode.cat.pick(b1, 1, Jenc.encode.cat.pick(b2, 2,
  Jenc.encode.cat.pick(b3, 3, Jenc.encode.cat.pick(b4, 4, Jenc.encode.cat.pick(b5, 5, Jenc.encode.cat.pick(b6, 6,
  Jenc.encode.cat.pick(b7, 7, Jenc.encode.cat.pick(b8, 8, Jenc.encode.cat.pick(b9, 9, Jenc.encode.cat.pick(b10, 10,
  Jenc.encode.cat.pick(b11, 11, 12)))))))))))), [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]) == True{} : Bool}:
  match b0:
    case True{}:
      Empty.absurd({Laws.jpg.memb(Jenc.encode.cat.pick(True{}, 0, Jenc.encode.cat.pick(b1, 1, Jenc.encode.cat.pick(b2,
        2, Jenc.encode.cat.pick(b3, 3, Jenc.encode.cat.pick(b4, 4, Jenc.encode.cat.pick(b5, 5,
        Jenc.encode.cat.pick(b6, 6, Jenc.encode.cat.pick(b7, 7, Jenc.encode.cat.pick(b8, 8, Jenc.encode.cat.pick(b9,
        9, Jenc.encode.cat.pick(b10, 10, Jenc.encode.cat.pick(b11, 11, 12)))))))))))), [1, 2, 3, 4, 5, 6, 7, 8, 9,
        10]) == True{} : Bool}, true_false(h0))
    case False{}:
      match b1:
        case True{}:
          {==}
        case False{}:
          match b2:
            case True{}:
              {==}
            case False{}:
              match b3:
                case True{}:
                  {==}
                case False{}:
                  match b4:
                    case True{}:
                      {==}
                    case False{}:
                      match b5:
                        case True{}:
                          {==}
                        case False{}:
                          match b6:
                            case True{}:
                              {==}
                            case False{}:
                              match b7:
                                case True{}:
                                  {==}
                                case False{}:
                                  match b8:
                                    case True{}:
                                      {==}
                                    case False{}:
                                      match b9:
                                        case True{}:
                                          {==}
                                        case False{}:
                                          match b10:
                                            case True{}:
                                              {==}
                                            case False{}:
                                              Empty.absurd({Laws.jpg.memb(Jenc.encode.cat.pick(False{}, 0,
                                                Jenc.encode.cat.pick(False{}, 1, Jenc.encode.cat.pick(False{}, 2,
                                                Jenc.encode.cat.pick(False{}, 3, Jenc.encode.cat.pick(False{}, 4,
                                                Jenc.encode.cat.pick(False{}, 5, Jenc.encode.cat.pick(False{}, 6,
                                                Jenc.encode.cat.pick(False{}, 7, Jenc.encode.cat.pick(False{}, 8,
                                                Jenc.encode.cat.pick(False{}, 9, Jenc.encode.cat.pick(False{}, 10,
                                                Jenc.encode.cat.pick(b11, 11, 12)))))))))))), [1, 2, 3, 4, 5, 6, 7, 8,
                                                9, 10]) == True{} : Bool}, W12.false_true(hh))

# the size of a magnitude, as its chain of comparisons, is one of Jenc.encode.dcsyms()
def memcat.dc.b(
  b0: Bool,
  b1: Bool,
  b2: Bool,
  b3: Bool,
  b4: Bool,
  b5: Bool,
  b6: Bool,
  b7: Bool,
  b8: Bool,
  b9: Bool,
  b10: Bool,
  b11: Bool,
  hh: {b11 == True{} : Bool}
) -> {Laws.jpg.memb(Jenc.encode.cat.pick(b0, 0, Jenc.encode.cat.pick(b1, 1, Jenc.encode.cat.pick(b2, 2,
  Jenc.encode.cat.pick(b3, 3, Jenc.encode.cat.pick(b4, 4, Jenc.encode.cat.pick(b5, 5, Jenc.encode.cat.pick(b6, 6,
  Jenc.encode.cat.pick(b7, 7, Jenc.encode.cat.pick(b8, 8, Jenc.encode.cat.pick(b9, 9, Jenc.encode.cat.pick(b10, 10,
  Jenc.encode.cat.pick(b11, 11, 12)))))))))))), Jenc.encode.dcsyms()) == True{} : Bool}:
  match b0:
    case True{}:
      {==}
    case False{}:
      match b1:
        case True{}:
          {==}
        case False{}:
          match b2:
            case True{}:
              {==}
            case False{}:
              match b3:
                case True{}:
                  {==}
                case False{}:
                  match b4:
                    case True{}:
                      {==}
                    case False{}:
                      match b5:
                        case True{}:
                          {==}
                        case False{}:
                          match b6:
                            case True{}:
                              {==}
                            case False{}:
                              match b7:
                                case True{}:
                                  {==}
                                case False{}:
                                  match b8:
                                    case True{}:
                                      {==}
                                    case False{}:
                                      match b9:
                                        case True{}:
                                          {==}
                                        case False{}:
                                          match b10:
                                            case True{}:
                                              {==}
                                            case False{}:
                                              match b11:
                                                case True{}:
                                                  {==}
                                                case False{}:
                                                  Empty.absurd({Laws.jpg.memb(Jenc.encode.cat.pick(False{}, 0,
                                                    Jenc.encode.cat.pick(False{}, 1, Jenc.encode.cat.pick(False{}, 2,
                                                    Jenc.encode.cat.pick(False{}, 3, Jenc.encode.cat.pick(False{}, 4,
                                                    Jenc.encode.cat.pick(False{}, 5, Jenc.encode.cat.pick(False{}, 6,
                                                    Jenc.encode.cat.pick(False{}, 7, Jenc.encode.cat.pick(False{}, 8,
                                                    Jenc.encode.cat.pick(False{}, 9, Jenc.encode.cat.pick(False{}, 10,
                                                    Jenc.encode.cat.pick(False{}, 11, 12)))))))))))),
                                                    Jenc.encode.dcsyms()) == True{} : Bool}, W12.false_true(hh))

# the size of an AC magnitude from 1 to 1023 is one of 1 to 10
def memcat.ac(
  +xx: U32,
  h0: {U32.is_lt(Jpeg.decode.abs(xx), 1) == False{} : Bool},
  hh: {U32.is_lt(Jpeg.decode.abs(xx), 1024) == True{} : Bool}
) -> {Laws.jpg.memb(Jenc.encode.cat(xx), [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]) == True{} : Bool}:
  memcat.ac.b(U32.is_lt(Jpeg.decode.abs(xx), 1), U32.is_lt(Jpeg.decode.abs(xx), 2), U32.is_lt(Jpeg.decode.abs(xx), 4),
    U32.is_lt(Jpeg.decode.abs(xx), 8), U32.is_lt(Jpeg.decode.abs(xx), 16), U32.is_lt(Jpeg.decode.abs(xx), 32),
    U32.is_lt(Jpeg.decode.abs(xx), 64), U32.is_lt(Jpeg.decode.abs(xx), 128), U32.is_lt(Jpeg.decode.abs(xx), 256),
    U32.is_lt(Jpeg.decode.abs(xx), 512), U32.is_lt(Jpeg.decode.abs(xx), 1024), U32.is_lt(Jpeg.decode.abs(xx), 2048),
    h0, hh)

# the size of a DC difference below 2048 in magnitude is one of the DC symbols
def memcat.dc(
  +xx: U32,
  hh: {U32.is_lt(Jpeg.decode.abs(xx), 2048) == True{} : Bool}
) -> {Laws.jpg.memb(Jenc.encode.cat(xx), Jenc.encode.dcsyms()) == True{} : Bool}:
  memcat.dc.b(U32.is_lt(Jpeg.decode.abs(xx), 1), U32.is_lt(Jpeg.decode.abs(xx), 2), U32.is_lt(Jpeg.decode.abs(xx), 4),
    U32.is_lt(Jpeg.decode.abs(xx), 8), U32.is_lt(Jpeg.decode.abs(xx), 16), U32.is_lt(Jpeg.decode.abs(xx), 32),
    U32.is_lt(Jpeg.decode.abs(xx), 64), U32.is_lt(Jpeg.decode.abs(xx), 128), U32.is_lt(Jpeg.decode.abs(xx), 256),
    U32.is_lt(Jpeg.decode.abs(xx), 512), U32.is_lt(Jpeg.decode.abs(xx), 1024), U32.is_lt(Jpeg.decode.abs(xx), 2048), hh)

# a word of four bits over 28 zeros is one of 0 to 15
def nib.b(
  b0: Bool,
  b1: Bool,
  b2: Bool,
  b3: Bool
) -> {Laws.jpg.memb(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, Word.zero(28n)}}}}}, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10,
  11, 12, 13, 14, 15]) == True{} : Bool}:
  match b0:
    case True{}:
      match b1:
        case True{}:
          match b2:
            case True{}:
              match b3:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match b3:
                case True{}:
                  {==}
                case False{}:
                  {==}
        case False{}:
          match b2:
            case True{}:
              match b3:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match b3:
                case True{}:
                  {==}
                case False{}:
                  {==}
    case False{}:
      match b1:
        case True{}:
          match b2:
            case True{}:
              match b3:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match b3:
                case True{}:
                  {==}
                case False{}:
                  {==}
        case False{}:
          match b2:
            case True{}:
              match b3:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match b3:
                case True{}:
                  {==}
                case False{}:
                  {==}

# the low four bits of a U32 are one of 0 to 15
def nib16(
  vv: U32
) -> {Laws.jpg.memb(U32.and(15, vv), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]) == True{} : Bool}:
  match vv:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{_b4, WCon{_b5, WCon{_b6, WCon{_b7, WCon{_b8, WCon{_b9,
      WCon{_b10, WCon{_b11, WCon{_b12, WCon{_b13, WCon{_b14, WCon{_b15, WCon{_b16, WCon{_b17, WCon{_b18, WCon{_b19,
      WCon{_b20, WCon{_b21, WCon{_b22, WCon{_b23, WCon{_b24, WCon{_b25, WCon{_b26, WCon{_b27, WCon{_b28, WCon{_b29,
      WCon{_b30, WCon{_b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      nib.b(b0, b1, b2, b3)

# the AC symbol of run nibble qq and size cc
def acsym(+qq: U32, +cc: U32) -> U32:
  U32.or(cc, U32.shln(qq, 4n))

# the facts the decoder needs of the AC symbol of nibble qq and size cc: in the table, not EOB or ZRL, its size and
# its run read back
def symok(+qq: U32, +cc: U32) -> Bool:
  +sy = acsym(qq, cc)
  Bool.and(Laws.jpg.memb(sy, Jenc.encode.acsyms()), Bool.and(Bool.not(U32.is_eq(sy, 0)), Bool.and(Bool.not(U32.is_eq(sy,
    240)), Bool.and(U32.is_eq(U32.and(15, sy), cc), U32.is_eq(U32.shrn(sy, 4n), qq)))))

# the facts for nibble qq and every size of a list
def allc(+qq: U32, cs: List<&2, U32>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case +cc <> rest:
      Laws.jpg.also(symok(qq, cc), allc(qq, rest))

# the facts for every nibble and size of two lists
def allq(qs: List<&2, U32>, +cs: List<&2, U32>) -> Bool:
  match qs:
    case Nil{}:
      True{}
    case +qq <> rest:
      Laws.jpg.also(allc(qq, cs), allq(rest, cs))

# the statement of allq.ok
def allq.ok.ty() -> Type:
  {allq([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]) == True{} : Bool}

# every nibble from 0 to 15 and size from 1 to 10 has the facts
def allq.ok() -> allq.ok.ty():
  {==}

# the rest of the sizes, as a size's membership step needs it
def IncIh(+_qq: U32, +_cc: U32, -rest: List<&2, U32>) -> Type:
  @hr: {Laws.jpg.memb(_cc, rest) == True{} : Bool} -> @ha: {allc(_qq, rest) == True{} : Bool} -> {symok(_qq,
    _cc) == True{} :
    Bool}

# a size of the list, by whether it is the list's first
def inc.b(
  eq: Bool,
  +qq: U32,
  +cc: U32,
  +xx: U32,
  +rest: List<&2, U32>,
  he: {U32.is_eq(cc, xx) == eq : Bool},
  hin: {Laws.jpg.eith(eq, Laws.jpg.memb(cc, rest)) == True{} : Bool},
  hall: {Laws.jpg.also(symok(qq, xx), allc(qq, rest)) == True{} : Bool},
  ih: IncIh(qq, cc, rest)
) -> {symok(qq, cc) == True{} : Bool}:
  match eq:
    case True{}:
      es = Equal.sym(U32, cc, xx, U32L.ueq(cc, xx, he))
      %es : {symok(qq, _) == True{} : Bool}
      W12.also_l(symok(qq, xx), allc(qq, rest), hall)
    case False{}:
      ih(hin, W12.also_r(symok(qq, xx), allc(qq, rest), hall))

# a size of a list whose sizes all have the facts has them
def inc(
  cs: List<&2, U32>,
  +qq: U32,
  +cc: U32,
  hin: {Laws.jpg.memb(cc, cs) == True{} : Bool},
  hall: {allc(qq, cs) == True{} : Bool}
) -> {symok(qq, cc) == True{} : Bool}:
  match cs:
    case Nil{}:
      Empty.absurd({symok(qq, cc) == True{} : Bool}, W12.false_true(hin))
    case +xx <> +rest:
      inc.b(U32.is_eq(cc, xx), qq, cc, xx, rest, {==}, hin, hall, hr => ha => inc(rest, qq, cc, hr, ha))

# the rest of the nibbles, as a nibble's membership step needs it
def InqIh(+_qq: U32, +_cc: U32, -rest: List<&2, U32>, -cs: List<&2, U32>) -> Type:
  @hr: {Laws.jpg.memb(_qq, rest) == True{} : Bool} -> @ha: {allq(rest, cs) == True{} : Bool} -> {symok(_qq,
    _cc) == True{} :
    Bool}

# a nibble of the list, by whether it is the list's first
def inq.b(
  eq: Bool,
  +qq: U32,
  +cc: U32,
  +xx: U32,
  +rest: List<&2, U32>,
  +cs: List<&2, U32>,
  he: {U32.is_eq(qq, xx) == eq : Bool},
  hin: {Laws.jpg.eith(eq, Laws.jpg.memb(qq, rest)) == True{} : Bool},
  hc: {Laws.jpg.memb(cc, cs) == True{} : Bool},
  hall: {Laws.jpg.also(allc(xx, cs), allq(rest, cs)) == True{} : Bool},
  ih: InqIh(qq, cc, rest, cs)
) -> {symok(qq, cc) == True{} : Bool}:
  match eq:
    case True{}:
      es = Equal.sym(U32, qq, xx, U32L.ueq(qq, xx, he))
      %es : {symok(_, cc) == True{} : Bool}
      inc(cs, xx, cc, hc, W12.also_l(allc(xx, cs), allq(rest, cs), hall))
    case False{}:
      ih(hin, W12.also_r(allc(xx, cs), allq(rest, cs), hall))

# a nibble and a size of lists whose pairs all have the facts have them
def inq(
  qs: List<&2, U32>,
  +cs: List<&2, U32>,
  +qq: U32,
  +cc: U32,
  hin: {Laws.jpg.memb(qq, qs) == True{} : Bool},
  +hc: {Laws.jpg.memb(cc, cs) == True{} : Bool},
  hall: {allq(qs, cs) == True{} : Bool}
) -> {symok(qq, cc) == True{} : Bool}:
  match qs:
    case Nil{}:
      Empty.absurd({symok(qq, cc) == True{} : Bool}, W12.false_true(hin))
    case +xx <> +rest:
      inq.b(U32.is_eq(qq, xx), qq, cc, xx, rest, cs, {==}, hin, hc, hall, hr => ha => inq(rest, cs, qq, cc, hr, hc, ha))

# the AC symbol of a run's nibble and an AC size has the facts
def symok.of(
  +run: U32,
  +cc: U32,
  hc: {Laws.jpg.memb(cc, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]) == True{} : Bool}
) -> {symok(U32.and(15, run), cc) == True{} : Bool}:
  inq([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10], U32.and(15, run), cc,
    nib16(run), hc, allq.ok())

# a word compare not above after its low bits is not above before them
def fin_ngt(
  aa: Bool,
  bb: Bool,
  tt: Cmp,
  hh: {Cmp.is_gt(Word.cmp.fin(aa, bb, tt)) == False{} : Bool}
) -> {Cmp.is_gt(tt) == False{} : Bool}:
  match tt:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({Cmp.is_gt(GT{}) == False{} : Bool}, true_false(hh))

# a one-bit word not above one whose bit is clear has a clear bit
def ngt_top0(
  aa: Bool,
  bb: Bool,
  tt: Word(0n),
  uu: Word(0n),
  hc: {wtop(0n, WCon{bb, uu}) == False{} : Bool},
  hh: {Cmp.is_gt(Word.cmp(1n, WCon{aa, tt}, WCon{bb, uu})) == False{} : Bool}
) -> {wtop(0n, WCon{aa, tt}) == False{} : Bool}:
  match aa bb:
    case True{} True{}:
      Empty.absurd({wtop(0n, WCon{True{}, tt}) == False{} : Bool}, true_false(hc))
    case False{} True{}:
      Empty.absurd({wtop(0n, WCon{False{}, tt}) == False{} : Bool}, true_false(hc))
    case True{} False{}:
      Empty.absurd({wtop(0n, WCon{True{}, tt}) == False{} : Bool}, true_false(hh))
    case False{} False{}:
      {==}

# a word not above one whose top bit is clear has a clear top bit
def ngt_top(
  nn: Nat,
  ww: Word(1n+nn),
  cw: Word(1n+nn),
  hc: {wtop(nn, cw) == False{} : Bool},
  hh: {Cmp.is_gt(Word.cmp(1n+nn, ww, cw)) == False{} : Bool}
) -> {wtop(nn, ww) == False{} : Bool}:
  match nn:
    case 0n:
      match ww cw:
        case WCon{aa, tt} WCon{bb, uu}:
          ngt_top0(aa, bb, tt, uu, hc, hh)
    case 1n+ +pp:
      match ww cw:
        case WCon{+aa, +tt} WCon{+bb, +uu}:
          ngt_top(pp, tt, uu, hc, fin_ngt(aa, bb, Word.cmp(1n+pp, tt, uu), hh))

# a compare that is below is not above
def lt_ngt(tt: Cmp, hh: {Cmp.is_lt(tt) == True{} : Bool}) -> {Cmp.is_gt(tt) == False{} : Bool}:
  match tt:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({Cmp.is_gt(EQ{}) == False{} : Bool}, W12.false_true(hh))
    case GT{}:
      Empty.absurd({Cmp.is_gt(GT{}) == False{} : Bool}, W12.false_true(hh))

# a U32 below one whose top bit is clear has sign 0
def small_sign(
  +xx: U32,
  +cc: U32,
  hc: {wtop(31n, uw(cc)) == False{} : Bool},
  hh: {U32.is_lt(xx, cc) == True{} : Bool}
) -> {Jpeg.decode.sign(xx) == 0 : U32}:
  match xx cc:
    case U32{+xw} U32{+cw}:
      Equal.trans(U32, Jpeg.decode.sign(U32{xw}), U32{WCon{wtop(31n, xw), Word.zero(31n)}}, 0, sign_top(U32{xw}),
        Equal.cong(Bool, U32, bb => U32{WCon{bb, Word.zero(31n)}}, wtop(31n, xw), False{}, ngt_top(31n, xw, cw, hc,
        lt_ngt(Word.cmp(32n, xw, cw), hh))))

# a U32 below 2048 is its own magnitude
def abs_small(+xx: U32, hh: {U32.is_lt(xx, 2048) == True{} : Bool}) -> {Jpeg.decode.abs(xx) == xx : U32}:
  abs_pos(xx, small_sign(xx, 2048, {==}, hh))

# below n + 1 is at most n
def lt_s_le(xx: Nat, zz: Nat) -> {Nat.is_lt(xx, 1n+zz) == Nat.is_le(xx, zz) : Bool}:
  match xx zz:
    case 0n 0n:
      {==}
    case 0n 1n+_q:
      {==}
    case 1n+pp 0n:
      Equal.sym(Bool, False{}, Nat.is_lt(pp, 0n), R.lt_zero_false(pp))
    case 1n+pp 1n+qq:
      lt_s_le(pp, qq)

# at least, read the other way, is at most
def ge_le(xx: Nat, yy: Nat) -> {Cmp.is_ge(Nat.cmp(xx, yy)) == Nat.is_le(yy, xx) : Bool}:
  match xx yy:
    case 0n 0n:
      {==}
    case 0n 1n+_q:
      {==}
    case 1n+_p 0n:
      {==}
    case 1n+pp 1n+qq:
      ge_le(pp, qq)

# not at most is above, read the other way
def nle_lt(xx: Nat, yy: Nat, hh: {Nat.is_le(xx, yy) == False{} : Bool}) -> {Nat.is_lt(yy, xx) == True{} : Bool}:
  match xx yy:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, true_false(hh))
    case 0n 1n+_q:
      Empty.absurd({Nat.is_lt(1n+_q, 0n) == True{} : Bool}, true_false(hh))
    case 1n+_p 0n:
      {==}
    case 1n+pp 1n+qq:
      nle_lt(pp, qq, hh)

# a U32 compare below, as Nat
def ult_n(
  +xx: U32,
  +yy: U32,
  hh: {U32.is_lt(xx, yy) == True{} : Bool}
) -> {Nat.is_lt(U32.to_nat(xx), U32.to_nat(yy)) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_lt(U32.to_nat(xx), U32.to_nat(yy)), U32.is_lt(xx, yy), True{}, Equal.sym(Bool, U32.is_lt(xx,
    yy), Nat.is_lt(U32.to_nat(xx), U32.to_nat(yy)), R.u32_lt(xx, yy)), hh)

# a Nat compare below, as U32
def n_ult(
  +xx: U32,
  +yy: U32,
  hh: {Nat.is_lt(U32.to_nat(xx), U32.to_nat(yy)) == True{} : Bool}
) -> {U32.is_lt(xx, yy) == True{} : Bool}:
  Equal.trans(Bool, U32.is_lt(xx, yy), Nat.is_lt(U32.to_nat(xx), U32.to_nat(yy)), True{}, R.u32_lt(xx, yy), hh)

# a clipped value is below the limit plus 1
def hi_lt(
  gg: Bool,
  +vv: U32,
  +lim: U32,
  +l1: U32,
  e1: {U32.to_nat(l1) == 1n+U32.to_nat(lim) : Nat},
  hg: {U32.is_gt(vv, lim) == gg : Bool},
  hl: {U32.is_lt(lim, l1) == True{} : Bool}
) -> {U32.is_lt(Jenc.encode.clip.hi(gg, vv, lim), l1) == True{} : Bool}:
  match gg:
    case True{}:
      hl
    case False{}:
      u_ngt_lt(vv, lim, l1, e1, hg)

# a value below 1024, plus 1024, is below 2048
def add1024(
  +cc: U32,
  hc: {U32.is_lt(cc, 1024) == True{} : Bool}
) -> {U32.is_lt((cc + 1024 : U32), 2048) == True{} : Bool}:
  +cn = U32.to_nat(cc)
  h1 = R.lt_add_mono(1024n, cn, 1024n, ult_n(cc, 1024, hc))
  +h2 = {Equal.trans(Bool, Nat.is_lt(Nat.add(cn, 1024n), 2048n), Nat.is_lt(Nat.add(1024n, cn), 2048n), True{},
    Equal.cong(Nat, Bool, nn => Nat.is_lt(nn, 2048n), Nat.add(cn, 1024n), Nat.add(1024n, cn), R.add_comm(cn, 1024n)),
    h1) : {Nat.is_lt(Nat.add(cn, 1024n), 2048n) == True{} : Bool}}
  n_ult((cc + 1024 : U32), 2048, Equal.trans(Bool, Nat.is_lt(U32.to_nat((cc + 1024 : U32)), 2048n),
    Nat.is_lt(Nat.add(cn, 1024n), 2048n), True{}, Equal.cong(Nat, Bool, nn => Nat.is_lt(nn, 2048n),
    U32.to_nat((cc + 1024 : U32)), Nat.add(cn, 1024n), R.u32_add_below(cc, 1024, 2048, R.lt_le(Nat.add(cn, 1024n),
    2048n, h2))), h2))

# 1024 less a value at most 1024 is below 2048
def sub1024(
  +mm: U32,
  hm: {U32.is_lt(mm, 1025) == True{} : Bool}
) -> {U32.is_lt((1024 - mm : U32), 2048) == True{} : Bool}:
  +mn = U32.to_nat(mm)
  hl = Equal.trans(Bool, Nat.is_le(mn, 1024n), Nat.is_lt(mn, 1025n), True{}, Equal.sym(Bool, Nat.is_lt(mn, 1025n),
    Nat.is_le(mn, 1024n), lt_s_le(mn, 1024n)), ult_n(mm, 1025, hm))
  n_ult((1024 - mm : U32), 2048, Equal.trans(Bool, Nat.is_lt(U32.to_nat((1024 - mm : U32)), 2048n),
    Nat.is_lt(Nat.sub(1024n, mn), 2048n), True{}, Equal.cong(Nat, Bool, nn => Nat.is_lt(nn, 2048n),
    U32.to_nat((1024 - mm : U32)), Nat.sub(1024n, mn), R.u32_sub_nat(1024, mm, hl)), R.le_lt_trans(Nat.sub(1024n,
    mn), 1024n, 2048n, R.sub_le(1024n, mn), {==})))

# a DC clipped and biased, by its sign, is below 2048
def bias.b(pos: Bool, +vv: U32) -> {U32.is_lt(Jenc.encode.dcbias.b(pos, vv), 2048) == True{} : Bool}:
  match pos:
    case True{}:
      add1024(Jenc.encode.clip.hi(U32.is_gt(vv, 1023), vv, 1023), hi_lt(U32.is_gt(vv, 1023), vv, 1023, 1024, {==},
        {==}, {==}))
    case False{}:
      +av = Jpeg.decode.abs(vv)
      sub1024(Jenc.encode.clip.hi(U32.is_gt(av, 1024), av, 1024), hi_lt(U32.is_gt(av, 1024), av, 1024, 1025, {==},
        {==}, {==}))

# a DC clipped and biased is below 2048
def bias_lt(+vv: U32) -> {U32.is_lt(Jenc.encode.dcbias(vv), 2048) == True{} : Bool}:
  bias.b(U32.is_eq(Jpeg.decode.sign(vv), 0), vv)

# the difference of two biased DCs, the first at least the second, is below 2048
def up_lt(
  +bb: U32,
  +pb: U32,
  hb: {U32.is_lt(bb, 2048) == True{} : Bool},
  hg: {U32.is_ge(bb, pb) == True{} : Bool}
) -> {U32.is_lt((bb - pb : U32), 2048) == True{} : Bool}:
  +bn = U32.to_nat(bb)
  +pn = U32.to_nat(pb)
  hl = Equal.trans(Bool, Nat.is_le(pn, bn), Cmp.is_ge(Nat.cmp(bn, pn)), True{}, Equal.sym(Bool, Cmp.is_ge(Nat.cmp(bn,
    pn)), Nat.is_le(pn, bn), ge_le(bn, pn)), Equal.trans(Bool, Cmp.is_ge(Nat.cmp(bn, pn)), U32.is_ge(bb, pb), True{},
    Equal.cong(Cmp, Bool, cc => Cmp.is_ge(cc), Nat.cmp(bn, pn), U32.cmp(bb, pb), Equal.sym(Cmp, U32.cmp(bb, pb),
    Nat.cmp(bn, pn), u_cmp(bb, pb))), hg))
  n_ult((bb - pb : U32), 2048, Equal.trans(Bool, Nat.is_lt(U32.to_nat((bb - pb : U32)), 2048n), Nat.is_lt(Nat.sub(bn,
    pn), 2048n), True{}, Equal.cong(Nat, Bool, nn => Nat.is_lt(nn, 2048n), U32.to_nat((bb - pb : U32)), Nat.sub(bn,
    pn), R.u32_sub_nat(bb, pb, hl)), R.le_lt_trans(Nat.sub(bn, pn), bn, 2048n, R.sub_le(bn, pn), ult_n(bb, 2048,
    hb))))

# the difference of two biased DCs, the first below the second, taken the other way, is below 2048
def down_lt(
  +bb: U32,
  +pb: U32,
  hp: {U32.is_lt(pb, 2048) == True{} : Bool},
  hg: {U32.is_ge(bb, pb) == False{} : Bool}
) -> {U32.is_lt((pb - bb : U32), 2048) == True{} : Bool}:
  +bn = U32.to_nat(bb)
  +pn = U32.to_nat(pb)
  hn = Equal.trans(Bool, Nat.is_le(pn, bn), Cmp.is_ge(Nat.cmp(bn, pn)), False{}, Equal.sym(Bool, Cmp.is_ge(Nat.cmp(bn,
    pn)), Nat.is_le(pn, bn), ge_le(bn, pn)), Equal.trans(Bool, Cmp.is_ge(Nat.cmp(bn, pn)), U32.is_ge(bb, pb), False{},
    Equal.cong(Cmp, Bool, cc => Cmp.is_ge(cc), Nat.cmp(bn, pn), U32.cmp(bb, pb), Equal.sym(Cmp, U32.cmp(bb, pb),
    Nat.cmp(bn, pn), u_cmp(bb, pb))), hg))
  hl = R.lt_le(bn, pn, nle_lt(pn, bn, hn))
  n_ult((pb - bb : U32), 2048, Equal.trans(Bool, Nat.is_lt(U32.to_nat((pb - bb : U32)), 2048n), Nat.is_lt(Nat.sub(pn,
    bn), 2048n), True{}, Equal.cong(Nat, Bool, nn => Nat.is_lt(nn, 2048n), U32.to_nat((pb - bb : U32)), Nat.sub(pn,
    bn), R.u32_sub_nat(pb, bb, hl)), R.le_lt_trans(Nat.sub(pn, bn), pn, 2048n, R.sub_le(pn, bn), ult_n(pb, 2048,
    hp))))

# the writer's bits of a code of kk bits are kk bits
def len_cb(kk: Nat, +code: U32) -> {List.length(&2, Bool, Laws.jpg.cb(kk, code)) == kk : Nat}:
  match kk:
    case 0n:
      {==}
    case 1n+ +pp:
      Equal.cong(Nat, Nat, nn => 1n+nn, List.length(&2, Bool, Laws.jpg.cb(pp, code)), pp, len_cb(pp, code))

# the magnitude bits of a negative DC difference -mm: none for size 0
def mzn(zero: Bool, +cat: U32, +mm: U32) -> List<&2, Bool>:
  match zero:
    case True{}:
      +_u = (cat + mm : U32)
      []
    case False{}:
      Laws.jpg.cb(U32.to_nat(cat), ((U32.shln(1, U32.to_nat(cat)) - 1 : U32) - mm : U32))

# the encoder's magnitude bits of a negative DC difference are mzn's, fed to the writer
def magn_eq(
  zero: Bool,
  +pp: Jenc.Put,
  +cat: U32,
  +mm: U32
) -> {Jenc.encode.magp.n(zero, pp, cat, mm) == Laws.jpg.feed(mzn(zero, cat, mm), pp) : Jenc.Put}:
  match zero:
    case True{}:
      {==}
    case False{}:
      W12.bits_go(U32.to_nat(cat), pp, ((U32.shln(1, U32.to_nat(cat)) - 1 : U32) - mm : U32))

# as many magnitude bits as the size, by whether the size is 0
def mzlen(
  zero: Bool,
  +cat: U32,
  +vv: U32,
  hz: {U32.is_eq(cat, 0) == zero : Bool}
) -> {Nat.is_eq(List.length(&2, Bool, mz(zero, cat, vv)), U32.to_nat(cat)) == True{} : Bool}:
  match zero:
    case True{}:
      ec = Equal.sym(U32, cat, 0, U32L.ueq(cat, 0, hz))
      %ec : {Nat.is_eq(0n, U32.to_nat(_)) == True{} : Bool}
      {==}
    case False{}:
      +kn = U32.to_nat(cat)
      el = Equal.sym(Nat, List.length(&2, Bool, Laws.jpg.cb(kn, Jenc.encode.mag(cat, vv))), kn, len_cb(kn,
        Jenc.encode.mag(cat,
        vv)))
      %el : {Nat.is_eq(_, kn) == True{} : Bool}
      R.nat_eq_refl(kn)

# as many magnitude bits of a negative difference as the size, by whether the size is 0
def mznlen(
  zero: Bool,
  +cat: U32,
  +mm: U32,
  hz: {U32.is_eq(cat, 0) == zero : Bool}
) -> {Nat.is_eq(List.length(&2, Bool, mzn(zero, cat, mm)), U32.to_nat(cat)) == True{} : Bool}:
  match zero:
    case True{}:
      ec = Equal.sym(U32, cat, 0, U32L.ueq(cat, 0, hz))
      %ec : {Nat.is_eq(0n, U32.to_nat(_)) == True{} : Bool}
      {==}
    case False{}:
      +kn = U32.to_nat(cat)
      +mg = ((U32.shln(1, kn) - 1 : U32) - mm : U32)
      el = Equal.sym(Nat, List.length(&2, Bool, Laws.jpg.cb(kn, mg)), kn, len_cb(kn, mg))
      %el : {Nat.is_eq(_, kn) == True{} : Bool}
      R.nat_eq_refl(kn)

# the DC book's code for a size, then the magnitude bits of a difference
def dcuse_eq(
  +cat: U32,
  +pp: Jenc.Put,
  +xx: U32
) -> {Jenc.encode.dc.use(Jenc.encode.sym(dcbk(), cat), pp, cat, xx) == (dcbk(), Laws.jpg.feed(List.append(&2, Bool,
  W12.code.dc(cat), mz(U32.is_eq(cat, 0), cat, xx)), pp)) : Array<U32> & Jenc.Put}:
  +vv = Laws.jpg.val(Array.get(U32, dcbk(), cat))
  +cd = W12.code.dc(cat)
  +mb = mz(U32.is_eq(cat, 0), cat, xx)
  Equal.trans(Array<U32> & Jenc.Put, Jenc.encode.dc.use(Jenc.encode.coded(Array.get(U32, dcbk(), cat)), pp, cat, xx),
    Jenc.encode.dc.use(Jenc.encode.coded((dcbk(), vv)), pp, cat, xx), (dcbk(), Laws.jpg.feed(List.append(&2, Bool, cd,
    mb), pp)), Equal.cong(Array<U32> & U32, Array<U32> & Jenc.Put, gg => Jenc.encode.dc.use(Jenc.encode.coded(gg), pp,
    cat, xx), Array.get(U32, dcbk(), cat), (dcbk(), vv), W10.get.eq(dcbk(), cat)), Equal.cong(Jenc.Put,
    Array<U32> & Jenc.Put, qq => (dcbk(), qq), Jenc.encode.magp.z(U32.is_eq(cat, 0), Jenc.encode.bits.go(
    U32.to_nat(U32.shrn(vv, 16n)), pp, U32.and(vv, 65535)), cat, xx), Laws.jpg.feed(List.append(&2, Bool, cd, mb), pp),
    Equal.trans(Jenc.Put, Jenc.encode.magp.z(U32.is_eq(cat, 0), Jenc.encode.bits.go(U32.to_nat(U32.shrn(vv, 16n)), pp,
    U32.and(vv, 65535)), cat, xx), Jenc.encode.magp.z(U32.is_eq(cat, 0), Laws.jpg.feed(cd, pp), cat, xx), Laws.jpg.feed(
    List.append(&2, Bool, cd, mb), pp), Equal.cong(Jenc.Put, Jenc.Put, qq => Jenc.encode.magp.z(U32.is_eq(cat, 0), qq,
    cat, xx), Jenc.encode.bits.go(U32.to_nat(U32.shrn(vv, 16n)), pp, U32.and(vv, 65535)), Laws.jpg.feed(cd, pp),
    W12.bits_go(U32.to_nat(U32.shrn(vv, 16n)), pp, U32.and(vv, 65535))), Equal.trans(Jenc.Put, Jenc.encode.magp.z(
    U32.is_eq(cat, 0), Laws.jpg.feed(cd, pp), cat, xx), Laws.jpg.feed(mb, Laws.jpg.feed(cd, pp)),
      Laws.jpg.feed(List.append(&2, Bool, cd, mb),
    pp), magp_eq(U32.is_eq(cat, 0), Laws.jpg.feed(cd, pp), cat, xx), Equal.sym(Jenc.Put, Laws.jpg.feed(List.append(&2,
      Bool, cd,
    mb), pp), Laws.jpg.feed(mb, Laws.jpg.feed(cd, pp)), W12.feed_app(cd, mb, pp))))))

# the DC book's code for a size, then the magnitude bits of a negative difference
def dcneg_eq(
  +cat: U32,
  +pp: Jenc.Put,
  +mm: U32
) -> {Jenc.encode.dc.use.neg(Jenc.encode.sym(dcbk(), cat), pp, cat, mm) == (dcbk(), Laws.jpg.feed(List.append(&2,
  Bool, W12.code.dc(cat), mzn(U32.is_eq(cat, 0), cat, mm)), pp)) : Array<U32> & Jenc.Put}:
  +vv = Laws.jpg.val(Array.get(U32, dcbk(), cat))
  +cd = W12.code.dc(cat)
  +mb = mzn(U32.is_eq(cat, 0), cat, mm)
  Equal.trans(Array<U32> & Jenc.Put, Jenc.encode.dc.use.neg(Jenc.encode.coded(Array.get(U32, dcbk(), cat)), pp, cat,
    mm), Jenc.encode.dc.use.neg(Jenc.encode.coded((dcbk(), vv)), pp, cat, mm), (dcbk(), Laws.jpg.feed(List.append(&2,
    Bool, cd, mb), pp)), Equal.cong(Array<U32> & U32, Array<U32> & Jenc.Put, gg => Jenc.encode.dc.use.neg(
    Jenc.encode.coded(gg), pp, cat, mm), Array.get(U32, dcbk(), cat), (dcbk(), vv), W10.get.eq(dcbk(), cat)),
    Equal.cong(Jenc.Put, Array<U32> & Jenc.Put, qq => (dcbk(), qq), Jenc.encode.magp.n(U32.is_eq(cat, 0),
    Jenc.encode.bits.go(U32.to_nat(U32.shrn(vv, 16n)), pp, U32.and(vv, 65535)), cat, mm),
      Laws.jpg.feed(List.append(&2, Bool,
    cd, mb), pp), Equal.trans(Jenc.Put, Jenc.encode.magp.n(U32.is_eq(cat, 0), Jenc.encode.bits.go(U32.to_nat(
    U32.shrn(vv, 16n)), pp, U32.and(vv, 65535)), cat, mm), Jenc.encode.magp.n(U32.is_eq(cat, 0), Laws.jpg.feed(cd,
      pp), cat,
    mm), Laws.jpg.feed(List.append(&2, Bool, cd, mb), pp), Equal.cong(Jenc.Put, Jenc.Put, qq => Jenc.encode.magp.n(
    U32.is_eq(cat, 0), qq, cat, mm), Jenc.encode.bits.go(U32.to_nat(U32.shrn(vv, 16n)), pp, U32.and(vv, 65535)),
    Laws.jpg.feed(cd, pp), W12.bits_go(U32.to_nat(U32.shrn(vv, 16n)), pp, U32.and(vv, 65535))), Equal.trans(Jenc.Put,
    Jenc.encode.magp.n(U32.is_eq(cat, 0), Laws.jpg.feed(cd, pp), cat, mm), Laws.jpg.feed(mb, Laws.jpg.feed(cd, pp)),
      Laws.jpg.feed(
    List.append(&2, Bool, cd, mb), pp), magn_eq(U32.is_eq(cat, 0), Laws.jpg.feed(cd, pp), cat, mm), Equal.sym(Jenc.Put,
    Laws.jpg.feed(List.append(&2, Bool, cd, mb), pp), Laws.jpg.feed(mb, Laws.jpg.feed(cd, pp)), W12.feed_app(cd, mb,
      pp))))))

# the DC part of a block: a size of the DC table, its code and as many magnitude bits, fed to the writer
def DcRes(+bb: U32, +pb: U32, +pp: Jenc.Put) -> Type:
  &dcs: U32 -> &dcx: List<&2, Bool> -> &_e: {Jenc.encode.dcdiff(dcbk(), pp, bb, pb) == (dcbk(), Laws.jpg.feed(
    List.append(&2, Bool, W12.code.dc(dcs), dcx), pp)) : Array<U32> & Jenc.Put} -> &_h: {Laws.jpg.memb(dcs,
    Jenc.encode.dcsyms()) == True{} : Bool} -> {Nat.is_eq(List.length(&2, Bool, dcx), U32.to_nat(dcs)) == True{} :
    Bool}

# the DC part of a block, by the difference's sign
def dcres.b(
  up: Bool,
  +bb: U32,
  +pb: U32,
  +pp: Jenc.Put,
  hb: {U32.is_lt(bb, 2048) == True{} : Bool},
  hp: {U32.is_lt(pb, 2048) == True{} : Bool},
  hg: {U32.is_ge(bb, pb) == up : Bool}
) -> {Jenc.encode.dcdiff.b(up, dcbk(), pp, bb, pb) == Jenc.encode.dcdiff(dcbk(), pp, bb,
  pb) : Array<U32> & Jenc.Put} -> DcRes(bb, pb, pp):
  match up:
    case True{}:
      +xx = (bb - pb : U32)
      +cat = Jenc.encode.cat(xx)
      +hx = {up_lt(bb, pb, hb, hg) : {U32.is_lt(xx, 2048) == True{} : Bool}}
      ed => (cat, mz(U32.is_eq(cat, 0), cat, xx), Equal.trans(Array<U32> & Jenc.Put, Jenc.encode.dcdiff(dcbk(),
        pp, bb, pb), Jenc.encode.dc.use(Jenc.encode.sym(dcbk(), cat), pp, cat, xx), (dcbk(), Laws.jpg.feed(
        List.append(&2, Bool, W12.code.dc(cat), mz(U32.is_eq(cat, 0), cat, xx)), pp)), Equal.sym(Array<U32> &
        Jenc.Put, Jenc.encode.dcdiff.b(True{}, dcbk(), pp, bb, pb), Jenc.encode.dcdiff(dcbk(), pp, bb, pb), ed),
        dcuse_eq(cat, pp, xx)), memcat.dc(xx, Equal.trans(Bool, U32.is_lt(Jpeg.decode.abs(xx), 2048),
        U32.is_lt(xx, 2048), True{}, Equal.cong(U32, Bool, uu => U32.is_lt(uu, 2048), Jpeg.decode.abs(xx), xx,
        abs_small(xx, hx)), hx)), mzlen(U32.is_eq(cat, 0), cat, xx, {==}))
    case False{}:
      +mm = (pb - bb : U32)
      +cat = Jenc.encode.cat(mm)
      +hm = {down_lt(bb, pb, hp, hg) : {U32.is_lt(mm, 2048) == True{} : Bool}}
      ed => (cat, mzn(U32.is_eq(cat, 0), cat, mm), Equal.trans(Array<U32> & Jenc.Put, Jenc.encode.dcdiff(dcbk(), pp,
        bb, pb), Jenc.encode.dc.use.neg(Jenc.encode.sym(dcbk(), cat), pp, cat, mm), (dcbk(), Laws.jpg.feed(
        List.append(&2, Bool, W12.code.dc(cat), mzn(U32.is_eq(cat, 0), cat, mm)), pp)), Equal.sym(Array<U32> &
        Jenc.Put, Jenc.encode.dcdiff.b(False{}, dcbk(), pp, bb, pb), Jenc.encode.dcdiff(dcbk(), pp, bb, pb), ed),
        dcneg_eq(cat, pp, mm)), memcat.dc(mm, Equal.trans(Bool, U32.is_lt(Jpeg.decode.abs(mm), 2048),
        U32.is_lt(mm, 2048), True{}, Equal.cong(U32, Bool, uu => U32.is_lt(uu, 2048), Jpeg.decode.abs(mm), mm,
        abs_small(mm, hm)), hm)), mznlen(U32.is_eq(cat, 0), cat, mm, {==}))

# the DC part of a block from two biased DCs below 2048
def dcres(
  +bb: U32,
  +pb: U32,
  +pp: Jenc.Put,
  hb: {U32.is_lt(bb, 2048) == True{} : Bool},
  hp: {U32.is_lt(pb, 2048) == True{} : Bool}
) -> DcRes(bb, pb, pp):
  dcres.b(U32.is_ge(bb, pb), bb, pb, pp, hb, hp, {==}, {==})

# sixteen times a number
def sixteen(nn: Nat) -> Nat:
  Nat.double(Nat.double(Nat.double(Nat.double(nn))))

# a word shifted down keeps its number: the new top bit is clear
def pad_nat(nn: Nat, ww: Word(nn)) -> {Word.to_nat(1n+nn, Word.shr.pad(nn, ww)) == Word.to_nat(nn, ww) : Nat}:
  match nn:
    case 0n:
      {==}
    case 1n+ +pp:
      match ww:
        case WCon{False{}, tt}:
          Equal.cong(Nat, Nat, xx => Nat.double(xx), Word.to_nat(1n+pp, Word.shr.pad(pp, tt)), Word.to_nat(pp, tt),
            pad_nat(pp, tt))
        case WCon{True{}, tt}:
          Equal.cong(Nat, Nat, xx => 1n+Nat.double(xx), Word.to_nat(1n+pp, Word.shr.pad(pp, tt)), Word.to_nat(pp, tt),
            pad_nat(pp, tt))

# one more low bit on two words whose numbers differ by cc: they differ by twice cc
def nstep(
  bb: Bool,
  +pp: Nat,
  +tt: Word(pp),
  +uu: Word(pp),
  +cc: Nat,
  ee: {Word.to_nat(pp, tt) == Nat.add(Word.to_nat(pp, uu), cc) : Nat}
) -> {Word.to_nat(1n+pp, WCon{bb, tt}) == Nat.add(Word.to_nat(1n+pp, WCon{bb, uu}), Nat.double(cc)) : Nat}:
  match bb:
    case False{}:
      +un = Word.to_nat(pp, uu)
      Equal.trans(Nat, Nat.double(Word.to_nat(pp, tt)), Nat.double(Nat.add(un, cc)), Nat.add(Nat.double(un),
        Nat.double(cc)), Equal.cong(Nat, Nat, xx => Nat.double(xx), Word.to_nat(pp, tt), Nat.add(un, cc), ee),
        R.double_dist(un, cc))
    case True{}:
      +un = Word.to_nat(pp, uu)
      Equal.trans(Nat, 1n+Nat.double(Word.to_nat(pp, tt)), 1n+Nat.double(Nat.add(un, cc)), 1n+Nat.add(Nat.double(un),
        Nat.double(cc)), Equal.cong(Nat, Nat, xx => 1n+Nat.double(xx), Word.to_nat(pp, tt), Nat.add(un, cc), ee),
        Equal.cong(Nat, Nat, xx => 1n+xx, Nat.double(Nat.add(un, cc)), Nat.add(Nat.double(un), Nat.double(cc)),
        R.double_dist(un, cc)))

# zero and a word is zero
def and_zero_l(nn: Nat, ww: Word(nn)) -> {Word.and(nn, Word.zero(nn), ww) == Word.zero(nn) : Word(nn)}:
  match nn:
    case 0n:
      match ww:
        case WNil{}:
          {==}
    case 1n+ +pp:
      match ww:
        case WCon{_b, tt}:
          Equal.cong(Word(pp), Word.Con<pp>, xx => WCon{False{}, xx}, Word.and(pp, Word.zero(pp), tt), Word.zero(pp),
            and_zero_l(pp, tt))

# a U32 is its low four bits and sixteen times the rest
def n1(
  xx: U32
) -> {U32.to_nat(xx) == Nat.add(U32.to_nat(U32.and(15, xx)), sixteen(U32.to_nat(U32.shrn(xx, 4n)))) : Nat}:
  match xx:
    case U32{WCon{+b0, WCon{+b1, WCon{+b2, WCon{+b3, +tt}}}}}:
      +hn = Word.to_nat(28n, tt)
      +zz = Word.zero(28n)
      +e0 = {{==} : {Word.to_nat(28n, tt) == Nat.add(Word.to_nat(28n, zz), hn) : Nat}}
      +e1 = {nstep(b3, 28n, tt, zz, hn, e0) : {Word.to_nat(29n, WCon{b3, tt}) == Nat.add(Word.to_nat(29n, WCon{b3, zz}),
        Nat.double(hn)) : Nat}}
      +e2 = {nstep(b2, 29n, WCon{b3, tt}, WCon{b3, zz}, Nat.double(hn), e1) : {Word.to_nat(30n, WCon{b2, WCon{b3, tt}})
        == Nat.add(Word.to_nat(30n, WCon{b2, WCon{b3, zz}}), Nat.double(Nat.double(hn))) : Nat}}
      +e3 = {nstep(b1, 30n, WCon{b2, WCon{b3, tt}}, WCon{b2, WCon{b3, zz}}, Nat.double(Nat.double(hn)), e2) :
        {Word.to_nat(31n, WCon{b1, WCon{b2, WCon{b3, tt}}}) == Nat.add(Word.to_nat(31n, WCon{b1, WCon{b2, WCon{b3,
        zz}}}), Nat.double(Nat.double(Nat.double(hn)))) : Nat}}
      +e4 = {nstep(b0, 31n, WCon{b1, WCon{b2, WCon{b3, tt}}}, WCon{b1, WCon{b2, WCon{b3, zz}}}, Nat.double(Nat.double(
        Nat.double(hn))), e3) : {Word.to_nat(32n, WCon{b0, WCon{b1, WCon{b2, WCon{b3,
          tt}}}}) == Nat.add(Word.to_nat(32n,
        WCon{b0, WCon{b1, WCon{b2, WCon{b3, zz}}}}), sixteen(hn)) : Nat}}
      ea = Equal.sym(Word(28n), Word.and(28n, Word.zero(28n), tt), zz, and_zero_l(28n, tt))
      %ea : {Word.to_nat(32n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, tt}}}}) == Nat.add(Word.to_nat(32n, WCon{b0, WCon{b1,
        WCon{b2, WCon{b3, _}}}}), sixteen(U32.to_nat(U32.shrn(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, tt}}}}}, 4n))))
        : Nat}
      +p1 = Word.shr.pad(28n, tt)
      +p2 = Word.shr.pad(29n, p1)
      +p3 = Word.shr.pad(30n, p2)
      ep = Equal.sym(Nat, Word.to_nat(32n, Word.shr.pad(31n, p3)), hn, Equal.trans(Nat, Word.to_nat(32n,
        Word.shr.pad(31n, p3)), Word.to_nat(31n, p3), hn, pad_nat(31n, p3), Equal.trans(Nat, Word.to_nat(31n, p3),
        Word.to_nat(30n, p2), hn, pad_nat(30n, p2), Equal.trans(Nat, Word.to_nat(30n, p2), Word.to_nat(29n, p1), hn,
        pad_nat(29n, p1), pad_nat(28n, tt)))))
      %ep : {Word.to_nat(32n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, tt}}}}) == Nat.add(Word.to_nat(32n, WCon{b0, WCon{b1,
        WCon{b2, WCon{b3, zz}}}}), sixteen(_)) : Nat}
      e4

# both answers when the first holds are the second
def also_t(ok: Bool, -rest: Bool, hh: {ok == True{} : Bool}) -> {Laws.jpg.also(ok, rest) == rest : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Laws.jpg.also(False{}, rest) == rest : Bool}, W12.false_true(hh))

# two that hold
def and_tt(
  aa: Bool,
  -bb: Bool,
  ha: {aa == True{} : Bool},
  hb: {bb == True{} : Bool}
) -> {Bool.and(aa, bb) == True{} : Bool}:
  match aa:
    case True{}:
      hb
    case False{}:
      Empty.absurd({Bool.and(False{}, bb) == True{} : Bool}, W12.false_true(ha))

# either, when the first holds
def or_tl(aa: Bool, -bb: Bool, ha: {aa == True{} : Bool}) -> {Bool.or(aa, bb) == True{} : Bool}:
  match aa:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Bool.or(False{}, bb) == True{} : Bool}, W12.false_true(ha))

# not of one that fails
def not_f(aa: Bool, ha: {aa == False{} : Bool}) -> {Bool.not(aa) == True{} : Bool}:
  match aa:
    case True{}:
      Empty.absurd({Bool.not(True{}) == True{} : Bool}, true_false(ha))
    case False{}:
      {==}

# below is not equal
def lt_ne(xx: Nat, nn: Nat, hh: {Nat.is_lt(xx, nn) == True{} : Bool}) -> {Nat.is_eq(xx, nn) == False{} : Bool}:
  match xx nn:
    case 0n 0n:
      Empty.absurd({Nat.is_eq(0n, 0n) == False{} : Bool}, W12.false_true(hh))
    case 0n 1n+_q:
      {==}
    case 1n+_p 0n:
      {==}
    case 1n+ +pp 1n+ +qq:
      lt_ne(pp, qq, hh)

# below is not at least
def lt_nle(xx: Nat, nn: Nat, hh: {Nat.is_lt(xx, nn) == True{} : Bool}) -> {Nat.is_le(nn, xx) == False{} : Bool}:
  match xx nn:
    case 0n 0n:
      Empty.absurd({Nat.is_le(0n, 0n) == False{} : Bool}, W12.false_true(hh))
    case 0n 1n+_q:
      {==}
    case 1n+_p 0n:
      Empty.absurd({Nat.is_le(0n, 1n+_p) == False{} : Bool}, W12.false_true(hh))
    case 1n+ +pp 1n+ +qq:
      lt_nle(pp, qq, hh)

# adding a positive number makes more
def lt_add_pos(
  xx: Nat,
  +rr: Nat,
  hh: {Nat.is_lt(0n, rr) == True{} : Bool}
) -> {Nat.is_lt(xx, Nat.add(xx, rr)) == True{} : Bool}:
  match xx:
    case 0n:
      hh
    case 1n+ +pp:
      lt_add_pos(pp, rr, hh)

# above 0 is at least 1
def gt0(rr: Nat, hh: {Cmp.is_gt(Nat.cmp(rr, 0n)) == True{} : Bool}) -> {Nat.is_lt(0n, rr) == True{} : Bool}:
  match rr:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, W12.false_true(hh))
    case 1n+_p:
      {==}

# not above 0 is 0
def ngt0(rr: Nat, hh: {Cmp.is_gt(Nat.cmp(rr, 0n)) == False{} : Bool}) -> {rr == 0n : Nat}:
  match rr:
    case 0n:
      {==}
    case 1n+_p:
      Empty.absurd({1n+_p == 0n : Nat}, true_false(hh))

# a number is at most its double
def le_double(nn: Nat) -> {Nat.is_le(nn, Nat.double(nn)) == True{} : Bool}:
  match nn:
    case 0n:
      {==}
    case 1n+ +pp:
      R.le_trans(pp, Nat.double(pp), 1n+Nat.double(pp), le_double(pp), R.le_succ(Nat.double(pp)))

# a number is at most sixteen times it
def le_sixteen(+nn: Nat) -> {Nat.is_le(nn, sixteen(nn)) == True{} : Bool}:
  +d1 = Nat.double(nn)
  +d2 = Nat.double(d1)
  +d3 = Nat.double(d2)
  R.le_trans(nn, d1, sixteen(nn), le_double(nn), R.le_trans(d1, d2, sixteen(nn), le_double(d1), R.le_trans(d2, d3,
    sixteen(nn), le_double(d2), le_double(d3))))

# one less than a bound above j is a bound for j
def le_npred(
  jj: Nat,
  ll: Nat,
  hh: {Nat.is_le(1n+jj, ll) == True{} : Bool}
) -> {Nat.is_le(jj, Laws.jpg.npred(ll)) == True{} : Bool}:
  match ll:
    case 0n:
      Empty.absurd({Nat.is_le(jj, 0n) == True{} : Bool}, W12.false_true(hh))
    case 1n+_q:
      hh

# a bound above j is above 0
def pos_of_le(jj: Nat, ll: Nat, hh: {Nat.is_le(1n+jj, ll) == True{} : Bool}) -> {Nat.is_lt(0n, ll) == True{} : Bool}:
  match ll:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, W12.false_true(hh))
    case 1n+_q:
      {==}

# the lookups left after j tokens
def npreds(jj: Nat, ll: Nat) -> Nat:
  match jj:
    case 0n:
      ll
    case 1n+ +pp:
      npreds(pp, Laws.jpg.npred(ll))

# a bound of j + m leaves m after j tokens
def npl(
  jj: Nat,
  +mm: Nat,
  +ll: Nat,
  hh: {Nat.is_le(Nat.add(jj, mm), ll) == True{} : Bool}
) -> {Nat.is_le(mm, npreds(jj, ll)) == True{} : Bool}:
  match jj:
    case 0n:
      hh
    case 1n+ +pp:
      npl(pp, mm, Laws.jpg.npred(ll), le_npred(Nat.add(pp, mm), ll, hh))

# the index after j ZRLs
def kz(jj: Nat, +kk: U32) -> U32:
  match jj:
    case 0n:
      kk
    case 1n+ +pp:
      kz(pp, (kk + 16 : U32))

# a U32 sum whose Nat sum is at most 64 is the Nat sum
def uadd(
  +aa: U32,
  +bb: U32,
  hh: {Nat.is_le(Nat.add(U32.to_nat(aa), U32.to_nat(bb)), 64n) == True{} : Bool}
) -> {U32.to_nat((aa + bb : U32)) == Nat.add(U32.to_nat(aa), U32.to_nat(bb)) : Nat}:
  R.u32_add_below(aa, bb, 64, hh)

# the index after j ZRLs, as a Nat, while it stays below 64
def kz_nat(
  jj: Nat,
  +kk: U32,
  hh: {Nat.is_lt(Nat.add(U32.to_nat(kk), sixteen(jj)), 64n) == True{} : Bool}
) -> {U32.to_nat(kz(jj, kk)) == Nat.add(U32.to_nat(kk), sixteen(jj)) : Nat}:
  match jj:
    case 0n:
      Equal.sym(Nat, Nat.add(U32.to_nat(kk), 0n), U32.to_nat(kk), R.add_zero(U32.to_nat(kk)))
    case 1n+ +pp:
      +kn = U32.to_nat(kk)
      +sp = sixteen(pp)
      +ea = {R.add_assoc(kn, 16n, sp) : {Nat.add(Nat.add(kn, 16n), sp) == Nat.add(kn, 16n+sp) : Nat}}
      +hs = {Equal.trans(Bool, Nat.is_lt(Nat.add(Nat.add(kn, 16n), sp), 64n), Nat.is_lt(Nat.add(kn, 16n+sp), 64n),
        True{},
        Equal.cong(Nat, Bool, nn => Nat.is_lt(nn, 64n), Nat.add(Nat.add(kn, 16n), sp), Nat.add(kn, 16n+sp), ea), hh) :
        {Nat.is_lt(Nat.add(Nat.add(kn, 16n), sp), 64n) == True{} : Bool}}
      +e16 = {uadd(kk, 16, R.le_add_r(Nat.add(kn, 16n), sp, 64n, R.lt_le(Nat.add(Nat.add(kn, 16n), sp), 64n, hs))) :
        {U32.to_nat((kk + 16 : U32)) == Nat.add(kn, 16n) : Nat}}
      +h2 = {Equal.trans(Bool, Nat.is_lt(Nat.add(U32.to_nat((kk + 16 : U32)), sp), 64n), Nat.is_lt(Nat.add(Nat.add(kn,
        16n), sp), 64n), True{}, Equal.cong(Nat, Bool, nn => Nat.is_lt(Nat.add(nn, sp), 64n), U32.to_nat((kk + 16 :
        U32)), Nat.add(kn, 16n), e16), hs) : {Nat.is_lt(Nat.add(U32.to_nat((kk + 16 : U32)), sp), 64n) == True{} :
        Bool}}
      Equal.trans(Nat, U32.to_nat(kz(pp, (kk + 16 : U32))), Nat.add(U32.to_nat((kk + 16 : U32)), sp), Nat.add(kn,
        16n+sp), kz_nat(pp, (kk + 16 : U32), h2), Equal.trans(Nat, Nat.add(U32.to_nat((kk + 16 : U32)), sp),
        Nat.add(Nat.add(kn, 16n), sp), Nat.add(kn, 16n+sp), Equal.cong(Nat, Nat, nn => Nat.add(nn, sp), U32.to_nat((kk +
        16 : U32)), Nat.add(kn, 16n), e16), ea))

# a ZRL token is read at an index at most 48 with a lookup left, and moves the index on by 16
def zrl_ok(
  +kk: U32,
  +left: Nat,
  hz: {Nat.is_lt(0n, left) == True{} : Bool},
  hq: {U32.is_lt((kk + 16 : U32), 64) == True{} : Bool}
) -> {Laws.jpg.acok(Laws.JTok{240, []}, Laws.JAcSt{kk, left, False{}}) == True{} : Bool}:
  and_tt(Nat.is_lt(0n, left), Bool.or(U32.is_lt((kk + 16 : U32), 64), U32.is_eq((kk + 16 : U32), 64)), hz,
    or_tl(U32.is_lt((kk + 16 : U32), 64), U32.is_eq((kk + 16 : U32), 64), hq))

# j ZRL tokens before more are read in full as the more are from the index 16j on
def zrlwf(
  jj: Nat,
  +kk: U32,
  +left: Nat,
  +rest: List<&2, Laws.JTok>,
  hk: {Nat.is_lt(Nat.add(U32.to_nat(kk), sixteen(jj)), 64n) == True{} : Bool},
  +hl: {Nat.is_le(jj, left) == True{} : Bool}
) -> {Laws.jpg.acwf(List.append(&2, Laws.JTok, zrltoks(jj), rest), Laws.JAcSt{kk, left,
  False{}}) == Laws.jpg.acwf(rest, Laws.JAcSt{kz(jj, kk), npreds(jj, left), False{}}) : Bool}:
  match jj:
    case 0n:
      {==}
    case 1n+ +pp:
      +kn = U32.to_nat(kk)
      +sp = sixteen(pp)
      +tl = List.append(&2, Laws.JTok, zrltoks(pp), rest)
      +ea = {R.add_assoc(kn, 16n, sp) : {Nat.add(Nat.add(kn, 16n), sp) == Nat.add(kn, 16n+sp) : Nat}}
      +hs = {Equal.trans(Bool, Nat.is_lt(Nat.add(Nat.add(kn, 16n), sp), 64n), Nat.is_lt(Nat.add(kn, 16n+sp), 64n),
        True{},
        Equal.cong(Nat, Bool, nn => Nat.is_lt(nn, 64n), Nat.add(Nat.add(kn, 16n), sp), Nat.add(kn, 16n+sp), ea), hk) :
        {Nat.is_lt(Nat.add(Nat.add(kn, 16n), sp), 64n) == True{} : Bool}}
      +e16 = {uadd(kk, 16, R.le_add_r(Nat.add(kn, 16n), sp, 64n, R.lt_le(Nat.add(Nat.add(kn, 16n), sp), 64n, hs))) :
        {U32.to_nat((kk + 16 : U32)) == Nat.add(kn, 16n) : Nat}}
      +h2 = {Equal.trans(Bool, Nat.is_lt(Nat.add(U32.to_nat((kk + 16 : U32)), sp), 64n), Nat.is_lt(Nat.add(Nat.add(kn,
        16n), sp), 64n), True{}, Equal.cong(Nat, Bool, nn => Nat.is_lt(Nat.add(nn, sp), 64n), U32.to_nat((kk + 16 :
        U32)), Nat.add(kn, 16n), e16), hs) : {Nat.is_lt(Nat.add(U32.to_nat((kk + 16 : U32)), sp), 64n) == True{} :
        Bool}}
      +hq = {n_ult((kk + 16 : U32), 64, R.le_lt_trans(U32.to_nat((kk + 16 : U32)), Nat.add(U32.to_nat((kk + 16 :
        U32)), sp), 64n, R.le_add_more(U32.to_nat((kk + 16 : U32)), U32.to_nat((kk + 16 : U32)), sp, R.le_refl(
        U32.to_nat((kk + 16 : U32)))), h2)) : {U32.is_lt((kk + 16 : U32), 64) == True{} : Bool}}
      +tk = {Laws.JTok{240, []} : Laws.JTok}
      +st = {Laws.JAcSt{kk, left, False{}} : Laws.JAcSt}
      +en = {Equal.cong(Bool, Laws.JAcSt, bb => Laws.JAcSt{(kk + 16 : U32), Laws.jpg.npred(left), Bool.not(bb)},
        U32.is_lt((kk + 16 :
        U32), 64), True{}, hq) : {Laws.jpg.acnx(tk, st) == Laws.JAcSt{(kk + 16 : U32), Laws.jpg.npred(left),
          False{}} : Laws.JAcSt}}
      Equal.trans(Bool, Laws.jpg.also(Laws.jpg.acok(tk, st), Laws.jpg.acwf(tl, Laws.jpg.acnx(tk, st))),
        Laws.jpg.acwf(tl, Laws.jpg.acnx(tk, st)),
        Laws.jpg.acwf(rest, Laws.JAcSt{kz(pp, (kk + 16 : U32)), npreds(pp, Laws.jpg.npred(left)), False{}}),
          also_t(Laws.jpg.acok(tk, st),
        Laws.jpg.acwf(tl, Laws.jpg.acnx(tk, st)), zrl_ok(kk, left, pos_of_le(pp, left, hl), hq)), Equal.trans(Bool,
          Laws.jpg.acwf(tl,
        Laws.jpg.acnx(tk, st)), Laws.jpg.acwf(tl, Laws.JAcSt{(kk + 16 : U32), Laws.jpg.npred(left), False{}}),
          Laws.jpg.acwf(rest, Laws.JAcSt{kz(pp, (kk +
        16 : U32)), npreds(pp, Laws.jpg.npred(left)), False{}}), Equal.cong(Laws.JAcSt, Bool, ss => Laws.jpg.acwf(tl,
          ss), Laws.jpg.acnx(tk,
        st), Laws.JAcSt{(kk + 16 : U32), Laws.jpg.npred(left), False{}}, en), zrlwf(pp, (kk + 16 : U32),
          Laws.jpg.npred(left), rest, h2,
        le_npred(pp, left, hl))))

# c is at most y + c
def le_add_left(yy: Nat, +cc: Nat) -> {Nat.is_le(cc, Nat.add(yy, cc)) == True{} : Bool}:
  match yy:
    case 0n:
      R.le_refl(cc)
    case 1n+ +pp:
      R.le_trans(cc, Nat.add(pp, cc), 1n+Nat.add(pp, cc), le_add_left(pp, cc), R.le_succ(Nat.add(pp, cc)))

# adding the same on the right keeps at most
def le_addr(
  xx: Nat,
  yy: Nat,
  +cc: Nat,
  hh: {Nat.is_le(xx, yy) == True{} : Bool}
) -> {Nat.is_le(Nat.add(xx, cc), Nat.add(yy, cc)) == True{} : Bool}:
  match xx yy:
    case 0n _y:
      le_add_left(_y, cc)
    case 1n+_p 0n:
      Empty.absurd({Nat.is_le(Nat.add(1n+_p, cc), Nat.add(0n, cc)) == True{} : Bool}, W12.false_true(hh))
    case 1n+pp 1n+qq:
      le_addr(pp, qq, cc, hh)

# not of one that holds fails
def not_t(aa: Bool, ha: {Bool.not(aa) == True{} : Bool}) -> {aa == False{} : Bool}:
  match aa:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, W12.false_true(ha))
    case False{}:
      {==}

# an AC size, by whether it is 0
def memb_nz.b(
  zz: Bool,
  +xx: U32,
  hz: {U32.is_eq(xx, 0) == zz : Bool},
  hm: {Laws.jpg.memb(xx, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]) == True{} : Bool}
) -> {U32.is_eq(xx, 0) == False{} : Bool}:
  match zz:
    case True{}:
      ex = Equal.sym(U32, xx, 0, U32L.ueq(xx, 0, hz))
      Empty.absurd({U32.is_eq(xx, 0) == False{} : Bool}, W12.false_true(Equal.trans(Bool, Laws.jpg.memb(0, [1, 2, 3,
        4, 5, 6,
        7, 8, 9, 10]), Laws.jpg.memb(xx, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]), True{}, Equal.cong(U32, Bool,
          uu => Laws.jpg.memb(uu, [1,
        2, 3, 4, 5, 6, 7, 8, 9, 10]), 0, xx, ex), hm)))
    case False{}:
      hz

# a size from 1 to 10 is not 0
def memb_nz(
  +xx: U32,
  hm: {Laws.jpg.memb(xx, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]) == True{} : Bool}
) -> {U32.is_eq(xx, 0) == False{} : Bool}:
  memb_nz.b(U32.is_eq(xx, 0), xx, {==}, hm)

# a run and size token's own check, when its symbol is neither EOB nor ZRL
def acokk(
  eob: Bool,
  zrl: Bool,
  +sym: U32,
  ex: List<&2, Bool>,
  +kk: U32,
  he: {eob == False{} : Bool},
  hz: {zrl == False{} : Bool},
  h1: {U32.is_eq(U32.and(15, sym), 0) == False{} : Bool},
  h2: {U32.is_ge((kk + U32.shrn(sym, 4n) : U32), 64) == False{} : Bool},
  h3: {Nat.is_eq(List.length(&2, Bool, ex), U32.to_nat(U32.and(15, sym))) == True{} : Bool}
) -> {Laws.jpg.acok.k(eob, zrl, sym, ex, kk) == True{} : Bool}:
  match eob zrl:
    case True{} _z:
      Empty.absurd({Laws.jpg.acok.k(True{}, _z, sym, ex, kk) == True{} : Bool}, true_false(he))
    case False{} True{}:
      Empty.absurd({Laws.jpg.acok.k(False{}, True{}, sym, ex, kk) == True{} : Bool}, true_false(hz))
    case False{} False{}:
      and_tt(Bool.not(U32.is_eq(U32.and(15, sym), 0)), Bool.and(Bool.not(U32.is_ge((kk + U32.shrn(sym, 4n) : U32), 64)),
        Nat.is_eq(List.length(&2, Bool, ex), U32.to_nat(U32.and(15, sym)))), not_f(U32.is_eq(U32.and(15, sym), 0), h1),
        and_tt(Bool.not(U32.is_ge((kk + U32.shrn(sym, 4n) : U32), 64)), Nat.is_eq(List.length(&2, Bool, ex),
        U32.to_nat(U32.and(15, sym))), not_f(U32.is_ge((kk + U32.shrn(sym, 4n) : U32), 64), h2), h3))

# the state after a run and size token
def acnxk(
  eob: Bool,
  zrl: Bool,
  +sym: U32,
  +kk: U32,
  +left: Nat,
  he: {eob == False{} : Bool},
  hz: {zrl == False{} : Bool}
) -> {Laws.jpg.acnx.k(eob, zrl, sym, kk, left) == Laws.JAcSt{((kk + U32.shrn(sym, 4n) : U32) + 1 : U32),
  Laws.jpg.npred(left), U32.is_eq(((kk + U32.shrn(sym, 4n) : U32) + 1 : U32), 64)} : Laws.JAcSt}:
  match eob zrl:
    case True{} _z:
      Empty.absurd({Laws.jpg.acnx.k(True{}, _z, sym, kk, left) == Laws.JAcSt{((kk + U32.shrn(sym, 4n) : U32) + 1 : U32),
        Laws.jpg.npred(left), U32.is_eq(((kk + U32.shrn(sym, 4n) : U32) + 1 : U32), 64)} : Laws.JAcSt}, true_false(he))
    case False{} True{}:
      Empty.absurd({Laws.jpg.acnx.k(False{}, True{}, sym, kk, left) == Laws.JAcSt{((kk + U32.shrn(sym,
        4n) : U32) + 1 : U32),
        Laws.jpg.npred(left), U32.is_eq(((kk + U32.shrn(sym, 4n) : U32) + 1 : U32), 64)} : Laws.JAcSt}, true_false(hz))
    case False{} False{}:
      {==}

# a run and size token, then more, read from a state that has not ended
def symwf(
  +sym: U32,
  +ex: List<&2, Bool>,
  +kk: U32,
  +left: Nat,
  +ts: List<&2, Laws.JTok>,
  +he: {U32.is_eq(sym, 0) == False{} : Bool},
  +hz: {U32.is_eq(sym, 240) == False{} : Bool},
  hm: {Laws.jpg.memb(sym, Jenc.encode.acsyms()) == True{} : Bool},
  hp: {Nat.is_lt(0n, left) == True{} : Bool},
  h1: {U32.is_eq(U32.and(15, sym), 0) == False{} : Bool},
  h2: {U32.is_ge((kk + U32.shrn(sym, 4n) : U32), 64) == False{} : Bool},
  h3: {Nat.is_eq(List.length(&2, Bool, ex), U32.to_nat(U32.and(15, sym))) == True{} : Bool}
) -> {Laws.jpg.acwf(Laws.JTok{sym, ex} <> ts, Laws.JAcSt{kk, left, False{}}) == Laws.jpg.acwf(ts,
  Laws.JAcSt{((kk + U32.shrn(sym, 4n) : U32) + 1 : U32), Laws.jpg.npred(left), U32.is_eq(((kk + U32.shrn(sym,
  4n) : U32) + 1 : U32), 64)}) : Bool}:
  +tk = {Laws.JTok{sym, ex} : Laws.JTok}
  +st = {Laws.JAcSt{kk, left, False{}} : Laws.JAcSt}
  +n2 = ((kk + U32.shrn(sym, 4n) : U32) + 1 : U32)
  +ok = {and_tt(Nat.is_lt(0n, left), Bool.and(Laws.jpg.memb(sym, Jenc.encode.acsyms()), Laws.jpg.acok.k(U32.is_eq(sym,
    0),
    U32.is_eq(sym, 240), sym, ex, kk)), hp, and_tt(Laws.jpg.memb(sym, Jenc.encode.acsyms()),
      Laws.jpg.acok.k(U32.is_eq(sym, 0),
    U32.is_eq(sym, 240), sym, ex, kk), hm, acokk(U32.is_eq(sym, 0), U32.is_eq(sym, 240), sym, ex, kk, he, hz, h1, h2,
    h3))) : {Laws.jpg.acok(tk, st) == True{} : Bool}}
  Equal.trans(Bool, Laws.jpg.also(Laws.jpg.acok(tk, st), Laws.jpg.acwf(ts, Laws.jpg.acnx(tk, st))), Laws.jpg.acwf(ts,
    Laws.jpg.acnx(tk, st)), Laws.jpg.acwf(ts,
    Laws.JAcSt{n2, Laws.jpg.npred(left), U32.is_eq(n2, 64)}), also_t(Laws.jpg.acok(tk, st), Laws.jpg.acwf(ts,
      Laws.jpg.acnx(tk, st)), ok),
    Equal.cong(Laws.JAcSt, Bool, ss => Laws.jpg.acwf(ts, ss), Laws.jpg.acnx(tk, st), Laws.JAcSt{n2,
      Laws.jpg.npred(left), U32.is_eq(n2, 64)},
    acnxk(U32.is_eq(sym, 0), U32.is_eq(sym, 240), sym, kk, left, he, hz)))

# below n is n at most after adding 1
def lt_add1(
  aa: Nat,
  nn: Nat,
  hh: {Nat.is_lt(aa, nn) == True{} : Bool}
) -> {Nat.is_le(Nat.add(aa, 1n), nn) == True{} : Bool}:
  match aa nn:
    case 0n 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, W12.false_true(hh))
    case 0n 1n+qq:
      R.le_zero(qq)
    case 1n+_p 0n:
      Empty.absurd({Nat.is_le(Nat.add(1n+_p, 1n), 0n) == True{} : Bool}, W12.false_true(hh))
    case 1n+pp 1n+qq:
      lt_add1(pp, qq, hh)

# AC tokens joined, their lists regrouped
def app_t(
  xs: List<&2, Laws.JTok>,
  +ys: List<&2, Laws.JTok>,
  +zs: List<&2, Laws.JTok>
) -> {List.append(&2, Laws.JTok, List.append(&2, Laws.JTok, xs, ys), zs) == List.append(&2, Laws.JTok, xs,
  List.append(&2, Laws.JTok, ys, zs)) : List<&2, Laws.JTok>}:
  match xs:
    case Nil{}:
      {==}
    case +hh <> tt:
      Equal.cong(List<&2, Laws.JTok>, List<&2, Laws.JTok>, ws => hh <> ws, List.append(&2, Laws.JTok, List.append(&2,
        Laws.JTok, tt,
        ys), zs), List.append(&2, Laws.JTok, tt, List.append(&2, Laws.JTok, ys, zs)), app_t(tt, ys, zs))

# the AC coder from a state: tokens it writes to the writer, read in full by the decoder's loop from the matching
# state
def AclRes(-zz: List<&2, U32>, +run: U32, +kk: U32, +left: Nat, +pp: Jenc.Put) -> Type:
  &ts: List<&2, Laws.JTok> -> &_e: {Jenc.encode.ac(zz, run, (acbk(), pp)) == (acbk(), Laws.jpg.feed(W12.acbits(ts),
    pp)) :
    Array<U32> & Jenc.Put} -> {Laws.jpg.acwf(ts, Laws.JAcSt{kk, left, U32.is_eq(kk, 64)}) == True{} : Bool}

# the AC coder's positions: the decoder's index, the zero run, and the coefficients left make 64
def AclPos(+kk: U32, +run: U32, -zz: List<&2, U32>) -> Type:
  {Nat.add(U32.to_nat(kk), Nat.add(U32.to_nat(run), List.length(&2, U32, zz))) == 64n : Nat}

# the lookups left cover the zero run and the coefficients left
def AclLeft(+run: U32, -zz: List<&2, U32>, +left: Nat) -> Type:
  {Nat.is_le(Nat.add(U32.to_nat(run), List.length(&2, U32, zz)), left) == True{} : Bool}

# the AC coder on the rest of the coefficients, from any state that keeps the invariant
def AclIh(-ct: List<&2, U32>) -> Type:
  @r2: U32 -> @k2: U32 -> @l2: Nat -> @p2: Jenc.Put -> @e2: AclPos(k2, r2, ct) -> @h2: AclLeft(r2, ct, l2) ->
    AclRes(ct, r2, k2, l2, p2)

# a U32 above 0, as a Nat compare
def ugt0(
  +run: U32,
  gz: Bool,
  hg: {U32.is_gt(run, 0) == gz : Bool}
) -> {Cmp.is_gt(Nat.cmp(U32.to_nat(run), 0n)) == gz : Bool}:
  Equal.trans(Bool, Cmp.is_gt(Nat.cmp(U32.to_nat(run), 0n)), U32.is_gt(run, 0), gz, Equal.cong(Cmp, Bool, cc =>
    Cmp.is_gt(cc), Nat.cmp(U32.to_nat(run), 0n), U32.cmp(run, 0), Equal.sym(Cmp, U32.cmp(run, 0), Nat.cmp(U32.to_nat(
    run), 0n), u_cmp(run, 0))), hg)

# the AC coder at the end of the coefficients, by whether a zero run is open
def acl_nil(
  gz: Bool,
  +run: U32,
  +kk: U32,
  +left: Nat,
  +pp: Jenc.Put,
  +hg: {U32.is_gt(run, 0) == gz : Bool},
  ee: AclPos(kk, run, []),
  hl: AclLeft(run, [], left)
) -> AclRes([], run, kk, left, pp):
  match gz:
    case True{}:
      +rn = U32.to_nat(run)
      +kn = U32.to_nat(kk)
      +hr = {gt0(rn, ugt0(run, True{}, hg)) : {Nat.is_lt(0n, rn) == True{} : Bool}}
      +ez = {R.add_zero(rn) : {Nat.add(rn, 0n) == rn : Nat}}
      +e1 = {Equal.trans(Nat, Nat.add(kn, rn), Nat.add(kn, Nat.add(rn, 0n)), 64n, Equal.cong(Nat, Nat, nn => Nat.add(kn,
        nn), rn, Nat.add(rn, 0n), Equal.sym(Nat, Nat.add(rn, 0n), rn, ez)), ee) : {Nat.add(kn, rn) == 64n : Nat}}
      +hk = {Equal.trans(Bool, Nat.is_lt(kn, 64n), Nat.is_lt(kn, Nat.add(kn, rn)), True{}, Equal.cong(Nat, Bool, nn =>
        Nat.is_lt(kn, nn), 64n, Nat.add(kn, rn), Equal.sym(Nat, Nat.add(kn, rn), 64n, e1)), lt_add_pos(kn, rn, hr)) :
        {Nat.is_lt(kn, 64n) == True{} : Bool}}
      +he = {Equal.trans(Bool, U32.is_eq(kk, 64), Nat.is_eq(kn, 64n), False{}, R.u32_eq(kk, 64), lt_ne(kn, 64n, hk)) :
        {U32.is_eq(kk, 64) == False{} : Bool}}
      +hp = {R.lt_le_trans(0n, rn, left, hr, Equal.trans(Bool, Nat.is_le(rn, left), Nat.is_le(Nat.add(rn, 0n), left),
        True{}, Equal.cong(Nat, Bool, nn => Nat.is_le(nn, left), rn, Nat.add(rn, 0n), Equal.sym(Nat, Nat.add(rn, 0n),
          rn,
        ez)), hl)) : {Nat.is_lt(0n, left) == True{} : Bool}}
      +tk = {Laws.JTok{0, []} : Laws.JTok}
      +st = {Laws.JAcSt{kk, left, U32.is_eq(kk, 64)} : Laws.JAcSt}
      +c0 = W12.code.ac(0)
      +ok = {and_tt(Bool.not(U32.is_eq(kk, 64)), Bool.and(Nat.is_lt(0n, left), Bool.and(Laws.jpg.memb(0,
        Jenc.encode.acsyms()), Laws.jpg.acok.k(True{}, False{}, 0, [], kk))), not_f(U32.is_eq(kk, 64), he), and_tt(
        Nat.is_lt(0n, left), Bool.and(Laws.jpg.memb(0, Jenc.encode.acsyms()), Laws.jpg.acok.k(True{}, False{}, 0, [],
          kk)), hp,
        {==})) : {Laws.jpg.acok(tk, st) == True{} : Bool}}
      ([tk], Equal.trans(Array<U32> & Jenc.Put, Jenc.encode.eob.on(U32.is_gt(run, 0), (acbk(), pp)),
        Jenc.encode.eob.on(True{}, (acbk(), pp)), (acbk(), Laws.jpg.feed(W12.acbits([tk]), pp)), Equal.cong(Bool,
        Array<U32> & Jenc.Put, gg => Jenc.encode.eob.on(gg, (acbk(), pp)), U32.is_gt(run, 0), True{}, hg),
        Equal.trans(Array<U32> & Jenc.Put, Jenc.encode.emit(Jenc.encode.sym(acbk(), 0), pp), (acbk(), Laws.jpg.feed(c0,
        pp)), (acbk(), Laws.jpg.feed(W12.acbits([tk]), pp)), emitp.ac(0, pp), Equal.cong(List<&2, Bool>,
        Array<U32> & Jenc.Put, xs => (acbk(), Laws.jpg.feed(xs, pp)), c0, List.append(&2, Bool, c0, []), Equal.sym(
        List<&2, Bool>, List.append(&2, Bool, c0, []), c0, W12.app_nil(c0))))), Equal.trans(Bool,
          Laws.jpg.also(Laws.jpg.acok(tk,
        st), Laws.jpg.acwf([], Laws.jpg.acnx(tk, st))), Laws.jpg.acwf([], Laws.jpg.acnx(tk, st)), True{},
          also_t(Laws.jpg.acok(tk, st), Laws.jpg.acwf([],
        Laws.jpg.acnx(tk, st)), ok), {==}))
    case False{}:
      +rn = U32.to_nat(run)
      +kn = U32.to_nat(kk)
      +hr = {ngt0(rn, ugt0(run, False{}, hg)) : {rn == 0n : Nat}}
      +ek = {Equal.trans(Nat, kn, Nat.add(kn, 0n), 64n, Equal.sym(Nat, Nat.add(kn, 0n), kn, R.add_zero(kn)),
        Equal.trans(
        Nat, Nat.add(kn, 0n), Nat.add(kn, Nat.add(rn, 0n)), 64n, Equal.cong(Nat, Nat, nn => Nat.add(kn, Nat.add(nn,
          0n)),
        0n, rn, Equal.sym(Nat, rn, 0n, hr)), ee)) : {kn == 64n : Nat}}
      +he = {Equal.trans(Bool, U32.is_eq(kk, 64), Nat.is_eq(kn, 64n), True{}, R.u32_eq(kk, 64), Equal.trans(Bool,
        Nat.is_eq(kn, 64n), Nat.is_eq(64n, 64n), True{}, Equal.cong(Nat, Bool, nn => Nat.is_eq(nn, 64n), kn, 64n, ek),
        {==})) : {U32.is_eq(kk, 64) == True{} : Bool}}
      ([], Equal.cong(Bool, Array<U32> & Jenc.Put, gg => Jenc.encode.eob.on(gg, (acbk(), pp)), U32.is_gt(run, 0),
        False{}, hg), he)

# the AC coder past a zero coefficient, from its run one longer
def acl_zero(
  +cc: U32,
  +ct: List<&2, U32>,
  +run: U32,
  +kk: U32,
  +left: Nat,
  +pp: Jenc.Put,
  hz: {U32.is_eq(cc, 0) == True{} : Bool},
  res: AclRes(ct, (run + 1 : U32), kk, left, pp)
) -> AclRes(cc <> ct, run, kk, left, pp):
  (ts, eq, wf) = res
  (ts, Equal.trans(Array<U32> & Jenc.Put, Jenc.encode.ac(ct, Jenc.encode.ac.run(U32.is_eq(cc, 0), run),
    Jenc.encode.ac.at(U32.is_eq(cc, 0), cc, run, (acbk(), pp))), Jenc.encode.ac(ct, (run + 1 : U32), (acbk(),
    pp)), (acbk(), Laws.jpg.feed(W12.acbits(ts), pp)), Equal.cong(Bool, Array<U32> & Jenc.Put, zz => Jenc.encode.ac(ct,
    Jenc.encode.ac.run(zz, run), Jenc.encode.ac.at(zz, cc, run, (acbk(), pp))), U32.is_eq(cc, 0), True{}, hz), eq),
    wf)

# the invariant one coefficient on, past a zero
def acl_zero_pos(
  +ct: List<&2, U32>,
  +run: U32,
  +kk: U32,
  +left: Nat,
  +ee: {Nat.add(U32.to_nat(kk), Nat.add(U32.to_nat(run), 1n+List.length(&2, U32, ct))) == 64n : Nat},
  _hl: {Nat.is_le(Nat.add(U32.to_nat(run), 1n+List.length(&2, U32, ct)), left) == True{} : Bool}
) -> AclPos(kk, (run + 1 : U32), ct):
  +kn = U32.to_nat(kk)
  +rn = U32.to_nat(run)
  +ll = List.length(&2, U32, ct)
  +a2 = {Equal.trans(Bool, Nat.is_le(Nat.add(rn, 1n+ll), 64n), Nat.is_le(Nat.add(rn, 1n+ll), Nat.add(kn, Nat.add(rn,
    1n+ll))), True{}, Equal.cong(Nat, Bool, nn => Nat.is_le(Nat.add(rn, 1n+ll), nn), 64n, Nat.add(kn, Nat.add(rn,
    1n+ll)), Equal.sym(Nat, Nat.add(kn, Nat.add(rn, 1n+ll)), 64n, ee)), le_add_left(kn, Nat.add(rn, 1n+ll))) :
    {Nat.is_le(Nat.add(rn, 1n+ll), 64n) == True{} : Bool}}
  +er = {uadd(run, 1, R.le_trans(Nat.add(rn, 1n), Nat.add(rn, 1n+ll), 64n, R.le_add_mono(rn, 1n, 1n+ll, R.le_zero(ll)),
    a2)) : {U32.to_nat((run + 1 : U32)) == Nat.add(rn, 1n) : Nat}}
  +ea = {Equal.trans(Nat, Nat.add(U32.to_nat((run + 1 : U32)), ll), Nat.add(Nat.add(rn, 1n), ll), Nat.add(rn, 1n+ll),
    Equal.cong(Nat, Nat, nn => Nat.add(nn, ll), U32.to_nat((run + 1 : U32)), Nat.add(rn, 1n), er), R.add_assoc(rn, 1n,
    ll)) : {Nat.add(U32.to_nat((run + 1 : U32)), ll) == Nat.add(rn, 1n+ll) : Nat}}
  Equal.trans(Nat, Nat.add(kn, Nat.add(U32.to_nat((run + 1 : U32)), ll)), Nat.add(kn, Nat.add(rn, 1n+ll)), 64n,
    Equal.cong(Nat, Nat, nn => Nat.add(kn, nn), Nat.add(U32.to_nat((run + 1 : U32)), ll), Nat.add(rn, 1n+ll), ea), ee)

# the lookups left one coefficient on, past a zero
def acl_zero_left(
  +ct: List<&2, U32>,
  +run: U32,
  +kk: U32,
  +left: Nat,
  +ee: {Nat.add(U32.to_nat(kk), Nat.add(U32.to_nat(run), 1n+List.length(&2, U32, ct))) == 64n : Nat},
  hl: {Nat.is_le(Nat.add(U32.to_nat(run), 1n+List.length(&2, U32, ct)), left) == True{} : Bool}
) -> AclLeft((run + 1 : U32), ct, left):
  +kn = U32.to_nat(kk)
  +rn = U32.to_nat(run)
  +ll = List.length(&2, U32, ct)
  +a2 = {Equal.trans(Bool, Nat.is_le(Nat.add(rn, 1n+ll), 64n), Nat.is_le(Nat.add(rn, 1n+ll), Nat.add(kn, Nat.add(rn,
    1n+ll))), True{}, Equal.cong(Nat, Bool, nn => Nat.is_le(Nat.add(rn, 1n+ll), nn), 64n, Nat.add(kn, Nat.add(rn,
    1n+ll)), Equal.sym(Nat, Nat.add(kn, Nat.add(rn, 1n+ll)), 64n, ee)), le_add_left(kn, Nat.add(rn, 1n+ll))) :
    {Nat.is_le(Nat.add(rn, 1n+ll), 64n) == True{} : Bool}}
  +er = {uadd(run, 1, R.le_trans(Nat.add(rn, 1n), Nat.add(rn, 1n+ll), 64n, R.le_add_mono(rn, 1n, 1n+ll, R.le_zero(ll)),
    a2)) : {U32.to_nat((run + 1 : U32)) == Nat.add(rn, 1n) : Nat}}
  +ea = {Equal.trans(Nat, Nat.add(U32.to_nat((run + 1 : U32)), ll), Nat.add(Nat.add(rn, 1n), ll), Nat.add(rn, 1n+ll),
    Equal.cong(Nat, Nat, nn => Nat.add(nn, ll), U32.to_nat((run + 1 : U32)), Nat.add(rn, 1n), er), R.add_assoc(rn, 1n,
    ll)) : {Nat.add(U32.to_nat((run + 1 : U32)), ll) == Nat.add(rn, 1n+ll) : Nat}}
  Equal.trans(Bool, Nat.is_le(Nat.add(U32.to_nat((run + 1 : U32)), ll), left), Nat.is_le(Nat.add(rn, 1n+ll), left),
    True{}, Equal.cong(Nat, Bool, nn => Nat.is_le(nn, left), Nat.add(U32.to_nat((run + 1 : U32)), ll), Nat.add(rn,
    1n+ll), ea), hl)

# the type of acl_join's parameter hs
def acl_join.hs.ty(+_cc: U32, +_ct: List<&2, U32>, +_run: U32, +_pp: Jenc.Put, +_stk: List<&2, Laws.JTok>) -> Type:
  {Jenc.encode.ac(_cc <> _ct, _run, (acbk(), _pp)) == Jenc.encode.ac(_ct, 0, (acbk(), Laws.jpg.feed(W12.acbits(_stk),
    _pp))) : Array<U32> & Jenc.Put}

# the type of acl_join's parameter hw
def acl_join.hw.ty(+_kk: U32, +_left: Nat, +_stk: List<&2, Laws.JTok>, +_k2: U32, +_l2: Nat) -> Type:
  @ts: List<&2, Laws.JTok> -> {Laws.jpg.acwf(List.append(&2, Laws.JTok, _stk, ts), Laws.JAcSt{_kk, _left,
    U32.is_eq(_kk, 64)}) == Laws.jpg.acwf(ts, Laws.JAcSt{_k2, _l2, U32.is_eq(_k2, 64)}) : Bool}

# the tokens after a nonzero coefficient, joined to the AC coder's tokens after it
def acl_join(
  +cc: U32,
  +ct: List<&2, U32>,
  +run: U32,
  +kk: U32,
  +left: Nat,
  +pp: Jenc.Put,
  +stk: List<&2, Laws.JTok>,
  +k2: U32,
  +l2: Nat,
  hs: acl_join.hs.ty(cc, ct, run, pp, stk),
  hw: acl_join.hw.ty(kk, left, stk, k2, l2),
  res: AclRes(ct, 0, k2, l2, Laws.jpg.feed(W12.acbits(stk), pp))
) -> AclRes(cc <> ct, run, kk, left, pp):
  (+ts, eq, wf) = res
  +sb = W12.acbits(stk)
  (List.append(&2, Laws.JTok, stk, ts), Equal.trans(Array<U32> & Jenc.Put, Jenc.encode.ac(cc <> ct, run, (acbk(), pp)),
    Jenc.encode.ac(ct, 0, (acbk(), Laws.jpg.feed(sb, pp))), (acbk(), Laws.jpg.feed(W12.acbits(List.append(&2,
      Laws.JTok, stk,
    ts)), pp)), hs, Equal.trans(Array<U32> & Jenc.Put, Jenc.encode.ac(ct, 0, (acbk(), Laws.jpg.feed(sb, pp))), (acbk(),
    Laws.jpg.feed(W12.acbits(ts), Laws.jpg.feed(sb, pp))), (acbk(), Laws.jpg.feed(W12.acbits(List.append(&2,
      Laws.JTok, stk, ts)), pp)), eq,
    Equal.cong(Jenc.Put, Array<U32> & Jenc.Put, qq => (acbk(), qq), Laws.jpg.feed(W12.acbits(ts), Laws.jpg.feed(sb,
      pp)),
    Laws.jpg.feed(W12.acbits(List.append(&2, Laws.JTok, stk, ts)), pp), Equal.trans(Jenc.Put,
      Laws.jpg.feed(W12.acbits(ts), Laws.jpg.feed(sb,
    pp)), Laws.jpg.feed(List.append(&2, Bool, sb, W12.acbits(ts)), pp), Laws.jpg.feed(W12.acbits(List.append(&2,
      Laws.JTok, stk, ts)),
    pp), Equal.sym(Jenc.Put, Laws.jpg.feed(List.append(&2, Bool, sb, W12.acbits(ts)), pp),
      Laws.jpg.feed(W12.acbits(ts), Laws.jpg.feed(sb,
    pp)), W12.feed_app(sb, W12.acbits(ts), pp)), Equal.cong(List<&2, Bool>, Jenc.Put, xs => Laws.jpg.feed(xs, pp),
    List.append(&2, Bool, sb, W12.acbits(ts)), W12.acbits(List.append(&2, Laws.JTok, stk, ts)), Equal.sym(List<&2,
      Bool>,
    W12.acbits(List.append(&2, Laws.JTok, stk, ts)), List.append(&2, Bool, sb, W12.acbits(ts)), acbits_app(stk,
    ts))))))), Equal.trans(Bool, Laws.jpg.acwf(List.append(&2, Laws.JTok, stk, ts), Laws.JAcSt{kk, left, U32.is_eq(kk,
      64)}),
    Laws.jpg.acwf(ts, Laws.JAcSt{k2, l2, U32.is_eq(k2, 64)}), True{}, hw(ts), wf))

# a U32 compare at least 64, as Nat, fails below 64
def uge64_f(+xx: U32, hh: {Nat.is_lt(U32.to_nat(xx), 64n) == True{} : Bool}) -> {U32.is_ge(xx, 64) == False{} : Bool}:
  +xn = U32.to_nat(xx)
  Equal.trans(Bool, U32.is_ge(xx, 64), Cmp.is_ge(Nat.cmp(xn, 64n)), False{}, Equal.cong(Cmp, Bool, cc => Cmp.is_ge(cc),
    U32.cmp(xx, 64), Nat.cmp(xn, 64n), u_cmp(xx, 64)), Equal.trans(Bool, Cmp.is_ge(Nat.cmp(xn, 64n)), Nat.is_le(64n,
    xn), False{}, ge_le(xn, 64n), lt_nle(xn, 64n, hh)))

# the AC coder at a nonzero coefficient: ZRLs and its run and size token, then the rest
def acl_nz(
  +cc: U32,
  +ct: List<&2, U32>,
  +run: U32,
  +kk: U32,
  +left: Nat,
  +pp: Jenc.Put,
  +hz: {U32.is_eq(cc, 0) == False{} : Bool},
  +ee: {Nat.add(U32.to_nat(kk), Nat.add(U32.to_nat(run), 1n+List.length(&2, U32, ct))) == 64n : Nat},
  +hl: {Nat.is_le(Nat.add(U32.to_nat(run), 1n+List.length(&2, U32, ct)), left) == True{} : Bool},
  ih: AclIh(ct)
) -> AclRes(cc <> ct, run, kk, left, pp):
  +clip = Jenc.encode.clip(cc, 1023)
  +cat = Jenc.encode.cat(clip)
  +qq = U32.and(15, run)
  +sym = U32.or(cat, U32.shln(qq, 4n))
  +zj = U32.to_nat(U32.shrn(run, 4n))
  +ex = mz(U32.is_eq(cat, 0), cat, clip)
  +stk = stoks(zj, sym, cat, clip)
  +tk = {Laws.JTok{sym, ex} : Laws.JTok}
  +hcat = {memcat.ac(clip, clipnz.ac(cc, hz), clip.ac(cc)) : {Laws.jpg.memb(cat, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]) ==
    True{} : Bool}}
  +r0 = {symok.of(run, cat, hcat) : {symok(qq, cat) == True{} : Bool}}
  +a1 = Bool.not(U32.is_eq(sym, 0))
  +a2 = Bool.not(U32.is_eq(sym, 240))
  +a3 = U32.is_eq(U32.and(15, sym), cat)
  +a4 = U32.is_eq(U32.shrn(sym, 4n), qq)
  +hm = {W12.and_l(Laws.jpg.memb(sym, Jenc.encode.acsyms()), Bool.and(a1, Bool.and(a2, Bool.and(a3, a4))),
    r0) : {Laws.jpg.memb(sym,
    Jenc.encode.acsyms()) == True{} : Bool}}
  +r1 = {W12.and_r(Laws.jpg.memb(sym, Jenc.encode.acsyms()), Bool.and(a1, Bool.and(a2, Bool.and(a3, a4))),
    r0) : {Bool.and(a1,
    Bool.and(a2, Bool.and(a3, a4))) == True{} : Bool}}
  +he = {not_t(U32.is_eq(sym, 0), W12.and_l(a1, Bool.and(a2, Bool.and(a3, a4)), r1)) : {U32.is_eq(sym, 0) == False{} :
    Bool}}
  +r2 = {W12.and_r(a1, Bool.and(a2, Bool.and(a3, a4)), r1) : {Bool.and(a2, Bool.and(a3, a4)) == True{} : Bool}}
  +h240 = {not_t(U32.is_eq(sym, 240), W12.and_l(a2, Bool.and(a3, a4), r2)) : {U32.is_eq(sym, 240) == False{} : Bool}}
  +r3 = {W12.and_r(a2, Bool.and(a3, a4), r2) : {Bool.and(a3, a4) == True{} : Bool}}
  +ec = {U32L.ueq(U32.and(15, sym), cat, W12.and_l(a3, a4, r3)) : {U32.and(15, sym) == cat : U32}}
  +eq4 = {U32L.ueq(U32.shrn(sym, 4n), qq, W12.and_r(a3, a4, r3)) : {U32.shrn(sym, 4n) == qq : U32}}
  +kn = U32.to_nat(kk)
  +rn = U32.to_nat(run)
  +qn = U32.to_nat(qq)
  +sn = sixteen(zj)
  +ll = List.length(&2, U32, ct)
  +en1 = {n1(run) : {rn == Nat.add(qn, sn) : Nat}}
  +eas = {R.add_assoc(kn, rn, 1n+ll) : {Nat.add(Nat.add(kn, rn), 1n+ll) == Nat.add(kn, Nat.add(rn, 1n+ll)) : Nat}}
  +d1 = {Equal.trans(Bool, Nat.is_lt(Nat.add(kn, rn), 64n), Nat.is_lt(Nat.add(kn, rn), Nat.add(Nat.add(kn, rn), 1n+ll)),
    True{}, Equal.cong(Nat, Bool, nn => Nat.is_lt(Nat.add(kn, rn), nn), 64n, Nat.add(Nat.add(kn, rn), 1n+ll),
    Equal.sym(Nat, Nat.add(Nat.add(kn, rn), 1n+ll), 64n, Equal.trans(Nat, Nat.add(Nat.add(kn, rn), 1n+ll), Nat.add(kn,
    Nat.add(rn, 1n+ll)), 64n, eas, ee))), lt_add_pos(Nat.add(kn, rn), 1n+ll, {==})) : {Nat.is_lt(Nat.add(kn, rn), 64n)
    == True{} : Bool}}
  +slr = {Equal.trans(Bool, Nat.is_le(sn, rn), Nat.is_le(sn, Nat.add(qn, sn)), True{}, Equal.cong(Nat, Bool, nn =>
    Nat.is_le(sn, nn), rn, Nat.add(qn, sn), en1), le_add_left(qn, sn)) : {Nat.is_le(sn, rn) == True{} : Bool}}
  +d2 = {R.le_lt_trans(Nat.add(kn, sn), Nat.add(kn, rn), 64n, R.le_add_mono(kn, sn, rn, slr), d1) :
    {Nat.is_lt(Nat.add(kn, sn), 64n) == True{} : Bool}}
  +zlr = {R.le_trans(zj, sn, rn, le_sixteen(zj), slr) : {Nat.is_le(zj, rn) == True{} : Bool}}
  +d3 = {R.le_trans(Nat.add(zj, 1n+ll), Nat.add(rn, 1n+ll), left, le_addr(zj, rn, 1n+ll, zlr), hl) :
    {Nat.is_le(Nat.add(zj, 1n+ll), left) == True{} : Bool}}
  +hz3 = {R.le_add_r(zj, 1n+ll, left, d3) : {Nat.is_le(zj, left) == True{} : Bool}}
  +lz = npreds(zj, left)
  +hlz = {npl(zj, 1n+ll, left, d3) : {Nat.is_le(1n+ll, lz) == True{} : Bool}}
  +hp = {pos_of_le(ll, lz, hlz) : {Nat.is_lt(0n, lz) == True{} : Bool}}
  +h2 = {le_npred(ll, lz, hlz) : {Nat.is_le(ll, Laws.jpg.npred(lz)) == True{} : Bool}}
  +kzz = kz(zj, kk)
  +ekz = {kz_nat(zj, kk, d2) : {U32.to_nat(kzz) == Nat.add(kn, sn) : Nat}}
  +esum = {Equal.trans(Nat, Nat.add(U32.to_nat(kzz), qn), Nat.add(Nat.add(kn, sn), qn), Nat.add(kn, rn), Equal.cong(Nat,
    Nat, nn => Nat.add(nn, qn), U32.to_nat(kzz), Nat.add(kn, sn), ekz), Equal.trans(Nat, Nat.add(Nat.add(kn, sn), qn),
    Nat.add(kn, Nat.add(sn, qn)), Nat.add(kn, rn), R.add_assoc(kn, sn, qn), Equal.cong(Nat, Nat, nn => Nat.add(kn, nn),
    Nat.add(sn, qn), rn, Equal.trans(Nat, Nat.add(sn, qn), Nat.add(qn, sn), rn, R.add_comm(sn, qn), Equal.sym(Nat, rn,
    Nat.add(qn, sn), en1))))) : {Nat.add(U32.to_nat(kzz), qn) == Nat.add(kn, rn) : Nat}}
  +x1 = (kzz + qq : U32)
  +ex1 = {Equal.trans(Nat, U32.to_nat(x1), Nat.add(U32.to_nat(kzz), qn), Nat.add(kn, rn), uadd(kzz, qq,
    Equal.trans(Bool, Nat.is_le(Nat.add(U32.to_nat(kzz), qn), 64n), Nat.is_le(Nat.add(kn, rn), 64n), True{},
    Equal.cong(Nat, Bool, nn => Nat.is_le(nn, 64n), Nat.add(U32.to_nat(kzz), qn), Nat.add(kn, rn), esum), R.lt_le(
    Nat.add(kn, rn), 64n, d1))), esum) : {U32.to_nat(x1) == Nat.add(kn, rn) : Nat}}
  +xlt = {Equal.trans(Bool, Nat.is_lt(U32.to_nat(x1), 64n), Nat.is_lt(Nat.add(kn, rn), 64n), True{}, Equal.cong(Nat,
    Bool, nn => Nat.is_lt(nn, 64n), U32.to_nat(x1), Nat.add(kn, rn), ex1), d1) : {Nat.is_lt(U32.to_nat(x1), 64n) ==
    True{} : Bool}}
  +ex4 = {Equal.cong(U32, U32, uu => (kzz + uu : U32), U32.shrn(sym, 4n), qq, eq4) : {(kzz + U32.shrn(sym, 4n) : U32) ==
    x1 : U32}}
  +hge = {Equal.trans(Bool, U32.is_ge((kzz + U32.shrn(sym, 4n) : U32), 64), U32.is_ge(x1, 64), False{}, Equal.cong(U32,
    Bool, uu => U32.is_ge(uu, 64), (kzz + U32.shrn(sym, 4n) : U32), x1, ex4), uge64_f(x1, xlt)) : {U32.is_ge((kzz +
    U32.shrn(sym, 4n) : U32), 64) == False{} : Bool}}
  +h1 = {Equal.trans(Bool, U32.is_eq(U32.and(15, sym), 0), U32.is_eq(cat, 0), False{}, Equal.cong(U32, Bool, uu =>
    U32.is_eq(uu, 0), U32.and(15, sym), cat, ec), memb_nz(cat, hcat)) : {U32.is_eq(U32.and(15, sym), 0) == False{} :
    Bool}}
  +h3 = {Equal.trans(Bool, Nat.is_eq(List.length(&2, Bool, ex), U32.to_nat(U32.and(15, sym))), Nat.is_eq(List.length(&2,
    Bool, ex), U32.to_nat(cat)), True{}, Equal.cong(U32, Bool, uu => Nat.is_eq(List.length(&2, Bool, ex),
      U32.to_nat(uu)),
    U32.and(15, sym), cat, ec), mzlen(U32.is_eq(cat, 0), cat, clip, {==})) : {Nat.is_eq(List.length(&2, Bool, ex),
    U32.to_nat(U32.and(15, sym))) == True{} : Bool}}
  +k2 = ((kzz + U32.shrn(sym, 4n) : U32) + 1 : U32)
  +y1 = (kzz + U32.shrn(sym, 4n) : U32)
  +ey1 = {Equal.trans(Nat, U32.to_nat(y1), U32.to_nat(x1), Nat.add(kn, rn), Equal.cong(U32, Nat, uu => U32.to_nat(uu),
    y1, x1, ex4), ex1) : {U32.to_nat(y1) == Nat.add(kn, rn) : Nat}}
  +ek2 = {Equal.trans(Nat, U32.to_nat(k2), Nat.add(U32.to_nat(y1), 1n), Nat.add(Nat.add(kn, rn), 1n), uadd(y1, 1,
    Equal.trans(Bool, Nat.is_le(Nat.add(U32.to_nat(y1), 1n), 64n), Nat.is_le(Nat.add(Nat.add(kn, rn), 1n), 64n), True{},
    Equal.cong(Nat, Bool, nn => Nat.is_le(Nat.add(nn, 1n), 64n), U32.to_nat(y1), Nat.add(kn, rn), ey1), lt_add1(
    Nat.add(kn, rn), 64n, d1))), Equal.cong(Nat, Nat, nn => Nat.add(nn, 1n), U32.to_nat(y1), Nat.add(kn, rn), ey1)) :
    {U32.to_nat(k2) == Nat.add(Nat.add(kn, rn), 1n) : Nat}}
  +e2 = {Equal.trans(Nat, Nat.add(U32.to_nat(k2), ll), Nat.add(Nat.add(Nat.add(kn, rn), 1n), ll), 64n, Equal.cong(Nat,
    Nat, nn => Nat.add(nn, ll), U32.to_nat(k2), Nat.add(Nat.add(kn, rn), 1n), ek2), Equal.trans(Nat, Nat.add(Nat.add(
    Nat.add(kn, rn), 1n), ll), Nat.add(Nat.add(kn, rn), 1n+ll), 64n, R.add_assoc(Nat.add(kn, rn), 1n, ll),
    Equal.trans(Nat, Nat.add(Nat.add(kn, rn), 1n+ll), Nat.add(kn, Nat.add(rn, 1n+ll)), 64n, eas, ee))) :
    {Nat.add(U32.to_nat(k2), ll) == 64n : Nat}}
  +hk = {R.le_lt_trans(kn, Nat.add(kn, rn), 64n, R.le_add_more(kn, kn, rn, R.le_refl(kn)), d1) : {Nat.is_lt(kn, 64n) ==
    True{} : Bool}}
  +hE = {Equal.trans(Bool, U32.is_eq(kk, 64), Nat.is_eq(kn, 64n), False{}, R.u32_eq(kk, 64), lt_ne(kn, 64n, hk)) :
    {U32.is_eq(kk, 64) == False{} : Bool}}
  +hs = {Equal.trans(Array<U32> & Jenc.Put, Jenc.encode.ac(ct, Jenc.encode.ac.run(U32.is_eq(cc, 0), run),
    Jenc.encode.ac.at(U32.is_eq(cc, 0), cc, run, (acbk(), pp))), Jenc.encode.ac(ct, 0, Jenc.encode.ac.step(cc, run,
    (acbk(), pp))), Jenc.encode.ac(ct, 0, (acbk(), Laws.jpg.feed(W12.acbits(stk), pp))), Equal.cong(Bool,
    Array<U32> & Jenc.Put, zz => Jenc.encode.ac(ct, Jenc.encode.ac.run(zz, run), Jenc.encode.ac.at(zz, cc, run,
    (acbk(), pp))), U32.is_eq(cc, 0), False{}, hz), Equal.cong(Array<U32> & Jenc.Put, Array<U32> & Jenc.Put, st =>
    Jenc.encode.ac(ct, 0, st), Jenc.encode.ac.step(cc, run, (acbk(), pp)), (acbk(), Laws.jpg.feed(W12.acbits(stk), pp)),
    step_eq(cc, run, pp))) : {Jenc.encode.ac(cc <> ct, run, (acbk(), pp)) == Jenc.encode.ac(ct, 0, (acbk(),
    Laws.jpg.feed(W12.acbits(stk), pp))) : Array<U32> & Jenc.Put}}
  +zt = zrltoks(zj)
  acl_join(cc, ct, run, kk, left, pp, stk, k2, Laws.jpg.npred(lz), hs, +ts => Equal.trans(Bool,
    Laws.jpg.acwf(List.append(&2, Laws.JTok,
    stk, ts), Laws.JAcSt{kk, left, U32.is_eq(kk, 64)}), Laws.jpg.acwf(List.append(&2, Laws.JTok, stk, ts),
      Laws.JAcSt{kk, left, False{}}),
    Laws.jpg.acwf(ts, Laws.JAcSt{k2, Laws.jpg.npred(lz), U32.is_eq(k2, 64)}), Equal.cong(Bool, Bool,
      bb => Laws.jpg.acwf(List.append(&2, Laws.JTok,
    stk, ts), Laws.JAcSt{kk, left, bb}), U32.is_eq(kk, 64), False{}, hE), Equal.trans(Bool,
      Laws.jpg.acwf(List.append(&2, Laws.JTok,
    stk, ts), Laws.JAcSt{kk, left, False{}}), Laws.jpg.acwf(List.append(&2, Laws.JTok, zt, tk <> ts), Laws.JAcSt{kk,
      left, False{}}),
    Laws.jpg.acwf(ts, Laws.JAcSt{k2, Laws.jpg.npred(lz), U32.is_eq(k2, 64)}), Equal.cong(List<&2, Laws.JTok>, Bool,
      xs => Laws.jpg.acwf(xs,
    Laws.JAcSt{kk, left, False{}}), List.append(&2, Laws.JTok, stk, ts), List.append(&2, Laws.JTok, zt, tk <> ts),
      app_t(zt, [tk],
    ts)), Equal.trans(Bool, Laws.jpg.acwf(List.append(&2, Laws.JTok, zt, tk <> ts), Laws.JAcSt{kk, left, False{}}),
      Laws.jpg.acwf(tk <> ts,
    Laws.JAcSt{kzz, lz, False{}}), Laws.jpg.acwf(ts, Laws.JAcSt{k2, Laws.jpg.npred(lz), U32.is_eq(k2, 64)}), zrlwf(zj,
      kk, left, tk <> ts, d2,
    hz3), symwf(sym, ex, kzz, lz, ts, he, h240, hm, hp, h1, hge, h3)))), ih(0, k2, Laws.jpg.npred(lz),
      Laws.jpg.feed(W12.acbits(stk),
    pp), e2, h2))

# the AC coder at a coefficient, by whether it is zero
def acl_cons(
  zero: Bool,
  +cc: U32,
  +ct: List<&2, U32>,
  +run: U32,
  +kk: U32,
  +left: Nat,
  +pp: Jenc.Put,
  +hz: {U32.is_eq(cc, 0) == zero : Bool},
  +ee: {Nat.add(U32.to_nat(kk), Nat.add(U32.to_nat(run), 1n+List.length(&2, U32, ct))) == 64n : Nat},
  +hl: {Nat.is_le(Nat.add(U32.to_nat(run), 1n+List.length(&2, U32, ct)), left) == True{} : Bool},
  ih: AclIh(ct)
) -> AclRes(cc <> ct, run, kk, left, pp):
  match zero:
    case True{}:
      acl_zero(cc, ct, run, kk, left, pp, hz, ih((run + 1 : U32), kk, left, pp, acl_zero_pos(ct, run, kk, left, ee, hl),
        acl_zero_left(ct, run, kk, left, ee, hl)))
    case False{}:
      acl_nz(cc, ct, run, kk, left, pp, hz, ee, hl, ih)

# the AC coder over coefficients from a state that keeps the invariant writes tokens the decoder's loop reads in full
def acl(
  zz: List<&2, U32>,
  +run: U32,
  +kk: U32,
  +left: Nat,
  +pp: Jenc.Put,
  ee: AclPos(kk, run, zz),
  hl: AclLeft(run, zz, left)
) -> AclRes(zz, run, kk, left, pp):
  match zz:
    case Nil{}:
      acl_nil(U32.is_gt(run, 0), run, kk, left, pp, {==}, ee, hl)
    case +cc <> +ct:
      acl_cons(U32.is_eq(cc, 0), cc, ct, run, kk, left, pp, {==}, ee, hl, r2 => k2 => l2 => p2 => e2 => h2 => acl(ct,
        r2,
        k2, l2, p2, e2, h2))

# the encoder's books, written out
def book() -> Jenc.Book:
  Jenc.Book{dcbk(), acbk()}

# one block the encoder codes: a token the decoder reads whole, fed to the writer, the books back, and the next
# predictor below 2048
def BlkOut(+pred: U32, +pp: Jenc.Put, -zz: List<&2, U32>) -> Type:
  &bt: Laws.JBlkTok -> &dd: U32 -> &_e: {Jenc.encode.block.go(book(), pp, pred, zz) == (book(), dd,
    Laws.jpg.feed(W12.blkbits(bt),
    pp)) : Jenc.Book & U32 & Jenc.Put} -> &_h: {U32.is_lt(dd, 2048) == True{} : Bool} -> {Laws.jpg.blkwf(bt) == True{} :
    Bool}

# the type of blk_fin's parameter edc
def blk_fin.edc.ty(+_dc0: U32, +_pred: U32, +_pp: Jenc.Put, +_dcs: U32, +_dcx: List<&2, Bool>) -> Type:
  {Jenc.encode.dcdiff(dcbk(), _pp, Jenc.encode.dcbias(_dc0), _pred) == (dcbk(), Laws.jpg.feed(List.append(&2, Bool,
    W12.code.dc(_dcs), _dcx), _pp)) : Array<U32> & Jenc.Put}

# the block's AC part coded after its DC token
def blk_fin(
  +dc0: U32,
  +rest: List<&2, U32>,
  +pred: U32,
  +pp: Jenc.Put,
  +dcs: U32,
  +dcx: List<&2, Bool>,
  edc: blk_fin.edc.ty(dc0, pred, pp, dcs, dcx),
  hm: {Laws.jpg.memb(dcs, Jenc.encode.dcsyms()) == True{} : Bool},
  hl: {Nat.is_eq(List.length(&2, Bool, dcx), U32.to_nat(dcs)) == True{} : Bool},
  ares: AclRes(rest, 0, 1, 63n, Laws.jpg.feed(List.append(&2, Bool, W12.code.dc(dcs), dcx), pp))
) -> BlkOut(pred, pp, dc0 <> rest):
  (+ts, eac, wf) = ares
  +dd = Jenc.encode.dcbias(dc0)
  +cd = List.append(&2, Bool, W12.code.dc(dcs), dcx)
  +p1 = Laws.jpg.feed(cd, pp)
  +ab = W12.acbits(ts)
  +bt = {Laws.JBlkTok{dcs, dcx, ts} : Laws.JBlkTok}
  (bt, dd, Equal.trans(Jenc.Book & U32 & Jenc.Put, Jenc.encode.block.dc(Jenc.encode.dcdiff(dcbk(), pp, dd, pred),
    acbk(), dd, rest), Jenc.encode.block.dc((dcbk(), p1), acbk(), dd, rest), (book(), dd, Laws.jpg.feed(
    W12.blkbits(bt), pp)), Equal.cong(Array<U32> & Jenc.Put, Jenc.Book & U32 & Jenc.Put, gg => Jenc.encode.block.dc(gg,
    acbk(), dd, rest), Jenc.encode.dcdiff(dcbk(), pp, dd, pred), (dcbk(), p1), edc), Equal.trans(Jenc.Book &
    U32 & Jenc.Put, Jenc.encode.block.join(Jenc.encode.ac(rest, 0, (acbk(), p1)), dcbk(), dd),
    Jenc.encode.block.join((acbk(), Laws.jpg.feed(ab, p1)), dcbk(), dd), (book(), dd, Laws.jpg.feed(W12.blkbits(bt),
      pp)),
    Equal.cong(Array<U32> & Jenc.Put, Jenc.Book & U32 & Jenc.Put, gg => Jenc.encode.block.join(gg, dcbk(), dd),
    Jenc.encode.ac(rest, 0, (acbk(), p1)), (acbk(), Laws.jpg.feed(ab, p1)), eac), Equal.cong(Jenc.Put, Jenc.Book & U32 &
    Jenc.Put, qq => (book(), dd, qq), Laws.jpg.feed(ab, p1), Laws.jpg.feed(W12.blkbits(bt), pp), Equal.trans(Jenc.Put,
      Laws.jpg.feed(ab,
    p1), Laws.jpg.feed(List.append(&2, Bool, cd, ab), pp), Laws.jpg.feed(W12.blkbits(bt), pp), Equal.sym(Jenc.Put,
      Laws.jpg.feed(
    List.append(&2, Bool, cd, ab), pp), Laws.jpg.feed(ab, p1), W12.feed_app(cd, ab, pp)), Equal.cong(List<&2, Bool>,
      Jenc.Put,
    xs => Laws.jpg.feed(xs, pp), List.append(&2, Bool, cd, ab), W12.blkbits(bt), W12.app_assoc(W12.code.dc(dcs), dcx,
      ab)))))),
    bias_lt(dc0), and_tt(Laws.jpg.memb(dcs, Jenc.encode.dcsyms()), Bool.and(Nat.is_eq(List.length(&2, Bool, dcx),
    U32.to_nat(dcs)), Laws.jpg.acwf(ts, Laws.JAcSt{1, 63n, False{}})), hm, and_tt(Nat.is_eq(List.length(&2, Bool, dcx),
    U32.to_nat(dcs)), Laws.jpg.acwf(ts, Laws.JAcSt{1, 63n, False{}}), hl, wf)))

# the block after its DC token is named
def blk_dc(
  +dc0: U32,
  +rest: List<&2, U32>,
  +pred: U32,
  +pp: Jenc.Put,
  +hr: {List.length(&2, U32, rest) == 63n : Nat},
  dres: DcRes(Jenc.encode.dcbias(dc0), pred, pp)
) -> BlkOut(pred, pp, dc0 <> rest):
  (+dcs, +dcx, edc, hm, hl) = dres
  +p1 = Laws.jpg.feed(List.append(&2, Bool, W12.code.dc(dcs), dcx), pp)
  blk_fin(dc0, rest, pred, pp, dcs, dcx, edc, hm, hl, acl(rest, 0, 1, 63n, p1, Equal.cong(Nat, Nat, nn => Nat.add(1n,
    Nat.add(0n, nn)), List.length(&2, U32, rest), 63n, hr), Equal.trans(Bool, Nat.is_le(List.length(&2, U32, rest),
      63n),
    Nat.is_le(63n, 63n), True{}, Equal.cong(Nat, Bool, nn => Nat.is_le(nn, 63n), List.length(&2, U32, rest), 63n, hr),
    {==})))

# 0 is not a successor
def zero_ne(+nn: Nat, ee: {0n == 1n+nn : Nat}) -> Empty:
  true_false(Equal.cong(Nat, Bool, xx => Nat.is_eq(xx, 0n), 0n, 1n+nn, ee))

# a block of 64 coefficients the encoder codes, from a predictor below 2048
def blk(
  zz: List<&2, U32>,
  +pred: U32,
  +pp: Jenc.Put,
  hl: {List.length(&2, U32, zz) == 64n : Nat},
  hp: {U32.is_lt(pred, 2048) == True{} : Bool}
) -> BlkOut(pred, pp, zz):
  match zz:
    case Nil{}:
      Empty.absurd(BlkOut(pred, pp, []), zero_ne(63n, hl))
    case +dc0 <> +rest:
      blk_dc(dc0, rest, pred, pp, Equal.cong(Nat, Nat, nn => Laws.jpg.npred(nn), 1n+List.length(&2, U32, rest), 64n,
        hl),
        dcres(Jenc.encode.dcbias(dc0), pred, pp, bias_lt(dc0), hp))

# one value read at an index joins the values read so far, the array handed on
def vals.put(got: Array<U32> & U32, acc: List<&2, U32>) -> Array<U32> & List<&2, U32>:
  (aa, +vv) = got
  (aa, List.append(&2, U32, acc, [vv]))

# the read at one index
def vals.step(st: Array<U32> & List<&2, U32>, +gg: U32) -> Array<U32> & List<&2, U32>:
  (aa, acc) = st
  vals.put(Array.get(U32, aa, gg), acc)

# the values read, the array dropped
def vals.end(st: Array<U32> & List<&2, U32>) -> List<&2, U32>:
  (aa, acc) = st
  +_s = Jenc.encode.pix.sink(aa)
  acc

# the values an array holds at indexes, in order, after acc
def vals(gs: List<&2, U32>, st: Array<U32> & List<&2, U32>) -> List<&2, U32>:
  match gs:
    case Nil{}:
      vals.end(st)
    case +gg <> gt:
      vals(gt, vals.step(st, gg))

# U32 lists regrouped
def app_u(
  xs: List<&2, U32>,
  +ys: List<&2, U32>,
  +zs: List<&2, U32>
) -> {List.append(&2, U32, List.append(&2, U32, xs, ys), zs) == List.append(&2, U32, xs, List.append(&2, U32, ys,
  zs)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case +hh <> tt:
      Equal.cong(List<&2, U32>, List<&2, U32>, ws => hh <> ws, List.append(&2, U32, List.append(&2, U32, tt, ys), zs),
        List.append(&2, U32, tt, List.append(&2, U32, ys, zs)), app_u(tt, ys, zs))

# a U32 list with nothing after it
def app_nil_u(xs: List<&2, U32>) -> {List.append(&2, U32, xs, []) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case +hh <> tt:
      Equal.cong(List<&2, U32>, List<&2, U32>, ws => hh <> ws, List.append(&2, U32, tt, []), tt, app_nil_u(tt))

# the values after acc and pre, for the rest of the indexes
def VaccIh(-gt: List<&2, U32>, +_acc: List<&2, U32>) -> Type:
  @a2: Array<U32> -> @p2: List<&2, U32> -> {vals(gt, (a2, List.append(&2, U32, _acc, p2))) == List.append(&2, U32, _acc,
    vals(gt, (a2, p2))) : List<&2, U32>}

# one read joins acc and pre, whatever it returned
def vacc.got(
  got: Array<U32> & U32,
  +gt: List<&2, U32>,
  +acc: List<&2, U32>,
  +pre: List<&2, U32>,
  ih: VaccIh(gt, acc)
) -> {vals(gt, vals.put(got, List.append(&2, U32, acc, pre))) == List.append(&2, U32, acc, vals(gt, vals.put(got,
  pre))) : List<&2, U32>}:
  match got:
    case (a2, +vv):
      Equal.trans(List<&2, U32>, vals(gt, (a2, List.append(&2, U32, List.append(&2, U32, acc, pre), [vv]))), vals(gt,
        (a2, List.append(&2, U32, acc, List.append(&2, U32, pre, [vv])))), List.append(&2, U32, acc, vals(gt, (a2,
        List.append(&2, U32, pre, [vv])))), Equal.cong(List<&2, U32>, List<&2, U32>, ws => vals(gt, (a2, ws)),
        List.append(&2, U32, List.append(&2, U32, acc, pre), [vv]), List.append(&2, U32, acc, List.append(&2, U32, pre,
        [vv])), app_u(acc, pre, [vv])), ih(a2, List.append(&2, U32, pre, [vv])))

# the values an array holds at indexes, after acc and pre, are acc and then the values after pre
def vacc2(
  gs: List<&2, U32>,
  aa: Array<U32>,
  +acc: List<&2, U32>,
  +pre: List<&2, U32>
) -> {vals(gs, (aa, List.append(&2, U32, acc, pre))) == List.append(&2, U32, acc, vals(gs, (aa, pre))) : List<&2, U32>}:
  match gs:
    case Nil{}:
      {==}
    case +gg <> +gt:
      vacc.got(Array.get(U32, aa, gg), gt, acc, pre, a2 => p2 => vacc2(gt, a2, acc, p2))

# the values an array holds at indexes, after acc, are acc and then the values
def vacc(
  gs: List<&2, U32>,
  aa: Array<U32>,
  +acc: List<&2, U32>
) -> {vals(gs, (aa, acc)) == List.append(&2, U32, acc, vals(gs, (aa, []))) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, vals(gs, (aa, acc)), vals(gs, (aa, List.append(&2, U32, acc, []))), List.append(&2, U32,
    acc, vals(gs, (aa, []))), Equal.cong(List<&2, U32>, List<&2, U32>, ws => vals(gs, (aa, ws)), acc, List.append(&2,
    U32, acc, []), Equal.sym(List<&2, U32>, List.append(&2, U32, acc, []), acc, app_nil_u(acc))), vacc2(gs, aa, acc,
      []))

# the rest of the scan, from any state, is the AC coder over the values it reads
def SacIh(-gt: List<&2, U32>) -> Type:
  @a2: Array<U32> -> @r2: U32 -> @c2: Array<U32> -> @b2: Jenc.Put -> {Jenc.encode.scan.ac(gt, Jenc.Scan{a2, r2, c2, b2})
    == Jenc.encode.ac(vals(gt, (a2, [])), r2, (c2, b2)) : Array<U32> & Jenc.Put}

# the scan after a nonzero coefficient, whatever the AC coder handed back
def sac.hit(
  st: Array<U32> & Jenc.Put,
  a2: Array<U32>,
  +gt: List<&2, U32>,
  ih: SacIh(gt)
) -> {Jenc.encode.scan.ac(gt, Jenc.encode.scan.hit(st, a2)) == Jenc.encode.ac(vals(gt, (a2, [])), 0,
  st) : Array<U32> & Jenc.Put}:
  match st:
    case (c3, b3):
      ih(a2, 0, c3, b3)

# the scan at a coefficient, by whether it is zero
def sac.z(
  zz: Bool,
  +vv: U32,
  a2: Array<U32>,
  +gt: List<&2, U32>,
  +run: U32,
  ac: Array<U32>,
  +bit: Jenc.Put,
  ih: SacIh(gt)
) -> {Jenc.encode.scan.ac(gt, Jenc.encode.scan.bump(zz, Jenc.Scan{a2, run, ac, bit}, vv)) == Jenc.encode.ac(vals(gt,
  (a2, [])), Jenc.encode.ac.run(zz, run), Jenc.encode.ac.at(zz, vv, run, (ac, bit))) : Array<U32> & Jenc.Put}:
  match zz:
    case True{}:
      ih(a2, (run + 1 : U32), ac, bit)
    case False{}:
      sac.hit(Jenc.encode.ac.step(vv, run, (ac, bit)), a2, gt, ih)

# the values after one read, for an array known equal to another
def vacc_tr(
  -a2: Array<U32>,
  bb: Array<U32>,
  ee: {bb == a2 : Array<U32>},
  +gt: List<&2, U32>,
  +vv: U32
) -> {vals(gt, (a2, [vv])) == vv <> vals(gt, (a2, [])) : List<&2, U32>}:
  %ee : {vals(gt, (_, [vv])) == vv <> vals(gt, (_, [])) : List<&2, U32>}
  vacc(gt, bb, [vv])

# the scan at a coefficient, for an array known equal to another
def sacz_tr(
  zz: Bool,
  +vv: U32,
  -a2: Array<U32>,
  bb: Array<U32>,
  ee: {bb == a2 : Array<U32>},
  +gt: List<&2, U32>,
  +run: U32,
  ac: Array<U32>,
  +bit: Jenc.Put,
  ih: SacIh(gt)
) -> {Jenc.encode.scan.ac(gt, Jenc.encode.scan.bump(zz, Jenc.Scan{a2, run, ac, bit}, vv)) == Jenc.encode.ac(vals(gt,
  (a2, [])), Jenc.encode.ac.run(zz, run), Jenc.encode.ac.at(zz, vv, run, (ac, bit))) : Array<U32> & Jenc.Put}:
  %ee : {Jenc.encode.scan.ac(gt, Jenc.encode.scan.bump(zz, Jenc.Scan{_, run, ac, bit}, vv)) == Jenc.encode.ac(vals(gt,
    (_, [])), Jenc.encode.ac.run(zz, run), Jenc.encode.ac.at(zz, vv, run, (ac, bit))) : Array<U32> & Jenc.Put}
  sac.z(zz, vv, bb, gt, run, ac, bit, ih)

# the scan at an index, from two copies of the array read
def sac.d(
  -a2: Array<U32>,
  +vv: U32,
  +gt: List<&2, U32>,
  +run: U32,
  ac: Array<U32>,
  +bit: Jenc.Put,
  ih: SacIh(gt),
  dd: W10.Dup(a2)
) -> {Jenc.encode.scan.ac(gt, Jenc.encode.scan.bump(U32.is_eq(vv, 0), Jenc.Scan{a2, run, ac, bit},
  vv)) == Jenc.encode.ac(vals(gt, (a2, [vv])), run, (ac, bit)) : Array<U32> & Jenc.Put}:
  (b1, b2, e1, e2) = dd
  Equal.trans(Array<U32> & Jenc.Put, Jenc.encode.scan.ac(gt, Jenc.encode.scan.bump(U32.is_eq(vv, 0), Jenc.Scan{a2, run,
    ac, bit}, vv)), Jenc.encode.ac(vv <> vals(gt, (a2, [])), run, (ac, bit)), Jenc.encode.ac(vals(gt, (a2, [vv])), run,
    (ac, bit)), sacz_tr(U32.is_eq(vv, 0), vv, a2, b1, e1, gt, run, ac, bit, ih), Equal.cong(List<&2, U32>, Array<U32> &
    Jenc.Put, ws => Jenc.encode.ac(ws, run, (ac, bit)), vv <> vals(gt, (a2, [])), vals(gt, (a2, [vv])), Equal.sym(
    List<&2, U32>, vals(gt, (a2, [vv])), vv <> vals(gt, (a2, [])), vacc_tr(a2, b2, e2, gt, vv))))

# the scan at an index, whatever the read returned
def sac.got(
  got: Array<U32> & U32,
  +gt: List<&2, U32>,
  +run: U32,
  ac: Array<U32>,
  +bit: Jenc.Put,
  ih: SacIh(gt)
) -> {Jenc.encode.scan.ac(gt, Jenc.encode.scan.val(got, run, (ac, bit))) == Jenc.encode.ac(vals(gt, vals.put(got,
  [])), run, (ac, bit)) : Array<U32> & Jenc.Put}:
  match got:
    case (a2, +vv):
      sac.d(a2, vv, gt, run, ac, bit, ih, W10.dup(a2))

# the scan's AC part is the AC coder over the values it reads
def sac(
  gs: List<&2, U32>,
  aa: Array<U32>,
  +run: U32,
  ac: Array<U32>,
  +bit: Jenc.Put
) -> {Jenc.encode.scan.ac(gs, Jenc.Scan{aa, run, ac, bit}) == Jenc.encode.ac(vals(gs, (aa, [])), run, (ac,
  bit)) : Array<U32> & Jenc.Put}:
  match gs:
    case Nil{}:
      {==}
    case +gg <> +gt:
      sac.got(Array.get(U32, aa, gg), gt, run, ac, bit, a2 => r2 => c2 => b2 => sac(gt, a2, r2, c2, b2))

# the scan's and the block coder's last step build the same books, whatever the AC coder handed back
def book_join(
  got: Array<U32> & Jenc.Put,
  dc: Array<U32>,
  +dd: U32
) -> {Jenc.encode.scan.book(got, dc, dd) == Jenc.encode.block.join(got, dc, dd) : Jenc.Book & U32 & Jenc.Put}:
  match got:
    case (_a, _p):
      {==}

# the scan's AC part, for arrays known equal to others
def sac_tr(
  +gt: List<&2, U32>,
  -a2: Array<U32>,
  -ac: Array<U32>,
  bb: Array<U32>,
  cc: Array<U32>,
  eb: {bb == a2 : Array<U32>},
  ec: {cc == ac : Array<U32>},
  +p2: Jenc.Put
) -> {Jenc.encode.scan.ac(gt, Jenc.Scan{a2, 0, ac, p2}) == Jenc.encode.ac(vals(gt, (a2, [])), 0, (ac,
  p2)) : Array<U32> & Jenc.Put}:
  %eb : {Jenc.encode.scan.ac(gt, Jenc.Scan{_, 0, ac, p2}) == Jenc.encode.ac(vals(gt, (_, [])), 0, (ac, p2)) : Array<U32>
    & Jenc.Put}
  %ec : {Jenc.encode.scan.ac(gt, Jenc.Scan{bb, 0, _, p2}) == Jenc.encode.ac(vals(gt, (bb, [])), 0, (_, p2)) : Array<U32>
    & Jenc.Put}
  sac(gt, bb, 0, cc, p2)

# the last step's books, for arrays known equal to others
def bj_tr(
  +gt: List<&2, U32>,
  -a2: Array<U32>,
  -ac: Array<U32>,
  bb: Array<U32>,
  cc: Array<U32>,
  eb: {bb == a2 : Array<U32>},
  ec: {cc == ac : Array<U32>},
  +p2: Jenc.Put,
  dc2: Array<U32>,
  +dd: U32
) -> {Jenc.encode.scan.book(Jenc.encode.ac(vals(gt, (a2, [])), 0, (ac, p2)), dc2,
  dd) == Jenc.encode.block.join( Jenc.encode.ac(vals(gt, (a2, [])), 0, (ac, p2)), dc2,
  dd) : Jenc.Book & U32 & Jenc.Put}:
  %eb : {Jenc.encode.scan.book(Jenc.encode.ac(vals(gt, (_, [])), 0, (ac, p2)), dc2, dd) == Jenc.encode.block.join(
    Jenc.encode.ac(vals(gt, (_, [])), 0, (ac, p2)), dc2, dd) : Jenc.Book & U32 & Jenc.Put}
  %ec : {Jenc.encode.scan.book(Jenc.encode.ac(vals(gt, (bb, [])), 0, (_, p2)), dc2, dd) == Jenc.encode.block.join(
    Jenc.encode.ac(vals(gt, (bb, [])), 0, (_, p2)), dc2, dd) : Jenc.Book & U32 & Jenc.Put}
  book_join(Jenc.encode.ac(vals(gt, (bb, [])), 0, (cc, p2)), dc2, dd)

# the scan after its DC token, from copies of the arrays
def sjoin.d(
  -a2: Array<U32>,
  -ac: Array<U32>,
  +p2: Jenc.Put,
  dc2: Array<U32>,
  +dd: U32,
  +gt: List<&2, U32>,
  da: W10.Dup(a2),
  dk: W10.Dup(ac)
) -> {Jenc.encode.scan.book(Jenc.encode.scan.ac(gt, Jenc.Scan{a2, 0, ac, p2}), dc2,
  dd) == Jenc.encode.block.join( Jenc.encode.ac(vals(gt, (a2, [])), 0, (ac, p2)), dc2,
  dd) : Jenc.Book & U32 & Jenc.Put}:
  (x1, x2, ea1, ea2) = da
  (y1, y2, ec1, ec2) = dk
  Equal.trans(Jenc.Book & U32 & Jenc.Put, Jenc.encode.scan.book(Jenc.encode.scan.ac(gt, Jenc.Scan{a2, 0, ac, p2}), dc2,
    dd), Jenc.encode.scan.book(Jenc.encode.ac(vals(gt, (a2, [])), 0, (ac, p2)), dc2, dd), Jenc.encode.block.join(
    Jenc.encode.ac(vals(gt, (a2, [])), 0, (ac, p2)), dc2, dd), Equal.cong(Array<U32> & Jenc.Put, Jenc.Book & U32 &
    Jenc.Put, xx => Jenc.encode.scan.book(xx, dc2, dd), Jenc.encode.scan.ac(gt, Jenc.Scan{a2, 0, ac, p2}),
    Jenc.encode.ac(vals(gt, (a2, [])), 0, (ac, p2)), sac_tr(gt, a2, ac, x1, y1, ea1, ec1, p2)), bj_tr(gt, a2, ac, x2,
      y2,
    ea2, ec2, p2, dc2, dd))

# the scan after its DC token, whatever the DC coder handed back, is the block coder's
def sjoin(
  got: Array<U32> & Jenc.Put,
  ac: Array<U32>,
  +dd: U32,
  +gt: List<&2, U32>,
  a2: Array<U32>
) -> {Jenc.encode.scan.join(got, ac, dd, gt, a2) == Jenc.encode.block.dc(got, ac, dd, vals(gt, (a2,
  []))) : Jenc.Book & U32 & Jenc.Put}:
  match got:
    case (dc2, +p2):
      sjoin.d(a2, ac, p2, dc2, dd, gt, W10.dup(a2), W10.dup(ac))

# the scan with its DC value named, over any books
def sdc(
  book: Jenc.Book,
  +pp: Jenc.Put,
  +pred: U32,
  +vv: U32,
  +gt: List<&2, U32>,
  a2: Array<U32>
) -> {Jenc.encode.scan.dc(book, pp, pred, vv, gt, a2) == Jenc.encode.block.ac(book, pp, pred, vv, vals(gt, (a2,
  []))) : Jenc.Book & U32 & Jenc.Put}:
  match book:
    case Jenc.Book{dc, ac}:
      sjoin(Jenc.encode.dcdiff(dc, pp, Jenc.encode.dcbias(vv), pred), ac, Jenc.encode.dcbias(vv), gt, a2)

# the scan's DC value named, for an array known equal to another
def sdc_tr(
  book: Jenc.Book,
  +pp: Jenc.Put,
  +pred: U32,
  +vv: U32,
  +gt: List<&2, U32>,
  -a2: Array<U32>,
  bb: Array<U32>,
  ee: {bb == a2 : Array<U32>}
) -> {Jenc.encode.scan.dc(book, pp, pred, vv, gt, a2) == Jenc.encode.block.ac(book, pp, pred, vv, vals(gt, (a2,
  []))) : Jenc.Book & U32 & Jenc.Put}:
  %ee : {Jenc.encode.scan.dc(book, pp, pred, vv, gt, _) == Jenc.encode.block.ac(book, pp, pred, vv, vals(gt, (_, []))) :
    Jenc.Book & U32 & Jenc.Put}
  sdc(book, pp, pred, vv, gt, bb)

# the scan at its first index, from two copies of the array read
def sopen.d(
  -a2: Array<U32>,
  +vv: U32,
  +gt: List<&2, U32>,
  book: Jenc.Book,
  +pp: Jenc.Put,
  +pred: U32,
  dd: W10.Dup(a2)
) -> {Jenc.encode.scan.dc(book, pp, pred, vv, gt, a2) == Jenc.encode.block.go(book, pp, pred, vals(gt, (a2,
  [vv]))) : Jenc.Book & U32 & Jenc.Put}:
  (b1, b2, e1, e2) = dd
  Equal.trans(Jenc.Book & U32 & Jenc.Put, Jenc.encode.scan.dc(book, pp, pred, vv, gt, a2), Jenc.encode.block.go(book,
    pp,
    pred, vv <> vals(gt, (a2, []))), Jenc.encode.block.go(book, pp, pred, vals(gt, (a2, [vv]))), sdc_tr(book, pp, pred,
    vv, gt, a2, b1, e1), Equal.cong(List<&2, U32>, Jenc.Book & U32 & Jenc.Put, ws => Jenc.encode.block.go(book, pp,
      pred,
    ws), vv <> vals(gt, (a2, [])), vals(gt, (a2, [vv])), Equal.sym(List<&2, U32>, vals(gt, (a2, [vv])), vv <> vals(gt,
    (a2, [])), vacc_tr(a2, b2, e2, gt, vv))))

# the scan at its first index, whatever the read returned
def sopen(
  got: Array<U32> & U32,
  +gt: List<&2, U32>,
  book: Jenc.Book,
  +pp: Jenc.Put,
  +pred: U32
) -> {Jenc.encode.scan.open(gt, got, book, pp, pred) == Jenc.encode.block.go(book, pp, pred, vals(gt, vals.put(got,
  []))) : Jenc.Book & U32 & Jenc.Put}:
  match got:
    case (a2, +vv):
      sopen.d(a2, vv, gt, book, pp, pred, W10.dup(a2))

# the encoder's scan of a frequency plane is its block coder over the values the zigzag reads
def scan_blk(
  book: Jenc.Book,
  +pp: Jenc.Put,
  +pred: U32,
  aa: Array<U32>,
  +gg: U32,
  +gt: List<&2, U32>
) -> {Jenc.encode.scan(book, pp, pred, aa, gg <> gt) == Jenc.encode.block.go(book, pp, pred, vals(gg <> gt, (aa,
  []))) : Jenc.Book & U32 & Jenc.Put}:
  sopen(Array.get(U32, aa, gg), gt, book, pp, pred)

# the number of values read, after acc, whatever the read returned
def LenIh(-gt: List<&2, U32>) -> Type:
  @a2: Array<U32> -> {List.length(&2, U32, vals(gt, (a2, []))) == List.length(&2, U32, gt) : Nat}

# the count of values read, for an array known equal to another
def vlen_tr(
  -a2: Array<U32>,
  bb: Array<U32>,
  ee: {bb == a2 : Array<U32>},
  +gt: List<&2, U32>,
  ih: LenIh(gt)
) -> {List.length(&2, U32, vals(gt, (a2, []))) == List.length(&2, U32, gt) : Nat}:
  %ee : {List.length(&2, U32, vals(gt, (_, []))) == List.length(&2, U32, gt) : Nat}
  ih(bb)

# one read, then the rest, from two copies of the array read
def vlen.d(
  -a2: Array<U32>,
  +vv: U32,
  +gt: List<&2, U32>,
  ih: LenIh(gt),
  dd: W10.Dup(a2)
) -> {List.length(&2, U32, vals(gt, (a2, [vv]))) == 1n+List.length(&2, U32, gt) : Nat}:
  (b1, b2, e1, e2) = dd
  Equal.trans(Nat, List.length(&2, U32, vals(gt, (a2, [vv]))), List.length(&2, U32, vv <> vals(gt, (a2, []))),
    1n+List.length(&2, U32, gt), Equal.cong(List<&2, U32>, Nat, ws => List.length(&2, U32, ws), vals(gt, (a2, [vv])),
    vv <> vals(gt, (a2, [])), vacc_tr(a2, b1, e1, gt, vv)), Equal.cong(Nat, Nat, nn => 1n+nn, List.length(&2, U32,
    vals(gt, (a2, []))), List.length(&2, U32, gt), vlen_tr(a2, b2, e2, gt, ih)))

# one read, then the rest
def vlen.got(
  got: Array<U32> & U32,
  +gt: List<&2, U32>,
  ih: LenIh(gt)
) -> {List.length(&2, U32, vals(gt, vals.put(got, []))) == 1n+List.length(&2, U32, gt) : Nat}:
  match got:
    case (a2, +vv):
      vlen.d(a2, vv, gt, ih, W10.dup(a2))

# as many values as indexes
def vlen(
  gs: List<&2, U32>,
  aa: Array<U32>
) -> {List.length(&2, U32, vals(gs, (aa, []))) == List.length(&2, U32, gs) : Nat}:
  match gs:
    case Nil{}:
      {==}
    case +gg <> +gt:
      vlen.got(Array.get(U32, aa, gg), gt, a2 => vlen(gt, a2))

# the scan of an empty zigzag is the block coder of no values
def scan_nil(
  book: Jenc.Book,
  +pp: Jenc.Put,
  +pred: U32,
  aa: Array<U32>
) -> {Jenc.encode.scan(book, pp, pred, aa, []) == Jenc.encode.block.go(book, pp, pred, vals([], (aa,
  []))) : Jenc.Book & U32 & Jenc.Put}:
  {==}

# the encoder's scan of a frequency plane is its block coder over the values the zigzag reads
def scan_eq(
  book: Jenc.Book,
  +pp: Jenc.Put,
  +pred: U32,
  aa: Array<U32>,
  zig: List<&2, U32>
) -> {Jenc.encode.scan(book, pp, pred, aa, zig) == Jenc.encode.block.go(book, pp, pred, vals(zig, (aa,
  []))) : Jenc.Book & U32 & Jenc.Put}:
  match zig:
    case Nil{}:
      scan_nil(book, pp, pred, aa)
    case +gg <> +gt:
      scan_blk(book, pp, pred, aa, gg, gt)

# the count of values an array holds at the zigzag, from a copy of it
def lenz(
  -aa: Array<U32>,
  bb: Array<U32>,
  ee: {bb == aa : Array<U32>}
) -> {List.length(&2, U32, vals(Jpeg.decode.zig(), (aa, []))) == 64n : Nat}:
  %ee : {List.length(&2, U32, vals(Jpeg.decode.zig(), (_, []))) == 64n : Nat}
  vlen(Jpeg.decode.zig(), bb)

# a block of values, once they are known to be 64
def Blk64(+_pred: U32, +_pp: Jenc.Put, +_xs: List<&2, U32>) -> Type:
  @hl: {List.length(&2, U32, _xs) == 64n : Nat} -> BlkOut(_pred, _pp, _xs)

# the block of the values an array holds at the zigzag, once they are known to be 64, from a copy of it
def blkh(
  -aa: Array<U32>,
  bb: Array<U32>,
  ee: {bb == aa : Array<U32>},
  +pp: Jenc.Put,
  +pred: U32,
  hp: {U32.is_lt(pred, 2048) == True{} : Bool}
) -> Blk64(pred, pp, vals(Jpeg.decode.zig(), (aa, []))):
  %ee : Blk64(pred, pp, vals(Jpeg.decode.zig(), (_, [])))
  hl => blk(vals(Jpeg.decode.zig(), (bb, [])), pred, pp, hl, hp)

# the block of the values an array holds at the zigzag, the array one of two copies
def blkv(
  -aa: Array<U32>,
  +pp: Jenc.Put,
  +pred: U32,
  hp: {U32.is_lt(pred, 2048) == True{} : Bool},
  dd: W10.Dup(aa)
) -> BlkOut(pred, pp, vals(Jpeg.decode.zig(), (aa, []))):
  (b1, b2, e1, e2) = dd
  blkh(aa, b1, e1, pp, pred, hp)(lenz(aa, b2, e2))

# the encoder's scan of any frequency plane codes a block the decoder reads whole
def ScanOut(-aa: Array<U32>, +pp: Jenc.Put, +pred: U32) -> Type:
  &bt: Laws.JBlkTok -> &dd: U32 -> &_e: {Jenc.encode.scan(book(), pp, pred, aa, Jpeg.decode.zig()) == (book(), dd,
    Laws.jpg.feed(W12.blkbits(bt), pp)) : Jenc.Book & U32 & Jenc.Put} -> &_h: {U32.is_lt(dd, 2048) == True{} : Bool} ->
    {Laws.jpg.blkwf(bt) == True{} : Bool}

# the type of scan_fin's parameter es
def scan_fin.es.ty(_aa: Array<U32>, +_pp: Jenc.Put, +_pred: U32) -> Type:
  {Jenc.encode.scan(book(), _pp, _pred, _aa, Jpeg.decode.zig()) == Jenc.encode.block.go(book(), _pp, _pred,
    vals(Jpeg.decode.zig(), (_aa, []))) : Jenc.Book & U32 & Jenc.Put}

# the scan's block, moved along the scan's equation
def scan_fin(
  -aa: Array<U32>,
  +pp: Jenc.Put,
  +pred: U32,
  es: scan_fin.es.ty(aa, pp, pred),
  bo: BlkOut(pred, pp, vals(Jpeg.decode.zig(), (aa, [])))
) -> ScanOut(aa, pp, pred):
  (bt, +dd, eb, hd, hw) = bo
  (bt, dd, Equal.trans(Jenc.Book & U32 & Jenc.Put, Jenc.encode.scan(book(), pp, pred, aa, Jpeg.decode.zig()),
    Jenc.encode.block.go(book(), pp, pred, vals(Jpeg.decode.zig(), (aa, []))), (book(), dd, Laws.jpg.feed(
    W12.blkbits(bt), pp)), es, eb), hd, hw)

# the scan's equation for an array known equal to another
def scan_tr(
  -aa: Array<U32>,
  bb: Array<U32>,
  ee: {bb == aa : Array<U32>},
  +pp: Jenc.Put,
  +pred: U32
) -> {Jenc.encode.scan(book(), pp, pred, aa, Jpeg.decode.zig()) == Jenc.encode.block.go(book(), pp, pred,
  vals( Jpeg.decode.zig(), (aa, []))) : Jenc.Book & U32 & Jenc.Put}:
  %ee : {Jenc.encode.scan(book(), pp, pred, _, Jpeg.decode.zig()) == Jenc.encode.block.go(book(), pp, pred,
    vals(Jpeg.decode.zig(), (_, []))) : Jenc.Book & U32 & Jenc.Put}
  scan_eq(book(), pp, pred, bb, Jpeg.decode.zig())

# the scan of a plane, from copies of it
def scan_d(
  -aa: Array<U32>,
  +pp: Jenc.Put,
  +pred: U32,
  hp: {U32.is_lt(pred, 2048) == True{} : Bool},
  dd: W10.Dup(aa)
) -> ScanOut(aa, pp, pred):
  (b1, b2, e1, e2) = dd
  scan_fin(aa, pp, pred, scan_tr(aa, b1, e1, pp, pred), blkv(aa, pp, pred, hp, W10.dup.tr(b2, aa, e2, W10.dup(b2))))

# the scan of any plane
def scan_ok(
  aa: Array<U32>,
  +pp: Jenc.Put,
  +pred: U32,
  hp: {U32.is_lt(pred, 2048) == True{} : Bool}
) -> ScanOut(aa, pp, pred):
  scan_d(aa, pp, pred, hp, W10.dup(aa))

# one component's block of an MCU, flat or not
def ChOut(+flat: Bool, -plane: Array<U32>, +pp: Jenc.Put, +pred: U32, +kern: Jenc.Kern, +qs: List<&2, U32>) -> Type:
  &bt: Laws.JBlkTok -> &dd: U32 -> &_e: {Jenc.encode.chan.go(flat, plane, book(), pp, pred, kern, Jpeg.decode.zig(),
    qs) ==
    (book(), dd, Laws.jpg.feed(W12.blkbits(bt), pp)) : Jenc.Book & U32 & Jenc.Put} -> &_h: {U32.is_lt(dd,
      2048) == True{} :
    Bool} -> {Laws.jpg.blkwf(bt) == True{} : Bool}

# one component's block, by whether it is flat
def chan_ok(
  flat: Bool,
  plane: Array<U32>,
  +pp: Jenc.Put,
  +pred: U32,
  +kern: Jenc.Kern,
  +qs: List<&2, U32>,
  hp: {U32.is_lt(pred, 2048) == True{} : Bool}
) -> ChOut(flat, plane, pp, pred, kern, qs):
  match flat:
    case True{}:
      blk(List.replicate(U32, 64n, 0), pred, pp, {==}, hp)
    case False{}:
      scan_ok(Jenc.encode.freq(plane, kern), pp, pred, hp)

# the encoder's cosine kernel
def kern() -> Jenc.Kern:
  Jenc.encode.kern(Jpeg.decode.cos())

# three blocks' bits fed after bits already fed
def feed3b(+b1: Laws.JBlkTok, +b2: Laws.JBlkTok, +b3: Laws.JBlkTok, +bit: Jenc.Put) -> Jenc.Put:
  Laws.jpg.feed(W12.blkbits(b3), Laws.jpg.feed(W12.blkbits(b2), Laws.jpg.feed(W12.blkbits(b1), bit)))

# one MCU the encoder codes: three blocks the decoder reads whole, fed to the writer, the books back, and the next
# predictors below 2048
def McuOut(-tt: Jenc.Tile, +bit: Jenc.Put, +py: U32, +pb: U32, +pr: U32) -> Type:
  &t1: Laws.JBlkTok -> &t2: Laws.JBlkTok -> &t3: Laws.JBlkTok -> &aa: Array<U32> -> &d1: U32 -> &d2: U32 -> &d3: U32 ->
    &_e:
    {Jenc.encode.step.tile(tt, book(), bit, py, pb, pr, kern(), Jpeg.decode.zig(), Jenc.encode.quant()) == (aa,
    book(), d1, d2, d3, feed3b(t1, t2, t3, bit)) : Array<U32> & Jenc.Book & U32 & U32 & U32 & Jenc.Put} -> &_h1:
    {U32.is_lt(d1, 2048) == True{} : Bool} -> &_h2: {U32.is_lt(d2, 2048) == True{} : Bool} -> &_h3: {U32.is_lt(d3,
    2048) == True{} : Bool} -> &_w1: {Laws.jpg.blkwf(t1) == True{} : Bool} -> &_w2: {Laws.jpg.blkwf(t2) == True{} :
      Bool} ->
    {Laws.jpg.blkwf(t3) == True{} : Bool}

# the type of mcu3's parameter e1
def mcu3.e1.ty(_ys: Array<U32>, +_fy: Bool, +_bit: Jenc.Put, +_py: U32, +_t1: Laws.JBlkTok, +_d1: U32) -> Type:
  {Jenc.encode.chan.go(_fy, _ys, book(), _bit, _py, kern(), Jpeg.decode.zig(), Jenc.encode.quant()) == (book(), _d1,
    Laws.jpg.feed(W12.blkbits(_t1), _bit)) : Jenc.Book & U32 & Jenc.Put}

# the type of mcu3's parameter e2
def mcu3.e2.ty(
  _bs: Array<U32>,
  +_fb: Bool,
  +_bit: Jenc.Put,
  +_pb: U32,
  +_t1: Laws.JBlkTok,
  +_t2: Laws.JBlkTok,
  +_d2: U32
) -> Type:
  {Jenc.encode.chan.go(_fb, _bs, book(), Laws.jpg.feed(W12.blkbits(_t1), _bit), _pb, kern(), Jpeg.decode.zig(),
    Jenc.encode.quant()) == (book(), _d2, Laws.jpg.feed(W12.blkbits(_t2), Laws.jpg.feed(W12.blkbits(_t1),
    _bit))) : Jenc.Book & U32 & Jenc.Put}

# the type of mcu3's parameter c3
def mcu3.c3.ty(_rs: Array<U32>, +_fr: Bool, +_bit: Jenc.Put, +_pr: U32, +_t1: Laws.JBlkTok, +_t2: Laws.JBlkTok) -> Type:
  ChOut(_fr, _rs, Laws.jpg.feed(W12.blkbits(_t2), Laws.jpg.feed(W12.blkbits(_t1), _bit)), _pr, kern(),
    Jenc.encode.quant())

# the MCU's Cr block, after its Y and Cb blocks
def mcu3(
  pix: Array<U32>,
  -ys: Array<U32>,
  -bs: Array<U32>,
  -rs: Array<U32>,
  -fy: Bool,
  -fb: Bool,
  -fr: Bool,
  +bit: Jenc.Put,
  +py: U32,
  +pb: U32,
  +pr: U32,
  +t1: Laws.JBlkTok,
  +d1: U32,
  e1: mcu3.e1.ty(ys, fy, bit, py, t1, d1),
  h1: {U32.is_lt(d1, 2048) == True{} : Bool},
  w1: {Laws.jpg.blkwf(t1) == True{} : Bool},
  +t2: Laws.JBlkTok,
  +d2: U32,
  e2: mcu3.e2.ty(bs, fb, bit, pb, t1, t2, d2),
  h2: {U32.is_lt(d2, 2048) == True{} : Bool},
  w2: {Laws.jpg.blkwf(t2) == True{} : Bool},
  c3: mcu3.c3.ty(rs, fr, bit, pr, t1, t2)
) -> McuOut(Jenc.Tile{pix, ys, bs, rs, fy, fb, fr}, bit, py, pb, pr):
  (+t3, +d3, e3, h3, w3) = c3
  +kn = kern()
  +zg = Jpeg.decode.zig()
  +qs = Jenc.encode.quant()
  +p1 = Laws.jpg.feed(W12.blkbits(t1), bit)
  +p2 = Laws.jpg.feed(W12.blkbits(t2), p1)
  +p3 = Laws.jpg.feed(W12.blkbits(t3), p2)
  (t1, t2, t3, pix, d1, d2, d3, Equal.trans(Array<U32> & Jenc.Book & U32 & U32 & U32 & Jenc.Put, Jenc.encode.step.cb(
    Jenc.encode.chan.go(fy, ys, book(), bit, py, kn, zg, qs), pix, bs, rs, fb, fr, pb, pr, kn, zg, qs),
    Jenc.encode.step.cb((book(), d1, p1), pix, bs, rs, fb, fr, pb, pr, kn, zg, qs), (pix, book(), d1, d2, d3, p3),
    Equal.cong(Jenc.Book & U32 & Jenc.Put, Array<U32> & Jenc.Book & U32 & U32 & U32 & Jenc.Put, gg =>
    Jenc.encode.step.cb(gg, pix, bs, rs, fb, fr, pb, pr, kn, zg, qs), Jenc.encode.chan.go(fy, ys, book(), bit, py, kn,
    zg, qs), (book(), d1, p1), e1), Equal.trans(Array<U32> & Jenc.Book & U32 & U32 & U32 & Jenc.Put,
    Jenc.encode.step.cr(Jenc.encode.chan.go(fb, bs, book(), p1, pb, kn, zg, qs), pix, rs, fr, d1, pr, kn, zg, qs),
    Jenc.encode.step.cr((book(), d2, p2), pix, rs, fr, d1, pr, kn, zg, qs), (pix, book(), d1, d2, d3, p3),
    Equal.cong(Jenc.Book & U32 & Jenc.Put, Array<U32> & Jenc.Book & U32 & U32 & U32 & Jenc.Put, gg =>
    Jenc.encode.step.cr(gg, pix, rs, fr, d1, pr, kn, zg, qs), Jenc.encode.chan.go(fb, bs, book(), p1, pb, kn, zg, qs),
    (book(), d2, p2), e2), Equal.cong(Jenc.Book & U32 & Jenc.Put, Array<U32> & Jenc.Book & U32 & U32 & U32 &
    Jenc.Put, gg => Jenc.encode.step.end(Jenc.encode.chan.pair(gg, pix), d1, d2), Jenc.encode.chan.go(fr, rs, book(),
    p2, pr, kn, zg, qs), (book(), d3, p3), e3))), h1, h2, h3, w1, w2, w3)

# the type of mcu2's parameter e1
def mcu2.e1.ty(_ys: Array<U32>, +_fy: Bool, +_bit: Jenc.Put, +_py: U32, +_t1: Laws.JBlkTok, +_d1: U32) -> Type:
  {Jenc.encode.chan.go(_fy, _ys, book(), _bit, _py, kern(), Jpeg.decode.zig(), Jenc.encode.quant()) == (book(), _d1,
    Laws.jpg.feed(W12.blkbits(_t1), _bit)) : Jenc.Book & U32 & Jenc.Put}

# the MCU's Cb and Cr blocks, after its Y block
def mcu2(
  pix: Array<U32>,
  -ys: Array<U32>,
  -bs: Array<U32>,
  rs: Array<U32>,
  -fy: Bool,
  -fb: Bool,
  +fr: Bool,
  +bit: Jenc.Put,
  +py: U32,
  +pb: U32,
  +pr: U32,
  hr: {U32.is_lt(pr, 2048) == True{} : Bool},
  +t1: Laws.JBlkTok,
  +d1: U32,
  e1: mcu2.e1.ty(ys, fy, bit, py, t1, d1),
  h1: {U32.is_lt(d1, 2048) == True{} : Bool},
  w1: {Laws.jpg.blkwf(t1) == True{} : Bool},
  c2: ChOut(fb, bs, Laws.jpg.feed(W12.blkbits(t1), bit), pb, kern(), Jenc.encode.quant())
) -> McuOut(Jenc.Tile{pix, ys, bs, rs, fy, fb, fr}, bit, py, pb, pr):
  (+t2, +d2, e2, h2, w2) = c2
  mcu3(pix, ys, bs, rs, fy, fb, fr, bit, py, pb, pr, t1, d1, e1, h1, w1, t2, d2, e2, h2, w2, chan_ok(fr, rs,
    Laws.jpg.feed(
    W12.blkbits(t2), Laws.jpg.feed(W12.blkbits(t1), bit)), pr, kern(), Jenc.encode.quant(), hr))

# the MCU's blocks, after its Y block
def mcu1(
  pix: Array<U32>,
  -ys: Array<U32>,
  bs: Array<U32>,
  rs: Array<U32>,
  -fy: Bool,
  +fb: Bool,
  +fr: Bool,
  +bit: Jenc.Put,
  +py: U32,
  +pb: U32,
  +pr: U32,
  hb: {U32.is_lt(pb, 2048) == True{} : Bool},
  hr: {U32.is_lt(pr, 2048) == True{} : Bool},
  c1: ChOut(fy, ys, bit, py, kern(), Jenc.encode.quant())
) -> McuOut(Jenc.Tile{pix, ys, bs, rs, fy, fb, fr}, bit, py, pb, pr):
  (+t1, +d1, e1, h1, w1) = c1
  mcu2(pix, ys, bs, rs, fy, fb, fr, bit, py, pb, pr, hr, t1, d1, e1, h1, w1, chan_ok(fb, bs,
    Laws.jpg.feed(W12.blkbits(t1),
    bit), pb, kern(), Jenc.encode.quant(), hb))

# every MCU's tile, whatever it holds, codes three blocks the decoder reads whole
def mcu(
  tt: Jenc.Tile,
  +bit: Jenc.Put,
  +py: U32,
  +pb: U32,
  +pr: U32,
  hy: {U32.is_lt(py, 2048) == True{} : Bool},
  hb: {U32.is_lt(pb, 2048) == True{} : Bool},
  hr: {U32.is_lt(pr, 2048) == True{} : Bool}
) -> McuOut(tt, bit, py, pb, pr):
  match tt:
    case Jenc.Tile{pix, ys, bs, rs, +fy, +fb, +fr}:
      mcu1(pix, ys, bs, rs, fy, fb, fr, bit, py, pb, pr, hb, hr, chan_ok(fy, ys, bit, py, kern(), Jenc.encode.quant(),
        hy))

# three for each MCU
def tri(nn: Nat) -> Nat:
  match nn:
    case 0n:
      0n
    case 1n+mm:
      1n+(1n+(1n+tri(mm)))

# the encoder's MCU loop from a state: the blocks it codes, fed to the writer, three per MCU, each read whole
def McusOut(
  nn: Nat,
  -aa: Array<U32>,
  +py: U32,
  +pb: U32,
  +pr: U32,
  +bit: Jenc.Put,
  +mx: U32,
  +my: U32,
  +mw: U32,
  +ww: U32,
  +hh: U32
) -> Type:
  &ts: List<&2, Laws.JBlkTok> -> &_e: {Jenc.encode.mcus(nn, (aa, book(), py, pb, pr, bit), mx, my, mw, ww, hh,
    Jenc.encode.ctx()) == Laws.jpg.feed(W12.tbits(ts), bit) : Jenc.Put} -> &_l: {List.length(&2, Laws.JBlkTok,
      ts) == tri(nn) : Nat} ->
    {Laws.jpg.allwf(ts) == True{} : Bool}

# the rest of the MCU loop, from any state
def McusIh(+_nn: Nat, +_mw: U32, +_ww: U32, +_hh: U32) -> Type:
  @a2: Array<U32> -> @q1: U32 -> @q2: U32 -> @q3: U32 -> @p2: Jenc.Put -> @x2: U32 -> @y2: U32 -> @h1: {U32.is_lt(q1,
    2048) == True{} : Bool} -> @h2: {U32.is_lt(q2, 2048) == True{} : Bool} -> @h3: {U32.is_lt(q3, 2048) == True{} :
    Bool} -> McusOut(_nn, a2, q1, q2, q3, p2, x2, y2, _mw, _ww, _hh)

# three blocks, then the rest's blocks, fed to the writer
def feed_tri(
  +t1: Laws.JBlkTok,
  +t2: Laws.JBlkTok,
  +t3: Laws.JBlkTok,
  +ts: List<&2, Laws.JBlkTok>,
  +bit: Jenc.Put
) -> {Laws.jpg.feed(W12.tbits(ts), feed3b(t1, t2, t3, bit)) == Laws.jpg.feed(W12.tbits(t1 <> t2 <> t3 <> ts),
  bit) : Jenc.Put}:
  +b1 = W12.blkbits(t1)
  +b2 = W12.blkbits(t2)
  +b3 = W12.blkbits(t3)
  +rs = W12.tbits(ts)
  Equal.sym(Jenc.Put, Laws.jpg.feed(List.append(&2, Bool, b1, List.append(&2, Bool, b2, List.append(&2, Bool, b3,
    rs))), bit),
    Laws.jpg.feed(rs, feed3b(t1, t2, t3, bit)), Equal.trans(Jenc.Put, Laws.jpg.feed(List.append(&2, Bool, b1,
      List.append(&2, Bool,
    b2, List.append(&2, Bool, b3, rs))), bit), Laws.jpg.feed(List.append(&2, Bool, b2, List.append(&2, Bool, b3, rs)),
    Laws.jpg.feed(b1, bit)), Laws.jpg.feed(rs, feed3b(t1, t2, t3, bit)), W12.feed_app(b1, List.append(&2, Bool, b2,
      List.append(&2,
    Bool, b3, rs)), bit), Equal.trans(Jenc.Put, Laws.jpg.feed(List.append(&2, Bool, b2, List.append(&2, Bool, b3, rs)),
    Laws.jpg.feed(b1, bit)), Laws.jpg.feed(List.append(&2, Bool, b3, rs), Laws.jpg.feed(b2, Laws.jpg.feed(b1, bit))),
      Laws.jpg.feed(rs, feed3b(t1, t2,
    t3, bit)), W12.feed_app(b2, List.append(&2, Bool, b3, rs), Laws.jpg.feed(b1, bit)), W12.feed_app(b3, rs,
      Laws.jpg.feed(b2,
    Laws.jpg.feed(b1, bit))))))

# the type of mcus_fin's parameter ee
def mcus_fin.ee.ty(
  _aa: Array<U32>,
  +_py: U32,
  +_pb: U32,
  +_pr: U32,
  +_bit: Jenc.Put,
  +_mx: U32,
  +_my: U32,
  +_ww: U32,
  +_hh: U32,
  +_t1: Laws.JBlkTok,
  +_t2: Laws.JBlkTok,
  +_t3: Laws.JBlkTok,
  _a2: Array<U32>,
  +_d1: U32,
  +_d2: U32,
  +_d3: U32
) -> Type:
  {Jenc.encode.step.tile(Jenc.encode.tile(_aa, _ww, _hh, (_mx * 8 : U32), (_my * 8 : U32)), book(), _bit, _py, _pb,
    _pr, kern(), Jpeg.decode.zig(), Jenc.encode.quant()) == (_a2, book(), _d1, _d2, _d3, feed3b(_t1, _t2, _t3,
    _bit)) : Array<U32> & Jenc.Book & U32 & U32 & U32 & Jenc.Put}

# the type of mcus_fin's parameter rest
def mcus_fin.rest.ty(
  +_nn: Nat,
  +_bit: Jenc.Put,
  +_mx: U32,
  +_my: U32,
  +_mw: U32,
  +_ww: U32,
  +_hh: U32,
  +_t1: Laws.JBlkTok,
  +_t2: Laws.JBlkTok,
  +_t3: Laws.JBlkTok,
  _a2: Array<U32>,
  +_d1: U32,
  +_d2: U32,
  +_d3: U32
) -> Type:
  McusOut(_nn, _a2, _d1, _d2, _d3, feed3b(_t1, _t2, _t3, _bit), Jenc.encode.nx(U32.is_lt((_mx + 1 : U32), _mw), _mx),
    Jenc.encode.ny(U32.is_lt((_mx + 1 : U32), _mw), _my), _mw, _ww, _hh)

# the MCU loop after one MCU, its rest named
def mcus_fin(
  +nn: Nat,
  -aa: Array<U32>,
  +py: U32,
  +pb: U32,
  +pr: U32,
  +bit: Jenc.Put,
  +mx: U32,
  +my: U32,
  +mw: U32,
  +ww: U32,
  +hh: U32,
  +t1: Laws.JBlkTok,
  +t2: Laws.JBlkTok,
  +t3: Laws.JBlkTok,
  -a2: Array<U32>,
  +d1: U32,
  +d2: U32,
  +d3: U32,
  ee: mcus_fin.ee.ty(aa, py, pb, pr, bit, mx, my, ww, hh, t1, t2, t3, a2, d1, d2, d3),
  w1: {Laws.jpg.blkwf(t1) == True{} : Bool},
  w2: {Laws.jpg.blkwf(t2) == True{} : Bool},
  w3: {Laws.jpg.blkwf(t3) == True{} : Bool},
  rest: mcus_fin.rest.ty(nn, bit, mx, my, mw, ww, hh, t1, t2, t3, a2, d1, d2, d3)
) -> McusOut(1n+nn, aa, py, pb, pr, bit, mx, my, mw, ww, hh):
  (+ts, er, el, ew) = rest
  +mo = U32.is_lt((mx + 1 : U32), mw)
  +cx = Jenc.encode.ctx()
  +p3 = feed3b(t1, t2, t3, bit)
  (t1 <> t2 <> t3 <> ts, Equal.trans(Jenc.Put, Jenc.encode.mcus(nn, Jenc.encode.step.y(aa, book(), bit, py, pb, pr,
    (mx * 8 : U32), (my * 8 : U32), ww, hh, cx), Jenc.encode.nx(mo, mx), Jenc.encode.ny(mo, my), mw, ww, hh, cx),
    Jenc.encode.mcus(nn, (a2, book(), d1, d2, d3, p3), Jenc.encode.nx(mo, mx), Jenc.encode.ny(mo, my), mw, ww, hh, cx),
    Laws.jpg.feed(W12.tbits(t1 <> t2 <> t3 <> ts), bit), Equal.cong(Array<U32> & Jenc.Book & U32 & U32 & U32 & Jenc.Put,
    Jenc.Put, gg => Jenc.encode.mcus(nn, gg, Jenc.encode.nx(mo, mx), Jenc.encode.ny(mo, my), mw, ww, hh, cx),
    Jenc.encode.step.y(aa, book(), bit, py, pb, pr, (mx * 8 : U32), (my * 8 : U32), ww, hh, cx), (a2, book(), d1,
    d2, d3, p3), ee), Equal.trans(Jenc.Put, Jenc.encode.mcus(nn, (a2, book(), d1, d2, d3, p3), Jenc.encode.nx(mo, mx),
    Jenc.encode.ny(mo, my), mw, ww, hh, cx), Laws.jpg.feed(W12.tbits(ts), p3),
      Laws.jpg.feed(W12.tbits(t1 <> t2 <> t3 <> ts), bit), er,
    feed_tri(t1, t2, t3, ts, bit))), Equal.cong(Nat, Nat, kk => 1n+(1n+(1n+kk)), List.length(&2, Laws.JBlkTok, ts),
      tri(nn), el),
    Equal.trans(Bool, Laws.jpg.also(Laws.jpg.blkwf(t1), Laws.jpg.also(Laws.jpg.blkwf(t2),
      Laws.jpg.also(Laws.jpg.blkwf(t3), Laws.jpg.allwf(ts)))),
    Laws.jpg.also(Laws.jpg.blkwf(t2), Laws.jpg.also(Laws.jpg.blkwf(t3), Laws.jpg.allwf(ts))), True{},
      also_t(Laws.jpg.blkwf(t1), Laws.jpg.also(Laws.jpg.blkwf(t2),
    Laws.jpg.also(Laws.jpg.blkwf(t3), Laws.jpg.allwf(ts))), w1), Equal.trans(Bool, Laws.jpg.also(Laws.jpg.blkwf(t2),
      Laws.jpg.also(Laws.jpg.blkwf(t3),
    Laws.jpg.allwf(ts))), Laws.jpg.also(Laws.jpg.blkwf(t3), Laws.jpg.allwf(ts)), True{}, also_t(Laws.jpg.blkwf(t2),
      Laws.jpg.also(Laws.jpg.blkwf(t3),
    Laws.jpg.allwf(ts)), w2), Equal.trans(Bool, Laws.jpg.also(Laws.jpg.blkwf(t3), Laws.jpg.allwf(ts)),
      Laws.jpg.allwf(ts), True{}, also_t(
    Laws.jpg.blkwf(t3), Laws.jpg.allwf(ts), w3), ew))))

# the MCU loop after one MCU, its MCU named
def mcus_step(
  +nn: Nat,
  -aa: Array<U32>,
  +py: U32,
  +pb: U32,
  +pr: U32,
  +bit: Jenc.Put,
  +mx: U32,
  +my: U32,
  +mw: U32,
  +ww: U32,
  +hh: U32,
  ih: McusIh(nn, mw, ww, hh),
  mo: McuOut(Jenc.encode.tile(aa, ww, hh, (mx * 8 : U32), (my * 8 : U32)), bit, py, pb, pr)
) -> McusOut(1n+nn, aa, py, pb, pr, bit, mx, my, mw, ww, hh):
  (+t1, +t2, +t3, a2, +d1, +d2, +d3, e, h1, h2, h3, w1, w2, w3) = mo
  +mv = U32.is_lt((mx + 1 : U32), mw)
  mcus_fin(nn, aa, py, pb, pr, bit, mx, my, mw, ww, hh, t1, t2, t3, a2, d1, d2, d3, e, w1, w2, w3, ih(a2, d1, d2, d3,
    feed3b(t1, t2, t3, bit), Jenc.encode.nx(mv, mx), Jenc.encode.ny(mv, my), h1, h2, h3))

# the encoder's MCU loop, from predictors below 2048, codes three blocks per MCU, each read whole
def mcus_ok(
  nn: Nat,
  aa: Array<U32>,
  +py: U32,
  +pb: U32,
  +pr: U32,
  +bit: Jenc.Put,
  +mx: U32,
  +my: U32,
  +mw: U32,
  +ww: U32,
  +hh: U32,
  hy: {U32.is_lt(py, 2048) == True{} : Bool},
  hb: {U32.is_lt(pb, 2048) == True{} : Bool},
  hr: {U32.is_lt(pr, 2048) == True{} : Bool}
) -> McusOut(nn, aa, py, pb, pr, bit, mx, my, mw, ww, hh):
  match nn:
    case 0n:
      ([], {==}, {==}, {==})
    case 1n+ +mm:
      mcus_step(mm, aa, py, pb, pr, bit, mx, my, mw, ww, hh, a2 => q1 => q2 => q3 => p2 => x2 => y2 => h1 => h2 => h3 =>
        mcus_ok(mm, a2, q1, q2, q3, p2, x2, y2, mw, ww, hh, h1, h2, h3), mcu(Jenc.encode.tile(aa, ww, hh,
          (mx * 8 : U32),
        (my * 8 : U32)), bit, py, pb, pr, hy, hb, hr))

# the bits of a zero block: the DC code of size 0, then EOB (Annex K: 00, 1010)
def zb() -> List<&2, Bool>:
  [False{}, False{}, True{}, False{}, True{}, False{}]

# the encoder's zero block, packed six bits at once, is the model writer fed its bits
def zput_eq(
  ws: W12.WS,
  hh: {W12.wshort(ws) == True{} : Bool}
) -> {Jenc.encode.zput(W12.wput(ws)) == W12.wput(W12.wm(zb(), ws)) : Jenc.Put}:
  match ws:
    case W12.WS{out, pp}:
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
                                      Empty.absurd({Jenc.encode.zput(W12.wput(W12.WS{out,
                                        p0 <> p1 <> p2 <> p3 <> p4 <> p5 <> p6 <> p7 <> t7})) ==
                                        W12.wput(W12.wm([False{}, False{}, True{}, False{}, True{}, False{}],
                                        W12.WS{out, p0 <> p1 <> p2 <> p3 <> p4 <> p5 <> p6 <> p7 <> t7})) : Jenc.Put},
                                        W12.long8(t7, hh))

# the model writer fed two runs of bits is fed their join
def wm_app(
  xs: List<&2, Bool>,
  +ys: List<&2, Bool>,
  ws: W12.WS
) -> {W12.wm(List.append(&2, Bool, xs, ys), ws) == W12.wm(ys, W12.wm(xs, ws)) : W12.WS}:
  match xs:
    case Nil{}:
      {==}
    case bb <> rest:
      wm_app(rest, ys, W12.wstep(ws, bb))

# the model writer keeps fewer than 8 pending bits
def wm_short(
  bs: List<&2, Bool>,
  +ws: W12.WS,
  hh: {W12.wshort(ws) == True{} : Bool}
) -> {W12.wshort(W12.wm(bs, ws)) == True{} : Bool}:
  match bs:
    case Nil{}:
      hh
    case +bb <> rest:
      wm_short(rest, W12.wstep(ws, bb), W12.wstep.short(ws, bb, hh))

# a zero block: DC size 0, then EOB
def zbt() -> Laws.JBlkTok:
  Laws.JBlkTok{0, [], [Laws.JTok{0, []}]}

# the zero blocks of n MCUs
def ztoks(nn: Nat) -> List<&2, Laws.JBlkTok>:
  match nn:
    case 0n:
      []
    case 1n+mm:
      zbt() <> zbt() <> zbt() <> ztoks(mm)

# three zero blocks, packed, are the model writer fed their bits
def ztri_eq(
  +ws: W12.WS,
  +hh: {W12.wshort(ws) == True{} : Bool}
) -> {Jenc.encode.ztri(W12.wput(ws)) == W12.wput(W12.wm(zb(), W12.wm(zb(), W12.wm(zb(), ws)))) : Jenc.Put}:
  +w1 = W12.wm(zb(), ws)
  +w2 = W12.wm(zb(), w1)
  +h1 = {wm_short(zb(), ws, hh) : {W12.wshort(w1) == True{} : Bool}}
  +h2 = {wm_short(zb(), w1, h1) : {W12.wshort(w2) == True{} : Bool}}
  Equal.trans(Jenc.Put, Jenc.encode.zput(Jenc.encode.zput(Jenc.encode.zput(W12.wput(ws)))),
    Jenc.encode.zput(Jenc.encode.zput(W12.wput(w1))), W12.wput(W12.wm(zb(), w2)), Equal.cong(Jenc.Put, Jenc.Put, pp =>
    Jenc.encode.zput(Jenc.encode.zput(pp)), Jenc.encode.zput(W12.wput(ws)), W12.wput(w1), zput_eq(ws, hh)), Equal.trans(
    Jenc.Put, Jenc.encode.zput(Jenc.encode.zput(W12.wput(w1))), Jenc.encode.zput(W12.wput(w2)), W12.wput(W12.wm(zb(),
      w2)),
    Equal.cong(Jenc.Put, Jenc.Put, pp => Jenc.encode.zput(pp), Jenc.encode.zput(W12.wput(w1)), W12.wput(w2), zput_eq(w1,
    h1)), zput_eq(w2, h2)))

# the encoder's zero MCUs are the model writer fed the zero blocks' bits
def nm(
  nn: Nat,
  +ws: W12.WS,
  +hh: {W12.wshort(ws) == True{} : Bool}
) -> {Jenc.encode.neutral.mcus(nn, W12.wput(ws)) == W12.wput(W12.wm(W12.tbits(ztoks(nn)), ws)) : Jenc.Put}:
  match nn:
    case 0n:
      {==}
    case 1n+ +mm:
      +zz = zb()
      +w3 = W12.wm(zz, W12.wm(zz, W12.wm(zz, ws)))
      +h3 = {wm_short(zz, W12.wm(zz, W12.wm(zz, ws)), wm_short(zz, W12.wm(zz, ws), wm_short(zz, ws,
        hh))) : {W12.wshort(w3) ==
        True{} : Bool}}
      +tt = W12.tbits(ztoks(mm))
      Equal.trans(Jenc.Put, Jenc.encode.neutral.mcus(mm, Jenc.encode.ztri(W12.wput(ws))), Jenc.encode.neutral.mcus(mm,
        W12.wput(w3)), W12.wput(W12.wm(List.append(&2, Bool, zz, List.append(&2, Bool, zz, List.append(&2, Bool, zz,
          tt))),
        ws)), Equal.cong(Jenc.Put, Jenc.Put, pp => Jenc.encode.neutral.mcus(mm, pp), Jenc.encode.ztri(W12.wput(ws)),
        W12.wput(w3), ztri_eq(ws, hh)), Equal.trans(Jenc.Put, Jenc.encode.neutral.mcus(mm, W12.wput(w3)),
          W12.wput(W12.wm(tt,
        w3)), W12.wput(W12.wm(List.append(&2, Bool, zz, List.append(&2, Bool, zz, List.append(&2, Bool, zz, tt))), ws)),
        nm(mm, w3, h3), Equal.cong(W12.WS, Jenc.Put, ss => W12.wput(ss), W12.wm(tt, w3), W12.wm(List.append(&2, Bool,
          zz,
        List.append(&2, Bool, zz, List.append(&2, Bool, zz, tt))), ws), Equal.sym(W12.WS, W12.wm(List.append(&2, Bool,
          zz,
        List.append(&2, Bool, zz, List.append(&2, Bool, zz, tt))), ws), W12.wm(tt, w3), Equal.trans(W12.WS, W12.wm(
        List.append(&2, Bool, zz, List.append(&2, Bool, zz, List.append(&2, Bool, zz, tt))), ws), W12.wm(List.append(&2,
        Bool, zz, List.append(&2, Bool, zz, tt)), W12.wm(zz, ws)), W12.wm(tt, w3), wm_app(zz, List.append(&2, Bool, zz,
        List.append(&2, Bool, zz, tt)), ws), Equal.trans(W12.WS, W12.wm(List.append(&2, Bool, zz, List.append(&2,
          Bool, zz,
        tt)), W12.wm(zz, ws)), W12.wm(List.append(&2, Bool, zz, tt), W12.wm(zz, W12.wm(zz, ws))), W12.wm(tt, w3),
          wm_app(zz,
        List.append(&2, Bool, zz, tt), W12.wm(zz, ws)), wm_app(zz, tt, W12.wm(zz, W12.wm(zz, ws)))))))))

# three zero blocks more
def zwf.s(
  +mm: Nat,
  rr: &_l: {List.length(&2, Laws.JBlkTok, ztoks(mm)) == tri(mm) : Nat} -> {Laws.jpg.allwf(ztoks(mm)) == True{} : Bool}
) -> &_l: {List.length(&2, Laws.JBlkTok,
  ztoks(1n+mm)) == tri(1n+mm) : Nat} -> {Laws.jpg.allwf(ztoks(1n+mm)) == True{} : Bool}:
  (el, ew) = rr
  (Equal.cong(Nat, Nat, kk => 1n+(1n+(1n+kk)), List.length(&2, Laws.JBlkTok, ztoks(mm)), tri(mm), el), ew)

# every zero MCU's blocks are read whole, three per MCU
def zwf(
  nn: Nat
) -> &_l: {List.length(&2, Laws.JBlkTok, ztoks(nn)) == tri(nn) : Nat} -> {Laws.jpg.allwf(ztoks(nn)) == True{} : Bool}:
  match nn:
    case 0n:
      ({==}, {==})
    case 1n+ +mm:
      zwf.s(mm, zwf(mm))

# reversing onto acc keeps every element
def lenrev.go(
  xs: List<&2, U32>,
  +acc: List<&2, U32>
) -> {List.length(&2, U32, List.reverse.go(&2, U32, xs, acc)) == Nat.add(List.length(&2, U32, xs), List.length(&2,
  U32, acc)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +hh <> +tt:
      Equal.trans(Nat, List.length(&2, U32, List.reverse.go(&2, U32, tt, hh <> acc)), Nat.add(List.length(&2, U32, tt),
        1n+List.length(&2, U32, acc)), 1n+Nat.add(List.length(&2, U32, tt), List.length(&2, U32, acc)), lenrev.go(tt,
        hh <> acc), R.add_succ(List.length(&2, U32, tt), List.length(&2, U32, acc)))

# the encoder's zigzag read, whatever the reads return, gives one value per index left and one more
def zzl(
  rest: List<&2, U32>,
  got: Array<U32> & U32,
  qv: U32 & List<&2, U32>,
  +acc: List<&2, U32>
) -> {List.length(&2, U32, Jenc.encode.zzq.go(rest, got, qv, acc)) == 1n+Nat.add(List.length(&2, U32, rest),
  List.length(&2, U32, acc)) : Nat}:
  match rest:
    case Nil{}:
      match got:
        case (_a, +vv):
          match qv:
            case (+qq, _t):
              Equal.trans(Nat, List.length(&2, U32, List.reverse.go(&2, U32, Jenc.encode.qdiv(vv, qq) <> acc, [])),
                Nat.add(1n+List.length(&2, U32, acc), 0n), 1n+List.length(&2, U32, acc), lenrev.go(Jenc.encode.qdiv(vv,
                qq) <> acc, []), R.add_zero(1n+List.length(&2, U32, acc)))
    case +gg <> +gt:
      match got:
        case (aa, +vv):
          match qv:
            case (+qq, qt):
              Equal.trans(Nat, List.length(&2, U32, Jenc.encode.zzq.go(gt, Array.get(U32, aa, gg),
                Jenc.encode.zzq.take(qt), Jenc.encode.qdiv(vv, qq) <> acc)), 1n+Nat.add(List.length(&2, U32, gt),
                1n+List.length(&2, U32, acc)), 1n+(1n+Nat.add(List.length(&2, U32, gt), List.length(&2, U32, acc))),
                zzl(gt, Array.get(U32, aa, gg), Jenc.encode.zzq.take(qt), Jenc.encode.qdiv(vv, qq) <> acc),
                Equal.cong(Nat, Nat, nn => 1n+nn, Nat.add(List.length(&2, U32, gt), 1n+List.length(&2, U32, acc)),
                1n+Nat.add(List.length(&2, U32, gt), List.length(&2, U32, acc)), R.add_succ(List.length(&2, U32, gt),
                List.length(&2, U32, acc))))

# a block's coefficients, flat or transformed, are 64
def zzlen(
  flat: Bool,
  rows: List<&2, List<&2, U32>>
) -> {List.length(&2, U32, Jenc.encode.zz(flat, rows, kern(), Jpeg.decode.zig(), Jenc.encode.quant())) == 64n : Nat}:
  match flat:
    case True{}:
      {==}
    case False{}:
      +kn = kern()
      zzl([1, 8, 16, 9, 2, 3, 10, 17, 24, 32, 25, 18, 11, 4, 5, 12, 19, 26, 33, 40, 48, 41, 34, 27, 20, 13, 6, 7, 14,
        21,
        28, 35, 42, 49, 56, 57, 50, 43, 36, 29, 22, 15, 23, 30, 37, 44, 51, 58, 59, 52, 45, 38, 31, 39, 46, 53, 60,
          61, 54,
        47, 55, 62, 63], Array.get(U32, Jenc.encode.zzq.load(Jenc.encode.fdct.go(Jenc.encode.pass1(Jenc.encode.levels(
        rows), kn, Jpeg.decode.plane(64), 0), kn), Jpeg.decode.plane(64), 0), 0), Jenc.encode.zzq.take(
        Jenc.encode.quant()), [])

# one block the solid path codes: its tile's rows, then the block coder
def BUseOut(-got: Array<U32> & List<&2, List<&2, U32>> & Bool, +pp: Jenc.Put, +pred: U32) -> Type:
  &bt: Laws.JBlkTok -> &aa: Array<U32> -> &dd: U32 -> &_e: {Jenc.encode.block.use(book(), pp, pred, got, kern(),
    Jpeg.decode.zig(), Jenc.encode.quant()) == (aa, book(), dd, Laws.jpg.feed(W12.blkbits(bt), pp)) : Array<U32> &
    Jenc.Book & U32 & Jenc.Put} -> &_h: {U32.is_lt(dd, 2048) == True{} : Bool} -> {Laws.jpg.blkwf(bt) == True{} : Bool}

# the block coder's result, with the array handed on
def buse.fin(
  aa: Array<U32>,
  -zz: List<&2, U32>,
  +pp: Jenc.Put,
  +pred: U32,
  bo: BlkOut(pred, pp, zz)
) -> &bt: Laws.JBlkTok -> &a2: Array<U32> -> &dd: U32 -> &_e: {Jenc.encode.block.pair(Jenc.encode.block.go(book(), pp,
  pred, zz), aa) == (a2, book(), dd, Laws.jpg.feed(W12.blkbits(bt),
  pp)) : Array<U32> & Jenc.Book & U32 & Jenc.Put} -> &_h:
  {U32.is_lt(dd, 2048) == True{} : Bool} -> {Laws.jpg.blkwf(bt) == True{} : Bool}:
  (+bt, +dd, eb, hd, hw) = bo
  (bt, aa, dd, Equal.cong(Jenc.Book & U32 & Jenc.Put, Array<U32> & Jenc.Book & U32 & Jenc.Put, gg =>
    Jenc.encode.block.pair(gg, aa), Jenc.encode.block.go(book(), pp, pred, zz), (book(), dd,
      Laws.jpg.feed(W12.blkbits(bt),
    pp)), eb), hd, hw)

# the solid path's block, the rows and flag named
def buse.p(
  aa: Array<U32>,
  +rows: List<&2, List<&2, U32>>,
  +flat: Bool,
  +pp: Jenc.Put,
  +pred: U32,
  hp: {U32.is_lt(pred, 2048) == True{} : Bool}
) -> BUseOut((aa, rows, flat), pp, pred):
  buse.fin(aa, Jenc.encode.zz(flat, rows, kern(), Jpeg.decode.zig(), Jenc.encode.quant()), pp, pred, blk(
    Jenc.encode.zz(flat, rows, kern(), Jpeg.decode.zig(), Jenc.encode.quant()), pred, pp, zzlen(flat, rows), hp))

# the solid path's block, the rows and flag together
def buse.r(
  aa: Array<U32>,
  rf: List<&2, List<&2, U32>> & Bool,
  +pp: Jenc.Put,
  +pred: U32,
  hp: {U32.is_lt(pred, 2048) == True{} : Bool}
) -> BUseOut((aa, rf), pp, pred):
  match rf:
    case (+rows, +flat):
      buse.p(aa, rows, flat, pp, pred, hp)

# the solid path's block, whatever the tile's rows are
def buse(
  got: Array<U32> & List<&2, List<&2, U32>> & Bool,
  +pp: Jenc.Put,
  +pred: U32,
  hp: {U32.is_lt(pred, 2048) == True{} : Bool}
) -> BUseOut(got, pp, pred):
  match got:
    case (aa, rf):
      buse.r(aa, rf, pp, pred, hp)

# the rows the solid path reads for one component of its one-pixel picture
def srows(aa: Array<U32>, +ch: U32) -> Array<U32> & List<&2, List<&2, U32>> & Bool:
  Jenc.encode.rows(8n, Jenc.encode.rowpix(8n, Jenc.encode.sample(aa, 1, 1, 0, 0, ch), 1, 1, 0, 0, ch), 1, 1, 0, 0, ch)

# the solid path's first MCU: three blocks the decoder reads whole
def SolOut(-aa: Array<U32>, +bit: Jenc.Put) -> Type:
  &t1: Laws.JBlkTok -> &t2: Laws.JBlkTok -> &t3: Laws.JBlkTok -> &_e: {Jenc.encode.solid.y(aa, book(), bit,
    Jenc.encode.ctx()) ==
    feed3b(t1, t2, t3,
      bit) : Jenc.Put} -> &_w1: {Laws.jpg.blkwf(t1) == True{} : Bool} -> &_w2: {Laws.jpg.blkwf(t2) == True{} :
    Bool} -> {Laws.jpg.blkwf(t3) == True{} : Bool}

# the type of sol3's parameter e1
def sol3.e1.ty(_aa: Array<U32>, +_bit: Jenc.Put, +_t1: Laws.JBlkTok, _a1: Array<U32>, +_d1: U32) -> Type:
  {Jenc.encode.block.use(book(), _bit, 1024, srows(_aa, 0), kern(), Jpeg.decode.zig(), Jenc.encode.quant()) == (_a1,
    book(), _d1, Laws.jpg.feed(W12.blkbits(_t1), _bit)) : Array<U32> & Jenc.Book & U32 & Jenc.Put}

# the type of sol3's parameter e2
def sol3.e2.ty(
  +_bit: Jenc.Put,
  +_t1: Laws.JBlkTok,
  _a1: Array<U32>,
  +_t2: Laws.JBlkTok,
  _a2: Array<U32>,
  +_d2: U32
) -> Type:
  {Jenc.encode.block.use(book(), Laws.jpg.feed(W12.blkbits(_t1), _bit), 1024, srows(_a1, 1), kern(),
    Jpeg.decode.zig(), Jenc.encode.quant()) == (_a2, book(), _d2, Laws.jpg.feed(W12.blkbits(_t2),
    Laws.jpg.feed(W12.blkbits(_t1), _bit))) : Array<U32> & Jenc.Book & U32 & Jenc.Put}

# the solid path's Cr block, after its Y and Cb blocks
def sol3(
  -aa: Array<U32>,
  +bit: Jenc.Put,
  +t1: Laws.JBlkTok,
  -a1: Array<U32>,
  +d1: U32,
  e1: sol3.e1.ty(aa, bit, t1, a1, d1),
  w1: {Laws.jpg.blkwf(t1) == True{} : Bool},
  +t2: Laws.JBlkTok,
  -a2: Array<U32>,
  +d2: U32,
  e2: sol3.e2.ty(bit, t1, a1, t2, a2, d2),
  w2: {Laws.jpg.blkwf(t2) == True{} : Bool},
  b3: BUseOut(srows(a2, 2), Laws.jpg.feed(W12.blkbits(t2), Laws.jpg.feed(W12.blkbits(t1), bit)), 1024)
) -> SolOut(aa, bit):
  (+t3, a3, +d3, e3, _h, w3) = b3
  +cx = Jenc.encode.ctx()
  +kn = kern()
  +zg = Jpeg.decode.zig()
  +qs = Jenc.encode.quant()
  +p1 = Laws.jpg.feed(W12.blkbits(t1), bit)
  +p2 = Laws.jpg.feed(W12.blkbits(t2), p1)
  +p3 = Laws.jpg.feed(W12.blkbits(t3), p2)
  (t1, t2, t3, Equal.trans(Jenc.Put, Jenc.encode.solid.cb(Jenc.encode.block.use(book(), bit, 1024, srows(aa, 0), kn,
    zg, qs), cx), Jenc.encode.solid.cb((a1, book(), d1, p1), cx), p3, Equal.cong(Array<U32> & Jenc.Book & U32 &
    Jenc.Put, Jenc.Put, gg => Jenc.encode.solid.cb(gg, cx), Jenc.encode.block.use(book(), bit, 1024, srows(aa, 0), kn,
    zg, qs), (a1, book(), d1, p1), e1), Equal.trans(Jenc.Put, Jenc.encode.solid.cr(Jenc.encode.block.use(book(),
    p1, 1024, srows(a1, 1), kn, zg, qs), cx), Jenc.encode.solid.cr((a2, book(), d2, p2), cx), p3, Equal.cong(
    Array<U32> & Jenc.Book & U32 & Jenc.Put, Jenc.Put, gg => Jenc.encode.solid.cr(gg, cx), Jenc.encode.block.use(
    book(), p1, 1024, srows(a1, 1), kn, zg, qs), (a2, book(), d2, p2), e2), Equal.cong(Array<U32> & Jenc.Book &
    U32 & Jenc.Put, Jenc.Put, gg => Jenc.encode.solid.end(gg), Jenc.encode.block.use(book(), p2, 1024, srows(a2, 2),
    kn, zg, qs), (a3, book(), d3, p3), e3))), w1, w2, w3)

# the type of sol2's parameter e1
def sol2.e1.ty(_aa: Array<U32>, +_bit: Jenc.Put, +_t1: Laws.JBlkTok, _a1: Array<U32>, +_d1: U32) -> Type:
  {Jenc.encode.block.use(book(), _bit, 1024, srows(_aa, 0), kern(), Jpeg.decode.zig(), Jenc.encode.quant()) == (_a1,
    book(), _d1, Laws.jpg.feed(W12.blkbits(_t1), _bit)) : Array<U32> & Jenc.Book & U32 & Jenc.Put}

# the solid path's Cb and Cr blocks, after its Y block
def sol2(
  -aa: Array<U32>,
  +bit: Jenc.Put,
  +t1: Laws.JBlkTok,
  -a1: Array<U32>,
  +d1: U32,
  e1: sol2.e1.ty(aa, bit, t1, a1, d1),
  w1: {Laws.jpg.blkwf(t1) == True{} : Bool},
  b2: BUseOut(srows(a1, 1), Laws.jpg.feed(W12.blkbits(t1), bit), 1024)
) -> SolOut(aa, bit):
  (+t2, a2, +d2, e2, _h, w2) = b2
  sol3(aa, bit, t1, a1, d1, e1, w1, t2, a2, d2, e2, w2, buse(srows(a2, 2), Laws.jpg.feed(W12.blkbits(t2), Laws.jpg.feed(
    W12.blkbits(t1), bit)), 1024, {==}))

# the solid path's blocks, after its Y block
def sol1(-aa: Array<U32>, +bit: Jenc.Put, b1: BUseOut(srows(aa, 0), bit, 1024)) -> SolOut(aa, bit):
  (+t1, a1, +d1, e1, _h, w1) = b1
  sol2(aa, bit, t1, a1, d1, e1, w1, buse(srows(a1, 1), Laws.jpg.feed(W12.blkbits(t1), bit), 1024, {==}))

# the solid path's first MCU, whatever its one pixel holds
def sol(aa: Array<U32>, +bit: Jenc.Put) -> SolOut(aa, bit):
  sol1(aa, bit, buse(srows(aa, 0), bit, 1024, {==}))

# the encoder's MCU count
def mcun(+ww: U32, +hh: U32) -> U32:
  (U32.div((ww + 7 : U32), 8) * U32.div((hh + 7 : U32), 8) : U32)

# the statement of bookeq
def bookeq.ty() -> Type:
  {Jenc.encode.book(Jenc.encode.dccounts(), Jenc.encode.dcsyms(), Jenc.encode.accounts(),
    Jenc.encode.acsyms()) == book() : Jenc.Book}

# the encoder's books are the books written out
def bookeq() -> bookeq.ty():
  Equal.trans(Jenc.Book, Jenc.Book{Jenc.encode.huff(Jenc.encode.dccounts(), Jenc.encode.dcsyms()), Jenc.encode.huff(
    Jenc.encode.accounts(), Jenc.encode.acsyms())}, Jenc.Book{W12.dcbook.lit(), Jenc.encode.huff(Jenc.encode.accounts(),
    Jenc.encode.acsyms())}, book(), Equal.cong(Array<U32>, Jenc.Book, xx => Jenc.Book{xx, Jenc.encode.huff(
    Jenc.encode.accounts(), Jenc.encode.acsyms())}, Jenc.encode.huff(Jenc.encode.dccounts(), Jenc.encode.dcsyms()),
    W12.dcbook.lit(), W12.dcbook.eq()), Equal.cong(Array<U32>, Jenc.Book, xx => Jenc.Book{W12.dcbook.lit(), xx},
    Jenc.encode.huff(Jenc.encode.accounts(), Jenc.encode.acsyms()), W12.acbook.lit(), W12.acbook.eq()))

# blocks' bits, two lists joined
def tbits_app(
  xs: List<&2, Laws.JBlkTok>,
  +ys: List<&2, Laws.JBlkTok>
) -> {W12.tbits(List.append(&2, Laws.JBlkTok, xs, ys)) == List.append(&2, Bool, W12.tbits(xs),
  W12.tbits(ys)) : List<&2, Bool>}:
  match xs:
    case Nil{}:
      {==}
    case +tt <> +rest:
      Equal.trans(List<&2, Bool>, List.append(&2, Bool, W12.blkbits(tt), W12.tbits(List.append(&2, Laws.JBlkTok, rest,
        ys))),
        List.append(&2, Bool, W12.blkbits(tt), List.append(&2, Bool, W12.tbits(rest), W12.tbits(ys))), List.append(&2,
          Bool,
        List.append(&2, Bool, W12.blkbits(tt), W12.tbits(rest)), W12.tbits(ys)), Equal.cong(List<&2, Bool>, List<&2,
          Bool>,
        zs => List.append(&2, Bool, W12.blkbits(tt), zs), W12.tbits(List.append(&2, Laws.JBlkTok, rest, ys)),
          List.append(&2,
        Bool, W12.tbits(rest), W12.tbits(ys)), tbits_app(rest, ys)), Equal.sym(List<&2, Bool>, List.append(&2, Bool,
        List.append(&2, Bool, W12.blkbits(tt), W12.tbits(rest)), W12.tbits(ys)), List.append(&2, Bool, W12.blkbits(tt),
        List.append(&2, Bool, W12.tbits(rest), W12.tbits(ys))), W12.app_assoc(W12.blkbits(tt), W12.tbits(rest),
        W12.tbits(ys))))

# a list of blocks, n MCUs' worth, each read whole
def ZOut(+_zs: List<&2, Laws.JBlkTok>, +_nn: Nat) -> Type:
  &_l: {List.length(&2, Laws.JBlkTok, _zs) == tri(_nn) : Nat} -> {Laws.jpg.allwf(_zs) == True{} : Bool}

# a path's entropy-coded bytes: blocks the decoder reads whole, three per MCU, fed to the writer and padded
def PathOut(-bytes: List<&2, U32>, +nn: Nat) -> Type:
  &ts: List<&2, Laws.JBlkTok> -> &_e: {bytes == Jenc.encode.pad(Laws.jpg.feed(W12.tbits(ts),
    Jenc.encode.put0())) : List<&2, U32>} ->
    &_l: {List.length(&2, Laws.JBlkTok, ts) == tri(nn) : Nat} -> {Laws.jpg.allwf(ts) == True{} : Bool}

# the neutral path, the zero blocks' count and checks named
def neutral_fin(
  +ww: U32,
  +hh: U32,
  rr: ZOut(ztoks(U32.to_nat(mcun(ww, hh))), U32.to_nat(mcun(ww, hh)))
) -> PathOut(Jenc.encode.neutral(ww, hh), U32.to_nat(mcun(ww, hh))):
  (el, ew) = rr
  +nn = U32.to_nat(mcun(ww, hh))
  +ws = {W12.WS{[], []} : W12.WS}
  +zt = W12.tbits(ztoks(nn))
  (ztoks(nn), Equal.cong(Jenc.Put, List<&2, U32>, pp => Jenc.encode.pad(pp), Jenc.encode.neutral.mcus(nn, W12.wput(ws)),
    Laws.jpg.feed(zt, W12.wput(ws)), Equal.trans(Jenc.Put, Jenc.encode.neutral.mcus(nn, W12.wput(ws)),
      W12.wput(W12.wm(zt, ws)),
    Laws.jpg.feed(zt, W12.wput(ws)), nm(nn, ws, {==}), Equal.sym(Jenc.Put, Laws.jpg.feed(zt, W12.wput(ws)),
      W12.wput(W12.wm(zt, ws)),
    W12.wfeed(zt, ws, {==})))), el, ew)

# the neutral path
def neutral_ok(+ww: U32, +hh: U32) -> PathOut(Jenc.encode.neutral(ww, hh), U32.to_nat(mcun(ww, hh))):
  neutral_fin(ww, hh, zwf(U32.to_nat(mcun(ww, hh))))

# the type of go_fin's parameter rr
def go_fin.rr.ty(+_ww: U32, +_hh: U32, +_px: List<&2, U32>) -> Type:
  McusOut(U32.to_nat(mcun(_ww, _hh)), Jenc.encode.pix.load(U32.to_nat((_ww * _hh : U32)), _px,
    Jpeg.decode.plane((_ww * _hh : U32)), 0), 1024, 1024, 1024, Jenc.encode.put0(), 0, 0, U32.div((_ww + 7 : U32), 8),
    _ww, _hh)

# the go path, its MCU loop's blocks named
def go_fin(
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  rr: go_fin.rr.ty(ww, hh, px)
) -> PathOut(Jenc.encode.go(ww, hh, px), U32.to_nat(mcun(ww, hh))):
  (+ts, er, el, ew) = rr
  +nn = U32.to_nat(mcun(ww, hh))
  +mw = U32.div((ww + 7 : U32), 8)
  +cx = Jenc.encode.ctx()
  +p0 = Jenc.encode.put0()
  (ts, Equal.cong(Jenc.Put, List<&2, U32>, pp => Jenc.encode.pad(pp), Jenc.encode.mcus(nn, (Jenc.encode.pix.load(
    U32.to_nat((ww * hh : U32)), px, Jpeg.decode.plane((ww * hh : U32)), 0), Jenc.encode.book(Jenc.encode.dccounts(),
    Jenc.encode.dcsyms(), Jenc.encode.accounts(), Jenc.encode.acsyms()), 1024, 1024, 1024, p0), 0, 0, mw, ww, hh, cx),
    Laws.jpg.feed(W12.tbits(ts), p0), Equal.trans(Jenc.Put, Jenc.encode.mcus(nn,
      (Jenc.encode.pix.load(U32.to_nat((ww * hh :
    U32)), px, Jpeg.decode.plane((ww * hh : U32)), 0), Jenc.encode.book(Jenc.encode.dccounts(), Jenc.encode.dcsyms(),
    Jenc.encode.accounts(), Jenc.encode.acsyms()), 1024, 1024, 1024, p0), 0, 0, mw, ww, hh, cx), Jenc.encode.mcus(nn,
    (Jenc.encode.pix.load(U32.to_nat((ww * hh : U32)), px, Jpeg.decode.plane((ww * hh : U32)), 0), book(), 1024, 1024,
    1024, p0), 0, 0, mw, ww, hh, cx), Laws.jpg.feed(W12.tbits(ts), p0), Equal.cong(Jenc.Book, Jenc.Put, bk =>
    Jenc.encode.mcus(nn, (Jenc.encode.pix.load(U32.to_nat((ww * hh : U32)), px, Jpeg.decode.plane((ww * hh : U32)), 0),
    bk, 1024, 1024, 1024, p0), 0, 0, mw, ww, hh, cx), Jenc.encode.book(Jenc.encode.dccounts(), Jenc.encode.dcsyms(),
    Jenc.encode.accounts(), Jenc.encode.acsyms()), book(), bookeq()), er)), el, ew)

# the go path
def go_ok(+ww: U32, +hh: U32, +px: List<&2, U32>) -> PathOut(Jenc.encode.go(ww, hh, px), U32.to_nat(mcun(ww, hh))):
  go_fin(ww, hh, px, mcus_ok(U32.to_nat(mcun(ww, hh)), Jenc.encode.pix.load(U32.to_nat((ww * hh : U32)), px,
    Jpeg.decode.plane((ww * hh : U32)), 0), 1024, 1024, 1024, Jenc.encode.put0(), 0, 0, U32.div((ww + 7 : U32), 8), ww,
    hh, {==}, {==}, {==}))

# the solid path's first MCU is the model writer fed its blocks' bits
def sol_ws(
  +t1: Laws.JBlkTok,
  +t2: Laws.JBlkTok,
  +t3: Laws.JBlkTok
) -> {feed3b(t1, t2, t3, Jenc.encode.put0()) == W12.wput(W12.wm(W12.tbits( t1 <> t2 <> t3 <> []), W12.WS{[],
  []})) : Jenc.Put}:
  +ws = {W12.WS{[], []} : W12.WS}
  +tb = W12.tbits(t1 <> t2 <> t3 <> [])
  Equal.trans(Jenc.Put, feed3b(t1, t2, t3, W12.wput(ws)), Laws.jpg.feed(tb, W12.wput(ws)), W12.wput(W12.wm(tb, ws)),
    feed_tri(t1, t2, t3, [], W12.wput(ws)), W12.wfeed(tb, ws, {==}))

# the solid path, its first MCU named
def solid_fin(
  +ww: U32,
  +hh: U32,
  +color: U32,
  so: SolOut(Array.set(U32, Jpeg.decode.plane(1), 0, color), Jenc.encode.put0()),
  rr: ZOut(ztoks(U32.to_nat((mcun(ww, hh) - 1 : U32))), U32.to_nat((mcun(ww, hh) - 1 : U32)))
) -> PathOut(Jenc.encode.solid(ww, hh, color), 1n+U32.to_nat((mcun(ww, hh) - 1 : U32))):
  (+t1, +t2, +t3, es, w1, w2, w3) = so
  (el, ew) = rr
  +kk = U32.to_nat((mcun(ww, hh) - 1 : U32))
  +ws = {W12.WS{[], []} : W12.WS}
  +xb = W12.tbits(t1 <> t2 <> t3 <> [])
  +zk = ztoks(kk)
  +zt = W12.tbits(zk)
  +w1s = W12.wm(xb, ws)
  +hs = {wm_short(xb, ws, {==}) : {W12.wshort(w1s) == True{} : Bool}}
  +p0 = Jenc.encode.put0()
  +cx = Jenc.encode.ctx()
  +ts = {t1 <> t2 <> t3 <> zk : List<&2, Laws.JBlkTok>}
  (ts, Equal.cong(Jenc.Put, List<&2, U32>, pp => Jenc.encode.pad(pp), Jenc.encode.neutral.mcus(kk, Jenc.encode.solid.y(
    Array.set(U32, Jpeg.decode.plane(1), 0, color), Jenc.encode.book(Jenc.encode.dccounts(), Jenc.encode.dcsyms(),
      Jenc.encode.accounts(), Jenc.encode.acsyms()),
    p0, cx)), Laws.jpg.feed(W12.tbits(ts), p0), Equal.trans(Jenc.Put, Jenc.encode.neutral.mcus(kk,
      Jenc.encode.solid.y(Array.set(U32, Jpeg.decode.plane(1), 0, color),
    Jenc.encode.book(Jenc.encode.dccounts(), Jenc.encode.dcsyms(), Jenc.encode.accounts(), Jenc.encode.acsyms()), p0,
    cx)), Jenc.encode.neutral.mcus(kk, W12.wput(w1s)), Laws.jpg.feed(W12.tbits(ts), p0), Equal.cong(Jenc.Put,
      Jenc.Put, pp =>
    Jenc.encode.neutral.mcus(kk, pp), Jenc.encode.solid.y(Array.set(U32, Jpeg.decode.plane(1), 0, color),
      Jenc.encode.book(Jenc.encode.dccounts(),
    Jenc.encode.dcsyms(), Jenc.encode.accounts(), Jenc.encode.acsyms()), p0, cx), W12.wput(w1s), Equal.trans(Jenc.Put,
    Jenc.encode.solid.y(Array.set(U32, Jpeg.decode.plane(1), 0, color), Jenc.encode.book(Jenc.encode.dccounts(),
      Jenc.encode.dcsyms(), Jenc.encode.accounts(),
    Jenc.encode.acsyms()), p0, cx), Jenc.encode.solid.y(Array.set(U32, Jpeg.decode.plane(1), 0, color), book(), p0,
      cx), W12.wput(w1s), Equal.cong(Jenc.Book,
    Jenc.Put, bk => Jenc.encode.solid.y(Array.set(U32, Jpeg.decode.plane(1), 0, color), bk, p0, cx),
      Jenc.encode.book(Jenc.encode.dccounts(), Jenc.encode.dcsyms(),
    Jenc.encode.accounts(), Jenc.encode.acsyms()), book(), bookeq()), Equal.trans(Jenc.Put,
      Jenc.encode.solid.y(Array.set(U32, Jpeg.decode.plane(1), 0, color),
    book(), p0, cx), feed3b(t1, t2, t3, p0), W12.wput(w1s), es, sol_ws(t1, t2, t3)))), Equal.trans(Jenc.Put,
    Jenc.encode.neutral.mcus(kk, W12.wput(w1s)), W12.wput(W12.wm(zt, w1s)), Laws.jpg.feed(W12.tbits(ts), p0), nm(kk,
      w1s, hs),
    Equal.trans(Jenc.Put, W12.wput(W12.wm(zt, w1s)), W12.wput(W12.wm(List.append(&2, Bool, xb, zt), ws)),
      Laws.jpg.feed(W12.tbits(
    ts), p0), Equal.cong(W12.WS, Jenc.Put, ss => W12.wput(ss), W12.wm(zt, w1s), W12.wm(List.append(&2, Bool, xb, zt),
      ws),
    Equal.sym(W12.WS, W12.wm(List.append(&2, Bool, xb, zt), ws), W12.wm(zt, w1s), wm_app(xb, zt, ws))), Equal.trans(
    Jenc.Put, W12.wput(W12.wm(List.append(&2, Bool, xb, zt), ws)), Laws.jpg.feed(List.append(&2, Bool, xb, zt), p0),
      Laws.jpg.feed(
    W12.tbits(ts), p0), Equal.sym(Jenc.Put, Laws.jpg.feed(List.append(&2, Bool, xb, zt), W12.wput(ws)), W12.wput(W12.wm(
    List.append(&2, Bool, xb, zt), ws)), W12.wfeed(List.append(&2, Bool, xb, zt), ws, {==})), Equal.cong(List<&2, Bool>,
    Jenc.Put, bs => Laws.jpg.feed(bs, p0), List.append(&2, Bool, xb, zt), W12.tbits(ts), Equal.sym(List<&2, Bool>,
      W12.tbits(ts),
    List.append(&2, Bool, xb, zt), tbits_app(t1 <> t2 <> t3 <> [], zk)))))))), Equal.cong(Nat, Nat, nn =>
    1n+(1n+(1n+nn)), List.length(&2, Laws.JBlkTok, zk), tri(kk), el), Equal.trans(Bool,
      Laws.jpg.also(Laws.jpg.blkwf(t1),
    Laws.jpg.also(Laws.jpg.blkwf(t2), Laws.jpg.also(Laws.jpg.blkwf(t3), Laws.jpg.allwf(zk)))),
      Laws.jpg.also(Laws.jpg.blkwf(t2), Laws.jpg.also(Laws.jpg.blkwf(t3),
    Laws.jpg.allwf(zk))), True{}, also_t(Laws.jpg.blkwf(t1), Laws.jpg.also(Laws.jpg.blkwf(t2),
      Laws.jpg.also(Laws.jpg.blkwf(t3), Laws.jpg.allwf(
    zk))), w1), Equal.trans(Bool, Laws.jpg.also(Laws.jpg.blkwf(t2), Laws.jpg.also(Laws.jpg.blkwf(t3),
      Laws.jpg.allwf(zk))),
    Laws.jpg.also(Laws.jpg.blkwf(t3), Laws.jpg.allwf(zk)), True{}, also_t(Laws.jpg.blkwf(t2),
      Laws.jpg.also(Laws.jpg.blkwf(t3), Laws.jpg.allwf(
    zk)), w2), Equal.trans(Bool, Laws.jpg.also(Laws.jpg.blkwf(t3), Laws.jpg.allwf(zk)),
      Laws.jpg.allwf(zk), True{},
    also_t(Laws.jpg.blkwf(t3), Laws.jpg.allwf(zk), w3), ew))))

# the solid path
def solid_ok(
  +ww: U32,
  +hh: U32,
  +color: U32
) -> PathOut(Jenc.encode.solid(ww, hh, color), 1n+U32.to_nat((mcun(ww, hh) - 1 : U32))):
  solid_fin(ww, hh, color, sol(Array.set(U32, Jpeg.decode.plane(1), 0, color), Jenc.encode.put0()), zwf(U32.to_nat((
    mcun(ww, hh) - 1 : U32))))

# a path's blocks, counted again
def path_tr(
  -bytes: List<&2, U32>,
  +aa: Nat,
  +bb: Nat,
  ee: {aa == bb : Nat},
  po: PathOut(bytes, aa)
) -> PathOut(bytes, bb):
  %ee : PathOut(bytes, _)
  po

# the path the watch picks
def disp(
  neu: Bool,
  sol: Bool,
  +color: U32,
  +px: List<&2, U32>,
  +ww: U32,
  +hh: U32,
  hn: {1n+U32.to_nat((mcun(ww, hh) - 1 : U32)) == U32.to_nat(mcun(ww, hh)) : Nat}
) -> PathOut(Jenc.encode.dispatch.b(neu, sol, color, px, ww, hh), U32.to_nat(mcun(ww, hh))):
  match neu:
    case True{}:
      neutral_ok(ww, hh)
    case False{}:
      match sol:
        case True{}:
          path_tr(Jenc.encode.solid(ww, hh, color), 1n+U32.to_nat((mcun(ww, hh) - 1 : U32)), U32.to_nat(mcun(ww, hh)),
            hn,
            solid_ok(ww, hh, color))
        case False{}:
          go_ok(ww, hh, px)

# whatever the watch finds, its colour and samples together
def arm_use2(
  +tag: U32,
  rest: U32 & List<&2, U32>,
  +ww: U32,
  +hh: U32,
  hn: {1n+U32.to_nat((mcun(ww, hh) - 1 : U32)) == U32.to_nat(mcun(ww, hh)) : Nat}
) -> PathOut(Jenc.encode.arm.use((tag, rest), ww, hh), U32.to_nat(mcun(ww, hh))):
  match rest:
    case (+color, +px):
      disp(U32.is_eq(tag, 0), U32.is_eq(tag, 1), color, px, ww, hh, hn)

# whatever the watch finds
def arm_use(
  got: U32 & U32 & List<&2, U32>,
  +ww: U32,
  +hh: U32,
  hn: {1n+U32.to_nat((mcun(ww, hh) - 1 : U32)) == U32.to_nat(mcun(ww, hh)) : Nat}
) -> PathOut(Jenc.encode.arm.use(got, ww, hh), U32.to_nat(mcun(ww, hh))):
  match got:
    case (+tag, rest):
      arm_use2(tag, rest, ww, hh, hn)

# the encoder's entropy-coded bytes are blocks the decoder reads whole, three per MCU, fed to the writer and padded
def arm_ok(
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  hn: {1n+U32.to_nat((mcun(ww, hh) - 1 : U32)) == U32.to_nat(mcun(ww, hh)) : Nat}
) -> PathOut(Jenc.encode.arm(ww, hh, px), U32.to_nat(mcun(ww, hh))):
  arm_use(Jenc.encode.watch(U32.to_nat((ww * hh : U32)), px), ww, hh, hn)

# eight times a number
def eight(nn: Nat) -> Nat:
  Nat.double(Nat.double(Nat.double(nn)))

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
def shl_top(nn: Nat, +cc: Bool, ww: Word(1n+nn)) -> {fst.bw(1n+nn, Word.shl.out(1n+nn, cc, ww)) == wtop(nn, ww) : Bool}:
  match nn:
    case 0n:
      match ww:
        case WCon{_b, _t}:
          {==}
    case 1n+ +pp:
      match ww:
        case WCon{+bb, +tt}:
          Equal.trans(Bool, fst.bw(2n+pp, Word.shl.out.con(1n+pp, cc, Word.shl.out(1n+pp, bb, tt))), fst.bw(1n+pp,
            Word.shl.out(1n+pp, bb, tt)), wtop(pp, tt), Equal.cong(Bool & Word(2n+pp), Bool, xx => fst.bw(2n+pp, xx),
            Word.shl.out.con(1n+pp, cc, Word.shl.out(1n+pp, bb, tt)), (fst.bw(1n+pp, Word.shl.out(1n+pp, bb, tt)),
            WCon{cc, snd.bw(1n+pp, Word.shl.out(1n+pp, bb, tt))}), con_eta(1n+pp, cc, Word.shl.out(1n+pp, bb, tt))),
            shl_top(pp, bb, tt))

# the word a shift out leaves, when the top bit is clear, is c plus twice the word
def shl_nat(
  nn: Nat,
  +cc: Bool,
  ww: Word(1n+nn),
  hh: {wtop(nn, ww) == False{} : Bool}
) -> {Word.to_nat(1n+nn, snd.bw(1n+nn, Word.shl.out(1n+nn, cc, ww))) == Nat.add(R.bit(cc),
  Nat.double(Word.to_nat(1n+nn, ww))) : Nat}:
  match nn:
    case 0n:
      match ww:
        case WCon{False{}, WNil{}}:
          R.to_nat_con(0n, cc, WNil{})
        case WCon{True{}, WNil{}}:
          Empty.absurd({Word.to_nat(1n, snd.bw(1n, Word.shl.out(1n, cc, WCon{True{}, WNil{}}))) == Nat.add(R.bit(cc),
            Nat.double(Word.to_nat(1n, WCon{True{}, WNil{}}))) : Nat}, true_false(hh))
    case 1n+ +pp:
      match ww:
        case WCon{+bb, +tt}:
          +sx = snd.bw(1n+pp, Word.shl.out(1n+pp, bb, tt))
          +tn = Word.to_nat(1n+pp, tt)
          Equal.trans(Nat, Word.to_nat(2n+pp, snd.bw(2n+pp, Word.shl.out.con(1n+pp, cc, Word.shl.out(1n+pp, bb, tt)))),
            Word.to_nat(2n+pp, WCon{cc, sx}), Nat.add(R.bit(cc), Nat.double(Word.to_nat(2n+pp, WCon{bb, tt}))),
            Equal.cong(Bool & Word(2n+pp), Nat, xx => Word.to_nat(2n+pp, snd.bw(2n+pp, xx)), Word.shl.out.con(1n+pp, cc,
            Word.shl.out(1n+pp, bb, tt)), (fst.bw(1n+pp, Word.shl.out(1n+pp, bb, tt)), WCon{cc, sx}), con_eta(1n+pp, cc,
            Word.shl.out(1n+pp, bb, tt))), Equal.trans(Nat, Word.to_nat(2n+pp, WCon{cc, sx}), Nat.add(R.bit(cc),
            Nat.double(Word.to_nat(1n+pp, sx))), Nat.add(R.bit(cc), Nat.double(Word.to_nat(2n+pp, WCon{bb, tt}))),
            R.to_nat_con(1n+pp, cc, sx), Equal.cong(Nat, Nat, xx => Nat.add(R.bit(cc), Nat.double(xx)),
              Word.to_nat(1n+pp,
            sx), Word.to_nat(2n+pp, WCon{bb, tt}), Equal.trans(Nat, Word.to_nat(1n+pp, sx), Nat.add(R.bit(bb),
            Nat.double(tn)), Word.to_nat(2n+pp, WCon{bb, tt}), shl_nat(pp, bb, tt, hh), Equal.sym(Nat,
            Word.to_nat(2n+pp, WCon{bb, tt}), Nat.add(R.bit(bb), Nat.double(tn)), R.to_nat_con(1n+pp, bb, tt))))))

# the quotient of a long division
def dq(+pp: Nat, pr: Word(pp) & U32) -> Word(pp):
  match pr:
    case (qq, _r):
      qq

# the remainder of a long division
def dr(+pp: Nat, pr: Word(pp) & U32) -> U32:
  match pr:
    case (_q, rr):
      rr

# a long division by 8 of a word of m bits: the word is the remainder and eight times the quotient, the remainder
# below 8
def DivInv(+mm: Nat, -aa: Word(mm)) -> Type:
  &_e: {Word.to_nat(mm, aa) == Nat.add(U32.to_nat(dr(mm, U32.divmod.go(mm, aa, 8))), eight(Word.to_nat(mm, dq(mm,
    U32.divmod.go(mm, aa, 8))))) : Nat} -> {U32.is_lt(dr(mm, U32.divmod.go(mm, aa, 8)), 8) == True{} : Bool}

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
      Empty.absurd({Cmp.is_lt(EQ{}) == True{} : Bool}, true_false(hh))
    case GT{}:
      Empty.absurd({Cmp.is_lt(GT{}) == True{} : Bool}, true_false(hh))

# twice a number below n is below twice n
def lt_dbl0(
  rr: Nat,
  nn: Nat,
  hh: {Nat.is_lt(rr, nn) == True{} : Bool}
) -> {Nat.is_lt(Nat.double(rr), Nat.double(nn)) == True{} : Bool}:
  match rr nn:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, W12.false_true(hh))
    case 0n 1n+_m:
      {==}
    case 1n+_r 0n:
      Empty.absurd({Nat.is_lt(Nat.double(1n+_r), 0n) == True{} : Bool}, W12.false_true(hh))
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
      Empty.absurd({Nat.is_lt(1n, 0n) == True{} : Bool}, W12.false_true(hh))
    case 0n 1n+_m:
      {==}
    case 1n+_r 0n:
      Empty.absurd({Nat.is_lt(1n+Nat.double(1n+_r), 0n) == True{} : Bool}, W12.false_true(hh))
    case 1n+rp 1n+mp:
      lt_dbl1(rp, mp, hh)

# a bit and twice a number below n are below twice n
def lt_dbl(
  bb: Bool,
  rr: Nat,
  nn: Nat,
  hh: {Nat.is_lt(rr, nn) == True{} : Bool}
) -> {Nat.is_lt(Nat.add(R.bit(bb), Nat.double(rr)), Nat.double(nn)) == True{} : Bool}:
  match bb:
    case False{}:
      lt_dbl0(rr, nn, hh)
    case True{}:
      lt_dbl1(rr, nn, hh)

# the type of divg's parameter eh
def divg.eh.ty(+_pp: Nat, +_a0: Bool, +_hi: Word(_pp), +_qq: Word(_pp), +_rn: Nat) -> Type:
  {Word.to_nat(1n+_pp, WCon{_a0, _hi}) == Nat.add(Nat.add(R.bit(_a0), Nat.double(_rn)),
    Nat.double(eight(Word.to_nat(_pp, _qq)))) : Nat}

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
  +es: {Word.to_nat(32n, ss) == Nat.add(R.bit(a0), Nat.double(rn)) : Nat},
  eh0: divg.eh.ty(pp, a0, hi, qq, rn),
  +hr: {Nat.is_lt(rn, 8n) == True{} : Bool}
) -> &_e: {Word.to_nat(1n+pp, WCon{a0, hi}) == Nat.add(U32.to_nat(dr(1n+pp, U32.divmod.go.fin(pp, qq, U32{ss}, 8,
  gg))), eight(Word.to_nat(1n+pp, dq(1n+pp, U32.divmod.go.fin(pp, qq, U32{ss}, 8,
  gg))))) : Nat} -> {U32.is_lt(dr(1n+pp, U32.divmod.go.fin(pp, qq, U32{ss}, 8, gg)), 8) == True{} : Bool}:
  match gg:
    case False{}:
      +eh = {eh0 : {Word.to_nat(1n+pp, WCon{a0, hi}) == Nat.add(Nat.add(R.bit(a0), Nat.double(rn)),
        Nat.double(eight(Word.to_nat(pp, qq)))) : Nat}}
      +sn = Word.to_nat(32n, ss)
      (Equal.trans(Nat, Word.to_nat(1n+pp, WCon{a0, hi}), Nat.add(Nat.add(R.bit(a0), Nat.double(rn)), Nat.double(eight(
        Word.to_nat(pp, qq)))), Nat.add(sn, Nat.double(eight(Word.to_nat(pp, qq)))), eh, Equal.cong(Nat, Nat, xx =>
        Nat.add(xx, Nat.double(eight(Word.to_nat(pp, qq)))), Nat.add(R.bit(a0), Nat.double(rn)), sn, Equal.sym(Nat, sn,
        Nat.add(R.bit(a0), Nat.double(rn)), es))), nge_lt(U32.cmp(U32{ss}, 8), hg))
    case True{}:
      +eh = {eh0 : {Word.to_nat(1n+pp, WCon{a0, hi}) == Nat.add(Nat.add(R.bit(a0), Nat.double(rn)),
        Nat.double(eight(Word.to_nat(pp, qq)))) : Nat}}
      +sn = Word.to_nat(32n, ss)
      +dd = Nat.double(eight(Word.to_nat(pp, qq)))
      +h8 = {Equal.trans(Bool, Nat.is_le(8n, sn), Cmp.is_ge(Nat.cmp(sn, 8n)), True{}, Equal.sym(Bool,
        Cmp.is_ge(Nat.cmp(sn,
        8n)), Nat.is_le(8n, sn), ge_le(sn, 8n)), Equal.trans(Bool, Cmp.is_ge(Nat.cmp(sn, 8n)), U32.is_ge(U32{ss}, 8),
        True{}, Equal.cong(Cmp, Bool, cc => Cmp.is_ge(cc), Nat.cmp(sn, 8n), U32.cmp(U32{ss}, 8), Equal.sym(Cmp,
        U32.cmp(U32{ss}, 8), Nat.cmp(sn, 8n), u_cmp(U32{ss}, 8))), hg)) : {Nat.is_le(8n, sn) == True{} : Bool}}
      +er = {R.u32_sub_nat(U32{ss}, 8, h8) : {U32.to_nat((U32{ss} - 8 : U32)) == Nat.sub(sn, 8n) : Nat}}
      +h16 = {Equal.trans(Bool, Nat.is_lt(sn, 16n), Nat.is_lt(Nat.add(R.bit(a0), Nat.double(rn)), 16n), True{},
        Equal.cong(Nat, Bool, xx => Nat.is_lt(xx, 16n), sn, Nat.add(R.bit(a0), Nat.double(rn)), es), lt_dbl(a0, rn, 8n,
        hr)) : {Nat.is_lt(sn, 16n) == True{} : Bool}}
      (Equal.trans(Nat, Word.to_nat(1n+pp, WCon{a0, hi}), Nat.add(sn, dd), Nat.add(U32.to_nat((U32{ss} - 8 : U32)),
        8n+dd), Equal.trans(Nat, Word.to_nat(1n+pp, WCon{a0, hi}), Nat.add(Nat.add(R.bit(a0), Nat.double(rn)), dd),
        Nat.add(sn, dd), eh, Equal.cong(Nat, Nat, xx => Nat.add(xx, dd), Nat.add(R.bit(a0), Nat.double(rn)), sn,
        Equal.sym(Nat, sn, Nat.add(R.bit(a0), Nat.double(rn)), es))), Equal.sym(Nat, Nat.add(U32.to_nat((U32{ss} - 8 :
        U32)), 8n+dd), Nat.add(sn, dd), Equal.trans(Nat, Nat.add(U32.to_nat((U32{ss} - 8 : U32)), 8n+dd), Nat.add(
        Nat.sub(sn, 8n), 8n+dd), Nat.add(sn, dd), Equal.cong(Nat, Nat, xx => Nat.add(xx, 8n+dd), U32.to_nat((U32{ss} - 8
        : U32)), Nat.sub(sn, 8n), er), Equal.trans(Nat, Nat.add(Nat.sub(sn, 8n), Nat.add(8n, dd)), Nat.add(8n, Nat.add(
        Nat.sub(sn, 8n), dd)), Nat.add(sn, dd), R.add_swap(Nat.sub(sn, 8n), 8n, dd), Equal.trans(Nat, Nat.add(8n,
        Nat.add(Nat.sub(sn, 8n), dd)), Nat.add(Nat.add(8n, Nat.sub(sn, 8n)), dd), Nat.add(sn, dd), Equal.sym(Nat,
        Nat.add(Nat.add(8n, Nat.sub(sn, 8n)), dd), Nat.add(8n, Nat.add(Nat.sub(sn, 8n), dd)), R.add_assoc(8n,
        Nat.sub(sn, 8n), dd)), Equal.cong(Nat, Nat, xx => Nat.add(xx, dd), Nat.add(8n, Nat.sub(sn, 8n)), sn,
          R.add_sub(8n,
        sn, h8))))))), n_ult((U32{ss} - 8 : U32), 8, Equal.trans(Bool, Nat.is_lt(U32.to_nat((U32{ss} - 8 : U32)), 8n),
        Nat.is_lt(Nat.sub(sn, 8n), 8n), True{}, Equal.cong(Nat, Bool, xx => Nat.is_lt(xx, 8n), U32.to_nat((U32{ss} - 8 :
        U32)), Nat.sub(sn, 8n), er), R.sub_lt(8n, sn, 8n, h8, h16))))

# the division by 8 invariant for a long division's result x of a word of p + 1 bits
def DivR(+pp: Nat, -aa: Word(1n+pp), xx: Word(1n+pp) & U32) -> Type:
  &_e: {Word.to_nat(1n+pp, aa) == Nat.add(U32.to_nat(dr(1n+pp, xx)), eight(Word.to_nat(1n+pp, dq(1n+pp, xx)))) : Nat} ->
    {U32.is_lt(dr(1n+pp, xx), 8) == True{} : Bool}

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
  ee: {Word.to_nat(pp, hi) == Nat.add(Word.to_nat(32n, rw), eight(Word.to_nat(pp, qq))) : Nat},
  +hl: {U32.is_lt(U32{rw}, 8) == True{} : Bool}
) -> DivR(pp, WCon{a0, hi}, U32.divmod.go.rec(pp, a0, 8, (qq, U32{rw}))):
  +ss = snd.bw(32n, Word.shl.out(32n, a0, rw))
  +rn = Word.to_nat(32n, rw)
  +qn = Word.to_nat(pp, qq)
  +ht = {ngt_top(31n, rw, uw(8), {==}, lt_ngt(Word.cmp(32n, rw, uw(8)), hl)) : {wtop(31n, rw) == False{} :
    Bool}}
  +hf = {Equal.trans(Bool, fst.bw(32n, Word.shl.out(32n, a0, rw)), wtop(31n, rw), False{}, shl_top(31n, a0, rw),
    ht) : {fst.bw(32n, Word.shl.out(32n, a0, rw)) ==
    False{} : Bool}}
  +es = {shl_nat(31n, a0, rw, ht) : {Word.to_nat(32n, ss) == Nat.add(R.bit(a0), Nat.double(rn)) : Nat}}
  +eh = {Equal.trans(Nat, Word.to_nat(1n+pp, WCon{a0, hi}), Nat.add(R.bit(a0), Nat.double(Word.to_nat(pp, hi))),
    Nat.add(Nat.add(R.bit(a0), Nat.double(rn)), Nat.double(eight(qn))), R.to_nat_con(pp, a0, hi), Equal.trans(Nat,
    Nat.add(R.bit(a0), Nat.double(Word.to_nat(pp, hi))), Nat.add(R.bit(a0), Nat.double(Nat.add(rn, eight(qn)))),
    Nat.add(Nat.add(R.bit(a0), Nat.double(rn)), Nat.double(eight(qn))), Equal.cong(Nat, Nat, xx => Nat.add(R.bit(a0),
    Nat.double(xx)), Word.to_nat(pp, hi), Nat.add(rn, eight(qn)), ee), Equal.trans(Nat, Nat.add(R.bit(a0),
    Nat.double(Nat.add(rn, eight(qn)))), Nat.add(R.bit(a0), Nat.add(Nat.double(rn), Nat.double(eight(qn)))),
    Nat.add(Nat.add(R.bit(a0), Nat.double(rn)), Nat.double(eight(qn))), Equal.cong(Nat, Nat, xx => Nat.add(R.bit(a0),
    xx), Nat.double(Nat.add(rn, eight(qn))), Nat.add(Nat.double(rn), Nat.double(eight(qn))), R.double_dist(rn,
    eight(qn))), Equal.sym(Nat, Nat.add(Nat.add(R.bit(a0), Nat.double(rn)), Nat.double(eight(qn))), Nat.add(R.bit(a0),
    Nat.add(Nat.double(rn), Nat.double(eight(qn)))), R.add_assoc(R.bit(a0), Nat.double(rn), Nat.double(eight(qn))))))) :
    {Word.to_nat(1n+pp, WCon{a0, hi}) == Nat.add(Nat.add(R.bit(a0), Nat.double(rn)), Nat.double(eight(qn))) : Nat}}
  +gg = U32.is_ge(U32{ss}, 8)
  divr_tr(pp, WCon{a0, hi}, U32.divmod.go.rec(pp, a0, 8, (qq, U32{rw})), U32.divmod.go.fin(pp, qq, U32{ss}, 8, gg),
    Equal.trans(Word(1n+pp) & U32, U32.divmod.go.shl(pp, qq, 8, Word.shl.out(32n, a0, rw)), U32.divmod.go.shl(pp, qq,
      8, (fst.bw(32n, Word.shl.out(32n, a0, rw)), ss)),
    U32.divmod.go.fin(pp, qq, U32{ss}, 8, gg), Equal.cong(Bool & Word(32n), Word(1n+pp) & U32, tt =>
    U32.divmod.go.shl(pp, qq, 8, tt), Word.shl.out(32n, a0, rw), (fst.bw(32n, Word.shl.out(32n, a0, rw)), ss),
      bw_eta(32n, Word.shl.out(32n, a0, rw))), Equal.cong(Bool, Word(1n+pp) & U32,
    bb => U32.divmod.go.fin(pp, qq, U32{ss}, 8, Bool.or(bb, gg)), fst.bw(32n, Word.shl.out(32n, a0, rw)), False{},
      hf)), divg(gg, pp, a0, hi,
    qq, ss, rn, {==}, es, eh, ult_n(U32{rw}, 8, hl)))

# the type of divstep's parameter inv
def divstep.inv.ty(+_pp: Nat, +_hi: Word(_pp), _qr: Word(_pp) & U32) -> Type:
  &_e: {Word.to_nat(_pp, _hi) == Nat.add(U32.to_nat(dr(_pp, _qr)), eight(Word.to_nat(_pp, dq(_pp,
    _qr)))) : Nat} -> {U32.is_lt(dr(_pp, _qr), 8) == True{} : Bool}

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
def divfin_eta(qr: Word(32n) & U32) -> {U32.div.fin(qr) == U32{dq(32n, qr)} : U32}:
  match qr:
    case (_q, _r):
      {==}

# the division of a word by 8, its invariant named
def udiv8.fin(
  +xw: Word(32n),
  inv: DivInv(32n, xw)
) -> &rr: U32 -> &_e: {U32.to_nat(U32{xw}) == Nat.add(U32.to_nat(rr), eight(U32.to_nat(U32.div(U32{xw},
  8)))) : Nat} -> {U32.is_lt(rr, 8) == True{} : Bool}:
  (e, hl) = inv
  (dr(32n, U32.divmod.go(32n, xw, 8)), Equal.trans(Nat, Word.to_nat(32n, xw), Nat.add(U32.to_nat(dr(32n,
    U32.divmod.go(32n, xw, 8))), eight(Word.to_nat(32n, dq(32n,
    U32.divmod.go(32n, xw, 8))))), Nat.add(U32.to_nat(dr(32n, U32.divmod.go(32n, xw, 8))),
      eight(U32.to_nat(U32.div(U32{xw}, 8)))), e, Equal.cong(U32, Nat, uu =>
    Nat.add(U32.to_nat(dr(32n, U32.divmod.go(32n, xw, 8))), eight(U32.to_nat(uu))), U32{dq(32n, U32.divmod.go(32n, xw,
      8))}, U32.div(U32{xw}, 8), Equal.sym(U32,
    U32.div(U32{xw}, 8), U32{dq(32n, U32.divmod.go(32n, xw, 8))}, divfin_eta(U32.divmod.go(32n, xw, 8))))), hl)

# a U32 is a remainder below 8 and eight times its quotient by 8
def udiv8(
  xx: U32
) -> &rr: U32 -> &_e: {U32.to_nat(xx) == Nat.add(U32.to_nat(rr), eight(U32.to_nat(U32.div(xx,
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
  +ez = {R.word_zero_nat(nn) : {Word.to_nat(nn, Word.zero(nn)) == 0n : Nat}}
  +h1 = {R.lt_rw_l(pr, Nat.add(zn, pr), top, Equal.cong(Nat, Nat, xx => Nat.add(xx, pr), 0n, zn, Equal.sym(Nat, zn, 0n,
    ez)), hh) : {Nat.is_lt(Nat.add(zn, pr), top) == True{} : Bool}}
  Equal.trans(Nat, Word.to_nat(nn, Word.mul.go(nn, nn, aw, bw, Word.zero(nn))), Nat.add(zn, pr), pr, R.mulgo_nat(nn, nn,
    aw, bw, Word.zero(nn), h1), Equal.cong(Nat, Nat, xx => Nat.add(xx, pr), zn, 0n, ez))

# two to a sum is the product of the two powers
def pow_add(+aa: Nat, +bb: Nat) -> {Nat.pow(2n, Nat.add(aa, bb)) == Nat.mul(Nat.pow(2n, aa), Nat.pow(2n, bb)) : Nat}:
  match aa:
    case 0n:
      Equal.sym(Nat, Nat.add(Nat.pow(2n, bb), 0n), Nat.pow(2n, bb), R.add_zero(Nat.pow(2n, bb)))
    case 1n+ +pp:
      +pa = Nat.pow(2n, pp)
      +pb = Nat.pow(2n, bb)
      Equal.trans(Nat, Nat.pow(2n, 1n+Nat.add(pp, bb)), Nat.double(Nat.pow(2n, Nat.add(pp, bb))), Nat.mul(Nat.pow(2n,
        1n+pp), pb), R.pow2_succ(Nat.add(pp, bb)), Equal.trans(Nat, Nat.double(Nat.pow(2n, Nat.add(pp, bb))),
        Nat.double(Nat.mul(pa, pb)), Nat.mul(Nat.pow(2n, 1n+pp), pb), Equal.cong(Nat, Nat, xx => Nat.double(xx),
        Nat.pow(2n, Nat.add(pp, bb)), Nat.mul(pa, pb), pow_add(pp, bb)), Equal.trans(Nat, Nat.double(Nat.mul(pa, pb)),
        Nat.mul(Nat.double(pa), pb), Nat.mul(Nat.pow(2n, 1n+pp), pb), Equal.sym(Nat, Nat.mul(Nat.double(pa), pb),
        Nat.double(Nat.mul(pa, pb)), R.mul_double(pa, pb)), Equal.cong(Nat, Nat, xx => Nat.mul(xx, pb), Nat.double(pa),
        Nat.pow(2n, 1n+pp), Equal.sym(Nat, Nat.pow(2n, 1n+pp), Nat.double(pa), R.pow2_succ(pp))))))

# at most b is at most b + 1
def le_s(+aa: Nat, +bb: Nat, hh: {Nat.is_le(aa, bb) == True{} : Bool}) -> {Nat.is_le(aa, 1n+bb) == True{} : Bool}:
  R.le_trans(aa, bb, 1n+bb, hh, R.le_succ(bb))

# a number is at most its double
def le_dbl(nn: Nat) -> {Nat.is_le(nn, Nat.double(nn)) == True{} : Bool}:
  match nn:
    case 0n:
      {==}
    case 1n+ +pp:
      le_s(pp, Nat.double(pp), le_dbl(pp))

# two to a larger power is at least as large
def pow_le(+aa: Nat, +kk: Nat) -> {Nat.is_le(Nat.pow(2n, aa), Nat.pow(2n, Nat.add(kk, aa))) == True{} : Bool}:
  match kk:
    case 0n:
      R.le_refl(Nat.pow(2n, aa))
    case 1n+ +qq:
      R.le_trans(Nat.pow(2n, aa), Nat.pow(2n, Nat.add(qq, aa)), Nat.pow(2n, 1n+Nat.add(qq, aa)), pow_le(aa, qq),
        R.le_rw_r(Nat.pow(2n, Nat.add(qq, aa)), Nat.double(Nat.pow(2n, Nat.add(qq, aa))), Nat.pow(2n, 1n+Nat.add(qq,
          aa)),
        Equal.sym(Nat, Nat.pow(2n, 1n+Nat.add(qq, aa)), Nat.double(Nat.pow(2n, Nat.add(qq, aa))),
          R.pow2_succ(Nat.add(qq,
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
    bb), Nat.mul(bb, pp), R.mul_comm(pp, bb)), Equal.cong(Nat, Bool, xx => Nat.is_le(Nat.mul(bb, pp), xx), Nat.mul(pp,
    qq), Nat.mul(qq, pp), R.mul_comm(pp, qq))), R.le_mul_mono(bb, qq, pp, hh))

# a number is below it plus a positive number, added on the left
def lt_addq(
  +xx: Nat,
  +qq: Nat,
  hq: {Nat.is_lt(0n, qq) == True{} : Bool}
) -> {Nat.is_lt(xx, Nat.add(qq, xx)) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_lt(xx, Nat.add(qq, xx)), Nat.is_lt(xx, Nat.add(xx, qq)), True{}, Equal.cong(Nat, Bool, nn =>
    Nat.is_lt(xx, nn), Nat.add(qq, xx), Nat.add(xx, qq), R.add_comm(qq, xx)), lt_add_pos(xx, qq, hq))

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
      Empty.absurd({Nat.is_lt(Nat.mul(aa, bb), 0n) == True{} : Bool}, W12.false_true(Equal.trans(Bool, False{},
        Nat.is_lt(aa, 0n), True{}, R.lt_zero_false(aa), ha)))
    case 1n+ +p1:
      R.le_lt_trans(Nat.mul(aa, bb), Nat.mul(p1, qq), Nat.add(qq, Nat.mul(p1, qq)), R.le_trans(Nat.mul(aa, bb),
        Nat.mul(p1,
        bb), Nat.mul(p1, qq), R.le_mul_mono(aa, p1, bb, Equal.trans(Bool, Nat.is_le(aa, p1), Nat.is_lt(aa, 1n+p1),
        True{}, Equal.sym(Bool, Nat.is_lt(aa, 1n+p1), Nat.is_le(aa, p1), lt_s_le(aa, p1)), ha)), mul_le_r(p1, bb, qq,
        R.lt_le(bb, qq, hb))), lt_addq(Nat.mul(p1, qq), qq, R.le_lt_trans(0n, bb, qq, R.le_zero(bb), hb)))

# two to a larger power is at least as large, by the exponents' order
def pow_mono(
  +aa: Nat,
  +bb: Nat,
  hh: {Nat.is_le(aa, bb) == True{} : Bool}
) -> {Nat.is_le(Nat.pow(2n, aa), Nat.pow(2n, bb)) == True{} : Bool}:
  +dd = Nat.sub(bb, aa)
  R.le_rw_r(Nat.pow(2n, aa), Nat.pow(2n, Nat.add(dd, aa)), Nat.pow(2n, bb), Equal.cong(Nat, Nat, xx => Nat.pow(2n, xx),
    Nat.add(dd, aa), bb, Equal.trans(Nat, Nat.add(dd, aa), Nat.add(aa, dd), bb, R.add_comm(dd, aa), R.add_sub(aa, bb,
    hh))), pow_le(aa, dd))

# a product of numbers below 2^i and 2^j is below 2^(i + j)
def mul_pow(
  +aa: Nat,
  +bb: Nat,
  +ii: Nat,
  +jj: Nat,
  ha: {Nat.is_lt(aa, Nat.pow(2n, ii)) == True{} : Bool},
  +hb: {Nat.is_lt(bb, Nat.pow(2n, jj)) == True{} : Bool}
) -> {Nat.is_lt(Nat.mul(aa, bb), Nat.pow(2n, Nat.add(ii, jj))) == True{} : Bool}:
  R.lt_rw_r(Nat.mul(aa, bb), Nat.mul(Nat.pow(2n, ii), Nat.pow(2n, jj)), Nat.pow(2n, Nat.add(ii, jj)), Equal.sym(Nat,
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
def eight_iff(+aa: Nat, +bb: Nat) -> {Nat.is_lt(eight(aa), eight(bb)) == Nat.is_lt(aa, bb) : Bool}:
  Equal.trans(Bool, Nat.is_lt(eight(aa), eight(bb)), Nat.is_lt(Nat.double(Nat.double(aa)), Nat.double(
    Nat.double(bb))), Nat.is_lt(aa, bb), dbl_iff(Nat.double(Nat.double(aa)), Nat.double(Nat.double(bb))), Equal.trans(
    Bool, Nat.is_lt(Nat.double(Nat.double(aa)), Nat.double(Nat.double(bb))), Nat.is_lt(Nat.double(aa), Nat.double(bb)),
    Nat.is_lt(aa, bb), dbl_iff(Nat.double(aa), Nat.double(bb)), dbl_iff(aa, bb)))

# a quotient by 8 of a number at least 8 is above 0
def q_pos(
  qq: Nat,
  +xx: Nat,
  +rr: Nat,
  ee: {xx == Nat.add(rr, eight(qq)) : Nat},
  hr: {Nat.is_lt(rr, 8n) == True{} : Bool},
  hx: {Nat.is_le(8n, xx) == True{} : Bool}
) -> {Nat.is_lt(0n, qq) == True{} : Bool}:
  match qq:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, true_false(Equal.trans(Bool, True{}, Nat.is_le(8n, rr),
        False{}, Equal.sym(Bool, Nat.is_le(8n, rr), True{}, Equal.trans(Bool, Nat.is_le(8n, rr), Nat.is_le(8n, xx),
          True{},
        Equal.cong(Nat, Bool, nn => Nat.is_le(8n, nn), rr, xx, Equal.sym(Nat, xx, rr, Equal.trans(Nat, xx, Nat.add(rr,
        0n), rr, ee, R.add_zero(rr)))), hx)), lt_nle(rr, 8n, hr))))
    case 1n+_p:
      {==}

# a number an n-bit word holds
def Fits(+nn: Nat, +xx: Nat) -> Type:
  &ww: Word(nn) -> {Word.to_nat(nn, ww) == xx : Nat}

# half a number, rounded down
def half(nn: Nat) -> Nat:
  match nn:
    case 0n:
      0n
    case 1n+0n:
      0n
    case 1n+1n+pp:
      1n+half(pp)

# whether a number is odd
def odd(nn: Nat) -> Bool:
  match nn:
    case 0n:
      False{}
    case 1n+0n:
      True{}
    case 1n+1n+pp:
      odd(pp)

# a number is twice its half and its parity
def halfeq(nn: Nat) -> {nn == Nat.add(Nat.double(half(nn)), R.bit(odd(nn))) : Nat}:
  match nn:
    case 0n:
      {==}
    case 1n+0n:
      {==}
    case 1n+1n+ +pp:
      Equal.cong(Nat, Nat, xx => 2n+xx, pp, Nat.add(Nat.double(half(pp)), R.bit(odd(pp))), halfeq(pp))

# the low n bits of a number, as a word
def wof(nn: Nat, +xx: Nat) -> Word(nn):
  match nn:
    case 0n:
      WNil{}
    case 1n+pp:
      WCon{odd(xx), wof(pp, half(xx))}

# a number below 1 is 0
def lt1(xx: Nat, hh: {Nat.is_lt(xx, 1n) == True{} : Bool}) -> {0n == xx : Nat}:
  match xx:
    case 0n:
      {==}
    case 1n+_p:
      Empty.absurd({0n == 1n+_p : Nat}, W12.false_true(Equal.trans(Bool, False{}, Nat.is_lt(_p, 0n), True{},
        R.lt_zero_false(_p), hh)))

# a number below 2^n is held by its low n bits
def lt_fits(
  nn: Nat,
  +xx: Nat,
  hh: {Nat.is_lt(xx, Nat.pow(2n, nn)) == True{} : Bool}
) -> {Word.to_nat(nn, wof(nn, xx)) == xx : Nat}:
  match nn:
    case 0n:
      lt1(xx, hh)
    case 1n+ +pp:
      +hf = half(xx)
      +ob = R.bit(odd(xx))
      +ex = {Equal.trans(Nat, xx, Nat.add(Nat.double(hf), ob), Nat.add(ob, Nat.double(hf)), halfeq(xx), R.add_comm(
        Nat.double(hf), ob)) : {xx == Nat.add(ob, Nat.double(hf)) : Nat}}
      +hl = {R.lt_half(odd(xx), hf, Nat.pow(2n, pp), R.lt_rw_l(xx, Nat.add(ob, Nat.double(hf)), Nat.double(Nat.pow(2n,
        pp)), ex, R.lt_rw_r(xx, Nat.pow(2n, 1n+pp), Nat.double(Nat.pow(2n, pp)), R.pow2_succ(pp), hh))) : {Nat.is_lt(hf,
        Nat.pow(2n, pp)) == True{} : Bool}}
      Equal.trans(Nat, Word.to_nat(1n+pp, WCon{odd(xx), wof(pp, hf)}), Nat.add(ob, Nat.double(Word.to_nat(pp, wof(pp,
        hf)))), xx, R.to_nat_con(pp, odd(xx), wof(pp, hf)), Equal.trans(Nat, Nat.add(ob, Nat.double(Word.to_nat(pp,
          wof(pp,
        hf)))), Nat.add(ob, Nat.double(hf)), xx, Equal.cong(Nat, Nat, yy => Nat.add(ob, Nat.double(yy)), Word.to_nat(pp,
        wof(pp, hf)), hf, lt_fits(pp, hf, hl)), Equal.sym(Nat, xx, Nat.add(ob, Nat.double(hf)), ex)))

# a number below 2^n fits n bits
def mkfits(+nn: Nat, +xx: Nat, hh: {Nat.is_lt(xx, Nat.pow(2n, nn)) == True{} : Bool}) -> Fits(nn, xx):
  (wof(nn, xx), lt_fits(nn, xx, hh))

# a number n bits hold is below 2^n
def fits_lt(+nn: Nat, +xx: Nat, ff: Fits(nn, xx)) -> {Nat.is_lt(xx, Nat.pow(2n, nn)) == True{} : Bool}:
  (+ww, ee) = ff
  R.lt_rw_l(Word.to_nat(nn, ww), xx, Nat.pow(2n, nn), ee, R.word_lt_pow(nn, ww))

# a sum of two numbers of n bits fits n + 1 bits
def fits_add(+ii: Nat, +aa: Nat, +bb: Nat, fa: Fits(ii, aa), fb: Fits(ii, bb)) -> Fits(1n+ii, Nat.add(aa, bb)):
  +pw = Nat.pow(2n, ii)
  +ha = {fits_lt(ii, aa, fa) : {Nat.is_lt(aa, pw) == True{} : Bool}}
  +hb = {fits_lt(ii, bb, fb) : {Nat.is_lt(bb, pw) == True{} : Bool}}
  mkfits(1n+ii, Nat.add(aa, bb), R.lt_rw_r(Nat.add(aa, bb), Nat.double(pw), Nat.pow(2n, 1n+ii), Equal.sym(Nat,
    Nat.pow(2n, 1n+ii), Nat.double(pw), R.pow2_succ(ii)), R.lt_le_trans(Nat.add(aa, bb), Nat.add(aa, pw),
      Nat.double(pw),
    R.lt_add_mono(aa, bb, pw, hb), R.le_rw_r(Nat.add(aa, pw), Nat.add(pw, pw), Nat.double(pw), Equal.sym(Nat,
    Nat.double(pw), Nat.add(pw, pw), R.double_add(pw)), le_addr(aa, pw, pw, R.lt_le(aa, pw, ha))))))

# a product of numbers of i and j bits fits i + j bits
def fits_mul(
  +ii: Nat,
  +jj: Nat,
  +aa: Nat,
  +bb: Nat,
  fa: Fits(ii, aa),
  fb: Fits(jj, bb)
) -> Fits(Nat.add(ii, jj), Nat.mul(aa, bb)):
  mkfits(Nat.add(ii, jj), Nat.mul(aa, bb), mul_pow(aa, bb, ii, jj, fits_lt(ii, aa, fa), fits_lt(jj, bb, fb)))

# a number of i bits fits k + i bits
def fits_up(+ii: Nat, +kk: Nat, +aa: Nat, fa: Fits(ii, aa)) -> Fits(Nat.add(kk, ii), aa):
  mkfits(Nat.add(kk, ii), aa, R.lt_le_trans(aa, Nat.pow(2n, ii), Nat.pow(2n, Nat.add(kk, ii)), fits_lt(ii, aa, fa),
    pow_le(ii, kk)))

# U32 add, when the sum fits 32 bits, is Nat add
def uadd_fits(
  +au: U32,
  +bu: U32,
  ff: Fits(32n, Nat.add(U32.to_nat(au), U32.to_nat(bu)))
) -> {U32.to_nat((au + bu : U32)) == Nat.add(U32.to_nat(au), U32.to_nat(bu)) : Nat}:
  (+ww, ee) = ff
  +sm = Nat.add(U32.to_nat(au), U32.to_nat(bu))
  R.u32_add_below(au, bu, U32{ww}, R.le_rw_r(sm, sm, Word.to_nat(32n, ww), Equal.sym(Nat, Word.to_nat(32n, ww), sm, ee),
    R.le_refl(sm)))

# U32 mul, when the product fits 32 bits, is Nat mul
def umul_fits(
  +au: U32,
  +bu: U32,
  ff: Fits(32n, Nat.mul(U32.to_nat(au), U32.to_nat(bu)))
) -> {U32.to_nat((au * bu : U32)) == Nat.mul(U32.to_nat(au), U32.to_nat(bu)) : Nat}:
  (+ww, ee) = ff
  +pr = Nat.mul(U32.to_nat(au), U32.to_nat(bu))
  R.u32_mul_below(au, bu, U32{ww}, R.le_rw_r(pr, pr, Word.to_nat(32n, ww), Equal.sym(Nat, Word.to_nat(32n, ww), pr, ee),
    R.le_refl(pr)))

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
          R.word_zero_nat(mm)
    case 1n+ +pp:
      match aa:
        case WCon{+a0, +at}:
          Equal.trans(Nat, Word.to_nat(1n+Nat.add(pp, mm), WCon{a0, wapp(pp, mm, at, Word.zero(mm))}),
            Nat.add(R.bit(a0),
            Nat.double(Word.to_nat(Nat.add(pp, mm), wapp(pp, mm, at, Word.zero(mm))))), Word.to_nat(1n+pp, WCon{a0,
              at}),
            R.to_nat_con(Nat.add(pp, mm), a0, wapp(pp, mm, at, Word.zero(mm))), Equal.trans(Nat, Nat.add(R.bit(a0),
            Nat.double(Word.to_nat(Nat.add(pp, mm), wapp(pp, mm, at, Word.zero(mm))))), Nat.add(R.bit(a0), Nat.double(
            Word.to_nat(pp, at))), Word.to_nat(1n+pp, WCon{a0, at}), Equal.cong(Nat, Nat, xx => Nat.add(R.bit(a0),
            Nat.double(xx)), Word.to_nat(Nat.add(pp, mm), wapp(pp, mm, at, Word.zero(mm))), Word.to_nat(pp, at),
              zapp_nat(pp,
            mm, at)), Equal.sym(Nat, Word.to_nat(1n+pp, WCon{a0, at}), Nat.add(R.bit(a0), Nat.double(Word.to_nat(pp,
              at))),
            R.to_nat_con(pp, a0, at))))

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
      Empty.absurd({True{} == False{} : Bool}, true_false(Equal.trans(Bool, True{}, Cmp.is_gt(Word.cmp.fin(True{},
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
          +et = {nz0(pp, xt, fin_ngt(a0, False{}, Word.cmp(pp, xt, Word.zero(pp)), hh)) : {xt == Word.zero(pp) :
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
          hi_zero(pp, mm, xt, xh, ct, fin_ngt(x0, c0, Word.cmp(Nat.add(pp, mm), wapp(pp, mm, xt, xh), wapp(pp, mm, ct,
            Word.zero(mm))), hh))

# at most is not above
def le_ngt(tt: Cmp, hh: {Cmp.is_le(tt) == True{} : Bool}) -> {Cmp.is_gt(tt) == False{} : Bool}:
  match tt:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({Cmp.is_gt(GT{}) == False{} : Bool}, W12.false_true(hh))

# a side at most 65535 fits 16 bits
def fits16(+ww: U32, hh: {U32.is_le(ww, 65535) == True{} : Bool}) -> Fits(16n, U32.to_nat(ww)):
  match ww:
    case U32{+xw}:
      +lo = wlo(16n, 16n, xw)
      +hi = whi(16n, 16n, xw)
      +cl = wlo(16n, 16n, uw(65535))
      +es = {split_eq(16n, 16n, xw) : {wapp(16n, 16n, lo, hi) == xw : Word(32n)}}
      +hg = {Equal.trans(Bool, Cmp.is_gt(Word.cmp(32n, wapp(16n, 16n, lo, hi), wapp(16n, 16n, cl, Word.zero(16n)))),
        Cmp.is_gt(Word.cmp(32n, xw, uw(65535))), False{}, Equal.cong(Word(32n), Bool, ww2 => Cmp.is_gt(Word.cmp(32n,
          ww2,
        uw(65535))), wapp(16n, 16n, lo, hi), xw, es), le_ngt(Word.cmp(32n, xw, uw(65535)), hh)) :
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
def pow3(+kk: Nat) -> {Nat.pow(2n, 3n+kk) == eight(Nat.pow(2n, kk)) : Nat}:
  +p0 = Nat.pow(2n, kk)
  Equal.trans(Nat, Nat.pow(2n, 3n+kk), Nat.double(Nat.pow(2n, 2n+kk)), eight(p0), R.pow2_succ(2n+kk),
    Equal.cong(Nat, Nat, xx => Nat.double(xx), Nat.pow(2n, 2n+kk), Nat.double(Nat.double(p0)), Equal.trans(Nat,
      Nat.pow(2n,
    2n+kk), Nat.double(Nat.pow(2n, 1n+kk)), Nat.double(Nat.double(p0)), R.pow2_succ(1n+kk), Equal.cong(Nat, Nat, xx =>
    Nat.double(xx), Nat.pow(2n, 1n+kk), Nat.double(p0), R.pow2_succ(kk)))))

# a quotient by 8 of a number of k + 3 bits fits k bits
def qfits(
  +kk: Nat,
  +xx: Nat,
  +rr: Nat,
  +qq: Nat,
  ee: {xx == Nat.add(rr, eight(qq)) : Nat},
  ff: Fits(3n+kk, xx)
) -> Fits(kk, qq):
  +pk = Nat.pow(2n, kk)
  +hx = {fits_lt(3n+kk, xx, ff) : {Nat.is_lt(xx, Nat.pow(2n, 3n+kk)) == True{} : Bool}}
  +h8 = {R.le_lt_trans(eight(qq), xx, eight(pk), R.le_rw_r(eight(qq), Nat.add(rr, eight(qq)), xx,
    Equal.sym(Nat, xx, Nat.add(rr, eight(qq)), ee), le_add_left(rr, eight(qq))), R.lt_rw_r(xx, Nat.pow(2n,
    3n+kk), eight(pk), pow3(kk), hx)) : {Nat.is_lt(eight(qq), eight(pk)) == True{} : Bool}}
  mkfits(kk, qq, Equal.trans(Bool, Nat.is_lt(qq, pk), Nat.is_lt(eight(qq), eight(pk)), True{}, Equal.sym(
    Bool, Nat.is_lt(eight(qq), eight(pk)), Nat.is_lt(qq, pk), eight_iff(qq, pk)), h8))

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
  &rr: U32 -> &_e: {U32.to_nat((_ww + 7 : U32)) == Nat.add(U32.to_nat(rr), eight(U32.to_nat(U32.div((_ww + 7 : U32),
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
      U32.to_nat(rr), ed, ult_n(rr, 8, hr),
    R.le_rw_r(8n, Nat.add(U32.to_nat(ww), 7n), xx, Equal.sym(Nat, xx, Nat.add(U32.to_nat(ww), 7n), e7), h8)))

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
  +hw = {nle_lt(wn, 0n, Equal.trans(Bool, Nat.is_le(wn, 0n), Nat.is_eq(wn, 0n), False{}, ngt_le0(wn), Equal.trans(Bool,
    Nat.is_eq(wn, 0n), U32.is_eq(ww, 0), False{}, Equal.sym(Bool, U32.is_eq(ww, 0), Nat.is_eq(wn, 0n), R.u32_eq(ww, 0)),
    h0))) : {Nat.is_lt(0n, wn) == True{} : Bool}}
  mw_fin(ww, fits16(ww, hl), e7, le_addr(1n, wn, 7n, Equal.trans(Bool, Nat.is_le(1n, wn), Nat.is_lt(0n, wn), True{},
    Equal.sym(Bool,
    Nat.is_lt(0n, wn), Nat.is_le(1n, wn), R.lt_le_succ(0n, wn)), hw)), udiv8((ww + 7 : U32)))

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
  +pij = {pow_mono(ij, nn, R.le_trans(ij, Nat.add(ij, kk), nn, R.le_add_more(ij, ij, kk, R.le_refl(ij)), hs)) :
    {Nat.is_le(Nat.pow(2n, ij), Nat.pow(2n, nn)) == True{} : Bool}}
  +e1 = {word_mul_pow(nn, aw, bw, R.lt_le_trans(Nat.mul(an, bn), Nat.pow(2n, ij), Nat.pow(2n, nn), hab, pij)) :
    {Word.to_nat(nn, Word.mul(nn, aw, bw)) == Nat.mul(an, bn) : Nat}}
  +xw = Word.mul(nn, aw, bw)
  (e1, Equal.trans(Nat, Word.to_nat(nn, Word.mul(nn, xw, cw)), Nat.mul(Word.to_nat(nn, xw), cn), Nat.mul(Nat.mul(an,
    bn),
    cn), word_mul_pow(nn, xw, cw, Equal.trans(Bool, Nat.is_lt(Nat.mul(Word.to_nat(nn, xw), cn), Nat.pow(2n, nn)),
    Nat.is_lt(Nat.mul(Nat.mul(an, bn), cn), Nat.pow(2n, nn)), True{}, Equal.cong(Nat, Bool, xx => Nat.is_lt(Nat.mul(xx,
    cn), Nat.pow(2n, nn)), Word.to_nat(nn, xw), Nat.mul(an, bn), e1), R.lt_le_trans(Nat.mul(Nat.mul(an, bn), cn),
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
def tri_mul(nn: Nat) -> {tri(nn) == Nat.mul(nn, 3n) : Nat}:
  match nn:
    case 0n:
      {==}
    case 1n+ +pp:
      Equal.cong(Nat, Nat, xx => 3n+xx, tri(pp), Nat.mul(pp, 3n), tri_mul(pp))

# U32s of the same number are the same
def unat_eq(+aa: U32, +bb: U32, ee: {U32.to_nat(aa) == U32.to_nat(bb) : Nat}) -> {aa == bb : U32}:
  U32L.ueq(aa, bb, Equal.trans(Bool, U32.is_eq(aa, bb), Nat.is_eq(U32.to_nat(aa), U32.to_nat(bb)), True{}, R.u32_eq(aa,
    bb), Equal.trans(Bool, Nat.is_eq(U32.to_nat(aa), U32.to_nat(bb)), Nat.is_eq(U32.to_nat(bb), U32.to_nat(bb)), True{},
    Equal.cong(Nat, Bool, nn => Nat.is_eq(nn, U32.to_nat(bb)), U32.to_nat(aa), U32.to_nat(bb), ee), R.nat_eq_refl(
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
  +h1 = {R.le_rw_r(1n, Nat.add(wn, 8n), U32.to_nat((ww + 8 : U32)), Equal.sym(Nat, U32.to_nat((ww + 8 : U32)),
    Nat.add(wn,
    8n), e8), R.le_trans(1n, 8n, Nat.add(wn, 8n), {==}, le_add_left(wn, 8n))) : {Nat.is_le(1n, U32.to_nat((ww + 8 :
    U32))) == True{} : Bool}}
  unat_eq(((ww + 8 : U32) - 1 : U32), (ww + 7 : U32), Equal.trans(Nat, U32.to_nat(((ww + 8 : U32) - 1 : U32)), Nat.sub(
    U32.to_nat((ww + 8 : U32)), 1n), U32.to_nat((ww + 7 : U32)), R.u32_sub_nat((ww + 8 : U32), 1, h1), Equal.trans(Nat,
    Nat.sub(U32.to_nat((ww + 8 : U32)), 1n), Nat.sub(1n+Nat.add(wn, 7n), 1n), U32.to_nat((ww + 7 : U32)),
      Equal.cong(Nat,
    Nat, nn => Nat.sub(nn, 1n), U32.to_nat((ww + 8 : U32)), 1n+Nat.add(wn, 7n), Equal.trans(Nat, U32.to_nat((ww + 8 :
    U32)), Nat.add(wn, 8n), 1n+Nat.add(wn, 7n), e8, R.add_succ(wn, 7n))), Equal.trans(Nat, Nat.sub(Nat.add(wn, 7n), 0n),
    Nat.add(wn, 7n), U32.to_nat((ww + 7 : U32)), R.sub_zero(Nat.add(wn, 7n)), Equal.sym(Nat, U32.to_nat((ww + 7 : U32)),
    Nat.add(wn, 7n), e7)))))

# the encoder's MCU count and the decoder's block count, for sides of 1 to 65535: three blocks per MCU, at least one
# MCU
def CountOut(+ww: U32, +hh: U32) -> Type:
  &_n: {U32.to_nat(Jpeg.decode.nblocks(ww, hh, [1, 1, 1], [1, 1, 1], 1, 1)) == tri(U32.to_nat(mcun(ww, hh))) : Nat} ->
    &_p: {Nat.is_lt(0n, U32.to_nat(mcun(ww, hh))) == True{} : Bool} -> {1n+U32.to_nat((mcun(ww, hh) - 1 : U32)) ==
    U32.to_nat(mcun(ww, hh)) : Nat}

# a product of two numbers above 0 is above 0
def pos_mul(
  aa: Nat,
  +bb: Nat,
  ha: {Nat.is_lt(0n, aa) == True{} : Bool},
  hb: {Nat.is_lt(0n, bb) == True{} : Bool}
) -> {Nat.is_lt(0n, Nat.mul(aa, bb)) == True{} : Bool}:
  match aa:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, W12.false_true(ha))
    case 1n+ +pp:
      R.lt_le_trans(0n, bb, Nat.add(bb, Nat.mul(pp, bb)), hb, R.le_add_more(bb, bb, Nat.mul(pp, bb), R.le_refl(bb)))

# the type of count_fin's parameter pr
def count_fin.pr.ty(+_ww: U32, +_hh: U32) -> Type:
  &_p: {U32.to_nat(mcun(_ww, _hh)) == Nat.mul(U32.to_nat(U32.div((_ww + 7 : U32), 8)),
    U32.to_nat(U32.div((_hh + 7 : U32), 8))) : Nat} -> {U32.to_nat((mcun(_ww,
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
  +mm = mcun(ww, hh)
  +mn = U32.to_nat(mm)
  +pn = Nat.mul(U32.to_nat(mw), U32.to_nat(mh))
  +em = {em0 : {mn == pn : Nat}}
  +e3 = {e30 : {U32.to_nat((mm * 3 : U32)) == Nat.mul(pn, 3n) : Nat}}
  +hp = {R.lt_rw_r(0n, pn, mn, Equal.sym(Nat, mn, pn, em), pos_mul(U32.to_nat(mw), U32.to_nat(mh), pw, ph)) :
    {Nat.is_lt(0n, mn) == True{} : Bool}}
  +h1 = {Equal.trans(Bool, Nat.is_le(1n, mn), Nat.is_lt(0n, mn), True{}, Equal.sym(Bool, Nat.is_lt(0n, mn),
    Nat.is_le(1n,
    mn), R.lt_le_succ(0n, mn)), hp) : {Nat.is_le(1n, mn) == True{} : Bool}}
  +nb = {Equal.cong(U32, U32, uu => (uu * 3 : U32), (U32.div(((ww + 8 : U32) - 1 : U32),
    8) * U32.div(((hh + 8 : U32) - 1 :
    U32), 8) : U32), mm, Equal.trans(U32, (U32.div(((ww + 8 : U32) - 1 : U32),
      8) * U32.div(((hh + 8 : U32) - 1 : U32), 8)
    : U32), (mw * U32.div(((hh + 8 : U32) - 1 : U32), 8) : U32), mm, Equal.cong(U32, U32, uu => (U32.div(uu, 8) *
    U32.div(((hh + 8 : U32) - 1 : U32), 8) : U32), ((ww + 8 : U32) - 1 : U32), (ww + 7 : U32), cw), Equal.cong(U32, U32,
    uu => (mw * U32.div(uu, 8) : U32), ((hh + 8 : U32) - 1 : U32), (hh + 7 : U32), ch))) :
    {Jpeg.decode.nblocks(ww, hh, [1, 1, 1], [1, 1, 1], 1, 1) == (mm * 3 : U32) : U32}}
  (Equal.trans(Nat, U32.to_nat(Jpeg.decode.nblocks(ww, hh, [1, 1, 1], [1, 1, 1], 1, 1)), U32.to_nat((mm * 3 : U32)),
    tri(mn), Equal.cong(U32, Nat, uu => U32.to_nat(uu), Jpeg.decode.nblocks(ww, hh, [1, 1, 1], [1, 1, 1], 1, 1), (mm *
    3 : U32), nb), Equal.trans(Nat, U32.to_nat((mm * 3 : U32)), Nat.mul(pn, 3n), tri(mn), e3, Equal.trans(Nat,
    Nat.mul(pn, 3n), Nat.mul(mn, 3n), tri(mn), Equal.cong(Nat, Nat, xx => Nat.mul(xx, 3n), pn, mn, Equal.sym(Nat, mn,
    pn, em)), Equal.sym(Nat, tri(mn), Nat.mul(mn, 3n), tri_mul(mn))))), hp, Equal.trans(Nat, 1n+U32.to_nat((mm - 1 :
    U32)), Nat.add(1n, Nat.sub(mn, 1n)), mn, Equal.cong(Nat, Nat, xx => 1n+xx, U32.to_nat((mm - 1 : U32)), Nat.sub(mn,
      1n),
    R.u32_sub_nat(mm, 1, h1)), R.add_sub(1n, mn, h1)))

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
      Empty.absurd({Nat.is_eq(0n, 0n) == False{} : Bool}, W12.false_true(hh))
    case 1n+_p:
      {==}

# above 0 as a U32 is not 0
def gt0_ne(+ww: U32, hh: {U32.is_gt(ww, 0) == True{} : Bool}) -> {U32.is_eq(ww, 0) == False{} : Bool}:
  +wn = U32.to_nat(ww)
  Equal.trans(Bool, U32.is_eq(ww, 0), Nat.is_eq(wn, 0n), False{}, R.u32_eq(ww, 0), ne0(wn, gt0(wn, ugt0(ww, True{},
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
      Empty.absurd({Maybe.is_some(&2, Img.Raster, Img.decode_jpeg.out(None{})) == True{} : Bool}, W12.false_true(hh))

# three per MCU, at least one MCU, is not no blocks
def tri_pos(nn: Nat, hp: {Nat.is_lt(0n, nn) == True{} : Bool}, ee: {0n == tri(nn) : Nat}) -> Empty:
  match nn:
    case 0n:
      W12.false_true(hp)
    case 1n+pp:
      zero_ne(1n+(1n+tri(pp)), ee)

# the type of some_ts's parameter ea
def some_ts.ea.ty(+_ts: List<&2, Laws.JBlkTok>, +_ww: U32, +_hh: U32, +_px: List<&2, U32>) -> Type:
  {Jenc.encode.arm(_ww, _hh, _px) == Jenc.encode.pad(Laws.jpg.feed(W12.tbits(_ts), Jenc.encode.put0())) : List<&2, U32>}

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
  el: {List.length(&2, Laws.JBlkTok, ts) == tri(mn) : Nat},
  ew: {Laws.jpg.allwf(ts) == True{} : Bool},
  en: {U32.to_nat(Jpeg.decode.nblocks(ww, hh, [1, 1, 1], [1, 1, 1], 1, 1)) == tri(mn) : Nat},
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
        Jenc.encode.pad(Laws.jpg.feed(W12.tbits(tt <> rest), p0)),
        Jenc.encode.pad(Laws.jpg.feed(Laws.jpg.tbits(tt <> rest), p0)), ea, Equal.cong(List<&2, Bool>, List<&2, U32>,
          bs =>
        Jenc.encode.pad(Laws.jpg.feed(bs, p0)), W12.tbits(tt <> rest), Laws.jpg.tbits(tt <> rest), Equal.sym(List<&2,
        Bool>, Laws.jpg.tbits(tt <> rest), W12.tbits(tt <> rest), W12.tbits.eq(tt <> rest))))
      es = Equal.sym(List<&2, U32>, Jenc.encode.arm(ww, hh, px),
        Jenc.encode.pad(Laws.jpg.feed(Laws.jpg.tbits(tt <> rest),
        p0)), eb)
      %es : {Laws.jpg.psome(Jpeg.decode.run(fr, sc, tb, _, 0)) == True{} : Bool}
      W12.scan_some(tt, rest, ww, hh, hw0, hh0, ew, Equal.trans(Nat, U32.to_nat(Jpeg.decode.nblocks(ww, hh, [1, 1, 1],
        [1, 1,
        1], 1, 1)), tri(mn), 1n+List.length(&2, Laws.JBlkTok, rest), en, Equal.sym(Nat, 1n+List.length(&2, Laws.JBlkTok,
        rest), tri(mn), el)))

# the entropy-coded bytes' blocks named
def some_path(
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>,
  +hw0: {U32.is_eq(ww, 0) == False{} : Bool},
  +hh0: {U32.is_eq(hh, 0) == False{} : Bool},
  en: {U32.to_nat(Jpeg.decode.nblocks(ww, hh, [1, 1, 1], [1, 1, 1], 1, 1)) == tri(U32.to_nat(mcun(ww, hh))) : Nat},
  hp: {Nat.is_lt(0n, U32.to_nat(mcun(ww, hh))) == True{} : Bool},
  po: PathOut(Jenc.encode.arm(ww, hh, px), U32.to_nat(mcun(ww, hh)))
) -> {Laws.jpg.psome(Jpeg.decode.run(Laws.jpg.enc.frame(ww, hh), Laws.jpg.enc.scan(), Laws.jpg.enc.tabs(),
  Jenc.encode.arm(ww, hh, px), 0)) == True{} : Bool}:
  (ts, ea, el, ew) = po
  some_ts(ts, ww, hh, px, hw0, hh0, U32.to_nat(mcun(ww, hh)), ea, el, ew, en, hp)

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
  +h_good: {Png.enc.good(ww, hh, px) == True{} : Bool},
  +h_w: {U32.is_le(ww, 65535) == True{} : Bool},
  +h_h: {U32.is_le(hh, 65535) == True{} : Bool},
  ers: some_ok.ers.ty(ww, hh, px)
) -> {Maybe.is_some(&2, Img.Raster, Laws.jpg.back(Img.encode_jpeg(Img.Raster{ww, hh, px}))) == True{} : Bool}:
  +gw = U32.is_gt(ww, 0)
  +gh = U32.is_gt(hh, 0)
  +rw = Png.enc.rows(px, U32.is_zero(hh), U32.is_lt(Png.enc.len(px, 0), ww), ww, hh, Png.enc.len(px, 0))
  +hg = {W12.and_l(Bool.and(gw, gh), rw, h_good) : {Bool.and(gw, gh) == True{} : Bool}}
  +hw0 = {gt0_ne(ww, W12.and_l(gw, gh, hg)) : {U32.is_eq(ww, 0) == False{} : Bool}}
  +hh0 = {gt0_ne(hh, W12.and_r(gw, gh, hg)) : {U32.is_eq(hh, 0) == False{} : Bool}}
  +cp = Img.colours(px)
  es = Equal.sym(Maybe<&2, Img.Raster>, Laws.jpg.back(Img.encode_jpeg(Img.Raster{ww, hh, px})), Img.decode_jpeg.out(
    Jpeg.decode.run(Laws.jpg.enc.frame(ww, hh), Laws.jpg.enc.scan(), Laws.jpg.enc.tabs(), Jenc.encode.arm(ww, hh, cp),
      0)),
    ers)
  %es : {Maybe.is_some(&2, Img.Raster, _) == True{} : Bool}
  psome_some(Jpeg.decode.run(Laws.jpg.enc.frame(ww, hh), Laws.jpg.enc.scan(), Laws.jpg.enc.tabs(), Jenc.encode.arm(ww,
    hh, cp), 0), some_cnt(ww, hh, cp, hw0, hh0, count_ok(ww, hh, hw0, hh0, h_w, h_h)))
