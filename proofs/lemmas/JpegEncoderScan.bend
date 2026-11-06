# the JPEG encoder's MCU loop and the model bit writer it feeds
import Base
import ../../src/jpeg.bend as Jpeg
import ../../src/jpeg_enc.bend as Jenc
import ../../laws/JpegRoundTripKeepsSize.bend as L1
import ./BasicFacts.bend as M1
import ./JpegHuffmanCoding.bend as M2
import ./SubtractionAndHuffmanWalk.bend as M3

# or with zeros on the right is the word
def or_zero_r(nn: Nat, ww: Word(nn)) -> {Word.or(nn, ww, Word.zero(nn)) == ww : Word(nn)}:
  match nn:
    case 0n:
      match ww:
        case WNil{}:
          {==}
    case 1n+pp:
      match ww:
        case WCon{bb, tt}:
          match bb:
            case True{}:
              Equal.cong(Word(pp), Word.Con<pp>, xx => WCon{True{}, xx}, Word.or(pp, tt, Word.zero(pp)), tt,
                or_zero_r(pp, tt))
            case False{}:
              Equal.cong(Word(pp), Word.Con<pp>, xx => WCon{False{}, xx}, Word.or(pp, tt, Word.zero(pp)), tt,
                or_zero_r(pp, tt))

# the writer's step: shift up, or in the bit
def or_shl_u(xx: U32, bb: Bool) -> {U32.or(U32.shl(xx), L1.jpg.ubit(bb)) == M3.vstep(xx, bb) : U32}:
  match xx:
    case U32{ww}:
      match ww:
        case WCon{w0, wt}:
          Equal.cong(Word(31n), U32, zz => U32{WCon{bb, zz}}, Word.or(31n, Word.shl.put(31n, w0, wt), Word.zero(31n)),
            Word.shl.put(31n, w0, wt), or_zero_r(31n, Word.shl.put(31n, w0, wt)))

# bits folded into a value, the first bit highest: each shifts the value up and sits in the low bit
def vfold(bs: List<&2, Bool>, acc: U32) -> U32:
  match bs:
    case Nil{}:
      acc
    case bb <> rest:
      vfold(rest, M3.vstep(acc, bb))

# the encoder's bit writer holding out (bytes, newest first) and the pending bits pp, fewer than 8
def wst(out: List<&2, U32>, +pp: List<&2, Bool>) -> Jenc.Put:
  Jenc.Put{out, vfold(pp, 0), U32.from_nat(List.length(&2, Bool, pp))}

# seven pending bits: the next one finishes a byte
def is7(pp: List<&2, Bool>) -> Bool:
  Nat.is_eq(List.length(&2, Bool, pp), 7n)

# the writer after one more bit: a finished byte, or one more pending bit
def wone(full: Bool, out: List<&2, U32>, pp: List<&2, Bool>, bb: Bool) -> Jenc.Put:
  match full:
    case True{}:
      Jenc.Put{vfold(List.append(&2, Bool, pp, [bb]), 0) <> out, 0, 0}
    case False{}:
      wst(out, List.append(&2, Bool, pp, [bb]))

# fewer than 8 pending bits
def short(pp: List<&2, Bool>) -> Bool:
  Nat.is_lt(List.length(&2, Bool, pp), 8n)

# eight or more pending bits are not short
def long8(xs: List<&2, Bool>, hh: {Nat.is_lt(List.length(&2, Bool, xs), 0n) == True{} : Bool}) -> Empty:
  M1.huf.false_true(Equal.trans(Bool, False{}, Nat.is_lt(List.length(&2, Bool, xs), 0n), True{},
    M3.lt0(List.length(&2, Bool, xs)), hh))

# the writer's bit step on a model state, by the pending bits
def wbit.p(
  out: List<&2, U32>,
  pp: List<&2, Bool>,
  bb: Bool,
  hh: {short(pp) == True{} : Bool}
) -> {Jenc.encode.bit.n(U32.is_eq(U32.from_nat(List.length(&2, Bool, pp)), 7), out, M3.vstep(vfold(pp, 0), bb),
  U32.from_nat(List.length(&2, Bool, pp))) == wone(is7(pp), out, pp, bb) : Jenc.Put}:
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
                                  Empty.absurd({Jenc.encode.bit.n(U32.is_eq(U32.from_nat(List.length(&2, Bool,
                                    p0 <> p1 <> p2 <> p3 <> p4 <> p5 <> p6 <> p7 <> t7)), 7), out,
                                    M3.vstep(vfold(p0 <> p1 <> p2 <> p3 <> p4 <> p5 <> p6 <> p7 <> t7, 0), bb),
                                    U32.from_nat(List.length(&2, Bool, p0 <> p1 <> p2 <> p3 <> p4 <> p5 <> p6 <> p7 <>
                                    t7))) == wone(is7(p0 <> p1 <> p2 <> p3 <> p4 <> p5 <> p6 <> p7 <> t7), out,
                                    p0 <> p1 <> p2 <> p3 <> p4 <> p5 <> p6 <> p7 <> t7, bb) : Jenc.Put},
                                    long8(t7, hh))

# the writer's bit step: the model's next state
def wbit(
  out: List<&2, U32>,
  +pp: List<&2, Bool>,
  +bb: Bool,
  hh: {short(pp) == True{} : Bool}
) -> {Jenc.encode.bit(wst(out, pp), L1.jpg.ubit(bb)) == wone(is7(pp), out, pp, bb) : Jenc.Put}:
  +nn = U32.from_nat(List.length(&2, Bool, pp))
  +vv = vfold(pp, 0)
  Equal.trans(Jenc.Put, Jenc.encode.bit.n(U32.is_eq(nn, 7), out, U32.or(U32.shl(vv), U32.and(L1.jpg.ubit(bb), 1)),
    nn),
    Jenc.encode.bit.n(U32.is_eq(nn, 7), out, U32.or(U32.shl(vv), L1.jpg.ubit(bb)), nn), wone(is7(pp), out, pp, bb),
    Equal.cong(U32, Jenc.Put, xx => Jenc.encode.bit.n(U32.is_eq(nn, 7), out, U32.or(U32.shl(vv), xx), nn),
    U32.and(L1.jpg.ubit(bb), 1), L1.jpg.ubit(bb), M2.and_one(L1.jpg.ubit(bb))),
    Equal.trans(Jenc.Put, Jenc.encode.bit.n(U32.is_eq(nn, 7), out, U32.or(U32.shl(vv), L1.jpg.ubit(bb)), nn),
    Jenc.encode.bit.n(U32.is_eq(nn, 7), out, M3.vstep(vv, bb), nn), wone(is7(pp), out, pp, bb),
    Equal.cong(U32, Jenc.Put, xx => Jenc.encode.bit.n(U32.is_eq(nn, 7), out, xx, nn), U32.or(U32.shl(vv),
      L1.jpg.ubit(bb)),
    M3.vstep(vv, bb), or_shl_u(vv, bb)), wbit.p(out, pp, bb, hh)))

# the model writer's state: the finished bytes as their bits (newest first) and the pending bits
type WS is Data:
  WS{out: List<&2, List<&2, Bool>>, pp: List<&2, Bool>}

# bytes from their bits
def obytes(os: List<&2, List<&2, Bool>>) -> List<&2, U32>:
  match os:
    case Nil{}:
      []
    case oo <> rest:
      vfold(oo, 0) <> obytes(rest)

# the encoder's writer the model state stands for
def wput(ws: WS) -> Jenc.Put:
  match ws:
    case WS{out, pp}:
      wst(obytes(out), pp)

# one model step, by whether the pending bits finish a byte
def wstep.b(full: Bool, out: List<&2, List<&2, Bool>>, pp: List<&2, Bool>, bb: Bool) -> WS:
  match full:
    case True{}:
      WS{List.append(&2, Bool, pp, [bb]) <> out, []}
    case False{}:
      WS{out, List.append(&2, Bool, pp, [bb])}

# one model step
def wstep(ws: WS, bb: Bool) -> WS:
  match ws:
    case WS{out, +pp}:
      wstep.b(is7(pp), out, pp, bb)

# the model writer fed bits
def wm(bs: List<&2, Bool>, ws: WS) -> WS:
  match bs:
    case Nil{}:
      ws
    case bb <> rest:
      wm(rest, wstep(ws, bb))

# the pending bits of a model state are fewer than 8
def wshort(ws: WS) -> Bool:
  match ws:
    case WS{_out, pp}:
      short(pp)

# the writer's step and the model's agree, by whether the byte is finished
def wone.eq(
  full: Bool,
  +out: List<&2, List<&2, Bool>>,
  +pp: List<&2, Bool>,
  bb: Bool
) -> {wone(full, obytes(out), pp, bb) == wput(wstep.b(full, out, pp, bb)) : Jenc.Put}:
  match full:
    case True{}:
      {==}
    case False{}:
      {==}

# one bit on the encoder's writer is one model step
def wbit.ws(
  ws: WS,
  +bb: Bool,
  hh: {wshort(ws) == True{} : Bool}
) -> {Jenc.encode.bit(wput(ws), L1.jpg.ubit(bb)) == wput(wstep(ws, bb)) : Jenc.Put}:
  match ws:
    case WS{+out, +pp}:
      Equal.trans(Jenc.Put, Jenc.encode.bit(wst(obytes(out), pp), L1.jpg.ubit(bb)), wone(is7(pp), obytes(out), pp,
        bb),
        wput(wstep.b(is7(pp), out, pp, bb)), wbit(obytes(out), pp, bb, hh), wone.eq(is7(pp), out, pp, bb))

# after a step the pending bits are still fewer than 8, by the pending bits
def wstep.short.p(
  out: List<&2, List<&2, Bool>>,
  pp: List<&2, Bool>,
  bb: Bool,
  hh: {short(pp) == True{} : Bool}
) -> {wshort(wstep.b(is7(pp), out, pp, bb)) == True{} : Bool}:
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
                                  Empty.absurd({wshort(wstep.b(is7(p0 <> p1 <> p2 <> p3 <> p4 <> p5 <> p6 <> p7 <> t7),
                                    out, p0 <> p1 <> p2 <> p3 <> p4 <> p5 <> p6 <> p7 <> t7, bb)) == True{} : Bool},
                                    long8(t7, hh))

# after a step the pending bits are still fewer than 8
def wstep.short(ws: WS, bb: Bool, hh: {wshort(ws) == True{} : Bool}) -> {wshort(wstep(ws, bb)) == True{} : Bool}:
  match ws:
    case WS{out, pp}:
      wstep.short.p(out, pp, bb, hh)

# feeding bits to the encoder's writer is the model writer
def wfeed(
  bs: List<&2, Bool>,
  +ws: WS,
  +hh: {wshort(ws) == True{} : Bool}
) -> {L1.jpg.feed(bs, wput(ws)) == wput(wm(bs, ws)) : Jenc.Put}:
  match bs:
    case Nil{}:
      {==}
    case +bb <> rest:
      Equal.trans(Jenc.Put, L1.jpg.feed(rest, Jenc.encode.bit(wput(ws), L1.jpg.ubit(bb))), L1.jpg.feed(rest,
        wput(wstep(ws, bb))),
        wput(wm(rest, wstep(ws, bb))), Equal.cong(Jenc.Put, Jenc.Put, qq => L1.jpg.feed(rest, qq),
        Jenc.encode.bit(wput(ws), L1.jpg.ubit(bb)), wput(wstep(ws, bb)), wbit.ws(ws, bb, hh)),
        wfeed(rest, wstep(ws, bb), wstep.short(ws, bb, hh)))

# the encoder's book is the one written out
def dcbook.eq() -> {Jenc.encode.huff(Jenc.encode.dccounts(), Jenc.encode.dcsyms()) == M2.dcbook.lit() : Array<U32>}:
  {==}

# the encoder's book is the one written out
def acbook.eq() -> {Jenc.encode.huff(Jenc.encode.accounts(), Jenc.encode.acsyms()) == M2.acbook.lit() : Array<U32>}:
  {==}

# the blocks' bits, one after another
def tbits(ts: List<&2, L1.JBlkTok>) -> List<&2, Bool>:
  match ts:
    case Nil{}:
      []
    case tt <> rest:
      List.append(&2, Bool, M2.blkbits(tt), tbits(rest))

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
  &ts: List<&2, L1.JBlkTok> -> &_e: {Jenc.encode.mcus(nn, (aa, M2.book(), py, pb, pr, bit), mx, my, mw, ww, hh,
    Jenc.encode.ctx()) == L1.jpg.feed(tbits(ts), bit) : Jenc.Put} -> &_l: {List.length(&2, L1.JBlkTok,
      ts) == tri(nn) : Nat} ->
    {L1.jpg.allwf(ts) == True{} : Bool}

# the rest of the MCU loop, from any state
def McusIh(+_nn: Nat, +_mw: U32, +_ww: U32, +_hh: U32) -> Type:
  @a2: Array<U32> -> @q1: U32 -> @q2: U32 -> @q3: U32 -> @p2: Jenc.Put -> @x2: U32 -> @y2: U32 -> @h1: {U32.is_lt(q1,
    2048) == True{} : Bool} -> @h2: {U32.is_lt(q2, 2048) == True{} : Bool} -> @h3: {U32.is_lt(q3, 2048) == True{} :
    Bool} -> McusOut(_nn, a2, q1, q2, q3, p2, x2, y2, _mw, _ww, _hh)

# three blocks, then the rest's blocks, fed to the writer
def feed_tri(
  +t1: L1.JBlkTok,
  +t2: L1.JBlkTok,
  +t3: L1.JBlkTok,
  +ts: List<&2, L1.JBlkTok>,
  +bit: Jenc.Put
) -> {L1.jpg.feed(tbits(ts), M2.feed3b(t1, t2, t3, bit)) == L1.jpg.feed(tbits(t1 <> t2 <> t3 <> ts),
  bit) : Jenc.Put}:
  +b1 = M2.blkbits(t1)
  +b2 = M2.blkbits(t2)
  +b3 = M2.blkbits(t3)
  +rs = tbits(ts)
  Equal.sym(Jenc.Put, L1.jpg.feed(List.append(&2, Bool, b1, List.append(&2, Bool, b2, List.append(&2, Bool, b3,
    rs))), bit),
    L1.jpg.feed(rs, M2.feed3b(t1, t2, t3, bit)), Equal.trans(Jenc.Put, L1.jpg.feed(List.append(&2, Bool, b1,
      List.append(&2, Bool,
    b2, List.append(&2, Bool, b3, rs))), bit), L1.jpg.feed(List.append(&2, Bool, b2, List.append(&2, Bool, b3, rs)),
    L1.jpg.feed(b1, bit)), L1.jpg.feed(rs, M2.feed3b(t1, t2, t3, bit)), M2.feed_app(b1, List.append(&2, Bool, b2,
      List.append(&2,
    Bool, b3, rs)), bit), Equal.trans(Jenc.Put, L1.jpg.feed(List.append(&2, Bool, b2, List.append(&2, Bool, b3, rs)),
    L1.jpg.feed(b1, bit)), L1.jpg.feed(List.append(&2, Bool, b3, rs), L1.jpg.feed(b2, L1.jpg.feed(b1, bit))),
      L1.jpg.feed(rs, M2.feed3b(t1, t2,
    t3, bit)), M2.feed_app(b2, List.append(&2, Bool, b3, rs), L1.jpg.feed(b1, bit)), M2.feed_app(b3, rs,
      L1.jpg.feed(b2,
    L1.jpg.feed(b1, bit))))))

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
  +_t1: L1.JBlkTok,
  +_t2: L1.JBlkTok,
  +_t3: L1.JBlkTok,
  _a2: Array<U32>,
  +_d1: U32,
  +_d2: U32,
  +_d3: U32
) -> Type:
  {Jenc.encode.step.tile(Jenc.encode.tile(_aa, _ww, _hh, (_mx * 8 : U32), (_my * 8 : U32)), M2.book(), _bit, _py, _pb,
    _pr, M2.kern(), Jpeg.decode.zig(), Jenc.encode.quant()) == (_a2, M2.book(), _d1, _d2, _d3, M2.feed3b(_t1, _t2, _t3,
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
  +_t1: L1.JBlkTok,
  +_t2: L1.JBlkTok,
  +_t3: L1.JBlkTok,
  _a2: Array<U32>,
  +_d1: U32,
  +_d2: U32,
  +_d3: U32
) -> Type:
  McusOut(_nn, _a2, _d1, _d2, _d3, M2.feed3b(_t1, _t2, _t3, _bit), Jenc.encode.nx(U32.is_lt((_mx + 1 : U32), _mw), _mx),
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
  +t1: L1.JBlkTok,
  +t2: L1.JBlkTok,
  +t3: L1.JBlkTok,
  -a2: Array<U32>,
  +d1: U32,
  +d2: U32,
  +d3: U32,
  ee: mcus_fin.ee.ty(aa, py, pb, pr, bit, mx, my, ww, hh, t1, t2, t3, a2, d1, d2, d3),
  w1: {L1.jpg.blkwf(t1) == True{} : Bool},
  w2: {L1.jpg.blkwf(t2) == True{} : Bool},
  w3: {L1.jpg.blkwf(t3) == True{} : Bool},
  rest: mcus_fin.rest.ty(nn, bit, mx, my, mw, ww, hh, t1, t2, t3, a2, d1, d2, d3)
) -> McusOut(1n+nn, aa, py, pb, pr, bit, mx, my, mw, ww, hh):
  (+ts, er, el, ew) = rest
  +mo = U32.is_lt((mx + 1 : U32), mw)
  +cx = Jenc.encode.ctx()
  +p3 = M2.feed3b(t1, t2, t3, bit)
  (t1 <> t2 <> t3 <> ts, Equal.trans(Jenc.Put, Jenc.encode.mcus(nn, Jenc.encode.step.y(aa, M2.book(), bit, py, pb, pr,
    (mx * 8 : U32), (my * 8 : U32), ww, hh, cx), Jenc.encode.nx(mo, mx), Jenc.encode.ny(mo, my), mw, ww, hh, cx),
    Jenc.encode.mcus(nn, (a2, M2.book(), d1, d2, d3, p3), Jenc.encode.nx(mo, mx), Jenc.encode.ny(mo, my), mw, ww, hh,
        cx),
    L1.jpg.feed(tbits(t1 <> t2 <> t3 <> ts), bit), Equal.cong(Array<U32> & Jenc.Book & U32 & U32 & U32 & Jenc.Put,
    Jenc.Put, gg => Jenc.encode.mcus(nn, gg, Jenc.encode.nx(mo, mx), Jenc.encode.ny(mo, my), mw, ww, hh, cx),
    Jenc.encode.step.y(aa, M2.book(), bit, py, pb, pr, (mx * 8 : U32), (my * 8 : U32), ww, hh, cx), (a2, M2.book(), d1,
    d2, d3, p3), ee), Equal.trans(Jenc.Put, Jenc.encode.mcus(nn, (a2, M2.book(), d1, d2, d3, p3), Jenc.encode.nx(mo,
        mx),
    Jenc.encode.ny(mo, my), mw, ww, hh, cx), L1.jpg.feed(tbits(ts), p3),
      L1.jpg.feed(tbits(t1 <> t2 <> t3 <> ts), bit), er,
    feed_tri(t1, t2, t3, ts, bit))), Equal.cong(Nat, Nat, kk => 1n+(1n+(1n+kk)), List.length(&2, L1.JBlkTok, ts),
      tri(nn), el),
    Equal.trans(Bool, L1.jpg.also(L1.jpg.blkwf(t1), L1.jpg.also(L1.jpg.blkwf(t2),
      L1.jpg.also(L1.jpg.blkwf(t3), L1.jpg.allwf(ts)))),
    L1.jpg.also(L1.jpg.blkwf(t2), L1.jpg.also(L1.jpg.blkwf(t3), L1.jpg.allwf(ts))), True{},
      M2.also_t(L1.jpg.blkwf(t1), L1.jpg.also(L1.jpg.blkwf(t2),
    L1.jpg.also(L1.jpg.blkwf(t3), L1.jpg.allwf(ts))), w1), Equal.trans(Bool, L1.jpg.also(L1.jpg.blkwf(t2),
      L1.jpg.also(L1.jpg.blkwf(t3),
    L1.jpg.allwf(ts))), L1.jpg.also(L1.jpg.blkwf(t3), L1.jpg.allwf(ts)), True{}, M2.also_t(L1.jpg.blkwf(t2),
      L1.jpg.also(L1.jpg.blkwf(t3),
    L1.jpg.allwf(ts)), w2), Equal.trans(Bool, L1.jpg.also(L1.jpg.blkwf(t3), L1.jpg.allwf(ts)),
      L1.jpg.allwf(ts), True{}, M2.also_t(
    L1.jpg.blkwf(t3), L1.jpg.allwf(ts), w3), ew))))

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
  mo: M2.McuOut(Jenc.encode.tile(aa, ww, hh, (mx * 8 : U32), (my * 8 : U32)), bit, py, pb, pr)
) -> McusOut(1n+nn, aa, py, pb, pr, bit, mx, my, mw, ww, hh):
  (+t1, +t2, +t3, a2, +d1, +d2, +d3, e, h1, h2, h3, w1, w2, w3) = mo
  +mv = U32.is_lt((mx + 1 : U32), mw)
  mcus_fin(nn, aa, py, pb, pr, bit, mx, my, mw, ww, hh, t1, t2, t3, a2, d1, d2, d3, e, w1, w2, w3, ih(a2, d1, d2, d3,
    M2.feed3b(t1, t2, t3, bit), Jenc.encode.nx(mv, mx), Jenc.encode.ny(mv, my), h1, h2, h3))

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
        mcus_ok(mm, a2, q1, q2, q3, p2, x2, y2, mw, ww, hh, h1, h2, h3), M2.mcu(Jenc.encode.tile(aa, ww, hh,
          (mx * 8 : U32),
        (my * 8 : U32)), bit, py, pb, pr, hy, hb, hr))

# the bits of a zero block: the DC code of size 0, then EOB (Annex K: 00, 1010)
def jenc.zb() -> List<&2, Bool>:
  [False{}, False{}, True{}, False{}, True{}, False{}]

# the encoder's zero block, packed six bits at once, is the model writer fed its bits
def zput_eq(
  ws: WS,
  hh: {wshort(ws) == True{} : Bool}
) -> {Jenc.encode.zput(wput(ws)) == wput(wm(jenc.zb(), ws)) : Jenc.Put}:
  match ws:
    case WS{out, pp}:
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
                                      Empty.absurd({Jenc.encode.zput(wput(WS{out,
                                        p0 <> p1 <> p2 <> p3 <> p4 <> p5 <> p6 <> p7 <> t7})) ==
                                        wput(wm([False{}, False{}, True{}, False{}, True{}, False{}],
                                        WS{out, p0 <> p1 <> p2 <> p3 <> p4 <> p5 <> p6 <> p7 <> t7})) : Jenc.Put},
                                        long8(t7, hh))

# the model writer fed two runs of bits is fed their join
def wm_app(
  xs: List<&2, Bool>,
  +ys: List<&2, Bool>,
  ws: WS
) -> {wm(List.append(&2, Bool, xs, ys), ws) == wm(ys, wm(xs, ws)) : WS}:
  match xs:
    case Nil{}:
      {==}
    case bb <> rest:
      wm_app(rest, ys, wstep(ws, bb))

# the model writer keeps fewer than 8 pending bits
def wm_short(
  bs: List<&2, Bool>,
  +ws: WS,
  hh: {wshort(ws) == True{} : Bool}
) -> {wshort(wm(bs, ws)) == True{} : Bool}:
  match bs:
    case Nil{}:
      hh
    case +bb <> rest:
      wm_short(rest, wstep(ws, bb), wstep.short(ws, bb, hh))

# a zero block: DC size 0, then EOB
def zbt() -> L1.JBlkTok:
  L1.JBlkTok{0, [], [L1.JTok{0, []}]}

# the zero blocks of n MCUs
def ztoks(nn: Nat) -> List<&2, L1.JBlkTok>:
  match nn:
    case 0n:
      []
    case 1n+mm:
      zbt() <> zbt() <> zbt() <> ztoks(mm)

# three zero blocks, packed, are the model writer fed their bits
def ztri_eq(
  +ws: WS,
  +hh: {wshort(ws) == True{} : Bool}
) -> {Jenc.encode.ztri(wput(ws)) == wput(wm(jenc.zb(), wm(jenc.zb(), wm(jenc.zb(), ws)))) : Jenc.Put}:
  +w1 = wm(jenc.zb(), ws)
  +w2 = wm(jenc.zb(), w1)
  +h1 = {wm_short(jenc.zb(), ws, hh) : {wshort(w1) == True{} : Bool}}
  +h2 = {wm_short(jenc.zb(), w1, h1) : {wshort(w2) == True{} : Bool}}
  Equal.trans(Jenc.Put, Jenc.encode.zput(Jenc.encode.zput(Jenc.encode.zput(wput(ws)))),
    Jenc.encode.zput(Jenc.encode.zput(wput(w1))), wput(wm(jenc.zb(), w2)), Equal.cong(Jenc.Put, Jenc.Put, pp =>
    Jenc.encode.zput(Jenc.encode.zput(pp)), Jenc.encode.zput(wput(ws)), wput(w1), zput_eq(ws, hh)), Equal.trans(
    Jenc.Put, Jenc.encode.zput(Jenc.encode.zput(wput(w1))), Jenc.encode.zput(wput(w2)), wput(wm(jenc.zb(),
      w2)),
    Equal.cong(Jenc.Put, Jenc.Put, pp => Jenc.encode.zput(pp), Jenc.encode.zput(wput(w1)), wput(w2), zput_eq(w1,
    h1)), zput_eq(w2, h2)))

# the encoder's zero MCUs are the model writer fed the zero blocks' bits
def nm(
  nn: Nat,
  +ws: WS,
  +hh: {wshort(ws) == True{} : Bool}
) -> {Jenc.encode.neutral.mcus(nn, wput(ws)) == wput(wm(tbits(ztoks(nn)), ws)) : Jenc.Put}:
  match nn:
    case 0n:
      {==}
    case 1n+ +mm:
      +zz = jenc.zb()
      +w3 = wm(zz, wm(zz, wm(zz, ws)))
      +h3 = {wm_short(zz, wm(zz, wm(zz, ws)), wm_short(zz, wm(zz, ws), wm_short(zz, ws,
        hh))) : {wshort(w3) ==
        True{} : Bool}}
      +tt = tbits(ztoks(mm))
      Equal.trans(Jenc.Put, Jenc.encode.neutral.mcus(mm, Jenc.encode.ztri(wput(ws))), Jenc.encode.neutral.mcus(mm,
        wput(w3)), wput(wm(List.append(&2, Bool, zz, List.append(&2, Bool, zz, List.append(&2, Bool, zz,
          tt))),
        ws)), Equal.cong(Jenc.Put, Jenc.Put, pp => Jenc.encode.neutral.mcus(mm, pp), Jenc.encode.ztri(wput(ws)),
        wput(w3), ztri_eq(ws, hh)), Equal.trans(Jenc.Put, Jenc.encode.neutral.mcus(mm, wput(w3)),
          wput(wm(tt,
        w3)), wput(wm(List.append(&2, Bool, zz, List.append(&2, Bool, zz, List.append(&2, Bool, zz, tt))), ws)),
        nm(mm, w3, h3), Equal.cong(WS, Jenc.Put, ss => wput(ss), wm(tt, w3), wm(List.append(&2, Bool,
          zz,
        List.append(&2, Bool, zz, List.append(&2, Bool, zz, tt))), ws), Equal.sym(WS, wm(List.append(&2, Bool,
          zz,
        List.append(&2, Bool, zz, List.append(&2, Bool, zz, tt))), ws), wm(tt, w3), Equal.trans(WS, wm(
        List.append(&2, Bool, zz, List.append(&2, Bool, zz, List.append(&2, Bool, zz, tt))), ws), wm(List.append(&2,
        Bool, zz, List.append(&2, Bool, zz, tt)), wm(zz, ws)), wm(tt, w3), wm_app(zz, List.append(&2, Bool, zz,
        List.append(&2, Bool, zz, tt)), ws), Equal.trans(WS, wm(List.append(&2, Bool, zz, List.append(&2,
          Bool, zz,
        tt)), wm(zz, ws)), wm(List.append(&2, Bool, zz, tt), wm(zz, wm(zz, ws))), wm(tt, w3),
          wm_app(zz,
        List.append(&2, Bool, zz, tt), wm(zz, ws)), wm_app(zz, tt, wm(zz, wm(zz, ws)))))))))

# three zero blocks more
def zwf.s(
  +mm: Nat,
  rr: &_l: {List.length(&2, L1.JBlkTok, ztoks(mm)) == tri(mm) : Nat} -> {L1.jpg.allwf(ztoks(mm)) == True{} : Bool}
) -> &_l: {List.length(&2, L1.JBlkTok,
  ztoks(1n+mm)) == tri(1n+mm) : Nat} -> {L1.jpg.allwf(ztoks(1n+mm)) == True{} : Bool}:
  (el, ew) = rr
  (Equal.cong(Nat, Nat, kk => 1n+(1n+(1n+kk)), List.length(&2, L1.JBlkTok, ztoks(mm)), tri(mm), el), ew)

# every zero MCU's blocks are read whole, three per MCU
def zwf(
  nn: Nat
) -> &_l: {List.length(&2, L1.JBlkTok, ztoks(nn)) == tri(nn) : Nat} -> {L1.jpg.allwf(ztoks(nn)) == True{} : Bool}:
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
        hh <> acc), M1.ras.add_succ(List.length(&2, U32, tt), List.length(&2, U32, acc)))

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
                qq) <> acc, []), M1.ras.add_zero(1n+List.length(&2, U32, acc)))
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
                1n+Nat.add(List.length(&2, U32, gt), List.length(&2, U32, acc)), M1.ras.add_succ(List.length(&2, U32,
                    gt),
                List.length(&2, U32, acc))))

# a block's coefficients, flat or transformed, are 64
def zzlen(
  flat: Bool,
  rows: List<&2, List<&2, U32>>
) -> {List.length(&2, U32, Jenc.encode.zz(flat, rows, M2.kern(), Jpeg.decode.zig(), Jenc.encode.quant())) == 64n : Nat}:
  match flat:
    case True{}:
      {==}
    case False{}:
      +kn = M2.kern()
      zzl([1, 8, 16, 9, 2, 3, 10, 17, 24, 32, 25, 18, 11, 4, 5, 12, 19, 26, 33, 40, 48, 41, 34, 27, 20, 13, 6, 7, 14,
        21,
        28, 35, 42, 49, 56, 57, 50, 43, 36, 29, 22, 15, 23, 30, 37, 44, 51, 58, 59, 52, 45, 38, 31, 39, 46, 53, 60,
          61, 54,
        47, 55, 62, 63], Array.get(U32, Jenc.encode.zzq.load(Jenc.encode.fdct.go(Jenc.encode.pass1(Jenc.encode.levels(
        rows), kn, Jpeg.decode.plane(64), 0), kn), Jpeg.decode.plane(64), 0), 0), Jenc.encode.zzq.take(
        Jenc.encode.quant()), [])

# one block the solid path codes: its tile's rows, then the block coder
def BUseOut(-got: Array<U32> & List<&2, List<&2, U32>> & Bool, +pp: Jenc.Put, +pred: U32) -> Type:
  &bt: L1.JBlkTok -> &aa: Array<U32> -> &dd: U32 -> &_e: {Jenc.encode.block.use(M2.book(), pp, pred, got, M2.kern(),
    Jpeg.decode.zig(), Jenc.encode.quant()) == (aa, M2.book(), dd, L1.jpg.feed(M2.blkbits(bt), pp)) : Array<U32> &
    Jenc.Book & U32 & Jenc.Put} -> &_h: {U32.is_lt(dd, 2048) == True{} : Bool} -> {L1.jpg.blkwf(bt) == True{} : Bool}

# the block coder's result, with the array handed on
def buse.fin(
  aa: Array<U32>,
  -zz: List<&2, U32>,
  +pp: Jenc.Put,
  +pred: U32,
  bo: M2.BlkOut(pred, pp, zz)
) -> &bt: L1.JBlkTok -> &a2: Array<U32> -> &dd: U32 -> &_e: {Jenc.encode.block.pair(Jenc.encode.block.go(M2.book(), pp,
  pred, zz), aa) == (a2, M2.book(), dd, L1.jpg.feed(M2.blkbits(bt),
  pp)) : Array<U32> & Jenc.Book & U32 & Jenc.Put} -> &_h:
  {U32.is_lt(dd, 2048) == True{} : Bool} -> {L1.jpg.blkwf(bt) == True{} : Bool}:
  (+bt, +dd, eb, hd, hw) = bo
  (bt, aa, dd, Equal.cong(Jenc.Book & U32 & Jenc.Put, Array<U32> & Jenc.Book & U32 & Jenc.Put, gg =>
    Jenc.encode.block.pair(gg, aa), Jenc.encode.block.go(M2.book(), pp, pred, zz), (M2.book(), dd,
      L1.jpg.feed(M2.blkbits(bt),
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
  buse.fin(aa, Jenc.encode.zz(flat, rows, M2.kern(), Jpeg.decode.zig(), Jenc.encode.quant()), pp, pred, M2.jenc.blk(
    Jenc.encode.zz(flat, rows, M2.kern(), Jpeg.decode.zig(), Jenc.encode.quant()), pred, pp, zzlen(flat, rows), hp))

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
  &t1: L1.JBlkTok -> &t2: L1.JBlkTok -> &t3: L1.JBlkTok -> &_e: {Jenc.encode.solid.y(aa, M2.book(), bit,
    Jenc.encode.ctx()) ==
    M2.feed3b(t1, t2, t3,
      bit) : Jenc.Put} -> &_w1: {L1.jpg.blkwf(t1) == True{} : Bool} -> &_w2: {L1.jpg.blkwf(t2) == True{} :
    Bool} -> {L1.jpg.blkwf(t3) == True{} : Bool}

# the type of sol3's parameter e1
def sol3.e1.ty(_aa: Array<U32>, +_bit: Jenc.Put, +_t1: L1.JBlkTok, _a1: Array<U32>, +_d1: U32) -> Type:
  {Jenc.encode.block.use(M2.book(), _bit, 1024, srows(_aa, 0), M2.kern(), Jpeg.decode.zig(),
      Jenc.encode.quant()) == (_a1,
    M2.book(), _d1, L1.jpg.feed(M2.blkbits(_t1), _bit)) : Array<U32> & Jenc.Book & U32 & Jenc.Put}

# the type of sol3's parameter e2
def sol3.e2.ty(
  +_bit: Jenc.Put,
  +_t1: L1.JBlkTok,
  _a1: Array<U32>,
  +_t2: L1.JBlkTok,
  _a2: Array<U32>,
  +_d2: U32
) -> Type:
  {Jenc.encode.block.use(M2.book(), L1.jpg.feed(M2.blkbits(_t1), _bit), 1024, srows(_a1, 1), M2.kern(),
    Jpeg.decode.zig(), Jenc.encode.quant()) == (_a2, M2.book(), _d2, L1.jpg.feed(M2.blkbits(_t2),
    L1.jpg.feed(M2.blkbits(_t1), _bit))) : Array<U32> & Jenc.Book & U32 & Jenc.Put}

# the solid path's Cr block, after its Y and Cb blocks
def sol3(
  -aa: Array<U32>,
  +bit: Jenc.Put,
  +t1: L1.JBlkTok,
  -a1: Array<U32>,
  +d1: U32,
  e1: sol3.e1.ty(aa, bit, t1, a1, d1),
  w1: {L1.jpg.blkwf(t1) == True{} : Bool},
  +t2: L1.JBlkTok,
  -a2: Array<U32>,
  +d2: U32,
  e2: sol3.e2.ty(bit, t1, a1, t2, a2, d2),
  w2: {L1.jpg.blkwf(t2) == True{} : Bool},
  b3: BUseOut(srows(a2, 2), L1.jpg.feed(M2.blkbits(t2), L1.jpg.feed(M2.blkbits(t1), bit)), 1024)
) -> SolOut(aa, bit):
  (+t3, a3, +d3, e3, _h, w3) = b3
  +cx = Jenc.encode.ctx()
  +kn = M2.kern()
  +zg = Jpeg.decode.zig()
  +qs = Jenc.encode.quant()
  +p1 = L1.jpg.feed(M2.blkbits(t1), bit)
  +p2 = L1.jpg.feed(M2.blkbits(t2), p1)
  +p3 = L1.jpg.feed(M2.blkbits(t3), p2)
  (t1, t2, t3, Equal.trans(Jenc.Put, Jenc.encode.solid.cb(Jenc.encode.block.use(M2.book(), bit, 1024, srows(aa, 0), kn,
    zg, qs), cx), Jenc.encode.solid.cb((a1, M2.book(), d1, p1), cx), p3, Equal.cong(Array<U32> & Jenc.Book & U32 &
    Jenc.Put, Jenc.Put, gg => Jenc.encode.solid.cb(gg, cx), Jenc.encode.block.use(M2.book(), bit, 1024, srows(aa, 0),
        kn,
    zg, qs), (a1, M2.book(), d1, p1), e1), Equal.trans(Jenc.Put, Jenc.encode.solid.cr(Jenc.encode.block.use(M2.book(),
    p1, 1024, srows(a1, 1), kn, zg, qs), cx), Jenc.encode.solid.cr((a2, M2.book(), d2, p2), cx), p3, Equal.cong(
    Array<U32> & Jenc.Book & U32 & Jenc.Put, Jenc.Put, gg => Jenc.encode.solid.cr(gg, cx), Jenc.encode.block.use(
    M2.book(), p1, 1024, srows(a1, 1), kn, zg, qs), (a2, M2.book(), d2, p2), e2), Equal.cong(Array<U32> & Jenc.Book &
    U32 & Jenc.Put, Jenc.Put, gg => Jenc.encode.solid.end(gg), Jenc.encode.block.use(M2.book(), p2, 1024, srows(a2, 2),
    kn, zg, qs), (a3, M2.book(), d3, p3), e3))), w1, w2, w3)

# the type of sol2's parameter e1
def sol2.e1.ty(_aa: Array<U32>, +_bit: Jenc.Put, +_t1: L1.JBlkTok, _a1: Array<U32>, +_d1: U32) -> Type:
  {Jenc.encode.block.use(M2.book(), _bit, 1024, srows(_aa, 0), M2.kern(), Jpeg.decode.zig(),
      Jenc.encode.quant()) == (_a1,
    M2.book(), _d1, L1.jpg.feed(M2.blkbits(_t1), _bit)) : Array<U32> & Jenc.Book & U32 & Jenc.Put}

# the solid path's Cb and Cr blocks, after its Y block
def sol2(
  -aa: Array<U32>,
  +bit: Jenc.Put,
  +t1: L1.JBlkTok,
  -a1: Array<U32>,
  +d1: U32,
  e1: sol2.e1.ty(aa, bit, t1, a1, d1),
  w1: {L1.jpg.blkwf(t1) == True{} : Bool},
  b2: BUseOut(srows(a1, 1), L1.jpg.feed(M2.blkbits(t1), bit), 1024)
) -> SolOut(aa, bit):
  (+t2, a2, +d2, e2, _h, w2) = b2
  sol3(aa, bit, t1, a1, d1, e1, w1, t2, a2, d2, e2, w2, buse(srows(a2, 2), L1.jpg.feed(M2.blkbits(t2), L1.jpg.feed(
    M2.blkbits(t1), bit)), 1024, {==}))

# the solid path's blocks, after its Y block
def sol1(-aa: Array<U32>, +bit: Jenc.Put, b1: BUseOut(srows(aa, 0), bit, 1024)) -> SolOut(aa, bit):
  (+t1, a1, +d1, e1, _h, w1) = b1
  sol2(aa, bit, t1, a1, d1, e1, w1, buse(srows(a1, 1), L1.jpg.feed(M2.blkbits(t1), bit), 1024, {==}))

# the solid path's first MCU, whatever its one pixel holds
def sol(aa: Array<U32>, +bit: Jenc.Put) -> SolOut(aa, bit):
  sol1(aa, bit, buse(srows(aa, 0), bit, 1024, {==}))

# the encoder's MCU count
def mcun(+ww: U32, +hh: U32) -> U32:
  (U32.div((ww + 7 : U32), 8) * U32.div((hh + 7 : U32), 8) : U32)

# the encoder's books are the books written out, bk being them. The statement
# is written out, not named (a named one would have the checker normalize both
# sides where go_fin and solid_fin hand this proof on, building both Huffman
# books again at each use); bk only lets the header span lines
def bookeq(
  -bk: Jenc.Book,
  hb: {M2.book() == bk : Jenc.Book}
) -> {Jenc.encode.book(Jenc.encode.dccounts(), Jenc.encode.dcsyms(), Jenc.encode.accounts(),
  Jenc.encode.acsyms()) == bk : Jenc.Book}:
  %hb : {Jenc.encode.book(Jenc.encode.dccounts(), Jenc.encode.dcsyms(), Jenc.encode.accounts(),
    Jenc.encode.acsyms()) == _ : Jenc.Book}
  Equal.trans(Jenc.Book, Jenc.Book{Jenc.encode.huff(Jenc.encode.dccounts(), Jenc.encode.dcsyms()), Jenc.encode.huff(
    Jenc.encode.accounts(), Jenc.encode.acsyms())}, Jenc.Book{M2.dcbook.lit(), Jenc.encode.huff(Jenc.encode.accounts(),
    Jenc.encode.acsyms())}, M2.book(), Equal.cong(Array<U32>, Jenc.Book, xx => Jenc.Book{xx, Jenc.encode.huff(
    Jenc.encode.accounts(), Jenc.encode.acsyms())}, Jenc.encode.huff(Jenc.encode.dccounts(), Jenc.encode.dcsyms()),
    M2.dcbook.lit(), dcbook.eq()), Equal.cong(Array<U32>, Jenc.Book, xx => Jenc.Book{M2.dcbook.lit(), xx},
    Jenc.encode.huff(Jenc.encode.accounts(), Jenc.encode.acsyms()), M2.acbook.lit(), acbook.eq()))

# blocks' bits, two lists joined
def tbits_app(
  xs: List<&2, L1.JBlkTok>,
  +ys: List<&2, L1.JBlkTok>
) -> {tbits(List.append(&2, L1.JBlkTok, xs, ys)) == List.append(&2, Bool, tbits(xs),
  tbits(ys)) : List<&2, Bool>}:
  match xs:
    case Nil{}:
      {==}
    case +tt <> +rest:
      Equal.trans(List<&2, Bool>, List.append(&2, Bool, M2.blkbits(tt), tbits(List.append(&2, L1.JBlkTok, rest,
        ys))),
        List.append(&2, Bool, M2.blkbits(tt), List.append(&2, Bool, tbits(rest), tbits(ys))), List.append(&2,
          Bool,
        List.append(&2, Bool, M2.blkbits(tt), tbits(rest)), tbits(ys)), Equal.cong(List<&2, Bool>, List<&2,
          Bool>,
        zs => List.append(&2, Bool, M2.blkbits(tt), zs), tbits(List.append(&2, L1.JBlkTok, rest, ys)),
          List.append(&2,
        Bool, tbits(rest), tbits(ys)), tbits_app(rest, ys)), Equal.sym(List<&2, Bool>, List.append(&2, Bool,
        List.append(&2, Bool, M2.blkbits(tt), tbits(rest)), tbits(ys)), List.append(&2, Bool, M2.blkbits(tt),
        List.append(&2, Bool, tbits(rest), tbits(ys))), M2.huf.app_assoc(M2.blkbits(tt), tbits(rest),
        tbits(ys))))

# a list of blocks, n MCUs' worth, each read whole
def ZOut(+_zs: List<&2, L1.JBlkTok>, +_nn: Nat) -> Type:
  &_l: {List.length(&2, L1.JBlkTok, _zs) == tri(_nn) : Nat} -> {L1.jpg.allwf(_zs) == True{} : Bool}

# a path's entropy-coded bytes: blocks the decoder reads whole, three per MCU, fed to the writer and padded
def PathOut(-bytes: List<&2, U32>, +nn: Nat) -> Type:
  &ts: List<&2, L1.JBlkTok> -> &_e: {bytes == Jenc.encode.pad(L1.jpg.feed(tbits(ts),
    Jenc.encode.put0())) : List<&2, U32>} ->
    &_l: {List.length(&2, L1.JBlkTok, ts) == tri(nn) : Nat} -> {L1.jpg.allwf(ts) == True{} : Bool}

# the neutral path, the zero blocks' count and checks named
def neutral_fin(
  +ww: U32,
  +hh: U32,
  rr: ZOut(ztoks(U32.to_nat(mcun(ww, hh))), U32.to_nat(mcun(ww, hh)))
) -> PathOut(Jenc.encode.neutral(ww, hh), U32.to_nat(mcun(ww, hh))):
  (el, ew) = rr
  +nn = U32.to_nat(mcun(ww, hh))
  +ws = {WS{[], []} : WS}
  +zt = tbits(ztoks(nn))
  (ztoks(nn), Equal.cong(Jenc.Put, List<&2, U32>, pp => Jenc.encode.pad(pp), Jenc.encode.neutral.mcus(nn, wput(ws)),
    L1.jpg.feed(zt, wput(ws)), Equal.trans(Jenc.Put, Jenc.encode.neutral.mcus(nn, wput(ws)),
      wput(wm(zt, ws)),
    L1.jpg.feed(zt, wput(ws)), nm(nn, ws, {==}), Equal.sym(Jenc.Put, L1.jpg.feed(zt, wput(ws)),
      wput(wm(zt, ws)),
    wfeed(zt, ws, {==})))), el, ew)

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
    L1.jpg.feed(tbits(ts), p0), Equal.trans(Jenc.Put, Jenc.encode.mcus(nn,
      (Jenc.encode.pix.load(U32.to_nat((ww * hh :
    U32)), px, Jpeg.decode.plane((ww * hh : U32)), 0), Jenc.encode.book(Jenc.encode.dccounts(), Jenc.encode.dcsyms(),
    Jenc.encode.accounts(), Jenc.encode.acsyms()), 1024, 1024, 1024, p0), 0, 0, mw, ww, hh, cx), Jenc.encode.mcus(nn,
    (Jenc.encode.pix.load(U32.to_nat((ww * hh : U32)), px, Jpeg.decode.plane((ww * hh : U32)), 0), M2.book(), 1024,
        1024,
    1024, p0), 0, 0, mw, ww, hh, cx), L1.jpg.feed(tbits(ts), p0), Equal.cong(Jenc.Book, Jenc.Put, bk =>
    Jenc.encode.mcus(nn, (Jenc.encode.pix.load(U32.to_nat((ww * hh : U32)), px, Jpeg.decode.plane((ww * hh : U32)), 0),
    bk, 1024, 1024, 1024, p0), 0, 0, mw, ww, hh, cx), Jenc.encode.book(Jenc.encode.dccounts(), Jenc.encode.dcsyms(),
    Jenc.encode.accounts(), Jenc.encode.acsyms()), M2.book(), bookeq(M2.book(), {==})), er)), el, ew)

# the go path
def go_ok(+ww: U32, +hh: U32, +px: List<&2, U32>) -> PathOut(Jenc.encode.go(ww, hh, px), U32.to_nat(mcun(ww, hh))):
  go_fin(ww, hh, px, mcus_ok(U32.to_nat(mcun(ww, hh)), Jenc.encode.pix.load(U32.to_nat((ww * hh : U32)), px,
    Jpeg.decode.plane((ww * hh : U32)), 0), 1024, 1024, 1024, Jenc.encode.put0(), 0, 0, U32.div((ww + 7 : U32), 8), ww,
    hh, {==}, {==}, {==}))

# the solid path's first MCU is the model writer fed its blocks' bits
def sol_ws(
  +t1: L1.JBlkTok,
  +t2: L1.JBlkTok,
  +t3: L1.JBlkTok
) -> {M2.feed3b(t1, t2, t3, Jenc.encode.put0()) == wput(wm(tbits( t1 <> t2 <> t3 <> []), WS{[],
  []})) : Jenc.Put}:
  +ws = {WS{[], []} : WS}
  +tb = tbits(t1 <> t2 <> t3 <> [])
  Equal.trans(Jenc.Put, M2.feed3b(t1, t2, t3, wput(ws)), L1.jpg.feed(tb, wput(ws)), wput(wm(tb, ws)),
    feed_tri(t1, t2, t3, [], wput(ws)), wfeed(tb, ws, {==}))

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
  +ws = {WS{[], []} : WS}
  +xb = tbits(t1 <> t2 <> t3 <> [])
  +zk = ztoks(kk)
  +zt = tbits(zk)
  +w1s = wm(xb, ws)
  +hs = {wm_short(xb, ws, {==}) : {wshort(w1s) == True{} : Bool}}
  +p0 = Jenc.encode.put0()
  +cx = Jenc.encode.ctx()
  +ts = {t1 <> t2 <> t3 <> zk : List<&2, L1.JBlkTok>}
  (ts, Equal.cong(Jenc.Put, List<&2, U32>, pp => Jenc.encode.pad(pp), Jenc.encode.neutral.mcus(kk, Jenc.encode.solid.y(
    Array.set(U32, Jpeg.decode.plane(1), 0, color), Jenc.encode.book(Jenc.encode.dccounts(), Jenc.encode.dcsyms(),
      Jenc.encode.accounts(), Jenc.encode.acsyms()),
    p0, cx)), L1.jpg.feed(tbits(ts), p0), Equal.trans(Jenc.Put, Jenc.encode.neutral.mcus(kk,
      Jenc.encode.solid.y(Array.set(U32, Jpeg.decode.plane(1), 0, color),
    Jenc.encode.book(Jenc.encode.dccounts(), Jenc.encode.dcsyms(), Jenc.encode.accounts(), Jenc.encode.acsyms()), p0,
    cx)), Jenc.encode.neutral.mcus(kk, wput(w1s)), L1.jpg.feed(tbits(ts), p0), Equal.cong(Jenc.Put,
      Jenc.Put, pp =>
    Jenc.encode.neutral.mcus(kk, pp), Jenc.encode.solid.y(Array.set(U32, Jpeg.decode.plane(1), 0, color),
      Jenc.encode.book(Jenc.encode.dccounts(),
    Jenc.encode.dcsyms(), Jenc.encode.accounts(), Jenc.encode.acsyms()), p0, cx), wput(w1s), Equal.trans(Jenc.Put,
    Jenc.encode.solid.y(Array.set(U32, Jpeg.decode.plane(1), 0, color), Jenc.encode.book(Jenc.encode.dccounts(),
      Jenc.encode.dcsyms(), Jenc.encode.accounts(),
    Jenc.encode.acsyms()), p0, cx), Jenc.encode.solid.y(Array.set(U32, Jpeg.decode.plane(1), 0, color), M2.book(), p0,
      cx), wput(w1s), Equal.cong(Jenc.Book,
    Jenc.Put, bk => Jenc.encode.solid.y(Array.set(U32, Jpeg.decode.plane(1), 0, color), bk, p0, cx),
      Jenc.encode.book(Jenc.encode.dccounts(), Jenc.encode.dcsyms(),
    Jenc.encode.accounts(), Jenc.encode.acsyms()), M2.book(), bookeq(M2.book(), {==})), Equal.trans(Jenc.Put,
      Jenc.encode.solid.y(Array.set(U32, Jpeg.decode.plane(1), 0, color),
    M2.book(), p0, cx), M2.feed3b(t1, t2, t3, p0), wput(w1s), es, sol_ws(t1, t2, t3)))), Equal.trans(Jenc.Put,
    Jenc.encode.neutral.mcus(kk, wput(w1s)), wput(wm(zt, w1s)), L1.jpg.feed(tbits(ts), p0), nm(kk,
      w1s, hs),
    Equal.trans(Jenc.Put, wput(wm(zt, w1s)), wput(wm(List.append(&2, Bool, xb, zt), ws)),
      L1.jpg.feed(tbits(
    ts), p0), Equal.cong(WS, Jenc.Put, ss => wput(ss), wm(zt, w1s), wm(List.append(&2, Bool, xb, zt),
      ws),
    Equal.sym(WS, wm(List.append(&2, Bool, xb, zt), ws), wm(zt, w1s), wm_app(xb, zt, ws))), Equal.trans(
    Jenc.Put, wput(wm(List.append(&2, Bool, xb, zt), ws)), L1.jpg.feed(List.append(&2, Bool, xb, zt), p0),
      L1.jpg.feed(
    tbits(ts), p0), Equal.sym(Jenc.Put, L1.jpg.feed(List.append(&2, Bool, xb, zt), wput(ws)), wput(wm(
    List.append(&2, Bool, xb, zt), ws)), wfeed(List.append(&2, Bool, xb, zt), ws, {==})), Equal.cong(List<&2, Bool>,
    Jenc.Put, bs => L1.jpg.feed(bs, p0), List.append(&2, Bool, xb, zt), tbits(ts), Equal.sym(List<&2, Bool>,
      tbits(ts),
    List.append(&2, Bool, xb, zt), tbits_app(t1 <> t2 <> t3 <> [], zk)))))))), Equal.cong(Nat, Nat, nn =>
    1n+(1n+(1n+nn)), List.length(&2, L1.JBlkTok, zk), tri(kk), el), Equal.trans(Bool,
      L1.jpg.also(L1.jpg.blkwf(t1),
    L1.jpg.also(L1.jpg.blkwf(t2), L1.jpg.also(L1.jpg.blkwf(t3), L1.jpg.allwf(zk)))),
      L1.jpg.also(L1.jpg.blkwf(t2), L1.jpg.also(L1.jpg.blkwf(t3),
    L1.jpg.allwf(zk))), True{}, M2.also_t(L1.jpg.blkwf(t1), L1.jpg.also(L1.jpg.blkwf(t2),
      L1.jpg.also(L1.jpg.blkwf(t3), L1.jpg.allwf(
    zk))), w1), Equal.trans(Bool, L1.jpg.also(L1.jpg.blkwf(t2), L1.jpg.also(L1.jpg.blkwf(t3),
      L1.jpg.allwf(zk))),
    L1.jpg.also(L1.jpg.blkwf(t3), L1.jpg.allwf(zk)), True{}, M2.also_t(L1.jpg.blkwf(t2),
      L1.jpg.also(L1.jpg.blkwf(t3), L1.jpg.allwf(
    zk)), w2), Equal.trans(Bool, L1.jpg.also(L1.jpg.blkwf(t3), L1.jpg.allwf(zk)),
      L1.jpg.allwf(zk), True{},
    M2.also_t(L1.jpg.blkwf(t3), L1.jpg.allwf(zk), w3), ew))))

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
