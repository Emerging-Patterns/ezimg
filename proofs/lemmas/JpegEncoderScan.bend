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

# three for each MCU
def tri(nn: Nat) -> Nat:
  match nn:
    case 0n:
      0n
    case 1n+mm:
      1n+(1n+(1n+tri(mm)))

# the encoder's MCU loop from a state: the blocks it codes, fed to the writer, three per MCU, each read whole, each of
# the class the decoder's tables hold at its place from the start of an MCU on
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
  +hh: U32,
  +qq: U32
) -> Type:
  &ts: List<&2, L1.JBlkTok> -> &_e: {Jenc.encode.mcus(nn, (aa, Jenc.encode.bookof(False{}), Jenc.encode.bookof(True{}),
    py, pb, pr, bit), mx, my, mw, ww, hh, Jenc.encode.ctx(qq)) == L1.jpg.feed(L1.jpg.tbits(ts), bit) : Jenc.Put} ->
    &_l: {List.length(&2, L1.JBlkTok, ts) == tri(nn) : Nat} -> &_w: {L1.jpg.allwf(ts) == True{} : Bool} ->
    {L1.jpg.tagok(ts, (0, 0), L1.jpg.enc.frame(Jenc.K444{}, ww, hh), L1.jpg.enc.scan(Jenc.K444{})) == True{} :
    Bool}

# the rest of the MCU loop, from any state
def McusIh(+_nn: Nat, +_mw: U32, +_ww: U32, +_hh: U32, +_qq: U32) -> Type:
  @a2: Array<U32> -> @q1: U32 -> @q2: U32 -> @q3: U32 -> @p2: Jenc.Put -> @x2: U32 -> @y2: U32 -> @h1: {U32.is_lt(q1,
    2048) == True{} : Bool} -> @h2: {U32.is_lt(q2, 2048) == True{} : Bool} -> @h3: {U32.is_lt(q3, 2048) == True{} :
    Bool} -> McusOut(_nn, a2, q1, q2, q3, p2, x2, y2, _mw, _ww, _hh, _qq)

# three blocks, then the rest's blocks, fed to the writer
def feed_tri(
  +t1: L1.JBlkTok,
  +t2: L1.JBlkTok,
  +t3: L1.JBlkTok,
  +ts: List<&2, L1.JBlkTok>,
  +bit: Jenc.Put
) -> {L1.jpg.feed(L1.jpg.tbits(ts), M2.feed3b(t1, t2, t3, bit)) == L1.jpg.feed(L1.jpg.tbits(t1 <> t2 <> t3 <> ts),
  bit) : Jenc.Put}:
  +b1 = L1.jpg.blkbits(t1)
  +b2 = L1.jpg.blkbits(t2)
  +b3 = L1.jpg.blkbits(t3)
  +rs = L1.jpg.tbits(ts)
  Equal.sym(Jenc.Put, L1.jpg.feed(List.append(&2, Bool, b1, List.append(&2, Bool, b2, List.append(&2, Bool, b3,
    rs))), bit), L1.jpg.feed(rs, M2.feed3b(t1, t2, t3, bit)), Equal.trans(Jenc.Put, L1.jpg.feed(List.append(&2, Bool,
    b1, List.append(&2, Bool, b2, List.append(&2, Bool, b3, rs))), bit), L1.jpg.feed(List.append(&2, Bool, b2,
    List.append(&2, Bool, b3, rs)), L1.jpg.feed(b1, bit)), L1.jpg.feed(rs, M2.feed3b(t1, t2, t3, bit)),
    M2.feed_app(b1, List.append(&2, Bool, b2, List.append(&2, Bool, b3, rs)), bit), Equal.trans(Jenc.Put,
    L1.jpg.feed(List.append(&2, Bool, b2, List.append(&2, Bool, b3, rs)), L1.jpg.feed(b1, bit)),
    L1.jpg.feed(List.append(&2, Bool, b3, rs), L1.jpg.feed(b2, L1.jpg.feed(b1, bit))), L1.jpg.feed(rs,
    M2.feed3b(t1, t2, t3, bit)), M2.feed_app(b2, List.append(&2, Bool, b3, rs), L1.jpg.feed(b1, bit)),
    M2.feed_app(b3, rs, L1.jpg.feed(b2, L1.jpg.feed(b1, bit))))))

# a luminance block and two chrominance blocks, then more, sit at the places of the encoder's frame from the start
# of an MCU exactly when the more do
def tag3(
  +ww: U32,
  +hh: U32,
  +s1: U32,
  +x1: List<&2, Bool>,
  +a1: List<&2, L1.JTok>,
  +s2: U32,
  +x2: List<&2, Bool>,
  +a2: List<&2, L1.JTok>,
  +s3: U32,
  +x3: List<&2, Bool>,
  +a3: List<&2, L1.JTok>,
  +ts: List<&2, L1.JBlkTok>
) -> {L1.jpg.tagok(L1.JBlkTok{False{}, s1, x1, a1} <> L1.JBlkTok{True{}, s2, x2, a2} <> L1.JBlkTok{True{}, s3, x3,
  a3} <> ts, (0, 0), L1.jpg.enc.frame(Jenc.K444{}, ww, hh), L1.jpg.enc.scan(Jenc.K444{})) == L1.jpg.tagok(ts, (0,
  0), L1.jpg.enc.frame(Jenc.K444{}, ww, hh), L1.jpg.enc.scan(Jenc.K444{})) : Bool}:
  {==}

# the MCU's statement for the loop's state: its tile, both books, and the context's quantisation columns
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
  +_qq: U32,
  +_s1: U32,
  +_x1: List<&2, Bool>,
  +_a1: List<&2, L1.JTok>,
  +_s2: U32,
  +_x2: List<&2, Bool>,
  +_a2: List<&2, L1.JTok>,
  +_s3: U32,
  +_x3: List<&2, Bool>,
  +_a3: List<&2, L1.JTok>,
  _ar: Array<U32>,
  +_d1: U32,
  +_d2: U32,
  +_d3: U32
) -> Type:
  {Jenc.encode.step.y(_aa, Jenc.encode.bookof(False{}), Jenc.encode.bookof(True{}), _bit, _py, _pb, _pr, (_mx * 8 :
    U32), (_my * 8 : U32), _ww, _hh, Jenc.encode.ctx(_qq)) == (_ar, Jenc.encode.bookof(False{}),
    Jenc.encode.bookof(True{}), _d1, _d2, _d3, M2.feed3b(L1.JBlkTok{False{}, _s1, _x1, _a1}, L1.JBlkTok{True{}, _s2,
    _x2, _a2}, L1.JBlkTok{True{}, _s3, _x3, _a3}, _bit)) : Array<U32> & Jenc.Book & Jenc.Book & U32 & U32 & U32 &
    Jenc.Put}

# the type of mcus_fin's parameter rest
def mcus_fin.rest.ty(
  +_nn: Nat,
  +_bit: Jenc.Put,
  +_mx: U32,
  +_my: U32,
  +_mw: U32,
  +_ww: U32,
  +_hh: U32,
  +_qq: U32,
  +_s1: U32,
  +_x1: List<&2, Bool>,
  +_a1: List<&2, L1.JTok>,
  +_s2: U32,
  +_x2: List<&2, Bool>,
  +_a2: List<&2, L1.JTok>,
  +_s3: U32,
  +_x3: List<&2, Bool>,
  +_a3: List<&2, L1.JTok>,
  _ar: Array<U32>,
  +_d1: U32,
  +_d2: U32,
  +_d3: U32
) -> Type:
  McusOut(_nn, _ar, _d1, _d2, _d3, M2.feed3b(L1.JBlkTok{False{}, _s1, _x1, _a1}, L1.JBlkTok{True{}, _s2, _x2, _a2},
    L1.JBlkTok{True{}, _s3, _x3, _a3}, _bit), Jenc.encode.nx(U32.is_lt((_mx + 1 : U32), _mw), _mx),
    Jenc.encode.ny(U32.is_lt((_mx + 1 : U32), _mw), _my), _mw, _ww, _hh, _qq)

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
  +qq: U32,
  +s1: U32,
  +x1: List<&2, Bool>,
  +a1: List<&2, L1.JTok>,
  +s2: U32,
  +x2: List<&2, Bool>,
  +a2: List<&2, L1.JTok>,
  +s3: U32,
  +x3: List<&2, Bool>,
  +a3: List<&2, L1.JTok>,
  -ar: Array<U32>,
  +d1: U32,
  +d2: U32,
  +d3: U32,
  ee: mcus_fin.ee.ty(aa, py, pb, pr, bit, mx, my, ww, hh, qq, s1, x1, a1, s2, x2, a2, s3, x3, a3, ar, d1, d2, d3),
  w1: {L1.jpg.blkwf(L1.JBlkTok{False{}, s1, x1, a1}) == True{} : Bool},
  w2: {L1.jpg.blkwf(L1.JBlkTok{True{}, s2, x2, a2}) == True{} : Bool},
  w3: {L1.jpg.blkwf(L1.JBlkTok{True{}, s3, x3, a3}) == True{} : Bool},
  rest: mcus_fin.rest.ty(nn, bit, mx, my, mw, ww, hh, qq, s1, x1, a1, s2, x2, a2, s3, x3, a3, ar, d1, d2, d3)
) -> McusOut(1n+nn, aa, py, pb, pr, bit, mx, my, mw, ww, hh, qq):
  (+ts, er, el, ew, eg) = rest
  +t1 = {L1.JBlkTok{False{}, s1, x1, a1} : L1.JBlkTok}
  +t2 = {L1.JBlkTok{True{}, s2, x2, a2} : L1.JBlkTok}
  +t3 = {L1.JBlkTok{True{}, s3, x3, a3} : L1.JBlkTok}
  +mo = U32.is_lt((mx + 1 : U32), mw)
  +cx = Jenc.encode.ctx(qq)
  +p3 = M2.feed3b(t1, t2, t3, bit)
  +fr = L1.jpg.enc.frame(Jenc.K444{}, ww, hh)
  +sc = L1.jpg.enc.scan(Jenc.K444{})
  (t1 <> t2 <> t3 <> ts, Equal.trans(Jenc.Put, Jenc.encode.mcus(nn, Jenc.encode.step.y(aa, Jenc.encode.bookof(False{}),
    Jenc.encode.bookof(True{}), bit, py, pb, pr, (mx * 8 : U32), (my * 8 : U32), ww, hh, cx), Jenc.encode.nx(mo, mx),
    Jenc.encode.ny(mo, my), mw, ww, hh, cx), Jenc.encode.mcus(nn, (ar, Jenc.encode.bookof(False{}),
    Jenc.encode.bookof(True{}), d1, d2, d3, p3), Jenc.encode.nx(mo, mx), Jenc.encode.ny(mo, my), mw, ww, hh, cx),
    L1.jpg.feed(L1.jpg.tbits(t1 <> t2 <> t3 <> ts), bit), Equal.cong(Array<U32> & Jenc.Book & Jenc.Book & U32 & U32 &
    U32 & Jenc.Put, Jenc.Put, gg => Jenc.encode.mcus(nn, gg, Jenc.encode.nx(mo, mx), Jenc.encode.ny(mo, my), mw, ww,
    hh, cx), Jenc.encode.step.y(aa, Jenc.encode.bookof(False{}), Jenc.encode.bookof(True{}), bit, py, pb, pr, (mx * 8 :
    U32), (my * 8 : U32), ww, hh, cx), (ar, Jenc.encode.bookof(False{}), Jenc.encode.bookof(True{}), d1, d2, d3, p3),
    ee), Equal.trans(Jenc.Put, Jenc.encode.mcus(nn, (ar, Jenc.encode.bookof(False{}), Jenc.encode.bookof(True{}), d1,
    d2, d3, p3), Jenc.encode.nx(mo, mx), Jenc.encode.ny(mo, my), mw, ww, hh, cx), L1.jpg.feed(L1.jpg.tbits(ts), p3),
    L1.jpg.feed(L1.jpg.tbits(t1 <> t2 <> t3 <> ts), bit), er, feed_tri(t1, t2, t3, ts, bit))), Equal.cong(Nat, Nat,
    kk => 1n+(1n+(1n+kk)), List.length(&2, L1.JBlkTok, ts), tri(nn), el), Equal.trans(Bool,
    L1.jpg.also(L1.jpg.blkwf(t1), L1.jpg.also(L1.jpg.blkwf(t2), L1.jpg.also(L1.jpg.blkwf(t3), L1.jpg.allwf(ts)))),
    L1.jpg.also(L1.jpg.blkwf(t2), L1.jpg.also(L1.jpg.blkwf(t3), L1.jpg.allwf(ts))), True{},
    M2.also_t(L1.jpg.blkwf(t1), L1.jpg.also(L1.jpg.blkwf(t2), L1.jpg.also(L1.jpg.blkwf(t3), L1.jpg.allwf(ts))), w1),
    Equal.trans(Bool, L1.jpg.also(L1.jpg.blkwf(t2), L1.jpg.also(L1.jpg.blkwf(t3), L1.jpg.allwf(ts))),
    L1.jpg.also(L1.jpg.blkwf(t3), L1.jpg.allwf(ts)), True{}, M2.also_t(L1.jpg.blkwf(t2),
    L1.jpg.also(L1.jpg.blkwf(t3), L1.jpg.allwf(ts)), w2), Equal.trans(Bool, L1.jpg.also(L1.jpg.blkwf(t3),
    L1.jpg.allwf(ts)), L1.jpg.allwf(ts), True{}, M2.also_t(L1.jpg.blkwf(t3), L1.jpg.allwf(ts), w3), ew))),
    Equal.trans(Bool, L1.jpg.tagok(t1 <> t2 <> t3 <> ts, (0, 0), fr, sc), L1.jpg.tagok(ts, (0, 0), fr, sc), True{},
    tag3(ww, hh, s1, x1, a1, s2, x2, a2, s3, x3, a3, ts), eg))

# the type of mcus_step's parameter mo: the MCU at the loop's place, with the context's quantisation columns
def mcus_step.mo.ty(
  _aa: Array<U32>,
  +_bit: Jenc.Put,
  +_py: U32,
  +_pb: U32,
  +_pr: U32,
  +_mx: U32,
  +_my: U32,
  +_ww: U32,
  +_hh: U32,
  +_qq: U32
) -> Type:
  M2.McuOut(Jenc.encode.tile(_aa, _ww, _hh, (_mx * 8 : U32), (_my * 8 : U32)), _bit, _py, _pb, _pr,
    Jenc.encode.qcols(Jenc.encode.qrows(Jenc.encode.lumq(), _qq)),
    Jenc.encode.qcols(Jenc.encode.qrows(Jenc.encode.chrq(), _qq)))

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
  +qq: U32,
  ih: McusIh(nn, mw, ww, hh, qq),
  mo: mcus_step.mo.ty(aa, bit, py, pb, pr, mx, my, ww, hh, qq)
) -> McusOut(1n+nn, aa, py, pb, pr, bit, mx, my, mw, ww, hh, qq):
  (+s1, +x1, +a1, +s2, +x2, +a2, +s3, +x3, +a3, ar, +d1, +d2, +d3, e, h1, h2, h3, w1, w2, w3) = mo
  +mv = U32.is_lt((mx + 1 : U32), mw)
  mcus_fin(nn, aa, py, pb, pr, bit, mx, my, mw, ww, hh, qq, s1, x1, a1, s2, x2, a2, s3, x3, a3, ar, d1, d2, d3, e, w1,
    w2, w3, ih(ar, d1, d2, d3, M2.feed3b(L1.JBlkTok{False{}, s1, x1, a1}, L1.JBlkTok{True{}, s2, x2, a2},
    L1.JBlkTok{True{}, s3, x3, a3}, bit), Jenc.encode.nx(mv, mx), Jenc.encode.ny(mv, my), h1, h2, h3))

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
  +qq: U32,
  hy: {U32.is_lt(py, 2048) == True{} : Bool},
  hb: {U32.is_lt(pb, 2048) == True{} : Bool},
  hr: {U32.is_lt(pr, 2048) == True{} : Bool}
) -> McusOut(nn, aa, py, pb, pr, bit, mx, my, mw, ww, hh, qq):
  match nn:
    case 0n:
      ([], {==}, {==}, {==}, {==})
    case 1n+ +mm:
      mcus_step(mm, aa, py, pb, pr, bit, mx, my, mw, ww, hh, qq, a2 => q1 => q2 => q3 => p2 => x2 => y2 => h1 => h2 =>
        h3 => mcus_ok(mm, a2, q1, q2, q3, p2, x2, y2, mw, ww, hh, qq, h1, h2, h3), M2.mcu(Jenc.encode.tile(aa, ww, hh,
        (mx * 8 : U32), (my * 8 : U32)), bit, py, pb, pr, Jenc.encode.qcols(Jenc.encode.qrows(Jenc.encode.lumq(), qq)),
        Jenc.encode.qcols(Jenc.encode.qrows(Jenc.encode.chrq(), qq)), hy, hb, hr))

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

# the encoder's MCU count
def mcun(+ww: U32, +hh: U32) -> U32:
  (U32.div((ww + 7 : U32), 8) * U32.div((hh + 7 : U32), 8) : U32)

# blocks' bits, two lists joined
def tbits_app(
  xs: List<&2, L1.JBlkTok>,
  +ys: List<&2, L1.JBlkTok>
) -> {L1.jpg.tbits(List.append(&2, L1.JBlkTok, xs, ys)) == List.append(&2, Bool, L1.jpg.tbits(xs),
  L1.jpg.tbits(ys)) : List<&2, Bool>}:
  match xs:
    case Nil{}:
      {==}
    case +tt <> +rest:
      Equal.trans(List<&2, Bool>, List.append(&2, Bool, L1.jpg.blkbits(tt), L1.jpg.tbits(List.append(&2, L1.JBlkTok,
        rest, ys))), List.append(&2, Bool, L1.jpg.blkbits(tt), List.append(&2, Bool, L1.jpg.tbits(rest),
        L1.jpg.tbits(ys))), List.append(&2, Bool, List.append(&2, Bool, L1.jpg.blkbits(tt), L1.jpg.tbits(rest)),
        L1.jpg.tbits(ys)), Equal.cong(List<&2, Bool>, List<&2, Bool>, zs => List.append(&2, Bool, L1.jpg.blkbits(tt),
        zs), L1.jpg.tbits(List.append(&2, L1.JBlkTok, rest, ys)), List.append(&2, Bool, L1.jpg.tbits(rest),
        L1.jpg.tbits(ys)), tbits_app(rest, ys)), Equal.sym(List<&2, Bool>, List.append(&2, Bool, List.append(&2, Bool,
        L1.jpg.blkbits(tt), L1.jpg.tbits(rest)), L1.jpg.tbits(ys)), List.append(&2, Bool, L1.jpg.blkbits(tt),
        List.append(&2, Bool, L1.jpg.tbits(rest), L1.jpg.tbits(ys))), M2.huf.app_assoc(L1.jpg.blkbits(tt),
        L1.jpg.tbits(rest), L1.jpg.tbits(ys))))

# the blocks per MCU of a layout's frame: three, or one for a gray frame
def kcnt(+kd: Jenc.Layout, +nn: Nat) -> Nat:
  match kd:
    case Jenc.K444{}:
      tri(nn)
    case Jenc.KGray{}:
      nn

# a path's entropy-coded bytes: blocks the decoder reads whole, as many per MCU as the layout's frame has, fed to
# the writer and padded, each of the class the decoder's tables hold at its place in the scan
def PathOut(-bytes: List<&2, U32>, +nn: Nat, +kd: Jenc.Layout, +ww: U32, +hh: U32) -> Type:
  &ts: List<&2, L1.JBlkTok> -> &_e: {bytes == Jenc.encode.pad(L1.jpg.feed(L1.jpg.tbits(ts),
    Jenc.encode.put0())) : List<&2, U32>} -> &_l: {List.length(&2, L1.JBlkTok, ts) == kcnt(kd, nn) : Nat} -> &_w:
    {L1.jpg.allwf(ts) == True{} : Bool} -> {L1.jpg.inorder(ts, L1.jpg.enc.frame(kd, ww, hh), L1.jpg.enc.scan(kd)) ==
    True{} : Bool}

# the type of go_fin's parameter rr
def go_fin.rr.ty(+_ww: U32, +_hh: U32, +_qq: U32, +_px: List<&2, U32>) -> Type:
  McusOut(U32.to_nat(mcun(_ww, _hh)), Jenc.encode.pix.load(U32.to_nat((_ww * _hh : U32)), _px,
    Jpeg.decode.plane((_ww * _hh : U32)), 0), 1024, 1024, 1024, Jenc.encode.put0(), 0, 0, U32.div((_ww + 7 :
    U32), 8), _ww, _hh, _qq)

# the entropy-coded bytes, its MCU loop's blocks named
def go_fin(
  +ww: U32,
  +hh: U32,
  +qq: U32,
  +px: List<&2, U32>,
  rr: go_fin.rr.ty(ww, hh, qq, px)
) -> PathOut(Jenc.encode.arm3(ww, hh, qq, px), U32.to_nat(mcun(ww, hh)), Jenc.K444{}, ww, hh):
  (+ts, er, el, ew, eg) = rr
  (ts, Equal.cong(Jenc.Put, List<&2, U32>, pp => Jenc.encode.pad(pp), Jenc.encode.mcus(U32.to_nat(mcun(ww, hh)),
    (Jenc.encode.pix.load(U32.to_nat((ww * hh : U32)), px, Jpeg.decode.plane((ww * hh : U32)), 0),
    Jenc.encode.bookof(False{}), Jenc.encode.bookof(True{}), 1024, 1024, 1024, Jenc.encode.put0()), 0, 0, U32.div((ww +
    7 : U32), 8), ww, hh, Jenc.encode.ctx(qq)), L1.jpg.feed(L1.jpg.tbits(ts), Jenc.encode.put0()), er), el, ew, eg)

# the three-component entropy-coded bytes are blocks the decoder reads whole, three per MCU, in the order of its
# scan
def arm3_ok(
  +ww: U32,
  +hh: U32,
  +qq: U32,
  +px: List<&2, U32>
) -> PathOut(Jenc.encode.arm3(ww, hh, qq, px), U32.to_nat(mcun(ww, hh)), Jenc.K444{}, ww, hh):
  go_fin(ww, hh, qq, px, mcus_ok(U32.to_nat(mcun(ww, hh)), Jenc.encode.pix.load(U32.to_nat((ww * hh : U32)), px,
    Jpeg.decode.plane((ww * hh : U32)), 0), 1024, 1024, 1024, Jenc.encode.put0(), 0, 0, U32.div((ww + 7 : U32), 8), ww,
    hh, qq, {==}, {==}, {==}))

# the luminance quantisation columns of a quality, as the encoder's context holds them
def qlum(+qq: U32) -> List<&2, Jenc.Oct>:
  Jenc.encode.qcols(Jenc.encode.qrows(Jenc.encode.lumq(), qq))

# a gray MCU the encoder codes: one luminance block the decoder reads whole, fed to the writer, the book back, and
# the next predictor below 2048
def GStepOut(-tt: Jenc.GTile, +bit: Jenc.Put, +py: U32, +qq: U32) -> Type:
  &s1: U32 -> &x1: List<&2, Bool> -> &a1: List<&2, L1.JTok> -> &aa: Array<U32> -> &d1: U32 -> &_e:
    {Jenc.encode.gstep.tile(tt, Jenc.encode.bookof(False{}), bit, py, M2.kern(), Jpeg.decode.zig(), qlum(qq)) == (aa,
    Jenc.encode.bookof(False{}), d1, L1.jpg.feed(L1.jpg.blkbits(L1.JBlkTok{False{}, s1, x1, a1}), bit)) :
    Array<U32> & Jenc.Book & U32 & Jenc.Put} -> &_h: {U32.is_lt(d1, 2048) == True{} : Bool} ->
    {L1.jpg.blkwf(L1.JBlkTok{False{}, s1, x1, a1}) == True{} : Bool}

# a gray MCU, its block's coder named
def gstep_fin(
  pix: Array<U32>,
  -ys: Array<U32>,
  +fy: Bool,
  +bit: Jenc.Put,
  +py: U32,
  +qq: U32,
  co: M2.ChOut(False{}, fy, ys, bit, py, M2.kern(), qlum(qq))
) -> GStepOut(Jenc.GTile{pix, ys, fy}, bit, py, qq):
  (+s1, +x1, +a1, +d1, e1, h1, w1) = co
  (s1, x1, a1, pix, d1, Equal.cong(Jenc.Book & U32 & Jenc.Put, Array<U32> & Jenc.Book & U32 & Jenc.Put, gg =>
    Jenc.encode.gstep.end(gg, pix), Jenc.encode.chan.go(fy, ys, Jenc.encode.bookof(False{}), bit, py, M2.kern(),
    Jpeg.decode.zig(), qlum(qq)), (Jenc.encode.bookof(False{}), d1, L1.jpg.feed(L1.jpg.blkbits(L1.JBlkTok{False{},
    s1, x1, a1}), bit)), e1), h1, w1)

# the encoder's gray MCU, from a predictor below 2048
def gstep_ok(
  tt: Jenc.GTile,
  +bit: Jenc.Put,
  +py: U32,
  +qq: U32,
  hy: {U32.is_lt(py, 2048) == True{} : Bool}
) -> GStepOut(tt, bit, py, qq):
  match tt:
    case Jenc.GTile{pix, ys, +fy}:
      gstep_fin(pix, ys, fy, bit, py, qq, M2.chan_ok(False{}, fy, ys, bit, py, M2.kern(), qlum(qq), hy))

# the encoder's gray MCU loop from a state: its blocks, fed to the writer, one per MCU, each read whole, each a
# luminance block, which the gray frame's tables hold at every place
def GMcusOut(
  nn: Nat,
  -aa: Array<U32>,
  +py: U32,
  +bit: Jenc.Put,
  +mx: U32,
  +my: U32,
  +mw: U32,
  +ww: U32,
  +hh: U32,
  +qq: U32
) -> Type:
  &ts: List<&2, L1.JBlkTok> -> &_e: {Jenc.encode.gmcus(nn, (aa, Jenc.encode.bookof(False{}), py, bit), mx, my, mw,
    ww, hh, Jenc.encode.ctx(qq)) == L1.jpg.feed(L1.jpg.tbits(ts), bit) : Jenc.Put} -> &_l: {List.length(&2,
    L1.JBlkTok, ts) == nn : Nat} -> &_w: {L1.jpg.allwf(ts) == True{} : Bool} -> {L1.jpg.tagok(ts, (0, 0),
    L1.jpg.enc.frame(Jenc.KGray{}, ww, hh), L1.jpg.enc.scan(Jenc.KGray{})) == True{} : Bool}

# the rest of the gray MCU loop, from any state
def GMcusIh(+_nn: Nat, +_mw: U32, +_ww: U32, +_hh: U32, +_qq: U32) -> Type:
  @a2: Array<U32> -> @q1: U32 -> @p2: Jenc.Put -> @x2: U32 -> @y2: U32 -> @h1: {U32.is_lt(q1, 2048) == True{} :
    Bool} -> GMcusOut(_nn, a2, q1, p2, x2, y2, _mw, _ww, _hh, _qq)

# a luminance block, then more, sit at the places of the gray frame from the start exactly when the more do
def gtag1(
  +ww: U32,
  +hh: U32,
  +s1: U32,
  +x1: List<&2, Bool>,
  +a1: List<&2, L1.JTok>,
  +ts: List<&2, L1.JBlkTok>
) -> {L1.jpg.tagok(L1.JBlkTok{False{}, s1, x1, a1} <> ts, (0, 0), L1.jpg.enc.frame(Jenc.KGray{}, ww, hh),
  L1.jpg.enc.scan(Jenc.KGray{})) == L1.jpg.tagok(ts, (0, 0), L1.jpg.enc.frame(Jenc.KGray{}, ww, hh),
  L1.jpg.enc.scan(Jenc.KGray{})) : Bool}:
  {==}

# the type of gmcus_fin's parameter rest
def gmcus_fin.rest.ty(
  +_nn: Nat,
  +_bit: Jenc.Put,
  +_mx: U32,
  +_my: U32,
  +_mw: U32,
  +_ww: U32,
  +_hh: U32,
  +_qq: U32,
  +_s1: U32,
  +_x1: List<&2, Bool>,
  +_a1: List<&2, L1.JTok>,
  _ar: Array<U32>,
  +_d1: U32
) -> Type:
  GMcusOut(_nn, _ar, _d1, L1.jpg.feed(L1.jpg.blkbits(L1.JBlkTok{False{}, _s1, _x1, _a1}), _bit),
    Jenc.encode.nx(U32.is_lt((_mx + 1 : U32), _mw), _mx), Jenc.encode.ny(U32.is_lt((_mx + 1 : U32), _mw), _my), _mw,
    _ww, _hh, _qq)

# the type of gmcus_fin's parameter ee
def gmcus_fin.ee.ty(
  _aa: Array<U32>,
  +_py: U32,
  +_bit: Jenc.Put,
  +_mx: U32,
  +_my: U32,
  +_ww: U32,
  +_hh: U32,
  +_qq: U32,
  +_s1: U32,
  +_x1: List<&2, Bool>,
  +_a1: List<&2, L1.JTok>,
  _ar: Array<U32>,
  +_d1: U32
) -> Type:
  {Jenc.encode.gstep(_aa, Jenc.encode.bookof(False{}), _bit, _py, (_mx * 8 : U32), (_my * 8 : U32), _ww, _hh,
    Jenc.encode.ctx(_qq)) == (_ar, Jenc.encode.bookof(False{}), _d1, L1.jpg.feed(L1.jpg.blkbits(L1.JBlkTok{False{},
    _s1, _x1, _a1}), _bit)) : Array<U32> & Jenc.Book & U32 & Jenc.Put}

# the gray MCU loop after one MCU, its rest named
def gmcus_fin(
  +nn: Nat,
  -aa: Array<U32>,
  +py: U32,
  +bit: Jenc.Put,
  +mx: U32,
  +my: U32,
  +mw: U32,
  +ww: U32,
  +hh: U32,
  +qq: U32,
  +s1: U32,
  +x1: List<&2, Bool>,
  +a1: List<&2, L1.JTok>,
  -ar: Array<U32>,
  +d1: U32,
  ee: gmcus_fin.ee.ty(aa, py, bit, mx, my, ww, hh, qq, s1, x1, a1, ar, d1),
  w1: {L1.jpg.blkwf(L1.JBlkTok{False{}, s1, x1, a1}) == True{} : Bool},
  rest: gmcus_fin.rest.ty(nn, bit, mx, my, mw, ww, hh, qq, s1, x1, a1, ar, d1)
) -> GMcusOut(1n+nn, aa, py, bit, mx, my, mw, ww, hh, qq):
  (+ts, er, el, ew, eg) = rest
  +t1 = {L1.JBlkTok{False{}, s1, x1, a1} : L1.JBlkTok}
  +mo = U32.is_lt((mx + 1 : U32), mw)
  +cx = Jenc.encode.ctx(qq)
  +p1 = L1.jpg.feed(L1.jpg.blkbits(t1), bit)
  (t1 <> ts, Equal.trans(Jenc.Put, Jenc.encode.gmcus(nn, Jenc.encode.gstep(aa, Jenc.encode.bookof(False{}), bit, py,
    (mx * 8 : U32), (my * 8 :
    U32), ww, hh, cx), Jenc.encode.nx(mo, mx), Jenc.encode.ny(mo, my), mw, ww, hh, cx), Jenc.encode.gmcus(nn, (ar,
    Jenc.encode.bookof(False{}), d1, p1), Jenc.encode.nx(mo, mx), Jenc.encode.ny(mo, my), mw, ww, hh, cx),
      L1.jpg.feed(L1.jpg.tbits(t1 <> ts),
    bit), Equal.cong(Array<U32> & Jenc.Book & U32 & Jenc.Put, Jenc.Put, gg => Jenc.encode.gmcus(nn, gg,
    Jenc.encode.nx(mo, mx), Jenc.encode.ny(mo, my), mw, ww, hh, cx), Jenc.encode.gstep(aa,
      Jenc.encode.bookof(False{}), bit, py, (mx * 8 :
    U32), (my * 8 : U32), ww, hh, cx), (ar, Jenc.encode.bookof(False{}), d1, p1), ee), Equal.trans(Jenc.Put,
      Jenc.encode.gmcus(nn, (ar, Jenc.encode.bookof(False{}),
    d1, p1), Jenc.encode.nx(mo, mx), Jenc.encode.ny(mo, my), mw, ww, hh, cx), L1.jpg.feed(L1.jpg.tbits(ts), p1),
    L1.jpg.feed(L1.jpg.tbits(t1 <> ts), bit), er, Equal.sym(Jenc.Put, L1.jpg.feed(L1.jpg.tbits(t1 <> ts), bit),
    L1.jpg.feed(L1.jpg.tbits(ts), p1), M2.feed_app(L1.jpg.blkbits(t1), L1.jpg.tbits(ts), bit)))), Equal.cong(Nat,
    Nat, kk => 1n+kk, List.length(&2, L1.JBlkTok, ts), nn, el), Equal.trans(Bool, L1.jpg.also(L1.jpg.blkwf(t1),
    L1.jpg.allwf(ts)), L1.jpg.allwf(ts), True{}, M2.also_t(L1.jpg.blkwf(t1), L1.jpg.allwf(ts), w1), ew),
    Equal.trans(Bool, L1.jpg.tagok(t1 <> ts, (0, 0), L1.jpg.enc.frame(Jenc.KGray{}, ww, hh),
    L1.jpg.enc.scan(Jenc.KGray{})), L1.jpg.tagok(ts, (0, 0), L1.jpg.enc.frame(Jenc.KGray{}, ww, hh),
    L1.jpg.enc.scan(Jenc.KGray{})), True{}, gtag1(ww, hh, s1, x1, a1, ts), eg))

# the gray MCU loop after one MCU, its MCU named
def gmcus_step(
  +nn: Nat,
  -aa: Array<U32>,
  +py: U32,
  +bit: Jenc.Put,
  +mx: U32,
  +my: U32,
  +mw: U32,
  +ww: U32,
  +hh: U32,
  +qq: U32,
  ih: GMcusIh(nn, mw, ww, hh, qq),
  mo: GStepOut(Jenc.encode.gtile(aa, ww, hh, (mx * 8 : U32), (my * 8 : U32)), bit, py, qq)
) -> GMcusOut(1n+nn, aa, py, bit, mx, my, mw, ww, hh, qq):
  (+s1, +x1, +a1, ar, +d1, e, h1, w1) = mo
  +mv = U32.is_lt((mx + 1 : U32), mw)
  gmcus_fin(nn, aa, py, bit, mx, my, mw, ww, hh, qq, s1, x1, a1, ar, d1, e, w1, ih(ar, d1,
    L1.jpg.feed(L1.jpg.blkbits(L1.JBlkTok{False{}, s1, x1, a1}), bit), Jenc.encode.nx(mv, mx), Jenc.encode.ny(mv,
    my), h1))

# the encoder's gray MCU loop, from a predictor below 2048, codes one block per MCU, each read whole
def gmcus_ok(
  nn: Nat,
  aa: Array<U32>,
  +py: U32,
  +bit: Jenc.Put,
  +mx: U32,
  +my: U32,
  +mw: U32,
  +ww: U32,
  +hh: U32,
  +qq: U32,
  hy: {U32.is_lt(py, 2048) == True{} : Bool}
) -> GMcusOut(nn, aa, py, bit, mx, my, mw, ww, hh, qq):
  match nn:
    case 0n:
      ([], {==}, {==}, {==}, {==})
    case 1n+ +mm:
      gmcus_step(mm, aa, py, bit, mx, my, mw, ww, hh, qq, a2 => q1 => p2 => x2 => y2 => h1 => gmcus_ok(mm, a2, q1,
        p2, x2, y2, mw, ww, hh, qq, h1), gstep_ok(Jenc.encode.gtile(aa, ww, hh, (mx * 8 : U32), (my * 8 : U32)), bit,
        py, qq, hy))

# the type of ggo_fin's parameter rr
def ggo_fin.rr.ty(+_ww: U32, +_hh: U32, +_qq: U32, +_px: List<&2, U32>) -> Type:
  GMcusOut(U32.to_nat(mcun(_ww, _hh)), Jenc.encode.pix.load(U32.to_nat((_ww * _hh : U32)), _px,
    Jpeg.decode.plane((_ww * _hh : U32)), 0), 1024, Jenc.encode.put0(), 0, 0, U32.div((_ww + 7 : U32), 8), _ww, _hh,
    _qq)

# the gray entropy-coded bytes, its MCU loop's blocks named
def ggo_fin(
  +ww: U32,
  +hh: U32,
  +qq: U32,
  +px: List<&2, U32>,
  rr: ggo_fin.rr.ty(ww, hh, qq, px)
) -> PathOut(Jenc.encode.armg(ww, hh, qq, px), U32.to_nat(mcun(ww, hh)), Jenc.KGray{}, ww, hh):
  (+ts, er, el, ew, eg) = rr
  (ts, Equal.cong(Jenc.Put, List<&2, U32>, pp => Jenc.encode.pad(pp), Jenc.encode.gmcus(U32.to_nat(mcun(ww, hh)),
    (Jenc.encode.pix.load(U32.to_nat((ww * hh : U32)), px, Jpeg.decode.plane((ww * hh : U32)), 0),
    Jenc.encode.bookof(False{}), 1024, Jenc.encode.put0()), 0, 0, U32.div((ww + 7 : U32), 8), ww, hh,
    Jenc.encode.ctx(qq)), L1.jpg.feed(L1.jpg.tbits(ts), Jenc.encode.put0()), er), el, ew, eg)

# the gray entropy-coded bytes are luminance blocks the decoder reads whole, one per MCU
def armg_ok(
  +ww: U32,
  +hh: U32,
  +qq: U32,
  +px: List<&2, U32>
) -> PathOut(Jenc.encode.armg(ww, hh, qq, px), U32.to_nat(mcun(ww, hh)), Jenc.KGray{}, ww, hh):
  ggo_fin(ww, hh, qq, px, gmcus_ok(U32.to_nat(mcun(ww, hh)), Jenc.encode.pix.load(U32.to_nat((ww * hh : U32)), px,
    Jpeg.decode.plane((ww * hh : U32)), 0), 1024, Jenc.encode.put0(), 0, 0, U32.div((ww + 7 : U32), 8), ww, hh, qq,
    {==}))

# the encoder's entropy-coded bytes, in either layout, are blocks the decoder reads whole, as many per MCU as the
# layout's frame has, in the order of its scan
def arm_ok(
  +ww: U32,
  +hh: U32,
  +qq: U32,
  +kd: Jenc.Layout,
  +px: List<&2, U32>
) -> PathOut(Jenc.encode.arm(ww, hh, qq, kd, px), U32.to_nat(mcun(ww, hh)), kd, ww, hh):
  match kd:
    case Jenc.K444{}:
      arm3_ok(ww, hh, qq, px)
    case Jenc.KGray{}:
      armg_ok(ww, hh, qq, px)
