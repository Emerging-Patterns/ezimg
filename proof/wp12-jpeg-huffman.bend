# proof/wp12-jpeg-huffman: lemmas for IMG-JPG-3's Huffman round trip: the encoder's bit writer against the
# decoder's bit reader, the Annex K tables the encoder's books hold against the ones the decoder builds, and the
# decoder's scan loop over blocks of well-formed tokens (decode.run returns a picture).
# PROOF.bend imports this file as W12, so the gate checks it.
import Base
import ../LAWS.bend as Laws
import ../src/jpeg.bend as Jpeg
import ../src/jpeg_enc.bend as Jenc
import ./u32.bend as U32L
import ./wp6-raster.bend as R
import ./wp10-jpeg-finish.bend as W10

# a word shifted up one place with bb in the low bit, the top bit dropped
def vstep(xx: U32, bb: Bool) -> U32:
  match xx:
    case U32{ww}:
      match ww:
        case WCon{w0, wt}:
          U32{WCon{bb, Word.shl.put(31n, w0, wt)}}

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

# and with zeros on the right is zeros
def and_zero_r(nn: Nat, ww: Word(nn)) -> {Word.and(nn, ww, Word.zero(nn)) == Word.zero(nn) : Word(nn)}:
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
              Equal.cong(Word(pp), Word.Con<pp>, xx => WCon{False{}, xx}, Word.and(pp, tt, Word.zero(pp)),
                Word.zero(pp), and_zero_r(pp, tt))
            case False{}:
              Equal.cong(Word(pp), Word.Con<pp>, xx => WCon{False{}, xx}, Word.and(pp, tt, Word.zero(pp)),
                Word.zero(pp), and_zero_r(pp, tt))

# the writer's step: shift up, or in the bit
def or_shl_u(xx: U32, bb: Bool) -> {U32.or(U32.shl(xx), Laws.jpg.ubit(bb)) == vstep(xx, bb) : U32}:
  match xx:
    case U32{ww}:
      match ww:
        case WCon{w0, wt}:
          Equal.cong(Word(31n), U32, zz => U32{WCon{bb, zz}}, Word.or(31n, Word.shl.put(31n, w0, wt), Word.zero(31n)),
            Word.shl.put(31n, w0, wt), or_zero_r(31n, Word.shl.put(31n, w0, wt)))

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
def or_u_shl(xx: U32, bb: Bool) -> {U32.or(Laws.jpg.ubit(bb), U32.shl(xx)) == vstep(xx, bb) : U32}:
  match xx:
    case U32{ww}:
      match ww:
        case WCon{w0, wt}:
          or_u_shl.b(bb, Word.shl.put(31n, w0, wt))

# and with 1, by the low bit
def and_one.b(
  w0: Bool,
  +wt: Word(31n)
) -> {U32{WCon{Bool.and(w0, True{}), Word.and(31n, wt, Word.zero(31n))}} == U32{WCon{w0, Word.zero(31n)}} : U32}:
  match w0:
    case True{}:
      Equal.cong(Word(31n), U32, zz => U32{WCon{True{}, zz}}, Word.and(31n, wt, Word.zero(31n)), Word.zero(31n),
        and_zero_r(31n, wt))
    case False{}:
      Equal.cong(Word(31n), U32, zz => U32{WCon{False{}, zz}}, Word.and(31n, wt, Word.zero(31n)), Word.zero(31n),
        and_zero_r(31n, wt))

# and with 1 is the low bit
def and_one(xx: U32) -> {U32.and(xx, 1) == Laws.jpg.ubit(Laws.jpg.bit0(xx)) : U32}:
  match xx:
    case U32{ww}:
      match ww:
        case WCon{w0, wt}:
          and_one.b(w0, wt)

# bits folded into a value, the first bit highest: each shifts the value up and sits in the low bit
def vfold(bs: List<&2, Bool>, acc: U32) -> U32:
  match bs:
    case Nil{}:
      acc
    case bb <> rest:
      vfold(rest, vstep(acc, bb))

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

# the type False names: Unit for False, Empty for True
def false_ty(bb: Bool) -> Type:
  match bb:
    case False{}:
      Unit
    case True{}:
      Empty

# False is never True
def false_true(ee: {False{} == True{} : Bool}) -> Empty:
  %ee : false_ty(_)
  Unit{}

# nothing is below zero
def lt0(xx: Nat) -> {False{} == Nat.is_lt(xx, 0n) : Bool}:
  match xx:
    case 0n:
      {==}
    case 1n+_pp:
      {==}

# eight or more pending bits are not short
def long8(xs: List<&2, Bool>, hh: {Nat.is_lt(List.length(&2, Bool, xs), 0n) == True{} : Bool}) -> Empty:
  false_true(Equal.trans(Bool, False{}, Nat.is_lt(List.length(&2, Bool, xs), 0n), True{},
    lt0(List.length(&2, Bool, xs)), hh))

# the writer's bit step on a model state, by the pending bits
def wbit.p(
  out: List<&2, U32>,
  pp: List<&2, Bool>,
  bb: Bool,
  hh: {short(pp) == True{} : Bool}
) -> {Jenc.encode.bit.n(U32.is_eq(U32.from_nat(List.length(&2, Bool, pp)), 7), out, vstep(vfold(pp, 0), bb),
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
                                    vstep(vfold(p0 <> p1 <> p2 <> p3 <> p4 <> p5 <> p6 <> p7 <> t7, 0), bb),
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
) -> {Jenc.encode.bit(wst(out, pp), Laws.jpg.ubit(bb)) == wone(is7(pp), out, pp, bb) : Jenc.Put}:
  +nn = U32.from_nat(List.length(&2, Bool, pp))
  +vv = vfold(pp, 0)
  Equal.trans(Jenc.Put, Jenc.encode.bit.n(U32.is_eq(nn, 7), out, U32.or(U32.shl(vv), U32.and(Laws.jpg.ubit(bb), 1)),
    nn),
    Jenc.encode.bit.n(U32.is_eq(nn, 7), out, U32.or(U32.shl(vv), Laws.jpg.ubit(bb)), nn), wone(is7(pp), out, pp, bb),
    Equal.cong(U32, Jenc.Put, xx => Jenc.encode.bit.n(U32.is_eq(nn, 7), out, U32.or(U32.shl(vv), xx), nn),
    U32.and(Laws.jpg.ubit(bb), 1), Laws.jpg.ubit(bb), and_one(Laws.jpg.ubit(bb))),
    Equal.trans(Jenc.Put, Jenc.encode.bit.n(U32.is_eq(nn, 7), out, U32.or(U32.shl(vv), Laws.jpg.ubit(bb)), nn),
    Jenc.encode.bit.n(U32.is_eq(nn, 7), out, vstep(vv, bb), nn), wone(is7(pp), out, pp, bb),
    Equal.cong(U32, Jenc.Put, xx => Jenc.encode.bit.n(U32.is_eq(nn, 7), out, xx, nn), U32.or(U32.shl(vv),
      Laws.jpg.ubit(bb)),
    vstep(vv, bb), or_shl_u(vv, bb)), wbit.p(out, pp, bb, hh)))

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
) -> {Jenc.encode.bit(wput(ws), Laws.jpg.ubit(bb)) == wput(wstep(ws, bb)) : Jenc.Put}:
  match ws:
    case WS{+out, +pp}:
      Equal.trans(Jenc.Put, Jenc.encode.bit(wst(obytes(out), pp), Laws.jpg.ubit(bb)), wone(is7(pp), obytes(out), pp,
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
) -> {Laws.jpg.feed(bs, wput(ws)) == wput(wm(bs, ws)) : Jenc.Put}:
  match bs:
    case Nil{}:
      {==}
    case +bb <> rest:
      Equal.trans(Jenc.Put, Laws.jpg.feed(rest, Jenc.encode.bit(wput(ws), Laws.jpg.ubit(bb))), Laws.jpg.feed(rest,
        wput(wstep(ws, bb))),
        wput(wm(rest, wstep(ws, bb))), Equal.cong(Jenc.Put, Jenc.Put, qq => Laws.jpg.feed(rest, qq),
        Jenc.encode.bit(wput(ws), Laws.jpg.ubit(bb)), wput(wstep(ws, bb)), wbit.ws(ws, bb, hh)),
        wfeed(rest, wstep(ws, bb), wstep.short(ws, bb, hh)))

# the encoder's bit loop feeds the code's bits
def bits_go(
  kk: Nat,
  pp: Jenc.Put,
  +code: U32
) -> {Jenc.encode.bits.go(kk, pp, code) == Laws.jpg.feed(Laws.jpg.cb(kk, code), pp) : Jenc.Put}:
  match kk:
    case 0n:
      {==}
    case 1n+ +qq:
      +bt = U32.shrn(code, qq)
      Equal.trans(Jenc.Put, Jenc.encode.bits.go(qq, Jenc.encode.bit(pp, U32.and(bt, 1)), code),
        Jenc.encode.bits.go(qq, Jenc.encode.bit(pp, Laws.jpg.ubit(Laws.jpg.bit0(bt))), code),
          Laws.jpg.feed(Laws.jpg.cb(1n+qq, code), pp),
        Equal.cong(U32, Jenc.Put, xx => Jenc.encode.bits.go(qq, Jenc.encode.bit(pp, xx), code), U32.and(bt, 1),
        Laws.jpg.ubit(Laws.jpg.bit0(bt)), and_one(bt)), bits_go(qq, Jenc.encode.bit(pp,
          Laws.jpg.ubit(Laws.jpg.bit0(bt))), code))

# a code of at most 16 bits, written with its length and value, is its bits fed to the writer
def bits_code(
  +cc: List<&2, Bool>,
  pp: Jenc.Put,
  hh: {Nat.is_le(List.length(&2, Bool, cc), 16n) == True{} : Bool}
) -> {Jenc.encode.bits(pp, U32.from_nat(List.length(&2, Bool, cc)), vfold(cc, 0)) == Laws.jpg.feed(cc, pp) : Jenc.Put}:
  match cc:
    case Nil{}:
      bits_go(0n, pp, vfold([], 0))
    case +h0 <> t0:
      match t0:
        case Nil{}:
          bits_go(1n, pp, vfold(h0 <> [], 0))
        case +h1 <> t1:
          match t1:
            case Nil{}:
              bits_go(2n, pp, vfold(h0 <> h1 <> [], 0))
            case +h2 <> t2:
              match t2:
                case Nil{}:
                  bits_go(3n, pp, vfold(h0 <> h1 <> h2 <> [], 0))
                case +h3 <> t3:
                  match t3:
                    case Nil{}:
                      bits_go(4n, pp, vfold(h0 <> h1 <> h2 <> h3 <> [], 0))
                    case +h4 <> t4:
                      match t4:
                        case Nil{}:
                          bits_go(5n, pp, vfold(h0 <> h1 <> h2 <> h3 <> h4 <> [], 0))
                        case +h5 <> t5:
                          match t5:
                            case Nil{}:
                              bits_go(6n, pp, vfold(h0 <> h1 <> h2 <> h3 <> h4 <> h5 <> [], 0))
                            case +h6 <> t6:
                              match t6:
                                case Nil{}:
                                  bits_go(7n, pp, vfold(h0 <> h1 <> h2 <> h3 <> h4 <> h5 <> h6 <> [], 0))
                                case +h7 <> t7:
                                  match t7:
                                    case Nil{}:
                                      bits_go(8n, pp, vfold(h0 <> h1 <> h2 <> h3 <> h4 <> h5 <> h6 <> h7 <> [], 0))
                                    case +h8 <> t8:
                                      match t8:
                                        case Nil{}:
                                          bits_go(9n, pp,
                                            vfold(h0 <> h1 <> h2 <> h3 <> h4 <> h5 <> h6 <> h7 <> h8 <> [], 0))
                                        case +h9 <> t9:
                                          match t9:
                                            case Nil{}:
                                              bits_go(10n, pp,
                                                vfold(h0 <> h1 <> h2 <> h3 <> h4 <> h5 <> h6 <> h7 <> h8 <> h9 <> [],
                                                0))
                                            case +h10 <> t10:
                                              match t10:
                                                case Nil{}:
                                                  bits_go(11n, pp,
                                                    vfold(h0 <> h1 <> h2 <> h3 <> h4 <> h5 <> h6 <> h7 <> h8 <> h9 <>
                                                    h10 <> [], 0))
                                                case +h11 <> t11:
                                                  match t11:
                                                    case Nil{}:
                                                      bits_go(12n, pp,
                                                        vfold(h0 <> h1 <> h2 <> h3 <> h4 <> h5 <> h6 <> h7 <> h8 <> h9
                                                        <> h10 <> h11 <> [], 0))
                                                    case +h12 <> t12:
                                                      match t12:
                                                        case Nil{}:
                                                          bits_go(13n, pp,
                                                            vfold(h0 <> h1 <> h2 <> h3 <> h4 <> h5 <> h6 <> h7 <> h8 <>
                                                            h9 <> h10 <> h11 <> h12 <> [], 0))
                                                        case +h13 <> t13:
                                                          match t13:
                                                            case Nil{}:
                                                              bits_go(14n, pp,
                                                                vfold(h0 <> h1 <> h2 <> h3 <> h4 <> h5 <> h6 <> h7 <>
                                                                h8 <> h9 <> h10 <> h11 <> h12 <> h13 <> [], 0))
                                                            case +h14 <> t14:
                                                              match t14:
                                                                case Nil{}:
                                                                  bits_go(15n, pp,
                                                                    vfold(h0 <> h1 <> h2 <> h3 <> h4 <> h5 <> h6 <> h7
                                                                    <> h8 <> h9 <> h10 <> h11 <> h12 <> h13 <> h14 <>
                                                                    [], 0))
                                                                case +h15 <> t15:
                                                                  match t15:
                                                                    case Nil{}:
                                                                      bits_go(16n, pp,
                                                                        vfold(h0 <> h1 <> h2 <> h3 <> h4 <> h5 <> h6 <>
                                                                        h7 <> h8 <> h9 <> h10 <> h11 <> h12 <> h13 <>
                                                                        h14 <> h15 <> [], 0))
                                                                    case _h16 <> _t16:
                                                                      Empty.absurd({Jenc.encode.bits(pp,
                                                                        U32.from_nat(List.length(&2, Bool,
                                                                        h0 <> h1 <> h2 <> h3 <> h4 <> h5 <> h6 <> h7 <>
                                                                        h8 <> h9 <> h10 <> h11 <> h12 <> h13 <> h14 <>
                                                                        h15 <> _h16 <> _t16)),
                                                                        vfold(h0 <> h1 <> h2 <> h3 <> h4 <> h5 <> h6 <>
                                                                          h7 <> h8 <> h9 <> h10 <> h11 <> h12 <> h13 <>
                                                                          h14 <> h15 <> _h16 <> _t16,
                                                                          0)) == Laws.jpg.feed(h0 <> h1 <> h2 <> h3 <>
                                                                          h4 <> h5 <> h6 <> h7 <> h8 <> h9 <> h10 <>
                                                                          h11 <> h12 <> h13 <> h14 <> h15 <> _h16 <>
                                                                          _t16, pp) : Jenc.Put}, false_true(hh))

# 1 or 0 is the bit as a U32
def bitu_u(bb: Bool) -> {Laws.jpg.bitu(bb) == Laws.jpg.ubit(bb) : U32}:
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# a code's value is the model's fold of its bits
def num_v(bs: List<&2, Bool>, +acc: U32) -> {Laws.jpg.num(bs, acc) == vfold(bs, acc) : U32}:
  match bs:
    case Nil{}:
      {==}
    case +bb <> rest:
      Equal.trans(U32, Laws.jpg.num(rest, U32.or(U32.shl(acc), Laws.jpg.bitu(bb))), Laws.jpg.num(rest, vstep(acc,
        bb)), vfold(rest, vstep(acc, bb)),
        Equal.cong(U32, U32, xx => Laws.jpg.num(rest, xx), U32.or(U32.shl(acc), Laws.jpg.bitu(bb)), vstep(acc, bb),
        Equal.trans(U32, U32.or(U32.shl(acc), Laws.jpg.bitu(bb)), U32.or(U32.shl(acc), Laws.jpg.ubit(bb)), vstep(acc,
          bb),
        Equal.cong(U32, U32, xx => U32.or(U32.shl(acc), xx), Laws.jpg.bitu(bb), Laws.jpg.ubit(bb), bitu_u(bb)),
          or_shl_u(acc, bb))),
        num_v(rest, vstep(acc, bb)))

# feeding two lists is feeding their join
def feed_app(
  xs: List<&2, Bool>,
  +ys: List<&2, Bool>,
  pp: Jenc.Put
) -> {Laws.jpg.feed(List.append(&2, Bool, xs, ys), pp) == Laws.jpg.feed(ys, Laws.jpg.feed(xs, pp)) : Jenc.Put}:
  match xs:
    case Nil{}:
      {==}
    case bb <> rest:
      feed_app(rest, ys, Jenc.encode.bit(pp, Laws.jpg.ubit(bb)))

# the first answer of a true also
def also_l(ok: Bool, -rest: Bool, hh: {Laws.jpg.also(ok, rest) == True{} : Bool}) -> {ok == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, false_true(hh))

# the second answer of a true also
def also_r(ok: Bool, -rest: Bool, hh: {Laws.jpg.also(ok, rest) == True{} : Bool}) -> {rest == True{} : Bool}:
  match ok:
    case True{}:
      hh
    case False{}:
      Empty.absurd({rest == True{} : Bool}, false_true(hh))

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
      +h1 = {also_l(Nat.is_le(List.length(&2, Bool, cc), 16n), Laws.jpg.codes16(rest), hh) :
        {Nat.is_le(List.length(&2, Bool, cc), 16n) == True{} : Bool}}
      +nn = U32.from_nat(List.length(&2, Bool, cc))
      Equal.trans(Jenc.Put, Laws.jpg.write(rest, Jenc.encode.bits(pp, nn, Laws.jpg.num(cc, 0))), Laws.jpg.write(rest,
        Laws.jpg.feed(cc, pp)),
        Laws.jpg.feed(List.concat(&2, Bool, cc <> rest), pp), Equal.cong(Jenc.Put, Jenc.Put,
          qq => Laws.jpg.write(rest, qq),
        Jenc.encode.bits(pp, nn, Laws.jpg.num(cc, 0)), Laws.jpg.feed(cc, pp), Equal.trans(Jenc.Put,
          Jenc.encode.bits(pp, nn, Laws.jpg.num(cc, 0)),
        Jenc.encode.bits(pp, nn, vfold(cc, 0)), Laws.jpg.feed(cc, pp), Equal.cong(U32, Jenc.Put,
          vv => Jenc.encode.bits(pp, nn,
        vv), Laws.jpg.num(cc, 0), vfold(cc, 0), num_v(cc, 0)), bits_code(cc, pp, h1))),
        Equal.trans(Jenc.Put, Laws.jpg.write(rest, Laws.jpg.feed(cc, pp)), Laws.jpg.feed(List.concat(&2, Bool, rest),
          Laws.jpg.feed(cc, pp)),
        Laws.jpg.feed(List.concat(&2, Bool, cc <> rest), pp), wcodes_feed(rest, Laws.jpg.feed(cc, pp),
          also_r(Nat.is_le(List.length(&2,
        Bool, cc), 16n), Laws.jpg.codes16(rest), hh)), Equal.sym(Jenc.Put, Laws.jpg.feed(List.concat(&2, Bool,
          cc <> rest), pp),
        Laws.jpg.feed(List.concat(&2, Bool, rest), Laws.jpg.feed(cc, pp)), feed_app(cc, List.concat(&2, Bool, rest),
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
      mo.join(is7(pp), pp, bb, moct(rest, mo.next(is7(pp), pp, bb)))

# the encoder's pad of a model writer is the finished bytes, then the last byte's, stuffed
def pad_base(
  +out: List<&2, List<&2, Bool>>,
  pp: List<&2, Bool>,
  hh: {short(pp) == True{} : Bool}
) -> {Jenc.encode.pad(wst(obytes(out), pp)) == Jenc.encode.stuff.all(obytes(out), W10.stf(obytes(pendo(pp)),
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
                                  Empty.absurd({Jenc.encode.pad(wst(obytes(out),
                                    p0 <> p1 <> p2 <> p3 <> p4 <> p5 <> p6 <> p7 <> t7)) ==
                                    Jenc.encode.stuff.all(obytes(out),
                                    W10.stf(obytes(pendo(p0 <> p1 <> p2 <> p3 <> p4 <> p5 <> p6 <> p7 <> t7)),
                                      [])) : List<&2, U32>}, long8(t7, hh))

# after one more bit the pending bits are still fewer than 8
def next_short(
  pp: List<&2, Bool>,
  bb: Bool,
  hh: {short(pp) == True{} : Bool}
) -> {short(mo.next(is7(pp), pp, bb)) == True{} : Bool}:
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
                                  Empty.absurd({short(mo.next(is7(p0 <> p1 <> p2 <> p3 <> p4 <> p5 <> p6 <> p7 <> t7),
                                    p0 <> p1 <> p2 <> p3 <> p4 <> p5 <> p6 <> p7 <> t7, bb)) == True{} : Bool},
                                    long8(t7, hh))

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
) -> {wstep.b(full, out, pp, bb) == WS{wo(full, out, pp, bb), mo.next(full, pp, bb)} : WS}:
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
) -> {Jenc.encode.stuff.all(obytes(wo(full, out, pp, bb)), W10.stf(obytes(rest),
  [])) == Jenc.encode.stuff.all(obytes(out), W10.stf(obytes(mo.join(full, pp, bb, rest)), [])) : List<&2, U32>}:
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
  +hh: {short(pp) == True{} : Bool}
) -> {Jenc.encode.pad(wput(wm(bs, WS{out, pp}))) == Jenc.encode.stuff.all(obytes(out), W10.stf(obytes(moct(bs, pp)),
  [])) : List<&2, U32>}:
  match bs:
    case Nil{}:
      pad_base(out, pp, hh)
    case +bb <> +rest:
      +fl = is7(pp)
      +o2 = wo(fl, out, pp, bb)
      +p2 = mo.next(fl, pp, bb)
      Equal.trans(List<&2, U32>, Jenc.encode.pad(wput(wm(rest, wstep.b(fl, out, pp, bb)))),
        Jenc.encode.pad(wput(wm(rest, WS{o2, p2}))), Jenc.encode.stuff.all(obytes(out), W10.stf(obytes(moct(bb <> rest,
        pp)), [])), Equal.cong(WS, List<&2, U32>, ws => Jenc.encode.pad(wput(wm(rest, ws))), wstep.b(fl, out, pp, bb),
        WS{o2, p2}, wstep.parts(fl, out, pp, bb)),
        Equal.trans(List<&2, U32>, Jenc.encode.pad(wput(wm(rest, WS{o2, p2}))), Jenc.encode.stuff.all(obytes(o2),
        W10.stf(obytes(moct(rest, p2)), [])), Jenc.encode.stuff.all(obytes(out), W10.stf(obytes(moct(bb <> rest, pp)),
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
      eb = Equal.sym(U32, bo, 255, U32L.ueq(bo, 255, ee))
      %eb : {Jpeg.decode.nbits(1n+left, True{}, _ <> (0 <> rest), False{}, Jpeg.decode.head.is(_ <> (0 <> rest), 255),
        Jpeg.decode.head.is(_ <> (0 <> rest), 0), 0, 0, ok, acc) == rfresh(left, _, rest, ok, acc) : Jpeg.Bits & U32}
      {==}

# the reader's model: the bits left in its buffer, and the bytes after them as their bits
type RS is Data:
  RS{qq: List<&2, Bool>, os: List<&2, List<&2, Bool>>}

# the reader's buffer holding bits qq: the first at bit 7, the rest below it, zeros under them
def rbuf(+qq: List<&2, Bool>) -> U32:
  U32.shln(vfold(qq, 0), Nat.sub(8n, List.length(&2, Bool, qq)))

# the stuffed bytes of a model reader
def rxs(os: List<&2, List<&2, Bool>>) -> List<&2, U32>:
  W10.stf(obytes(os), [])

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
  hs: {short(q0 <> t0) == True{} : Bool}
) -> {canon(1n+left, RS{q0 <> t0, os}, ok, acc) == canon(left, rnext(RS{q0 <> t0, os}), ok, vstep(acc,
  rhead(RS{q0 <> t0, os}))) : Jpeg.Bits & U32}:
  match t0:
    case Nil{}:
      Equal.cong(U32, Jpeg.Bits & U32, xx => Jpeg.decode.nbits(left, U32.is_eq(U32.from_nat(List.length(&2, Bool,
        [])), 0), rxs(os), False{}, Jpeg.decode.head.is(rxs(os), 255), Jpeg.decode.head.is(rxs(os), 0),
        U32.from_nat(List.length(&2, Bool, [])), rbuf([]), ok, xx), U32.or(Laws.jpg.ubit(q0), U32.shl(acc)),
        vstep(acc, q0), or_u_shl(acc, q0))
    case +q1 <> t1:
      match t1:
        case Nil{}:
          Equal.cong(U32, Jpeg.Bits & U32, xx => Jpeg.decode.nbits(left, U32.is_eq(U32.from_nat(List.length(&2, Bool,
            q1 <> [])), 0), rxs(os), False{}, Jpeg.decode.head.is(rxs(os), 255), Jpeg.decode.head.is(rxs(os), 0),
            U32.from_nat(List.length(&2, Bool, q1 <> [])), rbuf(q1 <> []), ok, xx), U32.or(Laws.jpg.ubit(q0),
              U32.shl(acc)),
            vstep(acc, q0), or_u_shl(acc, q0))
        case +q2 <> t2:
          match t2:
            case Nil{}:
              Equal.cong(U32, Jpeg.Bits & U32, xx => Jpeg.decode.nbits(left, U32.is_eq(U32.from_nat(List.length(&2,
                Bool,
                q1 <> q2 <> [])), 0), rxs(os), False{}, Jpeg.decode.head.is(rxs(os), 255),
                  Jpeg.decode.head.is(rxs(os), 0),
                U32.from_nat(List.length(&2, Bool, q1 <> q2 <> [])), rbuf(q1 <> q2 <> []), ok, xx),
                  U32.or(Laws.jpg.ubit(q0), U32.shl(acc)),
                vstep(acc, q0), or_u_shl(acc, q0))
            case +q3 <> t3:
              match t3:
                case Nil{}:
                  Equal.cong(U32, Jpeg.Bits & U32, xx => Jpeg.decode.nbits(left,
                    U32.is_eq(U32.from_nat(List.length(&2, Bool,
                    q1 <> q2 <> q3 <> [])), 0), rxs(os), False{}, Jpeg.decode.head.is(rxs(os), 255),
                      Jpeg.decode.head.is(rxs(os), 0),
                    U32.from_nat(List.length(&2, Bool, q1 <> q2 <> q3 <> [])), rbuf(q1 <> q2 <> q3 <> []), ok, xx),
                      U32.or(Laws.jpg.ubit(q0), U32.shl(acc)),
                    vstep(acc, q0), or_u_shl(acc, q0))
                case +q4 <> t4:
                  match t4:
                    case Nil{}:
                      Equal.cong(U32, Jpeg.Bits & U32, xx => Jpeg.decode.nbits(left,
                        U32.is_eq(U32.from_nat(List.length(&2, Bool,
                        q1 <> q2 <> q3 <> q4 <> [])), 0), rxs(os), False{}, Jpeg.decode.head.is(rxs(os), 255),
                          Jpeg.decode.head.is(rxs(os), 0),
                        U32.from_nat(List.length(&2, Bool, q1 <> q2 <> q3 <> q4 <> [])),
                          rbuf(q1 <> q2 <> q3 <> q4 <> []), ok, xx), U32.or(Laws.jpg.ubit(q0), U32.shl(acc)),
                        vstep(acc, q0), or_u_shl(acc, q0))
                    case +q5 <> t5:
                      match t5:
                        case Nil{}:
                          Equal.cong(U32, Jpeg.Bits & U32, xx => Jpeg.decode.nbits(left,
                            U32.is_eq(U32.from_nat(List.length(&2, Bool,
                            q1 <> q2 <> q3 <> q4 <> q5 <> [])), 0), rxs(os), False{}, Jpeg.decode.head.is(rxs(os),
                              255), Jpeg.decode.head.is(rxs(os), 0),
                            U32.from_nat(List.length(&2, Bool, q1 <> q2 <> q3 <> q4 <> q5 <> [])),
                              rbuf(q1 <> q2 <> q3 <> q4 <> q5 <> []), ok, xx), U32.or(Laws.jpg.ubit(q0), U32.shl(acc)),
                            vstep(acc, q0), or_u_shl(acc, q0))
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
                                vstep(acc, q0), or_u_shl(acc, q0))
                            case _q7 <> t7:
                              Empty.absurd({canon(1n+left, RS{q0 <> q1 <> q2 <> q3 <> q4 <> q5 <> q6 <> _q7 <> t7,
                                os}, ok, acc) == canon(left,
                                rnext(RS{q0 <> q1 <> q2 <> q3 <> q4 <> q5 <> q6 <> _q7 <> t7, os}), ok, vstep(acc,
                                rhead(RS{q0 <> q1 <> q2 <> q3 <> q4 <> q5 <> q6 <> _q7 <> t7,
                                os}))) : Jpeg.Bits & U32}, long8(t7, hs))

# one bit read with the buffer empty: the next byte's first bit
def rstep.o(
  +left: Nat,
  oo: List<&2, Bool>,
  +ot: List<&2, List<&2, Bool>>,
  +ok: U32,
  +acc: U32,
  h8: {Nat.is_eq(List.length(&2, Bool, oo), 8n) == True{} : Bool}
) -> {canon(1n+left, RS{[], oo <> ot}, ok, acc) == canon(left, rnext(RS{[], oo <> ot}), ok, vstep(acc, rhead(RS{[],
  oo <> ot}))) : Jpeg.Bits & U32}:
  match oo:
    case Nil{}:
      Empty.absurd({canon(1n+left, RS{[], ([]) <> ot}, ok, acc) == canon(left, rnext(RS{[], ([]) <> ot}), ok,
        vstep(acc, rhead(RS{[], ([]) <> ot}))) : Jpeg.Bits & U32}, false_true(h8))
    case +o0 <> t0:
      match t0:
        case Nil{}:
          Empty.absurd({canon(1n+left, RS{[], (o0 <> []) <> ot}, ok, acc) == canon(left, rnext(RS{[],
            (o0 <> []) <> ot}), ok, vstep(acc, rhead(RS{[], (o0 <> []) <> ot}))) : Jpeg.Bits & U32}, false_true(h8))
        case +o1 <> t1:
          match t1:
            case Nil{}:
              Empty.absurd({canon(1n+left, RS{[], (o0 <> o1 <> []) <> ot}, ok, acc) == canon(left, rnext(RS{[],
                (o0 <> o1 <> []) <> ot}), ok, vstep(acc, rhead(RS{[], (o0 <> o1 <> []) <> ot}))) : Jpeg.Bits & U32},
                false_true(h8))
            case +o2 <> t2:
              match t2:
                case Nil{}:
                  Empty.absurd({canon(1n+left, RS{[], (o0 <> o1 <> o2 <> []) <> ot}, ok, acc) == canon(left,
                    rnext(RS{[], (o0 <> o1 <> o2 <> []) <> ot}), ok, vstep(acc, rhead(RS{[],
                    (o0 <> o1 <> o2 <> []) <> ot}))) : Jpeg.Bits & U32}, false_true(h8))
                case +o3 <> t3:
                  match t3:
                    case Nil{}:
                      Empty.absurd({canon(1n+left, RS{[], (o0 <> o1 <> o2 <> o3 <> []) <> ot}, ok, acc) == canon(left,
                        rnext(RS{[], (o0 <> o1 <> o2 <> o3 <> []) <> ot}), ok, vstep(acc, rhead(RS{[],
                        (o0 <> o1 <> o2 <> o3 <> []) <> ot}))) : Jpeg.Bits & U32}, false_true(h8))
                    case +o4 <> t4:
                      match t4:
                        case Nil{}:
                          Empty.absurd({canon(1n+left, RS{[], (o0 <> o1 <> o2 <> o3 <> o4 <> []) <> ot}, ok,
                            acc) == canon(left, rnext(RS{[], (o0 <> o1 <> o2 <> o3 <> o4 <> []) <> ot}), ok,
                            vstep(acc, rhead(RS{[], (o0 <> o1 <> o2 <> o3 <> o4 <> []) <> ot}))) : Jpeg.Bits & U32},
                            false_true(h8))
                        case +o5 <> t5:
                          match t5:
                            case Nil{}:
                              Empty.absurd({canon(1n+left, RS{[], (o0 <> o1 <> o2 <> o3 <> o4 <> o5 <> []) <> ot}, ok,
                                acc) == canon(left, rnext(RS{[], (o0 <> o1 <> o2 <> o3 <> o4 <> o5 <> []) <> ot}), ok,
                                vstep(acc, rhead(RS{[],
                                (o0 <> o1 <> o2 <> o3 <> o4 <> o5 <> []) <> ot}))) : Jpeg.Bits & U32}, false_true(h8))
                            case +o6 <> t6:
                              match t6:
                                case Nil{}:
                                  Empty.absurd({canon(1n+left, RS{[],
                                    (o0 <> o1 <> o2 <> o3 <> o4 <> o5 <> o6 <> []) <> ot}, ok, acc) == canon(left,
                                    rnext(RS{[], (o0 <> o1 <> o2 <> o3 <> o4 <> o5 <> o6 <> []) <> ot}), ok,
                                    vstep(acc, rhead(RS{[],
                                    (o0 <> o1 <> o2 <> o3 <> o4 <> o5 <> o6 <> []) <> ot}))) : Jpeg.Bits & U32},
                                    false_true(h8))
                                case +o7 <> t7:
                                  match t7:
                                    case Nil{}:
                                      Equal.trans(Jpeg.Bits & U32, canon(1n+left, RS{[],
                                        (o0 <> o1 <> o2 <> o3 <> o4 <> o5 <> o6 <> o7 <> []) <> ot}, ok, acc),
                                        rfresh(left, vfold(o0 <> o1 <> o2 <> o3 <> o4 <> o5 <> o6 <> o7 <> [], 0),
                                        rxs(ot), ok, acc),
                                        canon(left, rnext(RS{[],
                                          (o0 <> o1 <> o2 <> o3 <> o4 <> o5 <> o6 <> o7 <> []) <> ot}), ok, vstep(acc,
                                          rhead(RS{[], (o0 <> o1 <> o2 <> o3 <> o4 <> o5 <> o6 <> o7 <> []) <> ot}))),
                                          rbyte(U32.is_eq(vfold(o0 <> o1 <> o2 <> o3 <> o4 <> o5 <> o6 <> o7 <> [],
                                          0), 255), left, vfold(o0 <> o1 <> o2 <> o3 <> o4 <> o5 <> o6 <> o7 <> [], 0),
                                        rxs(ot), ok, acc, {==}), Equal.cong(U32, Jpeg.Bits & U32,
                                          xx => Jpeg.decode.nbits(left, False{}, rxs(ot),
                                        False{}, Jpeg.decode.head.is(rxs(ot), 255), Jpeg.decode.head.is(rxs(ot), 0),
                                          7, rbuf(o1 <> o2 <> o3 <> o4 <> o5 <> o6 <> o7 <> []), ok, xx),
                                        U32.or(Laws.jpg.ubit(o0), U32.shl(acc)), vstep(acc, o0), or_u_shl(acc, o0)))
                                    case _o8 <> t8:
                                      Empty.absurd({canon(1n+left, RS{[],
                                        (o0 <> o1 <> o2 <> o3 <> o4 <> o5 <> o6 <> o7 <> _o8 <> t8) <> ot}, ok,
                                        acc) == canon(left, rnext(RS{[],
                                        (o0 <> o1 <> o2 <> o3 <> o4 <> o5 <> o6 <> o7 <> _o8 <> t8) <> ot}), ok,
                                        vstep(acc, rhead(RS{[],
                                        (o0 <> o1 <> o2 <> o3 <> o4 <> o5 <> o6 <> o7 <> _o8 <> t8) <> ot}))) :
                                        Jpeg.Bits & U32}, false_true(h8))

# a model reader's buffer holds fewer than 8 bits
def rshort(ss: RS) -> Bool:
  match ss:
    case RS{qq, _os}:
      short(qq)

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
) -> {canon(1n+left, ss, ok, acc) == canon(left, rnext(ss), ok, vstep(acc, rhead(ss))) : Jpeg.Bits & U32}:
  match ss:
    case RS{qq, os}:
      match qq:
        case +q0 <> t0:
          rstep.q(left, q0, t0, os, ok, acc, hs)
        case Nil{}:
          match os:
            case Nil{}:
              Empty.absurd({canon(1n+left, RS{[], []}, ok, acc) == canon(left, rnext(RS{[], []}), ok, vstep(acc,
                rhead(RS{[], []}))) : Jpeg.Bits & U32}, false_true(hn))
            case +oo <> +ot:
              rstep.o(left, oo, ot, ok, acc, also_l(Nat.is_eq(List.length(&2, Bool, oo), 8n), oct8(ot), h8))

# below b after one more is below b
def lt_succ_l(aa: Nat, bb: Nat, hh: {Nat.is_lt(1n+aa, bb) == True{} : Bool}) -> {Nat.is_lt(aa, bb) == True{} : Bool}:
  match aa bb:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, false_true(hh))
    case 0n 1n+_q:
      {==}
    case 1n+_p 0n:
      Empty.absurd({Nat.is_lt(1n+_p, 0n) == True{} : Bool}, false_true(hh))
    case 1n+pp 1n+qq:
      lt_succ_l(pp, qq, hh)

# a number equal to b + 1 less one is below b + 1
def eq_lt_succ(aa: Nat, bb: Nat, hh: {Nat.is_eq(1n+aa, bb) == True{} : Bool}) -> {Nat.is_lt(aa, bb) == True{} : Bool}:
  match aa bb:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, false_true(hh))
    case 0n 1n+_q:
      {==}
    case 1n+_p 0n:
      Empty.absurd({Nat.is_lt(1n+_p, 0n) == True{} : Bool}, false_true(hh))
    case 1n+pp 1n+qq:
      eq_lt_succ(pp, qq, hh)

# m + 1 at most l says l is above 0
def le_pos(mm: Nat, ll: Nat, hh: {Nat.is_le(1n+mm, ll) == True{} : Bool}) -> {Nat.is_lt(0n, ll) == True{} : Bool}:
  match ll:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, false_true(hh))
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
                  eq_lt_succ(List.length(&2, Bool, tt), 8n, also_l(Nat.is_eq(1n+List.length(&2, Bool, tt), 8n),
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
                  also_r(Nat.is_eq(0n, 8n), oct8(ot), h8)
                case _o0 <> +tt:
                  also_r(Nat.is_eq(1n+List.length(&2, Bool, tt), 8n), oct8(ot), h8)

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
                false_true(hn))
            case oo <> +ot:
              match oo:
                case Nil{}:
                  Empty.absurd({rem(RS{[], [] <> ot}) == rhead(RS{[], [] <> ot}) <> rem(rnext(RS{[], [] <> ot})) :
                    List<&2, Bool>}, false_true(also_l(Nat.is_eq(0n, 8n), oct8(ot), h8)))
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
) -> {canon(mm, ss, ok, acc) == (rbits(radv(mm, ss), ok), vfold(List.take(&2, Bool, rem(ss), mm),
  acc)) : Jpeg.Bits & U32}:
  match mm:
    case 0n:
      match ss:
        case RS{+qq, +os}:
          Equal.cong(List<&2, Bool>, Jpeg.Bits & U32, tk => (rbits(RS{qq, os}, ok), vfold(tk, acc)), [],
            List.take(&2, Bool, rem(RS{qq, os}), 0n), Equal.sym(List<&2, Bool>, List.take(&2, Bool, rem(RS{qq, os}),
            0n), [], take0(rem(RS{qq, os}))))
    case 1n+ +pp:
      +hn = {le_pos(pp, List.length(&2, Bool, rem(ss)), hl) : {rsome(ss) == True{} : Bool}}
      +nx = rnext(ss)
      +er = {rem_cons(ss, h8, hn) : {rem(ss) == rhead(ss) <> rem(nx) : List<&2, Bool>}}
      +h2 = {Equal.cong(List<&2, Bool>, Bool, xs => Nat.is_le(1n+pp, List.length(&2, Bool, xs)), rem(ss),
        rhead(ss) <> rem(nx), er) : {Nat.is_le(1n+pp, List.length(&2, Bool, rem(ss))) == Nat.is_le(pp,
        List.length(&2, Bool, rem(nx))) : Bool}}
      Equal.trans(Jpeg.Bits & U32, canon(1n+pp, ss, ok, acc), canon(pp, nx, ok, vstep(acc, rhead(ss))),
        (rbits(radv(1n+pp, ss), ok), vfold(List.take(&2, Bool, rem(ss), 1n+pp), acc)),
        rstep(pp, ss, ok, acc, hs, h8, hn),
        Equal.trans(Jpeg.Bits & U32, canon(pp, nx, ok, vstep(acc, rhead(ss))), (rbits(radv(pp, nx), ok),
        vfold(List.take(&2, Bool, rem(nx), pp), vstep(acc, rhead(ss)))), (rbits(radv(1n+pp, ss), ok),
        vfold(List.take(&2, Bool, rem(ss), 1n+pp), acc)),
        rread(pp, nx, ok, vstep(acc, rhead(ss)), rnext_short(ss, hs, h8), rnext_oct8(ss, h8),
        Equal.trans(Bool, Nat.is_le(pp, List.length(&2, Bool, rem(nx))), Nat.is_le(1n+pp, List.length(&2, Bool,
        rem(ss))), True{}, Equal.sym(Bool, Nat.is_le(1n+pp, List.length(&2, Bool, rem(ss))), Nat.is_le(pp,
        List.length(&2, Bool, rem(nx))), h2), hl)),
        Equal.cong(List<&2, Bool>, Jpeg.Bits & U32, xs => (rbits(radv(pp, nx), ok), vfold(List.take(&2, Bool, xs,
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
                                                                        : Nat}, false_true(hh))

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

# joining is associative
def app_assoc(
  xs: List<&2, Bool>,
  +ys: List<&2, Bool>,
  +zs: List<&2, Bool>
) -> {List.append(&2, Bool, List.append(&2, Bool, xs, ys), zs) == List.append(&2, Bool, xs, List.append(&2, Bool, ys,
  zs)) : List<&2, Bool>}:
  match xs:
    case Nil{}:
      {==}
    case +hh <> tt:
      Equal.cong(List<&2, Bool>, List<&2, Bool>, ws => hh <> ws, List.append(&2, Bool, List.append(&2, Bool, tt, ys),
        zs), List.append(&2, Bool, tt, List.append(&2, Bool, ys, zs)), app_assoc(tt, ys, zs))

# the left of a true and
def and_l(aa: Bool, -bb: Bool, hh: {Bool.and(aa, bb) == True{} : Bool}) -> {aa == True{} : Bool}:
  match aa:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, false_true(hh))

# the right of a true and
def and_r(aa: Bool, -bb: Bool, hh: {Bool.and(aa, bb) == True{} : Bool}) -> {bb == True{} : Bool}:
  match aa:
    case True{}:
      hh
    case False{}:
      Empty.absurd({bb == True{} : Bool}, false_true(hh))

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
      +h16 = {also_l(Nat.is_le(ln, 16n), Laws.jpg.codes16(rest), hc) : {Nat.is_le(ln, 16n) == True{} : Bool}}
      +ea = {Equal.trans(List<&2, Bool>, rem(ss), List.append(&2, Bool, List.concat(&2, Bool, cc <> rest), tl),
        List.append(&2, Bool, cc, mr), he, app_assoc(cc, List.concat(&2, Bool, rest), tl)) :
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
      +vr = {Equal.trans(U32, vfold(List.take(&2, Bool, rem(ss), ln), 0), vfold(List.take(&2, Bool, List.append(&2,
        Bool, cc, mr), ln), 0), Laws.jpg.num(cc, 0), Equal.cong(List<&2, Bool>, U32, xs => vfold(List.take(&2, Bool,
          xs, ln), 0),
        rem(ss), List.append(&2, Bool, cc, mr), ea), Equal.trans(U32, vfold(List.take(&2, Bool, List.append(&2, Bool,
        cc, mr), ln), 0), vfold(cc, 0), Laws.jpg.num(cc, 0), Equal.cong(List<&2, Bool>, U32, xs => vfold(xs, 0),
        List.take(&2, Bool, List.append(&2, Bool, cc, mr), ln), cc, take_app(cc, mr)), Equal.sym(U32, Laws.jpg.num(cc,
          0),
        vfold(cc, 0), num_v(cc, 0)))) : {vfold(List.take(&2, Bool, rem(ss), ln), 0) == Laws.jpg.num(cc, 0) : U32}}
      +er = {Equal.trans(Jpeg.Bits & U32, Jpeg.decode.read.n(nn, rbits(ss, ok)), canon(U32.to_nat(nn), ss, ok, 0),
        (rbits(s2, ok), Laws.jpg.num(cc, 0)), read_canon(nn, ss, ok), Equal.trans(Jpeg.Bits & U32,
          canon(U32.to_nat(nn), ss,
        ok, 0), canon(ln, ss, ok, 0), (rbits(s2, ok), Laws.jpg.num(cc, 0)), Equal.cong(Nat, Jpeg.Bits & U32,
          kk => canon(kk, ss,
        ok, 0), U32.to_nat(nn), ln, tn16(ln, h16)), Equal.trans(Jpeg.Bits & U32, canon(ln, ss, ok, 0), (rbits(s2, ok),
        vfold(List.take(&2, Bool, rem(ss), ln), 0)), (rbits(s2, ok), Laws.jpg.num(cc, 0)), rread(ln, ss, ok, 0, hs,
          h8, hl),
        Equal.cong(U32, Jpeg.Bits & U32, vv => (rbits(s2, ok), vv), vfold(List.take(&2, Bool, rem(ss), ln), 0),
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
        (Laws.jpg.nums(rest), ok), reads_m(rest, s2, ok, tl, and_l(rshort(s2), roct8(s2), ok2), and_r(rshort(s2),
          roct8(s2),
        ok2), also_r(Nat.is_le(ln, 16n), Laws.jpg.codes16(rest), hc), e2)))

# a list joined with nothing is the list
def app_nil(xs: List<&2, Bool>) -> {List.append(&2, Bool, xs, []) == xs : List<&2, Bool>}:
  match xs:
    case Nil{}:
      {==}
    case +hh <> tt:
      Equal.cong(List<&2, Bool>, List<&2, Bool>, ws => hh <> ws, List.append(&2, Bool, tt, []), tt, app_nil(tt))

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
      mpad(rest, mo.next(is7(pp), pp, bb))

# the last byte's bits are the pending bits and the pad
def pendo_concat(
  +pp: List<&2, Bool>
) -> {List.concat(&2, Bool, pendo(pp)) == List.append(&2, Bool, pp, padbits(pp)) : List<&2, Bool>}:
  match pp:
    case Nil{}:
      {==}
    case +hh <> +tt:
      app_nil(List.append(&2, Bool, hh <> tt, List.replicate(Bool, Nat.sub(8n, List.length(&2, Bool, hh <> tt)),
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
        List.concat(&2, Bool, mm), xs, hm), app_assoc(pp, [bb], xs))
    case False{}:
      Equal.trans(List<&2, Bool>, List.concat(&2, Bool, mm), List.append(&2, Bool, List.append(&2, Bool, pp, [bb]), xs),
        List.append(&2, Bool, pp, bb <> xs), hm, app_assoc(pp, [bb], xs))

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
      +fl = is7(pp)
      +p2 = mo.next(fl, pp, bb)
      join_concat(fl, pp, bb, moct(rest, p2), List.append(&2, Bool, rest, mpad(rest, p2)), concat_moct(rest, p2))

# a byte one more bit finishes has 8 bits
def join_oct8(
  pp: List<&2, Bool>,
  bb: Bool,
  mm: List<&2, List<&2, Bool>>,
  hs: {short(pp) == True{} : Bool},
  hm: {oct8(mm) == True{} : Bool}
) -> {oct8(mo.join(is7(pp), pp, bb, mm)) == True{} : Bool}:
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
                                  Empty.absurd({oct8(mo.join(is7(p0 <> p1 <> p2 <> p3 <> p4 <> p5 <> p6 <> p7 <> t7),
                                    p0 <> p1 <> p2 <> p3 <> p4 <> p5 <> p6 <> p7 <> t7, bb, mm)) == True{} : Bool},
                                    long8(t7, hs))

# the last byte has 8 bits
def pendo_oct8(pp: List<&2, Bool>, hs: {short(pp) == True{} : Bool}) -> {oct8(pendo(pp)) == True{} : Bool}:
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
                                    True{} : Bool}, long8(t7, hs))

# every byte of the model has 8 bits
def oct8_moct(
  bs: List<&2, Bool>,
  +pp: List<&2, Bool>,
  +hs: {short(pp) == True{} : Bool}
) -> {oct8(moct(bs, pp)) == True{} : Bool}:
  match bs:
    case Nil{}:
      pendo_oct8(pp, hs)
    case +bb <> +rest:
      +fl = is7(pp)
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
    Equal.trans(List<&2, U32>, Jenc.encode.pad(Laws.jpg.feed(bs, wput(WS{[], []}))), Jenc.encode.pad(wput(wm(bs,
      WS{[], []}))),
    rxs(os), Equal.cong(Jenc.Put, List<&2, U32>, qq => Jenc.encode.pad(qq), Laws.jpg.feed(bs, wput(WS{[], []})),
    wput(wm(bs, WS{[], []})), wfeed(bs, WS{[], []}, {==})), pad_m(bs, [], [], {==}))) :
    {Jenc.encode.pad(Laws.jpg.write(cs, Jenc.encode.put0())) == rxs(os) : List<&2, U32>}}
  Equal.trans(List<&2, U32> & U32, Laws.jpg.reads(cs, Jpeg.Bits{0, 1, 0, Jenc.encode.pad(Laws.jpg.write(cs,
    Jenc.encode.put0()))}),
    Laws.jpg.reads(cs, rbits(RS{[], os}, 1)), (Laws.jpg.nums(cs), 1), Equal.cong(List<&2, U32>, List<&2, U32> & U32,
      xs => Laws.jpg.reads(cs,
    Jpeg.Bits{0, 1, 0, xs}), Jenc.encode.pad(Laws.jpg.write(cs, Jenc.encode.put0())), rxs(os), ep),
    reads_m(cs, RS{[], os}, 1, mpad(bs, []), {==}, oct8_moct(bs, [], {==}), hc, concat_moct(bs, [])))

# a Huffman walk over bits: the symbol found and the bits it took, or none
type HW is Data:
  HWHit{sym: U32, used: Nat}
  HWMiss{}

# the table's answer for one more code bit, before the walk over the bits after it
def hw.pick(look: Maybe<&2, U32>, rest: HW) -> HW:
  match look:
    case Some{+ss}:
      match rest:
        case _r:
          HWHit{ss, 1n}
    case None{}:
      match rest:
        case HWHit{+ss, +nn}:
          HWHit{ss, 1n+nn}
        case HWMiss{}:
          HWMiss{}

# the decoder's Huffman lookup over a list of bits, code and len so far: each bit extends the code, the
# table asked at each length
def hw(bs: List<&2, Bool>, +tab: Jpeg.Huff, +code: U32, +len: U32) -> HW:
  match bs:
    case Nil{}:
      HWMiss{}
    case +bb <> rest:
      match tab:
        case Jpeg.Huff{+cs, +ls, +ys}:
          hw.pick(Jpeg.decode.look(cs, ls, ys, vstep(code, bb), (len + 1 : U32)), hw(rest, Jpeg.Huff{cs, ls, ys},
            vstep(code, bb), (len + 1 : U32)))

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
) -> {Jpeg.decode.ask.bit(Jpeg.Huff{cs, ls, ys}, (bits, vstep(0, bb)), code, len) == Jpeg.Ask{Jpeg.decode.look(cs, ls,
  ys, vstep(code, bb), (len + 1 : U32)), vstep(code, bb), (len + 1 : U32), bits} : Jpeg.Ask}:
  Equal.cong(U32, Jpeg.Ask, xx => Jpeg.Ask{Jpeg.decode.look(cs, ls, ys, xx, (len + 1 : U32)), xx, (len + 1 : U32),
    bits}, U32.or(U32.shl(code), Laws.jpg.ubit(bb)), vstep(code, bb), or_shl_u(code, bb))

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
  vstep(code, rhead(ss)), (len + 1 : U32)), vstep(code, rhead(ss)), (len + 1 : U32), rbits(rnext(ss), ok)} : Jpeg.Ask}:
  +hh = {Jpeg.Huff{cs, ls, ys} : Jpeg.Huff}
  +nx = rnext(ss)
  +bb = rhead(ss)
  Equal.trans(Jpeg.Ask, Jpeg.decode.ask.bit(hh, Jpeg.decode.one(rbits(ss, ok)), code, len),
    Jpeg.decode.ask.bit(hh, (rbits(nx, ok), vstep(0, bb)), code, len), Jpeg.Ask{Jpeg.decode.look(cs, ls, ys,
    vstep(code, bb), (len + 1 : U32)), vstep(code, bb), (len + 1 : U32), rbits(nx, ok)},
    Equal.cong(Jpeg.Bits & U32, Jpeg.Ask, gg => Jpeg.decode.ask.bit(hh, gg, code, len), Jpeg.decode.one(rbits(ss,
    ok)), (rbits(nx, ok), vstep(0, bb)), Equal.trans(Jpeg.Bits & U32, Jpeg.decode.one(rbits(ss, ok)),
    canon(1n, ss, ok, 0), (rbits(nx, ok), vstep(0, bb)), one_canon(ss, ok), Equal.trans(Jpeg.Bits & U32,
    canon(1n, ss, ok, 0), canon(0n, nx, ok, vstep(0, bb)), (rbits(nx, ok), vstep(0, bb)),
    rstep(0n, ss, ok, 0, hs, h8, hn), canon0(nx, ok, vstep(0, bb))))),
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
def hwres(rr: HW, ss: RS, +ok: U32) -> Jpeg.Hit:
  match rr:
    case HWHit{+sym, +nn}:
      Jpeg.Hit{sym, rbits(radv(nn, ss), ok), ok}
    case HWMiss{}:
      Jpeg.Hit{0, rbits(ss, ok), 0}

# a walk that hits within left asks
def hw.fits(rr: HW, +left: Nat) -> Bool:
  match rr:
    case HWHit{_s, +nn}:
      Nat.is_le(nn, left)
    case HWMiss{}:
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
def pick_pos(look: Maybe<&2, U32>, rest: HW, hf: {hw.fits(hw.pick(look, rest), 0n) == True{} : Bool}) -> Empty:
  match look:
    case Some{_s}:
      false_true(hf)
    case None{}:
      match rest:
        case HWHit{_s, _n}:
          false_true(hf)
        case HWMiss{}:
          false_true(hf)

# the walk over the bits after the first, as the lookup after one bit needs it
def HwIh(-rest: HW, +_lf: Nat, -s0: RS, +_ok: U32, +_cd: U32, +_ln: U32, -tab: Jpeg.Huff) -> Type:
  @hr: {hw.fits(rest, _lf) == True{} : Bool} -> {Jpeg.decode.huff(_lf, Jpeg.Ask{None{}, _cd, _ln,
    rbits(rnext(s0), _ok)}, tab) == hwres(rest, rnext(s0), _ok) : Jpeg.Hit}

# the decoder's lookup after one bit, by the table's answer at that length
def hw.case(
  look: Maybe<&2, U32>,
  rest: HW,
  left: Nat,
  +s0: RS,
  +ok: U32,
  +code: U32,
  +len: U32,
  +tab: Jpeg.Huff,
  hf: {hw.fits(hw.pick(look, rest), 1n+left) == True{} : Bool},
  ih: HwIh(rest, left, s0, ok, code, len, tab)
) -> {Jpeg.decode.huff(left, Jpeg.Ask{look, code, len, rbits(rnext(s0), ok)}, tab) == hwres(hw.pick(look, rest), s0,
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
        case HWHit{+s2, +nn}:
          ih(hf)
        case HWMiss{}:
          Empty.absurd({Jpeg.decode.huff(left, Jpeg.Ask{None{}, code, len, rbits(rnext(s0), ok)}, tab) ==
            hwres(HWMiss{}, s0, ok) : Jpeg.Hit}, false_true(hf))

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
  hf: {hw.fits(hw(bs, Jpeg.Huff{cs, ls, ys}, code, len), left) == True{} : Bool}
) -> {Jpeg.decode.huff(left, Jpeg.Ask{None{}, code, len, rbits(ss, ok)}, Jpeg.Huff{cs, ls, ys}) == hwres(hw(bs,
  Jpeg.Huff{cs, ls, ys}, code, len), ss, ok) : Jpeg.Hit}:
  match bs:
    case Nil{}:
      Empty.absurd({Jpeg.decode.huff(left, Jpeg.Ask{None{}, code, len, rbits(ss, ok)}, Jpeg.Huff{cs, ls, ys}) ==
        hwres(HWMiss{}, ss, ok) : Jpeg.Hit}, false_true(hf))
    case +bb <> +rest:
      match left:
        case 0n:
          +tab = {Jpeg.Huff{cs, ls, ys} : Jpeg.Huff}
          +c2 = vstep(code, bb)
          +l2 = (len + 1 : U32)
          Empty.absurd({Jpeg.decode.huff(0n, Jpeg.Ask{None{}, code, len, rbits(ss, ok)}, tab) ==
            hwres(hw(bb <> rest, tab, code, len), ss, ok) : Jpeg.Hit}, pick_pos(Jpeg.decode.look(cs, ls, ys, c2, l2),
            hw(rest, tab, c2, l2), hf))
        case 1n+ +pp:
          +tab = {Jpeg.Huff{cs, ls, ys} : Jpeg.Huff}
          +c2 = vstep(code, bb)
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
            Jpeg.decode.huff(pp, Jpeg.Ask{lk, c2, l2, rbits(nx, ok)}, tab), hwres(hw(bb <> rest, tab, code, len), ss,
            ok), Equal.cong(Jpeg.Ask, Jpeg.Hit, aa => Jpeg.decode.huff(pp, aa, tab), Jpeg.decode.ask(rbits(ss, ok),
            code, len, tab), Jpeg.Ask{lk, c2, l2, rbits(nx, ok)}, Equal.trans(Jpeg.Ask, Jpeg.decode.ask(rbits(ss,
            ok), code, len, tab), Jpeg.Ask{Jpeg.decode.look(cs, ls, ys, vstep(code, rhead(ss)), l2),
            vstep(code, rhead(ss)), l2, rbits(nx, ok)}, Jpeg.Ask{lk, c2, l2, rbits(nx, ok)},
            ask_step(ss, ok, code, len, cs, ls, ys, hs, h8, hn), Equal.cong(Bool, Jpeg.Ask, xb =>
            Jpeg.Ask{Jpeg.decode.look(cs, ls, ys, vstep(code, xb), l2), vstep(code, xb), l2, rbits(nx, ok)},
            rhead(ss), bb, eh))),
            hw.case(lk, hw(rest, tab, c2, l2), pp, ss, ok, c2, l2, tab, hf, hr => hwalk(rest, pp, nx, ok, c2, l2, cs,
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
                orelse(Jpeg.decode.look(c2, l2, s2, code, len), None{}) : Maybe<&2, U32>}, false_true(hh))
        case _l <> _lt:
          Empty.absurd({Jpeg.decode.look(c2, List.append(&2, U32, _l <> _lt, l2), List.append(&2, U32, s1, s2), code,
            len) == orelse(Jpeg.decode.look(c2, l2, s2, code, len), Jpeg.decode.look([], _l <> _lt, s1, code, len)) :
            Maybe<&2, U32>}, false_true(hh))
    case +cc <> +ct:
      match l1:
        case Nil{}:
          Empty.absurd({Jpeg.decode.look(cc <> List.append(&2, U32, ct, c2), l2, List.append(&2, U32, s1, s2), code,
            len) == orelse(Jpeg.decode.look(c2, l2, s2, code, len), Jpeg.decode.look(cc <> ct, [], s1, code, len)) :
            Maybe<&2, U32>}, false_true(hh))
        case +ll <> +lt:
          match s1:
            case Nil{}:
              Empty.absurd({Jpeg.decode.look(cc <> List.append(&2, U32, ct, c2), ll <> List.append(&2, U32, lt, l2),
                s2, code, len) == orelse(Jpeg.decode.look(c2, l2, s2, code, len), Jpeg.decode.look(cc <> ct, ll <> lt,
                [], code, len)) : Maybe<&2, U32>}, false_true(hh))
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

# one group of a table: a length, and its codes and symbols in order
type HG is Data:
  HG{len: U32, cs: List<&2, U32>, ys: List<&2, U32>}

# the groups' codes
def gc(gs: List<&2, HG>) -> List<&2, U32>:
  match gs:
    case Nil{}:
      []
    case HG{_l, cs, _y} <> rest:
      List.append(&2, U32, cs, gc(rest))

# the groups' lengths, one per code
def gl(gs: List<&2, HG>) -> List<&2, U32>:
  match gs:
    case Nil{}:
      []
    case HG{+ln, cs, _y} <> rest:
      List.append(&2, U32, List.replicate(U32, List.length(&2, U32, cs), ln), gl(rest))

# the groups' symbols
def gsy(gs: List<&2, HG>) -> List<&2, U32>:
  match gs:
    case Nil{}:
      []
    case HG{_l, _c, ys} <> rest:
      List.append(&2, U32, ys, gsy(rest))

# every group has as many symbols as codes
def wfg(gs: List<&2, HG>) -> Bool:
  match gs:
    case Nil{}:
      True{}
    case HG{+ln, +cs, ys} <> rest:
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
def lookg(gs: List<&2, HG>, +code: U32, +len: U32) -> Maybe<&2, U32>:
  match gs:
    case Nil{}:
      None{}
    case HG{+ln, cs, ys} <> rest:
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
  gs: List<&2, HG>,
  +code: U32,
  +len: U32,
  +hh: {wfg(gs) == True{} : Bool}
) -> {Jpeg.decode.look(gc(gs), gl(gs), gsy(gs), code, len) == lookg(gs, code, len) : Maybe<&2, U32>}:
  match gs:
    case Nil{}:
      {==}
    case HG{+ln, +cs, +ys} <> +rest:
      +rp = List.replicate(U32, List.length(&2, U32, cs), ln)
      Equal.trans(Maybe<&2, U32>, Jpeg.decode.look(List.append(&2, U32, cs, gc(rest)), List.append(&2, U32, rp,
        gl(rest)),
        List.append(&2, U32, ys, gsy(rest)), code, len), orelse(Jpeg.decode.look(gc(rest), gl(rest), gsy(rest), code,
          len),
        Jpeg.decode.look(cs, rp, ys, code, len)), lookg(HG{ln, cs, ys} <> rest, code, len),
        look_app(cs, rp, ys, gc(rest), gl(rest), gsy(rest), code, len, also_l(sm3(cs, rp, ys), wfg(rest), hh)),
        Equal.trans(Maybe<&2, U32>, orelse(Jpeg.decode.look(gc(rest), gl(rest), gsy(rest), code, len),
        Jpeg.decode.look(cs, rp, ys, code, len)), orelse(lookg(rest, code, len), Jpeg.decode.look(cs, rp, ys, code,
          len)),
        lookg(HG{ln, cs, ys} <> rest, code, len), Equal.cong(Maybe<&2, U32>, Maybe<&2, U32>, mm => orelse(mm,
        Jpeg.decode.look(cs, rp, ys, code, len)), Jpeg.decode.look(gc(rest), gl(rest), gsy(rest), code, len),
        lookg(rest, code, len), look_g(rest, code, len, also_r(sm3(cs, rp, ys), wfg(rest), hh))),
        Equal.cong(Maybe<&2, U32>, Maybe<&2, U32>, mm => orelse(lookg(rest, code, len), mm), Jpeg.decode.look(cs, rp,
        ys, code, len), lookgrp(U32.is_eq(ln, len), ln, cs, ys, code, len), lookgrp_eq(U32.is_eq(ln, len), ln, cs, ys,
        code, len, {==}))))

# the walk with the lookup over groups
def hwg(bs: List<&2, Bool>, +gs: List<&2, HG>, +code: U32, +len: U32) -> HW:
  match bs:
    case Nil{}:
      HWMiss{}
    case +bb <> rest:
      hw.pick(lookg(gs, vstep(code, bb), (len + 1 : U32)), hwg(rest, gs, vstep(code, bb), (len + 1 : U32)))

# the walk over a table in groups is the walk with the lookup over groups
def hw_g(
  bs: List<&2, Bool>,
  +gs: List<&2, HG>,
  +code: U32,
  +len: U32,
  +hh: {wfg(gs) == True{} : Bool}
) -> {hw(bs, Jpeg.Huff{gc(gs), gl(gs), gsy(gs)}, code, len) == hwg(bs, gs, code, len) : HW}:
  match bs:
    case Nil{}:
      {==}
    case +bb <> rest:
      +c2 = vstep(code, bb)
      +l2 = (len + 1 : U32)
      Equal.trans(HW, hw.pick(Jpeg.decode.look(gc(gs), gl(gs), gsy(gs), c2, l2), hw(rest, Jpeg.Huff{gc(gs), gl(gs),
        gsy(gs)}, c2, l2)), hw.pick(lookg(gs, c2, l2), hw(rest, Jpeg.Huff{gc(gs), gl(gs), gsy(gs)}, c2, l2)),
        hwg(bb <> rest, gs, code, len), Equal.cong(Maybe<&2, U32>, HW, mm => hw.pick(mm, hw(rest, Jpeg.Huff{gc(gs),
        gl(gs), gsy(gs)}, c2, l2)), Jpeg.decode.look(gc(gs), gl(gs), gsy(gs), c2, l2), lookg(gs, c2, l2), look_g(gs,
        c2, l2, hh)), Equal.cong(HW, HW, rr => hw.pick(lookg(gs, c2, l2), rr), hw(rest, Jpeg.Huff{gc(gs), gl(gs),
        gsy(gs)}, c2, l2), hwg(rest, gs, c2, l2), hw_g(rest, gs, c2, l2, hh)))

# a walk that hit symbol ss after nn bits
def hw.is(rr: HW, +ss: U32, +nn: Nat) -> Bool:
  match rr:
    case HWHit{+tt, +jj}:
      Bool.and(U32.is_eq(tt, ss), Nat.is_eq(jj, nn))
    case HWMiss{}:
      False{}

# a symbol's code, at most 16 bits, walked over the table in groups, hits the symbol at its last bit
def hwchk(+cc: List<&2, Bool>, +gs: List<&2, HG>, +ss: U32) -> Bool:
  Bool.and(Nat.is_le(List.length(&2, Bool, cc), 16n), hw.is(hwg(cc, gs, 0, 0), ss, List.length(&2, Bool, cc)))

# a walk known to hit symbol ss after nn bits
def hwis(rr: HW, +ss: U32, +nn: Nat, +hh: {hw.is(rr, ss, nn) == True{} : Bool}) -> {rr == HWHit{ss, nn} : HW}:
  match rr:
    case HWHit{+tt, +jj}:
      +et = {U32L.ueq(tt, ss, and_l(U32.is_eq(tt, ss), Nat.is_eq(jj, nn), hh)) : {tt == ss : U32}}
      +ej = {R.nat_eq_true(jj, nn, and_r(U32.is_eq(tt, ss), Nat.is_eq(jj, nn), hh)) : {jj == nn : Nat}}
      Equal.trans(HW, HWHit{tt, jj}, HWHit{ss, jj}, HWHit{ss, nn}, Equal.cong(U32, HW, xx =>
        HWHit{xx, jj}, tt, ss, et), Equal.cong(Nat, HW, xx => HWHit{ss, xx}, jj, nn, ej))
    case HWMiss{}:
      Empty.absurd({HWMiss{} == HWHit{ss, nn} : HW}, false_true(hh))

# the dc book the encoder builds, written out
def dcbook.lit() -> Array<U32>:
  ANode{ANode{ANode{ANode{ANode{ANode{ANode{ANode{ALeaf{131072}, ALeaf{196610}}, ANode{ALeaf{196611},
    ALeaf{196612}}}, ANode{ANode{ALeaf{196613}, ALeaf{196614}}, ANode{ALeaf{262158}, ALeaf{327710}}}},
    ANode{ANode{ANode{ALeaf{393278}, ALeaf{458878}}, ANode{ALeaf{524542}, ALeaf{590334}}}, ANode{ANode{ALeaf{0},
    ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}},
    ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}, ANode{ANode{ANode{ALeaf{0}, ALeaf{0}},
    ANode{ALeaf{0}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}},
    ANode{ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}},
    ANode{ALeaf{0}, ALeaf{0}}}}, ANode{ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}},
    ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{0}},
    ANode{ALeaf{0}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}},
    ANode{ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}},
    ANode{ALeaf{0}, ALeaf{0}}}}}}}, ANode{ANode{ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0},
    ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}, ANode{ANode{ANode{ALeaf{0}, ALeaf{0}},
    ANode{ALeaf{0}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}},
    ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}},
    ANode{ALeaf{0}, ALeaf{0}}}}, ANode{ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}},
    ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}}, ANode{ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{0}},
    ANode{ALeaf{0}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}},
    ANode{ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}},
    ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}},
    ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}, ANode{ANode{ANode{ALeaf{0}, ALeaf{0}},
    ANode{ALeaf{0}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}}}},
    ANode{ANode{ANode{ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}, ANode{ANode{ALeaf{0},
    ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}, ANode{ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}},
    ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{0}},
    ANode{ALeaf{0}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}},
    ANode{ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}},
    ANode{ALeaf{0}, ALeaf{0}}}}}}, ANode{ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}},
    ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}, ANode{ANode{ANode{ALeaf{0}, ALeaf{0}},
    ANode{ALeaf{0}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}},
    ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}},
    ANode{ALeaf{0}, ALeaf{0}}}}, ANode{ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}},
    ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}}}, ANode{ANode{ANode{ANode{ANode{ANode{ALeaf{0},
    ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}},
    ANode{ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}},
    ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}},
    ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}, ANode{ANode{ANode{ALeaf{0}, ALeaf{0}},
    ANode{ALeaf{0}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}},
    ANode{ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}},
    ANode{ALeaf{0}, ALeaf{0}}}}, ANode{ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}},
    ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{0}},
    ANode{ALeaf{0}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}},
    ANode{ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}},
    ANode{ALeaf{0}, ALeaf{0}}}}}}}}}

# the dc table the decoder builds, in groups of one code length
def dcgrp() -> List<&2, HG>:
  [HG{2, [0], [0]}, HG{3, [2, 3, 4, 5, 6], [1, 2, 3, 4, 5]}, HG{4, [14], [6]}, HG{5, [30], [7]},
    HG{6, [62], [8]}, HG{7, [126], [9]}, HG{8, [254], [10]}, HG{9, [510], [11]}]

# the encoder's book is the one written out
def dcbook.eq() -> {Jenc.encode.huff(Jenc.encode.dccounts(), Jenc.encode.dcsyms()) == dcbook.lit() : Array<U32>}:
  {==}

# the statement of dctab.eq
def dctab.eq.ty() -> Type:
  {Jpeg.decode.canon(272n, 0n, Jenc.encode.dccounts(), Jenc.encode.dcsyms(), 0, 0, [], [],
    []) == Jpeg.Huff{gc(dcgrp()), gl(dcgrp()), gsy(dcgrp())} : Jpeg.Huff}

# the decoder's table is the groups'
def dctab.eq() -> dctab.eq.ty():
  {==}

# the dc table in groups, as the decoder holds it
def dctab() -> Jpeg.Huff:
  Jpeg.Huff{gc(dcgrp()), gl(dcgrp()), gsy(dcgrp())}

# every group has as many symbols as codes
def dcgrp.wf() -> {wfg(dcgrp()) == True{} : Bool}:
  {==}

# a symbol's code in the dc book
def code.dc(+sy: U32) -> List<&2, Bool>:
  Laws.jpg.cbw(Laws.jpg.val(Array.get(U32, dcbook.lit(), sy)))

# the check for one symbol: its book code hits it
def chk.dc(+ss: U32) -> Bool:
  hwchk(code.dc(ss), dcgrp(), ss)

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
      es = Equal.sym(U32, ss, xx, U32L.ueq(ss, xx, he))
      %es : {chk.dc(_) == True{} : Bool}
      also_l(chk.dc(xx), all.dc(rest), hall)
    case False{}:
      ih(hin, also_r(chk.dc(xx), all.dc(rest), hall))

# a symbol of a list whose symbols all pass passes
def memb.dc(
  xs: List<&2, U32>,
  +ss: U32,
  hin: {Laws.jpg.memb(ss, xs) == True{} : Bool},
  hall: {all.dc(xs) == True{} : Bool}
) -> {chk.dc(ss) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({chk.dc(ss) == True{} : Bool}, false_true(hin))
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
  +he: {rem(ss) == List.append(&2, Bool, code.dc(sy), tl) : List<&2, Bool>},
  +hc: {chk.dc(sy) == True{} : Bool}
) -> {Jpeg.decode.huff(16n, Jpeg.Ask{None{}, 0, 0, rbits(ss, ok)}, Jpeg.Huff{gc(dcgrp()), gl(dcgrp()),
  gsy(dcgrp())}) == Jpeg.Hit{sy, rbits(radv(List.length(&2, Bool, code.dc(sy)), ss), ok), ok} : Jpeg.Hit}:
  +cc = code.dc(sy)
  +nn = List.length(&2, Bool, cc)
  +gs = dcgrp()
  +tab = {Jpeg.Huff{gc(gs), gl(gs), gsy(gs)} : Jpeg.Huff}
  +eh = {hwis(hwg(cc, gs, 0, 0), sy, nn, and_r(Nat.is_le(nn, 16n), hw.is(hwg(cc, gs, 0, 0), sy, nn), hc)) :
    {hwg(cc, gs, 0, 0) == HWHit{sy, nn} : HW}}
  +ew = {Equal.trans(HW, hw(cc, tab, 0, 0), hwg(cc, gs, 0, 0), HWHit{sy, nn}, hw_g(cc, gs, 0, 0,
    dcgrp.wf()), eh) : {hw(cc, tab, 0, 0) == HWHit{sy, nn} : HW}}
  +hf = {Equal.trans(Bool, hw.fits(hw(cc, tab, 0, 0), 16n), hw.fits(HWHit{sy, nn}, 16n), True{},
    Equal.cong(HW, Bool, rr => hw.fits(rr, 16n), hw(cc, tab, 0, 0), HWHit{sy, nn}, ew),
    and_l(Nat.is_le(nn, 16n), hw.is(hwg(cc, gs, 0, 0), sy, nn), hc)) :
    {hw.fits(hw(cc, tab, 0, 0), 16n) == True{} : Bool}}
  Equal.trans(Jpeg.Hit, Jpeg.decode.huff(16n, Jpeg.Ask{None{}, 0, 0, rbits(ss, ok)}, tab), hwres(hw(cc, tab,
    0, 0), ss, ok), Jpeg.Hit{sy, rbits(radv(nn, ss), ok), ok}, hwalk(cc, 16n, ss, ok, 0, 0, gc(gs),
    gl(gs), gsy(gs), tl, hs, h8, he, hf), Equal.cong(HW, Jpeg.Hit, rr => hwres(rr, ss, ok), hw(cc, tab,
    0, 0), HWHit{sy, nn}, ew))

# the ac book the encoder builds, written out
def acbook.lit() -> Array<U32>:
  ANode{ANode{ANode{ANode{ANode{ANode{ANode{ANode{ALeaf{262154}, ALeaf{131072}}, ANode{ALeaf{131073},
    ALeaf{196612}}}, ANode{ANode{ALeaf{262155}, ALeaf{327706}}, ANode{ALeaf{458872}, ALeaf{524536}}}},
    ANode{ANode{ANode{ALeaf{656374}, ALeaf{1113986}}, ANode{ALeaf{1113987}, ALeaf{0}}}, ANode{ANode{ALeaf{0},
    ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{262156}}, ANode{ALeaf{327707},
    ALeaf{458873}}}, ANode{ANode{ALeaf{590326}, ALeaf{722934}}, ANode{ALeaf{1113988}, ALeaf{1113989}}}},
    ANode{ANode{ANode{ALeaf{1113990}, ALeaf{1113991}}, ANode{ALeaf{1113992}, ALeaf{0}}}, ANode{ANode{ALeaf{0},
    ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}}, ANode{ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{327708}},
    ANode{ALeaf{524537}, ALeaf{656375}}}, ANode{ANode{ALeaf{790516}, ALeaf{1113993}}, ANode{ALeaf{1113994},
    ALeaf{1113995}}}}, ANode{ANode{ANode{ALeaf{1113996}, ALeaf{1113997}}, ANode{ALeaf{1113998}, ALeaf{0}}},
    ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{393274}},
    ANode{ALeaf{590327}, ALeaf{790517}}}, ANode{ANode{ALeaf{1113999}, ALeaf{1114000}}, ANode{ALeaf{1114001},
    ALeaf{1114002}}}}, ANode{ANode{ANode{ALeaf{1114003}, ALeaf{1114004}}, ANode{ALeaf{1114005}, ALeaf{0}}},
    ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}}}, ANode{ANode{ANode{ANode{ANode{ANode{ALeaf{0},
    ALeaf{393275}}, ANode{ALeaf{656376}, ALeaf{1114006}}}, ANode{ANode{ALeaf{1114007}, ALeaf{1114008}},
    ANode{ALeaf{1114009}, ALeaf{1114010}}}}, ANode{ANode{ANode{ALeaf{1114011}, ALeaf{1114012}}, ANode{ALeaf{1114013},
    ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{0},
    ALeaf{458874}}, ANode{ALeaf{722935}, ALeaf{1114014}}}, ANode{ANode{ALeaf{1114015}, ALeaf{1114016}},
    ANode{ALeaf{1114017}, ALeaf{1114018}}}}, ANode{ANode{ANode{ALeaf{1114019}, ALeaf{1114020}}, ANode{ALeaf{1114021},
    ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}},
    ANode{ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{458875}}, ANode{ALeaf{790518}, ALeaf{1114022}}},
    ANode{ANode{ALeaf{1114023}, ALeaf{1114024}}, ANode{ALeaf{1114025}, ALeaf{1114026}}}},
    ANode{ANode{ANode{ALeaf{1114027}, ALeaf{1114028}}, ANode{ALeaf{1114029}, ALeaf{0}}}, ANode{ANode{ALeaf{0},
    ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{524538}}, ANode{ALeaf{790519},
    ALeaf{1114030}}}, ANode{ANode{ALeaf{1114031}, ALeaf{1114032}}, ANode{ALeaf{1114033}, ALeaf{1114034}}}},
    ANode{ANode{ANode{ALeaf{1114035}, ALeaf{1114036}}, ANode{ALeaf{1114037}, ALeaf{0}}}, ANode{ANode{ALeaf{0},
    ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}}}}, ANode{ANode{ANode{ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{590328}},
    ANode{ALeaf{1015744}, ALeaf{1114038}}}, ANode{ANode{ALeaf{1114039}, ALeaf{1114040}}, ANode{ALeaf{1114041},
    ALeaf{1114042}}}}, ANode{ANode{ANode{ALeaf{1114043}, ALeaf{1114044}}, ANode{ALeaf{1114045}, ALeaf{0}}},
    ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{590329}},
    ANode{ALeaf{1114046}, ALeaf{1114047}}}, ANode{ANode{ALeaf{1114048}, ALeaf{1114049}}, ANode{ALeaf{1114050},
    ALeaf{1114051}}}}, ANode{ANode{ANode{ALeaf{1114052}, ALeaf{1114053}}, ANode{ALeaf{1114054}, ALeaf{0}}},
    ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}}, ANode{ANode{ANode{ANode{ANode{ALeaf{0},
    ALeaf{590330}}, ANode{ALeaf{1114055}, ALeaf{1114056}}}, ANode{ANode{ALeaf{1114057}, ALeaf{1114058}},
    ANode{ALeaf{1114059}, ALeaf{1114060}}}}, ANode{ANode{ANode{ALeaf{1114061}, ALeaf{1114062}}, ANode{ALeaf{1114063},
    ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{0},
    ALeaf{656377}}, ANode{ALeaf{1114064}, ALeaf{1114065}}}, ANode{ANode{ALeaf{1114066}, ALeaf{1114067}},
    ANode{ALeaf{1114068}, ALeaf{1114069}}}}, ANode{ANode{ANode{ALeaf{1114070}, ALeaf{1114071}}, ANode{ALeaf{1114072},
    ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}}},
    ANode{ANode{ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{656378}}, ANode{ALeaf{1114073}, ALeaf{1114074}}},
    ANode{ANode{ALeaf{1114075}, ALeaf{1114076}}, ANode{ALeaf{1114077}, ALeaf{1114078}}}},
    ANode{ANode{ANode{ALeaf{1114079}, ALeaf{1114080}}, ANode{ALeaf{1114081}, ALeaf{0}}}, ANode{ANode{ALeaf{0},
    ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{722936}}, ANode{ALeaf{1114082},
    ALeaf{1114083}}}, ANode{ANode{ALeaf{1114084}, ALeaf{1114085}}, ANode{ALeaf{1114086}, ALeaf{1114087}}}},
    ANode{ANode{ANode{ALeaf{1114088}, ALeaf{1114089}}, ANode{ALeaf{1114090}, ALeaf{0}}}, ANode{ANode{ALeaf{0},
    ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}}, ANode{ANode{ANode{ANode{ANode{ALeaf{0}, ALeaf{1114091}},
    ANode{ALeaf{1114092}, ALeaf{1114093}}}, ANode{ANode{ALeaf{1114094}, ALeaf{1114095}}, ANode{ALeaf{1114096},
    ALeaf{1114097}}}}, ANode{ANode{ANode{ALeaf{1114098}, ALeaf{1114099}}, ANode{ALeaf{1114100}, ALeaf{0}}},
    ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}, ANode{ANode{ANode{ANode{ALeaf{722937},
    ALeaf{1114101}}, ANode{ALeaf{1114102}, ALeaf{1114103}}}, ANode{ANode{ALeaf{1114104}, ALeaf{1114105}},
    ANode{ALeaf{1114106}, ALeaf{1114107}}}}, ANode{ANode{ANode{ALeaf{1114108}, ALeaf{1114109}}, ANode{ALeaf{1114110},
    ALeaf{0}}}, ANode{ANode{ALeaf{0}, ALeaf{0}}, ANode{ALeaf{0}, ALeaf{0}}}}}}}}}

# the ac table the decoder builds, in groups of one code length
def acgrp() -> List<&2, HG>:
  [HG{2, [0, 1], [1, 2]}, HG{3, [4], [3]}, HG{4, [10, 11, 12], [0, 4, 17]}, HG{5, [26, 27, 28], [5, 18,
    33]}, HG{6, [58, 59], [49, 65]}, HG{7, [120, 121, 122, 123], [6, 19, 81, 97]}, HG{8, [248, 249, 250], [7,
    34, 113]}, HG{9, [502, 503, 504, 505, 506], [20, 50, 129, 145, 161]}, HG{10, [1014, 1015, 1016, 1017, 1018],
    [8, 35, 66, 177, 193]}, HG{11, [2038, 2039, 2040, 2041], [21, 82, 209, 240]}, HG{12, [4084, 4085, 4086,
    4087], [36, 51, 98, 114]}, HG{15, [32704], [130]}, HG{16, [65410, 65411, 65412, 65413, 65414, 65415, 65416,
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

# the encoder's book is the one written out
def acbook.eq() -> {Jenc.encode.huff(Jenc.encode.accounts(), Jenc.encode.acsyms()) == acbook.lit() : Array<U32>}:
  {==}

# the statement of actab.eq
def actab.eq.ty() -> Type:
  {Jpeg.decode.canon(272n, 0n, Jenc.encode.accounts(), Jenc.encode.acsyms(), 0, 0, [], [],
    []) == Jpeg.Huff{gc(acgrp()), gl(acgrp()), gsy(acgrp())} : Jpeg.Huff}

# the decoder's table is the groups'
def actab.eq() -> actab.eq.ty():
  {==}

# the ac table in groups, as the decoder holds it
def actab() -> Jpeg.Huff:
  Jpeg.Huff{gc(acgrp()), gl(acgrp()), gsy(acgrp())}

# every group has as many symbols as codes
def acgrp.wf() -> {wfg(acgrp()) == True{} : Bool}:
  {==}

# a symbol's code in the ac book
def code.ac(+sy: U32) -> List<&2, Bool>:
  Laws.jpg.cbw(Laws.jpg.val(Array.get(U32, acbook.lit(), sy)))

# the check for one symbol: its book code hits it
def chk.ac(+ss: U32) -> Bool:
  hwchk(code.ac(ss), acgrp(), ss)

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
      es = Equal.sym(U32, ss, xx, U32L.ueq(ss, xx, he))
      %es : {chk.ac(_) == True{} : Bool}
      also_l(chk.ac(xx), all.ac(rest), hall)
    case False{}:
      ih(hin, also_r(chk.ac(xx), all.ac(rest), hall))

# a symbol of a list whose symbols all pass passes
def memb.ac(
  xs: List<&2, U32>,
  +ss: U32,
  hin: {Laws.jpg.memb(ss, xs) == True{} : Bool},
  hall: {all.ac(xs) == True{} : Bool}
) -> {chk.ac(ss) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({chk.ac(ss) == True{} : Bool}, false_true(hin))
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
  +he: {rem(ss) == List.append(&2, Bool, code.ac(sy), tl) : List<&2, Bool>},
  +hc: {chk.ac(sy) == True{} : Bool}
) -> {Jpeg.decode.huff(16n, Jpeg.Ask{None{}, 0, 0, rbits(ss, ok)}, Jpeg.Huff{gc(acgrp()), gl(acgrp()),
  gsy(acgrp())}) == Jpeg.Hit{sy, rbits(radv(List.length(&2, Bool, code.ac(sy)), ss), ok), ok} : Jpeg.Hit}:
  +cc = code.ac(sy)
  +nn = List.length(&2, Bool, cc)
  +gs = acgrp()
  +tab = {Jpeg.Huff{gc(gs), gl(gs), gsy(gs)} : Jpeg.Huff}
  +eh = {hwis(hwg(cc, gs, 0, 0), sy, nn, and_r(Nat.is_le(nn, 16n), hw.is(hwg(cc, gs, 0, 0), sy, nn), hc)) :
    {hwg(cc, gs, 0, 0) == HWHit{sy, nn} : HW}}
  +ew = {Equal.trans(HW, hw(cc, tab, 0, 0), hwg(cc, gs, 0, 0), HWHit{sy, nn}, hw_g(cc, gs, 0, 0,
    acgrp.wf()), eh) : {hw(cc, tab, 0, 0) == HWHit{sy, nn} : HW}}
  +hf = {Equal.trans(Bool, hw.fits(hw(cc, tab, 0, 0), 16n), hw.fits(HWHit{sy, nn}, 16n), True{},
    Equal.cong(HW, Bool, rr => hw.fits(rr, 16n), hw(cc, tab, 0, 0), HWHit{sy, nn}, ew),
    and_l(Nat.is_le(nn, 16n), hw.is(hwg(cc, gs, 0, 0), sy, nn), hc)) :
    {hw.fits(hw(cc, tab, 0, 0), 16n) == True{} : Bool}}
  Equal.trans(Jpeg.Hit, Jpeg.decode.huff(16n, Jpeg.Ask{None{}, 0, 0, rbits(ss, ok)}, tab), hwres(hw(cc, tab,
    0, 0), ss, ok), Jpeg.Hit{sy, rbits(radv(nn, ss), ok), ok}, hwalk(cc, 16n, ss, ok, 0, 0, gc(gs),
    gl(gs), gsy(gs), tl, hs, h8, he, hf), Equal.cong(HW, Jpeg.Hit, rr => hwres(rr, ss, ok), hw(cc, tab,
    0, 0), HWHit{sy, nn}, ew))

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
  +vr = {Equal.trans(U32, vfold(List.take(&2, Bool, rem(ss), ln), 0), vfold(List.take(&2, Bool, List.append(&2,
    Bool, cc, mr), ln), 0), Laws.jpg.num(cc, 0), Equal.cong(List<&2, Bool>, U32, xs => vfold(List.take(&2, Bool, xs,
    ln), 0), rem(ss), List.append(&2, Bool, cc, mr), ea), Equal.trans(U32, vfold(List.take(&2, Bool, List.append(&2,
    Bool, cc, mr), ln), 0), vfold(cc, 0), Laws.jpg.num(cc, 0), Equal.cong(List<&2, Bool>, U32, xs => vfold(xs, 0),
    List.take(&2, Bool, List.append(&2, Bool, cc, mr), ln), cc, take_app(cc, mr)), Equal.sym(U32,
    Laws.jpg.num(cc, 0), vfold(cc, 0), num_v(cc, 0)))) : {vfold(List.take(&2, Bool, rem(ss), ln), 0) ==
    Laws.jpg.num(cc, 0) : U32}}
  Equal.trans(Jpeg.Bits & U32, Jpeg.decode.read.n(nn, rbits(ss, ok)), canon(U32.to_nat(nn), ss, ok, 0),
    (rbits(s2, ok), Laws.jpg.num(cc, 0)), read_canon(nn, ss, ok), Equal.trans(Jpeg.Bits & U32, canon(U32.to_nat(nn),
    ss, ok, 0), canon(ln, ss, ok, 0), (rbits(s2, ok), Laws.jpg.num(cc, 0)), Equal.cong(Nat, Jpeg.Bits & U32, kk =>
    canon(kk, ss, ok, 0), U32.to_nat(nn), ln, tn16(ln, h16)), Equal.trans(Jpeg.Bits & U32, canon(ln, ss, ok, 0),
    (rbits(s2, ok), vfold(List.take(&2, Bool, rem(ss), ln), 0)), (rbits(s2, ok), Laws.jpg.num(cc, 0)), rread(ln, ss,
    ok, 0, hs, h8, hl), Equal.cong(U32, Jpeg.Bits & U32, vv => (rbits(s2, ok), vv), vfold(List.take(&2, Bool, rem(ss),
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
      +h16 = {also_l(Nat.is_le(ln, 16n), Laws.jpg.codes16(rest), hc) : {Nat.is_le(ln, 16n) == True{} : Bool}}
      +ea = {Equal.trans(List<&2, Bool>, rem(ss), List.append(&2, Bool, List.concat(&2, Bool, cc <> rest), tl),
        List.append(&2, Bool, cc, mr), he, app_assoc(cc, List.concat(&2, Bool, rest), tl)) :
        {rem(ss) == List.append(&2, Bool, cc, mr) : List<&2, Bool>}}
      +s2 = radv(ln, ss)
      +ok2 = {radv_ok(ln, ss, hs, h8) : {Bool.and(rshort(s2), roct8(s2)) == True{} : Bool}}
      skip.join(cc, rest, ss, ok, tl, read1(cc, ss, ok, mr, hs, h8, h16, ea), skip_m(rest, s2, ok, tl, and_l(rshort(s2),
        roct8(s2), ok2), and_r(rshort(s2), roct8(s2), ok2), also_r(Nat.is_le(ln, 16n), Laws.jpg.codes16(rest), hc),
        rem_after(cc, ss, mr, hs, h8, ea)))

# the encoder's code for a symbol from its dc book is the code's bits fed to the writer
def emit_feed.dc(
  +sy: U32,
  +pp: Jenc.Put
) -> {Laws.jpg.emit(Jenc.encode.emit(Jenc.encode.sym(dcbook.lit(), sy), pp)) == Laws.jpg.feed(code.dc(sy),
  pp) : Jenc.Put}:
  +vv = Laws.jpg.val(Array.get(U32, dcbook.lit(), sy))
  Equal.trans(Jenc.Put, Laws.jpg.emit(Jenc.encode.emit(Jenc.encode.coded(Array.get(U32, dcbook.lit(), sy)), pp)),
    Laws.jpg.emit(Jenc.encode.emit(Jenc.encode.coded((dcbook.lit(), vv)), pp)), Laws.jpg.feed(code.dc(sy), pp),
    Equal.cong(Array<U32> & U32, Jenc.Put, gg => Laws.jpg.emit(Jenc.encode.emit(Jenc.encode.coded(gg), pp)),
    Array.get(U32, dcbook.lit(), sy), (dcbook.lit(), vv), W10.get.eq(dcbook.lit(), sy)), bits_go(U32.to_nat(
    U32.shrn(vv, 16n)), pp, U32.and(vv, 65535)))

# the model's bits for codes pre, a symbol's code from the dc book, and codes post
def symbits.dc(+pre: List<&2, List<&2, Bool>>, +sy: U32, +post: List<&2, List<&2, Bool>>) -> List<&2, Bool>:
  List.append(&2, Bool, List.concat(&2, Bool, pre), List.append(&2, Bool, code.dc(sy), List.concat(&2, Bool, post)))

# the bytes the writer makes of them
def SymBytes.dc(+pre: List<&2, List<&2, Bool>>, +sy: U32, +post: List<&2, List<&2, Bool>>) -> Type:
  {Laws.jpg.sym.bytes(pre, dcbook.lit(), sy, post) == rxs(moct(symbits.dc(pre, sy, post), [])) : List<&2, U32>}

# the reader after codes pre back
def SymSkip.dc(+pre: List<&2, List<&2, Bool>>, +sy: U32, +post: List<&2, List<&2, Bool>>) -> Type:
  Skip(pre, RS{[], moct(symbits.dc(pre, sy, post), [])}, 1, List.append(&2, Bool, List.append(&2, Bool, code.dc(sy),
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
) -> {Laws.jpg.sym.back(pre, dcbook.lit(), dctab(), sy, post) == (sy, (Laws.jpg.nums(post), 1), 1) : U32 & (List<&2,
  U32> & U32) & U32}:
  (k1, k2, k3) = sk
  +cc = code.dc(sy)
  +cp = List.concat(&2, Bool, pre)
  +cq = List.concat(&2, Bool, post)
  +bs = List.append(&2, Bool, cp, List.append(&2, Bool, cc, cq))
  +os = moct(bs, [])
  +mp = mpad(bs, [])
  +s0 = {RS{[], os} : RS}
  +mr = List.append(&2, Bool, List.append(&2, Bool, cc, cq), mp)
  +s1 = skm(pre, s0)
  +tl = List.append(&2, Bool, cq, mp)
  +e1 = {Equal.trans(List<&2, Bool>, rem(s1), mr, List.append(&2, Bool, cc, tl), k2, app_assoc(cc, cq, mp)) :
    {rem(s1) == List.append(&2, Bool, cc, tl) : List<&2, Bool>}}
  +f1 = {k3 : {Bool.and(rshort(s1), roct8(s1)) == True{} : Bool}}
  +hs1 = {and_l(rshort(s1), roct8(s1), f1) : {rshort(s1) == True{} : Bool}}
  +h81 = {and_r(rshort(s1), roct8(s1), f1) : {roct8(s1) == True{} : Bool}}
  +s2 = radv(List.length(&2, Bool, cc), s1)
  +f2 = {radv_ok(List.length(&2, Bool, cc), s1, hs1, h81) : {Bool.and(rshort(s2), roct8(s2)) == True{} : Bool}}
  +eh = {huff.dc(s1, 1, sy, tl, hs1, h81, e1, memb.dc(Jenc.encode.dcsyms(), sy, hy, all.dc.ok())) :
    {Jpeg.decode.huff(16n, Jpeg.Ask{None{}, 0, 0, rbits(s1, 1)}, dctab()) == Jpeg.Hit{sy, rbits(s2, 1), 1} : Jpeg.Hit}}
  Equal.trans(U32 & (List<&2, U32> & U32) & U32, Laws.jpg.sym.back(pre, dcbook.lit(), dctab(), sy, post),
    Laws.jpg.hit(Jpeg.decode.huff(16n, Jpeg.Ask{None{}, 0, 0, rbits(s1, 1)}, dctab()), post), (sy,
    (Laws.jpg.nums(post), 1), 1),
    Equal.cong(Jpeg.Bits, U32 & (List<&2, U32> & U32) & U32, bb => Laws.jpg.hit(Jpeg.decode.huff(16n,
    Jpeg.Ask{None{}, 0, 0, bb}, dctab()), post), Laws.jpg.skip(pre, Jpeg.Bits{0, 1, 0, Laws.jpg.sym.bytes(pre,
      dcbook.lit(), sy, post)}), rbits(s1, 1), Equal.trans(Jpeg.Bits, Laws.jpg.skip(pre, Jpeg.Bits{0, 1, 0,
    Laws.jpg.sym.bytes(pre, dcbook.lit(), sy, post)}), Laws.jpg.skip(pre, rbits(s0,
    1)), rbits(s1, 1), Equal.cong(List<&2, U32>, Jpeg.Bits, xs => Laws.jpg.skip(pre, Jpeg.Bits{0, 1, 0, xs}),
    Laws.jpg.sym.bytes(pre, dcbook.lit(), sy, post), rxs(os), eb), k1)),
    Equal.trans(U32 & (List<&2, U32> & U32) & U32, Laws.jpg.hit(Jpeg.decode.huff(16n, Jpeg.Ask{None{}, 0, 0, rbits(s1,
    1)}, dctab()), post),
    Laws.jpg.hit(Jpeg.Hit{sy, rbits(s2, 1), 1}, post), (sy, (Laws.jpg.nums(post), 1), 1), Equal.cong(Jpeg.Hit,
    U32 & (List<&2, U32> & U32) & U32, hh => Laws.jpg.hit(hh, post), Jpeg.decode.huff(16n, Jpeg.Ask{None{}, 0, 0,
    rbits(s1, 1)}, dctab()),
    Jpeg.Hit{sy, rbits(s2, 1), 1}, eh), Equal.cong(List<&2, U32> & U32, U32 & (List<&2, U32> & U32) & U32, rr => (sy,
    rr, 1), Laws.jpg.reads(post, rbits(s2, 1)), (Laws.jpg.nums(post), 1), reads_m(post, s2, 1, mp, and_l(rshort(s2),
    roct8(s2), f2), and_r(rshort(s2), roct8(s2), f2), hq, rem_after(cc, s1, tl, hs1, h81, e1)))))

# codes pre, a symbol's code from the dc book and codes post, round trip through the writer and the reader
def sym_rt.dc(
  +pre: List<&2, List<&2, Bool>>,
  +hp: {Laws.jpg.codes16(pre) == True{} : Bool},
  +sy: U32,
  +hy: {Laws.jpg.memb(sy, Jenc.encode.dcsyms()) == True{} : Bool},
  +post: List<&2, List<&2, Bool>>,
  +hq: {Laws.jpg.codes16(post) == True{} : Bool}
) -> {Laws.jpg.sym.back(pre, dcbook.lit(), dctab(), sy, post) == (sy, (Laws.jpg.nums(post), 1), 1) : U32 & (List<&2,
  U32> & U32) & U32}:
  +cc = code.dc(sy)
  +cp = List.concat(&2, Bool, pre)
  +cq = List.concat(&2, Bool, post)
  +bs = List.append(&2, Bool, cp, List.append(&2, Bool, cc, cq))
  +os = moct(bs, [])
  +mp = mpad(bs, [])
  +p0 = Jenc.encode.put0()
  +ew = {Equal.trans(Jenc.Put, Laws.jpg.write(post, Laws.jpg.emit(Jenc.encode.emit(Jenc.encode.sym(dcbook.lit(), sy),
    Laws.jpg.write(pre, p0)))), Laws.jpg.write(post, Laws.jpg.feed(cc,
    Laws.jpg.write(pre, p0))), Laws.jpg.feed(bs, p0), Equal.cong(Jenc.Put, Jenc.Put, qq => Laws.jpg.write(post, qq),
    Laws.jpg.emit(Jenc.encode.emit(Jenc.encode.sym(dcbook.lit(), sy), Laws.jpg.write(pre, p0))), Laws.jpg.feed(cc,
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
    Laws.jpg.feed(cc, Laws.jpg.feed(cp, p0))), feed_app(cc, cq, Laws.jpg.feed(cp, p0))), Equal.sym(Jenc.Put,
      Laws.jpg.feed(bs, p0),
    Laws.jpg.feed(List.append(&2, Bool, cc, cq), Laws.jpg.feed(cp, p0)), feed_app(cp, List.append(&2, Bool, cc, cq),
      p0)))))) :
    {Laws.jpg.write(post, Laws.jpg.emit(Jenc.encode.emit(Jenc.encode.sym(dcbook.lit(), sy), Laws.jpg.write(pre,
      p0)))) == Laws.jpg.feed(bs, p0) : Jenc.Put}}
  +eb = {Equal.trans(List<&2, U32>, Laws.jpg.sym.bytes(pre, dcbook.lit(), sy, post),
    Jenc.encode.pad(Laws.jpg.feed(bs, wput(WS{[], []}))), rxs(os), Equal.cong(Jenc.Put, List<&2, U32>, qq =>
    Jenc.encode.pad(qq), Laws.jpg.write(post, Laws.jpg.emit(Jenc.encode.emit(Jenc.encode.sym(dcbook.lit(), sy),
      Laws.jpg.write(pre, p0)))), Laws.jpg.feed(bs, p0), ew),
    Equal.trans(List<&2, U32>, Jenc.encode.pad(Laws.jpg.feed(bs, wput(WS{[], []}))), Jenc.encode.pad(wput(wm(bs, WS{[],
    []}))), rxs(os), Equal.cong(Jenc.Put, List<&2, U32>, qq => Jenc.encode.pad(qq), Laws.jpg.feed(bs, wput(WS{[], []})),
    wput(wm(bs, WS{[], []})), wfeed(bs, WS{[], []}, {==})), pad_m(bs, [], [], {==}))) :
    {Laws.jpg.sym.bytes(pre, dcbook.lit(), sy, post) == rxs(os) : List<&2, U32>}}
  +s0 = {RS{[], os} : RS}
  +mr = List.append(&2, Bool, List.append(&2, Bool, cc, cq), mp)
  +e0 = {Equal.trans(List<&2, Bool>, rem(s0), List.append(&2, Bool, bs, mp), List.append(&2, Bool, cp, mr),
    concat_moct(bs, []), app_assoc(cp, List.append(&2, Bool, cc, cq), mp)) : {rem(s0) == List.append(&2, Bool, cp,
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
    Jenc.encode.dcsyms()), cn, sy, post), Laws.jpg.sym.back(pre, dcbook.lit(), cn, sy, post), (sy, (Laws.jpg.nums(post),
    1), 1), Equal.cong(Array<U32>, U32 & (List<&2, U32> & U32) & U32, bk => Laws.jpg.sym.back(pre, bk, cn, sy, post),
    Jenc.encode.huff(Jenc.encode.dccounts(), Jenc.encode.dcsyms()), dcbook.lit(), dcbook.eq()),
    Equal.trans(U32 & (List<&2, U32> & U32) & U32, Laws.jpg.sym.back(pre, dcbook.lit(), cn, sy, post),
    Laws.jpg.sym.back(pre, dcbook.lit(), dctab(), sy, post), (sy, (Laws.jpg.nums(post), 1), 1), Equal.cong(Jpeg.Huff,
    U32 & (List<&2, U32> & U32) & U32, tb => Laws.jpg.sym.back(pre, dcbook.lit(), tb, sy, post), cn, dctab(),
    dctab.eq()), sym_rt.dc(pre, hp, sy, hy, post, hq)))

# the encoder's code for a symbol from its ac book is the code's bits fed to the writer
def emit_feed.ac(
  +sy: U32,
  +pp: Jenc.Put
) -> {Laws.jpg.emit(Jenc.encode.emit(Jenc.encode.sym(acbook.lit(), sy), pp)) == Laws.jpg.feed(code.ac(sy),
  pp) : Jenc.Put}:
  +vv = Laws.jpg.val(Array.get(U32, acbook.lit(), sy))
  Equal.trans(Jenc.Put, Laws.jpg.emit(Jenc.encode.emit(Jenc.encode.coded(Array.get(U32, acbook.lit(), sy)), pp)),
    Laws.jpg.emit(Jenc.encode.emit(Jenc.encode.coded((acbook.lit(), vv)), pp)), Laws.jpg.feed(code.ac(sy), pp),
    Equal.cong(Array<U32> & U32, Jenc.Put, gg => Laws.jpg.emit(Jenc.encode.emit(Jenc.encode.coded(gg), pp)),
    Array.get(U32, acbook.lit(), sy), (acbook.lit(), vv), W10.get.eq(acbook.lit(), sy)), bits_go(U32.to_nat(
    U32.shrn(vv, 16n)), pp, U32.and(vv, 65535)))

# the model's bits for codes pre, a symbol's code from the ac book, and codes post
def symbits.ac(+pre: List<&2, List<&2, Bool>>, +sy: U32, +post: List<&2, List<&2, Bool>>) -> List<&2, Bool>:
  List.append(&2, Bool, List.concat(&2, Bool, pre), List.append(&2, Bool, code.ac(sy), List.concat(&2, Bool, post)))

# the bytes the writer makes of them
def SymBytes.ac(+pre: List<&2, List<&2, Bool>>, +sy: U32, +post: List<&2, List<&2, Bool>>) -> Type:
  {Laws.jpg.sym.bytes(pre, acbook.lit(), sy, post) == rxs(moct(symbits.ac(pre, sy, post), [])) : List<&2, U32>}

# the reader after codes pre back
def SymSkip.ac(+pre: List<&2, List<&2, Bool>>, +sy: U32, +post: List<&2, List<&2, Bool>>) -> Type:
  Skip(pre, RS{[], moct(symbits.ac(pre, sy, post), [])}, 1, List.append(&2, Bool, List.append(&2, Bool, code.ac(sy),
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
) -> {Laws.jpg.sym.back(pre, acbook.lit(), actab(), sy, post) == (sy, (Laws.jpg.nums(post), 1), 1) : U32 & (List<&2,
  U32> & U32) & U32}:
  (k1, k2, k3) = sk
  +cc = code.ac(sy)
  +cp = List.concat(&2, Bool, pre)
  +cq = List.concat(&2, Bool, post)
  +bs = List.append(&2, Bool, cp, List.append(&2, Bool, cc, cq))
  +os = moct(bs, [])
  +mp = mpad(bs, [])
  +s0 = {RS{[], os} : RS}
  +mr = List.append(&2, Bool, List.append(&2, Bool, cc, cq), mp)
  +s1 = skm(pre, s0)
  +tl = List.append(&2, Bool, cq, mp)
  +e1 = {Equal.trans(List<&2, Bool>, rem(s1), mr, List.append(&2, Bool, cc, tl), k2, app_assoc(cc, cq, mp)) :
    {rem(s1) == List.append(&2, Bool, cc, tl) : List<&2, Bool>}}
  +f1 = {k3 : {Bool.and(rshort(s1), roct8(s1)) == True{} : Bool}}
  +hs1 = {and_l(rshort(s1), roct8(s1), f1) : {rshort(s1) == True{} : Bool}}
  +h81 = {and_r(rshort(s1), roct8(s1), f1) : {roct8(s1) == True{} : Bool}}
  +s2 = radv(List.length(&2, Bool, cc), s1)
  +f2 = {radv_ok(List.length(&2, Bool, cc), s1, hs1, h81) : {Bool.and(rshort(s2), roct8(s2)) == True{} : Bool}}
  +eh = {huff.ac(s1, 1, sy, tl, hs1, h81, e1, memb.ac(Jenc.encode.acsyms(), sy, hy, all.ac.ok())) :
    {Jpeg.decode.huff(16n, Jpeg.Ask{None{}, 0, 0, rbits(s1, 1)}, actab()) == Jpeg.Hit{sy, rbits(s2, 1), 1} : Jpeg.Hit}}
  Equal.trans(U32 & (List<&2, U32> & U32) & U32, Laws.jpg.sym.back(pre, acbook.lit(), actab(), sy, post),
    Laws.jpg.hit(Jpeg.decode.huff(16n, Jpeg.Ask{None{}, 0, 0, rbits(s1, 1)}, actab()), post), (sy,
    (Laws.jpg.nums(post), 1), 1),
    Equal.cong(Jpeg.Bits, U32 & (List<&2, U32> & U32) & U32, bb => Laws.jpg.hit(Jpeg.decode.huff(16n,
    Jpeg.Ask{None{}, 0, 0, bb}, actab()), post), Laws.jpg.skip(pre, Jpeg.Bits{0, 1, 0, Laws.jpg.sym.bytes(pre,
      acbook.lit(), sy, post)}), rbits(s1, 1), Equal.trans(Jpeg.Bits, Laws.jpg.skip(pre, Jpeg.Bits{0, 1, 0,
    Laws.jpg.sym.bytes(pre, acbook.lit(), sy, post)}), Laws.jpg.skip(pre, rbits(s0,
    1)), rbits(s1, 1), Equal.cong(List<&2, U32>, Jpeg.Bits, xs => Laws.jpg.skip(pre, Jpeg.Bits{0, 1, 0, xs}),
    Laws.jpg.sym.bytes(pre, acbook.lit(), sy, post), rxs(os), eb), k1)),
    Equal.trans(U32 & (List<&2, U32> & U32) & U32, Laws.jpg.hit(Jpeg.decode.huff(16n, Jpeg.Ask{None{}, 0, 0, rbits(s1,
    1)}, actab()), post),
    Laws.jpg.hit(Jpeg.Hit{sy, rbits(s2, 1), 1}, post), (sy, (Laws.jpg.nums(post), 1), 1), Equal.cong(Jpeg.Hit,
    U32 & (List<&2, U32> & U32) & U32, hh => Laws.jpg.hit(hh, post), Jpeg.decode.huff(16n, Jpeg.Ask{None{}, 0, 0,
    rbits(s1, 1)}, actab()),
    Jpeg.Hit{sy, rbits(s2, 1), 1}, eh), Equal.cong(List<&2, U32> & U32, U32 & (List<&2, U32> & U32) & U32, rr => (sy,
    rr, 1), Laws.jpg.reads(post, rbits(s2, 1)), (Laws.jpg.nums(post), 1), reads_m(post, s2, 1, mp, and_l(rshort(s2),
    roct8(s2), f2), and_r(rshort(s2), roct8(s2), f2), hq, rem_after(cc, s1, tl, hs1, h81, e1)))))

# codes pre, a symbol's code from the ac book and codes post, round trip through the writer and the reader
def sym_rt.ac(
  +pre: List<&2, List<&2, Bool>>,
  +hp: {Laws.jpg.codes16(pre) == True{} : Bool},
  +sy: U32,
  +hy: {Laws.jpg.memb(sy, Jenc.encode.acsyms()) == True{} : Bool},
  +post: List<&2, List<&2, Bool>>,
  +hq: {Laws.jpg.codes16(post) == True{} : Bool}
) -> {Laws.jpg.sym.back(pre, acbook.lit(), actab(), sy, post) == (sy, (Laws.jpg.nums(post), 1), 1) : U32 & (List<&2,
  U32> & U32) & U32}:
  +cc = code.ac(sy)
  +cp = List.concat(&2, Bool, pre)
  +cq = List.concat(&2, Bool, post)
  +bs = List.append(&2, Bool, cp, List.append(&2, Bool, cc, cq))
  +os = moct(bs, [])
  +mp = mpad(bs, [])
  +p0 = Jenc.encode.put0()
  +ew = {Equal.trans(Jenc.Put, Laws.jpg.write(post, Laws.jpg.emit(Jenc.encode.emit(Jenc.encode.sym(acbook.lit(), sy),
    Laws.jpg.write(pre, p0)))), Laws.jpg.write(post, Laws.jpg.feed(cc,
    Laws.jpg.write(pre, p0))), Laws.jpg.feed(bs, p0), Equal.cong(Jenc.Put, Jenc.Put, qq => Laws.jpg.write(post, qq),
    Laws.jpg.emit(Jenc.encode.emit(Jenc.encode.sym(acbook.lit(), sy), Laws.jpg.write(pre, p0))), Laws.jpg.feed(cc,
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
    Laws.jpg.feed(cc, Laws.jpg.feed(cp, p0))), feed_app(cc, cq, Laws.jpg.feed(cp, p0))), Equal.sym(Jenc.Put,
      Laws.jpg.feed(bs, p0),
    Laws.jpg.feed(List.append(&2, Bool, cc, cq), Laws.jpg.feed(cp, p0)), feed_app(cp, List.append(&2, Bool, cc, cq),
      p0)))))) :
    {Laws.jpg.write(post, Laws.jpg.emit(Jenc.encode.emit(Jenc.encode.sym(acbook.lit(), sy), Laws.jpg.write(pre,
      p0)))) == Laws.jpg.feed(bs, p0) : Jenc.Put}}
  +eb = {Equal.trans(List<&2, U32>, Laws.jpg.sym.bytes(pre, acbook.lit(), sy, post),
    Jenc.encode.pad(Laws.jpg.feed(bs, wput(WS{[], []}))), rxs(os), Equal.cong(Jenc.Put, List<&2, U32>, qq =>
    Jenc.encode.pad(qq), Laws.jpg.write(post, Laws.jpg.emit(Jenc.encode.emit(Jenc.encode.sym(acbook.lit(), sy),
      Laws.jpg.write(pre, p0)))), Laws.jpg.feed(bs, p0), ew),
    Equal.trans(List<&2, U32>, Jenc.encode.pad(Laws.jpg.feed(bs, wput(WS{[], []}))), Jenc.encode.pad(wput(wm(bs, WS{[],
    []}))), rxs(os), Equal.cong(Jenc.Put, List<&2, U32>, qq => Jenc.encode.pad(qq), Laws.jpg.feed(bs, wput(WS{[], []})),
    wput(wm(bs, WS{[], []})), wfeed(bs, WS{[], []}, {==})), pad_m(bs, [], [], {==}))) :
    {Laws.jpg.sym.bytes(pre, acbook.lit(), sy, post) == rxs(os) : List<&2, U32>}}
  +s0 = {RS{[], os} : RS}
  +mr = List.append(&2, Bool, List.append(&2, Bool, cc, cq), mp)
  +e0 = {Equal.trans(List<&2, Bool>, rem(s0), List.append(&2, Bool, bs, mp), List.append(&2, Bool, cp, mr),
    concat_moct(bs, []), app_assoc(cp, List.append(&2, Bool, cc, cq), mp)) : {rem(s0) == List.append(&2, Bool, cp,
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
    Jenc.encode.acsyms()), cn, sy, post), Laws.jpg.sym.back(pre, acbook.lit(), cn, sy, post), (sy, (Laws.jpg.nums(post),
    1), 1), Equal.cong(Array<U32>, U32 & (List<&2, U32> & U32) & U32, bk => Laws.jpg.sym.back(pre, bk, cn, sy, post),
    Jenc.encode.huff(Jenc.encode.accounts(), Jenc.encode.acsyms()), acbook.lit(), acbook.eq()),
    Equal.trans(U32 & (List<&2, U32> & U32) & U32, Laws.jpg.sym.back(pre, acbook.lit(), cn, sy, post),
    Laws.jpg.sym.back(pre, acbook.lit(), actab(), sy, post), (sy, (Laws.jpg.nums(post), 1), 1), Equal.cong(Jpeg.Huff,
    U32 & (List<&2, U32> & U32) & U32, tb => Laws.jpg.sym.back(pre, acbook.lit(), tb, sy, post), cn, actab(),
    actab.eq()), sym_rt.ac(pre, hp, sy, hy, post, hq)))

# the bits of AC tokens: each symbol's code in the AC book, then its magnitude bits
def acbits(ts: List<&2, Laws.JTok>) -> List<&2, Bool>:
  match ts:
    case Nil{}:
      []
    case Laws.JTok{+sym, ex} <> rest:
      List.append(&2, Bool, code.ac(sym), List.append(&2, Bool, ex, acbits(rest)))

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
          Empty.absurd({Laws.JTok{_s, _e} <> _rest == [] : List<&2, Laws.JTok>}, false_true(hw))

# an empty list of bits
def isnil.eq(xs: List<&2, Bool>, hh: {Laws.jpg.isnil(xs) == True{} : Bool}) -> {xs == [] : List<&2, Bool>}:
  match xs:
    case Nil{}:
      {==}
    case _h <> _t:
      Empty.absurd({_h <> _t == [] : List<&2, Bool>}, false_true(hh))

# the rest of the AC loop, as a token's step needs it
def IhAc(-rest: List<&2, Laws.JTok>, +pp: Nat, +rr: List<&2, Bool>) -> Type:
  @kk: U32 -> @zz: List<&2, U32> -> @ss: RS -> @hs: {rshort(ss) == True{} : Bool} ->
    @h8: {roct8(ss) == True{} : Bool} -> @he: {rem(ss) == List.append(&2, Bool, acbits(rest), rr) :
    List<&2, Bool>} -> @hw: {Laws.jpg.acwf(rest, Laws.JAcSt{kk, pp, False{}}) == True{} : Bool} ->
    AcRes(Jpeg.decode.ac(pp, Jpeg.Ac{kk, zz, rbits(ss, 1), 0, 1}, actb()), rr)

# the tail after an empty list of magnitude bits and no tokens is the tail
def tail.nil(
  +ex: List<&2, Bool>,
  +rest: List<&2, Laws.JTok>,
  +rr: List<&2, Bool>,
  xe: {ex == [] : List<&2, Bool>},
  re: {rest == [] : List<&2, Laws.JTok>}
) -> {List.append(&2, Bool, ex, List.append(&2, Bool, acbits(rest), rr)) == rr : List<&2, Bool>}:
  Equal.trans(List<&2, Bool>, List.append(&2, Bool, ex, List.append(&2, Bool, acbits(rest), rr)), List.append(&2, Bool,
    acbits(rest), rr), rr, Equal.cong(List<&2, Bool>, List<&2, Bool>, xs => List.append(&2, Bool, xs,
    List.append(&2, Bool, acbits(rest), rr)), ex, [], xe), Equal.cong(List<&2, Laws.JTok>, List<&2, Bool>, ts =>
    List.append(&2, Bool, acbits(ts), rr), rest, [], re))

# the tail after an empty list of magnitude bits
def tail.ex(
  +ex: List<&2, Bool>,
  +rest: List<&2, Laws.JTok>,
  +rr: List<&2, Bool>,
  xe: {ex == [] : List<&2, Bool>}
) -> {List.append(&2, Bool, ex, List.append(&2, Bool, acbits(rest), rr)) == List.append(&2, Bool, acbits(rest),
  rr) : List<&2, Bool>}:
  Equal.cong(List<&2, Bool>, List<&2, Bool>, xs => List.append(&2, Bool, xs, List.append(&2, Bool, acbits(rest), rr)),
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
  er: {rem(s1) == List.append(&2, Bool, ex, List.append(&2, Bool, acbits(rest), rr)) : List<&2, Bool>},
  hk: {Laws.jpg.isnil(ex) == True{} : Bool},
  hr: {Laws.jpg.acwf(rest, Laws.JAcSt{kk, pp, True{}}) == True{} : Bool}
) -> AcRes(Jpeg.decode.ac(pp, Jpeg.Ac{kk, zz, rbits(s1, 1), 1, 1}, actb()), rr):
  acres.done(pp, kk, zz, s1, rr, Equal.trans(List<&2, Bool>, rem(s1), List.append(&2, Bool, ex, List.append(&2,
    Bool, acbits(rest), rr)), rr, er, tail.nil(ex, rest, rr, isnil.eq(ex, hk), acwf.fin(rest, kk, pp, hr))), f1)

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
  er: {rem(s1) == List.append(&2, Bool, ex, List.append(&2, Bool, acbits(rest), rr)) : List<&2, Bool>},
  +hk: {Bool.and(Laws.jpg.isnil(ex), Bool.or(False{}, c2)) == True{} : Bool},
  hr: {Laws.jpg.acwf(rest, Laws.JAcSt{(kk + 16 : U32), pp, True{}}) == True{} : Bool}
) -> AcRes(Jpeg.decode.ac(pp, Jpeg.decode.ac.zrl.eq(c2, zz, rbits(s1, 1), 1), actb()), rr):
  match c2:
    case True{}:
      acres.done(pp, 64, zz, s1, rr, Equal.trans(List<&2, Bool>, rem(s1), List.append(&2, Bool, ex,
        List.append(&2, Bool, acbits(rest), rr)), rr, er, tail.nil(ex, rest, rr, isnil.eq(ex, and_l(Laws.jpg.isnil(ex),
        True{}, hk)), acwf.fin(rest, (kk + 16 : U32), pp, hr))), f1)
    case False{}:
      Empty.absurd(AcRes(Jpeg.decode.ac(pp, Jpeg.decode.ac.zrl.eq(False{}, zz, rbits(s1, 1), 1), actb()), rr),
        false_true(Equal.trans(Bool, False{}, Bool.and(Laws.jpg.isnil(ex), False{}), True{}, Equal.sym(Bool,
        Bool.and(Laws.jpg.isnil(ex), False{}), False{}, R.and_false_r(Laws.jpg.isnil(ex))), hk)))

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
  +er: {rem(s1) == List.append(&2, Bool, ex, List.append(&2, Bool, acbits(rest), rr)) : List<&2, Bool>},
  h2: {U32.is_eq((kk + 16 : U32), 64) == c2 : Bool},
  +hk: {Bool.and(Laws.jpg.isnil(ex), Bool.or(c1, c2)) == True{} : Bool},
  hr: {Laws.jpg.acwf(rest, Laws.JAcSt{(kk + 16 : U32), pp, Bool.not(c1)}) == True{} : Bool},
  ih: IhAc(rest, pp, rr)
) -> AcRes(Jpeg.decode.ac(pp, Jpeg.decode.ac.zrl.k(c1, (kk + 16 : U32), zz, rbits(s1, 1), 1), actb()), rr):
  match c1:
    case True{}:
      ih((kk + 16 : U32), zz, s1, and_l(rshort(s1), roct8(s1), f1), and_r(rshort(s1), roct8(s1), f1),
        Equal.trans(List<&2, Bool>, rem(s1), List.append(&2, Bool, ex, List.append(&2, Bool, acbits(rest), rr)),
        List.append(&2, Bool, acbits(rest), rr), er, tail.ex(ex, rest, rr, isnil.eq(ex, and_l(Laws.jpg.isnil(ex),
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
  +e2: {rem(s2) == List.append(&2, Bool, acbits(rest), rr) : List<&2, Bool>},
  hr: {Laws.jpg.acwf(rest, Laws.JAcSt{n2, pp, c3}) == True{} : Bool},
  ih: IhAc(rest, pp, rr)
) -> AcRes(Jpeg.decode.ac(pp, Jpeg.decode.ac.stored(c3, n2, zz, rbits(s2, 1), 1), actb()), rr):
  match c3:
    case True{}:
      acres.done(pp, n2, zz, s2, rr, Equal.trans(List<&2, Bool>, rem(s2), List.append(&2, Bool, acbits(rest), rr),
        rr, e2, Equal.cong(List<&2, Laws.JTok>, List<&2, Bool>, ts => List.append(&2, Bool, acbits(ts), rr), rest, [],
        acwf.fin(rest, n2, pp, hr))), f2)
    case False{}:
      ih(n2, zz, s2, and_l(rshort(s2), roct8(s2), f2), and_r(rshort(s2), roct8(s2), f2), e2, hr)

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
  +er: {rem(s1) == List.append(&2, Bool, ex, List.append(&2, Bool, acbits(rest), rr)) : List<&2, Bool>},
  hk: RunOk(c1, c2, sym, ex),
  hr: RunRest(rest, kk, sym, pp),
  ih: IhAc(rest, pp, rr)
) -> AcRes(Jpeg.decode.ac(pp, Jpeg.decode.ac.run.b(c1, c2, U32.and(15, sym), (kk + U32.shrn(sym, 4n) : U32), rbits(s1,
  1), zz, 1), actb()), rr):
  match c1:
    case True{}:
      Empty.absurd(AcRes(Jpeg.decode.ac(pp, Jpeg.decode.ac.run.b(True{}, c2, U32.and(15, sym), (kk + U32.shrn(sym,
        4n) : U32), rbits(s1, 1), zz, 1), actb()), rr), false_true(hk))
    case False{}:
      match c2:
        case True{}:
          Empty.absurd(AcRes(Jpeg.decode.ac(pp, Jpeg.decode.ac.run.b(False{}, True{}, U32.and(15, sym), (kk +
            U32.shrn(sym, 4n) : U32), rbits(s1, 1), zz, 1), actb()), rr), false_true(hk))
        case False{}:
          +sz = U32.and(15, sym)
          +nk = (kk + U32.shrn(sym, 4n) : U32)
          +ln = List.length(&2, Bool, ex)
          +mr = List.append(&2, Bool, acbits(rest), rr)
          +s2 = radv(ln, s1)
          +hs1 = {and_l(rshort(s1), roct8(s1), f1) : {rshort(s1) == True{} : Bool}}
          +h81 = {and_r(rshort(s1), roct8(s1), f1) : {roct8(s1) == True{} : Bool}}
          +el = {R.nat_eq_true(ln, U32.to_nat(sz), hk) : {ln == U32.to_nat(sz) : Nat}}
          +hl = {Equal.trans(Bool, Nat.is_le(ln, List.length(&2, Bool, rem(s1))), Nat.is_le(ln, List.length(&2,
            Bool, List.append(&2, Bool, ex, mr))), True{}, Equal.cong(List<&2, Bool>, Bool, xs => Nat.is_le(ln,
            List.length(&2, Bool, xs)), rem(s1), List.append(&2, Bool, ex, mr), er), len_app(ex, mr)) :
            {Nat.is_le(ln, List.length(&2, Bool, rem(s1))) == True{} : Bool}}
          +vv = vfold(List.take(&2, Bool, rem(s1), ln), 0)
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
  +er: {rem(s1) == List.append(&2, Bool, ex, List.append(&2, Bool, acbits(rest), rr)) : List<&2, Bool>},
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
def sim(
  ts: List<&2, Laws.JTok>,
  +left: Nat,
  +kk: U32,
  +zz: List<&2, U32>,
  +ss: RS,
  +rr: List<&2, Bool>,
  +hs: {rshort(ss) == True{} : Bool},
  +h8: {roct8(ss) == True{} : Bool},
  +he: {rem(ss) == List.append(&2, Bool, acbits(ts), rr) : List<&2, Bool>},
  +hw: {Laws.jpg.acwf(ts, Laws.JAcSt{kk, left, False{}}) == True{} : Bool}
) -> AcRes(Jpeg.decode.ac(left, Jpeg.Ac{kk, zz, rbits(ss, 1), 0, 1}, actb()), rr):
  match ts:
    case Nil{}:
      Empty.absurd(AcRes(Jpeg.decode.ac(left, Jpeg.Ac{kk, zz, rbits(ss, 1), 0, 1}, actb()), rr), false_true(hw))
    case +tt <> +rest:
      match tt:
        case Laws.JTok{+sym, +ex}:
          match left:
            case 0n:
              Empty.absurd(AcRes(Jpeg.decode.ac(0n, Jpeg.Ac{kk, zz, rbits(ss, 1), 0, 1}, actb()), rr),
                false_true(hw))
            case 1n+ +pp:
              +e0 = U32.is_eq(sym, 0)
              +e2 = U32.is_eq(sym, 240)
              +ha = {also_l(Laws.jpg.acok(Laws.JTok{sym, ex}, Laws.JAcSt{kk, 1n+pp, False{}}), Laws.jpg.acwf(rest,
                Laws.jpg.acnx(Laws.JTok{sym, ex}, Laws.JAcSt{kk, 1n+pp,
                False{}})), hw) : {Bool.and(Laws.jpg.memb(sym, Jenc.encode.acsyms()), Laws.jpg.acok.k(e0, e2, sym, ex,
                  kk)) ==
                True{} : Bool}}
              +hr = {also_r(Laws.jpg.acok(Laws.JTok{sym, ex}, Laws.JAcSt{kk, 1n+pp, False{}}), Laws.jpg.acwf(rest,
                Laws.jpg.acnx(Laws.JTok{sym, ex}, Laws.JAcSt{kk, 1n+pp,
                False{}})), hw) : {Laws.jpg.acwf(rest, Laws.jpg.acnx.k(e0, e2, sym, kk, 1n+pp)) == True{} : Bool}}
              +cc = code.ac(sym)
              +tl = List.append(&2, Bool, ex, List.append(&2, Bool, acbits(rest), rr))
              +he1 = {Equal.trans(List<&2, Bool>, rem(ss), List.append(&2, Bool, List.append(&2, Bool, cc,
                List.append(&2, Bool, ex, acbits(rest))), rr), List.append(&2, Bool, cc, tl), he,
                Equal.trans(List<&2, Bool>, List.append(&2, Bool, List.append(&2, Bool, cc, List.append(&2, Bool, ex,
                acbits(rest))), rr), List.append(&2, Bool, cc, List.append(&2, Bool, List.append(&2, Bool, ex,
                acbits(rest)), rr)), List.append(&2, Bool, cc, tl), app_assoc(cc, List.append(&2, Bool, ex,
                acbits(rest)), rr), Equal.cong(List<&2, Bool>, List<&2, Bool>, xs => List.append(&2, Bool, cc, xs),
                List.append(&2, Bool, List.append(&2, Bool, ex, acbits(rest)), rr), tl, app_assoc(ex, acbits(rest),
                rr)))) : {rem(ss) == List.append(&2, Bool, cc, tl) : List<&2, Bool>}}
              +s1 = radv(List.length(&2, Bool, cc), ss)
              +eh = {huff.ac(ss, 1, sym, tl, hs, h8, he1, memb.ac(Jenc.encode.acsyms(), sym, and_l(Laws.jpg.memb(sym,
                Jenc.encode.acsyms()), Laws.jpg.acok.k(e0, e2, sym, ex, kk), ha), all.ac.ok())) : {Jpeg.decode.huff(16n,
                Jpeg.Ask{None{}, 0, 0, rbits(ss, 1)}, actb()) == Jpeg.Hit{sym, rbits(s1, 1), 1} : Jpeg.Hit}}
              sh = Equal.sym(Jpeg.Hit, Jpeg.decode.huff(16n, Jpeg.Ask{None{}, 0, 0, rbits(ss, 1)}, actb()),
                Jpeg.Hit{sym, rbits(s1, 1), 1}, eh)
              %sh : AcRes(Jpeg.decode.ac(pp, Jpeg.decode.ac.step(_, kk, zz, 1), actb()), rr)
              sim.k(e0, e2, pp, sym, kk, zz, s1, ex, rest, rr, radv_ok(List.length(&2, Bool, cc), ss, hs, h8),
                rem_after(cc, ss, tl, hs, h8, he1), and_r(Laws.jpg.memb(sym, Jenc.encode.acsyms()),
                  Laws.jpg.acok.k(e0, e2,
                sym, ex, kk), ha), hr, k2 => z2 => s2 => a2 => b2 => c2 => d2 => sim(rest, pp, k2, z2, s2, rr, a2, b2,
                c2, d2))

# the DC table the decoder holds, in groups
def dctb() -> Jpeg.Huff:
  dctab()

# the quantisation table the decoder holds for the encoder's frame: 64 ones
def ones64() -> List<&2, U32>:
  List.replicate(U32, 64n, 1)

# a block's bits: the DC symbol's code in the DC book, its magnitude bits, and the AC tokens' bits
def blkbits(bt: Laws.JBlkTok) -> List<&2, Bool>:
  match bt:
    case Laws.JBlkTok{+dcs, dcx, acs}:
      List.append(&2, Bool, code.dc(dcs), List.append(&2, Bool, dcx, acbits(acs)))

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
      Empty.absurd({_h <> _t == [] : List<&2, Bool>}, false_true(hh))

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
  +er: {rem(s1) == List.append(&2, Bool, dcx, List.append(&2, Bool, acbits(acs), rr)) : List<&2, Bool>},
  +hz: {U32.is_eq(dcs, 0) == zz : Bool},
  +hl: {Nat.is_eq(List.length(&2, Bool, dcx), U32.to_nat(dcs)) == True{} : Bool},
  +hw: {Laws.jpg.acwf(acs, Laws.JAcSt{1, 63n, False{}}) == True{} : Bool}
) -> BlkRes(Jpeg.decode.block.cat(zz, dcs, rbits(s1, 1), pred, 1, actb(), ones64(), Jpeg.decode.qok(ones64())), rr):
  match zz:
    case True{}:
      +hs1 = {and_l(rshort(s1), roct8(s1), f1) : {rshort(s1) == True{} : Bool}}
      +h81 = {and_r(rshort(s1), roct8(s1), f1) : {roct8(s1) == True{} : Bool}}
      +mr = List.append(&2, Bool, acbits(acs), rr)
      +dz = {U32L.ueq(dcs, 0, hz) : {dcs == 0 : U32}}
      +hl0 = {Equal.trans(Bool, Nat.is_eq(List.length(&2, Bool, dcx), U32.to_nat(0)), Nat.is_eq(List.length(&2, Bool,
        dcx), U32.to_nat(dcs)), True{}, Equal.cong(U32, Bool, xx => Nat.is_eq(List.length(&2, Bool, dcx),
        U32.to_nat(xx)), 0, dcs, Equal.sym(U32, dcs, 0, dz)), hl) : {Nat.is_eq(List.length(&2, Bool, dcx), 0n) ==
        True{} : Bool}}
      +e1 = {Equal.trans(List<&2, Bool>, rem(s1), List.append(&2, Bool, dcx, mr), mr, er, Equal.cong(List<&2, Bool>,
        List<&2, Bool>, xs => List.append(&2, Bool, xs, mr), dcx, [], len0(dcx, hl0))) : {rem(s1) == mr :
        List<&2, Bool>}}
      +dc = (pred + Jpeg.decode.extend(0, 0) : U32)
      blk.from.ac(Jpeg.decode.ac(63n, Jpeg.Ac{1, dc <> Jpeg.decode.zeros(63n, []), rbits(s1, 1), 0, 1}, actb()),
        dc, rr, sim(acs, 63n, 1, dc <> Jpeg.decode.zeros(63n, []), s1, rr, hs1, h81, e1, hw))
    case False{}:
      +hs1 = {and_l(rshort(s1), roct8(s1), f1) : {rshort(s1) == True{} : Bool}}
      +h81 = {and_r(rshort(s1), roct8(s1), f1) : {roct8(s1) == True{} : Bool}}
      +mr = List.append(&2, Bool, acbits(acs), rr)
      +ln = List.length(&2, Bool, dcx)
      +s2 = radv(ln, s1)
      +el = {R.nat_eq_true(ln, U32.to_nat(dcs), hl) : {ln == U32.to_nat(dcs) : Nat}}
      +hl2 = {Equal.trans(Bool, Nat.is_le(ln, List.length(&2, Bool, rem(s1))), Nat.is_le(ln, List.length(&2,
        Bool, List.append(&2, Bool, dcx, mr))), True{}, Equal.cong(List<&2, Bool>, Bool, xs => Nat.is_le(ln,
        List.length(&2, Bool, xs)), rem(s1), List.append(&2, Bool, dcx, mr), er), len_app(dcx, mr)) :
        {Nat.is_le(ln, List.length(&2, Bool, rem(s1))) == True{} : Bool}}
      +vv = vfold(List.take(&2, Bool, rem(s1), ln), 0)
      +erd = {Equal.trans(Jpeg.Bits & U32, Jpeg.decode.read.n(dcs, rbits(s1, 1)), canon(U32.to_nat(dcs), s1, 1,
        0), (rbits(s2, 1), vv), read_canon(dcs, s1, 1), Equal.trans(Jpeg.Bits & U32, canon(U32.to_nat(dcs),
        s1, 1, 0), canon(ln, s1, 1, 0), (rbits(s2, 1), vv), Equal.cong(Nat, Jpeg.Bits & U32, mm =>
        canon(mm, s1, 1, 0), U32.to_nat(dcs), ln, Equal.sym(Nat, ln, U32.to_nat(dcs), el)), rread(ln, s1, 1, 0,
        hs1, h81, hl2))) : {Jpeg.decode.read.n(dcs, rbits(s1, 1)) == (rbits(s2, 1), vv) : Jpeg.Bits & U32}}
      +dc = (pred + Jpeg.decode.extend(dcs, vv) : U32)
      sr = Equal.sym(Jpeg.Bits & U32, Jpeg.decode.read.n(dcs, rbits(s1, 1)), (rbits(s2, 1), vv), erd)
      %sr : BlkRes(Jpeg.decode.block.diff(_, dcs, pred, 1, actb(), ones64(), Jpeg.decode.qok(ones64())), rr)
      blk.from.ac(Jpeg.decode.ac(63n, Jpeg.Ac{1, dc <> Jpeg.decode.zeros(63n, []), rbits(s2, 1), 0, 1}, actb()),
        dc, rr, sim(acs, 63n, 1, dc <> Jpeg.decode.zeros(63n, []), s2, rr, and_l(rshort(s2), roct8(s2),
        radv_ok(ln, s1, hs1, h81)), and_r(rshort(s2), roct8(s2), radv_ok(ln, s1, hs1, h81)),
        rem_after(dcx, s1, mr, hs1, h81, er), hw))

# the decoder reads one block's bits whole: the reader left at the tail, ok still 1
def bsim(
  bt: Laws.JBlkTok,
  +pred: U32,
  +ss: RS,
  +rr: List<&2, Bool>,
  +hs: {rshort(ss) == True{} : Bool},
  +h8: {roct8(ss) == True{} : Bool},
  +he: {rem(ss) == List.append(&2, Bool, blkbits(bt), rr) : List<&2, Bool>},
  +hw: {Laws.jpg.blkwf(bt) == True{} : Bool}
) -> BlkRes(Jpeg.decode.block.go(rbits(ss, 1), pred, dctb(), actb(), ones64()), rr):
  match bt:
    case Laws.JBlkTok{+dcs, +dcx, +acs}:
      +cc = code.dc(dcs)
      +tl = List.append(&2, Bool, dcx, List.append(&2, Bool, acbits(acs), rr))
      +he1 = {Equal.trans(List<&2, Bool>, rem(ss), List.append(&2, Bool, List.append(&2, Bool, cc, List.append(&2,
        Bool, dcx, acbits(acs))), rr), List.append(&2, Bool, cc, tl), he, Equal.trans(List<&2, Bool>,
        List.append(&2, Bool, List.append(&2, Bool, cc, List.append(&2, Bool, dcx, acbits(acs))), rr),
        List.append(&2, Bool, cc, List.append(&2, Bool, List.append(&2, Bool, dcx, acbits(acs)), rr)),
        List.append(&2, Bool, cc, tl), app_assoc(cc, List.append(&2, Bool, dcx, acbits(acs)), rr),
        Equal.cong(List<&2, Bool>, List<&2, Bool>, xs => List.append(&2, Bool, cc, xs), List.append(&2, Bool,
        List.append(&2, Bool, dcx, acbits(acs)), rr), tl, app_assoc(dcx, acbits(acs), rr)))) : {rem(ss) ==
        List.append(&2, Bool, cc, tl) : List<&2, Bool>}}
      +ha = {and_r(Laws.jpg.memb(dcs, Jenc.encode.dcsyms()), Bool.and(Nat.is_eq(List.length(&2, Bool, dcx),
        U32.to_nat(dcs)), Laws.jpg.acwf(acs, Laws.JAcSt{1, 63n, False{}})), hw) : {Bool.and(Nat.is_eq(List.length(&2,
          Bool, dcx),
        U32.to_nat(dcs)), Laws.jpg.acwf(acs, Laws.JAcSt{1, 63n, False{}})) == True{} : Bool}}
      +s1 = radv(List.length(&2, Bool, cc), ss)
      +eh = {huff.dc(ss, 1, dcs, tl, hs, h8, he1, memb.dc(Jenc.encode.dcsyms(), dcs, and_l(Laws.jpg.memb(dcs,
        Jenc.encode.dcsyms()), Bool.and(Nat.is_eq(List.length(&2, Bool, dcx), U32.to_nat(dcs)), Laws.jpg.acwf(acs,
          Laws.JAcSt{1,
        63n, False{}})), hw), all.dc.ok())) : {Jpeg.decode.huff(16n, Jpeg.Ask{None{}, 0, 0, rbits(ss, 1)},
        dctb()) == Jpeg.Hit{dcs, rbits(s1, 1), 1} : Jpeg.Hit}}
      sh = Equal.sym(Jpeg.Hit, Jpeg.decode.huff(16n, Jpeg.Ask{None{}, 0, 0, rbits(ss, 1)}, dctb()), Jpeg.Hit{dcs,
        rbits(s1, 1), 1}, eh)
      %sh : BlkRes(Jpeg.decode.block.dc(_, pred, actb(), ones64(), Jpeg.decode.qok(ones64())), rr)
      bsim.z(U32.is_eq(dcs, 0), dcs, dcx, acs, pred, s1, rr, radv_ok(List.length(&2, Bool, cc), ss, hs, h8),
        rem_after(cc, ss, tl, hs, h8, he1), {==}, and_l(Nat.is_eq(List.length(&2, Bool, dcx), U32.to_nat(dcs)),
        Laws.jpg.acwf(acs, Laws.JAcSt{1, 63n, False{}}), ha), and_r(Nat.is_eq(List.length(&2, Bool, dcx),
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

# the blocks' bits, one after another
def tbits(ts: List<&2, Laws.JBlkTok>) -> List<&2, Bool>:
  match ts:
    case Nil{}:
      []
    case tt <> rest:
      List.append(&2, Bool, blkbits(tt), tbits(rest))

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
def fl(
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
  res: BlkRes(blk, List.append(&2, Bool, tbits(ts), tl)),
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
              +hs = {and_l(rshort(se), roct8(se), e3) : {rshort(se) == True{} : Bool}}
              +h8 = {and_r(rshort(se), roct8(se), e3) : {roct8(se) == True{} : Bool}}
              +mr = List.append(&2, Bool, tbits(rest), tl)
              +he = {Equal.trans(List<&2, Bool>, rem(se), List.append(&2, Bool, List.append(&2, Bool,
                blkbits(tt), tbits(rest)), tl), List.append(&2, Bool, blkbits(tt), mr), e2,
                app_assoc(blkbits(tt), tbits(rest), tl)) : {rem(se) == List.append(&2, Bool, blkbits(tt),
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
              fl(rest, nb, Jpeg.decode.adv.ctrl(Jpeg.decode.adv(ct, fr, sc, 0)), Jpeg.decode.preds.next(
                Jpeg.decode.adv.duef(Jpeg.decode.adv(ct, fr, sc, 0)), preds, cc, pd), ww, hh,
                Jpeg.decode.paint.use(Jpeg.decode.geom(ct, fr, sc), U32.is_eq(cc, 0), ss, yy),
                Jpeg.decode.paint.use(Jpeg.decode.geom(ct, fr, sc), U32.is_eq(cc, 1), ss, cb),
                Jpeg.decode.paint.use(Jpeg.decode.geom(ct, fr, sc), U32.is_eq(cc, 2), ss, cr), tl,
                blkres.tr(gb, nb, mr, Equal.sym(Jpeg.Blk, nb, gb, en), bsim(tt, pn, se, mr, hs, h8, he,
                also_l(Laws.jpg.blkwf(tt), Laws.jpg.allwf(rest), hw))), also_r(Laws.jpg.blkwf(tt),
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
  +he: {rem(RS{[], os}) == List.append(&2, Bool, tbits(tt <> rest), tl) : List<&2, Bool>},
  +hw: {Laws.jpg.allwf(tt <> rest) == True{} : Bool},
  hn: NBlk(ww, hh, rest)
) -> {Laws.jpg.psome(Jpeg.decode.run(Laws.jpg.enc.frame(ww, hh), Laws.jpg.enc.scan(), tabsg(), rxs(os),
  0)) == True{} : Bool}:
  +fr = Laws.jpg.enc.frame(ww, hh)
  +sc = Laws.jpg.enc.scan()
  +s0 = {RS{[], os} : RS}
  +mr = List.append(&2, Bool, tbits(rest), tl)
  +he1 = {Equal.trans(List<&2, Bool>, rem(s0), List.append(&2, Bool, List.append(&2, Bool, blkbits(tt),
    tbits(rest)), tl), List.append(&2, Bool, blkbits(tt), mr), he, app_assoc(blkbits(tt), tbits(rest), tl)) :
    {rem(s0) == List.append(&2, Bool, blkbits(tt), mr) : List<&2, Bool>}}
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
  fl(rest, bo, Jpeg.Ctrl{0, 0, 0, 0, 0, 0}, Jpeg.decode.pred.zero(), ww, hh, Jpeg.decode.plane((ww * hh : U32)),
    Jpeg.decode.plane((ww * hh : U32)), Jpeg.decode.plane((ww * hh : U32)), tl, blkres.tr(bg, bo, mr,
    Equal.sym(Jpeg.Blk, bo, bg, bof(rbits(s0, 1), 0, Jpeg.decode.pred.zero(), ww, hh)), bsim(tt,
    Jpeg.decode.pred.get(Jpeg.decode.pred.zero(), 0), s0, mr, {==}, h8, he1, also_l(Laws.jpg.blkwf(tt),
      Laws.jpg.allwf(rest),
    hw))), also_r(Laws.jpg.blkwf(tt), Laws.jpg.allwf(rest), hw))

# the code the encoder's AC book holds for a symbol is the literal book's
def acode.eq(+sy: U32) -> {Laws.jpg.acode(sy) == code.ac(sy) : List<&2, Bool>}:
  Equal.cong(Array<U32>, List<&2, Bool>, bk => Laws.jpg.cbw(Laws.jpg.val(Array.get(U32, bk, sy))),
    Jenc.encode.huff(Jenc.encode.accounts(), Jenc.encode.acsyms()), acbook.lit(), acbook.eq())

# the code the encoder's DC book holds for a symbol is the literal book's
def dcode.eq(+sy: U32) -> {Laws.jpg.dcode(sy) == code.dc(sy) : List<&2, Bool>}:
  Equal.cong(Array<U32>, List<&2, Bool>, bk => Laws.jpg.cbw(Laws.jpg.val(Array.get(U32, bk, sy))),
    Jenc.encode.huff(Jenc.encode.dccounts(), Jenc.encode.dcsyms()), dcbook.lit(), dcbook.eq())

# AC tokens' bits over the encoder's book are their bits over the literal book
def acbits.eq(ts: List<&2, Laws.JTok>) -> {Laws.jpg.acbits(ts) == acbits(ts) : List<&2, Bool>}:
  match ts:
    case Nil{}:
      {==}
    case Laws.JTok{+sym, +ex} <> +rest:
      Equal.trans(List<&2, Bool>, List.append(&2, Bool, Laws.jpg.acode(sym), List.append(&2, Bool, ex,
        Laws.jpg.acbits(rest))), List.append(&2, Bool, code.ac(sym), List.append(&2, Bool, ex,
        Laws.jpg.acbits(rest))), List.append(&2, Bool, code.ac(sym), List.append(&2, Bool, ex, acbits(rest))),
        Equal.cong(List<&2, Bool>, List<&2, Bool>, xs => List.append(&2, Bool, xs, List.append(&2, Bool, ex,
        Laws.jpg.acbits(rest))), Laws.jpg.acode(sym), code.ac(sym), acode.eq(sym)), Equal.cong(List<&2, Bool>,
        List<&2, Bool>, ys => List.append(&2, Bool, code.ac(sym), List.append(&2, Bool, ex, ys)),
        Laws.jpg.acbits(rest), acbits(rest), acbits.eq(rest)))

# a block's bits over the encoder's books are its bits over the literal books
def blkbits.eq(bt: Laws.JBlkTok) -> {Laws.jpg.blkbits(bt) == blkbits(bt) : List<&2, Bool>}:
  match bt:
    case Laws.JBlkTok{+dcs, +dcx, +acs}:
      Equal.trans(List<&2, Bool>, List.append(&2, Bool, Laws.jpg.dcode(dcs), List.append(&2, Bool, dcx,
        Laws.jpg.acbits(acs))), List.append(&2, Bool, code.dc(dcs), List.append(&2, Bool, dcx, Laws.jpg.acbits(acs))),
        List.append(&2, Bool, code.dc(dcs), List.append(&2, Bool, dcx, acbits(acs))), Equal.cong(List<&2, Bool>,
        List<&2, Bool>, xs => List.append(&2, Bool, xs, List.append(&2, Bool, dcx, Laws.jpg.acbits(acs))),
        Laws.jpg.dcode(dcs), code.dc(dcs), dcode.eq(dcs)), Equal.cong(List<&2, Bool>, List<&2, Bool>,
        ys => List.append(&2, Bool, code.dc(dcs), List.append(&2, Bool, dcx, ys)), Laws.jpg.acbits(acs), acbits(acs),
        acbits.eq(acs)))

# blocks' bits over the encoder's books are their bits over the literal books
def tbits.eq(ts: List<&2, Laws.JBlkTok>) -> {Laws.jpg.tbits(ts) == tbits(ts) : List<&2, Bool>}:
  match ts:
    case Nil{}:
      {==}
    case +tt <> +rest:
      Equal.trans(List<&2, Bool>, List.append(&2, Bool, Laws.jpg.blkbits(tt), Laws.jpg.tbits(rest)), List.append(&2,
        Bool, blkbits(tt), Laws.jpg.tbits(rest)), List.append(&2, Bool, blkbits(tt), tbits(rest)), Equal.cong(List<&2,
        Bool>, List<&2, Bool>, xs => List.append(&2, Bool, xs, Laws.jpg.tbits(rest)), Laws.jpg.blkbits(tt),
        blkbits(tt), blkbits.eq(tt)), Equal.cong(List<&2, Bool>, List<&2, Bool>, ys => List.append(&2, Bool,
        blkbits(tt), ys), Laws.jpg.tbits(rest), tbits(rest), tbits.eq(rest)))

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
  +bs = tbits(tt <> rest)
  +os = moct(bs, [])
  +fr = Laws.jpg.enc.frame(ww, hh)
  +sc = Laws.jpg.enc.scan()
  eb = Equal.sym(List<&2, Bool>, Laws.jpg.tbits(tt <> rest), bs, tbits.eq(tt <> rest))
  et = Equal.sym(Jpeg.Tabs, Laws.jpg.enc.tabs(), tabsg(), tabs.eq())
  ep = Equal.sym(List<&2, U32>, Jenc.encode.pad(Laws.jpg.feed(bs, Jenc.encode.put0())), rxs(os), Equal.trans(List<&2,
    U32>, Jenc.encode.pad(Laws.jpg.feed(bs, wput(WS{[], []}))), Jenc.encode.pad(wput(wm(bs, WS{[], []}))), rxs(os),
    Equal.cong(Jenc.Put, List<&2, U32>, qq => Jenc.encode.pad(qq), Laws.jpg.feed(bs, wput(WS{[], []})), wput(wm(bs,
    WS{[], []})), wfeed(bs, WS{[], []}, {==})), pad_m(bs, [], [], {==})))
  %eb : {Laws.jpg.psome(Jpeg.decode.run(fr, sc, Laws.jpg.enc.tabs(), Jenc.encode.pad(Laws.jpg.feed(_,
    Jenc.encode.put0())), 0)) == True{} : Bool}
  %et : {Laws.jpg.psome(Jpeg.decode.run(fr, sc, _, Jenc.encode.pad(Laws.jpg.feed(bs, Jenc.encode.put0())),
    0)) == True{} : Bool}
  %ep : {Laws.jpg.psome(Jpeg.decode.run(fr, sc, tabsg(), _, 0)) == True{} : Bool}
  dec(tt, rest, mpad(bs, []), ww, hh, os, hw0, hh0, oct8_moct(bs, [], {==}), concat_moct(bs, []), hw, hn)

