# the inflate reader over a stored block's header and data, and 8-bit masks
import Base
import ../../src/inflate.bend as Inf
import ../../src/png.bend as Png
import ../../laws/defs/PngSpecification.bend as D1
import ./BasicFacts.bend as M1

# ---- A. the bit reader on one byte ----

# the integer the reader folds from bits, low bit first: what rd.raw
# accumulates in `acc` while `got` counts the bits so far
def rdv(bits: List<&2, U32>, +acc: U32, +got: U32) -> U32:
  match bits:
    case Nil{}:
      acc
    case +bt <> tl:
      rdv(tl, ((bt << U32.to_nat(got) : U32) .|. acc : U32), (got + 1 : U32))

# a word or'd with zero is itself
def w_or_zero(nn: Nat, ww: Word(nn)) -> {Word.or(nn, ww, Word.zero(nn)) == ww : Word(nn)}:
  match nn:
    case 0n:
      match ww:
        case WNil{}:
          {==}
    case 1n+pp:
      match ww:
        case WCon{False{}, tt}:
          Equal.cong(Word(pp), Word.Con<pp>, xx => WCon{False{}, xx}, Word.or(pp, tt, Word.zero(pp)), tt,
            w_or_zero(pp, tt))
        case WCon{True{}, tt}:
          Equal.cong(Word(pp), Word.Con<pp>, xx => WCon{True{}, xx}, Word.or(pp, tt, Word.zero(pp)), tt,
            w_or_zero(pp, tt))

# a U32 or'd with zero is itself
def u_or_zero(uu: U32) -> {U32.or(uu, 0) == uu : U32}:
  match uu:
    case U32{ww}:
      Equal.cong(Word(32n), U32, xx => U32{xx}, Word.or(32n, ww, Word.zero(32n)), ww, w_or_zero(32n, ww))

# the eight bits of a byte, read back: the low byte, each bit or'd with zero
def rd8.raw(+xx: U32) -> {rdv(Inf.bits.push(7n, xx, []), 0, 0) == U32.or(U32.and(255, xx), 0) : U32}:
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

# the eight bits of any U32's low byte, read back, are that byte
def rd8(+xx: U32) -> {rdv(Inf.bits.push(7n, xx, []), 0, 0) == U32.and(255, xx) : U32}:
  Equal.trans(U32, rdv(Inf.bits.push(7n, xx, []), 0, 0), U32.or(U32.and(255, xx), 0), U32.and(255, xx), rd8.raw(xx),
    u_or_zero(U32.and(255, xx)))

# the sixteen bits of LEN, low byte first, read back: the low 16 bits
def rd16.raw(
  +cc: U32
) -> {rdv(List.append(&2, U32, Inf.bits.push(7n, Png.enc.byte(cc), []), Inf.bits.push(7n, Png.enc.hi(cc), [])), 0, 0) ==
  U32.or(U32.and(65535, cc), 0) : U32}:
  match cc:
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

# the sixteen bits the encoder writes for a U32, read back, are its low 16 bits
def rd16(
  +cc: U32
) -> {rdv(List.append(&2, U32, Inf.bits.push(7n, Png.enc.byte(cc), []), Inf.bits.push(7n, Png.enc.hi(cc), [])), 0, 0) ==
  U32.and(65535, cc) : U32}:
  Equal.trans(U32, rdv(List.append(&2, U32, Inf.bits.push(7n, Png.enc.byte(cc), []), Inf.bits.push(7n,
    Png.enc.hi(cc), [])), 0, 0), U32.or(U32.and(65535, cc), 0), U32.and(65535, cc), rd16.raw(cc),
    u_or_zero(U32.and(65535, cc)))

# the low 16 bits of the complement are the complement of the low 16 bits
def nlen_mask(+cc: U32) -> {U32.and(65535, U32.xor(cc, 65535)) == U32.xor(U32.and(65535, cc), 65535) : U32}:
  match cc:
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

# one bit of cmp_zero_nlt: the rest given, as cc
def cmp_zero_nlt.at(
  cc: Cmp,
  bb: Bool,
  ih: {cc == LT{} : Cmp} -> Empty,
  ee: {Word.cmp.fin(bb, False{}, cc) == LT{} : Cmp}
) -> Empty:
  match cc:
    case LT{}:
      ih({==})
    case GT{}:
      %ee : M1.lt_ty(_)
      Unit{}
    case EQ{}:
      match bb:
        case False{}:
          %ee : M1.lt_ty(_)
          Unit{}
        case True{}:
          %ee : M1.lt_ty(_)
          Unit{}

# no word is below zero
def cmp_zero_nlt(nn: Nat, ww: Word(nn), ee: {Word.cmp(nn, ww, Word.zero(nn)) == LT{} : Cmp}) -> Empty:
  match nn:
    case 0n:
      match ww:
        case WNil{}:
          %ee : M1.lt_ty(_)
          Unit{}
    case 1n+(+pp):
      match ww:
        case WCon{bb, +tt}:
          cmp_zero_nlt.at(Word.cmp(pp, tt, Word.zero(pp)), bb, xx => cmp_zero_nlt(pp, tt, xx), ee)

# a U32 whose low eight bits are b0 to b7 compared with 255, the rest's comparison with zero given as cc
def le8.cmp(b0: Bool, b1: Bool, b2: Bool, b3: Bool, b4: Bool, b5: Bool, b6: Bool, b7: Bool, cc: Cmp) -> Cmp:
  Word.cmp.fin(b0, True{}, Word.cmp.fin(b1, True{}, Word.cmp.fin(b2, True{}, Word.cmp.fin(b3, True{}, Word.cmp.fin(b4,
    True{}, Word.cmp.fin(b5, True{}, Word.cmp.fin(b6, True{}, Word.cmp.fin(b7, True{}, cc))))))))

# a U32 at most 255 has its high 24 bits clear, once their comparison with zero is named cc
def mask8.hi(
  cc: Cmp,
  hi: Word(24n),
  ec: {Word.cmp(24n, hi, Word.zero(24n)) == cc : Cmp},
  b0: Bool,
  b1: Bool,
  b2: Bool,
  b3: Bool,
  b4: Bool,
  b5: Bool,
  b6: Bool,
  b7: Bool,
  h_le: {Cmp.is_le(le8.cmp(b0, b1, b2, b3, b4, b5, b6, b7, cc)) == True{} : Bool}
) -> {hi == Word.zero(24n) : Word(24n)}:
  match cc:
    case LT{}:
      Empty.absurd({hi == Word.zero(24n) : Word(24n)}, cmp_zero_nlt(24n, hi, ec))
    case GT{}:
      Empty.absurd({hi == Word.zero(24n) : Word(24n)}, M1.false_true(h_le))
    case EQ{}:
      M1.weq(24n, hi, Word.zero(24n), Equal.cong(Cmp, Bool, xx => Cmp.is_eq(xx), Word.cmp(24n, hi, Word.zero(24n)),
        EQ{}, ec))

# a U32 at most 255 is its own low byte
def mask8(+xx: U32, h_le: {U32.is_le(xx, 255) == True{} : Bool}) -> {U32.and(255, xx) == xx : U32}:
  match xx:
    case U32{WCon{+b0, WCon{+b1, WCon{+b2, WCon{+b3, WCon{+b4, WCon{+b5, WCon{+b6, WCon{+b7, +hi}}}}}}}}}:
      eh = Equal.sym(Word(24n), hi, Word.zero(24n), mask8.hi(Word.cmp(24n, hi, Word.zero(24n)), hi, {==}, b0, b1, b2,
        b3, b4, b5, b6, b7, h_le))
      %eh : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.and(24n,
        Word.zero(24n), _)}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7,
        _}}}}}}}}} : U32}
      {==}

# ---- B. the inflate reader over stored blocks ----

# the reader where a block header starts: three bits for BFINAL and BTYPE,
# after the zlib header or a stored block that was not the last. `left` is
# what the last block's count ran down to, `out` the bytes so far, newest first
def st.blk(+left: U32, out: List<&2, U32>) -> Inf.St:
  Inf.st.make(Inf.PByte{}, Inf.MBlk{}, Inf.WLit{}, 0, 0, 3, False{}, left, 0, out, [], [], [], [], 0, 0, 120, 0, 0, 0,
    0, 0, 0, 0, 0)

# the reader on the bits of some bytes
def run.bytes(xs: List<&2, U32>, st: Inf.St) -> Maybe<&2, List<&2, U32>>:
  Inf.inflate.go(Inf.bits.of(xs), st)

# the sixteen-bit field the encoder writes for a U32, as the reader folds it
def t16(+cc: U32) -> U32:
  rdv(List.append(&2, U32, Inf.bits.push(7n, Png.enc.byte(cc), []), Inf.bits.push(7n, Png.enc.hi(cc), [])), 0, 0)

# the reader after LEN and NLEN: data bytes next, or the block's end when LEN is 0
def st.nlen(fin: Bool, +left: U32, out: List<&2, U32>) -> Inf.St:
  Inf.rd.nlen.ok(U32.is_zero(left), Inf.WLit{}, fin, left, 0, out, [], [], [], [], 0, 0, 120, 0, 0, 0, 0, 0, 0)

# a stored block's five header bytes, as the reader first folds them: the
# NLEN check still open
def bhead.raw(
  fin: Bool,
  +cc: U32,
  +nl: U32,
  rest: List<&2, U32>,
  +left: U32,
  out: List<&2, U32>
) -> {run.bytes(List.append(&2, U32, Png.enc.head(fin, cc, nl), rest), st.blk(left, out)) ==
  Inf.inflate.go(Inf.bits.of(rest), Inf.st.gate(U32.is_eq(t16(nl), U32.xor(t16(cc), 65535)), st.nlen(fin, t16(cc),
  out), Inf.st.fail())) : Maybe<&2, List<&2, U32>>}:
  match fin:
    case True{}:
      {==}
    case False{}:
      {==}

# NLEN, the complement of LEN, passes the reader's check
def nlen_pass(+cc: U32) -> {U32.is_eq(t16(U32.xor(cc, 65535)), U32.xor(t16(cc), 65535)) == True{} : Bool}:
  e1 = Equal.sym(U32, t16(U32.xor(cc, 65535)), U32.and(65535, U32.xor(cc, 65535)), rd16(U32.xor(cc, 65535)))
  %e1 : {U32.is_eq(_, U32.xor(t16(cc), 65535)) == True{} : Bool}
  e2 = Equal.sym(U32, t16(cc), U32.and(65535, cc), rd16(cc))
  %e2 : {U32.is_eq(U32.and(65535, U32.xor(cc, 65535)), U32.xor(_, 65535)) == True{} : Bool}
  e3 = Equal.sym(U32, U32.and(65535, U32.xor(cc, 65535)), U32.xor(U32.and(65535, cc), 65535), nlen_mask(cc))
  %e3 : {U32.is_eq(_, U32.xor(U32.and(65535, cc), 65535)) == True{} : Bool}
  M1.u32_eq_refl(U32.xor(U32.and(65535, cc), 65535))

# a stored block's five header bytes, LEN then its complement, leave the reader
# at the data with LEN's low 16 bits to count
def bhead(
  +fin: Bool,
  +cc: U32,
  +rest: List<&2, U32>,
  +left: U32,
  +out: List<&2, U32>
) -> {run.bytes(List.append(&2, U32, Png.enc.head(fin, cc, U32.xor(cc, 65535)), rest), st.blk(left, out)) ==
  Inf.inflate.go(Inf.bits.of(rest), st.nlen(fin, U32.and(65535, cc), out)) : Maybe<&2, List<&2, U32>>}:
  +mm = U32.and(65535, cc)
  +lhs = run.bytes(List.append(&2, U32, Png.enc.head(fin, cc, U32.xor(cc, 65535)), rest), st.blk(left, out))
  Equal.trans(Maybe<&2, List<&2, U32>>, lhs,
    Inf.inflate.go(Inf.bits.of(rest), Inf.st.gate(U32.is_eq(t16(U32.xor(cc, 65535)), U32.xor(t16(cc), 65535)),
      st.nlen(fin, t16(cc), out), Inf.st.fail())),
    Inf.inflate.go(Inf.bits.of(rest), st.nlen(fin, mm, out)),
    bhead.raw(fin, cc, U32.xor(cc, 65535), rest, left, out),
    Equal.trans(Maybe<&2, List<&2, U32>>,
      Inf.inflate.go(Inf.bits.of(rest), Inf.st.gate(U32.is_eq(t16(U32.xor(cc, 65535)), U32.xor(t16(cc), 65535)),
        st.nlen(fin, t16(cc), out), Inf.st.fail())),
      Inf.inflate.go(Inf.bits.of(rest), st.nlen(fin, t16(cc), out)),
      Inf.inflate.go(Inf.bits.of(rest), st.nlen(fin, mm, out)),
      Equal.cong(Bool, Maybe<&2, List<&2, U32>>, bb => Inf.inflate.go(Inf.bits.of(rest), Inf.st.gate(bb, st.nlen(fin,
        t16(cc), out), Inf.st.fail())), U32.is_eq(t16(U32.xor(cc, 65535)), U32.xor(t16(cc), 65535)), True{},
        nlen_pass(cc)),
      Equal.cong(U32, Maybe<&2, List<&2, U32>>, vv => Inf.inflate.go(Inf.bits.of(rest), st.nlen(fin, vv, out)), t16(cc),
        mm, rd16(cc))))

# the answer bytes.go started from was true
def bytes.ok(+xs: List<&2, U32>, +ok: Bool, hh: {D1.bytes.go(xs, ok) == True{} : Bool}) -> {ok == True{} : Bool}:
  match xs ok:
    case Nil{} False{}:
      Empty.absurd({False{} == True{} : Bool}, M1.false_true(hh))
    case _hd <> _tl False{}:
      Empty.absurd({False{} == True{} : Bool}, M1.false_true(hh))
    case _xs True{}:
      {==}

# the rest of a byte list is a byte list
def bytes.tail(
  +xs: List<&2, U32>,
  +ok: Bool,
  hh: {D1.bytes.go(xs, ok) == True{} : Bool}
) -> {D1.bytes.go(xs, True{}) == True{} : Bool}:
  match ok:
    case False{}:
      Empty.absurd({D1.bytes.go(xs, True{}) == True{} : Bool}, M1.false_true(bytes.ok(xs, False{}, hh)))
    case True{}:
      hh

# a count `nn` that runs down to zero exactly over `xs`, one per value: `zz`
# says whether `nn` is zero, as the reader's `left` is tested
def cnt(xs: List<&2, U32>, zz: Bool, +nn: U32) -> Bool:
  match xs zz:
    case Nil{} _zz:
      zz
    case _hd <> _tl True{}:
      False{}
    case _hd <> tl False{}:
      cnt(tl, U32.is_zero((nn - 1 : U32)), (nn - 1 : U32))

# the reader when a stored block's count `left` was just tested: `zz` says it
# is zero
def st.dz(zz: Bool, fin: Bool, +left: U32, out: List<&2, U32>) -> Inf.St:
  Inf.rd.data.z(zz, Inf.WLit{}, fin, left, 0, out, [], [], [], [], 0, 0, 120, 0, 0, 0, 0, 0, 0)

# the reader at a stored block's end
def st.after(fin: Bool, +left: U32, out: List<&2, U32>) -> Inf.St:
  Inf.rd.after(fin, Inf.WLit{}, left, 0, out, [], [], [], [], 0, 0, 120, 0, 0, 0, 0, 0, 0)

# a stored block's data bytes: the reader copies each one and counts down to the block's end
def dl(
  +xs: List<&2, U32>,
  +zz: Bool,
  +left: U32,
  +fin: Bool,
  +out: List<&2, U32>,
  +rest: List<&2, U32>,
  h_cnt: {cnt(xs, zz, left) == True{} : Bool},
  +h_by: {D1.bytes.go(xs, True{}) == True{} : Bool}
) -> {run.bytes(List.append(&2, U32, xs, rest), st.dz(zz, fin, left, out)) == run.bytes(rest, st.after(fin, M1.cd(xs,
  left), List.reverse.go(&2, U32, xs, out))) : Maybe<&2, List<&2, U32>>}:
  match xs zz:
    case Nil{} True{}:
      {==}
    case Nil{} False{}:
      Empty.absurd({run.bytes(rest, st.dz(False{}, fin, left, out)) == run.bytes(rest, st.after(fin, left, out)) :
        Maybe<&2, List<&2, U32>>}, M1.false_true(h_cnt))
    case +hd <> +tl True{}:
      Empty.absurd({run.bytes(List.append(&2, U32, hd <> tl, rest), st.dz(True{}, fin, left, out)) == run.bytes(rest,
        st.after(fin, M1.cd(tl, (left - 1 : U32)), List.reverse.go(&2, U32, tl, hd <> out))) : Maybe<&2, List<&2,
            U32>>},
        M1.false_true(h_cnt))
    case +hd <> +tl False{}:
      +l2 = (left - 1 : U32)
      +eh = Equal.trans(U32, rdv(Inf.bits.push(7n, hd, []), 0, 0), U32.and(255, hd), hd, rd8(hd), mask8(hd,
        bytes.ok(tl, U32.is_le(hd, 255), h_by)))
      Equal.trans(Maybe<&2, List<&2, U32>>,
        run.bytes(List.append(&2, U32, tl, rest), st.dz(U32.is_zero(l2), fin, l2, rdv(Inf.bits.push(7n, hd, []), 0, 0)
          <> out)),
        run.bytes(List.append(&2, U32, tl, rest), st.dz(U32.is_zero(l2), fin, l2, hd <> out)),
        run.bytes(rest, st.after(fin, M1.cd(tl, l2), List.reverse.go(&2, U32, tl, hd <> out))),
        Equal.cong(U32, Maybe<&2, List<&2, U32>>, vv => run.bytes(List.append(&2, U32, tl, rest), st.dz(U32.is_zero(l2),
          fin, l2, vv <> out)), rdv(Inf.bits.push(7n, hd, []), 0, 0), hd, eh),
        dl(tl, U32.is_zero(l2), l2, fin, hd <> out, rest, h_cnt, bytes.tail(tl, U32.is_le(hd, 255), h_by)))

# nlen.ok and data.z branch alike on the zero test
def nz_dz(
  zz: Bool,
  +fin: Bool,
  +left: U32,
  +out: List<&2, U32>,
  +rest: List<&2, U32>
) -> {run.bytes(rest, Inf.rd.nlen.ok(zz, Inf.WLit{}, fin, left, 0, out, [], [], [], [], 0, 0, 120, 0, 0, 0, 0, 0, 0)) ==
  run.bytes(rest, st.dz(zz, fin, left, out)) : Maybe<&2, List<&2, U32>>}:
  match zz:
    case True{}:
      {==}
    case False{}:
      {==}

# a stored block of the bytes `xs` whose LEN field is `cc`: when the low 16
# bits of `cc` count `xs` exactly, the reader copies `xs` and ends the block
def blk.go(
  +fin: Bool,
  +cc: U32,
  +xs: List<&2, U32>,
  +rest: List<&2, U32>,
  +left: U32,
  +out: List<&2, U32>,
  h_cnt: {cnt(xs, U32.is_zero(U32.and(65535, cc)), U32.and(65535, cc)) == True{} : Bool},
  h_by: {D1.bytes.go(xs, True{}) == True{} : Bool}
) -> {run.bytes(List.append(&2, U32, Png.enc.head(fin, cc, U32.xor(cc, 65535)), List.append(&2, U32, xs, rest)),
  st.blk(left, out)) == run.bytes(rest, st.after(fin, M1.cd(xs, U32.and(65535, cc)), List.reverse.go(&2, U32, xs, out))) :  # noqa: S002
  Maybe<&2, List<&2, U32>>}:
  +mm = U32.and(65535, cc)
  +xr = List.append(&2, U32, xs, rest)
  Equal.trans(Maybe<&2, List<&2, U32>>,
    run.bytes(List.append(&2, U32, Png.enc.head(fin, cc, U32.xor(cc, 65535)), xr), st.blk(left, out)),
    run.bytes(xr, st.nlen(fin, mm, out)),
    run.bytes(rest, st.after(fin, M1.cd(xs, mm), List.reverse.go(&2, U32, xs, out))),
    bhead(fin, cc, xr, left, out),
    Equal.trans(Maybe<&2, List<&2, U32>>, run.bytes(xr, st.nlen(fin, mm, out)),
      run.bytes(xr, st.dz(U32.is_zero(mm), fin, mm, out)),
      run.bytes(rest, st.after(fin, M1.cd(xs, mm), List.reverse.go(&2, U32, xs, out))),
      nz_dz(U32.is_zero(mm), fin, mm, out, xr),
      dl(xs, U32.is_zero(mm), mm, fin, out, rest, h_cnt, h_by)))

# the same block with its bytes appended to the header first
def blk(
  +fin: Bool,
  +cc: U32,
  +xs: List<&2, U32>,
  +rest: List<&2, U32>,
  +left: U32,
  +out: List<&2, U32>,
  h_cnt: {cnt(xs, U32.is_zero(U32.and(65535, cc)), U32.and(65535, cc)) == True{} : Bool},
  h_by: {D1.bytes.go(xs, True{}) == True{} : Bool}
) -> {run.bytes(List.append(&2, U32, List.append(&2, U32, Png.enc.head(fin, cc, U32.xor(cc, 65535)), xs), rest),
  st.blk(left, out)) == run.bytes(rest, st.after(fin, M1.cd(xs, U32.and(65535, cc)), List.reverse.go(&2, U32, xs, out))) :  # noqa: S002
  Maybe<&2, List<&2, U32>>}:
  match fin:
    case True{}:
      blk.go(True{}, cc, xs, rest, left, out, h_cnt, h_by)
    case False{}:
      blk.go(False{}, cc, xs, rest, left, out, h_cnt, h_by)
