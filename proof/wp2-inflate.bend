# proof/wp2-inflate: lemmas for IMG-PNG-7, stored zlib blocks through
# Inf.inflate. PROOF.bend imports this file, so the gate checks it. Part A
# is the bit reader on one byte, part B the inflate reader over whole stored
# blocks, part C the U32 and Nat counting, part D the encoder's blocks.
import Base
import ../LAWS.bend as Laws
import ./u32.bend as U32L
import ../src/inflate.bend as Inf
import ../src/png.bend as Png

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

# the Adler field rd.adler folds, big-endian, from the bytes it reads
def run.of(bytes: List<&2, U32>, +run: U32) -> U32:
  match bytes:
    case Nil{}:
      run
    case +bt <> tl:
      run.of(tl, ((255 .&. rdv(Inf.bits.push(7n, bt, []), 0, 0) : U32) .|. (run << 8n : U32) : U32))

# the four bytes enc.be writes, folded back, each bit or'd with zero twice
def run_be.raw(+ss: U32) -> {run.of(Png.enc.be(ss), 0) == U32.or(U32.or(ss, 0), 0) : U32}:
  match ss:
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

# the four bytes enc.be writes, folded back as rd.adler folds them, are the U32
def run_be(+ss: U32) -> {run.of(Png.enc.be(ss), 0) == ss : U32}:
  Equal.trans(U32, run.of(Png.enc.be(ss), 0), U32.or(U32.or(ss, 0), 0), ss, run_be.raw(ss),
    Equal.trans(U32, U32.or(U32.or(ss, 0), 0), U32.or(ss, 0), ss, u_or_zero(U32.or(ss, 0)), u_or_zero(ss)))

# the Cmp LT names: Empty for LT, Unit otherwise
def lt_ty(cc: Cmp) -> Type:
  match cc:
    case LT{}:
      Empty
    case EQ{}:
      Unit
    case GT{}:
      Unit

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
      %ee : lt_ty(_)
      Unit{}
    case EQ{}:
      match bb:
        case False{}:
          %ee : lt_ty(_)
          Unit{}
        case True{}:
          %ee : lt_ty(_)
          Unit{}

# no word is below zero
def cmp_zero_nlt(nn: Nat, ww: Word(nn), ee: {Word.cmp(nn, ww, Word.zero(nn)) == LT{} : Cmp}) -> Empty:
  match nn:
    case 0n:
      match ww:
        case WNil{}:
          %ee : lt_ty(_)
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
      Empty.absurd({hi == Word.zero(24n) : Word(24n)}, U32L.false_true(h_le))
    case EQ{}:
      U32L.weq(24n, hi, Word.zero(24n), Equal.cong(Cmp, Bool, xx => Cmp.is_eq(xx), Word.cmp(24n, hi, Word.zero(24n)),
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

# a U32 whose low sixteen bits are b0 to b15 compared with 65535, the rest's comparison with zero given as cc
def le16.cmp(
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
  b12: Bool,
  b13: Bool,
  b14: Bool,
  b15: Bool,
  cc: Cmp
) -> Cmp:
  Word.cmp.fin(b0, True{}, Word.cmp.fin(b1, True{}, Word.cmp.fin(b2, True{}, Word.cmp.fin(b3, True{}, Word.cmp.fin(b4,
    True{}, Word.cmp.fin(b5, True{}, Word.cmp.fin(b6, True{}, Word.cmp.fin(b7, True{}, Word.cmp.fin(b8, True{},
    Word.cmp.fin(b9, True{}, Word.cmp.fin(b10, True{}, Word.cmp.fin(b11, True{}, Word.cmp.fin(b12, True{},
    Word.cmp.fin(b13, True{}, Word.cmp.fin(b14, True{}, Word.cmp.fin(b15, True{}, cc))))))))))))))))

# a U32 at most 65535 has its high 16 bits clear, once their comparison with zero is named cc
def mask16.hi(
  cc: Cmp,
  hi: Word(16n),
  ec: {Word.cmp(16n, hi, Word.zero(16n)) == cc : Cmp},
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
  b12: Bool,
  b13: Bool,
  b14: Bool,
  b15: Bool,
  h_le: {Cmp.is_le(le16.cmp(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, cc)) == True{} :
    Bool}
) -> {hi == Word.zero(16n) : Word(16n)}:
  match cc:
    case LT{}:
      Empty.absurd({hi == Word.zero(16n) : Word(16n)}, cmp_zero_nlt(16n, hi, ec))
    case GT{}:
      Empty.absurd({hi == Word.zero(16n) : Word(16n)}, U32L.false_true(h_le))
    case EQ{}:
      U32L.weq(16n, hi, Word.zero(16n), Equal.cong(Cmp, Bool, xx => Cmp.is_eq(xx), Word.cmp(16n, hi, Word.zero(16n)),
        EQ{}, ec))

# a U32 at most 65535 is its own low 16 bits
def mask16(+xx: U32, h_le: {U32.is_le(xx, 65535) == True{} : Bool}) -> {U32.and(65535, xx) == xx : U32}:
  match xx:
    case U32{WCon{+b0, WCon{+b1, WCon{+b2, WCon{+b3, WCon{+b4, WCon{+b5, WCon{+b6, WCon{+b7, WCon{+b8, WCon{+b9,
      WCon{+b10, WCon{+b11, WCon{+b12, WCon{+b13, WCon{+b14, WCon{+b15, +hi}}}}}}}}}}}}}}}}}:
      eh = Equal.sym(Word(16n), hi, Word.zero(16n), mask16.hi(Word.cmp(16n, hi, Word.zero(16n)), hi, {==},
        b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, h_le))
      %eh : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10,
        WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, Word.and(16n, Word.zero(16n), _)}}}}}}}}}}}}}}}}} ==
        U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10,
        WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, _}}}}}}}}}}}}}}}}} : U32}
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

# the zlib header 120 1 leaves the reader at the first block header
def hdr(
  rest: List<&2, U32>
) -> {run.bytes(120 <> 1 <> rest, Inf.st.empty()) == run.bytes(rest, st.blk(0, [])) : Maybe<&2, List<&2, U32>>}:
  {==}

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
  U32L.u32_eq_refl(U32.xor(U32.and(65535, cc), 65535))

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
def bytes.ok(+xs: List<&2, U32>, +ok: Bool, hh: {Laws.bytes.go(xs, ok) == True{} : Bool}) -> {ok == True{} : Bool}:
  match xs ok:
    case Nil{} False{}:
      Empty.absurd({False{} == True{} : Bool}, U32L.false_true(hh))
    case _hd <> _tl False{}:
      Empty.absurd({False{} == True{} : Bool}, U32L.false_true(hh))
    case _xs True{}:
      {==}

# the rest of a byte list is a byte list
def bytes.tail(
  +xs: List<&2, U32>,
  +ok: Bool,
  hh: {Laws.bytes.go(xs, ok) == True{} : Bool}
) -> {Laws.bytes.go(xs, True{}) == True{} : Bool}:
  match ok:
    case False{}:
      Empty.absurd({Laws.bytes.go(xs, True{}) == True{} : Bool}, U32L.false_true(bytes.ok(xs, False{}, hh)))
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

# what a count runs down to over `xs`
def cd(xs: List<&2, U32>, +nn: U32) -> U32:
  match xs:
    case Nil{}:
      nn
    case _hd <> tl:
      cd(tl, (nn - 1 : U32))

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
  +h_by: {Laws.bytes.go(xs, True{}) == True{} : Bool}
) -> {run.bytes(List.append(&2, U32, xs, rest), st.dz(zz, fin, left, out)) == run.bytes(rest, st.after(fin, cd(xs,
  left), List.reverse.go(&2, U32, xs, out))) : Maybe<&2, List<&2, U32>>}:
  match xs zz:
    case Nil{} True{}:
      {==}
    case Nil{} False{}:
      Empty.absurd({run.bytes(rest, st.dz(False{}, fin, left, out)) == run.bytes(rest, st.after(fin, left, out)) :
        Maybe<&2, List<&2, U32>>}, U32L.false_true(h_cnt))
    case +hd <> +tl True{}:
      Empty.absurd({run.bytes(List.append(&2, U32, hd <> tl, rest), st.dz(True{}, fin, left, out)) == run.bytes(rest,
        st.after(fin, cd(tl, (left - 1 : U32)), List.reverse.go(&2, U32, tl, hd <> out))) : Maybe<&2, List<&2, U32>>},
        U32L.false_true(h_cnt))
    case +hd <> +tl False{}:
      +l2 = (left - 1 : U32)
      +eh = Equal.trans(U32, rdv(Inf.bits.push(7n, hd, []), 0, 0), U32.and(255, hd), hd, rd8(hd), mask8(hd,
        bytes.ok(tl, U32.is_le(hd, 255), h_by)))
      Equal.trans(Maybe<&2, List<&2, U32>>,
        run.bytes(List.append(&2, U32, tl, rest), st.dz(U32.is_zero(l2), fin, l2, rdv(Inf.bits.push(7n, hd, []), 0, 0)
          <> out)),
        run.bytes(List.append(&2, U32, tl, rest), st.dz(U32.is_zero(l2), fin, l2, hd <> out)),
        run.bytes(rest, st.after(fin, cd(tl, l2), List.reverse.go(&2, U32, tl, hd <> out))),
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

# the reader where the Adler-32 field starts
def st.adler(out: List<&2, U32>) -> Inf.St:
  Inf.st.make(Inf.PByte{}, Inf.MAdler{}, Inf.WLit{}, 0, 0, 8, True{}, 4, 0, out, [], [], [], [], 0, 0, 120, 0, 0, 0, 0,
    0, 0, 0, 0)

# the reader once the Adler-32 field is read, `zz` its check
def st.done(zz: Bool, +raw: List<&2, U32>, +run: U32) -> Inf.St:
  Inf.rd.adler.eq(zz, raw, Inf.WLit{}, True{}, 0, 0, [], [], [], [], 0, 0, 120, 0, 0, 0, run, 0, 0)

# the last block's end leads to the Adler-32 field
def after_last(
  +left: U32,
  +out: List<&2, U32>,
  +rest: List<&2, U32>
) -> {run.bytes(rest, st.after(True{}, left, out)) == run.bytes(rest, st.adler(out)) : Maybe<&2, List<&2, U32>>}:
  {==}

# the four Adler bytes, as the reader first folds them
def adler.raw(
  +ss: U32,
  +out: List<&2, U32>
) -> {run.bytes(Png.enc.be(ss), st.adler(out)) == Inf.inflate.go([], st.done(U32.is_eq(Inf.adler.of(List.reverse(&2,
  U32, out)), run.of(Png.enc.be(ss), 0)), List.reverse(&2, U32, out), run.of(Png.enc.be(ss), 0))) : Maybe<&2, List<&2,
  U32>>}:
  {==}

# the four Adler bytes of the bytes copied: the reader answers those bytes
def adler.ok(
  +ss: U32,
  +out: List<&2, U32>,
  e_sum: {ss == Inf.adler.of(List.reverse(&2, U32, out)) : U32}
) -> {run.bytes(Png.enc.be(ss), st.adler(out)) == Some{List.reverse(&2, U32, out)} : Maybe<&2, List<&2, U32>>}:
  +raw = List.reverse(&2, U32, out)
  +aa = Inf.adler.of(raw)
  +r4 = run.of(Png.enc.be(ss), 0)
  Equal.trans(Maybe<&2, List<&2, U32>>, run.bytes(Png.enc.be(ss), st.adler(out)),
    Inf.inflate.go([], st.done(U32.is_eq(aa, r4), raw, r4)), Some{raw},
    adler.raw(ss, out),
    Equal.trans(Maybe<&2, List<&2, U32>>, Inf.inflate.go([], st.done(U32.is_eq(aa, r4), raw, r4)),
      Inf.inflate.go([], st.done(U32.is_eq(aa, ss), raw, r4)), Some{raw},
      Equal.cong(U32, Maybe<&2, List<&2, U32>>, vv => Inf.inflate.go([], st.done(U32.is_eq(aa, vv), raw, r4)), r4, ss,
        run_be(ss)),
      Equal.trans(Maybe<&2, List<&2, U32>>, Inf.inflate.go([], st.done(U32.is_eq(aa, ss), raw, r4)),
        Inf.inflate.go([], st.done(U32.is_eq(aa, aa), raw, r4)), Some{raw},
        Equal.cong(U32, Maybe<&2, List<&2, U32>>, vv => Inf.inflate.go([], st.done(U32.is_eq(aa, vv), raw, r4)), ss, aa,
          e_sum),
        Equal.cong(Bool, Maybe<&2, List<&2, U32>>, bb => Inf.inflate.go([], st.done(bb, raw, r4)), U32.is_eq(aa, aa),
          True{}, U32L.u32_eq_refl(aa)))))

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
  h_by: {Laws.bytes.go(xs, True{}) == True{} : Bool}
) -> {run.bytes(List.append(&2, U32, Png.enc.head(fin, cc, U32.xor(cc, 65535)), List.append(&2, U32, xs, rest)),
  st.blk(left, out)) == run.bytes(rest, st.after(fin, cd(xs, U32.and(65535, cc)), List.reverse.go(&2, U32, xs, out))) :
  Maybe<&2, List<&2, U32>>}:
  +mm = U32.and(65535, cc)
  +xr = List.append(&2, U32, xs, rest)
  Equal.trans(Maybe<&2, List<&2, U32>>,
    run.bytes(List.append(&2, U32, Png.enc.head(fin, cc, U32.xor(cc, 65535)), xr), st.blk(left, out)),
    run.bytes(xr, st.nlen(fin, mm, out)),
    run.bytes(rest, st.after(fin, cd(xs, mm), List.reverse.go(&2, U32, xs, out))),
    bhead(fin, cc, xr, left, out),
    Equal.trans(Maybe<&2, List<&2, U32>>, run.bytes(xr, st.nlen(fin, mm, out)),
      run.bytes(xr, st.dz(U32.is_zero(mm), fin, mm, out)),
      run.bytes(rest, st.after(fin, cd(xs, mm), List.reverse.go(&2, U32, xs, out))),
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
  h_by: {Laws.bytes.go(xs, True{}) == True{} : Bool}
) -> {run.bytes(List.append(&2, U32, List.append(&2, U32, Png.enc.head(fin, cc, U32.xor(cc, 65535)), xs), rest),
  st.blk(left, out)) == run.bytes(rest, st.after(fin, cd(xs, U32.and(65535, cc)), List.reverse.go(&2, U32, xs, out))) :
  Maybe<&2, List<&2, U32>>}:
  match fin:
    case True{}:
      blk.go(True{}, cc, xs, rest, left, out, h_cnt, h_by)
    case False{}:
      blk.go(False{}, cc, xs, rest, left, out, h_cnt, h_by)

# ---- C. U32 and Nat counting ----
# From ezjson's PROOF.bend (JSON-TREE-6): U32 decrement as a Nat, and U32
# comparison as Nat comparison.

# Unit for True, Empty for False: tells them apart
def true_ty(bb: Bool) -> Type:
  match bb:
    case False{}:
      Empty
    case True{}:
      Unit

# True is never False
law true_false:
  for ee: {True{} == False{} : Bool}
  Empty

# the proof of true_false
def true_false(ee):
  %ee : true_ty(_)
  Unit{}

# one bit of adc_zero_carry, the rest given
law adc_zero_carry.at:
  for +qq: Nat
  for ab: Bool
  for -at: Word(qq)
  for ih: {Word.adc(qq, at, Word.zero(qq), True{}, True{}) == at : Word(qq)}
  {Word.adc.con(qq, at, Word.zero(qq), True{}, Bool.full_add(ab, True{}, True{})) == WCon{ab, at} : Word.Con<qq>}

# the proof of adc_zero_carry.at
def adc_zero_carry.at(qq, ab, at, ih):
  match ab:
    case True{}:
      Equal.cong(Word(qq), Word.Con<qq>, ww => WCon{True{}, ww},
        Word.adc(qq, at, Word.zero(qq), True{}, True{}), at, ih)
    case False{}:
      Equal.cong(Word(qq), Word.Con<qq>, ww => WCon{False{}, ww},
        Word.adc(qq, at, Word.zero(qq), True{}, True{}), at, ih)

# subtracting zero with the carry in adds nothing: a - 0 - 1 + 1 is a
law adc_zero_carry:
  for +pp: Nat
  for +aw: Word(pp)
  {Word.adc(pp, aw, Word.zero(pp), True{}, True{}) == aw : Word(pp)}

# the proof of adc_zero_carry
def adc_zero_carry(pp, aw):
  match pp:
    case 0n:
      match aw:
        case WNil{}:
          {==}
    case 1n+(+qq):
      match aw:
        case WCon{ab, +at}:
          adc_zero_carry.at(qq, ab, at, adc_zero_carry(qq, at))

# a word whose first bit is clear and that is not zero: the rest is not zero
law fin_ff:
  for cc: Cmp
  for h_nz: {Cmp.is_eq(Word.cmp.fin(False{}, False{}, cc)) == False{} : Bool}
  {Cmp.is_eq(cc) == False{} : Bool}

# the proof of fin_ff
def fin_ff(cc, h_nz):
  match cc:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({Cmp.is_eq(EQ{}) == False{} : Bool}, true_false(h_nz))
    case GT{}:
      {==}

# subtracting zero with no carry in takes one: a - 0 - 1, one less than a
# when a is not zero
law adc_zero_borrow:
  for +pp: Nat
  for +aw: Word(pp)
  for h_nz: {Cmp.is_eq(Word.cmp(pp, aw, Word.zero(pp))) == False{} : Bool}
  {1n+Word.to_nat(pp, Word.adc(pp, aw, Word.zero(pp), True{}, False{})) == Word.to_nat(pp, aw) : Nat}

# the proof of adc_zero_borrow
def adc_zero_borrow(pp, aw, h_nz):
  match pp:
    case 0n:
      match aw:
        case WNil{}:
          Empty.absurd({1n == 0n : Nat}, true_false(h_nz))
    case 1n+(+qq):
      match aw:
        case WCon{True{}, +at}:
          lc = Equal.sym(Word(qq), Word.adc(qq, at, Word.zero(qq), True{}, True{}), at, adc_zero_carry(qq, at))
          %lc : {1n+Nat.double(Word.to_nat(qq, _)) == 1n+Nat.double(Word.to_nat(qq, at)) : Nat}
          {==}
        case WCon{False{}, +at}:
          ih = adc_zero_borrow(qq, at, fin_ff(Word.cmp(qq, at, Word.zero(qq)), h_nz))
          %ih : {2n+Nat.double(Word.to_nat(qq, Word.adc(qq, at, Word.zero(qq), True{}, False{})))
            == Nat.double(_) : Nat}
          {==}

# one less than a nonzero U32, as a Nat
law u32_dec:
  for +uu: U32
  for h_nz: {U32.is_zero(uu) == False{} : Bool}
  {U32.to_nat(uu) == 1n+U32.to_nat(U32.sub(uu, 1)) : Nat}

# the proof of u32_dec
def u32_dec(uu, h_nz):
  match uu:
    case U32{WCon{True{}, +at}}:
      lc = Equal.sym(Word(31n), Word.adc(31n, at, Word.zero(31n), True{}, True{}), at, adc_zero_carry(31n, at))
      %lc : {1n+Nat.double(Word.to_nat(31n, at)) == 1n+Nat.double(Word.to_nat(31n, _)) : Nat}
      {==}
    case U32{WCon{False{}, +at}}:
      ih = adc_zero_borrow(31n, at, fin_ff(Word.cmp(31n, at, Word.zero(31n)), h_nz))
      %ih : {Nat.double(_)
        == 2n+Nat.double(Word.to_nat(31n, Word.adc(31n, at, Word.zero(31n), True{}, False{}))) : Nat}
      {==}

# adding the carry then taking it back, from the lowest bit up, is nothing
law adc_inc_dec:
  for +qq: Nat
  for +aw: Word(qq)
  for cc: Bool
  {Word.adc(qq, Word.adc(qq, aw, Word.zero(qq), False{}, cc), Word.zero(qq), True{}, Bool.not(cc)) == aw : Word(qq)}

# the proof of adc_inc_dec
def adc_inc_dec(qq, aw, cc):
  match qq:
    case 0n:
      match aw:
        case WNil{}:
          {==}
    case 1n+(+pp):
      match aw cc:
        case WCon{False{}, +at} False{}:
          Equal.cong(Word(pp), Word.Con<pp>, ww => WCon{False{}, ww},
            Word.adc(pp, Word.adc(pp, at, Word.zero(pp), False{}, False{}), Word.zero(pp), True{}, True{}), at,
            adc_inc_dec(pp, at, False{}))
        case WCon{True{}, +at} False{}:
          Equal.cong(Word(pp), Word.Con<pp>, ww => WCon{True{}, ww},
            Word.adc(pp, Word.adc(pp, at, Word.zero(pp), False{}, False{}), Word.zero(pp), True{}, True{}), at,
            adc_inc_dec(pp, at, False{}))
        case WCon{False{}, +at} True{}:
          Equal.cong(Word(pp), Word.Con<pp>, ww => WCon{False{}, ww},
            Word.adc(pp, Word.adc(pp, at, Word.zero(pp), False{}, False{}), Word.zero(pp), True{}, True{}), at,
            adc_inc_dec(pp, at, False{}))
        case WCon{True{}, +at} True{}:
          Equal.cong(Word(pp), Word.Con<pp>, ww => WCon{True{}, ww},
            Word.adc(pp, Word.adc(pp, at, Word.zero(pp), False{}, True{}), Word.zero(pp), True{}, False{}), at,
            adc_inc_dec(pp, at, True{}))

# one more then one less is the same U32
law u32_dec_inc:
  for +uu: U32
  {U32.sub(U32.add(uu, 1), 1) == uu : U32}

# the proof of u32_dec_inc
def u32_dec_inc(uu):
  match uu:
    case U32{WCon{False{}, +at}}:
      Equal.cong(Word(31n), U32, ww => U32{WCon{False{}, ww}},
        Word.adc(31n, Word.adc(31n, at, Word.zero(31n), False{}, False{}), Word.zero(31n), True{}, True{}), at,
        adc_inc_dec(31n, at, False{}))
    case U32{WCon{True{}, +at}}:
      Equal.cong(Word(31n), U32, ww => U32{WCon{True{}, ww}},
        Word.adc(31n, Word.adc(31n, at, Word.zero(31n), False{}, True{}), Word.zero(31n), True{}, False{}), at,
        adc_inc_dec(31n, at, True{}))

# adding one more on the right
law nat_add_succ:
  for +aa: Nat
  for +bb: Nat
  {Nat.add(aa, 1n+bb) == 1n+Nat.add(aa, bb) : Nat}

# the proof of nat_add_succ
def nat_add_succ(aa, bb):
  match aa:
    case 0n:
      {==}
    case 1n+(+pp):
      Equal.cong(Nat, Nat, xx => 1n+xx, Nat.add(pp, 1n+bb), 1n+Nat.add(pp, bb), nat_add_succ(pp, bb))

# a bit as a Nat
def bit_nat(bb: Bool) -> Nat:
  match bb:
    case False{}:
      0n
    case True{}:
      1n

# comparing a bit and twice a Nat: the rest decides, the bit breaks a tie
law nat_cmp_bits:
  for +aa: Nat
  for +bb: Nat
  for xx: Bool
  for yy: Bool
  {Nat.cmp(Nat.add(bit_nat(xx), Nat.double(aa)), Nat.add(bit_nat(yy), Nat.double(bb))) ==
    Word.cmp.fin(xx, yy, Nat.cmp(aa, bb)) : Cmp}

# the proof of nat_cmp_bits
def nat_cmp_bits(aa, bb, xx, yy):
  match aa bb:
    case 0n 0n:
      match xx yy:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}
    case 1n+(+ap) 0n:
      match xx yy:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}
    case 0n 1n+(+bp):
      match xx yy:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}
    case 1n+(+ap) 1n+(+bp):
      match xx yy:
        case False{} False{}:
          nat_cmp_bits(ap, bp, False{}, False{})
        case False{} True{}:
          nat_cmp_bits(ap, bp, False{}, True{})
        case True{} False{}:
          nat_cmp_bits(ap, bp, True{}, False{})
        case True{} True{}:
          nat_cmp_bits(ap, bp, True{}, True{})

# words compare as the Nats they are
law w_cmp:
  for +nn: Nat
  for aa: Word(nn)
  for bb: Word(nn)
  {Word.cmp(nn, aa, bb) == Nat.cmp(Word.to_nat(nn, aa), Word.to_nat(nn, bb)) : Cmp}

# the proof of w_cmp
def w_cmp(nn, aa, bb):
  match nn:
    case 0n:
      match aa bb:
        case WNil{} WNil{}:
          {==}
    case 1n+(+pp):
      match aa bb:
        case WCon{False{}, +at} WCon{False{}, +bt}:
          Equal.trans(Cmp, Word.cmp.fin(False{}, False{}, Word.cmp(pp, at, bt)), Word.cmp.fin(False{}, False{},
            Nat.cmp(Word.to_nat(pp, at), Word.to_nat(pp, bt))),
            Nat.cmp(Nat.add(bit_nat(False{}), Nat.double(Word.to_nat(pp, at))), Nat.add(bit_nat(False{}),
              Nat.double(Word.to_nat(pp, bt)))),
            Equal.cong(Cmp, Cmp, zz => Word.cmp.fin(False{}, False{}, zz), Word.cmp(pp, at, bt),
              Nat.cmp(Word.to_nat(pp, at), Word.to_nat(pp, bt)),
              w_cmp(pp, at, bt)),
            Equal.sym(Cmp, Nat.cmp(Nat.add(bit_nat(False{}), Nat.double(Word.to_nat(pp, at))),
              Nat.add(bit_nat(False{}), Nat.double(Word.to_nat(pp, bt)))),
              Word.cmp.fin(False{}, False{}, Nat.cmp(Word.to_nat(pp, at), Word.to_nat(pp, bt))),
                nat_cmp_bits(Word.to_nat(pp, at), Word.to_nat(pp, bt), False{}, False{})))
        case WCon{False{}, +at} WCon{True{}, +bt}:
          Equal.trans(Cmp, Word.cmp.fin(False{}, True{}, Word.cmp(pp, at, bt)), Word.cmp.fin(False{}, True{},
            Nat.cmp(Word.to_nat(pp, at), Word.to_nat(pp, bt))),
            Nat.cmp(Nat.add(bit_nat(False{}), Nat.double(Word.to_nat(pp, at))), Nat.add(bit_nat(True{}),
              Nat.double(Word.to_nat(pp, bt)))),
            Equal.cong(Cmp, Cmp, zz => Word.cmp.fin(False{}, True{}, zz), Word.cmp(pp, at, bt), Nat.cmp(Word.to_nat(pp,
              at), Word.to_nat(pp, bt)),
              w_cmp(pp, at, bt)),
            Equal.sym(Cmp, Nat.cmp(Nat.add(bit_nat(False{}), Nat.double(Word.to_nat(pp, at))), Nat.add(bit_nat(True{}),
              Nat.double(Word.to_nat(pp, bt)))),
              Word.cmp.fin(False{}, True{}, Nat.cmp(Word.to_nat(pp, at), Word.to_nat(pp, bt))),
                nat_cmp_bits(Word.to_nat(pp, at), Word.to_nat(pp, bt), False{}, True{})))
        case WCon{True{}, +at} WCon{False{}, +bt}:
          Equal.trans(Cmp, Word.cmp.fin(True{}, False{}, Word.cmp(pp, at, bt)), Word.cmp.fin(True{}, False{},
            Nat.cmp(Word.to_nat(pp, at), Word.to_nat(pp, bt))),
            Nat.cmp(Nat.add(bit_nat(True{}), Nat.double(Word.to_nat(pp, at))), Nat.add(bit_nat(False{}),
              Nat.double(Word.to_nat(pp, bt)))),
            Equal.cong(Cmp, Cmp, zz => Word.cmp.fin(True{}, False{}, zz), Word.cmp(pp, at, bt), Nat.cmp(Word.to_nat(pp,
              at), Word.to_nat(pp, bt)),
              w_cmp(pp, at, bt)),
            Equal.sym(Cmp, Nat.cmp(Nat.add(bit_nat(True{}), Nat.double(Word.to_nat(pp, at))), Nat.add(bit_nat(False{}),
              Nat.double(Word.to_nat(pp, bt)))),
              Word.cmp.fin(True{}, False{}, Nat.cmp(Word.to_nat(pp, at), Word.to_nat(pp, bt))),
                nat_cmp_bits(Word.to_nat(pp, at), Word.to_nat(pp, bt), True{}, False{})))
        case WCon{True{}, +at} WCon{True{}, +bt}:
          Equal.trans(Cmp, Word.cmp.fin(True{}, True{}, Word.cmp(pp, at, bt)), Word.cmp.fin(True{}, True{},
            Nat.cmp(Word.to_nat(pp, at), Word.to_nat(pp, bt))),
            Nat.cmp(Nat.add(bit_nat(True{}), Nat.double(Word.to_nat(pp, at))), Nat.add(bit_nat(True{}),
              Nat.double(Word.to_nat(pp, bt)))),
            Equal.cong(Cmp, Cmp, zz => Word.cmp.fin(True{}, True{}, zz), Word.cmp(pp, at, bt), Nat.cmp(Word.to_nat(pp,
              at), Word.to_nat(pp, bt)),
              w_cmp(pp, at, bt)),
            Equal.sym(Cmp, Nat.cmp(Nat.add(bit_nat(True{}), Nat.double(Word.to_nat(pp, at))), Nat.add(bit_nat(True{}),
              Nat.double(Word.to_nat(pp, bt)))),
              Word.cmp.fin(True{}, True{}, Nat.cmp(Word.to_nat(pp, at), Word.to_nat(pp, bt))),
                nat_cmp_bits(Word.to_nat(pp, at), Word.to_nat(pp, bt), True{}, True{})))

# U32s compare as the Nats they are
law u_cmp:
  for aa: U32
  for bb: U32
  {U32.cmp(aa, bb) == Nat.cmp(U32.to_nat(aa), U32.to_nat(bb)) : Cmp}

# the proof of u_cmp
def u_cmp(aa, bb):
  match aa bb:
    case U32{xw} U32{yw}:
      w_cmp(32n, xw, yw)

# adding 0 on the right
def nat_add_zero(+aa: Nat) -> {Nat.add(aa, 0n) == aa : Nat}:
  match aa:
    case 0n:
      {==}
    case 1n+(+pp):
      Equal.cong(Nat, Nat, xx => 1n+xx, Nat.add(pp, 0n), pp, nat_add_zero(pp))

# the Type a Nat names for telling 0 from a successor: Unit for 0
def zs_ty(nn: Nat) -> Type:
  match nn:
    case 0n:
      Unit
    case 1n+_pp:
      Empty

# 0 is no successor
def zero_succ(kk: Nat, ee: {0n == 1n+kk : Nat}) -> Empty:
  %ee : zs_ty(_)
  Unit{}

# one less, or zero
def pred(nn: Nat) -> Nat:
  match nn:
    case 0n:
      0n
    case 1n+pp:
      pp

# a Nat is at most itself plus more
def nle_add(+aa: Nat, +bb: Nat) -> {Nat.is_le(aa, Nat.add(aa, bb)) == True{} : Bool}:
  match aa bb:
    case 0n 0n:
      {==}
    case 0n 1n+_bp:
      {==}
    case 1n+(+ap) _bb:
      nle_add(ap, bb)

# at most is transitive
def nle_trans(
  +aa: Nat,
  +bb: Nat,
  +cc: Nat,
  h_ab: {Nat.is_le(aa, bb) == True{} : Bool},
  h_bc: {Nat.is_le(bb, cc) == True{} : Bool}
) -> {Nat.is_le(aa, cc) == True{} : Bool}:
  match aa bb cc:
    case 0n _bb 0n:
      {==}
    case 0n _bb 1n+_cp:
      {==}
    case 1n+_ap 0n _cc:
      Empty.absurd({Nat.is_le(aa, cc) == True{} : Bool}, U32L.false_true(h_ab))
    case 1n+_ap 1n+_bp 0n:
      Empty.absurd({Nat.is_le(aa, 0n) == True{} : Bool}, U32L.false_true(h_bc))
    case 1n+(+ap) 1n+(+bp) 1n+(+cp):
      nle_trans(ap, bp, cp, h_ab, h_bc)

# a sum with a successor on the right is at most n: its left addend is below n
def nlt_add(
  +aa: Nat,
  +bb: Nat,
  +nn: Nat,
  h_le: {Nat.is_le(Nat.add(aa, 1n+bb), nn) == True{} : Bool}
) -> {Nat.is_lt(aa, nn) == True{} : Bool}:
  match aa nn:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, U32L.false_true(h_le))
    case 0n 1n+_np:
      {==}
    case 1n+_ap 0n:
      Empty.absurd({Nat.is_lt(aa, 0n) == True{} : Bool}, U32L.false_true(h_le))
    case 1n+(+ap) 1n+(+np):
      nlt_add(ap, bb, np, h_le)

# the word of all ones
def ones(nn: Nat) -> Word(nn):
  match nn:
    case 0n:
      WNil{}
    case 1n+pp:
      WCon{True{}, ones(pp)}

# one bit of ones_nlt: the rest given, as cc
def ones_nlt.at(
  cc: Cmp,
  bb: Bool,
  ih: {cc == LT{} : Cmp} -> Empty,
  ee: {Word.cmp.fin(True{}, bb, cc) == LT{} : Cmp}
) -> Empty:
  match cc:
    case LT{}:
      ih({==})
    case GT{}:
      %ee : lt_ty(_)
      Unit{}
    case EQ{}:
      match bb:
        case False{}:
          %ee : lt_ty(_)
          Unit{}
        case True{}:
          %ee : lt_ty(_)
          Unit{}

# no word is above all ones
def ones_nlt(nn: Nat, ww: Word(nn), ee: {Word.cmp(nn, ones(nn), ww) == LT{} : Cmp}) -> Empty:
  match nn:
    case 0n:
      match ww:
        case WNil{}:
          %ee : lt_ty(_)
          Unit{}
    case 1n+(+pp):
      match ww:
        case WCon{bb, +tt}:
          ones_nlt.at(Word.cmp(pp, ones(pp), tt), bb, xx => ones_nlt(pp, tt, xx), ee)

# the top U32, compared with a word, once the comparison is named cc
def top_nlt.at(
  cc: Cmp,
  ww: Word(32n),
  ec: {Word.cmp(32n, ones(32n), ww) == cc : Cmp}
) -> {Cmp.is_lt(cc) == False{} : Bool}:
  match cc:
    case LT{}:
      Empty.absurd({True{} == False{} : Bool}, ones_nlt(32n, ww, ec))
    case EQ{}:
      {==}
    case GT{}:
      {==}

# the top U32, 0 - 1, is below nothing
def top_nlt(+cap: U32) -> {U32.is_lt(U32.sub(0, 1), cap) == False{} : Bool}:
  match cap:
    case U32{+ww}:
      top_nlt.at(Word.cmp(32n, ones(32n), ww), ww, {==})

# a U32 below cap plus one, as a Nat, once whether the sum is zero is named zz
def inc_nat.at(
  +aa: U32,
  +cap: U32,
  zz: Bool,
  ez: {U32.is_zero(U32.add(aa, 1)) == zz : Bool},
  h_lt: {U32.is_lt(aa, cap) == True{} : Bool}
) -> {U32.to_nat(U32.add(aa, 1)) == 1n+U32.to_nat(aa) : Nat}:
  match zz:
    case False{}:
      Equal.trans(Nat, U32.to_nat(U32.add(aa, 1)), 1n+U32.to_nat(U32.sub(U32.add(aa, 1), 1)), 1n+U32.to_nat(aa),
        u32_dec(U32.add(aa, 1), ez),
        Equal.cong(U32, Nat, uu => 1n+U32.to_nat(uu), U32.sub(U32.add(aa, 1), 1), aa, u32_dec_inc(aa)))
    case True{}:
      e0 = U32L.ueq(U32.add(aa, 1), 0, ez)
      back = Equal.sym(U32, U32.sub(U32.add(aa, 1), 1), aa, u32_dec_inc(aa))
      down = Equal.cong(U32, U32, xx => U32.sub(xx, 1), U32.add(aa, 1), 0, e0)
      at_top = Equal.trans(U32, aa, U32.sub(U32.add(aa, 1), 1), U32.sub(0, 1), back, down)
      top = Equal.cong(U32, Bool, xx => U32.is_lt(xx, cap), aa, U32.sub(0, 1), at_top)
      Empty.absurd({U32.to_nat(U32.add(aa, 1)) == 1n+U32.to_nat(aa) : Nat}, true_false(Equal.trans(Bool, True{},
        U32.is_lt(U32.sub(0, 1), cap), False{},
        Equal.trans(Bool, True{}, U32.is_lt(aa, cap), U32.is_lt(U32.sub(0, 1), cap), Equal.sym(Bool,
          U32.is_lt(aa, cap), True{}, h_lt), top), top_nlt(cap))))

# a U32 below cap plus one, as a Nat
def inc_nat(
  +aa: U32,
  +cap: U32,
  h_lt: {U32.is_lt(aa, cap) == True{} : Bool}
) -> {U32.to_nat(U32.add(aa, 1)) == 1n+U32.to_nat(aa) : Nat}:
  inc_nat.at(aa, cap, U32.is_zero(U32.add(aa, 1)), {==}, h_lt)

# a U32 is below cap when its Nat is
def u_lt(
  +aa: U32,
  +cap: U32,
  h_lt: {Nat.is_lt(U32.to_nat(aa), U32.to_nat(cap)) == True{} : Bool}
) -> {U32.is_lt(aa, cap) == True{} : Bool}:
  Equal.trans(Bool, U32.is_lt(aa, cap), Nat.is_lt(U32.to_nat(aa), U32.to_nat(cap)), True{},
    Equal.cong(Cmp, Bool, cc => Cmp.is_lt(cc), U32.cmp(aa, cap), Nat.cmp(U32.to_nat(aa), U32.to_nat(cap)),
      u_cmp(aa, cap)), h_lt)

# U32 at-most is Nat at-most
def u_le(+aa: U32, +bb: U32) -> {U32.is_le(aa, bb) == Nat.is_le(U32.to_nat(aa), U32.to_nat(bb)) : Bool}:
  Equal.cong(Cmp, Bool, cc => Cmp.is_le(cc), U32.cmp(aa, bb), Nat.cmp(U32.to_nat(aa), U32.to_nat(bb)), u_cmp(aa, bb))

# U32 at-most is transitive
def u_le_trans(
  +aa: U32,
  +bb: U32,
  +cc: U32,
  h_ab: {U32.is_le(aa, bb) == True{} : Bool},
  h_bc: {U32.is_le(bb, cc) == True{} : Bool}
) -> {U32.is_le(aa, cc) == True{} : Bool}:
  Equal.trans(Bool, U32.is_le(aa, cc), Nat.is_le(U32.to_nat(aa), U32.to_nat(cc)), True{}, u_le(aa, cc),
    nle_trans(U32.to_nat(aa), U32.to_nat(bb), U32.to_nat(cc),
      Equal.trans(Bool, Nat.is_le(U32.to_nat(aa), U32.to_nat(bb)), U32.is_le(aa, bb), True{}, Equal.sym(Bool,
        U32.is_le(aa, bb), Nat.is_le(U32.to_nat(aa), U32.to_nat(bb)), u_le(aa, bb)), h_ab),
      Equal.trans(Bool, Nat.is_le(U32.to_nat(bb), U32.to_nat(cc)), U32.is_le(bb, cc), True{}, Equal.sym(Bool,
        U32.is_le(bb, cc), Nat.is_le(U32.to_nat(bb), U32.to_nat(cc)), u_le(bb, cc)), h_bc)))

# counting xs up from aa, as a Nat, when the sum stays within cap
def up(
  +xs: List<&2, U32>,
  +aa: U32,
  +cap: U32,
  +h_le: {Nat.is_le(Nat.add(U32.to_nat(aa), List.length(&2, U32, xs)), U32.to_nat(cap)) == True{} : Bool}
) -> {U32.to_nat(Png.enc.len(xs, aa)) == Nat.add(U32.to_nat(aa), List.length(&2, U32, xs)) : Nat}:
  match xs:
    case Nil{}:
      Equal.sym(Nat, Nat.add(U32.to_nat(aa), 0n), U32.to_nat(aa), nat_add_zero(U32.to_nat(aa)))
    case _hd <> +tl:
      +xx = U32.to_nat(aa)
      +nt = List.length(&2, U32, tl)
      +a1 = U32.add(aa, 1)
      +inc = inc_nat(aa, cap, u_lt(aa, cap, nlt_add(xx, nt, U32.to_nat(cap), h_le)))
      +sw = Equal.trans(Nat, Nat.add(xx, 1n+nt), 1n+Nat.add(xx, nt), Nat.add(U32.to_nat(a1), nt), nat_add_succ(xx, nt),
        Equal.cong(Nat, Nat, yy => Nat.add(yy, nt), 1n+xx, U32.to_nat(a1), Equal.sym(Nat, U32.to_nat(a1), 1n+xx, inc)))
      +h2 = Equal.trans(Bool, Nat.is_le(Nat.add(U32.to_nat(a1), nt), U32.to_nat(cap)), Nat.is_le(Nat.add(xx, 1n+nt),
        U32.to_nat(cap)), True{}, Equal.cong(Nat, Bool, yy => Nat.is_le(yy, U32.to_nat(cap)), Nat.add(U32.to_nat(a1),
        nt), Nat.add(xx, 1n+nt), Equal.sym(Nat, Nat.add(xx, 1n+nt), Nat.add(U32.to_nat(a1), nt), sw)), h_le)
      Equal.trans(Nat, U32.to_nat(Png.enc.len(tl, a1)), Nat.add(U32.to_nat(a1), nt), Nat.add(xx, 1n+nt),
        up(tl, a1, cap, h2), Equal.sym(Nat, Nat.add(xx, 1n+nt), Nat.add(U32.to_nat(a1), nt), sw))

# a count whose Nat is the length runs down to zero exactly over xs
def ncnt(
  +xs: List<&2, U32>,
  +nn: U32,
  zz: Bool,
  ez: {U32.is_zero(nn) == zz : Bool},
  h_n: {U32.to_nat(nn) == List.length(&2, U32, xs) : Nat}
) -> {cnt(xs, zz, nn) == True{} : Bool}:
  match xs zz:
    case Nil{} True{}:
      {==}
    case Nil{} False{}:
      Empty.absurd({False{} == True{} : Bool}, zero_succ(U32.to_nat(U32.sub(nn, 1)), Equal.trans(Nat, 0n,
        U32.to_nat(nn), 1n+U32.to_nat(U32.sub(nn, 1)), Equal.sym(Nat, U32.to_nat(nn), 0n, h_n), u32_dec(nn, ez))))
    case _hd <> +tl True{}:
      e0 = Equal.cong(U32, Nat, uu => U32.to_nat(uu), nn, 0, U32L.ueq(nn, 0, ez))
      Empty.absurd({False{} == True{} : Bool}, zero_succ(List.length(&2, U32, tl), Equal.trans(Nat, 0n, U32.to_nat(nn),
        1n+List.length(&2, U32, tl), Equal.sym(Nat, U32.to_nat(nn), 0n, e0), h_n)))
    case _hd <> +tl False{}:
      +n1 = U32.sub(nn, 1)
      e1 = Equal.trans(Nat, 1n+U32.to_nat(n1), U32.to_nat(nn), 1n+List.length(&2, U32, tl), Equal.sym(Nat,
        U32.to_nat(nn), 1n+U32.to_nat(n1), u32_dec(nn, ez)), h_n)
      ncnt(tl, n1, U32.is_zero(n1), {==}, Equal.cong(Nat, Nat, kk => pred(kk), 1n+U32.to_nat(n1),
        1n+List.length(&2, U32, tl), e1))

# a block of at most sz bytes, sz at most 65535: its LEN, counted by enc.len,
# keeps its low 16 bits, and those run down to zero exactly over the block
def blk_cnt(
  +xs: List<&2, U32>,
  +sz: U32,
  +h_len: {Nat.is_le(List.length(&2, U32, xs), U32.to_nat(sz)) == True{} : Bool},
  h_sz: {U32.is_le(sz, 65535) == True{} : Bool}
) -> {cnt(xs, U32.is_zero(U32.and(65535, Png.enc.len(xs, 0))), U32.and(65535, Png.enc.len(xs, 0))) == True{} :
  Bool}:
  +ll = Png.enc.len(xs, 0)
  +nl = up(xs, 0, sz, h_len)
  +h_ls = Equal.trans(Bool, U32.is_le(ll, sz), Nat.is_le(U32.to_nat(ll), U32.to_nat(sz)), True{}, u_le(ll, sz),
    Equal.trans(Bool, Nat.is_le(U32.to_nat(ll), U32.to_nat(sz)), Nat.is_le(List.length(&2, U32, xs), U32.to_nat(sz)),
      True{}, Equal.cong(Nat, Bool, kk => Nat.is_le(kk, U32.to_nat(sz)), U32.to_nat(ll), List.length(&2, U32, xs),
      nl), h_len))
  +em = mask16(ll, u_le_trans(ll, sz, 65535, h_ls, h_sz))
  Equal.trans(Bool, cnt(xs, U32.is_zero(U32.and(65535, ll)), U32.and(65535, ll)), cnt(xs, U32.is_zero(ll), ll), True{},
    Equal.cong(U32, Bool, vv => cnt(xs, U32.is_zero(vv), vv), U32.and(65535, ll), ll, em),
    ncnt(xs, ll, U32.is_zero(ll), {==}, nl))

# ---- D. the encoder's stored blocks ----

# enc.cat.go is List.reverse.go
def catgo_rev(
  +xs: List<&2, U32>,
  +ys: List<&2, U32>
) -> {Png.enc.cat.go(xs, ys) == List.reverse.go(&2, U32, xs, ys) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case +hd <> +tl:
      catgo_rev(tl, hd <> ys)

# reversing onto acc, then reversing that onto ys: acc reversed onto xs then ys
def revrev(
  +xs: List<&2, U32>,
  +acc: List<&2, U32>,
  +ys: List<&2, U32>
) -> {List.reverse.go(&2, U32, List.reverse.go(&2, U32, xs, acc), ys) == List.reverse.go(&2, U32, acc, List.append(&2,
  U32, xs, ys)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case +hd <> +tl:
      revrev(tl, hd <> acc, ys)

# enc.cat is List.append
def cat_app(
  +xs: List<&2, U32>,
  +ys: List<&2, U32>
) -> {Png.enc.cat(xs, ys) == List.append(&2, U32, xs, ys) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, Png.enc.cat(xs, ys), List.reverse.go(&2, U32, List.reverse(&2, U32, xs), ys),
    List.append(&2, U32, xs, ys), catgo_rev(List.reverse(&2, U32, xs), ys), revrev(xs, [], ys))

# a list reversed, reversed onto out: the list, then out
def rr(
  +xs: List<&2, U32>,
  +out: List<&2, U32>
) -> {List.reverse.go(&2, U32, List.reverse(&2, U32, xs), out) == List.append(&2, U32, xs, out) : List<&2, U32>}:
  revrev(xs, [], out)

# appending nothing
def app_nil(+xs: List<&2, U32>) -> {List.append(&2, U32, xs, []) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case +hd <> +tl:
      Equal.cong(List<&2, U32>, List<&2, U32>, ll => hd <> ll, List.append(&2, U32, tl, []), tl, app_nil(tl))

# append associates
def app_assoc(
  +aa: List<&2, U32>,
  +bb: List<&2, U32>,
  +cc: List<&2, U32>
) -> {List.append(&2, U32, List.append(&2, U32, aa, bb), cc) == List.append(&2, U32, aa, List.append(&2, U32, bb, cc)) :
  List<&2, U32>}:
  match aa:
    case Nil{}:
      {==}
    case +hd <> +tl:
      Equal.cong(List<&2, U32>, List<&2, U32>, ll => hd <> ll, List.append(&2, U32, List.append(&2, U32, tl, bb), cc),
        List.append(&2, U32, tl, List.append(&2, U32, bb, cc)), app_assoc(tl, bb, cc))

# a list reversed onto out is as long as both
def len_revgo(
  +xs: List<&2, U32>,
  +out: List<&2, U32>
) -> {List.length(&2, U32, List.reverse.go(&2, U32, xs, out)) == Nat.add(List.length(&2, U32, xs), List.length(&2, U32,
  out)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +hd <> +tl:
      Equal.trans(Nat, List.length(&2, U32, List.reverse.go(&2, U32, tl, hd <> out)), Nat.add(List.length(&2, U32, tl),
        1n+List.length(&2, U32, out)), 1n+Nat.add(List.length(&2, U32, tl), List.length(&2, U32, out)),
        len_revgo(tl, hd <> out), nat_add_succ(List.length(&2, U32, tl), List.length(&2, U32, out)))

# a list reversed is as long
def len_rev(
  +xs: List<&2, U32>
) -> {List.length(&2, U32, List.reverse(&2, U32, xs)) == List.length(&2, U32, xs) : Nat}:
  Equal.trans(Nat, List.length(&2, U32, List.reverse(&2, U32, xs)), Nat.add(List.length(&2, U32, xs), 0n),
    List.length(&2, U32, xs), len_revgo(xs, []), nat_add_zero(List.length(&2, U32, xs)))

# bytes reversed onto bytes are bytes
def bytes_revgo(
  +xs: List<&2, U32>,
  +out: List<&2, U32>,
  +h_xs: {Laws.bytes.go(xs, True{}) == True{} : Bool},
  h_out: {Laws.bytes.go(out, True{}) == True{} : Bool}
) -> {Laws.bytes.go(List.reverse.go(&2, U32, xs, out), True{}) == True{} : Bool}:
  match xs:
    case Nil{}:
      h_out
    case +hd <> +tl:
      +eh = bytes.ok(tl, U32.is_le(hd, 255), h_xs)
      bytes_revgo(tl, hd <> out, bytes.tail(tl, U32.is_le(hd, 255), h_xs), Equal.trans(Bool, Laws.bytes.go(out,
        U32.is_le(hd, 255)), Laws.bytes.go(out, True{}), True{}, Equal.cong(Bool, Bool, bb => Laws.bytes.go(out, bb),
        U32.is_le(hd, 255), True{}, eh), h_out))

# one stored block as enc.stored writes it, of at most sz bytes: the reader copies it
def st_blk(
  +fin: Bool,
  +xs: List<&2, U32>,
  +rest: List<&2, U32>,
  +left: U32,
  +out: List<&2, U32>,
  +sz: U32,
  h_len: {Nat.is_le(List.length(&2, U32, xs), U32.to_nat(sz)) == True{} : Bool},
  h_sz: {U32.is_le(sz, 65535) == True{} : Bool},
  h_by: {Laws.bytes.go(xs, True{}) == True{} : Bool}
) -> {run.bytes(List.append(&2, U32, Png.enc.stored(fin, xs), rest), st.blk(left, out)) == run.bytes(rest,
  st.after(fin, cd(xs, U32.and(65535, Png.enc.len(xs, 0))), List.reverse.go(&2, U32, xs, out))) :
  Maybe<&2, List<&2, U32>>}:
  +ll = Png.enc.len(xs, 0)
  +hd = Png.enc.head(fin, ll, U32.xor(ll, 65535))
  Equal.trans(Maybe<&2, List<&2, U32>>, run.bytes(List.append(&2, U32, Png.enc.cat(hd, xs), rest), st.blk(left, out)),
    run.bytes(List.append(&2, U32, List.append(&2, U32, hd, xs), rest), st.blk(left, out)),
    run.bytes(rest, st.after(fin, cd(xs, U32.and(65535, ll)), List.reverse.go(&2, U32, xs, out))),
    Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, bs => run.bytes(List.append(&2, U32, bs, rest), st.blk(left,
      out)), Png.enc.cat(hd, xs), List.append(&2, U32, hd, xs), cat_app(hd, xs)),
    blk(fin, ll, xs, rest, left, out, blk_cnt(xs, sz, h_len, h_sz), h_by))

# the open block, as the invariant counts it, is at most sz bytes
def acc_len(
  +acc: List<&2, U32>,
  +room: U32,
  +sz: U32,
  inv: {Nat.add(List.length(&2, U32, acc), U32.to_nat(room)) == U32.to_nat(sz) : Nat}
) -> {Nat.is_le(List.length(&2, U32, List.reverse(&2, U32, acc)), U32.to_nat(sz)) == True{} : Bool}:
  +na = List.length(&2, U32, acc)
  +le = Equal.trans(Bool, Nat.is_le(na, U32.to_nat(sz)), Nat.is_le(na, Nat.add(na, U32.to_nat(room))), True{},
    Equal.cong(Nat, Bool, kk => Nat.is_le(na, kk), U32.to_nat(sz), Nat.add(na, U32.to_nat(room)), Equal.sym(Nat,
      Nat.add(na, U32.to_nat(room)), U32.to_nat(sz), inv)), nle_add(na, U32.to_nat(room)))
  Equal.trans(Bool, Nat.is_le(List.length(&2, U32, List.reverse(&2, U32, acc)), U32.to_nat(sz)), Nat.is_le(na,
    U32.to_nat(sz)), True{}, Equal.cong(Nat, Bool, kk => Nat.is_le(kk, U32.to_nat(sz)), List.length(&2, U32,
    List.reverse(&2, U32, acc)), na, len_rev(acc)), le)

# enc.feed's blocks, the open block `acc` first (newest first, `room` bytes
# still free in it): the reader copies them all and reaches the Adler field
def fl(
  +xs: List<&2, U32>,
  +zz: Bool,
  +room: U32,
  +sz: U32,
  +acc: List<&2, U32>,
  +rest: List<&2, U32>,
  +left: U32,
  +out: List<&2, U32>,
  ez: {U32.is_zero(room) == zz : Bool},
  +inv: {Nat.add(List.length(&2, U32, acc), U32.to_nat(room)) == U32.to_nat(sz) : Nat},
  +h_nz: {U32.is_zero(sz) == False{} : Bool},
  +h_sz: {U32.is_le(sz, 65535) == True{} : Bool},
  +h_bx: {Laws.bytes.go(xs, True{}) == True{} : Bool},
  +h_ba: {Laws.bytes.go(acc, True{}) == True{} : Bool}
) -> {run.bytes(List.append(&2, U32, Png.enc.feed(xs, zz, room, sz, acc), rest), st.blk(left, out)) ==
  run.bytes(rest, st.adler(List.reverse.go(&2, U32, xs, List.reverse.go(&2, U32, List.reverse(&2, U32, acc), out)))) :
  Maybe<&2, List<&2, U32>>}:
  match xs zz:
    case Nil{} _zz:
      +ra = List.reverse(&2, U32, acc)
      +o1 = List.reverse.go(&2, U32, ra, out)
      +c1 = cd(ra, U32.and(65535, Png.enc.len(ra, 0)))
      +h_bra = bytes_revgo(acc, [], h_ba, {==})
      Equal.trans(Maybe<&2, List<&2, U32>>, run.bytes(List.append(&2, U32, Png.enc.stored(True{}, ra), rest),
        st.blk(left, out)), run.bytes(rest, st.after(True{}, c1, o1)), run.bytes(rest, st.adler(o1)),
        st_blk(True{}, ra, rest, left, out, sz, acc_len(acc, room, sz, inv), h_sz, h_bra),
        after_last(c1, o1, rest))
    case +hd <> +tl True{}:
      +ra = List.reverse(&2, U32, acc)
      +o1 = List.reverse.go(&2, U32, ra, out)
      +c1 = cd(ra, U32.and(65535, Png.enc.len(ra, 0)))
      +h_bra = bytes_revgo(acc, [], h_ba, {==})
      +s1 = (sz - 1 : U32)
      +bs = Png.enc.stored(False{}, ra)
      +ff = Png.enc.feed(tl, U32.is_zero(s1), s1, sz, [hd])
      +e_hd = bytes.ok(tl, U32.is_le(hd, 255), h_bx)
      Equal.trans(Maybe<&2, List<&2, U32>>, run.bytes(List.append(&2, U32, Png.enc.cat(bs, ff), rest), st.blk(left,
        out)), run.bytes(List.append(&2, U32, List.append(&2, U32, bs, ff), rest), st.blk(left, out)),
        run.bytes(rest, st.adler(List.reverse.go(&2, U32, tl, hd <> o1))),
        Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, ll => run.bytes(List.append(&2, U32, ll, rest), st.blk(left,
          out)), Png.enc.cat(bs, ff), List.append(&2, U32, bs, ff), cat_app(bs, ff)),
        Equal.trans(Maybe<&2, List<&2, U32>>, run.bytes(List.append(&2, U32, List.append(&2, U32, bs, ff), rest),
          st.blk(left, out)), run.bytes(List.append(&2, U32, bs, List.append(&2, U32, ff, rest)), st.blk(left, out)),
          run.bytes(rest, st.adler(List.reverse.go(&2, U32, tl, hd <> o1))),
          Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, ll => run.bytes(ll, st.blk(left, out)),
            List.append(&2, U32, List.append(&2, U32, bs, ff), rest), List.append(&2, U32, bs, List.append(&2, U32, ff,
            rest)), app_assoc(bs, ff, rest)),
          Equal.trans(Maybe<&2, List<&2, U32>>, run.bytes(List.append(&2, U32, bs, List.append(&2, U32, ff, rest)),
            st.blk(left, out)), run.bytes(List.append(&2, U32, ff, rest), st.blk(c1, o1)),
            run.bytes(rest, st.adler(List.reverse.go(&2, U32, tl, hd <> o1))),
            st_blk(False{}, ra, List.append(&2, U32, ff, rest), left, out, sz, acc_len(acc, room, sz, inv), h_sz,
              h_bra),
            fl(tl, U32.is_zero(s1), s1, sz, [hd], rest, c1, o1, {==}, Equal.sym(Nat, U32.to_nat(sz), 1n+U32.to_nat(s1),
              u32_dec(sz, h_nz)), h_nz, h_sz, bytes.tail(tl, U32.is_le(hd, 255), h_bx), Equal.cong(Bool, Bool,
              bb => Laws.bytes.go([], bb), U32.is_le(hd, 255), True{}, e_hd)))))
    case +hd <> +tl False{}:
      +o1 = List.reverse.go(&2, U32, List.reverse(&2, U32, acc), out)
      +r1 = (room - 1 : U32)
      +na = List.length(&2, U32, acc)
      +e_hd = bytes.ok(tl, U32.is_le(hd, 255), h_bx)
      +inv2 = Equal.trans(Nat, 1n+Nat.add(na, U32.to_nat(r1)), Nat.add(na, 1n+U32.to_nat(r1)), U32.to_nat(sz),
        Equal.sym(Nat, Nat.add(na, 1n+U32.to_nat(r1)), 1n+Nat.add(na, U32.to_nat(r1)), nat_add_succ(na,
          U32.to_nat(r1))),
        Equal.trans(Nat, Nat.add(na, 1n+U32.to_nat(r1)), Nat.add(na, U32.to_nat(room)), U32.to_nat(sz),
          Equal.cong(Nat, Nat, kk => Nat.add(na, kk), 1n+U32.to_nat(r1), U32.to_nat(room), Equal.sym(Nat,
            U32.to_nat(room), 1n+U32.to_nat(r1), u32_dec(room, ez))), inv))
      +e_out = Equal.trans(List<&2, U32>, List.reverse.go(&2, U32, List.reverse(&2, U32, hd <> acc), out),
        hd <> List.append(&2, U32, acc, out), hd <> o1, rr(hd <> acc, out),
        Equal.cong(List<&2, U32>, List<&2, U32>, ll => hd <> ll, List.append(&2, U32, acc, out), o1,
          Equal.sym(List<&2, U32>, o1, List.append(&2, U32, acc, out), rr(acc, out))))
      Equal.trans(Maybe<&2, List<&2, U32>>, run.bytes(List.append(&2, U32, Png.enc.feed(tl, U32.is_zero(r1), r1, sz,
        hd <> acc), rest), st.blk(left, out)), run.bytes(rest, st.adler(List.reverse.go(&2, U32, tl,
        List.reverse.go(&2, U32, List.reverse(&2, U32, hd <> acc), out)))),
        run.bytes(rest, st.adler(List.reverse.go(&2, U32, tl, hd <> o1))),
        fl(tl, U32.is_zero(r1), r1, sz, hd <> acc, rest, left, out, {==}, inv2, h_nz, h_sz, bytes.tail(tl,
          U32.is_le(hd, 255), h_bx), Equal.trans(Bool, Laws.bytes.go(acc, U32.is_le(hd, 255)), Laws.bytes.go(acc,
          True{}), True{}, Equal.cong(Bool, Bool, bb => Laws.bytes.go(acc, bb), U32.is_le(hd, 255), True{}, e_hd),
          h_ba)),
        Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, ll => run.bytes(rest, st.adler(List.reverse.go(&2, U32, tl,
          ll))), List.reverse.go(&2, U32, List.reverse(&2, U32, hd <> acc), out), hd <> o1, e_out))

# enc.blocks: one final block when xs fits in sz bytes (zz), enc.feed's blocks
# otherwise; either way the reader copies xs and reaches the Adler field
def bl.at(
  zz: Bool,
  +sz: U32,
  +xs: List<&2, U32>,
  +rest: List<&2, U32>,
  +left: U32,
  +out: List<&2, U32>,
  +ez: {U32.is_le(Png.enc.len(xs, 0), sz) == zz : Bool},
  +h_nz: {U32.is_zero(sz) == False{} : Bool},
  +h_sz: {U32.is_le(sz, 65535) == True{} : Bool},
  +h_bx: {Laws.bytes.go(xs, True{}) == True{} : Bool},
  +h_n: {U32.to_nat(Png.enc.len(xs, 0)) == List.length(&2, U32, xs) : Nat}
) -> {run.bytes(List.append(&2, U32, Png.enc.blocks.fit(zz, sz, Png.enc.len(xs, 0), xs), rest), st.blk(left, out)) ==
  run.bytes(rest, st.adler(List.reverse.go(&2, U32, xs, out))) : Maybe<&2, List<&2, U32>>}:
  match zz:
    case True{}:
      +nn = Png.enc.len(xs, 0)
      +hd = Png.enc.head(True{}, nn, U32.xor(nn, 65535))
      +em = mask16(nn, u_le_trans(nn, sz, 65535, ez, h_sz))
      +hc = Equal.trans(Bool, cnt(xs, U32.is_zero(U32.and(65535, nn)), U32.and(65535, nn)), cnt(xs, U32.is_zero(nn),
        nn), True{}, Equal.cong(U32, Bool, vv => cnt(xs, U32.is_zero(vv), vv), U32.and(65535, nn), nn, em),
        ncnt(xs, nn, U32.is_zero(nn), {==}, h_n))
      Equal.trans(Maybe<&2, List<&2, U32>>, run.bytes(List.append(&2, U32, Png.enc.cat(hd, xs), rest), st.blk(left,
        out)), run.bytes(List.append(&2, U32, List.append(&2, U32, hd, xs), rest), st.blk(left, out)),
        run.bytes(rest, st.adler(List.reverse.go(&2, U32, xs, out))),
        Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, ll => run.bytes(List.append(&2, U32, ll, rest),
          st.blk(left, out)), Png.enc.cat(hd, xs), List.append(&2, U32, hd, xs), cat_app(hd, xs)),
        Equal.trans(Maybe<&2, List<&2, U32>>, run.bytes(List.append(&2, U32, List.append(&2, U32, hd, xs), rest),
          st.blk(left, out)), run.bytes(rest, st.after(True{}, cd(xs, U32.and(65535, nn)), List.reverse.go(&2, U32, xs,
          out))), run.bytes(rest, st.adler(List.reverse.go(&2, U32, xs, out))),
          blk(True{}, nn, xs, rest, left, out, hc, h_bx),
          after_last(cd(xs, U32.and(65535, nn)), List.reverse.go(&2, U32, xs, out), rest)))
    case False{}:
      fl(xs, U32.is_zero(sz), sz, sz, [], rest, left, out, {==}, {==}, h_nz, h_sz, h_bx, {==})

# a size at least 1 is not zero, once whether it is zero is named zz
def sz_nz(
  zz: Bool,
  +sz: U32,
  ez: {U32.is_zero(sz) == zz : Bool},
  h_one: {U32.is_le(1, sz) == True{} : Bool}
) -> {U32.is_zero(sz) == False{} : Bool}:
  match zz:
    case False{}:
      ez
    case True{}:
      e1 = Equal.cong(U32, Bool, xx => U32.is_le(1, xx), sz, 0, U32L.ueq(sz, 0, ez))
      Empty.absurd({U32.is_zero(sz) == False{} : Bool}, true_false(Equal.trans(Bool, True{}, U32.is_le(1, sz),
        U32.is_le(1, 0), Equal.sym(Bool, U32.is_le(1, sz), True{}, h_one), e1)))

# a list reversed onto nothing, reversed again, is the list
def rev_rev(+xs: List<&2, U32>) -> {List.reverse(&2, U32, List.reverse.go(&2, U32, xs, [])) == xs : List<&2, U32>}:
  Equal.trans(List<&2, U32>, List.reverse(&2, U32, List.reverse.go(&2, U32, xs, [])), List.append(&2, U32, xs, []),
    xs, revrev(xs, [], []), app_nil(xs))

# IMG-PNG-7: the zlib stream of xs in stored blocks of sz bytes inflates to xs
def inflate_stored(
  +sz: U32,
  +xs: List<&2, U32>,
  +h_sz: {Bool.and(U32.is_le(1, sz), U32.is_le(sz, 65535)) == True{} : Bool},
  +h_by: {Laws.bytes(xs) == True{} : Bool},
  +h_n: {U32.to_nat(Png.enc.len(xs, 0)) == List.length(&2, U32, xs) : Nat}
) -> {Inf.inflate(Laws.zlib.stored(sz, xs)) == Some{xs} : Maybe<&2, List<&2, U32>>}:
  +h_one = U32L.and_left(U32.is_le(1, sz), U32.is_le(sz, 65535), h_sz)
  +h_top = U32L.and_right(U32.is_le(1, sz), U32.is_le(sz, 65535), h_sz)
  +h_nz = sz_nz(U32.is_zero(sz), sz, {==}, h_one)
  +aa = Inf.adler.of(xs)
  +bb = Png.enc.blocks(sz, xs)
  +ox = List.reverse.go(&2, U32, xs, [])
  +rx = rev_rev(xs)
  Equal.trans(Maybe<&2, List<&2, U32>>, run.bytes(Laws.zlib.stored(sz, xs), Inf.st.empty()),
    run.bytes(Png.enc.cat(bb, Png.enc.be(aa)), st.blk(0, [])), Some{xs},
    hdr(Png.enc.cat(bb, Png.enc.be(aa))),
    Equal.trans(Maybe<&2, List<&2, U32>>, run.bytes(Png.enc.cat(bb, Png.enc.be(aa)), st.blk(0, [])),
      run.bytes(List.append(&2, U32, bb, Png.enc.be(aa)), st.blk(0, [])), Some{xs},
      Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, ll => run.bytes(ll, st.blk(0, [])), Png.enc.cat(bb,
        Png.enc.be(aa)), List.append(&2, U32, bb, Png.enc.be(aa)), cat_app(bb, Png.enc.be(aa))),
      Equal.trans(Maybe<&2, List<&2, U32>>, run.bytes(List.append(&2, U32, bb, Png.enc.be(aa)), st.blk(0, [])),
        run.bytes(Png.enc.be(aa), st.adler(ox)), Some{xs},
        bl.at(U32.is_le(Png.enc.len(xs, 0), sz), sz, xs, Png.enc.be(aa), 0, [], {==}, h_nz, h_top, h_by, h_n),
        Equal.trans(Maybe<&2, List<&2, U32>>, run.bytes(Png.enc.be(aa), st.adler(ox)), Some{List.reverse(&2, U32,
          ox)}, Some{xs},
          adler.ok(aa, ox, Equal.cong(List<&2, U32>, U32, ll => Inf.adler.of(ll), xs, List.reverse(&2, U32, ox),
            Equal.sym(List<&2, U32>, List.reverse(&2, U32, ox), xs, rx))),
          Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, ll => Some{ll}, List.reverse(&2, U32, ox), xs, rx)))))
