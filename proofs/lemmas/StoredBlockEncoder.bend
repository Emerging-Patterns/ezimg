# the stored blocks the zlib encoder writes, and 16-bit masks
import Base
import ../../src/inflate.bend as Inf
import ../../src/png.bend as Png
import ../../laws/defs/PngSpecification.bend as D1
import ./BasicFacts.bend as M1
import ./StoredBlockReader.bend as M2

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
      Empty.absurd({hi == Word.zero(16n) : Word(16n)}, M2.cmp_zero_nlt(16n, hi, ec))
    case GT{}:
      Empty.absurd({hi == Word.zero(16n) : Word(16n)}, M1.false_true(h_le))
    case EQ{}:
      M1.weq(16n, hi, Word.zero(16n), Equal.cong(Cmp, Bool, xx => Cmp.is_eq(xx), Word.cmp(16n, hi, Word.zero(16n)),
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

# the reader where the Adler-32 field starts
def st.adler(out: List<&2, U32>, +pend: U32) -> Inf.St:
  Inf.st.byte(Inf.MAdler{}, 8, 0, Inf.Cx{True{}, 4, 0, out, Inf.TNone{}, 0, pend, 0, Inf.hs.none()})

# the last block's end leads to the Adler-32 field
def after_last(
  +bud: Maybe<&2, Nat>,
  +left: U32,
  +out: List<&2, U32>,
  +rest: List<&2, U32>,
  +pend: U32
) -> {M2.run.bytes(bud, rest, M2.st.after(True{}, left, out, pend)) == M2.run.bytes(bud, rest, st.adler(out,
  pend)) : Maybe<&2,
  List<&2, U32>>}:
  {==}

# the Type a Nat names for telling 0 from a successor: Unit for 0
def zs_ty(nn: Nat) -> Type:
  match nn:
    case 0n:
      Unit
    case 1n+_pp:
      Empty

# 0 is no successor
def inf.zero_succ(kk: Nat, ee: {0n == 1n+kk : Nat}) -> Empty:
  %ee : zs_ty(_)
  Unit{}

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
      Empty.absurd({Nat.is_le(aa, cc) == True{} : Bool}, M1.false_true(h_ab))
    case 1n+_ap 1n+_bp 0n:
      Empty.absurd({Nat.is_le(aa, 0n) == True{} : Bool}, M1.false_true(h_bc))
    case 1n+(+ap) 1n+(+bp) 1n+(+cp):
      nle_trans(ap, bp, cp, h_ab, h_bc)

# U32 at-most is Nat at-most
def u_le(+aa: U32, +bb: U32) -> {U32.is_le(aa, bb) == Nat.is_le(U32.to_nat(aa), U32.to_nat(bb)) : Bool}:
  Equal.cong(Cmp, Bool, cc => Cmp.is_le(cc), U32.cmp(aa, bb), Nat.cmp(U32.to_nat(aa), U32.to_nat(bb)), M1.u_cmp(aa, bb))

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

# a count whose Nat is the length runs down to zero exactly over xs
def ncnt(
  +xs: List<&2, U32>,
  +nn: U32,
  zz: Bool,
  ez: {U32.is_zero(nn) == zz : Bool},
  h_n: {U32.to_nat(nn) == List.length(&2, U32, xs) : Nat}
) -> {M2.cnt(xs, zz, nn) == True{} : Bool}:
  match xs zz:
    case Nil{} True{}:
      {==}
    case Nil{} False{}:
      Empty.absurd({False{} == True{} : Bool}, inf.zero_succ(U32.to_nat(U32.sub(nn, 1)), Equal.trans(Nat, 0n,
        U32.to_nat(nn), 1n+U32.to_nat(U32.sub(nn, 1)), Equal.sym(Nat, U32.to_nat(nn), 0n, h_n), M1.u32_dec(nn, ez))))
    case _hd <> +tl True{}:
      e0 = Equal.cong(U32, Nat, uu => U32.to_nat(uu), nn, 0, M1.ueq(nn, 0, ez))
      Empty.absurd({False{} == True{} : Bool}, inf.zero_succ(List.length(&2, U32, tl), Equal.trans(Nat, 0n,
          U32.to_nat(nn),
        1n+List.length(&2, U32, tl), Equal.sym(Nat, U32.to_nat(nn), 0n, e0), h_n)))
    case _hd <> +tl False{}:
      +n1 = U32.sub(nn, 1)
      e1 = Equal.trans(Nat, 1n+U32.to_nat(n1), U32.to_nat(nn), 1n+List.length(&2, U32, tl), Equal.sym(Nat,
        U32.to_nat(nn), 1n+U32.to_nat(n1), M1.u32_dec(nn, ez)), h_n)
      ncnt(tl, n1, U32.is_zero(n1), {==}, Equal.cong(Nat, Nat, kk => M1.pred(kk), 1n+U32.to_nat(n1),
        1n+List.length(&2, U32, tl), e1))

# a block of at most sz bytes, sz at most 65535: its LEN, counted by enc.len,
# keeps its low 16 bits, and those run down to zero exactly over the block
def blk_cnt(
  +xs: List<&2, U32>,
  +sz: U32,
  +h_len: {Nat.is_le(List.length(&2, U32, xs), U32.to_nat(sz)) == True{} : Bool},
  h_sz: {U32.is_le(sz, 65535) == True{} : Bool}
) -> {M2.cnt(xs, U32.is_zero(U32.and(65535, Png.enc.len(xs, 0))), U32.and(65535, Png.enc.len(xs, 0))) == True{} :
  Bool}:
  +ll = Png.enc.len(xs, 0)
  +nl = M1.up(xs, 0, sz, h_len)
  +h_ls = Equal.trans(Bool, U32.is_le(ll, sz), Nat.is_le(U32.to_nat(ll), U32.to_nat(sz)), True{}, u_le(ll, sz),
    Equal.trans(Bool, Nat.is_le(U32.to_nat(ll), U32.to_nat(sz)), Nat.is_le(List.length(&2, U32, xs), U32.to_nat(sz)),
      True{}, Equal.cong(Nat, Bool, kk => Nat.is_le(kk, U32.to_nat(sz)), U32.to_nat(ll), List.length(&2, U32, xs),
      nl), h_len))
  +em = mask16(ll, u_le_trans(ll, sz, 65535, h_ls, h_sz))
  Equal.trans(Bool, M2.cnt(xs, U32.is_zero(U32.and(65535, ll)), U32.and(65535, ll)), M2.cnt(xs, U32.is_zero(ll), ll),
      True{},
    Equal.cong(U32, Bool, vv => M2.cnt(xs, U32.is_zero(vv), vv), U32.and(65535, ll), ll, em),
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

# enc.cat is List.append
def cat_app(
  +xs: List<&2, U32>,
  +ys: List<&2, U32>
) -> {Png.enc.cat(xs, ys) == List.append(&2, U32, xs, ys) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, Png.enc.cat(xs, ys), List.reverse.go(&2, U32, List.reverse(&2, U32, xs), ys),
    List.append(&2, U32, xs, ys), catgo_rev(List.reverse(&2, U32, xs), ys), M1.revrev(xs, [], ys))

# bytes reversed onto bytes are bytes
def bytes_revgo(
  +xs: List<&2, U32>,
  +out: List<&2, U32>,
  +h_xs: {D1.bytes.go(xs, True{}) == True{} : Bool},
  h_out: {D1.bytes.go(out, True{}) == True{} : Bool}
) -> {D1.bytes.go(List.reverse.go(&2, U32, xs, out), True{}) == True{} : Bool}:
  match xs:
    case Nil{}:
      h_out
    case +hd <> +tl:
      +eh = M2.bytes.ok(tl, U32.is_le(hd, 255), h_xs)
      bytes_revgo(tl, hd <> out, M2.bytes.tail(tl, U32.is_le(hd, 255), h_xs), Equal.trans(Bool, D1.bytes.go(out,
        U32.is_le(hd, 255)), D1.bytes.go(out, True{}), True{}, Equal.cong(Bool, Bool, bb => D1.bytes.go(out, bb),
        U32.is_le(hd, 255), True{}, eh), h_out))

# one stored block as enc.stored writes it, of at most sz bytes: the reader copies it
def st_blk(
  +bud: Maybe<&2, Nat>,
  +fin: Bool,
  +xs: List<&2, U32>,
  +rest: List<&2, U32>,
  +left: U32,
  +out: List<&2, U32>,
  +pend: U32,
  +sz: U32,
  h_len: {Nat.is_le(List.length(&2, U32, xs), U32.to_nat(sz)) == True{} : Bool},
  h_sz: {U32.is_le(sz, 65535) == True{} : Bool},
  h_by: {D1.bytes.go(xs, True{}) == True{} : Bool}
) -> {M2.run.bytes(bud, List.append(&2, U32, Png.enc.stored(fin, xs), rest), M2.st.blk(left, out, pend)) ==
  M2.run.bytes(bud, rest, M2.st.after(fin, M1.cd(xs, U32.and(65535, Png.enc.len(xs, 0))), List.reverse.go(&2, U32,
    xs, out),
  (pend + U32.and(65535, Png.enc.len(xs, 0)) : U32))) : Maybe<&2, List<&2, U32>>}:
  +ll = Png.enc.len(xs, 0)
  +hd = Png.enc.head(fin, ll, U32.xor(ll, 65535))
  Equal.trans(Maybe<&2, List<&2, U32>>, M2.run.bytes(bud, List.append(&2, U32, Png.enc.cat(hd, xs), rest),
    M2.st.blk(left,
      out, pend)),
    M2.run.bytes(bud, List.append(&2, U32, List.append(&2, U32, hd, xs), rest), M2.st.blk(left, out, pend)),
    M2.run.bytes(bud, rest, M2.st.after(fin, M1.cd(xs, U32.and(65535, ll)), List.reverse.go(&2, U32, xs, out), (pend +
      U32.and(65535, ll) : U32))),
    Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, bs => M2.run.bytes(bud, List.append(&2, U32, bs, rest),
      M2.st.blk(left, out, pend)), Png.enc.cat(hd, xs), List.append(&2, U32, hd, xs), cat_app(hd, xs)),
    M2.blk(bud, fin, ll, xs, rest, left, out, pend, blk_cnt(xs, sz, h_len, h_sz), h_by))

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
    List.reverse(&2, U32, acc)), na, M1.len_rev(acc)), le)

# the stored bytes enc.feed's blocks owe the window, on top of `pend`: each
# block's LEN, as the reader adds it
def pend.fl(xs: List<&2, U32>, zz: Bool, +room: U32, +sz: U32, acc: List<&2, U32>, +pend: U32) -> U32:
  match xs zz:
    case Nil{} _zz:
      (pend + U32.and(65535, Png.enc.len(List.reverse(&2, U32, acc), 0)) : U32)
    case +hd <> tl True{}:
      +s1 = (sz - 1 : U32)
      pend.fl(tl, U32.is_zero(s1), s1, sz, [hd], (pend + U32.and(65535, Png.enc.len(List.reverse(&2, U32, acc), 0)) :
        U32))
    case +hd <> tl False{}:
      +r1 = (room - 1 : U32)
      pend.fl(tl, U32.is_zero(r1), r1, sz, hd <> acc, pend)

# enc.feed's blocks, the open block `acc` first (newest first, `room` bytes
# still free in it): the reader copies them all and reaches the Adler field
def fl(
  +bud: Maybe<&2, Nat>,
  +xs: List<&2, U32>,
  +zz: Bool,
  +room: U32,
  +sz: U32,
  +acc: List<&2, U32>,
  +rest: List<&2, U32>,
  +left: U32,
  +out: List<&2, U32>,
  +pend: U32,
  ez: {U32.is_zero(room) == zz : Bool},
  +inv: {Nat.add(List.length(&2, U32, acc), U32.to_nat(room)) == U32.to_nat(sz) : Nat},
  +h_nz: {U32.is_zero(sz) == False{} : Bool},
  +h_sz: {U32.is_le(sz, 65535) == True{} : Bool},
  +h_bx: {D1.bytes.go(xs, True{}) == True{} : Bool},
  +h_ba: {D1.bytes.go(acc, True{}) == True{} : Bool}
) -> {M2.run.bytes(bud, List.append(&2, U32, Png.enc.feed(xs, zz, room, sz, acc), rest), M2.st.blk(left, out, pend)) ==
  M2.run.bytes(bud, rest, st.adler(List.reverse.go(&2, U32, xs, List.reverse.go(&2, U32, List.reverse(&2, U32, acc),
    out)),
  pend.fl(xs, zz, room, sz, acc, pend))) : Maybe<&2, List<&2, U32>>}:
  match xs zz:
    case Nil{} _zz:
      +ra = List.reverse(&2, U32, acc)
      +o1 = List.reverse.go(&2, U32, ra, out)
      +c1 = M1.cd(ra, U32.and(65535, Png.enc.len(ra, 0)))
      +h_bra = bytes_revgo(acc, [], h_ba, {==})
      +p1 = (pend + U32.and(65535, Png.enc.len(ra, 0)) : U32)
      Equal.trans(Maybe<&2, List<&2, U32>>, M2.run.bytes(bud, List.append(&2, U32, Png.enc.stored(True{}, ra), rest),
        M2.st.blk(left, out, pend)), M2.run.bytes(bud, rest, M2.st.after(True{}, c1, o1, p1)), M2.run.bytes(bud, rest,
        st.adler(o1, p1)),
        st_blk(bud, True{}, ra, rest, left, out, pend, sz, acc_len(acc, room, sz, inv), h_sz, h_bra),
        after_last(bud, c1, o1, rest, p1))
    case +hd <> +tl True{}:
      +ra = List.reverse(&2, U32, acc)
      +o1 = List.reverse.go(&2, U32, ra, out)
      +c1 = M1.cd(ra, U32.and(65535, Png.enc.len(ra, 0)))
      +h_bra = bytes_revgo(acc, [], h_ba, {==})
      +s1 = (sz - 1 : U32)
      +bs = Png.enc.stored(False{}, ra)
      +ff = Png.enc.feed(tl, U32.is_zero(s1), s1, sz, [hd])
      +e_hd = M2.bytes.ok(tl, U32.is_le(hd, 255), h_bx)
      +p1 = (pend + U32.and(65535, Png.enc.len(ra, 0)) : U32)
      +pz = pend.fl(tl, U32.is_zero(s1), s1, sz, [hd], p1)
      Equal.trans(Maybe<&2, List<&2, U32>>, M2.run.bytes(bud, List.append(&2, U32, Png.enc.cat(bs, ff), rest),
        M2.st.blk(left, out, pend)), M2.run.bytes(bud, List.append(&2, U32, List.append(&2, U32, bs, ff), rest),
        M2.st.blk(left, out, pend)),
        M2.run.bytes(bud, rest, st.adler(List.reverse.go(&2, U32, tl, hd <> o1), pz)),
        Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, ll => M2.run.bytes(bud, List.append(&2, U32, ll, rest),
          M2.st.blk(left, out, pend)), Png.enc.cat(bs, ff), List.append(&2, U32, bs, ff), cat_app(bs, ff)),
        Equal.trans(Maybe<&2, List<&2, U32>>, M2.run.bytes(bud, List.append(&2, U32, List.append(&2, U32, bs, ff),
          rest),
          M2.st.blk(left, out, pend)), M2.run.bytes(bud, List.append(&2, U32, bs, List.append(&2, U32, ff, rest)),
          M2.st.blk(left, out, pend)),
          M2.run.bytes(bud, rest, st.adler(List.reverse.go(&2, U32, tl, hd <> o1), pz)),
          Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, ll => M2.run.bytes(bud, ll, M2.st.blk(left, out, pend)),
            List.append(&2, U32, List.append(&2, U32, bs, ff), rest), List.append(&2, U32, bs, List.append(&2, U32, ff,
            rest)), M1.app_assoc(bs, ff, rest)),
          Equal.trans(Maybe<&2, List<&2, U32>>, M2.run.bytes(bud, List.append(&2, U32, bs, List.append(&2, U32, ff,
            rest)),
            M2.st.blk(left, out, pend)), M2.run.bytes(bud, List.append(&2, U32, ff, rest), M2.st.blk(c1, o1, p1)),
            M2.run.bytes(bud, rest, st.adler(List.reverse.go(&2, U32, tl, hd <> o1), pz)),
            st_blk(bud, False{}, ra, List.append(&2, U32, ff, rest), left, out, pend, sz, acc_len(acc, room, sz,
              inv), h_sz,
              h_bra),
            fl(bud, tl, U32.is_zero(s1), s1, sz, [hd], rest, c1, o1, p1, {==}, Equal.sym(Nat, U32.to_nat(sz),
              1n+U32.to_nat(s1),
              M1.u32_dec(sz, h_nz)), h_nz, h_sz, M2.bytes.tail(tl, U32.is_le(hd, 255), h_bx), Equal.cong(Bool, Bool,
              bb => D1.bytes.go([], bb), U32.is_le(hd, 255), True{}, e_hd)))))
    case +hd <> +tl False{}:
      +o1 = List.reverse.go(&2, U32, List.reverse(&2, U32, acc), out)
      +r1 = (room - 1 : U32)
      +na = List.length(&2, U32, acc)
      +e_hd = M2.bytes.ok(tl, U32.is_le(hd, 255), h_bx)
      +inv2 = Equal.trans(Nat, 1n+Nat.add(na, U32.to_nat(r1)), Nat.add(na, 1n+U32.to_nat(r1)), U32.to_nat(sz),
        Equal.sym(Nat, Nat.add(na, 1n+U32.to_nat(r1)), 1n+Nat.add(na, U32.to_nat(r1)), M1.nat_add_succ(na,
          U32.to_nat(r1))),
        Equal.trans(Nat, Nat.add(na, 1n+U32.to_nat(r1)), Nat.add(na, U32.to_nat(room)), U32.to_nat(sz),
          Equal.cong(Nat, Nat, kk => Nat.add(na, kk), 1n+U32.to_nat(r1), U32.to_nat(room), Equal.sym(Nat,
            U32.to_nat(room), 1n+U32.to_nat(r1), M1.u32_dec(room, ez))), inv))
      +e_out = Equal.trans(List<&2, U32>, List.reverse.go(&2, U32, List.reverse(&2, U32, hd <> acc), out),
        hd <> List.append(&2, U32, acc, out), hd <> o1, M1.rr(hd <> acc, out),
        Equal.cong(List<&2, U32>, List<&2, U32>, ll => hd <> ll, List.append(&2, U32, acc, out), o1,
          Equal.sym(List<&2, U32>, o1, List.append(&2, U32, acc, out), M1.rr(acc, out))))
      +pz = pend.fl(tl, U32.is_zero(r1), r1, sz, hd <> acc, pend)
      Equal.trans(Maybe<&2, List<&2, U32>>, M2.run.bytes(bud, List.append(&2, U32, Png.enc.feed(tl, U32.is_zero(r1),
        r1, sz,
        hd <> acc), rest), M2.st.blk(left, out, pend)), M2.run.bytes(bud, rest, st.adler(List.reverse.go(&2, U32, tl,
        List.reverse.go(&2, U32, List.reverse(&2, U32, hd <> acc), out)), pz)),
        M2.run.bytes(bud, rest, st.adler(List.reverse.go(&2, U32, tl, hd <> o1), pz)),
        fl(bud, tl, U32.is_zero(r1), r1, sz, hd <> acc, rest, left, out, pend, {==}, inv2, h_nz, h_sz, M2.bytes.tail(tl,
          U32.is_le(hd, 255), h_bx), Equal.trans(Bool, D1.bytes.go(acc, U32.is_le(hd, 255)), D1.bytes.go(acc,
          True{}), True{}, Equal.cong(Bool, Bool, bb => D1.bytes.go(acc, bb), U32.is_le(hd, 255), True{}, e_hd),
          h_ba)),
        Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, ll => M2.run.bytes(bud, rest,
          st.adler(List.reverse.go(&2, U32,
          tl, ll), pz)), List.reverse.go(&2, U32, List.reverse(&2, U32, hd <> acc), out), hd <> o1, e_out))
