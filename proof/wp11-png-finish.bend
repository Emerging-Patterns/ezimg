# proof/wp11-png-finish: lemmas for the PNG encodings past one stored block
# (IMG-PNG-2) and for ancillary chunks in the chunk walker (IMG-PNG-9). Each
# is a law proved here, or a def whose type is the fact it proves; PROOF.bend
# imports this file, so the gate checks it. No number near 2^29 or 2^32 is
# written as a Nat: the checker holds a Nat in unary.
import Base
import ../LAWS.bend as Laws
import ../main.bend as Img
import ../src/crc.bend as Crc
import ../src/png.bend as Png
import ../src/inflate.bend as Inf
import ./u32.bend as U32L
import ./wp1-crc.bend as Wp1
import ./wp2-inflate.bend as Wp2
import ./wp6-raster.bend as R
import ./wp9-png-roundtrip.bend as W9

# ---- A. U32 and Nat facts ----

# U32s of the same value are the same U32
def u32.same(+uu: U32, +vv: U32, en: {U32.to_nat(uu) == U32.to_nat(vv) : Nat}) -> {uu == vv : U32}:
  U32L.ueq(uu, vv, Equal.trans(Bool, U32.is_eq(uu, vv), Nat.is_eq(U32.to_nat(vv), U32.to_nat(vv)), True{},
    Equal.trans(Bool, U32.is_eq(uu, vv), Nat.is_eq(U32.to_nat(uu), U32.to_nat(vv)), Nat.is_eq(U32.to_nat(vv),
      U32.to_nat(vv)), R.u32_eq(uu, vv), Equal.cong(Nat, Bool, kk => Nat.is_eq(kk, U32.to_nat(vv)), U32.to_nat(uu),
      U32.to_nat(vv), en)),
    R.nat_eq_refl(U32.to_nat(vv))))

# a U32 is_zero calls zero is worth 0
def zero.val(+uu: U32, ez: {True{} == U32.is_zero(uu) : Bool}) -> {U32.to_nat(uu) == 0n : Nat}:
  Equal.cong(U32, Nat, xx => U32.to_nat(xx), uu, 0, U32L.ueq(uu, 0, Equal.sym(Bool, True{}, U32.is_zero(uu), ez)))

# a U32 worth 0 is zero
def zero.is(+uu: U32, e0: {U32.to_nat(uu) == 0n : Nat}) -> {U32.is_zero(uu) == True{} : Bool}:
  Equal.trans(Bool, U32.is_zero(uu), Nat.is_eq(U32.to_nat(uu), 0n), True{}, R.u32_eq(uu, 0),
    Equal.cong(Nat, Bool, kk => Nat.is_eq(kk, 0n), U32.to_nat(uu), 0n, e0))

# a U32 is_eq calls 1 is worth 1
def one.val(+uu: U32, e1: {True{} == U32.is_eq(uu, 1) : Bool}) -> {U32.to_nat(uu) == 1n : Nat}:
  Equal.cong(U32, Nat, xx => U32.to_nat(xx), uu, 1, U32L.ueq(uu, 1, Equal.sym(Bool, True{}, U32.is_eq(uu, 1), e1)))

# a U32 above some successor's predecessor is not zero, once is_zero's answer is named
def pos.at(
  zz: Bool,
  +uu: U32,
  +kk: Nat,
  +ez: {U32.is_zero(uu) == zz : Bool},
  +hh: {Nat.is_le(1n+kk, U32.to_nat(uu)) == True{} : Bool}
) -> {U32.is_zero(uu) == False{} : Bool}:
  match zz:
    case False{}:
      ez
    case True{}:
      +e0 = {zero.val(uu, Equal.sym(Bool, U32.is_zero(uu), True{}, ez)) : {U32.to_nat(uu) == 0n : Nat}}
      Empty.absurd({U32.is_zero(uu) == False{} : Bool}, U32L.false_true(Equal.trans(Bool, False{},
        Nat.is_le(1n+kk, U32.to_nat(uu)), True{}, Equal.sym(Bool, Nat.is_le(1n+kk, U32.to_nat(uu)), False{},
        Equal.cong(Nat, Bool, xx => Nat.is_le(1n+kk, xx), U32.to_nat(uu), 0n, e0)), hh)))

# a U32 at least a successor is not zero
def pos(+uu: U32, +kk: Nat, hh: {Nat.is_le(1n+kk, U32.to_nat(uu)) == True{} : Bool}) -> {U32.is_zero(uu) == False{} :
  Bool}:
  pos.at(U32.is_zero(uu), uu, kk, {==}, hh)

# a U32 neither 0 nor 1 less one is not zero, once is_zero's answer is named
def two.at(
  zz: Bool,
  +uu: U32,
  +ez: {U32.is_zero((uu - 1 : U32)) == zz : Bool},
  +hz: {False{} == U32.is_zero(uu) : Bool},
  +h1: {False{} == U32.is_eq(uu, 1) : Bool}
) -> {U32.is_zero((uu - 1 : U32)) == False{} : Bool}:
  match zz:
    case False{}:
      ez
    case True{}:
      +e0 = {zero.val((uu - 1 : U32), Equal.sym(Bool, U32.is_zero((uu - 1 : U32)), True{}, ez)) :
        {U32.to_nat((uu - 1 : U32)) == 0n : Nat}}
      +e1 = {Equal.trans(Nat, U32.to_nat(uu), 1n+U32.to_nat((uu - 1 : U32)), 1n, Wp1.u32_dec(uu, Equal.sym(Bool,
        False{}, U32.is_zero(uu), hz)), Equal.cong(Nat, Nat, kk => 1n+kk, U32.to_nat((uu - 1 : U32)), 0n, e0)) :
        {U32.to_nat(uu) == 1n : Nat}}
      Empty.absurd({U32.is_zero((uu - 1 : U32)) == False{} : Bool}, U32L.false_true(Equal.trans(Bool, False{},
        U32.is_eq(uu, 1), True{}, h1, Equal.trans(Bool, U32.is_eq(uu, 1), Nat.is_eq(U32.to_nat(uu), 1n), True{},
        R.u32_eq(uu, 1), Equal.cong(Nat, Bool, kk => Nat.is_eq(kk, 1n), U32.to_nat(uu), 1n, e1)))))

# a U32 neither 0 nor 1, less one, is not zero
def two(
  +uu: U32,
  +hz: {False{} == U32.is_zero(uu) : Bool},
  +h1: {False{} == U32.is_eq(uu, 1) : Bool}
) -> {U32.is_zero((uu - 1 : U32)) == False{} : Bool}:
  two.at(U32.is_zero((uu - 1 : U32)), uu, {==}, hz, h1)

# not at most is above
def nle.lt(aa: Nat, bb: Nat, hh: {Nat.is_le(aa, bb) == False{} : Bool}) -> {Nat.is_lt(bb, aa) == True{} : Bool}:
  match aa bb:
    case 0n bb0:
      Empty.absurd({Nat.is_lt(bb0, 0n) == True{} : Bool}, U32L.false_true(Equal.trans(Bool, False{}, Nat.is_le(0n, bb0),
        True{}, Equal.sym(Bool, Nat.is_le(0n, bb0), False{}, hh), R.le_zero(bb0))))
    case 1n+_ap 0n:
      {==}
    case 1n+ap 1n+bp:
      nle.lt(ap, bp, hh)

# one more on the left of a sum, one less on the right: the same sum
def shift(
  +aa: Nat,
  +uu: U32,
  +vv: U32,
  +nn: Nat,
  +ev: {U32.to_nat(uu) == 1n+U32.to_nat(vv) : Nat},
  +ee: {Nat.add(aa, U32.to_nat(uu)) == nn : Nat}
) -> {Nat.add(1n+aa, U32.to_nat(vv)) == nn : Nat}:
  Equal.trans(Nat, 1n+Nat.add(aa, U32.to_nat(vv)), Nat.add(aa, U32.to_nat(uu)), nn,
    Equal.trans(Nat, 1n+Nat.add(aa, U32.to_nat(vv)), Nat.add(aa, 1n+U32.to_nat(vv)), Nat.add(aa, U32.to_nat(uu)),
      Equal.sym(Nat, Nat.add(aa, 1n+U32.to_nat(vv)), 1n+Nat.add(aa, U32.to_nat(vv)), R.add_succ(aa,
        U32.to_nat(vv))),
      Equal.cong(Nat, Nat, kk => Nat.add(aa, kk), 1n+U32.to_nat(vv), U32.to_nat(uu), Equal.sym(Nat, U32.to_nat(uu),
        1n+U32.to_nat(vv), ev))),
    ee)

# a list at most cap's value long is counted in a U32 to its length
def len.of(
  +xs: List<&2, U32>,
  +cap: U32,
  +hh: {Nat.is_le(List.length(&2, U32, xs), U32.to_nat(cap)) == True{} : Bool}
) -> {U32.to_nat(Png.enc.len(xs, 0)) == List.length(&2, U32, xs) : Nat}:
  Equal.trans(Nat, U32.to_nat(Png.enc.len(xs, 0)), U32.to_nat(U32.from_nat(List.length(&2, U32, xs))),
    List.length(&2, U32, xs), Equal.cong(U32, Nat, uu => U32.to_nat(uu), Png.enc.len(xs, 0),
    U32.from_nat(List.length(&2, U32, xs)), W9.len.word(xs)), W9.nat.fits(List.length(&2, U32, xs), cap, hh))

# ---- B. enc.crc.list, and the bytes enc.pour writes ----

# enc.crc.list is the CRC fold and the bytes reversed onto the accumulator
def crcl(
  xs: List<&2, U32>,
  +cc: U32,
  +acc: List<&2, U32>
) -> {Png.enc.crc.list(xs, cc, acc) == (Crc.crc.fold(xs, cc), List.reverse.go(&2, U32, xs, acc)) : U32 & List<&2,
  U32>}:
  match xs:
    case Nil{}:
      {==}
    case +hd <> tl:
      crcl(tl, Crc.crc.byte(cc, hd), hd <> acc)

# the bytes enc.pour writes, in order: its walk without the CRC
def bs(
  xs: List<&2, U32>,
  znew: Bool,
  zlast: Bool,
  +room: U32,
  +left: U32,
  +len: U32,
  +bf: U32
) -> List<&2, U32>:
  match xs znew zlast:
    case Nil{} _z _last:
      []
    case +h <> +t False{} False{}:
      +room2 = (room - 1 : U32)
      h <> bs(t, False{}, U32.is_eq(room2, 1), room2, (left - 1 : U32), len, bf)
    case +h <> +t False{} True{}:
      +left2 = (left - 1 : U32)
      h <> bs(t, True{}, False{}, 0, left2, Png.enc.cap(left2), Png.enc.bf(left2))
    case +h <> t True{} _last:
      +nlen = (len .^. 65535 : U32)
      +left2 = (left - 1 : U32)
      +room2 = (len - 1 : U32)
      bf <> Png.enc.byte(len) <> Png.enc.hi(len) <> Png.enc.byte(nlen) <> Png.enc.hi(nlen) <> h <> bs(t,
        U32.is_zero(room2), U32.is_eq(room2, 1), room2, left2, Png.enc.cap(left2), Png.enc.bf(left2))

# enc.pour is enc.crc.list over bs
def pour.bs(
  xs: List<&2, U32>,
  znew: Bool,
  zlast: Bool,
  +room: U32,
  +left: U32,
  +len: U32,
  +bf: U32,
  +cc: U32,
  +acc: List<&2, U32>
) -> {Png.enc.pour(xs, znew, zlast, room, left, len, bf, cc, acc) == Png.enc.crc.list(bs(xs, znew, zlast, room, left,
  len, bf), cc, acc) : U32 & List<&2, U32>}:
  match xs znew zlast:
    case Nil{} _z _last:
      {==}
    case +h <> +t False{} False{}:
      pour.bs(t, False{}, U32.is_eq((room - 1 : U32), 1), (room - 1 : U32), (left - 1 : U32), len, bf,
        Crc.crc.byte(cc, h), h <> acc)
    case +h <> +t False{} True{}:
      +left2 = (left - 1 : U32)
      pour.bs(t, True{}, False{}, 0, left2, Png.enc.cap(left2), Png.enc.bf(left2), Crc.crc.byte(cc, h), h <> acc)
    case +h <> t True{} _last:
      +nlen = (len .^. 65535 : U32)
      +b1 = Png.enc.byte(len)
      +b2 = Png.enc.hi(len)
      +b3 = Png.enc.byte(nlen)
      +b4 = Png.enc.hi(nlen)
      +c1 = Crc.crc.byte(cc, bf)
      +c2 = Crc.crc.byte(c1, b1)
      +c3 = Crc.crc.byte(c2, b2)
      +c4 = Crc.crc.byte(c3, b3)
      +c5 = Crc.crc.byte(c4, b4)
      +left2 = (left - 1 : U32)
      +room2 = (len - 1 : U32)
      pour.bs(t, U32.is_zero(room2), U32.is_eq(room2, 1), room2, left2, Png.enc.cap(left2), Png.enc.bf(left2),
        Crc.crc.byte(c5, h), h <> b4 <> b3 <> b2 <> b1 <> bf <> acc)

# ---- C. bs against enc.feed, byte by byte ----

# The block size, 65535, is named mx here and its value is U32.to_nat(mx): a
# closed Nat as large as 65535 in a type is expanded in unary and overflows
# the checker's stack. Each lemma takes mx with {mx == 65535 : U32}.

# where the open block stands against the nx bytes still to come: a final
# block holds them all, rp their count; any other block is full, its room the
# feed's, and more bytes follow it
def fin.ok(fin: Bool, +rp: U32, +rf: U32, +nx: Nat) -> Type:
  match fin:
    case True{}:
      {U32.to_nat(rp) == nx : Nat}
    case False{}:
      {U32.to_nat(rp) == U32.to_nat(rf) : Nat} & {Nat.is_lt(U32.to_nat(rp), nx) == True{} : Bool}

# at a block boundary the walk carries the next block's length and BFINAL
def at.edge(+rp: U32, +left: U32, +plen: U32, +pbf: U32) -> Type:
  {U32.is_zero(rp) == True{} : Bool} -> {plen == Png.enc.cap(left) : U32} & {pbf == Png.enc.bf(left) : U32}

# what sim proves: the open block's header, the block so far, then the rest
# of bs are enc.feed's blocks of mx bytes
def sim.ty(
  +xs: List<&2, U32>,
  +znew: Bool,
  +zlast: Bool,
  +zf: Bool,
  +fin: Bool,
  +acc: List<&2, U32>,
  +rf: U32,
  +rp: U32,
  +left: U32,
  +plen: U32,
  +pbf: U32,
  +ll: U32,
  +mx: U32
) -> Type:
  {List.append(&2, U32, Png.enc.head(fin, ll, (ll .^. 65535 : U32)), List.reverse.go(&2, U32, acc, bs(xs, znew, zlast,
    rp, left, plen, pbf))) == Png.enc.feed(xs, zf, rf, mx, acc) : List<&2, U32>}

# one byte less on both sides of fin.ok
def fo.dec(
  fin: Bool,
  +rp: U32,
  +rf: U32,
  +rp2: U32,
  +rf2: U32,
  +nt: Nat,
  +ep: {U32.to_nat(rp) == 1n+U32.to_nat(rp2) : Nat},
  +ef: {U32.to_nat(rf) == 1n+U32.to_nat(rf2) : Nat},
  hf: fin.ok(fin, rp, rf, 1n+nt)
) -> fin.ok(fin, rp2, rf2, nt):
  match fin:
    case True{}:
      Wp1.succ_inj(U32.to_nat(rp2), nt, Equal.trans(Nat, 1n+U32.to_nat(rp2), U32.to_nat(rp), 1n+nt, Equal.sym(Nat,
        U32.to_nat(rp), 1n+U32.to_nat(rp2), ep), hf))
    case False{}:
      (e_rr, h_lt) = hf
      +e2 = {Wp1.succ_inj(U32.to_nat(rp2), U32.to_nat(rf2), Equal.trans(Nat, 1n+U32.to_nat(rp2), U32.to_nat(rp),
        1n+U32.to_nat(rf2), Equal.sym(Nat, U32.to_nat(rp), 1n+U32.to_nat(rp2), ep), Equal.trans(Nat, U32.to_nat(rp),
        U32.to_nat(rf), 1n+U32.to_nat(rf2), e_rr, ef))) : {U32.to_nat(rp2) == U32.to_nat(rf2) : Nat}}
      +l2 = {Equal.trans(Bool, Nat.is_lt(1n+U32.to_nat(rp2), 1n+nt), Nat.is_lt(U32.to_nat(rp), 1n+nt), True{},
        Equal.cong(Nat, Bool, kk => Nat.is_lt(kk, 1n+nt), 1n+U32.to_nat(rp2), U32.to_nat(rp), Equal.sym(Nat,
        U32.to_nat(rp), 1n+U32.to_nat(rp2), ep)), h_lt) : {Nat.is_lt(U32.to_nat(rp2), nt) == True{} : Bool}}
      (e2, l2)

# enc.cap.at with the block size named
def capm(zz: Bool, +left: U32, +mx: U32) -> U32:
  match zz:
    case True{}:
      left
    case False{}:
      mx

# enc.cap.at is capm at 65535
def cap.m(zz: Bool, +left: U32, +mx: U32, +emx: {mx == 65535 : U32}) -> {Png.enc.cap.at(zz, left) == capm(zz, left, mx) :
  U32}:
  match zz:
    case True{}:
      {==}
    case False{}:
      Equal.sym(U32, mx, 65535, emx)

# the block size is not zero
def mx.nz(+mx: U32, +emx: {mx == 65535 : U32}) -> {U32.is_zero(mx) == False{} : Bool}:
  Equal.cong(U32, Bool, uu => U32.is_zero(uu), mx, 65535, emx)

# at most 65535 is at most the block size
def le.mx(+left: U32, +mx: U32, +emx: {mx == 65535 : U32}) -> {U32.is_le(left, mx) == U32.is_le(left, 65535) : Bool}:
  Equal.cong(U32, Bool, uu => U32.is_le(left, uu), mx, 65535, emx)

# a new block's length is not zero when bytes are left
def cap.nz(
  zz: Bool,
  +left: U32,
  +mx: U32,
  +kk: Nat,
  +nzm: {U32.is_zero(mx) == False{} : Bool},
  +hn: {U32.to_nat(left) == 1n+kk : Nat}
) -> {U32.is_zero(capm(zz, left, mx)) == False{} : Bool}:
  match zz:
    case True{}:
      Wp1.u32_nonzero(left, kk, hn)
    case False{}:
      nzm

# a new block's room after its first byte is within the feed's
def cap.le(
  zz: Bool,
  +left: U32,
  +mx: U32,
  +kk: Nat,
  +nzm: {U32.is_zero(mx) == False{} : Bool},
  +ez: {U32.is_le(left, mx) == zz : Bool},
  +hn: {U32.to_nat(left) == 1n+kk : Nat}
) -> {Nat.is_le(U32.to_nat((capm(zz, left, mx) - 1 : U32)), U32.to_nat((mx - 1 : U32))) == True{} : Bool}:
  match zz:
    case True{}:
      +l1 = (left - 1 : U32)
      +m1 = (mx - 1 : U32)
      +e_l = {Wp1.u32_dec(left, Wp1.u32_nonzero(left, kk, hn)) : {U32.to_nat(left) == 1n+U32.to_nat(l1) : Nat}}
      +e_m = {Wp1.u32_dec(mx, nzm) : {U32.to_nat(mx) == 1n+U32.to_nat(m1) : Nat}}
      +h0 = {Equal.trans(Bool, Nat.is_le(U32.to_nat(left), U32.to_nat(mx)), U32.is_le(left, mx), True{},
        Equal.sym(Bool, U32.is_le(left, mx), Nat.is_le(U32.to_nat(left), U32.to_nat(mx)), R.u32_le(left, mx)), ez) :
        {Nat.is_le(U32.to_nat(left), U32.to_nat(mx)) == True{} : Bool}}
      R.le_rw_r(1n+U32.to_nat(l1), U32.to_nat(mx), 1n+U32.to_nat(m1), e_m, R.le_rw_l(U32.to_nat(left),
        1n+U32.to_nat(l1), U32.to_nat(mx), e_l, h0))
    case False{}:
      R.le_refl(U32.to_nat((mx - 1 : U32)))

# where a new block stands: final when the bytes left fit, else full
def cap.fo(
  zz: Bool,
  +left: U32,
  +mx: U32,
  +kk: Nat,
  +nzm: {U32.is_zero(mx) == False{} : Bool},
  +ez: {U32.is_le(left, mx) == zz : Bool},
  +hn: {U32.to_nat(left) == 1n+kk : Nat}
) -> fin.ok(zz, (capm(zz, left, mx) - 1 : U32), (mx - 1 : U32), kk):
  match zz:
    case True{}:
      Wp1.u32_pred(left, kk, hn)
    case False{}:
      +m1 = (mx - 1 : U32)
      +e_m = {Wp1.u32_dec(mx, nzm) : {U32.to_nat(mx) == 1n+U32.to_nat(m1) : Nat}}
      +h0 = {Equal.trans(Bool, Nat.is_le(1n+kk, 1n+U32.to_nat(m1)), U32.is_le(left, mx), False{},
        Equal.sym(Bool, U32.is_le(left, mx), Nat.is_le(1n+kk, 1n+U32.to_nat(m1)), Equal.trans(Bool,
          U32.is_le(left, mx), Nat.is_le(U32.to_nat(left), U32.to_nat(mx)), Nat.is_le(1n+kk, 1n+U32.to_nat(m1)),
          R.u32_le(left, mx), Equal.trans(Bool, Nat.is_le(U32.to_nat(left), U32.to_nat(mx)), Nat.is_le(1n+kk,
          U32.to_nat(mx)), Nat.is_le(1n+kk, 1n+U32.to_nat(m1)), Equal.cong(Nat, Bool, xx => Nat.is_le(xx,
          U32.to_nat(mx)), U32.to_nat(left), 1n+kk, hn), Equal.cong(Nat, Bool, xx => Nat.is_le(1n+kk, xx),
          U32.to_nat(mx), 1n+U32.to_nat(m1), e_m)))), ez) : {Nat.is_le(kk, U32.to_nat(m1)) == False{} : Bool}}
      ({==}, nle.lt(kk, U32.to_nat(m1), h0))

# fin.ok of enc.cap.at's room from capm's
def fo.cm(
  +zz: Bool,
  +left: U32,
  +mx: U32,
  +nt: Nat,
  +emx: {mx == 65535 : U32},
  hh: fin.ok(zz, (capm(zz, left, mx) - 1 : U32), (mx - 1 : U32), nt)
) -> fin.ok(zz, (Png.enc.cap.at(zz, left) - 1 : U32), (mx - 1 : U32), nt):
  %Equal.sym(U32, Png.enc.cap.at(zz, left), capm(zz, left, mx), cap.m(zz, left, mx, emx)) : fin.ok(zz, (_ - 1 : U32),
    (mx - 1 : U32), nt)
  hh

# the header bs writes at a new block is enc.head's for the block's BFINAL
def hdr(
  zz: Bool,
  +left: U32,
  +rest: List<&2, U32>
) -> {Png.enc.bf.at(zz) <> Png.enc.byte(Png.enc.cap.at(zz, left)) <> Png.enc.hi(Png.enc.cap.at(zz, left)) <>
  Png.enc.byte((Png.enc.cap.at(zz, left) .^. 65535 : U32)) <> Png.enc.hi((Png.enc.cap.at(zz, left) .^. 65535 : U32))
  <> rest == List.append(&2, U32, Png.enc.head(zz, Png.enc.cap.at(zz, left), (Png.enc.cap.at(zz, left) .^. 65535 :
  U32)), rest) : List<&2, U32>}:
  match zz:
    case True{}:
      {==}
    case False{}:
      {==}

# the open block, reversed, is counted to its header's length when it ends
def len.blk(
  +acc: List<&2, U32>,
  +rf: U32,
  +ll: U32,
  +mx: U32,
  +ha: {Nat.add(List.length(&2, U32, acc), U32.to_nat(rf)) == U32.to_nat(mx) : Nat},
  +hl: {U32.to_nat(ll) == List.length(&2, U32, acc) : Nat}
) -> {Png.enc.len(List.reverse(&2, U32, acc), 0) == ll : U32}:
  +ra = List.reverse(&2, U32, acc)
  +na = List.length(&2, U32, acc)
  +e_r = {Wp2.len_rev(acc) : {List.length(&2, U32, ra) == na : Nat}}
  +h_b = {Equal.trans(Bool, Nat.is_le(na, U32.to_nat(mx)), Nat.is_le(na, Nat.add(na, U32.to_nat(rf))), True{},
    Equal.cong(Nat, Bool, kk => Nat.is_le(na, kk), U32.to_nat(mx), Nat.add(na, U32.to_nat(rf)), Equal.sym(Nat,
    Nat.add(na, U32.to_nat(rf)), U32.to_nat(mx), ha)), Wp2.nle_add(na, U32.to_nat(rf))) : {Nat.is_le(na,
    U32.to_nat(mx)) == True{} : Bool}}
  +h_r = {R.le_rw_l(na, List.length(&2, U32, ra), U32.to_nat(mx), Equal.sym(Nat, List.length(&2, U32, ra), na, e_r),
    h_b) : {Nat.is_le(List.length(&2, U32, ra), U32.to_nat(mx)) == True{} : Bool}}
  u32.same(Png.enc.len(ra, 0), ll, Equal.trans(Nat, U32.to_nat(Png.enc.len(ra, 0)), na, U32.to_nat(ll), Equal.trans(Nat,
    U32.to_nat(Png.enc.len(ra, 0)), List.length(&2, U32, ra), na, len.of(ra, mx, h_r), e_r), Equal.sym(Nat,
    U32.to_nat(ll), na, hl)))

# no bytes left: the open block is enc.feed's final block
def sim.nil(
  fin: Bool,
  +acc: List<&2, U32>,
  +rf: U32,
  +rp: U32,
  +ll: U32,
  +mx: U32,
  +ha: {Nat.add(List.length(&2, U32, acc), U32.to_nat(rf)) == U32.to_nat(mx) : Nat},
  +hl: {U32.to_nat(ll) == Nat.add(List.length(&2, U32, acc), U32.to_nat(rp)) : Nat},
  hf: fin.ok(fin, rp, rf, 0n)
) -> {List.append(&2, U32, Png.enc.head(fin, ll, (ll .^. 65535 : U32)), List.reverse(&2, U32, acc)) ==
  Png.enc.stored(True{}, List.reverse(&2, U32, acc)) : List<&2, U32>}:
  match fin:
    case False{}:
      (_e_rr, h_lt) = hf
      Empty.absurd({List.append(&2, U32, Png.enc.head(False{}, ll, (ll .^. 65535 : U32)), List.reverse(&2, U32, acc)) ==
        Png.enc.stored(True{}, List.reverse(&2, U32, acc)) : List<&2, U32>}, U32L.false_true(Equal.trans(Bool,
        False{}, Nat.is_lt(U32.to_nat(rp), 0n), True{}, R.lt_zero_false(U32.to_nat(rp)), h_lt)))
    case True{}:
      +e_rp = {hf : {U32.to_nat(rp) == 0n : Nat}}
      +ra = List.reverse(&2, U32, acc)
      +na = List.length(&2, U32, acc)
      +hd = Png.enc.head(True{}, ll, (ll .^. 65535 : U32))
      +hl0 = {Equal.trans(Nat, U32.to_nat(ll), Nat.add(na, 0n), na, Equal.trans(Nat, U32.to_nat(ll), Nat.add(na,
        U32.to_nat(rp)), Nat.add(na, 0n), hl, Equal.cong(Nat, Nat, kk => Nat.add(na, kk), U32.to_nat(rp), 0n, e_rp)),
        R.add_zero(na)) : {U32.to_nat(ll) == na : Nat}}
      +e_len = {len.blk(acc, rf, ll, mx, ha, hl0) : {Png.enc.len(ra, 0) == ll : U32}}
      Equal.trans(List<&2, U32>, List.append(&2, U32, hd, ra), Png.enc.cat(hd, ra), Png.enc.stored(True{}, ra),
        Equal.sym(List<&2, U32>, Png.enc.cat(hd, ra), List.append(&2, U32, hd, ra), Wp2.cat_app(hd, ra)),
        Equal.cong(U32, List<&2, U32>, uu => Png.enc.cat(Png.enc.head(True{}, uu, (uu .^. 65535 : U32)), ra), ll,
          Png.enc.len(ra, 0), Equal.sym(U32, Png.enc.len(ra, 0), ll, e_len)))

# a room that is not zero leaves at.edge nothing to ask
def edge.no(
  +rp: U32,
  +left: U32,
  +plen: U32,
  +pbf: U32,
  +nz: {U32.is_zero(rp) == False{} : Bool}
) -> at.edge(rp, left, plen, pbf):
  ez => Empty.absurd({plen == Png.enc.cap(left) : U32} & {pbf == Png.enc.bf(left) : U32},
    U32L.false_true(Equal.trans(Bool, False{}, U32.is_zero(rp), True{}, Equal.sym(Bool, U32.is_zero(rp), False{}, nz),
    ez)))

# a new block's bytes as bs writes them for length u and BFINAL v: the
# header, the first byte, then the rest of the walk
def open.bs(
  +h: U32,
  +t: List<&2, U32>,
  +l2: U32,
  +uu: U32,
  +vv: U32
) -> List<&2, U32>:
  +nlen = (uu .^. 65535 : U32)
  +room2 = (uu - 1 : U32)
  vv <> Png.enc.byte(uu) <> Png.enc.hi(uu) <> Png.enc.byte(nlen) <> Png.enc.hi(nlen) <> h <> bs(t, U32.is_zero(room2),
    U32.is_eq(room2, 1), room2, l2, Png.enc.cap(l2), Png.enc.bf(l2))

# a new block from left bytes, h then t: bs's bytes are enc.feed's from a
# block holding h alone
def open.feed(
  +h: U32,
  +t: List<&2, U32>,
  +left: U32,
  +mx: U32,
  +ih: {List.append(&2, U32, Png.enc.head(U32.is_le(left, 65535), Png.enc.cap(left), (Png.enc.cap(left) .^. 65535 :
    U32)), h <> bs(t, U32.is_zero((Png.enc.cap(left) - 1 : U32)), U32.is_eq((Png.enc.cap(left) - 1 : U32), 1),
    (Png.enc.cap(left) - 1 : U32), (left - 1 : U32), Png.enc.cap((left - 1 : U32)), Png.enc.bf((left - 1 : U32)))) ==
    Png.enc.feed(t, U32.is_zero((mx - 1 : U32)), (mx - 1 : U32), mx, [h]) : List<&2, U32>}
) -> {open.bs(h, t, (left - 1 : U32), Png.enc.cap(left), Png.enc.bf(left)) == Png.enc.feed(t, U32.is_zero((mx - 1 :
  U32)), (mx - 1 : U32), mx, [h]) : List<&2, U32>}:
  +zz = U32.is_le(left, 65535)
  +cp = Png.enc.cap(left)
  +l2 = (left - 1 : U32)
  +q = bs(t, U32.is_zero((cp - 1 : U32)), U32.is_eq((cp - 1 : U32), 1), (cp - 1 : U32), l2, Png.enc.cap(l2),
    Png.enc.bf(l2))
  Equal.trans(List<&2, U32>, open.bs(h, t, l2, cp, Png.enc.bf(left)), List.append(&2, U32, Png.enc.head(zz, cp, (cp .^.
    65535 : U32)), h <> q), Png.enc.feed(t, U32.is_zero((mx - 1 : U32)), (mx - 1 : U32), mx, [h]),
    hdr(zz, left, h <> q), ih)

# the facts a new block's walk starts from, for sim: the feed holds h, with
# mx - 1 bytes of room; bs has cap(left) - 1 left in the block
def open.ih(
  +h: U32,
  +t: List<&2, U32>,
  +left: U32,
  +mx: U32,
  +emx: {mx == 65535 : U32},
  +hn: {U32.to_nat(left) == 1n+List.length(&2, U32, t) : Nat},
  sim_t: @zn: Bool -> @zl: Bool -> @zf: Bool -> @fin: Bool -> @rf: U32 -> @rp: U32 -> @plen: U32 -> @pbf: U32 ->
    @ll: U32 -> {zn == U32.is_zero(rp) : Bool} -> {zl == U32.is_eq(rp, 1) : Bool} -> {zf == U32.is_zero(rf) : Bool} ->
    {Nat.add(1n, U32.to_nat(rf)) == U32.to_nat(mx) : Nat} -> {U32.to_nat(ll) == Nat.add(1n, U32.to_nat(rp)) : Nat}
    -> {Nat.is_le(U32.to_nat(rp), U32.to_nat(rf)) == True{} : Bool} -> {U32.to_nat((left - 1 : U32)) ==
    List.length(&2, U32, t) : Nat} -> fin.ok(fin, rp, rf, List.length(&2, U32, t)) -> at.edge(rp, (left - 1 : U32),
    plen, pbf) -> sim.ty(t, zn, zl, zf, fin, [h], rf, rp, (left - 1 : U32), plen, pbf, ll, mx)
) -> {open.bs(h, t, (left - 1 : U32), Png.enc.cap(left), Png.enc.bf(left)) == Png.enc.feed(t, U32.is_zero((mx - 1 :
  U32)), (mx - 1 : U32), mx, [h]) : List<&2, U32>}:
  +nt = List.length(&2, U32, t)
  +zz = U32.is_le(left, 65535)
  +cp = Png.enc.cap(left)
  +cm = capm(zz, left, mx)
  +c1 = (cp - 1 : U32)
  +m1 = (mx - 1 : U32)
  +l2 = (left - 1 : U32)
  +nzm = {mx.nz(mx, emx) : {U32.is_zero(mx) == False{} : Bool}}
  +e_cm = {cap.m(zz, left, mx, emx) : {cp == cm : U32}}
  +ezm = {le.mx(left, mx, emx) : {U32.is_le(left, mx) == zz : Bool}}
  +nz_cp = {Equal.trans(Bool, U32.is_zero(cp), U32.is_zero(cm), False{}, Equal.cong(U32, Bool, uu => U32.is_zero(uu),
    cp, cm, e_cm), cap.nz(zz, left, mx, nt, nzm, hn)) : {U32.is_zero(cp) == False{} : Bool}}
  +ha2 = {Equal.sym(Nat, U32.to_nat(mx), 1n+U32.to_nat(m1), Wp1.u32_dec(mx, nzm)) : {Nat.add(1n, U32.to_nat(m1)) ==
    U32.to_nat(mx) : Nat}}
  +hl2 = {Wp1.u32_dec(cp, nz_cp) : {U32.to_nat(cp) == Nat.add(1n, U32.to_nat(c1)) : Nat}}
  +hle2 = {Equal.trans(Bool, Nat.is_le(U32.to_nat(c1), U32.to_nat(m1)), Nat.is_le(U32.to_nat((cm - 1 : U32)),
    U32.to_nat(m1)), True{}, Equal.cong(U32, Bool, uu => Nat.is_le(U32.to_nat((uu - 1 : U32)), U32.to_nat(m1)), cp, cm,
    e_cm), cap.le(zz, left, mx, nt, nzm, ezm, hn)) : {Nat.is_le(U32.to_nat(c1), U32.to_nat(m1)) == True{} : Bool}}
  +hn2 = {Wp1.u32_pred(left, nt, hn) : {U32.to_nat(l2) == nt : Nat}}
  hf2 = {fo.cm(zz, left, mx, nt, emx, cap.fo(zz, left, mx, nt, nzm, ezm, hn)) : fin.ok(zz, c1, m1, nt)}
  open.feed(h, t, left, mx, sim_t(U32.is_zero(c1), U32.is_eq(c1, 1), U32.is_zero(m1), zz, m1, c1, Png.enc.cap(l2),
    Png.enc.bf(l2), cp, {==}, {==}, {==}, ha2, hl2, hle2, hn2, hf2, _ez => ({==}, {==})))

# a block boundary with bytes left: the full block closes and a new one opens
def sim.edge(
  fin: Bool,
  +h: U32,
  +t: List<&2, U32>,
  +acc: List<&2, U32>,
  +rf: U32,
  +rp: U32,
  +left: U32,
  +plen: U32,
  +pbf: U32,
  +ll: U32,
  +mx: U32,
  +zf: Bool,
  +hzf: {zf == U32.is_zero(rf) : Bool},
  +ha: {Nat.add(List.length(&2, U32, acc), U32.to_nat(rf)) == U32.to_nat(mx) : Nat},
  +hl: {U32.to_nat(ll) == Nat.add(List.length(&2, U32, acc), U32.to_nat(rp)) : Nat},
  +e0: {U32.to_nat(rp) == 0n : Nat},
  +e_ob: {open.bs(h, t, (left - 1 : U32), Png.enc.cap(left), Png.enc.bf(left)) == Png.enc.feed(t, U32.is_zero((mx -
    1 : U32)), (mx - 1 : U32), mx, [h]) : List<&2, U32>},
  hf: fin.ok(fin, rp, rf, 1n+List.length(&2, U32, t)),
  pe: {plen == Png.enc.cap(left) : U32} & {pbf == Png.enc.bf(left) : U32}
) -> {List.append(&2, U32, Png.enc.head(fin, ll, (ll .^. 65535 : U32)), List.reverse.go(&2, U32, acc, open.bs(h, t,
  (left - 1 : U32), plen, pbf))) == Png.enc.feed(h <> t, zf, rf, mx, acc) : List<&2, U32>}:
  match fin:
    case True{}:
      Empty.absurd({List.append(&2, U32, Png.enc.head(True{}, ll, (ll .^. 65535 : U32)), List.reverse.go(&2, U32, acc,
        open.bs(h, t, (left - 1 : U32), plen, pbf))) == Png.enc.feed(h <> t, zf, rf, mx, acc) : List<&2, U32>},
        Wp1.zero_succ(List.length(&2, U32, t), Equal.trans(Nat, 0n, U32.to_nat(rp), 1n+List.length(&2, U32, t),
        Equal.sym(Nat, U32.to_nat(rp), 0n, e0), hf)))
    case False{}:
      (e_rr, _h_lt) = hf
      (e_plen, e_pbf) = pe
      +na = List.length(&2, U32, acc)
      +ra = List.reverse(&2, U32, acc)
      +l2 = (left - 1 : U32)
      +cp = Png.enc.cap(left)
      +e_rf0 = {Equal.trans(Nat, U32.to_nat(rf), U32.to_nat(rp), 0n, Equal.sym(Nat, U32.to_nat(rp), U32.to_nat(rf),
        e_rr), e0) : {U32.to_nat(rf) == 0n : Nat}}
      +e_zf = {Equal.trans(Bool, zf, U32.is_zero(rf), True{}, hzf, zero.is(rf, e_rf0)) : {zf == True{} : Bool}}
      +ff = Png.enc.feed(t, U32.is_zero((mx - 1 : U32)), (mx - 1 : U32), mx, [h])
      +hd0 = Png.enc.head(False{}, ll, (ll .^. 65535 : U32))
      +hl0 = {Equal.trans(Nat, U32.to_nat(ll), Nat.add(na, 0n), na, Equal.trans(Nat, U32.to_nat(ll), Nat.add(na,
        U32.to_nat(rp)), Nat.add(na, 0n), hl, Equal.cong(Nat, Nat, kk => Nat.add(na, kk), U32.to_nat(rp), 0n, e0)),
        R.add_zero(na)) : {U32.to_nat(ll) == na : Nat}}
      +e_len = {len.blk(acc, rf, ll, mx, ha, hl0) : {Png.enc.len(ra, 0) == ll : U32}}
      +e_bs = {Equal.trans(List<&2, U32>, open.bs(h, t, l2, plen, pbf), open.bs(h, t, l2, cp, Png.enc.bf(left)), ff,
        Equal.trans(List<&2, U32>, open.bs(h, t, l2, plen, pbf), open.bs(h, t, l2, cp, pbf), open.bs(h, t, l2, cp,
          Png.enc.bf(left)), Equal.cong(U32, List<&2, U32>, uu => open.bs(h, t, l2, uu, pbf), plen, cp, e_plen),
          Equal.cong(U32, List<&2, U32>, uu => open.bs(h, t, l2, cp, uu), pbf, Png.enc.bf(left), e_pbf)),
        e_ob) : {open.bs(h, t, l2, plen, pbf) == ff : List<&2, U32>}}
      Equal.trans(List<&2, U32>, List.append(&2, U32, hd0, List.reverse.go(&2, U32, acc, open.bs(h, t, l2, plen, pbf))),
        List.append(&2, U32, List.append(&2, U32, hd0, ra), ff), Png.enc.feed(h <> t, zf, rf, mx, acc),
        Equal.trans(List<&2, U32>, List.append(&2, U32, hd0, List.reverse.go(&2, U32, acc, open.bs(h, t, l2, plen,
          pbf))), List.append(&2, U32, hd0, List.append(&2, U32, ra, ff)), List.append(&2, U32, List.append(&2, U32,
          hd0, ra), ff),
          Equal.trans(List<&2, U32>, List.append(&2, U32, hd0, List.reverse.go(&2, U32, acc, open.bs(h, t, l2, plen,
            pbf))), List.append(&2, U32, hd0, List.reverse.go(&2, U32, acc, ff)), List.append(&2, U32, hd0,
            List.append(&2, U32, ra, ff)),
            Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.append(&2, U32, hd0, List.reverse.go(&2, U32, acc,
              ys)), open.bs(h, t, l2, plen, pbf), ff, e_bs),
            Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.append(&2, U32, hd0, ys), List.reverse.go(&2, U32, acc,
              ff), List.append(&2, U32, ra, ff), W9.revgo_acc(acc, [], ff))),
          Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, hd0, ra), ff), List.append(&2, U32, hd0,
            List.append(&2, U32, ra, ff)), Wp2.app_assoc(hd0, ra, ff))),
        Equal.trans(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, hd0, ra), ff), Png.enc.feed(h <> t, True{},
          rf, mx, acc), Png.enc.feed(h <> t, zf, rf, mx, acc),
          Equal.trans(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, hd0, ra), ff), List.append(&2, U32,
            Png.enc.cat(hd0, ra), ff), Png.enc.feed(h <> t, True{}, rf, mx, acc),
            Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.append(&2, U32, ys, ff), List.append(&2, U32, hd0, ra),
              Png.enc.cat(hd0, ra), Equal.sym(List<&2, U32>, Png.enc.cat(hd0, ra), List.append(&2, U32, hd0, ra),
              Wp2.cat_app(hd0, ra))),
            Equal.trans(List<&2, U32>, List.append(&2, U32, Png.enc.cat(hd0, ra), ff), Png.enc.cat(Png.enc.cat(hd0,
              ra), ff), Png.enc.feed(h <> t, True{}, rf, mx, acc),
              Equal.sym(List<&2, U32>, Png.enc.cat(Png.enc.cat(hd0, ra), ff), List.append(&2, U32, Png.enc.cat(hd0,
                ra), ff), Wp2.cat_app(Png.enc.cat(hd0, ra), ff)),
              Equal.cong(U32, List<&2, U32>, uu => Png.enc.cat(Png.enc.cat(Png.enc.head(False{}, uu, (uu .^. 65535 :
                U32)), ra), ff), ll, Png.enc.len(ra, 0), Equal.sym(U32, Png.enc.len(ra, 0), ll, e_len)))),
          Equal.cong(Bool, List<&2, U32>, zb => Png.enc.feed(h <> t, zb, rf, mx, acc), True{}, zf, Equal.sym(Bool,
            zf, True{}, e_zf))))

# bs against enc.feed: the open block (acc, newest first, with rf bytes of
# room in the feed) under a header of length ll and BFINAL fin, then bs from
# rp bytes left in the block, are enc.feed's blocks
def sim(
  xs: List<&2, U32>,
  znew: Bool,
  zlast: Bool,
  +zf: Bool,
  +fin: Bool,
  +acc: List<&2, U32>,
  +rf: U32,
  +rp: U32,
  +left: U32,
  +plen: U32,
  +pbf: U32,
  +ll: U32,
  +mx: U32,
  +emx: {mx == 65535 : U32},
  +hzn: {znew == U32.is_zero(rp) : Bool},
  +hzl: {zlast == U32.is_eq(rp, 1) : Bool},
  +hzf: {zf == U32.is_zero(rf) : Bool},
  +ha: {Nat.add(List.length(&2, U32, acc), U32.to_nat(rf)) == U32.to_nat(mx) : Nat},
  +hl: {U32.to_nat(ll) == Nat.add(List.length(&2, U32, acc), U32.to_nat(rp)) : Nat},
  +hle: {Nat.is_le(U32.to_nat(rp), U32.to_nat(rf)) == True{} : Bool},
  +hn: {U32.to_nat(left) == List.length(&2, U32, xs) : Nat},
  hf: fin.ok(fin, rp, rf, List.length(&2, U32, xs)),
  hb: at.edge(rp, left, plen, pbf)
) -> sim.ty(xs, znew, zlast, zf, fin, acc, rf, rp, left, plen, pbf, ll, mx):
  match xs znew zlast:
    case Nil{} _zn _zl:
      sim.nil(fin, acc, rf, rp, ll, mx, ha, hl, hf)
    case +h <> +t False{} False{}:
      +rp2 = (rp - 1 : U32)
      +rf2 = (rf - 1 : U32)
      +l2 = (left - 1 : U32)
      +nt = List.length(&2, U32, t)
      +na = List.length(&2, U32, acc)
      +nz_rp = {Equal.sym(Bool, False{}, U32.is_zero(rp), hzn) : {U32.is_zero(rp) == False{} : Bool}}
      +e_rp = {Wp1.u32_dec(rp, nz_rp) : {U32.to_nat(rp) == 1n+U32.to_nat(rp2) : Nat}}
      +nz_rp2 = {two(rp, hzn, hzl) : {U32.is_zero(rp2) == False{} : Bool}}
      +h_rf = {R.le_rw_l(U32.to_nat(rp), 1n+U32.to_nat(rp2), U32.to_nat(rf), e_rp, hle) :
        {Nat.is_le(1n+U32.to_nat(rp2), U32.to_nat(rf)) == True{} : Bool}}
      +nz_rf = {pos(rf, U32.to_nat(rp2), h_rf) : {U32.is_zero(rf) == False{} : Bool}}
      +e_rf = {Wp1.u32_dec(rf, nz_rf) : {U32.to_nat(rf) == 1n+U32.to_nat(rf2) : Nat}}
      +e_zf = {Equal.trans(Bool, zf, U32.is_zero(rf), False{}, hzf, nz_rf) : {zf == False{} : Bool}}
      +ha2 = {shift(na, rf, rf2, U32.to_nat(mx), e_rf, ha) : {Nat.add(1n+na, U32.to_nat(rf2)) == U32.to_nat(mx) : Nat}}
      +hl2 = {Equal.sym(Nat, Nat.add(1n+na, U32.to_nat(rp2)), U32.to_nat(ll), shift(na, rp, rp2, U32.to_nat(ll), e_rp,
        Equal.sym(Nat, U32.to_nat(ll), Nat.add(na, U32.to_nat(rp)), hl))) : {U32.to_nat(ll) == Nat.add(1n+na,
        U32.to_nat(rp2)) : Nat}}
      +hle2 = {R.le_rw_r(1n+U32.to_nat(rp2), U32.to_nat(rf), 1n+U32.to_nat(rf2), e_rf, h_rf) :
        {Nat.is_le(U32.to_nat(rp2), U32.to_nat(rf2)) == True{} : Bool}}
      +hn2 = {Wp1.u32_pred(left, nt, hn) : {U32.to_nat(l2) == nt : Nat}}
      hf2 = {fo.dec(fin, rp, rf, rp2, rf2, nt, e_rp, e_rf, hf) : fin.ok(fin, rp2, rf2, nt)}
      Equal.trans(List<&2, U32>, List.append(&2, U32, Png.enc.head(fin, ll, (ll .^. 65535 : U32)), List.reverse.go(&2,
        U32, acc, bs(h <> t, False{}, False{}, rp, left, plen, pbf))), Png.enc.feed(h <> t, False{}, rf, mx, acc),
        Png.enc.feed(h <> t, zf, rf, mx, acc),
        sim(t, False{}, U32.is_eq(rp2, 1), U32.is_zero(rf2), fin, h <> acc, rf2, rp2, l2, plen, pbf, ll, mx, emx,
          Equal.sym(Bool, U32.is_zero(rp2), False{}, nz_rp2), {==}, {==}, ha2, hl2, hle2, hn2, hf2, edge.no(rp2, l2,
          plen, pbf, nz_rp2)),
        Equal.cong(Bool, List<&2, U32>, zb => Png.enc.feed(h <> t, zb, rf, mx, acc), False{}, zf, Equal.sym(Bool, zf,
          False{}, e_zf)))
    case +h <> +t False{} True{}:
      +rf2 = (rf - 1 : U32)
      +l2 = (left - 1 : U32)
      +nt = List.length(&2, U32, t)
      +na = List.length(&2, U32, acc)
      +e_rp = {one.val(rp, hzl) : {U32.to_nat(rp) == 1n+U32.to_nat(0) : Nat}}
      +h_rf = {R.le_rw_l(U32.to_nat(rp), 1n, U32.to_nat(rf), e_rp, hle) : {Nat.is_le(1n, U32.to_nat(rf)) == True{} :
        Bool}}
      +nz_rf = {pos(rf, 0n, h_rf) : {U32.is_zero(rf) == False{} : Bool}}
      +e_rf = {Wp1.u32_dec(rf, nz_rf) : {U32.to_nat(rf) == 1n+U32.to_nat(rf2) : Nat}}
      +e_zf = {Equal.trans(Bool, zf, U32.is_zero(rf), False{}, hzf, nz_rf) : {zf == False{} : Bool}}
      +ha2 = {shift(na, rf, rf2, U32.to_nat(mx), e_rf, ha) : {Nat.add(1n+na, U32.to_nat(rf2)) == U32.to_nat(mx) : Nat}}
      +hl2 = {Equal.sym(Nat, Nat.add(1n+na, U32.to_nat(0)), U32.to_nat(ll), shift(na, rp, 0, U32.to_nat(ll), e_rp,
        Equal.sym(Nat, U32.to_nat(ll), Nat.add(na, U32.to_nat(rp)), hl))) : {U32.to_nat(ll) == Nat.add(1n+na,
        U32.to_nat(0)) : Nat}}
      +hle2 = {R.le_zero(U32.to_nat(rf2)) : {Nat.is_le(U32.to_nat(0), U32.to_nat(rf2)) == True{} : Bool}}
      +hn2 = {Wp1.u32_pred(left, nt, hn) : {U32.to_nat(l2) == nt : Nat}}
      hf2 = {fo.dec(fin, rp, rf, 0, rf2, nt, e_rp, e_rf, hf) : fin.ok(fin, 0, rf2, nt)}
      Equal.trans(List<&2, U32>, List.append(&2, U32, Png.enc.head(fin, ll, (ll .^. 65535 : U32)), List.reverse.go(&2,
        U32, acc, bs(h <> t, False{}, True{}, rp, left, plen, pbf))), Png.enc.feed(h <> t, False{}, rf, mx, acc),
        Png.enc.feed(h <> t, zf, rf, mx, acc),
        sim(t, True{}, False{}, U32.is_zero(rf2), fin, h <> acc, rf2, 0, l2, Png.enc.cap(l2), Png.enc.bf(l2), ll, mx,
          emx, {==}, {==}, {==}, ha2, hl2, hle2, hn2, hf2, _ez => ({==}, {==})),
        Equal.cong(Bool, List<&2, U32>, zb => Png.enc.feed(h <> t, zb, rf, mx, acc), False{}, zf, Equal.sym(Bool, zf,
          False{}, e_zf)))
    case +h <> +t True{} _zl:
      +l2 = (left - 1 : U32)
      +ez = {Equal.sym(Bool, True{}, U32.is_zero(rp), hzn) : {U32.is_zero(rp) == True{} : Bool}}
      +e0 = {zero.val(rp, hzn) : {U32.to_nat(rp) == 0n : Nat}}
      +e_ob = {open.ih(h, t, left, mx, emx, hn, zn => zl => zb => fb => rf3 => rp3 => pl3 => pb3 => ll3 => a1 => a2 =>
        a3 => a4 => a5 => a6 => a7 => a8 => a9 => sim(t, zn, zl, zb, fb, [h], rf3, rp3, l2, pl3, pb3, ll3, mx, emx,
        a1, a2, a3, a4, a5, a6, a7, a8, a9)) : {open.bs(h, t, l2, Png.enc.cap(left), Png.enc.bf(left)) ==
        Png.enc.feed(t, U32.is_zero((mx - 1 : U32)), (mx - 1 : U32), mx, [h]) : List<&2, U32>}}
      sim.edge(fin, h, t, acc, rf, rp, left, plen, pbf, ll, mx, zf, hzf, ha, hl, e0, e_ob, hf, hb(ez))

# the first block: bs from the start writes enc.feed's blocks for every
# non-empty list of left bytes
def sim.start(
  +h: U32,
  +t: List<&2, U32>,
  +left: U32,
  +mx: U32,
  +emx: {mx == 65535 : U32},
  +hn: {U32.to_nat(left) == 1n+List.length(&2, U32, t) : Nat}
) -> {bs(h <> t, True{}, False{}, 0, left, Png.enc.cap(left), Png.enc.bf(left)) == Png.enc.feed(h <> t, False{}, mx,
  mx, []) : List<&2, U32>}:
  +l2 = (left - 1 : U32)
  open.ih(h, t, left, mx, emx, hn, zn => zl => zb => fb => rf3 => rp3 => pl3 => pb3 => ll3 => a1 => a2 => a3 => a4 =>
    a5 => a6 => a7 => a8 => a9 => sim(t, zn, zl, zb, fb, [h], rf3, rp3, l2, pl3, pb3, ll3, mx, emx, a1, a2, a3, a4, a5,
    a6, a7, a8, a9))

# enc.blocks at 65535 for a list longer than one block is bs from the start
def sim.blocks(
  xs: List<&2, U32>,
  +mx: U32,
  +emx: {mx == 65535 : U32},
  +hn: {U32.to_nat(Png.enc.len(xs, 0)) == List.length(&2, U32, xs) : Nat},
  +hbig: {U32.is_le(Png.enc.len(xs, 0), 65535) == False{} : Bool}
) -> {Png.enc.blocks(65535, xs) == bs(xs, True{}, False{}, 0, Png.enc.len(xs, 0), Png.enc.cap(Png.enc.len(xs, 0)),
  Png.enc.bf(Png.enc.len(xs, 0))) : List<&2, U32>}:
  match xs:
    case Nil{}:
      Empty.absurd({Png.enc.blocks(65535, []) == bs([], True{}, False{}, 0, 0, Png.enc.cap(0), Png.enc.bf(0)) :
        List<&2, U32>}, U32L.false_true(Equal.sym(Bool, True{}, False{}, hbig)))
    case +h <> +t:
      +nn = Png.enc.len(h <> t, 0)
      +bb = bs(h <> t, True{}, False{}, 0, nn, Png.enc.cap(nn), Png.enc.bf(nn))
      Equal.trans(List<&2, U32>, Png.enc.blocks(65535, h <> t), Png.enc.blocks.fit(False{}, 65535, nn, h <> t), bb,
        Equal.cong(Bool, List<&2, U32>, zb => Png.enc.blocks.fit(zb, 65535, nn, h <> t), U32.is_le(nn, 65535), False{},
          hbig),
        Equal.trans(List<&2, U32>, Png.enc.feed(h <> t, False{}, 65535, 65535, []), Png.enc.feed(h <> t, False{}, mx, mx,
          []), bb, Equal.cong(U32, List<&2, U32>, uu => Png.enc.feed(h <> t, False{}, uu, uu, []), 65535, mx,
          Equal.sym(U32, mx, 65535, emx)), Equal.sym(List<&2, U32>, bb, Png.enc.feed(h <> t, False{}, mx, mx, []),
          sim.start(h, t, nn, mx, emx, hn))))

# ---- D. U32.div and U32.mod ----

# a word shifted left with c coming in: nothing falls out, and it is c + 2 w
def sho.ok(nn: Nat, +cc: Bool, +ww: Word(nn), pp: Bool & Word(nn)) -> Type:
  match pp:
    case (tt, ss):
      {tt == False{} : Bool} & {Word.to_nat(nn, ss) == Nat.add(R.bit(cc), Nat.double(Word.to_nat(nn, ww))) : Nat}

# one step of so: the lower bits shifted, then this bit in front
def sho.step(
  +pp: Nat,
  +cc: Bool,
  +bb: Bool,
  +tt: Word(pp),
  yy: Bool & Word(pp),
  ih: sho.ok(pp, bb, tt, yy)
) -> sho.ok(1n+pp, cc, WCon{bb, tt}, Word.shl.out.con(pp, cc, yy)):
  match yy:
    case (hi, +t2):
      (e_hi, e_t2) = ih
      +vt = Word.to_nat(pp, tt)
      (e_hi, Equal.trans(Nat, Word.to_nat(1n+pp, WCon{cc, t2}), Nat.add(R.bit(cc), Nat.double(Word.to_nat(pp, t2))),
        Nat.add(R.bit(cc), Nat.double(Word.to_nat(1n+pp, WCon{bb, tt}))), R.to_nat_con(pp, cc, t2),
        Equal.cong(Nat, Nat, kk => Nat.add(R.bit(cc), Nat.double(kk)), Word.to_nat(pp, t2), Word.to_nat(1n+pp,
          WCon{bb, tt}), Equal.trans(Nat, Word.to_nat(pp, t2), Nat.add(R.bit(bb), Nat.double(vt)), Word.to_nat(1n+pp,
          WCon{bb, tt}), e_t2, Equal.sym(Nat, Word.to_nat(1n+pp, WCon{bb, tt}), Nat.add(R.bit(bb), Nat.double(vt)),
          R.to_nat_con(pp, bb, tt))))))

# shifting a word left with c coming in, when c + 2 w is at most a word's value
def sho(
  nn: Nat,
  +cc: Bool,
  +ww: Word(nn),
  +tw: Word(nn),
  +hh: {Nat.is_le(Nat.add(R.bit(cc), Nat.double(Word.to_nat(nn, ww))), Word.to_nat(nn, tw)) == True{} : Bool}
) -> sho.ok(nn, cc, ww, Word.shl.out(nn, cc, ww)):
  match nn:
    case 0n:
      match cc ww tw:
        case False{} WNil{} WNil{}:
          ({==}, {==})
        case True{} WNil{} WNil{}:
          Empty.absurd(sho.ok(0n, True{}, WNil{}, (True{}, WNil{})), U32L.false_true(hh))
    case 1n+(+pp):
      match ww tw:
        case WCon{+bb, +tt} WCon{+sb, +st}:
          +vt = Word.to_nat(pp, tt)
          +vs = Word.to_nat(pp, st)
          +wb = Word.to_nat(1n+pp, WCon{bb, tt})
          +ws = Word.to_nat(1n+pp, WCon{sb, st})
          +xb = Nat.add(R.bit(bb), Nat.double(vt))
          +xs = Nat.add(R.bit(sb), Nat.double(vs))
          +h0 = {R.le_add_l(R.bit(cc), Nat.double(wb), ws, hh) : {Nat.is_le(Nat.double(wb), ws) == True{} : Bool}}
          +h1 = {R.le_rw_r(Nat.double(xb), ws, xs, R.to_nat_con(pp, sb, st), R.le_rw_l(Nat.double(wb), Nat.double(xb),
            ws, Equal.cong(Nat, Nat, kk => Nat.double(kk), wb, xb, R.to_nat_con(pp, bb, tt)), h0)) :
            {Nat.is_le(Nat.double(xb), xs) == True{} : Bool}}
          +h2 = {R.le_half(sb, xb, vs, h1) : {Nat.is_le(xb, vs) == True{} : Bool}}
          sho.step(pp, cc, bb, tt, Word.shl.out(pp, bb, tt), sho(pp, bb, tt, st, h2))

# at least in Cmp is at most the other way
def ge.le(aa: Nat, bb: Nat, +hh: {Cmp.is_ge(Nat.cmp(aa, bb)) == True{} : Bool}) -> {Nat.is_le(bb, aa) == True{} :
  Bool}:
  match aa bb:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({Nat.is_le(1n+bp, 0n) == True{} : Bool}, U32L.false_true(hh))
    case 1n+_ap 0n:
      {==}
    case 1n+ap 1n+bp:
      ge.le(ap, bp, hh)

# not at least in Cmp is below
def nge.lt(aa: Nat, bb: Nat, +hh: {Cmp.is_ge(Nat.cmp(aa, bb)) == False{} : Bool}) -> {Nat.is_lt(aa, bb) == True{} :
  Bool}:
  match aa bb:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, U32L.false_true(Equal.sym(Bool, True{}, False{}, hh)))
    case 0n 1n+_bp:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.is_lt(1n+ap, 0n) == True{} : Bool}, U32L.false_true(Equal.sym(Bool, True{}, False{}, hh)))
    case 1n+ap 1n+bp:
      nge.lt(ap, bp, hh)

# U32.is_ge is Nat's
def u.ge(+uu: U32, +vv: U32) -> {U32.is_ge(uu, vv) == Cmp.is_ge(Nat.cmp(U32.to_nat(uu), U32.to_nat(vv))) : Bool}:
  Equal.cong(Cmp, Bool, cc => Cmp.is_ge(cc), U32.cmp(uu, vv), Nat.cmp(U32.to_nat(uu), U32.to_nat(vv)), Wp2.u_cmp(uu,
    vv))

# a bit plus x is below y when 2 plus x is at most y
def bit.lt(
  aa: Bool,
  +xx: Nat,
  +yy: Nat,
  +hh: {Nat.is_le(2n+xx, yy) == True{} : Bool}
) -> {Nat.is_lt(Nat.add(R.bit(aa), xx), yy) == True{} : Bool}:
  match aa:
    case False{}:
      Equal.trans(Bool, Nat.is_lt(xx, yy), Nat.is_le(1n+xx, yy), True{}, R.lt_le_succ(xx, yy), R.le_trans(1n+xx, 2n+xx,
        yy, R.le_succ(1n+xx), hh))
    case True{}:
      Equal.trans(Bool, Nat.is_lt(1n+xx, yy), Nat.is_le(2n+xx, yy), True{}, R.lt_le_succ(1n+xx, yy), hh)

# 2 r and a bit is below 2 b when r is below b
def dbl.lt(
  +aa: Bool,
  +rn: Nat,
  +bn: Nat,
  +hh: {Nat.is_lt(rn, bn) == True{} : Bool}
) -> {Nat.is_lt(Nat.add(R.bit(aa), Nat.double(rn)), Nat.add(bn, bn)) == True{} : Bool}:
  +h1 = {Equal.trans(Bool, Nat.is_le(1n+rn, bn), Nat.is_lt(rn, bn), True{}, Equal.sym(Bool, Nat.is_lt(rn, bn),
    Nat.is_le(1n+rn, bn), R.lt_le_succ(rn, bn)), hh) : {Nat.is_le(1n+rn, bn) == True{} : Bool}}
  +h2 = {R.le_add_both(1n+rn, bn, 1n+rn, bn, h1, h1) : {Nat.is_le(Nat.add(1n+rn, 1n+rn), Nat.add(bn, bn)) == True{} :
    Bool}}
  +h3 = {Equal.trans(Nat, 2n+Nat.double(rn), 2n+Nat.add(rn, rn), Nat.add(1n+rn, 1n+rn), Equal.cong(Nat, Nat, kk =>
    2n+kk, Nat.double(rn), Nat.add(rn, rn), R.double_add(rn)), Equal.cong(Nat, Nat, kk => 1n+kk, 1n+Nat.add(rn, rn),
    Nat.add(rn, 1n+rn), Equal.sym(Nat, Nat.add(rn, 1n+rn), 1n+Nat.add(rn, rn), R.add_succ(rn, rn)))) :
    {2n+Nat.double(rn) == Nat.add(1n+rn, 1n+rn) : Nat}}
  +h4 = {R.le_rw_l(Nat.add(1n+rn, 1n+rn), 2n+Nat.double(rn), Nat.add(bn, bn), Equal.sym(Nat, 2n+Nat.double(rn),
    Nat.add(1n+rn, 1n+rn), h3), h2) : {Nat.is_le(2n+Nat.double(rn), Nat.add(bn, bn)) == True{} : Bool}}
  bit.lt(aa, Nat.double(rn), Nat.add(bn, bn), h4)

# a + 2 (q b + r) is 2 q b + (a + 2 r)
def alg.lhs(
  +an: Nat,
  +qb: Nat,
  +rn: Nat
) -> {Nat.add(an, Nat.double(Nat.add(qb, rn))) == Nat.add(Nat.double(qb), Nat.add(an, Nat.double(rn))) : Nat}:
  Equal.trans(Nat, Nat.add(an, Nat.double(Nat.add(qb, rn))), Nat.add(an, Nat.add(Nat.double(qb), Nat.double(rn))),
    Nat.add(Nat.double(qb), Nat.add(an, Nat.double(rn))), Equal.cong(Nat, Nat, kk => Nat.add(an, kk),
    Nat.double(Nat.add(qb, rn)), Nat.add(Nat.double(qb), Nat.double(rn)), R.double_dist(qb, rn)), R.add_swap(an,
    Nat.double(qb), Nat.double(rn)))

# what U32.divmod.go gives: the word is q * b + r, with r below b
def dm.ok(mm: Nat, +aw: Word(mm), +bu: U32, qr: Word(mm) & U32) -> Type:
  match qr:
    case (+qw, +ru):
      {Word.to_nat(mm, aw) == Nat.add(Nat.mul(Word.to_nat(mm, qw), U32.to_nat(bu)), U32.to_nat(ru)) : Nat} &
        {Nat.is_lt(U32.to_nat(ru), U32.to_nat(bu)) == True{} : Bool}

# the step where the new bit makes the remainder reach b: q gets a 1 and b comes off
def dm.sub(
  +pp: Nat,
  +a0: Bool,
  +hi: Word(pp),
  +bu: U32,
  +qw: Word(pp),
  +rn: Nat,
  +su: U32,
  +e1: {Word.to_nat(pp, hi) == Nat.add(Nat.mul(Word.to_nat(pp, qw), U32.to_nat(bu)), rn) : Nat},
  +es: {U32.to_nat(su) == Nat.add(R.bit(a0), Nat.double(rn)) : Nat},
  +hge: {Nat.is_le(U32.to_nat(bu), U32.to_nat(su)) == True{} : Bool},
  +hlt: {Nat.is_lt(U32.to_nat(su), Nat.add(U32.to_nat(bu), U32.to_nat(bu))) == True{} : Bool}
) -> dm.ok(1n+pp, WCon{a0, hi}, bu, (WCon{True{}, qw}, U32.sub(su, bu))):
  +bn = U32.to_nat(bu)
  +sn = U32.to_nat(su)
  +qn = Word.to_nat(pp, qw)
  +qb = Nat.mul(qn, bn)
  +an = R.bit(a0)
  +dd = Nat.mul(Nat.double(qn), bn)
  +e_sub = {R.u32_sub_nat(su, bu, hge) : {U32.to_nat(U32.sub(su, bu)) == Nat.sub(sn, bn) : Nat}}
  +e_l = {Equal.trans(Nat, Word.to_nat(1n+pp, WCon{a0, hi}), Nat.add(an, Nat.double(Nat.add(qb, rn))),
    Nat.add(Nat.double(qb), Nat.add(an, Nat.double(rn))), Equal.trans(Nat, Word.to_nat(1n+pp, WCon{a0, hi}),
    Nat.add(an, Nat.double(Word.to_nat(pp, hi))), Nat.add(an, Nat.double(Nat.add(qb, rn))), R.to_nat_con(pp, a0, hi),
    Equal.cong(Nat, Nat, kk => Nat.add(an, Nat.double(kk)), Word.to_nat(pp, hi), Nat.add(qb, rn), e1)), alg.lhs(an, qb,
    rn)) : {Word.to_nat(1n+pp, WCon{a0, hi}) == Nat.add(Nat.double(qb), Nat.add(an, Nat.double(rn))) : Nat}}
  +e_r = {Equal.trans(Nat, Nat.add(Nat.add(bn, dd), Nat.sub(sn, bn)), Nat.add(dd, sn), Nat.add(Nat.double(qb),
    Nat.add(an, Nat.double(rn))),
    Equal.trans(Nat, Nat.add(Nat.add(bn, dd), Nat.sub(sn, bn)), Nat.add(dd, Nat.add(bn, Nat.sub(sn, bn))), Nat.add(dd,
      sn),
      Equal.trans(Nat, Nat.add(Nat.add(bn, dd), Nat.sub(sn, bn)), Nat.add(bn, Nat.add(dd, Nat.sub(sn, bn))),
        Nat.add(dd, Nat.add(bn, Nat.sub(sn, bn))), R.add_assoc(bn, dd, Nat.sub(sn, bn)), R.add_swap(bn, dd,
        Nat.sub(sn, bn))),
      Equal.cong(Nat, Nat, kk => Nat.add(dd, kk), Nat.add(bn, Nat.sub(sn, bn)), sn, R.add_sub(bn, sn, hge))),
    Equal.trans(Nat, Nat.add(dd, sn), Nat.add(Nat.double(qb), sn), Nat.add(Nat.double(qb), Nat.add(an,
      Nat.double(rn))), Equal.cong(Nat, Nat, kk => Nat.add(kk, sn), dd, Nat.double(qb), R.mul_double(qn, bn)),
      Equal.cong(Nat, Nat, kk => Nat.add(Nat.double(qb), kk), sn, Nat.add(an, Nat.double(rn)), es))) :
    {Nat.add(Nat.add(bn, dd), Nat.sub(sn, bn)) == Nat.add(Nat.double(qb), Nat.add(an, Nat.double(rn))) : Nat}}
  +e_all = {Equal.trans(Nat, Word.to_nat(1n+pp, WCon{a0, hi}), Nat.add(Nat.double(qb), Nat.add(an, Nat.double(rn))),
    Nat.add(Nat.add(bn, dd), U32.to_nat(U32.sub(su, bu))), e_l, Equal.trans(Nat, Nat.add(Nat.double(qb), Nat.add(an,
    Nat.double(rn))), Nat.add(Nat.add(bn, dd), Nat.sub(sn, bn)), Nat.add(Nat.add(bn, dd), U32.to_nat(U32.sub(su, bu))),
    Equal.sym(Nat, Nat.add(Nat.add(bn, dd), Nat.sub(sn, bn)), Nat.add(Nat.double(qb), Nat.add(an, Nat.double(rn))),
    e_r), Equal.cong(Nat, Nat, kk => Nat.add(Nat.add(bn, dd), kk), Nat.sub(sn, bn), U32.to_nat(U32.sub(su, bu)),
    Equal.sym(Nat, U32.to_nat(U32.sub(su, bu)), Nat.sub(sn, bn), e_sub)))) : {Word.to_nat(1n+pp, WCon{a0, hi}) ==
    Nat.add(Nat.add(bn, dd), U32.to_nat(U32.sub(su, bu))) : Nat}}
  +l_sub = {R.lt_rw_l(Nat.sub(sn, bn), U32.to_nat(U32.sub(su, bu)), bn, Equal.sym(Nat, U32.to_nat(U32.sub(su, bu)),
    Nat.sub(sn, bn), e_sub), R.sub_lt(bn, sn, bn, hge, hlt)) : {Nat.is_lt(U32.to_nat(U32.sub(su, bu)), bn) == True{} :
    Bool}}
  (e_all, l_sub)

# the step where the remainder stays below b: q gets a 0
def dm.keep(
  +pp: Nat,
  +a0: Bool,
  +hi: Word(pp),
  +bu: U32,
  +qw: Word(pp),
  +rn: Nat,
  +su: U32,
  +e1: {Word.to_nat(pp, hi) == Nat.add(Nat.mul(Word.to_nat(pp, qw), U32.to_nat(bu)), rn) : Nat},
  +es: {U32.to_nat(su) == Nat.add(R.bit(a0), Nat.double(rn)) : Nat},
  +hlt: {Nat.is_lt(U32.to_nat(su), U32.to_nat(bu)) == True{} : Bool}
) -> dm.ok(1n+pp, WCon{a0, hi}, bu, (WCon{False{}, qw}, su)):
  +bn = U32.to_nat(bu)
  +qn = Word.to_nat(pp, qw)
  +qb = Nat.mul(qn, bn)
  +an = R.bit(a0)
  +e_all = {Equal.trans(Nat, Word.to_nat(1n+pp, WCon{a0, hi}), Nat.add(Nat.double(qb), Nat.add(an, Nat.double(rn))),
    Nat.add(Nat.mul(Nat.double(qn), bn), U32.to_nat(su)), Equal.trans(Nat, Word.to_nat(1n+pp, WCon{a0, hi}),
    Nat.add(an, Nat.double(Nat.add(qb, rn))), Nat.add(Nat.double(qb), Nat.add(an, Nat.double(rn))), Equal.trans(Nat,
    Word.to_nat(1n+pp, WCon{a0, hi}), Nat.add(an, Nat.double(Word.to_nat(pp, hi))), Nat.add(an, Nat.double(Nat.add(qb,
    rn))), R.to_nat_con(pp, a0, hi), Equal.cong(Nat, Nat, kk => Nat.add(an, Nat.double(kk)), Word.to_nat(pp, hi),
    Nat.add(qb, rn), e1)), alg.lhs(an, qb, rn)), Equal.trans(Nat, Nat.add(Nat.double(qb), Nat.add(an, Nat.double(rn))),
    Nat.add(Nat.mul(Nat.double(qn), bn), Nat.add(an, Nat.double(rn))), Nat.add(Nat.mul(Nat.double(qn), bn),
    U32.to_nat(su)), Equal.cong(Nat, Nat, kk => Nat.add(kk, Nat.add(an, Nat.double(rn))), Nat.double(qb),
    Nat.mul(Nat.double(qn), bn), Equal.sym(Nat, Nat.mul(Nat.double(qn), bn), Nat.double(qb), R.mul_double(qn, bn))),
    Equal.cong(Nat, Nat, kk => Nat.add(Nat.mul(Nat.double(qn), bn), kk), Nat.add(an, Nat.double(rn)), U32.to_nat(su),
    Equal.sym(Nat, U32.to_nat(su), Nat.add(an, Nat.double(rn)), es)))) : {Word.to_nat(1n+pp, WCon{a0, hi}) ==
    Nat.add(Nat.mul(Nat.double(qn), bn), U32.to_nat(su)) : Nat}}
  (e_all, hlt)

# divmod.go.fin, as it picks on whether the shifted remainder reached b
def dm.fin(
  +pp: Nat,
  +a0: Bool,
  +hi: Word(pp),
  +bu: U32,
  +qw: Word(pp),
  +rn: Nat,
  +su: U32,
  zg: Bool,
  +eg: {U32.is_ge(su, bu) == zg : Bool},
  +e1: {Word.to_nat(pp, hi) == Nat.add(Nat.mul(Word.to_nat(pp, qw), U32.to_nat(bu)), rn) : Nat},
  +es: {U32.to_nat(su) == Nat.add(R.bit(a0), Nat.double(rn)) : Nat},
  +hlt: {Nat.is_lt(U32.to_nat(su), Nat.add(U32.to_nat(bu), U32.to_nat(bu))) == True{} : Bool}
) -> dm.ok(1n+pp, WCon{a0, hi}, bu, U32.divmod.go.fin(pp, qw, su, bu, zg)):
  match zg:
    case True{}:
      +hg = {Equal.trans(Bool, Cmp.is_ge(Nat.cmp(U32.to_nat(su), U32.to_nat(bu))), U32.is_ge(su, bu), True{},
        Equal.sym(Bool, U32.is_ge(su, bu), Cmp.is_ge(Nat.cmp(U32.to_nat(su), U32.to_nat(bu))), u.ge(su, bu)), eg) :
        {Cmp.is_ge(Nat.cmp(U32.to_nat(su), U32.to_nat(bu))) == True{} : Bool}}
      dm.sub(pp, a0, hi, bu, qw, rn, su, e1, es, ge.le(U32.to_nat(su), U32.to_nat(bu), hg), hlt)
    case False{}:
      +hg = {Equal.trans(Bool, Cmp.is_ge(Nat.cmp(U32.to_nat(su), U32.to_nat(bu))), U32.is_ge(su, bu), False{},
        Equal.sym(Bool, U32.is_ge(su, bu), Cmp.is_ge(Nat.cmp(U32.to_nat(su), U32.to_nat(bu))), u.ge(su, bu)), eg) :
        {Cmp.is_ge(Nat.cmp(U32.to_nat(su), U32.to_nat(bu))) == False{} : Bool}}
      dm.keep(pp, a0, hi, bu, qw, rn, su, e1, es, nge.lt(U32.to_nat(su), U32.to_nat(bu), hg))

# divmod.go.shl: the remainder shifted with the new bit, nothing falling out
def dm.shl(
  +pp: Nat,
  +a0: Bool,
  +hi: Word(pp),
  +bu: U32,
  +qw: Word(pp),
  +rw: Word(32n),
  yy: Bool & Word(32n),
  hy: sho.ok(32n, a0, rw, yy),
  +e1: {Word.to_nat(pp, hi) == Nat.add(Nat.mul(Word.to_nat(pp, qw), U32.to_nat(bu)), Word.to_nat(32n, rw)) : Nat},
  +lt1: {Nat.is_lt(Word.to_nat(32n, rw), U32.to_nat(bu)) == True{} : Bool}
) -> dm.ok(1n+pp, WCon{a0, hi}, bu, U32.divmod.go.shl(pp, qw, bu, yy)):
  match yy:
    case (tt, +ss):
      (e_t, +e_s) = hy
      +rn = Word.to_nat(32n, rw)
      +hlt = {R.lt_rw_l(Nat.add(R.bit(a0), Nat.double(rn)), U32.to_nat(U32{ss}), Nat.add(U32.to_nat(bu),
        U32.to_nat(bu)), Equal.sym(Nat, Word.to_nat(32n, ss), Nat.add(R.bit(a0), Nat.double(rn)), e_s), dbl.lt(a0, rn,
        U32.to_nat(bu), lt1)) : {Nat.is_lt(U32.to_nat(U32{ss}), Nat.add(U32.to_nat(bu), U32.to_nat(bu))) == True{} :
        Bool}}
      %Equal.sym(Bool, tt, False{}, e_t) : dm.ok(1n+pp, WCon{a0, hi}, bu, U32.divmod.go.fin(pp, qw, U32{ss}, bu,
        Bool.or(_, U32.is_ge(U32{ss}, bu))))
      dm.fin(pp, a0, hi, bu, qw, rn, U32{ss}, U32.is_ge(U32{ss}, bu), {==}, e1, e_s, hlt)

# divmod.go.rec with the remainder and the bound taken apart into words
def dm.rec2(
  +pp: Nat,
  +a0: Bool,
  +hi: Word(pp),
  +bu: U32,
  +qw: Word(pp),
  ru: U32,
  tu: U32,
  +e1: {Word.to_nat(pp, hi) == Nat.add(Nat.mul(Word.to_nat(pp, qw), U32.to_nat(bu)), U32.to_nat(ru)) : Nat},
  +lt1: {Nat.is_lt(U32.to_nat(ru), U32.to_nat(bu)) == True{} : Bool},
  +hb2: {Nat.is_le(Nat.add(U32.to_nat(bu), U32.to_nat(bu)), U32.to_nat(tu)) == True{} : Bool}
) -> dm.ok(1n+pp, WCon{a0, hi}, bu, U32.divmod.go.rec(pp, a0, bu, (qw, ru))):
  match ru tu:
    case U32{+rw} U32{+tw}:
      +rn = Word.to_nat(32n, rw)
      +bb = Nat.add(U32.to_nat(bu), U32.to_nat(bu))
      +hbd = {R.le_trans(Nat.add(R.bit(a0), Nat.double(rn)), bb, Word.to_nat(32n, tw), R.lt_le(Nat.add(R.bit(a0),
        Nat.double(rn)), bb, dbl.lt(a0, rn, U32.to_nat(bu), lt1)), hb2) : {Nat.is_le(Nat.add(R.bit(a0),
        Nat.double(rn)), Word.to_nat(32n, tw)) == True{} : Bool}}
      dm.shl(pp, a0, hi, bu, qw, rw, Word.shl.out(32n, a0, rw), sho(32n, a0, rw, tw, hbd), e1, lt1)

# divmod.go.rec: the bits above, divided, then this bit shifted in
def dm.rec(
  +pp: Nat,
  +a0: Bool,
  +hi: Word(pp),
  +bu: U32,
  +tu: U32,
  xx: Word(pp) & U32,
  ih: dm.ok(pp, hi, bu, xx),
  +hb2: {Nat.is_le(Nat.add(U32.to_nat(bu), U32.to_nat(bu)), U32.to_nat(tu)) == True{} : Bool}
) -> dm.ok(1n+pp, WCon{a0, hi}, bu, U32.divmod.go.rec(pp, a0, bu, xx)):
  match xx:
    case (+qw, +ru):
      (e1, lt1) = ih
      dm.rec2(pp, a0, hi, bu, qw, ru, tu, e1, lt1, hb2)

# U32.divmod.go by a b above 0 with 2 b some U32's value: the word is q b + r, r below b
def dm(
  mm: Nat,
  aw: Word(mm),
  +bu: U32,
  +tu: U32,
  +hb0: {Nat.is_lt(0n, U32.to_nat(bu)) == True{} : Bool},
  +hb2: {Nat.is_le(Nat.add(U32.to_nat(bu), U32.to_nat(bu)), U32.to_nat(tu)) == True{} : Bool}
) -> dm.ok(mm, aw, bu, U32.divmod.go(mm, aw, bu)):
  match mm aw:
    case 0n WNil{}:
      ({==}, hb0)
    case 1n+(+pp) WCon{+a0, +hi}:
      dm.rec(pp, a0, hi, bu, tu, U32.divmod.go(pp, hi, bu), dm(pp, hi, bu, tu, hb0, hb2), hb2)

# what U32.div and U32.mod give
def dvm.ty(+nu: U32, +bu: U32) -> Type:
  {U32.to_nat(nu) == Nat.add(Nat.mul(U32.to_nat(U32.div(nu, bu)), U32.to_nat(bu)), U32.to_nat(U32.mod(nu, bu))) : Nat}
    & {Nat.is_lt(U32.to_nat(U32.mod(nu, bu)), U32.to_nat(bu)) == True{} : Bool}

# the quotient and remainder divmod.go leaves, read by div.fin and mod.fin
def dvm.pair(
  +aw: Word(32n),
  +bu: U32,
  xx: Word(32n) & U32,
  hh: dm.ok(32n, aw, bu, xx)
) -> {Word.to_nat(32n, aw) == Nat.add(Nat.mul(U32.to_nat(U32.div.fin(xx)), U32.to_nat(bu)),
  U32.to_nat(U32.mod.fin(xx))) : Nat} & {Nat.is_lt(U32.to_nat(U32.mod.fin(xx)), U32.to_nat(bu)) == True{} : Bool}:
  match xx:
    case (+qw, +ru):
      hh

# U32.div and U32.mod by a nonzero b, once is_zero's answer is named
def dvm.at(
  zz: Bool,
  +aw: Word(32n),
  +bu: U32,
  +tu: U32,
  +ez: {U32.is_zero(bu) == zz : Bool},
  +hb0: {Nat.is_lt(0n, U32.to_nat(bu)) == True{} : Bool},
  +hb2: {Nat.is_le(Nat.add(U32.to_nat(bu), U32.to_nat(bu)), U32.to_nat(tu)) == True{} : Bool}
) -> {Word.to_nat(32n, aw) == Nat.add(Nat.mul(U32.to_nat(U32.div.if(aw, bu, zz)), U32.to_nat(bu)),
  U32.to_nat(U32.mod.if(aw, bu, zz))) : Nat} & {Nat.is_lt(U32.to_nat(U32.mod.if(aw, bu, zz)), U32.to_nat(bu)) ==
  True{} : Bool}:
  match zz:
    case False{}:
      dvm.pair(aw, bu, U32.divmod.go(32n, aw, bu), dm(32n, aw, bu, tu, hb0, hb2))
    case True{}:
      +e0 = {zero.val(bu, Equal.sym(Bool, U32.is_zero(bu), True{}, ez)) : {U32.to_nat(bu) == 0n : Nat}}
      Empty.absurd({Word.to_nat(32n, aw) == Nat.add(Nat.mul(U32.to_nat(U32.div.if(aw, bu, True{})), U32.to_nat(bu)),
        U32.to_nat(U32.mod.if(aw, bu, True{}))) : Nat} & {Nat.is_lt(U32.to_nat(U32.mod.if(aw, bu, True{})),
        U32.to_nat(bu)) == True{} : Bool}, U32L.false_true(Equal.trans(Bool, False{}, Nat.is_lt(0n, U32.to_nat(bu)),
        True{}, Equal.cong(Nat, Bool, kk => Nat.is_lt(0n, kk), 0n, U32.to_nat(bu), Equal.sym(Nat, U32.to_nat(bu), 0n,
        e0)), hb0)))

# U32.div and U32.mod: n is q b + r with r below b, for b above 0 whose double
# is some U32's value
def dvm(
  nu: U32,
  +bu: U32,
  +tu: U32,
  +hb0: {Nat.is_lt(0n, U32.to_nat(bu)) == True{} : Bool},
  +hb2: {Nat.is_le(Nat.add(U32.to_nat(bu), U32.to_nat(bu)), U32.to_nat(tu)) == True{} : Bool}
) -> dvm.ty(nu, bu):
  match nu:
    case U32{+aw}:
      dvm.at(U32.is_zero(bu), aw, bu, tu, {==}, hb0, hb2)

# ---- E. adding without a carry out, and the block count ----

# the adder's carry out of the top bit
def cy(nn: Nat, aw: Word(nn), bw: Word(nn), cc: Bool) -> Bool:
  match nn:
    case 0n:
      cc
    case 1n+pp:
      match aw bw cc:
        case WCon{False{}, at} WCon{False{}, bt} False{}:
          cy(pp, at, bt, False{})
        case WCon{False{}, at} WCon{False{}, bt} True{}:
          cy(pp, at, bt, False{})
        case WCon{False{}, at} WCon{True{}, bt} False{}:
          cy(pp, at, bt, False{})
        case WCon{False{}, at} WCon{True{}, bt} True{}:
          cy(pp, at, bt, True{})
        case WCon{True{}, at} WCon{False{}, bt} False{}:
          cy(pp, at, bt, False{})
        case WCon{True{}, at} WCon{False{}, bt} True{}:
          cy(pp, at, bt, True{})
        case WCon{True{}, at} WCon{True{}, bt} False{}:
          cy(pp, at, bt, True{})
        case WCon{True{}, at} WCon{True{}, bt} True{}:
          cy(pp, at, bt, True{})

# one bit of cfa: this bit's sum and carry, then the bits above
def cfa.arm(
  +pp: Nat,
  +at: Word(pp),
  +bt: Word(pp),
  +ab: Bool,
  +bb: Bool,
  +cc: Bool,
  +ss: Bool,
  +kk: Bool,
  +e_bits: {Nat.add(R.bit(cc), Nat.add(R.bit(ab), R.bit(bb))) == Nat.add(R.bit(ss), Nat.double(R.bit(kk))) : Nat},
  +er: {Word.to_nat(pp, Word.adc(pp, at, bt, False{}, kk)) == Nat.add(R.bit(kk), Nat.add(Word.to_nat(pp, at),
    Word.to_nat(pp, bt))) : Nat}
) -> {Word.to_nat(1n+pp, WCon{ss, Word.adc(pp, at, bt, False{}, kk)}) == Nat.add(R.bit(cc), Nat.add(Word.to_nat(1n+pp,
  WCon{ab, at}), Word.to_nat(1n+pp, WCon{bb, bt}))) : Nat}:
  +na = Word.to_nat(pp, at)
  +nb = Word.to_nat(pp, bt)
  +mm = Nat.add(R.bit(kk), Nat.add(na, nb))
  +wa = Word.to_nat(1n+pp, WCon{ab, at})
  +wb = Word.to_nat(1n+pp, WCon{bb, bt})
  +xa = Nat.add(R.bit(ab), Nat.double(na))
  +xb = Nat.add(R.bit(bb), Nat.double(nb))
  +e_in = {Equal.trans(Nat, Nat.add(R.bit(cc), Nat.add(wa, wb)), Nat.add(R.bit(cc), Nat.add(xa, wb)),
    Nat.add(R.bit(cc), Nat.add(xa, xb)),
    Equal.cong(Nat, Nat, xx => Nat.add(R.bit(cc), Nat.add(xx, wb)), wa, xa, R.to_nat_con(pp, ab, at)),
    Equal.cong(Nat, Nat, xx => Nat.add(R.bit(cc), Nat.add(xa, xx)), wb, xb, R.to_nat_con(pp, bb, bt))) :
    {Nat.add(R.bit(cc), Nat.add(wa, wb)) == Nat.add(R.bit(cc), Nat.add(xa, xb)) : Nat}}
  +e_all = {Equal.trans(Nat, Nat.add(R.bit(cc), Nat.add(wa, wb)), Nat.add(R.bit(cc), Nat.add(xa, xb)),
    Nat.add(R.bit(ss), Nat.double(mm)), e_in, R.sum_regroup(R.bit(cc), R.bit(ab), R.bit(bb), R.bit(ss), R.bit(kk), na,
    nb, e_bits)) : {Nat.add(R.bit(cc), Nat.add(wa, wb)) == Nat.add(R.bit(ss), Nat.double(mm)) : Nat}}
  Equal.trans(Nat, Word.to_nat(1n+pp, WCon{ss, Word.adc(pp, at, bt, False{}, kk)}),
    Nat.add(R.bit(ss), Nat.double(Word.to_nat(pp, Word.adc(pp, at, bt, False{}, kk)))),
    Nat.add(R.bit(cc), Nat.add(wa, wb)),
    R.to_nat_con(pp, ss, Word.adc(pp, at, bt, False{}, kk)),
    Equal.trans(Nat, Nat.add(R.bit(ss), Nat.double(Word.to_nat(pp, Word.adc(pp, at, bt, False{}, kk)))),
      Nat.add(R.bit(ss), Nat.double(mm)), Nat.add(R.bit(cc), Nat.add(wa, wb)),
      Equal.cong(Nat, Nat, xx => Nat.add(R.bit(ss), Nat.double(xx)), Word.to_nat(pp, Word.adc(pp, at, bt, False{}, kk)),
        mm, er),
      Equal.sym(Nat, Nat.add(R.bit(cc), Nat.add(wa, wb)), Nat.add(R.bit(ss), Nat.double(mm)), e_all)))

# the adder with no carry out is the sum
def cfa(
  nn: Nat,
  aw: Word(nn),
  bw: Word(nn),
  cc: Bool,
  +hh: {cy(nn, aw, bw, cc) == False{} : Bool}
) -> {Word.to_nat(nn, Word.adc(nn, aw, bw, False{}, cc)) == Nat.add(R.bit(cc), Nat.add(Word.to_nat(nn, aw),
  Word.to_nat(nn, bw))) : Nat}:
  match nn:
    case 0n:
      match aw bw cc:
        case WNil{} WNil{} False{}:
          {==}
        case WNil{} WNil{} True{}:
          Empty.absurd({0n == 1n : Nat}, U32L.false_true(Equal.sym(Bool, True{}, False{}, hh)))
    case 1n+(+pp):
      match aw bw cc:
        case WCon{False{}, +at} WCon{False{}, +bt} False{}:
          cfa.arm(pp, at, bt, False{}, False{}, False{}, False{}, False{}, {==}, cfa(pp, at, bt, False{}, hh))
        case WCon{False{}, +at} WCon{False{}, +bt} True{}:
          cfa.arm(pp, at, bt, False{}, False{}, True{}, True{}, False{}, {==}, cfa(pp, at, bt, False{}, hh))
        case WCon{False{}, +at} WCon{True{}, +bt} False{}:
          cfa.arm(pp, at, bt, False{}, True{}, False{}, True{}, False{}, {==}, cfa(pp, at, bt, False{}, hh))
        case WCon{False{}, +at} WCon{True{}, +bt} True{}:
          cfa.arm(pp, at, bt, False{}, True{}, True{}, False{}, True{}, {==}, cfa(pp, at, bt, True{}, hh))
        case WCon{True{}, +at} WCon{False{}, +bt} False{}:
          cfa.arm(pp, at, bt, True{}, False{}, False{}, True{}, False{}, {==}, cfa(pp, at, bt, False{}, hh))
        case WCon{True{}, +at} WCon{False{}, +bt} True{}:
          cfa.arm(pp, at, bt, True{}, False{}, True{}, False{}, True{}, {==}, cfa(pp, at, bt, True{}, hh))
        case WCon{True{}, +at} WCon{True{}, +bt} False{}:
          cfa.arm(pp, at, bt, True{}, True{}, False{}, False{}, True{}, {==}, cfa(pp, at, bt, True{}, hh))
        case WCon{True{}, +at} WCon{True{}, +bt} True{}:
          cfa.arm(pp, at, bt, True{}, True{}, True{}, True{}, True{}, {==}, cfa(pp, at, bt, True{}, hh))

# the carry out of a U32 add
def cy32(uu: U32, vv: U32) -> Bool:
  match uu vv:
    case U32{xw} U32{yw}:
      cy(32n, xw, yw, False{})

# a U32 add with no carry out is the sum
def add.cf(uu: U32, vv: U32, +hh: {cy32(uu, vv) == False{} : Bool}) -> {U32.to_nat(U32.add(uu, vv)) ==
  Nat.add(U32.to_nat(uu), U32.to_nat(vv)) : Nat}:
  match uu vv:
    case U32{+xw} U32{+yw}:
      cfa(32n, xw, yw, False{}, hh)

# the block size doubled is a U32's value
def mx.dbl(+mx: U32, +emx: {mx == 65535 : U32}) -> {U32.to_nat(U32.add(mx, mx)) == Nat.add(U32.to_nat(mx),
  U32.to_nat(mx)) : Nat}:
  add.cf(mx, mx, Equal.cong(U32, Bool, uu => cy32(uu, uu), mx, 65535, emx))

# the block size is at least 2
def mx.two(+mx: U32, +emx: {mx == 65535 : U32}) -> {U32.to_nat(mx) == 2n+U32.to_nat(((mx - 1 : U32) - 1 : U32)) :
  Nat}:
  +m1 = (mx - 1 : U32)
  +nz1 = {Equal.cong(U32, Bool, uu => U32.is_zero((uu - 1 : U32)), mx, 65535, emx) : {U32.is_zero(m1) == False{} :
    Bool}}
  Equal.trans(Nat, U32.to_nat(mx), 1n+U32.to_nat(m1), 2n+U32.to_nat((m1 - 1 : U32)), Wp1.u32_dec(mx, mx.nz(mx, emx)),
    Equal.cong(Nat, Nat, kk => 1n+kk, U32.to_nat(m1), 1n+U32.to_nat((m1 - 1 : U32)), Wp1.u32_dec(m1, nz1)))

# k blocks of m bytes hold x bytes with the last block not empty: k is ceil(x / m)
def kok(+xn: Nat, kk: Nat, +mn: Nat) -> Type:
  match kk:
    case 0n:
      {xn == 0n : Nat}
    case 1n+(+kp):
      {Nat.is_lt(Nat.mul(kp, mn), xn) == True{} : Bool} & {Nat.is_le(xn, Nat.mul(1n+kp, mn)) == True{} : Bool}

# x below x + y when y is above 0
def lt.more(+xx: Nat, +yy: Nat, +hh: {Nat.is_lt(0n, yy) == True{} : Bool}) -> {Nat.is_lt(xx, Nat.add(xx, yy)) == True{} :
  Bool}:
  R.lt_rw_l(Nat.add(xx, 0n), xx, Nat.add(xx, yy), R.add_zero(xx), R.lt_add_mono(xx, 0n, yy, hh))

# q blocks exactly: ceil(q m / m) is q
def nb.exact(
  qn: Nat,
  +mn: Nat,
  +xn: Nat,
  +ee: {xn == Nat.mul(qn, mn) : Nat},
  +hm: {Nat.is_lt(0n, mn) == True{} : Bool}
) -> kok(xn, qn, mn):
  match qn:
    case 0n:
      ee
    case 1n+(+kp):
      +km = Nat.mul(kp, mn)
      +e2 = {Equal.trans(Nat, xn, Nat.add(mn, km), Nat.add(km, mn), ee, R.add_comm(mn, km)) : {xn == Nat.add(km, mn) :
        Nat}}
      (R.lt_rw_r(km, Nat.add(km, mn), xn, Equal.sym(Nat, xn, Nat.add(km, mn), e2), lt.more(km, mn, hm)),
        R.le_rw_l(Nat.mul(1n+kp, mn), xn, Nat.mul(1n+kp, mn), Equal.sym(Nat, xn, Nat.mul(1n+kp, mn), ee),
        R.le_refl(Nat.mul(1n+kp, mn))))

# q blocks and a remainder r from 1 to m - 1: ceil is q + 1
def nb.rem(
  +qn: Nat,
  +mn: Nat,
  +xn: Nat,
  +rn: Nat,
  +ee: {xn == Nat.add(Nat.mul(qn, mn), rn) : Nat},
  +h1: {Nat.is_lt(0n, rn) == True{} : Bool},
  +hr: {Nat.is_lt(rn, mn) == True{} : Bool}
) -> kok(xn, 1n+qn, mn):
  +qm = Nat.mul(qn, mn)
  (R.lt_rw_r(qm, Nat.add(qm, rn), xn, Equal.sym(Nat, xn, Nat.add(qm, rn), ee), lt.more(qm, rn, h1)),
    R.le_rw_l(Nat.add(qm, rn), xn, Nat.mul(1n+qn, mn), Equal.sym(Nat, xn, Nat.add(qm, rn), ee), R.le_rw_r(Nat.add(qm,
    rn), Nat.add(qm, mn), Nat.mul(1n+qn, mn), R.add_comm(qm, mn), R.le_add_mono(qm, rn, mn, R.lt_le(rn, mn, hr)))))

# x at most x times m for m above 0
def le.mul(+xx: Nat, +mn: Nat, +hm: {Nat.is_lt(0n, mn) == True{} : Bool}) -> {Nat.is_le(xx, Nat.mul(xx, mn)) == True{} :
  Bool}:
  +h1 = {Equal.trans(Bool, Nat.is_le(1n, mn), Nat.is_lt(0n, mn), True{}, Equal.sym(Bool, Nat.is_lt(0n, mn),
    Nat.is_le(1n, mn), R.lt_le_succ(0n, mn)), hm) : {Nat.is_le(1n, mn) == True{} : Bool}}
  R.le_rw_l(Nat.mul(1n, xx), xx, Nat.mul(xx, mn), R.add_zero(xx), R.le_rw_r(Nat.mul(1n, xx), Nat.mul(mn, xx),
    Nat.mul(xx, mn), R.mul_comm(mn, xx), R.le_mul_mono(1n, mn, xx, h1)))

# enc.nblk with the block size named
def nblk.m(+nn: U32, +mx: U32) -> U32:
  Png.enc.nblk.at(U32.is_zero(U32.mod(nn, mx)), U32.div(nn, mx))

# enc.nblk is nblk.m at 65535
def nblk.eq(+nn: U32, +mx: U32, +emx: {mx == 65535 : U32}) -> {Png.enc.nblk(nn) == nblk.m(nn, mx) : U32}:
  Equal.cong(U32, U32, uu => Png.enc.nblk.at(U32.is_zero(U32.mod(nn, uu)), U32.div(nn, uu)), 65535, mx, Equal.sym(U32,
    mx, 65535, emx))

# nblk.m, once whether the remainder is zero is named
def nb.at(
  zz: Bool,
  +nn: U32,
  +mx: U32,
  +ez: {U32.is_zero(U32.mod(nn, mx)) == zz : Bool},
  +e_n: {U32.to_nat(nn) == Nat.add(Nat.mul(U32.to_nat(U32.div(nn, mx)), U32.to_nat(mx)), U32.to_nat(U32.mod(nn,
    mx))) : Nat},
  +l_r: {Nat.is_lt(U32.to_nat(U32.mod(nn, mx)), U32.to_nat(mx)) == True{} : Bool},
  +hm: {Nat.is_lt(0n, U32.to_nat(mx)) == True{} : Bool}
) -> kok(U32.to_nat(nn), U32.to_nat(Png.enc.nblk.at(zz, U32.div(nn, mx))), U32.to_nat(mx)):
  match zz:
    case True{}:
      +qu = U32.div(nn, mx)
      +ru = U32.mod(nn, mx)
      +qn = U32.to_nat(qu)
      +mn = U32.to_nat(mx)
      +xn = U32.to_nat(nn)
      +e0 = {zero.val(ru, Equal.sym(Bool, U32.is_zero(ru), True{}, ez)) : {U32.to_nat(ru) == 0n : Nat}}
      nb.exact(qn, mn, xn, Equal.trans(Nat, xn, Nat.add(Nat.mul(qn, mn), 0n), Nat.mul(qn, mn), Equal.trans(Nat, xn,
        Nat.add(Nat.mul(qn, mn), U32.to_nat(ru)), Nat.add(Nat.mul(qn, mn), 0n), e_n, Equal.cong(Nat, Nat, kk =>
        Nat.add(Nat.mul(qn, mn), kk), U32.to_nat(ru), 0n, e0)), R.add_zero(Nat.mul(qn, mn))), hm)
    case False{}:
      +qu = U32.div(nn, mx)
      +ru = U32.mod(nn, mx)
      +qn = U32.to_nat(qu)
      +mn = U32.to_nat(mx)
      +xn = U32.to_nat(nn)
      +h1 = {Equal.trans(Bool, Nat.is_lt(0n, U32.to_nat(ru)), Bool.not(Nat.is_eq(U32.to_nat(ru), 0n)), True{},
        R.pos_eq(U32.to_nat(ru)), Equal.cong(Bool, Bool, bb => Bool.not(bb), Nat.is_eq(U32.to_nat(ru), 0n), False{},
        Equal.trans(Bool, Nat.is_eq(U32.to_nat(ru), 0n), U32.is_zero(ru), False{}, Equal.sym(Bool, U32.is_zero(ru),
        Nat.is_eq(U32.to_nat(ru), U32.to_nat(0)), R.u32_eq(ru, 0)), ez))) : {Nat.is_lt(0n, U32.to_nat(ru)) == True{} :
        Bool}}
      +h_q1 = {R.le_rw_r(Nat.add(qn, 1n), Nat.add(Nat.mul(qn, mn), U32.to_nat(ru)), xn, Equal.sym(Nat, xn,
        Nat.add(Nat.mul(qn, mn), U32.to_nat(ru)), e_n), R.le_add_both(qn, Nat.mul(qn, mn), 1n, U32.to_nat(ru),
        le.mul(qn, mn, hm), Equal.trans(Bool, Nat.is_le(1n, U32.to_nat(ru)), Nat.is_lt(0n, U32.to_nat(ru)), True{},
        Equal.sym(Bool, Nat.is_lt(0n, U32.to_nat(ru)), Nat.is_le(1n, U32.to_nat(ru)), R.lt_le_succ(0n,
        U32.to_nat(ru))), h1))) : {Nat.is_le(Nat.add(qn, 1n), xn) == True{} : Bool}}
      +e_q1 = {Equal.trans(Nat, U32.to_nat((qu + 1 : U32)), Nat.add(qn, 1n), 1n+qn, R.u32_add_below(qu, 1, nn, h_q1),
        W9.add.one.nat(qn)) : {U32.to_nat((qu + 1 : U32)) == 1n+qn : Nat}}
      %Equal.sym(Nat, U32.to_nat((qu + 1 : U32)), 1n+qn, e_q1) : kok(xn, _, mn)
      nb.rem(qn, mn, xn, U32.to_nat(ru), e_n, h1, l_r)

# the pair U32.div and U32.mod give, taken apart
def nb.go(
  +nn: U32,
  +mx: U32,
  pr: dvm.ty(nn, mx),
  +hm: {Nat.is_lt(0n, U32.to_nat(mx)) == True{} : Bool}
) -> kok(U32.to_nat(nn), U32.to_nat(nblk.m(nn, mx)), U32.to_nat(mx)):
  (+e_n, +l_r) = pr
  nb.at(U32.is_zero(U32.mod(nn, mx)), nn, mx, {==}, e_n, l_r, hm)

# enc.nblk(n) blocks of 65535 bytes hold n bytes, the last one not empty
def nb.k(+nn: U32, +mx: U32, +emx: {mx == 65535 : U32}) -> kok(U32.to_nat(nn), U32.to_nat(Png.enc.nblk(nn)),
  U32.to_nat(mx)):
  +mn = U32.to_nat(mx)
  +hm = {Equal.trans(Bool, Nat.is_lt(0n, mn), Nat.is_lt(0n, 2n+U32.to_nat(((mx - 1 : U32) - 1 : U32))), True{},
    Equal.cong(Nat, Bool, kk => Nat.is_lt(0n, kk), mn, 2n+U32.to_nat(((mx - 1 : U32) - 1 : U32)), mx.two(mx, emx)),
    {==}) : {Nat.is_lt(0n, mn) == True{} : Bool}}
  +h2 = {R.le_rw_r(Nat.add(mn, mn), Nat.add(mn, mn), U32.to_nat(U32.add(mx, mx)), Equal.sym(Nat,
    U32.to_nat(U32.add(mx, mx)), Nat.add(mn, mn), mx.dbl(mx, emx)), R.le_refl(Nat.add(mn, mn))) :
    {Nat.is_le(Nat.add(mn, mn), U32.to_nat(U32.add(mx, mx))) == True{} : Bool}}
  %Equal.sym(U32, Png.enc.nblk(nn), nblk.m(nn, mx), nblk.eq(nn, mx, emx)) : kok(U32.to_nat(nn), U32.to_nat(_), mn)
  nb.go(nn, mx, dvm(nn, mx, U32.add(mx, mx), hm, h2), hm)

# ---- F. how many bytes bs writes ----

# at most 0 is 0
def le.zero(xx: Nat, +hh: {Nat.is_le(xx, 0n) == True{} : Bool}) -> {xx == 0n : Nat}:
  match xx:
    case 0n:
      {==}
    case 1n+pp:
      Empty.absurd({1n+pp == 0n : Nat}, U32L.false_true(hh))

# nothing is below itself
def lt.irr(mm: Nat, +hh: {Nat.is_lt(mm, mm) == True{} : Bool}) -> Empty:
  match mm:
    case 0n:
      U32L.false_true(hh)
    case 1n+pp:
      lt.irr(pp, hh)

# m + x is not below m
def lt.self(+mm: Nat, +xx: Nat, +hh: {Nat.is_lt(Nat.add(mm, xx), mm) == True{} : Bool}) -> Empty:
  lt.irr(mm, R.le_lt_trans(mm, Nat.add(mm, xx), mm, Wp2.nle_add(mm, xx), hh))

# a sum that is 0 has a right part 0
def add.zero.r(aa: Nat, +bb: Nat, +hh: {Nat.add(aa, bb) == 0n : Nat}) -> {bb == 0n : Nat}:
  match aa:
    case 0n:
      hh
    case 1n+pp:
      Empty.absurd({bb == 0n : Nat}, Wp1.zero_succ(Nat.add(pp, bb), Equal.sym(Nat, 1n+Nat.add(pp, bb), 0n, hh)))

# no bytes left, no blocks left
def kok.nil(kk: Nat, +mn: Nat, hk: kok(0n, kk, mn)) -> {Nat.mul(kk, 5n) == 0n : Nat}:
  match kk:
    case 0n:
      {==}
    case 1n+(+kp):
      (h_lt, _h_le) = hk
      Empty.absurd({Nat.mul(1n+kp, 5n) == 0n : Nat}, U32L.false_true(Equal.trans(Bool, False{}, Nat.is_lt(Nat.mul(kp,
        mn), 0n), True{}, R.lt_zero_false(Nat.mul(kp, mn)), h_lt)))

# a new block's room after its first byte is at most the bytes after it
def ks.le(
  zz: Bool,
  +left: U32,
  +mx: U32,
  +nt: Nat,
  +nzm: {U32.is_zero(mx) == False{} : Bool},
  +ez: {U32.is_le(left, mx) == zz : Bool},
  +hn: {U32.to_nat(left) == 1n+nt : Nat}
) -> {Nat.is_le(U32.to_nat((capm(zz, left, mx) - 1 : U32)), nt) == True{} : Bool}:
  match zz:
    case True{}:
      R.le_rw_l(nt, U32.to_nat((left - 1 : U32)), nt, Equal.sym(Nat, U32.to_nat((left - 1 : U32)), nt,
        Wp1.u32_pred(left, nt, hn)), R.le_refl(nt))
    case False{}:
      +m1 = (mx - 1 : U32)
      +e_m = {Wp1.u32_dec(mx, nzm) : {U32.to_nat(mx) == 1n+U32.to_nat(m1) : Nat}}
      +h0 = {Equal.trans(Bool, Nat.is_le(1n+nt, 1n+U32.to_nat(m1)), U32.is_le(left, mx), False{},
        Equal.sym(Bool, U32.is_le(left, mx), Nat.is_le(1n+nt, 1n+U32.to_nat(m1)), Equal.trans(Bool,
          U32.is_le(left, mx), Nat.is_le(U32.to_nat(left), U32.to_nat(mx)), Nat.is_le(1n+nt, 1n+U32.to_nat(m1)),
          R.u32_le(left, mx), Equal.trans(Bool, Nat.is_le(U32.to_nat(left), U32.to_nat(mx)), Nat.is_le(1n+nt,
          U32.to_nat(mx)), Nat.is_le(1n+nt, 1n+U32.to_nat(m1)), Equal.cong(Nat, Bool, xx => Nat.is_le(xx,
          U32.to_nat(mx)), U32.to_nat(left), 1n+nt, hn), Equal.cong(Nat, Bool, xx => Nat.is_le(1n+nt, xx),
          U32.to_nat(mx), 1n+U32.to_nat(m1), e_m)))), ez) : {Nat.is_le(nt, U32.to_nat(m1)) == False{} : Bool}}
      R.lt_le(U32.to_nat(m1), nt, nle.lt(nt, U32.to_nat(m1), h0))

# the blocks after a new block: one fewer than before it
def ks.k(
  zz: Bool,
  kp: Nat,
  +left: U32,
  +mx: U32,
  +nt: Nat,
  +nzm: {U32.is_zero(mx) == False{} : Bool},
  +ez: {U32.is_le(left, mx) == zz : Bool},
  +hn: {U32.to_nat(left) == 1n+nt : Nat},
  +h_lt: {Nat.is_lt(Nat.mul(kp, U32.to_nat(mx)), 1n+nt) == True{} : Bool},
  +h_le: {Nat.is_le(1n+nt, Nat.add(U32.to_nat(mx), Nat.mul(kp, U32.to_nat(mx)))) == True{} : Bool}
) -> kok(Nat.sub(nt, U32.to_nat((capm(zz, left, mx) - 1 : U32))), kp, U32.to_nat(mx)):
  match zz kp:
    case True{} 0n:
      +e_l = {Wp1.u32_pred(left, nt, hn) : {U32.to_nat((left - 1 : U32)) == nt : Nat}}
      Equal.trans(Nat, Nat.sub(nt, U32.to_nat((left - 1 : U32))), Nat.sub(nt, nt), 0n, Equal.cong(Nat, Nat, xx =>
        Nat.sub(nt, xx), U32.to_nat((left - 1 : U32)), nt, e_l), R.sub_zero_le(nt, nt, R.le_refl(nt)))
    case True{} 1n+(+k2):
      +mn = U32.to_nat(mx)
      +h0 = {Equal.trans(Bool, Nat.is_le(U32.to_nat(left), mn), U32.is_le(left, mx), True{}, Equal.sym(Bool,
        U32.is_le(left, mx), Nat.is_le(U32.to_nat(left), mn), R.u32_le(left, mx)), ez) : {Nat.is_le(U32.to_nat(left),
        mn) == True{} : Bool}}
      +h1 = {R.le_rw_l(U32.to_nat(left), 1n+nt, mn, hn, h0) : {Nat.is_le(1n+nt, mn) == True{} : Bool}}
      Empty.absurd(kok(Nat.sub(nt, U32.to_nat((left - 1 : U32))), 1n+k2, mn), lt.self(mn, Nat.mul(k2, mn),
        R.lt_le_trans(Nat.add(mn, Nat.mul(k2, mn)), 1n+nt, mn, h_lt, h1)))
    case False{} 0n:
      +mn = U32.to_nat(mx)
      +m1 = U32.to_nat((mx - 1 : U32))
      +xn = Nat.sub(nt, m1)
      +e_m = {Wp1.u32_dec(mx, nzm) : {mn == 1n+m1 : Nat}}
      +h_m = {ks.le(False{}, left, mx, nt, nzm, ez, hn) : {Nat.is_le(m1, nt) == True{} : Bool}}
      +e_x = {Equal.trans(Nat, 1n+nt, 1n+Nat.add(m1, xn), Nat.add(mn, xn), Equal.cong(Nat, Nat, kk => 1n+kk, nt,
        Nat.add(m1, xn), Equal.sym(Nat, Nat.add(m1, xn), nt, R.add_sub(m1, nt, h_m))), Equal.cong(Nat, Nat, kk =>
        Nat.add(kk, xn), 1n+m1, mn, Equal.sym(Nat, mn, 1n+m1, e_m))) : {1n+nt == Nat.add(mn, xn) : Nat}}
      +h2 = {R.le_rw_l(1n+nt, Nat.add(mn, xn), Nat.add(mn, 0n), e_x, h_le) : {Nat.is_le(Nat.add(mn, xn), Nat.add(mn,
        0n)) == True{} : Bool}}
      le.zero(xn, R.le_cancel(mn, xn, 0n, h2))
    case False{} 1n+(+k2):
      +mn = U32.to_nat(mx)
      +m1 = U32.to_nat((mx - 1 : U32))
      +xn = Nat.sub(nt, m1)
      +km = Nat.mul(k2, mn)
      +e_m = {Wp1.u32_dec(mx, nzm) : {mn == 1n+m1 : Nat}}
      +h_m = {ks.le(False{}, left, mx, nt, nzm, ez, hn) : {Nat.is_le(m1, nt) == True{} : Bool}}
      +e_x = {Equal.trans(Nat, 1n+nt, 1n+Nat.add(m1, xn), Nat.add(mn, xn), Equal.cong(Nat, Nat, kk => 1n+kk, nt,
        Nat.add(m1, xn), Equal.sym(Nat, Nat.add(m1, xn), nt, R.add_sub(m1, nt, h_m))), Equal.cong(Nat, Nat, kk =>
        Nat.add(kk, xn), 1n+m1, mn, Equal.sym(Nat, mn, 1n+m1, e_m))) : {1n+nt == Nat.add(mn, xn) : Nat}}
      (R.lt_cancel(mn, km, xn, R.lt_rw_r(Nat.add(mn, km), 1n+nt, Nat.add(mn, xn), e_x, h_lt)), R.le_cancel(mn, xn,
        Nat.mul(1n+k2, mn), R.le_rw_l(1n+nt, Nat.add(mn, xn), Nat.add(mn, Nat.mul(1n+k2, mn)), e_x, h_le)))

# what cnt proves: bs writes its bytes and 5 more for each block header
def cnt.ty(
  +xs: List<&2, U32>,
  +znew: Bool,
  +zlast: Bool,
  +rp: U32,
  +left: U32,
  +plen: U32,
  +pbf: U32,
  +kk: Nat
) -> Type:
  {List.length(&2, U32, bs(xs, znew, zlast, rp, left, plen, pbf)) == Nat.add(List.length(&2, U32, xs), Nat.mul(kk,
    5n)) : Nat}

# the header, the first byte and the rest of a new block: six more bytes
def cnt.open(
  +h: U32,
  +t: List<&2, U32>,
  +l2: U32,
  +plen: U32,
  +pbf: U32,
  +kp: Nat,
  +ih: {List.length(&2, U32, bs(t, U32.is_zero((plen - 1 : U32)), U32.is_eq((plen - 1 : U32), 1), (plen - 1 : U32),
    l2, Png.enc.cap(l2), Png.enc.bf(l2))) == Nat.add(List.length(&2, U32, t), Nat.mul(kp, 5n)) : Nat}
) -> {List.length(&2, U32, open.bs(h, t, l2, plen, pbf)) == Nat.add(1n+List.length(&2, U32, t), Nat.mul(1n+kp, 5n)) :
  Nat}:
  +nt = List.length(&2, U32, t)
  +k5 = Nat.mul(kp, 5n)
  Equal.trans(Nat, 6n+List.length(&2, U32, bs(t, U32.is_zero((plen - 1 : U32)), U32.is_eq((plen - 1 : U32), 1),
    (plen - 1 : U32), l2, Png.enc.cap(l2), Png.enc.bf(l2))), 6n+Nat.add(nt, k5), 1n+Nat.add(nt, 5n+k5),
    Equal.cong(Nat, Nat, xx => 6n+xx, List.length(&2, U32, bs(t, U32.is_zero((plen - 1 : U32)), U32.is_eq((plen - 1 :
    U32), 1), (plen - 1 : U32), l2, Png.enc.cap(l2), Png.enc.bf(l2))), Nat.add(nt, k5), ih),
    Equal.cong(Nat, Nat, xx => 1n+xx, 5n+Nat.add(nt, k5), Nat.add(nt, 5n+k5), Equal.sym(Nat, Nat.add(nt, 5n+k5),
    5n+Nat.add(nt, k5), R.add_swap(nt, 5n, k5))))

# kok along an equation of the byte count
def kok.rw(+xa: Nat, +xb: Nat, +kk: Nat, +mn: Nat, +ee: {xa == xb : Nat}, hk: kok(xa, kk, mn)) -> kok(xb, kk, mn):
  %ee : kok(_, kk, mn)
  hk

# a new block with kp + 1 blocks to go: the header and the first byte, then
# the rest of the walk, with kp blocks after this one
def cnt.edge(
  +h: U32,
  +t: List<&2, U32>,
  +left: U32,
  +plen: U32,
  +pbf: U32,
  +mx: U32,
  +emx: {mx == 65535 : U32},
  +kp: Nat,
  +hn: {U32.to_nat(left) == 1n+List.length(&2, U32, t) : Nat},
  +h_lt: {Nat.is_lt(Nat.mul(kp, U32.to_nat(mx)), 1n+List.length(&2, U32, t)) == True{} : Bool},
  +h_le: {Nat.is_le(1n+List.length(&2, U32, t), Nat.add(U32.to_nat(mx), Nat.mul(kp, U32.to_nat(mx)))) == True{} :
    Bool},
  pe: {plen == Png.enc.cap(left) : U32} & {pbf == Png.enc.bf(left) : U32},
  cnt_t: @xn: Nat -> {Nat.add(U32.to_nat((plen - 1 : U32)), xn) == List.length(&2, U32, t) : Nat} -> kok(xn, kp,
    U32.to_nat(mx)) -> cnt.ty(t, U32.is_zero((plen - 1 : U32)), U32.is_eq((plen - 1 : U32), 1), (plen - 1 : U32),
    (left - 1 : U32), Png.enc.cap((left - 1 : U32)), Png.enc.bf((left - 1 : U32)), kp)
) -> {List.length(&2, U32, open.bs(h, t, (left - 1 : U32), plen, pbf)) == Nat.add(1n+List.length(&2, U32, t),
  Nat.mul(1n+kp, 5n)) : Nat}:
  (+e_plen, _e_pbf) = pe
  +nt = List.length(&2, U32, t)
  +zz = U32.is_le(left, 65535)
  +cm = capm(zz, left, mx)
  +mn = U32.to_nat(mx)
  +c2 = U32.to_nat((plen - 1 : U32))
  +nzm = {mx.nz(mx, emx) : {U32.is_zero(mx) == False{} : Bool}}
  +ezm = {le.mx(left, mx, emx) : {U32.is_le(left, mx) == zz : Bool}}
  +e_c = {Equal.cong(U32, Nat, uu => U32.to_nat((uu - 1 : U32)), plen, cm, Equal.trans(U32, plen, Png.enc.cap(left), cm,
    e_plen, cap.m(zz, left, mx, emx))) : {c2 == U32.to_nat((cm - 1 : U32)) : Nat}}
  +h_c = {R.le_rw_l(U32.to_nat((cm - 1 : U32)), c2, nt, Equal.sym(Nat, c2, U32.to_nat((cm - 1 : U32)), e_c), ks.le(zz,
    left, mx, nt, nzm, ezm, hn)) : {Nat.is_le(c2, nt) == True{} : Bool}}
  +x2 = Nat.sub(nt, c2)
  +hx2 = {R.add_sub(c2, nt, h_c) : {Nat.add(c2, x2) == nt : Nat}}
  hk2 = kok.rw(Nat.sub(nt, U32.to_nat((cm - 1 : U32))), x2, kp, mn, Equal.cong(Nat, Nat, kk => Nat.sub(nt, kk),
    U32.to_nat((cm - 1 : U32)), c2, Equal.sym(Nat, c2, U32.to_nat((cm - 1 : U32)), e_c)), ks.k(zz, kp, left, mx, nt,
    nzm, ezm, hn, h_lt, h_le))
  cnt.open(h, t, (left - 1 : U32), plen, pbf, kp, cnt_t(x2, hx2, hk2))

# bs from a state: its bytes, and a header for each of the kk blocks it opens,
# xn the bytes after the open block (rp of them still in it)
def cnt(
  xs: List<&2, U32>,
  znew: Bool,
  zlast: Bool,
  +kk: Nat,
  +rp: U32,
  +left: U32,
  +plen: U32,
  +pbf: U32,
  +mx: U32,
  +xn: Nat,
  +emx: {mx == 65535 : U32},
  +hzn: {znew == U32.is_zero(rp) : Bool},
  +hzl: {zlast == U32.is_eq(rp, 1) : Bool},
  +hn: {U32.to_nat(left) == List.length(&2, U32, xs) : Nat},
  +hx: {Nat.add(U32.to_nat(rp), xn) == List.length(&2, U32, xs) : Nat},
  hk: kok(xn, kk, U32.to_nat(mx)),
  hb: at.edge(rp, left, plen, pbf)
) -> cnt.ty(xs, znew, zlast, rp, left, plen, pbf, kk):
  match xs znew zlast:
    case Nil{} _zn _zl:
      +e_x = {add.zero.r(U32.to_nat(rp), xn, hx) : {xn == 0n : Nat}}
      Equal.sym(Nat, Nat.mul(kk, 5n), 0n, kok.nil(kk, U32.to_nat(mx), kok.rw(xn, 0n, kk, U32.to_nat(mx), e_x, hk)))
    case +h <> +t False{} False{}:
      +rp2 = (rp - 1 : U32)
      +l2 = (left - 1 : U32)
      +nt = List.length(&2, U32, t)
      +nz_rp = {Equal.sym(Bool, False{}, U32.is_zero(rp), hzn) : {U32.is_zero(rp) == False{} : Bool}}
      +e_rp = {Wp1.u32_dec(rp, nz_rp) : {U32.to_nat(rp) == 1n+U32.to_nat(rp2) : Nat}}
      +nz_rp2 = {two(rp, hzn, hzl) : {U32.is_zero(rp2) == False{} : Bool}}
      +hx2 = {Wp1.succ_inj(Nat.add(U32.to_nat(rp2), xn), nt, Equal.trans(Nat, 1n+Nat.add(U32.to_nat(rp2), xn),
        Nat.add(U32.to_nat(rp), xn), 1n+nt, Equal.cong(Nat, Nat, kk2 => Nat.add(kk2, xn), 1n+U32.to_nat(rp2),
        U32.to_nat(rp), Equal.sym(Nat, U32.to_nat(rp), 1n+U32.to_nat(rp2), e_rp)), hx)) : {Nat.add(U32.to_nat(rp2),
        xn) == nt : Nat}}
      +hn2 = {Wp1.u32_pred(left, nt, hn) : {U32.to_nat(l2) == nt : Nat}}
      Equal.cong(Nat, Nat, x2 => 1n+x2, List.length(&2, U32, bs(t, False{}, U32.is_eq(rp2, 1), rp2, l2, plen, pbf)),
        Nat.add(nt, Nat.mul(kk, 5n)), cnt(t, False{}, U32.is_eq(rp2, 1), kk, rp2, l2, plen, pbf, mx, xn, emx,
        Equal.sym(Bool, U32.is_zero(rp2), False{}, nz_rp2), {==}, hn2, hx2, hk, edge.no(rp2, l2, plen, pbf, nz_rp2)))
    case +h <> +t False{} True{}:
      +l2 = (left - 1 : U32)
      +nt = List.length(&2, U32, t)
      +e_rp = {one.val(rp, hzl) : {U32.to_nat(rp) == 1n : Nat}}
      +hx2 = {Wp1.succ_inj(xn, nt, Equal.trans(Nat, 1n+xn, Nat.add(U32.to_nat(rp), xn), 1n+nt, Equal.cong(Nat, Nat,
        kk2 => Nat.add(kk2, xn), 1n, U32.to_nat(rp), Equal.sym(Nat, U32.to_nat(rp), 1n, e_rp)), hx)) :
        {Nat.add(U32.to_nat(0), xn) == nt : Nat}}
      +hn2 = {Wp1.u32_pred(left, nt, hn) : {U32.to_nat(l2) == nt : Nat}}
      Equal.cong(Nat, Nat, x2 => 1n+x2, List.length(&2, U32, bs(t, True{}, False{}, 0, l2, Png.enc.cap(l2),
        Png.enc.bf(l2))), Nat.add(nt, Nat.mul(kk, 5n)), cnt(t, True{}, False{}, kk, 0, l2, Png.enc.cap(l2),
        Png.enc.bf(l2), mx, xn, emx, {==}, {==}, hn2, hx2, hk, _ez => ({==}, {==})))
    case +h <> +t True{} _zl:
      match kk:
        case 0n:
          +nt = List.length(&2, U32, t)
          +e0 = {zero.val(rp, hzn) : {U32.to_nat(rp) == 0n : Nat}}
          +e_xn = {Equal.trans(Nat, xn, Nat.add(U32.to_nat(rp), xn), 1n+nt, Equal.cong(Nat, Nat, kk2 => Nat.add(kk2, xn),
            0n, U32.to_nat(rp), Equal.sym(Nat, U32.to_nat(rp), 0n, e0)), hx) : {xn == 1n+nt : Nat}}
          Empty.absurd(cnt.ty(h <> t, True{}, _zl, rp, left, plen, pbf, 0n), Wp1.zero_succ(nt, Equal.trans(Nat, 0n, xn,
            1n+nt, Equal.sym(Nat, xn, 0n, hk), e_xn)))
        case 1n+(+kp):
          (+h_lt, +h_le) = hk
          +nt = List.length(&2, U32, t)
          +l2 = (left - 1 : U32)
          +mn = U32.to_nat(mx)
          +e0 = {zero.val(rp, hzn) : {U32.to_nat(rp) == 0n : Nat}}
          +e_xn = {Equal.trans(Nat, xn, Nat.add(U32.to_nat(rp), xn), 1n+nt, Equal.cong(Nat, Nat, kk2 => Nat.add(kk2, xn),
            0n, U32.to_nat(rp), Equal.sym(Nat, U32.to_nat(rp), 0n, e0)), hx) : {xn == 1n+nt : Nat}}
          +ez = {Equal.sym(Bool, True{}, U32.is_zero(rp), hzn) : {U32.is_zero(rp) == True{} : Bool}}
          +hn2 = {Wp1.u32_pred(left, nt, hn) : {U32.to_nat(l2) == nt : Nat}}
          cnt.edge(h, t, left, plen, pbf, mx, emx, kp, hn, R.lt_rw_r(Nat.mul(kp, mn), xn, 1n+nt, e_xn, h_lt),
            R.le_rw_l(xn, 1n+nt, Nat.mul(1n+kp, mn), e_xn, h_le), hb(ez), x2 => a1 => a2 => cnt(t, U32.is_zero((plen - 1
            : U32)), U32.is_eq((plen - 1 : U32), 1), kp, (plen - 1 : U32), l2, Png.enc.cap(l2), Png.enc.bf(l2), mx, x2,
            emx, {==}, {==}, hn2, a1, a2, _ez => ({==}, {==})))

# the blocks enc.blocks writes for more than one block: the bytes, and 5 for
# each of the enc.nblk block headers
def cnt.blocks(
  +xs: List<&2, U32>,
  +mx: U32,
  +emx: {mx == 65535 : U32},
  +hn: {U32.to_nat(Png.enc.len(xs, 0)) == List.length(&2, U32, xs) : Nat},
  +hbig: {U32.is_le(Png.enc.len(xs, 0), 65535) == False{} : Bool}
) -> {List.length(&2, U32, Png.enc.blocks(65535, xs)) == Nat.add(List.length(&2, U32, xs),
  Nat.mul(U32.to_nat(Png.enc.nblk(Png.enc.len(xs, 0))), 5n)) : Nat}:
  +nn = Png.enc.len(xs, 0)
  +kk = U32.to_nat(Png.enc.nblk(nn))
  +bb = bs(xs, True{}, False{}, 0, nn, Png.enc.cap(nn), Png.enc.bf(nn))
  Equal.trans(Nat, List.length(&2, U32, Png.enc.blocks(65535, xs)), List.length(&2, U32, bb), Nat.add(List.length(&2,
    U32, xs), Nat.mul(kk, 5n)), Equal.cong(List<&2, U32>, Nat, ys => List.length(&2, U32, ys), Png.enc.blocks(65535,
    xs), bb, sim.blocks(xs, mx, emx, hn, hbig)), cnt(xs, True{}, False{}, kk, 0, nn, Png.enc.cap(nn), Png.enc.bf(nn), mx,
    List.length(&2, U32, xs), emx, {==}, {==}, hn, {==}, kok.rw(U32.to_nat(nn), List.length(&2, U32, xs), kk,
    U32.to_nat(mx), hn, nb.k(nn, mx, emx)), _ez => ({==}, {==})))

# ---- G. the wide file, laid out as spec.png ----

# the CRC register and the accumulator after a run of bytes
def fr(+xs: List<&2, U32>, +cc: U32, +acc: List<&2, U32>) -> U32 & List<&2, U32>:
  (Crc.crc.fold(xs, cc), List.reverse.go(&2, U32, xs, acc))

# folding a list then more is folding both
def fold.app(
  xs: List<&2, U32>,
  +ys: List<&2, U32>,
  +cc: U32
) -> {Crc.crc.fold(List.append(&2, U32, xs, ys), cc) == Crc.crc.fold(ys, Crc.crc.fold(xs, cc)) : U32}:
  match xs:
    case Nil{}:
      {==}
    case +hd <> tl:
      fold.app(tl, ys, Crc.crc.byte(cc, hd))

# a run, then more: one run over both
def fr.app(
  +xs: List<&2, U32>,
  +ys: List<&2, U32>,
  +cc: U32,
  +acc: List<&2, U32>
) -> {fr(ys, Crc.crc.fold(xs, cc), List.reverse.go(&2, U32, xs, acc)) == fr(List.append(&2, U32, xs, ys), cc, acc) :
  U32 & List<&2, U32>}:
  +f2 = Crc.crc.fold(ys, Crc.crc.fold(xs, cc))
  +fa = Crc.crc.fold(List.append(&2, U32, xs, ys), cc)
  +r2 = List.reverse.go(&2, U32, ys, List.reverse.go(&2, U32, xs, acc))
  +ra = List.reverse.go(&2, U32, List.append(&2, U32, xs, ys), acc)
  Equal.trans(U32 & List<&2, U32>, (f2, r2), (fa, r2), (fa, ra),
    Equal.cong(U32, U32 & List<&2, U32>, uu => (uu, r2), f2, fa, Equal.sym(U32, fa, f2, fold.app(xs, ys, cc))),
    Equal.cong(List<&2, U32>, U32 & List<&2, U32>, ll => (fa, ll), r2, ra, Equal.sym(List<&2, U32>, ra, r2,
      W9.revgo_app(xs, ys, acc))))

# three runs reversed onto nothing, reversed back: the runs in order
def rev3(
  +aa: List<&2, U32>,
  +bb: List<&2, U32>,
  +cc: List<&2, U32>
) -> {List.reverse(&2, U32, List.reverse.go(&2, U32, cc, List.reverse.go(&2, U32, bb, List.reverse.go(&2, U32, aa,
  [])))) == List.append(&2, U32, aa, List.append(&2, U32, bb, cc)) : List<&2, U32>}:
  +ab = List.append(&2, U32, aa, bb)
  +abc = List.append(&2, U32, ab, cc)
  Equal.trans(List<&2, U32>, List.reverse(&2, U32, List.reverse.go(&2, U32, cc, List.reverse.go(&2, U32, bb,
    List.reverse.go(&2, U32, aa, [])))), List.reverse(&2, U32, List.reverse.go(&2, U32, abc, [])),
    List.append(&2, U32, aa, List.append(&2, U32, bb, cc)),
    Equal.cong(List<&2, U32>, List<&2, U32>, ll => List.reverse(&2, U32, ll), List.reverse.go(&2, U32, cc,
      List.reverse.go(&2, U32, bb, List.reverse.go(&2, U32, aa, []))), List.reverse.go(&2, U32, abc, []),
      Equal.trans(List<&2, U32>, List.reverse.go(&2, U32, cc, List.reverse.go(&2, U32, bb, List.reverse.go(&2, U32,
        aa, []))), List.reverse.go(&2, U32, cc, List.reverse.go(&2, U32, ab, [])), List.reverse.go(&2, U32, abc, []),
        Equal.cong(List<&2, U32>, List<&2, U32>, ll => List.reverse.go(&2, U32, cc, ll), List.reverse.go(&2, U32, bb,
          List.reverse.go(&2, U32, aa, [])), List.reverse.go(&2, U32, ab, []), Equal.sym(List<&2, U32>,
          List.reverse.go(&2, U32, ab, []), List.reverse.go(&2, U32, bb, List.reverse.go(&2, U32, aa, [])),
          W9.revgo_app(aa, bb, []))),
        Equal.sym(List<&2, U32>, List.reverse.go(&2, U32, abc, []), List.reverse.go(&2, U32, cc, List.reverse.go(&2,
          U32, ab, [])), W9.revgo_app(ab, cc, [])))),
    Equal.trans(List<&2, U32>, List.reverse(&2, U32, List.reverse.go(&2, U32, abc, [])), abc, List.append(&2, U32, aa,
      List.append(&2, U32, bb, cc)), Wp2.rev_rev(abc), Wp2.app_assoc(aa, bb, cc)))

# the end of the IDAT chunk as seal.crc writes it: the length, the type and
# data, the CRC-32 of them, then IEND, once the whole file is reversed
def tail.eq(
  +ll: U32,
  +tt: List<&2, U32>,
  +ie: List<&2, U32>
) -> {List.reverse(&2, U32, Png.enc.cat.go(ie, Png.enc.cat.go(Png.enc.be((Crc.crc.fold(tt, 4294967295) .^.
  4294967295 : U32)), List.reverse.go(&2, U32, tt, Png.enc.cat.go(Png.enc.be(ll), []))))) == List.append(&2, U32,
  Png.enc.be(ll), List.append(&2, U32, tt, List.append(&2, U32, Png.enc.be((Crc.crc.fold(tt, 4294967295) .^.
  4294967295 : U32)), ie))) : List<&2, U32>}:
  +bl = Png.enc.be(ll)
  +ee = Png.enc.be((Crc.crc.fold(tt, 4294967295) .^. 4294967295 : U32))
  +a0 = List.reverse.go(&2, U32, bl, [])
  +a1 = List.reverse.go(&2, U32, tt, a0)
  +a2 = List.reverse.go(&2, U32, ee, a1)
  +lt = List.append(&2, U32, bl, tt)
  Equal.trans(List<&2, U32>, List.reverse(&2, U32, Png.enc.cat.go(ie, Png.enc.cat.go(ee, List.reverse.go(&2, U32, tt,
    Png.enc.cat.go(bl, []))))), List.reverse(&2, U32, List.reverse.go(&2, U32, ie, List.reverse.go(&2, U32, ee,
    List.reverse.go(&2, U32, lt, [])))), List.append(&2, U32, bl, List.append(&2, U32, tt, List.append(&2, U32, ee,
    ie))),
    Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.reverse(&2, U32, ys), Png.enc.cat.go(ie, Png.enc.cat.go(ee,
      List.reverse.go(&2, U32, tt, Png.enc.cat.go(bl, [])))), List.reverse.go(&2, U32, ie, List.reverse.go(&2, U32, ee,
      List.reverse.go(&2, U32, lt, []))),
      Equal.trans(List<&2, U32>, Png.enc.cat.go(ie, Png.enc.cat.go(ee, List.reverse.go(&2, U32, tt, Png.enc.cat.go(bl,
        [])))), Png.enc.cat.go(ie, Png.enc.cat.go(ee, a1)), List.reverse.go(&2, U32, ie, List.reverse.go(&2, U32, ee,
        List.reverse.go(&2, U32, lt, []))),
        Equal.cong(List<&2, U32>, List<&2, U32>, ys => Png.enc.cat.go(ie, Png.enc.cat.go(ee, List.reverse.go(&2, U32,
          tt, ys))), Png.enc.cat.go(bl, []), a0, Wp2.catgo_rev(bl, [])),
        Equal.trans(List<&2, U32>, Png.enc.cat.go(ie, Png.enc.cat.go(ee, a1)), Png.enc.cat.go(ie, a2),
          List.reverse.go(&2, U32, ie, List.reverse.go(&2, U32, ee, List.reverse.go(&2, U32, lt, []))),
          Equal.cong(List<&2, U32>, List<&2, U32>, ys => Png.enc.cat.go(ie, ys), Png.enc.cat.go(ee, a1), a2,
            Wp2.catgo_rev(ee, a1)),
          Equal.trans(List<&2, U32>, Png.enc.cat.go(ie, a2), List.reverse.go(&2, U32, ie, a2), List.reverse.go(&2, U32,
            ie, List.reverse.go(&2, U32, ee, List.reverse.go(&2, U32, lt, []))), Wp2.catgo_rev(ie, a2),
            Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.reverse.go(&2, U32, ie, List.reverse.go(&2, U32, ee,
              ys)), a1, List.reverse.go(&2, U32, lt, []), Equal.sym(List<&2, U32>, List.reverse.go(&2, U32, lt, []), a1,
              W9.revgo_app(bl, tt, []))))))),
    Equal.trans(List<&2, U32>, List.reverse(&2, U32, List.reverse.go(&2, U32, ie, List.reverse.go(&2, U32, ee,
      List.reverse.go(&2, U32, lt, [])))), List.append(&2, U32, lt, List.append(&2, U32, ee, ie)), List.append(&2, U32,
      bl, List.append(&2, U32, tt, List.append(&2, U32, ee, ie))), rev3(lt, ee, ie), Wp2.app_assoc(bl, tt,
      List.append(&2, U32, ee, ie))))

# the zlib stream of stored blocks bb and an Adler-32 sum
def zb(+bb: List<&2, U32>, +sum: U32) -> List<&2, U32>:
  Png.enc.cat([120, 1], Png.enc.cat(bb, Png.enc.be(sum)))

# the IDAT type, the zlib header and the stored blocks
def t0(+bb: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, Png.enc.be(Png.tag.idat()), List.append(&2, U32, [120, 1], bb))

# the chunk's type and data as enc.chunk counts them are t0 then the sum
def body.eq(
  +bb: List<&2, U32>,
  +sum: U32
) -> {Png.enc.cat(Png.enc.be(Png.tag.idat()), zb(bb, sum)) == List.append(&2, U32, t0(bb), Png.enc.be(sum)) :
  List<&2, U32>}:
  +bi = Png.enc.be(Png.tag.idat())
  +bs2 = Png.enc.be(sum)
  +zz = List.append(&2, U32, [120, 1], List.append(&2, U32, bb, bs2))
  Equal.trans(List<&2, U32>, Png.enc.cat(bi, zb(bb, sum)), List.append(&2, U32, bi, zz), List.append(&2, U32, t0(bb),
    bs2),
    Equal.trans(List<&2, U32>, Png.enc.cat(bi, zb(bb, sum)), List.append(&2, U32, bi, zb(bb, sum)), List.append(&2,
      U32, bi, zz), Wp2.cat_app(bi, zb(bb, sum)), Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.append(&2, U32,
      bi, ys), zb(bb, sum), zz, Equal.trans(List<&2, U32>, zb(bb, sum), List.append(&2, U32, [120, 1],
      Png.enc.cat(bb, bs2)), zz, Wp2.cat_app([120, 1], Png.enc.cat(bb, bs2)), Equal.cong(List<&2, U32>, List<&2, U32>,
      ys => List.append(&2, U32, [120, 1], ys), Png.enc.cat(bb, bs2), List.append(&2, U32, bb, bs2),
      Wp2.cat_app(bb, bs2))))),
    Equal.sym(List<&2, U32>, List.append(&2, U32, t0(bb), bs2), List.append(&2, U32, bi, zz), Equal.trans(List<&2,
      U32>, List.append(&2, U32, t0(bb), bs2), List.append(&2, U32, bi, List.append(&2, U32, List.append(&2, U32, [120,
      1], bb), bs2)), List.append(&2, U32, bi, zz), Wp2.app_assoc(bi, List.append(&2, U32, [120, 1], bb), bs2),
      Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.append(&2, U32, bi, ys), List.append(&2, U32,
      List.append(&2, U32, [120, 1], bb), bs2), zz, Wp2.app_assoc([120, 1], bb, bs2)))))

# the file after the IDAT type as the encoder writes it, from t0 on
def gg(+xs: List<&2, U32>, +uu: U32, +ie: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, Png.enc.be(uu), List.append(&2, U32, xs, List.append(&2, U32, Png.enc.be((Crc.crc.fold(xs,
    4294967295) .^. 4294967295 : U32)), ie)))

# enc.chunk of IDAT, then IEND, is gg of its type and data
def chunk.gg(
  +data: List<&2, U32>,
  +ie: List<&2, U32>
) -> {Png.enc.cat(Png.enc.chunk(Png.tag.idat(), data), ie) == gg(Png.enc.cat(Png.enc.be(Png.tag.idat()), data),
  Png.enc.len(data, 0), ie) : List<&2, U32>}:
  +body = Png.enc.cat(Png.enc.be(Png.tag.idat()), data)
  +be_c = Png.enc.be(Crc.crc32(body))
  +be_n = Png.enc.be(Png.enc.len(data, 0))
  Equal.trans(List<&2, U32>, Png.enc.cat(Png.enc.cat(be_n, Png.enc.cat(body, be_c)), ie), List.append(&2, U32,
    List.append(&2, U32, be_n, List.append(&2, U32, body, be_c)), ie), gg(body, Png.enc.len(data, 0), ie),
    Equal.trans(List<&2, U32>, Png.enc.cat(Png.enc.cat(be_n, Png.enc.cat(body, be_c)), ie), List.append(&2, U32,
      Png.enc.cat(be_n, Png.enc.cat(body, be_c)), ie), List.append(&2, U32, List.append(&2, U32, be_n, List.append(&2,
      U32, body, be_c)), ie), Wp2.cat_app(Png.enc.cat(be_n, Png.enc.cat(body, be_c)), ie), Equal.cong(List<&2, U32>,
      List<&2, U32>, ys => List.append(&2, U32, ys, ie), Png.enc.cat(be_n, Png.enc.cat(body, be_c)), List.append(&2,
      U32, be_n, List.append(&2, U32, body, be_c)), Equal.trans(List<&2, U32>, Png.enc.cat(be_n, Png.enc.cat(body,
      be_c)), List.append(&2, U32, be_n, Png.enc.cat(body, be_c)), List.append(&2, U32, be_n, List.append(&2, U32,
      body, be_c)), Wp2.cat_app(be_n, Png.enc.cat(body, be_c)), Equal.cong(List<&2, U32>, List<&2, U32>, ys =>
      List.append(&2, U32, be_n, ys), Png.enc.cat(body, be_c), List.append(&2, U32, body, be_c), Wp2.cat_app(body,
      be_c))))),
    Equal.trans(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, be_n, List.append(&2, U32, body, be_c)), ie),
      List.append(&2, U32, be_n, List.append(&2, U32, List.append(&2, U32, body, be_c), ie)), gg(body,
      Png.enc.len(data, 0), ie), Wp2.app_assoc(be_n, List.append(&2, U32, body, be_c), ie), Equal.cong(List<&2, U32>,
      List<&2, U32>, ys => List.append(&2, U32, be_n, ys), List.append(&2, U32, List.append(&2, U32, body, be_c), ie),
      List.append(&2, U32, body, List.append(&2, U32, be_c, ie)), Wp2.app_assoc(body, be_c, ie))))

# the IDAT chunk from its CRC run: the run over the type, header and blocks,
# then the Adler-32 sum, the CRC, and IEND, is enc.chunk's IDAT then IEND
def tail.chunk(
  +bb: List<&2, U32>,
  +sum: U32,
  +ll: U32,
  +ie: List<&2, U32>,
  +hl: {ll == Png.enc.len(zb(bb, sum), 0) : U32}
) -> {Png.enc.seal.adler(fr(t0(bb), 4294967295, Png.enc.cat.go(Png.enc.be(ll), [])), sum, ie) ==
  Png.enc.cat(Png.enc.chunk(Png.tag.idat(), zb(bb, sum)), ie) : List<&2, U32>}:
  +aa = Png.enc.cat.go(Png.enc.be(ll), [])
  +bs2 = Png.enc.be(sum)
  +tt = List.append(&2, U32, t0(bb), bs2)
  +c0 = Crc.crc.fold(t0(bb), 4294967295)
  +r0 = List.reverse.go(&2, U32, t0(bb), aa)
  +body = Png.enc.cat(Png.enc.be(Png.tag.idat()), zb(bb, sum))
  Equal.trans(List<&2, U32>, Png.enc.seal.crc(Png.enc.crc.list(bs2, c0, r0), ie), gg(tt, ll, ie),
    Png.enc.cat(Png.enc.chunk(Png.tag.idat(), zb(bb, sum)), ie),
    Equal.trans(List<&2, U32>, Png.enc.seal.crc(Png.enc.crc.list(bs2, c0, r0), ie), Png.enc.seal.crc(fr(tt,
      4294967295, aa), ie), gg(tt, ll, ie),
      Equal.cong(U32 & List<&2, U32>, List<&2, U32>, pp => Png.enc.seal.crc(pp, ie), Png.enc.crc.list(bs2, c0, r0),
        fr(tt, 4294967295, aa), Equal.trans(U32 & List<&2, U32>, Png.enc.crc.list(bs2, c0, r0), fr(bs2, c0, r0),
        fr(tt, 4294967295, aa), crcl(bs2, c0, r0), fr.app(t0(bb), bs2, 4294967295, aa))),
      tail.eq(ll, tt, ie)),
    Equal.sym(List<&2, U32>, Png.enc.cat(Png.enc.chunk(Png.tag.idat(), zb(bb, sum)), ie), gg(tt, ll, ie),
      Equal.trans(List<&2, U32>, Png.enc.cat(Png.enc.chunk(Png.tag.idat(), zb(bb, sum)), ie), gg(body,
        Png.enc.len(zb(bb, sum), 0), ie), gg(tt, ll, ie), chunk.gg(zb(bb, sum), ie),
        Equal.trans(List<&2, U32>, gg(body, Png.enc.len(zb(bb, sum), 0), ie), gg(tt, Png.enc.len(zb(bb, sum), 0), ie),
          gg(tt, ll, ie), Equal.cong(List<&2, U32>, List<&2, U32>, xs => gg(xs, Png.enc.len(zb(bb, sum), 0), ie), body,
          tt, body.eq(bb, sum)), Equal.cong(U32, List<&2, U32>, uu => gg(tt, uu, ie), Png.enc.len(zb(bb, sum), 0), ll,
          Equal.sym(U32, ll, Png.enc.len(zb(bb, sum), 0), hl))))))

# seal.wide up to the Adler field: the CRC run over the IDAT type, the zlib
# header and bs's blocks
def wide.front(
  +raw: List<&2, U32>,
  +nn: U32,
  +sum: U32,
  +aa: List<&2, U32>,
  +ie: List<&2, U32>
) -> {Png.enc.seal.body(Png.enc.crc.list(Png.enc.be(Png.tag.idat()), 4294967295, aa), raw, nn, sum, ie) ==
  Png.enc.seal.adler(fr(t0(bs(raw, True{}, False{}, 0, nn, Png.enc.cap(nn), Png.enc.bf(nn))), 4294967295, aa), sum,
  ie) : List<&2, U32>}:
  +bi = Png.enc.be(Png.tag.idat())
  +bb = bs(raw, True{}, False{}, 0, nn, Png.enc.cap(nn), Png.enc.bf(nn))
  +c1 = Crc.crc.fold(bi, 4294967295)
  +a1 = List.reverse.go(&2, U32, bi, aa)
  +c2 = Crc.crc.fold([120, 1], c1)
  +a2 = List.reverse.go(&2, U32, [120, 1], a1)
  Equal.trans(List<&2, U32>, Png.enc.seal.body(Png.enc.crc.list(bi, 4294967295, aa), raw, nn, sum, ie),
    Png.enc.seal.body(fr(bi, 4294967295, aa), raw, nn, sum, ie), Png.enc.seal.adler(fr(t0(bb), 4294967295, aa), sum,
    ie),
    Equal.cong(U32 & List<&2, U32>, List<&2, U32>, pp => Png.enc.seal.body(pp, raw, nn, sum, ie),
      Png.enc.crc.list(bi, 4294967295, aa), fr(bi, 4294967295, aa), crcl(bi, 4294967295, aa)),
    Equal.trans(List<&2, U32>, Png.enc.seal.run(Png.enc.crc.list([120, 1], c1, a1), raw, nn, sum, ie),
      Png.enc.seal.run(fr([120, 1], c1, a1), raw, nn, sum, ie), Png.enc.seal.adler(fr(t0(bb), 4294967295, aa), sum,
      ie),
      Equal.cong(U32 & List<&2, U32>, List<&2, U32>, pp => Png.enc.seal.run(pp, raw, nn, sum, ie),
        Png.enc.crc.list([120, 1], c1, a1), fr([120, 1], c1, a1), crcl([120, 1], c1, a1)),
      Equal.cong(U32 & List<&2, U32>, List<&2, U32>, pp => Png.enc.seal.adler(pp, sum, ie), Png.enc.pour(raw, True{},
        False{}, 0, nn, Png.enc.cap(nn), Png.enc.bf(nn), c2, a2), fr(t0(bb), 4294967295, aa),
        Equal.trans(U32 & List<&2, U32>, Png.enc.pour(raw, True{}, False{}, 0, nn, Png.enc.cap(nn), Png.enc.bf(nn), c2,
          a2), Png.enc.crc.list(bb, c2, a2), fr(t0(bb), 4294967295, aa), pour.bs(raw, True{}, False{}, 0, nn,
          Png.enc.cap(nn), Png.enc.bf(nn), c2, a2),
          Equal.trans(U32 & List<&2, U32>, Png.enc.crc.list(bb, c2, a2), fr(bb, c2, a2), fr(t0(bb), 4294967295, aa),
            crcl(bb, c2, a2),
            Equal.trans(U32 & List<&2, U32>, fr(bb, c2, a2), fr(List.append(&2, U32, [120, 1], bb), c1, a1),
              fr(t0(bb), 4294967295, aa), fr.app([120, 1], bb, c1, a1), fr.app(bi, List.append(&2, U32, [120, 1],
              bb), 4294967295, aa)))))))

# seal.wide after the signature and IHDR: the IDAT chunk holding the zlib
# stream of stored blocks of 65535 bytes, then IEND, when its length field is
# right. The IHDR stays out of the statement: its CRC over a symbolic width
# and height costs the checker seconds each time a type holding it is read.
def wide.tail(
  +raw: List<&2, U32>,
  +mx: U32,
  +ie: List<&2, U32>,
  +emx: {mx == 65535 : U32},
  +hn: {U32.to_nat(Png.enc.len(raw, 0)) == List.length(&2, U32, raw) : Nat},
  +hbig: {U32.is_le(Png.enc.len(raw, 0), 65535) == False{} : Bool},
  +hl: {Png.enc.idat.ln(Png.enc.len(raw, 0)) == Png.enc.len(Laws.zlib.stored(65535, raw), 0) : U32}
) -> {Png.enc.seal.body(Png.enc.crc.list(Png.enc.be(Png.tag.idat()), 4294967295,
  Png.enc.cat.go(Png.enc.be(Png.enc.idat.ln(Png.enc.len(raw, 0))), [])), raw, Png.enc.len(raw, 0), Inf.adler.of(raw),
  ie) == Png.enc.cat(Png.enc.chunk(Png.tag.idat(), Laws.zlib.stored(65535, raw)), ie) : List<&2, U32>}:
  +nn = Png.enc.len(raw, 0)
  +sum = Inf.adler.of(raw)
  +ll = Png.enc.idat.ln(nn)
  +aa = Png.enc.cat.go(Png.enc.be(ll), [])
  +bb = bs(raw, True{}, False{}, 0, nn, Png.enc.cap(nn), Png.enc.bf(nn))
  +bl = Png.enc.blocks(65535, raw)
  +e_b = {sim.blocks(raw, mx, emx, hn, hbig) : {bl == bb : List<&2, U32>}}
  +zz = Laws.zlib.stored(65535, raw)
  +hl2 = {Equal.trans(U32, ll, Png.enc.len(zz, 0), Png.enc.len(zb(bb, sum), 0), hl, Equal.cong(List<&2, U32>, U32, ys =>
    Png.enc.len(zb(ys, sum), 0), bl, bb, e_b)) : {ll == Png.enc.len(zb(bb, sum), 0) : U32}}
  Equal.trans(List<&2, U32>, Png.enc.seal.body(Png.enc.crc.list(Png.enc.be(Png.tag.idat()), 4294967295, aa), raw, nn,
    sum, ie), Png.enc.seal.adler(fr(t0(bb), 4294967295, aa), sum, ie), Png.enc.cat(Png.enc.chunk(Png.tag.idat(), zz),
    ie), wide.front(raw, nn, sum, aa, ie), Equal.trans(List<&2, U32>, Png.enc.seal.adler(fr(t0(bb), 4294967295, aa),
    sum, ie), Png.enc.cat(Png.enc.chunk(Png.tag.idat(), zb(bb, sum)), ie), Png.enc.cat(Png.enc.chunk(Png.tag.idat(),
    zz), ie), tail.chunk(bb, sum, ll, ie, hl2), Equal.cong(List<&2, U32>, List<&2, U32>, ys =>
    Png.enc.cat(Png.enc.chunk(Png.tag.idat(), zb(ys, sum)), ie), bb, bl, Equal.sym(List<&2, U32>, bl, bb, e_b))))

# 2 and x + 4 is x + 6
def add.six(+xx: Nat) -> {2n+Nat.add(xx, 4n) == Nat.add(xx, 6n) : Nat}:
  Equal.sym(Nat, Nat.add(xx, 6n), 2n+Nat.add(xx, 4n), Equal.trans(Nat, Nat.add(xx, 6n), 1n+Nat.add(xx, 5n),
    2n+Nat.add(xx, 4n), R.add_succ(xx, 5n), Equal.cong(Nat, Nat, kk => 1n+kk, Nat.add(xx, 5n), 1n+Nat.add(xx, 4n),
    R.add_succ(xx, 4n))))

# the zlib stream of stored blocks of 65535 bytes: 6 bytes, the list, and 5
# for each of enc.nblk's block headers
def zlib.len(
  +raw: List<&2, U32>,
  +mx: U32,
  +emx: {mx == 65535 : U32},
  +hn: {U32.to_nat(Png.enc.len(raw, 0)) == List.length(&2, U32, raw) : Nat},
  +hbig: {U32.is_le(Png.enc.len(raw, 0), 65535) == False{} : Bool}
) -> {List.length(&2, U32, Laws.zlib.stored(65535, raw)) == Nat.add(Nat.add(List.length(&2, U32, raw),
  Nat.mul(U32.to_nat(Png.enc.nblk(Png.enc.len(raw, 0))), 5n)), 6n) : Nat}:
  +bl = Png.enc.blocks(65535, raw)
  +be_s = Png.enc.be(Inf.adler.of(raw))
  +xx = Nat.add(List.length(&2, U32, raw), Nat.mul(U32.to_nat(Png.enc.nblk(Png.enc.len(raw, 0))), 5n))
  +ap = List.append(&2, U32, [120, 1], List.append(&2, U32, bl, be_s))
  Equal.trans(Nat, List.length(&2, U32, Laws.zlib.stored(65535, raw)), List.length(&2, U32, ap), Nat.add(xx, 6n),
    Equal.cong(List<&2, U32>, Nat, ys => List.length(&2, U32, ys), Laws.zlib.stored(65535, raw), ap, Equal.trans(List<&2,
    U32>, Laws.zlib.stored(65535, raw), List.append(&2, U32, [120, 1], Png.enc.cat(bl, be_s)), ap, Wp2.cat_app([120, 1],
    Png.enc.cat(bl, be_s)), Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.append(&2, U32, [120, 1], ys),
    Png.enc.cat(bl, be_s), List.append(&2, U32, bl, be_s), Wp2.cat_app(bl, be_s)))),
    Equal.trans(Nat, List.length(&2, U32, ap), 2n+Nat.add(List.length(&2, U32, bl), 4n), Nat.add(xx, 6n),
      Equal.cong(Nat, Nat, kk => 2n+kk, List.length(&2, U32, List.append(&2, U32, bl, be_s)), Nat.add(List.length(&2,
      U32, bl), 4n), W9.len.app(bl, be_s)),
      Equal.trans(Nat, 2n+Nat.add(List.length(&2, U32, bl), 4n), 2n+Nat.add(xx, 4n), Nat.add(xx, 6n), Equal.cong(Nat,
        Nat, kk => 2n+Nat.add(kk, 4n), List.length(&2, U32, bl), xx, cnt.blocks(raw, mx, emx, hn, hbig)),
        add.six(xx))))

# the IDAT length the encoder writes is the zlib stream's, when the stream is
# at most some U32's value long
def idat.len(
  +raw: List<&2, U32>,
  +mx: U32,
  +tu: U32,
  +emx: {mx == 65535 : U32},
  +hn: {U32.to_nat(Png.enc.len(raw, 0)) == List.length(&2, U32, raw) : Nat},
  +hbig: {U32.is_le(Png.enc.len(raw, 0), 65535) == False{} : Bool},
  +h_tu: {Nat.is_le(Nat.add(Nat.add(List.length(&2, U32, raw), Nat.mul(U32.to_nat(Png.enc.nblk(Png.enc.len(raw, 0))),
    5n)), 6n), U32.to_nat(tu)) == True{} : Bool}
) -> {Png.enc.idat.ln(Png.enc.len(raw, 0)) == Png.enc.len(Laws.zlib.stored(65535, raw), 0) : U32}:
  +nn = Png.enc.len(raw, 0)
  +kb = Png.enc.nblk(nn)
  +k5 = Nat.mul(U32.to_nat(kb), 5n)
  +n0 = List.length(&2, U32, raw)
  +xx = Nat.add(n0, k5)
  +tn = U32.to_nat(tu)
  +h_x = {R.le_add_r(xx, 6n, tn, h_tu) : {Nat.is_le(xx, tn) == True{} : Bool}}
  +h_k = {R.le_add_l(n0, k5, tn, h_x) : {Nat.is_le(k5, tn) == True{} : Bool}}
  +e_m = {R.u32_mul_below(kb, 5, tu, h_k) : {U32.to_nat((kb * 5 : U32)) == k5 : Nat}}
  +h_a = {R.le_rw_l(xx, Nat.add(U32.to_nat(nn), U32.to_nat((kb * 5 : U32))), tn, Equal.trans(Nat, xx, Nat.add(U32.to_nat(nn),
    k5), Nat.add(U32.to_nat(nn), U32.to_nat((kb * 5 : U32))), Equal.cong(Nat, Nat, kk => Nat.add(kk, k5), n0,
    U32.to_nat(nn), Equal.sym(Nat, U32.to_nat(nn), n0, hn)), Equal.cong(Nat, Nat, kk => Nat.add(U32.to_nat(nn), kk), k5,
    U32.to_nat((kb * 5 : U32)), Equal.sym(Nat, U32.to_nat((kb * 5 : U32)), k5, e_m))), h_x) :
    {Nat.is_le(Nat.add(U32.to_nat(nn), U32.to_nat((kb * 5 : U32))), tn) == True{} : Bool}}
  +e_a = {Equal.trans(Nat, U32.to_nat((nn + (kb * 5 : U32) : U32)), Nat.add(U32.to_nat(nn), U32.to_nat((kb * 5 : U32))), xx,
    R.u32_add_below(nn, (kb * 5 : U32), tu, h_a), Equal.trans(Nat, Nat.add(U32.to_nat(nn), U32.to_nat((kb * 5 : U32))),
    Nat.add(n0, U32.to_nat((kb * 5 : U32))), xx, Equal.cong(Nat, Nat, kk => Nat.add(kk, U32.to_nat((kb * 5 : U32))),
    U32.to_nat(nn), n0, hn), Equal.cong(Nat, Nat, kk => Nat.add(n0, kk), U32.to_nat((kb * 5 : U32)), k5, e_m))) :
    {U32.to_nat((nn + (kb * 5 : U32) : U32)) == xx : Nat}}
  +s1 = (nn + (kb * 5 : U32) : U32)
  +h_6 = {R.le_rw_l(Nat.add(xx, 6n), Nat.add(U32.to_nat(s1), 6n), tn, Equal.cong(Nat, Nat, kk => Nat.add(kk, 6n), xx,
    U32.to_nat(s1), Equal.sym(Nat, U32.to_nat(s1), xx, e_a)), h_tu) : {Nat.is_le(Nat.add(U32.to_nat(s1), U32.to_nat(6)),
    tn) == True{} : Bool}}
  +e_i = {Equal.trans(Nat, U32.to_nat((s1 + 6 : U32)), Nat.add(U32.to_nat(s1), 6n), Nat.add(xx, 6n),
    R.u32_add_below(s1, 6, tu, h_6), Equal.cong(Nat, Nat, kk => Nat.add(kk, 6n), U32.to_nat(s1), xx, e_a)) :
    {U32.to_nat(Png.enc.idat.ln(nn)) == Nat.add(xx, 6n) : Nat}}
  +zz = Laws.zlib.stored(65535, raw)
  +e_z = {zlib.len(raw, mx, emx, hn, hbig) : {List.length(&2, U32, zz) == Nat.add(xx, 6n) : Nat}}
  +e_zl = {len.of(zz, tu, R.le_rw_l(Nat.add(xx, 6n), List.length(&2, U32, zz), tn, Equal.sym(Nat, List.length(&2, U32,
    zz), Nat.add(xx, 6n), e_z), h_tu)) : {U32.to_nat(Png.enc.len(zz, 0)) == List.length(&2, U32, zz) : Nat}}
  u32.same(Png.enc.idat.ln(nn), Png.enc.len(zz, 0), Equal.trans(Nat, U32.to_nat(Png.enc.idat.ln(nn)), Nat.add(xx, 6n),
    U32.to_nat(Png.enc.len(zz, 0)), e_i, Equal.sym(Nat, U32.to_nat(Png.enc.len(zz, 0)), Nat.add(xx, 6n), Equal.trans(Nat,
    U32.to_nat(Png.enc.len(zz, 0)), List.length(&2, U32, zz), Nat.add(xx, 6n), e_zl, e_z))))

# ---- H. enc.rgb.go against bs ----

# Adler-32 as enc.rgb.go adds it up, then packed
def afold(xs: List<&2, U32>, +aa: U32, +bb: U32) -> U32:
  match xs:
    case Nil{}:
      ((bb << 16n : U32) .|. aa : U32)
    case +x <> t:
      +a2 = Png.enc.add(aa, x)
      +b2 = Png.enc.add(bb, a2)
      afold(t, a2, b2)

# the raw bytes enc.rgb.go's cursor has still to write, for a picture of
# rows wn samples wide: a filter byte first at a row's start, red while the
# sample is still in px, then green and blue of col
def cur(filt: Bool, zred: Bool, zgrn: Bool, px: List<&2, U32>, +col: U32, +row: U32, +wn: Nat) -> List<&2, U32>:
  match filt:
    case True{}:
      W9.sc(px, 0n, wn, True{})
    case False{}:
      match zred:
        case True{}:
          W9.sc(px, U32.to_nat(row), wn, True{})
        case False{}:
          match zgrn:
            case True{}:
              Png.enc.g(col) <> Png.enc.b(col) <> W9.sc(px, Png.enc.pred(U32.to_nat(row)), wn, True{})
            case False{}:
              Png.enc.b(col) <> W9.sc(px, Png.enc.pred(U32.to_nat(row)), wn, True{})

# the room bs has in its open block: none at a block's start
def rm(zblock: Bool, +need: U32) -> U32:
  match zblock:
    case True{}:
      0
    case False{}:
      need

# the facts enc.rgb.go's block state carries, nr the raw bytes still to come:
# at a block's start, left counts them; inside a block, need bytes are left
# in it, and left less len counts the bytes after it
def rg.hyp(
  zblock: Bool,
  +zdone: Bool,
  +zspan: Bool,
  +zneed: Bool,
  +nr: Nat,
  +left: U32,
  +len: U32,
  +need: U32,
  +pl: U32,
  +plen: U32,
  +pbf: U32
) -> Type:
  match zblock:
    case True{}:
      {zdone == U32.is_zero(left) : Bool} & {U32.to_nat(left) == nr : Nat}
    case False{}:
      {zdone == False{} : Bool} & ({zspan == True{} : Bool} & ({zneed == U32.is_zero(need) : Bool} &
        ({U32.to_nat(pl) == nr : Nat} & ({Nat.add(U32.to_nat(len), nr) == Nat.add(U32.to_nat(left), U32.to_nat(need)) :
        Nat} & at.edge(need, pl, plen, pbf)))))

# what enc.rgb.go returns: the CRC run over bs's blocks, and Adler-32 of the raw bytes
def rg.val(
  zblock: Bool,
  +rr: List<&2, U32>,
  +cc: U32,
  +acc: List<&2, U32>,
  +aa: U32,
  +bb: U32,
  +left: U32,
  +need: U32,
  +pl: U32,
  +plen: U32,
  +pbf: U32
) -> (U32 & List<&2, U32>) & U32:
  match zblock:
    case True{}:
      (fr(bs(rr, True{}, False{}, 0, left, Png.enc.cap(left), Png.enc.bf(left)), cc, acc), afold(rr, aa, bb))
    case False{}:
      (fr(bs(rr, U32.is_zero(need), U32.is_eq(need, 1), need, pl, plen, pbf), cc, acc), afold(rr, aa, bb))

# no raw bytes left: enc.rgb.go's end is bs's
def nil.r(
  xs: List<&2, U32>,
  +z1: Bool,
  +z2: Bool,
  +r1: U32,
  +l1: U32,
  +n1: U32,
  +f1: U32,
  +cc: U32,
  +acc: List<&2, U32>,
  +aa: U32,
  +bb: U32,
  +hh: {List.length(&2, U32, xs) == 0n : Nat}
) -> {Png.enc.rgb.fin(cc, acc, aa, bb) == (fr(bs(xs, z1, z2, r1, l1, n1, f1), cc, acc), afold(xs, aa, bb)) : (U32 &
  List<&2, U32>) & U32}:
  match xs:
    case Nil{}:
      {==}
    case _x <> t:
      Empty.absurd({Png.enc.rgb.fin(cc, acc, aa, bb) == (fr(bs(_x <> t, z1, z2, r1, l1, n1, f1), cc, acc), afold(_x <> t,
        aa, bb)) : (U32 & List<&2, U32>) & U32}, Wp1.zero_succ(List.length(&2, U32, t), Equal.sym(Nat, 1n+List.length(&2,
        U32, t), 0n, hh)))

# one raw byte: bs writes it, and the block goes on or closes
def step(
  z1: Bool,
  +xb: U32,
  +rr: List<&2, U32>,
  +need: U32,
  +pl: U32,
  +plen: U32,
  +pbf: U32,
  +cc: U32,
  +acc: List<&2, U32>,
  +aa: U32,
  +bb: U32,
  -gg: (U32 & List<&2, U32>) & U32,
  +ez1: {U32.is_eq(need, 1) == z1 : Bool},
  +nz: {U32.is_zero(need) == False{} : Bool},
  ih: @xx: U32 -> @yy: U32 -> at.edge((need - 1 : U32), (pl - 1 : U32), xx, yy) -> {gg == (fr(bs(rr, U32.is_zero((need -
    1 : U32)), U32.is_eq((need - 1 : U32), 1), (need - 1 : U32), (pl - 1 : U32), xx, yy), Crc.crc.byte(cc, xb),
    xb <> acc), afold(rr, Png.enc.add(aa, xb), Png.enc.add(bb, Png.enc.add(aa, xb)))) : (U32 & List<&2, U32>) & U32}
) -> {gg == (fr(bs(xb <> rr, False{}, U32.is_eq(need, 1), need, pl, plen, pbf), cc, acc), afold(xb <> rr, aa, bb)) :
  (U32 & List<&2, U32>) & U32}:
  match z1:
    case True{}:
      +n1 = (need - 1 : U32)
      +p1 = (pl - 1 : U32)
      +c1 = Crc.crc.byte(cc, xb)
      +a2 = Png.enc.add(aa, xb)
      +b2 = Png.enc.add(bb, a2)
      +e1 = {one.val(need, Equal.sym(Bool, U32.is_eq(need, 1), True{}, ez1)) : {U32.to_nat(need) == 1n : Nat}}
      +e0 = {u32.same(n1, 0, Wp1.u32_pred(need, 0n, e1)) : {n1 == 0 : U32}}
      %Equal.sym(Bool, U32.is_eq(need, 1), True{}, ez1) : {gg == (fr(bs(xb <> rr, False{}, _, need, pl, plen, pbf), cc,
        acc), afold(xb <> rr, aa, bb)) : (U32 & List<&2, U32>) & U32}
      Equal.trans((U32 & List<&2, U32>) & U32, gg, (fr(bs(rr, U32.is_zero(n1), U32.is_eq(n1, 1), n1, p1,
        Png.enc.cap(p1), Png.enc.bf(p1)), c1, xb <> acc), afold(rr, a2, b2)), (fr(bs(rr, True{}, False{}, 0, p1,
        Png.enc.cap(p1), Png.enc.bf(p1)), c1, xb <> acc), afold(rr, a2, b2)),
        ih(Png.enc.cap(p1), Png.enc.bf(p1), _ez => ({==}, {==})),
        Equal.cong(U32, (U32 & List<&2, U32>) & U32, uu => (fr(bs(rr, U32.is_zero(uu), U32.is_eq(uu, 1), uu, p1,
          Png.enc.cap(p1), Png.enc.bf(p1)), c1, xb <> acc), afold(rr, a2, b2)), n1, 0, e0))
    case False{}:
      +n1 = (need - 1 : U32)
      +p1 = (pl - 1 : U32)
      +c1 = Crc.crc.byte(cc, xb)
      +a2 = Png.enc.add(aa, xb)
      +b2 = Png.enc.add(bb, a2)
      +nz1 = {two(need, Equal.sym(Bool, U32.is_zero(need), False{}, nz), Equal.sym(Bool, U32.is_eq(need, 1), False{},
        ez1)) : {U32.is_zero(n1) == False{} : Bool}}
      %Equal.sym(Bool, U32.is_eq(need, 1), False{}, ez1) : {gg == (fr(bs(xb <> rr, False{}, _, need, pl, plen, pbf), cc,
        acc), afold(xb <> rr, aa, bb)) : (U32 & List<&2, U32>) & U32}
      Equal.trans((U32 & List<&2, U32>) & U32, gg, (fr(bs(rr, U32.is_zero(n1), U32.is_eq(n1, 1), n1, p1, plen, pbf), c1,
        xb <> acc), afold(rr, a2, b2)), (fr(bs(rr, False{}, U32.is_eq(n1, 1), n1, p1, plen, pbf), c1, xb <> acc),
        afold(rr, a2, b2)),
        ih(plen, pbf, edge.no(n1, p1, plen, pbf, nz1)),
        Equal.cong(Bool, (U32 & List<&2, U32>) & U32, zb => (fr(bs(rr, zb, U32.is_eq(n1, 1), n1, p1, plen, pbf), c1,
          xb <> acc), afold(rr, a2, b2)), U32.is_zero(n1), False{}, nz1))

# a raw byte in a block, from the rg state: the facts for the state after it,
# then step, then rg.val read with the byte in front
def rg.byte(
  +pp: Nat,
  +xb: U32,
  +rr: List<&2, U32>,
  +r2: List<&2, U32>,
  +need: U32,
  +pl: U32,
  +plen: U32,
  +pbf: U32,
  +cc: U32,
  +acc: List<&2, U32>,
  +aa: U32,
  +bb: U32,
  +left: U32,
  +len: U32,
  +kk: Nat,
  +xn: Nat,
  -gg: (U32 & List<&2, U32>) & U32,
  +e_r: {rr == xb <> r2 : List<&2, U32>},
  +e_zn: {False{} == U32.is_zero(need) : Bool},
  +hx: {Nat.add(U32.to_nat(need), xn) == List.length(&2, U32, rr) : Nat},
  +hw: {Nat.is_le(Nat.add(Nat.add(List.length(&2, U32, rr), 1n), Nat.double(kk)), 2n+pp) == True{} : Bool},
  +e_pl: {U32.to_nat(pl) == List.length(&2, U32, rr) : Nat},
  +e_ll: {Nat.add(U32.to_nat(len), List.length(&2, U32, rr)) == Nat.add(U32.to_nat(left), U32.to_nat(need)) : Nat},
  ih: @xx: U32 -> @yy: U32 -> at.edge((need - 1 : U32), (pl - 1 : U32), xx, yy) -> {Nat.add(U32.to_nat((need - 1 : U32)),
    xn) == List.length(&2, U32, r2) : Nat} -> {Nat.is_le(Nat.add(Nat.add(List.length(&2, U32, r2), 1n),
    Nat.double(kk)), 1n+pp) == True{} : Bool} -> {U32.to_nat((pl - 1 : U32)) == List.length(&2, U32, r2) : Nat} ->
    {Nat.add(U32.to_nat(len), List.length(&2, U32, r2)) == Nat.add(U32.to_nat(left), U32.to_nat((need - 1 : U32))) :
    Nat} -> {gg == (fr(bs(r2, U32.is_zero((need - 1 : U32)), U32.is_eq((need - 1 : U32), 1), (need - 1 : U32), (pl - 1 :
    U32), xx, yy), Crc.crc.byte(cc, xb), xb <> acc), afold(r2, Png.enc.add(aa, xb), Png.enc.add(bb, Png.enc.add(aa,
    xb)))) : (U32 & List<&2, U32>) & U32}
) -> {gg == rg.val(False{}, rr, cc, acc, aa, bb, left, need, pl, plen, pbf) : (U32 & List<&2, U32>) & U32}:
  +n1 = (need - 1 : U32)
  +nr = List.length(&2, U32, r2)
  +nz = {Equal.sym(Bool, False{}, U32.is_zero(need), e_zn) : {U32.is_zero(need) == False{} : Bool}}
  +e_n = {Wp1.u32_dec(need, nz) : {U32.to_nat(need) == 1n+U32.to_nat(n1) : Nat}}
  +e_len = {Equal.cong(List<&2, U32>, Nat, ys => List.length(&2, U32, ys), rr, xb <> r2, e_r) : {List.length(&2, U32,
    rr) == 1n+nr : Nat}}
  +hx2 = {Wp1.succ_inj(Nat.add(U32.to_nat(n1), xn), nr, Equal.trans(Nat, 1n+Nat.add(U32.to_nat(n1), xn),
    Nat.add(U32.to_nat(need), xn), 1n+nr, Equal.cong(Nat, Nat, kz => Nat.add(kz, xn), 1n+U32.to_nat(n1),
    U32.to_nat(need), Equal.sym(Nat, U32.to_nat(need), 1n+U32.to_nat(n1), e_n)), Equal.trans(Nat, Nat.add(U32.to_nat(need),
    xn), List.length(&2, U32, rr), 1n+nr, hx, e_len))) : {Nat.add(U32.to_nat(n1), xn) == nr : Nat}}
  +hw2 = {Equal.trans(Bool, Nat.is_le(Nat.add(Nat.add(1n+nr, 1n), Nat.double(kk)), 2n+pp), Nat.is_le(Nat.add(Nat.add(
    List.length(&2, U32, rr), 1n), Nat.double(kk)), 2n+pp), True{}, Equal.cong(Nat, Bool, kz =>
    Nat.is_le(Nat.add(Nat.add(kz, 1n), Nat.double(kk)), 2n+pp), 1n+nr, List.length(&2, U32, rr), Equal.sym(Nat,
    List.length(&2, U32, rr), 1n+nr, e_len)), hw) : {Nat.is_le(Nat.add(Nat.add(nr, 1n), Nat.double(kk)), 1n+pp) ==
    True{} : Bool}}
  +epl2 = {Wp1.u32_pred(pl, nr, Equal.trans(Nat, U32.to_nat(pl), List.length(&2, U32, rr), 1n+nr, e_pl, e_len)) :
    {U32.to_nat((pl - 1 : U32)) == nr : Nat}}
  +ell2 = {Wp1.succ_inj(Nat.add(U32.to_nat(len), nr), Nat.add(U32.to_nat(left), U32.to_nat(n1)), Equal.trans(Nat,
    1n+Nat.add(U32.to_nat(len), nr), Nat.add(U32.to_nat(len), 1n+nr), 1n+Nat.add(U32.to_nat(left), U32.to_nat(n1)),
    Equal.sym(Nat, Nat.add(U32.to_nat(len), 1n+nr), 1n+Nat.add(U32.to_nat(len), nr), R.add_succ(U32.to_nat(len), nr)),
    Equal.trans(Nat, Nat.add(U32.to_nat(len), 1n+nr), Nat.add(U32.to_nat(left), 1n+U32.to_nat(n1)),
    1n+Nat.add(U32.to_nat(left), U32.to_nat(n1)), Equal.trans(Nat, Nat.add(U32.to_nat(len), 1n+nr),
    Nat.add(U32.to_nat(len), List.length(&2, U32, rr)), Nat.add(U32.to_nat(left), 1n+U32.to_nat(n1)), Equal.cong(Nat, Nat,
    kz => Nat.add(U32.to_nat(len), kz), 1n+nr, List.length(&2, U32, rr), Equal.sym(Nat, List.length(&2, U32, rr), 1n+nr,
    e_len)), Equal.trans(Nat, Nat.add(U32.to_nat(len), List.length(&2, U32, rr)), Nat.add(U32.to_nat(left),
    U32.to_nat(need)), Nat.add(U32.to_nat(left), 1n+U32.to_nat(n1)), e_ll, Equal.cong(Nat, Nat, kz =>
    Nat.add(U32.to_nat(left), kz), U32.to_nat(need), 1n+U32.to_nat(n1), e_n))), R.add_succ(U32.to_nat(left),
    U32.to_nat(n1))))) : {Nat.add(U32.to_nat(len), nr) == Nat.add(U32.to_nat(left), U32.to_nat(n1)) : Nat}}
  Equal.trans((U32 & List<&2, U32>) & U32, gg, (fr(bs(xb <> r2, False{}, U32.is_eq(need, 1), need, pl, plen, pbf), cc,
    acc), afold(xb <> r2, aa, bb)), rg.val(False{}, rr, cc, acc, aa, bb, left, need, pl, plen, pbf),
    step(U32.is_eq(need, 1), xb, r2, need, pl, plen, pbf, cc, acc, aa, bb, gg, {==}, nz, xx => yy => ee => ih(xx, yy,
      ee, hx2, hw2, epl2, ell2)),
    Equal.sym((U32 & List<&2, U32>) & U32, rg.val(False{}, rr, cc, acc, aa, bb, left, need, pl, plen, pbf),
      (fr(bs(xb <> r2, False{}, U32.is_eq(need, 1), need, pl, plen, pbf), cc, acc), afold(xb <> r2, aa, bb)),
      Equal.trans((U32 & List<&2, U32>) & U32, rg.val(False{}, rr, cc, acc, aa, bb, left, need, pl, plen, pbf),
        (fr(bs(rr, False{}, U32.is_eq(need, 1), need, pl, plen, pbf), cc, acc), afold(rr, aa, bb)),
        (fr(bs(xb <> r2, False{}, U32.is_eq(need, 1), need, pl, plen, pbf), cc, acc), afold(xb <> r2, aa, bb)),
        Equal.cong(Bool, (U32 & List<&2, U32>) & U32, zb => (fr(bs(rr, zb, U32.is_eq(need, 1), need, pl, plen, pbf),
          cc, acc), afold(rr, aa, bb)), U32.is_zero(need), False{}, nz),
        Equal.cong(List<&2, U32>, (U32 & List<&2, U32>) & U32, ys => (fr(bs(ys, False{}, U32.is_eq(need, 1), need, pl,
          plen, pbf), cc, acc), afold(ys, aa, bb)), rr, xb <> r2, e_r))))

# the five header bytes bs writes at a block's start from left bytes
def hd5(+left: U32) -> List<&2, U32>:
  +len = Png.enc.cap(left)
  +nlen = (len .^. 65535 : U32)
  [Png.enc.bf(left), Png.enc.byte(len), Png.enc.hi(len), Png.enc.byte(nlen), Png.enc.hi(nlen)]

# a new block, split as enc.rgb.go writes it: the header, then the bytes with
# the block's whole length in hand, once whether that length is 1 is named
def spl.at(
  z1: Bool,
  +h: U32,
  +t: List<&2, U32>,
  +left: U32,
  +ez1: {U32.is_eq(Png.enc.cap(left), 1) == z1 : Bool},
  +nzc: {U32.is_zero(Png.enc.cap(left)) == False{} : Bool}
) -> {open.bs(h, t, (left - 1 : U32), Png.enc.cap(left), Png.enc.bf(left)) == List.append(&2, U32, hd5(left), bs(h <> t,
  False{}, U32.is_eq(Png.enc.cap(left), 1), Png.enc.cap(left), left, Png.enc.cap((left - 1 : U32)),
  Png.enc.bf((left - 1 : U32)))) : List<&2, U32>}:
  match z1:
    case True{}:
      +cp = Png.enc.cap(left)
      +l1 = (left - 1 : U32)
      +e1 = {one.val(cp, Equal.sym(Bool, U32.is_eq(cp, 1), True{}, ez1)) : {U32.to_nat(cp) == 1n : Nat}}
      +e0 = {u32.same((cp - 1 : U32), 0, Wp1.u32_pred(cp, 0n, e1)) : {(cp - 1 : U32) == 0 : U32}}
      %Equal.sym(Bool, U32.is_eq(cp, 1), True{}, ez1) : {open.bs(h, t, l1, cp, Png.enc.bf(left)) == List.append(&2, U32,
        hd5(left), bs(h <> t, False{}, _, cp, left, Png.enc.cap(l1), Png.enc.bf(l1))) : List<&2, U32>}
      Equal.cong(U32, List<&2, U32>, uu => List.append(&2, U32, hd5(left), h <> bs(t, U32.is_zero(uu), U32.is_eq(uu, 1),
        uu, l1, Png.enc.cap(l1), Png.enc.bf(l1))), (cp - 1 : U32), 0, e0)
    case False{}:
      +cp = Png.enc.cap(left)
      +l1 = (left - 1 : U32)
      +nz1 = {two(cp, Equal.sym(Bool, U32.is_zero(cp), False{}, nzc), Equal.sym(Bool, U32.is_eq(cp, 1), False{}, ez1)) :
        {U32.is_zero((cp - 1 : U32)) == False{} : Bool}}
      %Equal.sym(Bool, U32.is_eq(cp, 1), False{}, ez1) : {open.bs(h, t, l1, cp, Png.enc.bf(left)) == List.append(&2, U32,
        hd5(left), bs(h <> t, False{}, _, cp, left, Png.enc.cap(l1), Png.enc.bf(l1))) : List<&2, U32>}
      Equal.cong(Bool, List<&2, U32>, zb => List.append(&2, U32, hd5(left), h <> bs(t, zb, U32.is_eq((cp - 1 : U32), 1),
        (cp - 1 : U32), l1, Png.enc.cap(l1), Png.enc.bf(l1))), U32.is_zero((cp - 1 : U32)), False{}, nz1)

# a block's start with bytes left: the header, then the bytes with the block's
# whole length in hand
def spl(
  xs: List<&2, U32>,
  +left: U32,
  +hn: {U32.to_nat(left) == List.length(&2, U32, xs) : Nat},
  +nzl: {U32.is_zero(left) == False{} : Bool},
  +nzc: {U32.is_zero(Png.enc.cap(left)) == False{} : Bool}
) -> {bs(xs, True{}, False{}, 0, left, Png.enc.cap(left), Png.enc.bf(left)) == List.append(&2, U32, hd5(left), bs(xs,
  False{}, U32.is_eq(Png.enc.cap(left), 1), Png.enc.cap(left), left, Png.enc.cap((left - 1 : U32)),
  Png.enc.bf((left - 1 : U32)))) : List<&2, U32>}:
  match xs:
    case Nil{}:
      Empty.absurd({bs([], True{}, False{}, 0, left, Png.enc.cap(left), Png.enc.bf(left)) == List.append(&2, U32,
        hd5(left), bs([], False{}, U32.is_eq(Png.enc.cap(left), 1), Png.enc.cap(left), left, Png.enc.cap((left - 1 :
        U32)), Png.enc.bf((left - 1 : U32)))) : List<&2, U32>}, U32L.false_true(Equal.trans(Bool, False{},
        U32.is_zero(left), True{}, Equal.sym(Bool, U32.is_zero(left), False{}, nzl), zero.is(left, hn))))
    case +h <> +t:
      spl.at(U32.is_eq(Png.enc.cap(left), 1), h, t, left, {==}, nzc)

# the pair at.edge gives, used to rewrite bs's length and BFINAL
def n0.pe(
  +rr: List<&2, U32>,
  +pl: U32,
  +plen: U32,
  +pbf: U32,
  pe: {plen == Png.enc.cap(pl) : U32} & {pbf == Png.enc.bf(pl) : U32}
) -> {bs(rr, True{}, False{}, 0, pl, plen, pbf) == bs(rr, True{}, False{}, 0, pl, Png.enc.cap(pl), Png.enc.bf(pl)) :
  List<&2, U32>}:
  (+e_l, +e_b) = pe
  Equal.trans(List<&2, U32>, bs(rr, True{}, False{}, 0, pl, plen, pbf), bs(rr, True{}, False{}, 0, pl, Png.enc.cap(pl),
    pbf), bs(rr, True{}, False{}, 0, pl, Png.enc.cap(pl), Png.enc.bf(pl)), Equal.cong(U32, List<&2, U32>, uu => bs(rr,
    True{}, False{}, 0, pl, uu, pbf), plen, Png.enc.cap(pl), e_l), Equal.cong(U32, List<&2, U32>, uu => bs(rr, True{},
    False{}, 0, pl, Png.enc.cap(pl), uu), pbf, Png.enc.bf(pl), e_b))

# a block's end in enc.rgb.go's state is a block's start in bs's
def n0.bs(
  +rr: List<&2, U32>,
  +need: U32,
  +pl: U32,
  +plen: U32,
  +pbf: U32,
  +left2: U32,
  +ez: {True{} == U32.is_zero(need) : Bool},
  +e_pl: {U32.to_nat(pl) == List.length(&2, U32, rr) : Nat},
  +e_l2: {U32.to_nat(left2) == List.length(&2, U32, rr) : Nat},
  hb: at.edge(need, pl, plen, pbf)
) -> {bs(rr, U32.is_zero(need), U32.is_eq(need, 1), need, pl, plen, pbf) == bs(rr, True{}, False{}, 0, left2,
  Png.enc.cap(left2), Png.enc.bf(left2)) : List<&2, U32>}:
  +e0 = {u32.same(need, 0, zero.val(need, ez)) : {need == 0 : U32}}
  +e_p = {u32.same(pl, left2, Equal.trans(Nat, U32.to_nat(pl), List.length(&2, U32, rr), U32.to_nat(left2), e_pl,
    Equal.sym(Nat, U32.to_nat(left2), List.length(&2, U32, rr), e_l2))) : {pl == left2 : U32}}
  Equal.trans(List<&2, U32>, bs(rr, U32.is_zero(need), U32.is_eq(need, 1), need, pl, plen, pbf), bs(rr, True{}, False{},
    0, pl, plen, pbf), bs(rr, True{}, False{}, 0, left2, Png.enc.cap(left2), Png.enc.bf(left2)),
    Equal.cong(U32, List<&2, U32>, uu => bs(rr, U32.is_zero(uu), U32.is_eq(uu, 1), uu, pl, plen, pbf), need, 0, e0),
    Equal.trans(List<&2, U32>, bs(rr, True{}, False{}, 0, pl, plen, pbf), bs(rr, True{}, False{}, 0, pl, Png.enc.cap(pl),
      Png.enc.bf(pl)), bs(rr, True{}, False{}, 0, left2, Png.enc.cap(left2), Png.enc.bf(left2)), n0.pe(rr, pl, plen, pbf,
      hb(Equal.sym(Bool, True{}, U32.is_zero(need), ez))), Equal.cong(U32, List<&2, U32>, uu => bs(rr, True{}, False{},
      0, uu, Png.enc.cap(uu), Png.enc.bf(uu)), pl, left2, e_p)))

# out of fuel at a block's start: no raw bytes are left
def z0.m1(
  kk: Nat,
  +xn: Nat,
  +nr: Nat,
  +mn: Nat,
  +hx: {xn == nr : Nat},
  hk: kok(xn, kk, mn),
  +hw: {Nat.is_le(Nat.add(Nat.add(nr, 0n), Nat.double(kk)), 1n) == True{} : Bool}
) -> {nr == 0n : Nat}:
  match kk:
    case 0n:
      Equal.trans(Nat, nr, xn, 0n, Equal.sym(Nat, xn, nr, hx), hk)
    case 1n+kp:
      Empty.absurd({nr == 0n : Nat}, U32L.false_true(R.le_add_l(Nat.add(nr, 0n), 2n+Nat.double(kp), 1n, hw)))

# out of fuel inside a block: no raw bytes are left
def z0.s2(+nr: Nat, +dk: Nat, +hw: {Nat.is_le(Nat.add(Nat.add(nr, 1n), dk), 1n) == True{} : Bool}) -> {nr == 0n : Nat}:
  +h1 = {R.le_add_r(Nat.add(nr, 1n), dk, 1n, hw) : {Nat.is_le(Nat.add(nr, 1n), 1n) == True{} : Bool}}
  +h2 = {R.le_rw_l(Nat.add(nr, 1n), 1n+Nat.add(nr, 0n), 1n, R.add_succ(nr, 0n), h1) : {Nat.is_le(Nat.add(nr, 0n), 0n) ==
    True{} : Bool}}
  Equal.trans(Nat, nr, Nat.add(nr, 0n), 0n, Equal.sym(Nat, Nat.add(nr, 0n), nr, R.add_zero(nr)), le.zero(Nat.add(nr, 0n),
    h2))

# the fuel after a block header: one step fewer, one block fewer, one more to close it
def hw.head(
  +nr: Nat,
  +dk: Nat,
  +pp: Nat,
  +hw: {Nat.is_le(Nat.add(Nat.add(nr, 0n), 2n+dk), 2n+pp) == True{} : Bool}
) -> {Nat.is_le(Nat.add(Nat.add(nr, 1n), dk), 1n+pp) == True{} : Bool}:
  +ee = {Equal.trans(Nat, Nat.add(Nat.add(nr, 0n), 2n+dk), Nat.add(nr, 2n+dk), 1n+Nat.add(Nat.add(nr, 1n), dk),
    Equal.cong(Nat, Nat, kz => Nat.add(kz, 2n+dk), Nat.add(nr, 0n), nr, R.add_zero(nr)), Equal.trans(Nat, Nat.add(nr,
    2n+dk), 1n+Nat.add(nr, 1n+dk), 1n+Nat.add(Nat.add(nr, 1n), dk), R.add_succ(nr, 1n+dk), Equal.cong(Nat, Nat, kz =>
    1n+kz, Nat.add(nr, 1n+dk), Nat.add(Nat.add(nr, 1n), dk), Equal.sym(Nat, Nat.add(Nat.add(nr, 1n), dk), Nat.add(nr,
    1n+dk), R.add_assoc(nr, 1n, dk))))) : {Nat.add(Nat.add(nr, 0n), 2n+dk) == 1n+Nat.add(Nat.add(nr, 1n), dk) : Nat}}
  R.le_rw_l(Nat.add(Nat.add(nr, 0n), 2n+dk), 1n+Nat.add(Nat.add(nr, 1n), dk), 2n+pp, ee, hw)

# the fuel at a block's end: the step that closes it
def hw.end(
  +nr: Nat,
  +dk: Nat,
  +pp: Nat,
  +hw: {Nat.is_le(Nat.add(Nat.add(nr, 1n), dk), 2n+pp) == True{} : Bool}
) -> {Nat.is_le(Nat.add(Nat.add(nr, 0n), dk), 1n+pp) == True{} : Bool}:
  R.le_rw_l(Nat.add(Nat.add(nr, 1n), dk), 1n+Nat.add(Nat.add(nr, 0n), dk), 2n+pp, Equal.cong(Nat, Nat, kz => Nat.add(kz,
    dk), Nat.add(nr, 1n), 1n+Nat.add(nr, 0n), R.add_succ(nr, 0n)), hw)

# a sum that is 0 has a left part 0
def add.zero.l(aa: Nat, +bb: Nat, +hh: {Nat.add(aa, bb) == 0n : Nat}) -> {aa == 0n : Nat}:
  match aa:
    case 0n:
      {==}
    case 1n+pp:
      Empty.absurd({1n+pp == 0n : Nat}, Wp1.zero_succ(Nat.add(pp, bb), Equal.sym(Nat, 1n+Nat.add(pp, bb), 0n, hh)))

# a byte is due in the block, so the raw bytes are not gone
def need.nil(
  +need: U32,
  +xn: Nat,
  +e_zn: {False{} == U32.is_zero(need) : Bool},
  +hx: {Nat.add(U32.to_nat(need), xn) == 0n : Nat}
) -> Empty:
  U32L.false_true(Equal.trans(Bool, False{}, U32.is_zero(need), True{}, e_zn, zero.is(need, add.zero.l(U32.to_nat(need),
    xn, hx))))

# the filter byte: 0, then the row's samples
def cur.filt(
  +s: U32,
  +t: List<&2, U32>,
  +row: U32,
  +wp: Nat,
  +er: {U32.to_nat(row) == 1n+wp : Nat}
) -> {W9.sc(s <> t, 0n, 1n+wp, True{}) == 0 <> W9.sc(s <> t, U32.to_nat(row), 1n+wp, True{}) : List<&2, U32>}:
  Equal.cong(Nat, List<&2, U32>, kz => 0 <> W9.sc(s <> t, kz, 1n+wp, True{}), 1n+wp, U32.to_nat(row), Equal.sym(Nat,
    U32.to_nat(row), 1n+wp, er))

# a red byte: the sample's red, then its green and blue and the rest of the row
def cur.red(
  +s: U32,
  +t: List<&2, U32>,
  +row: U32,
  +wn: Nat,
  +hrow: {U32.is_zero(row) == False{} : Bool}
) -> {W9.sc(s <> t, U32.to_nat(row), wn, True{}) == Png.enc.r(s) <> Png.enc.g(s) <> Png.enc.b(s) <> W9.sc(t,
  Png.enc.pred(U32.to_nat(row)), wn, True{}) : List<&2, U32>}:
  +r1 = U32.to_nat((row - 1 : U32))
  +er = {Wp1.u32_dec(row, hrow) : {U32.to_nat(row) == 1n+r1 : Nat}}
  Equal.trans(List<&2, U32>, W9.sc(s <> t, U32.to_nat(row), wn, True{}), W9.sc(s <> t, 1n+r1, wn, True{}), Png.enc.r(s)
    <> Png.enc.g(s) <> Png.enc.b(s) <> W9.sc(t, Png.enc.pred(U32.to_nat(row)), wn, True{}),
    Equal.cong(Nat, List<&2, U32>, kz => W9.sc(s <> t, kz, wn, True{}), U32.to_nat(row), 1n+r1, er),
    Equal.cong(Nat, List<&2, U32>, kz => Png.enc.r(s) <> Png.enc.g(s) <> Png.enc.b(s) <> W9.sc(t, Png.enc.pred(kz), wn,
      True{}), 1n+r1, U32.to_nat(row), Equal.sym(Nat, U32.to_nat(row), 1n+r1, er)))

# a row's last blue byte: the next row starts with its filter byte
def cur.last(
  +col: U32,
  +px: List<&2, U32>,
  +row: U32,
  +wn: Nat,
  +e1: {True{} == U32.is_eq(row, 1) : Bool}
) -> {Png.enc.b(col) <> W9.sc(px, Png.enc.pred(U32.to_nat(row)), wn, True{}) == Png.enc.b(col) <> W9.sc(px, 0n, wn,
  True{}) : List<&2, U32>}:
  Equal.cong(Nat, List<&2, U32>, kz => Png.enc.b(col) <> W9.sc(px, Png.enc.pred(kz), wn, True{}), U32.to_nat(row), 1n,
    one.val(row, e1))

# a blue byte inside a row: the next sample's red comes next
def cur.blue(
  +col: U32,
  +px: List<&2, U32>,
  +row: U32,
  +wn: Nat,
  +hrow: {U32.is_zero(row) == False{} : Bool}
) -> {Png.enc.b(col) <> W9.sc(px, Png.enc.pred(U32.to_nat(row)), wn, True{}) == Png.enc.b(col) <> W9.sc(px,
  U32.to_nat((row - 1 : U32)), wn, True{}) : List<&2, U32>}:
  Equal.cong(Nat, List<&2, U32>, kz => Png.enc.b(col) <> W9.sc(px, Png.enc.pred(kz), wn, True{}), U32.to_nat(row),
    1n+U32.to_nat((row - 1 : U32)), Wp1.u32_dec(row, hrow))

# enc.rgb.go writes bs's blocks of the raw bytes its cursor walks, with their
# CRC run, and the Adler-32 of those bytes, while its fuel covers a step per
# raw byte and two per block (the header, and the step that closes it)
def rg(
  fuel: Nat,
  +zblock: Bool,
  +zdone: Bool,
  +zspan: Bool,
  +zneed: Bool,
  +filt: Bool,
  +zred: Bool,
  +zgrn: Bool,
  +zlast: Bool,
  +px: List<&2, U32>,
  +col: U32,
  +row: U32,
  +ww: U32,
  +need: U32,
  +cc: U32,
  +acc: List<&2, U32>,
  +aa: U32,
  +bb: U32,
  +left: U32,
  +len: U32,
  +pl: U32,
  +plen: U32,
  +pbf: U32,
  +kk: Nat,
  +xn: Nat,
  +wp: Nat,
  +mx: U32,
  +emx: {mx == 65535 : U32},
  +ew: {U32.to_nat(ww) == 1n+wp : Nat},
  +hrow: {U32.is_zero(row) == False{} : Bool},
  hfw: {filt == True{} : Bool} -> {row == ww : U32},
  hbl: {filt == False{} : Bool} -> {zred == False{} : Bool} -> {zgrn == False{} : Bool} -> {zlast == U32.is_eq(row, 1) :
    Bool},
  +hx: {Nat.add(U32.to_nat(rm(zblock, need)), xn) == List.length(&2, U32, cur(filt, zred, zgrn, px, col, row, 1n+wp)) :
    Nat},
  hk: kok(xn, kk, U32.to_nat(mx)),
  +hw: {Nat.is_le(Nat.add(Nat.add(List.length(&2, U32, cur(filt, zred, zgrn, px, col, row, 1n+wp)),
    R.bit(Bool.not(zblock))), Nat.double(kk)), 1n+fuel) == True{} : Bool},
  hb: rg.hyp(zblock, zdone, zspan, zneed, List.length(&2, U32, cur(filt, zred, zgrn, px, col, row, 1n+wp)), left, len,
    need, pl, plen, pbf)
) -> {Png.enc.rgb.go(fuel, zblock, zdone, zspan, zneed, filt, zred, zgrn, zlast, px, col, row, ww, need, cc, acc, aa, bb,
  left, len) == rg.val(zblock, cur(filt, zred, zgrn, px, col, row, 1n+wp), cc, acc, aa, bb, left, need, pl, plen, pbf) :
  (U32 & List<&2, U32>) & U32}:
  match fuel:
    case 0n:
      match zblock:
        case True{}:
          +rr = cur(filt, zred, zgrn, px, col, row, 1n+wp)
          nil.r(rr, True{}, False{}, 0, left, Png.enc.cap(left), Png.enc.bf(left), cc, acc, aa, bb, z0.m1(kk, xn,
            List.length(&2, U32, rr), U32.to_nat(mx), hx, hk, hw))
        case False{}:
          +rr = cur(filt, zred, zgrn, px, col, row, 1n+wp)
          nil.r(rr, U32.is_zero(need), U32.is_eq(need, 1), need, pl, plen, pbf, cc, acc, aa, bb,
            z0.s2(List.length(&2, U32, rr), Nat.double(kk), hw))
    case 1n+(+pp):
      match zblock:
        case True{}:
          match zdone:
            case True{}:
              (e_zd, e_l) = hb
              +rr = cur(filt, zred, zgrn, px, col, row, 1n+wp)
              nil.r(rr, True{}, False{}, 0, left, Png.enc.cap(left), Png.enc.bf(left), cc, acc, aa, bb,
                Equal.trans(Nat, List.length(&2, U32, rr), U32.to_nat(left), 0n, Equal.sym(Nat, U32.to_nat(left),
                List.length(&2, U32, rr), e_l), zero.val(left, e_zd)))
            case False{}:
              match kk:
                case 0n:
                  (e_zd, e_l) = hb
                  +rr = cur(filt, zred, zgrn, px, col, row, 1n+wp)
                  +e_r0 = {Equal.trans(Nat, U32.to_nat(left), List.length(&2, U32, rr), 0n, e_l, Equal.trans(Nat,
                    List.length(&2, U32, rr), xn, 0n, Equal.sym(Nat, xn, List.length(&2, U32, rr), hx), hk)) :
                    {U32.to_nat(left) == 0n : Nat}}
                  Empty.absurd({Png.enc.rgb.go(1n+pp, True{}, False{}, zspan, zneed, filt, zred, zgrn, zlast, px, col,
                    row, ww, need, cc, acc, aa, bb, left, len) == rg.val(True{}, rr, cc, acc, aa, bb, left, need, pl,
                    plen, pbf) : (U32 & List<&2, U32>) & U32}, U32L.false_true(Equal.trans(Bool, False{},
                    U32.is_zero(left), True{}, e_zd, zero.is(left, e_r0))))
                case 1n+(+kp):
                  match hk hb:
                    case Tuple{h_lt, h_le} Tuple{e_zd, +e_l}:
                      +rr = cur(filt, zred, zgrn, px, col, row, 1n+wp)
                      +nr = List.length(&2, U32, rr)
                      +mn = U32.to_nat(mx)
                      +l1 = (left - 1 : U32)
                      +nt = U32.to_nat(l1)
                      +nzl = {Equal.sym(Bool, False{}, U32.is_zero(left), e_zd) : {U32.is_zero(left) == False{} : Bool}}
                      +e_lt = {Wp1.u32_dec(left, nzl) : {U32.to_nat(left) == 1n+nt : Nat}}
                      +e_R = {Equal.trans(Nat, nr, U32.to_nat(left), 1n+nt, Equal.sym(Nat, U32.to_nat(left), nr, e_l),
                        e_lt) : {nr == 1n+nt : Nat}}
                      +zz = U32.is_le(left, 65535)
                      +cp = Png.enc.cap(left)
                      +cm = capm(zz, left, mx)
                      +c1 = (cp - 1 : U32)
                      +nzm = {mx.nz(mx, emx) : {U32.is_zero(mx) == False{} : Bool}}
                      +ezm = {le.mx(left, mx, emx) : {U32.is_le(left, mx) == zz : Bool}}
                      +e_cm = {cap.m(zz, left, mx, emx) : {cp == cm : U32}}
                      +nz_cp = {Equal.trans(Bool, U32.is_zero(cp), U32.is_zero(cm), False{}, Equal.cong(U32, Bool, uu =>
                        U32.is_zero(uu), cp, cm, e_cm), cap.nz(zz, left, mx, nt, nzm, e_lt)) : {U32.is_zero(cp) ==
                        False{} : Bool}}
                      +e_cp = {Wp1.u32_dec(cp, nz_cp) : {U32.to_nat(cp) == 1n+U32.to_nat(c1) : Nat}}
                      +e_c = {Equal.cong(U32, Nat, uu => U32.to_nat((uu - 1 : U32)), cp, cm, e_cm) : {U32.to_nat(c1) ==
                        U32.to_nat((cm - 1 : U32)) : Nat}}
                      +h_c = {R.le_rw_l(U32.to_nat((cm - 1 : U32)), U32.to_nat(c1), nt, Equal.sym(Nat, U32.to_nat(c1),
                        U32.to_nat((cm - 1 : U32)), e_c), ks.le(zz, left, mx, nt, nzm, ezm, e_lt)) :
                        {Nat.is_le(U32.to_nat(c1), nt) == True{} : Bool}}
                      +x2 = Nat.sub(nt, U32.to_nat(c1))
                      +hx2 = {Equal.trans(Nat, Nat.add(U32.to_nat(cp), x2), 1n+Nat.add(U32.to_nat(c1), x2), nr,
                        Equal.cong(Nat, Nat, kz => Nat.add(kz, x2), U32.to_nat(cp), 1n+U32.to_nat(c1), e_cp),
                        Equal.trans(Nat, 1n+Nat.add(U32.to_nat(c1), x2), 1n+nt, nr, Equal.cong(Nat, Nat, kz => 1n+kz,
                        Nat.add(U32.to_nat(c1), x2), nt, R.add_sub(U32.to_nat(c1), nt, h_c)), Equal.sym(Nat, nr, 1n+nt,
                        e_R))) : {Nat.add(U32.to_nat(cp), x2) == nr : Nat}}
                      +h_lt2 = {R.lt_rw_r(Nat.mul(kp, mn), xn, 1n+nt, Equal.trans(Nat, xn, nr, 1n+nt, hx, e_R), h_lt) :
                        {Nat.is_lt(Nat.mul(kp, mn), 1n+nt) == True{} : Bool}}
                      +h_le2 = {R.le_rw_l(xn, 1n+nt, Nat.add(mn, Nat.mul(kp, mn)), Equal.trans(Nat, xn, nr, 1n+nt, hx, e_R),
                        h_le) : {Nat.is_le(1n+nt, Nat.add(mn, Nat.mul(kp, mn))) == True{} : Bool}}
                      hk2 = kok.rw(Nat.sub(nt, U32.to_nat((cm - 1 : U32))), x2, kp, mn, Equal.cong(Nat, Nat, kz =>
                        Nat.sub(nt, kz), U32.to_nat((cm - 1 : U32)), U32.to_nat(c1), Equal.sym(Nat, U32.to_nat(c1),
                        U32.to_nat((cm - 1 : U32)), e_c)), ks.k(zz, kp, left, mx, nt, nzm, ezm, e_lt, h_lt2, h_le2))
                      +hw2 = {hw.head(nr, Nat.double(kp), pp, hw) : {Nat.is_le(Nat.add(Nat.add(nr, 1n), Nat.double(kp)),
                        1n+pp) == True{} : Bool}}
                      +ell2 = {Equal.trans(Nat, Nat.add(U32.to_nat(cp), nr), Nat.add(nr, U32.to_nat(cp)),
                        Nat.add(U32.to_nat(left), U32.to_nat(cp)), R.add_comm(U32.to_nat(cp), nr), Equal.cong(Nat, Nat,
                        kz => Nat.add(kz, U32.to_nat(cp)), nr, U32.to_nat(left), Equal.sym(Nat, U32.to_nat(left), nr,
                        e_l))) : {Nat.add(U32.to_nat(cp), nr) == Nat.add(U32.to_nat(left), U32.to_nat(cp)) : Nat}}
                      +bf = Png.enc.bf(left)
                      +nlen = (cp .^. 65535 : U32)
                      +b1 = Png.enc.byte(cp)
                      +b2 = Png.enc.hi(cp)
                      +b3 = Png.enc.byte(nlen)
                      +b4 = Png.enc.hi(nlen)
                      +c5 = Crc.crc.byte(Crc.crc.byte(Crc.crc.byte(Crc.crc.byte(Crc.crc.byte(cc, bf), b1), b2), b3), b4)
                      +a4 = {b4 <> b3 <> b2 <> b1 <> bf <> acc : List<&2, U32>}
                      +bb2 = bs(rr, False{}, U32.is_eq(cp, 1), cp, left, Png.enc.cap(l1), Png.enc.bf(l1))
                      +ih = {rg(pp, False{}, False{}, True{}, False{}, filt, zred, zgrn, zlast, px, col, row, ww, cp, c5, a4,
                        aa, bb, left, cp, left, Png.enc.cap(l1), Png.enc.bf(l1), kp, x2, wp, mx, emx, ew, hrow, hfw, hbl,
                        hx2, hk2, hw2, ({==}, ({==}, (Equal.sym(Bool, U32.is_zero(cp), False{}, nz_cp), (e_l, (ell2,
                        edge.no(cp, left, Png.enc.cap(l1), Png.enc.bf(l1), nz_cp))))))) : {Png.enc.rgb.go(pp, False{},
                        False{}, True{}, False{}, filt, zred, zgrn, zlast, px, col, row, ww, cp, c5, a4, aa, bb, left, cp)
                        == (fr(bs(rr, U32.is_zero(cp), U32.is_eq(cp, 1), cp, left, Png.enc.cap(l1), Png.enc.bf(l1)), c5,
                        a4), afold(rr, aa, bb)) : (U32 & List<&2, U32>) & U32}}
                      Equal.trans((U32 & List<&2, U32>) & U32, Png.enc.rgb.go(pp, False{}, False{}, True{}, False{}, filt,
                        zred, zgrn, zlast, px, col, row, ww, cp, c5, a4, aa, bb, left, cp), (fr(bb2, c5, a4), afold(rr, aa,
                        bb)), rg.val(True{}, rr, cc, acc, aa, bb, left, need, pl, plen, pbf),
                        Equal.trans((U32 & List<&2, U32>) & U32, Png.enc.rgb.go(pp, False{}, False{}, True{}, False{}, filt,
                          zred, zgrn, zlast, px, col, row, ww, cp, c5, a4, aa, bb, left, cp), (fr(bs(rr, U32.is_zero(cp),
                          U32.is_eq(cp, 1), cp, left, Png.enc.cap(l1), Png.enc.bf(l1)), c5, a4), afold(rr, aa, bb)),
                          (fr(bb2, c5, a4), afold(rr, aa, bb)), ih, Equal.cong(Bool, (U32 & List<&2, U32>) & U32, zb =>
                          (fr(bs(rr, zb, U32.is_eq(cp, 1), cp, left, Png.enc.cap(l1), Png.enc.bf(l1)), c5, a4), afold(rr,
                          aa, bb)), U32.is_zero(cp), False{}, nz_cp)),
                        Equal.sym((U32 & List<&2, U32>) & U32, rg.val(True{}, rr, cc, acc, aa, bb, left, need, pl, plen,
                          pbf), (fr(bb2, c5, a4), afold(rr, aa, bb)), Equal.trans((U32 & List<&2, U32>) & U32,
                          rg.val(True{}, rr, cc, acc, aa, bb, left, need, pl, plen, pbf), (fr(List.append(&2, U32,
                          hd5(left), bb2), cc, acc), afold(rr, aa, bb)), (fr(bb2, c5, a4), afold(rr, aa, bb)),
                          Equal.cong(List<&2, U32>, (U32 & List<&2, U32>) & U32, ys => (fr(ys, cc, acc), afold(rr, aa, bb)),
                          bs(rr, True{}, False{}, 0, left, cp, bf), List.append(&2, U32, hd5(left), bb2), spl(rr, left,
                          e_l, nzl, nz_cp)), Equal.cong(U32 & List<&2, U32>, (U32 & List<&2, U32>) & U32, qq => (qq,
                          afold(rr, aa, bb)), fr(List.append(&2, U32, hd5(left), bb2), cc, acc), fr(bb2, c5, a4),
                          Equal.sym(U32 & List<&2, U32>, fr(bb2, c5, a4), fr(List.append(&2, U32, hd5(left), bb2), cc,
                          acc), fr.app(hd5(left), bb2, cc, acc))))))
        case False{}:
          match zdone:
            case True{}:
              (e_d, _rest) = hb
              Empty.absurd({Png.enc.rgb.go(1n+pp, False{}, True{}, zspan, zneed, filt, zred, zgrn, zlast, px, col, row,
                ww, need, cc, acc, aa, bb, left, len) == rg.val(False{}, cur(filt, zred, zgrn, px, col, row, 1n+wp), cc,
                acc, aa, bb, left, need, pl, plen, pbf) : (U32 & List<&2, U32>) & U32}, U32L.false_true(Equal.sym(Bool,
                True{}, False{}, e_d)))
            case False{}:
              match zspan:
                case False{}:
                  (_e_d, (e_s, _rest)) = hb
                  Empty.absurd({Png.enc.rgb.go(1n+pp, False{}, False{}, False{}, zneed, filt, zred, zgrn, zlast, px,
                    col, row, ww, need, cc, acc, aa, bb, left, len) == rg.val(False{}, cur(filt, zred, zgrn, px, col,
                    row, 1n+wp), cc, acc, aa, bb, left, need, pl, plen, pbf) : (U32 & List<&2, U32>) & U32},
                    U32L.false_true(e_s))
                case True{}:
                  match zneed:
                    case True{}:
                      (_e_d, (_e_s, (+e_zn, (+e_pl, (+e_ll, hbe))))) = hb
                      +rr = cur(filt, zred, zgrn, px, col, row, 1n+wp)
                      +nr = List.length(&2, U32, rr)
                      +l2 = (left - len : U32)
                      +e_n0 = {zero.val(need, e_zn) : {U32.to_nat(need) == 0n : Nat}}
                      +e_lf = {Equal.trans(Nat, U32.to_nat(left), Nat.add(U32.to_nat(left), 0n), Nat.add(U32.to_nat(len),
                        nr), Equal.sym(Nat, Nat.add(U32.to_nat(left), 0n), U32.to_nat(left),
                        R.add_zero(U32.to_nat(left))), Equal.trans(Nat, Nat.add(U32.to_nat(left), 0n),
                        Nat.add(U32.to_nat(left), U32.to_nat(need)), Nat.add(U32.to_nat(len), nr), Equal.cong(Nat, Nat,
                        kz => Nat.add(U32.to_nat(left), kz), 0n, U32.to_nat(need), Equal.sym(Nat, U32.to_nat(need), 0n,
                        e_n0)), Equal.sym(Nat, Nat.add(U32.to_nat(len), nr), Nat.add(U32.to_nat(left),
                        U32.to_nat(need)), e_ll))) : {U32.to_nat(left) == Nat.add(U32.to_nat(len), nr) : Nat}}
                      +h_ll = {R.le_rw_r(U32.to_nat(len), Nat.add(U32.to_nat(len), nr), U32.to_nat(left), Equal.sym(Nat,
                        U32.to_nat(left), Nat.add(U32.to_nat(len), nr), e_lf), Wp2.nle_add(U32.to_nat(len), nr)) :
                        {Nat.is_le(U32.to_nat(len), U32.to_nat(left)) == True{} : Bool}}
                      +e_l2 = {Equal.trans(Nat, U32.to_nat(l2), Nat.sub(U32.to_nat(left), U32.to_nat(len)), nr,
                        R.u32_sub_nat(left, len, h_ll), Equal.trans(Nat, Nat.sub(U32.to_nat(left), U32.to_nat(len)),
                        Nat.sub(Nat.add(U32.to_nat(len), nr), U32.to_nat(len)), nr, Equal.cong(Nat, Nat, kz =>
                        Nat.sub(kz, U32.to_nat(len)), U32.to_nat(left), Nat.add(U32.to_nat(len), nr), e_lf),
                        R.sub_add_cancel(U32.to_nat(len), nr))) : {U32.to_nat(l2) == nr : Nat}}
                      +hx2 = {Equal.trans(Nat, xn, Nat.add(U32.to_nat(need), xn), nr, Equal.cong(Nat, Nat, kz =>
                        Nat.add(kz, xn), 0n, U32.to_nat(need), Equal.sym(Nat, U32.to_nat(need), 0n, e_n0)), hx) :
                        {Nat.add(U32.to_nat(0), xn) == nr : Nat}}
                      +ih = {rg(pp, True{}, U32.is_zero(l2), False{}, False{}, filt, zred, zgrn, zlast, px, col, row, ww,
                        need, cc, acc, aa, bb, l2, len, pl, plen, pbf, kk, xn, wp, mx, emx, ew, hrow, hfw, hbl, hx2, hk,
                        hw.end(nr, Nat.double(kk), pp, hw), ({==}, e_l2)) : {Png.enc.rgb.go(pp, True{},
                        U32.is_zero(l2), False{}, False{}, filt, zred, zgrn, zlast, px, col, row, ww, need, cc, acc, aa,
                        bb, l2, len) == (fr(bs(rr, True{}, False{}, 0, l2, Png.enc.cap(l2), Png.enc.bf(l2)), cc, acc),
                        afold(rr, aa, bb)) : (U32 & List<&2, U32>) & U32}}
                      Equal.trans((U32 & List<&2, U32>) & U32, Png.enc.rgb.go(pp, True{}, U32.is_zero(l2), False{},
                        False{}, filt, zred, zgrn, zlast, px, col, row, ww, need, cc, acc, aa, bb, l2, len),
                        (fr(bs(rr, True{}, False{}, 0, l2, Png.enc.cap(l2), Png.enc.bf(l2)), cc, acc), afold(rr, aa,
                        bb)), rg.val(False{}, rr, cc, acc, aa, bb, left, need, pl, plen, pbf), ih,
                        Equal.cong(List<&2, U32>, (U32 & List<&2, U32>) & U32, ys => (fr(ys, cc, acc), afold(rr, aa,
                        bb)), bs(rr, True{}, False{}, 0, l2, Png.enc.cap(l2), Png.enc.bf(l2)), bs(rr,
                        U32.is_zero(need), U32.is_eq(need, 1), need, pl, plen, pbf), Equal.sym(List<&2, U32>, bs(rr,
                        U32.is_zero(need), U32.is_eq(need, 1), need, pl, plen, pbf), bs(rr, True{}, False{}, 0, l2,
                        Png.enc.cap(l2), Png.enc.bf(l2)), n0.bs(rr, need, pl, plen, pbf, l2, e_zn, e_pl, e_l2, hbe))))
                      case False{}:
                        match filt:
                          case True{}:
                            match px:
                              case Nil{}:
                                (_e_d, (_e_s, (e_zn, _rest))) = hb
                                Empty.absurd({Png.enc.rgb.go(1n+pp, False{}, False{}, True{}, False{}, True{}, zred, zgrn, zlast, [], col, row, ww, need, cc, acc, aa, bb, left, len) == rg.val(False{}, cur(True{}, zred, zgrn, [], col, row, 1n+wp), cc, acc, aa, bb, left, need, pl, plen, pbf) : (U32 & List<&2, U32>) & U32}, need.nil(need, xn, e_zn, hx))
                              case +s <> +t:
                                (_e_d, (_e_s, (+e_zn, (+e_pl, (+e_ll, _hbe))))) = hb
                                +r2 = cur(False{}, True{}, False{}, s <> t, col, row, 1n+wp)
                                +e_R = {cur.filt(s, t, row, wp, Equal.trans(Nat, U32.to_nat(row), U32.to_nat(ww), 1n+wp, Equal.cong(U32, Nat, uu => U32.to_nat(uu), row, ww, hfw({==})), ew)) : {cur(True{}, zred, zgrn, s <> t, col, row, 1n+wp) == 0 <> r2 : List<&2, U32>}}
                                rg.byte(pp, 0, cur(True{}, zred, zgrn, s <> t, col, row, 1n+wp), r2, need, pl, plen, pbf, cc, acc, aa, bb, left, len, kk, xn, Png.enc.rgb.go(pp, False{}, False{}, True{}, U32.is_zero((need - 1 : U32)), False{}, True{}, False{}, False{}, s <> t, col, row, ww, (need - 1 : U32), Crc.crc.byte(cc, 0), 0 <> acc, Png.enc.add(aa, 0), Png.enc.add(bb, Png.enc.add(aa, 0)), left, len), e_R, e_zn, hx, hw, e_pl, e_ll, xx => yy => h1 => h2 => h3 => h4 => h5 => rg(pp, False{}, False{}, True{}, U32.is_zero((need - 1 : U32)), False{}, True{}, False{}, False{}, s <> t, col, row, ww, (need - 1 : U32), Crc.crc.byte(cc, 0), 0 <> acc, Png.enc.add(aa, 0), Png.enc.add(bb, Png.enc.add(aa, 0)), left, len, (pl - 1 : U32), xx, yy, kk, xn, wp, mx, emx, ew, hrow, ef => Empty.absurd({row == ww : U32}, U32L.false_true(ef)), _e1 => e2 => _e3 => Empty.absurd({False{} == U32.is_eq(row, 1) : Bool}, U32L.false_true(Equal.sym(Bool, True{}, False{}, e2))), h2, hk, h3, ({==}, ({==}, ({==}, (h4, (h5, h1)))))))
                          case False{}:
                            match zred:
                              case True{}:
                                match zgrn:
                                  case _gn:
                                    match zlast:
                                      case _ls:
                                        match px:
                                          case Nil{}:
                                            (_e_d, (_e_s, (e_zn, _rest))) = hb
                                            Empty.absurd({Png.enc.rgb.go(1n+pp, False{}, False{}, True{}, False{}, False{}, True{}, _gn, _ls, [], col, row, ww, need, cc, acc, aa, bb, left, len) == rg.val(False{}, cur(False{}, True{}, _gn, [], col, row, 1n+wp), cc, acc, aa, bb, left, need, pl, plen, pbf) : (U32 & List<&2, U32>) & U32}, need.nil(need, xn, e_zn, hx))
                                          case +s <> +t:
                                            (_e_d, (_e_s, (+e_zn, (+e_pl, (+e_ll, _hbe))))) = hb
                                            +r2 = cur(False{}, False{}, True{}, t, s, row, 1n+wp)
                                            +e_R = {cur.red(s, t, row, 1n+wp, hrow) : {cur(False{}, True{}, _gn, s <> t, col, row, 1n+wp) == Png.enc.r(s) <> r2 : List<&2, U32>}}
                                            rg.byte(pp, Png.enc.r(s), cur(False{}, True{}, _gn, s <> t, col, row, 1n+wp), r2, need, pl, plen, pbf, cc, acc, aa, bb, left, len, kk, xn, Png.enc.rgb.go(pp, False{}, False{}, True{}, U32.is_zero((need - 1 : U32)), False{}, False{}, True{}, False{}, t, s, row, ww, (need - 1 : U32), Crc.crc.byte(cc, Png.enc.r(s)), Png.enc.r(s) <> acc, Png.enc.add(aa, Png.enc.r(s)), Png.enc.add(bb, Png.enc.add(aa, Png.enc.r(s))), left, len), e_R, e_zn, hx, hw, e_pl, e_ll, xx => yy => h1 => h2 => h3 => h4 => h5 => rg(pp, False{}, False{}, True{}, U32.is_zero((need - 1 : U32)), False{}, False{}, True{}, False{}, t, s, row, ww, (need - 1 : U32), Crc.crc.byte(cc, Png.enc.r(s)), Png.enc.r(s) <> acc, Png.enc.add(aa, Png.enc.r(s)), Png.enc.add(bb, Png.enc.add(aa, Png.enc.r(s))), left, len, (pl - 1 : U32), xx, yy, kk, xn, wp, mx, emx, ew, hrow, ef => Empty.absurd({row == ww : U32}, U32L.false_true(ef)), _e1 => _e2 => e3 => Empty.absurd({False{} == U32.is_eq(row, 1) : Bool}, U32L.false_true(Equal.sym(Bool, True{}, False{}, e3))), h2, hk, h3, ({==}, ({==}, ({==}, (h4, (h5, h1)))))))
                              case False{}:
                                match zgrn:
                                  case True{}:
                                    (_e_d, (_e_s, (+e_zn, (+e_pl, (+e_ll, _hbe))))) = hb
                                    +r2 = cur(False{}, False{}, False{}, px, col, row, 1n+wp)
                                    +e_R = {{==} : {cur(False{}, False{}, True{}, px, col, row, 1n+wp) == Png.enc.g(col) <> r2 : List<&2, U32>}}
                                    rg.byte(pp, Png.enc.g(col), cur(False{}, False{}, True{}, px, col, row, 1n+wp), r2, need, pl, plen, pbf, cc, acc, aa, bb, left, len, kk, xn, Png.enc.rgb.go(pp, False{}, False{}, True{}, U32.is_zero((need - 1 : U32)), False{}, False{}, False{}, U32.is_eq(row, 1), px, col, row, ww, (need - 1 : U32), Crc.crc.byte(cc, Png.enc.g(col)), Png.enc.g(col) <> acc, Png.enc.add(aa, Png.enc.g(col)), Png.enc.add(bb, Png.enc.add(aa, Png.enc.g(col))), left, len), e_R, e_zn, hx, hw, e_pl, e_ll, xx => yy => h1 => h2 => h3 => h4 => h5 => rg(pp, False{}, False{}, True{}, U32.is_zero((need - 1 : U32)), False{}, False{}, False{}, U32.is_eq(row, 1), px, col, row, ww, (need - 1 : U32), Crc.crc.byte(cc, Png.enc.g(col)), Png.enc.g(col) <> acc, Png.enc.add(aa, Png.enc.g(col)), Png.enc.add(bb, Png.enc.add(aa, Png.enc.g(col))), left, len, (pl - 1 : U32), xx, yy, kk, xn, wp, mx, emx, ew, hrow, ef => Empty.absurd({row == ww : U32}, U32L.false_true(ef)), _e1 => _e2 => _e3 => {==}, h2, hk, h3, ({==}, ({==}, ({==}, (h4, (h5, h1)))))))
                                  case False{}:
                                    match zlast:
                                      case True{}:
                                        (_e_d, (_e_s, (+e_zn, (+e_pl, (+e_ll, _hbe))))) = hb
                                        +r2 = cur(True{}, True{}, False{}, px, col, ww, 1n+wp)
                                        +e_R = {cur.last(col, px, row, 1n+wp, hbl({==}, {==}, {==})) : {cur(False{}, False{}, False{}, px, col, row, 1n+wp) == Png.enc.b(col) <> r2 : List<&2, U32>}}
                                        rg.byte(pp, Png.enc.b(col), cur(False{}, False{}, False{}, px, col, row, 1n+wp), r2, need, pl, plen, pbf, cc, acc, aa, bb, left, len, kk, xn, Png.enc.rgb.go(pp, False{}, False{}, True{}, U32.is_zero((need - 1 : U32)), True{}, True{}, False{}, False{}, px, col, ww, ww, (need - 1 : U32), Crc.crc.byte(cc, Png.enc.b(col)), Png.enc.b(col) <> acc, Png.enc.add(aa, Png.enc.b(col)), Png.enc.add(bb, Png.enc.add(aa, Png.enc.b(col))), left, len), e_R, e_zn, hx, hw, e_pl, e_ll, xx => yy => h1 => h2 => h3 => h4 => h5 => rg(pp, False{}, False{}, True{}, U32.is_zero((need - 1 : U32)), True{}, True{}, False{}, False{}, px, col, ww, ww, (need - 1 : U32), Crc.crc.byte(cc, Png.enc.b(col)), Png.enc.b(col) <> acc, Png.enc.add(aa, Png.enc.b(col)), Png.enc.add(bb, Png.enc.add(aa, Png.enc.b(col))), left, len, (pl - 1 : U32), xx, yy, kk, xn, wp, mx, emx, ew, Wp1.u32_nonzero(ww, wp, ew), _ef => {==}, ef => Empty.absurd({True{} == False{} : Bool} -> {False{} == False{} : Bool} -> {False{} == U32.is_eq(ww, 1) : Bool}, U32L.false_true(Equal.sym(Bool, True{}, False{}, ef))), h2, hk, h3, ({==}, ({==}, ({==}, (h4, (h5, h1)))))))
                                      case False{}:
                                        (_e_d, (_e_s, (+e_zn, (+e_pl, (+e_ll, _hbe))))) = hb
                                        +r2 = cur(False{}, True{}, False{}, px, col, (row - 1 : U32), 1n+wp)
                                        +e_R = {cur.blue(col, px, row, 1n+wp, hrow) : {cur(False{}, False{}, False{}, px, col, row, 1n+wp) == Png.enc.b(col) <> r2 : List<&2, U32>}}
                                        rg.byte(pp, Png.enc.b(col), cur(False{}, False{}, False{}, px, col, row, 1n+wp), r2, need, pl, plen, pbf, cc, acc, aa, bb, left, len, kk, xn, Png.enc.rgb.go(pp, False{}, False{}, True{}, U32.is_zero((need - 1 : U32)), False{}, True{}, False{}, False{}, px, col, (row - 1 : U32), ww, (need - 1 : U32), Crc.crc.byte(cc, Png.enc.b(col)), Png.enc.b(col) <> acc, Png.enc.add(aa, Png.enc.b(col)), Png.enc.add(bb, Png.enc.add(aa, Png.enc.b(col))), left, len), e_R, e_zn, hx, hw, e_pl, e_ll, xx => yy => h1 => h2 => h3 => h4 => h5 => rg(pp, False{}, False{}, True{}, U32.is_zero((need - 1 : U32)), False{}, True{}, False{}, False{}, px, col, (row - 1 : U32), ww, (need - 1 : U32), Crc.crc.byte(cc, Png.enc.b(col)), Png.enc.b(col) <> acc, Png.enc.add(aa, Png.enc.b(col)), Png.enc.add(bb, Png.enc.add(aa, Png.enc.b(col))), left, len, (pl - 1 : U32), xx, yy, kk, xn, wp, mx, emx, ew, two(row, Equal.sym(Bool, U32.is_zero(row), False{}, hrow), hbl({==}, {==}, {==})), ef => Empty.absurd({(row - 1 : U32) == ww : U32}, U32L.false_true(ef)), _e1 => e2 => _e3 => Empty.absurd({False{} == U32.is_eq((row - 1 : U32), 1) : Bool}, U32L.false_true(Equal.sym(Bool, True{}, False{}, e2))), h2, hk, h3, ({==}, ({==}, ({==}, (h4, (h5, h1)))))))

# ---- I. Adler-32 as enc.rgb.go adds it is Inf.adler.of ----

# The Adler modulus, 65521, is named pm below, for the same reason as mx.

# enc.add.at with the modulus named
def addm(zz: Bool, +tt: U32, +pm: U32) -> U32:
  match zz:
    case True{}:
      (tt - pm : U32)
    case False{}:
      tt

# enc.add.at is addm at 65521
def addm.eq(zz: Bool, +tt: U32, +pm: U32, +epm: {pm == 65521 : U32}) -> {Png.enc.add.at(zz, tt) == addm(zz, tt, pm) :
  U32}:
  match zz:
    case True{}:
      Equal.cong(U32, U32, uu => (tt - uu : U32), 65521, pm, Equal.sym(U32, pm, 65521, epm))
    case False{}:
      {==}

# at most and below cannot both hold the other way round
def le.lt.no(+aa: Nat, +bb: Nat, +h1: {Nat.is_le(aa, bb) == True{} : Bool}, +h2: {Nat.is_lt(bb, aa) == True{} : Bool}) ->
  Empty:
  lt.irr(aa, R.le_lt_trans(aa, bb, aa, h1, h2))

# t below 2 m is t mod m after one subtraction of m, or none: which one is t >= m's answer
def md.at(
  zz: Bool,
  qn: Nat,
  +tt: U32,
  +pm: U32,
  +ez: {U32.is_ge(tt, pm) == zz : Bool},
  +e_t: {U32.to_nat(tt) == Nat.add(Nat.mul(qn, U32.to_nat(pm)), U32.to_nat(U32.mod(tt, pm))) : Nat},
  +l_r: {Nat.is_lt(U32.to_nat(U32.mod(tt, pm)), U32.to_nat(pm)) == True{} : Bool},
  +ht: {Nat.is_lt(U32.to_nat(tt), Nat.add(U32.to_nat(pm), U32.to_nat(pm))) == True{} : Bool}
) -> {addm(zz, tt, pm) == U32.mod(tt, pm) : U32}:
  match zz qn:
    case True{} 0n:
      +mn = U32.to_nat(pm)
      +rn = U32.to_nat(U32.mod(tt, pm))
      +hg = {ge.le(U32.to_nat(tt), mn, Equal.trans(Bool, Cmp.is_ge(Nat.cmp(U32.to_nat(tt), mn)), U32.is_ge(tt, pm),
        True{}, Equal.sym(Bool, U32.is_ge(tt, pm), Cmp.is_ge(Nat.cmp(U32.to_nat(tt), mn)), u.ge(tt, pm)), ez)) :
        {Nat.is_le(mn, U32.to_nat(tt)) == True{} : Bool}}
      Empty.absurd({(tt - pm : U32) == U32.mod(tt, pm) : U32}, le.lt.no(mn, rn, R.le_rw_r(mn, U32.to_nat(tt), rn, e_t,
        hg), l_r))
    case True{} 1n+qp:
      match qp:
        case 0n:
          +mn = U32.to_nat(pm)
          +rn = U32.to_nat(U32.mod(tt, pm))
          +hg = {ge.le(U32.to_nat(tt), mn, Equal.trans(Bool, Cmp.is_ge(Nat.cmp(U32.to_nat(tt), mn)), U32.is_ge(tt, pm),
            True{}, Equal.sym(Bool, U32.is_ge(tt, pm), Cmp.is_ge(Nat.cmp(U32.to_nat(tt), mn)), u.ge(tt, pm)), ez)) :
            {Nat.is_le(mn, U32.to_nat(tt)) == True{} : Bool}}
          +e_t2 = {Equal.trans(Nat, U32.to_nat(tt), Nat.add(Nat.add(mn, 0n), rn), Nat.add(mn, rn), e_t, Equal.cong(Nat,
            Nat, kz => Nat.add(kz, rn), Nat.add(mn, 0n), mn, R.add_zero(mn))) : {U32.to_nat(tt) == Nat.add(mn, rn) :
            Nat}}
          u32.same((tt - pm : U32), U32.mod(tt, pm), Equal.trans(Nat, U32.to_nat((tt - pm : U32)), Nat.sub(U32.to_nat(tt),
            mn), rn, R.u32_sub_nat(tt, pm, hg), Equal.trans(Nat, Nat.sub(U32.to_nat(tt), mn), Nat.sub(Nat.add(mn, rn),
            mn), rn, Equal.cong(Nat, Nat, kz => Nat.sub(kz, mn), U32.to_nat(tt), Nat.add(mn, rn), e_t2),
            R.sub_add_cancel(mn, rn))))
        case 1n+(+qq):
          +mn = U32.to_nat(pm)
          +rn = U32.to_nat(U32.mod(tt, pm))
          +yy = Nat.add(mn, Nat.mul(qq, mn))
          +h1 = {R.le_add_mono(mn, mn, yy, Wp2.nle_add(mn, Nat.mul(qq, mn))) : {Nat.is_le(Nat.add(mn, mn), Nat.add(mn,
            yy)) == True{} : Bool}}
          +h2 = {R.le_rw_r(Nat.add(mn, mn), Nat.add(Nat.add(mn, yy), rn), U32.to_nat(tt), Equal.sym(Nat, U32.to_nat(tt),
            Nat.add(Nat.add(mn, yy), rn), e_t), R.le_trans(Nat.add(mn, mn), Nat.add(mn, yy), Nat.add(Nat.add(mn, yy),
            rn), h1, Wp2.nle_add(Nat.add(mn, yy), rn))) : {Nat.is_le(Nat.add(mn, mn), U32.to_nat(tt)) == True{} : Bool}}
          Empty.absurd({(tt - pm : U32) == U32.mod(tt, pm) : U32}, le.lt.no(Nat.add(mn, mn), U32.to_nat(tt), h2, ht))
    case False{} 0n:
      u32.same(tt, U32.mod(tt, pm), e_t)
    case False{} 1n+(+qp):
      +mn = U32.to_nat(pm)
      +rn = U32.to_nat(U32.mod(tt, pm))
      +yy = Nat.add(mn, Nat.mul(qp, mn))
      +hl = {nge.lt(U32.to_nat(tt), mn, Equal.trans(Bool, Cmp.is_ge(Nat.cmp(U32.to_nat(tt), mn)), U32.is_ge(tt, pm),
        False{}, Equal.sym(Bool, U32.is_ge(tt, pm), Cmp.is_ge(Nat.cmp(U32.to_nat(tt), mn)), u.ge(tt, pm)), ez)) :
        {Nat.is_lt(U32.to_nat(tt), mn) == True{} : Bool}}
      +h2 = {R.le_rw_r(mn, Nat.add(yy, rn), U32.to_nat(tt), Equal.sym(Nat, U32.to_nat(tt), Nat.add(yy, rn), e_t),
        R.le_trans(mn, yy, Nat.add(yy, rn), Wp2.nle_add(mn, Nat.mul(qp, mn)), Wp2.nle_add(yy, rn))) : {Nat.is_le(mn,
        U32.to_nat(tt)) == True{} : Bool}}
      Empty.absurd({tt == U32.mod(tt, pm) : U32}, le.lt.no(mn, U32.to_nat(tt), h2, hl))

# the modulus doubled is a U32's value
def pm.dbl(+pm: U32, +epm: {pm == 65521 : U32}) -> {U32.to_nat(U32.add(pm, pm)) == Nat.add(U32.to_nat(pm),
  U32.to_nat(pm)) : Nat}:
  add.cf(pm, pm, Equal.cong(U32, Bool, uu => cy32(uu, uu), pm, 65521, epm))

# U32.mod by the modulus: a quotient and a remainder below it
def pm.dvm(+tt: U32, +pm: U32, +epm: {pm == 65521 : U32}) -> dvm.ty(tt, pm):
  +mn = U32.to_nat(pm)
  +hm = {Equal.trans(Bool, Nat.is_lt(0n, mn), U32.is_lt(0, pm), True{}, Equal.sym(Bool, U32.is_lt(0, pm), Nat.is_lt(0n,
    mn), R.u32_lt(0, pm)), Equal.cong(U32, Bool, uu => U32.is_lt(0, uu), pm, 65521, epm)) : {Nat.is_lt(0n, mn) == True{} :
    Bool}}
  +h2 = {R.le_rw_r(Nat.add(mn, mn), Nat.add(mn, mn), U32.to_nat(U32.add(pm, pm)), Equal.sym(Nat,
    U32.to_nat(U32.add(pm, pm)), Nat.add(mn, mn), pm.dbl(pm, epm)), R.le_refl(Nat.add(mn, mn))) :
    {Nat.is_le(Nat.add(mn, mn), U32.to_nat(U32.add(pm, pm))) == True{} : Bool}}
  dvm(tt, pm, U32.add(pm, pm), hm, h2)

# the pair pm.dvm gives, taken apart, for one subtraction
def md.go(
  +tt: U32,
  +pm: U32,
  pr: dvm.ty(tt, pm),
  +ht: {Nat.is_lt(U32.to_nat(tt), Nat.add(U32.to_nat(pm), U32.to_nat(pm))) == True{} : Bool}
) -> {addm(U32.is_ge(tt, pm), tt, pm) == U32.mod(tt, pm) : U32}:
  (+e_t, +l_r) = pr
  md.at(U32.is_ge(tt, pm), U32.to_nat(U32.div(tt, pm)), tt, pm, {==}, e_t, l_r, ht)

# enc.add.at of a sum below twice the modulus is the sum mod 65521
def mod.once(
  +tt: U32,
  +pm: U32,
  +epm: {pm == 65521 : U32},
  +ht: {Nat.is_lt(U32.to_nat(tt), Nat.add(U32.to_nat(pm), U32.to_nat(pm))) == True{} : Bool}
) -> {Png.enc.add.at(U32.is_ge(tt, 65521), tt) == (tt % 65521 : U32) : U32}:
  +e65 = {Equal.sym(U32, pm, 65521, epm) : {65521 == pm : U32}}
  Equal.trans(U32, Png.enc.add.at(U32.is_ge(tt, 65521), tt), addm(U32.is_ge(tt, pm), tt, pm), (tt % 65521 : U32),
    Equal.trans(U32, Png.enc.add.at(U32.is_ge(tt, 65521), tt), Png.enc.add.at(U32.is_ge(tt, pm), tt), addm(U32.is_ge(tt,
      pm), tt, pm), Equal.cong(U32, U32, uu => Png.enc.add.at(U32.is_ge(tt, uu), tt), 65521, pm, e65),
      addm.eq(U32.is_ge(tt, pm), tt, pm, epm)),
    Equal.trans(U32, addm(U32.is_ge(tt, pm), tt, pm), U32.mod(tt, pm), (tt % 65521 : U32), md.go(tt, pm, pm.dvm(tt, pm,
      epm), ht), Equal.cong(U32, U32, uu => U32.mod(tt, uu), pm, 65521, epm)))

# the remainder pm.dvm gives, read as mod 65521
def mod.lt.go(+tt: U32, +pm: U32, +epm: {pm == 65521 : U32}, pr: dvm.ty(tt, pm)) -> {Nat.is_lt(U32.to_nat((tt % 65521 :
  U32)), U32.to_nat(pm)) == True{} : Bool}:
  (_e_t, +l_r) = pr
  R.lt_rw_l(U32.to_nat(U32.mod(tt, pm)), U32.to_nat((tt % 65521 : U32)), U32.to_nat(pm), Equal.cong(U32, Nat, uu =>
    U32.to_nat(U32.mod(tt, uu)), pm, 65521, epm), l_r)

# U32.mod by 65521 is below it
def mod.lt(+tt: U32, +pm: U32, +epm: {pm == 65521 : U32}) -> {Nat.is_lt(U32.to_nat((tt % 65521 : U32)), U32.to_nat(pm))
  == True{} : Bool}:
  mod.lt.go(tt, pm, epm, pm.dvm(tt, pm, epm))

# one Adler-32 add of values below the modulus is the add mod 65521
def add.mod(
  +ss: U32,
  +xx: U32,
  +pm: U32,
  +epm: {pm == 65521 : U32},
  +hs: {Nat.is_lt(U32.to_nat(ss), U32.to_nat(pm)) == True{} : Bool},
  +hx: {Nat.is_lt(U32.to_nat(xx), U32.to_nat(pm)) == True{} : Bool}
) -> {Png.enc.add(ss, xx) == ((ss + xx : U32) % 65521 : U32) : U32}:
  +mn = U32.to_nat(pm)
  +sn = U32.to_nat(ss)
  +xn = U32.to_nat(xx)
  +h1 = {Equal.trans(Bool, Nat.is_le(1n+sn, mn), Nat.is_lt(sn, mn), True{}, Equal.sym(Bool, Nat.is_lt(sn, mn),
    Nat.is_le(1n+sn, mn), R.lt_le_succ(sn, mn)), hs) : {Nat.is_le(1n+sn, mn) == True{} : Bool}}
  +h2 = {R.le_add_both(1n+sn, mn, xn, mn, h1, R.lt_le(xn, mn, hx)) : {Nat.is_le(1n+Nat.add(sn, xn), Nat.add(mn, mn)) ==
    True{} : Bool}}
  +h3 = {Equal.trans(Bool, Nat.is_lt(Nat.add(sn, xn), Nat.add(mn, mn)), Nat.is_le(1n+Nat.add(sn, xn), Nat.add(mn, mn)),
    True{}, R.lt_le_succ(Nat.add(sn, xn), Nat.add(mn, mn)), h2) : {Nat.is_lt(Nat.add(sn, xn), Nat.add(mn, mn)) ==
    True{} : Bool}}
  +e_s = {R.u32_add_below(ss, xx, U32.add(pm, pm), R.le_rw_r(Nat.add(sn, xn), Nat.add(mn, mn), U32.to_nat(U32.add(pm,
    pm)), Equal.sym(Nat, U32.to_nat(U32.add(pm, pm)), Nat.add(mn, mn), pm.dbl(pm, epm)), R.lt_le(Nat.add(sn, xn),
    Nat.add(mn, mn), h3))) : {U32.to_nat((ss + xx : U32)) == Nat.add(sn, xn) : Nat}}
  mod.once((ss + xx : U32), pm, epm, R.lt_rw_l(Nat.add(sn, xn), U32.to_nat((ss + xx : U32)), Nat.add(mn, mn),
    Equal.sym(Nat, U32.to_nat((ss + xx : U32)), Nat.add(sn, xn), e_s), h3))

# a byte is below the modulus
def byte.pm(+xx: U32, +pm: U32, +epm: {pm == 65521 : U32}, +hh: {U32.is_le(xx, 255) == True{} : Bool}) ->
  {Nat.is_lt(U32.to_nat(xx), U32.to_nat(pm)) == True{} : Bool}:
  R.le_lt_trans(U32.to_nat(xx), U32.to_nat(255), U32.to_nat(pm), Equal.trans(Bool, Nat.is_le(U32.to_nat(xx),
    U32.to_nat(255)), U32.is_le(xx, 255), True{}, Equal.sym(Bool, U32.is_le(xx, 255), Nat.is_le(U32.to_nat(xx),
    U32.to_nat(255)), R.u32_le(xx, 255)), hh), Equal.trans(Bool, Nat.is_lt(U32.to_nat(255), U32.to_nat(pm)),
    U32.is_lt(255, pm), True{}, Equal.sym(Bool, U32.is_lt(255, pm), Nat.is_lt(U32.to_nat(255), U32.to_nat(pm)),
    R.u32_lt(255, pm)), Equal.cong(U32, Bool, uu => U32.is_lt(255, uu), pm, 65521, epm)))

# afold of bytes is Inf.adler's fold, from sums below the modulus
def ad.eq(
  xs: List<&2, U32>,
  +aa: U32,
  +bb: U32,
  +pm: U32,
  +epm: {pm == 65521 : U32},
  +hby: {Laws.bytes.go(xs, True{}) == True{} : Bool},
  +ha: {Nat.is_lt(U32.to_nat(aa), U32.to_nat(pm)) == True{} : Bool},
  +hb: {Nat.is_lt(U32.to_nat(bb), U32.to_nat(pm)) == True{} : Bool}
) -> {afold(xs, aa, bb) == Inf.adler.fin(Inf.adler.go(xs, aa, bb)) : U32}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      +a2 = ((aa + x : U32) % 65521 : U32)
      +b2 = ((bb + a2 : U32) % 65521 : U32)
      +hxb = {Wp2.bytes.ok(t, U32.is_le(x, 255), hby) : {U32.is_le(x, 255) == True{} : Bool}}
      +e_a = {add.mod(aa, x, pm, epm, ha, byte.pm(x, pm, epm, hxb)) : {Png.enc.add(aa, x) == a2 : U32}}
      +l_a = {mod.lt((aa + x : U32), pm, epm) : {Nat.is_lt(U32.to_nat(a2), U32.to_nat(pm)) == True{} : Bool}}
      +e_b = {Equal.trans(U32, Png.enc.add(bb, Png.enc.add(aa, x)), Png.enc.add(bb, a2), b2, Equal.cong(U32, U32, uu =>
        Png.enc.add(bb, uu), Png.enc.add(aa, x), a2, e_a), add.mod(bb, a2, pm, epm, hb, l_a)) : {Png.enc.add(bb,
        Png.enc.add(aa, x)) == b2 : U32}}
      +l_b = {mod.lt((bb + a2 : U32), pm, epm) : {Nat.is_lt(U32.to_nat(b2), U32.to_nat(pm)) == True{} : Bool}}
      Equal.trans(U32, afold(t, Png.enc.add(aa, x), Png.enc.add(bb, Png.enc.add(aa, x))), afold(t, a2, b2),
        Inf.adler.fin(Inf.adler.go(t, a2, b2)),
        Equal.trans(U32, afold(t, Png.enc.add(aa, x), Png.enc.add(bb, Png.enc.add(aa, x))), afold(t, a2,
          Png.enc.add(bb, Png.enc.add(aa, x))), afold(t, a2, b2), Equal.cong(U32, U32, uu => afold(t, uu, Png.enc.add(bb,
          Png.enc.add(aa, x))), Png.enc.add(aa, x), a2, e_a), Equal.cong(U32, U32, uu => afold(t, a2, uu),
          Png.enc.add(bb, Png.enc.add(aa, x)), b2, e_b)),
        ad.eq(t, a2, b2, pm, epm, Wp2.bytes.tail(t, U32.is_le(x, 255), hby), l_a, l_b))

# enc.rgb.go's Adler-32 of bytes is Inf.adler.of
def afold.adler(
  +xs: List<&2, U32>,
  +pm: U32,
  +epm: {pm == 65521 : U32},
  +hby: {Laws.bytes(xs) == True{} : Bool}
) -> {afold(xs, 1, 0) == Inf.adler.of(xs) : U32}:
  +lt1 = {Equal.trans(Bool, Nat.is_lt(U32.to_nat(1), U32.to_nat(pm)), U32.is_lt(1, pm), True{}, Equal.sym(Bool,
    U32.is_lt(1, pm), Nat.is_lt(U32.to_nat(1), U32.to_nat(pm)), R.u32_lt(1, pm)), Equal.cong(U32, Bool, uu =>
    U32.is_lt(1, uu), pm, 65521, epm)) : {Nat.is_lt(U32.to_nat(1), U32.to_nat(pm)) == True{} : Bool}}
  +lt0 = {Equal.trans(Bool, Nat.is_lt(U32.to_nat(0), U32.to_nat(pm)), U32.is_lt(0, pm), True{}, Equal.sym(Bool,
    U32.is_lt(0, pm), Nat.is_lt(U32.to_nat(0), U32.to_nat(pm)), R.u32_lt(0, pm)), Equal.cong(U32, Bool, uu =>
    U32.is_lt(0, uu), pm, 65521, epm)) : {Nat.is_lt(U32.to_nat(0), U32.to_nat(pm)) == True{} : Bool}}
  ad.eq(xs, 1, 0, pm, epm, hby, lt1, lt0)

# ---- J. enc.wide.rgb after the signature and IHDR ----

# twice k, as a product
def mul2(kk: Nat) -> {Nat.mul(kk, 2n) == Nat.double(kk) : Nat}:
  match kk:
    case 0n:
      {==}
    case 1n+kp:
      Equal.cong(Nat, Nat, xx => 2n+xx, Nat.mul(kp, 2n), Nat.double(kp), mul2(kp))

# a count above 65535 is not zero, once is_zero's answer is named
def big.nz.at(zz: Bool, +nn: U32, +ez: {U32.is_zero(nn) == zz : Bool}, +hbig: {U32.is_le(nn, 65535) == False{} : Bool}) ->
  {U32.is_zero(nn) == False{} : Bool}:
  match zz:
    case False{}:
      ez
    case True{}:
      +e0 = {U32L.ueq(nn, 0, ez) : {nn == 0 : U32}}
      Empty.absurd({U32.is_zero(nn) == False{} : Bool}, U32L.false_true(Equal.trans(Bool, False{}, U32.is_le(nn, 65535),
        True{}, Equal.sym(Bool, U32.is_le(nn, 65535), False{}, hbig), Equal.cong(U32, Bool, uu => U32.is_le(uu, 65535),
        nn, 0, e0))))

# the fuel enc.wide.rgb.z gives enc.rgb.go: a step per raw byte and two per
# block, less one
def rgb.fuel(
  +nn: U32,
  +tu: U32,
  +nr: Nat,
  +hn: {U32.to_nat(nn) == nr : Nat},
  +nz: {U32.is_zero(nn) == False{} : Bool},
  +h_tu: {Nat.is_le(Nat.add(Nat.add(nr, Nat.mul(U32.to_nat(Png.enc.nblk(nn)), 5n)), 6n), U32.to_nat(tu)) == True{} :
    Bool}
) -> {Nat.is_le(Nat.add(Nat.add(nr, 0n), Nat.double(U32.to_nat(Png.enc.nblk(nn)))), 1n+U32.to_nat(((nn +
  (Png.enc.nblk(nn) * 2 : U32) : U32) - 1 : U32))) == True{} : Bool}:
  +kb = Png.enc.nblk(nn)
  +kn = U32.to_nat(kb)
  +k2 = Nat.mul(kn, 2n)
  +tn = U32.to_nat(tu)
  +s1 = (nn + (kb * 2 : U32) : U32)
  +h5 = {R.le_add_r(Nat.add(nr, Nat.mul(kn, 5n)), 6n, tn, h_tu) : {Nat.is_le(Nat.add(nr, Nat.mul(kn, 5n)), tn) == True{} :
    Bool}}
  +h25 = {R.le_rw_r(k2, Nat.mul(5n, kn), Nat.mul(kn, 5n), R.mul_comm(5n, kn), R.le_rw_l(Nat.mul(2n, kn), k2,
    Nat.mul(5n, kn), R.mul_comm(2n, kn), R.le_mul_mono(2n, 5n, kn, {==}))) : {Nat.is_le(k2, Nat.mul(kn, 5n)) == True{} :
    Bool}}
  +h2 = {R.le_trans(Nat.add(nr, k2), Nat.add(nr, Nat.mul(kn, 5n)), tn, R.le_add_mono(nr, k2, Nat.mul(kn, 5n), h25), h5) :
    {Nat.is_le(Nat.add(nr, k2), tn) == True{} : Bool}}
  +e_m = {R.u32_mul_below(kb, 2, tu, R.le_add_l(nr, k2, tn, h2)) : {U32.to_nat((kb * 2 : U32)) == k2 : Nat}}
  +e_s = {Equal.trans(Nat, U32.to_nat(s1), Nat.add(U32.to_nat(nn), U32.to_nat((kb * 2 : U32))), Nat.add(nr, k2),
    R.u32_add_below(nn, (kb * 2 : U32), tu, R.le_rw_l(Nat.add(nr, k2), Nat.add(U32.to_nat(nn), U32.to_nat((kb * 2 :
    U32))), tn, Equal.trans(Nat, Nat.add(nr, k2), Nat.add(U32.to_nat(nn), k2), Nat.add(U32.to_nat(nn), U32.to_nat((kb *
    2 : U32))), Equal.cong(Nat, Nat, xx => Nat.add(xx, k2), nr, U32.to_nat(nn), Equal.sym(Nat, U32.to_nat(nn), nr, hn)),
    Equal.cong(Nat, Nat, xx => Nat.add(U32.to_nat(nn), xx), k2, U32.to_nat((kb * 2 : U32)), Equal.sym(Nat,
    U32.to_nat((kb * 2 : U32)), k2, e_m))), h2)), Equal.trans(Nat, Nat.add(U32.to_nat(nn), U32.to_nat((kb * 2 : U32))),
    Nat.add(nr, U32.to_nat((kb * 2 : U32))), Nat.add(nr, k2), Equal.cong(Nat, Nat, xx => Nat.add(xx, U32.to_nat((kb * 2 :
    U32))), U32.to_nat(nn), nr, hn), Equal.cong(Nat, Nat, xx => Nat.add(nr, xx), U32.to_nat((kb * 2 : U32)), k2, e_m))) :
    {U32.to_nat(s1) == Nat.add(nr, k2) : Nat}}
  +e_n = {Equal.trans(Nat, U32.to_nat(nn), 1n+U32.to_nat((nn - 1 : U32)), 1n+U32.to_nat((nn - 1 : U32)), Wp1.u32_dec(nn,
    nz), {==}) : {U32.to_nat(nn) == 1n+U32.to_nat((nn - 1 : U32)) : Nat}}
  +nz1 = {Wp1.u32_nonzero(s1, Nat.add(U32.to_nat((nn - 1 : U32)), k2), Equal.trans(Nat, U32.to_nat(s1), Nat.add(nr, k2),
    1n+Nat.add(U32.to_nat((nn - 1 : U32)), k2), e_s, Equal.cong(Nat, Nat, xx => Nat.add(xx, k2), nr, 1n+U32.to_nat((nn -
    1 : U32)), Equal.trans(Nat, nr, U32.to_nat(nn), 1n+U32.to_nat((nn - 1 : U32)), Equal.sym(Nat, U32.to_nat(nn), nr, hn),
    e_n)))) : {U32.is_zero(s1) == False{} : Bool}}
  +e_st = {Equal.sym(Nat, U32.to_nat(s1), 1n+U32.to_nat((s1 - 1 : U32)), Wp1.u32_dec(s1, nz1)) : {1n+U32.to_nat((s1 - 1
    : U32)) == U32.to_nat(s1) : Nat}}
  +e_l = {Equal.trans(Nat, Nat.add(Nat.add(nr, 0n), Nat.double(kn)), Nat.add(nr, Nat.double(kn)), Nat.add(nr, k2),
    Equal.cong(Nat, Nat, xx => Nat.add(xx, Nat.double(kn)), Nat.add(nr, 0n), nr, R.add_zero(nr)), Equal.cong(Nat, Nat,
    xx => Nat.add(nr, xx), Nat.double(kn), k2, Equal.sym(Nat, k2, Nat.double(kn), mul2(kn)))) :
    {Nat.add(Nat.add(nr, 0n), Nat.double(kn)) == Nat.add(nr, k2) : Nat}}
  R.le_rw_r(Nat.add(Nat.add(nr, 0n), Nat.double(kn)), Nat.add(nr, k2), 1n+U32.to_nat((s1 - 1 : U32)), Equal.trans(Nat,
    Nat.add(nr, k2), U32.to_nat(s1), 1n+U32.to_nat((s1 - 1 : U32)), Equal.sym(Nat, U32.to_nat(s1), Nat.add(nr, k2), e_s),
    Equal.sym(Nat, 1n+U32.to_nat((s1 - 1 : U32)), U32.to_nat(s1), e_st)), R.le_rw_l(Nat.add(nr, k2),
    Nat.add(Nat.add(nr, 0n), Nat.double(kn)), Nat.add(nr, k2), Equal.sym(Nat, Nat.add(Nat.add(nr, 0n), Nat.double(kn)),
    Nat.add(nr, k2), e_l), R.le_refl(Nat.add(nr, k2))))

# enc.wide.rgb after the signature and IHDR: the IDAT chunk holding the zlib
# stream of the scanlines in stored blocks of 65535 bytes, then IEND
def rgb.tail(
  +px: List<&2, U32>,
  +ww: U32,
  +wp: Nat,
  +mx: U32,
  +pm: U32,
  +tu: U32,
  +ie: List<&2, U32>,
  +emx: {mx == 65535 : U32},
  +epm: {pm == 65521 : U32},
  +ew: {U32.to_nat(ww) == 1n+wp : Nat},
  +hn: {U32.to_nat(Png.enc.len(W9.sc(px, 0n, 1n+wp, True{}), 0)) == List.length(&2, U32, W9.sc(px, 0n, 1n+wp, True{}))
    : Nat},
  +hbig: {U32.is_le(Png.enc.len(W9.sc(px, 0n, 1n+wp, True{}), 0), 65535) == False{} : Bool},
  +hby: {Laws.bytes(W9.sc(px, 0n, 1n+wp, True{})) == True{} : Bool},
  +hl: {Png.enc.idat.ln(Png.enc.len(W9.sc(px, 0n, 1n+wp, True{}), 0)) == Png.enc.len(Laws.zlib.stored(65535,
    W9.sc(px, 0n, 1n+wp, True{})), 0) : U32},
  +h_tu: {Nat.is_le(Nat.add(Nat.add(List.length(&2, U32, W9.sc(px, 0n, 1n+wp, True{})),
    Nat.mul(U32.to_nat(Png.enc.nblk(Png.enc.len(W9.sc(px, 0n, 1n+wp, True{}), 0))), 5n)), 6n), U32.to_nat(tu)) == True{}
    : Bool}
) -> {Png.enc.wide.rgb.go(Png.enc.crc.list(Png.enc.be(Png.tag.idat()), 4294967295,
  Png.enc.cat.go(Png.enc.be(Png.enc.idat.ln(Png.enc.len(W9.sc(px, 0n, 1n+wp, True{}), 0))), [])), px, ww,
  Png.enc.len(W9.sc(px, 0n, 1n+wp, True{}), 0), ie) == Png.enc.cat(Png.enc.chunk(Png.tag.idat(),
  Laws.zlib.stored(65535, W9.sc(px, 0n, 1n+wp, True{}))), ie) : List<&2, U32>}:
  +raw = W9.sc(px, 0n, 1n+wp, True{})
  +nr = List.length(&2, U32, raw)
  +nn = Png.enc.len(raw, 0)
  +kn = U32.to_nat(Png.enc.nblk(nn))
  +ll = Png.enc.idat.ln(nn)
  +aa = Png.enc.cat.go(Png.enc.be(ll), [])
  +bi = Png.enc.be(Png.tag.idat())
  +c1 = Crc.crc.fold(bi, 4294967295)
  +a1 = List.reverse.go(&2, U32, bi, aa)
  +c2 = Crc.crc.fold([120, 1], c1)
  +a2 = List.reverse.go(&2, U32, [120, 1], a1)
  +steps = ((nn + (Png.enc.nblk(nn) * 2 : U32) : U32) - 1 : U32)
  +sum = Inf.adler.of(raw)
  +bb = bs(raw, True{}, False{}, 0, nn, Png.enc.cap(nn), Png.enc.bf(nn))
  +bl = Png.enc.blocks(65535, raw)
  +e_b = {sim.blocks(raw, mx, emx, hn, hbig) : {bl == bb : List<&2, U32>}}
  +zz = Laws.zlib.stored(65535, raw)
  +hl2 = {Equal.trans(U32, ll, Png.enc.len(zz, 0), Png.enc.len(zb(bb, sum), 0), hl, Equal.cong(List<&2, U32>, U32, ys =>
    Png.enc.len(zb(ys, sum), 0), bl, bb, e_b)) : {ll == Png.enc.len(zb(bb, sum), 0) : U32}}
  +nz = {big.nz.at(U32.is_zero(nn), nn, {==}, hbig) : {U32.is_zero(nn) == False{} : Bool}}
  -go = Png.enc.rgb.go(U32.to_nat(steps), True{}, False{}, False{}, False{}, True{}, True{}, False{}, False{}, px, 0, ww,
    ww, 0, c2, a2, 1, 0, nn, 0)
  +e_go = {rg(U32.to_nat(steps), True{}, False{}, False{}, False{}, True{}, True{}, False{}, False{}, px, 0, ww, ww, 0, c2,
    a2, 1, 0, nn, 0, nn, 0, 0, kn, nr, wp, mx, emx, ew, Wp1.u32_nonzero(ww, wp, ew), _ef => {==}, ef =>
    Empty.absurd({True{} == False{} : Bool} -> {False{} == False{} : Bool} -> {False{} == U32.is_eq(ww, 1) : Bool},
    U32L.false_true(Equal.sym(Bool, True{}, False{}, ef))), {==}, kok.rw(U32.to_nat(nn), nr, kn, U32.to_nat(mx), hn,
    nb.k(nn, mx, emx)), rgb.fuel(nn, tu, nr, hn, nz, h_tu), (Equal.sym(Bool, U32.is_zero(nn), False{}, nz), hn)) : {go ==
    (fr(bb, c2, a2), afold(raw, 1, 0)) : (U32 & List<&2, U32>) & U32}}
  +e_fr = {Equal.trans(U32 & List<&2, U32>, fr(bb, c2, a2), fr(List.append(&2, U32, [120, 1], bb), c1, a1), fr(t0(bb),
    4294967295, aa), fr.app([120, 1], bb, c1, a1), fr.app(bi, List.append(&2, U32, [120, 1], bb), 4294967295, aa)) :
    {fr(bb, c2, a2) == fr(t0(bb), 4294967295, aa) : U32 & List<&2, U32>}}
  Equal.trans(List<&2, U32>, Png.enc.wide.rgb.go(Png.enc.crc.list(bi, 4294967295, aa), px, ww, nn, ie),
    Png.enc.wide.rgb.go(fr(bi, 4294967295, aa), px, ww, nn, ie), Png.enc.cat(Png.enc.chunk(Png.tag.idat(), zz), ie),
    Equal.cong(U32 & List<&2, U32>, List<&2, U32>, pp => Png.enc.wide.rgb.go(pp, px, ww, nn, ie), Png.enc.crc.list(bi,
      4294967295, aa), fr(bi, 4294967295, aa), crcl(bi, 4294967295, aa)),
    Equal.trans(List<&2, U32>, Png.enc.wide.rgb.z(Png.enc.crc.list([120, 1], c1, a1), px, ww, nn, ie),
      Png.enc.wide.rgb.z(fr([120, 1], c1, a1), px, ww, nn, ie), Png.enc.cat(Png.enc.chunk(Png.tag.idat(), zz), ie),
      Equal.cong(U32 & List<&2, U32>, List<&2, U32>, pp => Png.enc.wide.rgb.z(pp, px, ww, nn, ie),
        Png.enc.crc.list([120, 1], c1, a1), fr([120, 1], c1, a1), crcl([120, 1], c1, a1)),
      Equal.trans(List<&2, U32>, Png.enc.wide.rgb.out(go, ie), Png.enc.wide.rgb.out((fr(bb, c2, a2), afold(raw, 1, 0)),
        ie), Png.enc.cat(Png.enc.chunk(Png.tag.idat(), zz), ie),
        Equal.cong((U32 & List<&2, U32>) & U32, List<&2, U32>, gg => Png.enc.wide.rgb.out(gg, ie), go, (fr(bb, c2, a2),
          afold(raw, 1, 0)), e_go),
        Equal.trans(List<&2, U32>, Png.enc.seal.adler(fr(bb, c2, a2), afold(raw, 1, 0), ie),
          Png.enc.seal.adler(fr(t0(bb), 4294967295, aa), sum, ie), Png.enc.cat(Png.enc.chunk(Png.tag.idat(), zz), ie),
          Equal.trans(List<&2, U32>, Png.enc.seal.adler(fr(bb, c2, a2), afold(raw, 1, 0), ie),
            Png.enc.seal.adler(fr(bb, c2, a2), sum, ie), Png.enc.seal.adler(fr(t0(bb), 4294967295, aa), sum, ie),
            Equal.cong(U32, List<&2, U32>, uu => Png.enc.seal.adler(fr(bb, c2, a2), uu, ie), afold(raw, 1, 0), sum,
              afold.adler(raw, pm, epm, hby)),
            Equal.cong(U32 & List<&2, U32>, List<&2, U32>, pp => Png.enc.seal.adler(pp, sum, ie), fr(bb, c2, a2),
              fr(t0(bb), 4294967295, aa), e_fr)),
          Equal.trans(List<&2, U32>, Png.enc.seal.adler(fr(t0(bb), 4294967295, aa), sum, ie),
            Png.enc.cat(Png.enc.chunk(Png.tag.idat(), zb(bb, sum)), ie), Png.enc.cat(Png.enc.chunk(Png.tag.idat(), zz),
            ie), tail.chunk(bb, sum, ll, ie, hl2), Equal.cong(List<&2, U32>, List<&2, U32>, ys =>
            Png.enc.cat(Png.enc.chunk(Png.tag.idat(), zb(ys, sum)), ie), bb, bl, Equal.sym(List<&2, U32>, bl, bb,
            e_b)))))))
