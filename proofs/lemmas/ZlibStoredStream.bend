# the zlib header and Adler-32 field around stored blocks, and their inflate
import Base
import ../../src/inflate.bend as Inf
import ../../src/png.bend as Png
import ../../laws/InflateReadsStoredBlocks.bend as L1
import ../../laws/defs/PngSpecification.bend as D1
import ./BasicFacts.bend as M1
import ./StoredBlockEncoder.bend as M2
import ./StoredBlockReader.bend as M3

# the Adler field rd.adler folds, big-endian, from the bytes it reads
def run.of(bytes: List<&2, U32>, +run: U32) -> U32:
  match bytes:
    case Nil{}:
      run
    case +bt <> tl:
      run.of(tl, ((255 .&. M3.rdv(M3.bits8(bt), 0, 0) : U32) .|. (run << 8n : U32) : U32))

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
    Equal.trans(U32, U32.or(U32.or(ss, 0), 0), U32.or(ss, 0), ss, M3.u_or_zero(U32.or(ss, 0)), M3.u_or_zero(ss)))


# the zlib header 120 1 leaves the reader at the first block header
def hdr(
  +bud: Maybe<&2, Nat>,
  rest: List<&2, U32>
) -> {M3.run.bytes(bud, 120 <> 1 <> rest, Inf.st.empty()) == M3.run.bytes(bud, rest, M3.st.blk(0, [], 0)) :
  Maybe<&2, List<&2, U32>>}:
  {==}

# the reader once the Adler-32 field is read, `zz` its check
def st.done(zz: Bool, +raw: List<&2, U32>, +run: U32, +pend: U32) -> Inf.St:
  Inf.rd.adler.eq(zz, 0, Inf.Cx{True{}, 0, 0, raw, Inf.TNone{}, 0, pend, run, Inf.hs.none()})

# the four Adler bytes, as the reader first folds them
def adler.raw(
  +bud: Maybe<&2, Nat>,
  +ss: U32,
  +out: List<&2, U32>,
  +pend: U32
) -> {M3.run.bytes(bud, Png.enc.be(ss), M2.st.adler(out, pend)) == M3.run.bytes(bud, [],
  st.done(U32.is_eq(Inf.adler.of(List.reverse(&2, U32, out)), run.of(Png.enc.be(ss), 0)), List.reverse(&2, U32, out),
  run.of(Png.enc.be(ss), 0), pend)) : Maybe<&2, List<&2, U32>>}:
  {==}

# the four Adler bytes of the bytes copied: the reader answers those bytes,
# measured against the budget if any
def adler.ok(
  +bud: Maybe<&2, Nat>,
  +ss: U32,
  +out: List<&2, U32>,
  +pend: U32,
  e_sum: {ss == Inf.adler.of(List.reverse(&2, U32, out)) : U32}
) -> {M3.run.bytes(bud, Png.enc.be(ss), M2.st.adler(out, pend)) == Inf.inflate.out(bud, List.reverse(&2, U32, out)) :
  Maybe<&2, List<&2, U32>>}:
  +raw = List.reverse(&2, U32, out)
  +aa = Inf.adler.of(raw)
  +r4 = run.of(Png.enc.be(ss), 0)
  +fin = Inf.inflate.out(bud, raw)
  Equal.trans(Maybe<&2, List<&2, U32>>, M3.run.bytes(bud, Png.enc.be(ss), M2.st.adler(out, pend)),
    M3.run.bytes(bud, [], st.done(U32.is_eq(aa, r4), raw, r4, pend)), fin,
    adler.raw(bud, ss, out, pend),
    Equal.trans(Maybe<&2, List<&2, U32>>, M3.run.bytes(bud, [], st.done(U32.is_eq(aa, r4), raw, r4, pend)),
      M3.run.bytes(bud, [], st.done(U32.is_eq(aa, ss), raw, r4, pend)), fin,
      Equal.cong(U32, Maybe<&2, List<&2, U32>>, vv => M3.run.bytes(bud, [], st.done(U32.is_eq(aa, vv), raw, r4,
        pend)), r4, ss, run_be(ss)),
      Equal.trans(Maybe<&2, List<&2, U32>>, M3.run.bytes(bud, [], st.done(U32.is_eq(aa, ss), raw, r4, pend)),
        M3.run.bytes(bud, [], st.done(U32.is_eq(aa, aa), raw, r4, pend)), fin,
        Equal.cong(U32, Maybe<&2, List<&2, U32>>, vv => M3.run.bytes(bud, [], st.done(U32.is_eq(aa, vv), raw, r4,
          pend)), ss, aa, e_sum),
        Equal.cong(Bool, Maybe<&2, List<&2, U32>>, bb => M3.run.bytes(bud, [], st.done(bb, raw, r4, pend)),
          U32.is_eq(aa, aa), True{}, M1.u32_eq_refl(aa)))))

# the stored bytes enc.blocks owes the window on top of `pend`: one block's
# LEN when xs fits in sz bytes (zz), enc.feed's blocks' otherwise
def pend.at(zz: Bool, +sz: U32, +xs: List<&2, U32>, +pend: U32) -> U32:
  match zz:
    case True{}:
      (pend + U32.and(65535, Png.enc.len(xs, 0)) : U32)
    case False{}:
      M2.pend.fl(xs, U32.is_zero(sz), sz, sz, [], pend)

# enc.blocks: one final block when xs fits in sz bytes (zz), enc.feed's blocks
# otherwise; either way the reader copies xs and reaches the Adler field
def bl.at(
  +bud: Maybe<&2, Nat>,
  zz: Bool,
  +sz: U32,
  +xs: List<&2, U32>,
  +rest: List<&2, U32>,
  +left: U32,
  +out: List<&2, U32>,
  +pend: U32,
  +ez: {U32.is_le(Png.enc.len(xs, 0), sz) == zz : Bool},
  +h_nz: {U32.is_zero(sz) == False{} : Bool},
  +h_sz: {U32.is_le(sz, 65535) == True{} : Bool},
  +h_bx: {D1.bytes.go(xs, True{}) == True{} : Bool},
  +h_n: {U32.to_nat(Png.enc.len(xs, 0)) == List.length(&2, U32, xs) : Nat}
) -> {M3.run.bytes(bud, List.append(&2, U32, Png.enc.blocks.fit(zz, sz, Png.enc.len(xs, 0), xs), rest),
  M3.st.blk(left, out, pend)) == M3.run.bytes(bud, rest, M2.st.adler(List.reverse.go(&2, U32, xs, out), pend.at(zz,
  sz, xs, pend))) : Maybe<&2, List<&2, U32>>}:
  match zz:
    case True{}:
      +nn = Png.enc.len(xs, 0)
      +hd = Png.enc.head(True{}, nn, U32.xor(nn, 65535))
      +em = M2.mask16(nn, M2.u_le_trans(nn, sz, 65535, ez, h_sz))
      +hc = Equal.trans(Bool, M3.cnt(xs, U32.is_zero(U32.and(65535, nn)), U32.and(65535, nn)), M3.cnt(xs,
        U32.is_zero(nn), nn), True{}, Equal.cong(U32, Bool, vv => M3.cnt(xs, U32.is_zero(vv), vv), U32.and(65535,
        nn), nn, em), M2.ncnt(xs, nn, U32.is_zero(nn), {==}, h_n))
      +p1 = (pend + U32.and(65535, nn) : U32)
      +o1 = List.reverse.go(&2, U32, xs, out)
      +b0 = M3.st.blk(left, out, pend)
      Equal.trans(Maybe<&2, List<&2, U32>>, M3.run.bytes(bud, List.append(&2, U32, Png.enc.cat(hd, xs), rest), b0),
        M3.run.bytes(bud, List.append(&2, U32, List.append(&2, U32, hd, xs), rest), b0),
        M3.run.bytes(bud, rest, M2.st.adler(o1, p1)),
        Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, ll => M3.run.bytes(bud, List.append(&2, U32, ll, rest),
          b0), Png.enc.cat(hd, xs), List.append(&2, U32, hd, xs), M2.cat_app(hd, xs)),
        Equal.trans(Maybe<&2, List<&2, U32>>, M3.run.bytes(bud, List.append(&2, U32, List.append(&2, U32, hd, xs),
          rest), b0), M3.run.bytes(bud, rest, M3.st.after(True{}, M1.cd(xs, U32.and(65535, nn)), o1, p1)),
          M3.run.bytes(bud, rest, M2.st.adler(o1, p1)),
          M3.blk(bud, True{}, nn, xs, rest, left, out, pend, hc, h_bx),
          M2.after_last(bud, M1.cd(xs, U32.and(65535, nn)), o1, rest, p1)))
    case False{}:
      M2.fl(bud, xs, U32.is_zero(sz), sz, sz, [], rest, left, out, pend, {==}, {==}, h_nz, h_sz, h_bx, {==})

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
      e1 = Equal.cong(U32, Bool, xx => U32.is_le(1, xx), sz, 0, M1.ueq(sz, 0, ez))
      Empty.absurd({U32.is_zero(sz) == False{} : Bool}, M1.true_false(Equal.trans(Bool, True{}, U32.is_le(1, sz),
        U32.is_le(1, 0), Equal.sym(Bool, U32.is_le(1, sz), True{}, h_one), e1)))

# the zlib stream of xs in stored blocks of sz bytes, driven with the budget
# `bud`: the answer is xs, measured against the budget if any
def stored_out(
  +bud: Maybe<&2, Nat>,
  +sz: U32,
  +xs: List<&2, U32>,
  +h_sz: {Bool.and(U32.is_le(1, sz), U32.is_le(sz, 65535)) == True{} : Bool},
  +h_by: {D1.bytes(xs) == True{} : Bool},
  +h_n: {U32.to_nat(Png.enc.len(xs, 0)) == List.length(&2, U32, xs) : Nat}
) -> {Inf.inflate.drive(L1.zlib.stored(sz, xs), Inf.st.empty(), bud) == Inf.inflate.out(bud, xs) : Maybe<&2, List<&2,
  U32>>}:
  +h_one = M1.and_left(U32.is_le(1, sz), U32.is_le(sz, 65535), h_sz)
  +h_top = M1.and_right(U32.is_le(1, sz), U32.is_le(sz, 65535), h_sz)
  +h_nz = sz_nz(U32.is_zero(sz), sz, {==}, h_one)
  +aa = Inf.adler.of(xs)
  +bb = Png.enc.blocks(sz, xs)
  +ox = List.reverse.go(&2, U32, xs, [])
  +rx = M1.inf.rev_rev(xs)
  +zz = U32.is_le(Png.enc.len(xs, 0), sz)
  +pz = pend.at(zz, sz, xs, 0)
  +b0 = M3.st.blk(0, [], 0)
  +fx = Inf.inflate.out(bud, xs)
  Equal.trans(Maybe<&2, List<&2, U32>>, M3.run.bytes(bud, L1.zlib.stored(sz, xs), Inf.st.empty()),
    M3.run.bytes(bud, Png.enc.cat(bb, Png.enc.be(aa)), b0), fx,
    hdr(bud, Png.enc.cat(bb, Png.enc.be(aa))),
    Equal.trans(Maybe<&2, List<&2, U32>>, M3.run.bytes(bud, Png.enc.cat(bb, Png.enc.be(aa)), b0),
      M3.run.bytes(bud, List.append(&2, U32, bb, Png.enc.be(aa)), b0), fx,
      Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, ll => M3.run.bytes(bud, ll, b0), Png.enc.cat(bb,
        Png.enc.be(aa)), List.append(&2, U32, bb, Png.enc.be(aa)), M2.cat_app(bb, Png.enc.be(aa))),
      Equal.trans(Maybe<&2, List<&2, U32>>, M3.run.bytes(bud, List.append(&2, U32, bb, Png.enc.be(aa)), b0),
        M3.run.bytes(bud, Png.enc.be(aa), M2.st.adler(ox, pz)), fx,
        bl.at(bud, zz, sz, xs, Png.enc.be(aa), 0, [], 0, {==}, h_nz, h_top, h_by, h_n),
        Equal.trans(Maybe<&2, List<&2, U32>>, M3.run.bytes(bud, Png.enc.be(aa), M2.st.adler(ox, pz)),
          Inf.inflate.out(bud, List.reverse(&2, U32, ox)), fx,
          adler.ok(bud, aa, ox, pz, Equal.cong(List<&2, U32>, U32, ll => Inf.adler.of(ll), xs, List.reverse(&2, U32,
            ox), Equal.sym(List<&2, U32>, List.reverse(&2, U32, ox), xs, rx))),
          Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, ll => Inf.inflate.out(bud, ll), List.reverse(&2, U32,
            ox), xs, rx)))))

# laws/InflateReadsStoredBlocks.bend: the zlib stream of xs in stored blocks of sz bytes inflates to xs
def inflate_stored(
  +sz: U32,
  +xs: List<&2, U32>,
  +h_sz: {Bool.and(U32.is_le(1, sz), U32.is_le(sz, 65535)) == True{} : Bool},
  +h_by: {D1.bytes(xs) == True{} : Bool},
  +h_n: {U32.to_nat(Png.enc.len(xs, 0)) == List.length(&2, U32, xs) : Nat}
) -> {Inf.inflate(L1.zlib.stored(sz, xs)) == Some{xs} : Maybe<&2, List<&2, U32>>}:
  stored_out(None{}, sz, xs, h_sz, h_by, h_n)

# the same stream with a budget of at least its length: inflate.upto answers xs
def upto_stored(
  +lim: Nat,
  +sz: U32,
  +xs: List<&2, U32>,
  +h_sz: {Bool.and(U32.is_le(1, sz), U32.is_le(sz, 65535)) == True{} : Bool},
  +h_by: {D1.bytes(xs) == True{} : Bool},
  +h_n: {U32.to_nat(Png.enc.len(xs, 0)) == List.length(&2, U32, xs) : Nat},
  +h_lim: {Nat.is_le(List.length(&2, U32, xs), lim) == True{} : Bool}
) -> {Inf.inflate.upto(lim, L1.zlib.stored(sz, xs)) == Some{xs} : Maybe<&2, List<&2, U32>>}:
  Equal.trans(Maybe<&2, List<&2, U32>>, Inf.inflate.upto(lim, L1.zlib.stored(sz, xs)),
    Inf.inflate.out(Some{lim}, xs), Some{xs},
    stored_out(Some{lim}, sz, xs, h_sz, h_by, h_n),
    Equal.cong(Bool, Maybe<&2, List<&2, U32>>, bb => Inf.inflate.upto.fin(bb, xs), Nat.is_le(List.length(&2, U32,
      xs), lim), True{}, h_lim))

def L1.inflate_enc_zlib(xs, h_by, h_n):
  inflate_stored(65535, xs, {==}, h_by, h_n)
