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
