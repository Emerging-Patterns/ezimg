# At bit depths other than 8, each sample is the specification's unpacking
# of the unfiltered scanline bytes (PNG section 7.2), and each pixel its
# packing to 0xAARRGGBB. Samples of 1, 2 and 4 bits are packed into bytes
# most significant bit first; 16-bit samples are two bytes, most significant
# first. A gray sample of d bits scales to 8 bits as v * 255 / (2^d - 1),
# which is bit replication (section 13.12); a 16-bit sample reduces to its
# high byte; a tRNS key compares with the samples at their full width before
# either. Indexed samples of 1, 2 and 4 bits are palette indices, as at 8.
# The decoder read bit depth 8 alone until 2026-11.
import Base
import ../src/png.bend as Png
import ./PngSamplesFollowColourType.bend as L1

# ---- unpacking ----

# 2^d - 1: the largest sample of d bits, and the mask that takes one
def spec.max(+dd: U32) -> U32:
  U32.sub(U32.shln(1, U32.to_nat(dd)), 1)

# the samples of one byte at bit depth d of 1, 2 or 4, most significant
# first: with k samples still to come, the next is the d bits k - 1 samples
# up from the bottom
def spec.byte.go(+dd: U32, +bb: U32, kk: Nat) -> List<&2, U32>:
  match kk:
    case 0n:
      Nil{}
    case 1n+(+pp):
      U32.and(U32.shrn(bb, Nat.mul(pp, U32.to_nat(dd))), spec.max(dd)) <> spec.byte.go(dd, bb, pp)

# the 8 / d samples of a byte
def spec.byte(+dd: U32, +bb: U32) -> List<&2, U32>:
  spec.byte.go(dd, bb, Nat.div(8n, U32.to_nat(dd)))

# every sample a row's bytes hold, in order, the unused bits at its end too
def spec.samples(+dd: U32, row: List<&2, U32>) -> List<&2, U32>:
  match row:
    case Nil{}:
      Nil{}
    case +bb <> tl:
      List.append(&2, U32, spec.byte(dd, bb), spec.samples(dd, tl))

# a 16-bit value from its two bytes, most significant first
def spec.u16(+hi: U32, +lo: U32) -> U32:
  U32.or(U32.shln(hi, 8n), lo)

# the 16-bit samples of a row, two bytes each; a last byte alone is no sample
def spec.pairs(row: List<&2, U32>) -> List<&2, U32>:
  match row:
    case +hi <> +lo <> tl:
      spec.u16(hi, lo) <> spec.pairs(tl)
    case _row:
      Nil{}

# LAW: a scanline of 1-bit samples: the first count of its bits, most significant first
law png_unpack_1:
  for +count: Nat
  for +row: List<&2, U32>
  {Png.unpack.row(1, count, row) == List.take(&2, U32, spec.samples(1, row), count) : List<&2, U32>}

# LAW: a scanline of 2-bit samples: the first count of its 2-bit fields, most significant first
law png_unpack_2:
  for +count: Nat
  for +row: List<&2, U32>
  {Png.unpack.row(2, count, row) == List.take(&2, U32, spec.samples(2, row), count) : List<&2, U32>}

# LAW: a scanline of 4-bit samples: the first count of its 4-bit fields, most significant first
law png_unpack_4:
  for +count: Nat
  for +row: List<&2, U32>
  {Png.unpack.row(4, count, row) == List.take(&2, U32, spec.samples(4, row), count) : List<&2, U32>}

# LAW: a scanline of 8-bit samples: its bytes
law png_unpack_8:
  for +count: Nat
  for +row: List<&2, U32>
  {Png.unpack.row(8, count, row) == row : List<&2, U32>}

# LAW: a scanline of 16-bit samples: its byte pairs, most significant first
law png_unpack_16:
  for +count: Nat
  for +row: List<&2, U32>
  {Png.unpack.row(16, count, row) == spec.pairs(row) : List<&2, U32>}

# ---- packing ----

# an RGB tRNS key: red, green and blue, each 16 bits
type Key3 is Data:
  Key3{+r: U32, +g: U32, +b: U32}

# a 16-bit sample reduced to 8 bits: its high byte
def spec.hi(+vv: U32) -> U32:
  U32.shrn(vv, 8n)

# a d-bit gray sample scaled to 8 bits: v * 255 / (2^d - 1)
def spec.up(+dd: U32, +vv: U32) -> U32:
  U32.div(U32.mul(vv, 255), spec.max(dd))

# the alpha a key gives a sample: 0 when it is the key, 255 otherwise or with no key
def spec.key.alpha(key: Maybe<&2, U32>, +ss: U32) -> U32:
  match key:
    case None{}:
      255
    case Some{+kk}:
      L1.spec.key.alpha(U32.is_eq(ss, kk))

# gray of d bits, with key k when there is one: alpha 0 where the unscaled sample is k
def spec.grey.low(+dd: U32, xs: List<&2, U32>, +key: Maybe<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case +gg <> tl:
      L1.spec.argb(spec.key.alpha(key, gg), spec.up(dd, gg), spec.up(dd, gg), spec.up(dd, gg)) <> spec.grey.low(dd,
        tl, key)

# 16-bit gray, with key k when there is one, compared at 16 bits
def spec.grey16(xs: List<&2, U32>, +key: Maybe<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case +gg <> tl:
      L1.spec.argb(spec.key.alpha(key, gg), spec.hi(gg), spec.hi(gg), spec.hi(gg)) <> spec.grey16(tl, key)

# the alpha an RGB key gives a triple
def spec.rgb.alpha(key: Maybe<&2, Key3>, +rr: U32, +gg: U32, +bb: U32) -> U32:
  match key:
    case None{}:
      255
    case Some{Key3{+kr, +kg, +kb}}:
      L1.spec.key.alpha(Bool.and(U32.is_eq(rr, kr), Bool.and(U32.is_eq(gg, kg), U32.is_eq(bb, kb))))

# 16-bit RGB with an optional key: alpha 0 where all three samples are the key's, compared at 16 bits
def spec.rgb16(xs: List<&2, U32>, +key: Maybe<&2, Key3>) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case +rr <> +gg <> +bb <> tl:
      L1.spec.cons(L1.spec.argb(spec.rgb.alpha(key, rr, gg, bb), spec.hi(rr), spec.hi(gg), spec.hi(bb)),
        spec.rgb16(tl, key))
    case Nil{}:
      Some{Nil{}}
    case _xs:
      None{}

# 16-bit gray and alpha: each pair packed from its high bytes; none when a pair is cut short
def spec.ga16(xs: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case +gg <> +aa <> tl:
      L1.spec.cons(L1.spec.argb(spec.hi(aa), spec.hi(gg), spec.hi(gg), spec.hi(gg)), spec.ga16(tl))
    case Nil{}:
      Some{Nil{}}
    case _xs:
      None{}

# 16-bit RGBA: each quadruple packed from its high bytes; none when one is cut short
def spec.rgba16(xs: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case +rr <> +gg <> +bb <> +aa <> tl:
      L1.spec.cons(L1.spec.argb(spec.hi(aa), spec.hi(rr), spec.hi(gg), spec.hi(bb)), spec.rgba16(tl))
    case Nil{}:
      Some{Nil{}}
    case _xs:
      None{}

# a bit depth of 1, 2 or 4
def spec.low(+dd: U32) -> Bool:
  Bool.or(U32.is_eq(dd, 1), Bool.or(U32.is_eq(dd, 2), U32.is_eq(dd, 4)))

# LAW: gray of 1, 2 or 4 bits without tRNS: each sample v decodes to gray v * 255 / (2^d - 1), alpha 255
law png_px_grey_low:
  for +dd: U32
  for +xs: List<&2, U32>
  for +plte: List<&2, U32>
  for h_dd: {spec.low(dd) == True{} : Bool}
  {Png.px.deep(0, dd, xs, plte, []) == Some{spec.grey.low(dd, xs, None{})} : Maybe<&2, List<&2, U32>>}

# LAW: gray of 1, 2 or 4 bits with tRNS bytes k1, k0: the key k1 * 256 + k0 is compared with the unscaled sample
law png_px_grey_low_key:
  for +dd: U32
  for +xs: List<&2, U32>
  for +plte: List<&2, U32>
  for +k1: U32
  for +k0: U32
  for h_dd: {spec.low(dd) == True{} : Bool}
  {Png.px.deep(0, dd, xs, plte, [k1, k0]) == Some{spec.grey.low(dd, xs, Some{spec.u16(k1, k0)})}
    : Maybe<&2, List<&2, U32>>}

# LAW: 16-bit gray without tRNS: each sample decodes to its high byte, alpha 255
law png_px_grey16:
  for +xs: List<&2, U32>
  for +plte: List<&2, U32>
  {Png.px.deep(0, 16, xs, plte, []) == Some{spec.grey16(xs, None{})} : Maybe<&2, List<&2, U32>>}

# LAW: 16-bit gray with tRNS bytes k1, k0: alpha 0 where the 16-bit sample is k1 * 256 + k0
law png_px_grey16_key:
  for +xs: List<&2, U32>
  for +plte: List<&2, U32>
  for +k1: U32
  for +k0: U32
  {Png.px.deep(0, 16, xs, plte, [k1, k0]) == Some{spec.grey16(xs, Some{spec.u16(k1, k0)})}
    : Maybe<&2, List<&2, U32>>}

# LAW: 16-bit RGB without tRNS: each triple decodes to its high bytes, alpha 255
law png_px_rgb16:
  for +xs: List<&2, U32>
  for +plte: List<&2, U32>
  {Png.px.deep(2, 16, xs, plte, []) == spec.rgb16(xs, None{}) : Maybe<&2, List<&2, U32>>}

# LAW: 16-bit RGB with six tRNS bytes: alpha 0 where all three 16-bit samples are the key's
law png_px_rgb16_key:
  for +xs: List<&2, U32>
  for +plte: List<&2, U32>
  for +r1: U32
  for +r0: U32
  for +g1: U32
  for +g0: U32
  for +b1: U32
  for +b0: U32
  {Png.px.deep(2, 16, xs, plte, [r1, r0, g1, g0, b1, b0]) == spec.rgb16(xs, Some{Key3{spec.u16(r1, r0),
    spec.u16(g1, g0), spec.u16(b1, b0)}}) : Maybe<&2, List<&2, U32>>}

# LAW: 16-bit gray and alpha: each pair decodes to its high bytes, whatever tRNS holds
law png_px_ga16:
  for +xs: List<&2, U32>
  for +plte: List<&2, U32>
  for +trns: List<&2, U32>
  {Png.px.deep(4, 16, xs, plte, trns) == spec.ga16(xs) : Maybe<&2, List<&2, U32>>}

# LAW: 16-bit RGBA: each quadruple decodes to its high bytes, whatever tRNS holds
law png_px_rgba16:
  for +xs: List<&2, U32>
  for +plte: List<&2, U32>
  for +trns: List<&2, U32>
  {Png.px.deep(6, 16, xs, plte, trns) == spec.rgba16(xs) : Maybe<&2, List<&2, U32>>}

# LAW: indexed colour of 1, 2, 4 or 8 bits: the indices decode as at 8 bits, exactly when each is below the palette's
# entry count
law png_px_indexed_deep:
  for +dd: U32
  for +xs: List<&2, U32>
  for +plte: List<&2, U32>
  for +trns: List<&2, U32>
  for h_dd: {Bool.or(spec.low(dd), U32.is_eq(dd, 8)) == True{} : Bool}
  {Png.px.deep(3, dd, xs, plte, trns) == L1.spec.idx(xs, L1.spec.pal(plte, L1.spec.alphas(plte, trns)))
    : Maybe<&2, List<&2, U32>>}
