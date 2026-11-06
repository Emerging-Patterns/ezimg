# the PNG file layout, the bitwise CRC-32 and the sample packing, as the
# specifications state them
import Base
import ../../main.bend as Img
import ../../src/png.bend as Png
import ./SizeBounds.bend as D2

# ok, and every sample of px has alpha 255
def all.opaque(px: List<&2, U32>, ok: Bool) -> Bool:
  match px:
    case Nil{}:
      ok
    case pp <> rest:
      all.opaque(rest, Bool.and(U32.is_eq(U32.shrn(pp, 24n), 255), ok))

# every value is at most 255, and `ok` carries that forward
def bytes.go(xs: List<&2, U32>, ok: Bool) -> Bool:
  match xs ok:
    case _xs False{}:
      False{}
    case Nil{} True{}:
      True{}
    case +xx <> tl True{}:
      bytes.go(tl, U32.is_le(xx, 255))

# every value of xs is a byte, 0 to 255
def bytes(xs: List<&2, U32>) -> Bool:
  bytes.go(xs, True{})

# the ISO 3309 / ITU-T V.42 CRC-32 polynomial, reflected (PNG section 5.5
# and Annex D): 0xEDB88320
def crc.ref.poly() -> U32:
  3988292384

# one bit, as the specification's sample code does it: when the low bit of
# the register is set, shift right and xor in the polynomial; else shift right
def crc.ref.shift(odd: Bool, +cc: U32) -> U32:
  match odd:
    case True{}:
      ((cc >> 1n : U32) .^. crc.ref.poly() : U32)
    case False{}:
      (cc >> 1n : U32)

# one bit step of the register, low bit first. The register is taken apart
# first, so a register the checker cannot compute stays one stuck match
# instead of being copied into both the test and the shift at every step
def crc.ref.step(cc: U32) -> U32:
  match cc:
    case U32{+ww}:
      crc.ref.shift(U32.is_eq((U32{ww} .&. 1 : U32), 1), U32{ww})

# nn bit steps
def crc.ref.bits(nn: Nat, +cc: U32) -> U32:
  match nn:
    case 0n:
      cc
    case 1n+pp:
      crc.ref.bits(pp, crc.ref.step(cc))

# one byte: xor it into the register, then eight bit steps. Bytes are U32 in
# ezimg and the byte is xored in whole, so for 0 to 255 this is ISO 3309
def crc.ref.byte(+cc: U32, +bb: U32) -> U32:
  crc.ref.bits(8n, (cc .^. bb : U32))

# every byte in order, the register still inverted
def crc.ref.fold(xs: List<&2, U32>, +cc: U32) -> U32:
  match xs:
    case Nil{}:
      cc
    case +bb <> tl:
      crc.ref.fold(tl, crc.ref.byte(cc, bb))

# the bitwise CRC-32: register preset to all ones, all ones xored at the end
def crc.ref(xs: List<&2, U32>) -> U32:
  (crc.ref.fold(xs, 4294967295) .^. 4294967295 : U32)

# the four bytes of a U32, most significant first
def spec.be4(+nn: U32) -> List<&2, U32>:
  [U32.and(255, U32.shrn(nn, 24n)), U32.and(255, U32.shrn(nn, 16n)), U32.and(255, U32.shrn(nn, 8n)), U32.and(255, nn)]

# the colour types the PNG specification defines for bit depth 8
def spec.colour.ok(+cc: U32) -> Bool:
  Bool.or(U32.is_eq(cc, 0), Bool.or(U32.is_eq(cc, 2), Bool.or(U32.is_eq(cc, 3), Bool.or(U32.is_eq(cc, 4),
    U32.is_eq(cc, 6)))))

# the colour types and bit depths of PNG table 11.1 (W3C PNG, third
# edition, section 11.2.1): gray (0) at 1, 2, 4, 8 and 16 bits, RGB (2) at
# 8 and 16, indexed colour (3) at 1, 2, 4 and 8, gray with alpha (4) at 8
# and 16, and RGB with alpha (6) at 8 and 16. No other pairing is a PNG
def spec.depth.ok(+cc: U32, +dd: U32) -> Bool:
  +grey = Bool.or(U32.is_eq(dd, 1), Bool.or(U32.is_eq(dd, 2), Bool.or(U32.is_eq(dd, 4), Bool.or(U32.is_eq(dd, 8),
    U32.is_eq(dd, 16)))))
  +wide = Bool.or(U32.is_eq(dd, 8), U32.is_eq(dd, 16))
  +index = Bool.or(U32.is_eq(dd, 1), Bool.or(U32.is_eq(dd, 2), Bool.or(U32.is_eq(dd, 4), U32.is_eq(dd, 8))))
  Bool.or(Bool.and(grey, U32.is_eq(cc, 0)), Bool.or(Bool.and(wide, U32.is_eq(cc, 2)),
    Bool.or(Bool.and(index, U32.is_eq(cc, 3)), Bool.or(Bool.and(wide, U32.is_eq(cc, 4)),
      Bool.and(wide, U32.is_eq(cc, 6))))))

# the interlace methods PNG section 8.1 defines: 0, none, and 1, Adam7
def spec.inter.ok(+ii: U32) -> Bool:
  Bool.or(U32.is_eq(ii, 0), U32.is_eq(ii, 1))

# the samples of the unfiltered bytes, when the scanlines unfilter
def spec.px.then(
  mm: Maybe<&2, List<&2, U32>>,
  +colour: U32,
  plte: List<&2, U32>,
  trns: List<&2, U32>
) -> Maybe<&2, List<&2, U32>>:
  match mm:
    case None{}:
      None{}
    case Some{raw}:
      Png.px.of(colour, raw, plte, trns)

# a sample's alpha is 255: its top byte, shifted down, is 255
def opaque(cc: U32) -> Bool:
  U32.is_eq(U32.shrn(cc, 24n), 255)

# every sample's alpha is 255
def all_opaque(px: List<&2, U32>) -> Bool:
  List.all(~&2, ~U32, ~opaque, px)

# a chunk as PNG section 5.3 lays it out, then rest: the length of the data,
# the four type bytes, the data, and the CRC-32 of the type and the data, the
# length and the CRC four bytes each, most significant first
def spec.chunk(+typ: List<&2, U32>, +data: List<&2, U32>, rest: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, spec.be4(U32.from_nat(List.length(&2, U32, data))), List.append(&2, U32, typ,
    List.append(&2, U32, data, List.append(&2, U32, spec.be4(crc.ref(List.append(&2, U32, typ, data))), rest))))

# a chunk that may be left out, then rest
def spec.chunk.opt(+typ: List<&2, U32>, mm: Maybe<&2, List<&2, U32>>, rest: List<&2, U32>) -> List<&2, U32>:
  match mm:
    case None{}:
      rest
    case Some{data}:
      spec.chunk(typ, data, rest)

# one IDAT chunk for each list of bytes, in order, then rest
def spec.idats(ds: List<&2, List<&2, U32>>, rest: List<&2, U32>) -> List<&2, U32>:
  match ds:
    case Nil{}:
      rest
    case data <> tl:
      spec.chunk([73, 68, 65, 84], data, spec.idats(tl, rest))

# the IHDR data: width, height, bit depth 8, the colour type, and compression,
# filter and interlace methods 0
def spec.ihdr.data(+ww: U32, +hh: U32, +cc: U32) -> List<&2, U32>:
  List.append(&2, U32, spec.be4(ww), List.append(&2, U32, spec.be4(hh), [8, cc, 0, 0, 0]))

# a PNG file in the order PNG section 5.6 gives, then rest: the signature,
# IHDR, PLTE if there is one, tRNS if there is one, the IDAT chunks, IEND,
# and the bytes of rest after IEND
def spec.png.then(
  +ww: U32,
  +hh: U32,
  +cc: U32,
  plte: Maybe<&2, List<&2, U32>>,
  trns: Maybe<&2, List<&2, U32>>,
  idats: List<&2, List<&2, U32>>,
  rest: List<&2, U32>
) -> List<&2, U32>:
  List.append(&2, U32, Img.png_sig(), spec.chunk([73, 72, 68, 82], spec.ihdr.data(ww, hh, cc),
    spec.chunk.opt([80, 76, 84, 69], plte, spec.chunk.opt([116, 82, 78, 83], trns,
      spec.idats(idats, spec.chunk([73, 69, 78, 68], [], rest))))))

# a PNG file in the order PNG section 5.6 gives, with nothing after IEND
def spec.png(
  +ww: U32,
  +hh: U32,
  +cc: U32,
  plte: Maybe<&2, List<&2, U32>>,
  trns: Maybe<&2, List<&2, U32>>,
  idats: List<&2, List<&2, U32>>
) -> List<&2, U32>:
  spec.png.then(ww, hh, cc, plte, trns, idats, [])

# a list a chunk's data may be: its length, counted in a U32, does not wrap,
# and it is below 2^31, the bound PNG section 7.1 puts on a chunk's length
def spec.fits(xs: List<&2, U32>) -> Type:
  {U32.to_nat(U32.from_nat(List.length(&2, U32, xs))) == List.length(&2, U32, xs) : Nat} &
    {D2.below(31n, List.length(&2, U32, xs)) == True{} : Bool}

# a width or height IHDR may give: from 1 to 2^31 - 1 (PNG section 11.2.1)
def spec.side(+nn: U32) -> Bool:
  Bool.and(U32.is_gt(nn, 0), D2.below(31n, U32.to_nat(nn)))

# a chunk that may be left out fits
def spec.fits.opt(mm: Maybe<&2, List<&2, U32>>) -> Type:
  match mm:
    case None{}:
      Unit
    case Some{xs}:
      spec.fits(xs)

# every list fits
def spec.fits.all(ds: List<&2, List<&2, U32>>) -> Type:
  match ds:
    case Nil{}:
      Unit
    case xs <> tl:
      spec.fits(xs) & spec.fits.all(tl)

# a palette's length is a multiple of 3 from 3 to 768: 1 to 256 entries
def spec.pal.len(xs: List<&2, U32>) -> Bool:
  +nn = U32.from_nat(List.length(&2, U32, xs))
  Bool.and(U32.is_gt(nn, 0), Bool.and(U32.is_zero((nn % 3 : U32)), U32.is_le(nn, 768)))

# PLTE (PNG section 11.2.3): colour type 3 needs one; it may appear for colour
# types 2, 3 and 6, with a palette's length
def spec.plte.ok(+cc: U32, mm: Maybe<&2, List<&2, U32>>) -> Bool:
  match mm:
    case None{}:
      Bool.not(U32.is_eq(cc, 3))
    case Some{xs}:
      Bool.and(Bool.or(U32.is_eq(cc, 2), Bool.or(U32.is_eq(cc, 3), U32.is_eq(cc, 6))), spec.pal.len(xs))

# tRNS (PNG section 11.3.2.1): it may appear for colour types 0 and 2, and for
# colour type 3 after a PLTE
def spec.trns.ok(+cc: U32, plte: Maybe<&2, List<&2, U32>>, trns: Maybe<&2, List<&2, U32>>) -> Bool:
  match trns:
    case None{}:
      True{}
    case Some{_xs}:
      Bool.or(Bool.or(U32.is_eq(cc, 0), U32.is_eq(cc, 2)), Bool.and(U32.is_eq(cc, 3), Maybe.is_some(&2, List<&2, U32>,
        plte)))

# a chunk's data, or no bytes when it is left out
def spec.or.nil(mm: Maybe<&2, List<&2, U32>>) -> List<&2, U32>:
  match mm:
    case None{}:
      []
    case Some{xs}:
      xs

# a raster of the samples when there are exactly h * w of them, counted as
# natural numbers: h rows of w
def spec.raster.keep(ok: Bool, +ww: U32, +hh: U32, px: List<&2, U32>) -> Maybe<&2, Img.Raster>:
  match ok:
    case True{}:
      Some{Img.raster(ww, hh, px)}
    case False{}:
      None{}

# a raster of the samples, when there are some and they are h * w
def spec.raster(mm: Maybe<&2, List<&2, U32>>, +ww: U32, +hh: U32) -> Maybe<&2, Img.Raster>:
  match mm:
    case None{}:
      None{}
    case Some{+px}:
      spec.raster.keep(Nat.is_eq(List.length(&2, U32, px), Nat.mul(U32.to_nat(hh), U32.to_nat(ww))), ww, hh, px)

# the pixel stage's raster from the inflated data: the scanlines unfiltered,
# then packed by px.of for the colour type, PLTE and tRNS; none when the data
# does not inflate or a stage refuses
def spec.decoded(
  mm: Maybe<&2, List<&2, U32>>,
  +ww: U32,
  +hh: U32,
  +cc: U32,
  plte: List<&2, U32>,
  trns: List<&2, U32>
) -> Maybe<&2, Img.Raster>:
  match mm:
    case None{}:
      None{}
    case Some{raw}:
      spec.raster(spec.px.then(Png.unfilter(raw, ww, hh, Png.png.bpp(cc)), cc, plte, trns), ww, hh)
