# ezimg: the laws. Each law carries the SPEC.md row it proves, or proves part
# of, on its own comment line. PROOF.bend fills them; `bend PROOF.bend` is the
# gate. Every row is pending: the 85 closed laws that stood here were retired
# (docs/rfc/ezimg-law-inventory.md keeps what each one pointed toward), and
# the quantified laws land row by row. The imports keep every module under
# the gate's checker until laws reach them.
import Base
import ./main.bend as Img
import ./src/crc.bend as Crc
import ./src/inflate.bend as Inf
import ./src/png.bend as Png
import ./src/jpeg.bend as Jpeg
import ./src/jpeg_enc.bend as Jenc

# LAW: every sample Jpeg.rgb packs is opaque, for every Y, Cb and Cr
# IMG-PIX-1
law jpeg_rgb_opaque:
  for +yy: U32
  for +cb: U32
  for +cr: U32
  {U32.shrn(Jpeg.rgb(yy, cb, cr), 24n) == 255 : U32}

# LAW: every sample Jpeg.gray packs is opaque, for every level
# IMG-PIX-1
law jpeg_gray_opaque:
  for +yy: U32
  {U32.shrn(Jpeg.gray(yy), 24n) == 255 : U32}

# LAW: encode_jpeg refuses exactly the rasters encode_png refuses
# IMG-JPG-4
law jpeg_png_refuse_alike:
  for +img: Img.Raster
  {Maybe.is_none(&2, List<&2, U32>, Img.encode_jpeg(img)) ==
    Maybe.is_none(&2, List<&2, U32>, Img.encode_png(img)) : Bool}

# every sample's colour, alpha cleared: the specification's own copy
def alpha.drop(px: List<&2, U32>) -> List<&2, U32>:
  match px:
    case Nil{}:
      Nil{}
    case pp <> rest:
      U32.and(16777215, pp) <> alpha.drop(rest)

# LAW: two rasters of one size whose samples differ only in alpha encode to the same JPEG bytes
# IMG-PIX-2
law jpeg_alpha_blind:
  for +ww: U32
  for +hh: U32
  for +pa: List<&2, U32>
  for +pb: List<&2, U32>
  for +same: {alpha.drop(pa) == alpha.drop(pb) : List<&2, U32>}
  {Img.encode_jpeg(Img.raster(ww, hh, pa)) == Img.encode_jpeg(Img.raster(ww, hh, pb)) : Maybe<&2, List<&2, U32>>}

# a sample through a function, or none
def opt.map(~ff: U32 -> U32, mm: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match mm:
    case None{}:
      None{}
    case Some{vv}:
      Some{ff(vv)}

# LAW: map keeps the width and the height
# IMG-RAS-5
law map_size:
  for ~ff: U32 -> U32
  for +img: Img.Raster
  {Img.size(Img.map(~ff, img)) == Img.size(img) : U32 & U32}

# LAW: sample k of map(f, r) is f of sample k of r, for every k, and none past the end
# IMG-RAS-5
law map_at:
  for ~ff: U32 -> U32
  for +img: Img.Raster
  for +kk: Nat
  {List.get(&2, U32, Img.pixels(Img.map(~ff, img)), kk) ==
    opt.map(~ff, List.get(&2, U32, Img.pixels(img), kk)) : Maybe<&2, U32>}

# LAW: bytes that open with the eight signature bytes parse as the signature, whatever follows
# IMG-PNG-1
law sig_opens:
  for +rest: List<&2, U32>
  {Img.parse_signature(List.append(&2, U32, Img.png_sig(), rest)) == Some{Img.png_sig()} : Maybe<&2, List<&2, U32>>}

# LAW: parse_signature is some only when the bytes open with the eight signature bytes
# IMG-PNG-1
law sig_only:
  for +xs: List<&2, U32>
  for h_some: {Maybe.is_some(&2, List<&2, U32>, Img.parse_signature(xs)) == True{} : Bool}
  {xs == List.append(&2, U32, Img.png_sig(), List.drop(&2, U32, xs, 8n)) : List<&2, U32>}

# ---- wp1-crc ----

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

# LAW: Crc.crc32 is the bitwise ISO 3309 CRC-32, for every byte list
# IMG-PNG-5
law crc32_bitwise:
  for xs: List<&2, U32>
  {Crc.crc32(xs) == crc.ref(xs) : U32}

# a PNG chunk as bytes (PNG section 5.3): the four length bytes, the four
# chunk type bytes, the data, and the four CRC bytes
type Chunk is Data:
  Chunk{
    +l0: U32, +l1: U32, +l2: U32, +l3: U32, +t0: U32, +t1: U32, +t2: U32, +t3: U32, +data: List<&2, U32>,
    +s0: U32, +s1: U32, +s2: U32, +s3: U32
  }

# four bytes read as one number, most significant byte first (PNG section 7.1)
def be.word(+aa: U32, +bb: U32, +cc: U32, +dd: U32) -> U32:
  ((((aa << 24n : U32) .|. (bb << 16n : U32) : U32) .|. (cc << 8n : U32) : U32) .|. dd : U32)

# a chunk's bytes, then rest
def chunk.onto(ck: Chunk, rest: List<&2, U32>) -> List<&2, U32>:
  match ck:
    case Chunk{l0, l1, l2, l3, t0, t1, t2, t3, data, s0, s1, s2, s3}:
      l0 <> l1 <> l2 <> l3 <> t0 <> t1 <> t2 <> t3 <> List.append(&2, U32, data, s0 <> s1 <> s2 <> s3 <> rest)

# chunks' bytes one after another, then rest
def chunks.onto(cs: List<&2, Chunk>, rest: List<&2, U32>) -> List<&2, U32>:
  match cs:
    case Nil{}:
      rest
    case ck <> tl:
      chunk.onto(ck, chunks.onto(tl, rest))

# the chunk's length field counts its data bytes
def chunk.framed(ck: Chunk) -> Type:
  match ck:
    case Chunk{l0, l1, l2, l3, _t0, _t1, _t2, _t3, data, _s0, _s1, _s2, _s3}:
      {U32.to_nat(be.word(l0, l1, l2, l3)) == List.length(&2, U32, data) : Nat}

# every chunk's length field counts its data bytes
def chunks.framed(cs: List<&2, Chunk>) -> Type:
  match cs:
    case Nil{}:
      Unit
    case ck <> tl:
      chunk.framed(ck) & chunks.framed(tl)

# the CRC a chunk stores
def chunk.stored(ck: Chunk) -> U32:
  match ck:
    case Chunk{_l0, _l1, _l2, _l3, _t0, _t1, _t2, _t3, _data, s0, s1, s2, s3}:
      be.word(s0, s1, s2, s3)

# the CRC-32 of a chunk's type and data
def chunk.sum(ck: Chunk) -> U32:
  match ck:
    case Chunk{_l0, _l1, _l2, _l3, t0, t1, t2, t3, data, _s0, _s1, _s2, _s3}:
      crc.ref(t0 <> t1 <> t2 <> t3 <> data)

# LAW: after the signature and any framed chunks, a framed chunk whose stored CRC differs from the CRC-32 of its type
# and data makes decode_png none, whatever follows
# IMG-PNG-5
law png_crc_refused:
  for +pre: List<&2, Chunk>
  for +bad: Chunk
  for +rest: List<&2, U32>
  for h_pre: chunks.framed(pre)
  for h_bad: chunk.framed(bad)
  for h_crc: {chunk.stored(bad) == chunk.sum(bad) : U32} -> Empty
  {Img.decode_png(List.append(&2, U32, Img.png_sig(), chunks.onto(pre, chunk.onto(bad, rest))))
    == None{} : Maybe<&2, Img.Raster>}
