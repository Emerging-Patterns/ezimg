# `Crc.crc32(xs)` equals the bitwise ISO 3309 CRC-32 of `xs` for every byte
# list, and `decode_png` returns none for every input in which some chunk up
# to IEND has a stored CRC that differs from the CRC-32 of its type and data.
# Bytes after IEND are not read (laws/PngIgnoresBytesAfterIend.bend), so a
# chunk there is not checked.
import Base
import ../main.bend as Img
import ../src/crc.bend as Crc
import ./defs/PngSpecification.bend as D1

# LAW: Crc.crc32 is the bitwise ISO 3309 CRC-32, for every byte list
law crc32_bitwise:
  for xs: List<&2, U32>
  {Crc.crc32(xs) == D1.crc.ref(xs) : U32}

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

# the chunk is not IEND: its type is not 73 69 78 68 (PNG section 11.2.5)
def chunk.open(ck: Chunk) -> Bool:
  match ck:
    case Chunk{_l0, _l1, _l2, _l3, t0, t1, t2, t3, _data, _s0, _s1, _s2, _s3}:
      Bool.not(U32.is_eq(be.word(t0, t1, t2, t3), 1229278788))

# no chunk is IEND
def chunks.open(cs: List<&2, Chunk>) -> Type:
  match cs:
    case Nil{}:
      Unit
    case ck <> tl:
      {chunk.open(ck) == True{} : Bool} & chunks.open(tl)

# the CRC a chunk stores
def chunk.stored(ck: Chunk) -> U32:
  match ck:
    case Chunk{_l0, _l1, _l2, _l3, _t0, _t1, _t2, _t3, _data, s0, s1, s2, s3}:
      be.word(s0, s1, s2, s3)

# the CRC-32 of a chunk's type and data
def chunk.sum(ck: Chunk) -> U32:
  match ck:
    case Chunk{_l0, _l1, _l2, _l3, t0, t1, t2, t3, data, _s0, _s1, _s2, _s3}:
      D1.crc.ref(t0 <> t1 <> t2 <> t3 <> data)

# LAW: after the signature and any framed chunks none of which is IEND, a framed chunk whose stored CRC differs from
# the CRC-32 of its type and data makes decode_png none, whatever follows
law png_crc_refused:
  for +pre: List<&2, Chunk>
  for +bad: Chunk
  for +rest: List<&2, U32>
  for h_pre: chunks.framed(pre)
  for h_open: chunks.open(pre)
  for h_bad: chunk.framed(bad)
  for h_crc: {chunk.stored(bad) == chunk.sum(bad) : U32} -> Empty
  {Img.decode_png(List.append(&2, U32, Img.png_sig(), chunks.onto(pre, chunk.onto(bad, rest))))
    == None{} : Maybe<&2, Img.Raster>}
