# For every byte list `xs` shorter than 2^32 bytes and every block size from 1
# to 65535, `Inf.inflate` of the zlib stream of `xs` in stored blocks of that
# size is `Some(xs)`.
import Base
import ../src/inflate.bend as Inf
import ../src/png.bend as Png
import ./defs/PngSpecification.bend as D1

# the zlib stream ezimg writes for xs in stored blocks of at most sz bytes:
# CMF and FLG 120 1, the encoder's stored blocks, and the Adler-32 of xs
def zlib.stored(+sz: U32, +xs: List<&2, U32>) -> List<&2, U32>:
  Png.enc.cat([120, 1], Png.enc.cat(Png.enc.blocks(sz, xs), Png.enc.be(Inf.adler.of(xs))))

# LAW: every byte list with fewer than 2^32 bytes, in the zlib stream ezimg writes with stored blocks of any size from 1
# to 65535, inflates to itself
law inflate_stored:
  for +sz: U32
  for +xs: List<&2, U32>
  for h_sz: {Bool.and(U32.is_le(1, sz), U32.is_le(sz, 65535)) == True{} : Bool}
  for h_by: {D1.bytes(xs) == True{} : Bool}
  for h_n: {U32.to_nat(Png.enc.len(xs, 0)) == List.length(&2, U32, xs) : Nat}
  {Inf.inflate(zlib.stored(sz, xs)) == Some{xs} : Maybe<&2, List<&2, U32>>}

# LAW: the zlib stream enc.zlib writes for a PNG's IDAT inflates to the bytes it was given
law inflate_enc_zlib:
  for +xs: List<&2, U32>
  for h_by: {D1.bytes(xs) == True{} : Bool}
  for h_n: {U32.to_nat(Png.enc.len(xs, 0)) == List.length(&2, U32, xs) : Nat}
  {Inf.inflate(Png.enc.zlib(xs, Png.enc.len(xs, 0))) == Some{xs} : Maybe<&2, List<&2, U32>>}
