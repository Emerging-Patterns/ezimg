# `inflate.upto` reads the zlib streams ezimg writes: for every byte list
# `xs` shorter than 2^32 bytes, in stored blocks of any size from 1 to 65535
# (the streams laws/InflateReadsStoredBlocks.bend has inflate read), and every
# budget of at least `xs`'s length, `Inf.inflate.upto` answers `Some(xs)`, as
# `Inf.inflate` does. A stored block's bytes are read from the input one for
# one, so the budget is met by the final length check: a stream of stored
# blocks never fills the Huffman window the per-byte cap counts.
#
# This is the converse of laws/InflateUptoKeepsBudget.bend for these streams
# only. For a stream with Huffman blocks it is not proved (see there).
import Base
import ../src/inflate.bend as Inf
import ../src/png.bend as Png
import ./InflateReadsStoredBlocks.bend as L1
import ./defs/PngSpecification.bend as D1

# LAW: every byte list with fewer than 2^32 bytes, in the zlib stream ezimg writes with stored blocks of any size from 1
# to 65535, inflates under any budget of at least its length to itself
law upto_stored:
  for +lim: Nat
  for +sz: U32
  for +xs: List<&2, U32>
  for h_sz: {Bool.and(U32.is_le(1, sz), U32.is_le(sz, 65535)) == True{} : Bool}
  for h_by: {D1.bytes(xs) == True{} : Bool}
  for h_n: {U32.to_nat(Png.enc.len(xs, 0)) == List.length(&2, U32, xs) : Nat}
  for h_lim: {Nat.is_le(List.length(&2, U32, xs), lim) == True{} : Bool}
  {Inf.inflate.upto(lim, L1.zlib.stored(sz, xs)) == Some{xs} : Maybe<&2, List<&2, U32>>}

# LAW: the zlib stream enc.zlib writes for a PNG's IDAT inflates under any budget of at least its length to the bytes
# it was given
law upto_enc_zlib:
  for +lim: Nat
  for +xs: List<&2, U32>
  for h_by: {D1.bytes(xs) == True{} : Bool}
  for h_n: {U32.to_nat(Png.enc.len(xs, 0)) == List.length(&2, U32, xs) : Nat}
  for h_lim: {Nat.is_le(List.length(&2, U32, xs), lim) == True{} : Bool}
  {Inf.inflate.upto(lim, Png.enc.zlib(xs, Png.enc.len(xs, 0))) == Some{xs} : Maybe<&2, List<&2, U32>>}
