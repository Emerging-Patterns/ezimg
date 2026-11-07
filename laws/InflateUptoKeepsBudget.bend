# `inflate.upto(n, xs)` is inflate with an output budget of n bytes, for a
# caller that knows how much a stream may decode to (a PNG's IDAT decodes to
# `h * (1 + w * bpp)` bytes): it stops as soon as the bytes a Huffman block
# has emitted pass n, so a hostile stream cannot make it build much more than
# the budget, and stored bytes, which cannot expand, are measured at the end.
# What it answers is inflate's answer: when it answers some bytes, inflate
# answers the same bytes for xs, and there are at most n of them.
#
# The converse, that it answers inflate's output whenever that output has at
# most n bytes, is proved for the stored streams ezimg writes
# (laws/InflateUptoReadsStoredBlocks.bend). For a stream with Huffman blocks
# it is not proved: that needs the bytes in the window to stay at most the
# final output's length at every byte, an invariant over every transition of
# the Huffman reader, which is trusted (src/inflate.bend). Comparing it with
# zlib on real streams, with the budget at and one byte under each output's
# length, exercises it, which is a test.
import Base
import ../src/inflate.bend as Inf

# LAW: when inflate.upto with a budget answers some bytes, inflate answers the same bytes
law upto_is_inflate:
  for +lim: Nat
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for h_up: {Inf.inflate.upto(lim, xs) == Some{ys} : Maybe<&2, List<&2, U32>>}
  {Inf.inflate(xs) == Some{ys} : Maybe<&2, List<&2, U32>>}

# LAW: when inflate.upto with a budget answers some bytes, there are at most the budget of them
law upto_within:
  for +lim: Nat
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for h_up: {Inf.inflate.upto(lim, xs) == Some{ys} : Maybe<&2, List<&2, U32>>}
  {Nat.is_le(List.length(&2, U32, ys), lim) == True{} : Bool}
