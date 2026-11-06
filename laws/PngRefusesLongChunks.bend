# `decode_png` returns none for every input in which some chunk up to IEND
# has a length field of 2^31 or more: PNG section 7.1 limits a chunk's
# length to 2^31 - 1. Until 2026-11 the decoder took any length a U32
# holds; refusing longer ones is a deliberate change.
import Base
import ../main.bend as Img
import ./CrcIsIso3309.bend as L1
import ./defs/SizeBounds.bend as D2

# LAW: after the signature and any framed chunks none of which is IEND, a length field of 2^31 or more makes
# decode_png none, whatever follows
law png_long_chunk_refused:
  for +pre: List<&2, L1.Chunk>
  for +l0: U32
  for +l1: U32
  for +l2: U32
  for +l3: U32
  for +rest: List<&2, U32>
  for h_pre: L1.chunks.framed(pre)
  for h_open: L1.chunks.open(pre)
  for h_long: {D2.below(31n, U32.to_nat(L1.be.word(l0, l1, l2, l3))) == False{} : Bool}
  {Img.decode_png(List.append(&2, U32, Img.png_sig(), L1.chunks.onto(pre, l0 <> l1 <> l2 <> l3 <> rest)))
    == None{} : Maybe<&2, Img.Raster>}
