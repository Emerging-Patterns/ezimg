# proofs of laws/PngRefusesLongChunks.bend
import Base
import ../main.bend as Img
import ../src/png.bend as Png
import ../laws/PngRefusesLongChunks.bend as Laws
import ../laws/CrcIsIso3309.bend as L1
import ../laws/defs/SizeBounds.bend as D2
import ./CrcIsIso3309.bend as P1
import ./lemmas/CrcReference.bend as M2
import ./lemmas/PngEncoderArithmetic.bend as M3

# the long length field itself: the walker refuses there
def long.at(
  +l0: U32,
  +l1: U32,
  +l2: U32,
  +l3: U32,
  +rest: List<&2, U32>,
  +pg: Png.Pg,
  h_long: {D2.below(31n, U32.to_nat(L1.be.word(l0, l1, l2, l3))) == False{} : Bool}
) -> {Png.png.go(l0 <> l1 <> l2 <> l3 <> rest, Png.ZLen{}, False{}, 0, 0, [], [], pg) == None{} : Maybe<&2, Png.Pic>}:
  +ln = Png.be.u32(l0, l1, l2, l3)
  M2.walk_long(l0, l1, l2, l3, rest, pg, Equal.trans(Bool, Png.png.short(ln), D2.below(31n, U32.to_nat(ln)), False{},
    M3.short.nat(ln), h_long))

# every chunk before the long one: walked to its CRC and then refused, ended
# with bytes still to come, or on to the next chunk
law long.all:
  for +pre: List<&2, L1.Chunk>
  for +l0: U32
  for +l1: U32
  for +l2: U32
  for +l3: U32
  for +rest: List<&2, U32>
  for +pg: Png.Pg
  for h_pre: L1.chunks.framed(pre)
  for h_open: L1.chunks.open(pre)
  for h_long: {D2.below(31n, U32.to_nat(L1.be.word(l0, l1, l2, l3))) == False{} : Bool}
  {Png.png.go(L1.chunks.onto(pre, l0 <> l1 <> l2 <> l3 <> rest), Png.ZLen{}, False{}, 0, 0, [], [], pg)
    == None{} : Maybe<&2, Png.Pic>}

# the proof of long.all
def long.all(pre, l0, l1, l2, l3, rest, pg, h_pre, h_open, h_long):
  match pre:
    case Nil{}:
      long.at(l0, l1, l2, l3, rest, pg, h_long)
    case +ck <> +tl:
      (h_ck, h_tl) = h_pre
      (h_op, h_ot) = h_open
      P1.walk_pass(ck, L1.chunks.onto(tl, l0 <> l1 <> l2 <> l3 <> rest), pg, h_ck, h_op,
        pp => long.all(tl, l0, l1, l2, l3, rest, pp, h_tl, h_ot, h_long))

def Laws.png_long_chunk_refused(pre, l0, l1, l2, l3, rest, h_pre, h_open, h_long):
  Equal.cong(Maybe<&2, Png.Pic>, Maybe<&2, Img.Raster>, mm => Img.decode_png.pic(mm),
    Png.png.go(L1.chunks.onto(pre, l0 <> l1 <> l2 <> l3 <> rest), Png.ZLen{}, False{}, 0, 0, [], [], Png.pg.empty()),
    None{}, long.all(pre, l0, l1, l2, l3, rest, Png.pg.empty(), h_pre, h_open, h_long))
