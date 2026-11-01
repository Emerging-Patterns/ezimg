# proofs of laws/InflateReadsStoredBlocks.bend
import Base
import ../laws/InflateReadsStoredBlocks.bend as Laws
import ./lemmas/ZlibStoredStream.bend as M1

def Laws.inflate_stored(sz, xs, h_sz, h_by, h_n):
  M1.inflate_stored(sz, xs, h_sz, h_by, h_n)
