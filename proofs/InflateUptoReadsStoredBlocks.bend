# proofs of laws/InflateUptoReadsStoredBlocks.bend: the stored-block walk of
# proofs/lemmas/ZlibStoredStream.bend holds under any budget, which the
# stream then meets at its final length check
import Base
import ../laws/InflateUptoReadsStoredBlocks.bend as Laws
import ./lemmas/ZlibStoredStream.bend as M1

def Laws.upto_stored(lim, sz, xs, h_sz, h_by, h_n, h_lim):
  M1.upto_stored(lim, sz, xs, h_sz, h_by, h_n, h_lim)

def Laws.upto_enc_zlib(lim, xs, h_by, h_n, h_lim):
  M1.upto_stored(lim, 65535, xs, {==}, h_by, h_n, h_lim)
