# proofs of laws/CrcIsIso3309.bend
import Base
import ../main.bend as Img
import ../src/crc.bend as Crc
import ../src/png.bend as Png
import ../laws/CrcIsIso3309.bend as Laws
import ./lemmas/BasicFacts.bend as M1
import ./lemmas/CrcReference.bend as M2

# a judged chunk: a stored CRC unequal to the computed one is refused
law judge_bad:
  for zz: Bool
  for +got: U32
  for +want: U32
  for +ee: {U32.is_eq(got, want) == zz : Bool}
  for h_ne: {got == want : U32} -> Empty
  for +typ: U32
  for +data: List<&2, U32>
  for +pg: Png.Pg
  for +em: Bool
  for +rest: List<&2, U32>
  {Png.png.crc(Png.png.judge.at(zz, typ, data, pg), em, Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [],
    Png.png.pgof(Png.png.judge.at(zz, typ, data, pg)))) == None{} : Maybe<&2, Png.Pic>}

# the proof of judge_bad
def judge_bad(zz, got, want, ee, h_ne, typ, data, pg, em, rest):
  match zz:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({Png.png.crc(Png.png.judge.at(True{}, typ, data, pg), em, Png.png.go(rest, Png.ZLen{}, False{}, 0,
        0, [], [], Png.png.pgof(Png.png.judge.at(True{}, typ, data, pg)))) == None{} : Maybe<&2, Png.Pic>},
        h_ne(M1.ueq(got, want, ee)))

# a chunk whose stored CRC differs from the CRC-32 of its type and data:
# once the walker reaches its CRC bytes, the decode is none
law crc_bad:
  for +data: List<&2, U32>
  for +t0: U32
  for +t1: U32
  for +t2: U32
  for +t3: U32
  for +s0: U32
  for +s1: U32
  for +s2: U32
  for +s3: U32
  for +rest: List<&2, U32>
  for +pg: Png.Pg
  for h_ne: {Png.be.u32(s0, s1, s2, s3) == Crc.crc32(t0 <> t1 <> t2 <> t3 <> data) : U32} -> Empty
  {M2.at_crc(s0, s1, s2, s3, rest, Png.be.u32(t0, t1, t2, t3), List.reverse.go(&2, U32, data, [t3, t2, t1, t0]),
    List.reverse.go(&2, U32, data, []), pg) == None{} : Maybe<&2, Png.Pic>}

# the proof of crc_bad
def crc_bad(data, t0, t1, t2, t3, s0, s1, s2, s3, rest, pg, h_ne):
  +got = Png.be.u32(s0, s1, s2, s3)
  +want = Crc.crc32(List.reverse(&2, U32, List.reverse.go(&2, U32, data, [t3, t2, t1, t0])))
  judge_bad(U32.is_eq(got, want), got, want, {==},
    ee => h_ne(Equal.trans(U32, got, want, Crc.crc32(t0 <> t1 <> t2 <> t3 <> data), ee,
      Equal.cong(List<&2, U32>, U32, xs => Crc.crc32(xs),
        List.reverse(&2, U32, List.reverse.go(&2, U32, data, [t3, t2, t1, t0])), t0 <> t1 <> t2 <> t3 <> data,
        M2.crc_bytes(data, t0, t1, t2, t3)))),
    Png.be.u32(t0, t1, t2, t3), List.reverse.go(&2, U32, data, []), pg, List.is_empty(&2, U32, rest), rest)

# a judged chunk with more bytes after it: whatever the judgement, the decode
# is none when the walk over the rest is none
law judge_more:
  for em: Bool
  for +he: {em == False{} : Bool}
  for nx: Png.Nx
  for +rest: List<&2, U32>
  for ih: {Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], Png.png.pgof(nx)) == None{} : Maybe<&2, Png.Pic>}
  {Png.png.crc(nx, em, Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], Png.png.pgof(nx)))
    == None{} : Maybe<&2, Png.Pic>}

# the proof of judge_more
def judge_more(em, he, nx, rest, ih):
  match em:
    case True{}:
      Empty.absurd({Png.png.crc(nx, True{}, Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], Png.png.pgof(nx)))
        == None{} : Maybe<&2, Png.Pic>}, M1.true_false(he))
    case False{}:
      match nx:
        case Png.NBad{}:
          {==}
        case Png.NEnd{_pg}:
          {==}
        case Png.NMore{_pg}:
          ih

# ---- chunks as the laws lay them out ----

# a chunk's bytes are never empty
law chunk_full:
  for ck: Laws.Chunk
  for rest: List<&2, U32>
  {List.is_empty(&2, U32, Laws.chunk.onto(ck, rest)) == False{} : Bool}

# the proof of chunk_full
def chunk_full(ck, _rest):
  match ck:
    case Laws.Chunk{_l0, _l1, _l2, _l3, _t0, _t1, _t2, _t3, _data, _s0, _s1, _s2, _s3}:
      {==}

# chunks before a chunk are never empty
law chunks_full:
  for cs: List<&2, Laws.Chunk>
  for ck: Laws.Chunk
  for rest: List<&2, U32>
  {List.is_empty(&2, U32, Laws.chunks.onto(cs, Laws.chunk.onto(ck, rest))) == False{} : Bool}

# the proof of chunks_full
def chunks_full(cs, ck, rest):
  match cs:
    case Nil{}:
      chunk_full(ck, rest)
    case hd <> tl:
      chunk_full(hd, Laws.chunks.onto(tl, Laws.chunk.onto(ck, rest)))

# a chunk walked to its CRC and refused, the CRC it should store named sum
law walk_bad.at:
  for +l0: U32
  for +l1: U32
  for +l2: U32
  for +l3: U32
  for +t0: U32
  for +t1: U32
  for +t2: U32
  for +t3: U32
  for +data: List<&2, U32>
  for +s0: U32
  for +s1: U32
  for +s2: U32
  for +s3: U32
  for +rest: List<&2, U32>
  for +pg: Png.Pg
  for +hn: {U32.to_nat(Png.be.u32(l0, l1, l2, l3)) == List.length(&2, U32, data) : Nat}
  for +sum: U32
  for +es: {Crc.crc32(t0 <> t1 <> t2 <> t3 <> data) == sum : U32}
  for h_ne: {Png.be.u32(s0, s1, s2, s3) == sum : U32} -> Empty
  {Png.png.go(l0 <> l1 <> l2 <> l3 <> t0 <> t1 <> t2 <> t3 <> List.append(&2, U32, data, s0 <> s1 <> s2 <> s3 <> rest),
    Png.ZLen{}, False{}, 0, 0, [], [], pg) == None{} : Maybe<&2, Png.Pic>}

# the proof of walk_bad.at
def walk_bad.at(l0, l1, l2, l3, t0, t1, t2, t3, data, s0, s1, s2, s3, rest, pg, hn, sum, es, h_ne):
  Equal.trans(Maybe<&2, Png.Pic>,
    Png.png.go(l0 <> l1 <> l2 <> l3 <> t0 <> t1 <> t2 <> t3 <> List.append(&2, U32, data, s0 <> s1 <> s2 <> s3 <> rest),
      Png.ZLen{}, False{}, 0, 0, [], [], pg),
    M2.at_crc(s0, s1, s2, s3, rest, Png.be.u32(t0, t1, t2, t3), List.reverse.go(&2, U32, data, [t3, t2, t1, t0]),
      List.reverse.go(&2, U32, data, []), pg),
    None{},
    M2.walk_chunk(l0, l1, l2, l3, t0, t1, t2, t3, data, s0, s1, s2, s3, rest, pg, hn),
    crc_bad(data, t0, t1, t2, t3, s0, s1, s2, s3, rest, pg,
      ee => h_ne(Equal.trans(U32, Png.be.u32(s0, s1, s2, s3), Crc.crc32(t0 <> t1 <> t2 <> t3 <> data), sum, ee, es))))

# the bad chunk itself: walked to its CRC and refused
law walk_bad:
  for +bad: Laws.Chunk
  for +rest: List<&2, U32>
  for +pg: Png.Pg
  for h_bad: Laws.chunk.framed(bad)
  for h_crc: {Laws.chunk.stored(bad) == Laws.chunk.sum(bad) : U32} -> Empty
  {Png.png.go(Laws.chunk.onto(bad, rest), Png.ZLen{}, False{}, 0, 0, [], [], pg) == None{} : Maybe<&2, Png.Pic>}

# the proof of walk_bad
def walk_bad(bad, rest, pg, h_bad, h_crc):
  match bad:
    case Laws.Chunk{+l0, +l1, +l2, +l3, +t0, +t1, +t2, +t3, +data, +s0, +s1, +s2, +s3}:
      walk_bad.at(l0, l1, l2, l3, t0, t1, t2, t3, data, s0, s1, s2, s3, rest, pg, h_bad,
        Laws.chunk.sum(Laws.Chunk{l0, l1, l2, l3, t0, t1, t2, t3, data, s0, s1, s2, s3}),
        M2.crc32_ref(t0 <> t1 <> t2 <> t3 <> data), h_crc)

# a chunk before the bad one: walked to its CRC and judged; whatever the
# judgement, more bytes follow, so the decode is none when the walk over them is
law walk_pass:
  for +ck: Laws.Chunk
  for +rest: List<&2, U32>
  for +pg: Png.Pg
  for h_ck: Laws.chunk.framed(ck)
  for +full: {List.is_empty(&2, U32, rest) == False{} : Bool}
  for ih: @pp: Png.Pg -> {Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], pp) == None{} : Maybe<&2, Png.Pic>}
  {Png.png.go(Laws.chunk.onto(ck, rest), Png.ZLen{}, False{}, 0, 0, [], [], pg) == None{} : Maybe<&2, Png.Pic>}

# the proof of walk_pass
def walk_pass(ck, rest, pg, h_ck, full, ih):
  match ck:
    case Laws.Chunk{+l0, +l1, +l2, +l3, +t0, +t1, +t2, +t3, +data, +s0, +s1, +s2, +s3}:
      +nx = {Png.png.judge(Png.be.u32(s0, s1, s2, s3), List.reverse.go(&2, U32, data, [t3, t2, t1, t0]),
        Png.be.u32(t0, t1, t2, t3), List.reverse.go(&2, U32, data, []), pg) : Png.Nx}
      Equal.trans(Maybe<&2, Png.Pic>,
        Png.png.go(Laws.chunk.onto(Laws.Chunk{l0, l1, l2, l3, t0, t1, t2, t3, data, s0, s1, s2, s3}, rest),
          Png.ZLen{}, False{}, 0, 0, [], [], pg),
        M2.at_crc(s0, s1, s2, s3, rest, Png.be.u32(t0, t1, t2, t3), List.reverse.go(&2, U32, data, [t3, t2, t1, t0]),
          List.reverse.go(&2, U32, data, []), pg),
        None{},
        M2.walk_chunk(l0, l1, l2, l3, t0, t1, t2, t3, data, s0, s1, s2, s3, rest, pg, h_ck),
        judge_more(List.is_empty(&2, U32, rest), full, nx, rest, ih(Png.png.pgof(nx))))

# every chunk before the bad one: walked to its CRC, and then either refused,
# ended with bytes still to come, or on to the next chunk
law walk_all:
  for +pre: List<&2, Laws.Chunk>
  for +bad: Laws.Chunk
  for +rest: List<&2, U32>
  for +pg: Png.Pg
  for h_pre: Laws.chunks.framed(pre)
  for h_bad: Laws.chunk.framed(bad)
  for h_crc: {Laws.chunk.stored(bad) == Laws.chunk.sum(bad) : U32} -> Empty
  {Png.png.go(Laws.chunks.onto(pre, Laws.chunk.onto(bad, rest)), Png.ZLen{}, False{}, 0, 0, [], [], pg)
    == None{} : Maybe<&2, Png.Pic>}

# the proof of walk_all
def walk_all(pre, bad, rest, pg, h_pre, h_bad, h_crc):
  match pre:
    case Nil{}:
      walk_bad(bad, rest, pg, h_bad, h_crc)
    case +ck <> +tl:
      (h_ck, h_tl) = h_pre
      walk_pass(ck, Laws.chunks.onto(tl, Laws.chunk.onto(bad, rest)), pg, h_ck, chunks_full(tl, bad, rest),
        pp => walk_all(tl, bad, rest, pp, h_tl, h_bad, h_crc))

def Laws.crc32_bitwise(xs):
  M2.crc32_ref(xs)

def Laws.png_crc_refused(pre, bad, rest, h_pre, h_bad, h_crc):
  Equal.cong(Maybe<&2, Png.Pic>, Maybe<&2, Img.Raster>, mm => Img.decode_png.pic(mm),
    Png.png.go(Laws.chunks.onto(pre, Laws.chunk.onto(bad, rest)), Png.ZLen{}, False{}, 0, 0, [], [], Png.pg.empty()),
    None{}, walk_all(pre, bad, rest, Png.pg.empty(), h_pre, h_bad, h_crc))
