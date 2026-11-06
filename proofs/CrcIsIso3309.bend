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
  for +rest: List<&2, U32>
  {Png.png.crc(Png.png.judge.at(zz, typ, data, pg), _u => Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [],
    Png.png.pgof(Png.png.judge.at(zz, typ, data, pg)))) == None{} : Maybe<&2, Png.Pic>}

# the proof of judge_bad
def judge_bad(zz, got, want, ee, h_ne, typ, data, pg, rest):
  match zz:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({Png.png.crc(Png.png.judge.at(True{}, typ, data, pg), _u => Png.png.go(rest, Png.ZLen{}, False{}, 0,
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
    Png.be.u32(t0, t1, t2, t3), List.reverse.go(&2, U32, data, []), pg, rest)

# the judgement ended the image: IEND was taken
def nx.ends(nx: Png.Nx) -> Bool:
  match nx:
    case Png.NBad{}:
      False{}
    case Png.NEnd{_pg}:
      True{}
    case Png.NMore{_pg}:
      False{}

# a judged chunk that did not end the image: the decode is none when the walk
# over the rest is none
law judge_more:
  for nx: Png.Nx
  for +ne: {nx.ends(nx) == False{} : Bool}
  for +rest: List<&2, U32>
  for ih: {Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], Png.png.pgof(nx)) == None{} : Maybe<&2, Png.Pic>}
  {Png.png.crc(nx, _u => Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], Png.png.pgof(nx)))
    == None{} : Maybe<&2, Png.Pic>}

# the proof of judge_more
def judge_more(nx, ne, rest, ih):
  match nx:
    case Png.NBad{}:
      {==}
    case Png.NEnd{+pg}:
      Empty.absurd({Png.png.crc(Png.NEnd{pg}, _u => Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [],
        Png.png.pgof(Png.NEnd{pg}))) == None{} : Maybe<&2, Png.Pic>}, M1.true_false(ne))
    case Png.NMore{_pg}:
      ih

# ---- a chunk that is not IEND never ends the image ----

# a guarded state is not an end
def open.allow(zz: Bool, +pg: Png.Pg) -> {nx.ends(Png.png.allow(zz, pg)) == False{} : Bool}:
  match zz:
    case True{}:
      {==}
    case False{}:
      {==}

# an IHDR's fields, good or not, do not end the image
def open.ihdr.ok(
  zz: Bool,
  +ww: U32,
  +hh: U32,
  +dd: U32,
  +cc: U32,
  +comp: U32,
  +ff: U32,
  +ii: U32
) -> {nx.ends(Png.png.ihdr.ok(zz, ww, hh, dd, cc, comp, ff, ii)) == False{} : Bool}:
  match zz:
    case True{}:
      {==}
    case False{}:
      {==}

# an IHDR, parsed or not, does not end the image
def open.ihdr.put(mm: Maybe<&2, Png.Ihdr>) -> {nx.ends(Png.png.ihdr.put(mm)) == False{} : Bool}:
  match mm:
    case None{}:
      {==}
    case Some{Png.Ihdr{+w, +h, +d, +c, +comp, +f, +i}}:
      open.ihdr.ok(Png.png.good(w, h, d, c, comp, f, i), w, h, d, c, comp, f, i)

# IHDR does not end the image
def open.on.ihdr(ihdr: Bool, +data: List<&2, U32>) -> {nx.ends(Png.png.on.ihdr(ihdr, data)) == False{} : Bool}:
  match ihdr:
    case True{}:
      {==}
    case False{}:
      open.ihdr.put(Png.parse_ihdr(List.reverse(&2, U32, data)))

# IDAT does not end the image
def open.idat.try(
  zz: Bool,
  +data: List<&2, U32>,
  +pg: Png.Pg
) -> {nx.ends(Png.png.idat.try(zz, data, pg)) == False{} : Bool}:
  match zz:
    case True{}:
      {==}
    case False{}:
      {==}

# IDAT, wherever it comes, does not end the image
def open.on.idat(
  ihdr: Bool,
  +idat_done: Bool,
  +need: Bool,
  +data: List<&2, U32>,
  +pg: Png.Pg
) -> {nx.ends(Png.png.on.idat(ihdr, idat_done, need, data, pg)) == False{} : Bool}:
  match ihdr:
    case False{}:
      {==}
    case True{}:
      open.idat.try(Bool.and(Bool.not(idat_done), need), data, pg)

# PLTE does not end the image
def open.on.plte(
  ihdr: Bool,
  +saw_plte: Bool,
  +saw_idat: Bool,
  +colour: U32,
  +data: List<&2, U32>,
  +pg: Png.Pg
) -> {nx.ends(Png.png.on.plte(ihdr, saw_plte, saw_idat, colour, data, pg)) == False{} : Bool}:
  match ihdr:
    case False{}:
      {==}
    case True{}:
      open.allow(Bool.and(Bool.not(saw_plte), Bool.and(Bool.not(saw_idat), Bool.and(Png.png.plte.ok(colour),
        Png.png.mod3(data)))), Png.pg.plte(pg, List.reverse(&2, U32, data)))

# a tRNS taken or ignored does not end the image
def open.trns.take(
  zz: Bool,
  +data: List<&2, U32>,
  +pg: Png.Pg
) -> {nx.ends(Png.png.trns.take(zz, data, pg)) == False{} : Bool}:
  match zz:
    case True{}:
      {==}
    case False{}:
      {==}

# tRNS does not end the image
def open.on.trns(
  ihdr: Bool,
  +saw_trns: Bool,
  +saw_idat: Bool,
  +colour: U32,
  +saw_plte: Bool,
  +data: List<&2, U32>,
  +pg: Png.Pg
) -> {nx.ends(Png.png.on.trns(ihdr, saw_trns, saw_idat, colour, saw_plte, data, pg)) == False{} : Bool}:
  match ihdr:
    case False{}:
      {==}
    case True{}:
      open.trns.take(Bool.and(Bool.not(saw_idat), Bool.and(Bool.not(saw_trns), Png.png.trns.ok(colour, saw_plte))),
        data, pg)

# an ancillary chunk or a refused critical one does not end the image
def open.other.at(anc: Bool, +pg: Png.Pg) -> {nx.ends(Png.png.other.at(anc, pg)) == False{} : Bool}:
  match anc:
    case True{}:
      {==}
    case False{}:
      {==}

# any other chunk does not end the image
def open.on.other(
  ihdr: Bool,
  +anc: Bool,
  +pg: Png.Pg
) -> {nx.ends(Png.png.on.other(ihdr, anc, pg)) == False{} : Bool}:
  match ihdr:
    case False{}:
      {==}
    case True{}:
      open.other.at(anc, pg)

# tRNS or another chunk
def open.apply.tr(
  ztrns: Bool,
  +anc: Bool,
  +ihdr: Bool,
  +saw_plte: Bool,
  +saw_idat: Bool,
  +saw_trns: Bool,
  +colour: U32,
  +data: List<&2, U32>,
  +pg: Png.Pg
) -> {nx.ends(Png.png.apply.tr(ztrns, anc, ihdr, saw_plte, saw_idat, saw_trns, colour, data, pg)) == False{} : Bool}:
  match ztrns:
    case True{}:
      open.on.trns(ihdr, saw_trns, saw_idat, colour, saw_plte, data, pg)
    case False{}:
      open.on.other(ihdr, anc, pg)

# PLTE, tRNS or another chunk
def open.apply.pl(
  zplte: Bool,
  +ztrns: Bool,
  +anc: Bool,
  +ihdr: Bool,
  +saw_plte: Bool,
  +saw_idat: Bool,
  +saw_trns: Bool,
  +colour: U32,
  +data: List<&2, U32>,
  +pg: Png.Pg
) -> {nx.ends(Png.png.apply.pl(zplte, ztrns, anc, ihdr, saw_plte, saw_idat, saw_trns, colour, data, pg)) == False{}
  : Bool}:
  match zplte:
    case True{}:
      open.on.plte(ihdr, saw_plte, saw_idat, colour, data, pg)
    case False{}:
      open.apply.tr(ztrns, anc, ihdr, saw_plte, saw_idat, saw_trns, colour, data, pg)

# not IEND: on to PLTE, tRNS or another chunk
def open.apply.ie(
  ziend: Bool,
  ez: {ziend == False{} : Bool},
  +zplte: Bool,
  +ztrns: Bool,
  +anc: Bool,
  +ihdr: Bool,
  +saw_plte: Bool,
  +saw_idat: Bool,
  +saw_trns: Bool,
  +colour: U32,
  +data: List<&2, U32>,
  +pg: Png.Pg
) -> {nx.ends(Png.png.apply.ie(ziend, zplte, ztrns, anc, ihdr, saw_plte, saw_idat, saw_trns, colour, data, pg))
  == False{} : Bool}:
  match ziend:
    case True{}:
      Empty.absurd({nx.ends(Png.png.apply.ie(True{}, zplte, ztrns, anc, ihdr, saw_plte, saw_idat, saw_trns, colour,
        data, pg)) == False{} : Bool}, M1.true_false(ez))
    case False{}:
      open.apply.pl(zplte, ztrns, anc, ihdr, saw_plte, saw_idat, saw_trns, colour, data, pg)

# IDAT, or not IEND
def open.apply.id(
  zidat: Bool,
  +ziend: Bool,
  ez: {ziend == False{} : Bool},
  +zplte: Bool,
  +ztrns: Bool,
  +anc: Bool,
  +ihdr: Bool,
  +saw_plte: Bool,
  +saw_idat: Bool,
  +idat_done: Bool,
  +saw_trns: Bool,
  +colour: U32,
  +data: List<&2, U32>,
  +pg: Png.Pg
) -> {nx.ends(Png.png.apply.id(zidat, ziend, zplte, ztrns, anc, ihdr, saw_plte, saw_idat, idat_done, saw_trns, colour,
  data, pg)) == False{} : Bool}:
  match zidat:
    case True{}:
      open.on.idat(ihdr, idat_done, Bool.or(Bool.not(U32.is_eq(colour, 3)), saw_plte), data, pg)
    case False{}:
      open.apply.ie(ziend, ez, zplte, ztrns, anc, ihdr, saw_plte, saw_idat, saw_trns, colour, data, pg)

# IHDR, or the rest
def open.apply.go(
  zihdr: Bool,
  +zidat: Bool,
  +ziend: Bool,
  ez: {ziend == False{} : Bool},
  +zplte: Bool,
  +ztrns: Bool,
  +anc: Bool,
  +ihdr: Bool,
  +saw_plte: Bool,
  +saw_idat: Bool,
  +idat_done: Bool,
  +saw_trns: Bool,
  +colour: U32,
  +data: List<&2, U32>,
  +pg: Png.Pg
) -> {nx.ends(Png.png.apply.go(zihdr, zidat, ziend, zplte, ztrns, anc, ihdr, saw_plte, saw_idat, idat_done, saw_trns,
  colour, data, pg)) == False{} : Bool}:
  match zihdr:
    case True{}:
      open.on.ihdr(ihdr, data)
    case False{}:
      open.apply.id(zidat, ziend, ez, zplte, ztrns, anc, ihdr, saw_plte, saw_idat, idat_done, saw_trns, colour, data,
        pg)

# after IEND every chunk is refused; before, a chunk that is not IEND does not end the image
def open.apply.at(
  iend: Bool,
  +zihdr: Bool,
  +zidat: Bool,
  +ziend: Bool,
  ez: {ziend == False{} : Bool},
  +zplte: Bool,
  +ztrns: Bool,
  +anc: Bool,
  +ihdr: Bool,
  +saw_plte: Bool,
  +saw_idat: Bool,
  +idat_done: Bool,
  +saw_trns: Bool,
  +colour: U32,
  +data: List<&2, U32>,
  +pg: Png.Pg
) -> {nx.ends(Png.png.apply.at(iend, zihdr, zidat, ziend, zplte, ztrns, anc, ihdr, saw_plte, saw_idat, idat_done,
  saw_trns, colour, data, pg)) == False{} : Bool}:
  match iend:
    case True{}:
      {==}
    case False{}:
      open.apply.go(zihdr, zidat, ziend, ez, zplte, ztrns, anc, ihdr, saw_plte, saw_idat, idat_done, saw_trns, colour,
        data, pg)

# a chunk whose type is not IEND does not end the image, whatever the state
def open.apply(
  +typ: U32,
  ht: {U32.is_eq(typ, Png.tag.iend()) == False{} : Bool},
  +data: List<&2, U32>,
  pg: Png.Pg
) -> {nx.ends(Png.png.apply(typ, data, pg)) == False{} : Bool}:
  match pg:
    case Png.Pg{+w, +h, +d, +colour, +comp, +f, +i, +idat, +plte, +trns, +ihdr, +saw_plte, +saw_idat, +idat_done,
      +saw_trns, +iend}:
      open.apply.at(iend, U32.is_eq(typ, Png.tag.ihdr()), U32.is_eq(typ, Png.tag.idat()), U32.is_eq(typ,
        Png.tag.iend()), ht, U32.is_eq(typ, Png.tag.plte()), U32.is_eq(typ, Png.tag.trns()), Png.tag.anc(typ), ihdr,
        saw_plte, saw_idat, idat_done, saw_trns, colour, data,
        Png.Pg{w, h, d, colour, comp, f, i, idat, plte, trns, ihdr, saw_plte, saw_idat, idat_done, saw_trns, iend})

# a judged chunk that is not IEND, CRC right or wrong, does not end the image
def open.judge.at(
  zz: Bool,
  +typ: U32,
  ht: {U32.is_eq(typ, Png.tag.iend()) == False{} : Bool},
  +data: List<&2, U32>,
  +pg: Png.Pg
) -> {nx.ends(Png.png.judge.at(zz, typ, data, pg)) == False{} : Bool}:
  match zz:
    case False{}:
      {==}
    case True{}:
      open.apply(typ, ht, data, pg)

# ---- chunks as the laws lay them out ----

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

# the law's "not IEND" is the decoder's: Bool.not(z) is True exactly when z is False
def open.typ(zz: Bool, ho: {Bool.not(zz) == True{} : Bool}) -> {zz == False{} : Bool}:
  match zz:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, M1.false_true(ho))
    case False{}:
      {==}

# a chunk before the bad one: walked to its CRC and judged; whatever the
# judgement, more bytes follow, so the decode is none when the walk over them is
law walk_pass:
  for +ck: Laws.Chunk
  for +rest: List<&2, U32>
  for +pg: Png.Pg
  for h_ck: Laws.chunk.framed(ck)
  for h_op: {Laws.chunk.open(ck) == True{} : Bool}
  for ih: @pp: Png.Pg -> {Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], pp) == None{} : Maybe<&2, Png.Pic>}
  {Png.png.go(Laws.chunk.onto(ck, rest), Png.ZLen{}, False{}, 0, 0, [], [], pg) == None{} : Maybe<&2, Png.Pic>}

# the proof of walk_pass
def walk_pass(ck, rest, pg, h_ck, h_op, ih):
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
        judge_more(nx, open.judge.at(U32.is_eq(Png.be.u32(s0, s1, s2, s3), Crc.crc32(List.reverse(&2, U32,
          List.reverse.go(&2, U32, data, [t3, t2, t1, t0])))), Png.be.u32(t0, t1, t2, t3),
          open.typ(U32.is_eq(Png.be.u32(t0, t1, t2, t3), Png.tag.iend()), h_op), List.reverse.go(&2, U32, data, []),
          pg),
          rest, ih(Png.png.pgof(nx))))

# every chunk before the bad one: walked to its CRC, and then either refused,
# ended with bytes still to come, or on to the next chunk
law walk_all:
  for +pre: List<&2, Laws.Chunk>
  for +bad: Laws.Chunk
  for +rest: List<&2, U32>
  for +pg: Png.Pg
  for h_pre: Laws.chunks.framed(pre)
  for h_open: Laws.chunks.open(pre)
  for h_bad: Laws.chunk.framed(bad)
  for h_crc: {Laws.chunk.stored(bad) == Laws.chunk.sum(bad) : U32} -> Empty
  {Png.png.go(Laws.chunks.onto(pre, Laws.chunk.onto(bad, rest)), Png.ZLen{}, False{}, 0, 0, [], [], pg)
    == None{} : Maybe<&2, Png.Pic>}

# the proof of walk_all
def walk_all(pre, bad, rest, pg, h_pre, h_open, h_bad, h_crc):
  match pre:
    case Nil{}:
      walk_bad(bad, rest, pg, h_bad, h_crc)
    case +ck <> +tl:
      (h_ck, h_tl) = h_pre
      (h_op, h_ot) = h_open
      walk_pass(ck, Laws.chunks.onto(tl, Laws.chunk.onto(bad, rest)), pg, h_ck, h_op,
        pp => walk_all(tl, bad, rest, pp, h_tl, h_ot, h_bad, h_crc))

def Laws.crc32_bitwise(xs):
  M2.crc32_ref(xs)

def Laws.png_crc_refused(pre, bad, rest, h_pre, h_open, h_bad, h_crc):
  Equal.cong(Maybe<&2, Png.Pic>, Maybe<&2, Img.Raster>, mm => Img.decode_png.pic(mm),
    Png.png.go(Laws.chunks.onto(pre, Laws.chunk.onto(bad, rest)), Png.ZLen{}, False{}, 0, 0, [], [], Png.pg.empty()),
    None{}, walk_all(pre, bad, rest, Png.pg.empty(), h_pre, h_open, h_bad, h_crc))
