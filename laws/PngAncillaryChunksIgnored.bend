# Ancillary chunks where PNG section 5.6 allows them change nothing
# decode_png makes of a file: after IHDR, PLTE, tRNS and the IDAT chunks,
# and with tRNS before PLTE where the decoder takes that order, the file
# decodes to the raster the colour type packs from the unfiltered inflated
# IDAT data, with the PLTE and tRNS data. After the IDAT chunks a tRNS is one
# of them too: misplaced, it is ignored (laws/PngIgnoresFaultyTrns.bend);
# until 2026-11 it refused the image.
import Base
import ../main.bend as Img
import ../src/inflate.bend as Inf
import ./defs/PngSpecification.bend as D1

# an ancillary chunk (PNG section 5.4): its four-byte type, read as one number most significant byte first, and its
# data
type Anc is Data:
  Anc{+typ: U32, +data: List<&2, U32>}

# ancillary chunks laid out as spec.chunk, one after another, then rest
def spec.ancs(cs: List<&2, Anc>, rest: List<&2, U32>) -> List<&2, U32>:
  match cs:
    case Nil{}:
      rest
    case Anc{+typ, +data} <> tl:
      D1.spec.chunk(D1.spec.be4(typ), data, spec.ancs(tl, rest))

# the ancillary bit (PNG section 5.4): bit 5 of the type's first byte is 1
def spec.anc.bit(+typ: U32) -> Bool:
  U32.is_eq(U32.and(U32.shrn(typ, 24n), 32), 32)

# each chunk is ancillary, is not tRNS (1951551059, the bytes 116 82 78 83), and has fewer than 2^32 data bytes
def spec.ancs.ok(cs: List<&2, Anc>) -> Type:
  match cs:
    case Nil{}:
      Unit
    case Anc{+typ, +data} <> tl:
      {spec.anc.bit(typ) == True{} : Bool} & ({U32.is_eq(typ, 1951551059) == False{} : Bool} & (D1.spec.fits(data) &
        spec.ancs.ok(tl)))

# a chunk type after the IDAT chunks: any, when there was an IDAT; not tRNS otherwise
def spec.trns.after(idat: Bool, +typ: U32) -> Type:
  match idat:
    case True{}:
      Unit
    case False{}:
      {U32.is_eq(typ, 1951551059) == False{} : Bool}

# each chunk is ancillary and has fewer than 2^32 data bytes; tRNS is among them only when an IDAT came before
def spec.ancs.after(idat: Bool, cs: List<&2, Anc>) -> Type:
  match cs:
    case Nil{}:
      Unit
    case Anc{+typ, +data} <> tl:
      {spec.anc.bit(typ) == True{} : Bool} & (spec.trns.after(idat, typ) & (D1.spec.fits(data) &
        spec.ancs.after(idat, tl)))

# PLTE, ancillary chunks a1 and tRNS, then rest; with late, tRNS comes first, an order the decoder also takes when
# the colour type allows tRNS with no PLTE yet
def spec.mid(
  late: Bool,
  plte: Maybe<&2, List<&2, U32>>,
  a1: List<&2, Anc>,
  trns: Maybe<&2, List<&2, U32>>,
  rest: List<&2, U32>
) -> List<&2, U32>:
  match late:
    case False{}:
      D1.spec.chunk.opt([80, 76, 84, 69], plte, spec.ancs(a1, D1.spec.chunk.opt([116, 82, 78, 83], trns, rest)))
    case True{}:
      D1.spec.chunk.opt([116, 82, 78, 83], trns, spec.ancs(a1, D1.spec.chunk.opt([80, 76, 84, 69], plte, rest)))

# a PNG file as spec.png lays it out, with ancillary chunks where PNG section 5.6 allows them: a0 after IHDR, a1
# between PLTE and tRNS, a2 after them, and a3 after the IDAT chunks, before IEND
def spec.png.anc(
  +ww: U32,
  +hh: U32,
  +cc: U32,
  late: Bool,
  a0: List<&2, Anc>,
  plte: Maybe<&2, List<&2, U32>>,
  a1: List<&2, Anc>,
  trns: Maybe<&2, List<&2, U32>>,
  a2: List<&2, Anc>,
  idats: List<&2, List<&2, U32>>,
  a3: List<&2, Anc>
) -> List<&2, U32>:
  List.append(&2, U32, Img.png_sig(), D1.spec.chunk([73, 72, 68, 82], D1.spec.ihdr.data(ww, hh, cc), spec.ancs(a0,
    spec.mid(late, plte, a1, trns, spec.ancs(a2, D1.spec.idats(idats, spec.ancs(a3, D1.spec.chunk([73, 69, 78, 68], [],
    []))))))))

# LAW: ancillary chunks where PNG section 5.6 allows them leave what decode_png makes of a file: the file png_walk
# reads, with ancillary chunks after IHDR, PLTE, tRNS and the IDAT chunks (tRNS among the last when there is an
# IDAT), and with tRNS before PLTE where the decoder takes that order (late), decodes to the raster px.of packs from
# the unfiltered inflated IDAT data, with the IHDR colour type and the PLTE and tRNS data
law png_walk_anc:
  for +ww: U32
  for +hh: U32
  for +cc: U32
  for +late: Bool
  for +a0: List<&2, Anc>
  for +plte: Maybe<&2, List<&2, U32>>
  for +a1: List<&2, Anc>
  for +trns: Maybe<&2, List<&2, U32>>
  for +a2: List<&2, Anc>
  for +idats: List<&2, List<&2, U32>>
  for +a3: List<&2, Anc>
  for h_ww: {U32.is_gt(ww, 0) == True{} : Bool}
  for h_hh: {U32.is_gt(hh, 0) == True{} : Bool}
  for h_cc: {D1.spec.colour.ok(cc) == True{} : Bool}
  for h_pl: {D1.spec.plte.ok(cc, plte) == True{} : Bool}
  for h_tr: {D1.spec.trns.ok(cc, plte, trns) == True{} : Bool}
  for h_late: {Bool.or(Bool.not(late), D1.spec.trns.ok(cc, None{}, trns)) == True{} : Bool}
  for h_fp: D1.spec.fits.opt(plte)
  for h_ft: D1.spec.fits.opt(trns)
  for h_fi: D1.spec.fits.all(idats)
  for h_a0: spec.ancs.ok(a0)
  for h_a1: spec.ancs.ok(a1)
  for h_a2: spec.ancs.ok(a2)
  for h_a3: spec.ancs.after(Bool.not(List.is_empty(&2, List<&2, U32>, idats)), a3)
  {Img.decode_png(spec.png.anc(ww, hh, cc, late, a0, plte, a1, trns, a2, idats, a3)) == D1.spec.decoded(Inf.inflate(
    List.concat(&2, U32, idats)), ww, hh, cc, D1.spec.or.nil(plte), D1.spec.or.nil(trns)) : Maybe<&2, Img.Raster>}
