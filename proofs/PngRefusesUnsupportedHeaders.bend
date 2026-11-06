# proofs of laws/PngRefusesUnsupportedHeaders.bend
import Base
import ../main.bend as Img
import ../src/crc.bend as Crc
import ../src/png.bend as Png
import ../laws/PngRefusesUnsupportedHeaders.bend as Laws
import ../laws/defs/PngSpecification.bend as D1
import ../laws/defs/SizeBounds.bend as D2
import ./lemmas/BasicFacts.bend as M1
import ./lemmas/PngChunkWalker.bend as M2

# the shape of the IHDR check with five tests: the sides, the colour type
# and bit depth, compression, filter and interlace methods
def shape(g1: Bool, g2: Bool, g3: Bool, g4: Bool, g5: Bool) -> Bool:
  Bool.and(g1, Bool.and(g2, Bool.and(g3, Bool.and(g4, g5))))

# a false second test makes the whole check false
law shape_second:
  for g1: Bool
  for g2: Bool
  for -g3: Bool
  for -g4: Bool
  for -g5: Bool
  for h2: {g2 == False{} : Bool}
  {shape(g1, g2, g3, g4, g5) == False{} : Bool}

# the proof of shape_second
def shape_second(g1, g2, _g3, _g4, _g5, h2):
  match g1:
    case False{}:
      {==}
    case True{}:
      match g2:
        case False{}:
          {==}
        case True{}:
          Empty.absurd({shape(True{}, True{}, _g3, _g4, _g5) == False{} : Bool}, M1.pdec.true_false(h2))

# a false fifth test makes the whole check false
law shape_fifth:
  for g1: Bool
  for g2: Bool
  for g3: Bool
  for g4: Bool
  for g5: Bool
  for h5: {g5 == False{} : Bool}
  {shape(g1, g2, g3, g4, g5) == False{} : Bool}

# the proof of shape_fifth
def shape_fifth(g1, g2, g3, g4, g5, h5):
  match g1:
    case False{}:
      {==}
    case True{}:
      match g2:
        case False{}:
          {==}
        case True{}:
          match g3:
            case False{}:
              {==}
            case True{}:
              match g4:
                case False{}:
                  {==}
                case True{}:
                  match g5:
                    case False{}:
                      {==}
                    case True{}:
                      Empty.absurd({shape(True{}, True{}, True{}, True{}, True{}) == False{} : Bool},
                        M1.pdec.true_false(h5))

# byte 3, 2, 1 and 0 of a U32, as spec.be4 writes them
def by3(+nn: U32) -> U32:
  U32.and(255, U32.shrn(nn, 24n))

def by2(+nn: U32) -> U32:
  U32.and(255, U32.shrn(nn, 16n))

def by1(+nn: U32) -> U32:
  U32.and(255, U32.shrn(nn, 8n))

def by0(+nn: U32) -> U32:
  U32.and(255, nn)

# the width or height the decoder reads back from spec.be4's bytes
def be.back(+nn: U32) -> U32:
  Png.be.u32(by3(nn), by2(nn), by1(nn), by0(nn))

# the IHDR data as the walker holds it, last byte first
def ihdr.held(+ww: U32, +hh: U32, +dd: U32, +cc: U32, +comp: U32, +ff: U32, +ii: U32) -> List<&2, U32>:
  [ii, ff, comp, cc, dd, by0(hh), by1(hh), by2(hh), by3(hh), by0(ww), by1(ww), by2(ww), by3(ww)]

# the IHDR chunk judged, CRC right or wrong: png.good refuses the fields, so the chunk is refused
def ihdr.judged(
  zz: Bool,
  +ww: U32,
  +hh: U32,
  +dd: U32,
  +cc: U32,
  +comp: U32,
  +ff: U32,
  +ii: U32,
  more: Unit -> Maybe<&2, Png.Pic>,
  hg: {Png.png.good(be.back(ww), be.back(hh), dd, cc, comp, ff, ii) == False{} : Bool}
) -> {Img.decode_png.pic(Png.png.crc(Png.png.judge.at(zz, Png.tag.ihdr(), ihdr.held(ww, hh, dd, cc, comp, ff, ii),
  Png.pg.empty()), more)) == None{} : Maybe<&2, Img.Raster>}:
  match zz:
    case False{}:
      {==}
    case True{}:
      Equal.cong(Bool, Maybe<&2, Img.Raster>,
        gg => Img.decode_png.pic(Png.png.crc(Png.png.ihdr.ok(gg, be.back(ww), be.back(hh), dd, cc, comp, ff, ii),
          more)),
        Png.png.good(be.back(ww), be.back(hh), dd, cc, comp, ff, ii), False{}, hg)

# the walker at the CRC of that IHDR chunk, whatever the CRC bytes, the bytes after and the CRC register so far
def ihdr.at.crc(
  +c3: U32,
  +c2: U32,
  +c1: U32,
  +c0: U32,
  +rest: List<&2, U32>,
  +crc: List<&2, U32>,
  +ww: U32,
  +hh: U32,
  +dd: U32,
  +cc: U32,
  +comp: U32,
  +ff: U32,
  +ii: U32,
  hg: {Png.png.good(be.back(ww), be.back(hh), dd, cc, comp, ff, ii) == False{} : Bool}
) -> {Img.decode_png.pic(Png.png.go(c3 <> c2 <> c1 <> c0 <> rest, Png.ZCrc{}, False{}, 0, Png.tag.ihdr(), crc,
  ihdr.held(ww, hh, dd, cc, comp, ff, ii), Png.pg.empty())) == None{} : Maybe<&2, Img.Raster>}:
  ihdr.judged(U32.is_eq(Png.be.u32(c3, c2, c1, c0), Crc.crc32(List.reverse(&2, U32, crc))), ww, hh, dd, cc, comp, ff,
    ii,
    _u => Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], Png.png.pgof(Png.png.judge(Png.be.u32(c3, c2, c1, c0),
      crc, Png.tag.ihdr(), ihdr.held(ww, hh, dd, cc, comp, ff, ii), Png.pg.empty()))),
    hg)

# a file whose IHDR png.good refuses decodes to none
def ihdr.refused(
  +ww: U32,
  +hh: U32,
  +dd: U32,
  +cc: U32,
  +comp: U32,
  +ff: U32,
  +ii: U32,
  +crc: U32,
  +rest: List<&2, U32>,
  hg: {Png.png.good(be.back(ww), be.back(hh), dd, cc, comp, ff, ii) == False{} : Bool}
) -> {Img.decode_png(Laws.spec.ihdr.file(ww, hh, dd, cc, comp, ff, ii, crc, rest)) == None{} : Maybe<&2, Img.Raster>}:
  ihdr.at.crc(by3(crc), by2(crc), by1(crc), by0(crc), rest,
    List.append(&2, U32, ihdr.held(ww, hh, dd, cc, comp, ff, ii), [82, 68, 72, 73]), ww, hh, dd, cc, comp, ff, ii, hg)

# png.good refuses a colour type and bit depth table 11.1 does not pair
def good.depth(
  +ww: U32,
  +hh: U32,
  +dd: U32,
  +cc: U32,
  +comp: U32,
  +ff: U32,
  +ii: U32,
  h_dd: {D1.spec.depth.ok(cc, dd) == False{} : Bool}
) -> {Png.png.good(ww, hh, dd, cc, comp, ff, ii) == False{} : Bool}:
  shape_second(Bool.and(Png.png.side(ww), Png.png.side(hh)), Png.png.depth.ok(cc, dd), U32.is_zero(comp),
    U32.is_zero(ff), Png.png.inter.ok(ii), h_dd)

# png.good refuses an interlace method other than 0 and 1
def good.interlace(
  +ww: U32,
  +hh: U32,
  +dd: U32,
  +cc: U32,
  +comp: U32,
  +ff: U32,
  +ii: U32,
  h_ii: {D1.spec.inter.ok(ii) == False{} : Bool}
) -> {Png.png.good(ww, hh, dd, cc, comp, ff, ii) == False{} : Bool}:
  shape_fifth(Bool.and(Png.png.side(ww), Png.png.side(hh)), Png.png.depth.ok(cc, dd), U32.is_zero(comp),
    U32.is_zero(ff), Png.png.inter.ok(ii), h_ii)

# both sides' second tests, one false, make the pair of sides false
law sides_false:
  for aa: Bool
  for bb: Bool
  for cc: Bool
  for _dd: Bool
  for hh: {Bool.and(bb, _dd) == False{} : Bool}
  {Bool.and(Bool.and(aa, bb), Bool.and(cc, _dd)) == False{} : Bool}

# the proof of sides_false
def sides_false(aa, bb, cc, _dd, hh):
  match aa:
    case False{}:
      {==}
    case True{}:
      match bb:
        case False{}:
          {==}
        case True{}:
          match cc:
            case False{}:
              {==}
            case True{}:
              hh

# png.good refuses a width or height of 2^31 or more
def good.size(
  +ww: U32,
  +hh: U32,
  +dd: U32,
  +cc: U32,
  +comp: U32,
  +ff: U32,
  +ii: U32,
  h_big: {Bool.and(D2.below(31n, U32.to_nat(ww)), D2.below(31n, U32.to_nat(hh))) == False{} : Bool}
) -> {Png.png.good(ww, hh, dd, cc, comp, ff, ii) == False{} : Bool}:
  +g1 = Bool.and(Png.png.side(ww), Png.png.side(hh))
  +sw = D1.spec.side(ww)
  +e1 = {Equal.trans(Bool, g1, Bool.and(sw, D1.spec.side(hh)), False{},
    Equal.trans(Bool, g1, Bool.and(sw, Png.png.side(hh)), Bool.and(sw, D1.spec.side(hh)),
      Equal.cong(Bool, Bool, bb => Bool.and(bb, Png.png.side(hh)), Png.png.side(ww), sw, M2.side.same(ww)),
      Equal.cong(Bool, Bool, bb => Bool.and(sw, bb), Png.png.side(hh), D1.spec.side(hh), M2.side.same(hh))),
    sides_false(U32.is_gt(ww, 0), D2.below(31n, U32.to_nat(ww)), U32.is_gt(hh, 0), D2.below(31n, U32.to_nat(hh)),
      h_big)) : {g1 == False{} : Bool}}
  Equal.cong(Bool, Bool, gg => shape(gg, Png.png.depth.ok(cc, dd), U32.is_zero(comp), U32.is_zero(ff),
    Png.png.inter.ok(ii)), g1, False{}, e1)

# the sides read back are the sides
def big.back(
  +ww: U32,
  +hh: U32,
  h_big: {Bool.and(D2.below(31n, U32.to_nat(ww)), D2.below(31n, U32.to_nat(hh))) == False{} : Bool}
) -> {Bool.and(D2.below(31n, U32.to_nat(be.back(ww))), D2.below(31n, U32.to_nat(be.back(hh)))) == False{} : Bool}:
  +bh = D2.below(31n, U32.to_nat(be.back(hh)))
  Equal.trans(Bool, Bool.and(D2.below(31n, U32.to_nat(be.back(ww))), bh), Bool.and(D2.below(31n, U32.to_nat(ww)), bh),
    False{},
    Equal.cong(U32, Bool, uu => Bool.and(D2.below(31n, U32.to_nat(uu)), bh), be.back(ww), ww, M2.prt.be.back(ww)),
    Equal.trans(Bool, Bool.and(D2.below(31n, U32.to_nat(ww)), bh), Bool.and(D2.below(31n, U32.to_nat(ww)),
      D2.below(31n, U32.to_nat(hh))), False{},
      Equal.cong(U32, Bool, uu => Bool.and(D2.below(31n, U32.to_nat(ww)), D2.below(31n, U32.to_nat(uu))), be.back(hh),
        hh, M2.prt.be.back(hh)), h_big))

def Laws.png_size_refused(ww, hh, dd, cc, comp, ff, ii, crc, rest, h_big):
  ihdr.refused(ww, hh, dd, cc, comp, ff, ii, crc, rest,
    good.size(be.back(ww), be.back(hh), dd, cc, comp, ff, ii, big.back(ww, hh, h_big)))

def Laws.png_depth_refused(ww, hh, dd, cc, comp, ff, ii, crc, rest, h_dd):
  ihdr.refused(ww, hh, dd, cc, comp, ff, ii, crc, rest,
    good.depth(be.back(ww), be.back(hh), dd, cc, comp, ff, ii, h_dd))

def Laws.png_interlace_refused(ww, hh, dd, cc, comp, ff, ii, crc, rest, h_ii):
  ihdr.refused(ww, hh, dd, cc, comp, ff, ii, crc, rest,
    good.interlace(be.back(ww), be.back(hh), dd, cc, comp, ff, ii, h_ii))

def Laws.png_header_takes(ww, hh, dd, cc, ii, h_ww, h_hh, h_dd, h_ii):
  +sh = Png.png.side(hh)
  +rr = Bool.and(D1.spec.depth.ok(cc, dd), D1.spec.inter.ok(ii))
  Equal.trans(Bool, Png.png.good(ww, hh, dd, cc, 0, 0, ii), Bool.and(Bool.and(True{}, sh), rr), True{},
    Equal.cong(Bool, Bool, bb => Bool.and(Bool.and(bb, sh), rr), Png.png.side(ww), True{}, M2.side.ok(ww, h_ww)),
    Equal.trans(Bool, Bool.and(Bool.and(True{}, sh), rr), Bool.and(Bool.and(True{}, True{}), rr), True{},
      Equal.cong(Bool, Bool, bb => Bool.and(Bool.and(True{}, bb), rr), sh, True{}, M2.side.ok(hh, h_hh)),
      Equal.trans(Bool, Bool.and(Bool.and(True{}, True{}), rr), Bool.and(Bool.and(True{}, True{}), Bool.and(True{},
        D1.spec.inter.ok(ii))), True{},
        Equal.cong(Bool, Bool, bb => Bool.and(Bool.and(True{}, True{}), Bool.and(bb, D1.spec.inter.ok(ii))),
          D1.spec.depth.ok(cc, dd), True{}, h_dd),
        Equal.cong(Bool, Bool, bb => Bool.and(Bool.and(True{}, True{}), Bool.and(True{}, bb)), D1.spec.inter.ok(ii),
          True{}, h_ii))))
