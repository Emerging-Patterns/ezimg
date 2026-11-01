# proofs of laws/PngRefusesUnsupportedHeaders.bend
import Base
import ../main.bend as Img
import ../src/crc.bend as Crc
import ../src/png.bend as Png
import ../laws/PngRefusesUnsupportedHeaders.bend as Laws
import ../laws/defs/PngSpecification.bend as D1
import ./lemmas/BasicFacts.bend as M1

# the shape of an IHDR check with six tests: the size, the depth, the colour
# type, and the three methods
def shape(g1: Bool, g2: Bool, g3: Bool, g4: Bool, g5: Bool, g6: Bool) -> Bool:
  Bool.and(g1, Bool.and(Bool.and(g2, g3), Bool.and(g4, Bool.and(g5, g6))))

# a false second test makes the whole check false
law shape_second:
  for g1: Bool
  for g2: Bool
  for -g3: Bool
  for -g4: Bool
  for -g5: Bool
  for -g6: Bool
  for h2: {g2 == False{} : Bool}
  {shape(g1, g2, g3, g4, g5, g6) == False{} : Bool}

# the proof of shape_second
def shape_second(g1, g2, _g3, _g4, _g5, _g6, h2):
  match g1:
    case False{}:
      {==}
    case True{}:
      match g2:
        case False{}:
          {==}
        case True{}:
          Empty.absurd({shape(True{}, True{}, _g3, _g4, _g5, _g6) == False{} : Bool}, M1.pdec.true_false(h2))

# a false third test makes the whole check false
law shape_third:
  for g1: Bool
  for g2: Bool
  for g3: Bool
  for -g4: Bool
  for -g5: Bool
  for -g6: Bool
  for h3: {g3 == False{} : Bool}
  {shape(g1, g2, g3, g4, g5, g6) == False{} : Bool}

# the proof of shape_third
def shape_third(g1, g2, g3, _g4, _g5, _g6, h3):
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
              Empty.absurd({shape(True{}, True{}, True{}, _g4, _g5, _g6) == False{} : Bool}, M1.pdec.true_false(h3))

# a false sixth test makes the whole check false
law shape_sixth:
  for g1: Bool
  for g2: Bool
  for g3: Bool
  for g4: Bool
  for g5: Bool
  for g6: Bool
  for h6: {g6 == False{} : Bool}
  {shape(g1, g2, g3, g4, g5, g6) == False{} : Bool}

# the proof of shape_sixth
def shape_sixth(g1, g2, g3, g4, g5, g6, h6):
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
                      match g6:
                        case False{}:
                          {==}
                        case True{}:
                          Empty.absurd({shape(True{}, True{}, True{}, True{}, True{}, True{}) == False{} : Bool},
                            M1.pdec.true_false(h6))

# or regrouped: a false a | (b | r) is a false (a | b) | r
law or_regroup:
  for e0: Bool
  for -e2: Bool
  for -rr: Bool
  for h_or: {Bool.or(e0, Bool.or(e2, rr)) == False{} : Bool}
  {Bool.or(Bool.or(e0, e2), rr) == False{} : Bool}

# the proof of or_regroup
def or_regroup(e0, _e2, _rr, h_or):
  match e0:
    case False{}:
      h_or
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, M1.pdec.true_false(h_or))

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
  empty: Bool,
  more: Maybe<&2, Png.Pic>,
  hg: {Png.png.good(be.back(ww), be.back(hh), dd, cc, comp, ff, ii) == False{} : Bool}
) -> {Img.decode_png.pic(Png.png.crc(Png.png.judge.at(zz, Png.tag.ihdr(), ihdr.held(ww, hh, dd, cc, comp, ff, ii),
  Png.pg.empty()), empty, more)) == None{} : Maybe<&2, Img.Raster>}:
  match zz:
    case False{}:
      {==}
    case True{}:
      Equal.cong(Bool, Maybe<&2, Img.Raster>,
        gg => Img.decode_png.pic(Png.png.crc(Png.png.ihdr.ok(gg, be.back(ww), be.back(hh), dd, cc, comp, ff, ii),
          empty, more)),
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
    ii, List.is_empty(&2, U32, rest),
    Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], Png.png.pgof(Png.png.judge(Png.be.u32(c3, c2, c1, c0), crc,
      Png.tag.ihdr(), ihdr.held(ww, hh, dd, cc, comp, ff, ii), Png.pg.empty()))),
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

# png.good refuses a bit depth other than 8
def good.depth(
  +ww: U32,
  +hh: U32,
  +dd: U32,
  +cc: U32,
  +comp: U32,
  +ff: U32,
  +ii: U32,
  h_dd: {U32.is_eq(dd, 8) == False{} : Bool}
) -> {Png.png.good(ww, hh, dd, cc, comp, ff, ii) == False{} : Bool}:
  shape_second(Bool.and(U32.is_gt(ww, 0), U32.is_gt(hh, 0)), U32.is_eq(dd, 8), Png.png.col(cc), U32.is_zero(comp),
    U32.is_zero(ff), U32.is_zero(ii), h_dd)

# png.good refuses an interlace method other than 0
def good.interlace(
  +ww: U32,
  +hh: U32,
  +dd: U32,
  +cc: U32,
  +comp: U32,
  +ff: U32,
  +ii: U32,
  h_ii: {U32.is_eq(ii, 0) == False{} : Bool}
) -> {Png.png.good(ww, hh, dd, cc, comp, ff, ii) == False{} : Bool}:
  shape_sixth(Bool.and(U32.is_gt(ww, 0), U32.is_gt(hh, 0)), U32.is_eq(dd, 8), Png.png.col(cc), U32.is_zero(comp),
    U32.is_zero(ff), U32.is_zero(ii), h_ii)

# png.good refuses a colour type outside 0, 2, 3, 4 and 6
def good.colour(
  +ww: U32,
  +hh: U32,
  +dd: U32,
  +cc: U32,
  +comp: U32,
  +ff: U32,
  +ii: U32,
  h_cc: {D1.spec.colour.ok(cc) == False{} : Bool}
) -> {Png.png.good(ww, hh, dd, cc, comp, ff, ii) == False{} : Bool}:
  shape_third(Bool.and(U32.is_gt(ww, 0), U32.is_gt(hh, 0)), U32.is_eq(dd, 8), Png.png.col(cc), U32.is_zero(comp),
    U32.is_zero(ff), U32.is_zero(ii),
    or_regroup(U32.is_eq(cc, 0), U32.is_eq(cc, 2), Bool.or(U32.is_eq(cc, 3), Bool.or(U32.is_eq(cc, 4),
      U32.is_eq(cc, 6))), h_cc))

def Laws.png_depth_refused(ww, hh, dd, cc, comp, ff, ii, crc, rest, h_dd):
  ihdr.refused(ww, hh, dd, cc, comp, ff, ii, crc, rest,
    good.depth(be.back(ww), be.back(hh), dd, cc, comp, ff, ii, h_dd))

def Laws.png_interlace_refused(ww, hh, dd, cc, comp, ff, ii, crc, rest, h_ii):
  ihdr.refused(ww, hh, dd, cc, comp, ff, ii, crc, rest,
    good.interlace(be.back(ww), be.back(hh), dd, cc, comp, ff, ii, h_ii))

def Laws.png_colour_refused(ww, hh, dd, cc, comp, ff, ii, crc, rest, h_cc):
  ihdr.refused(ww, hh, dd, cc, comp, ff, ii, crc, rest,
    good.colour(be.back(ww), be.back(hh), dd, cc, comp, ff, ii, h_cc))
