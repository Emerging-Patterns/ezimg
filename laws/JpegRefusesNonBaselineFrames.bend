# `decode_jpeg` returns none for every input that opens with SOI, then
# segments other than frame headers (DHT, DQT, SOS, DRI, COM, APP0 to APP15)
# each with a length field that fits its body, then a frame header other than
# SOF0 and SOF1 (baseline and extended sequential Huffman, which this decoder
# reads alike), or an SOF0 or SOF1 segment whose sample precision is not 8,
# whatever follows.
import Base
import ../main.bend as Img

# the markers of segments that are not frame headers (T.81 Table B.1): DHT, DQT, SOS, DRI, COM, APP0 to APP15
type Mk is Data:
  MDht{}
  MDqt{}
  MSos{}
  MDri{}
  MCom{}
  MApp0{}
  MApp1{}
  MApp2{}
  MApp3{}
  MApp4{}
  MApp5{}
  MApp6{}
  MApp7{}
  MApp8{}
  MApp9{}
  MApp10{}
  MApp11{}
  MApp12{}
  MApp13{}
  MApp14{}
  MApp15{}

# a marker's second byte
def mk.byte(mk: Mk) -> U32:
  match mk:
    case MDht{}:
      196
    case MDqt{}:
      219
    case MSos{}:
      218
    case MDri{}:
      221
    case MCom{}:
      254
    case MApp0{}:
      224
    case MApp1{}:
      225
    case MApp2{}:
      226
    case MApp3{}:
      227
    case MApp4{}:
      228
    case MApp5{}:
      229
    case MApp6{}:
      230
    case MApp7{}:
      231
    case MApp8{}:
      232
    case MApp9{}:
      233
    case MApp10{}:
      234
    case MApp11{}:
      235
    case MApp12{}:
      236
    case MApp13{}:
      237
    case MApp14{}:
      238
    case MApp15{}:
      239

# a segment that is not a frame header: its marker, the two bytes of its length field, and its body
type Seg is Data:
  Seg{mk: Mk, hi: U32, lo: U32, body: List<&2, U32>}

# a segment's bytes: FF, the marker, the length field, the body
def seg.bytes(sg: Seg) -> List<&2, U32>:
  match sg:
    case Seg{mk, hi, lo, body}:
      255 <> (mk.byte(mk) <> (hi <> (lo <> body)))

# the length a length field gives, high byte first
def seg.len(+hi: U32, +lo: U32) -> U32:
  U32.or(U32.shln(hi, 8n), lo)

# a length field fits its body: it is at least 2, and 2 more than the body's length
def seg.Fits(+hi: U32, +lo: U32, +body: List<&2, U32>) -> Type:
  {U32.is_lt(seg.len(hi, lo), 2) == False{} : Bool}
    & {U32.to_nat((seg.len(hi, lo) - 2 : U32)) == List.length(&2, U32, body) : Nat}

# every segment's length field fits its body
def segs.Fit(ss: List<&2, Seg>) -> Type:
  match ss:
    case Nil{}:
      Unit
    case Seg{_mk, +hi, +lo, +body} <> rest:
      seg.Fits(hi, lo, body) & segs.Fit(rest)

# the bytes of the segments, in order
def segs.bytes(ss: List<&2, Seg>) -> List<&2, U32>:
  match ss:
    case Nil{}:
      Nil{}
    case sg <> rest:
      List.append(&2, U32, seg.bytes(sg), segs.bytes(rest))

# SOI, then the segments, then the rest
def jpeg.lead(ss: List<&2, Seg>, rest: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, [255, 216], List.append(&2, U32, segs.bytes(ss), rest))

# the frame headers other than SOF0 and SOF1 (T.81 Table B.1): SOF2, SOF3, SOF5 to SOF7, SOF9 to SOF11, SOF13 to
# SOF15
type Sofn is Data:
  Sof2{}
  Sof3{}
  Sof5{}
  Sof6{}
  Sof7{}
  Sof9{}
  Sof10{}
  Sof11{}
  Sof13{}
  Sof14{}
  Sof15{}

# a frame header's second byte
def sofn.byte(sn: Sofn) -> U32:
  match sn:
    case Sof2{}:
      194
    case Sof3{}:
      195
    case Sof5{}:
      197
    case Sof6{}:
      198
    case Sof7{}:
      199
    case Sof9{}:
      201
    case Sof10{}:
      202
    case Sof11{}:
      203
    case Sof13{}:
      205
    case Sof14{}:
      206
    case Sof15{}:
      207

# LAW: bytes that open with SOI and segments that are not frame headers, then a frame header other than SOF0 and
# SOF1, decode to none, whatever follows
law jpeg_refuse_sofn:
  for +segs: List<&2, Seg>
  for h_fit: segs.Fit(segs)
  for +sn: Sofn
  for +rest: List<&2, U32>
  {Img.decode_jpeg(jpeg.lead(segs, 255 <> (sofn.byte(sn) <> rest))) == None{} : Maybe<&2, Img.Raster>}

# the marker of a sequential Huffman frame header this decoder reads: SOF1 (extended) or SOF0 (baseline)
def sof.byte(+ext: Bool) -> U32:
  Bool.pick(U32, ext, 193, 192)

# LAW: bytes that open with SOI and segments that are not frame headers, then an SOF0 or SOF1 segment whose sample
# precision is not 8, decode to none, whatever follows
law jpeg_refuse_precision:
  for +segs: List<&2, Seg>
  for h_fit: segs.Fit(segs)
  for +ext: Bool
  for +hi: U32
  for +lo: U32
  for +pp: U32
  for +body: List<&2, U32>
  for h_len: seg.Fits(hi, lo, pp <> body)
  for h_pp: {U32.is_eq(pp, 8) == False{} : Bool}
  for +rest: List<&2, U32>
  {Img.decode_jpeg(jpeg.lead(segs, List.append(&2, U32, 255 <> (sof.byte(ext) <> (hi <> (lo <> (pp <> body)))),
    rest)))
    == None{} : Maybe<&2, Img.Raster>}
