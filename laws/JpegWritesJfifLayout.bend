# When `encode_jpeg_with(r, q, s)` is some, at any quality and either
# subsampling, it begins with SOI and ends with EOI, and it is SOI, APP0 with
# the JFIF identifier, DQT, SOF0 carrying `r`'s width and height, two DHT,
# SOS, the entropy-coded data and EOI; so is `encode_jpeg(r)`,
# encode_jpeg_with at quality 75 and 4:2:0.
import Base
import ../main.bend as Img

# a JPEG marker segment: FF, the marker, the length (the body's plus two) high byte first, then the body
def jfif.seg(+mark: U32, +body: List<&2, U32>) -> List<&2, U32>:
  +nn = (U32.from_nat(List.length(&2, U32, body)) + 2 : U32)
  255 <> (mark <> (U32.shrn(nn, 8n) <> (U32.and(nn, 255) <> body)))

# a baseline JFIF file: SOI; APP0 opening with the JFIF identifier; DQT; SOF0 opening with precision 8,
# the height and the width, each high byte first; two DHT; SOS; the entropy-coded bytes; EOI
def jfif.file(
  +ww: U32,
  +hh: U32,
  app: List<&2, U32>,
  dq: List<&2, U32>,
  sof: List<&2, U32>,
  dc: List<&2, U32>,
  ac: List<&2, U32>,
  sos: List<&2, U32>,
  ent: List<&2, U32>
) -> List<&2, U32>:
  +frame = List.append(&2, U32, [8, U32.shrn(hh, 8n), U32.and(hh, 255), U32.shrn(ww, 8n), U32.and(ww, 255)], sof)
  List.append(&2, U32, List.append(&2, U32, [255, 216], List.append(&2, U32,
    jfif.seg(224, List.append(&2, U32, [74, 70, 73, 70, 0], app)), List.append(&2, U32, jfif.seg(219, dq),
    List.append(&2, U32, jfif.seg(192, frame), List.append(&2, U32, jfif.seg(196, dc),
    List.append(&2, U32, jfif.seg(196, ac), jfif.seg(218, sos))))))), List.append(&2, U32, ent, [255, 217]))

# LAW: when encode_jpeg(r) is some, it is SOI, APP0 with the JFIF identifier, DQT, SOF0 carrying r's width
# and height, DHT, SOS, the entropy-coded bytes and EOI
law jpeg_enc_layout:
  for +img: Img.Raster
  for h_some: {Maybe.is_some(&2, List<&2, U32>, Img.encode_jpeg(img)) == True{} : Bool}
  exs app: List<&2, U32>
  exs dq: List<&2, U32>
  exs sof: List<&2, U32>
  exs dc: List<&2, U32>
  exs ac: List<&2, U32>
  exs sos: List<&2, U32>
  exs ent: List<&2, U32>
  {Img.encode_jpeg(img) == Some{jfif.file(Img.width(img), Img.height(img), app, dq, sof, dc, ac, sos, ent)}
    : Maybe<&2, List<&2, U32>>}

# LAW: when encode_jpeg_with(r, q, s) is some, at any quality and either subsampling, it is SOI, APP0 with the JFIF
# identifier, DQT, SOF0 carrying r's width and height, DHT, SOS, the entropy-coded bytes and EOI
law jpeg_enc_layout_q:
  for +img: Img.Raster
  for +qq: U32
  for +sub: Bool
  for h_some: {Maybe.is_some(&2, List<&2, U32>, Img.encode_jpeg_with(img, qq, sub)) == True{} : Bool}
  exs app: List<&2, U32>
  exs dq: List<&2, U32>
  exs sof: List<&2, U32>
  exs dc: List<&2, U32>
  exs ac: List<&2, U32>
  exs sos: List<&2, U32>
  exs ent: List<&2, U32>
  {Img.encode_jpeg_with(img, qq, sub) == Some{jfif.file(Img.width(img), Img.height(img), app, dq, sof, dc, ac, sos,
    ent)} : Maybe<&2, List<&2, U32>>}

# LAW: when encode_jpeg_with(r, q, s) is some, at any quality and either subsampling, it begins with SOI and ends
# with EOI
law jpeg_enc_ends_q:
  for +img: Img.Raster
  for +qq: U32
  for +sub: Bool
  for h_some: {Maybe.is_some(&2, List<&2, U32>, Img.encode_jpeg_with(img, qq, sub)) == True{} : Bool}
  exs mid: List<&2, U32>
  {Img.encode_jpeg_with(img, qq, sub) == Some{List.append(&2, U32, [255, 216], List.append(&2, U32, mid, [255, 217]))}
    : Maybe<&2, List<&2, U32>>}

# LAW: when encode_jpeg(r) is some, it begins with SOI and ends with EOI
law jpeg_enc_ends:
  for +img: Img.Raster
  for h_some: {Maybe.is_some(&2, List<&2, U32>, Img.encode_jpeg(img)) == True{} : Bool}
  exs mid: List<&2, U32>
  {Img.encode_jpeg(img) == Some{List.append(&2, U32, [255, 216], List.append(&2, U32, mid, [255, 217]))}
    : Maybe<&2, List<&2, U32>>}
