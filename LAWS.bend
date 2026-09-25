# ezimg: the laws. Each law carries the SPEC.md row it proves, or proves part
# of, on its own comment line. PROOF.bend fills them; `bend PROOF.bend` is the
# gate. Every row is pending: the 85 closed laws that stood here were retired
# (docs/rfc/ezimg-law-inventory.md keeps what each one pointed toward), and
# the quantified laws land row by row. The imports keep every module under
# the gate's checker until laws reach them.
import Base
import ./main.bend as Img
import ./src/crc.bend as Crc
import ./src/inflate.bend as Inf
import ./src/png.bend as Png
import ./src/jpeg.bend as Jpeg
import ./src/jpeg_enc.bend as Jenc

# LAW: every sample Jpeg.rgb packs is opaque, for every Y, Cb and Cr
# IMG-PIX-1
law jpeg_rgb_opaque:
  for +yy: U32
  for +cb: U32
  for +cr: U32
  {U32.shrn(Jpeg.rgb(yy, cb, cr), 24n) == 255 : U32}

# LAW: every sample Jpeg.gray packs is opaque, for every level
# IMG-PIX-1
law jpeg_gray_opaque:
  for +yy: U32
  {U32.shrn(Jpeg.gray(yy), 24n) == 255 : U32}

# LAW: encode_jpeg refuses exactly the rasters encode_png refuses
# IMG-JPG-4
law jpeg_png_refuse_alike:
  for +img: Img.Raster
  {Maybe.is_none(&2, List<&2, U32>, Img.encode_jpeg(img)) ==
    Maybe.is_none(&2, List<&2, U32>, Img.encode_png(img)) : Bool}

# every sample's colour, alpha cleared: the specification's own copy
def alpha.drop(px: List<&2, U32>) -> List<&2, U32>:
  match px:
    case Nil{}:
      Nil{}
    case pp <> rest:
      U32.and(16777215, pp) <> alpha.drop(rest)

# LAW: two rasters of one size whose samples differ only in alpha encode to the same JPEG bytes
# IMG-PIX-2
law jpeg_alpha_blind:
  for +ww: U32
  for +hh: U32
  for +pa: List<&2, U32>
  for +pb: List<&2, U32>
  for +same: {alpha.drop(pa) == alpha.drop(pb) : List<&2, U32>}
  {Img.encode_jpeg(Img.raster(ww, hh, pa)) == Img.encode_jpeg(Img.raster(ww, hh, pb)) : Maybe<&2, List<&2, U32>>}

# a sample through a function, or none
def opt.map(~ff: U32 -> U32, mm: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match mm:
    case None{}:
      None{}
    case Some{vv}:
      Some{ff(vv)}

# LAW: map keeps the width and the height
# IMG-RAS-5
law map_size:
  for ~ff: U32 -> U32
  for +img: Img.Raster
  {Img.size(Img.map(~ff, img)) == Img.size(img) : U32 & U32}

# LAW: sample k of map(f, r) is f of sample k of r, for every k, and none past the end
# IMG-RAS-5
law map_at:
  for ~ff: U32 -> U32
  for +img: Img.Raster
  for +kk: Nat
  {List.get(&2, U32, Img.pixels(Img.map(~ff, img)), kk) ==
    opt.map(~ff, List.get(&2, U32, Img.pixels(img), kk)) : Maybe<&2, U32>}

# LAW: bytes that open with the eight signature bytes parse as the signature, whatever follows
# IMG-PNG-1
law sig_opens:
  for +rest: List<&2, U32>
  {Img.parse_signature(List.append(&2, U32, Img.png_sig(), rest)) == Some{Img.png_sig()} : Maybe<&2, List<&2, U32>>}

# LAW: parse_signature is some only when the bytes open with the eight signature bytes
# IMG-PNG-1
law sig_only:
  for +xs: List<&2, U32>
  for h_some: {Maybe.is_some(&2, List<&2, U32>, Img.parse_signature(xs)) == True{} : Bool}
  {xs == List.append(&2, U32, Img.png_sig(), List.drop(&2, U32, xs, 8n)) : List<&2, U32>}

# ---- wp4-png-encode ----

# a sample's alpha is 255: its top byte, shifted down, is 255
def opaque(cc: U32) -> Bool:
  U32.is_eq(U32.shrn(cc, 24n), 255)

# every sample's alpha is 255
def all_opaque(px: List<&2, U32>) -> Bool:
  List.all(~&2, ~U32, ~opaque, px)

# the colour type the PNG specification gives an 8-bit picture: 2 (RGB) when
# every sample is opaque, 6 (RGBA) otherwise
def colour_type(opq: Bool) -> U32:
  match opq:
    case True{}:
      2
    case False{}:
      6

# a word's four bytes, most significant first
def be32(+nn: U32) -> List<&2, U32>:
  [((nn >> 24n : U32) .&. 255 : U32), ((nn >> 16n : U32) .&. 255 : U32), ((nn >> 8n : U32) .&. 255 : U32),
    (nn .&. 255 : U32)]

# the signature, then IHDR's length (13), its type, and its data: width,
# height, bit depth 8, the colour type, compression 0, filter 0, interlace 0
def ihdr_head(+ww: U32, +hh: U32, +ct: U32) -> List<&2, U32>:
  List.append(&2, U32, Img.png_sig(), List.append(&2, U32, [0, 0, 0, 13, 73, 72, 68, 82],
    List.append(&2, U32, be32(ww), List.append(&2, U32, be32(hh), [8, ct, 0, 0, 0]))))

# LAW: an encoded PNG opens with the signature and an IHDR chunk of the
# raster's width and height, bit depth 8, compression, filter and interlace 0,
# and colour type 2 when every sample has alpha 255, 6 otherwise
# IMG-PNG-4
law png_ihdr:
  for +ww: U32
  for +hh: U32
  for +px: List<&2, U32>
  for h_some: {Maybe.is_some(&2, List<&2, U32>, Img.encode_png(Img.raster(ww, hh, px))) == True{} : Bool}
  exs rest: List<&2, U32>
  {Img.encode_png(Img.raster(ww, hh, px)) ==
    Some{List.append(&2, U32, ihdr_head(ww, hh, colour_type(all_opaque(px))), rest)} : Maybe<&2, List<&2, U32>>}
