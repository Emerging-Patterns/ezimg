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

# ---- wp2-inflate ----

# every value is at most 255, and `ok` carries that forward
def bytes.go(xs: List<&2, U32>, ok: Bool) -> Bool:
  match xs ok:
    case _xs False{}:
      False{}
    case Nil{} True{}:
      True{}
    case +xx <> tl True{}:
      bytes.go(tl, U32.is_le(xx, 255))

# every value of xs is a byte, 0 to 255
def bytes(xs: List<&2, U32>) -> Bool:
  bytes.go(xs, True{})

# the zlib stream ezimg writes for xs in stored blocks of at most sz bytes:
# CMF and FLG 120 1, the encoder's stored blocks, and the Adler-32 of xs
def zlib.stored(+sz: U32, +xs: List<&2, U32>) -> List<&2, U32>:
  Png.enc.cat([120, 1], Png.enc.cat(Png.enc.blocks(sz, xs), Png.enc.be(Inf.adler.of(xs))))

# LAW: every byte list with fewer than 2^32 bytes, in the zlib stream ezimg writes with stored blocks of any size from 1
# to 65535, inflates to itself
# IMG-PNG-7
law inflate_stored:
  for +sz: U32
  for +xs: List<&2, U32>
  for h_sz: {Bool.and(U32.is_le(1, sz), U32.is_le(sz, 65535)) == True{} : Bool}
  for h_by: {bytes(xs) == True{} : Bool}
  for h_n: {U32.to_nat(Png.enc.len(xs, 0)) == List.length(&2, U32, xs) : Nat}
  {Inf.inflate(zlib.stored(sz, xs)) == Some{xs} : Maybe<&2, List<&2, U32>>}

# LAW: the zlib stream enc.zlib writes for a PNG's IDAT inflates to the bytes it was given
# IMG-PNG-7
law inflate_enc_zlib:
  for +xs: List<&2, U32>
  for h_by: {bytes(xs) == True{} : Bool}
  for h_n: {U32.to_nat(Png.enc.len(xs, 0)) == List.length(&2, U32, xs) : Nat}
  {Inf.inflate(Png.enc.zlib(xs, Png.enc.len(xs, 0))) == Some{xs} : Maybe<&2, List<&2, U32>>}
