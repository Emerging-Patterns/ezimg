# ezimg: the laws. Closed equalities for the signature, the markers, and the
# pixel helpers. PROOF.bend fills them.
import Base
import ./main.bend as Img

# a 2 by 3 picture, six samples
def swatch() -> Img.Raster:
  Img.raster(2, 3, [9, 8, 7, 6, 5, 4])

# LAW: ISO/IEC 15948 / W3C PNG — the signature is these eight bytes
law png_signature:
  {Img.png_sig() == [137, 80, 78, 71, 13, 10, 26, 10] : List<&2, U32>}

# LAW: the PNG signature is eight bytes long
law png_signature_len:
  {Img.nbytes(Img.png_sig()) == 8 : U32}

# LAW: ISO/IEC 10918-1 | ITU-T T.81 — a JPEG opens with FF D8
law jpeg_marker:
  {Img.jpeg_soi() == [255, 216] : List<&2, U32>}

# LAW: width reads the width a picture was built with
law width_reads:
  {Img.width(swatch()) == 2 : U32}

# LAW: height reads the height a picture was built with
law height_reads:
  {Img.height(swatch()) == 3 : U32}

# LAW: pixels reads the samples a picture was built with
law pixels_read:
  {Img.pixels(swatch()) == [9, 8, 7, 6, 5, 4] : List<&2, U32>}

# LAW: size is the width and the height
law size_pair:
  {Img.size(swatch()) == (2, 3) : U32 & U32}

# LAW: the sample count is width times height
law count_is_area:
  {Img.count(swatch()) == 6 : U32}

# LAW: a solid fill is that sample, width times height times
law fill_solid:
  {Img.fill(2, 2, 7) == Img.raster(2, 2, [7, 7, 7, 7]) : Img.Raster}

# LAW: a PNG signature parses as itself
law parse_png_sig:
  {Img.parse_signature(Img.png_sig()) == Some{Img.png_sig()} : Maybe<&2, List<&2, U32>>}

# LAW: bytes after the signature still parse as the signature
law parse_png_prefix:
  {Img.parse_signature(List.append(&2, U32, Img.png_sig(), [1, 2]))
    == Some{Img.png_sig()} : Maybe<&2, List<&2, U32>>}

# LAW: a JPEG marker is not a PNG signature
law parse_jpeg_not_png:
  {Img.parse_signature(Img.jpeg_soi()) == None{} : Maybe<&2, List<&2, U32>>}

# LAW: PNG decode returns none
law decode_png_none:
  {Img.decode_png(Img.png_sig()) == None{} : Maybe<&2, Img.Raster>}

# LAW: JPEG decode returns none
law decode_jpeg_none:
  {Img.decode_jpeg(Img.jpeg_soi()) == None{} : Maybe<&2, Img.Raster>}
