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

# LAW: get reads the sample at a point inside the picture
law get_inside:
  {Img.get(swatch(), 1, 1) == Some{6} : Maybe<&2, U32>}

# LAW: get is none when x is outside the picture
law get_outside_x:
  {Img.get(swatch(), 2, 0) == None{} : Maybe<&2, U32>}

# LAW: get is none when y is outside the picture
law get_outside_y:
  {Img.get(swatch(), 0, 3) == None{} : Maybe<&2, U32>}

# LAW: set writes the sample at a point inside the picture
law set_inside:
  {Img.set(swatch(), 1, 1, 1) == Img.raster(2, 3, [9, 8, 7, 1, 5, 4]) : Img.Raster}

# LAW: set outside the picture leaves it unchanged
law set_outside:
  {Img.set(swatch(), 4, 1, 1) == swatch() : Img.Raster}

# LAW: get reads back what set wrote
law set_get:
  {Img.get(Img.set(swatch(), 0, 2, 3), 0, 2) == Some{3} : Maybe<&2, U32>}

# LAW: cropping the whole picture is the picture
law crop_all:
  {Img.crop(swatch(), 0, 0, 2, 3) == swatch() : Img.Raster}

# LAW: crop keeps the rectangle that sits inside
law crop_rect:
  {Img.crop(swatch(), 1, 1, 1, 2) == Img.raster(1, 2, [6, 4]) : Img.Raster}

# LAW: a rectangle past the edge is clipped to the picture
law crop_clip:
  {Img.crop(swatch(), 1, 2, 4, 4) == Img.raster(1, 1, [4]) : Img.Raster}

# LAW: a rectangle that misses the picture is empty
law crop_miss:
  {Img.crop(swatch(), 2, 0, 1, 1) == Img.raster(0, 0, []) : Img.Raster}

# LAW: a zero side is an empty picture
law crop_zero:
  {Img.crop(swatch(), 0, 0, 2, 0) == Img.raster(0, 0, []) : Img.Raster}

# LAW: blit copies source samples onto dest at the offset
law blit_at:
  {Img.blit(Img.fill(3, 2, 0), Img.raster(2, 2, [1, 2, 3, 4]), 1, 0)
    == Img.raster(3, 2, [0, 1, 2, 0, 3, 4]) : Img.Raster}

# LAW: blit drops the source samples that fall outside dest
law blit_clip:
  {Img.blit(Img.fill(3, 2, 0), Img.raster(2, 2, [1, 2, 3, 4]), 2, 1)
    == Img.raster(3, 2, [0, 0, 0, 0, 0, 1]) : Img.Raster}

# LAW: blit entirely outside dest leaves dest unchanged
law blit_miss:
  {Img.blit(swatch(), Img.raster(1, 1, [9]), 5, 5) == swatch() : Img.Raster}

# LAW: map sends every sample through the function
law map_inc:
  {Img.map(~(c => (c + 1 : U32)), swatch())
    == Img.raster(2, 3, [10, 9, 8, 7, 6, 5]) : Img.Raster}

# LAW: samples are opaque U32 values, so premultiply leaves the picture
law premultiply_opaque:
  {Img.premultiply(swatch()) == swatch() : Img.Raster}

# LAW: an opaque sample is already straight, so straight leaves the picture
law straight_opaque:
  {Img.straight(swatch()) == swatch() : Img.Raster}

# LAW: straight after premultiply is the picture
law straight_premultiply:
  {Img.straight(Img.premultiply(swatch())) == swatch() : Img.Raster}
