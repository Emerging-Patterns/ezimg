# ezimg: the laws. Closed equalities for the signature, the markers, the
# pixel helpers, and the PNG clauses. PROOF.bend fills them.
import Base
import ./main.bend as Img
import ./crc.bend as Crc
import ./inflate.bend as Inf
import ./png.bend as Png

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

# chunks of a 1 by 1 colour-type-2 image, after the signature
def fix.rgb.body() -> List<&2, U32>:
  [
    0, 0, 0, 13, 73, 72, 68, 82, 0, 0, 0, 1, 0, 0, 0, 1, 8, 2, 0, 0, 0, 144, 119, 83, 222, 0, 0, 0, 15, 73, 68, 65, 84,
    120, 1, 1, 4, 0, 251, 255, 0, 255, 0, 0, 3, 1, 1, 0, 141, 29, 229, 130, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130
  ]

# that image, signature included
def fix.rgb() -> List<&2, U32>:
  List.append(&2, U32, Img.png_sig(), fix.rgb.body())

# chunks of a 1 by 1 colour-type-6 image
def fix.rgba.body() -> List<&2, U32>:
  [
    0, 0, 0, 13, 73, 72, 68, 82, 0, 0, 0, 1, 0, 0, 0, 1, 8, 6, 0, 0, 0, 31, 21, 196, 137, 0, 0, 0, 16, 73, 68, 65, 84,
    120, 1, 1, 5, 0, 250, 255, 0, 255, 0, 0, 128, 4, 129, 1, 128, 25, 47, 133, 176, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66,
    96, 130
  ]

# that image, signature included
def fix.rgba() -> List<&2, U32>:
  List.append(&2, U32, Img.png_sig(), fix.rgba.body())

# chunks of a 1 by 1 colour-type-0 image
def fix.grey.body() -> List<&2, U32>:
  [
    0, 0, 0, 13, 73, 72, 68, 82, 0, 0, 0, 1, 0, 0, 0, 1, 8, 0, 0, 0, 0, 58, 126, 155, 85, 0, 0, 0, 13, 73, 68, 65, 84,
    120, 1, 1, 2, 0, 253, 255, 0, 7, 0, 9, 0, 8, 185, 172, 134, 135, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130
  ]

# that image, signature included
def fix.grey() -> List<&2, U32>:
  List.append(&2, U32, Img.png_sig(), fix.grey.body())

# chunks of a 1 by 1 colour-type-4 image
def fix.ga.body() -> List<&2, U32>:
  [
    0, 0, 0, 13, 73, 72, 68, 82, 0, 0, 0, 1, 0, 0, 0, 1, 8, 4, 0, 0, 0, 181, 28, 12, 2, 0, 0, 0, 14, 73, 68, 65, 84,
    120, 1, 1, 3, 0, 252, 255, 0, 7, 200, 0, 217, 0, 208, 31, 173, 36, 248, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130
  ]

# that image, signature included
def fix.ga() -> List<&2, U32>:
  List.append(&2, U32, Img.png_sig(), fix.ga.body())

# chunks of a 1 by 1 colour-type-3 image
def fix.idx.body() -> List<&2, U32>:
  [
    0, 0, 0, 13, 73, 72, 68, 82, 0, 0, 0, 1, 0, 0, 0, 1, 8, 3, 0, 0, 0, 40, 203, 52, 187, 0, 0, 0, 3, 80, 76, 84, 69,
    255, 0, 0, 25, 226, 9, 55, 0, 0, 0, 13, 73, 68, 65, 84, 120, 1, 1, 2, 0, 253, 255, 0, 0, 0, 2, 0, 1, 126, 5, 13,
    210, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130
  ]

# that image, signature included
def fix.idx() -> List<&2, U32>:
  List.append(&2, U32, Img.png_sig(), fix.idx.body())

# LAW: ISO 3309 / ITU-T V.42 — CRC-32 of the check digits is 3421780262
law crc32_digits:
  {Crc.crc32([49, 50, 51, 52, 53, 54, 55, 56, 57]) == 3421780262 : U32}

# LAW: ISO/IEC 15948 / W3C PNG — CRC-32 of an IHDR type and its data
law crc32_ihdr:
  {Crc.crc32([73, 72, 68, 82, 0, 0, 0, 1, 0, 0, 0, 1, 8, 2, 0, 0, 0]) == 2423739358 : U32}

# LAW: ISO/IEC 15948 / W3C PNG — CRC-32 of the IEND type
law crc32_iend:
  {Crc.crc32([73, 69, 78, 68]) == 2923585666 : U32}

# LAW: ISO/IEC 15948 / W3C PNG — IHDR is width, height, depth, colour, compression, filter, interlace
law parse_ihdr_fields:
  {Png.parse_ihdr([0, 0, 0, 2, 0, 0, 0, 3, 8, 2, 0, 0, 0]) == Some{Png.Ihdr{2, 3, 8, 2, 0, 0, 0}} : Maybe<&2, Png.Ihdr>}

# LAW: ISO/IEC 15948 / W3C PNG — filter None copies the scanline
law unfilter_none:
  {Png.unfilter([0, 10, 20, 30], 3, 1, 1) == Some{[10, 20, 30]} : Maybe<&2, List<&2, U32>>}

# LAW: ISO/IEC 15948 / W3C PNG — filter Sub adds the left neighbour
law unfilter_sub:
  {Png.unfilter([1, 10, 20, 30], 3, 1, 1) == Some{[10, 30, 60]} : Maybe<&2, List<&2, U32>>}

# LAW: ISO/IEC 15948 / W3C PNG — filter Up adds the byte above
law unfilter_up:
  {Png.unfilter([0, 1, 2, 3, 2, 4, 5, 6], 3, 2, 1) == Some{[1, 2, 3, 5, 7, 9]} : Maybe<&2, List<&2, U32>>}

# LAW: ISO/IEC 15948 / W3C PNG — filter Average adds the mean of left and above
law unfilter_average:
  {Png.unfilter([3, 10, 20], 2, 1, 1) == Some{[10, 25]} : Maybe<&2, List<&2, U32>>}

# LAW: ISO/IEC 15948 / W3C PNG — filter Paeth adds the Paeth predictor
law unfilter_paeth:
  {Png.unfilter([0, 10, 20, 4, 5, 6], 2, 2, 1) == Some{[10, 20, 15, 26]} : Maybe<&2, List<&2, U32>>}

# LAW: PNG compression method 0 — a stored zlib block inflates to its payload
law inflate_stored:
  {Inf.inflate([120, 1, 1, 4, 0, 251, 255, 0, 255, 0, 0, 3, 1, 1, 0])
    == Some{[0, 255, 0, 0]} : Maybe<&2, List<&2, U32>>}

# LAW: ISO/IEC 15948 / W3C PNG — chunks after the signature decode colour type 2
law decode_chunks:
  {Png.decode(fix.rgb.body()) == Some{Png.Pic{1, 1, [4294901760]}} : Maybe<&2, Png.Pic>}

# LAW: ISO/IEC 15948 / W3C PNG — 8-bit colour type 2, interlace 0, is opaque red
law decode_png_rgb:
  {Img.decode_png(fix.rgb()) == Some{Img.raster(1, 1, [4294901760])} : Maybe<&2, Img.Raster>}

# LAW: ISO/IEC 15948 / W3C PNG — 8-bit colour type 6 keeps the alpha sample
law decode_png_rgba:
  {Img.decode_png(fix.rgba()) == Some{Img.raster(1, 1, [2164195328])} : Maybe<&2, Img.Raster>}

# LAW: ISO/IEC 15948 / W3C PNG — 8-bit colour type 0 expands grey to opaque RGB
law decode_png_grey:
  {Img.decode_png(fix.grey()) == Some{Img.raster(1, 1, [4278650631])} : Maybe<&2, Img.Raster>}

# LAW: ISO/IEC 15948 / W3C PNG — 8-bit colour type 4 keeps grey and alpha
law decode_png_ga:
  {Img.decode_png(fix.ga()) == Some{Img.raster(1, 1, [3355903751])} : Maybe<&2, Img.Raster>}

# LAW: ISO/IEC 15948 / W3C PNG — 8-bit colour type 3 reads the palette index
law decode_png_idx:
  {Img.decode_png(fix.idx()) == Some{Img.raster(1, 1, [4294901760])} : Maybe<&2, Img.Raster>}
