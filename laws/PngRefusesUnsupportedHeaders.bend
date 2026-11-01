# `decode_png` returns none for every input whose IHDR has a bit depth other
# than 8, an interlace method other than 0, or a colour type outside 0, 2, 3,
# 4 and 6.
import Base
import ../main.bend as Img
import ./defs/PngSpecification.bend as D1

# a PNG file whose first chunk is an IHDR: the signature, the length 13, the
# type IHDR, width, height, bit depth, colour type, compression, filter and
# interlace methods, any four CRC bytes, and any bytes after
def spec.ihdr.file(
  +ww: U32,
  +hh: U32,
  +dd: U32,
  +cc: U32,
  +comp: U32,
  +ff: U32,
  +ii: U32,
  +crc: U32,
  rest: List<&2, U32>
) -> List<&2, U32>:
  List.append(&2, U32, Img.png_sig(), List.append(&2, U32, [0, 0, 0, 13, 73, 72, 68, 82],
    List.append(&2, U32, D1.spec.be4(ww), List.append(&2, U32, D1.spec.be4(hh), List.append(&2, U32, [dd, cc, comp, ff,
        ii],
      List.append(&2, U32, D1.spec.be4(crc), rest))))))

# LAW: an IHDR whose bit depth is not 8 makes decode_png none, whatever the other fields, the CRC and the rest
law png_depth_refused:
  for +ww: U32
  for +hh: U32
  for +dd: U32
  for +cc: U32
  for +comp: U32
  for +ff: U32
  for +ii: U32
  for +crc: U32
  for +rest: List<&2, U32>
  for h_dd: {U32.is_eq(dd, 8) == False{} : Bool}
  {Img.decode_png(spec.ihdr.file(ww, hh, dd, cc, comp, ff, ii, crc, rest)) == None{} : Maybe<&2, Img.Raster>}

# LAW: an IHDR whose interlace method is not 0 makes decode_png none, whatever the other fields, the CRC and the rest
law png_interlace_refused:
  for +ww: U32
  for +hh: U32
  for +dd: U32
  for +cc: U32
  for +comp: U32
  for +ff: U32
  for +ii: U32
  for +crc: U32
  for +rest: List<&2, U32>
  for h_ii: {U32.is_eq(ii, 0) == False{} : Bool}
  {Img.decode_png(spec.ihdr.file(ww, hh, dd, cc, comp, ff, ii, crc, rest)) == None{} : Maybe<&2, Img.Raster>}

# LAW: an IHDR whose colour type is not 0, 2, 3, 4 or 6 makes decode_png none, whatever the other fields, the CRC
# and the rest
law png_colour_refused:
  for +ww: U32
  for +hh: U32
  for +dd: U32
  for +cc: U32
  for +comp: U32
  for +ff: U32
  for +ii: U32
  for +crc: U32
  for +rest: List<&2, U32>
  for h_cc: {D1.spec.colour.ok(cc) == False{} : Bool}
  {Img.decode_png(spec.ihdr.file(ww, hh, dd, cc, comp, ff, ii, crc, rest)) == None{} : Maybe<&2, Img.Raster>}
