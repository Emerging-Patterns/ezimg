# `decode_png` returns none for every input whose IHDR pairs a colour type
# with a bit depth PNG table 11.1 does not list (so every colour type other
# than 0, 2, 3, 4 and 6), or has an interlace method other than 0 (none) and
# 1 (Adam7), or a width or height of 2^31 or more (PNG section 11.2.1 allows
# 1 to 2^31 - 1). Every pairing the table lists, at either interlace method,
# with sides in that range, passes the IHDR check. Until 2026-11 the decoder
# refused every bit depth but 8 and Adam7, and took any nonzero side; reading
# those depths and Adam7, and refusing sides of 2^31 or more, are deliberate
# changes.
import Base
import ../main.bend as Img
import ../src/png.bend as Png
import ./defs/PngSpecification.bend as D1
import ./defs/SizeBounds.bend as D2

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

# LAW: an IHDR whose colour type and bit depth table 11.1 does not pair makes decode_png none, whatever the other
# fields, the CRC and the rest
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
  for h_dd: {D1.spec.depth.ok(cc, dd) == False{} : Bool}
  {Img.decode_png(spec.ihdr.file(ww, hh, dd, cc, comp, ff, ii, crc, rest)) == None{} : Maybe<&2, Img.Raster>}

# LAW: an IHDR whose interlace method is neither 0 nor 1 makes decode_png none, whatever the other fields, the CRC
# and the rest
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
  for h_ii: {D1.spec.inter.ok(ii) == False{} : Bool}
  {Img.decode_png(spec.ihdr.file(ww, hh, dd, cc, comp, ff, ii, crc, rest)) == None{} : Maybe<&2, Img.Raster>}

# LAW: an IHDR whose width or height is 2^31 or more makes decode_png none, whatever the other fields, the CRC and
# the rest
law png_size_refused:
  for +ww: U32
  for +hh: U32
  for +dd: U32
  for +cc: U32
  for +comp: U32
  for +ff: U32
  for +ii: U32
  for +crc: U32
  for +rest: List<&2, U32>
  for h_big: {Bool.and(D2.below(31n, U32.to_nat(ww)), D2.below(31n, U32.to_nat(hh))) == False{} : Bool}
  {Img.decode_png(spec.ihdr.file(ww, hh, dd, cc, comp, ff, ii, crc, rest)) == None{} : Maybe<&2, Img.Raster>}

# LAW: the IHDR check takes every pairing table 11.1 lists, at interlace method 0 or 1, with sides from 1 to
# 2^31 - 1 and compression and filter method 0
law png_header_takes:
  for +ww: U32
  for +hh: U32
  for +dd: U32
  for +cc: U32
  for +ii: U32
  for h_ww: {D1.spec.side(ww) == True{} : Bool}
  for h_hh: {D1.spec.side(hh) == True{} : Bool}
  for h_dd: {D1.spec.depth.ok(cc, dd) == True{} : Bool}
  for h_ii: {D1.spec.inter.ok(ii) == True{} : Bool}
  {Png.png.good(ww, hh, dd, cc, 0, 0, ii) == True{} : Bool}
