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
# ---- wp5-png-decode ----

# the four bytes of a U32, most significant first
def spec.be4(+nn: U32) -> List<&2, U32>:
  [U32.and(255, U32.shrn(nn, 24n)), U32.and(255, U32.shrn(nn, 16n)), U32.and(255, U32.shrn(nn, 8n)), U32.and(255, nn)]

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
    List.append(&2, U32, spec.be4(ww), List.append(&2, U32, spec.be4(hh), List.append(&2, U32, [dd, cc, comp, ff, ii],
      List.append(&2, U32, spec.be4(crc), rest))))))

# the colour types the PNG specification defines for bit depth 8
def spec.colour.ok(+cc: U32) -> Bool:
  Bool.or(U32.is_eq(cc, 0), Bool.or(U32.is_eq(cc, 2), Bool.or(U32.is_eq(cc, 3), Bool.or(U32.is_eq(cc, 4),
    U32.is_eq(cc, 6)))))

# LAW: an IHDR whose bit depth is not 8 makes decode_png none, whatever the other fields, the CRC and the rest
# IMG-PNG-8
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
# IMG-PNG-8
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
# IMG-PNG-8
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
  for h_cc: {spec.colour.ok(cc) == False{} : Bool}
  {Img.decode_png(spec.ihdr.file(ww, hh, dd, cc, comp, ff, ii, crc, rest)) == None{} : Maybe<&2, Img.Raster>}

# a sample packed 0xAARRGGBB: alpha in the top byte, then red, green and blue
def spec.argb(+aa: U32, +rr: U32, +gg: U32, +bb: U32) -> U32:
  ((((aa << 24n : U32) .|. (rr << 16n : U32) : U32) .|. (gg << 8n : U32) : U32) .|. bb : U32)

# the alpha of a sample checked against a tRNS key: 0 when it matches, 255 otherwise
def spec.key.alpha(hit: Bool) -> U32:
  match hit:
    case True{}:
      0
    case False{}:
      255

# a list of samples, or none
def spec.cons(+hd: U32, mm: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match mm:
    case None{}:
      None{}
    case Some{tl}:
      Some{hd <> tl}

# colour type 0: each gray byte g is 0xFFgggggg
def spec.grey(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case +gg <> tl:
      spec.argb(255, gg, gg, gg) <> spec.grey(tl)

# colour type 0 with a tRNS key: a gray byte equal to the key has alpha 0
def spec.grey.key(xs: List<&2, U32>, +kk: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case +gg <> tl:
      spec.argb(spec.key.alpha(U32.is_eq(gg, kk)), gg, gg, gg) <> spec.grey.key(tl, kk)

# colour type 4: each gray and alpha pair is 0xAAgggggg; none when a pair is cut short
def spec.ga(xs: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case +gg <> +aa <> tl:
      spec.cons(spec.argb(aa, gg, gg, gg), spec.ga(tl))
    case _xs:
      None{}

# colour type 2: each RGB triple is 0xFFrrggbb; none when a triple is cut short
def spec.rgb(xs: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case +rr <> +gg <> +bb <> tl:
      spec.cons(spec.argb(255, rr, gg, bb), spec.rgb(tl))
    case _xs:
      None{}

# colour type 2 with a tRNS key: a triple equal to the key in all three channels has alpha 0
def spec.rgb.key(xs: List<&2, U32>, +kr: U32, +kg: U32, +kb: U32) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case +rr <> +gg <> +bb <> tl:
      spec.cons(spec.argb(spec.key.alpha(Bool.and(U32.is_eq(rr, kr), Bool.and(U32.is_eq(gg, kg), U32.is_eq(bb, kb)))),
        rr, gg, bb), spec.rgb.key(tl, kr, kg, kb))
    case _xs:
      None{}

# colour type 6: each RGBA quadruple is 0xAArrggbb; none when one is cut short
def spec.rgba(xs: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case +rr <> +gg <> +bb <> +aa <> tl:
      spec.cons(spec.argb(aa, rr, gg, bb), spec.rgba(tl))
    case _xs:
      None{}

# the palette: entry k is PLTE's triple k packed with alpha tRNS byte k, or
# 255 past the end of tRNS
def spec.pal(xs: List<&2, U32>, als: List<&2, U32>) -> List<&2, U32>:
  match xs als:
    case +rr <> +gg <> +bb <> tl Nil{}:
      spec.argb(255, rr, gg, bb) <> spec.pal(tl, [])
    case +rr <> +gg <> +bb <> tl +aa <> at:
      spec.argb(aa, rr, gg, bb) <> spec.pal(tl, at)
    case _xs _als:
      Nil{}

# one index's entry, if the palette has it, before the rest
def spec.idx.at(me: Maybe<&2, U32>, rest: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match me:
    case None{}:
      None{}
    case Some{+cc}:
      spec.cons(cc, rest)

# colour type 3: each index is its palette entry; none when an index is past the palette
def spec.idx(xs: List<&2, U32>, +pal: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case +ix <> tl:
      spec.idx.at(List.get(&2, U32, pal, U32.to_nat(ix)), spec.idx(tl, pal))

# LAW: colour type 0 without tRNS: each gray byte g decodes to 0xFFgggggg
# IMG-PNG-9
law png_px_grey:
  for +xs: List<&2, U32>
  {Png.px.of(0, xs, [], []) == Some{spec.grey(xs)} : Maybe<&2, List<&2, U32>>}

# LAW: colour type 0 with tRNS key k: each gray byte g decodes to 0xFFgggggg, alpha 0 when g is k
# IMG-PNG-9
law png_px_grey_key:
  for +xs: List<&2, U32>
  for +kk: U32
  {Png.px.of(0, xs, [], [0, kk]) == Some{spec.grey.key(xs, kk)} : Maybe<&2, List<&2, U32>>}

# LAW: colour type 4: each gray and alpha pair decodes to 0xAAgggggg
# IMG-PNG-9
law png_px_ga:
  for +xs: List<&2, U32>
  {Png.px.of(4, xs, [], []) == spec.ga(xs) : Maybe<&2, List<&2, U32>>}

# LAW: colour type 2 without tRNS: each RGB triple decodes to 0xFFrrggbb, whatever suggested palette there is
# IMG-PNG-9
law png_px_rgb:
  for +xs: List<&2, U32>
  for +plte: List<&2, U32>
  {Png.px.of(2, xs, plte, []) == spec.rgb(xs) : Maybe<&2, List<&2, U32>>}

# LAW: colour type 2 with tRNS key (kr, kg, kb): each triple decodes to 0xFFrrggbb, alpha 0 when it is the key
# IMG-PNG-9
law png_px_rgb_key:
  for +xs: List<&2, U32>
  for +plte: List<&2, U32>
  for +kr: U32
  for +kg: U32
  for +kb: U32
  {Png.px.of(2, xs, plte, [0, kr, 0, kg, 0, kb]) == spec.rgb.key(xs, kr, kg, kb) : Maybe<&2, List<&2, U32>>}

# LAW: colour type 6: each RGBA quadruple decodes to 0xAArrggbb, whatever suggested palette there is
# IMG-PNG-9
law png_px_rgba:
  for +xs: List<&2, U32>
  for +plte: List<&2, U32>
  {Png.px.of(6, xs, plte, []) == spec.rgba(xs) : Maybe<&2, List<&2, U32>>}

# LAW: colour type 3: when the indices decode, each is its palette entry with alpha from tRNS or 255
# IMG-PNG-9
law png_px_indexed:
  for +xs: List<&2, U32>
  for +plte: List<&2, U32>
  for +trns: List<&2, U32>
  for h_some: {Maybe.is_some(&2, List<&2, U32>, Png.px.of(3, xs, plte, trns)) == True{} : Bool}
  {Png.px.of(3, xs, plte, trns) == spec.idx(xs, spec.pal(plte, trns)) : Maybe<&2, List<&2, U32>>}

# the samples of the unfiltered bytes, when the scanlines unfilter
def spec.px.then(
  mm: Maybe<&2, List<&2, U32>>,
  +colour: U32,
  plte: List<&2, U32>,
  trns: List<&2, U32>
) -> Maybe<&2, List<&2, U32>>:
  match mm:
    case None{}:
      None{}
    case Some{raw}:
      Png.px.of(colour, raw, plte, trns)

# a picture of those samples, when there are some
def spec.pic(mm: Maybe<&2, List<&2, U32>>, +ww: U32, +hh: U32) -> Maybe<&2, Png.Pic>:
  match mm:
    case None{}:
      None{}
    case Some{px}:
      Some{Png.Pic{ww, hh, px}}

# LAW: the decoder's last stage packs the unfiltered bytes of the inflated IDAT data with px.of, for the IHDR's
# colour type, PLTE and tRNS, and keeps the width and height
# IMG-PNG-9
law png_samples_frame:
  for +raw: List<&2, U32>
  for +ww: U32
  for +hh: U32
  for +colour: U32
  for +plte: List<&2, U32>
  for +trns: List<&2, U32>
  {Png.png.samples(Some{raw}, ww, hh, colour, plte, trns) ==
    spec.pic(spec.px.then(Png.unfilter(raw, ww, hh, Png.png.bpp(colour)), colour, plte, trns), ww, hh)
    : Maybe<&2, Png.Pic>}
