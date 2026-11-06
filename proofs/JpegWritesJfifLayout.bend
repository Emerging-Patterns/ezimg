# proofs of laws/JpegWritesJfifLayout.bend
import Base
import ../main.bend as Img
import ../src/jpeg_enc.bend as Jenc
import ../laws/JpegWritesJfifLayout.bend as Laws
import ./lemmas/BasicFacts.bend as M1
import ./lemmas/JpegEncoderGuard.bend as M2

# what jpeg_enc_layout says of an encoding mm of a raster of width ww and height hh
def lay.Ty(mm: Maybe<&2, List<&2, U32>>, ww: U32, hh: U32) -> Type:
  &app: List<&2, U32> -> &dq: List<&2, U32> -> &sof: List<&2, U32> -> &dc: List<&2, U32>
    -> &ac: List<&2, U32> -> &sos: List<&2, U32> -> &ent: List<&2, U32>
    -> {mm == Some{Laws.jfif.file(ww, hh, app, dq, sof, dc, ac, sos, ent)} : Maybe<&2, List<&2, U32>>}

# an accepted raster's encoding is the header, the entropy-coded bytes and EOI
def lay.pick(
  ok: Bool,
  +ww: U32,
  +hh: U32,
  +qq: U32,
  +px: List<&2, U32>,
  e_ok: {Img.encode_jpeg.good(ww, hh, px) == ok : Bool},
  h_some: {Maybe.is_some(&2, List<&2, U32>, Img.encode_jpeg.pick(ok, ww, hh, qq, Img.colours(px))) == True{} : Bool}
) -> lay.Ty(Img.encode_jpeg.pick(ok, ww, hh, qq, Img.colours(px)), ww, hh):
  match ok:
    case False{}:
      Empty.absurd(lay.Ty(None{}, ww, hh), M1.false_true(h_some))
    case True{}:
      +cp = Img.colours(px)
      ([1, 1, 0, 0, 1, 0, 1, 0, 0], (0 <> Jenc.encode.join(Jenc.encode.qz(Jenc.encode.lumq(), qq), 1 <>
        Jenc.encode.qz(Jenc.encode.chrq(), qq)), ([3, 1, 17, 0, 2, 17, 1, 3, 17, 1],
        (0 <> Jenc.encode.join(Jenc.encode.join(Jenc.encode.dccounts(), Jenc.encode.dcsyms()), 1 <>
        Jenc.encode.join(Jenc.encode.cdccounts(), Jenc.encode.dcsyms())),
        (16 <> Jenc.encode.join(Jenc.encode.join(Jenc.encode.accounts(), Jenc.encode.acsyms()), 17 <>
        Jenc.encode.join(Jenc.encode.caccounts(), Jenc.encode.cacsyms())), ([3, 1, 0, 2, 17, 3, 17, 0, 63, 0],
        (Jenc.encode.arm(ww, hh, qq, cp),
        Equal.cong(Bool, Maybe<&2, List<&2, U32>>, bb => Some{Jenc.encode.pick(bb, ww, hh, qq, cp)},
          Jenc.encode.bad(ww, hh), False{}, M2.bad(ww, hh, px, e_ok)))))))))

def Laws.jpeg_enc_layout_q(img, qq, h_some):
  match img:
    case Img.Raster{+ww, +hh, +px}:
      lay.pick(Img.encode_jpeg.good(ww, hh, px), ww, hh, qq, px, {==}, h_some)

def Laws.jpeg_enc_layout(img, h_some):
  Laws.jpeg_enc_layout_q(img, Img.encode_jpeg.quality(), h_some)

# what jpeg_enc_ends says of an encoding mm
def ends.Ty(mm: Maybe<&2, List<&2, U32>>) -> Type:
  &mid: List<&2, U32>
    -> {mm == Some{List.append(&2, U32, [255, 216], List.append(&2, U32, mid, [255, 217]))} : Maybe<&2, List<&2, U32>>}

# the encoder's output opens with SOI and closes with EOI, whichever way its size test goes
def ends.bad(
  bad: Bool,
  +ww: U32,
  +hh: U32,
  +qq: U32,
  +cp: List<&2, U32>
) -> ends.Ty(Some{Jenc.encode.pick(bad, ww, hh, qq, cp)}):
  match bad:
    case True{}:
      ([], {==})
    case False{}:
      (List.append(&2, U32, Jenc.encode.join(Jenc.encode.app0(), Jenc.encode.join(Jenc.encode.dqt(qq),
        Jenc.encode.join(Jenc.encode.sof(ww, hh), Jenc.encode.join(Jenc.encode.dht(0, Jenc.encode.dccounts(),
        Jenc.encode.dcsyms(), Jenc.encode.cdccounts(), Jenc.encode.dcsyms()), Jenc.encode.join(Jenc.encode.dht(16,
        Jenc.encode.accounts(), Jenc.encode.acsyms(), Jenc.encode.caccounts(), Jenc.encode.cacsyms()),
        Jenc.encode.sos()))))), Jenc.encode.arm(ww, hh, qq, cp)), {==})

# an accepted raster's encoding opens with SOI and closes with EOI
def ends.pick(
  ok: Bool,
  +ww: U32,
  +hh: U32,
  +qq: U32,
  +cp: List<&2, U32>,
  h_some: {Maybe.is_some(&2, List<&2, U32>, Img.encode_jpeg.pick(ok, ww, hh, qq, cp)) == True{} : Bool}
) -> ends.Ty(Img.encode_jpeg.pick(ok, ww, hh, qq, cp)):
  match ok:
    case False{}:
      Empty.absurd(ends.Ty(None{}), M1.false_true(h_some))
    case True{}:
      ends.bad(Jenc.encode.bad(ww, hh), ww, hh, qq, cp)

def Laws.jpeg_enc_ends_q(img, qq, h_some):
  match img:
    case Img.Raster{+ww, +hh, +px}:
      ends.pick(Img.encode_jpeg.good(ww, hh, px), ww, hh, qq, Img.colours(px), h_some)

def Laws.jpeg_enc_ends(img, h_some):
  Laws.jpeg_enc_ends_q(img, Img.encode_jpeg.quality(), h_some)
