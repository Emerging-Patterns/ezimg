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

# an accepted raster's encoding, in either layout, is the header, the entropy-coded bytes and EOI
def lay.kd(
  +kd: Jenc.Layout,
  +ww: U32,
  +hh: U32,
  +qq: U32,
  +cp: List<&2, U32>
) -> lay.Ty(Some{Jenc.encode.pick(False{}, ww, hh, qq, kd, cp)}, ww, hh):
  match kd:
    case Jenc.K444{}:
      ([1, 1, 0, 0, 1, 0, 1, 0, 0], (Jenc.encode.dqtbody(Jenc.K444{}, qq), (Jenc.encode.sofcomps(Jenc.K444{}),
        (Jenc.encode.dcbody(Jenc.K444{}), (Jenc.encode.acbody(Jenc.K444{}), (Jenc.encode.sosbody(Jenc.K444{}),
        (Jenc.encode.arm(ww, hh, qq, Jenc.K444{}, cp), {==})))))))
    case Jenc.KGray{}:
      ([1, 1, 0, 0, 1, 0, 1, 0, 0], (Jenc.encode.dqtbody(Jenc.KGray{}, qq), (Jenc.encode.sofcomps(Jenc.KGray{}),
        (Jenc.encode.dcbody(Jenc.KGray{}), (Jenc.encode.acbody(Jenc.KGray{}), (Jenc.encode.sosbody(Jenc.KGray{}),
        (Jenc.encode.arm(ww, hh, qq, Jenc.KGray{}, cp), {==})))))))
    case Jenc.K420{}:
      ([1, 1, 0, 0, 1, 0, 1, 0, 0], (Jenc.encode.dqtbody(Jenc.K420{}, qq), (Jenc.encode.sofcomps(Jenc.K420{}),
        (Jenc.encode.dcbody(Jenc.K420{}), (Jenc.encode.acbody(Jenc.K420{}), (Jenc.encode.sosbody(Jenc.K420{}),
        (Jenc.encode.arm(ww, hh, qq, Jenc.K420{}, cp), {==})))))))

# an accepted raster's encoding is the header, the entropy-coded bytes and EOI
def lay.pick(
  ok: Bool,
  +ww: U32,
  +hh: U32,
  +qq: U32,
  +sub: Bool,
  +px: List<&2, U32>,
  e_ok: {Img.encode_jpeg.good(ww, hh, px) == ok : Bool},
  h_some: {Maybe.is_some(&2, List<&2, U32>, Img.encode_jpeg.pick(ok, ww, hh, qq, sub, Img.colours(px))) == True{} :
    Bool}
) -> lay.Ty(Img.encode_jpeg.pick(ok, ww, hh, qq, sub, Img.colours(px)), ww, hh):
  match ok:
    case False{}:
      Empty.absurd(lay.Ty(None{}, ww, hh), M1.false_true(h_some))
    case True{}:
      +cp = Img.colours(px)
      +kd = Jenc.encode.kindof(sub, cp)
      eb = Equal.cong(Bool, Maybe<&2, List<&2, U32>>, bb => Some{Jenc.encode.pick(bb, ww, hh, qq, kd, cp)},
        Jenc.encode.bad(ww, hh), False{}, M2.bad(ww, hh, px, e_ok))
      es = Equal.sym(Maybe<&2, List<&2, U32>>, Some{Jenc.encode.pick(Jenc.encode.bad(ww, hh), ww, hh, qq, kd, cp)},
        Some{Jenc.encode.pick(False{}, ww, hh, qq, kd, cp)}, eb)
      %es : lay.Ty(_, ww, hh)
      lay.kd(kd, ww, hh, qq, cp)

def Laws.jpeg_enc_layout_q(img, qq, sub, h_some):
  match img:
    case Img.Raster{+ww, +hh, +px}:
      lay.pick(Img.encode_jpeg.good(ww, hh, px), ww, hh, qq, sub, px, {==}, h_some)

def Laws.jpeg_enc_layout(img, h_some):
  Laws.jpeg_enc_layout_q(img, Img.encode_jpeg.quality(), True{}, h_some)

# what jpeg_enc_ends says of an encoding mm
def ends.Ty(mm: Maybe<&2, List<&2, U32>>) -> Type:
  &mid: List<&2, U32>
    -> {mm == Some{List.append(&2, U32, [255, 216], List.append(&2, U32, mid, [255, 217]))} : Maybe<&2, List<&2, U32>>}

# the encoder's accepted output, in either layout, opens with SOI and closes with EOI
def ends.kd(
  +kd: Jenc.Layout,
  +ww: U32,
  +hh: U32,
  +qq: U32,
  +cp: List<&2, U32>
) -> ends.Ty(Some{Jenc.encode.pick(False{}, ww, hh, qq, kd, cp)}):
  match kd:
    case Jenc.K444{}:
      (List.append(&2, U32, Jenc.encode.join(Jenc.encode.app0(), Jenc.encode.join(Jenc.encode.dqt(Jenc.K444{}, qq),
        Jenc.encode.join(Jenc.encode.sof(Jenc.K444{}, ww, hh), Jenc.encode.join(Jenc.encode.seg(196,
        Jenc.encode.dcbody(Jenc.K444{})), Jenc.encode.join(Jenc.encode.seg(196, Jenc.encode.acbody(Jenc.K444{})),
        Jenc.encode.seg(218, Jenc.encode.sosbody(Jenc.K444{}))))))), Jenc.encode.arm(ww, hh, qq, Jenc.K444{}, cp)),
        {==})
    case Jenc.KGray{}:
      (List.append(&2, U32, Jenc.encode.join(Jenc.encode.app0(), Jenc.encode.join(Jenc.encode.dqt(Jenc.KGray{}, qq),
        Jenc.encode.join(Jenc.encode.sof(Jenc.KGray{}, ww, hh), Jenc.encode.join(Jenc.encode.seg(196,
        Jenc.encode.dcbody(Jenc.KGray{})), Jenc.encode.join(Jenc.encode.seg(196, Jenc.encode.acbody(Jenc.KGray{})),
        Jenc.encode.seg(218, Jenc.encode.sosbody(Jenc.KGray{}))))))), Jenc.encode.arm(ww, hh, qq, Jenc.KGray{}, cp)),
        {==})
    case Jenc.K420{}:
      (List.append(&2, U32, Jenc.encode.join(Jenc.encode.app0(), Jenc.encode.join(Jenc.encode.dqt(Jenc.K420{}, qq),
        Jenc.encode.join(Jenc.encode.sof(Jenc.K420{}, ww, hh), Jenc.encode.join(Jenc.encode.seg(196,
        Jenc.encode.dcbody(Jenc.K420{})), Jenc.encode.join(Jenc.encode.seg(196, Jenc.encode.acbody(Jenc.K420{})),
        Jenc.encode.seg(218, Jenc.encode.sosbody(Jenc.K420{}))))))), Jenc.encode.arm(ww, hh, qq, Jenc.K420{}, cp)),
        {==})

# the encoder's output opens with SOI and closes with EOI, whichever way its size test goes
def ends.bad(
  bad: Bool,
  +ww: U32,
  +hh: U32,
  +qq: U32,
  +kd: Jenc.Layout,
  +cp: List<&2, U32>
) -> ends.Ty(Some{Jenc.encode.pick(bad, ww, hh, qq, kd, cp)}):
  match bad:
    case True{}:
      ([], {==})
    case False{}:
      ends.kd(kd, ww, hh, qq, cp)

# an accepted raster's encoding opens with SOI and closes with EOI
def ends.pick(
  ok: Bool,
  +ww: U32,
  +hh: U32,
  +qq: U32,
  +sub: Bool,
  +cp: List<&2, U32>,
  h_some: {Maybe.is_some(&2, List<&2, U32>, Img.encode_jpeg.pick(ok, ww, hh, qq, sub, cp)) == True{} : Bool}
) -> ends.Ty(Img.encode_jpeg.pick(ok, ww, hh, qq, sub, cp)):
  match ok:
    case False{}:
      Empty.absurd(ends.Ty(None{}), M1.false_true(h_some))
    case True{}:
      ends.bad(Jenc.encode.bad(ww, hh), ww, hh, qq, Jenc.encode.kindof(sub, cp), cp)

def Laws.jpeg_enc_ends_q(img, qq, sub, h_some):
  match img:
    case Img.Raster{+ww, +hh, +px}:
      ends.pick(Img.encode_jpeg.good(ww, hh, px), ww, hh, qq, sub, Img.colours(px), h_some)

def Laws.jpeg_enc_ends(img, h_some):
  Laws.jpeg_enc_ends_q(img, Img.encode_jpeg.quality(), True{}, h_some)
