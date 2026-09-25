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
