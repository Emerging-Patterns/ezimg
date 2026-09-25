# ezimg: the proofs. `bend PROOF.bend` is the gate: its first line must be
# exactly `All terms check.`
import Base
import ./LAWS.bend as Laws
import ./main.bend as Img
import ./src/png.bend as Png
import ./src/jpeg.bend as Jpeg

# U32.or with 0xFF000000 first has alpha 255, whatever the other operand:
# the 32 bits are taken apart four at a time, and Bool.or(True, b) is True.
def alpha.first(xx: U32) -> {U32.shrn(U32.or(4278190080, xx), 24n) == 255 : U32}:
  match xx:
    case U32{w0}:
      match w0:
        case WCon{_b0, WCon{_b1, WCon{_b2, WCon{_b3, w4}}}}:
          match w4:
            case WCon{_b4, WCon{_b5, WCon{_b6, WCon{_b7, w8}}}}:
              match w8:
                case WCon{_b8, WCon{_b9, WCon{_b10, WCon{_b11, w12}}}}:
                  match w12:
                    case WCon{_b12, WCon{_b13, WCon{_b14, WCon{_b15, w16}}}}:
                      match w16:
                        case WCon{_b16, WCon{_b17, WCon{_b18, WCon{_b19, w20}}}}:
                          match w20:
                            case WCon{_b20, WCon{_b21, WCon{_b22, WCon{_b23, w24}}}}:
                              match w24:
                                case WCon{_b24, WCon{_b25, WCon{_b26, WCon{_b27, w28}}}}:
                                  match w28:
                                    case WCon{_b28, WCon{_b29, WCon{_b30, WCon{_b31, w32}}}}:
                                      match w32:
                                        case WNil{}:
                                          {==}

def Laws.jpeg_rgb_opaque(yy, cb, cr):
  alpha.first(Jpeg.rgb.bits(yy, cb, cr))

def Laws.jpeg_gray_opaque(yy):
  alpha.first(Jpeg.gray.bits(yy))

# encode_jpeg and encode_png branch on the same guard, so they are none together
def refuse.alike(
  ok: Bool,
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>
) -> {Maybe.is_none(&2, List<&2, U32>, Img.encode_jpeg.pick(ok, ww, hh, px)) ==
  Maybe.is_none(&2, List<&2, U32>, Png.enc.open(ok, ww, hh, px)) : Bool}:
  match ok:
    case False{}:
      {==}
    case True{}:
      {==}

def Laws.jpeg_png_refuse_alike(img):
  match img:
    case Img.Raster{+ww, +hh, +px}:
      refuse.alike(Png.enc.good(ww, hh, px), ww, hh, px)
