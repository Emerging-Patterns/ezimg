# proofs of laws/DecodedSamplesPackArgb.bend
import Base
import ../laws/DecodedSamplesPackArgb.bend as Laws
import ./lemmas/JpegSamplesPacked.bend as M1

def Laws.jpeg_gray_level(yy):
  match yy:
    case U32{w0}:
      match w0:
        case WCon{b0, WCon{b1, WCon{b2, WCon{b3, w4}}}}:
          match w4:
            case WCon{b4, WCon{b5, WCon{b6, WCon{b7, w8}}}}:
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
                                          (M1.or_byte(b0, b1, b2, b3, b4, b5, b6, b7),
                                            (M1.or_byte(b0, b1, b2, b3, b4, b5, b6, b7), {==}))
