# proofs of laws/PngIgnoresBytesAfterIend.bend
import Base
import ../laws/PngIgnoresBytesAfterIend.bend as Laws
import ./lemmas/PngImageWalk.bend as M1

def Laws.png_after_iend(ww, hh, cc, plte, trns, idats, rest, h_ww, h_hh, h_cc, h_pl, h_tr, h_fp, h_ft, h_fi):
  M1.walk.decoded(ww, hh, cc, plte, trns, idats, rest, h_ww, h_hh, h_cc, h_pl, h_tr, h_fp, h_ft, h_fi)
