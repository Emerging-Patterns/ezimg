# proofs of laws/CountIsArea.bend
import Base
import ../main.bend as Img
import ../laws/CountIsArea.bend as Laws
import ./lemmas/BasicFacts.bend as M1

def Laws.count_samples(img):
  match img:
    case Img.Raster{_ww, _hh, _px}:
      {==}

def Laws.count_area(img, h_wf):
  match img:
    case Img.Raster{+ww, +hh, +px}:
      M1.ras.nat_eq_true(List.length(&2, U32, px), Nat.mul(U32.to_nat(ww), U32.to_nat(hh)), h_wf)
