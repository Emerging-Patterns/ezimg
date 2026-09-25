# proof/wp9-png-roundtrip: lemmas for the PNG round trip (IMG-PNG-2) and the
# chunk walker's lift of the pixel stage (IMG-PNG-9). Each is a law proved
# here, or a def whose type is the fact it proves; PROOF.bend imports this
# file, so the gate checks it.
import Base
import ../LAWS.bend as Laws
import ../main.bend as Img
import ../src/crc.bend as Crc
import ../src/png.bend as Png
import ../src/inflate.bend as Inf
import ./u32.bend as U32L
import ./wp1-crc.bend as Wp1
import ./wp2-inflate.bend as Wp2
import ./wp6-raster.bend as R

# ---- A. four bytes of a U32, put back together ----

# a U32 from its 32 bits, low bit first
def w32(
  b0: Bool,
  b1: Bool,
  b2: Bool,
  b3: Bool,
  b4: Bool,
  b5: Bool,
  b6: Bool,
  b7: Bool,
  b8: Bool,
  b9: Bool,
  b10: Bool,
  b11: Bool,
  b12: Bool,
  b13: Bool,
  b14: Bool,
  b15: Bool,
  b16: Bool,
  b17: Bool,
  b18: Bool,
  b19: Bool,
  b20: Bool,
  b21: Bool,
  b22: Bool,
  b23: Bool,
  b24: Bool,
  b25: Bool,
  b26: Bool,
  b27: Bool,
  b28: Bool,
  b29: Bool,
  b30: Bool,
  b31: Bool
) -> U32:
  U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11,
    WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22,
    WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31,
    WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

# a bit or'd with false once, twice and three times: what is left of a bit
# the checker cannot compute after be.u32 puts it back in place
def or1(bb: Bool) -> Bool:
  Bool.or(bb, False{})

# twice
def or2(bb: Bool) -> Bool:
  Bool.or(Bool.or(bb, False{}), False{})

# three times
def or3(bb: Bool) -> Bool:
  Bool.or(Bool.or(Bool.or(bb, False{}), False{}), False{})

# each is the bit: once
def or1.id(bb: Bool) -> {or1(bb) == bb : Bool}:
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# twice
def or2.id(bb: Bool) -> {or2(bb) == bb : Bool}:
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# three times
def or3.id(bb: Bool) -> {or3(bb) == bb : Bool}:
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# the bits of byte 1 or'd with false once, byte 2 twice and byte 3 three
# times: the word is the same. One rewrite per bit, highest first
def be.fix(
  +b0: Bool,
  +b1: Bool,
  +b2: Bool,
  +b3: Bool,
  +b4: Bool,
  +b5: Bool,
  +b6: Bool,
  +b7: Bool,
  +b8: Bool,
  +b9: Bool,
  +b10: Bool,
  +b11: Bool,
  +b12: Bool,
  +b13: Bool,
  +b14: Bool,
  +b15: Bool,
  +b16: Bool,
  +b17: Bool,
  +b18: Bool,
  +b19: Bool,
  +b20: Bool,
  +b21: Bool,
  +b22: Bool,
  +b23: Bool,
  +b24: Bool,
  +b25: Bool,
  +b26: Bool,
  +b27: Bool,
  +b28: Bool,
  +b29: Bool,
  +b30: Bool,
  +b31: Bool
) -> {w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13), or1(b14), or1(b15),
  or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24), or3(b25), or3(b26),
  or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == w32(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13,
  b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : U32}:
  %or1.id(b8) : {w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13), or1(b14),
    or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24), or3(b25),
    or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == w32(b0, b1, b2, b3, b4, b5, b6, b7, _, b9, b10, b11,
    b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : U32}
  %or1.id(b9) : {w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13), or1(b14),
    or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24), or3(b25),
    or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), _, b10,
    b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : U32}
  %or1.id(b10) : {w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), _, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29,
    b30, b31) : U32}
  %or1.id(b11) : {w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), _, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28,
    b29, b30, b31) : U32}
  %or1.id(b12) : {w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), or1(b11), _, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27,
    b28, b29, b30, b31) : U32}
  %or1.id(b13) : {w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), _, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26,
    b27, b28, b29, b30, b31) : U32}
  %or1.id(b14) : {w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13), _, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25,
    b26, b27, b28, b29, b30, b31) : U32}
  %or1.id(b15) : {w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13), or1(b14), _, b16, b17, b18, b19, b20, b21, b22, b23, b24,
    b25, b26, b27, b28, b29, b30, b31) : U32}
  %or2.id(b16) : {w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13), or1(b14), or1(b15), _, b17, b18, b19, b20, b21, b22, b23,
    b24, b25, b26, b27, b28, b29, b30, b31) : U32}
  %or2.id(b17) : {w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13), or1(b14), or1(b15), or2(b16), _, b18, b19, b20, b21, b22,
    b23, b24, b25, b26, b27, b28, b29, b30, b31) : U32}
  %or2.id(b18) : {w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13), or1(b14), or1(b15), or2(b16), or2(b17), _, b19, b20, b21,
    b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : U32}
  %or2.id(b19) : {w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13), or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), _, b20,
    b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : U32}
  %or2.id(b20) : {w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13), or1(b14), or1(b15), or2(b16), or2(b17), or2(b18),
    or2(b19), _, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : U32}
  %or2.id(b21) : {w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13), or1(b14), or1(b15), or2(b16), or2(b17), or2(b18),
    or2(b19), or2(b20), _, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : U32}
  %or2.id(b22) : {w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13), or1(b14), or1(b15), or2(b16), or2(b17), or2(b18),
    or2(b19), or2(b20), or2(b21), _, b23, b24, b25, b26, b27, b28, b29, b30, b31) : U32}
  %or2.id(b23) : {w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13), or1(b14), or1(b15), or2(b16), or2(b17), or2(b18),
    or2(b19), or2(b20), or2(b21), or2(b22), _, b24, b25, b26, b27, b28, b29, b30, b31) : U32}
  %or3.id(b24) : {w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13), or1(b14), or1(b15), or2(b16), or2(b17), or2(b18),
    or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), _, b25, b26, b27, b28, b29, b30, b31) : U32}
  %or3.id(b25) : {w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13), or1(b14), or1(b15), or2(b16), or2(b17), or2(b18),
    or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24), _, b26, b27, b28, b29, b30, b31) : U32}
  %or3.id(b26) : {w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13), or1(b14), or1(b15), or2(b16), or2(b17), or2(b18),
    or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24), or3(b25), _, b27, b28, b29, b30, b31) : U32}
  %or3.id(b27) : {w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13), or1(b14), or1(b15), or2(b16), or2(b17), or2(b18),
    or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24), or3(b25), or3(b26), _, b28, b29, b30, b31) : U32}
  %or3.id(b28) : {w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13), or1(b14), or1(b15), or2(b16), or2(b17), or2(b18),
    or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24), or3(b25), or3(b26), or3(b27), _, b29, b30, b31) : U32}
  %or3.id(b29) : {w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13), or1(b14), or1(b15), or2(b16), or2(b17), or2(b18),
    or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24), or3(b25), or3(b26), or3(b27), or3(b28), _, b30,
    b31) : U32}
  %or3.id(b30) : {w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13), or1(b14), or1(b15), or2(b16), or2(b17), or2(b18),
    or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24), or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), _,
    b31) : U32}
  %or3.id(b31) : {w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13), or1(b14), or1(b15), or2(b16), or2(b17), or2(b18),
    or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24), or3(b25), or3(b26), or3(b27), or3(b28), or3(b29),
    or3(b30), _) : U32}
  {==}

# the four bytes spec.be4 writes, read back big-endian by the decoder, are the
# U32: its 32 bits taken apart, both sides are be.fix's words
def be.back(
  +nn: U32
) -> {Png.be.u32(U32.and(255, U32.shrn(nn, 24n)), U32.and(255, U32.shrn(nn, 16n)), U32.and(255, U32.shrn(nn, 8n)),
  U32.and(255, nn)) == nn : U32}:
  match nn:
    case U32{w0}:
      match w0:
        case WCon{+b0, WCon{+b1, WCon{+b2, WCon{+b3, w4}}}}:
          match w4:
            case WCon{+b4, WCon{+b5, WCon{+b6, WCon{+b7, w8}}}}:
              match w8:
                case WCon{+b8, WCon{+b9, WCon{+b10, WCon{+b11, w12}}}}:
                  match w12:
                    case WCon{+b12, WCon{+b13, WCon{+b14, WCon{+b15, w16}}}}:
                      match w16:
                        case WCon{+b16, WCon{+b17, WCon{+b18, WCon{+b19, w20}}}}:
                          match w20:
                            case WCon{+b20, WCon{+b21, WCon{+b22, WCon{+b23, w24}}}}:
                              match w24:
                                case WCon{+b24, WCon{+b25, WCon{+b26, WCon{+b27, w28}}}}:
                                  match w28:
                                    case WCon{+b28, WCon{+b29, WCon{+b30, WCon{+b31, w32}}}}:
                                      match w32:
                                        case WNil{}:
                                          be.fix(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
                                            b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
                                            b31)

# ---- B. the chunk walker over chunks laid out as spec.chunk ----

# the four bytes spec.be4 writes, most significant first
def bt3(+nn: U32) -> U32:
  U32.and(255, U32.shrn(nn, 24n))

# the second byte
def bt2(+nn: U32) -> U32:
  U32.and(255, U32.shrn(nn, 16n))

# the third byte
def bt1(+nn: U32) -> U32:
  U32.and(255, U32.shrn(nn, 8n))

# the low byte
def bt0(+nn: U32) -> U32:
  U32.and(255, nn)

# the walker applies the chunk to its state, then goes on with the bytes after
def chunk.next(+typ: U32, +data: List<&2, U32>, +rest: List<&2, U32>, +pg: Png.Pg) -> Maybe<&2, Png.Pic>:
  Png.png.crc(Png.png.apply(typ, data, pg), List.is_empty(&2, U32, rest), Png.png.go(rest, Png.ZLen{}, False{}, 0, 0,
    [], [], Png.png.pgof(Png.png.apply(typ, data, pg))))

# one chunk laid out as spec.chunk: its length field counts the data and its
# stored CRC is the CRC-32 of its type and data, so the walker applies it
def chunk.walk(
  +t0: U32,
  +t1: U32,
  +t2: U32,
  +t3: U32,
  +data: List<&2, U32>,
  +rest: List<&2, U32>,
  +pg: Png.Pg,
  hf: Laws.spec.fits(data)
) -> {Png.png.go(Laws.spec.chunk([t0, t1, t2, t3], data, rest), Png.ZLen{}, False{}, 0, 0, [], [], pg) ==
  chunk.next(Png.be.u32(t0, t1, t2, t3), List.reverse(&2, U32, data), rest, pg) : Maybe<&2, Png.Pic>}:
  +nn = U32.from_nat(List.length(&2, U32, data))
  +sum = Laws.crc.ref(t0 <> t1 <> t2 <> t3 <> data)
  +typ = Png.be.u32(t0, t1, t2, t3)
  +crc = List.reverse.go(&2, U32, data, [t3, t2, t1, t0])
  +dat = List.reverse.go(&2, U32, data, [])
  +got = Png.be.u32(bt3(sum), bt2(sum), bt1(sum), bt0(sum))
  +want = Crc.crc32(List.reverse(&2, U32, crc))
  +hn = {Equal.trans(Nat, U32.to_nat(Png.be.u32(bt3(nn), bt2(nn), bt1(nn), bt0(nn))), U32.to_nat(nn),
    List.length(&2, U32, data), Equal.cong(U32, Nat, uu => U32.to_nat(uu), Png.be.u32(bt3(nn), bt2(nn), bt1(nn),
    bt0(nn)), nn, be.back(nn)), hf) : {U32.to_nat(Png.be.u32(bt3(nn), bt2(nn), bt1(nn), bt0(nn))) ==
    List.length(&2, U32, data) : Nat}}
  +e_want = {Equal.trans(U32, want, Crc.crc32(t0 <> t1 <> t2 <> t3 <> data), sum,
    Equal.cong(List<&2, U32>, U32, xs => Crc.crc32(xs), List.reverse(&2, U32, crc), t0 <> t1 <> t2 <> t3 <> data,
      Wp1.crc_bytes(data, t0, t1, t2, t3)), Wp1.crc32_ref(t0 <> t1 <> t2 <> t3 <> data)) : {want == sum : U32}}
  +e_eq = {Equal.trans(Bool, U32.is_eq(got, want), U32.is_eq(sum, want), True{},
    Equal.cong(U32, Bool, uu => U32.is_eq(uu, want), got, sum, be.back(sum)),
    Equal.trans(Bool, U32.is_eq(sum, want), U32.is_eq(sum, sum), True{},
      Equal.cong(U32, Bool, uu => U32.is_eq(sum, uu), want, sum, e_want), U32L.u32_eq_refl(sum))) :
    {U32.is_eq(got, want) == True{} : Bool}}
  Equal.trans(Maybe<&2, Png.Pic>,
    Png.png.go(Laws.spec.chunk([t0, t1, t2, t3], data, rest), Png.ZLen{}, False{}, 0, 0, [], [], pg),
    Wp1.at_crc(bt3(sum), bt2(sum), bt1(sum), bt0(sum), rest, typ, crc, dat, pg),
    chunk.next(typ, dat, rest, pg),
    Wp1.walk_chunk(bt3(nn), bt2(nn), bt1(nn), bt0(nn), t0, t1, t2, t3, data, bt3(sum), bt2(sum), bt1(sum), bt0(sum),
      rest, pg, hn),
    Equal.cong(Bool, Maybe<&2, Png.Pic>, zz => Png.png.crc(Png.png.judge.at(zz, typ, dat, pg), List.is_empty(&2, U32,
      rest), Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], Png.png.pgof(Png.png.judge.at(zz, typ, dat, pg)))),
      U32.is_eq(got, want), True{}, e_eq))

# a chunk the state takes, NMore: the walker goes on with the bytes after it
def chunk.more(
  +t0: U32,
  +t1: U32,
  +t2: U32,
  +t3: U32,
  +data: List<&2, U32>,
  +rest: List<&2, U32>,
  +pg: Png.Pg,
  +pg2: Png.Pg,
  hf: Laws.spec.fits(data),
  ea: {Png.png.apply(Png.be.u32(t0, t1, t2, t3), List.reverse(&2, U32, data), pg) == Png.NMore{pg2} : Png.Nx}
) -> {Png.png.go(Laws.spec.chunk([t0, t1, t2, t3], data, rest), Png.ZLen{}, False{}, 0, 0, [], [], pg) ==
  Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], pg2) : Maybe<&2, Png.Pic>}:
  Equal.trans(Maybe<&2, Png.Pic>,
    Png.png.go(Laws.spec.chunk([t0, t1, t2, t3], data, rest), Png.ZLen{}, False{}, 0, 0, [], [], pg),
    chunk.next(Png.be.u32(t0, t1, t2, t3), List.reverse(&2, U32, data), rest, pg),
    Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], pg2),
    chunk.walk(t0, t1, t2, t3, data, rest, pg, hf),
    Equal.cong(Png.Nx, Maybe<&2, Png.Pic>, nx => Png.png.crc(nx, List.is_empty(&2, U32, rest), Png.png.go(rest,
      Png.ZLen{}, False{}, 0, 0, [], [], Png.png.pgof(nx))), Png.png.apply(Png.be.u32(t0, t1, t2, t3),
      List.reverse(&2, U32, data), pg), Png.NMore{pg2}, ea))

# the last chunk, which ends the image, NEnd: the walker finishes the picture
def chunk.end(
  +t0: U32,
  +t1: U32,
  +t2: U32,
  +t3: U32,
  +data: List<&2, U32>,
  +pg: Png.Pg,
  +pg2: Png.Pg,
  hf: Laws.spec.fits(data),
  ea: {Png.png.apply(Png.be.u32(t0, t1, t2, t3), List.reverse(&2, U32, data), pg) == Png.NEnd{pg2} : Png.Nx}
) -> {Png.png.go(Laws.spec.chunk([t0, t1, t2, t3], data, []), Png.ZLen{}, False{}, 0, 0, [], [], pg) ==
  Png.png.finish(pg2) : Maybe<&2, Png.Pic>}:
  Equal.trans(Maybe<&2, Png.Pic>,
    Png.png.go(Laws.spec.chunk([t0, t1, t2, t3], data, []), Png.ZLen{}, False{}, 0, 0, [], [], pg),
    chunk.next(Png.be.u32(t0, t1, t2, t3), List.reverse(&2, U32, data), [], pg),
    Png.png.finish(pg2),
    chunk.walk(t0, t1, t2, t3, data, [], pg, hf),
    Equal.cong(Png.Nx, Maybe<&2, Png.Pic>, nx => Png.png.crc(nx, True{}, Png.png.go([], Png.ZLen{}, False{}, 0, 0, [],
      [], Png.png.pgof(nx))), Png.png.apply(Png.be.u32(t0, t1, t2, t3), List.reverse(&2, U32, data), pg),
      Png.NEnd{pg2}, ea))

# ---- C. the walker's state, chunk by chunk ----

# the state after IHDR, PLTE when there is one, and tRNS when there is one,
# with idat the IDAT data so far, newest first, and sid whether an IDAT came
def st(
  +ww: U32,
  +hh: U32,
  +cc: U32,
  +plte: Maybe<&2, List<&2, U32>>,
  +trns: Maybe<&2, List<&2, U32>>,
  idat: List<&2, U32>,
  sid: Bool
) -> Png.Pg:
  Png.Pg{ww, hh, 8, cc, 0, 0, 0, idat, Laws.spec.or.nil(plte), Laws.spec.or.nil(trns), True{},
    Maybe.is_some(&2, List<&2, U32>, plte), sid, False{}, Maybe.is_some(&2, List<&2, U32>, trns), False{}}

# or regrouped to the right
def or.right(aa: Bool, +bb: Bool, +rr: Bool) -> {Bool.or(Bool.or(aa, bb), rr) == Bool.or(aa, Bool.or(bb, rr)) : Bool}:
  match aa:
    case True{}:
      {==}
    case False{}:
      {==}

# the colour types spec.colour.ok names are the ones png.col accepts
def col.ok(+cc: U32, h_cc: {Laws.spec.colour.ok(cc) == True{} : Bool}) -> {Png.png.col(cc) == True{} : Bool}:
  Equal.trans(Bool, Png.png.col(cc), Laws.spec.colour.ok(cc), True{},
    or.right(U32.is_eq(cc, 0), U32.is_eq(cc, 2), Bool.or(U32.is_eq(cc, 3), Bool.or(U32.is_eq(cc, 4), U32.is_eq(cc,
    6)))), h_cc)

# png.good takes a nonzero width and height, bit depth 8, a colour type it
# knows, and methods 0
def good.ok(
  +ww: U32,
  +hh: U32,
  +cc: U32,
  h_ww: {U32.is_gt(ww, 0) == True{} : Bool},
  h_hh: {U32.is_gt(hh, 0) == True{} : Bool},
  h_cc: {Laws.spec.colour.ok(cc) == True{} : Bool}
) -> {Png.png.good(ww, hh, 8, cc, 0, 0, 0) == True{} : Bool}:
  +e_c = col.ok(cc, h_cc)
  %Equal.sym(Bool, U32.is_gt(ww, 0), True{}, h_ww) : {Bool.and(Bool.and(_, U32.is_gt(hh, 0)), Bool.and(Png.png.col(cc),
    True{})) == True{} : Bool}
  %Equal.sym(Bool, U32.is_gt(hh, 0), True{}, h_hh) : {Bool.and(Bool.and(True{}, _), Bool.and(Png.png.col(cc),
    True{})) == True{} : Bool}
  %Equal.sym(Bool, Png.png.col(cc), True{}, e_c) : {Bool.and(Bool.and(True{}, True{}), Bool.and(_, True{})) ==
    True{} : Bool}
  {==}

# an IHDR png.good takes starts the state
def ihdr.ok.true(
  zz: Bool,
  +ww: U32,
  +hh: U32,
  +cc: U32,
  ez: {zz == True{} : Bool}
) -> {Png.png.ihdr.ok(zz, ww, hh, 8, cc, 0, 0, 0) == Png.NMore{st(ww, hh, cc, None{}, None{}, [], False{})} : Png.Nx}:
  match zz:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Png.NBad{} == Png.NMore{st(ww, hh, cc, None{}, None{}, [], False{})} : Png.Nx},
        U32L.false_true(ez))

# the IHDR chunk: its width and height read back, png.good takes it
def ihdr.step(
  +ww: U32,
  +hh: U32,
  +cc: U32,
  h_ww: {U32.is_gt(ww, 0) == True{} : Bool},
  h_hh: {U32.is_gt(hh, 0) == True{} : Bool},
  h_cc: {Laws.spec.colour.ok(cc) == True{} : Bool}
) -> {Png.png.apply(Png.be.u32(73, 72, 68, 82), List.reverse(&2, U32, Laws.spec.ihdr.data(ww, hh, cc)), Png.pg.empty())
  == Png.NMore{st(ww, hh, cc, None{}, None{}, [], False{})} : Png.Nx}:
  +wb = Png.be.u32(bt3(ww), bt2(ww), bt1(ww), bt0(ww))
  +hb = Png.be.u32(bt3(hh), bt2(hh), bt1(hh), bt0(hh))
  Equal.trans(Png.Nx, Png.png.ihdr.ok(Png.png.good(wb, hb, 8, cc, 0, 0, 0), wb, hb, 8, cc, 0, 0, 0),
    Png.png.ihdr.ok(Png.png.good(ww, hh, 8, cc, 0, 0, 0), ww, hh, 8, cc, 0, 0, 0),
    Png.NMore{st(ww, hh, cc, None{}, None{}, [], False{})},
    Equal.trans(Png.Nx, Png.png.ihdr.ok(Png.png.good(wb, hb, 8, cc, 0, 0, 0), wb, hb, 8, cc, 0, 0, 0),
      Png.png.ihdr.ok(Png.png.good(ww, hb, 8, cc, 0, 0, 0), ww, hb, 8, cc, 0, 0, 0),
      Png.png.ihdr.ok(Png.png.good(ww, hh, 8, cc, 0, 0, 0), ww, hh, 8, cc, 0, 0, 0),
      Equal.cong(U32, Png.Nx, xx => Png.png.ihdr.ok(Png.png.good(xx, hb, 8, cc, 0, 0, 0), xx, hb, 8, cc, 0, 0, 0), wb,
        ww, be.back(ww)),
      Equal.cong(U32, Png.Nx, xx => Png.png.ihdr.ok(Png.png.good(ww, xx, 8, cc, 0, 0, 0), ww, xx, 8, cc, 0, 0, 0), hb,
        hh, be.back(hh))),
    ihdr.ok.true(Png.png.good(ww, hh, 8, cc, 0, 0, 0), ww, hh, cc, good.ok(ww, hh, cc, h_ww, h_hh, h_cc)))

# a chunk the checks take goes on to the next
def allow.true(zz: Bool, +pg: Png.Pg, ez: {zz == True{} : Bool}) -> {Png.png.allow(zz, pg) == Png.NMore{pg} : Png.Nx}:
  match zz:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Png.NBad{} == Png.NMore{pg} : Png.Nx}, U32L.false_true(ez))

# the PLTE chunk after IHDR: its colour type allows it and its length is a
# palette's, so the state keeps its data
def plte.step(
  +ww: U32,
  +hh: U32,
  +cc: U32,
  +pp: List<&2, U32>,
  h_pl: {Laws.spec.plte.ok(cc, Some{pp}) == True{} : Bool}
) -> {Png.png.apply(Png.be.u32(80, 76, 84, 69), List.reverse(&2, U32, pp), st(ww, hh, cc, None{}, None{}, [],
  False{})) == Png.NMore{st(ww, hh, cc, Some{pp}, None{}, [], False{})} : Png.Nx}:
  +ok = Bool.or(U32.is_eq(cc, 2), Bool.or(U32.is_eq(cc, 3), U32.is_eq(cc, 6)))
  +e_len = {Wp2.len_rev(pp) : {List.length(&2, U32, List.reverse(&2, U32, pp)) == List.length(&2, U32, pp) : Nat}}
  +e_ok = {Equal.trans(Bool, Bool.and(ok, Png.png.mod3(List.reverse(&2, U32, pp))), Bool.and(ok, Laws.spec.pal.len(pp)),
    True{}, Equal.cong(Nat, Bool, kk => Bool.and(ok, Bool.and(U32.is_gt(U32.from_nat(kk), 0),
      Bool.and(U32.is_zero((U32.from_nat(kk) % 3 : U32)), U32.is_le(U32.from_nat(kk), 768)))),
      List.length(&2, U32, List.reverse(&2, U32, pp)), List.length(&2, U32, pp), e_len), h_pl) :
    {Bool.and(ok, Png.png.mod3(List.reverse(&2, U32, pp))) == True{} : Bool}}
  +pg0 = st(ww, hh, cc, None{}, None{}, [], False{})
  Equal.trans(Png.Nx, Png.png.allow(Bool.and(ok, Png.png.mod3(List.reverse(&2, U32, pp))), Png.pg.plte(pg0,
    List.reverse(&2, U32, List.reverse(&2, U32, pp)))),
    Png.NMore{Png.pg.plte(pg0, List.reverse(&2, U32, List.reverse(&2, U32, pp)))},
    Png.NMore{st(ww, hh, cc, Some{pp}, None{}, [], False{})},
    allow.true(Bool.and(ok, Png.png.mod3(List.reverse(&2, U32, pp))), Png.pg.plte(pg0, List.reverse(&2, U32,
      List.reverse(&2, U32, pp))), e_ok),
    Equal.cong(List<&2, U32>, Png.Nx, xs => Png.NMore{Png.pg.plte(pg0, xs)}, List.reverse(&2, U32, List.reverse(&2, U32,
      pp)), pp, Wp2.rev_rev(pp)))

# PLTE, when there is one
def walk.plte(
  +ww: U32,
  +hh: U32,
  +cc: U32,
  +plte: Maybe<&2, List<&2, U32>>,
  +rest: List<&2, U32>,
  h_pl: {Laws.spec.plte.ok(cc, plte) == True{} : Bool},
  hf: Laws.spec.fits.opt(plte)
) -> {Png.png.go(Laws.spec.chunk.opt([80, 76, 84, 69], plte, rest), Png.ZLen{}, False{}, 0, 0, [], [], st(ww, hh, cc,
  None{}, None{}, [], False{})) == Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], st(ww, hh, cc, plte, None{}, [],
  False{})) : Maybe<&2, Png.Pic>}:
  match plte:
    case None{}:
      {==}
    case Some{+pp}:
      chunk.more(80, 76, 84, 69, pp, rest, st(ww, hh, cc, None{}, None{}, [], False{}), st(ww, hh, cc, Some{pp}, None{},
        [], False{}), hf, plte.step(ww, hh, cc, pp, h_pl))

# the tRNS chunk after IHDR and PLTE, if any: its colour type allows it, so
# the state keeps its data
def trns.step(
  +ww: U32,
  +hh: U32,
  +cc: U32,
  +plte: Maybe<&2, List<&2, U32>>,
  +tt: List<&2, U32>,
  h_tr: {Laws.spec.trns.ok(cc, plte, Some{tt}) == True{} : Bool}
) -> {Png.png.apply(Png.be.u32(116, 82, 78, 83), List.reverse(&2, U32, tt), st(ww, hh, cc, plte, None{}, [], False{}))
  == Png.NMore{st(ww, hh, cc, plte, Some{tt}, [], False{})} : Png.Nx}:
  +ok = Png.png.trns.ok(cc, Maybe.is_some(&2, List<&2, U32>, plte))
  +pg0 = st(ww, hh, cc, plte, None{}, [], False{})
  Equal.trans(Png.Nx, Png.png.allow(ok, Png.pg.trns(pg0, List.reverse(&2, U32, List.reverse(&2, U32, tt)))),
    Png.NMore{Png.pg.trns(pg0, List.reverse(&2, U32, List.reverse(&2, U32, tt)))},
    Png.NMore{st(ww, hh, cc, plte, Some{tt}, [], False{})},
    allow.true(ok, Png.pg.trns(pg0, List.reverse(&2, U32, List.reverse(&2, U32, tt))), h_tr),
    Equal.cong(List<&2, U32>, Png.Nx, xs => Png.NMore{Png.pg.trns(pg0, xs)}, List.reverse(&2, U32, List.reverse(&2, U32,
      tt)), tt, Wp2.rev_rev(tt)))

# tRNS, when there is one
def walk.trns(
  +ww: U32,
  +hh: U32,
  +cc: U32,
  +plte: Maybe<&2, List<&2, U32>>,
  +trns: Maybe<&2, List<&2, U32>>,
  +rest: List<&2, U32>,
  h_tr: {Laws.spec.trns.ok(cc, plte, trns) == True{} : Bool},
  hf: Laws.spec.fits.opt(trns)
) -> {Png.png.go(Laws.spec.chunk.opt([116, 82, 78, 83], trns, rest), Png.ZLen{}, False{}, 0, 0, [], [], st(ww, hh, cc,
  plte, None{}, [], False{})) == Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], st(ww, hh, cc, plte, trns, [],
  False{})) : Maybe<&2, Png.Pic>}:
  match trns:
    case None{}:
      {==}
    case Some{+tt}:
      chunk.more(116, 82, 78, 83, tt, rest, st(ww, hh, cc, plte, None{}, [], False{}), st(ww, hh, cc, plte, Some{tt},
        [], False{}), hf, trns.step(ww, hh, cc, plte, tt, h_tr))

# a colour type other than 3, or a PLTE: what IDAT and IEND ask of the state
def need(+cc: U32, +plte: Maybe<&2, List<&2, U32>>) -> Bool:
  Bool.or(Bool.not(U32.is_eq(cc, 3)), Maybe.is_some(&2, List<&2, U32>, plte))

# or with true is true
def or.true(bb: Bool) -> {Bool.or(bb, True{}) == True{} : Bool}:
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# spec.plte.ok gives what IDAT and IEND ask: colour type 3 has a PLTE
def need.ok(
  +cc: U32,
  +plte: Maybe<&2, List<&2, U32>>,
  h_pl: {Laws.spec.plte.ok(cc, plte) == True{} : Bool}
) -> {need(cc, plte) == True{} : Bool}:
  match plte:
    case None{}:
      Equal.cong(Bool, Bool, bb => Bool.or(bb, False{}), Bool.not(U32.is_eq(cc, 3)), True{}, h_pl)
    case Some{_pp}:
      or.true(Bool.not(U32.is_eq(cc, 3)))

# an IDAT the checks take is added to the state
def idat.try.true(
  zz: Bool,
  +data: List<&2, U32>,
  +pg: Png.Pg,
  ez: {zz == True{} : Bool}
) -> {Png.png.idat.try(zz, data, pg) == Png.NMore{Png.pg.idat(pg, data)} : Png.Nx}:
  match zz:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Png.NBad{} == Png.NMore{Png.pg.idat(pg, data)} : Png.Nx}, U32L.false_true(ez))

# an IDAT chunk: its data goes in front of the IDAT data so far
def idat.step(
  +ww: U32,
  +hh: U32,
  +cc: U32,
  +plte: Maybe<&2, List<&2, U32>>,
  +trns: Maybe<&2, List<&2, U32>>,
  +dd: List<&2, U32>,
  +acc: List<&2, U32>,
  +sid: Bool,
  h_nd: {need(cc, plte) == True{} : Bool}
) -> {Png.png.apply(Png.be.u32(73, 68, 65, 84), List.reverse(&2, U32, dd), st(ww, hh, cc, plte, trns, acc, sid)) ==
  Png.NMore{st(ww, hh, cc, plte, trns, List.append(&2, U32, List.reverse(&2, U32, dd), acc), True{})} : Png.Nx}:
  idat.try.true(need(cc, plte), List.reverse(&2, U32, dd), st(ww, hh, cc, plte, trns, acc, sid), h_nd)

# an IEND the checks take ends the image
def iend.ok.true(
  zz: Bool,
  +pg: Png.Pg,
  ez: {zz == True{} : Bool}
) -> {Png.png.iend.ok(zz, pg) == Png.NEnd{Png.pg.iend(pg)} : Png.Nx}:
  match zz:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Png.NBad{} == Png.NEnd{Png.pg.iend(pg)} : Png.Nx}, U32L.false_true(ez))

# the IEND chunk, empty: it ends the image
def iend.step(
  +ww: U32,
  +hh: U32,
  +cc: U32,
  +plte: Maybe<&2, List<&2, U32>>,
  +trns: Maybe<&2, List<&2, U32>>,
  +acc: List<&2, U32>,
  +sid: Bool,
  h_nd: {need(cc, plte) == True{} : Bool}
) -> {Png.png.apply(Png.be.u32(73, 69, 78, 68), List.reverse(&2, U32, []), st(ww, hh, cc, plte, trns, acc, sid)) ==
  Png.NEnd{Png.pg.iend(st(ww, hh, cc, plte, trns, acc, sid))} : Png.Nx}:
  iend.ok.true(need(cc, plte), st(ww, hh, cc, plte, trns, acc, sid), h_nd)

# reversing an append onto acc: the second part, onto the first reversed
def revgo_app(
  +aa: List<&2, U32>,
  +bb: List<&2, U32>,
  +acc: List<&2, U32>
) -> {List.reverse.go(&2, U32, List.append(&2, U32, aa, bb), acc) == List.reverse.go(&2, U32, bb, List.reverse.go(&2,
  U32, aa, acc)) : List<&2, U32>}:
  match aa:
    case Nil{}:
      {==}
    case +hd <> +tl:
      revgo_app(tl, bb, hd <> acc)

# reversing onto an append: the reversal onto the front part, then the rest
def revgo_acc(
  +dd: List<&2, U32>,
  +aa: List<&2, U32>,
  +rr: List<&2, U32>
) -> {List.reverse.go(&2, U32, dd, List.append(&2, U32, aa, rr)) == List.append(&2, U32, List.reverse.go(&2, U32, dd,
  aa), rr) : List<&2, U32>}:
  match dd:
    case Nil{}:
      {==}
    case +hd <> +tl:
      revgo_acc(tl, hd <> aa, rr)

# the reversal of done then d: d reversed, then done reversed
def rev_app(
  +done: List<&2, U32>,
  +dd: List<&2, U32>
) -> {List.append(&2, U32, List.reverse(&2, U32, dd), List.reverse(&2, U32, done)) == List.reverse(&2, U32,
  List.append(&2, U32, done, dd)) : List<&2, U32>}:
  Equal.sym(List<&2, U32>, List.reverse(&2, U32, List.append(&2, U32, done, dd)), List.append(&2, U32,
    List.reverse(&2, U32, dd), List.reverse(&2, U32, done)),
    Equal.trans(List<&2, U32>, List.reverse(&2, U32, List.append(&2, U32, done, dd)), List.reverse.go(&2, U32, dd,
      List.reverse(&2, U32, done)), List.append(&2, U32, List.reverse(&2, U32, dd), List.reverse(&2, U32, done)),
      revgo_app(done, dd, []), revgo_acc(dd, [], List.reverse(&2, U32, done))))

# the IDAT chunks, then IEND: with done the IDAT data read so far, the image
# is the samples of done and the rest of the data, inflated
def walk.idats(
  +ww: U32,
  +hh: U32,
  +cc: U32,
  +plte: Maybe<&2, List<&2, U32>>,
  +trns: Maybe<&2, List<&2, U32>>,
  +ds: List<&2, List<&2, U32>>,
  +done: List<&2, U32>,
  +sid: Bool,
  +h_nd: {need(cc, plte) == True{} : Bool},
  hf: Laws.spec.fits.all(ds)
) -> {Png.png.go(Laws.spec.idats(ds, Laws.spec.chunk([73, 69, 78, 68], [], [])), Png.ZLen{}, False{}, 0, 0, [], [],
  st(ww, hh, cc, plte, trns, List.reverse(&2, U32, done), sid)) == Png.png.samples(Inf.inflate(List.append(&2, U32,
  done, List.concat(&2, U32, ds))), ww, hh, cc, Laws.spec.or.nil(plte), Laws.spec.or.nil(trns)) : Maybe<&2, Png.Pic>}:
  match ds:
    case Nil{}:
      +pl = Laws.spec.or.nil(plte)
      +tr = Laws.spec.or.nil(trns)
      +pg = st(ww, hh, cc, plte, trns, List.reverse(&2, U32, done), sid)
      Equal.trans(Maybe<&2, Png.Pic>,
        Png.png.go(Laws.spec.chunk([73, 69, 78, 68], [], []), Png.ZLen{}, False{}, 0, 0, [], [], pg),
        Png.png.finish(Png.pg.iend(pg)),
        Png.png.samples(Inf.inflate(List.append(&2, U32, done, [])), ww, hh, cc, pl, tr),
        chunk.end(73, 69, 78, 68, [], pg, Png.pg.iend(pg), {==}, iend.step(ww, hh, cc, plte, trns,
          List.reverse(&2, U32, done), sid, h_nd)),
        Equal.trans(Maybe<&2, Png.Pic>, Png.png.finish(Png.pg.iend(pg)),
          Png.png.samples(Inf.inflate(done), ww, hh, cc, pl, tr),
          Png.png.samples(Inf.inflate(List.append(&2, U32, done, [])), ww, hh, cc, pl, tr),
          Equal.cong(List<&2, U32>, Maybe<&2, Png.Pic>, xs => Png.png.samples(Inf.inflate(xs), ww, hh, cc, pl, tr),
            List.reverse(&2, U32, List.reverse(&2, U32, done)), done, Wp2.rev_rev(done)),
          Equal.cong(List<&2, U32>, Maybe<&2, Png.Pic>, xs => Png.png.samples(Inf.inflate(xs), ww, hh, cc, pl, tr),
            done, List.append(&2, U32, done, []), Equal.sym(List<&2, U32>, List.append(&2, U32, done, []), done,
            Wp2.app_nil(done)))))
    case +dd <> +tl:
      (hd, htl) = hf
      +pl = Laws.spec.or.nil(plte)
      +tr = Laws.spec.or.nil(trns)
      +rest = Laws.spec.idats(tl, Laws.spec.chunk([73, 69, 78, 68], [], []))
      +pg = st(ww, hh, cc, plte, trns, List.reverse(&2, U32, done), sid)
      +d2 = List.append(&2, U32, done, dd)
      Equal.trans(Maybe<&2, Png.Pic>,
        Png.png.go(Laws.spec.chunk([73, 68, 65, 84], dd, rest), Png.ZLen{}, False{}, 0, 0, [], [], pg),
        Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], st(ww, hh, cc, plte, trns, List.append(&2, U32,
          List.reverse(&2, U32, dd), List.reverse(&2, U32, done)), True{})),
        Png.png.samples(Inf.inflate(List.append(&2, U32, done, List.append(&2, U32, dd, List.concat(&2, U32, tl)))), ww,
          hh, cc, pl, tr),
        chunk.more(73, 68, 65, 84, dd, rest, pg, st(ww, hh, cc, plte, trns, List.append(&2, U32, List.reverse(&2, U32,
        dd),
          List.reverse(&2, U32, done)), True{}), hd, idat.step(ww, hh, cc, plte, trns, dd, List.reverse(&2, U32, done),
          sid, h_nd)),
        Equal.trans(Maybe<&2, Png.Pic>,
          Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], st(ww, hh, cc, plte, trns, List.append(&2, U32,
            List.reverse(&2, U32, dd), List.reverse(&2, U32, done)), True{})),
          Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], st(ww, hh, cc, plte, trns, List.reverse(&2, U32, d2),
            True{})),
          Png.png.samples(Inf.inflate(List.append(&2, U32, done, List.append(&2, U32, dd, List.concat(&2, U32, tl)))),
            ww, hh, cc, pl, tr),
          Equal.cong(List<&2, U32>, Maybe<&2, Png.Pic>, xs => Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], st(ww,
            hh, cc, plte, trns, xs, True{})), List.append(&2, U32, List.reverse(&2, U32, dd), List.reverse(&2, U32,
            done)), List.reverse(&2, U32, d2), rev_app(done, dd)),
          Equal.trans(Maybe<&2, Png.Pic>,
            Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], st(ww, hh, cc, plte, trns, List.reverse(&2, U32, d2),
              True{})),
            Png.png.samples(Inf.inflate(List.append(&2, U32, d2, List.concat(&2, U32, tl))), ww, hh, cc, pl, tr),
            Png.png.samples(Inf.inflate(List.append(&2, U32, done, List.append(&2, U32, dd, List.concat(&2, U32, tl)))),
              ww, hh, cc, pl, tr),
            walk.idats(ww, hh, cc, plte, trns, tl, d2, True{}, h_nd, htl),
            Equal.cong(List<&2, U32>, Maybe<&2, Png.Pic>, xs => Png.png.samples(Inf.inflate(xs), ww, hh, cc, pl, tr),
              List.append(&2, U32, d2, List.concat(&2, U32, tl)), List.append(&2, U32, done, List.append(&2, U32, dd,
              List.concat(&2, U32, tl))), Wp2.app_assoc(done, dd, List.concat(&2, U32, tl))))))

# the chunks after the signature: IHDR, PLTE and tRNS where there are some,
# the IDAT chunks and IEND leave the samples of the IDAT data, inflated
def walk.png(
  +ww: U32,
  +hh: U32,
  +cc: U32,
  +plte: Maybe<&2, List<&2, U32>>,
  +trns: Maybe<&2, List<&2, U32>>,
  +idats: List<&2, List<&2, U32>>,
  h_ww: {U32.is_gt(ww, 0) == True{} : Bool},
  h_hh: {U32.is_gt(hh, 0) == True{} : Bool},
  h_cc: {Laws.spec.colour.ok(cc) == True{} : Bool},
  +h_pl: {Laws.spec.plte.ok(cc, plte) == True{} : Bool},
  h_tr: {Laws.spec.trns.ok(cc, plte, trns) == True{} : Bool},
  h_fp: Laws.spec.fits.opt(plte),
  h_ft: Laws.spec.fits.opt(trns),
  h_fi: Laws.spec.fits.all(idats)
) -> {Png.decode(Laws.spec.chunk([73, 72, 68, 82], Laws.spec.ihdr.data(ww, hh, cc), Laws.spec.chunk.opt([80, 76, 84,
  69], plte, Laws.spec.chunk.opt([116, 82, 78, 83], trns, Laws.spec.idats(idats, Laws.spec.chunk([73, 69, 78, 68], [],
  [])))))) == Png.png.samples(Inf.inflate(List.concat(&2, U32, idats)), ww, hh, cc, Laws.spec.or.nil(plte),
  Laws.spec.or.nil(trns)) : Maybe<&2, Png.Pic>}:
  +r3 = Laws.spec.idats(idats, Laws.spec.chunk([73, 69, 78, 68], [], []))
  +r2 = Laws.spec.chunk.opt([116, 82, 78, 83], trns, r3)
  +r1 = Laws.spec.chunk.opt([80, 76, 84, 69], plte, r2)
  +s0 = st(ww, hh, cc, None{}, None{}, [], False{})
  +s1 = st(ww, hh, cc, plte, None{}, [], False{})
  +s2 = st(ww, hh, cc, plte, trns, [], False{})
  Equal.trans(Maybe<&2, Png.Pic>,
    Png.png.go(Laws.spec.chunk([73, 72, 68, 82], Laws.spec.ihdr.data(ww, hh, cc), r1), Png.ZLen{}, False{}, 0, 0, [],
      [], Png.pg.empty()),
    Png.png.go(r1, Png.ZLen{}, False{}, 0, 0, [], [], s0),
    Png.png.samples(Inf.inflate(List.concat(&2, U32, idats)), ww, hh, cc, Laws.spec.or.nil(plte),
      Laws.spec.or.nil(trns)),
    chunk.more(73, 72, 68, 82, Laws.spec.ihdr.data(ww, hh, cc), r1, Png.pg.empty(), s0, {==}, ihdr.step(ww, hh, cc,
      h_ww, h_hh, h_cc)),
    Equal.trans(Maybe<&2, Png.Pic>, Png.png.go(r1, Png.ZLen{}, False{}, 0, 0, [], [], s0),
      Png.png.go(r2, Png.ZLen{}, False{}, 0, 0, [], [], s1),
      Png.png.samples(Inf.inflate(List.concat(&2, U32, idats)), ww, hh, cc, Laws.spec.or.nil(plte),
        Laws.spec.or.nil(trns)),
      walk.plte(ww, hh, cc, plte, r2, h_pl, h_fp),
      Equal.trans(Maybe<&2, Png.Pic>, Png.png.go(r2, Png.ZLen{}, False{}, 0, 0, [], [], s1),
        Png.png.go(r3, Png.ZLen{}, False{}, 0, 0, [], [], s2),
        Png.png.samples(Inf.inflate(List.concat(&2, U32, idats)), ww, hh, cc, Laws.spec.or.nil(plte),
          Laws.spec.or.nil(trns)),
        walk.trns(ww, hh, cc, plte, trns, r3, h_tr, h_ft),
        walk.idats(ww, hh, cc, plte, trns, idats, [], False{}, need.ok(cc, plte, h_pl), h_fi))))

# the picture of px.of's samples, as a raster: spec.raster's
def frame.px(
  mm: Maybe<&2, List<&2, U32>>,
  +ww: U32,
  +hh: U32
) -> {Img.decode_png.pic(Png.png.pic(mm, ww, hh)) == Laws.spec.raster(mm, ww, hh) : Maybe<&2, Img.Raster>}:
  match mm:
    case None{}:
      {==}
    case Some{_px}:
      {==}

# the unfiltered scanlines packed, as a raster
def frame.scan(
  mm: Maybe<&2, List<&2, U32>>,
  +ww: U32,
  +hh: U32,
  +cc: U32,
  +plte: List<&2, U32>,
  +trns: List<&2, U32>
) -> {Img.decode_png.pic(Png.png.pack(mm, ww, hh, cc, plte, trns)) == Laws.spec.raster(Laws.spec.px.then(mm, cc, plte,
  trns), ww, hh) : Maybe<&2, Img.Raster>}:
  match mm:
    case None{}:
      {==}
    case Some{+raw}:
      frame.px(Png.px.of(cc, raw, plte, trns), ww, hh)

# the decoder's last stages, from the inflated data, as a raster: spec.decoded
def frame.decoded(
  mm: Maybe<&2, List<&2, U32>>,
  +ww: U32,
  +hh: U32,
  +cc: U32,
  +plte: List<&2, U32>,
  +trns: List<&2, U32>
) -> {Img.decode_png.pic(Png.png.samples(mm, ww, hh, cc, plte, trns)) == Laws.spec.decoded(mm, ww, hh, cc, plte, trns) :
  Maybe<&2, Img.Raster>}:
  match mm:
    case None{}:
      {==}
    case Some{+raw}:
      frame.scan(Png.unfilter(raw, ww, hh, Png.png.bpp(cc)), ww, hh, cc, plte, trns)

# ---- D. the encoder's file, laid out as spec.png ----

# adding zero with no carry in leaves a word
def adc.zero(pp: Nat, tt: Word(pp)) -> {Word.adc(pp, tt, Word.zero(pp), False{}, False{}) == tt : Word(pp)}:
  match pp:
    case 0n:
      match tt:
        case WNil{}:
          {==}
    case 1n+(+qq):
      match tt:
        case WCon{False{}, rest}:
          Equal.cong(Word(qq), Word.Con<qq>, ww => WCon{False{}, ww}, Word.adc(qq, rest, Word.zero(qq), False{},
            False{}), rest, adc.zero(qq, rest))
        case WCon{True{}, rest}:
          Equal.cong(Word(qq), Word.Con<qq>, ww => WCon{True{}, ww}, Word.adc(qq, rest, Word.zero(qq), False{},
            False{}),
            rest, adc.zero(qq, rest))

# adding zero with a carry in is the increment
def adc.carry(
  pp: Nat,
  tt: Word(pp)
) -> {Word.adc(pp, tt, Word.zero(pp), False{}, True{}) == Word.inc(pp, tt) : Word(pp)}:
  match pp:
    case 0n:
      match tt:
        case WNil{}:
          {==}
    case 1n+(+qq):
      match tt:
        case WCon{False{}, rest}:
          Equal.cong(Word(qq), Word.Con<qq>, ww => WCon{True{}, ww}, Word.adc(qq, rest, Word.zero(qq), False{},
            False{}), rest, adc.zero(qq, rest))
        case WCon{True{}, rest}:
          Equal.cong(Word(qq), Word.Con<qq>, ww => WCon{False{}, ww}, Word.adc(qq, rest, Word.zero(qq), False{},
            True{}),
            Word.inc(qq, rest), adc.carry(qq, rest))

# adding one is the increment
def add.one(uu: U32) -> {U32.add(uu, 1) == U32.inc(uu) : U32}:
  match uu:
    case U32{WCon{False{}, rest}}:
      Equal.cong(Word(31n), U32, ww => U32{WCon{True{}, ww}}, Word.adc(31n, rest, Word.zero(31n), False{}, False{}),
        rest, adc.zero(31n, rest))
    case U32{WCon{True{}, rest}}:
      Equal.cong(Word(31n), U32, ww => U32{WCon{False{}, ww}}, Word.adc(31n, rest, Word.zero(31n), False{}, True{}),
        Word.inc(31n, rest), adc.carry(31n, rest))

# counting a list in a word from k ends at k plus its length, taken in a word
def len.from(
  +xs: List<&2, U32>,
  +kk: Nat
) -> {Png.enc.len(xs, U32.from_nat(kk)) == U32.from_nat(Nat.add(kk, List.length(&2, U32, xs))) : U32}:
  match xs:
    case Nil{}:
      Equal.cong(Nat, U32, nn => U32.from_nat(nn), kk, Nat.add(kk, 0n), Equal.sym(Nat, Nat.add(kk, 0n), kk,
        Wp2.nat_add_zero(kk)))
    case _hd <> +tl:
      +lt = List.length(&2, U32, tl)
      Equal.trans(U32, Png.enc.len(tl, U32.add(U32.from_nat(kk), 1)), Png.enc.len(tl, U32.from_nat(1n+kk)),
        U32.from_nat(Nat.add(kk, 1n+lt)),
        Equal.cong(U32, U32, uu => Png.enc.len(tl, uu), U32.add(U32.from_nat(kk), 1), U32.from_nat(1n+kk),
          add.one(U32.from_nat(kk))),
        Equal.trans(U32, Png.enc.len(tl, U32.from_nat(1n+kk)), U32.from_nat(1n+Nat.add(kk, lt)),
          U32.from_nat(Nat.add(kk, 1n+lt)), len.from(tl, 1n+kk),
          Equal.cong(Nat, U32, nn => U32.from_nat(nn), 1n+Nat.add(kk, lt), Nat.add(kk, 1n+lt), Equal.sym(Nat,
            Nat.add(kk, 1n+lt), 1n+Nat.add(kk, lt), Wp2.nat_add_succ(kk, lt)))))

# the encoder's count of a list is its length, taken in a word
def len.word(+xs: List<&2, U32>) -> {Png.enc.len(xs, 0) == U32.from_nat(List.length(&2, U32, xs)) : U32}:
  len.from(xs, 0n)

# a chunk's bytes: length, type, data, CRC, then rest
def chunk.form(
  +nn: U32,
  +tb: List<&2, U32>,
  +data: List<&2, U32>,
  +crc: U32,
  +rest: List<&2, U32>
) -> List<&2, U32>:
  List.append(&2, U32, Png.enc.be(nn), List.append(&2, U32, tb, List.append(&2, U32, data, List.append(&2, U32,
    Png.enc.be(crc), rest))))

# the chunk enc.chunk writes, then rest, is spec.chunk's
def chunk.same(
  +tag: U32,
  +data: List<&2, U32>,
  +rest: List<&2, U32>
) -> {List.append(&2, U32, Png.enc.chunk(tag, data), rest) == Laws.spec.chunk(Png.enc.be(tag), data, rest) :
  List<&2, U32>}:
  +tb = Png.enc.be(tag)
  +body = Png.enc.cat(tb, data)
  +crc = Crc.crc32(body)
  +ee = Png.enc.be(crc)
  +n0 = Png.enc.len(data, 0)
  Equal.trans(List<&2, U32>, List.append(&2, U32, Png.enc.chunk(tag, data), rest),
    chunk.form(n0, tb, data, crc, rest),
    Laws.spec.chunk(tb, data, rest),
    Equal.trans(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, Png.enc.be(n0), Png.enc.cat(body, ee)), rest),
      List.append(&2, U32, List.append(&2, U32, Png.enc.be(n0), List.append(&2, U32, body, ee)), rest),
      chunk.form(n0, tb, data, crc, rest),
      Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.append(&2, U32, List.append(&2, U32, Png.enc.be(n0), ys),
        rest), Png.enc.cat(body, ee), List.append(&2, U32, body, ee), Wp2.cat_app(body, ee)),
      Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.append(&2, U32, Png.enc.be(n0), List.append(&2, U32, tb,
        ys)), List.append(&2, U32, List.append(&2, U32, data, ee), rest), List.append(&2, U32, data, List.append(&2,
        U32, ee, rest)), Wp2.app_assoc(data, ee, rest))),
    Equal.trans(List<&2, U32>, chunk.form(n0, tb, data, crc, rest),
      chunk.form(U32.from_nat(List.length(&2, U32, data)), tb, data, crc, rest),
      Laws.spec.chunk(tb, data, rest),
      Equal.cong(U32, List<&2, U32>, uu => chunk.form(uu, tb, data, crc, rest), n0, U32.from_nat(List.length(&2, U32,
        data)), len.word(data)),
      Equal.cong(U32, List<&2, U32>, uu => chunk.form(U32.from_nat(List.length(&2, U32, data)), tb, data, uu, rest),
        crc, Laws.crc.ref(List.append(&2, U32, tb, data)), Wp1.crc32_ref(List.append(&2, U32, tb, data)))))


# the signature enc.cat puts in front is png_sig's
def sig.cat(
  +rest: List<&2, U32>
) -> {Png.enc.cat(Png.enc.sig(), rest) == List.append(&2, U32, Img.png_sig(), rest) : List<&2, U32>}:
  {==}

# the file enc.seal.one lays out, for any IHDR data and zlib stream: the
# signature, IHDR, one IDAT and IEND, as spec.chunk lays them out. The data
# stays a variable here, so the checker never compares the IHDR CRC term
def seal.gen(
  +ihd: List<&2, U32>,
  +zz: List<&2, U32>
) -> {Png.enc.cat(Png.enc.sig(), Png.enc.cat(Png.enc.chunk(Png.tag.ihdr(), ihd),
  Png.enc.cat(Png.enc.chunk(Png.tag.idat(),
  zz), Png.enc.chunk(Png.tag.iend(), [])))) == List.append(&2, U32, Img.png_sig(), Laws.spec.chunk([73, 72, 68, 82],
  ihd, Laws.spec.chunk([73, 68, 65, 84], zz, Laws.spec.chunk([73, 69, 78, 68], [], [])))) : List<&2, U32>}:
  +ih = Png.enc.chunk(Png.tag.ihdr(), ihd)
  +id = Png.enc.chunk(Png.tag.idat(), zz)
  +ie = Png.enc.chunk(Png.tag.iend(), [])
  +sig = Img.png_sig()
  +t_ih = Png.enc.be(Png.tag.ihdr())
  +t_id = Png.enc.be(Png.tag.idat())
  Equal.trans(List<&2, U32>, Png.enc.cat(Png.enc.sig(), Png.enc.cat(ih, Png.enc.cat(id, ie))),
    List.append(&2, U32, sig, List.append(&2, U32, ih, List.append(&2, U32, id, ie))),
    List.append(&2, U32, sig, Laws.spec.chunk(t_ih, ihd, Laws.spec.chunk(t_id, zz, ie))),
    Equal.trans(List<&2, U32>, Png.enc.cat(Png.enc.sig(), Png.enc.cat(ih, Png.enc.cat(id, ie))),
      List.append(&2, U32, sig, List.append(&2, U32, ih, Png.enc.cat(id, ie))),
      List.append(&2, U32, sig, List.append(&2, U32, ih, List.append(&2, U32, id, ie))),
      Equal.cong(List<&2, U32>, List<&2, U32>, ys => Png.enc.cat(Png.enc.sig(), ys), Png.enc.cat(ih, Png.enc.cat(id,
        ie)), List.append(&2, U32, ih, Png.enc.cat(id, ie)), Wp2.cat_app(ih, Png.enc.cat(id, ie))),
      Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.append(&2, U32, sig, List.append(&2, U32, ih, ys)),
        Png.enc.cat(id, ie), List.append(&2, U32, id, ie), Wp2.cat_app(id, ie))),
    Equal.trans(List<&2, U32>, List.append(&2, U32, sig, List.append(&2, U32, ih, List.append(&2, U32, id, ie))),
      List.append(&2, U32, sig, Laws.spec.chunk(t_ih, ihd, List.append(&2, U32, id, ie))),
      List.append(&2, U32, sig, Laws.spec.chunk(t_ih, ihd, Laws.spec.chunk(t_id, zz, ie))),
      Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.append(&2, U32, sig, ys), List.append(&2, U32, ih,
        List.append(&2, U32, id, ie)), Laws.spec.chunk(t_ih, ihd, List.append(&2, U32, id, ie)),
        chunk.same(Png.tag.ihdr(), ihd, List.append(&2, U32, id, ie))),
      Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.append(&2, U32, sig, Laws.spec.chunk(t_ih, ihd, ys)),
        List.append(&2, U32, id, ie), Laws.spec.chunk(t_id, zz, ie), chunk.same(Png.tag.idat(), zz, ie))))

# the file enc.seal.one writes is spec.png's, with no PLTE or tRNS and one IDAT
def seal.one.same(
  +ww: U32,
  +hh: U32,
  +op: Bool,
  +raw: List<&2, U32>,
  +nn: U32
) -> {Png.enc.seal.one(ww, hh, op, raw, nn) == Laws.spec.png(ww, hh, Png.enc.ct(op), None{}, None{},
  [Png.enc.zlib(raw, nn)]) : List<&2, U32>}:
  seal.gen(Png.enc.ihdr(ww, hh, Png.enc.ct(op)), Png.enc.zlib(raw, nn))

# ---- E. the scanlines enc.raw writes, and their count ----

# adding a word to zero leaves the word
def adc.zl(pp: Nat, tt: Word(pp)) -> {Word.adc(pp, Word.zero(pp), tt, False{}, False{}) == tt : Word(pp)}:
  match pp:
    case 0n:
      match tt:
        case WNil{}:
          {==}
    case 1n+(+qq):
      match tt:
        case WCon{False{}, rest}:
          Equal.cong(Word(qq), Word.Con<qq>, ww => WCon{False{}, ww}, Word.adc(qq, Word.zero(qq), rest, False{},
            False{}), rest, adc.zl(qq, rest))
        case WCon{True{}, rest}:
          Equal.cong(Word(qq), Word.Con<qq>, ww => WCon{True{}, ww}, Word.adc(qq, Word.zero(qq), rest, False{},
            False{}),
            rest, adc.zl(qq, rest))

# an incremented word added in is a carry in
def adc.inc(
  pp: Nat,
  +xx: Word(pp),
  +yy: Word(pp)
) -> {Word.adc(pp, Word.inc(pp, xx), yy, False{}, False{}) == Word.adc(pp, xx, yy, False{}, True{}) : Word(pp)}:
  match pp:
    case 0n:
      match xx yy:
        case WNil{} WNil{}:
          {==}
    case 1n+(+qq):
      match xx yy:
        case WCon{False{}, _xt} WCon{False{}, _yt}:
          {==}
        case WCon{False{}, _xt} WCon{True{}, _yt}:
          {==}
        case WCon{True{}, +xt} WCon{False{}, +yt}:
          Equal.cong(Word(qq), Word.Con<qq>, ww => WCon{False{}, ww}, Word.adc(qq, Word.inc(qq, xt), yt, False{},
            False{}), Word.adc(qq, xt, yt, False{}, True{}), adc.inc(qq, xt, yt))
        case WCon{True{}, +xt} WCon{True{}, +yt}:
          Equal.cong(Word(qq), Word.Con<qq>, ww => WCon{True{}, ww}, Word.adc(qq, Word.inc(qq, xt), yt, False{},
            False{}), Word.adc(qq, xt, yt, False{}, True{}), adc.inc(qq, xt, yt))

# a carry in is an increment of the sum
def adc.cin(
  pp: Nat,
  +xx: Word(pp),
  +yy: Word(pp)
) -> {Word.adc(pp, xx, yy, False{}, True{}) == Word.inc(pp, Word.adc(pp, xx, yy, False{}, False{})) : Word(pp)}:
  match pp:
    case 0n:
      match xx yy:
        case WNil{} WNil{}:
          {==}
    case 1n+(+qq):
      match xx yy:
        case WCon{False{}, _xt} WCon{False{}, _yt}:
          {==}
        case WCon{False{}, +xt} WCon{True{}, +yt}:
          Equal.cong(Word(qq), Word.Con<qq>, ww => WCon{False{}, ww}, Word.adc(qq, xt, yt, False{}, True{}),
            Word.inc(qq, Word.adc(qq, xt, yt, False{}, False{})), adc.cin(qq, xt, yt))
        case WCon{True{}, +xt} WCon{False{}, +yt}:
          Equal.cong(Word(qq), Word.Con<qq>, ww => WCon{False{}, ww}, Word.adc(qq, xt, yt, False{}, True{}),
            Word.inc(qq, Word.adc(qq, xt, yt, False{}, False{})), adc.cin(qq, xt, yt))
        case WCon{True{}, _xt} WCon{True{}, _yt}:
          {==}

# zero plus a U32 is the U32
def add.zl(uu: U32) -> {U32.add(0, uu) == uu : U32}:
  match uu:
    case U32{ww}:
      Equal.cong(Word(32n), U32, xx => U32{xx}, Word.adc(32n, Word.zero(32n), ww, False{}, False{}), ww, adc.zl(32n,
        ww))

# an incremented U32 added in: the sum incremented
def add.inc(+xx: U32, +yy: U32) -> {U32.add(U32.inc(xx), yy) == U32.inc(U32.add(xx, yy)) : U32}:
  match xx yy:
    case U32{+xw} U32{+yw}:
      Equal.cong(Word(32n), U32, ww => U32{ww}, Word.adc(32n, Word.inc(32n, xw), yw, False{}, False{}),
        Word.inc(32n, Word.adc(32n, xw, yw, False{}, False{})), Equal.trans(Word(32n), Word.adc(32n, Word.inc(32n, xw),
        yw, False{}, False{}), Word.adc(32n, xw, yw, False{}, True{}), Word.inc(32n, Word.adc(32n, xw, yw, False{},
        False{})), adc.inc(32n, xw, yw), adc.cin(32n, xw, yw)))

# two naturals taken in words and added: their sum taken in a word
def add.nat(aa: Nat, +bb: Nat) -> {U32.add(U32.from_nat(aa), U32.from_nat(bb)) == U32.from_nat(Nat.add(aa, bb)) : U32}:
  match aa:
    case 0n:
      add.zl(U32.from_nat(bb))
    case 1n+(+pp):
      Equal.trans(U32, U32.add(U32.inc(U32.from_nat(pp)), U32.from_nat(bb)), U32.inc(U32.add(U32.from_nat(pp),
        U32.from_nat(bb))), U32.inc(U32.from_nat(Nat.add(pp, bb))), add.inc(U32.from_nat(pp), U32.from_nat(bb)),
        Equal.cong(U32, U32, uu => U32.inc(uu), U32.add(U32.from_nat(pp), U32.from_nat(bb)), U32.from_nat(Nat.add(pp,
        bb)), add.nat(pp, bb)))

# the channel bytes enc.push writes for a sample, in order: red, green, blue,
# and alpha when the picture is not opaque
def chans(op: Bool, +cc: U32) -> List<&2, U32>:
  match op:
    case True{}:
      [Png.enc.r(cc), Png.enc.g(cc), Png.enc.b(cc)]
    case False{}:
      [Png.enc.r(cc), Png.enc.g(cc), Png.enc.b(cc), Png.enc.a(cc)]

# enc.nch in a word is nchn
def nch.nat(op: Bool) -> {Png.enc.nch(op) == U32.from_nat(Laws.spec.nch(op)) : U32}:
  match op:
    case True{}:
      {==}
    case False{}:
      {==}

# a sample's channels, then more bytes: nchn more bytes
def len.chans(
  op: Bool,
  +cc: U32,
  +rest: List<&2, U32>
) -> {List.length(&2, U32, List.append(&2, U32, chans(op, cc), rest)) == Nat.add(Laws.spec.nch(op), List.length(&2,
  U32, rest)) : Nat}:
  match op:
    case True{}:
      {==}
    case False{}:
      {==}

# enc.push is the channels reversed onto the accumulator
def push.rev(
  op: Bool,
  +cc: U32,
  +acc: List<&2, U32>
) -> {Png.enc.push(op, cc, acc) == List.reverse.go(&2, U32, chans(op, cc), acc) : List<&2, U32>}:
  match op:
    case True{}:
      {==}
    case False{}:
      {==}

# the bytes enc.raw writes, in order, from row position left: a filter byte 0
# where a row starts, then each sample's channels
def sc(px: List<&2, U32>, left: Nat, +ww: Nat, +op: Bool) -> List<&2, U32>:
  match px left:
    case Nil{} _left:
      []
    case +cc <> tl 0n:
      0 <> List.append(&2, U32, chans(op, cc), sc(tl, Png.enc.pred(ww), ww, op))
    case +cc <> tl 1n+pp:
      List.append(&2, U32, chans(op, cc), sc(tl, pp, ww, op))

# the count enc.raw carries, from row position left
def cnt(px: List<&2, U32>, left: Nat, +ww: Nat, +op: Bool, +nn: U32) -> U32:
  match px left:
    case Nil{} _left:
      nn
    case _cc <> tl 0n:
      cnt(tl, Png.enc.pred(ww), ww, op, ((nn + 1 : U32) + Png.enc.nch(op) : U32))
    case _cc <> tl 1n+pp:
      cnt(tl, pp, ww, op, (nn + Png.enc.nch(op) : U32))

# one sample's channels pushed: the bytes so far reversed onto them
def push.step(
  +op: Bool,
  +cc: U32,
  +rest: List<&2, U32>,
  +acc: List<&2, U32>
) -> {List.reverse.go(&2, U32, rest, Png.enc.push(op, cc, acc)) == List.reverse.go(&2, U32, List.append(&2, U32,
  chans(op, cc), rest), acc) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, List.reverse.go(&2, U32, rest, Png.enc.push(op, cc, acc)), List.reverse.go(&2, U32, rest,
    List.reverse.go(&2, U32, chans(op, cc), acc)), List.reverse.go(&2, U32, List.append(&2, U32, chans(op, cc), rest),
    acc), Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.reverse.go(&2, U32, rest, ys), Png.enc.push(op, cc, acc),
    List.reverse.go(&2, U32, chans(op, cc), acc), push.rev(op, cc, acc)), Equal.sym(List<&2, U32>, List.reverse.go(&2,
    U32, List.append(&2, U32, chans(op, cc), rest), acc), List.reverse.go(&2, U32, rest, List.reverse.go(&2, U32,
    chans(op, cc), acc)), revgo_app(chans(op, cc), rest, acc)))

# enc.raw: its bytes are sc's, after the accumulator, and its count is cnt's
def raw.eq(
  +px: List<&2, U32>,
  left: Nat,
  +ww: Nat,
  +op: Bool,
  +acc: List<&2, U32>,
  +nn: U32
) -> {Png.enc.raw(px, left, ww, op, acc, nn) == (List.reverse(&2, U32, List.reverse.go(&2, U32, sc(px, left, ww, op),
  acc)), cnt(px, left, ww, op, nn)) : List<&2, U32> & U32}:
  match px left:
    case Nil{} _left:
      {==}
    case +cc <> +tl 0n:
      +a1 = Png.enc.push(op, cc, 0 <> acc)
      +n2 = ((nn + 1 : U32) + Png.enc.nch(op) : U32)
      +pw = Png.enc.pred(ww)
      +rest = sc(tl, pw, ww, op)
      +ct = cnt(tl, pw, ww, op, n2)
      Equal.trans(List<&2, U32> & U32, Png.enc.raw(tl, pw, ww, op, a1, n2),
        (List.reverse(&2, U32, List.reverse.go(&2, U32, rest, a1)), ct),
        (List.reverse(&2, U32, List.reverse.go(&2, U32, List.append(&2, U32, chans(op, cc), rest), 0 <> acc)), ct),
        raw.eq(tl, pw, ww, op, a1, n2),
        Equal.cong(List<&2, U32>, List<&2, U32> & U32, xs => (List.reverse(&2, U32, xs), ct),
          List.reverse.go(&2, U32, rest, a1), List.reverse.go(&2, U32, List.append(&2, U32, chans(op, cc), rest),
          0 <> acc), push.step(op, cc, rest, 0 <> acc)))
    case +cc <> +tl 1n+(+pp):
      +a1 = Png.enc.push(op, cc, acc)
      +n2 = (nn + Png.enc.nch(op) : U32)
      +rest = sc(tl, pp, ww, op)
      +ct = cnt(tl, pp, ww, op, n2)
      Equal.trans(List<&2, U32> & U32, Png.enc.raw(tl, pp, ww, op, a1, n2),
        (List.reverse(&2, U32, List.reverse.go(&2, U32, rest, a1)), ct),
        (List.reverse(&2, U32, List.reverse.go(&2, U32, List.append(&2, U32, chans(op, cc), rest), acc)), ct),
        raw.eq(tl, pp, ww, op, a1, n2),
        Equal.cong(List<&2, U32>, List<&2, U32> & U32, xs => (List.reverse(&2, U32, xs), ct),
          List.reverse.go(&2, U32, rest, a1), List.reverse.go(&2, U32, List.append(&2, U32, chans(op, cc), rest), acc),
          push.step(op, cc, rest, acc)))

# a count from k plus n, taken in a word, is k + n taken in a word
def cnt.add(
  +kk: Nat,
  +nn: Nat,
  +uu: U32,
  eu: {uu == U32.from_nat(nn) : U32}
) -> {U32.add(U32.from_nat(kk), uu) == U32.from_nat(Nat.add(kk, nn)) : U32}:
  Equal.trans(U32, U32.add(U32.from_nat(kk), uu), U32.add(U32.from_nat(kk), U32.from_nat(nn)),
    U32.from_nat(Nat.add(kk, nn)), Equal.cong(U32, U32, xx => U32.add(U32.from_nat(kk), xx), uu, U32.from_nat(nn), eu),
    add.nat(kk, nn))

# cnt from k taken in a word ends at k plus the bytes sc writes, taken in a word
def cnt.word(
  +px: List<&2, U32>,
  left: Nat,
  +ww: Nat,
  +op: Bool,
  +kk: Nat
) -> {cnt(px, left, ww, op, U32.from_nat(kk)) == U32.from_nat(Nat.add(kk, List.length(&2, U32, sc(px, left, ww, op)))) :
  U32}:
  match px left:
    case Nil{} _left:
      Equal.cong(Nat, U32, nn => U32.from_nat(nn), kk, Nat.add(kk, 0n), Equal.sym(Nat, Nat.add(kk, 0n), kk,
        Wp2.nat_add_zero(kk)))
    case +cc <> +tl 0n:
      +pw = Png.enc.pred(ww)
      +rest = sc(tl, pw, ww, op)
      +ll = List.length(&2, U32, rest)
      +k0 = Nat.add(kk, 1n)
      +k1 = Nat.add(k0, Laws.spec.nch(op))
      +u0 = U32.add(U32.from_nat(kk), 1)
      +e_n = {Equal.trans(U32, U32.add(u0, Png.enc.nch(op)), U32.add(U32.from_nat(k0), Png.enc.nch(op)),
        U32.from_nat(k1), Equal.cong(U32, U32, uu => U32.add(uu, Png.enc.nch(op)), u0, U32.from_nat(k0),
        add.nat(kk, 1n)), cnt.add(k0, Laws.spec.nch(op), Png.enc.nch(op), nch.nat(op))) :
        {U32.add(u0, Png.enc.nch(op)) == U32.from_nat(k1) : U32}}
      +e_k = {Equal.trans(Nat, Nat.add(k1, ll), Nat.add(k0, Nat.add(Laws.spec.nch(op), ll)), Nat.add(kk,
        1n+Nat.add(Laws.spec.nch(op), ll)), R.add_assoc(k0, Laws.spec.nch(op), ll), R.add_assoc(kk, 1n,
        Nat.add(Laws.spec.nch(op), ll))) : {Nat.add(k1, ll) == Nat.add(kk, 1n+Nat.add(Laws.spec.nch(op), ll)) : Nat}}
      +lc = List.length(&2, U32, List.append(&2, U32, chans(op, cc), rest))
      +e_l = {Equal.cong(Nat, Nat, nn => Nat.add(kk, 1n+nn), Nat.add(Laws.spec.nch(op), ll), lc, Equal.sym(Nat, lc,
        Nat.add(Laws.spec.nch(op), ll), len.chans(op, cc, rest))) : {Nat.add(kk, 1n+Nat.add(Laws.spec.nch(op),
        ll)) == Nat.add(kk, 1n+lc) : Nat}}
      Equal.trans(U32, cnt(tl, pw, ww, op, U32.add(u0, Png.enc.nch(op))), cnt(tl, pw, ww, op, U32.from_nat(k1)),
        U32.from_nat(Nat.add(kk, 1n+lc)),
        Equal.cong(U32, U32, uu => cnt(tl, pw, ww, op, uu), U32.add(u0, Png.enc.nch(op)), U32.from_nat(k1), e_n),
        Equal.trans(U32, cnt(tl, pw, ww, op, U32.from_nat(k1)), U32.from_nat(Nat.add(k1, ll)),
          U32.from_nat(Nat.add(kk, 1n+lc)), cnt.word(tl, pw, ww, op, k1),
          Equal.cong(Nat, U32, nn => U32.from_nat(nn), Nat.add(k1, ll), Nat.add(kk, 1n+lc), Equal.trans(Nat,
            Nat.add(k1, ll), Nat.add(kk, 1n+Nat.add(Laws.spec.nch(op), ll)), Nat.add(kk, 1n+lc), e_k, e_l))))
    case +cc <> +tl 1n+(+pp):
      +rest = sc(tl, pp, ww, op)
      +ll = List.length(&2, U32, rest)
      +k1 = Nat.add(kk, Laws.spec.nch(op))
      +lc = List.length(&2, U32, List.append(&2, U32, chans(op, cc), rest))
      +e_l = {Equal.cong(Nat, Nat, nn => Nat.add(kk, nn), Nat.add(Laws.spec.nch(op), ll), lc, Equal.sym(Nat, lc,
        Nat.add(Laws.spec.nch(op), ll), len.chans(op, cc, rest))) : {Nat.add(kk, Nat.add(Laws.spec.nch(op),
          ll)) == Nat.add(kk, lc) :
        Nat}}
      Equal.trans(U32, cnt(tl, pp, ww, op, U32.add(U32.from_nat(kk), Png.enc.nch(op))), cnt(tl, pp, ww, op,
        U32.from_nat(k1)), U32.from_nat(Nat.add(kk, lc)),
        Equal.cong(U32, U32, uu => cnt(tl, pp, ww, op, uu), U32.add(U32.from_nat(kk), Png.enc.nch(op)),
          U32.from_nat(k1), cnt.add(kk, Laws.spec.nch(op), Png.enc.nch(op), nch.nat(op))),
        Equal.trans(U32, cnt(tl, pp, ww, op, U32.from_nat(k1)), U32.from_nat(Nat.add(k1, ll)),
          U32.from_nat(Nat.add(kk, lc)), cnt.word(tl, pp, ww, op, k1),
          Equal.cong(Nat, U32, nn => U32.from_nat(nn), Nat.add(k1, ll), Nat.add(kk, lc), Equal.trans(Nat, Nat.add(k1,
            ll), Nat.add(kk, Nat.add(Laws.spec.nch(op), ll)), Nat.add(kk, lc), R.add_assoc(kk, Laws.spec.nch(op), ll),
            e_l))))

# one more bit against a set bit keeps at most
def lestep(
  cc: Cmp,
  bit: Bool,
  hh: {Cmp.is_le(cc) == True{} : Bool}
) -> {Cmp.is_le(Word.cmp.fin(bit, True{}, cc)) == True{} : Bool}:
  match cc bit:
    case LT{} _bit:
      {==}
    case EQ{} True{}:
      {==}
    case EQ{} False{}:
      {==}
    case GT{} _bit:
      Empty.absurd({False{} == True{} : Bool}, U32L.false_true(hh))

# eight low bits against 255's, the rest equal: at most
def le8(
  +b0: Bool,
  +b1: Bool,
  +b2: Bool,
  +b3: Bool,
  +b4: Bool,
  +b5: Bool,
  +b6: Bool,
  +b7: Bool
) -> {Cmp.is_le(Wp2.le8.cmp(b0, b1, b2, b3, b4, b5, b6, b7, EQ{})) == True{} : Bool}:
  +c7 = Word.cmp.fin(b7, True{}, EQ{})
  +c6 = Word.cmp.fin(b6, True{}, c7)
  +c5 = Word.cmp.fin(b5, True{}, c6)
  +c4 = Word.cmp.fin(b4, True{}, c5)
  +c3 = Word.cmp.fin(b3, True{}, c4)
  +c2 = Word.cmp.fin(b2, True{}, c3)
  +c1 = Word.cmp.fin(b1, True{}, c2)
  lestep(c1, b0, lestep(c2, b1, lestep(c3, b2, lestep(c4, b3, lestep(c5, b4, lestep(c6, b5, lestep(c7, b6,
    lestep(EQ{}, b7, {==}))))))))

# a channel masked again is itself: the mask is first in both
def mask.red(cc: U32) -> {U32.and(255, Png.enc.r(cc)) == Png.enc.r(cc) : U32}:
  match cc:
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

# the same for green
def mask.grn(cc: U32) -> {U32.and(255, Png.enc.g(cc)) == Png.enc.g(cc) : U32}:
  match cc:
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

# the same for blue
def mask.blu(cc: U32) -> {U32.and(255, Png.enc.b(cc)) == Png.enc.b(cc) : U32}:
  match cc:
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

# the same for alpha
def mask.alp(cc: U32) -> {U32.and(255, Png.enc.a(cc)) == Png.enc.a(cc) : U32}:
  match cc:
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

# the alpha byte is the top byte shifted down
def alpha.top(cc: U32) -> {Png.enc.a(cc) == U32.shrn(cc, 24n) : U32}:
  match cc:
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

# a masked byte is below 256
def lt256(xx: U32) -> {U32.is_lt(U32.and(255, xx), 256) == True{} : Bool}:
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

# a masked byte is at most 255: its low eight bits against 255's
def le255(xx: U32) -> {U32.is_le(U32.and(255, xx), 255) == True{} : Bool}:
  match xx:
    case U32{w0}:
      match w0:
        case WCon{+b0, WCon{+b1, WCon{+b2, WCon{+b3, w4}}}}:
          match w4:
            case WCon{+b4, WCon{+b5, WCon{+b6, WCon{+b7, w8}}}}:
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
                                          le8(b0, b1, b2, b3, b4, b5, b6, b7)

# ---- F. the scanlines as rows, and each byte a byte ----

# every byte is its own low byte: masking it with 255 leaves it
def masked(xs: List<&2, U32>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case +xx <> tl:
      {U32.and(255, xx) == xx : U32} & masked(tl)

# masked lists appended are masked
def masked.app(
  +aa: List<&2, U32>,
  +bb: List<&2, U32>,
  ha: masked(aa),
  hb: masked(bb)
) -> masked(List.append(&2, U32, aa, bb)):
  match aa:
    case Nil{}:
      hb
    case +xx <> +tl:
      (ex, ht) = ha
      (ex, masked.app(tl, bb, ht, hb))

# a sample's channels are masked
def masked.chans(op: Bool, +cc: U32) -> masked(chans(op, cc)):
  match op:
    case True{}:
      (mask.red(cc), (mask.grn(cc), (mask.blu(cc), Unit{})))
    case False{}:
      (mask.red(cc), (mask.grn(cc), (mask.blu(cc), (mask.alp(cc), Unit{}))))

# the channels of samples, in order
def chans.all(+op: Bool, px: List<&2, U32>) -> List<&2, U32>:
  match px:
    case Nil{}:
      []
    case +cc <> tl:
      List.append(&2, U32, chans(op, cc), chans.all(op, tl))

# every channel is masked
def masked.all(+op: Bool, +px: List<&2, U32>) -> masked(chans.all(op, px)):
  match px:
    case Nil{}:
      Unit{}
    case +cc <> +tl:
      masked.app(chans(op, cc), chans.all(op, tl), masked.chans(op, cc), masked.all(op, tl))

# the channels of samples appended: the channels of each, appended
def chans.app(
  +op: Bool,
  +aa: List<&2, U32>,
  +bb: List<&2, U32>
) -> {chans.all(op, List.append(&2, U32, aa, bb)) == List.append(&2, U32, chans.all(op, aa), chans.all(op, bb)) :
  List<&2, U32>}:
  match aa:
    case Nil{}:
      {==}
    case +cc <> +tl:
      Equal.trans(List<&2, U32>, List.append(&2, U32, chans(op, cc), chans.all(op, List.append(&2, U32, tl, bb))),
        List.append(&2, U32, chans(op, cc), List.append(&2, U32, chans.all(op, tl), chans.all(op, bb))),
        List.append(&2, U32, List.append(&2, U32, chans(op, cc), chans.all(op, tl)), chans.all(op, bb)),
        Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.append(&2, U32, chans(op, cc), ys), chans.all(op,
          List.append(&2, U32, tl, bb)), List.append(&2, U32, chans.all(op, tl), chans.all(op, bb)), chans.app(op, tl,
          bb)),
        Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, chans(op, cc), chans.all(op, tl)),
          chans.all(op, bb)), List.append(&2, U32, chans(op, cc), List.append(&2, U32, chans.all(op, tl), chans.all(op,
          bb))), Wp2.app_assoc(chans(op, cc), chans.all(op, tl), chans.all(op, bb))))

# the channels of k samples: k times nchn bytes
def len.chans.all(
  +op: Bool,
  +px: List<&2, U32>
) -> {List.length(&2, U32, chans.all(op, px)) == Nat.mul(List.length(&2, U32, px), Laws.spec.nch(op)) : Nat}:
  match px:
    case Nil{}:
      {==}
    case +cc <> +tl:
      Equal.trans(Nat, List.length(&2, U32, List.append(&2, U32, chans(op, cc), chans.all(op, tl))),
        Nat.add(Laws.spec.nch(op),
        List.length(&2, U32, chans.all(op, tl))), Nat.add(Laws.spec.nch(op), Nat.mul(List.length(&2, U32, tl),
        Laws.spec.nch(op))),
        len.chans(op, cc, chans.all(op, tl)), Equal.cong(Nat, Nat, nn => Nat.add(Laws.spec.nch(op), nn),
        List.length(&2, U32,
        chans.all(op, tl)), Nat.mul(List.length(&2, U32, tl), Laws.spec.nch(op)), len.chans.all(op, tl)))

# the first k samples
def tk(kk: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match kk xs:
    case 0n _xs:
      []
    case 1n+_pp Nil{}:
      []
    case 1n+pp +hd <> tl:
      hd <> tk(pp, tl)

# the samples after the first k
def dr(kk: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match kk xs:
    case 0n xs:
      xs
    case 1n+_pp Nil{}:
      []
    case 1n+pp _hd <> tl:
      dr(pp, tl)

# xs is qq then rr, of lengths k and m
def split.of(+kk: Nat, +mm: Nat, +xs: List<&2, U32>, +qq: List<&2, U32>, +rr: List<&2, U32>) -> Type:
  {xs == List.append(&2, U32, qq, rr) : List<&2, U32>} & {List.length(&2, U32, qq) == kk : Nat} &
    {List.length(&2, U32, rr) == mm : Nat}

# what split proves: xs is its first k and the rest, of those lengths
def split.ty(+kk: Nat, +mm: Nat, +xs: List<&2, U32>) -> Type:
  split.of(kk, mm, xs, tk(kk, xs), dr(kk, xs))

# one more sample in front: the split one further
def split.up(
  +pp: Nat,
  +mm: Nat,
  +hd: U32,
  +tl: List<&2, U32>,
  sp: split.ty(pp, mm, tl)
) -> split.ty(1n+pp, mm, hd <> tl):
  (e1, (e2, e3)) = sp
  +qq = tk(pp, tl)
  +rr = dr(pp, tl)
  (Equal.cong(List<&2, U32>, List<&2, U32>, ys => hd <> ys, tl, List.append(&2, U32, qq, rr), e1),
    (Equal.cong(Nat, Nat, nn => 1n+nn, List.length(&2, U32, qq), pp, e2), e3))

# a list of k + m samples splits into k and m
def split(
  kk: Nat,
  +mm: Nat,
  +xs: List<&2, U32>,
  hl: {List.length(&2, U32, xs) == Nat.add(kk, mm) : Nat}
) -> split.ty(kk, mm, xs):
  match kk xs:
    case 0n _xs:
      ({==}, ({==}, hl))
    case 1n+pp Nil{}:
      Empty.absurd(split.ty(1n+pp, mm, []), Wp1.zero_succ(Nat.add(pp, mm), hl))
    case 1n+(+pp) +hd <> +tl:
      split.up(pp, mm, hd, tl, split(pp, mm, tl, Wp1.succ_inj(List.length(&2, U32, tl), Nat.add(pp, mm), hl)))

# the rows of h rows of w samples: each row the channels of its samples
def rows.of(hn: Nat, +ww: Nat, +op: Bool, +px: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match hn:
    case 0n:
      []
    case 1n+hp:
      chans.all(op, tk(ww, px)) <> rows.of(hp, ww, op, dr(ww, px))

# rows as scanlines: a filter byte 0 before each
def scan(rows: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match rows:
    case Nil{}:
      []
    case +row <> tl:
      0 <> List.append(&2, U32, row, scan(tl))

# inside a row: k samples with k positions left, then the next row
def sc.part(
  +qq: List<&2, U32>,
  kk: Nat,
  +rest: List<&2, U32>,
  +ww: Nat,
  +op: Bool,
  hq: {List.length(&2, U32, qq) == kk : Nat}
) -> {sc(List.append(&2, U32, qq, rest), kk, ww, op) == List.append(&2, U32, chans.all(op, qq), sc(rest, 0n, ww, op)) :
  List<&2, U32>}:
  match qq kk:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+pp:
      Empty.absurd({sc(rest, 1n+pp, ww, op) == sc(rest, 0n, ww, op) : List<&2, U32>}, Wp1.zero_succ(pp, hq))
    case +cc <> +tl 0n:
      Empty.absurd({sc(cc <> List.append(&2, U32, tl, rest), 0n, ww, op) == List.append(&2, U32, chans.all(op,
        cc <> tl), sc(rest, 0n, ww, op)) : List<&2, U32>}, Wp1.zero_succ(List.length(&2, U32, tl), Equal.sym(Nat,
        1n+List.length(&2, U32, tl), 0n, hq)))
    case +cc <> +tl 1n+(+pp):
      +ch = chans(op, cc)
      +ct = chans.all(op, tl)
      +sr = sc(rest, 0n, ww, op)
      Equal.trans(List<&2, U32>, List.append(&2, U32, ch, sc(List.append(&2, U32, tl, rest), pp, ww, op)),
        List.append(&2, U32, ch, List.append(&2, U32, ct, sr)), List.append(&2, U32, List.append(&2, U32, ch, ct), sr),
        Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.append(&2, U32, ch, ys), sc(List.append(&2, U32, tl, rest),
          pp, ww, op), List.append(&2, U32, ct, sr), sc.part(tl, pp, rest, ww, op, Wp1.succ_inj(List.length(&2, U32,
          tl), pp, hq))),
        Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, ch, ct), sr), List.append(&2, U32, ch,
          List.append(&2, U32, ct, sr)), Wp2.app_assoc(ch, ct, sr)))

# a whole row of 1 + w' samples, then the rest: a filter byte and the row's channels
def sc.row(
  +qq: List<&2, U32>,
  +rest: List<&2, U32>,
  +wp: Nat,
  +op: Bool,
  hq: {List.length(&2, U32, qq) == 1n+wp : Nat}
) -> {sc(List.append(&2, U32, qq, rest), 0n, 1n+wp, op) == 0 <> List.append(&2, U32, chans.all(op, qq), sc(rest, 0n,
  1n+wp, op)) : List<&2, U32>}:
  match qq:
    case Nil{}:
      Empty.absurd({sc(rest, 0n, 1n+wp, op) == 0 <> List.append(&2, U32, [], sc(rest, 0n, 1n+wp, op)) : List<&2, U32>},
        Wp1.zero_succ(wp, hq))
    case +cc <> +tl:
      +ch = chans(op, cc)
      +ct = chans.all(op, tl)
      +sr = sc(rest, 0n, 1n+wp, op)
      Equal.cong(List<&2, U32>, List<&2, U32>, ys => 0 <> ys, List.append(&2, U32, ch, sc(List.append(&2, U32, tl,
        rest), wp, 1n+wp, op)), List.append(&2, U32, List.append(&2, U32, ch, ct), sr), Equal.trans(List<&2, U32>,
        List.append(&2, U32, ch, sc(List.append(&2, U32, tl, rest), wp, 1n+wp, op)), List.append(&2, U32, ch,
        List.append(&2, U32, ct, sr)), List.append(&2, U32, List.append(&2, U32, ch, ct), sr),
        Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.append(&2, U32, ch, ys), sc(List.append(&2, U32, tl, rest),
          wp, 1n+wp, op), List.append(&2, U32, ct, sr), sc.part(tl, wp, rest, 1n+wp, op, Wp1.succ_inj(List.length(&2,
          U32, tl), wp, hq))),
        Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, ch, ct), sr), List.append(&2, U32, ch,
          List.append(&2, U32, ct, sr)), Wp2.app_assoc(ch, ct, sr))))

# h rows of 1 + w' samples, as the bytes of their rows: what sc.rows proves
def sc.rows.ty(+hn: Nat, +wp: Nat, +op: Bool, +px: List<&2, U32>) -> Type:
  {sc(px, 0n, 1n+wp, op) == scan(rows.of(hn, 1n+wp, op, px)) : List<&2, U32>}

# a row split off the front, then the rest by induction
def sc.rows.at(
  +hp: Nat,
  +wp: Nat,
  +op: Bool,
  +px: List<&2, U32>,
  sp: split.ty(1n+wp, Nat.mul(hp, 1n+wp), px),
  ih: @xs: List<&2, U32> -> {List.length(&2, U32, xs) == Nat.mul(hp, 1n+wp) : Nat} -> sc.rows.ty(hp, wp, op, xs)
) -> sc.rows.ty(1n+hp, wp, op, px):
  (e1, (e2, e3)) = sp
  +ww = {1n+wp : Nat}
  +qq = tk(ww, px)
  +rr = dr(ww, px)
  Equal.trans(List<&2, U32>, sc(px, 0n, ww, op), sc(List.append(&2, U32, qq, rr), 0n, ww, op),
    scan(rows.of(1n+hp, ww, op, px)),
    Equal.cong(List<&2, U32>, List<&2, U32>, xs => sc(xs, 0n, ww, op), px, List.append(&2, U32, qq, rr), e1),
    Equal.trans(List<&2, U32>, sc(List.append(&2, U32, qq, rr), 0n, ww, op), 0 <> List.append(&2, U32,
      chans.all(op, qq), sc(rr, 0n, ww, op)), scan(rows.of(1n+hp, ww, op, px)), sc.row(qq, rr, wp, op, e2),
      Equal.cong(List<&2, U32>, List<&2, U32>, ys => 0 <> List.append(&2, U32, chans.all(op, qq), ys), sc(rr, 0n,
        ww, op), scan(rows.of(hp, ww, op, rr)), ih(rr, e3))))

# h rows of 1 + w' samples: the bytes enc.raw writes are the rows as scanlines
def sc.rows(
  hn: Nat,
  +wp: Nat,
  +op: Bool,
  +px: List<&2, U32>,
  hl: {List.length(&2, U32, px) == Nat.mul(hn, 1n+wp) : Nat}
) -> sc.rows.ty(hn, wp, op, px):
  match hn:
    case 0n:
      match px:
        case Nil{}:
          {==}
        case +cc <> +tl:
          Empty.absurd({sc(cc <> tl, 0n, 1n+wp, op) == [] : List<&2, U32>}, Wp1.zero_succ(List.length(&2, U32, tl),
            Equal.sym(Nat, 1n+List.length(&2, U32, tl), 0n, hl)))
    case 1n+(+hp):
      sc.rows.at(hp, wp, op, px, split(1n+wp, Nat.mul(hp, 1n+wp), px, hl), xs => ex => sc.rows(hp, wp, op, xs, ex))

# the rows of h rows of w samples, concatenated: what rows.cat proves
def rows.cat.ty(+hn: Nat, +ww: Nat, +op: Bool, +px: List<&2, U32>) -> Type:
  {List.concat(&2, U32, rows.of(hn, ww, op, px)) == chans.all(op, px) : List<&2, U32>}

# a row split off the front, then the rest by induction
def rows.cat.at(
  +hp: Nat,
  +ww: Nat,
  +op: Bool,
  +px: List<&2, U32>,
  sp: split.ty(ww, Nat.mul(hp, ww), px),
  ih: @xs: List<&2, U32> -> {List.length(&2, U32, xs) == Nat.mul(hp, ww) : Nat} -> rows.cat.ty(hp, ww, op, xs)
) -> rows.cat.ty(1n+hp, ww, op, px):
  (e1, (_e2, e3)) = sp
  +qq = tk(ww, px)
  +rr = dr(ww, px)
  Equal.trans(List<&2, U32>, List.append(&2, U32, chans.all(op, qq), List.concat(&2, U32, rows.of(hp, ww, op, rr))),
    List.append(&2, U32, chans.all(op, qq), chans.all(op, rr)), chans.all(op, px),
    Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.append(&2, U32, chans.all(op, qq), ys), List.concat(&2, U32,
      rows.of(hp, ww, op, rr)), chans.all(op, rr), ih(rr, e3)),
    Equal.trans(List<&2, U32>, List.append(&2, U32, chans.all(op, qq), chans.all(op, rr)), chans.all(op,
      List.append(&2, U32, qq, rr)), chans.all(op, px), Equal.sym(List<&2, U32>, chans.all(op, List.append(&2, U32,
      qq, rr)), List.append(&2, U32, chans.all(op, qq), chans.all(op, rr)), chans.app(op, qq, rr)),
      Equal.cong(List<&2, U32>, List<&2, U32>, xs => chans.all(op, xs), List.append(&2, U32, qq, rr), px,
        Equal.sym(List<&2, U32>, px, List.append(&2, U32, qq, rr), e1))))

# the rows, concatenated, are the channels of every sample
def rows.cat(
  hn: Nat,
  +ww: Nat,
  +op: Bool,
  +px: List<&2, U32>,
  hl: {List.length(&2, U32, px) == Nat.mul(hn, ww) : Nat}
) -> rows.cat.ty(hn, ww, op, px):
  match hn:
    case 0n:
      match px:
        case Nil{}:
          {==}
        case +cc <> +tl:
          Empty.absurd({[] == chans.all(op, cc <> tl) : List<&2, U32>}, Wp1.zero_succ(List.length(&2, U32, tl),
            Equal.sym(Nat, 1n+List.length(&2, U32, tl), 0n, hl)))
    case 1n+(+hp):
      rows.cat.at(hp, ww, op, px, split(ww, Nat.mul(hp, ww), px, hl), xs => ex => rows.cat(hp, ww, op, xs, ex))

# h rows
def rows.len(
  hn: Nat,
  +ww: Nat,
  +op: Bool,
  +px: List<&2, U32>
) -> {List.length(&2, List<&2, U32>, rows.of(hn, ww, op, px)) == hn : Nat}:
  match hn:
    case 0n:
      {==}
    case 1n+(+hp):
      Equal.cong(Nat, Nat, nn => 1n+nn, List.length(&2, List<&2, U32>, rows.of(hp, ww, op, dr(ww, px))), hp,
        rows.len(hp, ww, op, dr(ww, px)))

# every row's bytes masked
def masked.rows(rows: List<&2, List<&2, U32>>) -> Type:
  match rows:
    case Nil{}:
      Unit
    case +row <> tl:
      masked(row) & masked.rows(tl)

# the rows of samples are masked
def masked.rows.of(hn: Nat, +ww: Nat, +op: Bool, +px: List<&2, U32>) -> masked.rows(rows.of(hn, ww, op, px)):
  match hn:
    case 0n:
      Unit{}
    case 1n+(+hp):
      (masked.all(op, tk(ww, px)), masked.rows.of(hp, ww, op, dr(ww, px)))

# subtracting zero leaves a U32
def sub.zero(+xx: U32) -> {U32.sub(xx, 0) == xx : U32}:
  match xx:
    case U32{+ww}:
      Equal.cong(Word(32n), U32, vv => U32{vv}, Word.adc(32n, ww, Word.zero(32n), True{}, True{}), ww,
        Wp2.adc_zero_carry(32n, ww))

# filter None leaves a row of masked bytes as it is
def frow(
  +row: List<&2, U32>,
  +bpp: U32,
  +prev: List<&2, U32>,
  +hist: List<&2, U32>,
  +phist: List<&2, U32>,
  hm: masked(row)
) -> {Laws.flt.row(row, Laws.FNone{}, bpp, prev, hist, phist) == row : List<&2, U32>}:
  match row:
    case Nil{}:
      {==}
    case +xx <> +tl:
      (ex, ht) = hm
      +bb = Laws.flt.up(prev)
      Equal.trans(List<&2, U32>, U32.and(255, U32.sub(xx, 0)) <> Laws.flt.row(tl, Laws.FNone{}, bpp,
        Laws.flt.next(prev),
        xx <> hist, bb <> phist), xx <> Laws.flt.row(tl, Laws.FNone{}, bpp, Laws.flt.next(prev), xx <> hist,
        bb <> phist), xx <> tl,
        Equal.cong(U32, List<&2, U32>, uu => uu <> Laws.flt.row(tl, Laws.FNone{}, bpp, Laws.flt.next(prev), xx <> hist,
          bb <> phist), U32.and(255, U32.sub(xx, 0)), xx, Equal.trans(U32, U32.and(255, U32.sub(xx, 0)), U32.and(255,
          xx), xx, Equal.cong(U32, U32, uu => U32.and(255, uu), U32.sub(xx, 0), xx, sub.zero(xx)), ex)),
        Equal.cong(List<&2, U32>, List<&2, U32>, ys => xx <> ys, Laws.flt.row(tl, Laws.FNone{}, bpp,
          Laws.flt.next(prev), xx <> hist, bb <> phist), tl, frow(tl, bpp, Laws.flt.next(prev), xx <> hist,
          bb <> phist, ht)))

# filter None over masked rows: the scanlines
def frows(
  +rows: List<&2, List<&2, U32>>,
  +bpp: U32,
  +prev: List<&2, U32>,
  hm: masked.rows(rows)
) -> {Laws.flt.rows(rows, Laws.FNone{}, bpp, prev) == scan(rows) : List<&2, U32>}:
  match rows:
    case Nil{}:
      {==}
    case +row <> +tl:
      (hr, ht) = hm
      Equal.trans(List<&2, U32>, 0 <> List.append(&2, U32, Laws.flt.row(row, Laws.FNone{}, bpp, prev, [], []),
        Laws.flt.rows(tl, Laws.FNone{}, bpp, row)), 0 <> List.append(&2, U32, row, Laws.flt.rows(tl, Laws.FNone{}, bpp,
        row)), 0 <> List.append(&2, U32, row, scan(tl)),
        Equal.cong(List<&2, U32>, List<&2, U32>, ys => 0 <> List.append(&2, U32, ys, Laws.flt.rows(tl, Laws.FNone{},
          bpp, row)), Laws.flt.row(row, Laws.FNone{}, bpp, prev, [], []), row, frow(row, bpp, prev, [], [], hr)),
        Equal.cong(List<&2, U32>, List<&2, U32>, ys => 0 <> List.append(&2, U32, row, ys), Laws.flt.rows(tl,
          Laws.FNone{}, bpp, row), scan(tl), frows(tl, bpp, row, ht)))

# a masked byte is below 256
def byte.lt(+xx: U32, ex: {U32.and(255, xx) == xx : U32}) -> {U32.is_lt(xx, 256) == True{} : Bool}:
  Equal.trans(Bool, U32.is_lt(xx, 256), U32.is_lt(U32.and(255, xx), 256), True{}, Equal.cong(U32, Bool, uu =>
    U32.is_lt(uu, 256), xx, U32.and(255, xx), Equal.sym(U32, U32.and(255, xx), xx, ex)), lt256(xx))

# a masked byte is at most 255
def byte.le(+xx: U32, ex: {U32.and(255, xx) == xx : U32}) -> {U32.is_le(xx, 255) == True{} : Bool}:
  Equal.trans(Bool, U32.is_le(xx, 255), U32.is_le(U32.and(255, xx), 255), True{}, Equal.cong(U32, Bool, uu =>
    U32.is_le(uu, 255), xx, U32.and(255, xx), Equal.sym(U32, U32.and(255, xx), xx, ex)), le255(xx))

# a masked row of n bytes: flt.bytes takes it
def fbytes(
  +xs: List<&2, U32>,
  nn: Nat,
  hm: masked(xs),
  hl: {List.length(&2, U32, xs) == nn : Nat}
) -> {Laws.flt.bytes(xs, nn, True{}) == True{} : Bool}:
  match xs nn:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+pp:
      Empty.absurd({False{} == True{} : Bool}, Wp1.zero_succ(pp, hl))
    case +xx <> +tl 0n:
      Empty.absurd({False{} == True{} : Bool}, Wp1.zero_succ(List.length(&2, U32, tl), Equal.sym(Nat,
        1n+List.length(&2, U32, tl), 0n, hl)))
    case +xx <> +tl 1n+(+pp):
      (ex, ht) = hm
      Equal.trans(Bool, Laws.flt.bytes(tl, pp, U32.is_lt(xx, 256)), Laws.flt.bytes(tl, pp, True{}), True{},
        Equal.cong(Bool, Bool, bb => Laws.flt.bytes(tl, pp, bb), U32.is_lt(xx, 256), True{}, byte.lt(xx, ex)),
        fbytes(tl, pp, ht, Wp1.succ_inj(List.length(&2, U32, tl), pp, hl)))

# the rows of h rows of w samples fit: what fit.rows proves
def fit.rows.ty(+hn: Nat, +ww: Nat, +op: Bool, +px: List<&2, U32>) -> Type:
  {Laws.flt.fit(rows.of(hn, ww, op, px), Nat.mul(ww, Laws.spec.nch(op)), True{}) == True{} : Bool}

# a row split off the front fits, then the rest by induction
def fit.rows.at(
  +hp: Nat,
  +ww: Nat,
  +op: Bool,
  +px: List<&2, U32>,
  sp: split.ty(ww, Nat.mul(hp, ww), px),
  ih: @xs: List<&2, U32> -> {List.length(&2, U32, xs) == Nat.mul(hp, ww) : Nat} -> fit.rows.ty(hp, ww, op, xs)
) -> fit.rows.ty(1n+hp, ww, op, px):
  (_e1, (e2, e3)) = sp
  +qq = tk(ww, px)
  +row = chans.all(op, qq)
  +nb = Nat.mul(ww, Laws.spec.nch(op))
  +e_len = {Equal.trans(Nat, List.length(&2, U32, row), Nat.mul(List.length(&2, U32, qq), Laws.spec.nch(op)), nb,
    len.chans.all(op, qq), Equal.cong(Nat, Nat, nn => Nat.mul(nn, Laws.spec.nch(op)), List.length(&2, U32, qq), ww,
    e2)) : {List.length(&2, U32, row) == nb : Nat}}
  Equal.trans(Bool, Laws.flt.fit(rows.of(hp, ww, op, dr(ww, px)), nb, Laws.flt.bytes(row, nb, True{})),
    Laws.flt.fit(rows.of(hp, ww, op, dr(ww, px)), nb, True{}), True{},
    Equal.cong(Bool, Bool, bb => Laws.flt.fit(rows.of(hp, ww, op, dr(ww, px)), nb, bb), Laws.flt.bytes(row, nb,
      True{}), True{}, fbytes(row, nb, masked.all(op, qq), e_len)),
    ih(dr(ww, px), e3))

# the rows of samples fit: each w times nchn masked bytes
def fit.rows(
  hn: Nat,
  +ww: Nat,
  +op: Bool,
  +px: List<&2, U32>,
  hl: {List.length(&2, U32, px) == Nat.mul(hn, ww) : Nat}
) -> fit.rows.ty(hn, ww, op, px):
  match hn:
    case 0n:
      {==}
    case 1n+(+hp):
      fit.rows.at(hp, ww, op, px, split(ww, Nat.mul(hp, ww), px, hl), xs => ex => fit.rows(hp, ww, op, xs, ex))

# masked bytes, then bytes: bytes
def bytes.app(
  +xs: List<&2, U32>,
  +rest: List<&2, U32>,
  hm: masked(xs),
  hr: {Laws.bytes.go(rest, True{}) == True{} : Bool}
) -> {Laws.bytes.go(List.append(&2, U32, xs, rest), True{}) == True{} : Bool}:
  match xs:
    case Nil{}:
      hr
    case +xx <> +tl:
      (ex, ht) = hm
      Equal.trans(Bool, Laws.bytes.go(List.append(&2, U32, tl, rest), U32.is_le(xx, 255)), Laws.bytes.go(List.append(&2,
        U32, tl, rest), True{}), True{}, Equal.cong(Bool, Bool, bb => Laws.bytes.go(List.append(&2, U32, tl, rest), bb),
        U32.is_le(xx, 255), True{}, byte.le(xx, ex)), bytes.app(tl, rest, ht, hr))

# masked rows as scanlines are bytes
def bytes.scan(
  +rows: List<&2, List<&2, U32>>,
  hm: masked.rows(rows)
) -> {Laws.bytes.go(scan(rows), True{}) == True{} : Bool}:
  match rows:
    case Nil{}:
      {==}
    case +row <> +tl:
      (hr, ht) = hm
      bytes.app(row, scan(tl), hr, bytes.scan(tl, ht))

# ---- G. the samples back, and the counts in range ----

# opaque samples: their red, green and blue, packed with alpha 255, are the samples
def rgb.back(
  +px: List<&2, U32>,
  +hop: {Laws.all_opaque(px) == True{} : Bool}
) -> {Laws.spec.rgb(chans.all(True{}, px)) == Some{px} : Maybe<&2, List<&2, U32>>}:
  match px:
    case Nil{}:
      {==}
    case +cc <> +tl:
      +ho = U32L.and_left(Laws.opaque(cc), Laws.all_opaque(tl), hop)
      +ht = U32L.and_right(Laws.opaque(cc), Laws.all_opaque(tl), hop)
      +e_sh = U32L.ueq(U32.shrn(cc, 24n), 255, ho)
      +pk = Laws.spec.argb(255, Png.enc.r(cc), Png.enc.g(cc), Png.enc.b(cc))
      +e_a = {Equal.trans(U32, Png.enc.a(cc), U32.shrn(cc, 24n), 255, alpha.top(cc), e_sh) : {Png.enc.a(cc) == 255 :
        U32}}
      +e_c = {Equal.trans(U32, pk, Laws.spec.argb(Png.enc.a(cc), Png.enc.r(cc), Png.enc.g(cc), Png.enc.b(cc)), cc,
        Equal.cong(U32, U32, aa => Laws.spec.argb(aa, Png.enc.r(cc), Png.enc.g(cc), Png.enc.b(cc)), 255, Png.enc.a(cc),
        Equal.sym(U32, Png.enc.a(cc), 255, e_a)), be.back(cc)) : {pk == cc : U32}}
      Equal.trans(Maybe<&2, List<&2, U32>>, Laws.spec.cons(pk, Laws.spec.rgb(chans.all(True{}, tl))),
        Laws.spec.cons(pk, Some{tl}), Some{cc <> tl},
        Equal.cong(Maybe<&2, List<&2, U32>>, Maybe<&2, List<&2, U32>>, mm => Laws.spec.cons(pk, mm),
          Laws.spec.rgb(chans.all(True{}, tl)), Some{tl}, rgb.back(tl, ht)),
        Equal.cong(U32, Maybe<&2, List<&2, U32>>, uu => Some{uu <> tl}, pk, cc, e_c))

# any samples: their red, green, blue and alpha, packed, are the samples
def rgba.back(+px: List<&2, U32>) -> {Laws.spec.rgba(chans.all(False{}, px)) == Some{px} : Maybe<&2, List<&2, U32>>}:
  match px:
    case Nil{}:
      {==}
    case +cc <> +tl:
      +pk = Laws.spec.argb(Png.enc.a(cc), Png.enc.r(cc), Png.enc.g(cc), Png.enc.b(cc))
      Equal.trans(Maybe<&2, List<&2, U32>>, Laws.spec.cons(pk, Laws.spec.rgba(chans.all(False{}, tl))),
        Laws.spec.cons(pk, Some{tl}), Some{cc <> tl},
        Equal.cong(Maybe<&2, List<&2, U32>>, Maybe<&2, List<&2, U32>>, mm => Laws.spec.cons(pk, mm),
          Laws.spec.rgba(chans.all(False{}, tl)), Some{tl}, rgba.back(tl)),
        Equal.cong(U32, Maybe<&2, List<&2, U32>>, uu => Some{uu <> tl}, pk, cc, be.back(cc)))

# a number is at most its successor
def le.succ(xx: Nat) -> {Nat.is_le(xx, 1n+xx) == True{} : Bool}:
  match xx:
    case 0n:
      {==}
    case 1n+pp:
      le.succ(pp)

# adding one on the right
def add.one.nat(+xx: Nat) -> {Nat.add(xx, 1n) == 1n+xx : Nat}:
  Equal.trans(Nat, Nat.add(xx, 1n), 1n+Nat.add(xx, 0n), 1n+xx, Wp2.nat_add_succ(xx, 0n), Equal.cong(Nat, Nat, nn =>
    1n+nn, Nat.add(xx, 0n), xx, Wp2.nat_add_zero(xx)))

# at most is not above
def le.not.gt(cc: Cmp, hh: {Cmp.is_le(cc) == True{} : Bool}) -> {Cmp.is_gt(cc) == False{} : Bool}:
  match cc:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({True{} == False{} : Bool}, U32L.false_true(hh))

# a natural at most a word's value, taken in a word, keeps its value
def nat.fits(
  kk: Nat,
  +cap: U32,
  +hh: {Nat.is_le(kk, U32.to_nat(cap)) == True{} : Bool}
) -> {U32.to_nat(U32.from_nat(kk)) == kk : Nat}:
  match kk:
    case 0n:
      {==}
    case 1n+(+pp):
      +cn = U32.to_nat(cap)
      +up = U32.from_nat(pp)
      +hp = R.le_trans(pp, 1n+pp, cn, le.succ(pp), hh)
      +ih = nat.fits(pp, cap, hp)
      +h_lt = {Equal.trans(Bool, Nat.is_lt(U32.to_nat(up), cn), Nat.is_lt(pp, cn), True{}, Equal.cong(Nat, Bool, nn =>
        Nat.is_lt(nn, cn), U32.to_nat(up), pp, ih), Equal.trans(Bool, Nat.is_lt(pp, cn), Nat.is_le(1n+pp, cn), True{},
        R.lt_le_succ(pp, cn), hh)) : {Nat.is_lt(U32.to_nat(up), cn) == True{} : Bool}}
      Equal.trans(Nat, U32.to_nat(U32.inc(up)), U32.to_nat(U32.add(up, 1)), 1n+pp,
        Equal.cong(U32, Nat, uu => U32.to_nat(uu), U32.inc(up), U32.add(up, 1), Equal.sym(U32, U32.add(up, 1),
          U32.inc(up), add.one(up))),
        Equal.trans(Nat, U32.to_nat(U32.add(up, 1)), 1n+U32.to_nat(up), 1n+pp, Wp2.inc_nat(up, cap, Wp2.u_lt(up, cap,
          h_lt)), Equal.cong(Nat, Nat, nn => 1n+nn, U32.to_nat(up), pp, ih)))

# a U32 whose value is at most cap's is not above cap
def gt.no(
  +uu: U32,
  +cap: U32,
  +nn: Nat,
  en: {U32.to_nat(uu) == nn : Nat},
  hh: {Nat.is_le(nn, U32.to_nat(cap)) == True{} : Bool}
) -> {U32.is_gt(uu, cap) == False{} : Bool}:
  +cn = U32.to_nat(cap)
  Equal.trans(Bool, U32.is_gt(uu, cap), Cmp.is_gt(Nat.cmp(nn, cn)), False{},
    Equal.trans(Bool, U32.is_gt(uu, cap), Cmp.is_gt(Nat.cmp(U32.to_nat(uu), cn)), Cmp.is_gt(Nat.cmp(nn, cn)),
      Equal.cong(Cmp, Bool, cc => Cmp.is_gt(cc), U32.cmp(uu, cap), Nat.cmp(U32.to_nat(uu), cn), Wp2.u_cmp(uu, cap)),
      Equal.cong(Nat, Bool, kk => Cmp.is_gt(Nat.cmp(kk, cn)), U32.to_nat(uu), nn, en)),
    le.not.gt(Nat.cmp(nn, cn), hh))

# a U32 whose value is at most cap's is at most cap
def le.yes(
  +uu: U32,
  +cap: U32,
  +nn: Nat,
  en: {U32.to_nat(uu) == nn : Nat},
  hh: {Nat.is_le(nn, U32.to_nat(cap)) == True{} : Bool}
) -> {U32.is_le(uu, cap) == True{} : Bool}:
  +cn = U32.to_nat(cap)
  Equal.trans(Bool, U32.is_le(uu, cap), Nat.is_le(nn, cn), True{},
    Equal.trans(Bool, U32.is_le(uu, cap), Nat.is_le(U32.to_nat(uu), cn), Nat.is_le(nn, cn), Wp2.u_le(uu, cap),
      Equal.cong(Nat, Bool, kk => Nat.is_le(kk, cn), U32.to_nat(uu), nn, en)), hh)

# a U32 above 0: its value is a successor
def gt.pos(+uu: U32, +pp: Nat, en: {U32.to_nat(uu) == 1n+pp : Nat}) -> {U32.is_gt(uu, 0) == True{} : Bool}:
  Equal.trans(Bool, U32.is_gt(uu, 0), Cmp.is_gt(Nat.cmp(1n+pp, 0n)), True{}, Equal.trans(Bool, U32.is_gt(uu, 0),
    Cmp.is_gt(Nat.cmp(U32.to_nat(uu), 0n)), Cmp.is_gt(Nat.cmp(1n+pp, 0n)), Equal.cong(Cmp, Bool, cc => Cmp.is_gt(cc),
    U32.cmp(uu, 0), Nat.cmp(U32.to_nat(uu), 0n), Wp2.u_cmp(uu, 0)), Equal.cong(Nat, Bool, kk => Cmp.is_gt(Nat.cmp(kk,
    0n)), U32.to_nat(uu), 1n+pp, en)), {==})

# the length of an append
def len.app(
  +aa: List<&2, U32>,
  +bb: List<&2, U32>
) -> {List.length(&2, U32, List.append(&2, U32, aa, bb)) == Nat.add(List.length(&2, U32, aa), List.length(&2, U32, bb))
  : Nat}:
  match aa:
    case Nil{}:
      {==}
    case _hd <> +tl:
      Equal.cong(Nat, Nat, nn => 1n+nn, List.length(&2, U32, List.append(&2, U32, tl, bb)), Nat.add(List.length(&2, U32,
        tl), List.length(&2, U32, bb)), len.app(tl, bb))

# the scanlines of h rows of w samples: h times a filter byte and w samples' channels
def len.scan.ty(+hn: Nat, +ww: Nat, +op: Bool, +px: List<&2, U32>) -> Type:
  {List.length(&2, U32, scan(rows.of(hn, ww, op, px))) == Nat.mul(hn, 1n+Nat.mul(ww, Laws.spec.nch(op))) : Nat}

# a row split off the front, then the rest by induction
def len.scan.at(
  +hp: Nat,
  +ww: Nat,
  +op: Bool,
  +px: List<&2, U32>,
  sp: split.ty(ww, Nat.mul(hp, ww), px),
  ih: @xs: List<&2, U32> -> {List.length(&2, U32, xs) == Nat.mul(hp, ww) : Nat} -> len.scan.ty(hp, ww, op, xs)
) -> len.scan.ty(1n+hp, ww, op, px):
  (_e1, (e2, e3)) = sp
  +qq = tk(ww, px)
  +rr = dr(ww, px)
  +row = chans.all(op, qq)
  +tl = scan(rows.of(hp, ww, op, rr))
  +nb = Nat.mul(ww, Laws.spec.nch(op))
  +e_row = {Equal.trans(Nat, List.length(&2, U32, row), Nat.mul(List.length(&2, U32, qq), Laws.spec.nch(op)), nb,
    len.chans.all(op, qq), Equal.cong(Nat, Nat, nn => Nat.mul(nn, Laws.spec.nch(op)), List.length(&2, U32, qq), ww,
    e2)) : {List.length(&2, U32, row) == nb : Nat}}
  Equal.cong(Nat, Nat, nn => 1n+nn, List.length(&2, U32, List.append(&2, U32, row, tl)), Nat.add(nb, Nat.mul(hp,
    1n+nb)), Equal.trans(Nat, List.length(&2, U32, List.append(&2, U32, row, tl)), Nat.add(List.length(&2, U32, row),
    List.length(&2, U32, tl)), Nat.add(nb, Nat.mul(hp, 1n+nb)), len.app(row, tl), Equal.trans(Nat,
    Nat.add(List.length(&2, U32, row), List.length(&2, U32, tl)), Nat.add(nb, List.length(&2, U32, tl)), Nat.add(nb,
    Nat.mul(hp, 1n+nb)), Equal.cong(Nat, Nat, nn => Nat.add(nn, List.length(&2, U32, tl)), List.length(&2, U32, row),
    nb, e_row), Equal.cong(Nat, Nat, nn => Nat.add(nb, nn), List.length(&2, U32, tl), Nat.mul(hp, 1n+nb), ih(rr,
    e3)))))

# the scanlines' length
def len.scan(
  hn: Nat,
  +ww: Nat,
  +op: Bool,
  +px: List<&2, U32>,
  hl: {List.length(&2, U32, px) == Nat.mul(hn, ww) : Nat}
) -> len.scan.ty(hn, ww, op, px):
  match hn:
    case 0n:
      {==}
    case 1n+(+hp):
      len.scan.at(hp, ww, op, px, split(ww, Nat.mul(hp, ww), px, hl), xs => ex => len.scan(hp, ww, op, xs, ex))

# ---- H. the one-block encoding's numbers ----

# enc.nch's value
def nch.val(op: Bool) -> {U32.to_nat(Png.enc.nch(op)) == Laws.spec.nch(op) : Nat}:
  match op:
    case True{}:
      {==}
    case False{}:
      {==}

# the decoder's bytes per pixel for the encoder's colour type: the channels
def bpp.eq(op: Bool) -> {Png.png.bpp(Png.enc.ct(op)) == Png.enc.nch(op) : U32}:
  match op:
    case True{}:
      {==}
    case False{}:
      {==}

# the zlib stream enc.zlib writes before the check that the block fits is taken
def zlib.at(zz: Bool, +raw: List<&2, U32>, +nn: U32) -> List<&2, U32>:
  Png.enc.cat([120, 1], Png.enc.cat(Png.enc.blocks.fit(zz, 65535, nn, raw), Png.enc.be(Inf.adler.of(raw))))

# one stored block: the zlib header, the block header, the bytes, and Adler-32
def zlib.len(
  +raw: List<&2, U32>,
  +nn: U32,
  hle: {U32.is_le(nn, 65535) == True{} : Bool}
) -> {List.length(&2, U32, Png.enc.zlib(raw, nn)) == 11n+List.length(&2, U32, raw) : Nat}:
  +hd = {Png.enc.head(True{}, nn, (nn .^. 65535 : U32)) : List<&2, U32>}
  +ad = Png.enc.be(Inf.adler.of(raw))
  +ln = List.length(&2, U32, raw)
  Equal.trans(Nat, List.length(&2, U32, zlib.at(U32.is_le(nn, 65535), raw, nn)), List.length(&2, U32, zlib.at(True{},
    raw, nn)), 11n+ln,
    Equal.cong(Bool, Nat, zz => List.length(&2, U32, zlib.at(zz, raw, nn)), U32.is_le(nn, 65535), True{}, hle),
    Equal.trans(Nat, List.length(&2, U32, zlib.at(True{}, raw, nn)), 7n+List.length(&2, U32, List.append(&2, U32, raw,
      ad)), 11n+ln,
      Equal.cong(List<&2, U32>, Nat, xs => 2n+List.length(&2, U32, xs), Png.enc.cat(List.append(&2, U32, hd, raw), ad),
        List.append(&2, U32, List.append(&2, U32, hd, raw), ad), Wp2.cat_app(List.append(&2, U32, hd, raw), ad)),
      Equal.trans(Nat, 7n+List.length(&2, U32, List.append(&2, U32, raw, ad)), 7n+Nat.add(ln, 4n), 11n+ln,
        Equal.cong(Nat, Nat, kk => 7n+kk, List.length(&2, U32, List.append(&2, U32, raw, ad)), Nat.add(ln, 4n),
          len.app(raw, ad)),
        Equal.cong(Nat, Nat, kk => 7n+kk, Nat.add(ln, 4n), Nat.add(4n, ln), R.add_comm(ln, 4n)))))

# a list of 11 bytes more than a count at most cap's fits in a U32 count,
# when 11 more than cap is at most cap2
def fits.small(
  +xs: List<&2, U32>,
  +nn: Nat,
  +cap: U32,
  +cap2: U32,
  el: {List.length(&2, U32, xs) == 11n+nn : Nat},
  hh: {Nat.is_le(nn, U32.to_nat(cap)) == True{} : Bool},
  hc: {Nat.is_le(11n+U32.to_nat(cap), U32.to_nat(cap2)) == True{} : Bool}
) -> Laws.spec.fits(xs):
  +ll = List.length(&2, U32, xs)
  +cn = U32.to_nat(cap)
  +c2 = U32.to_nat(cap2)
  +h1 = {R.le_add_mono(11n, nn, cn, hh) : {Nat.is_le(Nat.add(11n, nn), Nat.add(11n, cn)) == True{} : Bool}}
  +h2 = {R.le_trans(Nat.add(11n, nn), Nat.add(11n, cn), c2, h1, hc) : {Nat.is_le(Nat.add(11n, nn), c2) == True{} :
    Bool}}
  +h3 = {R.le_rw_l(Nat.add(11n, nn), ll, c2, Equal.sym(Nat, ll, 11n+nn, el), h2) : {Nat.is_le(ll, c2) == True{} :
    Bool}}
  nat.fits(ll, cap2, h3)
