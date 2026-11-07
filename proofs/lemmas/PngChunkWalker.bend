# the PNG chunk walker over chunks laid out as spec.chunk, and the frame it
# decodes
import Base
import ../../main.bend as Img
import ../../src/crc.bend as Crc
import ../../src/png.bend as Png
import ../../laws/defs/PngSpecification.bend as D1
import ./BasicFacts.bend as M1
import ./CrcReference.bend as M2
import ./PngEncoderArithmetic.bend as M3
import ../../laws/defs/SizeBounds.bend as D2

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
) -> {M1.w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13), or1(b14),
    or1(b15),
  or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24), or3(b25), or3(b26),
  or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == M1.w32(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13,  # noqa: S002
  b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : U32}:
  %or1.id(b8) : {M1.w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
      or1(b14),
    or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24), or3(b25),
    or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == M1.w32(b0, b1, b2, b3, b4, b5, b6, b7, _, b9, b10,
        b11,
    b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : U32}
  %or1.id(b9) : {M1.w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
      or1(b14),
    or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24), or3(b25),
    or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == M1.w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), _,
        b10,
    b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : U32}
  %or1.id(b10) : {M1.w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == M1.w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), _, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29,
    b30, b31) : U32}
  %or1.id(b11) : {M1.w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == M1.w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), _, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28,
    b29, b30, b31) : U32}
  %or1.id(b12) : {M1.w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == M1.w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), or1(b11), _, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27,
    b28, b29, b30, b31) : U32}
  %or1.id(b13) : {M1.w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == M1.w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), _, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26,
    b27, b28, b29, b30, b31) : U32}
  %or1.id(b14) : {M1.w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == M1.w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13), _, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25,
    b26, b27, b28, b29, b30, b31) : U32}
  %or1.id(b15) : {M1.w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == M1.w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13), or1(b14), _, b16, b17, b18, b19, b20, b21, b22, b23, b24,
    b25, b26, b27, b28, b29, b30, b31) : U32}
  %or2.id(b16) : {M1.w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == M1.w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13), or1(b14), or1(b15), _, b17, b18, b19, b20, b21, b22, b23,
    b24, b25, b26, b27, b28, b29, b30, b31) : U32}
  %or2.id(b17) : {M1.w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == M1.w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13), or1(b14), or1(b15), or2(b16), _, b18, b19, b20, b21, b22,
    b23, b24, b25, b26, b27, b28, b29, b30, b31) : U32}
  %or2.id(b18) : {M1.w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == M1.w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13), or1(b14), or1(b15), or2(b16), or2(b17), _, b19, b20, b21,
    b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : U32}
  %or2.id(b19) : {M1.w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == M1.w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13), or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), _, b20,
    b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : U32}
  %or2.id(b20) : {M1.w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == M1.w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13), or1(b14), or1(b15), or2(b16), or2(b17), or2(b18),
    or2(b19), _, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : U32}
  %or2.id(b21) : {M1.w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == M1.w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13), or1(b14), or1(b15), or2(b16), or2(b17), or2(b18),
    or2(b19), or2(b20), _, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : U32}
  %or2.id(b22) : {M1.w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == M1.w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13), or1(b14), or1(b15), or2(b16), or2(b17), or2(b18),
    or2(b19), or2(b20), or2(b21), _, b23, b24, b25, b26, b27, b28, b29, b30, b31) : U32}
  %or2.id(b23) : {M1.w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == M1.w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13), or1(b14), or1(b15), or2(b16), or2(b17), or2(b18),
    or2(b19), or2(b20), or2(b21), or2(b22), _, b24, b25, b26, b27, b28, b29, b30, b31) : U32}
  %or3.id(b24) : {M1.w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == M1.w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13), or1(b14), or1(b15), or2(b16), or2(b17), or2(b18),
    or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), _, b25, b26, b27, b28, b29, b30, b31) : U32}
  %or3.id(b25) : {M1.w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == M1.w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13), or1(b14), or1(b15), or2(b16), or2(b17), or2(b18),
    or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24), _, b26, b27, b28, b29, b30, b31) : U32}
  %or3.id(b26) : {M1.w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == M1.w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13), or1(b14), or1(b15), or2(b16), or2(b17), or2(b18),
    or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24), or3(b25), _, b27, b28, b29, b30, b31) : U32}
  %or3.id(b27) : {M1.w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == M1.w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13), or1(b14), or1(b15), or2(b16), or2(b17), or2(b18),
    or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24), or3(b25), or3(b26), _, b28, b29, b30, b31) : U32}
  %or3.id(b28) : {M1.w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == M1.w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13), or1(b14), or1(b15), or2(b16), or2(b17), or2(b18),
    or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24), or3(b25), or3(b26), or3(b27), _, b29, b30, b31) : U32}
  %or3.id(b29) : {M1.w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == M1.w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13), or1(b14), or1(b15), or2(b16), or2(b17), or2(b18),
    or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24), or3(b25), or3(b26), or3(b27), or3(b28), _, b30,
    b31) : U32}
  %or3.id(b30) : {M1.w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == M1.w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13), or1(b14), or1(b15), or2(b16), or2(b17), or2(b18),
    or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24), or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), _,
    b31) : U32}
  %or3.id(b31) : {M1.w32(b0, b1, b2, b3, b4, b5, b6, b7, or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13),
    or1(b14), or1(b15), or2(b16), or2(b17), or2(b18), or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24),
    or3(b25), or3(b26), or3(b27), or3(b28), or3(b29), or3(b30), or3(b31)) == M1.w32(b0, b1, b2, b3, b4, b5, b6, b7,
    or1(b8), or1(b9), or1(b10), or1(b11), or1(b12), or1(b13), or1(b14), or1(b15), or2(b16), or2(b17), or2(b18),
    or2(b19), or2(b20), or2(b21), or2(b22), or2(b23), or3(b24), or3(b25), or3(b26), or3(b27), or3(b28), or3(b29),
    or3(b30), _) : U32}
  {==}

# the four bytes spec.be4 writes, read back big-endian by the decoder, are the
# U32: its 32 bits taken apart, both sides are be.fix's words
def prt.be.back(
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
  Png.png.crc(Png.png.apply(typ, data, pg), _u => Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [],
    Png.png.pgof(Png.png.apply(typ, data, pg))))

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
  hf: D1.spec.fits(data)
) -> {Png.png.go(D1.spec.chunk([t0, t1, t2, t3], data, rest), Png.ZLen{}, False{}, 0, 0, [], [], pg) ==
  chunk.next(Png.be.u32(t0, t1, t2, t3), List.reverse(&2, U32, data), rest, pg) : Maybe<&2, Png.Pic>}:
  (+hfw, +hfs) = hf
  +nn = U32.from_nat(List.length(&2, U32, data))
  +sum = D1.crc.ref(t0 <> t1 <> t2 <> t3 <> data)
  +typ = Png.be.u32(t0, t1, t2, t3)
  +crc = List.reverse.go(&2, U32, data, [t3, t2, t1, t0])
  +dat = List.reverse.go(&2, U32, data, [])
  +got = Png.be.u32(bt3(sum), bt2(sum), bt1(sum), bt0(sum))
  +want = Crc.crc32(List.reverse(&2, U32, crc))
  +ln = List.length(&2, U32, data)
  +hn = {Equal.trans(Nat, U32.to_nat(Png.be.u32(bt3(nn), bt2(nn), bt1(nn), bt0(nn))), U32.to_nat(nn),
    ln, Equal.cong(U32, Nat, uu => U32.to_nat(uu), Png.be.u32(bt3(nn), bt2(nn), bt1(nn),
    bt0(nn)), nn, prt.be.back(nn)), hfw) : {U32.to_nat(Png.be.u32(bt3(nn), bt2(nn), bt1(nn), bt0(nn))) ==
    ln : Nat}}
  +hs = {Equal.trans(Bool, Png.png.short(Png.be.u32(bt3(nn), bt2(nn), bt1(nn), bt0(nn))), Png.png.short(nn), True{},
    Equal.cong(U32, Bool, uu => Png.png.short(uu), Png.be.u32(bt3(nn), bt2(nn), bt1(nn), bt0(nn)), nn,
      prt.be.back(nn)),
    Equal.trans(Bool, Png.png.short(nn), D2.below(31n, U32.to_nat(nn)), True{}, M3.short.nat(nn),
      Equal.trans(Bool, D2.below(31n, U32.to_nat(nn)), D2.below(31n, ln), True{},
        Equal.cong(Nat, Bool, kk => D2.below(31n, kk), U32.to_nat(nn), ln, hfw), hfs))) :
    {Png.png.short(Png.be.u32(bt3(nn), bt2(nn), bt1(nn), bt0(nn))) == True{} : Bool}}
  +e_want = {Equal.trans(U32, want, Crc.crc32(t0 <> t1 <> t2 <> t3 <> data), sum,
    Equal.cong(List<&2, U32>, U32, xs => Crc.crc32(xs), List.reverse(&2, U32, crc), t0 <> t1 <> t2 <> t3 <> data,
      M2.crc_bytes(data, t0, t1, t2, t3)), M2.crc32_ref(t0 <> t1 <> t2 <> t3 <> data)) : {want == sum : U32}}
  +e_eq = {Equal.trans(Bool, U32.is_eq(got, want), U32.is_eq(sum, want), True{},
    Equal.cong(U32, Bool, uu => U32.is_eq(uu, want), got, sum, prt.be.back(sum)),
    Equal.trans(Bool, U32.is_eq(sum, want), U32.is_eq(sum, sum), True{},
      Equal.cong(U32, Bool, uu => U32.is_eq(sum, uu), want, sum, e_want), M1.u32_eq_refl(sum))) :
    {U32.is_eq(got, want) == True{} : Bool}}
  Equal.trans(Maybe<&2, Png.Pic>,
    Png.png.go(D1.spec.chunk([t0, t1, t2, t3], data, rest), Png.ZLen{}, False{}, 0, 0, [], [], pg),
    M2.at_crc(bt3(sum), bt2(sum), bt1(sum), bt0(sum), rest, typ, crc, dat, pg),
    chunk.next(typ, dat, rest, pg),
    M2.walk_chunk(bt3(nn), bt2(nn), bt1(nn), bt0(nn), t0, t1, t2, t3, data, bt3(sum), bt2(sum), bt1(sum), bt0(sum),
      rest, pg, hn, hs),
    Equal.cong(Bool, Maybe<&2, Png.Pic>, zz => Png.png.crc(Png.png.judge.at(zz, typ, dat, pg),
      _u => Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], Png.png.pgof(Png.png.judge.at(zz, typ, dat, pg)))),
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
  hf: D1.spec.fits(data),
  ea: {Png.png.apply(Png.be.u32(t0, t1, t2, t3), List.reverse(&2, U32, data), pg) == Png.NMore{pg2} : Png.Nx}
) -> {Png.png.go(D1.spec.chunk([t0, t1, t2, t3], data, rest), Png.ZLen{}, False{}, 0, 0, [], [], pg) ==
  Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], pg2) : Maybe<&2, Png.Pic>}:
  Equal.trans(Maybe<&2, Png.Pic>,
    Png.png.go(D1.spec.chunk([t0, t1, t2, t3], data, rest), Png.ZLen{}, False{}, 0, 0, [], [], pg),
    chunk.next(Png.be.u32(t0, t1, t2, t3), List.reverse(&2, U32, data), rest, pg),
    Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], pg2),
    chunk.walk(t0, t1, t2, t3, data, rest, pg, hf),
    Equal.cong(Png.Nx, Maybe<&2, Png.Pic>, nx => Png.png.crc(nx, _u => Png.png.go(rest,
      Png.ZLen{}, False{}, 0, 0, [], [], Png.png.pgof(nx))), Png.png.apply(Png.be.u32(t0, t1, t2, t3),
      List.reverse(&2, U32, data), pg), Png.NMore{pg2}, ea))

# the chunk that ends the image, NEnd: the walker finishes the picture,
# whatever bytes follow
def chunk.end(
  +t0: U32,
  +t1: U32,
  +t2: U32,
  +t3: U32,
  +data: List<&2, U32>,
  +rest: List<&2, U32>,
  +pg: Png.Pg,
  +pg2: Png.Pg,
  hf: D1.spec.fits(data),
  ea: {Png.png.apply(Png.be.u32(t0, t1, t2, t3), List.reverse(&2, U32, data), pg) == Png.NEnd{pg2} : Png.Nx}
) -> {Png.png.go(D1.spec.chunk([t0, t1, t2, t3], data, rest), Png.ZLen{}, False{}, 0, 0, [], [], pg) ==
  Png.png.finish(pg2) : Maybe<&2, Png.Pic>}:
  Equal.trans(Maybe<&2, Png.Pic>,
    Png.png.go(D1.spec.chunk([t0, t1, t2, t3], data, rest), Png.ZLen{}, False{}, 0, 0, [], [], pg),
    chunk.next(Png.be.u32(t0, t1, t2, t3), List.reverse(&2, U32, data), rest, pg),
    Png.png.finish(pg2),
    chunk.walk(t0, t1, t2, t3, data, rest, pg, hf),
    Equal.cong(Png.Nx, Maybe<&2, Png.Pic>, nx => Png.png.crc(nx, _u => Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [],
      [], Png.png.pgof(nx))), Png.png.apply(Png.be.u32(t0, t1, t2, t3), List.reverse(&2, U32, data), pg),
      Png.NEnd{pg2}, ea))

# the decoder's test of a side is spec.side
law side.same:
  for +nn: U32
  {Png.png.side(nn) == D1.spec.side(nn) : Bool}

# the proof of side.same
def side.same(nn):
  Equal.cong(Bool, Bool, bb => Bool.and(U32.is_gt(nn, 0), bb), Png.png.short(nn), D2.below(31n, U32.to_nat(nn)),
    M3.short.nat(nn))

# a side spec.side takes, the decoder takes
def side.ok(+nn: U32, hh: {D1.spec.side(nn) == True{} : Bool}) -> {Png.png.side(nn) == True{} : Bool}:
  Equal.trans(Bool, Png.png.side(nn), D1.spec.side(nn), True{}, side.same(nn), hh)

# png.good takes a width and height from 1 to 2^31 - 1, bit depth 8, a
# colour type it knows, and methods 0
def good.ok(
  +ww: U32,
  +hh: U32,
  +cc: U32,
  h_ww: {D1.spec.side(ww) == True{} : Bool},
  h_hh: {D1.spec.side(hh) == True{} : Bool},
  h_cc: {D1.spec.colour.ok(cc) == True{} : Bool}
) -> {Png.png.good(ww, hh, 8, cc, 0, 0, 0) == True{} : Bool}:
  +sh = Png.png.side(hh)
  +rr = Bool.and(D1.spec.colour.ok(cc), True{})
  Equal.trans(Bool, Png.png.good(ww, hh, 8, cc, 0, 0, 0), Bool.and(Bool.and(True{}, sh), rr), True{},
    Equal.cong(Bool, Bool, bb => Bool.and(Bool.and(bb, sh), rr), Png.png.side(ww), True{}, side.ok(ww, h_ww)),
    Equal.trans(Bool, Bool.and(Bool.and(True{}, sh), rr), Bool.and(Bool.and(True{}, True{}), rr), True{},
      Equal.cong(Bool, Bool, bb => Bool.and(Bool.and(True{}, bb), rr), sh, True{}, side.ok(hh, h_hh)),
      Equal.cong(Bool, Bool, bb => Bool.and(Bool.and(True{}, True{}), Bool.and(bb, True{})), D1.spec.colour.ok(cc),
        True{}, h_cc)))

# an IHDR png.good takes starts the state
def ihdr.ok.true(
  zz: Bool,
  +ww: U32,
  +hh: U32,
  +cc: U32,
  ez: {zz == True{} : Bool}
) -> {Png.png.ihdr.ok(zz, ww, hh, 8, cc, 0, 0, 0) == Png.NMore{M1.st(ww, hh, cc, None{}, None{}, [],
    False{})} : Png.Nx}:
  match zz:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Png.NBad{} == Png.NMore{M1.st(ww, hh, cc, None{}, None{}, [], False{})} : Png.Nx},
        M1.false_true(ez))

# the IHDR chunk: its width and height read back, png.good takes it
def ihdr.step(
  +ww: U32,
  +hh: U32,
  +cc: U32,
  h_ww: {D1.spec.side(ww) == True{} : Bool},
  h_hh: {D1.spec.side(hh) == True{} : Bool},
  h_cc: {D1.spec.colour.ok(cc) == True{} : Bool}
) -> {Png.png.apply(Png.be.u32(73, 72, 68, 82), List.reverse(&2, U32, D1.spec.ihdr.data(ww, hh, cc)), Png.pg.empty())
  == Png.NMore{M1.st(ww, hh, cc, None{}, None{}, [], False{})} : Png.Nx}:
  +wb = Png.be.u32(bt3(ww), bt2(ww), bt1(ww), bt0(ww))
  +hb = Png.be.u32(bt3(hh), bt2(hh), bt1(hh), bt0(hh))
  Equal.trans(Png.Nx, Png.png.ihdr.ok(Png.png.good(wb, hb, 8, cc, 0, 0, 0), wb, hb, 8, cc, 0, 0, 0),
    Png.png.ihdr.ok(Png.png.good(ww, hh, 8, cc, 0, 0, 0), ww, hh, 8, cc, 0, 0, 0),
    Png.NMore{M1.st(ww, hh, cc, None{}, None{}, [], False{})},
    Equal.trans(Png.Nx, Png.png.ihdr.ok(Png.png.good(wb, hb, 8, cc, 0, 0, 0), wb, hb, 8, cc, 0, 0, 0),
      Png.png.ihdr.ok(Png.png.good(ww, hb, 8, cc, 0, 0, 0), ww, hb, 8, cc, 0, 0, 0),
      Png.png.ihdr.ok(Png.png.good(ww, hh, 8, cc, 0, 0, 0), ww, hh, 8, cc, 0, 0, 0),
      Equal.cong(U32, Png.Nx, xx => Png.png.ihdr.ok(Png.png.good(xx, hb, 8, cc, 0, 0, 0), xx, hb, 8, cc, 0, 0, 0), wb,
        ww, prt.be.back(ww)),
      Equal.cong(U32, Png.Nx, xx => Png.png.ihdr.ok(Png.png.good(ww, xx, 8, cc, 0, 0, 0), ww, xx, 8, cc, 0, 0, 0), hb,
        hh, prt.be.back(hh))),
    ihdr.ok.true(Png.png.good(ww, hh, 8, cc, 0, 0, 0), ww, hh, cc, good.ok(ww, hh, cc, h_ww, h_hh, h_cc)))

# a chunk the checks take goes on to the next
def allow.true(zz: Bool, +pg: Png.Pg, ez: {zz == True{} : Bool}) -> {Png.png.allow(zz, pg) == Png.NMore{pg} : Png.Nx}:
  match zz:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Png.NBad{} == Png.NMore{pg} : Png.Nx}, M1.false_true(ez))

# the PLTE chunk after IHDR: its colour type allows it and its length is a
# palette's, so the state keeps its data
def plte.step(
  +ww: U32,
  +hh: U32,
  +cc: U32,
  +pp: List<&2, U32>,
  h_pl: {D1.spec.plte.ok(cc, Some{pp}) == True{} : Bool}
) -> {Png.png.apply(Png.be.u32(80, 76, 84, 69), List.reverse(&2, U32, pp), M1.st(ww, hh, cc, None{}, None{}, [],
  False{})) == Png.NMore{M1.st(ww, hh, cc, Some{pp}, None{}, [], False{})} : Png.Nx}:
  +ok = Bool.or(U32.is_eq(cc, 2), Bool.or(U32.is_eq(cc, 3), U32.is_eq(cc, 6)))
  +e_len = {M1.len_rev(pp) : {List.length(&2, U32, List.reverse(&2, U32, pp)) == List.length(&2, U32, pp) : Nat}}
  +e_ok = {Equal.trans(Bool, Bool.and(ok, Png.png.mod3(List.reverse(&2, U32, pp))), Bool.and(ok, D1.spec.pal.len(pp)),
    True{}, Equal.cong(Nat, Bool, kk => Bool.and(ok, Bool.and(U32.is_gt(U32.from_nat(kk), 0),
      Bool.and(U32.is_zero((U32.from_nat(kk) % 3 : U32)), U32.is_le(U32.from_nat(kk), 768)))),
      List.length(&2, U32, List.reverse(&2, U32, pp)), List.length(&2, U32, pp), e_len), h_pl) :
    {Bool.and(ok, Png.png.mod3(List.reverse(&2, U32, pp))) == True{} : Bool}}
  +pg0 = M1.st(ww, hh, cc, None{}, None{}, [], False{})
  Equal.trans(Png.Nx, Png.png.allow(Bool.and(ok, Png.png.mod3(List.reverse(&2, U32, pp))), Png.pg.plte(pg0,
    List.reverse(&2, U32, List.reverse(&2, U32, pp)))),
    Png.NMore{Png.pg.plte(pg0, List.reverse(&2, U32, List.reverse(&2, U32, pp)))},
    Png.NMore{M1.st(ww, hh, cc, Some{pp}, None{}, [], False{})},
    allow.true(Bool.and(ok, Png.png.mod3(List.reverse(&2, U32, pp))), Png.pg.plte(pg0, List.reverse(&2, U32,
      List.reverse(&2, U32, pp))), e_ok),
    Equal.cong(List<&2, U32>, Png.Nx, xs => Png.NMore{Png.pg.plte(pg0, xs)}, List.reverse(&2, U32, List.reverse(&2, U32,
      pp)), pp, M1.inf.rev_rev(pp)))

# PLTE, when there is one
def walk.plte(
  +ww: U32,
  +hh: U32,
  +cc: U32,
  +plte: Maybe<&2, List<&2, U32>>,
  +rest: List<&2, U32>,
  h_pl: {D1.spec.plte.ok(cc, plte) == True{} : Bool},
  hf: D1.spec.fits.opt(plte)
) -> {Png.png.go(D1.spec.chunk.opt([80, 76, 84, 69], plte, rest), Png.ZLen{}, False{}, 0, 0, [], [], M1.st(ww, hh, cc,
  None{}, None{}, [], False{})) == Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], M1.st(ww, hh, cc, plte, None{}, [],  # noqa: S002
  False{})) : Maybe<&2, Png.Pic>}:
  match plte:
    case None{}:
      {==}
    case Some{+pp}:
      chunk.more(80, 76, 84, 69, pp, rest, M1.st(ww, hh, cc, None{}, None{}, [], False{}), M1.st(ww, hh, cc, Some{pp},
          None{},
        [], False{}), hf, plte.step(ww, hh, cc, pp, h_pl))

# a tRNS the checks take is kept in the state
def take.true(
  zz: Bool,
  +data: List<&2, U32>,
  +pg: Png.Pg,
  ez: {zz == True{} : Bool}
) -> {Png.png.trns.take(zz, data, pg) == Png.NMore{Png.pg.trns(pg, List.reverse(&2, U32, data))} : Png.Nx}:
  match zz:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Png.NMore{Png.png.seal(pg)} == Png.NMore{Png.pg.trns(pg, List.reverse(&2, U32, data))} : Png.Nx},
        M1.false_true(ez))

# the tRNS chunk after IHDR and PLTE, if any: its colour type allows it, so
# the state keeps its data
def trns.step(
  +ww: U32,
  +hh: U32,
  +cc: U32,
  +plte: Maybe<&2, List<&2, U32>>,
  +tt: List<&2, U32>,
  h_tr: {D1.spec.trns.ok(cc, plte, Some{tt}) == True{} : Bool}
) -> {Png.png.apply(Png.be.u32(116, 82, 78, 83), List.reverse(&2, U32, tt), M1.st(ww, hh, cc, plte, None{}, [],
    False{}))
  == Png.NMore{M1.st(ww, hh, cc, plte, Some{tt}, [], False{})} : Png.Nx}:
  +ok = Png.png.trns.ok(cc, Maybe.is_some(&2, List<&2, U32>, plte))
  +pg0 = M1.st(ww, hh, cc, plte, None{}, [], False{})
  Equal.trans(Png.Nx, Png.png.trns.take(ok, List.reverse(&2, U32, tt), pg0),
    Png.NMore{Png.pg.trns(pg0, List.reverse(&2, U32, List.reverse(&2, U32, tt)))},
    Png.NMore{M1.st(ww, hh, cc, plte, Some{tt}, [], False{})},
    take.true(ok, List.reverse(&2, U32, tt), pg0, h_tr),
    Equal.cong(List<&2, U32>, Png.Nx, xs => Png.NMore{Png.pg.trns(pg0, xs)}, List.reverse(&2, U32, List.reverse(&2, U32,
      tt)), tt, M1.inf.rev_rev(tt)))

# tRNS, when there is one
def walk.trns(
  +ww: U32,
  +hh: U32,
  +cc: U32,
  +plte: Maybe<&2, List<&2, U32>>,
  +trns: Maybe<&2, List<&2, U32>>,
  +rest: List<&2, U32>,
  h_tr: {D1.spec.trns.ok(cc, plte, trns) == True{} : Bool},
  hf: D1.spec.fits.opt(trns)
) -> {Png.png.go(D1.spec.chunk.opt([116, 82, 78, 83], trns, rest), Png.ZLen{}, False{}, 0, 0, [], [], M1.st(ww, hh, cc,
  plte, None{}, [], False{})) == Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], M1.st(ww, hh, cc, plte, trns, [],
  False{})) : Maybe<&2, Png.Pic>}:
  match trns:
    case None{}:
      {==}
    case Some{+tt}:
      chunk.more(116, 82, 78, 83, tt, rest, M1.st(ww, hh, cc, plte, None{}, [], False{}), M1.st(ww, hh, cc, plte,
          Some{tt},
        [], False{}), hf, trns.step(ww, hh, cc, plte, tt, h_tr))

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
  h_pl: {D1.spec.plte.ok(cc, plte) == True{} : Bool}
) -> {M1.need(cc, plte) == True{} : Bool}:
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
      Empty.absurd({Png.NBad{} == Png.NMore{Png.pg.idat(pg, data)} : Png.Nx}, M1.false_true(ez))

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
  h_nd: {M1.need(cc, plte) == True{} : Bool}
) -> {Png.png.apply(Png.be.u32(73, 68, 65, 84), List.reverse(&2, U32, dd), M1.st(ww, hh, cc, plte, trns, acc, sid)) ==
  Png.NMore{M1.st(ww, hh, cc, plte, trns, List.append(&2, U32, List.reverse(&2, U32, dd), acc), True{})} : Png.Nx}:
  idat.try.true(M1.need(cc, plte), List.reverse(&2, U32, dd), M1.st(ww, hh, cc, plte, trns, acc, sid), h_nd)

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
      Empty.absurd({Png.NBad{} == Png.NEnd{Png.pg.iend(pg)} : Png.Nx}, M1.false_true(ez))

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
def prt.rev_app(
  +done: List<&2, U32>,
  +dd: List<&2, U32>
) -> {List.append(&2, U32, List.reverse(&2, U32, dd), List.reverse(&2, U32, done)) == List.reverse(&2, U32,
  List.append(&2, U32, done, dd)) : List<&2, U32>}:
  Equal.sym(List<&2, U32>, List.reverse(&2, U32, List.append(&2, U32, done, dd)), List.append(&2, U32,
    List.reverse(&2, U32, dd), List.reverse(&2, U32, done)),
    Equal.trans(List<&2, U32>, List.reverse(&2, U32, List.append(&2, U32, done, dd)), List.reverse.go(&2, U32, dd,
      List.reverse(&2, U32, done)), List.append(&2, U32, List.reverse(&2, U32, dd), List.reverse(&2, U32, done)),
      revgo_app(done, dd, []), revgo_acc(dd, [], List.reverse(&2, U32, done))))

# the code's sample-count check keeps what spec.raster's keeps
def frame.keep(
  ok: Bool,
  +ww: U32,
  +hh: U32,
  +px: List<&2, U32>
) -> {Img.decode_png.keep(ok, ww, hh, px) == D1.spec.raster.keep(ok, ww, hh, px) : Maybe<&2, Img.Raster>}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

# the picture of px.of's samples, as a raster: spec.raster's
def frame.px(
  mm: Maybe<&2, List<&2, U32>>,
  +ww: U32,
  +hh: U32
) -> {Img.decode_png.pic(Png.png.pic(mm, ww, hh)) == D1.spec.raster(mm, ww, hh) : Maybe<&2, Img.Raster>}:
  match mm:
    case None{}:
      {==}
    case Some{+px}:
      frame.keep(Nat.is_eq(List.length(&2, U32, px), Nat.mul(U32.to_nat(hh), U32.to_nat(ww))), ww, hh, px)

# the unfiltered scanlines packed, as a raster
def frame.scan(
  mm: Maybe<&2, List<&2, U32>>,
  +ww: U32,
  +hh: U32,
  +cc: U32,
  +plte: List<&2, U32>,
  +trns: List<&2, U32>
) -> {Img.decode_png.pic(Png.png.pack(mm, ww, hh, cc, plte, trns)) == D1.spec.raster(D1.spec.px.then(mm, cc, plte,
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
) -> {Img.decode_png.pic(Png.png.samples(mm, ww, hh, cc, plte, trns)) == D1.spec.decoded(mm, ww, hh, cc, plte, trns) :
  Maybe<&2, Img.Raster>}:
  match mm:
    case None{}:
      {==}
    case Some{+raw}:
      frame.scan(Png.unfilter(raw, ww, hh, Png.png.bpp(cc)), ww, hh, cc, plte, trns)
