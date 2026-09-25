# src/crc: CRC-32. PNG covers the chunk type and the chunk data with the
# ISO 3309 / ITU-T V.42 polynomial (ISO/IEC 15948 / W3C PNG).
import Base

# the reflected polynomial
def crc.poly() -> U32:
  3988292384

# eight shifts, one per bit, low bit first. The Nat shrinks, so it is first.
def crc.bit(n: Nat, odd: Bool, +c: U32) -> U32:
  match n odd:
    case 0n _odd:
      c
    case 1n+p True{}:
      +n1 = ((c >> 1n : U32) .^. crc.poly() : U32)
      crc.bit(p, U32.is_eq((n1 .&. 1 : U32), 1), n1)
    case 1n+p False{}:
      +n0 = (c >> 1n : U32)
      crc.bit(p, U32.is_eq((n0 .&. 1 : U32), 1), n0)

# fold one byte into the register
def crc.byte(+c: U32, +b: U32) -> U32:
  +x = (c .^. b : U32)
  crc.bit(8n, U32.is_eq((x .&. 1 : U32), 1), x)

# fold every byte, register still inverted. The list shrinks, so it is first.
def crc.fold(xs: List<&2, U32>, +c: U32) -> U32:
  match xs:
    case Nil{}:
      c
    case Con{+b, t}:
      crc.fold(t, crc.byte(c, b))

# CRC-32 of the bytes, init and final xor all ones
def crc32(xs: List<&2, U32>) -> U32:
  (crc.fold(xs, 4294967295) .^. 4294967295 : U32)
