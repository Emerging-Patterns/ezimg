# proof/wp5-png-decode: Bool, list and U32 lemmas for the PNG decode rows
# (IMG-PNG-8, IMG-PNG-9). Each is a law proved here; PROOF.bend imports this
# file, so the gate checks it.
import Base

# the type True names here: Unit for True, Empty for False
def true_ty(bb: Bool) -> Type:
  match bb:
    case True{}:
      Unit
    case False{}:
      Empty

# True is never False
law true_false:
  for ee: {True{} == False{} : Bool}
  Empty

# the proof of true_false
def true_false(ee):
  %ee : true_ty(_)
  Unit{}

# the shape of an IHDR check with six tests: the size, the depth, the colour
# type, and the three methods
def shape(g1: Bool, g2: Bool, g3: Bool, g4: Bool, g5: Bool, g6: Bool) -> Bool:
  Bool.and(g1, Bool.and(Bool.and(g2, g3), Bool.and(g4, Bool.and(g5, g6))))

# a false second test makes the whole check false
law shape_second:
  for g1: Bool
  for g2: Bool
  for -g3: Bool
  for -g4: Bool
  for -g5: Bool
  for -g6: Bool
  for h2: {g2 == False{} : Bool}
  {shape(g1, g2, g3, g4, g5, g6) == False{} : Bool}

# the proof of shape_second
def shape_second(g1, g2, _g3, _g4, _g5, _g6, h2):
  match g1:
    case False{}:
      {==}
    case True{}:
      match g2:
        case False{}:
          {==}
        case True{}:
          Empty.absurd({shape(True{}, True{}, _g3, _g4, _g5, _g6) == False{} : Bool}, true_false(h2))

# a false third test makes the whole check false
law shape_third:
  for g1: Bool
  for g2: Bool
  for g3: Bool
  for -g4: Bool
  for -g5: Bool
  for -g6: Bool
  for h3: {g3 == False{} : Bool}
  {shape(g1, g2, g3, g4, g5, g6) == False{} : Bool}

# the proof of shape_third
def shape_third(g1, g2, g3, _g4, _g5, _g6, h3):
  match g1:
    case False{}:
      {==}
    case True{}:
      match g2:
        case False{}:
          {==}
        case True{}:
          match g3:
            case False{}:
              {==}
            case True{}:
              Empty.absurd({shape(True{}, True{}, True{}, _g4, _g5, _g6) == False{} : Bool}, true_false(h3))

# a false sixth test makes the whole check false
law shape_sixth:
  for g1: Bool
  for g2: Bool
  for g3: Bool
  for g4: Bool
  for g5: Bool
  for g6: Bool
  for h6: {g6 == False{} : Bool}
  {shape(g1, g2, g3, g4, g5, g6) == False{} : Bool}

# the proof of shape_sixth
def shape_sixth(g1, g2, g3, g4, g5, g6, h6):
  match g1:
    case False{}:
      {==}
    case True{}:
      match g2:
        case False{}:
          {==}
        case True{}:
          match g3:
            case False{}:
              {==}
            case True{}:
              match g4:
                case False{}:
                  {==}
                case True{}:
                  match g5:
                    case False{}:
                      {==}
                    case True{}:
                      match g6:
                        case False{}:
                          {==}
                        case True{}:
                          Empty.absurd({shape(True{}, True{}, True{}, True{}, True{}, True{}) == False{} : Bool},
                            true_false(h6))

# or regrouped: a false a | (b | r) is a false (a | b) | r
law or_regroup:
  for e0: Bool
  for -e2: Bool
  for -rr: Bool
  for h_or: {Bool.or(e0, Bool.or(e2, rr)) == False{} : Bool}
  {Bool.or(Bool.or(e0, e2), rr) == False{} : Bool}

# the proof of or_regroup
def or_regroup(e0, _e2, _rr, h_or):
  match e0:
    case False{}:
      h_or
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, true_false(h_or))

# ---- a U32 counted down, as a Nat: from ezjson PROOF.bend ----

# one bit of adc_zero_carry, the rest given
law adc_zero_carry.at:
  for +qq: Nat
  for ab: Bool
  for -at: Word(qq)
  for ih: {Word.adc(qq, at, Word.zero(qq), True{}, True{}) == at : Word(qq)}
  {Word.adc.con(qq, at, Word.zero(qq), True{}, Bool.full_add(ab, True{}, True{})) == WCon{ab, at} : Word.Con<qq>}

# the proof of adc_zero_carry.at
def adc_zero_carry.at(qq, ab, at, ih):
  match ab:
    case True{}:
      Equal.cong(Word(qq), Word.Con<qq>, ww => WCon{True{}, ww},
        Word.adc(qq, at, Word.zero(qq), True{}, True{}), at, ih)
    case False{}:
      Equal.cong(Word(qq), Word.Con<qq>, ww => WCon{False{}, ww},
        Word.adc(qq, at, Word.zero(qq), True{}, True{}), at, ih)

# subtracting zero with the carry in adds nothing: a - 0 - 1 + 1 is a
law adc_zero_carry:
  for +pp: Nat
  for +aw: Word(pp)
  {Word.adc(pp, aw, Word.zero(pp), True{}, True{}) == aw : Word(pp)}

# the proof of adc_zero_carry
def adc_zero_carry(pp, aw):
  match pp:
    case 0n:
      match aw:
        case WNil{}:
          {==}
    case 1n+(+qq):
      match aw:
        case WCon{ab, +at}:
          adc_zero_carry.at(qq, ab, at, adc_zero_carry(qq, at))

# a word whose first bit is clear and that is not zero: the rest is not zero
law fin_ff:
  for cc: Cmp
  for h_nz: {Cmp.is_eq(Word.cmp.fin(False{}, False{}, cc)) == False{} : Bool}
  {Cmp.is_eq(cc) == False{} : Bool}

# the proof of fin_ff
def fin_ff(cc, h_nz):
  match cc:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({Cmp.is_eq(EQ{}) == False{} : Bool}, true_false(h_nz))
    case GT{}:
      {==}

# subtracting zero with no carry in takes one: a - 0 - 1, one less than a
# when a is not zero
law adc_zero_borrow:
  for +pp: Nat
  for +aw: Word(pp)
  for h_nz: {Cmp.is_eq(Word.cmp(pp, aw, Word.zero(pp))) == False{} : Bool}
  {1n+Word.to_nat(pp, Word.adc(pp, aw, Word.zero(pp), True{}, False{})) == Word.to_nat(pp, aw) : Nat}

# the proof of adc_zero_borrow
def adc_zero_borrow(pp, aw, h_nz):
  match pp:
    case 0n:
      match aw:
        case WNil{}:
          Empty.absurd({1n == 0n : Nat}, true_false(h_nz))
    case 1n+(+qq):
      match aw:
        case WCon{True{}, +at}:
          lc = Equal.sym(Word(qq), Word.adc(qq, at, Word.zero(qq), True{}, True{}), at, adc_zero_carry(qq, at))
          %lc : {1n+Nat.double(Word.to_nat(qq, _)) == 1n+Nat.double(Word.to_nat(qq, at)) : Nat}
          {==}
        case WCon{False{}, +at}:
          ih = adc_zero_borrow(qq, at, fin_ff(Word.cmp(qq, at, Word.zero(qq)), h_nz))
          %ih : {2n+Nat.double(Word.to_nat(qq, Word.adc(qq, at, Word.zero(qq), True{}, False{})))
            == Nat.double(_) : Nat}
          {==}

# one less than a nonzero U32, as a Nat
law u32_dec:
  for +uu: U32
  for h_nz: {U32.is_zero(uu) == False{} : Bool}
  {U32.to_nat(uu) == 1n+U32.to_nat(U32.sub(uu, 1)) : Nat}

# the proof of u32_dec
def u32_dec(uu, h_nz):
  match uu:
    case U32{WCon{True{}, +at}}:
      lc = Equal.sym(Word(31n), Word.adc(31n, at, Word.zero(31n), True{}, True{}), at, adc_zero_carry(31n, at))
      %lc : {1n+Nat.double(Word.to_nat(31n, at)) == 1n+Nat.double(Word.to_nat(31n, _)) : Nat}
      {==}
    case U32{WCon{False{}, +at}}:
      ih = adc_zero_borrow(31n, at, fin_ff(Word.cmp(31n, at, Word.zero(31n)), h_nz))
      %ih : {Nat.double(_)
        == 2n+Nat.double(Word.to_nat(31n, Word.adc(31n, at, Word.zero(31n), True{}, False{}))) : Nat}
      {==}
