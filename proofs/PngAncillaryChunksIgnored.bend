# proofs of laws/PngAncillaryChunksIgnored.bend
import Base
import ../main.bend as Img
import ../src/inflate.bend as Inf
import ../src/png.bend as Png
import ../laws/PngAncillaryChunksIgnored.bend as Laws
import ../laws/defs/PngSpecification.bend as D1
import ./lemmas/BasicFacts.bend as M1
import ./lemmas/PngChunkWalker.bend as M2
import ./lemmas/PngImageWalk.bend as M4

# ---- K. ancillary chunks in the chunk walker ----

# a closed run once an IDAT came; none, the run's end with no IDAT before it
def sd.shut(sid: Bool) -> Png.Run:
  match sid:
    case True{}:
      Png.RShut{}
    case False{}:
      Png.RNone{}

# the IDAT run of st with its end named: none before an IDAT, open after
# one, closed once a chunk after the IDAT chunks has closed it
def sd.run(sid: Bool, done: Bool) -> Png.Run:
  match done:
    case False{}:
      M1.st.run(sid)
    case True{}:
      sd.shut(sid)

# st with the IDAT run's end named: done once a chunk after the IDAT
# chunks has closed the run
def sd(
  +ww: U32,
  +hh: U32,
  +cc: U32,
  +plte: Maybe<&2, List<&2, U32>>,
  +trns: Maybe<&2, List<&2, U32>>,
  +idat: List<&2, U32>,
  +sid: Bool,
  +done: Bool
) -> Png.Pg:
  Png.Pg{ww, hh, 8, cc, 0, 0, 0, idat, plte, trns, sd.run(sid, done)}

# a chunk after the IDAT chunks closes the run once one came
def seal.sd(sid: Bool, done: Bool) -> {Png.run.seal(sd.run(sid, done)) == sd.run(sid, Bool.or(sid, done)) : Png.Run}:
  match sid done:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# the walker's dispatch after IHDR on a type that is none of the five it
# reads, with the ancillary bit set: the chunk closes the IDAT run
def anc.at(
  z1: Bool,
  z2: Bool,
  z3: Bool,
  z4: Bool,
  z5: Bool,
  an: Bool,
  +run: Png.Run,
  +st: Bool,
  +sp: Bool,
  +colour: U32,
  +data: List<&2, U32>,
  +pg: Png.Pg,
  +e1: {z1 == False{} : Bool},
  +e2: {z2 == False{} : Bool},
  +e3: {z3 == False{} : Bool},
  +e4: {z4 == False{} : Bool},
  +e5: {z5 == False{} : Bool},
  +ea: {an == True{} : Bool}
) -> {Png.png.apply.go(z1, z2, z3, z4, z5, an, run, st, sp, colour, data, pg) == Png.NMore{Png.png.seal(pg)} : Png.Nx}:
  match z1 z2 z3 z4 z5 an:
    case False{} False{} False{} False{} False{} True{}:
      {==}
    case True{} _z2 _z3 _z4 _z5 _an:
      Empty.absurd({Png.png.apply.go(True{}, _z2, _z3, _z4, _z5, _an, run, st, sp, colour, data, pg) ==
        Png.NMore{Png.png.seal(pg)} : Png.Nx}, M1.false_true(Equal.sym(Bool, True{}, False{}, e1)))
    case False{} True{} _z3 _z4 _z5 _an:
      Empty.absurd({Png.png.apply.go(False{}, True{}, _z3, _z4, _z5, _an, run, st, sp, colour, data, pg) ==
        Png.NMore{Png.png.seal(pg)} : Png.Nx}, M1.false_true(Equal.sym(Bool, True{}, False{}, e2)))
    case False{} False{} True{} _z4 _z5 _an:
      Empty.absurd({Png.png.apply.go(False{}, False{}, True{}, _z4, _z5, _an, run, st, sp, colour, data, pg) ==
        Png.NMore{Png.png.seal(pg)} : Png.Nx}, M1.false_true(Equal.sym(Bool, True{}, False{}, e3)))
    case False{} False{} False{} True{} _z5 _an:
      Empty.absurd({Png.png.apply.go(False{}, False{}, False{}, True{}, _z5, _an, run, st, sp, colour, data, pg) ==
        Png.NMore{Png.png.seal(pg)} : Png.Nx}, M1.false_true(Equal.sym(Bool, True{}, False{}, e4)))
    case False{} False{} False{} False{} True{} _an:
      Empty.absurd({Png.png.apply.go(False{}, False{}, False{}, False{}, True{}, _an, run, st, sp, colour, data, pg) ==
        Png.NMore{Png.png.seal(pg)} : Png.Nx}, M1.false_true(Equal.sym(Bool, True{}, False{}, e5)))
    case False{} False{} False{} False{} False{} False{}:
      Empty.absurd({Png.png.apply.go(False{}, False{}, False{}, False{}, False{}, False{}, run, st, sp, colour, data,
        pg) == Png.NMore{Png.png.seal(pg)} : Png.Nx}, M1.false_true(ea))

# a type with the ancillary bit is not one whose bit is clear, once is_eq's answer is named
def neq.at(
  zz: Bool,
  +tt: U32,
  +kk: U32,
  +ez: {U32.is_eq(tt, kk) == zz : Bool},
  +hb: {Laws.spec.anc.bit(tt) == True{} : Bool},
  +hk: {Laws.spec.anc.bit(kk) == False{} : Bool}
) -> {U32.is_eq(tt, kk) == False{} : Bool}:
  match zz:
    case False{}:
      ez
    case True{}:
      Empty.absurd({U32.is_eq(tt, kk) == False{} : Bool}, M1.false_true(Equal.trans(Bool, False{},
        Laws.spec.anc.bit(kk), True{}, Equal.sym(Bool, Laws.spec.anc.bit(kk), False{}, hk), Equal.trans(Bool,
        Laws.spec.anc.bit(kk), Laws.spec.anc.bit(tt), True{}, Equal.cong(U32, Bool, uu => Laws.spec.anc.bit(uu), kk, tt,
        Equal.sym(U32, tt, kk, M1.ueq(tt, kk, ez))), hb))))

# a type with the ancillary bit is not one whose bit is clear
def neq(
  +tt: U32,
  +kk: U32,
  +hb: {Laws.spec.anc.bit(tt) == True{} : Bool},
  +hk: {Laws.spec.anc.bit(kk) == False{} : Bool}
) -> {U32.is_eq(tt, kk) == False{} : Bool}:
  neq.at(U32.is_eq(tt, kk), tt, kk, {==}, hb, hk)

# an ancillary chunk that is not tRNS: the walker closes the IDAT run and goes on
def anc.step(
  +tt: U32,
  +data: List<&2, U32>,
  +ww: U32,
  +hh: U32,
  +cc: U32,
  +plte: Maybe<&2, List<&2, U32>>,
  +trns: Maybe<&2, List<&2, U32>>,
  +idat: List<&2, U32>,
  +sid: Bool,
  +done: Bool,
  +hb: {Laws.spec.anc.bit(tt) == True{} : Bool},
  +ht: {U32.is_eq(tt, 1951551059) == False{} : Bool}
) -> {Png.png.apply(tt, data, sd(ww, hh, cc, plte, trns, idat, sid, done)) == Png.NMore{sd(ww, hh, cc, plte, trns,
  idat, sid, Bool.or(sid, done))} : Png.Nx}:
  +pg = sd(ww, hh, cc, plte, trns, idat, sid, done)
  Equal.trans(Png.Nx, Png.png.apply(tt, data, pg), Png.NMore{Png.png.seal(pg)},
    Png.NMore{sd(ww, hh, cc, plte, trns, idat, sid, Bool.or(sid, done))},
    anc.at(U32.is_eq(tt, Png.tag.ihdr()), U32.is_eq(tt, Png.tag.idat()), U32.is_eq(tt, Png.tag.iend()), U32.is_eq(tt,
      Png.tag.plte()), U32.is_eq(tt, Png.tag.trns()), Png.tag.anc(tt), sd.run(sid, done), Maybe.is_some(&2, List<&2,
      U32>, trns), Maybe.is_some(&2, List<&2, U32>, plte), cc, data, pg, neq(tt, Png.tag.ihdr(), hb, {==}), neq(tt,
      Png.tag.idat(), hb, {==}), neq(tt, Png.tag.iend(), hb, {==}), neq(tt, Png.tag.plte(), hb, {==}), ht, hb),
    Equal.cong(Png.Run, Png.Nx, rr => Png.NMore{Png.Pg{ww, hh, 8, cc, 0, 0, 0, idat, plte, trns, rr}},
      Png.run.seal(sd.run(sid, done)), sd.run(sid, Bool.or(sid, done)), seal.sd(sid, done)))

# tRNS after an IDAT, the run open or closed: the walker ignores it and the run is closed
def trns.late(
  +data: List<&2, U32>,
  +ww: U32,
  +hh: U32,
  +cc: U32,
  +plte: Maybe<&2, List<&2, U32>>,
  +trns: Maybe<&2, List<&2, U32>>,
  +idat: List<&2, U32>,
  done: Bool
) -> {Png.png.apply(1951551059, data, sd(ww, hh, cc, plte, trns, idat, True{}, done)) == Png.NMore{sd(ww, hh, cc, plte,
  trns, idat, True{}, Bool.or(True{}, done))} : Png.Nx}:
  match done:
    case True{}:
      {==}
    case False{}:
      {==}

# the walker's dispatch on tRNS after an IDAT: the chunk is ignored and closes the IDAT run
def anc.step.trns(
  zt: Bool,
  +tt: U32,
  +data: List<&2, U32>,
  +ww: U32,
  +hh: U32,
  +cc: U32,
  +plte: Maybe<&2, List<&2, U32>>,
  +trns: Maybe<&2, List<&2, U32>>,
  +idat: List<&2, U32>,
  +done: Bool,
  +hb: {Laws.spec.anc.bit(tt) == True{} : Bool},
  +ez: {U32.is_eq(tt, 1951551059) == zt : Bool}
) -> {Png.png.apply(tt, data, sd(ww, hh, cc, plte, trns, idat, True{}, done)) == Png.NMore{sd(ww, hh, cc, plte, trns,
  idat, True{}, Bool.or(True{}, done))} : Png.Nx}:
  match zt:
    case False{}:
      anc.step(tt, data, ww, hh, cc, plte, trns, idat, True{}, done, hb, ez)
    case True{}:
      Equal.trans(Png.Nx, Png.png.apply(tt, data, sd(ww, hh, cc, plte, trns, idat, True{}, done)),
        Png.png.apply(1951551059, data, sd(ww, hh, cc, plte, trns, idat, True{}, done)),
        Png.NMore{sd(ww, hh, cc, plte, trns, idat, True{}, Bool.or(True{}, done))},
        Equal.cong(U32, Png.Nx, uu => Png.png.apply(uu, data, sd(ww, hh, cc, plte, trns, idat, True{}, done)), tt,
          1951551059, M1.ueq(tt, 1951551059, ez)),
        trns.late(data, ww, hh, cc, plte, trns, idat, done))

# an ancillary chunk after the IDAT chunks, tRNS too when an IDAT came: the walker closes the run and goes on
def anc.step.late(
  sid: Bool,
  +tt: U32,
  +data: List<&2, U32>,
  +ww: U32,
  +hh: U32,
  +cc: U32,
  +plte: Maybe<&2, List<&2, U32>>,
  +trns: Maybe<&2, List<&2, U32>>,
  +idat: List<&2, U32>,
  +done: Bool,
  +hb: {Laws.spec.anc.bit(tt) == True{} : Bool},
  ht: Laws.spec.trns.after(sid, tt)
) -> {Png.png.apply(tt, data, sd(ww, hh, cc, plte, trns, idat, sid, done)) == Png.NMore{sd(ww, hh, cc, plte, trns,
  idat, sid, Bool.or(sid, done))} : Png.Nx}:
  match sid:
    case False{}:
      anc.step(tt, data, ww, hh, cc, plte, trns, idat, False{}, done, hb, ht)
    case True{}:
      anc.step.trns(U32.is_eq(tt, 1951551059), tt, data, ww, hh, cc, plte, trns, idat, done, hb, {==})

# ancillary chunks after the IDAT chunks: the walker skips them, closing the IDAT run if one came
def anc.walk.late(
  cs: List<&2, Laws.Anc>,
  +rest: List<&2, U32>,
  +ww: U32,
  +hh: U32,
  +cc: U32,
  +plte: Maybe<&2, List<&2, U32>>,
  +trns: Maybe<&2, List<&2, U32>>,
  +idat: List<&2, U32>,
  +sid: Bool,
  +done: Bool,
  hc: Laws.spec.ancs.after(sid, cs)
) -> {Png.png.go(Laws.spec.ancs(cs, rest), Png.ZLen{}, False{}, 0, 0, [], [], sd(ww, hh, cc, plte, trns, idat, sid,
  done)) == Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], sd(ww, hh, cc, plte, trns, idat, sid, M1.dn(cs, sid,
  done))) : Maybe<&2, Png.Pic>}:
  match cs:
    case Nil{}:
      {==}
    case Laws.Anc{+tt, +data} <> +tl:
      (hb, (ht, (hf, htl))) = hc
      +r1 = Laws.spec.ancs(tl, rest)
      +pg = sd(ww, hh, cc, plte, trns, idat, sid, done)
      +pg2 = sd(ww, hh, cc, plte, trns, idat, sid, Bool.or(sid, done))
      +ea = {Equal.trans(Png.Nx, Png.png.apply(Png.be.u32(M2.bt3(tt), M2.bt2(tt), M2.bt1(tt), M2.bt0(tt)),
        List.reverse(&2, U32, data), pg), Png.png.apply(tt, List.reverse(&2, U32, data), pg), Png.NMore{pg2},
        Equal.cong(U32, Png.Nx, uu => Png.png.apply(uu, List.reverse(&2, U32, data), pg), Png.be.u32(M2.bt3(tt),
        M2.bt2(tt), M2.bt1(tt), M2.bt0(tt)), tt, M2.prt.be.back(tt)), anc.step.late(sid, tt, List.reverse(&2, U32,
        data), ww, hh, cc, plte, trns, idat, done, hb, ht)) : {Png.png.apply(Png.be.u32(M2.bt3(tt), M2.bt2(tt),
        M2.bt1(tt), M2.bt0(tt)), List.reverse(&2, U32, data), pg) == Png.NMore{pg2} : Png.Nx}}
      Equal.trans(Maybe<&2, Png.Pic>, Png.png.go(D1.spec.chunk([M2.bt3(tt), M2.bt2(tt), M2.bt1(tt), M2.bt0(tt)], data,
        r1), Png.ZLen{}, False{}, 0, 0, [], [], pg), Png.png.go(r1, Png.ZLen{}, False{}, 0, 0, [], [], pg2),
        Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], sd(ww, hh, cc, plte, trns, idat, sid, M1.dn(tl, sid,
        Bool.or(sid, done)))),
        M2.chunk.more(M2.bt3(tt), M2.bt2(tt), M2.bt1(tt), M2.bt0(tt), data, r1, pg, pg2, hf, ea),
        anc.walk.late(tl, rest, ww, hh, cc, plte, trns, idat, sid, Bool.or(sid, done), htl))

# chunks fit for after an IDAT fit there with or without one known
def after.or_true(
  bb: Bool,
  +cs: List<&2, Laws.Anc>,
  hh: Laws.spec.ancs.after(True{}, cs)
) -> Laws.spec.ancs.after(Bool.or(bb, True{}), cs):
  match bb:
    case True{}:
      hh
    case False{}:
      hh

# the law's hypothesis, as the walk over the IDAT chunks starts it
def after.or_false(
  bb: Bool,
  +cs: List<&2, Laws.Anc>,
  hh: Laws.spec.ancs.after(bb, cs)
) -> Laws.spec.ancs.after(Bool.or(bb, False{}), cs):
  match bb:
    case True{}:
      hh
    case False{}:
      hh

# before any IDAT, ancillary chunks leave the run open
def dn.ff(cs: List<&2, Laws.Anc>) -> {M1.dn(cs, False{}, False{}) == False{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case _ac <> tl:
      dn.ff(tl)

# ancillary chunks: the walker skips them, closing the IDAT run if one came
def anc.walk(
  cs: List<&2, Laws.Anc>,
  +rest: List<&2, U32>,
  +ww: U32,
  +hh: U32,
  +cc: U32,
  +plte: Maybe<&2, List<&2, U32>>,
  +trns: Maybe<&2, List<&2, U32>>,
  +idat: List<&2, U32>,
  +sid: Bool,
  +done: Bool,
  hc: Laws.spec.ancs.ok(cs)
) -> {Png.png.go(Laws.spec.ancs(cs, rest), Png.ZLen{}, False{}, 0, 0, [], [], sd(ww, hh, cc, plte, trns, idat, sid,
  done)) == Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], sd(ww, hh, cc, plte, trns, idat, sid, M1.dn(cs, sid,
  done))) : Maybe<&2, Png.Pic>}:
  match cs:
    case Nil{}:
      {==}
    case Laws.Anc{+tt, +data} <> +tl:
      (hb, (ht, (hf, htl))) = hc
      +r1 = Laws.spec.ancs(tl, rest)
      +pg = sd(ww, hh, cc, plte, trns, idat, sid, done)
      +pg2 = sd(ww, hh, cc, plte, trns, idat, sid, Bool.or(sid, done))
      +ea = {Equal.trans(Png.Nx, Png.png.apply(Png.be.u32(M2.bt3(tt), M2.bt2(tt), M2.bt1(tt), M2.bt0(tt)),
        List.reverse(&2, U32, data), pg), Png.png.apply(tt, List.reverse(&2, U32, data), pg), Png.NMore{pg2},
        Equal.cong(U32, Png.Nx, uu => Png.png.apply(uu, List.reverse(&2, U32, data), pg), Png.be.u32(M2.bt3(tt),
        M2.bt2(tt), M2.bt1(tt), M2.bt0(tt)), tt, M2.prt.be.back(tt)), anc.step(tt, List.reverse(&2, U32, data), ww, hh,
            cc,
        plte, trns, idat, sid, done, hb, ht)) : {Png.png.apply(Png.be.u32(M2.bt3(tt), M2.bt2(tt), M2.bt1(tt),
        M2.bt0(tt)), List.reverse(&2, U32, data), pg) == Png.NMore{pg2} : Png.Nx}}
      Equal.trans(Maybe<&2, Png.Pic>, Png.png.go(D1.spec.chunk([M2.bt3(tt), M2.bt2(tt), M2.bt1(tt), M2.bt0(tt)], data,
        r1), Png.ZLen{}, False{}, 0, 0, [], [], pg), Png.png.go(r1, Png.ZLen{}, False{}, 0, 0, [], [], pg2),
        Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], sd(ww, hh, cc, plte, trns, idat, sid, M1.dn(tl, sid,
        Bool.or(sid, done)))),
        M2.chunk.more(M2.bt3(tt), M2.bt2(tt), M2.bt1(tt), M2.bt0(tt), data, r1, pg, pg2, hf, ea),
        anc.walk(tl, rest, ww, hh, cc, plte, trns, idat, sid, Bool.or(sid, done), htl))

# before any IDAT: ancillary chunks leave the state as it was
def anc.pre(
  +cs: List<&2, Laws.Anc>,
  +rest: List<&2, U32>,
  +ww: U32,
  +hh: U32,
  +cc: U32,
  +plte: Maybe<&2, List<&2, U32>>,
  +trns: Maybe<&2, List<&2, U32>>,
  hc: Laws.spec.ancs.ok(cs)
) -> {Png.png.go(Laws.spec.ancs(cs, rest), Png.ZLen{}, False{}, 0, 0, [], [], M1.st(ww, hh, cc, plte, trns, [],
  False{})) == Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], M1.st(ww, hh, cc, plte, trns, [],
  False{})) : Maybe<&2, Png.Pic>}:
  Equal.trans(Maybe<&2, Png.Pic>, Png.png.go(Laws.spec.ancs(cs, rest), Png.ZLen{}, False{}, 0, 0, [], [], sd(ww, hh, cc,
    plte, trns, [], False{}, False{})), Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], sd(ww, hh, cc, plte, trns,
      [],
    False{}, M1.dn(cs, False{}, False{}))), Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], sd(ww, hh, cc, plte,
        trns,
    [], False{}, False{})), anc.walk(cs, rest, ww, hh, cc, plte, trns, [], False{}, False{}, hc), Equal.cong(Bool,
    Maybe<&2, Png.Pic>, bb => Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], sd(ww, hh, cc, plte, trns, [],
      False{},
    bb)), M1.dn(cs, False{}, False{}), False{}, dn.ff(cs)))

# the IDAT chunks, ancillary chunks, then IEND: with done the IDAT data read
# so far, the image is the samples of done and the rest of the data, inflated
def pfin.walk.idats(
  ds: List<&2, List<&2, U32>>,
  +ww: U32,
  +hh: U32,
  +cc: U32,
  +plte: Maybe<&2, List<&2, U32>>,
  +trns: Maybe<&2, List<&2, U32>>,
  +a3: List<&2, Laws.Anc>,
  +done: List<&2, U32>,
  +sid: Bool,
  +h_nd: {M1.need(cc, plte) == True{} : Bool},
  hf: D1.spec.fits.all(ds),
  ha: Laws.spec.ancs.after(Bool.or(Bool.not(List.is_empty(&2, List<&2, U32>, ds)), sid), a3)
) -> {Png.png.go(D1.spec.idats(ds, Laws.spec.ancs(a3, D1.spec.chunk([73, 69, 78, 68], [], []))), Png.ZLen{},
  False{}, 0, 0, [], [], M1.st(ww, hh, cc, plte, trns, List.reverse(&2, U32, done), sid)) ==
  Png.png.samples(Inf.inflate.upto(D1.spec.budget(ww, hh, cc), List.append(&2, U32, done, List.concat(&2, U32, ds))),
    ww, hh, cc,
  D1.spec.or.nil(plte), D1.spec.or.nil(trns)) : Maybe<&2, Png.Pic>}:
  match ds:
    case Nil{}:
      +pl = D1.spec.or.nil(plte)
      +tr = D1.spec.or.nil(trns)
      +ie = D1.spec.chunk([73, 69, 78, 68], [], [])
      +pg = sd(ww, hh, cc, plte, trns, List.reverse(&2, U32, done), sid, M1.dn(a3, sid, False{}))
      Equal.trans(Maybe<&2, Png.Pic>, Png.png.go(Laws.spec.ancs(a3, ie), Png.ZLen{}, False{}, 0, 0, [], [], sd(ww, hh,
        cc,
        plte, trns, List.reverse(&2, U32, done), sid, False{})), Png.png.go(ie, Png.ZLen{}, False{}, 0, 0, [], [], pg),
        Png.png.samples(Inf.inflate.upto(D1.spec.budget(ww, hh, cc), List.append(&2, U32, done, [])), ww, hh, cc, pl,
          tr),
        anc.walk.late(a3, ie, ww, hh, cc, plte, trns, List.reverse(&2, U32, done), sid, False{}, ha),
        Equal.trans(Maybe<&2, Png.Pic>, Png.png.go(ie, Png.ZLen{}, False{}, 0, 0, [], [], pg),
          Png.png.finish(pg), Png.png.samples(Inf.inflate.upto(D1.spec.budget(ww, hh, cc),
            List.append(&2, U32, done, [])), ww, hh, cc, pl,
          tr),
          M2.chunk.end(73, 69, 78, 68, [], [], pg, pg, ({==}, {==}), M2.iend.ok.true(M1.need(cc, plte), pg,
            h_nd)),
          Equal.trans(Maybe<&2, Png.Pic>, Png.png.finish(pg),
            Png.png.samples(Inf.inflate.upto(D1.spec.budget(ww, hh, cc), done), ww, hh,
            cc,
            pl, tr), Png.png.samples(Inf.inflate.upto(D1.spec.budget(ww, hh, cc), List.append(&2, U32, done, [])), ww,
              hh, cc, pl, tr),
            M4.fin.done(ww, hh, cc, plte, trns, done, sd.run(sid, M1.dn(a3, sid, False{}))),
            Equal.cong(List<&2, U32>, Maybe<&2, Png.Pic>, xs => Png.png.samples(Inf.inflate.upto(D1.spec.budget(ww,
              hh, cc), xs), ww, hh, cc, pl, tr),
              done, List.append(&2, U32, done, []), Equal.sym(List<&2, U32>, List.append(&2, U32, done, []), done,
              M1.app_nil(done))))))
    case +dd <> +tl:
      (hd, htl) = hf
      +pl = D1.spec.or.nil(plte)
      +tr = D1.spec.or.nil(trns)
      +rest = D1.spec.idats(tl, Laws.spec.ancs(a3, D1.spec.chunk([73, 69, 78, 68], [], [])))
      +pg = M1.st(ww, hh, cc, plte, trns, List.reverse(&2, U32, done), sid)
      +d2 = List.append(&2, U32, done, dd)
      Equal.trans(Maybe<&2, Png.Pic>,
        Png.png.go(D1.spec.chunk([73, 68, 65, 84], dd, rest), Png.ZLen{}, False{}, 0, 0, [], [], pg),
        Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], M1.st(ww, hh, cc, plte, trns, List.append(&2, U32,
          List.reverse(&2, U32, dd), List.reverse(&2, U32, done)), True{})),
        Png.png.samples(Inf.inflate.upto(D1.spec.budget(ww, hh, cc), List.append(&2, U32, done, List.append(&2, U32,
          dd, List.concat(&2, U32, tl)))), ww,
          hh, cc, pl, tr),
        M2.chunk.more(73, 68, 65, 84, dd, rest, pg, M1.st(ww, hh, cc, plte, trns, List.append(&2, U32, List.reverse(&2,
          U32, dd), List.reverse(&2, U32, done)), True{}), hd, M2.idat.step(ww, hh, cc, plte, trns, dd, List.reverse(&2,
          U32, done), sid, h_nd)),
        Equal.trans(Maybe<&2, Png.Pic>,
          Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], M1.st(ww, hh, cc, plte, trns, List.append(&2, U32,
            List.reverse(&2, U32, dd), List.reverse(&2, U32, done)), True{})),
          Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], M1.st(ww, hh, cc, plte, trns, List.reverse(&2, U32, d2),
            True{})),
          Png.png.samples(Inf.inflate.upto(D1.spec.budget(ww, hh, cc), List.append(&2, U32, done, List.append(&2, U32,
            dd, List.concat(&2, U32, tl)))),
            ww, hh, cc, pl, tr),
          Equal.cong(List<&2, U32>, Maybe<&2, Png.Pic>, xs => Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [],
            M1.st(ww, hh, cc, plte, trns, xs, True{})), List.append(&2, U32, List.reverse(&2, U32, dd), List.reverse(&2,
            U32, done)), List.reverse(&2, U32, d2), M2.prt.rev_app(done, dd)),
          Equal.trans(Maybe<&2, Png.Pic>,
            Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], M1.st(ww, hh, cc, plte, trns, List.reverse(&2, U32, d2),
              True{})),
            Png.png.samples(Inf.inflate.upto(D1.spec.budget(ww, hh, cc), List.append(&2, U32, d2, List.concat(&2, U32,
              tl))), ww, hh, cc, pl, tr),
            Png.png.samples(Inf.inflate.upto(D1.spec.budget(ww, hh, cc), List.append(&2, U32, done, List.append(&2,
              U32, dd, List.concat(&2, U32, tl)))),
              ww, hh, cc, pl, tr),
            pfin.walk.idats(tl, ww, hh, cc, plte, trns, a3, d2, True{}, h_nd, htl,
              after.or_true(Bool.not(List.is_empty(&2, List<&2, U32>, tl)), a3, ha)),
            Equal.cong(List<&2, U32>, Maybe<&2, Png.Pic>, xs => Png.png.samples(Inf.inflate.upto(D1.spec.budget(ww,
              hh, cc), xs), ww, hh, cc, pl, tr),
              List.append(&2, U32, d2, List.concat(&2, U32, tl)), List.append(&2, U32, done, List.append(&2, U32, dd,
              List.concat(&2, U32, tl))), M1.app_assoc(done, dd, List.concat(&2, U32, tl))))))

# the PLTE chunk after tRNS: its colour type allows it and its length is a palette's, so the state keeps its data
# beside tRNS's
def plte.late(
  +ww: U32,
  +hh: U32,
  +cc: U32,
  +pp: List<&2, U32>,
  +trns: Maybe<&2, List<&2, U32>>,
  h_pl: {D1.spec.plte.ok(cc, Some{pp}) == True{} : Bool}
) -> {Png.png.apply(Png.be.u32(80, 76, 84, 69), List.reverse(&2, U32, pp), M1.st(ww, hh, cc, None{}, trns, [],
  False{})) == Png.NMore{M1.st(ww, hh, cc, Some{pp}, trns, [], False{})} : Png.Nx}:
  +ok = Bool.or(U32.is_eq(cc, 2), Bool.or(U32.is_eq(cc, 3), U32.is_eq(cc, 6)))
  +rp = List.reverse(&2, U32, pp)
  +e_len = {M1.len_rev(pp) : {List.length(&2, U32, rp) == List.length(&2, U32, pp) : Nat}}
  +e_ok = {Equal.trans(Bool, Bool.and(ok, Png.png.mod3(rp)), Bool.and(ok, D1.spec.pal.len(pp)), True{},
    Equal.cong(Nat, Bool, kk => Bool.and(ok, Bool.and(U32.is_gt(U32.from_nat(kk), 0),
      Bool.and(U32.is_zero((U32.from_nat(kk) % 3 : U32)), U32.is_le(U32.from_nat(kk), 768)))),
      List.length(&2, U32, rp), List.length(&2, U32, pp), e_len), h_pl) :
    {Bool.and(ok, Png.png.mod3(rp)) == True{} : Bool}}
  +pg0 = M1.st(ww, hh, cc, None{}, trns, [], False{})
  Equal.trans(Png.Nx, Png.png.allow(Bool.and(ok, Png.png.mod3(rp)), Png.pg.plte(pg0, List.reverse(&2, U32, rp))),
    Png.NMore{Png.pg.plte(pg0, List.reverse(&2, U32, rp))},
    Png.NMore{M1.st(ww, hh, cc, Some{pp}, trns, [], False{})},
    M2.allow.true(Bool.and(ok, Png.png.mod3(rp)), Png.pg.plte(pg0, List.reverse(&2, U32, rp)), e_ok),
    Equal.cong(List<&2, U32>, Png.Nx, xs => Png.NMore{Png.pg.plte(pg0, xs)}, List.reverse(&2, U32, rp), pp,
      M1.inf.rev_rev(pp)))

# PLTE after tRNS, when there is one
def walk.plte.late(
  +ww: U32,
  +hh: U32,
  +cc: U32,
  +plte: Maybe<&2, List<&2, U32>>,
  +trns: Maybe<&2, List<&2, U32>>,
  +rest: List<&2, U32>,
  h_pl: {D1.spec.plte.ok(cc, plte) == True{} : Bool},
  hf: D1.spec.fits.opt(plte)
) -> {Png.png.go(D1.spec.chunk.opt([80, 76, 84, 69], plte, rest), Png.ZLen{}, False{}, 0, 0, [], [], M1.st(ww, hh,
  cc, None{}, trns, [], False{})) == Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], M1.st(ww, hh, cc, plte, trns,
  [], False{})) : Maybe<&2, Png.Pic>}:
  match plte:
    case None{}:
      {==}
    case Some{+pp}:
      M2.chunk.more(80, 76, 84, 69, pp, rest, M1.st(ww, hh, cc, None{}, trns, [], False{}), M1.st(ww, hh, cc, Some{pp},
        trns, [], False{}), hf, plte.late(ww, hh, cc, pp, trns, h_pl))

# PLTE, a1 and tRNS, in either order: the state after them keeps both
def walk.mid(
  late: Bool,
  +ww: U32,
  +hh: U32,
  +cc: U32,
  +plte: Maybe<&2, List<&2, U32>>,
  +a1: List<&2, Laws.Anc>,
  +trns: Maybe<&2, List<&2, U32>>,
  +rest: List<&2, U32>,
  h_pl: {D1.spec.plte.ok(cc, plte) == True{} : Bool},
  h_tr: {D1.spec.trns.ok(cc, plte, trns) == True{} : Bool},
  h_late: {Bool.or(Bool.not(late), D1.spec.trns.ok(cc, None{}, trns)) == True{} : Bool},
  h_fp: D1.spec.fits.opt(plte),
  h_ft: D1.spec.fits.opt(trns),
  h_a1: Laws.spec.ancs.ok(a1)
) -> {Png.png.go(Laws.spec.mid(late, plte, a1, trns, rest), Png.ZLen{}, False{}, 0, 0, [], [], M1.st(ww, hh, cc,
  None{}, None{}, [], False{})) == Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], M1.st(ww, hh, cc, plte, trns,
  [], False{})) : Maybe<&2, Png.Pic>}:
  match late:
    case False{}:
      +r2 = D1.spec.chunk.opt([116, 82, 78, 83], trns, rest)
      +q1 = Laws.spec.ancs(a1, r2)
      +s1 = M1.st(ww, hh, cc, plte, None{}, [], False{})
      +s2 = M1.st(ww, hh, cc, plte, trns, [], False{})
      Equal.trans(Maybe<&2, Png.Pic>, Png.png.go(D1.spec.chunk.opt([80, 76, 84, 69], plte, q1), Png.ZLen{}, False{},
        0, 0, [], [], M1.st(ww, hh, cc, None{}, None{}, [], False{})), Png.png.go(q1, Png.ZLen{}, False{}, 0, 0, [], [],
        s1), Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], s2),
        M2.walk.plte(ww, hh, cc, plte, q1, h_pl, h_fp),
        Equal.trans(Maybe<&2, Png.Pic>, Png.png.go(q1, Png.ZLen{}, False{}, 0, 0, [], [], s1), Png.png.go(r2,
          Png.ZLen{}, False{}, 0, 0, [], [], s1), Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], s2),
          anc.pre(a1, r2, ww, hh, cc, plte, None{}, h_a1),
          M2.walk.trns(ww, hh, cc, plte, trns, rest, h_tr, h_ft)))
    case True{}:
      +r2 = D1.spec.chunk.opt([80, 76, 84, 69], plte, rest)
      +q1 = Laws.spec.ancs(a1, r2)
      +s1 = M1.st(ww, hh, cc, None{}, trns, [], False{})
      +s2 = M1.st(ww, hh, cc, plte, trns, [], False{})
      Equal.trans(Maybe<&2, Png.Pic>, Png.png.go(D1.spec.chunk.opt([116, 82, 78, 83], trns, q1), Png.ZLen{},
        False{}, 0, 0, [], [], M1.st(ww, hh, cc, None{}, None{}, [], False{})), Png.png.go(q1, Png.ZLen{}, False{}, 0,
        0, [], [], s1), Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], s2),
        M2.walk.trns(ww, hh, cc, None{}, trns, q1, h_late, h_ft),
        Equal.trans(Maybe<&2, Png.Pic>, Png.png.go(q1, Png.ZLen{}, False{}, 0, 0, [], [], s1), Png.png.go(r2,
          Png.ZLen{}, False{}, 0, 0, [], [], s1), Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], s2),
          anc.pre(a1, r2, ww, hh, cc, None{}, trns, h_a1),
          walk.plte.late(ww, hh, cc, plte, trns, rest, h_pl, h_fp)))

# the chunks after the signature, with ancillary chunks after IHDR, between PLTE and tRNS (in either order), after
# them and after the IDAT chunks: the samples of the IDAT data, inflated
def pfin.walk.png(
  +ww: U32,
  +hh: U32,
  +cc: U32,
  +late: Bool,
  +a0: List<&2, Laws.Anc>,
  +plte: Maybe<&2, List<&2, U32>>,
  +a1: List<&2, Laws.Anc>,
  +trns: Maybe<&2, List<&2, U32>>,
  +a2: List<&2, Laws.Anc>,
  +idats: List<&2, List<&2, U32>>,
  +a3: List<&2, Laws.Anc>,
  +h_ww: {D1.spec.side(ww) == True{} : Bool},
  +h_hh: {D1.spec.side(hh) == True{} : Bool},
  +h_cc: {D1.spec.colour.ok(cc) == True{} : Bool},
  +h_pl: {D1.spec.plte.ok(cc, plte) == True{} : Bool},
  +h_tr: {D1.spec.trns.ok(cc, plte, trns) == True{} : Bool},
  +h_late: {Bool.or(Bool.not(late), D1.spec.trns.ok(cc, None{}, trns)) == True{} : Bool},
  h_fp: D1.spec.fits.opt(plte),
  h_ft: D1.spec.fits.opt(trns),
  h_fi: D1.spec.fits.all(idats),
  h_a0: Laws.spec.ancs.ok(a0),
  h_a1: Laws.spec.ancs.ok(a1),
  h_a2: Laws.spec.ancs.ok(a2),
  h_a3: Laws.spec.ancs.after(Bool.not(List.is_empty(&2, List<&2, U32>, idats)), a3)
) -> {Png.decode(D1.spec.chunk([73, 72, 68, 82], D1.spec.ihdr.data(ww, hh, cc), Laws.spec.ancs(a0,
  Laws.spec.mid(late, plte, a1, trns, Laws.spec.ancs(a2, D1.spec.idats(idats, Laws.spec.ancs(a3,
  D1.spec.chunk([73, 69, 78, 68], [], [])))))))) == Png.png.samples(Inf.inflate.upto(D1.spec.budget(ww, hh, cc),
    List.concat(&2, U32, idats)), ww,
  hh, cc, D1.spec.or.nil(plte), D1.spec.or.nil(trns)) : Maybe<&2, Png.Pic>}:
  +r3 = D1.spec.idats(idats, Laws.spec.ancs(a3, D1.spec.chunk([73, 69, 78, 68], [], [])))
  +q2 = Laws.spec.ancs(a2, r3)
  +r1 = Laws.spec.mid(late, plte, a1, trns, q2)
  +q0 = Laws.spec.ancs(a0, r1)
  +s0 = M1.st(ww, hh, cc, None{}, None{}, [], False{})
  +s2 = M1.st(ww, hh, cc, plte, trns, [], False{})
  +out = Png.png.samples(Inf.inflate.upto(D1.spec.budget(ww, hh, cc), List.concat(&2, U32, idats)), ww, hh, cc,
    D1.spec.or.nil(plte),
    D1.spec.or.nil(trns))
  Equal.trans(Maybe<&2, Png.Pic>, Png.png.go(D1.spec.chunk([73, 72, 68, 82], D1.spec.ihdr.data(ww, hh, cc), q0),
    Png.ZLen{}, False{}, 0, 0, [], [], Png.pg.empty()), Png.png.go(q0, Png.ZLen{}, False{}, 0, 0, [], [], s0), out,
    M2.chunk.more(73, 72, 68, 82, D1.spec.ihdr.data(ww, hh, cc), q0, Png.pg.empty(), s0, ({==}, {==}),
      M2.ihdr.step(ww, hh, cc, h_ww, h_hh, h_cc)),
    Equal.trans(Maybe<&2, Png.Pic>, Png.png.go(q0, Png.ZLen{}, False{}, 0, 0, [], [], s0), Png.png.go(r1, Png.ZLen{},
      False{}, 0, 0, [], [], s0), out, anc.pre(a0, r1, ww, hh, cc, None{}, None{}, h_a0),
      Equal.trans(Maybe<&2, Png.Pic>, Png.png.go(r1, Png.ZLen{}, False{}, 0, 0, [], [], s0), Png.png.go(q2, Png.ZLen{},
        False{}, 0, 0, [], [], s2), out, walk.mid(late, ww, hh, cc, plte, a1, trns, q2, h_pl, h_tr, h_late, h_fp, h_ft,
        h_a1),
        Equal.trans(Maybe<&2, Png.Pic>, Png.png.go(q2, Png.ZLen{}, False{}, 0, 0, [], [], s2), Png.png.go(r3,
          Png.ZLen{}, False{}, 0, 0, [], [], s2), out, anc.pre(a2, r3, ww, hh, cc, plte, trns, h_a2),
          pfin.walk.idats(idats, ww, hh, cc, plte, trns, a3, [], False{}, M2.need.ok(cc, plte, h_pl), h_fi,
            after.or_false(Bool.not(List.is_empty(&2, List<&2, U32>, idats)), a3, h_a3))))))

# laws/PngSamplesFollowColourType.bend and laws/DecodedSamplesPackArgb.bend: ancillary chunks where PNG section 5.6
# allows them leave what the walker hands the pixel
# stage
def Laws.png_walk_anc(
  ww,
  hh,
  cc,
  late,
  a0,
  plte,
  a1,
  trns,
  a2,
  idats,
  a3,
  h_ww,
  h_hh,
  h_cc,
  h_pl,
  h_tr,
  h_late,
  h_fp,
  h_ft,
  h_fi,
  h_a0,
  h_a1,
  h_a2,
  h_a3
):
  +mm = Inf.inflate.upto(D1.spec.budget(ww, hh, cc), List.concat(&2, U32, idats))
  +pl = D1.spec.or.nil(plte)
  +tr = D1.spec.or.nil(trns)
  +fl = D1.spec.chunk([73, 72, 68, 82], D1.spec.ihdr.data(ww, hh, cc), Laws.spec.ancs(a0, Laws.spec.mid(late, plte,
    a1, trns, Laws.spec.ancs(a2, D1.spec.idats(idats, Laws.spec.ancs(a3, D1.spec.chunk([73, 69, 78, 68], [],
    [])))))))
  Equal.trans(Maybe<&2, Img.Raster>, Img.decode_png.pic(Png.decode(fl)), Img.decode_png.pic(Png.png.samples(mm, ww, hh,
    cc, pl, tr)), D1.spec.decoded(mm, ww, hh, cc, pl, tr),
    Equal.cong(Maybe<&2, Png.Pic>, Maybe<&2, Img.Raster>, xx => Img.decode_png.pic(xx), Png.decode(fl),
      Png.png.samples(mm, ww, hh, cc, pl, tr), pfin.walk.png(ww, hh, cc, late, a0, plte, a1, trns, a2, idats, a3, h_ww,
      h_hh, h_cc, h_pl, h_tr, h_late, h_fp, h_ft, h_fi, h_a0, h_a1, h_a2, h_a3)),
    M2.frame.decoded(mm, ww, hh, cc, pl, tr))
