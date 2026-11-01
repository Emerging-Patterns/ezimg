# the PNG decoder's walk from IHDR to IEND, and RGB and RGBA packing
import Base
import ../../main.bend as Img
import ../../src/inflate.bend as Inf
import ../../src/png.bend as Png
import ../../laws/PngSamplesFollowColourType.bend as L1
import ../../laws/defs/PngSpecification.bend as D1
import ./BasicFacts.bend as M1
import ./PngChunkWalker.bend as M2

# the IEND chunk, empty: it ends the image
def iend.step(
  +ww: U32,
  +hh: U32,
  +cc: U32,
  +plte: Maybe<&2, List<&2, U32>>,
  +trns: Maybe<&2, List<&2, U32>>,
  +acc: List<&2, U32>,
  +sid: Bool,
  h_nd: {M1.need(cc, plte) == True{} : Bool}
) -> {Png.png.apply(Png.be.u32(73, 69, 78, 68), List.reverse(&2, U32, []), M1.st(ww, hh, cc, plte, trns, acc, sid)) ==
  Png.NEnd{Png.pg.iend(M1.st(ww, hh, cc, plte, trns, acc, sid))} : Png.Nx}:
  M2.iend.ok.true(M1.need(cc, plte), M1.st(ww, hh, cc, plte, trns, acc, sid), h_nd)

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
  +h_nd: {M1.need(cc, plte) == True{} : Bool},
  hf: D1.spec.fits.all(ds)
) -> {Png.png.go(D1.spec.idats(ds, D1.spec.chunk([73, 69, 78, 68], [], [])), Png.ZLen{}, False{}, 0, 0, [], [],
  M1.st(ww, hh, cc, plte, trns, List.reverse(&2, U32, done), sid)) == Png.png.samples(Inf.inflate(List.append(&2, U32,
  done, List.concat(&2, U32, ds))), ww, hh, cc, D1.spec.or.nil(plte), D1.spec.or.nil(trns)) : Maybe<&2, Png.Pic>}:
  match ds:
    case Nil{}:
      +pl = D1.spec.or.nil(plte)
      +tr = D1.spec.or.nil(trns)
      +pg = M1.st(ww, hh, cc, plte, trns, List.reverse(&2, U32, done), sid)
      Equal.trans(Maybe<&2, Png.Pic>,
        Png.png.go(D1.spec.chunk([73, 69, 78, 68], [], []), Png.ZLen{}, False{}, 0, 0, [], [], pg),
        Png.png.finish(Png.pg.iend(pg)),
        Png.png.samples(Inf.inflate(List.append(&2, U32, done, [])), ww, hh, cc, pl, tr),
        M2.chunk.end(73, 69, 78, 68, [], pg, Png.pg.iend(pg), {==}, iend.step(ww, hh, cc, plte, trns,
          List.reverse(&2, U32, done), sid, h_nd)),
        Equal.trans(Maybe<&2, Png.Pic>, Png.png.finish(Png.pg.iend(pg)),
          Png.png.samples(Inf.inflate(done), ww, hh, cc, pl, tr),
          Png.png.samples(Inf.inflate(List.append(&2, U32, done, [])), ww, hh, cc, pl, tr),
          Equal.cong(List<&2, U32>, Maybe<&2, Png.Pic>, xs => Png.png.samples(Inf.inflate(xs), ww, hh, cc, pl, tr),
            List.reverse(&2, U32, List.reverse(&2, U32, done)), done, M1.inf.rev_rev(done)),
          Equal.cong(List<&2, U32>, Maybe<&2, Png.Pic>, xs => Png.png.samples(Inf.inflate(xs), ww, hh, cc, pl, tr),
            done, List.append(&2, U32, done, []), Equal.sym(List<&2, U32>, List.append(&2, U32, done, []), done,
            M1.app_nil(done)))))
    case +dd <> +tl:
      (hd, htl) = hf
      +pl = D1.spec.or.nil(plte)
      +tr = D1.spec.or.nil(trns)
      +rest = D1.spec.idats(tl, D1.spec.chunk([73, 69, 78, 68], [], []))
      +pg = M1.st(ww, hh, cc, plte, trns, List.reverse(&2, U32, done), sid)
      +d2 = List.append(&2, U32, done, dd)
      Equal.trans(Maybe<&2, Png.Pic>,
        Png.png.go(D1.spec.chunk([73, 68, 65, 84], dd, rest), Png.ZLen{}, False{}, 0, 0, [], [], pg),
        Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], M1.st(ww, hh, cc, plte, trns, List.append(&2, U32,
          List.reverse(&2, U32, dd), List.reverse(&2, U32, done)), True{})),
        Png.png.samples(Inf.inflate(List.append(&2, U32, done, List.append(&2, U32, dd, List.concat(&2, U32, tl)))), ww,
          hh, cc, pl, tr),
        M2.chunk.more(73, 68, 65, 84, dd, rest, pg, M1.st(ww, hh, cc, plte, trns, List.append(&2, U32, List.reverse(&2,
            U32,
        dd),
          List.reverse(&2, U32, done)), True{}), hd, M2.idat.step(ww, hh, cc, plte, trns, dd, List.reverse(&2, U32,
              done),
          sid, h_nd)),
        Equal.trans(Maybe<&2, Png.Pic>,
          Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], M1.st(ww, hh, cc, plte, trns, List.append(&2, U32,
            List.reverse(&2, U32, dd), List.reverse(&2, U32, done)), True{})),
          Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], M1.st(ww, hh, cc, plte, trns, List.reverse(&2, U32, d2),
            True{})),
          Png.png.samples(Inf.inflate(List.append(&2, U32, done, List.append(&2, U32, dd, List.concat(&2, U32, tl)))),
            ww, hh, cc, pl, tr),
          Equal.cong(List<&2, U32>, Maybe<&2, Png.Pic>, xs => Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [],
              M1.st(ww,
            hh, cc, plte, trns, xs, True{})), List.append(&2, U32, List.reverse(&2, U32, dd), List.reverse(&2, U32,
            done)), List.reverse(&2, U32, d2), M2.prt.rev_app(done, dd)),
          Equal.trans(Maybe<&2, Png.Pic>,
            Png.png.go(rest, Png.ZLen{}, False{}, 0, 0, [], [], M1.st(ww, hh, cc, plte, trns, List.reverse(&2, U32, d2),
              True{})),
            Png.png.samples(Inf.inflate(List.append(&2, U32, d2, List.concat(&2, U32, tl))), ww, hh, cc, pl, tr),
            Png.png.samples(Inf.inflate(List.append(&2, U32, done, List.append(&2, U32, dd, List.concat(&2, U32, tl)))),
              ww, hh, cc, pl, tr),
            walk.idats(ww, hh, cc, plte, trns, tl, d2, True{}, h_nd, htl),
            Equal.cong(List<&2, U32>, Maybe<&2, Png.Pic>, xs => Png.png.samples(Inf.inflate(xs), ww, hh, cc, pl, tr),
              List.append(&2, U32, d2, List.concat(&2, U32, tl)), List.append(&2, U32, done, List.append(&2, U32, dd,
              List.concat(&2, U32, tl))), M1.app_assoc(done, dd, List.concat(&2, U32, tl))))))

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
  h_cc: {D1.spec.colour.ok(cc) == True{} : Bool},
  +h_pl: {D1.spec.plte.ok(cc, plte) == True{} : Bool},
  h_tr: {D1.spec.trns.ok(cc, plte, trns) == True{} : Bool},
  h_fp: D1.spec.fits.opt(plte),
  h_ft: D1.spec.fits.opt(trns),
  h_fi: D1.spec.fits.all(idats)
) -> {Png.decode(D1.spec.chunk([73, 72, 68, 82], D1.spec.ihdr.data(ww, hh, cc), D1.spec.chunk.opt([80, 76, 84,
  69], plte, D1.spec.chunk.opt([116, 82, 78, 83], trns, D1.spec.idats(idats, D1.spec.chunk([73, 69, 78, 68], [],
  [])))))) == Png.png.samples(Inf.inflate(List.concat(&2, U32, idats)), ww, hh, cc, D1.spec.or.nil(plte),
  D1.spec.or.nil(trns)) : Maybe<&2, Png.Pic>}:
  +r3 = D1.spec.idats(idats, D1.spec.chunk([73, 69, 78, 68], [], []))
  +r2 = D1.spec.chunk.opt([116, 82, 78, 83], trns, r3)
  +r1 = D1.spec.chunk.opt([80, 76, 84, 69], plte, r2)
  +s0 = M1.st(ww, hh, cc, None{}, None{}, [], False{})
  +s1 = M1.st(ww, hh, cc, plte, None{}, [], False{})
  +s2 = M1.st(ww, hh, cc, plte, trns, [], False{})
  Equal.trans(Maybe<&2, Png.Pic>,
    Png.png.go(D1.spec.chunk([73, 72, 68, 82], D1.spec.ihdr.data(ww, hh, cc), r1), Png.ZLen{}, False{}, 0, 0, [],
      [], Png.pg.empty()),
    Png.png.go(r1, Png.ZLen{}, False{}, 0, 0, [], [], s0),
    Png.png.samples(Inf.inflate(List.concat(&2, U32, idats)), ww, hh, cc, D1.spec.or.nil(plte),
      D1.spec.or.nil(trns)),
    M2.chunk.more(73, 72, 68, 82, D1.spec.ihdr.data(ww, hh, cc), r1, Png.pg.empty(), s0, {==}, M2.ihdr.step(ww, hh, cc,
      h_ww, h_hh, h_cc)),
    Equal.trans(Maybe<&2, Png.Pic>, Png.png.go(r1, Png.ZLen{}, False{}, 0, 0, [], [], s0),
      Png.png.go(r2, Png.ZLen{}, False{}, 0, 0, [], [], s1),
      Png.png.samples(Inf.inflate(List.concat(&2, U32, idats)), ww, hh, cc, D1.spec.or.nil(plte),
        D1.spec.or.nil(trns)),
      M2.walk.plte(ww, hh, cc, plte, r2, h_pl, h_fp),
      Equal.trans(Maybe<&2, Png.Pic>, Png.png.go(r2, Png.ZLen{}, False{}, 0, 0, [], [], s1),
        Png.png.go(r3, Png.ZLen{}, False{}, 0, 0, [], [], s2),
        Png.png.samples(Inf.inflate(List.concat(&2, U32, idats)), ww, hh, cc, D1.spec.or.nil(plte),
          D1.spec.or.nil(trns)),
        M2.walk.trns(ww, hh, cc, plte, trns, r3, h_tr, h_ft),
        walk.idats(ww, hh, cc, plte, trns, idats, [], False{}, M2.need.ok(cc, plte, h_pl), h_fi))))

# one sample more on the accumulator is one sample more in front of the list
def onto.cons(
  +hd: U32,
  +acc: List<&2, U32>,
  mm: Maybe<&2, List<&2, U32>>
) -> {M1.onto(hd <> acc, mm) == M1.onto(acc, L1.spec.cons(hd, mm)) : Maybe<&2, List<&2, U32>>}:
  match mm:
    case None{}:
      {==}
    case Some{_ll}:
      {==}

# onto an empty accumulator is the list itself
def onto.nil(mm: Maybe<&2, List<&2, U32>>) -> {M1.onto([], mm) == mm : Maybe<&2, List<&2, U32>>}:
  match mm:
    case None{}:
      {==}
    case Some{_ll}:
      {==}

# px.rgb without a key packs each triple as spec.rgb does
def rgb.acc(
  xs: List<&2, U32>,
  +acc: List<&2, U32>
) -> {Png.px.rgb(xs, Png.KNone{}, acc) == M1.onto(acc, L1.spec.rgb(xs)) : Maybe<&2, List<&2, U32>>}:
  match xs:
    case Nil{}:
      {==}
    case +rr <> t1:
      match t1:
        case Nil{}:
          {==}
        case +gg <> t2:
          match t2:
            case Nil{}:
              {==}
            case +bb <> +tl:
              Equal.trans(Maybe<&2, List<&2, U32>>,
                Png.px.rgb(tl, Png.KNone{}, Png.px.pack(255, rr, gg, bb) <> acc),
                M1.onto(Png.px.pack(255, rr, gg, bb) <> acc, L1.spec.rgb(tl)),
                M1.onto(acc, L1.spec.cons(Png.px.pack(255, rr, gg, bb), L1.spec.rgb(tl))),
                rgb.acc(tl, Png.px.pack(255, rr, gg, bb) <> acc),
                onto.cons(Png.px.pack(255, rr, gg, bb), acc, L1.spec.rgb(tl)))

def L1.png_px_rgb(xs, _plte):
  Equal.trans(Maybe<&2, List<&2, U32>>, Png.px.rgb(xs, Png.KNone{}, []), M1.onto([], L1.spec.rgb(xs)),
    L1.spec.rgb(xs), rgb.acc(xs, []), onto.nil(L1.spec.rgb(xs)))

# px.rgba packs each quadruple as spec.rgba does
def rgba.acc(
  xs: List<&2, U32>,
  +acc: List<&2, U32>
) -> {Png.px.rgba(xs, acc) == M1.onto(acc, L1.spec.rgba(xs)) : Maybe<&2, List<&2, U32>>}:
  match xs:
    case Nil{}:
      {==}
    case +rr <> t1:
      match t1:
        case Nil{}:
          {==}
        case +gg <> t2:
          match t2:
            case Nil{}:
              {==}
            case +bb <> t3:
              match t3:
                case Nil{}:
                  {==}
                case +aa <> +tl:
                  Equal.trans(Maybe<&2, List<&2, U32>>,
                    Png.px.rgba(tl, Png.px.pack(aa, rr, gg, bb) <> acc),
                    M1.onto(Png.px.pack(aa, rr, gg, bb) <> acc, L1.spec.rgba(tl)),
                    M1.onto(acc, L1.spec.cons(Png.px.pack(aa, rr, gg, bb), L1.spec.rgba(tl))),
                    rgba.acc(tl, Png.px.pack(aa, rr, gg, bb) <> acc),
                    onto.cons(Png.px.pack(aa, rr, gg, bb), acc, L1.spec.rgba(tl)))

def L1.png_px_rgba(xs, _plte):
  Equal.trans(Maybe<&2, List<&2, U32>>, Png.px.rgba(xs, []), M1.onto([], L1.spec.rgba(xs)), L1.spec.rgba(xs),
    rgba.acc(xs, []), onto.nil(L1.spec.rgba(xs)))

# laws/PngSamplesFollowColourType.bend: the walker takes each chunk and leaves the pixel stage's inputs
def L1.png_walk(ww, hh, cc, plte, trns, idats, h_ww, h_hh, h_cc, h_pl, h_tr, h_fp, h_ft, h_fi):
  +mm = Inf.inflate(List.concat(&2, U32, idats))
  +pl = D1.spec.or.nil(plte)
  +tr = D1.spec.or.nil(trns)
  Equal.trans(Maybe<&2, Img.Raster>, Img.decode_png.pic(Png.decode(D1.spec.chunk([73, 72, 68, 82],
    D1.spec.ihdr.data(ww, hh, cc), D1.spec.chunk.opt([80, 76, 84, 69], plte, D1.spec.chunk.opt([116, 82, 78, 83],
    trns, D1.spec.idats(idats, D1.spec.chunk([73, 69, 78, 68], [], []))))))),
    Img.decode_png.pic(Png.png.samples(mm, ww, hh, cc, pl, tr)),
    D1.spec.decoded(mm, ww, hh, cc, pl, tr),
    Equal.cong(Maybe<&2, Png.Pic>, Maybe<&2, Img.Raster>, xx => Img.decode_png.pic(xx), Png.decode(D1.spec.chunk([73,
      72, 68, 82], D1.spec.ihdr.data(ww, hh, cc), D1.spec.chunk.opt([80, 76, 84, 69], plte,
      D1.spec.chunk.opt([116, 82, 78, 83], trns, D1.spec.idats(idats, D1.spec.chunk([73, 69, 78, 68], [],
      [])))))), Png.png.samples(mm, ww, hh, cc, pl, tr),
      walk.png(ww, hh, cc, plte, trns, idats, h_ww, h_hh, h_cc, h_pl, h_tr, h_fp, h_ft, h_fi)),
    M2.frame.decoded(mm, ww, hh, cc, pl, tr))
