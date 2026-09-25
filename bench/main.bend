# Pillow vs ezimg bench driver. EZR: "EZR1" + u32le w/h + row-major U32 samples.
# Built as a native ELF via `bend bench/main.bend -o …` (CC=bend-cc or clang -O3).
import ../main.bend as Img

def arg.at(xs: List<String>, nn: Nat) -> String:
  match xs nn:
    case Nil{} _n:
      ""
    case h <> _t 0n:
      h
    case _h <> t 1n+p:
      arg.at(t, p)

def u32.arg.go(mm: Maybe<&2, U32>) -> U32:
  match mm:
    case Some{n}:
      n
    case None{}:
      0

def u32.arg(ss: String) -> U32:
  u32.arg.go(U32.read(ss))

# n copies of x, prepended onto acc
def rep(nn: Nat, +xx: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match nn:
    case 0n:
      acc
    case 1n+p:
      rep(p, xx, {xx <> acc : List<&2, U32>})

# a solid Raster filled with one packed sample
def solid(+ww: U32, +hh: U32, +cc: U32) -> Img.Raster:
  Img.raster(ww, hh, rep(U32.to_nat((ww * hh : U32)), cc, []))

def u32.le(+nn: U32) -> U32 & U32 & U32 & U32:
  ((nn .&. 255 : U32), ((nn >> 8n : U32) .&. 255 : U32), ((nn >> 16n : U32) .&. 255 : U32),
    ((nn >> 24n : U32) .&. 255 : U32))

def push.u32.go(bb: U32 & U32 & U32 & U32, acc: List<&2, U32>) -> List<&2, U32>:
  (b0, b1, b2, b3) = bb
  {b3 <> {b2 <> {b1 <> {b0 <> acc : List<&2, U32>} : List<&2, U32>} : List<&2, U32>} : List<&2, U32>}

def push.u32(+nn: U32, acc: List<&2, U32>) -> List<&2, U32>:
  push.u32.go(u32.le(nn), acc)

def emit.px(px: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match px:
    case Nil{}:
      acc
    case h <> t:
      emit.px(t, push.u32(h, acc))

def emit.ezr(+ww: U32, +hh: U32, px: List<&2, U32>) -> List<&2, U32>:
  +magic = {49 <> {82 <> {90 <> {69 <> [] : List<&2, U32>} : List<&2, U32>} : List<&2, U32>} : List<&2, U32>}
  List.reverse(&2, U32, emit.px(px, push.u32(hh, push.u32(ww, magic))))

def raster.bytes(+img: Img.Raster) -> List<&2, U32>:
  emit.ezr(Img.width(img), Img.height(img), Img.pixels(img))

def u32.of4(+aa: U32, +bb: U32, +cc: U32, +dd: U32) -> U32:
  (aa .|. ((bb << 8n : U32) .|. ((cc << 16n : U32) .|. (dd << 24n : U32) : U32) : U32) : U32)

def parse.px(nn: Nat, xs: List<&2, U32>, acc: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match nn:
    case 0n:
      Some{List.reverse(&2, U32, acc)}
    case 1n+p:
      match xs:
        case a <> b <> c <> d <> rest:
          parse.px(p, rest, {u32.of4(a, b, c, d) <> acc : List<&2, U32>})
        case _other:
          None{}

def parse.ezr.px(+ww: U32, +hh: U32, mm: Maybe<&2, List<&2, U32>>) -> Maybe<&2, Img.Raster>:
  match mm:
    case None{}:
      None{}
    case Some{px}:
      Some{Img.raster(ww, hh, px)}

def parse.ezr(xs: List<&2, U32>) -> Maybe<&2, Img.Raster>:
  match xs:
    case 69 <> 90 <> 82 <> 49 <> a <> b <> c <> d <> e <> f <> g <> h <> rest:
      +w = u32.of4(a, b, c, d)
      +h = u32.of4(e, f, g, h)
      parse.ezr.px(w, h, parse.px(U32.to_nat((w * h : U32)), rest, []))
    case _other:
      None{}

# length of a byte list, accumulated in n
def ulen(xs: List<&2, U32>, +nn: U32) -> U32:
  match xs:
    case Nil{}:
      nn
    case _h <> t:
      ulen(t, (nn + 1 : U32))

# wrapping sum of (pixel + 1), so a failed decode stays 0 and identical pixels do not cancel
def pixsum(px: List<&2, U32>, +aa: U32) -> U32:
  match px:
    case Nil{}:
      aa
    case h <> t:
      pixsum(t, ((aa + h : U32) + 1 : U32))

# close the file once the write Result is Unit
def wrote.close(file: File, ok: Unit) -> IO(Unit):
  match ok:
    case Unit{}:
      File.close(file)

# force a write Result, then close the file
def wrote(pair: File & Result<&1, &1, U32 & String, Unit>) -> IO(Unit):
  (file, result) = pair
  do IO<Unit>:
    ok : Unit <- IO.pass(Unit, result)
    wrote.close(file, ok)

def write.file(path: String, data: List<&2, U32>) -> IO(Unit):
  do IO<Unit>:
    f : File <- IO.try(File, File.open(path, "w"))
    p : File & Result<&1, &1, U32 & String, Unit> <- File.write_bytes(f, data)
    wrote(p)

# after reading bytes, close the file and return them
def took.after(xs: List<&2, U32>, closed: Unit) -> List<&2, U32>:
  match closed:
    case Unit{}:
      xs

def took.bytes(pair: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(List<&2, U32>):
  (file, result) = pair
  do IO<List<&2, U32>>:
    xs : List<&2, U32> <- IO.pass(List<&2, U32>, result)
    closed : Unit <- File.close(file)
    return took.after(xs, closed)

def read.n(pair: File & Result<&1, &1, U32 & String, U32>) -> IO(List<&2, U32>):
  (file, result) = pair
  do IO<List<&2, U32>>:
    n : U32 <- IO.pass(U32, result)
    p : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(file, n)
    took.bytes(p)

def read.file(path: String) -> IO(List<&2, U32>):
  do IO<List<&2, U32>>:
    f : File <- IO.try(File, File.open(path, "r"))
    p : File & Result<&1, &1, U32 & String, U32> <- File.size(f)
    read.n(p)

def die.msg(msg: String) -> IO(Unit):
  IO.die(Unit, 1, msg)

def write.maybe(path: String, mm: Maybe<&2, Img.Raster>) -> IO(Unit):
  match mm:
    case None{}:
      die.msg("decode failed")
    case Some{img}:
      write.file(path, raster.bytes(img))

def write.png(path: String, mm: Maybe<&2, List<&2, U32>>) -> IO(Unit):
  match mm:
    case None{}:
      die.msg("encode_png failed")
    case Some{xs}:
      write.file(path, xs)

def load.ezr.go(mm: Maybe<&2, Img.Raster>) -> IO(Img.Raster):
  match mm:
    case None{}:
      IO.die(Img.Raster, 1, "bad ezr")
    case Some{img}:
      IO.pure(Img.Raster, img)

def load.ezr(path: String) -> IO(Img.Raster):
  do IO<Img.Raster>:
    xs : List<&2, U32> <- read.file(path)
    load.ezr.go(parse.ezr(xs))

def cmd.png.dec(src: String, dst: String) -> IO(Unit):
  do IO<Unit>:
    xs : List<&2, U32> <- read.file(src)
    write.maybe(dst, Img.decode_png(xs))

def cmd.png.enc(src: String, dst: String) -> IO(Unit):
  do IO<Unit>:
    img : Img.Raster <- load.ezr(src)
    write.png(dst, Img.encode_png(img))

def cmd.png.rt.go(dst: String, mm: Maybe<&2, List<&2, U32>>) -> IO(Unit):
  match mm:
    case None{}:
      die.msg("encode_png failed")
    case Some{xs}:
      write.maybe(dst, Img.decode_png(xs))

def cmd.png.rt(src: String, dst: String) -> IO(Unit):
  do IO<Unit>:
    img : Img.Raster <- load.ezr(src)
    cmd.png.rt.go(dst, Img.encode_png(img))

def cmd.jpeg.dec(src: String, dst: String) -> IO(Unit):
  do IO<Unit>:
    xs : List<&2, U32> <- read.file(src)
    write.maybe(dst, Img.decode_jpeg(xs))

def cmd.jpeg.enc(src: String, dst: String) -> IO(Unit):
  do IO<Unit>:
    img : Img.Raster <- load.ezr(src)
    write.file(dst, Img.encode_jpeg(img))

def cmd.jpeg.rt(src: String, dst: String) -> IO(Unit):
  do IO<Unit>:
    img : Img.Raster <- load.ezr(src)
    write.maybe(dst, Img.decode_jpeg(Img.encode_jpeg(img)))

def step.png.enc(+sum: U32, mm: Maybe<&2, List<&2, U32>>) -> U32:
  match mm:
    case None{}:
      sum
    case Some{xs}:
      (sum + ulen(xs, 0) : U32)

def loop.png.enc(+img: Img.Raster, nn: Nat, +sum: U32) -> U32:
  match nn:
    case 0n:
      sum
    case 1n+p:
      loop.png.enc(img, p, step.png.enc(sum, Img.encode_png(img)))

def step.raster(+sum: U32, mm: Maybe<&2, Img.Raster>) -> U32:
  match mm:
    case None{}:
      sum
    case Some{img}:
      (sum + pixsum(Img.pixels(img), 0) : U32)

def loop.png.dec(+xs: List<&2, U32>, nn: Nat, +sum: U32) -> U32:
  match nn:
    case 0n:
      sum
    case 1n+p:
      loop.png.dec(xs, p, step.raster(sum, Img.decode_png(xs)))

def step.jpeg.enc(+sum: U32, xs: List<&2, U32>) -> U32:
  (sum + ulen(xs, 0) : U32)

def loop.jpeg.enc(+img: Img.Raster, nn: Nat, +sum: U32) -> U32:
  match nn:
    case 0n:
      sum
    case 1n+p:
      loop.jpeg.enc(img, p, step.jpeg.enc(sum, Img.encode_jpeg(img)))

def loop.jpeg.dec(+xs: List<&2, U32>, nn: Nat, +sum: U32) -> U32:
  match nn:
    case 0n:
      sum
    case 1n+p:
      loop.jpeg.dec(xs, p, step.raster(sum, Img.decode_jpeg(xs)))

def show.ms(t0: Nat, t1: Nat, +sum: U32, +ww: U32, +hh: U32, +nn: U32) -> String:
  ("MS " ++ Nat.show(Nat.sub(t1, t0)) ++ " SUM " ++ U32.show(sum) ++ " W " ++ U32.show(ww) ++
    " H " ++ U32.show(hh) ++ " N " ++ U32.show(nn))

def bench.png.enc(+ww: U32, +hh: U32, +nn: U32) -> IO(Unit):
  +img = solid(ww, hh, 4286611584)
  +k = U32.to_nat(nn)
  do IO<Unit>:
    t0 : Nat <- IO.now()
    sum : U32 = loop.png.enc(img, k, 0)
    t1 : Nat <- IO.now()
    IO.print(show.ms(t0, t1, sum, ww, hh, nn))

def bench.jpeg.enc(+ww: U32, +hh: U32, +nn: U32) -> IO(Unit):
  +img = solid(ww, hh, 8421504)
  +k = U32.to_nat(nn)
  do IO<Unit>:
    t0 : Nat <- IO.now()
    sum : U32 = loop.jpeg.enc(img, k, 0)
    t1 : Nat <- IO.now()
    IO.print(show.ms(t0, t1, sum, ww, hh, nn))

# encode bench from an EZR file (gradient / noise / mixed fixtures)
def bench.png.enc.file.go(mm: Maybe<&2, Img.Raster>, +nn: U32) -> IO(Unit):
  match mm:
    case None{}:
      die.msg("bad ezr for bench-png-enc-file")
    case Some{+img}:
      +k = U32.to_nat(nn)
      +w = Img.width(img)
      +h = Img.height(img)
      do IO<Unit>:
        t0 : Nat <- IO.now()
        sum : U32 = loop.png.enc(img, k, 0)
        t1 : Nat <- IO.now()
        IO.print(show.ms(t0, t1, sum, w, h, nn))

def bench.png.enc.file(path: String, +nn: U32) -> IO(Unit):
  do IO<Unit>:
    xs : List<&2, U32> <- read.file(path)
    bench.png.enc.file.go(parse.ezr(xs), nn)

def bench.jpeg.enc.file.go(mm: Maybe<&2, Img.Raster>, +nn: U32) -> IO(Unit):
  match mm:
    case None{}:
      die.msg("bad ezr for bench-jpeg-enc-file")
    case Some{+img}:
      +k = U32.to_nat(nn)
      +w = Img.width(img)
      +h = Img.height(img)
      do IO<Unit>:
        t0 : Nat <- IO.now()
        sum : U32 = loop.jpeg.enc(img, k, 0)
        t1 : Nat <- IO.now()
        IO.print(show.ms(t0, t1, sum, w, h, nn))

def bench.jpeg.enc.file(path: String, +nn: U32) -> IO(Unit):
  do IO<Unit>:
    xs : List<&2, U32> <- read.file(path)
    bench.jpeg.enc.file.go(parse.ezr(xs), nn)

def bench.png.dec(path: String, +nn: U32) -> IO(Unit):
  +k = U32.to_nat(nn)
  do IO<Unit>:
    xs : List<&2, U32> <- read.file(path)
    t0 : Nat <- IO.now()
    sum : U32 = loop.png.dec(xs, k, 0)
    t1 : Nat <- IO.now()
    IO.print(show.ms(t0, t1, sum, 0, 0, nn))

def bench.jpeg.dec(path: String, +nn: U32) -> IO(Unit):
  +k = U32.to_nat(nn)
  do IO<Unit>:
    xs : List<&2, U32> <- read.file(path)
    t0 : Nat <- IO.now()
    sum : U32 = loop.jpeg.dec(xs, k, 0)
    t1 : Nat <- IO.now()
    IO.print(show.ms(t0, t1, sum, 0, 0, nn))

def run.m.at(zz: Bool, +cmd: String, _a: String, _b: String, _c: String) -> IO(Unit):
  match zz:
    case True{}:
      IO.print("pong")
    case False{}:
      die.msg("unknown command " ++ cmd)

def run.m(+cmd: String, +aa: String, +bb: String, +cc: String) -> IO(Unit):
  run.m.at(String.eq(cmd, "ping"), cmd, aa, bb, cc)

def run.l.at(zz: Bool, +cmd: String, +aa: String, +bb: String, +cc: String) -> IO(Unit):
  match zz:
    case True{}:
      bench.jpeg.enc.file(aa, u32.arg(bb))
    case False{}:
      run.m(cmd, aa, bb, cc)

def run.l(+cmd: String, +aa: String, +bb: String, +cc: String) -> IO(Unit):
  run.l.at(String.eq(cmd, "bench-jpeg-enc-file"), cmd, aa, bb, cc)

def run.k.at(zz: Bool, +cmd: String, +aa: String, +bb: String, +cc: String) -> IO(Unit):
  match zz:
    case True{}:
      bench.png.enc.file(aa, u32.arg(bb))
    case False{}:
      run.l(cmd, aa, bb, cc)

def run.k(+cmd: String, +aa: String, +bb: String, +cc: String) -> IO(Unit):
  run.k.at(String.eq(cmd, "bench-png-enc-file"), cmd, aa, bb, cc)

def run.j.at(zz: Bool, +cmd: String, +aa: String, +bb: String, +cc: String) -> IO(Unit):
  match zz:
    case True{}:
      bench.jpeg.dec(aa, u32.arg(bb))
    case False{}:
      run.k(cmd, aa, bb, cc)

def run.j(+cmd: String, +aa: String, +bb: String, +cc: String) -> IO(Unit):
  run.j.at(String.eq(cmd, "bench-jpeg-dec"), cmd, aa, bb, cc)

def run.i.at(zz: Bool, +cmd: String, +aa: String, +bb: String, +cc: String) -> IO(Unit):
  match zz:
    case True{}:
      bench.png.dec(aa, u32.arg(bb))
    case False{}:
      run.j(cmd, aa, bb, cc)

def run.i(+cmd: String, +aa: String, +bb: String, +cc: String) -> IO(Unit):
  run.i.at(String.eq(cmd, "bench-png-dec"), cmd, aa, bb, cc)

def run.h.at(zz: Bool, +cmd: String, +aa: String, +bb: String, +cc: String) -> IO(Unit):
  match zz:
    case True{}:
      bench.jpeg.enc(u32.arg(aa), u32.arg(bb), u32.arg(cc))
    case False{}:
      run.i(cmd, aa, bb, cc)

def run.h(+cmd: String, +aa: String, +bb: String, +cc: String) -> IO(Unit):
  run.h.at(String.eq(cmd, "bench-jpeg-enc"), cmd, aa, bb, cc)

def run.g.at(zz: Bool, +cmd: String, +aa: String, +bb: String, +cc: String) -> IO(Unit):
  match zz:
    case True{}:
      bench.png.enc(u32.arg(aa), u32.arg(bb), u32.arg(cc))
    case False{}:
      run.h(cmd, aa, bb, cc)

def run.g(+cmd: String, +aa: String, +bb: String, +cc: String) -> IO(Unit):
  run.g.at(String.eq(cmd, "bench-png-enc"), cmd, aa, bb, cc)

def run.f.at(zz: Bool, +cmd: String, +aa: String, +bb: String, +cc: String) -> IO(Unit):
  match zz:
    case True{}:
      cmd.jpeg.rt(aa, bb)
    case False{}:
      run.g(cmd, aa, bb, cc)

def run.f(+cmd: String, +aa: String, +bb: String, +cc: String) -> IO(Unit):
  run.f.at(String.eq(cmd, "jpeg-rt"), cmd, aa, bb, cc)

def run.e.at(zz: Bool, +cmd: String, +aa: String, +bb: String, +cc: String) -> IO(Unit):
  match zz:
    case True{}:
      cmd.jpeg.enc(aa, bb)
    case False{}:
      run.f(cmd, aa, bb, cc)

def run.e(+cmd: String, +aa: String, +bb: String, +cc: String) -> IO(Unit):
  run.e.at(String.eq(cmd, "jpeg-enc"), cmd, aa, bb, cc)

def run.d.at(zz: Bool, +cmd: String, +aa: String, +bb: String, +cc: String) -> IO(Unit):
  match zz:
    case True{}:
      cmd.jpeg.dec(aa, bb)
    case False{}:
      run.e(cmd, aa, bb, cc)

def run.d(+cmd: String, +aa: String, +bb: String, +cc: String) -> IO(Unit):
  run.d.at(String.eq(cmd, "jpeg-dec"), cmd, aa, bb, cc)

def run.c.at(zz: Bool, +cmd: String, +aa: String, +bb: String, +cc: String) -> IO(Unit):
  match zz:
    case True{}:
      cmd.png.rt(aa, bb)
    case False{}:
      run.d(cmd, aa, bb, cc)

def run.c(+cmd: String, +aa: String, +bb: String, +cc: String) -> IO(Unit):
  run.c.at(String.eq(cmd, "png-rt"), cmd, aa, bb, cc)

def run.b.at(zz: Bool, +cmd: String, +aa: String, +bb: String, +cc: String) -> IO(Unit):
  match zz:
    case True{}:
      cmd.png.enc(aa, bb)
    case False{}:
      run.c(cmd, aa, bb, cc)

def run.b(+cmd: String, +aa: String, +bb: String, +cc: String) -> IO(Unit):
  run.b.at(String.eq(cmd, "png-enc"), cmd, aa, bb, cc)

def run.named.at(zz: Bool, +cmd: String, +aa: String, +bb: String, +cc: String) -> IO(Unit):
  match zz:
    case True{}:
      cmd.png.dec(aa, bb)
    case False{}:
      run.b(cmd, aa, bb, cc)

def run.named(+cmd: String, +aa: String, +bb: String, +cc: String) -> IO(Unit):
  run.named.at(String.eq(cmd, "png-dec"), cmd, aa, bb, cc)

# the first four argv strings, empty when missing
def args4(xs: List<String>) -> String & String & String & String:
  match xs:
    case a <> b <> c <> d <> _t:
      (a, b, c, d)
    case a <> b <> c <> Nil{}:
      (a, b, c, "")
    case a <> b <> Nil{}:
      (a, b, "", "")
    case a <> Nil{}:
      (a, "", "", "")
    case Nil{}:
      ("", "", "", "")

def main.go(quad: String & String & String & String) -> IO(Unit):
  (a, b, c, d) = quad
  run.named(a, b, c, d)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    main.go(args4(args))
