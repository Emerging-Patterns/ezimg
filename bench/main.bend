# Pillow vs ezimg bench driver. EZR: "EZR1" + u32le w/h + row-major U32 samples.
# Built as a native ELF via `bend bench/main.bend -o …` (CC=bend-cc or clang -O3).
import ../main.bend as Img

def arg.at(xs: List<String>, n: Nat) -> String:
  match xs n:
    case Nil{} _n:
      ""
    case h <> _t 0n:
      h
    case _h <> t 1n+p:
      arg.at(t, p)

def u32.arg.go(m: Maybe<&2, U32>) -> U32:
  match m:
    case Some{n}:
      n
    case None{}:
      0

def u32.arg(s: String) -> U32:
  u32.arg.go(U32.read(s))

# n copies of x, prepended onto acc
def rep(n: Nat, +x: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      rep(p, x, {x <> acc : List<&2, U32>})

# a solid Raster filled with one packed sample
def solid(+w: U32, +h: U32, +c: U32) -> Img.Raster:
  Img.raster(w, h, rep(U32.to_nat((w * h : U32)), c, []))

def u32.le(+n: U32) -> U32 & U32 & U32 & U32:
  ((n .&. 255 : U32), ((n >> 8n : U32) .&. 255 : U32), ((n >> 16n : U32) .&. 255 : U32),
    ((n >> 24n : U32) .&. 255 : U32))

def push.u32.go(b: U32 & U32 & U32 & U32, acc: List<&2, U32>) -> List<&2, U32>:
  (b0, b1, b2, b3) = b
  {b3 <> {b2 <> {b1 <> {b0 <> acc : List<&2, U32>} : List<&2, U32>} : List<&2, U32>} : List<&2, U32>}

def push.u32(+n: U32, acc: List<&2, U32>) -> List<&2, U32>:
  push.u32.go(u32.le(n), acc)

def emit.px(px: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match px:
    case Nil{}:
      acc
    case h <> t:
      emit.px(t, push.u32(h, acc))

def emit.ezr(+w: U32, +h: U32, px: List<&2, U32>) -> List<&2, U32>:
  +magic = {49 <> {82 <> {90 <> {69 <> [] : List<&2, U32>} : List<&2, U32>} : List<&2, U32>} : List<&2, U32>}
  List.reverse(&2, U32, emit.px(px, push.u32(h, push.u32(w, magic))))

def raster.bytes(+img: Img.Raster) -> List<&2, U32>:
  emit.ezr(Img.width(img), Img.height(img), Img.pixels(img))

def u32.of4(+a: U32, +b: U32, +c: U32, +d: U32) -> U32:
  (a .|. ((b << 8n : U32) .|. ((c << 16n : U32) .|. (d << 24n : U32) : U32) : U32) : U32)

def parse.px(n: Nat, xs: List<&2, U32>, acc: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match n:
    case 0n:
      Some{List.reverse(&2, U32, acc)}
    case 1n+p:
      match xs:
        case a <> b <> c <> d <> rest:
          parse.px(p, rest, {u32.of4(a, b, c, d) <> acc : List<&2, U32>})
        case _other:
          None{}

def parse.ezr.px(+w: U32, +h: U32, m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, Img.Raster>:
  match m:
    case None{}:
      None{}
    case Some{px}:
      Some{Img.raster(w, h, px)}

def parse.ezr(xs: List<&2, U32>) -> Maybe<&2, Img.Raster>:
  match xs:
    case 69 <> 90 <> 82 <> 49 <> a <> b <> c <> d <> e <> f <> g <> h <> rest:
      +w = u32.of4(a, b, c, d)
      +h = u32.of4(e, f, g, h)
      parse.ezr.px(w, h, parse.px(U32.to_nat((w * h : U32)), rest, []))
    case _other:
      None{}

# length of a byte list, accumulated in n
def ulen(xs: List<&2, U32>, +n: U32) -> U32:
  match xs:
    case Nil{}:
      n
    case _h <> t:
      ulen(t, (n + 1 : U32))

# wrapping sum of (pixel + 1), so a failed decode stays 0 and identical pixels do not cancel
def pixsum(px: List<&2, U32>, +a: U32) -> U32:
  match px:
    case Nil{}:
      a
    case h <> t:
      pixsum(t, ((a + h : U32) + 1 : U32))

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

def write.maybe(path: String, m: Maybe<&2, Img.Raster>) -> IO(Unit):
  match m:
    case None{}:
      die.msg("decode failed")
    case Some{img}:
      write.file(path, raster.bytes(img))

def write.png(path: String, m: Maybe<&2, List<&2, U32>>) -> IO(Unit):
  match m:
    case None{}:
      die.msg("encode_png failed")
    case Some{xs}:
      write.file(path, xs)

def load.ezr.go(m: Maybe<&2, Img.Raster>) -> IO(Img.Raster):
  match m:
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

def cmd.png.rt.go(dst: String, m: Maybe<&2, List<&2, U32>>) -> IO(Unit):
  match m:
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

def step.png.enc(+sum: U32, m: Maybe<&2, List<&2, U32>>) -> U32:
  match m:
    case None{}:
      sum
    case Some{xs}:
      (sum + ulen(xs, 0) : U32)

def loop.png.enc(+img: Img.Raster, n: Nat, +sum: U32) -> U32:
  match n:
    case 0n:
      sum
    case 1n+p:
      loop.png.enc(img, p, step.png.enc(sum, Img.encode_png(img)))

def step.raster(+sum: U32, m: Maybe<&2, Img.Raster>) -> U32:
  match m:
    case None{}:
      sum
    case Some{img}:
      (sum + pixsum(Img.pixels(img), 0) : U32)

def loop.png.dec(+xs: List<&2, U32>, n: Nat, +sum: U32) -> U32:
  match n:
    case 0n:
      sum
    case 1n+p:
      loop.png.dec(xs, p, step.raster(sum, Img.decode_png(xs)))

def step.jpeg.enc(+sum: U32, xs: List<&2, U32>) -> U32:
  (sum + ulen(xs, 0) : U32)

def loop.jpeg.enc(+img: Img.Raster, n: Nat, +sum: U32) -> U32:
  match n:
    case 0n:
      sum
    case 1n+p:
      loop.jpeg.enc(img, p, step.jpeg.enc(sum, Img.encode_jpeg(img)))

def loop.jpeg.dec(+xs: List<&2, U32>, n: Nat, +sum: U32) -> U32:
  match n:
    case 0n:
      sum
    case 1n+p:
      loop.jpeg.dec(xs, p, step.raster(sum, Img.decode_jpeg(xs)))

def show.ms(t0: Nat, t1: Nat, +sum: U32, +w: U32, +h: U32, +n: U32) -> String:
  "MS " ++ Nat.show(Nat.sub(t1, t0)) ++ " SUM " ++ U32.show(sum) ++ " W " ++ U32.show(w) ++ " H " ++ U32.show(h) ++ " N " ++ U32.show(n)

def bench.png.enc(+w: U32, +h: U32, +n: U32) -> IO(Unit):
  +img = solid(w, h, 4286611584)
  +k = U32.to_nat(n)
  do IO<Unit>:
    t0 : Nat <- IO.now()
    sum : U32 = loop.png.enc(img, k, 0)
    t1 : Nat <- IO.now()
    IO.print(show.ms(t0, t1, sum, w, h, n))

def bench.jpeg.enc(+w: U32, +h: U32, +n: U32) -> IO(Unit):
  +img = solid(w, h, 8421504)
  +k = U32.to_nat(n)
  do IO<Unit>:
    t0 : Nat <- IO.now()
    sum : U32 = loop.jpeg.enc(img, k, 0)
    t1 : Nat <- IO.now()
    IO.print(show.ms(t0, t1, sum, w, h, n))

# encode bench from an EZR file (gradient / noise / mixed fixtures)
def bench.png.enc.file.go(m: Maybe<&2, Img.Raster>, +n: U32) -> IO(Unit):
  match m:
    case None{}:
      die.msg("bad ezr for bench-png-enc-file")
    case Some{+img}:
      +k = U32.to_nat(n)
      +w = Img.width(img)
      +h = Img.height(img)
      do IO<Unit>:
        t0 : Nat <- IO.now()
        sum : U32 = loop.png.enc(img, k, 0)
        t1 : Nat <- IO.now()
        IO.print(show.ms(t0, t1, sum, w, h, n))

def bench.png.enc.file(path: String, +n: U32) -> IO(Unit):
  do IO<Unit>:
    xs : List<&2, U32> <- read.file(path)
    bench.png.enc.file.go(parse.ezr(xs), n)

def bench.jpeg.enc.file.go(m: Maybe<&2, Img.Raster>, +n: U32) -> IO(Unit):
  match m:
    case None{}:
      die.msg("bad ezr for bench-jpeg-enc-file")
    case Some{+img}:
      +k = U32.to_nat(n)
      +w = Img.width(img)
      +h = Img.height(img)
      do IO<Unit>:
        t0 : Nat <- IO.now()
        sum : U32 = loop.jpeg.enc(img, k, 0)
        t1 : Nat <- IO.now()
        IO.print(show.ms(t0, t1, sum, w, h, n))

def bench.jpeg.enc.file(path: String, +n: U32) -> IO(Unit):
  do IO<Unit>:
    xs : List<&2, U32> <- read.file(path)
    bench.jpeg.enc.file.go(parse.ezr(xs), n)

def bench.png.dec(path: String, +n: U32) -> IO(Unit):
  +k = U32.to_nat(n)
  do IO<Unit>:
    xs : List<&2, U32> <- read.file(path)
    t0 : Nat <- IO.now()
    sum : U32 = loop.png.dec(xs, k, 0)
    t1 : Nat <- IO.now()
    IO.print(show.ms(t0, t1, sum, 0, 0, n))

def bench.jpeg.dec(path: String, +n: U32) -> IO(Unit):
  +k = U32.to_nat(n)
  do IO<Unit>:
    xs : List<&2, U32> <- read.file(path)
    t0 : Nat <- IO.now()
    sum : U32 = loop.jpeg.dec(xs, k, 0)
    t1 : Nat <- IO.now()
    IO.print(show.ms(t0, t1, sum, 0, 0, n))

def run.m.at(z: Bool, +cmd: String, _a: String, _b: String, _c: String) -> IO(Unit):
  match z:
    case True{}:
      IO.print("pong")
    case False{}:
      die.msg("unknown command " ++ cmd)

def run.m(+cmd: String, +a: String, +b: String, +c: String) -> IO(Unit):
  run.m.at(String.eq(cmd, "ping"), cmd, a, b, c)

def run.l.at(z: Bool, +cmd: String, +a: String, +b: String, +c: String) -> IO(Unit):
  match z:
    case True{}:
      bench.jpeg.enc.file(a, u32.arg(b))
    case False{}:
      run.m(cmd, a, b, c)

def run.l(+cmd: String, +a: String, +b: String, +c: String) -> IO(Unit):
  run.l.at(String.eq(cmd, "bench-jpeg-enc-file"), cmd, a, b, c)

def run.k.at(z: Bool, +cmd: String, +a: String, +b: String, +c: String) -> IO(Unit):
  match z:
    case True{}:
      bench.png.enc.file(a, u32.arg(b))
    case False{}:
      run.l(cmd, a, b, c)

def run.k(+cmd: String, +a: String, +b: String, +c: String) -> IO(Unit):
  run.k.at(String.eq(cmd, "bench-png-enc-file"), cmd, a, b, c)

def run.j.at(z: Bool, +cmd: String, +a: String, +b: String, +c: String) -> IO(Unit):
  match z:
    case True{}:
      bench.jpeg.dec(a, u32.arg(b))
    case False{}:
      run.k(cmd, a, b, c)

def run.j(+cmd: String, +a: String, +b: String, +c: String) -> IO(Unit):
  run.j.at(String.eq(cmd, "bench-jpeg-dec"), cmd, a, b, c)

def run.i.at(z: Bool, +cmd: String, +a: String, +b: String, +c: String) -> IO(Unit):
  match z:
    case True{}:
      bench.png.dec(a, u32.arg(b))
    case False{}:
      run.j(cmd, a, b, c)

def run.i(+cmd: String, +a: String, +b: String, +c: String) -> IO(Unit):
  run.i.at(String.eq(cmd, "bench-png-dec"), cmd, a, b, c)

def run.h.at(z: Bool, +cmd: String, +a: String, +b: String, +c: String) -> IO(Unit):
  match z:
    case True{}:
      bench.jpeg.enc(u32.arg(a), u32.arg(b), u32.arg(c))
    case False{}:
      run.i(cmd, a, b, c)

def run.h(+cmd: String, +a: String, +b: String, +c: String) -> IO(Unit):
  run.h.at(String.eq(cmd, "bench-jpeg-enc"), cmd, a, b, c)

def run.g.at(z: Bool, +cmd: String, +a: String, +b: String, +c: String) -> IO(Unit):
  match z:
    case True{}:
      bench.png.enc(u32.arg(a), u32.arg(b), u32.arg(c))
    case False{}:
      run.h(cmd, a, b, c)

def run.g(+cmd: String, +a: String, +b: String, +c: String) -> IO(Unit):
  run.g.at(String.eq(cmd, "bench-png-enc"), cmd, a, b, c)

def run.f.at(z: Bool, +cmd: String, +a: String, +b: String, +c: String) -> IO(Unit):
  match z:
    case True{}:
      cmd.jpeg.rt(a, b)
    case False{}:
      run.g(cmd, a, b, c)

def run.f(+cmd: String, +a: String, +b: String, +c: String) -> IO(Unit):
  run.f.at(String.eq(cmd, "jpeg-rt"), cmd, a, b, c)

def run.e.at(z: Bool, +cmd: String, +a: String, +b: String, +c: String) -> IO(Unit):
  match z:
    case True{}:
      cmd.jpeg.enc(a, b)
    case False{}:
      run.f(cmd, a, b, c)

def run.e(+cmd: String, +a: String, +b: String, +c: String) -> IO(Unit):
  run.e.at(String.eq(cmd, "jpeg-enc"), cmd, a, b, c)

def run.d.at(z: Bool, +cmd: String, +a: String, +b: String, +c: String) -> IO(Unit):
  match z:
    case True{}:
      cmd.jpeg.dec(a, b)
    case False{}:
      run.e(cmd, a, b, c)

def run.d(+cmd: String, +a: String, +b: String, +c: String) -> IO(Unit):
  run.d.at(String.eq(cmd, "jpeg-dec"), cmd, a, b, c)

def run.c.at(z: Bool, +cmd: String, +a: String, +b: String, +c: String) -> IO(Unit):
  match z:
    case True{}:
      cmd.png.rt(a, b)
    case False{}:
      run.d(cmd, a, b, c)

def run.c(+cmd: String, +a: String, +b: String, +c: String) -> IO(Unit):
  run.c.at(String.eq(cmd, "png-rt"), cmd, a, b, c)

def run.b.at(z: Bool, +cmd: String, +a: String, +b: String, +c: String) -> IO(Unit):
  match z:
    case True{}:
      cmd.png.enc(a, b)
    case False{}:
      run.c(cmd, a, b, c)

def run.b(+cmd: String, +a: String, +b: String, +c: String) -> IO(Unit):
  run.b.at(String.eq(cmd, "png-enc"), cmd, a, b, c)

def run.named.at(z: Bool, +cmd: String, +a: String, +b: String, +c: String) -> IO(Unit):
  match z:
    case True{}:
      cmd.png.dec(a, b)
    case False{}:
      run.b(cmd, a, b, c)

def run.named(+cmd: String, +a: String, +b: String, +c: String) -> IO(Unit):
  run.named.at(String.eq(cmd, "png-dec"), cmd, a, b, c)

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
