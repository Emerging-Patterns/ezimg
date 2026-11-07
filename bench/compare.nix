# Pillow compare script text (embedded; not a checked-in .py file).
# Consumed by writeText / writeShellApplication in default.nix.
{ drvBin ? "ezimg-bench" }:
''
import hashlib, io, math, os, random, struct, subprocess, sys, time, traceback
from PIL import Image
from PIL.PngImagePlugin import PngInfo

DRV = os.environ.get("EZIMG_BENCH_DRV", "${drvBin}")
WORK = os.environ.get("EZIMG_BENCH_WORK", os.path.join(os.environ.get("TMPDIR", "/tmp"), "ezimg-bench-work"))
MODE = os.environ.get("EZIMG_BENCH_MODE", "correctness")  # correctness | speed | all
os.makedirs(WORK, exist_ok=True)

GRAY_JPEG = 0xFF808080
GRAY_PNG = 0xFF808080
lines, cases, speed_rows = [], [], []
fails = 0

def log(msg=""):
    print(msg, flush=True)
    lines.append(msg)

def pack_rgba(r, g, b, a):
    return ((a & 255) << 24) | ((r & 255) << 16) | ((g & 255) << 8) | (b & 255)

def pack_rgb(r, g, b):
    return ((r & 255) << 16) | ((g & 255) << 8) | (b & 255)

def write_ezr(path, w, h, pix):
    open(path, "wb").write(b"EZR1" + struct.pack("<II", w, h) + struct.pack("<" + "I" * len(pix), *pix))

def read_ezr(path):
    b = open(path, "rb").read()
    if b[:4] != b"EZR1":
        raise ValueError("not ezr")
    w, h = struct.unpack_from("<II", b, 4)
    return w, h, list(struct.unpack_from("<" + "I" * (w * h), b, 12))

def ez(args, timeout):
    t0 = time.perf_counter()
    try:
        r = subprocess.run([DRV, *args], capture_output=True, timeout=timeout)
        return {"rc": r.returncode, "out": r.stdout.decode("utf-8", "replace"),
                "err": r.stderr.decode("utf-8", "replace"), "wall": time.perf_counter() - t0, "timeout": False}
    except subprocess.TimeoutExpired as e:
        out = e.stdout or b""; err = e.stderr or b""
        if isinstance(out, str): out = out.encode()
        if isinstance(err, str): err = err.encode()
        return {"rc": None, "out": out.decode("utf-8", "replace"), "err": err.decode("utf-8", "replace"),
                "wall": time.perf_counter() - t0, "timeout": True}

def parse_bench(out):
    parts = out.split()
    if len(parts) < 10 or parts[0] != "MS":
        return None
    return {parts[i]: int(parts[i + 1]) for i in range(0, 10, 2)}

def pillow_png(im, **kw):
    buf = io.BytesIO(); im.save(buf, format="PNG", optimize=False, **kw); return buf.getvalue()

def pillow_jpeg(im, **kw):
    buf = io.BytesIO(); im.save(buf, format="JPEG", **kw); return buf.getvalue()

def as_rgb_words(im):
    return [pack_rgb(r, g, b) for r, g, b in im.convert("RGB").getdata()]

def opaque(pix):
    return all((p >> 24) & 255 == 255 for p in pix)

def as_rgba_words(im):
    return [pack_rgba(r, g, b, a) for r, g, b, a in im.convert("RGBA").getdata()]

def channel_metrics(ez_pix, ref_pix, kind="rgb"):
    def chans(p):
        if kind == "gray":
            return [p & 255]
        if kind == "rgba":
            return [(p >> 24) & 255, (p >> 16) & 255, (p >> 8) & 255, p & 255]
        return [(p >> 16) & 255, (p >> 8) & 255, p & 255]
    se = md = n = bad = 0
    for a, b in zip(ez_pix, ref_pix):
        if a != b:
            bad += 1
        for x, y in zip(chans(a), chans(b)):
            d = int(x) - int(y); se += d * d; md = max(md, abs(d)); n += 1
    mse = se / n if n else 0.0
    psnr = math.inf if mse == 0 else 10.0 * math.log10((255.0 * 255.0) / mse)
    return {"exact": bad == 0 and len(ez_pix) == len(ref_pix), "bad": bad, "max_abs": md,
            "rmse": math.sqrt(mse), "psnr": psnr}

def add_case(group, name, status, detail, hard=True):
    global fails
    cases.append({"group": group, "name": name, "status": status, "detail": detail, "hard": hard})
    log(f"[{status}] {group} | {name}")
    log(f"    {detail}")
    if hard and status != "PASS":
        fails += 1

def run_decode(cmd, src, timeout=60):
    dst = src + ".ezr"
    r = ez([cmd, src, dst], timeout)
    if r["timeout"] or r["rc"] != 0 or not os.path.exists(dst):
        return r, None
    try:
        return r, read_ezr(dst)
    except Exception as e:
        r["err"] += "\n" + repr(e)
        return r, None

def correct_png():
    log("\n== PNG correctness ==")
    specs = []
    specs.append(("1x1 RGB red", Image.new("RGB", (1, 1), (255, 0, 0)), [pack_rgba(255, 0, 0, 255)]))
    specs.append(("1x1 RGBA partial", Image.new("RGBA", (1, 1), (255, 128, 64, 200)), [pack_rgba(255, 128, 64, 200)]))
    rgb = Image.new("RGB", (2, 3)); cols = [(1, 2, 3), (4, 5, 6), (7, 8, 9), (10, 11, 12), (13, 14, 15), (250, 251, 252)]
    rgb.putdata(cols)
    specs.append(("2x3 RGB", rgb, [pack_rgba(r, g, b, 255) for r, g, b in cols]))
    rgba = Image.new("RGBA", (2, 2)); acols = [(255, 0, 0, 255), (0, 255, 0, 128), (0, 0, 255, 0), (10, 20, 30, 1)]
    rgba.putdata(acols)
    specs.append(("2x2 RGBA", rgba, [pack_rgba(*c) for c in acols]))
    gray = Image.new("L", (4, 1)); gs = [0, 128, 255, 64]; gray.putdata(gs)
    specs.append(("4x1 L", gray, [pack_rgba(v, v, v, 255) for v in gs]))
    pal = Image.new("P", (2, 2))
    pal.putpalette([255, 0, 0, 0, 255, 0, 0, 0, 255, 255, 255, 0] + [0] * (768 - 12))
    pal.putdata([0, 1, 2, 3])
    specs.append(("2x2 P", pal, [pack_rgba(255, 0, 0, 255), pack_rgba(0, 255, 0, 255),
                                 pack_rgba(0, 0, 255, 255), pack_rgba(255, 255, 0, 255)]))
    for name, im, expected in specs:
        raw = pillow_png(im)
        path = os.path.join(WORK, "pil_" + name.replace(" ", "_") + ".png")
        open(path, "wb").write(raw)
        r, got = run_decode("png-dec", path, 120)
        if got is None:
            add_case("A pillow→ezimg png", name, "FAIL", f"decode rc={r['rc']} err={r['err'][:200]}")
        else:
            w, h, pix = got
            ok = (w, h) == im.size and pix == expected
            add_case("A pillow→ezimg png", name, "PASS" if ok else "FAIL",
                     f"Pillow {im.mode} {len(raw)}B → ezimg {w}x{h}")
        ezr = os.path.join(WORK, "src_" + name.replace(" ", "_") + ".ezr")
        write_ezr(ezr, im.size[0], im.size[1], expected)
        outp = ezr + ".png"
        er = ez(["png-enc", ezr, outp], 120)
        if er["timeout"] or er["rc"] != 0 or not os.path.exists(outp):
            add_case("B ezimg→pillow png", name, "FAIL", f"encode rc={er['rc']}")
        else:
            back = Image.open(outp); back.load()
            ok = as_rgba_words(back) == expected
            add_case("B ezimg→pillow png", name, "PASS" if ok else "FAIL",
                     f"ezimg png {os.path.getsize(outp)}B mode {back.mode}")
        rt = ezr + ".rt.ezr"
        rr = ez(["png-rt", ezr, rt], 120)
        if rr["timeout"] or rr["rc"] != 0 or not os.path.exists(rt):
            add_case("B ezimg png round-trip", name, "FAIL", f"rc={rr['rc']}")
        else:
            w, h, pix = read_ezr(rt)
            ok = (w, h) == im.size and pix == expected
            add_case("B ezimg png round-trip", name, "PASS" if ok else "FAIL", f"{w}x{h}")
    im = Image.new("RGB", (2, 2), (9, 8, 7))
    meta = PngInfo(); meta.add_text("Comment", "ezimg-bench")
    raw = pillow_png(im, pnginfo=meta)
    path = os.path.join(WORK, "pil_text.png"); open(path, "wb").write(raw)
    exp = [pack_rgba(9, 8, 7, 255)] * 4
    r, got = run_decode("png-dec", path, 60)
    ok = got is not None and got[2] == exp
    add_case("A pillow→ezimg png", "2x2 RGB + tEXt", "PASS" if ok else "FAIL", f"{len(raw)}B")

# Real-size PNGs written by Pillow, decoded by ezimg and compared sample for
# sample, each against a time budget. Pillow picks a filter per row, so the
# files hold every filter type, and fixed and dynamic Huffman blocks.
REAL_SIZES = [(320, 260), (800, 400)]
# Each file's budget is a floor plus microseconds per sample, about six
# times what the slowest of them takes today (an 800x400 RGBA file decodes in
# under a second), so a decoder that turns quadratic again, as the old
# distance-walking back-reference copy did, fails here.
REAL_FLOOR_S = 2.0
REAL_SAVES = [("zlib 1", {"compress_level": 1}, 10.0), ("zlib 6", {"compress_level": 6}, 10.0),
              ("zlib 9", {"compress_level": 9}, 10.0), ("optimize", {"optimize": True}, 10.0)]

def real_budget(w, h, rate):
    return REAL_FLOOR_S + rate * w * h / 1e6

def real_photo(w, h, mode, seed):
    # smooth gradients and waves with a little grain, like a photograph
    rng = random.Random(seed)
    buf = bytearray()
    for y in range(h):
        for x in range(w):
            r = 127 + 60 * math.sin(x / 23.0) + 50 * math.cos(y / 31.0) + rng.randrange(-6, 7)
            g = 127 + 70 * math.sin((x + y) / 41.0) + rng.randrange(-6, 7)
            b = 127 + 80 * math.cos((x - y) / 37.0) + rng.randrange(-6, 7)
            buf += bytes(max(0, min(255, int(v))) for v in (r, g, b))
            if mode == "RGBA":
                buf.append(max(0, min(255, int(200 + 55 * math.sin(x * y / 900.0)))))
    return Image.frombytes(mode, (w, h), bytes(buf))

def real_noise(w, h, mode, seed):
    rng = random.Random(seed)
    return Image.frombytes(mode, (w, h), bytes(rng.getrandbits(8) for _ in range(w * h * len(mode))))

def correct_png_real():
    log("\n== PNG correctness, real sizes ==")
    log(f"budget per file: {REAL_FLOOR_S:.0f} s + a rate per sample (wall: process, decode and EZR write)")
    for w, h in REAL_SIZES:
        for kind, make in (("photo", real_photo), ("noise", real_noise)):
            for mode in ("RGB", "RGBA"):
                im = make(w, h, mode, w * 31 + h)
                want = as_rgba_words(im)
                for label, kw, rate in REAL_SAVES:
                    budget = real_budget(w, h, rate)
                    name = f"{w}x{h} {kind} {mode} {label}"
                    buf = io.BytesIO(); im.save(buf, format="PNG", **kw); data = buf.getvalue()
                    path = os.path.join(WORK, "real_" + name.replace(" ", "_") + ".png")
                    open(path, "wb").write(data)
                    r, got = run_decode("png-dec", path, budget * 2 + 30)
                    if got is None:
                        add_case("F pillow→ezimg png real", name, "FAIL",
                                 f"{len(data)}B decode rc={r['rc']} timeout={r['timeout']} wall={r['wall']:.2f}s "
                                 f"err={r['err'][:200]}")
                        continue
                    gw, gh, pix = got
                    bad = sum(1 for a, b in zip(pix, want) if a != b)
                    same = (gw, gh) == (w, h) and len(pix) == len(want) and bad == 0
                    fast = r["wall"] <= budget
                    add_case("F pillow→ezimg png real", name, "PASS" if same and fast else "FAIL",
                             f"{len(data)}B {gw}x{gh} differing={bad} wall={r['wall']:.2f}s budget={budget:.0f}s"
                             + ("" if fast else " OVER BUDGET"))

def correct_jpeg():
    log("\n== JPEG correctness ==")
    for w, h in [(1, 1), (2, 2), (8, 8), (7, 5)]:
        name = f"ezimg gray128 {w}x{h}"
        pix = [GRAY_JPEG] * (w * h)
        ezr = os.path.join(WORK, f"gray_{w}x{h}.ezr"); write_ezr(ezr, w, h, pix)
        jpg = ezr + ".jpg"
        er = ez(["jpeg-enc", ezr, jpg], 60)
        if er["timeout"] or er["rc"] != 0 or not os.path.exists(jpg):
            add_case("C ezimg jpeg gray128", name, "FAIL", f"encode rc={er['rc']}")
            continue
        im = Image.open(jpg); im.load()
        ok_p = as_rgb_words(im) == [p & 0xFFFFFF for p in pix] and im.size == (w, h)
        add_case("C ezimg jpeg → Pillow", name, "PASS" if ok_p else "FAIL",
                 f"Pillow {im.size} {os.path.getsize(jpg)}B")
        r, got = run_decode("jpeg-dec", jpg, 60)
        if got is None:
            add_case("C ezimg jpeg round-trip", name, "FAIL", f"decode rc={r['rc']}")
        else:
            gw, gh, gpix = got
            ok = (gw, gh) == (w, h) and gpix == pix
            add_case("C ezimg jpeg round-trip", name, "PASS" if ok else "FAIL", f"{gw}x{gh}")

    solids = [
        ("Pillow L 8x8 gray128 q95", Image.new("L", (8, 8), 128), pillow_jpeg(Image.new("L", (8, 8), 128), quality=95), "gray"),
        ("Pillow RGB 8x8 gray128 q95 4:4:4", Image.new("RGB", (8, 8), (128, 128, 128)),
         pillow_jpeg(Image.new("RGB", (8, 8), (128, 128, 128)), quality=95, subsampling=0), "rgb"),
        ("Pillow RGB 8x8 red q95 4:4:4", Image.new("RGB", (8, 8), (220, 40, 40)),
         pillow_jpeg(Image.new("RGB", (8, 8), (220, 40, 40)), quality=95, subsampling=0), "rgb"),
    ]
    for name, im, data, kind in solids:
        path = os.path.join(WORK, name.replace(" ", "_") + ".jpg"); open(path, "wb").write(data)
        pil = Image.open(io.BytesIO(data)); pil.load()
        r, got = run_decode("jpeg-dec", path, 60)
        if got is None:
            add_case("D pillow→ezimg jpeg", name, "FAIL", f"rc={r['rc']}")
            continue
        # Every JPEG sample is packed 0xAARRGGBB with alpha 255, gray included.
        gpix = got[2]
        m = channel_metrics(gpix, as_rgb_words(pil), "rgb")
        ok = (m["exact"] or m["max_abs"] <= 1) and opaque(gpix)
        add_case("D pillow→ezimg jpeg", name, "PASS" if ok else "FAIL",
                 f"max_abs={m['max_abs']} opaque={opaque(gpix)}")

    def pattern(w, h, kind):
        rng = random.Random(1)
        pix = []
        for y in range(h):
            for x in range(w):
                if kind == "grad":
                    r = x * 255 // (w - 1); g = y * 255 // (h - 1); b = (x + y) * 255 // (w + h - 2)
                else:
                    r, g, b = rng.randrange(256), rng.randrange(256), rng.randrange(256)
                # opaque: encode_jpeg flattens a sample onto white by its alpha
                pix.append(pack_rgba(r, g, b, 255))
        im = Image.new("RGB", (w, h))
        im.putdata([((p >> 16) & 255, (p >> 8) & 255, p & 255) for p in pix])
        return pix, im

    for label, kind in (("gradient", "grad"), ("noise", "noise")):
        pix, im = pattern(16, 16, kind)
        data = pillow_jpeg(im, quality=95, subsampling=0)
        path = os.path.join(WORK, f"pil_16x16_{label}.jpg"); open(path, "wb").write(data)
        pil = Image.open(io.BytesIO(data)); pil.load()
        pref = as_rgb_words(pil)
        r, got = run_decode("jpeg-dec", path, 60)
        if got is None:
            add_case("D pillow→ezimg jpeg", f"16x16 {label} q95", "FAIL", f"rc={r['rc']}")
        else:
            m = channel_metrics(got[2], pref, "rgb")
            ok = m["max_abs"] <= 3 and m["psnr"] >= 45.0 and opaque(got[2])
            add_case("D pillow→ezimg jpeg", f"16x16 {label} q95", "PASS" if ok else "FAIL",
                     f"PSNR={m['psnr']:.2f} max_abs={m['max_abs']}")

        ezr = os.path.join(WORK, f"ez_16x16_{label}.ezr"); write_ezr(ezr, 16, 16, pix)
        # encode_jpeg is quality 75 with 4:2:0 chroma, as Pillow's quality=75, subsampling=2; encode_jpeg_with at
        # 4:4:4 (the bench's jpeg-enc-444) is Pillow's subsampling=0. The same Annex K tables at the same scale
        # and the same 2 by 2 chroma averaging, so ezimg's file should be about as close to the original and
        # about as small as Pillow's (libjpeg-turbo's)
        for mode, args, ss in (("4:2:0", ["jpeg-enc"], 2), ("4:4:4", ["jpeg-enc-444"], 0)):
          jpg = ezr + "." + mode.replace(":", "") + ".jpg"
          er = ez(args + [ezr, jpg] + (["75"] if ss == 0 else []), 60)
          if er["timeout"] or er["rc"] != 0:
            add_case("C2 ezimg jpeg lossy", f"16x16 {label} {mode}", "FAIL", f"encode rc={er['rc']}")
            continue
          enc = open(jpg, "rb").read()
          pil2 = Image.open(io.BytesIO(enc)); pil2.load()
          pref2 = as_rgb_words(pil2)
          mp = channel_metrics(pref2, pix, "rgb")
          ref = pillow_jpeg(im, quality=75, subsampling=ss)
          rim = Image.open(io.BytesIO(ref)); rim.load()
          mr = channel_metrics(as_rgb_words(rim), pix, "rgb")
          ok_enc = mp["psnr"] >= mr["psnr"] - 1.0 and len(enc) <= len(ref) * 1.15
          add_case("C2 ezimg jpeg → Pillow vs original", f"16x16 {label} {mode}",
                   "PASS" if ok_enc else "FAIL",
                   f"file {len(enc)}B PSNR={mp['psnr']:.2f} max_abs={mp['max_abs']}"
                   f" (Pillow q75 {mode}: {len(ref)}B PSNR={mr['psnr']:.2f})")
          r2, got2 = run_decode("jpeg-dec", jpg, 60)
          if got2 is None:
              add_case("C2 ezimg decode vs Pillow decode", f"16x16 {label} {mode}", "FAIL", "decode failed")
          else:
              both = channel_metrics(got2[2], pref2, "rgb")
              ok_both = both["max_abs"] <= 3 and both["psnr"] >= 45.0
              add_case("C2 ezimg decode vs Pillow decode", f"16x16 {label} {mode}",
                       "PASS" if ok_both else "FAIL",
                       f"PSNR={both['psnr']:.2f} max_abs={both['max_abs']}")

    # Subsampled chroma: every luma block of an MCU lands in its own place (BC-2).
    # Pillow smooths chroma when it upsamples and ezimg replicates it, as T.81
    # allows, so only luma is compared, on a smooth gradient.
    def luma(p):
        return 0.299 * ((p >> 16) & 255) + 0.587 * ((p >> 8) & 255) + 0.114 * (p & 255)
    for label, ss in (("4:2:2", 1), ("4:2:0", 2)):
        w = h = 16
        im = Image.new("RGB", (w, h))
        im.putdata([(x * 255 // 15, y * 255 // 15, (x + y) * 255 // 30) for y in range(h) for x in range(w)])
        data = pillow_jpeg(im, quality=95, subsampling=ss)
        tag = label.replace(":", "")
        path = os.path.join(WORK, f"pil_16x16_grad_{tag}.jpg"); open(path, "wb").write(data)
        pil = Image.open(io.BytesIO(data)); pil.load()
        r, got = run_decode("jpeg-dec", path, 60)
        if got is None:
            add_case("D pillow→ezimg jpeg", f"16x16 gradient {label}", "FAIL", f"rc={r['rc']}")
            continue
        dl = max(abs(luma(a) - luma(b)) for a, b in zip(got[2], as_rgb_words(pil)))
        ok = got[:2] == (w, h) and dl <= 3.0 and opaque(got[2])
        add_case("D pillow→ezimg jpeg", f"16x16 gradient {label}", "PASS" if ok else "FAIL", f"max luma diff={dl:.2f}")

    # Sequential files of several scans (T.81 E.2). jpegtran -scans recodes a Pillow file with one scan to each
    # component, or Y then Cb and Cr interleaved, or the components out of order, keeping every coefficient: ezimg
    # must decode each exactly as it decodes the one-scan file, and within 1 of Pillow. With -optimize each scan
    # has its own DHT between the scans; -restart 1 puts RSTn markers in each. A progressive recoding stays refused.
    jt = os.environ.get("EZIMG_JPEGTRAN")
    if not jt:
        add_case("D3 jpegtran -scans→ezimg", "jpegtran", "SKIP", "EZIMG_JPEGTRAN unset", hard=False)
    else:
        rng = random.Random(5)
        scripts = (("a scan to each component", "0;\n1;\n2;\n"), ("Y, then Cb and Cr", "0;\n1 2;\n"),
                   ("Cr, Y, Cb", "2;\n0;\n1;\n"), ("gray", "0;\n"))
        k = 0
        for w, h, mode, ss in ((37, 29, "RGB", 2), (40, 24, "RGB", 0), (17, 9, "RGB", 1), (23, 11, "L", 0)):
            im = Image.frombytes(mode, (w, h), bytes(rng.getrandbits(8) for _ in range(w * h * len(mode))))
            src = os.path.join(WORK, f"ms_{w}x{h}_{mode}_{ss}.jpg")
            open(src, "wb").write(pillow_jpeg(im, quality=85, subsampling=ss))
            _r0, one = run_decode("jpeg-dec", src, 60)
            for label, script in scripts:
                if (label == "gray") != (mode == "L"):
                    continue
                sf = src + ".scans"; open(sf, "w").write(script)
                for opt in ([], ["-optimize"], ["-restart", "1"]):
                    k += 1
                    name = f"{w}x{h} {mode} subsampling={ss} {label} {' '.join(opt)}".strip()
                    dst = os.path.join(WORK, f"ms_{k}.jpg")
                    subprocess.run([jt, "-copy", "none", "-scans", sf] + opt + ["-outfile", dst, src], check=True)
                    r, got = run_decode("jpeg-dec", dst, 60)
                    if got is None or one is None:
                        add_case("D3 jpegtran -scans→ezimg", name, "FAIL", f"rc={r['rc']} one-scan ok={one is not None}")
                        continue
                    pil = Image.open(dst); pil.load()
                    m = channel_metrics(got[2], as_rgb_words(pil), "rgb")
                    ok = got == one and m["max_abs"] <= 1 and opaque(got[2])
                    add_case("D3 jpegtran -scans→ezimg", name, "PASS" if ok else "FAIL",
                             f"same as one scan={got == one} Pillow max_abs={m['max_abs']}")
        prog = os.path.join(WORK, "ms_progressive.jpg")
        subprocess.run([jt, "-progressive", "-outfile", prog, os.path.join(WORK, "ms_37x29_RGB_2.jpg")], check=True)
        r, got = run_decode("jpeg-dec", prog, 60)
        add_case("D3 jpegtran -scans→ezimg", "progressive recoding refused", "PASS" if got is None else "FAIL",
                 f"rc={r['rc']}")

    # A JPEG decoded by ezimg and saved as PNG by ezimg keeps its colour and is
    # opaque: one sample format for every decoder and encoder (laws/DecodedSamplesPackArgb.bend).
    for name, im, kw in (("RGB 8x8 red 4:4:4", Image.new("RGB", (8, 8), (220, 40, 40)), {"subsampling": 0}),
                         ("L 8x8 gray128", Image.new("L", (8, 8), 128), {})):
        path = os.path.join(WORK, "x_" + name.replace(" ", "_").replace(":", "") + ".jpg")
        open(path, "wb").write(pillow_jpeg(im, quality=95, **kw))
        r, got = run_decode("jpeg-dec", path, 60)
        png = path + ".png"
        er = ez(["png-enc", path + ".ezr", png], 60) if got is not None else {"rc": None}
        if got is None or er["rc"] != 0 or not os.path.exists(png):
            add_case("E jpeg→ezimg→png", name, "FAIL", f"rc={er['rc']}")
            continue
        back = Image.open(png); back.load()
        want = im.convert("RGB").getpixel((0, 0))
        seen = back.convert("RGBA").getpixel((0, 0))
        ok = back.mode == "RGB" and max(abs(a - b) for a, b in zip(seen[:3], want)) <= 2
        add_case("E jpeg→ezimg→png", name, "PASS" if ok else "FAIL", f"mode {back.mode} pixel {seen} source {want}")

def speed():
    log("\n== Speed (printable; does not fail the check) ==")
    log("ezimg: IO.now around codec only (native ELF). Pillow: time.perf_counter in-process.")
    log("PNG Pillow optimize=False. JPEG Pillow quality=75 subsampling=2 (4:2:0), as encode_jpeg.")
    log("ezimg PNG solid: opaque gray128. ezimg JPEG solid: packed gray128.")
    jobs = [
        ("png-enc", 8, 8, 50, 30),
        ("png-enc", 64, 64, 40, 60),
        ("png-enc", 128, 128, 10, 60),
        ("png-enc", 256, 256, 5, 90),
        ("jpeg-enc", 8, 8, 100, 30),
        ("jpeg-enc", 64, 64, 50, 60),
        ("jpeg-enc", 128, 128, 20, 60),
        ("jpeg-enc", 256, 256, 5, 120),
    ]
    for kind, w, h, n, timeout in jobs:
        if kind == "png-enc":
            r = ez(["bench-png-enc", str(w), str(h), str(n)], timeout)
            im = Image.new("RGB", (w, h), (128, 128, 128))
            t0 = time.perf_counter()
            for _ in range(n):
                buf = io.BytesIO(); im.save(buf, format="PNG", optimize=False)
            pms = (time.perf_counter() - t0) * 1000
        else:
            r = ez(["bench-jpeg-enc", str(w), str(h), str(n)], timeout)
            im = Image.new("RGB", (w, h), (128, 128, 128))
            kw = dict(quality=75, subsampling=2)
            t0 = time.perf_counter()
            for _ in range(n):
                buf = io.BytesIO(); im.save(buf, format="JPEG", **kw)
            pms = (time.perf_counter() - t0) * 1000
        parsed = parse_bench(r["out"]) if not r["timeout"] else None
        if r["timeout"]:
            row = f"TIMEOUT {kind} {w}x{h} N={n} after {r['wall']:.1f}s"
        elif parsed is None:
            row = f"ERROR {kind} {w}x{h} rc={r['rc']} out={r['out']!r} err={r['err'][:120]!r}"
        else:
            ez_ms = parsed["MS"]
            # IO.now is 1ms; when MS==0 report wall/n as upper bound note
            ez_per = (ez_ms / n) if ez_ms > 0 else (r["wall"] * 1000 / n)
            note = "IO.now=0; wall/n" if ez_ms == 0 else "IO.now"
            p_per = pms / n
            ratio = ez_per / p_per if p_per > 0 else float("inf")
            row = (f"{kind:9} {w:4}x{h:<4} N={n:<4} "
                   f"ezimg {ez_per:8.4f} ms/op ({note})  "
                   f"Pillow {p_per:8.4f} ms/op  "
                   f"ratio {ratio:8.1f}x  "
                   f"raw={r['out'].strip()}")
        log(row)
        speed_rows.append(row)

    # one decode pair each
    for kind, make in (("png", "png"), ("jpeg", "jpeg")):
        w = h = 64
        ezr = os.path.join(WORK, f"spd_{kind}.ezr")
        write_ezr(ezr, w, h, [GRAY_PNG if kind == "png" else GRAY_JPEG] * (w * h))
        out = os.path.join(WORK, f"spd_{kind}." + ("png" if kind == "png" else "jpg"))
        er = ez([f"{kind}-enc", ezr, out], 60)
        if er["timeout"] or er["rc"] != 0:
            log(f"{kind}-dec skip: encode failed")
            continue
        n = 10
        r = ez([f"bench-{kind}-dec", out, str(n)], 90)
        data = open(out, "rb").read()
        t0 = time.perf_counter()
        for _ in range(n):
            im = Image.open(io.BytesIO(data)); im.load()
        pms = (time.perf_counter() - t0) * 1000
        parsed = parse_bench(r["out"]) if not r["timeout"] else None
        if parsed:
            ez_per = parsed["MS"] / n if parsed["MS"] else r["wall"] * 1000 / n
            p_per = pms / n
            ratio = ez_per / p_per if p_per > 0 else float("inf")
            log(f"{kind+'-dec':9} {w:4}x{h:<4} N={n:<4} "
                f"ezimg {ez_per:8.4f} ms/op  Pillow {p_per:8.4f} ms/op  ratio {ratio:8.1f}x  "
                f"raw={r['out'].strip()}")
        else:
            log(f"{kind}-dec error/timeout wall={r['wall']:.2f}")

def main():
    log("ezimg vs Pillow bench (Nix-embedded)")
    log(f"driver={DRV}")
    log(f"Pillow via PIL; mode={MODE}")
    ping = ez(["ping"], 10)
    if ping["out"].strip() != "pong":
        log("FAIL: driver ping"); sys.exit(2)
    log("driver ping ok (native ELF)")
    try:
        if MODE in ("correctness", "all"):
            correct_png(); correct_png_real(); correct_jpeg()
        if MODE in ("speed", "all"):
            speed()
    except Exception:
        log("HARNESS EXCEPTION"); log(traceback.format_exc()); sys.exit(2)
    log(f"\n== Summary: {fails} hard failure(s) of {len(cases)} cases ==")
    for c in cases:
        if c["status"] != "PASS" and c["hard"]:
            log(f"  FAIL {c['group']} | {c['name']}")
    if fails:
        sys.exit(1)
    log("ALL HARD CHECKS PASSED")

if __name__ == "__main__":
    main()
''
