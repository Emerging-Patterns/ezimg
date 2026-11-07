# A sequential frame may code its components over several scans (T.81 E.2,
# B.2.3): a scan holds one component (non-interleaved, A.2.2) or several, in
# the frame's order (interleaved, A.2.3), and tables, a restart interval,
# comments and application data may come between scans (B.2.4), a table
# defined there serving the scans after it. `decode_jpeg` reads such a file
# scan by scan. A segment marker after a scan's entropy-coded data ends that
# scan, the walk keeping the bytes after the marker (jpeg_scan_ends_at_segment).
# Those bytes are walked on from that marker with the frame, tables and restart
# interval the scan was read with, and the picture is the passes decode of the
# scans in file order, each with the tables and restart interval it was read
# with (jpeg_scans_in_turn, for two scans). The passes decode is none or a
# picture of the frame's width and height, whatever the scans
# (jpeg_passes_sized). Which scans it takes (every frame component in exactly
# one scan, the components of a scan in the frame's order) and where it places
# each scan's blocks are said on the code (src/jpeg.bend, decode.passes.ok and
# decode.plan); the sample values are trusted as they are for one scan.
# Progressive frames stay refused (laws/JpegRefusesNonBaselineFrames.bend).
import Base
import ../main.bend as Img
import ../src/jpeg.bend as Jpeg
import ./JpegRefusesNonBaselineFrames.bend as LR
import ./JpegRoundTripKeepsSize.bend as LT

# LAW: after a frame header, a segment marker (DHT, DQT, SOS, DRI, COM, APP0 to APP15) after a scan's stuffed
# entropy-coded bytes ends the scan: the walk holds the scan's bytes as it held them at EOI (jpeg_ent_walk), and
# every byte after the marker, for the walk that reads on
law jpeg_scan_ends_at_segment:
  for +xs: List<&2, U32>
  for h_stuffed: {LT.jpg.stuffed(xs, False{}, True{}) == True{} : Bool}
  for +mk: LR.Mk
  for +rest: List<&2, U32>
  for +frame: Jpeg.Frame
  for +scan: Jpeg.Scan
  for +tabs: Jpeg.Tabs
  for +ent: List<&2, U32>
  for +ri: U32
  for +bad: U32
  {Jpeg.decode.walk(List.append(&2, U32, xs, 255 <> (LR.mk.byte(mk) <> rest)), Jpeg.St{Jpeg.Ent{}, frame, scan, tabs,
    ent, ri, 1, bad}) == Jpeg.St{Jpeg.Rest{LR.mk.byte(mk), List.reverse.go(&2, U32, rest, [])}, frame, scan, tabs,
    List.reverse.go(&2, U32, xs, ent), ri, 1, bad} : Jpeg.St}

# LAW: a file from SOI whose walk reads a frame header and a scan, then ends that scan at a marker, and whose bytes
# after the marker, walked from it with that frame, the scan's tables and restart interval, read a second scan and
# EOI with nothing refused, decodes as the passes decode of the two scans in file order, each with the tables and
# restart interval the walk had when it read the scan
law jpeg_scans_in_turn:
  for +bytes: List<&2, U32>
  for h_soi: {Jpeg.decode.facts.soi(Jpeg.decode.facts(bytes)) == True{} : Bool}
  for +mark: U32
  for +acc: List<&2, U32>
  for +frame: Jpeg.Frame
  for +scan: Jpeg.Scan
  for +tabs: Jpeg.Tabs
  for +ent: List<&2, U32>
  for +ri: U32
  for h_walk: {Jpeg.decode.walk(bytes, Jpeg.decode.st0()) == Jpeg.St{Jpeg.Rest{mark, acc}, frame, scan, tabs, ent, ri,
    1, 0} : Jpeg.St}
  for +ns: U32
  for +sids: List<&2, U32>
  for +td: List<&2, U32>
  for +ta: List<&2, U32>
  for +ss: U32
  for +se: U32
  for +ah: U32
  for h_ns: {U32.is_eq(ns, 0) == False{} : Bool}
  for +tabs2: Jpeg.Tabs
  for +ent2: List<&2, U32>
  for +ri2: U32
  for h_next: {Jpeg.decode.walk(List.reverse(&2, U32, acc), Jpeg.decode.mark(mark, frame, Jpeg.decode.scan0(), tabs, [],
    ri, 1, 0)) == Jpeg.St{Jpeg.Stop{}, frame, Jpeg.Scan{ns, sids, td, ta, ss, se, ah}, tabs2, ent2, ri2, 1, 0} :
    Jpeg.St}
  {Img.decode_jpeg(bytes) == Img.decode_jpeg.out(Jpeg.decode.passes(frame, [Jpeg.Pass{scan, tabs, List.reverse(&2, U32,
    ent), ri}, Jpeg.Pass{Jpeg.Scan{ns, sids, td, ta, ss, se, ah}, tabs2, List.reverse(&2, U32, ent2), ri2}],
    Jpeg.decode.rgb.of(Jpeg.decode.facts(bytes), frame))) : Maybe<&2, Img.Raster>}

# LAW: the passes decode, whatever the scans, their tables and bytes and the colour coding, returns no picture or one
# of its frame's width and height
law jpeg_passes_sized:
  for +ww: U32
  for +hh: U32
  for +nf: U32
  for +ids: List<&2, U32>
  for +hs: List<&2, U32>
  for +vs: List<&2, U32>
  for +tq: List<&2, U32>
  for +hmax: U32
  for +vmax: U32
  for +passes: List<&2, Jpeg.Pass>
  for +rgb: Bool
  {LT.jpg.sized(Img.decode_jpeg.out(Jpeg.decode.passes(Jpeg.Frame{ww, hh, nf, ids, hs, vs, tq, hmax, vmax}, passes,
    rgb)), ww, hh) == True{} : Bool}
