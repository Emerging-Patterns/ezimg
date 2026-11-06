# ezimg's laws. Each guarantee is one file under laws/, its prose on top and
# its quantified laws under it, proved by the file of the same name under
# proofs/; LAWS.bend and PROOF.bend only import them. The gate: the first line
# `bend PROOF.bend` prints, on bend 2.0.38, is exactly `ALL PROOFS CHECK`.
# Tests and fixtures, the Pillow comparison in bench/ included, are never
# evidence for a guarantee; what ezimg cannot prove is said where it is
# assumed, on the code.
#
# The public interface is main.bend. There are four families: the raster type
# and its helpers, one sample format, PNG (ISO/IEC 15948 and the W3C PNG
# specification: decode_png, encode_png, parse_signature, and the CRC-32 and
# inflate they rest on) and JPEG (ISO/IEC 10918-1 / ITU-T T.81 baseline
# sequential, and JFIF, ITU-T T.871: decode_jpeg and encode_jpeg). The modules
# under src/ are internal: a law about one holds it in place without making it
# interface.
#
# A raster is well formed when its sample count equals `w * h` computed as a
# natural number (laws/defs/WellFormed.bend). A sample is one `U32`, packed
# `0xAARRGGBB`. The raster guarantees are stated over well-formed rasters.
#
# The reasoning behind each guarantee, its verdict against the code at
# `cbc4358` and the decisions that shaped it are in docs/rfc/ezimg-spec.md;
# every law as it stood then, the findings of the audit and the progress of
# the rollout are in docs/rfc/ezimg-law-inventory.md. They name the
# guarantees by the requirement IDs of docs/SPEC.md, the table these files
# replaced.
import Base
import ./laws/BlitCopiesCoveredPoints.bend as BlitCopiesCoveredPoints
import ./laws/CheckedRasterIsWellFormed.bend as CheckedRasterIsWellFormed
import ./laws/CountIsArea.bend as CountIsArea
import ./laws/CrcIsIso3309.bend as CrcIsIso3309
import ./laws/CropTakesIntersection.bend as CropTakesIntersection
import ./laws/DecodedSamplesPackArgb.bend as DecodedSamplesPackArgb
import ./laws/FillIsUniform.bend as FillIsUniform
import ./laws/GetSetTouchOnePoint.bend as GetSetTouchOnePoint
import ./laws/InflateReadsStoredBlocks.bend as InflateReadsStoredBlocks
import ./laws/InflateUptoKeepsBudget.bend as InflateUptoKeepsBudget
import ./laws/InflateUptoReadsStoredBlocks.bend as InflateUptoReadsStoredBlocks
import ./laws/JpegEncodeFlattensAlpha.bend as JpegEncodeFlattensAlpha
import ./laws/JpegEncodeRefusesBadRasters.bend as JpegEncodeRefusesBadRasters
import ./laws/JpegPlacesComponentSamples.bend as JpegPlacesComponentSamples
import ./laws/JpegReadsScansInTurn.bend as JpegReadsScansInTurn
import ./laws/JpegRefusesNonBaselineFrames.bend as JpegRefusesNonBaselineFrames
import ./laws/JpegRoundTripKeepsSize.bend as JpegRoundTripKeepsSize
import ./laws/JpegWritesJfifLayout.bend as JpegWritesJfifLayout
import ./laws/MapAppliesPerSample.bend as MapAppliesPerSample
import ./laws/PngAdam7PlacesPasses.bend as PngAdam7PlacesPasses
import ./laws/PngAncillaryChunksIgnored.bend as PngAncillaryChunksIgnored
import ./laws/PngDecodesWellFormed.bend as PngDecodesWellFormed
import ./laws/PngHeaderPicksColourType.bend as PngHeaderPicksColourType
import ./laws/PngIgnoresBytesAfterIend.bend as PngIgnoresBytesAfterIend
import ./laws/PngIgnoresFaultyTrns.bend as PngIgnoresFaultyTrns
import ./laws/PngRefusesBadRasters.bend as PngRefusesBadRasters
import ./laws/PngRefusesLongChunks.bend as PngRefusesLongChunks
import ./laws/PngRefusesUnsupportedHeaders.bend as PngRefusesUnsupportedHeaders
import ./laws/PngRoundTrips.bend as PngRoundTrips
import ./laws/PngSamplesFollowBitDepth.bend as PngSamplesFollowBitDepth
import ./laws/PngSamplesFollowColourType.bend as PngSamplesFollowColourType
import ./laws/SignatureMatchesPngMagic.bend as SignatureMatchesPngMagic
import ./laws/UnfilterUndoesFilter.bend as UnfilterUndoesFilter
