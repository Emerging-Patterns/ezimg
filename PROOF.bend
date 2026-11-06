# The proofs: proofs/<name>.bend proves laws/<name>.bend. The gate:
# `bend PROOF.bend` prints exactly `ALL PROOFS CHECK` as its first line.
import Base
import ./LAWS.bend as Laws
import ./proofs/BlitCopiesCoveredPoints.bend as PBlitCopiesCoveredPoints
import ./proofs/CheckedRasterIsWellFormed.bend as PCheckedRasterIsWellFormed
import ./proofs/CountIsArea.bend as PCountIsArea
import ./proofs/CrcIsIso3309.bend as PCrcIsIso3309
import ./proofs/CropTakesIntersection.bend as PCropTakesIntersection
import ./proofs/DecodedSamplesPackArgb.bend as PDecodedSamplesPackArgb
import ./proofs/FillIsUniform.bend as PFillIsUniform
import ./proofs/GetSetTouchOnePoint.bend as PGetSetTouchOnePoint
import ./proofs/InflateReadsStoredBlocks.bend as PInflateReadsStoredBlocks
import ./proofs/JpegEncodeIgnoresAlpha.bend as PJpegEncodeIgnoresAlpha
import ./proofs/JpegPlacesComponentSamples.bend as PJpegPlacesComponentSamples
import ./proofs/JpegRefusesNonBaselineFrames.bend as PJpegRefusesNonBaselineFrames
import ./proofs/JpegRefusesWhatPngRefuses.bend as PJpegRefusesWhatPngRefuses
import ./proofs/JpegRoundTripKeepsSize.bend as PJpegRoundTripKeepsSize
import ./proofs/JpegWritesJfifLayout.bend as PJpegWritesJfifLayout
import ./proofs/MapAppliesPerSample.bend as PMapAppliesPerSample
import ./proofs/PngAncillaryChunksIgnored.bend as PPngAncillaryChunksIgnored
import ./proofs/PngDecodesWellFormed.bend as PPngDecodesWellFormed
import ./proofs/PngHeaderPicksColourType.bend as PPngHeaderPicksColourType
import ./proofs/PngIgnoresBytesAfterIend.bend as PPngIgnoresBytesAfterIend
import ./proofs/PngRefusesBadRasters.bend as PPngRefusesBadRasters
import ./proofs/PngRefusesUnsupportedHeaders.bend as PPngRefusesUnsupportedHeaders
import ./proofs/PngRoundTrips.bend as PPngRoundTrips
import ./proofs/PngSamplesFollowColourType.bend as PPngSamplesFollowColourType
import ./proofs/SignatureMatchesPngMagic.bend as PSignatureMatchesPngMagic
import ./proofs/UnfilterUndoesFilter.bend as PUnfilterUndoesFilter
