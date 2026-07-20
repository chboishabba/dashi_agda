module DASHI.Compression.TriadicCodecBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Foundations.SSPTritCarrier
  using (SSPTrit; sspNegOne; sspZero; sspPosOne)

------------------------------------------------------------------------
-- Scope.
--
-- This module records the formal boundary needed by the compression
-- experiments discussed in the sibling runtime repository. It proves the
-- exact support/sign factorisation of a ternary symbol and separates:
--
--   * a ternary source model,
--   * a temporal residual transform,
--   * a context model,
--   * an entropy-coder backend, and
--   * an empirical benchmark receipt.
--
-- In particular, a grayscale temporal-residual benchmark encoded through a
-- zlib-backed `rANS` shim is not classified as evidence for a triadic coder.
------------------------------------------------------------------------

data ActiveSign : Set where
  negativeSign : ActiveSign
  positiveSign : ActiveSign

data TritFactor : Set where
  zeroFactor : TritFactor
  signedFactor : ActiveSign → TritFactor

factorTrit : SSPTrit → TritFactor
factorTrit sspNegOne = signedFactor negativeSign
factorTrit sspZero = zeroFactor
factorTrit sspPosOne = signedFactor positiveSign

unfactorTrit : TritFactor → SSPTrit
unfactorTrit zeroFactor = sspZero
unfactorTrit (signedFactor negativeSign) = sspNegOne
unfactorTrit (signedFactor positiveSign) = sspPosOne

factor-unfactor : ∀ f → factorTrit (unfactorTrit f) ≡ f
factor-unfactor zeroFactor = refl
factor-unfactor (signedFactor negativeSign) = refl
factor-unfactor (signedFactor positiveSign) = refl

unfactor-factor : ∀ t → unfactorTrit (factorTrit t) ≡ t
unfactor-factor sspNegOne = refl
unfactor-factor sspZero = refl
unfactor-factor sspPosOne = refl

support : SSPTrit → Bool
support sspNegOne = true
support sspZero = false
support sspPosOne = true

------------------------------------------------------------------------
-- Pipeline roles.
------------------------------------------------------------------------

data SourceAlphabet : Set where
  grayscaleBytes : SourceAlphabet
  ternaryActions : SourceAlphabet
  ternaryCellDeltas : SourceAlphabet

data TransformKind : Set where
  identityTransform : TransformKind
  temporalByteResidual : TransformKind
  ternaryResidual : TransformKind
  orbitCanonicalResidual : TransformKind

data ContextKind : Set where
  noContext : ContextKind
  previousTritContext : ContextKind
  previousTritAndBadBinContext : ContextKind
  previousTritBadBinRunLengthContext : ContextKind

data EntropyBackend : Set where
  zlibBackend : EntropyBackend
  lzmaBackend : EntropyBackend
  zlibRANSShim : EntropyBackend
  realRangeCoder : EntropyBackend
  realRANS : EntropyBackend

isRealTernaryEntropyBackend : EntropyBackend → Bool
isRealTernaryEntropyBackend zlibBackend = false
isRealTernaryEntropyBackend lzmaBackend = false
isRealTernaryEntropyBackend zlibRANSShim = false
isRealTernaryEntropyBackend realRangeCoder = true
isRealTernaryEntropyBackend realRANS = true

record CodecConfiguration : Set where
  constructor codecConfiguration
  field
    alphabet : SourceAlphabet
    transform : TransformKind
    context : ContextKind
    backend : EntropyBackend
open CodecConfiguration public

data EvidenceClass : Set where
  genericCompressionEvidence : EvidenceClass
  temporalModelEvidence : EvidenceClass
  triadicRepresentationEvidence : EvidenceClass
  triadicContextCodecEvidence : EvidenceClass

classifyTernaryPipeline : ContextKind → EntropyBackend → EvidenceClass
classifyTernaryPipeline noContext backend = triadicRepresentationEvidence
classifyTernaryPipeline previousTritContext zlibBackend =
  triadicRepresentationEvidence
classifyTernaryPipeline previousTritContext lzmaBackend =
  triadicRepresentationEvidence
classifyTernaryPipeline previousTritContext zlibRANSShim =
  triadicRepresentationEvidence
classifyTernaryPipeline previousTritContext realRangeCoder =
  triadicContextCodecEvidence
classifyTernaryPipeline previousTritContext realRANS =
  triadicContextCodecEvidence
classifyTernaryPipeline previousTritAndBadBinContext zlibBackend =
  triadicRepresentationEvidence
classifyTernaryPipeline previousTritAndBadBinContext lzmaBackend =
  triadicRepresentationEvidence
classifyTernaryPipeline previousTritAndBadBinContext zlibRANSShim =
  triadicRepresentationEvidence
classifyTernaryPipeline previousTritAndBadBinContext realRangeCoder =
  triadicContextCodecEvidence
classifyTernaryPipeline previousTritAndBadBinContext realRANS =
  triadicContextCodecEvidence
classifyTernaryPipeline previousTritBadBinRunLengthContext zlibBackend =
  triadicRepresentationEvidence
classifyTernaryPipeline previousTritBadBinRunLengthContext lzmaBackend =
  triadicRepresentationEvidence
classifyTernaryPipeline previousTritBadBinRunLengthContext zlibRANSShim =
  triadicRepresentationEvidence
classifyTernaryPipeline previousTritBadBinRunLengthContext realRangeCoder =
  triadicContextCodecEvidence
classifyTernaryPipeline previousTritBadBinRunLengthContext realRANS =
  triadicContextCodecEvidence

classifyConfiguration : CodecConfiguration → EvidenceClass
classifyConfiguration
  (codecConfiguration grayscaleBytes identityTransform noContext backend) =
  genericCompressionEvidence
classifyConfiguration
  (codecConfiguration grayscaleBytes identityTransform context backend) =
  genericCompressionEvidence
classifyConfiguration
  (codecConfiguration grayscaleBytes temporalByteResidual context backend) =
  temporalModelEvidence
classifyConfiguration
  (codecConfiguration grayscaleBytes ternaryResidual context backend) =
  temporalModelEvidence
classifyConfiguration
  (codecConfiguration grayscaleBytes orbitCanonicalResidual context backend) =
  temporalModelEvidence
classifyConfiguration
  (codecConfiguration ternaryActions transform context backend) =
  classifyTernaryPipeline context backend
classifyConfiguration
  (codecConfiguration ternaryCellDeltas transform context backend) =
  classifyTernaryPipeline context backend

------------------------------------------------------------------------
-- Canonical interpretation of the 600-frame result from the thread.
------------------------------------------------------------------------

sixHundredFrameConfiguration : CodecConfiguration
sixHundredFrameConfiguration =
  codecConfiguration
    grayscaleBytes
    temporalByteResidual
    noContext
    zlibRANSShim

sixHundredFrameEvidenceClass : EvidenceClass
sixHundredFrameEvidenceClass = classifyConfiguration sixHundredFrameConfiguration

sixHundredFrameIsTemporalModelEvidence :
  sixHundredFrameEvidenceClass ≡ temporalModelEvidence
sixHundredFrameIsTemporalModelEvidence = refl

------------------------------------------------------------------------
-- Empirical receipts carry measurements without promoting them to theorems.
-- Rates are integer thousandths of a bit per cell/pixel/trit.
------------------------------------------------------------------------

record CompressionMeasurement : Set where
  constructor compressionMeasurement
  field
    sampleLabel : String
    symbolsMeasured : Nat
    rawRateMilliBits : Nat
    transformedRateMilliBits : Nat
    backendUsed : EntropyBackend
    evidence : EvidenceClass
open CompressionMeasurement public

sixHundredFrameResidualMeasurement : CompressionMeasurement
sixHundredFrameResidualMeasurement =
  compressionMeasurement
    "600 grayscale frames: byte residual plus zlib-backed rANS shim"
    552960000
    1418
    32
    zlibRANSShim
    temporalModelEvidence

record TriadicCodecValidationContract : Set where
  constructor triadicCodecValidationContract
  field
    acceptedAlphabets : List SourceAlphabet
    requiredContexts : List ContextKind
    acceptedBackends : List EntropyBackend
    comparisonBackends : List EntropyBackend
    reportBitsPerTrit : Bool
    requireRoundtripTests : Bool
open TriadicCodecValidationContract public

canonicalTriadicCodecValidationContract : TriadicCodecValidationContract
canonicalTriadicCodecValidationContract =
  triadicCodecValidationContract
    (ternaryActions ∷ ternaryCellDeltas ∷ [])
    (previousTritContext
      ∷ previousTritAndBadBinContext
      ∷ previousTritBadBinRunLengthContext
      ∷ [])
    (realRangeCoder ∷ realRANS ∷ [])
    (zlibBackend ∷ lzmaBackend ∷ [])
    true
    true

triadicCodecBoundarySummary : String
triadicCodecBoundarySummary =
  "Exact ternary support/sign factorisation is proved. The 600-frame 0.032 bpp result is temporal-residual evidence, not triadic-context-codec evidence. A valid triadic benchmark requires a ternary source, explicit context model, real range/rANS backend, roundtrip tests, and bits-per-trit comparison."
