module DASHI.Combinatorics.TriadicVideoCodecObservationQuotient where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Triadic video codec as observation quotient and admissible reuse surface.
--
-- This records the sibling dashitest codec formalism at the DASHI boundary:
-- frame stream -> predictor/chart -> signed residual -> balanced ternary
-- planes -> quotient/reuse action -> entropy payload.  The important gate is
-- not compression alone; reuse is admissible only when equality/correction,
-- side information, and deterministic decoder reconstruction are all present.

data CodecPipelineLayer : Set where
  frameStreamLayer : CodecPipelineLayer
  predictorChartLayer : CodecPipelineLayer
  signedResidualLayer : CodecPipelineLayer
  balancedTernaryPlaneLayer : CodecPipelineLayer
  magnitudeSignQuotientLayer : CodecPipelineLayer
  blockReuseOrbitLayer : CodecPipelineLayer
  entropyPayloadLayer : CodecPipelineLayer
  deterministicDecodeLayer : CodecPipelineLayer

canonicalCodecPipeline : List CodecPipelineLayer
canonicalCodecPipeline =
  frameStreamLayer
  ∷ predictorChartLayer
  ∷ signedResidualLayer
  ∷ balancedTernaryPlaneLayer
  ∷ magnitudeSignQuotientLayer
  ∷ blockReuseOrbitLayer
  ∷ entropyPayloadLayer
  ∷ deterministicDecodeLayer
  ∷ []

data PredictorChartKind : Set where
  intraBaselineChart : PredictorChartKind
  temporalDeltaChart : PredictorChartKind
  motionCompensatedChart : PredictorChartKind
  blockReuseChart : PredictorChartKind
  reversibleColourChart : PredictorChartKind

data BalancedTernarySymbol : Set where
  negTrit : BalancedTernarySymbol
  zeroTrit : BalancedTernarySymbol
  posTrit : BalancedTernarySymbol

data ReuseAction : Set where
  newBlock : ReuseAction
  sameBlock : ReuseAction
  reuseBlock : ReuseAction
  reuseFlippedBlock : ReuseAction

data CodecAdmissibilityGate : Set where
  signedResidualCarriedGate : CodecAdmissibilityGate
  balancedTernaryExactGate : CodecAdmissibilityGate
  quotientMaskDeterministicGate : CodecAdmissibilityGate
  reuseEqualityOrCorrectionGate : CodecAdmissibilityGate
  sideInformationCountedGate : CodecAdmissibilityGate
  decoderReconstructionGate : CodecAdmissibilityGate
  entropyModelSerializedGate : CodecAdmissibilityGate
  residualDefectExplicitGate : CodecAdmissibilityGate

data CodecNonPromotionBoundary : Set where
  noBenchmarkOnlyCodecPromotion : CodecNonPromotionBoundary
  noHashOnlyReusePromotion : CodecNonPromotionBoundary
  noHeaderFreeRateClaim : CodecNonPromotionBoundary
  noDecoderlessCompressionClaim : CodecNonPromotionBoundary
  noResidualSuppressionWithoutCorrection : CodecNonPromotionBoundary
  noCodecPhysicsEquivalenceClaim : CodecNonPromotionBoundary

canonicalCodecGates : List CodecAdmissibilityGate
canonicalCodecGates =
  signedResidualCarriedGate
  ∷ balancedTernaryExactGate
  ∷ quotientMaskDeterministicGate
  ∷ reuseEqualityOrCorrectionGate
  ∷ sideInformationCountedGate
  ∷ decoderReconstructionGate
  ∷ entropyModelSerializedGate
  ∷ residualDefectExplicitGate
  ∷ []

canonicalCodecBoundaries : List CodecNonPromotionBoundary
canonicalCodecBoundaries =
  noBenchmarkOnlyCodecPromotion
  ∷ noHashOnlyReusePromotion
  ∷ noHeaderFreeRateClaim
  ∷ noDecoderlessCompressionClaim
  ∷ noResidualSuppressionWithoutCorrection
  ∷ noCodecPhysicsEquivalenceClaim
  ∷ []

record TriadicVideoCodecObservationQuotient : Set₁ where
  field
    FrameStream : Set
    PredictorChart : Set
    SignedResidual : Set
    BalancedPlane : Set
    MagnitudePlane : Set
    SignPlane : Set
    BlockOrbit : Set
    SideInformation : Set
    EntropyPayload : Set
    DecodedFrameStream : Set

    chooseChart :
      FrameStream →
      PredictorChart

    chartKind :
      PredictorChart →
      PredictorChartKind

    signedResidual :
      FrameStream →
      PredictorChart →
      SignedResidual

    balancedPlanes :
      SignedResidual →
      List BalancedPlane

    symbolOf :
      BalancedPlane →
      BalancedTernarySymbol

    magnitudePlane :
      BalancedPlane →
      MagnitudePlane

    signPlane :
      BalancedPlane →
      SignPlane

    reuseAction :
      BlockOrbit →
      ReuseAction

    reuseWitness :
      BlockOrbit →
      SideInformation

    encodePayload :
      List BalancedPlane →
      SideInformation →
      EntropyPayload

    decodePayload :
      EntropyPayload →
      SideInformation →
      DecodedFrameStream

    sideInformationFor :
      PredictorChart →
      BlockOrbit →
      SideInformation

    gateSatisfied :
      SideInformation →
      CodecAdmissibilityGate →
      Set

    sameDecodedStream :
      FrameStream →
      DecodedFrameStream →
      Set

    pipeline :
      List CodecPipelineLayer

    codecReading :
      String

open TriadicVideoCodecObservationQuotient public

record CodecReuseAdmissibilityWitness
    (codec : TriadicVideoCodecObservationQuotient) : Set where
  field
    stream :
      FrameStream codec

    chart :
      PredictorChart codec

    orbit :
      BlockOrbit codec

    sideInfo :
      SideInformation codec

    payload :
      EntropyPayload codec

    gates :
      List CodecAdmissibilityGate

    gatesAreCanonical :
      gates ≡ canonicalCodecGates

    sideInfoMatches :
      sideInformationFor codec chart orbit ≡ sideInfo

    payloadMatches :
      encodePayload codec
        (balancedPlanes codec (signedResidual codec stream chart))
        sideInfo
        ≡ payload

    decoded :
      DecodedFrameStream codec

    decodedMatches :
      decodePayload codec payload sideInfo ≡ decoded

    reconstructionReceipt :
      sameDecodedStream codec stream decoded

    witnessReading :
      String

open CodecReuseAdmissibilityWitness public

record CodecNonPromotionCertificate
    (codec : TriadicVideoCodecObservationQuotient) : Set where
  field
    boundaries :
      List CodecNonPromotionBoundary

    boundariesAreCanonical :
      boundaries ≡ canonicalCodecBoundaries

    benchmarkOnlyPromoted :
      Bool

    benchmarkOnlyPromotedIsFalse :
      benchmarkOnlyPromoted ≡ false

    hashOnlyReusePromoted :
      Bool

    hashOnlyReusePromotedIsFalse :
      hashOnlyReusePromoted ≡ false

    headerFreeRatePromoted :
      Bool

    headerFreeRatePromotedIsFalse :
      headerFreeRatePromoted ≡ false

    decoderlessCompressionPromoted :
      Bool

    decoderlessCompressionPromotedIsFalse :
      decoderlessCompressionPromoted ≡ false

    certificateReading :
      String

open CodecNonPromotionCertificate public

canonicalCodecNonPromotionCertificate :
  (codec : TriadicVideoCodecObservationQuotient) →
  CodecNonPromotionCertificate codec
canonicalCodecNonPromotionCertificate codec =
  record
    { boundaries =
        canonicalCodecBoundaries
    ; boundariesAreCanonical =
        refl
    ; benchmarkOnlyPromoted =
        false
    ; benchmarkOnlyPromotedIsFalse =
        refl
    ; hashOnlyReusePromoted =
        false
    ; hashOnlyReusePromotedIsFalse =
        refl
    ; headerFreeRatePromoted =
        false
    ; headerFreeRatePromotedIsFalse =
        refl
    ; decoderlessCompressionPromoted =
        false
    ; decoderlessCompressionPromotedIsFalse =
        refl
    ; certificateReading =
        "A triadic video quotient is codec-admissible only when side information is counted, reuse has equality or correction evidence, and deterministic decoding reconstructs the stream."
    }
