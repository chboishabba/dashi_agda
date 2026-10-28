module DASHI.Physics.Closure.R2P2ClockBiasIdentifiabilityMaxCutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)

import DASHI.Foundations.Base369BinaryTernaryRefinement as Refine
import DASHI.Physics.Closure.R2P2MountainOpticalClockComparisonExact as R2P2
import DASHI.Physics.Closure.QuantumClockProperTimeRedshiftBridge as Redshift

------------------------------------------------------------------------
-- R2P2 max-cut: physically interpretable observation identifiability.
--
-- Under a *toy* affine clock comparison y(h) = b + s*h, one height alone
-- cannot separate a slope from a clock/transfer offset. Even zero residual
-- at one height does not identify the mechanism. A second height may break
-- this particular ambiguity if the bias and mapping are shared and known.
--
-- The 3/6/9 integer labels merely select synthetic data. They are NOT
-- canonical optical clock quantum numbers, dimensional heights, or an
-- observed gravity departure. The general issue is model identifiability.
--
-- Source genealogy: Newton/Einstein weak field; gravitational redshift and
-- local position invariance experiments; Grotti et al. 2024 and Qin et al.
-- 2026 are external chronometric-geodesy/transfer exemplars.
-- Source author results remain source-owned. The finite example below and
-- its invariant/API are the only new DASHI mathematical constructions.
------------------------------------------------------------------------

data ⊥ : Set where

data CandidateClockResponse : Set where
  baselineWithLargeBias : CandidateClockResponse
  doubledSlopeWithSmallBias : CandidateClockResponse

candidateBias : CandidateClockResponse → Nat
candidateBias baselineWithLargeBias = 6
candidateBias doubledSlopeWithSmallBias = 3

candidateSlope : CandidateClockResponse → Nat
candidateSlope baselineWithLargeBias = 1
candidateSlope doubledSlopeWithSmallBias = 2

syntheticRate : CandidateClockResponse → Nat → Nat
syntheticRate candidate height =
  candidateBias candidate + candidateSlope candidate * height

oneHeightCannotDiscriminate :
  syntheticRate baselineWithLargeBias 3
  ≡ syntheticRate doubledSlopeWithSmallBias 3
oneHeightCannotDiscriminate = refl

firstCandidateAtNine :
  syntheticRate baselineWithLargeBias 9 ≡ 15
firstCandidateAtNine = refl

secondCandidateAtNine :
  syntheticRate doubledSlopeWithSmallBias 9 ≡ 21
secondCandidateAtNine = refl

secondHeightDiscriminatesTheseCandidates :
  syntheticRate baselineWithLargeBias 9
  ≡ syntheticRate doubledSlopeWithSmallBias 9 → ⊥
secondHeightDiscriminatesTheseCandidates ()

-- Reuse the exact finite 3/6/9/18 refinement square. Equality of this
-- address diamond DOES NOT yield equality of physical clock signals.
sameRefinementIndexDoesNotRemoveBias :
  Refine.binaryRefine (Refine.ternaryRefine Refine.phase3Resolution)
  ≡ Refine.ternaryRefine (Refine.binaryRefine Refine.phase3Resolution)
sameRefinementIndexDoesNotRemoveBias =
  Refine.binary-ternary-refinement-commutes Refine.phase3Resolution

record R2P2BiasIdentifiabilityMaxCut : Set where
  field
    source : R2P2.R2P2ClockComparisonBoundary
    sourceCanonical :
      source ≡ R2P2.canonicalR2P2ClockComparisonBoundary
    redshiftLaw : Redshift.QuantumClockProperTimeRedshiftBridge
    redshiftLawCanonical :
      redshiftLaw ≡ Redshift.canonicalQuantumClockProperTimeRedshiftBridge
    oneHeightHasAmbiguousResponse :
      syntheticRate baselineWithLargeBias 3
      ≡ syntheticRate doubledSlopeWithSmallBias 3
    secondHeightRemovesThisFiniteAmbiguity :
      syntheticRate baselineWithLargeBias 9
      ≡ syntheticRate doubledSlopeWithSmallBias 9 → ⊥
    universalBiasIdentifiabilityClaimed : Bool
    universalBiasIdentifiabilityClaimedIsFalse :
      universalBiasIdentifiabilityClaimed ≡ false
    stableBiasAcrossRealApparatusEstablished : Bool
    stableBiasAcrossRealApparatusEstablishedIsFalse :
      stableBiasAcrossRealApparatusEstablished ≡ false
    realMultiHeightR2P2DataIngested : Bool
    realMultiHeightR2P2DataIngestedIsFalse :
      realMultiHeightR2P2DataIngested ≡ false
    physicalQuantumGravityIdentified : Bool
    physicalQuantumGravityIdentifiedIsFalse :
      physicalQuantumGravityIdentified ≡ false
    requiredConsumerData : List String

open R2P2BiasIdentifiabilityMaxCut public

canonicalR2P2BiasIdentifiabilityMaxCut : R2P2BiasIdentifiabilityMaxCut
canonicalR2P2BiasIdentifiabilityMaxCut = record
  { source = R2P2.canonicalR2P2ClockComparisonBoundary
  ; sourceCanonical = refl
  ; redshiftLaw = Redshift.canonicalQuantumClockProperTimeRedshiftBridge
  ; redshiftLawCanonical = refl
  ; oneHeightHasAmbiguousResponse = oneHeightCannotDiscriminate
  ; secondHeightRemovesThisFiniteAmbiguity =
      secondHeightDiscriminatesTheseCandidates
  ; universalBiasIdentifiabilityClaimed = false
  ; universalBiasIdentifiabilityClaimedIsFalse = refl
  ; stableBiasAcrossRealApparatusEstablished = false
  ; stableBiasAcrossRealApparatusEstablishedIsFalse = refl
  ; realMultiHeightR2P2DataIngested = false
  ; realMultiHeightR2P2DataIngestedIsFalse = refl
  ; physicalQuantumGravityIdentified = false
  ; physicalQuantumGravityIdentifiedIsFalse = refl
  ; requiredConsumerData =
      "independent chronometric-geodesy potential model, surveyed datums and tides"
      ∷ "calibrated clock-specific biases and their temporal stability"
      ∷ "transfer-delay reciprocity and directional correction covariance"
      ∷ "two or more independent lever arms OR independently bounded offset"
      ∷ "same-epoch time-stamped frequency-ratio and uncertainty data"
      ∷ "declared alternative-gravity model and distinct predicted observable"
      ∷ []
  }

thisExampleDoesNotProveQuantumGravity :
  physicalQuantumGravityIdentified canonicalR2P2BiasIdentifiabilityMaxCut ≡ false
thisExampleDoesNotProveQuantumGravity =
  physicalQuantumGravityIdentifiedIsFalse canonicalR2P2BiasIdentifiabilityMaxCut

thisExampleDoesNotConsumeR2P2Measurements :
  realMultiHeightR2P2DataIngested canonicalR2P2BiasIdentifiabilityMaxCut ≡ false
thisExampleDoesNotConsumeR2P2Measurements =
  realMultiHeightR2P2DataIngestedIsFalse
    canonicalR2P2BiasIdentifiabilityMaxCut
