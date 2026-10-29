module DASHI.Physics.Closure.R2P2ThreeClockLoopClosure369Exact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Physics.Closure.R2P2MountainOpticalClockComparisonExact as R2P2
import DASHI.Foundations.Base369BinaryTernaryRefinement as Refine

------------------------------------------------------------------------
-- Optical-clock three-node ratio loop integrity.
-- Scientific prior art: optical frequency-ratio graph loop closures;
-- Fortier, Luiten and Margolis, "Optical atomic clocks: defining the
-- future of time and frequency metrology", Optica 13 (2026), 143-163,
-- DOI 10.1364/OPTICA.575770, published 2026-01-16.
-- Earlier Beloy et al. 2021 clock-network measurements and their original
-- experimental authors retain priority, as do earlier loop-closure papers.
--
-- For three nonzero optical frequencies fA, fB, fC, the products
-- (fA/fB)*(fB/fC)*(fC/fA) equal unity. A failed loop detects
-- inconsistency among observed edge ratios, but does NOT by itself prove
-- gravitational curvature or a non-Einstein metric. R2P2 has only two
-- documented physical clock sites, not a verified three-clock triangle.
--
-- The integers 3/6/9 below are deliberately tiny *synthetic examples*
-- selected from existing 369 numerals, not special physical frequencies.
------------------------------------------------------------------------

data ⊥ : Set where

record SyntheticThreeClockFrequencies : Set where
  field
    first : Nat
    second : Nat
    third : Nat

open SyntheticThreeClockFrequencies public

canonicalSyntheticThreeClockFrequencies : SyntheticThreeClockFrequencies
canonicalSyntheticThreeClockFrequencies = record
  { first = 3
  ; second = 6
  ; third = 9
  }

-- Products of the numerators and denominators of fA/fB, fB/fC, fC/fA.
loopNumerator : Nat
loopNumerator =
  first canonicalSyntheticThreeClockFrequencies
  * second canonicalSyntheticThreeClockFrequencies
  * third canonicalSyntheticThreeClockFrequencies

loopDenominator : Nat
loopDenominator =
  second canonicalSyntheticThreeClockFrequencies
  * third canonicalSyntheticThreeClockFrequencies
  * first canonicalSyntheticThreeClockFrequencies

syntheticCycleCloses : loopNumerator ≡ loopDenominator
syntheticCycleCloses = refl

syntheticCycleProduct : loopNumerator ≡ 162
syntheticCycleProduct = refl

-- A fabricated inconsistent third ratio fC' / fA with fC' = 10.
-- Other two edges remain from the same three-frequency model.
badThirdEdgeNumerator : Nat
badThirdEdgeNumerator =
  first canonicalSyntheticThreeClockFrequencies
  * second canonicalSyntheticThreeClockFrequencies
  * 10

badThirdEdgeDenominator : Nat
badThirdEdgeDenominator = loopDenominator

syntheticBadEdgeDoesNotClose :
  badThirdEdgeNumerator ≡ badThirdEdgeDenominator → ⊥
syntheticBadEdgeDoesNotClose ()

-- This is just a shared refinement-index bridge, not a dynamical theorem
-- connecting loop closure with the base-369 carrier phase.
canonicalThreeSixNineRefinement :
  Refine.binaryRefine (Refine.ternaryRefine Refine.phase3Resolution)
  ≡ Refine.ternaryRefine (Refine.binaryRefine Refine.phase3Resolution)
canonicalThreeSixNineRefinement =
  Refine.binary-ternary-refinement-commutes Refine.phase3Resolution

record ThreeClockLoopSourceBoundary : Set where
  field
    r2p2 : R2P2.R2P2ClockComparisonBoundary
    r2p2Canonical : r2p2 ≡ R2P2.canonicalR2P2ClockComparisonBoundary
    priorArtCitation : String
    finiteCycleAgreement : loopNumerator ≡ loopDenominator
    finiteCorruptionRejected :
      badThirdEdgeNumerator ≡ badThirdEdgeDenominator → ⊥
    r2p2ThirdRealClockProvided : Bool
    r2p2ThirdRealClockProvidedIsFalse :
      r2p2ThirdRealClockProvided ≡ false
    r2p2ThreeIndependentEdgesCalibrated : Bool
    r2p2ThreeIndependentEdgesCalibratedIsFalse :
      r2p2ThreeIndependentEdgesCalibrated ≡ false
    threeClockLoopNullImpliesCurvature : Bool
    threeClockLoopNullImpliesCurvatureIsFalse :
      threeClockLoopNullImpliesCurvature ≡ false
    finiteModelIsObservedFrequencyNetwork : Bool
    finiteModelIsObservedFrequencyNetworkIsFalse :
      finiteModelIsObservedFrequencyNetwork ≡ false
    requiredEvidence : List String

open ThreeClockLoopSourceBoundary public

canonicalThreeClockLoopSourceBoundary : ThreeClockLoopSourceBoundary
canonicalThreeClockLoopSourceBoundary = record
  { r2p2 = R2P2.canonicalR2P2ClockComparisonBoundary
  ; r2p2Canonical = refl
  ; priorArtCitation =
      "Fortier, Luiten, Margolis, Optica 13 (2026), DOI 10.1364/OPTICA.575770; earlier Beloy et al. clock networks"
  ; finiteCycleAgreement = syntheticCycleCloses
  ; finiteCorruptionRejected = syntheticBadEdgeDoesNotClose
  ; r2p2ThirdRealClockProvided = false
  ; r2p2ThirdRealClockProvidedIsFalse = refl
  ; r2p2ThreeIndependentEdgesCalibrated = false
  ; r2p2ThreeIndependentEdgesCalibratedIsFalse = refl
  ; threeClockLoopNullImpliesCurvature = false
  ; threeClockLoopNullImpliesCurvatureIsFalse = refl
  ; finiteModelIsObservedFrequencyNetwork = false
  ; finiteModelIsObservedFrequencyNetworkIsFalse = refl
  ; requiredEvidence =
      "third independently calibrated optical reference, if a future triangle is proposed"
      ∷ "three real signed frequency-ratio edges measured in compatible epochs"
      ∷ "covariance across edges, transfer paths, drift and systematic biases"
      ∷ "independent gravitational potential model for each physical clock site"
      ∷ []
  }

threeClockLoopCannotClaimCurvature :
  threeClockLoopNullImpliesCurvature canonicalThreeClockLoopSourceBoundary ≡ false
threeClockLoopCannotClaimCurvature =
  threeClockLoopNullImpliesCurvatureIsFalse canonicalThreeClockLoopSourceBoundary

twoClockR2P2DoesNotSupplyTriangle :
  r2p2ThirdRealClockProvided canonicalThreeClockLoopSourceBoundary ≡ false
twoClockR2P2DoesNotSupplyTriangle =
  r2p2ThirdRealClockProvidedIsFalse canonicalThreeClockLoopSourceBoundary
