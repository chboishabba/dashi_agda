module DASHI.Foundations.CompositeRadixPrimeLaneBridge where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Foundations.StageAtlasZeroToEleven as Atlas
import DASHI.TrackedPrimes as TP

------------------------------------------------------------------------
-- Composite radices are joined or primary-depth charts, not new p-adic fields.
------------------------------------------------------------------------

data RadixCarrierKind : Set where
  primeLocalFieldChart : RadixCarrierKind
  joinedPrimeProductChart : RadixCarrierKind
  primePowerDepthChart : RadixCarrierKind

record CompositeRadixPrimeLaneReceipt : Set where
  field
    radix : Nat
    leftFactor : Nat
    rightFactor : Nat
    factorisation :
      leftFactor * rightFactor ≡ radix
    carrierKind : RadixCarrierKind
    primeComponents : List TP.SSP
    primaryPrime : TP.SSP
    primaryDepth : Nat
    zeroDivisorWitnessRole : Bool
    standaloneLocalFieldClaimed : Bool
    crtIsomorphismKernelCheckedHere : Bool
    semanticMeaningDerivedFromRingStructure : Bool
    description : String

canonicalSixJoinedChart : CompositeRadixPrimeLaneReceipt
canonicalSixJoinedChart = record
  { radix = 6
  ; leftFactor = 2
  ; rightFactor = 3
  ; factorisation = refl
  ; carrierKind = joinedPrimeProductChart
  ; primeComponents = TP.p2 ∷ TP.p3 ∷ []
  ; primaryPrime = TP.p3
  ; primaryDepth = 1
  ; zeroDivisorWitnessRole = true
  ; standaloneLocalFieldClaimed = false
  ; crtIsomorphismKernelCheckedHere = false
  ; semanticMeaningDerivedFromRingStructure = false
  ; description =
      "6 is consumed as a joined binary/ternary chart; 2*3=6 witnesses the quotient-ring zero-divisor seam without inventing a 6-adic field."
  }

canonicalNinePrimaryDepthChart : CompositeRadixPrimeLaneReceipt
canonicalNinePrimaryDepthChart = record
  { radix = 9
  ; leftFactor = 3
  ; rightFactor = 3
  ; factorisation = refl
  ; carrierKind = primePowerDepthChart
  ; primeComponents = TP.p3 ∷ []
  ; primaryPrime = TP.p3
  ; primaryDepth = 2
  ; zeroDivisorWitnessRole = true
  ; standaloneLocalFieldClaimed = false
  ; crtIsomorphismKernelCheckedHere = false
  ; semanticMeaningDerivedFromRingStructure = false
  ; description =
      "9 is a depth-two 3-primary sheet, not a second prime lane and not a field modulo 9."
  }

data ThreeSixNineClosureBand : Set where
  lowLocalClosure3 : ThreeSixNineClosureBand
  middleReflexiveClosure6 : ThreeSixNineClosureBand
  highSystemicClosure9 : ThreeSixNineClosureBand

record ClosureBandCoordinate : Set where
  field
    atlasCoordinate : Atlas.StageAtlasZeroToEleven
    band : ThreeSixNineClosureBand
    coordinateMatchesBand : Bool
    balancedTernaryOrientationIsSeparate : Bool
    semanticInterpretationCandidateOnly : Bool

stage3LowClosure : ClosureBandCoordinate
stage3LowClosure = record
  { atlasCoordinate = Atlas.atlas-3
  ; band = lowLocalClosure3
  ; coordinateMatchesBand = true
  ; balancedTernaryOrientationIsSeparate = true
  ; semanticInterpretationCandidateOnly = true
  }

stage6MiddleClosure : ClosureBandCoordinate
stage6MiddleClosure = record
  { atlasCoordinate = Atlas.atlas-6
  ; band = middleReflexiveClosure6
  ; coordinateMatchesBand = true
  ; balancedTernaryOrientationIsSeparate = true
  ; semanticInterpretationCandidateOnly = true
  }

stage9HighClosure : ClosureBandCoordinate
stage9HighClosure = record
  { atlasCoordinate = Atlas.atlas-9
  ; band = highSystemicClosure9
  ; coordinateMatchesBand = true
  ; balancedTernaryOrientationIsSeparate = true
  ; semanticInterpretationCandidateOnly = true
  }

record CompositeRadixAuthorityBoundary : Set where
  field
    primeLanesAreIrreducibleLocalCarriers : Bool
    compositeRadixIsJoinedChart : Bool
    sixPromotedToPrimeField : Bool
    ninePromotedToPrimeField : Bool
    closureBandsIdentifiedWithBalancedTernaryValues : Bool
    semanticClosureDerivedWithoutLens : Bool

canonicalCompositeRadixAuthorityBoundary :
  CompositeRadixAuthorityBoundary
canonicalCompositeRadixAuthorityBoundary = record
  { primeLanesAreIrreducibleLocalCarriers = true
  ; compositeRadixIsJoinedChart = true
  ; sixPromotedToPrimeField = false
  ; ninePromotedToPrimeField = false
  ; closureBandsIdentifiedWithBalancedTernaryValues = false
  ; semanticClosureDerivedWithoutLens = false
  }
