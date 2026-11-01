module DASHI.Dynamics.LogisticDecimalPNFBridge where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import MonsterOntos as Monster
import DASHI.Foundations.StageAtlasZeroToEleven as Atlas

data SignedExponent : Set where
  negativeExponent : Nat → SignedExponent
  zeroExponent : SignedExponent
  positiveExponent : Nat → SignedExponent

three57NumeratorFactorisation : 357 ≡ 3 * 7 * 17
three57NumeratorFactorisation = refl

three57DenominatorFactorisation : 100 ≡ 2 * 2 * 5 * 5
three57DenominatorFactorisation = refl

three57ValuationSignature : Monster.SSP → SignedExponent
three57ValuationSignature Monster.p2 = negativeExponent 2
three57ValuationSignature Monster.p3 = positiveExponent 1
three57ValuationSignature Monster.p5 = negativeExponent 2
three57ValuationSignature Monster.p7 = positiveExponent 1
three57ValuationSignature Monster.p11 = zeroExponent
three57ValuationSignature Monster.p13 = zeroExponent
three57ValuationSignature Monster.p17 = positiveExponent 1
three57ValuationSignature Monster.p19 = zeroExponent
three57ValuationSignature Monster.p23 = zeroExponent
three57ValuationSignature Monster.p29 = zeroExponent
three57ValuationSignature Monster.p31 = zeroExponent
three57ValuationSignature Monster.p41 = zeroExponent
three57ValuationSignature Monster.p47 = zeroExponent
three57ValuationSignature Monster.p59 = zeroExponent
three57ValuationSignature Monster.p71 = zeroExponent

record ExactOnsetRoundingWitness (Exact : Set) : Set₁ where
  field
    exactOnset : Exact
    InNearestHundredthCell : Exact → Nat → Set
    exactOnsetRoundsTo357 : InNearestHundredthCell exactOnset 357
    lowerEndpointThousandths : Nat
    upperEndpointThousandths : Nat
    lowerIs3565 : lowerEndpointThousandths ≡ 3565
    upperIs3575 : upperEndpointThousandths ≡ 3575
    intervalConvention : String
    sourceReceipt : String

record RepresentationChangeReceipt : Set where
  field
    sourceFibre targetFibre : String
    exactIdentityPreserved : Bool
    approximationDepth : Nat
    errorWitnessRequired : Bool
    finiteArithmeticAddressabilityGained : Bool
    lostStructure gainedStructure : String
    stageMeaningPromoted : Bool

exactOnsetToThree57ChartReceipt : RepresentationChangeReceipt
exactOnsetToThree57ChartReceipt = record
  { sourceFibre = "exact-real logistic accumulation parameter"
  ; targetFibre = "nearest-hundredth rational display 357/100"
  ; exactIdentityPreserved = false
  ; approximationDepth = 2
  ; errorWitnessRequired = true
  ; finiteArithmeticAddressabilityGained = true
  ; lostStructure = "exact analytic identity"
  ; gainedStructure = "finite factorisation and 15-prime valuation signature"
  ; stageMeaningPromoted = false
  }

record DigitStageLens : Set where
  field
    promotedStage : Atlas.StageAtlasZeroToEleven
    firstFractionalStage : Atlas.StageAtlasZeroToEleven
    secondFractionalStage : Atlas.StageAtlasZeroToEleven
    calibrationReceipt : String
    exactDynamicsImpliesStageReading : Bool
    digitSemanticsIntrinsic : Bool

canonicalThree57CandidateStageLens : DigitStageLens
canonicalThree57CandidateStageLens = record
  { promotedStage = Atlas.atlas-3
  ; firstFractionalStage = Atlas.atlas-5
  ; secondFractionalStage = Atlas.atlas-7
  ; calibrationReceipt = "candidate reading after an exact-real to rational chart crossing"
  ; exactDynamicsImpliesStageReading = false
  ; digitSemanticsIntrinsic = false
  }

record LogisticDecimalAuthorityBoundary : Set where
  field
    rationalFactorisationProved : Bool
    fifteenPrimeSignatureExactFor357Over100 : Bool
    exactOnsetEqualTo357Over100 : Bool
    exactOnsetInRoundingCellProvedHere : Bool
    primeSignatureIntrinsicToExactOnset : Bool
    digitsCauseChaosClaimed : Bool
    stageLensCandidateOnly : Bool

canonicalLogisticDecimalAuthorityBoundary : LogisticDecimalAuthorityBoundary
canonicalLogisticDecimalAuthorityBoundary = record
  { rationalFactorisationProved = true
  ; fifteenPrimeSignatureExactFor357Over100 = true
  ; exactOnsetEqualTo357Over100 = false
  ; exactOnsetInRoundingCellProvedHere = false
  ; primeSignatureIntrinsicToExactOnset = false
  ; digitsCauseChaosClaimed = false
  ; stageLensCandidateOnly = true
  }
