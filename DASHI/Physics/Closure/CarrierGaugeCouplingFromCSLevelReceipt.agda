module DASHI.Physics.Closure.CarrierGaugeCouplingFromCSLevelReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CarrierScaleFromHeegnerReceipt as Scale

data CarrierGaugeCouplingFromCSLevelStatus : Set where
  csLevelGaugeCouplingCandidateRecordedNoYMRunning :
    CarrierGaugeCouplingFromCSLevelStatus

data CSLevelGaugeCouplingInput : Set where
  conductorLevelThree :
    CSLevelGaugeCouplingInput

  conductorLevelFour :
    CSLevelGaugeCouplingInput

  conductorLevelSeven :
    CSLevelGaugeCouplingInput

  levelRankDiagnosticOnly :
    CSLevelGaugeCouplingInput

canonicalCSLevelGaugeCouplingInputs :
  List CSLevelGaugeCouplingInput
canonicalCSLevelGaugeCouplingInputs =
  conductorLevelThree
  ∷ conductorLevelFour
  ∷ conductorLevelSeven
  ∷ levelRankDiagnosticOnly
  ∷ []

data CSLevelGaugeCouplingBlocker : Set where
  missingCSToFourDimensionalYMMap :
    CSLevelGaugeCouplingBlocker

  missingRenormalizedCouplingDefinition :
    CSLevelGaugeCouplingBlocker

  missingScaleDependentKRunning :
    CSLevelGaugeCouplingBlocker

canonicalCSLevelGaugeCouplingBlockers :
  List CSLevelGaugeCouplingBlocker
canonicalCSLevelGaugeCouplingBlockers =
  missingCSToFourDimensionalYMMap
  ∷ missingRenormalizedCouplingDefinition
  ∷ missingScaleDependentKRunning
  ∷ []

data CSLevelGaugeCouplingPromotion : Set where

csLevelGaugeCouplingPromotionImpossibleHere :
  CSLevelGaugeCouplingPromotion →
  ⊥
csLevelGaugeCouplingPromotionImpossibleHere ()

csLevelGaugeCouplingCandidateLabel : String
csLevelGaugeCouplingCandidateLabel =
  "g_carrier^2(k) candidate proportional to 1/k at fixed conductor level"

csLevelGaugeCouplingBoundaryLabel : String
csLevelGaugeCouplingBoundaryLabel =
  "fixed Chern-Simons/conductor levels record a carrier candidate, not a renormalized four-dimensional Yang-Mills running coupling"

record CarrierGaugeCouplingFromCSLevelReceipt : Setω where
  field
    status :
      CarrierGaugeCouplingFromCSLevelStatus

    carrierScaleReceipt :
      Scale.CarrierScaleFromHeegnerReceipt

    carrierScaleRecorded :
      Scale.carrierScaleNearCharmMass carrierScaleReceipt ≡ true

    canonicalP3Level :
      Nat

    canonicalP3LevelIsThree :
      canonicalP3Level ≡ 3

    canonicalP5Level :
      Nat

    canonicalP5LevelIsSeven :
      canonicalP5Level ≡ 7

    couplingCandidate :
      String

    couplingCandidateIsCanonical :
      couplingCandidate ≡ csLevelGaugeCouplingCandidateLabel

    boundaryStatement :
      String

    boundaryStatementIsCanonical :
      boundaryStatement ≡ csLevelGaugeCouplingBoundaryLabel

    csLevelCouplingCandidateRecorded :
      Bool

    csLevelCouplingCandidateRecordedIsTrue :
      csLevelCouplingCandidateRecorded ≡ true

    alphaSFromLevel3 :
      String

    alphaSFromLevel3IsCanonical :
      alphaSFromLevel3 ≡ "alpha_s = 1/3"

    alphaSLevel3NearCharmScale :
      Bool

    alphaSLevel3NearCharmScaleIsTrue :
      alphaSLevel3NearCharmScale ≡ true

    renormalizedYMCouplingConstructed :
      Bool

    renormalizedYMCouplingConstructedIsFalse :
      renormalizedYMCouplingConstructed ≡ false

    kRunningConstructed :
      Bool

    kRunningConstructedIsFalse :
      kRunningConstructed ≡ false

    continuumBetaRunningConstructed :
      Bool

    continuumBetaRunningConstructedIsFalse :
      continuumBetaRunningConstructed ≡ false

    continuumYangMillsConstructed :
      Bool

    continuumYangMillsConstructedIsFalse :
      continuumYangMillsConstructed ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    inputs :
      List CSLevelGaugeCouplingInput

    inputsAreCanonical :
      inputs ≡ canonicalCSLevelGaugeCouplingInputs

    blockers :
      List CSLevelGaugeCouplingBlocker

    blockersAreCanonical :
      blockers ≡ canonicalCSLevelGaugeCouplingBlockers

    promotionFlags :
      List CSLevelGaugeCouplingPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

open CarrierGaugeCouplingFromCSLevelReceipt public

canonicalCarrierGaugeCouplingFromCSLevelReceipt :
  CarrierGaugeCouplingFromCSLevelReceipt
canonicalCarrierGaugeCouplingFromCSLevelReceipt =
  record
    { status =
        csLevelGaugeCouplingCandidateRecordedNoYMRunning
    ; carrierScaleReceipt =
        Scale.canonicalCarrierScaleFromHeegnerReceipt
    ; carrierScaleRecorded =
        refl
    ; canonicalP3Level =
        3
    ; canonicalP3LevelIsThree =
        refl
    ; canonicalP5Level =
        7
    ; canonicalP5LevelIsSeven =
        refl
    ; couplingCandidate =
        csLevelGaugeCouplingCandidateLabel
    ; couplingCandidateIsCanonical =
        refl
    ; boundaryStatement =
        csLevelGaugeCouplingBoundaryLabel
    ; boundaryStatementIsCanonical =
        refl
    ; csLevelCouplingCandidateRecorded =
        true
    ; csLevelCouplingCandidateRecordedIsTrue =
        refl
    ; alphaSFromLevel3 =
        "alpha_s = 1/3"
    ; alphaSFromLevel3IsCanonical =
        refl
    ; alphaSLevel3NearCharmScale =
        true
    ; alphaSLevel3NearCharmScaleIsTrue =
        refl
    ; renormalizedYMCouplingConstructed =
        false
    ; renormalizedYMCouplingConstructedIsFalse =
        refl
    ; kRunningConstructed =
        false
    ; kRunningConstructedIsFalse =
        refl
    ; continuumBetaRunningConstructed =
        false
    ; continuumBetaRunningConstructedIsFalse =
        refl
    ; continuumYangMillsConstructed =
        false
    ; continuumYangMillsConstructedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; inputs =
        canonicalCSLevelGaugeCouplingInputs
    ; inputsAreCanonical =
        refl
    ; blockers =
        canonicalCSLevelGaugeCouplingBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    }

carrierGaugeCouplingFromCSLevelKeepsKRunningFalse :
  kRunningConstructed canonicalCarrierGaugeCouplingFromCSLevelReceipt ≡ false
carrierGaugeCouplingFromCSLevelKeepsKRunningFalse =
  refl
