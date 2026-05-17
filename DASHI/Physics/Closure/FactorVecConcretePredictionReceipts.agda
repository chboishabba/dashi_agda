module DASHI.Physics.Closure.FactorVecConcretePredictionReceipts where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.List.Base using (List; _∷_; [])

open import MonsterOntos using (SSP; p31; p59; p71; toNat)
open import Ontology.GodelLattice using (FactorVec)
open import Ontology.GodelLattice renaming (v15 to mkVec15)
open import DASHI.Physics.Closure.FactorVecFalsifiablePredictionLanes
  using (Ratio; ratio)

------------------------------------------------------------------------
-- Concrete fixed-number receipts for the first falsification lanes.
------------------------------------------------------------------------

zPoleApproxFactorVec : FactorVec
zPoleApproxFactorVec =
  mkVec15
    8 5 3 3 2
    2 2 2 1 1
    1 1 1 1 1

record ZPoleCarrierAssignmentReceipt : Set where
  field
    lambdaQCDGeV :
      String

    zPoleMassGeV :
      String

    logMassOverLambdaApprox :
      String

    assignedVector :
      FactorVec

    assignedVectorInterpretation :
      String

    scalarLogOfAssignedVectorApprox :
      String

    scalarReconstructionConsistentWithZPole :
      Bool

    scalarReconstructionConsistentWithZPoleIsFalse :
      scalarReconstructionConsistentWithZPole ≡ false

    dominantAdjacentRatioShape :
      String

    noFittedScaleHere :
      ⊤

open ZPoleCarrierAssignmentReceipt public

canonicalZPoleCarrierAssignmentReceipt :
  ZPoleCarrierAssignmentReceipt
canonicalZPoleCarrierAssignmentReceipt =
  record
    { lambdaQCDGeV =
        "0.217"
    ; zPoleMassGeV =
        "91.2"
    ; logMassOverLambdaApprox =
        "6.04"
    ; assignedVector =
        zPoleApproxFactorVec
    ; assignedVectorInterpretation =
        "coordinate fingerprint from floor(log(m/Lambda_QCD)/log p_i), not a claim that log(G(v)) reconstructs log(m/Lambda_QCD)"
    ; scalarLogOfAssignedVectorApprox =
        "about 46.44 for the corrected coordinate fingerprint, so G(v) is not the Z mass scalar at Lambda_QCD"
    ; scalarReconstructionConsistentWithZPole =
        false
    ; scalarReconstructionConsistentWithZPoleIsFalse =
        refl
    ; dominantAdjacentRatioShape =
        "adjacent-bin ratios near the Z pole are p_i or 1/p_i when exactly one dominant SSP lane changes by one exponent"
    ; noFittedScaleHere =
        tt
    }

data NeutrinoRatioStatus : Set where
  nearMissUnderCurrentData :
    NeutrinoRatioStatus

record NeutrinoMassRatioConcreteReceipt : Set where
  field
    predictedPrime :
      SSP

    predictedRatio :
      Ratio

    predictedRatioIsOneOver31 :
      predictedRatio ≡ ratio 1 (toNat p31)

    observedRatioApprox :
      String

    predictedRatioDecimalApprox :
      String

    discrepancyApprox :
      String

    currentStatus :
      NeutrinoRatioStatus

    requiresCarrierCorrectionOrRetarget :
      Bool

    requiresCarrierCorrectionOrRetargetIsTrue :
      requiresCarrierCorrectionOrRetarget ≡ true

open NeutrinoMassRatioConcreteReceipt public

canonicalNeutrinoMassRatioConcreteReceipt :
  NeutrinoMassRatioConcreteReceipt
canonicalNeutrinoMassRatioConcreteReceipt =
  record
    { predictedPrime =
        p31
    ; predictedRatio =
        ratio 1 (toNat p31)
    ; predictedRatioIsOneOver31 =
        refl
    ; observedRatioApprox =
        "7.53e-5 / 2.51e-3 = 0.0300"
    ; predictedRatioDecimalApprox =
        "1/31 = 0.032258..."
    ; discrepancyApprox =
        "about 7 percent; current lane status is pressured unless a carrier discretization correction closes the gap"
    ; currentStatus =
        nearMissUnderCurrentData
    ; requiresCarrierCorrectionOrRetarget =
        true
    ; requiresCarrierCorrectionOrRetargetIsTrue =
        refl
    }

record DarkSectorHighEndGapReceipt : Set where
  field
    lowerPrime :
      SSP

    upperPrime :
      SSP

    multiplicativeGap :
      Ratio

    multiplicativeGapIs71Over59 :
      multiplicativeGap ≡ ratio (toNat p71) (toNat p59)

    logGapApprox :
      String

    multiplicativeFactorApprox :
      String

    exclusionInterpretation :
      List String

open DarkSectorHighEndGapReceipt public

canonicalDarkSectorHighEndGapReceipt :
  DarkSectorHighEndGapReceipt
canonicalDarkSectorHighEndGapReceipt =
  record
    { lowerPrime =
        p59
    ; upperPrime =
        p71
    ; multiplicativeGap =
        ratio (toNat p71) (toNat p59)
    ; multiplicativeGapIs71Over59 =
        refl
    ; logGapApprox =
        "log(71/59) ~= 0.185"
    ; multiplicativeFactorApprox =
        "71/59 ~= 1.20"
    ; exclusionInterpretation =
        "largest adjacent SSP carrier gap is between 59 and 71"
        ∷ "dark-sector mediator scales landing in this carrier gap are natural MDL-inadmissibility candidates"
        ∷ "this is an exclusion-band receipt, not a positive dark-matter particle claim"
        ∷ []
    }
