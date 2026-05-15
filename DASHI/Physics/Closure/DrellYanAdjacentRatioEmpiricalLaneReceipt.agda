module DASHI.Physics.Closure.DrellYanAdjacentRatioEmpiricalLaneReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.Closure.FactorVecFalsifiablePredictionLanes
  using (DrellYanBinRatioLane; NoFreeParameters; noFreeParameters)
open import DASHI.Physics.Closure.HEPDataW3ComparisonLawReceipt as W3

------------------------------------------------------------------------
-- First empirical lane receipt for the FactorVec falsification program.
--
-- Scope: CMS-SMP-20-003 / HEPData ins2079374 t43 below-Z over Z-window
-- Drell-Yan ratio, with t44 covariance.  This attaches the existing W3
-- comparison-law receipt to the new DrellYanBinRatioLane protocol surface.
------------------------------------------------------------------------

data DrellYanAdjacentRatioEmpiricalLaneStatus : Set where
  attachedFromW3T43ComparisonLaw :
    DrellYanAdjacentRatioEmpiricalLaneStatus
  attachedButAboveStrictChi2Dof2 :
    DrellYanAdjacentRatioEmpiricalLaneStatus

data DrellYanAdjacentRatioEmpiricalLaneScope : Set where
  cmsSmp20003T43BelowZOverZPhiStarAdjacentMassWindowRatio :
    DrellYanAdjacentRatioEmpiricalLaneScope

record DrellYanAdjacentRatioEmpiricalLaneReceipt : Set₂ where
  field
    status :
      DrellYanAdjacentRatioEmpiricalLaneStatus

    scope :
      DrellYanAdjacentRatioEmpiricalLaneScope

    protocolSurface :
      Set₁

    protocolSurfaceIsDrellYanLane :
      protocolSurface ≡ DrellYanBinRatioLane

    sourceReceipt :
      W3.W3ComparisonLawReceipt

    table :
      String

    covarianceTable :
      String

    observableConvention :
      String

    freezeCommit :
      String

    fileSha256 :
      String

    projectionDigest :
      String

    chi2 :
      Float

    chi2PerDof :
      Float

    effectiveDof :
      Float

    meanPredData :
      Float

    zeroFit :
      NoFreeParameters

    criterionSatisfied :
      Bool

    criterionSatisfiedIsTrue :
      criterionSatisfied ≡ true

    strictChi2Dof2ProtocolPass :
      Bool

    strictChi2Dof2ProtocolPassIsFalse :
      strictChi2Dof2ProtocolPass ≡ false

    strictProtocolInterpretation :
      String

    comparisonLawStatus :
      W3.HEPDataW3ComparisonLawReceiptStatus

    boundedToT43Only :
      ⊤

    notAboveZPromotion :
      ⊤

    notes :
      List String

open DrellYanAdjacentRatioEmpiricalLaneReceipt public

canonicalDrellYanAdjacentRatioEmpiricalLaneReceipt :
  DrellYanAdjacentRatioEmpiricalLaneReceipt
canonicalDrellYanAdjacentRatioEmpiricalLaneReceipt =
  record
    { status =
        attachedButAboveStrictChi2Dof2
    ; scope =
        cmsSmp20003T43BelowZOverZPhiStarAdjacentMassWindowRatio
    ; protocolSurface =
        DrellYanBinRatioLane
    ; protocolSurfaceIsDrellYanLane =
        refl
    ; sourceReceipt =
        W3.canonicalHEPDataW3ComparisonLawReceipt
    ; table =
        "ins2079374/t43"
    ; covarianceTable =
        "ins2079374/t44"
    ; observableConvention =
        "DSIG/DPHISTAR(50-76 GeV) / DSIG/DPHISTAR(76-106 GeV)"
    ; freezeCommit =
        W3.W3ComparisonLawAcceptanceCriterion.freezeCommit
          W3.canonicalW3ComparisonLawAcceptanceCriterion
    ; fileSha256 =
        W3.W3ComparisonLawAcceptanceCriterion.fileSha256
          W3.canonicalW3ComparisonLawAcceptanceCriterion
    ; projectionDigest =
        W3.W3ComparisonLawAcceptanceCriterion.projectionDigest
          W3.canonicalW3ComparisonLawAcceptanceCriterion
    ; chi2 =
        W3.W3ComparisonLawAcceptanceCriterion.chi2
          W3.canonicalW3ComparisonLawAcceptanceCriterion
    ; chi2PerDof =
        W3.W3ComparisonLawAcceptanceCriterion.chi2PerDof
          W3.canonicalW3ComparisonLawAcceptanceCriterion
    ; effectiveDof =
        W3.W3ComparisonLawAcceptanceCriterion.effectiveDof
          W3.canonicalW3ComparisonLawAcceptanceCriterion
    ; meanPredData =
        W3.W3ComparisonLawAcceptanceCriterion.meanPredData
          W3.canonicalW3ComparisonLawAcceptanceCriterion
    ; zeroFit =
        noFreeParameters
    ; criterionSatisfied =
        W3.W3ComparisonLawAcceptanceCriterion.criterionSatisfied
          W3.canonicalW3ComparisonLawAcceptanceCriterion
    ; criterionSatisfiedIsTrue =
        refl
    ; strictChi2Dof2ProtocolPass =
        false
    ; strictChi2Dof2ProtocolPassIsFalse =
        refl
    ; strictProtocolInterpretation =
        "W3 comparison-law threshold was 4.0, but the stricter falsification-lane target chi2/dof <= 2 is not passed by 2.1565191176"
    ; comparisonLawStatus =
        W3.W3ComparisonLawReceipt.comparisonLawStatus
          W3.canonicalHEPDataW3ComparisonLawReceipt
    ; boundedToT43Only =
        tt
    ; notAboveZPromotion =
        tt
    ; notes =
        "First attached empirical lane for FactorVec falsification program"
        ∷ "Bounded to CMS-SMP-20-003 / HEPData ins2079374 t43 with t44 covariance"
        ∷ "Records chi2/dof = 2.1565191176 and mean pred/data = 0.9941233097 from the existing W3 comparison-law receipt"
        ∷ "This is ballpark empirical contact, not a strict chi2/dof <= 2 pass"
        ∷ "Does not promote above-Z t45/t46 or any fitted-parameter lane"
        ∷ []
    }

canonicalDrellYanAdjacentRatioEmpiricalLaneReceiptCriterionSatisfied :
  criterionSatisfied canonicalDrellYanAdjacentRatioEmpiricalLaneReceipt ≡ true
canonicalDrellYanAdjacentRatioEmpiricalLaneReceiptCriterionSatisfied = refl

canonicalDrellYanAdjacentRatioEmpiricalLaneReceiptStrictProtocolNotPassed :
  strictChi2Dof2ProtocolPass canonicalDrellYanAdjacentRatioEmpiricalLaneReceipt ≡ false
canonicalDrellYanAdjacentRatioEmpiricalLaneReceiptStrictProtocolNotPassed = refl
