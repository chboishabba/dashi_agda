module DASHI.Physics.Closure.DefectCriticalSeamIdentityDynamicsInstance where

-- Concrete identity-dynamics instance for the defect/quadratic critical seam.
--
-- This module inhabits the defect-monotonicity premise on the checked integer
-- shift carrier.  It does not inhabit CriticalSeamTheoremType and does not
-- promote signature, Clifford, Standard Model, or terminal claims.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Geometry.ProjectionDefect as PD
import DASHI.Geometry.ProjectionDefectToParallelogram as PDP
import DASHI.Physics.QuadraticEmergenceShiftInstance as QES
import DASHI.Physics.QuadraticPolarization as QP
import DASHI.Physics.Closure.DefectQuadraticParallelogramCriticalSeam as Seam

identityDynamics :
  ∀ {m : Nat} →
  PD.Additive.Carrier (QES.AdditiveVecℤ {m}) →
  PD.Additive.Carrier (QES.AdditiveVecℤ {m})
identityDynamics x = x

identityDefectEnergy :
  ∀ {m : Nat} →
  PD.Additive.Carrier (QES.AdditiveVecℤ {m}) →
  _
identityDefectEnergy {m} x =
  QP.Q̂core
    (PD.ProjectionDefect.D (QES.PDzero {m}) x)

identityDefectEnergyIsProjectionDefectCore :
  ∀ {m : Nat}
  (x : PD.Additive.Carrier (QES.AdditiveVecℤ {m})) →
  identityDefectEnergy x
  ≡
  QP.Q̂core
    (PD.ProjectionDefect.D (QES.PDzero {m}) x)
identityDefectEnergyIsProjectionDefectCore _ = refl

identityDefectEnergyMonotoneAlongDynamics :
  ∀ {m : Nat}
  (x : PD.Additive.Carrier (QES.AdditiveVecℤ {m})) →
  identityDefectEnergy (identityDynamics x) ≡ identityDefectEnergy x
identityDefectEnergyMonotoneAlongDynamics _ = refl

canonicalIdentityDefectMonotonicityEvidence :
  ∀ {m : Nat} → Seam.DefectMonotonicityEvidence m
canonicalIdentityDefectMonotonicityEvidence {m} =
  record
    { dynamicsMap =
        identityDynamics
    ; defectEnergy =
        identityDefectEnergy
    ; defectEnergyIsProjectionDefectCore =
        identityDefectEnergyIsProjectionDefectCore
    ; monotoneAlongDynamics =
        identityDefectEnergyMonotoneAlongDynamics
    }

canonicalIdentityDefectMonotonicityEvidence4 :
  Seam.DefectMonotonicityEvidence 4
canonicalIdentityDefectMonotonicityEvidence4 =
  canonicalIdentityDefectMonotonicityEvidence {4}

data IdentityDynamicsInstanceStage : Set where
  identityDynamicsSelected :
    IdentityDynamicsInstanceStage

  projectionDefectCoreEnergySelected :
    IdentityDynamicsInstanceStage

  monotonicityByReflexivityChecked :
    IdentityDynamicsInstanceStage

  shiftSupportStillSeparate :
    IdentityDynamicsInstanceStage

  generalCriticalSeamStillOpen :
    IdentityDynamicsInstanceStage

  downstreamPromotionStillBlocked :
    IdentityDynamicsInstanceStage

record IdentityDynamicsInstanceRow : Set where
  field
    stage :
      IdentityDynamicsInstanceStage

    artifact :
      String

    status :
      String

    promoted :
      Bool

    promotedIsFalse :
      promoted ≡ false

open IdentityDynamicsInstanceRow public

mkIdentityDynamicsInstanceRow :
  IdentityDynamicsInstanceStage →
  String →
  String →
  IdentityDynamicsInstanceRow
mkIdentityDynamicsInstanceRow stage artifact status =
  record
    { stage = stage
    ; artifact = artifact
    ; status = status
    ; promoted = false
    ; promotedIsFalse = refl
    }

canonicalIdentityDynamicsInstanceRows :
  List IdentityDynamicsInstanceRow
canonicalIdentityDynamicsInstanceRows =
  mkIdentityDynamicsInstanceRow
    identityDynamicsSelected
    "identityDynamics"
    "dynamicsMap x = x on the integer shift carrier"
  ∷ mkIdentityDynamicsInstanceRow
    projectionDefectCoreEnergySelected
    "identityDefectEnergy"
    "defectEnergy x = QP.Qhat-core (D (PDzero) x)"
  ∷ mkIdentityDynamicsInstanceRow
    monotonicityByReflexivityChecked
    "identityDefectEnergyMonotoneAlongDynamics"
    "monotoneAlongDynamics is inhabited by refl"
  ∷ mkIdentityDynamicsInstanceRow
    shiftSupportStillSeparate
    "canonicalShiftCarrierCriticalSeamSupport"
    "shift-carrier parallelogram and quadratic support remains imported support"
  ∷ mkIdentityDynamicsInstanceRow
    generalCriticalSeamStillOpen
    "CriticalSeamTheoremType"
    "identity dynamics does not prove the general defect/admissibility/hierarchy theorem"
  ∷ mkIdentityDynamicsInstanceRow
    downstreamPromotionStillBlocked
    "signature/Clifford/StandardModel/terminal guards"
    "downstream promotions remain false"
  ∷ []

record DefectCriticalSeamIdentityDynamicsInstance : Setω where
  field
    monotonicityEvidence :
      Seam.DefectMonotonicityEvidence 4

    shiftCarrierSupport :
      Seam.ShiftCarrierCriticalSeamSupport 4

    projectionParallelogramPackage :
      PDP.ProjectionDefectParallelogramPackage
        (QES.AdditiveVecℤ {4})
        QES.ScalarFieldℤ

    rowIndex :
      List IdentityDynamicsInstanceRow

    rowCount :
      Nat

    rowCountIs6 :
      rowCount ≡ 6

    identityDynamicsChecked :
      Bool

    identityDynamicsCheckedIsTrue :
      identityDynamicsChecked ≡ true

    defectEnergyCoreBindingChecked :
      Bool

    defectEnergyCoreBindingCheckedIsTrue :
      defectEnergyCoreBindingChecked ≡ true

    monotonicityChecked :
      Bool

    monotonicityCheckedIsTrue :
      monotonicityChecked ≡ true

    criticalSeamTheoremProved :
      Bool

    criticalSeamTheoremProvedIsFalse :
      criticalSeamTheoremProved ≡ false

    exactRemainingTheorem :
      Seam.CriticalSeamMissingTheorem

    exactRemainingTheoremIsDefectAdmissibilityHierarchy :
      exactRemainingTheorem
      ≡ Seam.missingDefectAdmissibilityHierarchyToParallelogram

    signaturePromoted :
      Bool

    signaturePromotedIsFalse :
      signaturePromoted ≡ false

    cliffordPromoted :
      Bool

    cliffordPromotedIsFalse :
      cliffordPromoted ≡ false

    standardModelPromoted :
      Bool

    standardModelPromotedIsFalse :
      standardModelPromoted ≡ false

    terminalUnificationPromoted :
      Bool

    terminalUnificationPromotedIsFalse :
      terminalUnificationPromoted ≡ false

    decisionNotes :
      List String

open DefectCriticalSeamIdentityDynamicsInstance public

canonicalDefectCriticalSeamIdentityDynamicsInstance :
  DefectCriticalSeamIdentityDynamicsInstance
canonicalDefectCriticalSeamIdentityDynamicsInstance =
  record
    { monotonicityEvidence =
        canonicalIdentityDefectMonotonicityEvidence4
    ; shiftCarrierSupport =
        Seam.canonicalShiftCarrierCriticalSeamSupport {4}
    ; projectionParallelogramPackage =
        Seam.ShiftCarrierCriticalSeamSupport.projectionParallelogramPackage
          (Seam.canonicalShiftCarrierCriticalSeamSupport {4})
    ; rowIndex =
        canonicalIdentityDynamicsInstanceRows
    ; rowCount =
        6
    ; rowCountIs6 =
        refl
    ; identityDynamicsChecked =
        true
    ; identityDynamicsCheckedIsTrue =
        refl
    ; defectEnergyCoreBindingChecked =
        true
    ; defectEnergyCoreBindingCheckedIsTrue =
        refl
    ; monotonicityChecked =
        true
    ; monotonicityCheckedIsTrue =
        refl
    ; criticalSeamTheoremProved =
        false
    ; criticalSeamTheoremProvedIsFalse =
        refl
    ; exactRemainingTheorem =
        Seam.missingDefectAdmissibilityHierarchyToParallelogram
    ; exactRemainingTheoremIsDefectAdmissibilityHierarchy =
        refl
    ; signaturePromoted =
        false
    ; signaturePromotedIsFalse =
        refl
    ; cliffordPromoted =
        false
    ; cliffordPromotedIsFalse =
        refl
    ; standardModelPromoted =
        false
    ; standardModelPromotedIsFalse =
        refl
    ; terminalUnificationPromoted =
        false
    ; terminalUnificationPromotedIsFalse =
        refl
    ; decisionNotes =
        "Identity dynamics inhabits DefectMonotonicityEvidence on the m=4 shift carrier."
        ∷ "The defect energy is definitionally the QP.Qhat-core of the projection-defect component D (PDzero) x."
        ∷ "Monotonicity along identity dynamics is checked by refl."
        ∷ "This does not prove CriticalSeamTheoremType; admissibility quotient and hierarchy consistency still have to force parallelogram/quadratic output."
        ∷ "Signature, Clifford, Standard Model, and terminal unification promotions remain false."
        ∷ []
    }

canonicalIdentityDynamicsInstanceRowCountIs6 :
  rowCount canonicalDefectCriticalSeamIdentityDynamicsInstance ≡ 6
canonicalIdentityDynamicsInstanceRowCountIs6 = refl

canonicalIdentityDynamicsMonotonicityChecked :
  monotonicityChecked canonicalDefectCriticalSeamIdentityDynamicsInstance
  ≡ true
canonicalIdentityDynamicsMonotonicityChecked = refl

canonicalIdentityDynamicsCriticalSeamStillOpen :
  criticalSeamTheoremProved canonicalDefectCriticalSeamIdentityDynamicsInstance
  ≡ false
canonicalIdentityDynamicsCriticalSeamStillOpen = refl

canonicalIdentityDynamicsSignaturePromotionFalse :
  signaturePromoted canonicalDefectCriticalSeamIdentityDynamicsInstance
  ≡ false
canonicalIdentityDynamicsSignaturePromotionFalse = refl

canonicalIdentityDynamicsCliffordPromotionFalse :
  cliffordPromoted canonicalDefectCriticalSeamIdentityDynamicsInstance
  ≡ false
canonicalIdentityDynamicsCliffordPromotionFalse = refl

canonicalIdentityDynamicsStandardModelPromotionFalse :
  standardModelPromoted canonicalDefectCriticalSeamIdentityDynamicsInstance
  ≡ false
canonicalIdentityDynamicsStandardModelPromotionFalse = refl

canonicalIdentityDynamicsTerminalPromotionFalse :
  terminalUnificationPromoted
    canonicalDefectCriticalSeamIdentityDynamicsInstance
  ≡ false
canonicalIdentityDynamicsTerminalPromotionFalse = refl
