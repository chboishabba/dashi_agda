module DASHI.Physics.Closure.DefectQuadraticParallelogramCriticalSeam where

-- Critical seam for the broad defect -> parallelogram -> quadratic route.
--
-- This module does not re-prove the existing shift-carrier theorem and does
-- not promote signature, Clifford, CCR, Standard Model, or terminal claims.
-- It packages the checked support already present in the repo and names the
-- exact first theorem still missing for the broader claim:
--
--   defect monotonicity
--   + admissibility quotient consistency
--   + hierarchy lift/project consistency
--   -> parallelogram identity
--   -> quadratic form.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Geometry.ProjectionDefect as PD
import DASHI.Geometry.ProjectionDefectToParallelogram as PDP
import DASHI.Geometry.QuadraticForm as QF
import DASHI.Physics.QuadraticEmergenceShiftInstance as QES
import DASHI.Physics.QuadraticPolarization as QP
import DASHI.Physics.Closure.ContractionForcesQuadraticStrong as CFQS
import DASHI.Physics.Closure.ContractionForcesQuadraticTheorem as CFQT
import DASHI.Promotion.DefectQuadraticClosureDependencyIndex as DQ

ParallelogramIdentityFor :
  ∀ {m : Nat} →
  QF.QuadraticForm
    (QES.AdditiveVecℤ {m})
    QES.ScalarFieldℤ →
  Set
ParallelogramIdentityFor {m} quadratic =
  ∀ x y →
    QF.ScalarField._+s_
      QES.ScalarFieldℤ
      (QF.QuadraticForm.Q quadratic
        (PD.Additive._+_ (QES.AdditiveVecℤ {m}) x y))
      (QF.QuadraticForm.Q quadratic
        (PD.Additive._+_
          (QES.AdditiveVecℤ {m})
          x
          (PD.Additive.-_ (QES.AdditiveVecℤ {m}) y)))
    ≡
    QF.ScalarField._+s_
      QES.ScalarFieldℤ
      (QF.ScalarField._+s_
        QES.ScalarFieldℤ
        (QF.QuadraticForm.Q quadratic x)
        (QF.QuadraticForm.Q quadratic x))
      (QF.ScalarField._+s_
        QES.ScalarFieldℤ
        (QF.QuadraticForm.Q quadratic y)
        (QF.QuadraticForm.Q quadratic y))

------------------------------------------------------------------------
-- General seam interfaces.  These are the theorem inputs that are not yet
-- inhabited for the intended real/operator carrier.

record DefectMonotonicityEvidence (m : Nat) : Setω where
  field
    dynamicsMap :
      PD.Additive.Carrier (QES.AdditiveVecℤ {m}) →
      PD.Additive.Carrier (QES.AdditiveVecℤ {m})

    defectEnergy :
      PD.Additive.Carrier (QES.AdditiveVecℤ {m}) →
      QF.ScalarField.S QES.ScalarFieldℤ

    defectEnergyIsProjectionDefectCore :
      ∀ x →
        defectEnergy x
        ≡
        QP.Q̂core
          (PD.ProjectionDefect.D (QES.PDzero {m}) x)

    monotoneAlongDynamics :
      ∀ x →
        defectEnergy (dynamicsMap x) ≡ defectEnergy x

record AdmissibilityQuotientConsistency (m : Nat) : Setω where
  field
    quotientCarrier :
      Set

    quotient :
      PD.Additive.Carrier (QES.AdditiveVecℤ {m}) →
      quotientCarrier

    quotientPreservesDefectEnergy :
      ∀ x y →
        quotient x ≡ quotient y →
        QP.Q̂core
          (PD.ProjectionDefect.D (QES.PDzero {m}) x)
        ≡
        QP.Q̂core
          (PD.ProjectionDefect.D (QES.PDzero {m}) y)

    quotientPreservesQuadraticEnergy :
      ∀ x y →
        quotient x ≡ quotient y →
        QP.Q̂core x ≡ QP.Q̂core y

record HierarchyLiftProjectConsistency (m : Nat) : Setω where
  field
    higherCarrier :
      Set

    lift :
      PD.Additive.Carrier (QES.AdditiveVecℤ {m}) →
      higherCarrier

    project :
      higherCarrier →
      PD.Additive.Carrier (QES.AdditiveVecℤ {m})

    projectAfterLift :
      ∀ x → project (lift x) ≡ x

    hierarchyPreservesQuadraticCore :
      ∀ x → QP.Q̂core (project (lift x)) ≡ QP.Q̂core x

record CriticalSeamTheoremOutput (m : Nat) : Setω where
  field
    projectionParallelogramPackage :
      PDP.ProjectionDefectParallelogramPackage
        (QES.AdditiveVecℤ {m})
        QES.ScalarFieldℤ

    quadraticWitness :
      PDP.ProjectionDefectQuadraticWitness
        (QES.AdditiveVecℤ {m})
        QES.ScalarFieldℤ

    parallelogramIdentity :
      ParallelogramIdentityFor
        (PDP.ProjectionDefectQuadraticWitness.quadratic quadraticWitness)

CriticalSeamTheoremType : Setω
CriticalSeamTheoremType =
  ∀ {m : Nat} →
  DefectMonotonicityEvidence m →
  AdmissibilityQuotientConsistency m →
  HierarchyLiftProjectConsistency m →
  CriticalSeamTheoremOutput m

criticalSeamTheoremTargetSurface : Setω
criticalSeamTheoremTargetSurface = CriticalSeamTheoremType

data CriticalSeamMissingTheorem : Set where
  missingDefectAdmissibilityHierarchyToParallelogram :
    CriticalSeamMissingTheorem

  missingRealAgreementUltrametric :
    CriticalSeamMissingTheorem

  missingRealOperatorStack :
    CriticalSeamMissingTheorem

  missingDownstreamSignatureCliffordSMTransfer :
    CriticalSeamMissingTheorem

data CriticalSeamStage : Set where
  shiftProjectionDefectChecked :
    CriticalSeamStage

  shiftParallelogramChecked :
    CriticalSeamStage

  shiftQuadraticWitnessChecked :
    CriticalSeamStage

  strongContractionSurfaceChecked :
    CriticalSeamStage

  generalCriticalSeamOpen :
    CriticalSeamStage

  downstreamPromotionBlocked :
    CriticalSeamStage

record CriticalSeamRow : Set where
  field
    stage :
      CriticalSeamStage

    modulePath :
      String

    artifact :
      String

    status :
      String

    promoted :
      Bool

    promotedIsFalse :
      promoted ≡ false

open CriticalSeamRow public

mkNonPromotingRow :
  CriticalSeamStage →
  String →
  String →
  String →
  CriticalSeamRow
mkNonPromotingRow stage modulePath artifact status =
  record
    { stage = stage
    ; modulePath = modulePath
    ; artifact = artifact
    ; status = status
    ; promoted = false
    ; promotedIsFalse = refl
    }

canonicalCriticalSeamRows :
  List CriticalSeamRow
canonicalCriticalSeamRows =
  mkNonPromotingRow
    shiftProjectionDefectChecked
    "DASHI.Promotion.DefectQuadraticClosureDependencyIndex"
    "canonicalProjectionDefect"
    "checked shift-carrier projection defect support"
  ∷ mkNonPromotingRow
    shiftParallelogramChecked
    "DASHI.Geometry.ProjectionDefectSplitForcesParallelogram"
    "projectionDefectParallelogramFromSplit"
    "checked integer shift-core parallelogram package"
  ∷ mkNonPromotingRow
    shiftQuadraticWitnessChecked
    "DASHI.Geometry.ProjectionDefectToParallelogram"
    "fromProjectionPackageWitness"
    "checked quadratic witness for the shift-carrier package"
  ∷ mkNonPromotingRow
    strongContractionSurfaceChecked
    "DASHI.Physics.Closure.ContractionForcesQuadraticStrong"
    "canonicalNontrivialInvariantStrong"
    "checked nontrivial strong package with invariance and normalization"
  ∷ mkNonPromotingRow
    generalCriticalSeamOpen
    "DASHI.Physics.Closure.DefectQuadraticParallelogramCriticalSeam"
    "CriticalSeamTheoremType"
    "open theorem: defect monotonicity plus quotient and hierarchy consistency must imply parallelogram/quadratic output"
  ∷ mkNonPromotingRow
    downstreamPromotionBlocked
    "DASHI.Promotion.DefectQuadraticClosureDependencyIndex"
    "signatureCliffordCCRPromoted"
    "signature, Clifford, CCR, SM, and terminal promotions remain false"
  ∷ []

------------------------------------------------------------------------
-- Concrete imported support.  This is the part that is actually checked.

record ShiftCarrierCriticalSeamSupport (m : Nat) : Setω where
  field
    dependencyIndex :
      DQ.DefectQuadraticClosureDependencyIndex

    projectionDefect :
      PD.ProjectionDefect (QES.AdditiveVecℤ {m})

    projectionParallelogramPackage :
      PDP.ProjectionDefectParallelogramPackage
        (QES.AdditiveVecℤ {m})
        QES.ScalarFieldℤ

    quadraticWitness :
      PDP.ProjectionDefectQuadraticWitness
        (QES.AdditiveVecℤ {m})
        QES.ScalarFieldℤ

    projectionQuadratic :
      QF.QuadraticForm
        (QES.AdditiveVecℤ {m})
        QES.ScalarFieldℤ

    strongPackage :
      CFQS.ContractionForcesQuadraticStrong

    theoremSurface :
      CFQT.ContractionForcesQuadraticTheorem

    parallelogramIdentity :
      ParallelogramIdentityFor projectionQuadratic

    quadraticWitnessNormalizesToProjectionQuadratic :
      ∀ x →
        QF.QuadraticForm.Q
          (PDP.ProjectionDefectQuadraticWitness.quadratic quadraticWitness)
          x
        ≡
        QF.QuadraticForm.Q projectionQuadratic x

open ShiftCarrierCriticalSeamSupport public

canonicalShiftCarrierCriticalSeamSupport :
  ∀ {m : Nat} → ShiftCarrierCriticalSeamSupport m
canonicalShiftCarrierCriticalSeamSupport {m} =
  record
    { dependencyIndex =
        DQ.canonicalDefectQuadraticClosureDependencyIndex
    ; projectionDefect =
        DQ.canonicalProjectionDefect {m}
    ; projectionParallelogramPackage =
        DQ.canonicalProjectionParallelogramPackage {m}
    ; quadraticWitness =
        DQ.canonicalProjectionQuadraticWitness {m}
    ; projectionQuadratic =
        DQ.canonicalProjectionQuadratic {m}
    ; strongPackage =
        DQ.canonicalStrongPackage
    ; theoremSurface =
        DQ.canonicalTheoremSurface
    ; parallelogramIdentity =
        QF.QuadraticForm.Parallelogram
          (DQ.canonicalProjectionQuadratic {m})
    ; quadraticWitnessNormalizesToProjectionQuadratic =
        λ _ → refl
    }

shiftSupportToTheoremOutput :
  ∀ {m : Nat} →
  ShiftCarrierCriticalSeamSupport m →
  CriticalSeamTheoremOutput m
shiftSupportToTheoremOutput support =
  record
    { projectionParallelogramPackage =
        ShiftCarrierCriticalSeamSupport.projectionParallelogramPackage support
    ; quadraticWitness =
        ShiftCarrierCriticalSeamSupport.quadraticWitness support
    ; parallelogramIdentity =
        QF.QuadraticForm.Parallelogram
          (PDP.ProjectionDefectQuadraticWitness.quadratic
            (ShiftCarrierCriticalSeamSupport.quadraticWitness support))
    }

------------------------------------------------------------------------
-- Critical seam ledger.  The checked shift support is present; the general
-- theorem and downstream physical promotions remain explicitly false.

record DefectQuadraticParallelogramCriticalSeam : Setω where
  field
    dependencyIndex :
      DQ.DefectQuadraticClosureDependencyIndex

    seamRows :
      List CriticalSeamRow

    seamRowCount :
      Nat

    seamRowCountIs6 :
      seamRowCount ≡ 6

    supportIndexRowCount :
      Nat

    supportIndexRowCountIs10 :
      supportIndexRowCount ≡
      DQ.supportRowCount dependencyIndex

    blockerIndexRowCount :
      Nat

    blockerIndexRowCountIs8 :
      blockerIndexRowCount ≡
      DQ.blockerRowCount dependencyIndex

    shiftCarrierSupport :
      ShiftCarrierCriticalSeamSupport 4

    shiftCarrierParallelogramChecked :
      Bool

    shiftCarrierParallelogramCheckedIsTrue :
      shiftCarrierParallelogramChecked ≡ true

    shiftCarrierQuadraticWitnessChecked :
      Bool

    shiftCarrierQuadraticWitnessCheckedIsTrue :
      shiftCarrierQuadraticWitnessChecked ≡ true

    criticalSeamTheoremTargetName :
      String

    criticalSeamTheoremTargetNamed :
      Bool

    criticalSeamTheoremTargetNamedIsTrue :
      criticalSeamTheoremTargetNamed ≡ true

    criticalSeamTheoremProved :
      Bool

    criticalSeamTheoremProvedIsFalse :
      criticalSeamTheoremProved ≡ false

    exactFirstMissingTheorem :
      CriticalSeamMissingTheorem

    exactFirstMissingTheoremIsDefectAdmissibilityHierarchy :
      exactFirstMissingTheorem
      ≡ missingDefectAdmissibilityHierarchyToParallelogram

    realAgreementUltrametricClosed :
      Bool

    realAgreementUltrametricClosedIsFalse :
      realAgreementUltrametricClosed ≡ false

    realOperatorStackClosed :
      Bool

    realOperatorStackClosedIsFalse :
      realOperatorStackClosed ≡ false

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

    nextTheoremStatement :
      String

    decisionNotes :
      List String

open DefectQuadraticParallelogramCriticalSeam public

canonicalDefectQuadraticParallelogramCriticalSeam :
  DefectQuadraticParallelogramCriticalSeam
canonicalDefectQuadraticParallelogramCriticalSeam =
  record
    { dependencyIndex =
        DQ.canonicalDefectQuadraticClosureDependencyIndex
    ; seamRows =
        canonicalCriticalSeamRows
    ; seamRowCount =
        6
    ; seamRowCountIs6 =
        refl
    ; supportIndexRowCount =
        10
    ; supportIndexRowCountIs10 =
        refl
    ; blockerIndexRowCount =
        8
    ; blockerIndexRowCountIs8 =
        refl
    ; shiftCarrierSupport =
        canonicalShiftCarrierCriticalSeamSupport {4}
    ; shiftCarrierParallelogramChecked =
        true
    ; shiftCarrierParallelogramCheckedIsTrue =
        refl
    ; shiftCarrierQuadraticWitnessChecked =
        true
    ; shiftCarrierQuadraticWitnessCheckedIsTrue =
        refl
    ; criticalSeamTheoremTargetName =
        "CriticalSeamTheoremType"
    ; criticalSeamTheoremTargetNamed =
        true
    ; criticalSeamTheoremTargetNamedIsTrue =
        refl
    ; criticalSeamTheoremProved =
        false
    ; criticalSeamTheoremProvedIsFalse =
        refl
    ; exactFirstMissingTheorem =
        missingDefectAdmissibilityHierarchyToParallelogram
    ; exactFirstMissingTheoremIsDefectAdmissibilityHierarchy =
        refl
    ; realAgreementUltrametricClosed =
        false
    ; realAgreementUltrametricClosedIsFalse =
        refl
    ; realOperatorStackClosed =
        false
    ; realOperatorStackClosedIsFalse =
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
    ; nextTheoremStatement =
        "prove CriticalSeamTheoremType: defect monotonicity plus admissibility quotient consistency plus hierarchy lift/project consistency implies a ProjectionDefectParallelogramPackage and QuadraticWitness"
    ; decisionNotes =
        "The checked positive support is the integer shift-carrier path: ProjectionDefect -> ProjectionDefectParallelogramPackage -> QuadraticForm."
        ∷ "The broader critical seam is not closed by the current support rows because the general defect-monotonicity, quotient, and hierarchy premises are still uninhabited."
        ∷ "The exact first missing theorem is missingDefectAdmissibilityHierarchyToParallelogram."
        ∷ "Signature, Clifford, Standard Model, and terminal unification promotion guards remain false here."
        ∷ []
    }

canonicalCriticalSeamRowCountIs6 :
  seamRowCount canonicalDefectQuadraticParallelogramCriticalSeam ≡ 6
canonicalCriticalSeamRowCountIs6 = refl

canonicalCriticalSeamFirstMissingTheorem :
  exactFirstMissingTheorem canonicalDefectQuadraticParallelogramCriticalSeam
  ≡ missingDefectAdmissibilityHierarchyToParallelogram
canonicalCriticalSeamFirstMissingTheorem = refl

canonicalCriticalSeamTheoremStillOpen :
  criticalSeamTheoremProved canonicalDefectQuadraticParallelogramCriticalSeam
  ≡ false
canonicalCriticalSeamTheoremStillOpen = refl

canonicalCriticalSeamSignaturePromotionFalse :
  signaturePromoted canonicalDefectQuadraticParallelogramCriticalSeam
  ≡ false
canonicalCriticalSeamSignaturePromotionFalse = refl

canonicalCriticalSeamCliffordPromotionFalse :
  cliffordPromoted canonicalDefectQuadraticParallelogramCriticalSeam
  ≡ false
canonicalCriticalSeamCliffordPromotionFalse = refl

canonicalCriticalSeamStandardModelPromotionFalse :
  standardModelPromoted canonicalDefectQuadraticParallelogramCriticalSeam
  ≡ false
canonicalCriticalSeamStandardModelPromotionFalse = refl

canonicalCriticalSeamTerminalPromotionFalse :
  terminalUnificationPromoted
    canonicalDefectQuadraticParallelogramCriticalSeam
  ≡ false
canonicalCriticalSeamTerminalPromotionFalse = refl
