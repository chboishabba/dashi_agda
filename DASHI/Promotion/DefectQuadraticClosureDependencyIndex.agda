module DASHI.Promotion.DefectQuadraticClosureDependencyIndex where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Geometry.ProjectionDefect as PD
import DASHI.Geometry.ProjectionDefectSplitForcesParallelogram as PDSP
import DASHI.Geometry.ProjectionDefectToParallelogram as PDP
import DASHI.Geometry.QuadraticForm as QF
import DASHI.Physics.ContractionQuadraticBridge as CQB
import DASHI.Physics.Closure.ContractionForcesQuadraticStrong as CFQS
import DASHI.Physics.Closure.ContractionForcesQuadraticTheorem as CFQT
import DASHI.Physics.QuadraticEmergenceShiftInstance as QES
import DASHI.Physics.QuadraticPolarization as QP

------------------------------------------------------------------------
-- Defect -> parallelogram -> quadratic closure dependency index.
--
-- This module is intentionally disjoint from the proof owners.  It records
-- the current checked spine and the remaining blockers for the broader
-- "defect monotonicity + admissibility quotient + hierarchy consistency
-- forces parallelogram/quadratic" claim.  It does not change any existing
-- proof module and it does not promote Clifford, CCR, SM, or terminal claims.

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data DependencyStatus : Set where
  internallyInhabited :
    DependencyStatus

  scopedCanonicalSurface :
    DependencyStatus

  residualBlocker :
    DependencyStatus

data ExactSupportLemma : Set where
  projectionDefectRecord :
    ExactSupportLemma

  shiftProjectionDefect :
    ExactSupportLemma

  integerVectorParallelogram :
    ExactSupportLemma

  projectionDefectSplitParallelogram :
    ExactSupportLemma

  projectionDefectEnergySplit :
    ExactSupportLemma

  projectionDefectParallelogramPackage :
    ExactSupportLemma

  projectionPackageQuadraticWitness :
    ExactSupportLemma

  contractionProjectionOrthogonalityBridge :
    ExactSupportLemma

  strongContractionQuadraticPackage :
    ExactSupportLemma

  canonicalContractionQuadraticTheorem :
    ExactSupportLemma

data ClosureBlocker : Set where
  realAgreementUltrametricBlocker :
    ClosureBlocker

  realOperatorStackBlocker :
    ClosureBlocker

  defectMonotonicityForGeneralCarrierBlocker :
    ClosureBlocker

  admissibilityQuotientConsistencyBlocker :
    ClosureBlocker

  hierarchyConsistencyToParallelogramBlocker :
    ClosureBlocker

  strictContractionToProjectionDefectPackageBlocker :
    ClosureBlocker

  generalParallelogramForNonShiftCarrierBlocker :
    ClosureBlocker

  signatureCliffordCCRPromotionBlocker :
    ClosureBlocker

record SupportRow : Set where
  field
    supportLemma :
      ExactSupportLemma

    status :
      DependencyStatus

    modulePath :
      String

    exportedName :
      String

    role :
      String

open SupportRow public

record BlockerRow : Set where
  field
    blocker :
      ClosureBlocker

    status :
      DependencyStatus

    missingArtifact :
      String

    promotionAffected :
      String

    promoted :
      Bool

    promotedIsFalse :
      promoted ≡ false

open BlockerRow public

mkSupportRow :
  ExactSupportLemma →
  DependencyStatus →
  String →
  String →
  String →
  SupportRow
mkSupportRow lemma status modulePath exportedName role =
  record
    { supportLemma = lemma
    ; status = status
    ; modulePath = modulePath
    ; exportedName = exportedName
    ; role = role
    }

mkBlockerRow :
  ClosureBlocker →
  String →
  String →
  BlockerRow
mkBlockerRow blocker missing affected =
  record
    { blocker = blocker
    ; status = residualBlocker
    ; missingArtifact = missing
    ; promotionAffected = affected
    ; promoted = false
    ; promotedIsFalse = refl
    }

canonicalSupportRows :
  List SupportRow
canonicalSupportRows =
  mkSupportRow
    projectionDefectRecord
    internallyInhabited
    "DASHI.Geometry.ProjectionDefect"
    "ProjectionDefect"
    "base record with P, D, D-def, idempotence, and Orth-PD fields"
  ∷ mkSupportRow
    shiftProjectionDefect
    internallyInhabited
    "DASHI.Physics.QuadraticEmergenceShiftInstance"
    "PDzero"
    "inhabited shift-carrier projection-defect instance"
  ∷ mkSupportRow
    integerVectorParallelogram
    internallyInhabited
    "DASHI.Physics.QuadraticEmergenceShiftInstance"
    "parallelogramQ̂core"
    "integer-vector sum-of-squares parallelogram law"
  ∷ mkSupportRow
    projectionDefectSplitParallelogram
    internallyInhabited
    "DASHI.Geometry.ProjectionDefectSplitForcesParallelogram"
    "projectionDefectSplitForcesParallelogram"
    "canonical split-regime route from projection defect to parallelogram"
  ∷ mkSupportRow
    projectionDefectEnergySplit
    internallyInhabited
    "DASHI.Geometry.ProjectionDefectSplitForcesParallelogram"
    "projectionDefectEnergySplit"
    "energy split across P and D for the shift projection"
  ∷ mkSupportRow
    projectionDefectParallelogramPackage
    internallyInhabited
    "DASHI.Geometry.ProjectionDefectSplitForcesParallelogram"
    "projectionDefectParallelogramFromSplit"
    "package carrying projection, emergence axioms, parallelogram, and split"
  ∷ mkSupportRow
    projectionPackageQuadraticWitness
    internallyInhabited
    "DASHI.Geometry.ProjectionDefectToParallelogram"
    "fromProjectionPackageWitness"
    "turns the package into a QuadraticForm witness"
  ∷ mkSupportRow
    contractionProjectionOrthogonalityBridge
    scopedCanonicalSurface
    "DASHI.Physics.ContractionQuadraticBridge"
    "contractionProjectionOrthogonality⇒quadratic"
    "strict contraction plus projection-defect package yields abstract quadratic output"
  ∷ mkSupportRow
    strongContractionQuadraticPackage
    internallyInhabited
    "DASHI.Physics.Closure.ContractionForcesQuadraticStrong"
    "canonicalNontrivialInvariantStrong"
    "nontrivial signed-permutation strong package with invariance and uniqueness witnesses"
  ∷ mkSupportRow
    canonicalContractionQuadraticTheorem
    scopedCanonicalSurface
    "DASHI.Physics.Closure.ContractionForcesQuadraticTheorem"
    "canonicalRealStackContractionForcesQuadraticTheorem"
    "theorem surface transporting the strong package into canonical quadratic/signature boundary"
  ∷ []

canonicalBlockerRows :
  List BlockerRow
canonicalBlockerRows =
  mkBlockerRow
    realAgreementUltrametricBlocker
    "inhabited AgreementUltrametric over the intended real/operator carrier"
    "real-stack contraction-to-quadratic promotion"
  ∷ mkBlockerRow
    realOperatorStackBlocker
    "inhabited RealOperatorStack tying the abstract carrier to analytic operators"
    "physics bridge and metrology promotion"
  ∷ mkBlockerRow
    defectMonotonicityForGeneralCarrierBlocker
    "proof that the projection defect is monotone under the intended contraction dynamics"
    "defect-monotonicity to parallelogram closure"
  ∷ mkBlockerRow
    admissibilityQuotientConsistencyBlocker
    "proof that the admissibility quotient preserves defect, shell, and energy witnesses"
    "admissibility quotient closure"
  ∷ mkBlockerRow
    hierarchyConsistencyToParallelogramBlocker
    "proof that hierarchy lift/project consistency forces the parallelogram law"
    "hierarchy-to-quadratic closure"
  ∷ mkBlockerRow
    strictContractionToProjectionDefectPackageBlocker
    "constructor from a strict contraction alone to the projection-defect parallelogram package"
    "unqualified contraction-forces-quadratic theorem"
  ∷ mkBlockerRow
    generalParallelogramForNonShiftCarrierBlocker
    "general-carrier parallelogram proof beyond the current integer shift-core instance"
    "full carrier-independent quadratic emergence"
  ∷ mkBlockerRow
    signatureCliffordCCRPromotionBlocker
    "downstream derivation from quadratic output to forced signature, Clifford, Dirac, CCR, and SM gates"
    "terminal physics promotion"
  ∷ []

------------------------------------------------------------------------
-- Typed bindings to the exact existing support.

canonicalProjectionDefect :
  ∀ {m : Nat} →
  PD.ProjectionDefect (QES.AdditiveVecℤ {m})
canonicalProjectionDefect {m} =
  QES.PDzero {m}

canonicalProjectionParallelogramPackage :
  ∀ {m : Nat} →
  PDP.ProjectionDefectParallelogramPackage
    (QES.AdditiveVecℤ {m})
    QES.ScalarFieldℤ
canonicalProjectionParallelogramPackage {m} =
  PDSP.projectionDefectParallelogramFromSplit {m}

canonicalProjectionQuadratic :
  ∀ {m : Nat} →
  QF.QuadraticForm
    (QES.AdditiveVecℤ {m})
    QES.ScalarFieldℤ
canonicalProjectionQuadratic {m} =
  QES.quadraticShift {m}

canonicalProjectionQuadraticWitness :
  ∀ {m : Nat} →
  PDP.ProjectionDefectQuadraticWitness
    (QES.AdditiveVecℤ {m})
    QES.ScalarFieldℤ
canonicalProjectionQuadraticWitness {m} =
  PDP.fromProjectionPackageWitness
    (QES.AdditiveVecℤ {m})
    QES.ScalarFieldℤ
    (canonicalProjectionParallelogramPackage {m})

canonicalStrongPackage :
  CFQS.ContractionForcesQuadraticStrong
canonicalStrongPackage =
  CFQS.canonicalNontrivialInvariantStrong

canonicalTheoremSurface :
  CFQT.ContractionForcesQuadraticTheorem
canonicalTheoremSurface =
  CFQT.canonicalRealStackContractionForcesQuadraticTheorem

canonicalTheoremAtDimension :
  Nat →
  CFQT.ContractionForcesQuadraticTheorem
canonicalTheoremAtDimension =
  CFQT.canonicalContractionForcesQuadraticTheorem

canonicalStrongNormalization :
  ∀ x →
    QF.QuadraticForm.Q
      (CFQS.ContractionForcesQuadraticStrong.derivedQuadratic
        canonicalStrongPackage)
      x
    ≡
    QP.Q̂core x
canonicalStrongNormalization =
  CFQS.uniqueUpToScaleWitness canonicalStrongPackage

record DefectQuadraticClosureDependencyIndex : Setω where
  field
    supportRows :
      List SupportRow

    blockerRows :
      List BlockerRow

    supportRowCount :
      Nat

    supportRowCountIs10 :
      supportRowCount ≡ listLength supportRows

    blockerRowCount :
      Nat

    blockerRowCountIs8 :
      blockerRowCount ≡ listLength blockerRows

    projectionDefectSupportPresent :
      Bool

    projectionDefectSupportPresentIsTrue :
      projectionDefectSupportPresent ≡ true

    parallelogramSupportPresent :
      Bool

    parallelogramSupportPresentIsTrue :
      parallelogramSupportPresent ≡ true

    quadraticWitnessSupportPresent :
      Bool

    quadraticWitnessSupportPresentIsTrue :
      quadraticWitnessSupportPresent ≡ true

    strongContractionQuadraticSurfacePresent :
      Bool

    strongContractionQuadraticSurfacePresentIsTrue :
      strongContractionQuadraticSurfacePresent ≡ true

    realAgreementUltrametricClosed :
      Bool

    realAgreementUltrametricClosedIsFalse :
      realAgreementUltrametricClosed ≡ false

    realOperatorStackClosed :
      Bool

    realOperatorStackClosedIsFalse :
      realOperatorStackClosed ≡ false

    defectMonotonicityClosed :
      Bool

    defectMonotonicityClosedIsFalse :
      defectMonotonicityClosed ≡ false

    admissibilityQuotientClosed :
      Bool

    admissibilityQuotientClosedIsFalse :
      admissibilityQuotientClosed ≡ false

    hierarchyConsistencyClosed :
      Bool

    hierarchyConsistencyClosedIsFalse :
      hierarchyConsistencyClosed ≡ false

    strictContractionAloneForcesQuadratic :
      Bool

    strictContractionAloneForcesQuadraticIsFalse :
      strictContractionAloneForcesQuadratic ≡ false

    signatureCliffordCCRPromoted :
      Bool

    signatureCliffordCCRPromotedIsFalse :
      signatureCliffordCCRPromoted ≡ false

    terminalUnificationPromoted :
      Bool

    terminalUnificationPromotedIsFalse :
      terminalUnificationPromoted ≡ false

    checkedProjectionDefect :
      ∀ {m : Nat} →
      PD.ProjectionDefect (QES.AdditiveVecℤ {m})

    checkedProjectionParallelogramPackage :
      ∀ {m : Nat} →
      PDP.ProjectionDefectParallelogramPackage
        (QES.AdditiveVecℤ {m})
        QES.ScalarFieldℤ

    checkedProjectionQuadratic :
      ∀ {m : Nat} →
      QF.QuadraticForm
        (QES.AdditiveVecℤ {m})
        QES.ScalarFieldℤ

    checkedStrongPackage :
      CFQS.ContractionForcesQuadraticStrong

    checkedTheoremSurface :
      CFQT.ContractionForcesQuadraticTheorem

    decisionNotes :
      List String

open DefectQuadraticClosureDependencyIndex public

canonicalDefectQuadraticClosureDependencyIndex :
  DefectQuadraticClosureDependencyIndex
canonicalDefectQuadraticClosureDependencyIndex =
  record
    { supportRows =
        canonicalSupportRows
    ; blockerRows =
        canonicalBlockerRows
    ; supportRowCount =
        10
    ; supportRowCountIs10 =
        refl
    ; blockerRowCount =
        8
    ; blockerRowCountIs8 =
        refl
    ; projectionDefectSupportPresent =
        true
    ; projectionDefectSupportPresentIsTrue =
        refl
    ; parallelogramSupportPresent =
        true
    ; parallelogramSupportPresentIsTrue =
        refl
    ; quadraticWitnessSupportPresent =
        true
    ; quadraticWitnessSupportPresentIsTrue =
        refl
    ; strongContractionQuadraticSurfacePresent =
        true
    ; strongContractionQuadraticSurfacePresentIsTrue =
        refl
    ; realAgreementUltrametricClosed =
        false
    ; realAgreementUltrametricClosedIsFalse =
        refl
    ; realOperatorStackClosed =
        false
    ; realOperatorStackClosedIsFalse =
        refl
    ; defectMonotonicityClosed =
        false
    ; defectMonotonicityClosedIsFalse =
        refl
    ; admissibilityQuotientClosed =
        false
    ; admissibilityQuotientClosedIsFalse =
        refl
    ; hierarchyConsistencyClosed =
        false
    ; hierarchyConsistencyClosedIsFalse =
        refl
    ; strictContractionAloneForcesQuadratic =
        false
    ; strictContractionAloneForcesQuadraticIsFalse =
        refl
    ; signatureCliffordCCRPromoted =
        false
    ; signatureCliffordCCRPromotedIsFalse =
        refl
    ; terminalUnificationPromoted =
        false
    ; terminalUnificationPromotedIsFalse =
        refl
    ; checkedProjectionDefect =
        canonicalProjectionDefect
    ; checkedProjectionParallelogramPackage =
        canonicalProjectionParallelogramPackage
    ; checkedProjectionQuadratic =
        canonicalProjectionQuadratic
    ; checkedStrongPackage =
        canonicalStrongPackage
    ; checkedTheoremSurface =
        canonicalTheoremSurface
    ; decisionNotes =
        "current closed spine is ProjectionDefect -> ProjectionDefectParallelogramPackage -> QuadraticForm on the integer shift carrier"
        ∷ "ContractionQuadraticBridge requires both a strict contraction and a projection-defect/parallelogram package; it does not derive that package from contraction alone"
        ∷ "ContractionForcesQuadraticStrong is inhabited for identity and nontrivial signed-permutation dynamics with explicit invariance and uniqueness witnesses"
        ∷ "the broader defect-monotonicity/admissibility-quotient/hierarchy-consistency route remains the exact blocker before claiming general quadratic emergence"
        ∷ "signature, Clifford, CCR, SM, and terminal unification promotions remain false in this index"
        ∷ []
    }

canonicalDefectQuadraticSupportRowCountIs10 :
  supportRowCount canonicalDefectQuadraticClosureDependencyIndex ≡ 10
canonicalDefectQuadraticSupportRowCountIs10 = refl

canonicalDefectQuadraticBlockerRowCountIs8 :
  blockerRowCount canonicalDefectQuadraticClosureDependencyIndex ≡ 8
canonicalDefectQuadraticBlockerRowCountIs8 = refl

canonicalDefectQuadraticTerminalPromotionIsFalse :
  terminalUnificationPromoted canonicalDefectQuadraticClosureDependencyIndex
    ≡ false
canonicalDefectQuadraticTerminalPromotionIsFalse = refl

