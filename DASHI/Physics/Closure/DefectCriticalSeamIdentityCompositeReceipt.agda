module DASHI.Physics.Closure.DefectCriticalSeamIdentityCompositeReceipt where

-- Composite receipt for the concrete identity/shift critical-seam path.
--
-- This module combines the three checked m = 4 concrete receipts:
--
--   identity dynamics,
--   identity quotient/hierarchy,
--   concrete shift reducer.
--
-- It records that the concrete identity/shift premises and concrete output
-- are checked.  It does not inhabit the general CriticalSeamTheoremType and
-- does not promote signature, Clifford, Standard Model, or terminal claims.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.DefectCriticalSeamIdentityDynamicsInstance as Dyn
import DASHI.Physics.Closure.DefectCriticalSeamIdentityQuotientHierarchy as Quot
import DASHI.Physics.Closure.DefectCriticalSeamConcreteShiftReducer as Red
import DASHI.Physics.Closure.DefectQuadraticParallelogramCriticalSeam as Seam

data IdentityCompositeStage : Set where
  stageIdentityDynamicsReceiptLoaded :
    IdentityCompositeStage

  stageIdentityDynamicsMonotonicityChecked :
    IdentityCompositeStage

  stageIdentityQuotientHierarchyReceiptLoaded :
    IdentityCompositeStage

  stageIdentityQuotientHierarchyPremisesChecked :
    IdentityCompositeStage

  stageConcreteShiftReducerReceiptLoaded :
    IdentityCompositeStage

  stageConcreteShiftOutputChecked :
    IdentityCompositeStage

  stageConcreteM4CompositeClosed :
    IdentityCompositeStage

  stageGeneralCriticalSeamStillOpen :
    IdentityCompositeStage

  stageDownstreamPromotionStillBlocked :
    IdentityCompositeStage

record IdentityCompositeRow : Set where
  field
    stage :
      IdentityCompositeStage

    modulePath :
      String

    artifact :
      String

    status :
      String

    checked :
      Bool

    checkedIsTrue :
      checked ≡ true

    promotesGeneralTheorem :
      Bool

    promotesGeneralTheoremIsFalse :
      promotesGeneralTheorem ≡ false

open IdentityCompositeRow public

mkIdentityCompositeRow :
  IdentityCompositeStage →
  String →
  String →
  String →
  IdentityCompositeRow
mkIdentityCompositeRow stage modulePath artifact status =
  record
    { stage = stage
    ; modulePath = modulePath
    ; artifact = artifact
    ; status = status
    ; checked = true
    ; checkedIsTrue = refl
    ; promotesGeneralTheorem = false
    ; promotesGeneralTheoremIsFalse = refl
    }

canonicalIdentityCompositeRows :
  List IdentityCompositeRow
canonicalIdentityCompositeRows =
  mkIdentityCompositeRow
    stageIdentityDynamicsReceiptLoaded
    "DASHI.Physics.Closure.DefectCriticalSeamIdentityDynamicsInstance"
    "canonicalDefectCriticalSeamIdentityDynamicsInstance"
    "loads the checked identity dynamics receipt for the m=4 shift carrier"
  ∷ mkIdentityCompositeRow
    stageIdentityDynamicsMonotonicityChecked
    "DASHI.Physics.Closure.DefectCriticalSeamIdentityDynamicsInstance"
    "canonicalIdentityDefectMonotonicityEvidence4"
    "defect energy monotonicity along identity dynamics is inhabited by refl"
  ∷ mkIdentityCompositeRow
    stageIdentityQuotientHierarchyReceiptLoaded
    "DASHI.Physics.Closure.DefectCriticalSeamIdentityQuotientHierarchy"
    "canonicalDefectCriticalSeamIdentityQuotientHierarchy"
    "loads the checked identity quotient and identity hierarchy receipt"
  ∷ mkIdentityCompositeRow
    stageIdentityQuotientHierarchyPremisesChecked
    "DASHI.Physics.Closure.DefectCriticalSeamIdentityQuotientHierarchy"
    "identityAdmissibilityQuotientConsistency and identityHierarchyLiftProjectConsistency"
    "quotient preservation, project-after-lift, and hierarchy quadratic preservation are checked for m=4"
  ∷ mkIdentityCompositeRow
    stageConcreteShiftReducerReceiptLoaded
    "DASHI.Physics.Closure.DefectCriticalSeamConcreteShiftReducer"
    "canonicalDefectCriticalSeamConcreteShiftReducer"
    "loads the concrete reducer from canonical shift support to CriticalSeamTheoremOutput 4"
  ∷ mkIdentityCompositeRow
    stageConcreteShiftOutputChecked
    "DASHI.Physics.Closure.DefectCriticalSeamConcreteShiftReducer"
    "canonicalShift4CriticalSeamOutput"
    "projection package, quadratic witness, quadratic form, and parallelogram identity are exposed"
  ∷ mkIdentityCompositeRow
    stageConcreteM4CompositeClosed
    "DASHI.Physics.Closure.DefectCriticalSeamIdentityCompositeReceipt"
    "canonicalDefectCriticalSeamIdentityCompositeReceipt"
    "the concrete identity/shift m=4 premise-and-output bundle is checked"
  ∷ mkIdentityCompositeRow
    stageGeneralCriticalSeamStillOpen
    "DASHI.Physics.Closure.DefectQuadraticParallelogramCriticalSeam"
    "CriticalSeamTheoremType"
    "the general defect/admissibility/hierarchy to parallelogram theorem is not inhabited here"
  ∷ mkIdentityCompositeRow
    stageDownstreamPromotionStillBlocked
    "DASHI.Physics.Closure.DefectQuadraticParallelogramCriticalSeam"
    "missingDefectAdmissibilityHierarchyToParallelogram"
    "signature, Clifford, Standard Model, and terminal promotions remain blocked by the broad theorem"
  ∷ []

record DefectCriticalSeamIdentityCompositeReceipt : Setω where
  field
    identityDynamicsInstance :
      Dyn.DefectCriticalSeamIdentityDynamicsInstance

    identityQuotientHierarchy :
      Quot.DefectCriticalSeamIdentityQuotientHierarchy

    concreteShiftReducer :
      Red.DefectCriticalSeamConcreteShiftReducer

    compositeRows :
      List IdentityCompositeRow

    compositeRowCount :
      Nat

    compositeRowCountIs9 :
      compositeRowCount ≡ 9

    concreteDimension :
      Nat

    concreteDimensionIs4 :
      concreteDimension ≡ 4

    identityDynamicsReceiptChecked :
      Bool

    identityDynamicsReceiptCheckedIsTrue :
      identityDynamicsReceiptChecked ≡ true

    identityDynamicsMonotonicityChecked :
      Bool

    identityDynamicsMonotonicityCheckedIsTrue :
      identityDynamicsMonotonicityChecked ≡ true

    identityQuotientHierarchyChecked :
      Bool

    identityQuotientHierarchyCheckedIsTrue :
      identityQuotientHierarchyChecked ≡ true

    identityQuotientHierarchyPremisesChecked :
      Bool

    identityQuotientHierarchyPremisesCheckedIsTrue :
      identityQuotientHierarchyPremisesChecked ≡ true

    concreteShiftReducerChecked :
      Bool

    concreteShiftReducerCheckedIsTrue :
      concreteShiftReducerChecked ≡ true

    concreteShiftOutputChecked :
      Bool

    concreteShiftOutputCheckedIsTrue :
      concreteShiftOutputChecked ≡ true

    allConcreteIdentityShiftPremisesChecked :
      Bool

    allConcreteIdentityShiftPremisesCheckedIsTrue :
      allConcreteIdentityShiftPremisesChecked ≡ true

    concreteCriticalSeamOutput :
      Seam.CriticalSeamTheoremOutput 4

    concreteCriticalSeamOutputComesFromReducer :
      Bool

    concreteCriticalSeamOutputComesFromReducerIsTrue :
      concreteCriticalSeamOutputComesFromReducer ≡ true

    generalCriticalSeamTheoremProved :
      Bool

    generalCriticalSeamTheoremProvedIsFalse :
      generalCriticalSeamTheoremProved ≡ false

    criticalSeamTheoremTypeInhabitedHere :
      Bool

    criticalSeamTheoremTypeInhabitedHereIsFalse :
      criticalSeamTheoremTypeInhabitedHere ≡ false

    exactStillMissingTheorem :
      Seam.CriticalSeamMissingTheorem

    exactStillMissingTheoremIsDefectAdmissibilityHierarchy :
      exactStillMissingTheorem
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

open DefectCriticalSeamIdentityCompositeReceipt public

canonicalDefectCriticalSeamIdentityCompositeReceipt :
  DefectCriticalSeamIdentityCompositeReceipt
canonicalDefectCriticalSeamIdentityCompositeReceipt =
  record
    { identityDynamicsInstance =
        Dyn.canonicalDefectCriticalSeamIdentityDynamicsInstance
    ; identityQuotientHierarchy =
        Quot.canonicalDefectCriticalSeamIdentityQuotientHierarchy
    ; concreteShiftReducer =
        Red.canonicalDefectCriticalSeamConcreteShiftReducer
    ; compositeRows =
        canonicalIdentityCompositeRows
    ; compositeRowCount =
        9
    ; compositeRowCountIs9 =
        refl
    ; concreteDimension =
        4
    ; concreteDimensionIs4 =
        refl
    ; identityDynamicsReceiptChecked =
        true
    ; identityDynamicsReceiptCheckedIsTrue =
        refl
    ; identityDynamicsMonotonicityChecked =
        true
    ; identityDynamicsMonotonicityCheckedIsTrue =
        refl
    ; identityQuotientHierarchyChecked =
        true
    ; identityQuotientHierarchyCheckedIsTrue =
        refl
    ; identityQuotientHierarchyPremisesChecked =
        true
    ; identityQuotientHierarchyPremisesCheckedIsTrue =
        refl
    ; concreteShiftReducerChecked =
        true
    ; concreteShiftReducerCheckedIsTrue =
        refl
    ; concreteShiftOutputChecked =
        true
    ; concreteShiftOutputCheckedIsTrue =
        refl
    ; allConcreteIdentityShiftPremisesChecked =
        true
    ; allConcreteIdentityShiftPremisesCheckedIsTrue =
        refl
    ; concreteCriticalSeamOutput =
        Red.canonicalShift4CriticalSeamOutput
    ; concreteCriticalSeamOutputComesFromReducer =
        true
    ; concreteCriticalSeamOutputComesFromReducerIsTrue =
        refl
    ; generalCriticalSeamTheoremProved =
        false
    ; generalCriticalSeamTheoremProvedIsFalse =
        refl
    ; criticalSeamTheoremTypeInhabitedHere =
        false
    ; criticalSeamTheoremTypeInhabitedHereIsFalse =
        refl
    ; exactStillMissingTheorem =
        Seam.missingDefectAdmissibilityHierarchyToParallelogram
    ; exactStillMissingTheoremIsDefectAdmissibilityHierarchy =
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
        "This composite combines the identity dynamics, identity quotient/hierarchy, and concrete shift reducer receipts."
        ∷ "All concrete identity/shift premises and the concrete CriticalSeamTheoremOutput 4 are checked."
        ∷ "The checked composite is an m=4 identity/shift instance, not CriticalSeamTheoremType."
        ∷ "The exact remaining theorem is missingDefectAdmissibilityHierarchyToParallelogram."
        ∷ "Signature, Clifford, Standard Model, and terminal unification promotion guards remain false."
        ∷ []
    }

canonicalIdentityCompositeRowCountIs9 :
  compositeRowCount canonicalDefectCriticalSeamIdentityCompositeReceipt
  ≡ 9
canonicalIdentityCompositeRowCountIs9 = refl

canonicalIdentityCompositeDimensionIs4 :
  concreteDimension canonicalDefectCriticalSeamIdentityCompositeReceipt
  ≡ 4
canonicalIdentityCompositeDimensionIs4 = refl

canonicalIdentityCompositeAllConcretePremisesChecked :
  allConcreteIdentityShiftPremisesChecked
    canonicalDefectCriticalSeamIdentityCompositeReceipt
  ≡ true
canonicalIdentityCompositeAllConcretePremisesChecked = refl

canonicalIdentityCompositeOutputComesFromReducer :
  concreteCriticalSeamOutputComesFromReducer
    canonicalDefectCriticalSeamIdentityCompositeReceipt
  ≡ true
canonicalIdentityCompositeOutputComesFromReducer = refl

canonicalIdentityCompositeGeneralTheoremStillOpen :
  generalCriticalSeamTheoremProved
    canonicalDefectCriticalSeamIdentityCompositeReceipt
  ≡ false
canonicalIdentityCompositeGeneralTheoremStillOpen = refl

canonicalIdentityCompositeTheoremTypeNotInhabitedHere :
  criticalSeamTheoremTypeInhabitedHere
    canonicalDefectCriticalSeamIdentityCompositeReceipt
  ≡ false
canonicalIdentityCompositeTheoremTypeNotInhabitedHere = refl

canonicalIdentityCompositeExactMissingTheorem :
  exactStillMissingTheorem
    canonicalDefectCriticalSeamIdentityCompositeReceipt
  ≡ Seam.missingDefectAdmissibilityHierarchyToParallelogram
canonicalIdentityCompositeExactMissingTheorem = refl

canonicalIdentityCompositeSignaturePromotionFalse :
  signaturePromoted canonicalDefectCriticalSeamIdentityCompositeReceipt
  ≡ false
canonicalIdentityCompositeSignaturePromotionFalse = refl

canonicalIdentityCompositeCliffordPromotionFalse :
  cliffordPromoted canonicalDefectCriticalSeamIdentityCompositeReceipt
  ≡ false
canonicalIdentityCompositeCliffordPromotionFalse = refl

canonicalIdentityCompositeStandardModelPromotionFalse :
  standardModelPromoted canonicalDefectCriticalSeamIdentityCompositeReceipt
  ≡ false
canonicalIdentityCompositeStandardModelPromotionFalse = refl

canonicalIdentityCompositeTerminalPromotionFalse :
  terminalUnificationPromoted
    canonicalDefectCriticalSeamIdentityCompositeReceipt
  ≡ false
canonicalIdentityCompositeTerminalPromotionFalse = refl
