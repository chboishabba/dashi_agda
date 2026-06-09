module DASHI.Physics.Closure.DefectCriticalSeamConcreteShiftReducer where

-- Concrete reducer for the checked integer shift-carrier seam.
--
-- This module does one narrow thing: it applies the already checked
-- `shiftSupportToTheoremOutput` reducer to the canonical m = 4 shift support.
-- It therefore produces a concrete `CriticalSeamTheoremOutput 4`.
--
-- It does not inhabit the general `CriticalSeamTheoremType`, and it does not
-- promote signature, Clifford, SM, or terminal unification.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Geometry.ProjectionDefect as PD
import DASHI.Geometry.ProjectionDefectToParallelogram as PDP
import DASHI.Geometry.QuadraticForm as QF
import DASHI.Physics.QuadraticEmergenceShiftInstance as QES
import DASHI.Physics.Closure.DefectQuadraticParallelogramCriticalSeam as Seam
import DASHI.Promotion.DefectQuadraticClosureDependencyIndex as DQ

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data ConcreteShiftReducerStage : Set where
  canonicalShiftSupportLoaded :
    ConcreteShiftReducerStage

  supportReducedToCriticalOutput :
    ConcreteShiftReducerStage

  outputProjectionPackageExposed :
    ConcreteShiftReducerStage

  outputQuadraticWitnessExposed :
    ConcreteShiftReducerStage

  outputParallelogramIdentityExposed :
    ConcreteShiftReducerStage

  generalTheoremAndPromotionHeld :
    ConcreteShiftReducerStage

record ConcreteShiftReducerRow : Set where
  field
    stage :
      ConcreteShiftReducerStage

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

open ConcreteShiftReducerRow public

mkConcreteShiftReducerRow :
  ConcreteShiftReducerStage →
  String →
  String →
  String →
  ConcreteShiftReducerRow
mkConcreteShiftReducerRow stage modulePath artifact status =
  record
    { stage = stage
    ; modulePath = modulePath
    ; artifact = artifact
    ; status = status
    ; promoted = false
    ; promotedIsFalse = refl
    }

canonicalConcreteShiftReducerRows :
  List ConcreteShiftReducerRow
canonicalConcreteShiftReducerRows =
  mkConcreteShiftReducerRow
    canonicalShiftSupportLoaded
    "DASHI.Physics.Closure.DefectQuadraticParallelogramCriticalSeam"
    "canonicalShiftCarrierCriticalSeamSupport {4}"
    "loads the checked m=4 integer shift-carrier projection/parallelogram/quadratic support"
  ∷ mkConcreteShiftReducerRow
    supportReducedToCriticalOutput
    "DASHI.Physics.Closure.DefectQuadraticParallelogramCriticalSeam"
    "shiftSupportToTheoremOutput"
    "reduces the checked shift support to a concrete CriticalSeamTheoremOutput 4"
  ∷ mkConcreteShiftReducerRow
    outputProjectionPackageExposed
    "DASHI.Geometry.ProjectionDefectToParallelogram"
    "ProjectionDefectParallelogramPackage"
    "exposes the output projection-defect parallelogram package"
  ∷ mkConcreteShiftReducerRow
    outputQuadraticWitnessExposed
    "DASHI.Geometry.ProjectionDefectToParallelogram"
    "ProjectionDefectQuadraticWitness"
    "exposes the output quadratic witness"
  ∷ mkConcreteShiftReducerRow
    outputParallelogramIdentityExposed
    "DASHI.Physics.Closure.DefectQuadraticParallelogramCriticalSeam"
    "ParallelogramIdentityFor"
    "exposes the output parallelogram identity for the shift quadratic"
  ∷ mkConcreteShiftReducerRow
    generalTheoremAndPromotionHeld
    "DASHI.Physics.Closure.DefectCriticalSeamConcreteShiftReducer"
    "generalCriticalSeamTheoremPromoted"
    "the concrete m=4 reducer does not inhabit CriticalSeamTheoremType and does not promote downstream physics"
  ∷ []

canonicalShift4Support :
  Seam.ShiftCarrierCriticalSeamSupport 4
canonicalShift4Support =
  Seam.canonicalShiftCarrierCriticalSeamSupport {4}

canonicalShift4CriticalSeamOutput :
  Seam.CriticalSeamTheoremOutput 4
canonicalShift4CriticalSeamOutput =
  Seam.shiftSupportToTheoremOutput canonicalShift4Support

canonicalShift4ProjectionParallelogramPackage :
  PDP.ProjectionDefectParallelogramPackage
    (QES.AdditiveVecℤ {4})
    QES.ScalarFieldℤ
canonicalShift4ProjectionParallelogramPackage =
  Seam.CriticalSeamTheoremOutput.projectionParallelogramPackage
    canonicalShift4CriticalSeamOutput

canonicalShift4QuadraticWitness :
  PDP.ProjectionDefectQuadraticWitness
    (QES.AdditiveVecℤ {4})
    QES.ScalarFieldℤ
canonicalShift4QuadraticWitness =
  Seam.CriticalSeamTheoremOutput.quadraticWitness
    canonicalShift4CriticalSeamOutput

canonicalShift4OutputQuadratic :
  QF.QuadraticForm
    (QES.AdditiveVecℤ {4})
    QES.ScalarFieldℤ
canonicalShift4OutputQuadratic =
  PDP.ProjectionDefectQuadraticWitness.quadratic
    canonicalShift4QuadraticWitness

canonicalShift4ParallelogramIdentity :
  Seam.ParallelogramIdentityFor canonicalShift4OutputQuadratic
canonicalShift4ParallelogramIdentity =
  Seam.CriticalSeamTheoremOutput.parallelogramIdentity
    canonicalShift4CriticalSeamOutput

canonicalShift4OutputPackageIsSupportPackage :
  canonicalShift4ProjectionParallelogramPackage
  ≡
  Seam.ShiftCarrierCriticalSeamSupport.projectionParallelogramPackage
    canonicalShift4Support
canonicalShift4OutputPackageIsSupportPackage = refl

canonicalShift4OutputWitnessIsSupportWitness :
  canonicalShift4QuadraticWitness
  ≡
  Seam.ShiftCarrierCriticalSeamSupport.quadraticWitness
    canonicalShift4Support
canonicalShift4OutputWitnessIsSupportWitness = refl

record DefectCriticalSeamConcreteShiftReducer : Setω where
  field
    dependencyIndex :
      DQ.DefectQuadraticClosureDependencyIndex

    criticalSeam :
      Seam.DefectQuadraticParallelogramCriticalSeam

    reducerRows :
      List ConcreteShiftReducerRow

    reducerRowCount :
      Nat

    reducerRowCountIs6 :
      reducerRowCount ≡ listLength reducerRows

    shiftDimension :
      Nat

    shiftDimensionIs4 :
      shiftDimension ≡ 4

    shiftSupport :
      Seam.ShiftCarrierCriticalSeamSupport 4

    reducedOutput :
      Seam.CriticalSeamTheoremOutput 4

    outputProjectionPackage :
      PDP.ProjectionDefectParallelogramPackage
        (QES.AdditiveVecℤ {4})
        QES.ScalarFieldℤ

    outputProjectionPackageIsReducedOutputPackage :
      outputProjectionPackage
      ≡
      Seam.CriticalSeamTheoremOutput.projectionParallelogramPackage
        reducedOutput

    reducedOutputPackageIsSupportPackage :
      Seam.CriticalSeamTheoremOutput.projectionParallelogramPackage
        reducedOutput
      ≡
      Seam.ShiftCarrierCriticalSeamSupport.projectionParallelogramPackage
        shiftSupport

    outputQuadraticWitness :
      PDP.ProjectionDefectQuadraticWitness
        (QES.AdditiveVecℤ {4})
        QES.ScalarFieldℤ

    outputQuadraticWitnessIsReducedOutputWitness :
      outputQuadraticWitness
      ≡
      Seam.CriticalSeamTheoremOutput.quadraticWitness reducedOutput

    reducedOutputWitnessIsSupportWitness :
      Seam.CriticalSeamTheoremOutput.quadraticWitness reducedOutput
      ≡
      Seam.ShiftCarrierCriticalSeamSupport.quadraticWitness shiftSupport

    outputQuadratic :
      QF.QuadraticForm
        (QES.AdditiveVecℤ {4})
        QES.ScalarFieldℤ

    outputQuadraticIsWitnessQuadratic :
      outputQuadratic
      ≡
      PDP.ProjectionDefectQuadraticWitness.quadratic
        outputQuadraticWitness

    outputParallelogramIdentity :
      Seam.ParallelogramIdentityFor outputQuadratic

    concreteShiftOutputCalculated :
      Bool

    concreteShiftOutputCalculatedIsTrue :
      concreteShiftOutputCalculated ≡ true

    generalCriticalSeamTheoremPromoted :
      Bool

    generalCriticalSeamTheoremPromotedIsFalse :
      generalCriticalSeamTheoremPromoted ≡ false

    criticalSeamTheoremTypeInhabitedHere :
      Bool

    criticalSeamTheoremTypeInhabitedHereIsFalse :
      criticalSeamTheoremTypeInhabitedHere ≡ false

    exactFirstMissingTheorem :
      Seam.CriticalSeamMissingTheorem

    exactFirstMissingTheoremIsGeneralSeam :
      exactFirstMissingTheorem
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

open DefectCriticalSeamConcreteShiftReducer public

canonicalDefectCriticalSeamConcreteShiftReducer :
  DefectCriticalSeamConcreteShiftReducer
canonicalDefectCriticalSeamConcreteShiftReducer =
  record
    { dependencyIndex =
        DQ.canonicalDefectQuadraticClosureDependencyIndex
    ; criticalSeam =
        Seam.canonicalDefectQuadraticParallelogramCriticalSeam
    ; reducerRows =
        canonicalConcreteShiftReducerRows
    ; reducerRowCount =
        6
    ; reducerRowCountIs6 =
        refl
    ; shiftDimension =
        4
    ; shiftDimensionIs4 =
        refl
    ; shiftSupport =
        canonicalShift4Support
    ; reducedOutput =
        canonicalShift4CriticalSeamOutput
    ; outputProjectionPackage =
        canonicalShift4ProjectionParallelogramPackage
    ; outputProjectionPackageIsReducedOutputPackage =
        refl
    ; reducedOutputPackageIsSupportPackage =
        refl
    ; outputQuadraticWitness =
        canonicalShift4QuadraticWitness
    ; outputQuadraticWitnessIsReducedOutputWitness =
        refl
    ; reducedOutputWitnessIsSupportWitness =
        refl
    ; outputQuadratic =
        canonicalShift4OutputQuadratic
    ; outputQuadraticIsWitnessQuadratic =
        refl
    ; outputParallelogramIdentity =
        canonicalShift4ParallelogramIdentity
    ; concreteShiftOutputCalculated =
        true
    ; concreteShiftOutputCalculatedIsTrue =
        refl
    ; generalCriticalSeamTheoremPromoted =
        false
    ; generalCriticalSeamTheoremPromotedIsFalse =
        refl
    ; criticalSeamTheoremTypeInhabitedHere =
        false
    ; criticalSeamTheoremTypeInhabitedHereIsFalse =
        refl
    ; exactFirstMissingTheorem =
        Seam.missingDefectAdmissibilityHierarchyToParallelogram
    ; exactFirstMissingTheoremIsGeneralSeam =
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
        "This reducer computes a concrete CriticalSeamTheoremOutput 4 from canonicalShiftCarrierCriticalSeamSupport."
        ∷ "The result is the already checked integer shift-carrier path, not a proof of CriticalSeamTheoremType."
        ∷ "The general theorem remains missingDefectAdmissibilityHierarchyToParallelogram."
        ∷ "Signature, Clifford, Standard Model, and terminal unification promotion guards remain false."
        ∷ []
    }

canonicalConcreteShiftReducerRowCountIs6 :
  reducerRowCount canonicalDefectCriticalSeamConcreteShiftReducer ≡ 6
canonicalConcreteShiftReducerRowCountIs6 = refl

canonicalConcreteShiftReducerOutputCalculated :
  concreteShiftOutputCalculated
    canonicalDefectCriticalSeamConcreteShiftReducer
  ≡ true
canonicalConcreteShiftReducerOutputCalculated = refl

canonicalConcreteShiftReducerGeneralTheoremNotPromoted :
  generalCriticalSeamTheoremPromoted
    canonicalDefectCriticalSeamConcreteShiftReducer
  ≡ false
canonicalConcreteShiftReducerGeneralTheoremNotPromoted = refl

canonicalConcreteShiftReducerTheoremTypeNotInhabitedHere :
  criticalSeamTheoremTypeInhabitedHere
    canonicalDefectCriticalSeamConcreteShiftReducer
  ≡ false
canonicalConcreteShiftReducerTheoremTypeNotInhabitedHere = refl

canonicalConcreteShiftReducerFirstMissingTheorem :
  exactFirstMissingTheorem canonicalDefectCriticalSeamConcreteShiftReducer
  ≡ Seam.missingDefectAdmissibilityHierarchyToParallelogram
canonicalConcreteShiftReducerFirstMissingTheorem = refl

canonicalConcreteShiftReducerSignaturePromotionFalse :
  signaturePromoted canonicalDefectCriticalSeamConcreteShiftReducer ≡ false
canonicalConcreteShiftReducerSignaturePromotionFalse = refl

canonicalConcreteShiftReducerCliffordPromotionFalse :
  cliffordPromoted canonicalDefectCriticalSeamConcreteShiftReducer ≡ false
canonicalConcreteShiftReducerCliffordPromotionFalse = refl

canonicalConcreteShiftReducerStandardModelPromotionFalse :
  standardModelPromoted canonicalDefectCriticalSeamConcreteShiftReducer
  ≡ false
canonicalConcreteShiftReducerStandardModelPromotionFalse = refl

canonicalConcreteShiftReducerTerminalPromotionFalse :
  terminalUnificationPromoted canonicalDefectCriticalSeamConcreteShiftReducer
  ≡ false
canonicalConcreteShiftReducerTerminalPromotionFalse = refl
