module DASHI.Cognition.PNF.SensibLawAuthorityTransformationUniversalCutBridgeExact where

------------------------------------------------------------------------
-- LEGACY MINIMAL-CUT CALIBRATION -> PROOF-RELEVANT UNIVERSAL CUT
--
-- `SensibLawAuthorityTransformationMinimalCutExact` predates the universal legal
-- graph and stores target/obstruction summaries as Strings plus status Booleans.
-- Those values remain useful source-calibrated expectations, but are NOT called
-- computed cuts here. Promotion requires a proof-bearing Algebra.MinimalCut over
-- a typed LegalGraph/FactSet/LegalProposition.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawAuthorityTransformationMinimalCutExact as Legacy
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra

record CutCalibrationTarget : Set where
  constructor cut-calibration-target
  field
    legacy : Legacy.MinimalCutResult
    typedGoal : Algebra.LegalProposition
    legacyTargetReference : String

open CutCalibrationTarget public

record ComputedCutPromotion
  (graph : Algebra.LegalGraph)
  (facts : Algebra.FactSet)
  (target : CutCalibrationTarget)
  : Set where
  constructor computed-cut-promotion
  field
    computedCut : Algebra.MinimalCut graph facts (typedGoal target)
    legacyCalibrationStillOnlyExpectation : Set
    sourceAndTransformationClassificationRechecked : Set

open ComputedCutPromotion public

------------------------------------------------------------------------
-- A transformation-class label also requires an explicit typed rule change.
------------------------------------------------------------------------

record ComputedTransformationPromotion
  (graph : Algebra.LegalGraph)
  (facts : Algebra.FactSet)
  (target : CutCalibrationTarget)
  : Set where
  constructor computed-transformation-promotion
  field
    cutPromotion : ComputedCutPromotion graph facts target
    typedTransformation : Algebra.LegalTransformation
    transformedGoalDerivation : Set
    transformationLegallyAvailableUnderSourceGraph : Set

open ComputedTransformationPromotion public

------------------------------------------------------------------------
-- Status vocabulary makes the old/new boundary executable for downstream
-- schedulers and CI roots.
------------------------------------------------------------------------

data CutComputationStatus : Set where
  legacyCalibrationOnly
  typedGoalMaterialised
  proofRelevantCutComputed
  transformationReopensGoal
  : CutComputationStatus

legacyMaboStatus : CutComputationStatus
legacyMaboStatus = legacyCalibrationOnly

legacyPabaiStatus : CutComputationStatus
legacyPabaiStatus = legacyCalibrationOnly

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data LegacyMinimalCutResultIsComputedCut : Set where
data ReachableBooleanIsDerivationTree : Set where
data TransformationClassLabelProvesLegalAvailability : Set where

legacyCalibrationIsNotComputedCut : LegacyMinimalCutResultIsComputedCut → ⊥
legacyCalibrationIsNotComputedCut ()

booleanDoesNotBecomeDerivation : ReachableBooleanIsDerivationTree → ⊥
booleanDoesNotBecomeDerivation ()

classLabelDoesNotProveAvailableTransformation :
  TransformationClassLabelProvesLegalAvailability → ⊥
classLabelDoesNotProveAvailableTransformation ()
