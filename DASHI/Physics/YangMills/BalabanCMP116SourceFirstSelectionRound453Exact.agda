{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116SourceFirstSelectionRound453Exact where

------------------------------------------------------------------------
-- ROUND453 / SOURCE-FIRST CMP116 -> SELECTED R406 PROJECTION
--
-- Audit result: the live variable-domain CMP116 route already has the desired
-- GRQFT specialization shape.  The selected R406 localization is not chosen
-- independently and then welded to the source application:
--
--   literal R429/CMP116 source object
--          ↓
--   canonicalApplication
--          ↓
--   selected R406 localization
--
-- R440.application is definitionally R429.canonicalApplication.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116CanonicalFourStageR406Round429Exact as R429
import DASHI.Physics.YangMills.BalabanCMP116VariableDomainPreferredR415Round440Exact as R440

sourceApplicationIsCanonicalSelection :
  ∀ {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {fourStage :
      R429.CanonicalFourStageR406Data
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base}
    (source : R440.VariableDomainCMP116Source fourStage) →
  R440.application source
  ≡ R429.canonicalApplication fourStage
sourceApplicationIsCanonicalSelection source = refl

selectedR406ApplicationChosenIndependentlyFromCMP116Source : Bool
selectedR406ApplicationChosenIndependentlyFromCMP116Source = false

postHocSourceToSelectedApplicationEqualityRequired : Bool
postHocSourceToSelectedApplicationEqualityRequired = false

sourceFirstProjectionIsDefinitional : Bool
sourceFirstProjectionIsDefinitional = true

round453SourceFirstSelectionCompilerLevel : ProofLevel
round453SourceFirstSelectionCompilerLevel = machineChecked
