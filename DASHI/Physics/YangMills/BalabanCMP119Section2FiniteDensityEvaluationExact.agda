module DASHI.Physics.YangMills.BalabanCMP119Section2FiniteDensityEvaluationExact where

------------------------------------------------------------------------
-- CMP119 SECTION-2 FINITE DENSITY EVALUATION SEMANTICS
--
-- The source dictionary already owns
--
--   rho = assembleDensity T effectiveAction.
--
-- What it did not own was the evaluation semantics of that representation.
-- This source-native refinement attaches exactly that missing meaning to the
-- SAME complete-density object:
--
--   evaluateDensity (assembleDensity operation action) slow
--     =
--   applyOperationAction operation action slow.
--
-- Downstream Round219 finite semantics can therefore be compiled from the
-- source object rather than chosen after the source family is constructed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP119Section2CompleteDensityDictionaryExact as CMP119

record CMP119Section2FiniteDensityEvaluation
    {Coupling Density Operation Action Field
      RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay : Set}
    (dataSet :
      CMP119.CMP119Section2CompleteDensity
        Coupling Density Operation Action Field
        RegularTerm RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay)
    (SlowField : Set) : Set₁ where
  field
    evaluateDensity :
      Density → SlowField → ℚ

    applyOperationAction :
      Operation → Action → SlowField → ℚ

    assembleDensityEvaluation :
      ∀ operation action slow →
      evaluateDensity
        (CMP119.assembleDensity dataSet operation action)
        slow
      ≡
      applyOperationAction operation action slow

open CMP119Section2FiniteDensityEvaluation public

sourceDensityEvaluationIsSelectedOperationAction :
  ∀ {Coupling Density Operation Action Field
      RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay SlowField}
    {dataSet :
      CMP119.CMP119Section2CompleteDensity
        Coupling Density Operation Action Field
        RegularTerm RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay}
    (semantics : CMP119Section2FiniteDensityEvaluation dataSet SlowField)
    slow →
  evaluateDensity semantics (CMP119.rho dataSet) slow
  ≡
  applyOperationAction semantics
    (CMP119.T dataSet)
    (CMP119.effectiveAction dataSet)
    slow
sourceDensityEvaluationIsSelectedOperationAction
  {dataSet = dataSet} semantics slow =
  trans
    (cong
      (λ density → evaluateDensity semantics density slow)
      (CMP119.densityEquation dataSet))
    (assembleDensityEvaluation semantics
      (CMP119.T dataSet)
      (CMP119.effectiveAction dataSet)
      slow)

cmp119Section2FiniteDensityEvaluationCompilerLevel : ProofLevel
cmp119Section2FiniteDensityEvaluationCompilerLevel = machineChecked

cmp119Section2SelectedEvaluationSameObjectLevel : ProofLevel
cmp119Section2SelectedEvaluationSameObjectLevel = machineChecked

-- Primary-source semantic leaf: instantiate this refinement with the literal
-- finite meaning of CMP119 Sect.2 representation (2.18)--(2.23).
literalCMP119Section2FiniteDensityEvaluationLevel : ProofLevel
literalCMP119Section2FiniteDensityEvaluationLevel = conditional
