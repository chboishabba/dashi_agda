module DASHI.Physics.YangMills.BalabanCMP119FiniteDensityAssemblySemanticsExact where

------------------------------------------------------------------------
-- CMP119 FINITE DENSITY ASSEMBLY SEMANTICS
--
-- Split the old end-to-end source weld into two independent meanings:
--
--   (A) evaluating assembleDensity T A is the finite application of T to A;
--   (B) on the selected source pair (T_k,A_k), that finite application is the
--       concrete physical localized T-operation at the unit functional.
--
-- The first statement belongs to the literal CMP119 representation semantics.
-- The second is the Gate4/P3 realization.  Their composition recovers the
-- previous assembled-density = physical-T equality.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119ResidualFamilyRound219Exact as R219
import DASHI.Physics.YangMills.BalabanCMP119AssembledFiniteSlowDensityExact as Assembled

record CMP119FiniteDensityAssemblySemantics
    {trajectory split}
    (source :
      Beta.BetaDrivenCompleteDensityInputs
        {trajectory = trajectory} {split = split})
    (family : R219.BetaDrivenCMP119ResidualFamily source)
    (SlowField : Set) : Set₁ where
  field
    evaluateDensity :
      Beta.Density source → SlowField → ℚ

    applyOperationAction :
      R219.Operation family →
      R219.Action family →
      SlowField → ℚ

    assembleDensityEvaluation :
      ∀ operation action slow →
      evaluateDensity
        (R219.assembleDensity family operation action)
        slow
      ≡
      applyOperationAction operation action slow

open CMP119FiniteDensityAssemblySemantics public

asAssembledDensityFiniteEvaluator :
  ∀ {trajectory split source family SlowField} →
  CMP119FiniteDensityAssemblySemantics
    {trajectory = trajectory} {split = split}
    source family SlowField →
  Assembled.CMP119AssembledDensityFiniteEvaluator family SlowField
asAssembledDensityFiniteEvaluator semantics = record
  { Assembled.CMP119AssembledDensityFiniteEvaluator.evaluateAssembledDensity =
      applyOperationAction semantics
  }

selectedDensityEvaluationIsAssembledWeight :
  ∀ {trajectory split source family SlowField}
    (semantics :
      CMP119FiniteDensityAssemblySemantics
        {trajectory = trajectory} {split = split}
        source family SlowField)
    cutoff slow →
  evaluateDensity semantics (Beta.densityAt source cutoff) slow
  ≡
  Assembled.assembledSelectedWeight
    (asAssembledDensityFiniteEvaluator semantics)
    cutoff slow
selectedDensityEvaluationIsAssembledWeight
  {family = family} semantics cutoff slow =
  trans
    (cong
      (λ density → evaluateDensity semantics density slow)
      (R219.densityEquation family cutoff))
    (assembleDensityEvaluation semantics
      (R219.operationAt family cutoff)
      (R219.effectiveActionAt family cutoff)
      slow)

selectedAssembledWeightIsSourceDensityEvaluation :
  ∀ {trajectory split source family SlowField}
    (semantics :
      CMP119FiniteDensityAssemblySemantics
        {trajectory = trajectory} {split = split}
        source family SlowField)
    cutoff slow →
  Assembled.assembledSelectedWeight
    (asAssembledDensityFiniteEvaluator semantics)
    cutoff slow
  ≡
  evaluateDensity semantics (Beta.densityAt source cutoff) slow
selectedAssembledWeightIsSourceDensityEvaluation semantics cutoff slow =
  sym (selectedDensityEvaluationIsAssembledWeight semantics cutoff slow)

cmp119FiniteDensityAssemblyCompilerLevel : ProofLevel
cmp119FiniteDensityAssemblyCompilerLevel = machineChecked

cmp119SelectedDensityEvaluationSameObjectLevel : ProofLevel
cmp119SelectedDensityEvaluationSameObjectLevel = machineChecked

-- Literal source-semantic leaf: instantiate the evaluation of the CMP119
-- representation so that assembleDensity means finite application of its own
-- T-coordinate to its own A-coordinate.
literalCMP119AssembleDensityEvaluationLevel : ProofLevel
literalCMP119AssembleDensityEvaluationLevel = conditional
