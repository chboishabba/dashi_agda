module DASHI.Physics.YangMills.BalabanCMP119FactorizedDensityConvergenceExact where

------------------------------------------------------------------------
-- COMPLETE CMP119 (2.18) CONVERGENCE FROM THE GENERATED FACTORIZED BUDGET
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP119FactorizedDensityApproximationExact as Approx
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq

record CMP119FactorizedDensityConvergence
    {SlowField Sequence Component Step : Set}
    (approximation :
      Approx.CMP119FactorizedDensityApproximation
        SlowField Sequence Component Step)
    (sequenceLimit :
      Seq.RealSequenceLimitByVanishingError) : Set₁ where
  field
    errorBudgetVanishes :
      ∀ scale slow →
      Seq.Vanishes sequenceLimit
        (λ refinement →
          Approx.densityErrorBudget
            approximation refinement scale slow)

open CMP119FactorizedDensityConvergence public

factorizedDensityApproximationConverges :
  ∀ {SlowField Sequence Component Step approximation sequenceLimit}
    (dataSet :
      CMP119FactorizedDensityConvergence
        {SlowField = SlowField}
        {Sequence = Sequence}
        {Component = Component}
        {Step = Step}
        approximation sequenceLimit)
    scale slow →
  Approx.densitySource approximation scale slow
  ≡
  Seq.limit sequenceLimit
    (λ refinement →
      Approx.densityApproximation
        approximation refinement scale slow)
factorizedDensityApproximationConverges
  {approximation = approximation}
  {sequenceLimit = sequenceLimit}
  dataSet scale slow =
  sym
    (Seq.limitFromVanishingError sequenceLimit
      (λ refinement →
        Approx.densityApproximation
          approximation refinement scale slow)
      (Approx.densitySource approximation scale slow)
      (λ refinement →
        Approx.densityErrorBudget
          approximation refinement scale slow)
      (λ refinement →
        Approx.factorizedDensityDifferenceBound
          approximation refinement scale slow)
      (errorBudgetVanishes dataSet scale slow))

cmp119FactorizedDensityConvergenceCompilerLevel : ProofLevel
cmp119FactorizedDensityConvergenceCompilerLevel = machineChecked

-- The remaining analytic payment is no longer a global density estimate.
-- It is exactly the vanishing of the finite budget generated from the
-- factorwise one-step marked errors.
literalCMP119FactorizedErrorBudgetVanishesLevel : ProofLevel
literalCMP119FactorizedErrorBudgetVanishesLevel = conditional
