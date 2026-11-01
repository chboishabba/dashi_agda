module DASHI.Physics.YangMills.BalabanCMP119Equation171WeightedFactorizedConvergenceExact where

------------------------------------------------------------------------
-- WEIGHTED EQ.(1.71) STEP QUADRATURES
--   -> COMPLETE FACTORIZED CMP119 DENSITY CONVERGENCE
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP119Equation171WeightedStepApproximationExact as Step
import DASHI.Physics.YangMills.BalabanCMP119FactorizedMarkedBudgetVanishesExact as Budget
import DASHI.Physics.YangMills.BalabanCMP119FactorizedDensityConvergenceExact as Convergence
import DASHI.Physics.YangMills.BalabanCMP122Equation171WeightedGate4RefinementLimitExact as Weighted
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanRealVanishingFiniteAlgebraExact as Vanishing

stepMarkedVanishesFromWeightedQuadrature :
  ∀ {trajectory split SlowField Sequence Component StepIndex factorized
      Scale Fine FunctionalValue embedding sequenceLimit}
    (dataSet :
      Step.CMP119Equation171WeightedStepApproximation
        {trajectory = trajectory} {split = split}
        {SlowField = SlowField} {Sequence = Sequence}
        {Component = Component} {Step = StepIndex}
        factorized
        {Scale = Scale} {Fine = Fine}
        {FunctionalValue = FunctionalValue}
        embedding sequenceLimit)
    scale sequence component step slow →
  Seq.Vanishes sequenceLimit
    (λ refinement →
      Step.markedMajorant dataSet
        refinement scale sequence component step slow)
stepMarkedVanishesFromWeightedQuadrature
  dataSet scale sequence component step slow =
  Weighted.oscillationModulusVanishes
    (Step.quadratureAt dataSet sequence component step)
    scale slow

asFactorizedStepMarkedVanishing :
  ∀ {trajectory split SlowField Sequence Component StepIndex factorized
      Scale Fine FunctionalValue embedding sequenceLimit}
    (dataSet :
      Step.CMP119Equation171WeightedStepApproximation
        {trajectory = trajectory} {split = split}
        {SlowField = SlowField} {Sequence = Sequence}
        {Component = Component} {Step = StepIndex}
        factorized
        {Scale = Scale} {Fine = Fine}
        {FunctionalValue = FunctionalValue}
        embedding sequenceLimit)
    (algebra :
      Vanishing.RealVanishingFiniteAlgebra sequenceLimit) →
  Budget.CMP119FactorizedStepMarkedVanishing
    (Step.asFactorizedDensityApproximation dataSet)
    sequenceLimit algebra
asFactorizedStepMarkedVanishing dataSet algebra = record
  { Budget.CMP119FactorizedStepMarkedVanishing.stepMarkedVanishes =
      stepMarkedVanishesFromWeightedQuadrature dataSet
  }

compileCompleteCMP119DensityConvergence :
  ∀ {trajectory split SlowField Sequence Component StepIndex factorized
      Scale Fine FunctionalValue embedding sequenceLimit}
    (dataSet :
      Step.CMP119Equation171WeightedStepApproximation
        {trajectory = trajectory} {split = split}
        {SlowField = SlowField} {Sequence = Sequence}
        {Component = Component} {Step = StepIndex}
        factorized
        {Scale = Scale} {Fine = Fine}
        {FunctionalValue = FunctionalValue}
        embedding sequenceLimit)
    (algebra :
      Vanishing.RealVanishingFiniteAlgebra sequenceLimit) →
  Convergence.CMP119FactorizedDensityConvergence
    (Step.asFactorizedDensityApproximation dataSet)
    sequenceLimit
compileCompleteCMP119DensityConvergence dataSet algebra =
  Budget.compileFactorizedDensityConvergence
    (asFactorizedStepMarkedVanishing dataSet algebra)

cmp119Equation171WeightedStepVanishingCompilerLevel : ProofLevel
cmp119Equation171WeightedStepVanishingCompilerLevel = machineChecked

cmp119Equation171CompleteDensityConvergenceCompilerLevel : ProofLevel
cmp119Equation171CompleteDensityConvergenceCompilerLevel = machineChecked
