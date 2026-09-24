module DASHI.Physics.YangMills.BalabanCMP119FactorizedMarkedBudgetVanishesExact where

------------------------------------------------------------------------
-- ONE-STEP MARKED ERRORS VANISH
--   -> COMPONENT BUDGETS VANISH
--   -> SEQUENCE BUDGETS VANISH
--   -> COMPLETE CMP119 (2.18) ERROR BUDGET VANISHES
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _*ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanDifferentiatedMarkedFactorProductExact as Product
import DASHI.Physics.YangMills.BalabanDecoupledActivityHessian as Hess
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as Sums
import DASHI.Physics.YangMills.BalabanCMP119FactorizedDensityApproximationExact as Approx
import DASHI.Physics.YangMills.BalabanCMP119FactorizedDensityConvergenceExact as Convergence
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanRealVanishingFiniteAlgebraExact as Vanishing

markedProductVanishes :
  ∀ {A : Set}
    {limitData : Seq.RealSequenceLimitByVanishingError}
    (algebra : Vanishing.RealVanishingFiniteAlgebra limitData)
    (ordinary : A → ℝ)
    (marked : A → Nat → ℝ)
    (xs : List A) →
  (∀ x →
    Seq.Vanishes limitData (marked x)) →
  Seq.Vanishes limitData
    (λ refinement →
      Product.markedProductMajorant
        ordinary
        (λ x → marked x refinement)
        xs)
markedProductVanishes algebra ordinary marked [] pointwise =
  Vanishing.vanishesZero algebra
markedProductVanishes algebra ordinary marked (x ∷ xs) pointwise =
  Vanishing.vanishesAdd algebra
    (λ refinement →
      marked x refinement
      *ℝ
      Hess.productℝ
        ordinary xs)
    (λ refinement →
      ordinary x
      *ℝ
      Product.markedProductMajorant
        ordinary
        (λ y → marked y refinement)
        xs)
    (Vanishing.vanishesScaleRight algebra
      (Hess.productℝ
        ordinary xs)
      (marked x)
      (pointwise x))
    (Vanishing.vanishesScaleLeft algebra
      (ordinary x)
      (λ refinement →
        Product.markedProductMajorant
          ordinary
          (λ y → marked y refinement)
          xs)
      (markedProductVanishes
        algebra ordinary marked xs pointwise))

realSumVanishes :
  ∀ {A : Set}
    {limitData : Seq.RealSequenceLimitByVanishingError}
    (algebra : Vanishing.RealVanishingFiniteAlgebra limitData)
    (values : List A)
    (sequence : A → Nat → ℝ) →
  (∀ x → Seq.Vanishes limitData (sequence x)) →
  Seq.Vanishes limitData
    (λ refinement →
      Sums.realSum values
        (λ x → sequence x refinement))
realSumVanishes algebra [] sequence pointwise =
  Vanishing.vanishesZero algebra
realSumVanishes algebra (x ∷ xs) sequence pointwise =
  Vanishing.vanishesAdd algebra
    (sequence x)
    (λ refinement →
      Sums.realSum xs
        (λ y → sequence y refinement))
    (pointwise x)
    (realSumVanishes algebra xs sequence pointwise)

record CMP119FactorizedStepMarkedVanishing
    {SlowField Sequence Component Step : Set}
    (approximation :
      Approx.CMP119FactorizedDensityApproximation
        SlowField Sequence Component Step)
    (limitData :
      Seq.RealSequenceLimitByVanishingError)
    (algebra :
      Vanishing.RealVanishingFiniteAlgebra limitData) : Set₁ where
  field
    stepMarkedVanishes :
      ∀ scale sequence component step slow →
      Seq.Vanishes limitData
        (λ refinement →
          Approx.markedMajorant approximation
            refinement scale sequence component step slow)

open CMP119FactorizedStepMarkedVanishing public

componentMarkedBudgetVanishes :
  ∀ {SlowField Sequence Component Step approximation limitData algebra}
    (dataSet :
      CMP119FactorizedStepMarkedVanishing
        {SlowField = SlowField}
        {Sequence = Sequence}
        {Component = Component}
        {Step = Step}
        approximation limitData algebra)
    scale sequence component slow →
  Seq.Vanishes limitData
    (λ refinement →
      Approx.componentMarkedMajorant approximation
        refinement scale sequence component slow)
componentMarkedBudgetVanishes
  {approximation = approximation}
  {algebra = algebra}
  dataSet scale sequence component slow =
  markedProductVanishes
    algebra
    (λ step →
      Approx.ordinaryMajorant approximation
        scale sequence component step slow)
    (λ step refinement →
      Approx.markedMajorant approximation
        refinement scale sequence component step slow)
    (Approx.orderedStepsAt approximation scale sequence component)
    (λ step →
      stepMarkedVanishes dataSet
        scale sequence component step slow)

componentProductMarkedBudgetVanishes :
  ∀ {SlowField Sequence Component Step approximation limitData algebra}
    (dataSet :
      CMP119FactorizedStepMarkedVanishing
        {SlowField = SlowField}
        {Sequence = Sequence}
        {Component = Component}
        {Step = Step}
        approximation limitData algebra)
    scale sequence slow →
  Seq.Vanishes limitData
    (λ refinement →
      Approx.componentProductMarkedMajorant approximation
        refinement scale sequence slow)
componentProductMarkedBudgetVanishes
  {approximation = approximation}
  {algebra = algebra}
  dataSet scale sequence slow =
  markedProductVanishes
    algebra
    (λ component →
      Approx.componentOrdinaryMajorant approximation
        scale sequence component slow)
    (λ component refinement →
      Approx.componentMarkedMajorant approximation
        refinement scale sequence component slow)
    (Approx.componentsAt approximation scale sequence)
    (λ component →
      componentMarkedBudgetVanishes
        dataSet scale sequence component slow)

sequenceErrorBudgetVanishes :
  ∀ {SlowField Sequence Component Step approximation limitData algebra}
    (dataSet :
      CMP119FactorizedStepMarkedVanishing
        {SlowField = SlowField}
        {Sequence = Sequence}
        {Component = Component}
        {Step = Step}
        approximation limitData algebra)
    scale sequence slow →
  Seq.Vanishes limitData
    (λ refinement →
      Approx.sequenceErrorBudget approximation
        refinement scale sequence slow)
sequenceErrorBudgetVanishes
  {approximation = approximation}
  {algebra = algebra}
  dataSet scale sequence slow =
  Vanishing.vanishesScaleLeft algebra
    (Approx.residualMajorant approximation scale sequence slow)
    (λ refinement →
      Approx.componentProductMarkedMajorant approximation
        refinement scale sequence slow)
    (componentProductMarkedBudgetVanishes
      dataSet scale sequence slow)

densityErrorBudgetVanishes :
  ∀ {SlowField Sequence Component Step approximation limitData algebra}
    (dataSet :
      CMP119FactorizedStepMarkedVanishing
        {SlowField = SlowField}
        {Sequence = Sequence}
        {Component = Component}
        {Step = Step}
        approximation limitData algebra)
    scale slow →
  Seq.Vanishes limitData
    (λ refinement →
      Approx.densityErrorBudget approximation
        refinement scale slow)
densityErrorBudgetVanishes
  {approximation = approximation}
  {algebra = algebra}
  dataSet scale slow =
  realSumVanishes
    algebra
    (Approx.admissibleSequences approximation scale)
    (λ sequence refinement →
      Approx.sequenceErrorBudget approximation
        refinement scale sequence slow)
    (λ sequence →
      sequenceErrorBudgetVanishes
        dataSet scale sequence slow)

compileFactorizedDensityConvergence :
  ∀ {SlowField Sequence Component Step approximation limitData algebra} →
  CMP119FactorizedStepMarkedVanishing
    {SlowField = SlowField}
    {Sequence = Sequence}
    {Component = Component}
    {Step = Step}
    approximation limitData algebra →
  Convergence.CMP119FactorizedDensityConvergence
    approximation limitData
compileFactorizedDensityConvergence dataSet = record
  { Convergence.CMP119FactorizedDensityConvergence.errorBudgetVanishes =
      densityErrorBudgetVanishes dataSet
  }

cmp119MarkedStepToDensityVanishingCompilerLevel : ProofLevel
cmp119MarkedStepToDensityVanishingCompilerLevel = machineChecked

cmp119FactorizedDensityConvergenceFromStepsLevel : ProofLevel
cmp119FactorizedDensityConvergenceFromStepsLevel = machineChecked
