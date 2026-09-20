module DASHI.Physics.YangMills.BalabanCMP119FiniteObservableExpectationConvergenceExact where

------------------------------------------------------------------------
-- COMPLETE CMP119 DENSITY CONVERGENCE -> FINITE OBSERVABLE EXPECTATION
--
-- This pays the finite expectation semantics algebra that sits between the
-- pointwise density theorem and the physical density->measure weld.
--
-- On one finite selected slow-field family:
--
--   rho_n(x) -> rho(x) pointwise with generated error e_n(x)
--
-- implies, for every fixed observable O,
--
--   sum_x rho_n(x) O(x) -> sum_x rho(x) O(x),
--
-- with explicit finite error
--
--   sum_x e_n(x) |O(x)|.
--
-- No measure identity is invented here.  The remaining physical theorem is
-- exactly that the literal finite Yang--Mills measure/expectation is represented
-- by this selected density sum.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _+ℝ_; _*ℝ_; _-ℝ_; absℝ; _≤ℝ_;
   ≤ℝ-trans; absMul; mulMonotoneNonnegative)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP119FactorizedDensityApproximationExact as Approx
import DASHI.Physics.YangMills.BalabanCMP119FactorizedDensityConvergenceExact as Conv
import DASHI.Physics.YangMills.BalabanCompactHaarFiniteQuadratureErrorExact as SumError
import DASHI.Physics.YangMills.BalabanDifferentiatedMarkedFactorProductExact as Product
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as Sums
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanRealVanishingFiniteAlgebraExact as Vanishing

sourceExpectation :
  ∀ {SlowField Sequence Component Step} →
  Approx.CMP119FactorizedDensityApproximation
    SlowField Sequence Component Step →
  List SlowField → Nat → (SlowField → ℝ) → ℝ
sourceExpectation approximation states scale observable =
  Sums.realSum states
    (λ slow →
      Approx.densitySource approximation scale slow
      *ℝ observable slow)

approximateExpectation :
  ∀ {SlowField Sequence Component Step} →
  Approx.CMP119FactorizedDensityApproximation
    SlowField Sequence Component Step →
  List SlowField → Nat → Nat → (SlowField → ℝ) → ℝ
approximateExpectation approximation states refinement scale observable =
  Sums.realSum states
    (λ slow →
      Approx.densityApproximation
        approximation refinement scale slow
      *ℝ observable slow)

expectationErrorBudget :
  ∀ {SlowField Sequence Component Step} →
  Approx.CMP119FactorizedDensityApproximation
    SlowField Sequence Component Step →
  List SlowField → Nat → Nat → (SlowField → ℝ) → ℝ
expectationErrorBudget approximation states refinement scale observable =
  Sums.realSum states
    (λ slow →
      Approx.densityErrorBudget
        approximation refinement scale slow
      *ℝ absℝ (observable slow))

expectationDifferencePointwise :
  ∀ {SlowField Sequence Component Step}
    (approximation :
      Approx.CMP119FactorizedDensityApproximation
        SlowField Sequence Component Step)
    refinement scale observable slow →
  absℝ
    ((Approx.densitySource approximation scale slow
       *ℝ observable slow)
      -ℝ
     (Approx.densityApproximation approximation refinement scale slow
       *ℝ observable slow))
  ≤ℝ
  Approx.densityErrorBudget approximation refinement scale slow
    *ℝ absℝ (observable slow)
expectationDifferencePointwise approximation refinement scale observable slow =
  let
    densityDifference =
      Approx.densitySource approximation scale slow
      -ℝ
      Approx.densityApproximation approximation refinement scale slow

    densityBound =
      Approx.factorizedDensityDifferenceBound
        approximation refinement scale slow
  in
  subst
    (λ difference →
      absℝ difference
      ≤ℝ
      Approx.densityErrorBudget approximation refinement scale slow
        *ℝ absℝ (observable slow))
    (DASHI.Foundations.RealAnalysisAxioms.subMulDistributes
      (Approx.densitySource approximation scale slow)
      (Approx.densityApproximation approximation refinement scale slow)
      (observable slow))
    (subst
      (λ left →
        left
        ≤ℝ
        Approx.densityErrorBudget approximation refinement scale slow
          *ℝ absℝ (observable slow))
      (absMul densityDifference (observable slow))
      (mulMonotoneNonnegative
        (Product.absNonnegative densityDifference)
        densityBound
        (Product.absNonnegative (observable slow))
        (DASHI.Foundations.RealAnalysisAxioms.≤ℝ-refl)))

finiteExpectationDifferenceBound :
  ∀ {SlowField Sequence Component Step}
    (approximation :
      Approx.CMP119FactorizedDensityApproximation
        SlowField Sequence Component Step)
    states refinement scale observable →
  absℝ
    (sourceExpectation approximation states scale observable
      -ℝ
     approximateExpectation
       approximation states refinement scale observable)
  ≤ℝ
  expectationErrorBudget
    approximation states refinement scale observable
finiteExpectationDifferenceBound approximation states refinement scale observable =
  ≤ℝ-trans
    (SumError.absDifferenceOfRealSumsBelowPointwiseAbs
      states
      (λ slow →
        Approx.densitySource approximation scale slow
        *ℝ observable slow)
      (λ slow →
        Approx.densityApproximation
          approximation refinement scale slow
        *ℝ observable slow))
    (SumError.realSumMonotone
      states
      (λ slow →
        absℝ
          ((Approx.densitySource approximation scale slow
             *ℝ observable slow)
            -ℝ
           (Approx.densityApproximation
             approximation refinement scale slow
             *ℝ observable slow)))
      (λ slow →
        Approx.densityErrorBudget
          approximation refinement scale slow
        *ℝ absℝ (observable slow))
      (λ slow →
        expectationDifferencePointwise
          approximation refinement scale observable slow))

finiteExpectationBudgetVanishes :
  ∀ {SlowField Sequence Component Step approximation sequenceLimit}
    (convergence :
      Conv.CMP119FactorizedDensityConvergence
        {SlowField = SlowField}
        {Sequence = Sequence}
        {Component = Component}
        {Step = Step}
        approximation sequenceLimit)
    (algebra :
      Vanishing.RealVanishingFiniteAlgebra sequenceLimit)
    states scale observable →
  Seq.Vanishes sequenceLimit
    (λ refinement →
      expectationErrorBudget
        approximation states refinement scale observable)
finiteExpectationBudgetVanishes convergence algebra [] scale observable =
  Vanishing.vanishesZero algebra
finiteExpectationBudgetVanishes
  {approximation = approximation}
  {sequenceLimit = sequenceLimit}
  convergence algebra (slow ∷ rest) scale observable =
  Vanishing.vanishesAdd algebra
    (λ refinement →
      Approx.densityErrorBudget
        approximation refinement scale slow
      *ℝ absℝ (observable slow))
    (λ refinement →
      expectationErrorBudget
        approximation rest refinement scale observable)
    (Vanishing.vanishesScaleRight algebra
      (absℝ (observable slow))
      (λ refinement →
        Approx.densityErrorBudget
          approximation refinement scale slow)
      (Conv.errorBudgetVanishes convergence scale slow))
    (finiteExpectationBudgetVanishes
      convergence algebra rest scale observable)

finiteObservableExpectationConverges :
  ∀ {SlowField Sequence Component Step approximation sequenceLimit}
    (convergence :
      Conv.CMP119FactorizedDensityConvergence
        {SlowField = SlowField}
        {Sequence = Sequence}
        {Component = Component}
        {Step = Step}
        approximation sequenceLimit)
    (algebra :
      Vanishing.RealVanishingFiniteAlgebra sequenceLimit)
    states scale observable →
  sourceExpectation approximation states scale observable
  ≡
  Seq.limit sequenceLimit
    (λ refinement →
      approximateExpectation
        approximation states refinement scale observable)
finiteObservableExpectationConverges
  {approximation = approximation}
  {sequenceLimit = sequenceLimit}
  convergence algebra states scale observable =
  sym
    (Seq.limitFromVanishingError sequenceLimit
      (λ refinement →
        approximateExpectation
          approximation states refinement scale observable)
      (sourceExpectation approximation states scale observable)
      (λ refinement →
        expectationErrorBudget
          approximation states refinement scale observable)
      (λ refinement →
        finiteExpectationDifferenceBound
          approximation states refinement scale observable)
      (finiteExpectationBudgetVanishes
        convergence algebra states scale observable))

cmp119FiniteObservableExpectationErrorCompilerLevel : ProofLevel
cmp119FiniteObservableExpectationErrorCompilerLevel = machineChecked

cmp119FiniteObservableExpectationConvergenceCompilerLevel : ProofLevel
cmp119FiniteObservableExpectationConvergenceCompilerLevel = machineChecked

-- Remaining physical payment:
-- identify the literal finite-volume YM expectation with sourceExpectation on
-- this exact density/state carrier.  The convergence algebra above is complete.
literalCMP119DensityToFiniteMeasureExpectationWeldLevel : ProofLevel
literalCMP119DensityToFiniteMeasureExpectationWeldLevel = conditional
