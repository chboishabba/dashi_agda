{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravitySourceExpectationToPhysicalHaarExact where

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; absℝ; _-ℝ_; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.Foundations.CMP119AntigravityRealHaarExpectationRepresentationExact as Target
import DASHI.Physics.YangMills.BalabanCMP119FactorizedDensityApproximationExact as Approx
import DASHI.Physics.YangMills.BalabanCMP119FiniteObservableExpectationConvergenceExact as Expect
import DASHI.Physics.YangMills.BalabanCompactHaarFiniteQuadratureErrorExact as Quad
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq

------------------------------------------------------------------------
-- AG-S1 / SOURCE EXPECTATION -> PRODUCT-HAAR QUADRATURE COMPILER
--
-- The finite expectation algebra is already complete.  The remaining physical
-- input is a refinement-indexed compact-Haar quadrature whose source integral
-- is the SAME physical expectation and whose quadrature sum is the SAME
-- CMP119 sourceExpectation.
------------------------------------------------------------------------

record CMP119PhysicalHaarQuadratureWeld
    {SlowField Sequence Component Step Cell : Set}
    (approximation :
      Approx.CMP119FactorizedDensityApproximation
        SlowField Sequence Component Step)
    (sequenceLimit : Seq.RealSequenceLimitByVanishingError)
    (scale : Nat)
    (observable : SlowField → ℝ) : Set₁ where
  field
    statesAt : Nat → List SlowField
    quadratureAt : Nat → Quad.FiniteQuadratureCellError Cell

    physicalHaarExpectation : ℝ

    sourceIntegralIsPhysical :
      ∀ refinement →
      Quad.sourceIntegral (quadratureAt refinement)
      ≡ physicalHaarExpectation

    sourceExpectationIsQuadrature :
      ∀ refinement →
      Expect.sourceExpectation
        approximation (statesAt refinement) scale observable
      ≡
      Quad.quadratureSum (quadratureAt refinement)

    quadratureErrorVanishes :
      Seq.Vanishes sequenceLimit
        (λ refinement →
          Quad.totalErrorBudget (quadratureAt refinement))

open CMP119PhysicalHaarQuadratureWeld public

compileCMP119PhysicalHaarRepresentation :
  ∀ {SlowField Sequence Component Step Cell approximation sequenceLimit scale observable}
    (weld :
      CMP119PhysicalHaarQuadratureWeld
        {SlowField = SlowField}
        {Sequence = Sequence}
        {Component = Component}
        {Step = Step}
        {Cell = Cell}
        approximation sequenceLimit scale observable) →
  Target.RealHaarExpectationRepresentation sequenceLimit
compileCMP119PhysicalHaarRepresentation
    {approximation = approximation}
    {scale = scale}
    {observable = observable}
    weld = record
  { Target.RealHaarExpectationRepresentation.finiteCMP119Expectation =
      λ refinement →
        Expect.sourceExpectation
          approximation (statesAt weld refinement) scale observable
  ; Target.RealHaarExpectationRepresentation.physicalHaarExpectation =
      physicalHaarExpectation weld
  ; Target.RealHaarExpectationRepresentation.representationError =
      λ refinement →
        Quad.totalErrorBudget (quadratureAt weld refinement)
  ; Target.RealHaarExpectationRepresentation.finiteApproximatesPhysical =
      λ refinement →
        subst
          (λ source →
            absℝ
              (source -ℝ
                Expect.sourceExpectation
                  approximation (statesAt weld refinement) scale observable)
            ≤ℝ
            Quad.totalErrorBudget (quadratureAt weld refinement))
          (sourceIntegralIsPhysical weld refinement)
          (subst
            (λ quadrature →
              absℝ
                (Quad.sourceIntegral (quadratureAt weld refinement)
                  -ℝ quadrature)
              ≤ℝ
              Quad.totalErrorBudget (quadratureAt weld refinement))
            (sym (sourceExpectationIsQuadrature weld refinement))
            (Quad.finiteQuadratureErrorBound
              (quadratureAt weld refinement)))
  ; Target.RealHaarExpectationRepresentation.representationErrorVanishes =
      quadratureErrorVanishes weld
  }

cmp119SourceExpectationToPhysicalHaarCompilerLevel : ProofLevel
cmp119SourceExpectationToPhysicalHaarCompilerLevel = machineChecked

-- Remaining AG-S1 payment is now exactly:
--   * construct literal product/constrained-Haar cells/nodes;
--   * identify their source integral with the physical CMP119 Haar integral;
--   * identify their quadrature sum with sourceExpectation;
--   * prove oscillation + mass-discrepancy budgets vanish.
literalCMP119PhysicalHaarQuadratureWeldLevel : ProofLevel
literalCMP119PhysicalHaarQuadratureWeldLevel = conditional
