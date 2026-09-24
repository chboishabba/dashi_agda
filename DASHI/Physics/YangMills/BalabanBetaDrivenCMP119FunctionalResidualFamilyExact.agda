module DASHI.Physics.YangMills.BalabanBetaDrivenCMP119FunctionalResidualFamilyExact where

------------------------------------------------------------------------
-- CMP119 EQ.(2.18) ON A FUNCTIONAL DENSITY CARRIER
--
-- Preferred source representation:
--
--   Density = SlowField -> ℝ
--   assembleDensity T A = applyOperationAction T A
--
-- Therefore the old F1a theorem
--
--   evaluate(assembleDensity T A) = applyOperationAction T A
--
-- is definitional and disappears.  The only source payment is the literal
-- Eq.(2.18) functional identity for rho_k itself.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenFunctionalDensityExact as Functional
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.Balaban1989BetaSplitInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.BalabanCMP119Section2CompleteDensityDictionaryExact as CMP119

record BetaDrivenCMP119FunctionalResidualFamily
    {trajectory split SlowField}
    (inputs :
      Functional.BetaDrivenFunctionalDensityInputs
        {trajectory = trajectory} {split = split} SlowField) : Set₂ where
  field
    Operation Action Field : Set
    RegularTerm RTerm BoundaryTerm VacuumTerm : Set
    SmallFieldScale BlockRadius AnalyticRadius Decay : Set

    operationAt : Nat → Operation
    effectiveActionAt : Nat → Action
    backgroundAt : Nat → Field
    regularEAt : Nat → RegularTerm
    rOperationAt : Nat → RTerm
    boundaryAt : Nat → BoundaryTerm
    vacuumAt : Nat → VacuumTerm

    epsilonAt : Nat → SmallFieldScale
    blockRadiusAt : Nat → BlockRadius
    alpha0At alpha1At : Nat → AnalyticRadius
    decayAt : Nat → Decay

    -- Literal application semantics of the source operation/action pair.
    applyOperationAction :
      Operation → Action → SlowField → ℝ

    assembleAction :
      ℚ → Field → RegularTerm → RTerm → BoundaryTerm → VacuumTerm → Action

    -- Eq.(2.18), now stated on the actual functional carrier.
    densityEquation : ∀ scale →
      Functional.densityAt inputs scale
      ≡
      applyOperationAction
        (operationAt scale)
        (effectiveActionAt scale)

    -- Eq.(2.23).
    actionEquation : ∀ scale →
      effectiveActionAt scale
      ≡ assembleAction
          (History.couplingAt
            (Functional.betaHistory inputs) scale)
          (backgroundAt scale)
          (regularEAt scale)
          (rOperationAt scale)
          (boundaryAt scale)
          (vacuumAt scale)

open BetaDrivenCMP119FunctionalResidualFamily public

assembleDensity :
  ∀ {trajectory split SlowField inputs}
    (family :
      BetaDrivenCMP119FunctionalResidualFamily
        {trajectory = trajectory} {split = split}
        {SlowField = SlowField} inputs) →
  Operation family → Action family → SlowField → ℝ
assembleDensity = applyOperationAction

assembleDensityEvaluation :
  ∀ {trajectory split SlowField inputs}
    (family :
      BetaDrivenCMP119FunctionalResidualFamily
        {trajectory = trajectory} {split = split}
        {SlowField = SlowField} inputs)
    operation action slow →
  assembleDensity family operation action slow
  ≡
  applyOperationAction family operation action slow
assembleDensityEvaluation family operation action slow = refl

selectedDensityPointwiseEquation :
  ∀ {trajectory split SlowField inputs}
    (family :
      BetaDrivenCMP119FunctionalResidualFamily
        {trajectory = trajectory} {split = split}
        {SlowField = SlowField} inputs)
    scale slow →
  Functional.densityAt inputs scale slow
  ≡
  applyOperationAction family
    (operationAt family scale)
    (effectiveActionAt family scale)
    slow
selectedDensityPointwiseEquation family scale slow =
  cong
    (λ density → density slow)
    (densityEquation family scale)

completeDensityAt :
  ∀ {trajectory split SlowField inputs}
    (family :
      BetaDrivenCMP119FunctionalResidualFamily
        {trajectory = trajectory} {split = split}
        {SlowField = SlowField} inputs)
    scale →
  CMP119.CMP119Section2CompleteDensity
    ℚ (SlowField → ℝ)
    (Operation family) (Action family) (Field family)
    (RegularTerm family) (RTerm family)
    (BoundaryTerm family) (VacuumTerm family)
    (SmallFieldScale family) (BlockRadius family)
    (AnalyticRadius family) (Decay family)
completeDensityAt {inputs = inputs} family scale = record
  { CMP119.CMP119Section2CompleteDensity.scale = scale
  ; CMP119.CMP119Section2CompleteDensity.g =
      History.couplingAt (Functional.betaHistory inputs) scale
  ; CMP119.CMP119Section2CompleteDensity.rho =
      Functional.densityAt inputs scale
  ; CMP119.CMP119Section2CompleteDensity.T =
      operationAt family scale
  ; CMP119.CMP119Section2CompleteDensity.effectiveAction =
      effectiveActionAt family scale
  ; CMP119.CMP119Section2CompleteDensity.background =
      backgroundAt family scale
  ; CMP119.CMP119Section2CompleteDensity.regularE =
      regularEAt family scale
  ; CMP119.CMP119Section2CompleteDensity.rOperationR =
      rOperationAt family scale
  ; CMP119.CMP119Section2CompleteDensity.boundaryB =
      boundaryAt family scale
  ; CMP119.CMP119Section2CompleteDensity.vacuumE =
      vacuumAt family scale
  ; CMP119.CMP119Section2CompleteDensity.epsilon =
      epsilonAt family scale
  ; CMP119.CMP119Section2CompleteDensity.blockRadius =
      blockRadiusAt family scale
  ; CMP119.CMP119Section2CompleteDensity.alpha0 =
      alpha0At family scale
  ; CMP119.CMP119Section2CompleteDensity.alpha1 =
      alpha1At family scale
  ; CMP119.CMP119Section2CompleteDensity.decayKappa =
      decayAt family scale
  ; CMP119.CMP119Section2CompleteDensity.assembleDensity =
      assembleDensity family
  ; CMP119.CMP119Section2CompleteDensity.assembleAction =
      assembleAction family
  ; CMP119.CMP119Section2CompleteDensity.densityEquation =
      densityEquation family scale
  ; CMP119.CMP119Section2CompleteDensity.actionEquation =
      actionEquation family scale
  }

functionalCMP119AssemblyEvaluationLevel : ProofLevel
functionalCMP119AssemblyEvaluationLevel = machineChecked

functionalCMP119PointwiseDensityEquationLevel : ProofLevel
functionalCMP119PointwiseDensityEquationLevel = machineChecked

functionalCMP119CompleteDensityCompilerLevel : ProofLevel
functionalCMP119CompleteDensityCompilerLevel = machineChecked

-- The remaining source theorem is now exactly Eq.(2.18) on the literal
-- functional density, not a second evaluator/application weld.
literalCMP119Equation218FunctionalRepresentationLevel : ProofLevel
literalCMP119Equation218FunctionalRepresentationLevel = conditional
