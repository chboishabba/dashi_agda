module DASHI.Physics.YangMills.BalabanBetaDrivenCMP119FunctionalOperatorExact where

------------------------------------------------------------------------
-- CMP119 T_k AS A LITERAL OPERATOR ON THE FUNCTIONAL DENSITY CARRIER
--
-- Preferred source types:
--
--   Density   = SlowField -> ℝ
--   Operation = Action -> SlowField -> ℝ
--
-- and therefore
--
--   assembleDensity T A = T A
--
-- definitionally.  There is no separate applyOperationAction field and no
-- evaluator theorem on this route.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenFunctionalDensityExact as Functional
import DASHI.Physics.YangMills.Balaban1989BetaSplitInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.BalabanCMP119Section2CompleteDensityDictionaryExact as CMP119

record BetaDrivenCMP119FunctionalOperatorFamily
    {trajectory split SlowField}
    (inputs :
      Functional.BetaDrivenFunctionalDensityInputs
        {trajectory = trajectory} {split = split} SlowField) : Set₂ where
  field
    Action Field : Set
    RegularTerm RTerm BoundaryTerm VacuumTerm : Set
    SmallFieldScale BlockRadius AnalyticRadius Decay : Set

    operationAt : Nat → Action → SlowField → ℝ
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

    assembleAction :
      ℚ → Field → RegularTerm → RTerm → BoundaryTerm → VacuumTerm → Action

    -- Literal CMP119 (2.18).
    densityEquation : ∀ scale →
      Functional.densityAt inputs scale
      ≡ operationAt scale (effectiveActionAt scale)

    -- Literal CMP119 (2.23).
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

open BetaDrivenCMP119FunctionalOperatorFamily public

Operation :
  ∀ {trajectory split SlowField inputs} →
  BetaDrivenCMP119FunctionalOperatorFamily
    {trajectory = trajectory} {split = split}
    {SlowField = SlowField} inputs →
  Set
Operation {SlowField = SlowField} family =
  Action family → SlowField → ℝ

assembleDensity :
  ∀ {trajectory split SlowField inputs}
    (family :
      BetaDrivenCMP119FunctionalOperatorFamily
        {trajectory = trajectory} {split = split}
        {SlowField = SlowField} inputs) →
  Operation family → Action family → SlowField → ℝ
assembleDensity family operation action =
  operation action

assembleDensityEvaluation :
  ∀ {trajectory split SlowField inputs}
    (family :
      BetaDrivenCMP119FunctionalOperatorFamily
        {trajectory = trajectory} {split = split}
        {SlowField = SlowField} inputs)
    operation action slow →
  assembleDensity family operation action slow
  ≡ operation action slow
assembleDensityEvaluation family operation action slow = refl

selectedDensityPointwiseEquation :
  ∀ {trajectory split SlowField inputs}
    (family :
      BetaDrivenCMP119FunctionalOperatorFamily
        {trajectory = trajectory} {split = split}
        {SlowField = SlowField} inputs)
    scale slow →
  Functional.densityAt inputs scale slow
  ≡
  operationAt family scale
    (effectiveActionAt family scale)
    slow
selectedDensityPointwiseEquation family scale slow =
  cong
    (λ density → density slow)
    (densityEquation family scale)

completeDensityAt :
  ∀ {trajectory split SlowField inputs}
    (family :
      BetaDrivenCMP119FunctionalOperatorFamily
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

functionalOperatorCMP119F1aDefinitionalLevel : ProofLevel
functionalOperatorCMP119F1aDefinitionalLevel = machineChecked

functionalOperatorCMP119CompleteDensityLevel : ProofLevel
functionalOperatorCMP119CompleteDensityLevel = machineChecked

literalCMP119Equation218OperatorRepresentationLevel : ProofLevel
literalCMP119Equation218OperatorRepresentationLevel = conditional
