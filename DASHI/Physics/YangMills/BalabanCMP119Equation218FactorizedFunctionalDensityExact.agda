module DASHI.Physics.YangMills.BalabanCMP119Equation218FactorizedFunctionalDensityExact where

------------------------------------------------------------------------
-- CMP119 (2.18)--(2.22): FINITE FACTORIZED FUNCTIONAL DENSITY
--
-- Source structure encoded literally:
--
--   * (2.18) sum over admissible domain sequences;
--   * (2.19) product over disjoint components of Z_k;
--   * (2.20)/(2.22) ordered product of one-step T operations per component.
--
-- This module contains only the finite algebra.  It does not guess the damaged
-- OCR coefficients or invent the still-unextracted source index sets.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; 1ℝ; _+ℝ_; _*ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaSplitInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.Balaban1989BetaDrivenFunctionalDensityExact as Functional

realProduct :
  ∀ {A : Set} →
  List A → (A → ℝ) → ℝ
realProduct [] value = 1ℝ
realProduct (x ∷ xs) value =
  value x *ℝ realProduct xs value

realSum :
  ∀ {A : Set} →
  List A → (A → ℝ) → ℝ
realSum [] value = 0ℝ
realSum (x ∷ xs) value =
  value x +ℝ realSum xs value

record CMP119Equation218FactorizedFunctionalData
    {trajectory split}
    (SlowField Sequence Component Step : Set) : Set₂ where
  field
    betaHistory :
      History.BetaSplitInverseSquareTerminalHistoryData trajectory split

    -- (2.18)
    admissibleSequences : Nat → List Sequence

    -- (2.19)
    componentsAt :
      Nat → Sequence → List Component

    -- (2.20)/(2.22), with list order carrying the printed ordered product.
    orderedStepsAt :
      Nat → Sequence → Component → List Step

    -- Applied one-step operation after all source variables required by that
    -- step have been fixed.  The extraction layer must identify this with the
    -- literal source T^(j) operation.
    oneStepValue :
      Nat → Sequence → Component → Step → SlowField → ℝ

    -- Any factor in the (2.18) sequence term that is not one of the explicit
    -- component T-products (characteristic/action/localization factor after
    -- the source decomposition) remains visible here rather than being hidden
    -- in oneStepValue.
    sequenceResidual :
      Nat → Sequence → SlowField → ℝ

    InSection2DensityClass :
      Nat → (SlowField → ℝ) → Set

    Section2ConditionsAndBounds :
      Nat → (SlowField → ℝ) → Set

    sourceScaleActive :
      ∀ scale → History.ActiveScale betaHistory scale

open CMP119Equation218FactorizedFunctionalData public

componentApplication :
  ∀ {trajectory split SlowField Sequence Component Step} →
  CMP119Equation218FactorizedFunctionalData
    {trajectory = trajectory} {split = split}
    SlowField Sequence Component Step →
  Nat → Sequence → Component → SlowField → ℝ
componentApplication dataSet scale sequence component slow =
  realProduct
    (orderedStepsAt dataSet scale sequence component)
    (λ step →
      oneStepValue dataSet scale sequence component step slow)

sequenceApplication :
  ∀ {trajectory split SlowField Sequence Component Step} →
  CMP119Equation218FactorizedFunctionalData
    {trajectory = trajectory} {split = split}
    SlowField Sequence Component Step →
  Nat → Sequence → SlowField → ℝ
sequenceApplication dataSet scale sequence slow =
  sequenceResidual dataSet scale sequence slow
  *ℝ
  realProduct
    (componentsAt dataSet scale sequence)
    (λ component →
      componentApplication dataSet scale sequence component slow)

factorizedDensity :
  ∀ {trajectory split SlowField Sequence Component Step} →
  CMP119Equation218FactorizedFunctionalData
    {trajectory = trajectory} {split = split}
    SlowField Sequence Component Step →
  Nat → SlowField → ℝ
factorizedDensity dataSet scale slow =
  realSum
    (admissibleSequences dataSet scale)
    (λ sequence →
      sequenceApplication dataSet scale sequence slow)

asFunctionalDensityInputs :
  ∀ {trajectory split SlowField Sequence Component Step} →
  CMP119Equation218FactorizedFunctionalData
    {trajectory = trajectory} {split = split}
    SlowField Sequence Component Step →
  Functional.BetaDrivenFunctionalDensityInputs
    {trajectory = trajectory} {split = split} SlowField
asFunctionalDensityInputs dataSet = record
  { Functional.BetaDrivenFunctionalDensityInputs.betaHistory =
      betaHistory dataSet
  ; Functional.BetaDrivenFunctionalDensityInputs.densityAt =
      factorizedDensity dataSet
  ; Functional.BetaDrivenFunctionalDensityInputs.InSection2DensityClass =
      InSection2DensityClass dataSet
  ; Functional.BetaDrivenFunctionalDensityInputs.Section2ConditionsAndBounds =
      Section2ConditionsAndBounds dataSet
  ; Functional.BetaDrivenFunctionalDensityInputs.sourceScaleActive =
      sourceScaleActive dataSet
  }

equation218DensityIsFactorizedByConstruction :
  ∀ {trajectory split SlowField Sequence Component Step}
    (dataSet :
      CMP119Equation218FactorizedFunctionalData
        {trajectory = trajectory} {split = split}
        SlowField Sequence Component Step)
    scale slow →
  Functional.densityAt
    (asFunctionalDensityInputs dataSet) scale slow
  ≡
  realSum
    (admissibleSequences dataSet scale)
    (λ sequence →
      sequenceResidual dataSet scale sequence slow
      *ℝ
      realProduct
        (componentsAt dataSet scale sequence)
        (λ component →
          realProduct
            (orderedStepsAt dataSet scale sequence component)
            (λ step →
              oneStepValue dataSet
                scale sequence component step slow)))
equation218DensityIsFactorizedByConstruction dataSet scale slow = refl

componentEquation219FactorizationByConstruction :
  ∀ {trajectory split SlowField Sequence Component Step}
    (dataSet :
      CMP119Equation218FactorizedFunctionalData
        {trajectory = trajectory} {split = split}
        SlowField Sequence Component Step)
    scale sequence component slow →
  componentApplication dataSet scale sequence component slow
  ≡
  realProduct
    (orderedStepsAt dataSet scale sequence component)
    (λ step →
      oneStepValue dataSet
        scale sequence component step slow)
componentEquation219FactorizationByConstruction dataSet scale sequence component slow =
  refl

equation218FactorizedFiniteAlgebraLevel : ProofLevel
equation218FactorizedFiniteAlgebraLevel = machineChecked

equation219ComponentProductLevel : ProofLevel
equation219ComponentProductLevel = machineChecked

equation220OrderedStepProductLevel : ProofLevel
equation220OrderedStepProductLevel = machineChecked

equation218FunctionalDensityCompilerLevel : ProofLevel
equation218FunctionalDensityCompilerLevel = machineChecked

-- Remaining source extraction: identify the actual admissible domain sequences,
-- components, ordered one-step operations and residual sequence factor printed
-- in CMP119 (2.18)--(2.22) with this finite carrier.
literalCMP119Equation218IndexExtractionLevel : ProofLevel
literalCMP119Equation218IndexExtractionLevel = conditional

literalCMP119Equation219ComponentExtractionLevel : ProofLevel
literalCMP119Equation219ComponentExtractionLevel = conditional

literalCMP119Equation220StepExtractionLevel : ProofLevel
literalCMP119Equation220StepExtractionLevel = conditional
