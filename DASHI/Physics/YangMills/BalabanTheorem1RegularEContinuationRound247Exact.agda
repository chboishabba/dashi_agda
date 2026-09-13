{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanTheorem1RegularEContinuationRound247Exact where

------------------------------------------------------------------------
-- ROUND247 / CMP119 THEOREM 1 -> PREFERRED CMP109/CMP116 CONTINUATION
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.Balaban1989Theorem1UVStabilityExact as Source
import DASHI.Physics.YangMills.BalabanCMP119RegularESection2PredicateRound246Exact as R246
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Continue
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as FiniteBeta
import DASHI.Physics.YangMills.Balaban1989FiniteModeInverseSquareTerminalHistoryExact as FiniteHistory
import DASHI.Physics.YangMills.Balaban1989ActiveScaleTheorem1BetaBridgeExact as Active

------------------------------------------------------------------------
-- Legacy all-Nat continuation retained for compatibility.
------------------------------------------------------------------------

asCMP109116Continuation :
  ∀ {trajectory split history}
    {dataSet : R246.BetaDrivenRegularESection2Inputs
      {trajectory = trajectory} {split = split} history} →
  Source.Balaban1989Theorem1Witness
    (Beta.betaDrivenCompleteDensityFlow
      (R246.asBetaDrivenCompleteDensityInputs dataSet)) →
  (Tangent : Set) →
  Continue.CMP109116LiteralEffectiveActionContinuation
asCMP109116Continuation {dataSet = dataSet} theorem1 Tangent = record
  { Continue.CMP109116LiteralEffectiveActionContinuation.Scale = Nat
  ; Continue.CMP109116LiteralEffectiveActionContinuation.Volume = R246.Volume dataSet
  ; Continue.CMP109116LiteralEffectiveActionContinuation.Background = R246.Background dataSet
  ; Continue.CMP109116LiteralEffectiveActionContinuation.Tangent = Tangent
  ; Continue.CMP109116LiteralEffectiveActionContinuation.Component = R246.Component dataSet
  ; Continue.CMP109116LiteralEffectiveActionContinuation.components =
      λ scale volume → R246.components (R246.regularEFormFromTheorem1 theorem1 scale) volume
  ; Continue.CMP109116LiteralEffectiveActionContinuation.cmp116PhysicalLocalizedActivity =
      λ scale volume component →
        R246.localizedRegularActivity
          (R246.regularEFormFromTheorem1 theorem1 scale) volume component
  ; Continue.CMP109116LiteralEffectiveActionContinuation.cmp109EffectivePotential =
      λ scale _ → R246.regularE (R246.regularEFormFromTheorem1 theorem1 scale)
  ; Continue.CMP109116LiteralEffectiveActionContinuation.effectivePotentialIsLocalizedCompositeSum =
      λ scale volume →
        R246.regularEIsLocalizedCompositeSum
          (R246.regularEFormFromTheorem1 theorem1 scale) volume
  }

continuationPotentialIsTheorem1RegularE :
  ∀ {trajectory split history}
    {dataSet : R246.BetaDrivenRegularESection2Inputs
      {trajectory = trajectory} {split = split} history}
    (theorem1 : Source.Balaban1989Theorem1Witness
      (Beta.betaDrivenCompleteDensityFlow
        (R246.asBetaDrivenCompleteDensityInputs dataSet)))
    (Tangent : Set) →
  ∀ scale volume background →
  Continue.cmp109EffectivePotential
    (asCMP109116Continuation theorem1 Tangent)
    scale volume background
  ≡ R246.regularE (R246.regularEFormFromTheorem1 theorem1 scale) background
continuationPotentialIsTheorem1RegularE theorem1 Tangent scale volume background = refl

------------------------------------------------------------------------
-- Preferred active-scale continuation.
--
-- Round246 recovered the actual source index discipline: CMP122 Theorem 1 is
-- available on the finite-history ActiveScale fibre, not on every Nat.  Package
-- the scale together with its source-active witness and use that fibre itself as
-- the continuation Scale.  This removes the stale all-Nat obligation without
-- weakening or post-hoc extending the source theorem.
------------------------------------------------------------------------

record ActiveScaleIndex
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {Mode Atom : Set}
    {betaData : FiniteBeta.FiniteModeBetaTrajectoryData trajectory Mode Atom}
    (history : FiniteHistory.FiniteModeInverseSquareTerminalHistoryData
      trajectory Mode Atom betaData) : Set where
  constructor active-scale-index
  field
    scale : Nat
    active : FiniteHistory.ActiveScale history scale

open ActiveScaleIndex public

asActiveCMP109116Continuation :
  ∀ {trajectory Mode Atom betaData history}
    {dataSet : R246.ActiveRegularESection2Inputs
      {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
      betaData history} →
  Active.ActiveBalaban1989Theorem1Witness
    (R246.asActiveRegularESection2Flow dataSet) →
  (Tangent : Set) →
  Continue.CMP109116LiteralEffectiveActionContinuation
asActiveCMP109116Continuation
    {history = history} {dataSet = dataSet} theorem1 Tangent = record
  { Continue.CMP109116LiteralEffectiveActionContinuation.Scale = ActiveScaleIndex history
  ; Continue.CMP109116LiteralEffectiveActionContinuation.Volume =
      R246.ActiveRegularESection2Inputs.Volume dataSet
  ; Continue.CMP109116LiteralEffectiveActionContinuation.Background =
      R246.ActiveRegularESection2Inputs.Background dataSet
  ; Continue.CMP109116LiteralEffectiveActionContinuation.Tangent = Tangent
  ; Continue.CMP109116LiteralEffectiveActionContinuation.Component =
      R246.ActiveRegularESection2Inputs.Component dataSet
  ; Continue.CMP109116LiteralEffectiveActionContinuation.components =
      λ index volume →
        R246.components
          (R246.activeRegularEFormFromTheorem1 theorem1
            (scale index) (active index))
          volume
  ; Continue.CMP109116LiteralEffectiveActionContinuation.cmp116PhysicalLocalizedActivity =
      λ index volume component →
        R246.localizedRegularActivity
          (R246.activeRegularEFormFromTheorem1 theorem1
            (scale index) (active index))
          volume component
  ; Continue.CMP109116LiteralEffectiveActionContinuation.cmp109EffectivePotential =
      λ index _ →
        R246.regularE
          (R246.activeRegularEFormFromTheorem1 theorem1
            (scale index) (active index))
  ; Continue.CMP109116LiteralEffectiveActionContinuation.effectivePotentialIsLocalizedCompositeSum =
      λ index volume →
        R246.regularEIsLocalizedCompositeSum
          (R246.activeRegularEFormFromTheorem1 theorem1
            (scale index) (active index))
          volume
  }

activeContinuationPotentialIsTheorem1RegularE :
  ∀ {trajectory Mode Atom betaData history}
    {dataSet : R246.ActiveRegularESection2Inputs
      {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
      betaData history}
    (theorem1 : Active.ActiveBalaban1989Theorem1Witness
      (R246.asActiveRegularESection2Flow dataSet))
    (Tangent : Set) →
  ∀ index volume background →
  Continue.cmp109EffectivePotential
    (asActiveCMP109116Continuation theorem1 Tangent)
    index volume background
  ≡ R246.regularE
      (R246.activeRegularEFormFromTheorem1 theorem1
        (scale index) (active index))
      background
activeContinuationPotentialIsTheorem1RegularE theorem1 Tangent index volume background = refl

------------------------------------------------------------------------
-- Least-privilege active continuation.
--
-- The CMP109/CMP116 continuation consumes only the regular-E/localization form.
-- It does not consume the independent quantitative Section-2 bounds.  Accept the
-- projected form witness directly so source acquisition and downstream payment
-- are not coupled more strongly than the consumer requires.
------------------------------------------------------------------------

asActiveCMP109116ContinuationFromRegularEForm :
  ∀ {trajectory Mode Atom betaData history}
    {dataSet : R246.ActiveRegularESection2Inputs
      {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
      betaData history} →
  R246.ActiveRegularESection2FormWitness dataSet →
  (Tangent : Set) →
  Continue.CMP109116LiteralEffectiveActionContinuation
asActiveCMP109116ContinuationFromRegularEForm
    {history = history} {dataSet = dataSet} formWitness Tangent = record
  { Continue.CMP109116LiteralEffectiveActionContinuation.Scale = ActiveScaleIndex history
  ; Continue.CMP109116LiteralEffectiveActionContinuation.Volume =
      R246.ActiveRegularESection2Inputs.Volume dataSet
  ; Continue.CMP109116LiteralEffectiveActionContinuation.Background =
      R246.ActiveRegularESection2Inputs.Background dataSet
  ; Continue.CMP109116LiteralEffectiveActionContinuation.Tangent = Tangent
  ; Continue.CMP109116LiteralEffectiveActionContinuation.Component =
      R246.ActiveRegularESection2Inputs.Component dataSet
  ; Continue.CMP109116LiteralEffectiveActionContinuation.components =
      λ index volume →
        R246.components
          (R246.regularEFormOnActiveScale formWitness
            (scale index) (active index))
          volume
  ; Continue.CMP109116LiteralEffectiveActionContinuation.cmp116PhysicalLocalizedActivity =
      λ index volume component →
        R246.localizedRegularActivity
          (R246.regularEFormOnActiveScale formWitness
            (scale index) (active index))
          volume component
  ; Continue.CMP109116LiteralEffectiveActionContinuation.cmp109EffectivePotential =
      λ index _ →
        R246.regularE
          (R246.regularEFormOnActiveScale formWitness
            (scale index) (active index))
  ; Continue.CMP109116LiteralEffectiveActionContinuation.effectivePotentialIsLocalizedCompositeSum =
      λ index volume →
        R246.regularEIsLocalizedCompositeSum
          (R246.regularEFormOnActiveScale formWitness
            (scale index) (active index))
          volume
  }

activeContinuationPotentialIsRegularEFormWitness :
  ∀ {trajectory Mode Atom betaData history}
    {dataSet : R246.ActiveRegularESection2Inputs
      {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
      betaData history}
    (formWitness : R246.ActiveRegularESection2FormWitness dataSet)
    (Tangent : Set) →
  ∀ index volume background →
  Continue.cmp109EffectivePotential
    (asActiveCMP109116ContinuationFromRegularEForm formWitness Tangent)
    index volume background
  ≡ R246.regularE
      (R246.regularEFormOnActiveScale formWitness
        (scale index) (active index))
      background
activeContinuationPotentialIsRegularEFormWitness formWitness Tangent index volume background = refl

theorem1RegularEContinuationCompilerLevel : ProofLevel
theorem1RegularEContinuationCompilerLevel = machineChecked

activeTheorem1RegularEContinuationCompilerLevel : ProofLevel
activeTheorem1RegularEContinuationCompilerLevel = machineChecked

activeRegularEFormWitnessContinuationCompilerLevel : ProofLevel
activeRegularEFormWitnessContinuationCompilerLevel = machineChecked

-- The literal physical/source payment is now the Section-2 predicate binding on
-- the exact beta-driven flow.  The imported Theorem-1 authority then yields the
-- regular E_k function and its localized decomposition on every selected scale.
literalCMP119RegularESection2PredicateInstantiationLevel : ProofLevel
literalCMP119RegularESection2PredicateInstantiationLevel =
  R246.literalCMP119RegularESection2PredicateInstantiationLevel

-- Preferred source-shaped payment: instantiate the active finite-history density
-- family with the consumer-minimal regular-E/localization Section-2 predicate.
-- Once that source witness is supplied, the active-scale CMP109/CMP116 carrier
-- above is compiler output rather than an additional analytic theorem.
literalActiveCMP119RegularESection2PredicateInstantiationLevel : ProofLevel
literalActiveCMP119RegularESection2PredicateInstantiationLevel =
  R246.literalCMP119RegularESection2PredicateInstantiationLevel

-- Least-privilege payment after projection: the continuation needs only the
-- active regular-E/localization form witness, not the independent Section-2
-- quantitative-bounds component of the full CMP122 witness.
literalActiveCMP119RegularESection2FormWitnessLevel : ProofLevel
literalActiveCMP119RegularESection2FormWitnessLevel =
  R246.literalActiveCMP119RegularESection2FormWitnessLevel
