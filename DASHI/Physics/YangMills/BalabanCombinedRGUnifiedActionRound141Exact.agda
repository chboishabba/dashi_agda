{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCombinedRGUnifiedActionRound141Exact where

------------------------------------------------------------------------
-- ROUND141: CMP122 COMPLETE DENSITY -> COMBINED RG STATE -> BC1 ACTION
--
-- The merged Round52 dictionary proves that the source complete-density flow
-- and a repository CombinedRG state trajectory share the same admissibility
-- consequences, but it deliberately does not identify a Density value with a
-- repository State or recover an effective potential from that state.
--
-- This module adds exactly those semantic realization maps and then derives the
-- Round132 same-action weld.  Thus `effectivePotentialOfDensity` is no longer an
-- arbitrary primitive in the strongest producer route: it factors through the
-- already-owned literal CMP122 -> repository RG trajectory dictionary.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.Balaban1989LiteralCombinedRGDictionaryExact as Dictionary
import DASHI.Physics.YangMills.BalabanClayGate4CombinedRGUVIterationExact as UV
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132

record CompleteDensityEffectiveActionRealization
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {History Cell : Set} {cutoff : Nat}
    (present : Present.PresentCutPhysicalSourceInputs History Cell cutoff)
    {State Bound : Set}
    {normData : UV.CombinedOneStepPolymerNormData State Bound}
    {admissibility : UV.CombinedRGAdmissibility normData}
    (dictionary : Dictionary.LiteralCombinedRGDictionary
      {C = ℚ}
      {Den = BetaDensity.Density inputs}
      {St = State}
      {B = Bound}
      {flow = BetaDensity.betaDrivenCompleteDensityFlow inputs}
      {normData = normData}
      admissibility) : Set₁ where
  field
    sourceScaleToDensityIndex :
      Source.Scale (Carrier.source (Present.bc1Carrier present)) → Nat

    densityToRepositoryState : BetaDensity.Density inputs → State

    sourceDensityRealizesDictionaryState :
      ∀ k →
      densityToRepositoryState (BetaDensity.densityAt inputs k)
      ≡ Dictionary.state dictionary k

    repositoryStateEffectivePotential :
      State →
      Source.Background (Carrier.source (Present.bc1Carrier present)) → ℝ

    selectedDictionaryStateRepresentsBC1Potential :
      ∀ background →
      repositoryStateEffectivePotential
        (Dictionary.state dictionary
          (sourceScaleToDensityIndex
            (Carrier.scale (Present.bc1Carrier present))))
        background
      ≡ Carrier.effectivePotential (Present.bc1Carrier present) background

open CompleteDensityEffectiveActionRealization public

asUnifiedGeneratedActionDensity :
  ∀ {trajectory split inputs History Cell cutoff present State Bound normData admissibility dictionary} →
  CompleteDensityEffectiveActionRealization
    {trajectory = trajectory} {split = split} {inputs = inputs}
    {History = History} {Cell = Cell} {cutoff = cutoff}
    present {State = State} {Bound = Bound}
    {normData = normData} {admissibility = admissibility} dictionary →
  R132.UnifiedGeneratedActionDensity
    {trajectory = trajectory} {split = split} {inputs = inputs} present
asUnifiedGeneratedActionDensity {present = present} {dictionary = dictionary} realization = record
  { R132.UnifiedGeneratedActionDensity.sourceScaleToDensityIndex =
      sourceScaleToDensityIndex realization
  ; R132.UnifiedGeneratedActionDensity.effectivePotentialOfDensity =
      λ density →
        repositoryStateEffectivePotential realization
          (densityToRepositoryState realization density)
  ; R132.UnifiedGeneratedActionDensity.selectedDensityRepresentsBC1EffectivePotential =
      λ background →
        let k = sourceScaleToDensityIndex realization
                  (Carrier.scale (Present.bc1Carrier present))
        in
        trans
          (cong
            (λ state → repositoryStateEffectivePotential realization state background)
            (sourceDensityRealizesDictionaryState realization k))
          (selectedDictionaryStateRepresentsBC1Potential realization background)
  }

combinedRGSelectedDensityRepresentsBC1Potential :
  ∀ {trajectory split inputs History Cell cutoff present State Bound normData admissibility dictionary}
    (realization : CompleteDensityEffectiveActionRealization
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {History = History} {Cell = Cell} {cutoff = cutoff}
      present {State = State} {Bound = Bound}
      {normData = normData} {admissibility = admissibility} dictionary) →
  ∀ background →
  R132.effectivePotentialOfDensity (asUnifiedGeneratedActionDensity realization)
    (BetaDensity.densityAt inputs
      (R132.selectedDensityIndex (asUnifiedGeneratedActionDensity realization)))
    background
  ≡ Carrier.effectivePotential (Present.bc1Carrier present) background
combinedRGSelectedDensityRepresentsBC1Potential realization =
  R132.selectedDensityRepresentsExactBC1Potential
    (asUnifiedGeneratedActionDensity realization)

completeDensityEffectiveActionRealizationCompilerLevel : ProofLevel
completeDensityEffectiveActionRealizationCompilerLevel = machineChecked

-- Remaining source semantics are now sharply split:
--   Density -> repository RG State realization, and
--   selected repository RG State -> exact BC1 effective potential.
-- The older CMP122 dictionary supplies the RG trajectory/admissibility part;
-- it cannot by itself manufacture either semantic equality.
literalCompleteDensityEffectiveActionRealizationLevel : ProofLevel
literalCompleteDensityEffectiveActionRealizationLevel = conditional
