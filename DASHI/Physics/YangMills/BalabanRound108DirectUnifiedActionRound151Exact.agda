{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanRound108DirectUnifiedActionRound151Exact where

------------------------------------------------------------------------
-- ROUND151: ROUND108 IS A DIRECT OR-ROUTE FROM BETA DENSITY TO THE BC1 ACTION
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanBetaDrivenDensityToCMP109116CarrierRound108Exact as R108
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132

record Round108DirectPresentCutActionRealization
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {History Cell : Set} {cutoff : Nat}
    (present : Present.PresentCutPhysicalSourceInputs History Cell cutoff)
    (family : R108.BetaDrivenLocalizedEffectiveActionFamily inputs) : Set₁ where
  field
    sourceScaleToDensityIndex :
      Source.Scale (Carrier.source (Present.bc1Carrier present)) → Nat

    presentBackgroundToRound108Background :
      Source.Background (Carrier.source (Present.bc1Carrier present)) →
      R108.Background family

    selectedRound108PotentialRepresentsBC1Potential :
      ∀ background →
      R108.potentialOfDensity family
        (BetaDensity.densityAt inputs
          (sourceScaleToDensityIndex
            (Carrier.scale (Present.bc1Carrier present))))
        (presentBackgroundToRound108Background background)
      ≡ Carrier.effectivePotential (Present.bc1Carrier present) background

open Round108DirectPresentCutActionRealization public

asUnifiedGeneratedActionDensity :
  ∀ {trajectory split inputs History Cell cutoff present family} →
  Round108DirectPresentCutActionRealization
    {trajectory = trajectory} {split = split} {inputs = inputs}
    {History = History} {Cell = Cell} {cutoff = cutoff}
    present family →
  R132.UnifiedGeneratedActionDensity
    {trajectory = trajectory} {split = split} {inputs = inputs} present
asUnifiedGeneratedActionDensity {inputs = inputs} {present = present}
    {family = family} realization = record
  { R132.UnifiedGeneratedActionDensity.sourceScaleToDensityIndex =
      sourceScaleToDensityIndex realization
  ; R132.UnifiedGeneratedActionDensity.effectivePotentialOfDensity =
      λ density background →
        R108.potentialOfDensity family density
          (presentBackgroundToRound108Background realization background)
  ; R132.UnifiedGeneratedActionDensity.selectedDensityRepresentsBC1EffectivePotential =
      selectedRound108PotentialRepresentsBC1Potential realization
  }

round108DirectSelectedDensityRepresentsBC1Potential :
  ∀ {trajectory split inputs History Cell cutoff present family}
    (realization : Round108DirectPresentCutActionRealization
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {History = History} {Cell = Cell} {cutoff = cutoff}
      present family) →
  ∀ background →
  R132.effectivePotentialOfDensity (asUnifiedGeneratedActionDensity realization)
    (BetaDensity.densityAt inputs
      (R132.selectedDensityIndex (asUnifiedGeneratedActionDensity realization)))
    background
  ≡ Carrier.effectivePotential (Present.bc1Carrier present) background
round108DirectSelectedDensityRepresentsBC1Potential realization =
  R132.selectedDensityRepresentsExactBC1Potential
    (asUnifiedGeneratedActionDensity realization)

round108ContinuationUsesLiteralBetaDensityPotential :
  ∀ {trajectory split inputs History Cell cutoff present family}
    (realization : Round108DirectPresentCutActionRealization
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {History = History} {Cell = Cell} {cutoff = cutoff}
      present family) →
  ∀ volume background →
  let k = sourceScaleToDensityIndex realization
            (Carrier.scale (Present.bc1Carrier present))
  in
  Source.cmp109EffectivePotential (R108.asCMP109116Continuation family)
      k volume background
  ≡ R108.potentialOfDensity family (BetaDensity.densityAt inputs k) background
round108ContinuationUsesLiteralBetaDensityPotential
    {present = present} {family = family} realization volume background =
  R108.cmp109PotentialIsLiteralBetaDrivenDensityPotential
    family
    (sourceScaleToDensityIndex realization
      (Carrier.scale (Present.bc1Carrier present)))
    volume background

round108DirectUnifiedActionCompilerLevel : ProofLevel
round108DirectUnifiedActionCompilerLevel = machineChecked

literalRound108DirectPresentCutActionRealizationLevel : ProofLevel
literalRound108DirectPresentCutActionRealizationLevel = conditional
