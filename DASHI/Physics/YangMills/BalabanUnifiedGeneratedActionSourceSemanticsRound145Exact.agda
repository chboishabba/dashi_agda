{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionSourceSemanticsRound145Exact where

------------------------------------------------------------------------
-- ROUND145: SOURCE-FIX THE DENSITY -> EFFECTIVE-ACTION SEMANTICS
--
-- BIDI / proof-search correction.
--
-- Round132 correctly kept the CMP122 density carrier distinct from the BC1
-- effective-potential carrier, but its interpretation function was a field of
-- the SAME record as the desired selected-density equality.  Consequently the
-- interface admits the degenerate choice
--
--   density |-> exact BC1 potential
--
-- for every density.  The selected equality is then refl, independently of the
-- source meaning of the CMP122 density.  That is too weak to certify physical
-- same-object provenance.
--
-- This module does two things:
--
--  1. proves the degenerate Round132 construction explicitly;
--  2. moves density interpretation outside the weld.  A strengthened weld is
--     indexed by a PRE-EXISTING source semantics and may only prove that the
--     selected source density, under that fixed interpretation, is the exact
--     BC1 potential.
--
-- This is a consumer correction, not a Clay promotion.  The source-facing leaf
-- becomes exactly: instantiate the physical CMP122 density interpretation and
-- prove its selected-scale equality with the BC1 generated action.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132

------------------------------------------------------------------------
-- Exact no-go audit for the old consumer shape.
------------------------------------------------------------------------

round132ConstantRepresentation :
  ∀ {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {History Cell : Set} {cutoff : Nat}
    (present : Present.PresentCutPhysicalSourceInputs History Cell cutoff)
    (sourceScaleToDensityIndex :
      Source.Scale (Carrier.source (Present.bc1Carrier present)) → Nat) →
  R132.UnifiedGeneratedActionDensity
    {trajectory = trajectory} {split = split} {inputs = inputs} present
round132ConstantRepresentation present sourceScaleToDensityIndex = record
  { R132.UnifiedGeneratedActionDensity.sourceScaleToDensityIndex =
      sourceScaleToDensityIndex
  ; R132.UnifiedGeneratedActionDensity.effectivePotentialOfDensity =
      λ _ → Carrier.effectivePotential (Present.bc1Carrier present)
  ; R132.UnifiedGeneratedActionDensity.selectedDensityRepresentsBC1EffectivePotential =
      λ _ → refl
  }

-- Therefore inhabiting Round132 alone is not evidence that its chosen
-- `effectivePotentialOfDensity` is the source semantics of the CMP122 density.
-- The strengthened object below removes that choice from the weld.

------------------------------------------------------------------------
-- Source-fixed semantics.
------------------------------------------------------------------------

record FixedEffectiveDensitySemantics
    {trajectory split}
    (inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split})
    {History Cell : Set} {cutoff : Nat}
    (present : Present.PresentCutPhysicalSourceInputs History Cell cutoff) : Set₁ where
  field
    interpretDensity :
      BetaDensity.Density inputs →
      Source.Background (Carrier.source (Present.bc1Carrier present)) → ℝ

open FixedEffectiveDensitySemantics public

record SourceSemanticUnifiedGeneratedActionDensity
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {History Cell : Set} {cutoff : Nat}
    (present : Present.PresentCutPhysicalSourceInputs History Cell cutoff)
    (semantics : FixedEffectiveDensitySemantics inputs present) : Set₁ where
  field
    sourceScaleToDensityIndex :
      Source.Scale (Carrier.source (Present.bc1Carrier present)) → Nat

    selectedSourceDensityRepresentsBC1EffectivePotential :
      ∀ background →
      interpretDensity semantics
        (BetaDensity.densityAt inputs
          (sourceScaleToDensityIndex
            (Carrier.scale (Present.bc1Carrier present))))
        background
      ≡ Carrier.effectivePotential (Present.bc1Carrier present) background

open SourceSemanticUnifiedGeneratedActionDensity public

asRound132 :
  ∀ {trajectory split inputs History Cell cutoff present semantics} →
  SourceSemanticUnifiedGeneratedActionDensity
    {trajectory = trajectory} {split = split} {inputs = inputs}
    {History = History} {Cell = Cell} {cutoff = cutoff}
    present semantics →
  R132.UnifiedGeneratedActionDensity
    {trajectory = trajectory} {split = split} {inputs = inputs} present
asRound132 {semantics = semantics} weld = record
  { R132.UnifiedGeneratedActionDensity.sourceScaleToDensityIndex =
      sourceScaleToDensityIndex weld
  ; R132.UnifiedGeneratedActionDensity.effectivePotentialOfDensity =
      interpretDensity semantics
  ; R132.UnifiedGeneratedActionDensity.selectedDensityRepresentsBC1EffectivePotential =
      selectedSourceDensityRepresentsBC1EffectivePotential weld
  }

selectedSourceDensityRepresentsExactBC1Potential :
  ∀ {trajectory split inputs History Cell cutoff present semantics}
    (weld : SourceSemanticUnifiedGeneratedActionDensity
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {History = History} {Cell = Cell} {cutoff = cutoff}
      present semantics) →
  ∀ background →
  interpretDensity semantics
    (BetaDensity.densityAt inputs
      (R132.selectedDensityIndex (asRound132 weld)))
    background
  ≡ Carrier.effectivePotential (Present.bc1Carrier present) background
selectedSourceDensityRepresentsExactBC1Potential weld =
  R132.selectedDensityRepresentsExactBC1Potential (asRound132 weld)

------------------------------------------------------------------------
-- Proof-search / authority boundary.
------------------------------------------------------------------------

round132ConstantRepresentationAuditLevel : ProofLevel
round132ConstantRepresentationAuditLevel = machineChecked

sourceSemanticRound132CompilerLevel : ProofLevel
sourceSemanticRound132CompilerLevel = machineChecked

-- Physical leaves.  These must come from the literal source realization, not
-- from choosing an interpretation after seeing the BC1 target.
literalCMP122EffectiveDensitySemanticsRound145Level : ProofLevel
literalCMP122EffectiveDensitySemanticsRound145Level = conditional

literalSelectedCMP122DensityIsBC1GeneratedActionRound145Level : ProofLevel
literalSelectedCMP122DensityIsBC1GeneratedActionRound145Level = conditional
