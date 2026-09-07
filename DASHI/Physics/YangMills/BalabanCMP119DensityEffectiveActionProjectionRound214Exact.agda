{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP119DensityEffectiveActionProjectionRound214Exact where

------------------------------------------------------------------------
-- ROUND214 / CMP119 SECT.2 DENSITY -> EFFECTIVE-ACTION PROJECTION
--
-- SOURCE LOCATOR
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- Sect.2 states that the k-th effective density rho_k(V_k) is represented by the
-- expansion (2.18), parametrized by localization-domain data, and that this
-- representation contains an effective action A_k.  Equation (2.23) gives the
-- source decomposition of A_k; (2.25)--(2.27) give the localized analytic
-- decomposition of its regular E_k part.
--
-- IMPORTANT SOURCE DISCIPLINE
--
-- The durable repository text is an OCR/search extract.  It identifies the
-- source carrier and equation locators but is not authority for every damaged
-- coefficient/sign in (2.23).  We therefore do not transcribe that OCR algebra
-- as a machine theorem here.  Instead we formalize the exact representation
-- coordinate required by the consumer: each complete-density object carries its
-- own source effective-action projection before R108 or BC1 is constructed.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Flow
import DASHI.Physics.YangMills.BalabanSourceFixedR108EffectiveActionFamilyRound213Exact as Fixed

------------------------------------------------------------------------
-- LITERAL SOURCE REPRESENTATION CONTRACT
------------------------------------------------------------------------

record CMP119CompleteDensityActionRepresentation
    {trajectory split}
    (inputs : Flow.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}) : Set₁ where
  field
    Background : Set

    -- Source meaning of a complete density.  The scale is NOT an argument of
    -- this map: a density object denotes its own action.  Scale appears only in
    -- the witness below saying that the selected densityAt scale is the Sect.2
    -- rho_k whose action coordinate is A_k.
    effectiveActionOfDensity :
      Flow.Density inputs → Background → ℝ

    IsCMP119Sect2EffectiveActionProjection :
      Nat → Flow.Density inputs → (Background → ℝ) → Set

    selectedDensityActionIsSourceProjection : ∀ scale →
      IsCMP119Sect2EffectiveActionProjection scale
        (Flow.densityAt inputs scale)
        (effectiveActionOfDensity (Flow.densityAt inputs scale))

open CMP119CompleteDensityActionRepresentation public

------------------------------------------------------------------------
-- SOURCE REPRESENTATION -> R108 FIXED SEMANTICS
------------------------------------------------------------------------

asFixedR108EffectiveDensitySemantics :
  ∀ {trajectory split inputs} →
  CMP119CompleteDensityActionRepresentation
    {trajectory = trajectory} {split = split} inputs →
  Fixed.FixedR108EffectiveDensitySemantics inputs
asFixedR108EffectiveDensitySemantics representation = record
  { Fixed.FixedR108EffectiveDensitySemantics.Background =
      Background representation
  ; Fixed.FixedR108EffectiveDensitySemantics.interpretDensity =
      effectiveActionOfDensity representation
  }

selectedEffectiveAction :
  ∀ {trajectory split inputs} →
  CMP119CompleteDensityActionRepresentation
    {trajectory = trajectory} {split = split} inputs →
  Nat → Background _ → ℝ
selectedEffectiveAction {inputs = inputs} representation scale =
  effectiveActionOfDensity representation (Flow.densityAt inputs scale)

selectedEffectiveActionHasCMP119SourceAuthority :
  ∀ {trajectory split inputs}
    (representation : CMP119CompleteDensityActionRepresentation
      {trajectory = trajectory} {split = split} inputs) →
  ∀ scale →
  IsCMP119Sect2EffectiveActionProjection representation scale
    (Flow.densityAt inputs scale)
    (selectedEffectiveAction representation scale)
selectedEffectiveActionHasCMP119SourceAuthority representation scale =
  selectedDensityActionIsSourceProjection representation scale

fixedR108SemanticsIsCMP119EffectiveAction :
  ∀ {trajectory split inputs}
    (representation : CMP119CompleteDensityActionRepresentation
      {trajectory = trajectory} {split = split} inputs) →
  ∀ density background →
  Fixed.interpretDensity (asFixedR108EffectiveDensitySemantics representation)
      density background
  ≡ effectiveActionOfDensity representation density background
fixedR108SemanticsIsCMP119EffectiveAction representation density background = refl

------------------------------------------------------------------------
-- AUTHORITY BOUNDARY
------------------------------------------------------------------------

cmp119DensityActionProjectionPackagingLevel : ProofLevel
cmp119DensityActionProjectionPackagingLevel = machineChecked

cmp119Sect2DensityContainsEffectiveActionLevel : ProofLevel
cmp119Sect2DensityContainsEffectiveActionLevel = standardImported

-- Physical/source leaf: instantiate this projection on the literal CMP119/122
-- complete-density carrier and check the source formula against the source PDF.
literalCMP119DensityEffectiveActionProjectionLevel : ProofLevel
literalCMP119DensityEffectiveActionProjectionLevel = conditional
