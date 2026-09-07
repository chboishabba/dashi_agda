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
-- expansion (2.18), parametrized by the localization-domain data, and that this
-- representation contains an effective action A_k.  Equation (2.23) then gives
-- the source decomposition of A_k, while (2.25)--(2.27) give the localized
-- analytic decomposition of its regular E_k part.
--
-- IMPORTANT SOURCE DISCIPLINE
--
-- The durable repository text is an OCR/search extract.  It is adequate for
-- identifying the source carrier and equation locators, but not for certifying
-- every coefficient/sign in (2.23).  This module therefore does NOT transcribe
-- the OCR-damaged algebraic formula as a machine theorem.  Instead it records
-- the least source-facing representation contract needed by the current
-- consumer: the action projection is part of the pre-existing CMP119 density
-- representation, before R108 or BC1 is constructed.
--
-- This removes the circular choice
--
--     choose Density -> Potential after seeing BC1
--
-- and replaces it by
--
--     source-represented density -> its own CMP119 A_k projection
--        -> R108 -> BC1.
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

    -- The action coordinate belonging to the Sect.2 representation of the SAME
    -- complete density.  It is not selected relative to a downstream target.
    effectiveActionOfDensity :
      Nat → Flow.Density inputs → Background → ℝ

    -- Source authority predicate: this projection is the A_k coordinate in the
    -- CMP119 Sect.2 representation (2.18), with its action structure located at
    -- (2.23) and regular localization at (2.25)--(2.27).
    IsCMP119Sect2EffectiveActionProjection :
      Nat → Flow.Density inputs → (Background → ℝ) → Set

    selectedDensityActionIsSourceProjection : ∀ scale →
      IsCMP119Sect2EffectiveActionProjection scale
        (Flow.densityAt inputs scale)
        (effectiveActionOfDensity scale (Flow.densityAt inputs scale))

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
      λ density background →
        -- A complete density belongs to a definite scale in the beta-driven
        -- sequence when consumed below.  The selected scale is supplied by the
        -- R108 family; the scale-indexed preferred semantics below avoids any
        -- post-hoc BC1 choice.
        effectiveActionOfDensity representation 0 density background
  }

-- The general scale-indexed projection is the actual preferred consumer.  It is
-- kept separate from the compatibility semantics above so no theorem silently
-- claims that all density values are represented at scale zero.
selectedEffectiveAction :
  ∀ {trajectory split inputs} →
  CMP119CompleteDensityActionRepresentation
    {trajectory = trajectory} {split = split} inputs →
  Nat → Background _ → ℝ
selectedEffectiveAction {inputs = inputs} representation scale =
  effectiveActionOfDensity representation scale (Flow.densityAt inputs scale)

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

------------------------------------------------------------------------
-- AUTHORITY BOUNDARY
------------------------------------------------------------------------

cmp119DensityActionProjectionPackagingLevel : ProofLevel
cmp119DensityActionProjectionPackagingLevel = machineChecked

-- Published source authority for the existence/meaning of A_k inside the Sect.2
-- density representation.  Exact repository instantiation must bind the literal
-- source density carrier and verify the equation/formula against the source PDF.
cmp119Sect2DensityContainsEffectiveActionLevel : ProofLevel
cmp119Sect2DensityContainsEffectiveActionLevel = standardImported

literalCMP119DensityEffectiveActionProjectionLevel : ProofLevel
literalCMP119DensityEffectiveActionProjectionLevel = conditional
