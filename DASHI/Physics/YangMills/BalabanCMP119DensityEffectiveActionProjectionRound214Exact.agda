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
--
-- ARCHAEOLOGY REFINEMENT (2026-09-11): Round58 already owns a raw CMP119 state
-- with scale-indexed effectiveDensity k and effectiveAction k.  The live source
-- seam is therefore not to invent another A_k.  It is to interpret those raw
-- action objects as the density-indexed Background -> Real source semantics used
-- here, while proving that the selected density/action pairs are the SAME raw
-- CMP119 pairs.  The bridge below makes that residual explicit without allowing
-- BC1 to choose the interpretation after the fact.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Flow
import DASHI.Physics.YangMills.BalabanSourceFixedR108EffectiveActionFamilyRound213Exact as Fixed
import DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact as Raw

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
-- RAW ROUND58 SOURCE PAIRS -> ROUND214 SOURCE SEMANTICS
------------------------------------------------------------------------
--
-- The raw source carrier deliberately leaves `Action` abstract.  This bridge
-- asks for exactly the missing interpretation of that already-existing object:
--
--   Density -> Action,
--   Action -> Background -> Real,
--
-- together with selected-scale receipts identifying the chosen density/action
-- with Raw.effectiveDensity k / Raw.effectiveAction k.  Source authority is
-- stated on the raw A_k itself; the compiler transports it through the selected
-- action identity.  No BC1 object occurs in this record.
------------------------------------------------------------------------

record RawCMP119DensityActionInterpretation
    {trajectory split}
    (inputs : Flow.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split})
    {RawBackground Fluctuation Action WilsonTerm SmallFieldTerm
      RTerm BoundaryTerm Vacuum : Set}
    (source : Raw.CMP119SourceNativeRawState
      (Flow.Density inputs) RawBackground Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum) : Set₁ where
  field
    actionOfDensity : Flow.Density inputs → Action
    evaluateAction : Action → RawBackground → ℝ

    selectedDensityIsRawDensity : ∀ scale →
      Flow.densityAt inputs scale ≡ Raw.effectiveDensity source scale

    selectedActionIsRawAction : ∀ scale →
      actionOfDensity (Flow.densityAt inputs scale)
      ≡ Raw.effectiveAction source scale

    IsCMP119Sect2EffectiveActionProjection :
      Nat → Flow.Density inputs → (RawBackground → ℝ) → Set

    rawSelectedActionHasSourceAuthority : ∀ scale →
      IsCMP119Sect2EffectiveActionProjection scale
        (Flow.densityAt inputs scale)
        (λ background →
          evaluateAction (Raw.effectiveAction source scale) background)

open RawCMP119DensityActionInterpretation public

rawInterpretationAsCompleteDensityActionRepresentation :
  ∀ {trajectory split inputs
      RawBackground Fluctuation Action WilsonTerm SmallFieldTerm
      RTerm BoundaryTerm Vacuum source} →
  RawCMP119DensityActionInterpretation
    {trajectory = trajectory} {split = split} inputs
    {RawBackground} {Fluctuation} {Action} {WilsonTerm} {SmallFieldTerm}
    {RTerm} {BoundaryTerm} {Vacuum} source →
  CMP119CompleteDensityActionRepresentation inputs
rawInterpretationAsCompleteDensityActionRepresentation
    {RawBackground = RawBackground} {source = source} bridge = record
  { CMP119CompleteDensityActionRepresentation.Background = RawBackground
  ; CMP119CompleteDensityActionRepresentation.effectiveActionOfDensity =
      λ density background →
        evaluateAction bridge (actionOfDensity bridge density) background
  ; CMP119CompleteDensityActionRepresentation.IsCMP119Sect2EffectiveActionProjection =
      IsCMP119Sect2EffectiveActionProjection bridge
  ; CMP119CompleteDensityActionRepresentation.selectedDensityActionIsSourceProjection =
      λ scale → selectedAuthority scale
  }
  where
  selectedAuthority : ∀ scale →
    IsCMP119Sect2EffectiveActionProjection bridge scale
      (Flow.densityAt inputs scale)
      (λ background →
        evaluateAction bridge
          (actionOfDensity bridge (Flow.densityAt inputs scale))
          background)
  selectedAuthority scale
    rewrite selectedActionIsRawAction bridge scale =
      rawSelectedActionHasSourceAuthority bridge scale

rawSelectedDensityIdentity :
  ∀ {trajectory split inputs
      RawBackground Fluctuation Action WilsonTerm SmallFieldTerm
      RTerm BoundaryTerm Vacuum source}
    (bridge : RawCMP119DensityActionInterpretation
      {trajectory = trajectory} {split = split} inputs
      {RawBackground} {Fluctuation} {Action} {WilsonTerm} {SmallFieldTerm}
      {RTerm} {BoundaryTerm} {Vacuum} source) →
  ∀ scale →
  Flow.densityAt inputs scale ≡ Raw.effectiveDensity source scale
rawSelectedDensityIdentity bridge = selectedDensityIsRawDensity bridge

rawSelectedActionIdentity :
  ∀ {trajectory split inputs
      RawBackground Fluctuation Action WilsonTerm SmallFieldTerm
      RTerm BoundaryTerm Vacuum source}
    (bridge : RawCMP119DensityActionInterpretation
      {trajectory = trajectory} {split = split} inputs
      {RawBackground} {Fluctuation} {Action} {WilsonTerm} {SmallFieldTerm}
      {RTerm} {BoundaryTerm} {Vacuum} source) →
  ∀ scale →
  actionOfDensity bridge (Flow.densityAt inputs scale)
  ≡ Raw.effectiveAction source scale
rawSelectedActionIdentity bridge = selectedActionIsRawAction bridge

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

rawCMP119DensityActionInterpretationCompilerLevel : ProofLevel
rawCMP119DensityActionInterpretationCompilerLevel = machineChecked

cmp119Sect2DensityContainsEffectiveActionLevel : ProofLevel
cmp119Sect2DensityContainsEffectiveActionLevel = standardImported

-- Physical/source leaf: instantiate the raw density/action interpretation on the
-- literal finite-history CMP119 source family and check the selected A_k source
-- formula against the primary source.  R108/BC1 remain downstream and cannot
-- define this interpretation.
literalCMP119DensityEffectiveActionProjectionLevel : ProofLevel
literalCMP119DensityEffectiveActionProjectionLevel = conditional
