{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyS1LiteralActiveRegularEASTExact where

------------------------------------------------------------------------
-- S1 EXACT OPEN LEMMA / TYPED AST.
--
-- Overlay AA leaves one S1 source payment: on the selected beta-driven source,
-- every ACTUAL active finite-history scale carries the literal CMP119 regular-E
-- / CMP116 localization form.  Nothing quantitative from the rest of CMP122
-- Theorem 1 is consumed by the preferred cosmology route.
--
-- This file makes the residual fail-closed.  The four fields below are the
-- entire unproved AST at each active scale:
--
--   I1  literal regular E_k : PublishedB -> R;
--   I2  literal localized component family;
--   I3  literal CMP116 localized activities;
--   I4  exact source equality E_k = finite sum of those same activities.
--
-- The active-scale witness is an index, not a fifth invariant.  No all-Nat
-- extension, quantitative Section-2 package, post-hoc Background equality, or
-- ten independent tangent choices are admitted here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanCMP119RegularESection2PredicateRound246Exact as R246
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as FiniteBeta
import DASHI.Physics.YangMills.Balaban1989FiniteModeInverseSquareTerminalHistoryExact as History

record LiteralActiveRegularEFormAt
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {Mode Atom : Set}
    {betaData : FiniteBeta.FiniteModeBetaTrajectoryData trajectory Mode Atom}
    {history : History.FiniteModeInverseSquareTerminalHistoryData
      trajectory Mode Atom betaData}
    (dataSet : R246.ActiveRegularESection2Inputs
      {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
      betaData history)
    (scale : Nat)
    (active : History.ActiveScale history scale) : Set₁ where
  field
    -- I1: the literal source regular effective action at this active scale.
    regularE :
      R246.ActiveRegularESection2Inputs.Background dataSet → ℝ

    -- I2: the literal finite localized component family.
    components :
      R246.ActiveRegularESection2Inputs.Volume dataSet →
      List (R246.ActiveRegularESection2Inputs.Component dataSet)

    -- I3: the literal CMP116 localized activity on the SAME Background carrier.
    localizedRegularActivity :
      R246.ActiveRegularESection2Inputs.Volume dataSet →
      R246.ActiveRegularESection2Inputs.Component dataSet →
      R246.ActiveRegularESection2Inputs.Background dataSet → ℝ

    -- I4: the exact source identity; no numerical/analytic bound is substituted
    -- for this same-object equality.
    regularEIsLocalizedCompositeSum :
      ∀ volume background →
      regularE background
      ≡ Finite.sumFunctions
          (Finite.mapList
            (localizedRegularActivity volume)
            (components volume))
          background

open LiteralActiveRegularEFormAt public

-- Exact typed AST of the surviving S1 lemma.
LiteralActiveRegularEFormLemma :
  ∀ {trajectory Mode Atom betaData history} →
  (dataSet : R246.ActiveRegularESection2Inputs
    {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
    betaData history) → Set₁
LiteralActiveRegularEFormLemma {history = history} dataSet =
  ∀ scale →
  (active : History.ActiveScale history scale) →
  LiteralActiveRegularEFormAt dataSet scale active

-- The AST is definitionally sufficient to inhabit the existing least-privilege
-- Round246 witness.  Hence the new record introduces no extra theorem below S1.
asCMP119RegularESection2Form :
  ∀ {trajectory Mode Atom betaData history dataSet scale active} →
  LiteralActiveRegularEFormAt
    {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
    {betaData = betaData} {history = history}
    dataSet scale active →
  R246.CMP119RegularESection2Form
    (R246.ActiveRegularESection2Inputs.Density dataSet)
    (R246.ActiveRegularESection2Inputs.Background dataSet)
    (R246.ActiveRegularESection2Inputs.Volume dataSet)
    (R246.ActiveRegularESection2Inputs.Component dataSet)
    scale
    (R246.ActiveRegularESection2Inputs.densityAt dataSet scale)
asCMP119RegularESection2Form ast = record
  { R246.CMP119RegularESection2Form.regularE = regularE ast
  ; R246.CMP119RegularESection2Form.components = components ast
  ; R246.CMP119RegularESection2Form.localizedRegularActivity =
      localizedRegularActivity ast
  ; R246.CMP119RegularESection2Form.regularEIsLocalizedCompositeSum =
      regularEIsLocalizedCompositeSum ast
  }

compileActiveRegularESection2FormWitness :
  ∀ {trajectory Mode Atom betaData history}
    {dataSet : R246.ActiveRegularESection2Inputs
      {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
      betaData history} →
  LiteralActiveRegularEFormLemma dataSet →
  R246.ActiveRegularESection2FormWitness dataSet
compileActiveRegularESection2FormWitness ast = record
  { R246.ActiveRegularESection2FormWitness.regularEFormOnActiveScale =
      λ scale active → asCMP119RegularESection2Form (ast scale active)
  }

------------------------------------------------------------------------
-- Closed-world residual ledger.
------------------------------------------------------------------------

unprovenInvariantCount : Nat
unprovenInvariantCount = 4

literalRegularEObjectRequired : Bool
literalRegularEObjectRequired = true

literalLocalizedComponentFamilyRequired : Bool
literalLocalizedComponentFamilyRequired = true

literalLocalizedActivityObjectRequired : Bool
literalLocalizedActivityObjectRequired = true

literalLocalizedCompositeSumEqualityRequired : Bool
literalLocalizedCompositeSumEqualityRequired = true

requiresInactiveScaleExtension : Bool
requiresInactiveScaleExtension = false

requiresFullSection2QuantitativePackage : Bool
requiresFullSection2QuantitativePackage = false

requiresPostHocBackgroundEquality : Bool
requiresPostHocBackgroundEquality = false

requiresIndependentTenTangentChoices : Bool
requiresIndependentTenTangentChoices = false

astCompilesToActiveRegularESection2FormWitness : Bool
astCompilesToActiveRegularESection2FormWitness = true

s1LiteralActiveRegularEASTCompilerLevel : ProofLevel
s1LiteralActiveRegularEASTCompilerLevel = machineChecked

-- The only conditional source payment represented by this AST.
s1LiteralActiveRegularEASTPaymentLevel : ProofLevel
s1LiteralActiveRegularEASTPaymentLevel =
  R246.literalActiveCMP119RegularESection2FormWitnessLevel
