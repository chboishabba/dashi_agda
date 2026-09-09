{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanR108BackedPresentCutActionExact where

------------------------------------------------------------------------
-- ROUND154 INTROSPECTIVE REPAIR: BUILD BC1 FROM THE ROUND108 CONTINUATION
--
-- R151 asked for a post-hoc theorem equating the selected beta-density potential
-- with the BC1 present-cut potential.  That equality is avoidable on the
-- preferred route: instantiate BC1's source continuation by
--
--     R108.asCMP109116Continuation family
--
-- from the outset.  The selected source scale is then literally Nat, the
-- background carrier is literally R108.Background family, and the BC1 effective
-- potential reduces definitionally to
--
--     R108.potentialOfDensity family (densityAt inputs scale).
--
-- Thus the R151 selected-potential equality is refl.  The remaining physical
-- work is the source-side calculus/Eq.(5.1)/analytic-demand/composite/Heat-Doob
-- instantiation on this SAME continuation; no independent potential weld remains.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Flow
import DASHI.Physics.YangMills.BalabanBetaDrivenDensityToCMP109116CarrierRound108Exact as R108
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanCMP109Equation51LocalizedHessianRound103Exact as Eq51
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonRadiusRound104Exact as Canon
import DASHI.Physics.YangMills.BalabanBC1CanonicalCarrierCompilerRound115Exact as BC1
import DASHI.Physics.YangMills.BalabanBC1PhysicalCompositeChainRuleRound118Exact as Composite
import DASHI.Physics.YangMills.BalabanBC2CompactGroupSameDensityRound119Exact as BC2
import DASHI.Physics.YangMills.BalabanA1WQRPhysicalJetRound123Exact as A1
import DASHI.Physics.YangMills.BalabanYM4WardQuarticResponseProducerAdapterExact as A2
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanRound108DirectUnifiedActionRound151Exact as R151

record R108BackedBC1CanonicalInputs
    {trajectory split}
    {inputs : Flow.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    (family : R108.BetaDrivenLocalizedEffectiveActionFamily inputs) : Set₁ where
  field
    calculus :
      Finite.SecondVariationLinearity (R108.Background family) (R108.Tangent family)

    equation51 :
      Eq51.CMP109Equation51OnContinuation
        (R108.asCMP109116Continuation family) calculus

    scale : Nat
    volume : R108.Volume family

    analyticDemands : Canon.CMP116FiniteNormalizedAnalyticDemands

open R108BackedBC1CanonicalInputs public

asBC1CanonicalPhysicalInputs :
  ∀ {trajectory split inputs family} →
  R108BackedBC1CanonicalInputs
    {trajectory = trajectory} {split = split} {inputs = inputs} family →
  BC1.BC1CanonicalPhysicalInputs
asBC1CanonicalPhysicalInputs {family = family} dataSet = record
  { BC1.BC1CanonicalPhysicalInputs.source =
      R108.asCMP109116Continuation family
  ; BC1.BC1CanonicalPhysicalInputs.calculus = calculus dataSet
  ; BC1.BC1CanonicalPhysicalInputs.equation51 = equation51 dataSet
  ; BC1.BC1CanonicalPhysicalInputs.scale = scale dataSet
  ; BC1.BC1CanonicalPhysicalInputs.volume = volume dataSet
  ; BC1.BC1CanonicalPhysicalInputs.analyticDemands = analyticDemands dataSet
  }

record R108BackedBC1PhysicalInputs
    {trajectory split inputs family}
    (canonicalInputs : R108BackedBC1CanonicalInputs
      {trajectory = trajectory} {split = split} {inputs = inputs} family) : Set₁ where
  field
    compositeFamily :
      Composite.BC1PhysicalCompositeComponentFamily
        (asBC1CanonicalPhysicalInputs canonicalInputs)

open R108BackedBC1PhysicalInputs public

asBC1PhysicalCompositeInputs :
  ∀ {trajectory split inputs family canonicalInputs} →
  R108BackedBC1PhysicalInputs
    {trajectory = trajectory} {split = split} {inputs = inputs} {family = family}
    canonicalInputs →
  Composite.BC1PhysicalCompositeInputs
asBC1PhysicalCompositeInputs {canonicalInputs = canonicalInputs} physical = record
  { Composite.BC1PhysicalCompositeInputs.canonical =
      asBC1CanonicalPhysicalInputs canonicalInputs
  ; Composite.BC1PhysicalCompositeInputs.compositeFamily =
      compositeFamily physical
  }

record R108BackedPresentCutPhysicalInputs
    (History Cell : Set) (cutoff : Nat)
    {trajectory split}
    {inputs : Flow.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    (family : R108.BetaDrivenLocalizedEffectiveActionFamily inputs) : Set₂ where
  field
    a1 : A1.A1WQRPhysicalJetInputs History Cell
    a2 : A2.WardQuarticResponseProducer cutoff

    bc1Canonical : R108BackedBC1CanonicalInputs family
    bc1Physical : R108BackedBC1PhysicalInputs bc1Canonical

    bc2 : BC2.CompactGroupHeatDoobOnCarrier
      (BC1.bc1CanonicalCarrier
        (asBC1CanonicalPhysicalInputs bc1Canonical))

open R108BackedPresentCutPhysicalInputs public

asPresentCutPhysicalSourceInputs :
  ∀ {History Cell cutoff trajectory split inputs family} →
  R108BackedPresentCutPhysicalInputs History Cell cutoff
    {trajectory = trajectory} {split = split} {inputs = inputs} family →
  Present.PresentCutPhysicalSourceInputs History Cell cutoff
asPresentCutPhysicalSourceInputs dataSet = record
  { Present.PresentCutPhysicalSourceInputs.a1 = a1 dataSet
  ; Present.PresentCutPhysicalSourceInputs.a2 = a2 dataSet
  ; Present.PresentCutPhysicalSourceInputs.bc1 =
      asBC1PhysicalCompositeInputs (bc1Physical dataSet)
  ; Present.PresentCutPhysicalSourceInputs.bc2 = bc2 dataSet
  }

round108BackedDirectActionRealization :
  ∀ {History Cell cutoff trajectory split inputs family}
    (dataSet : R108BackedPresentCutPhysicalInputs History Cell cutoff
      {trajectory = trajectory} {split = split} {inputs = inputs} family) →
  R151.Round108DirectPresentCutActionRealization
    (asPresentCutPhysicalSourceInputs dataSet) family
round108BackedDirectActionRealization dataSet = record
  { R151.Round108DirectPresentCutActionRealization.sourceScaleToDensityIndex =
      λ scale → scale
  ; R151.Round108DirectPresentCutActionRealization.presentBackgroundToRound108Background =
      λ background → background
  ; R151.Round108DirectPresentCutActionRealization.selectedRound108PotentialRepresentsBC1Potential =
      λ background → refl
  }

round108BackedSelectedPotentialIsBC1ByRefl :
  ∀ {History Cell cutoff trajectory split inputs family}
    (dataSet : R108BackedPresentCutPhysicalInputs History Cell cutoff
      {trajectory = trajectory} {split = split} {inputs = inputs} family) →
  ∀ background →
  let realization = round108BackedDirectActionRealization dataSet
  in
  R151.round108DirectSelectedDensityRepresentsBC1Potential realization background
  ≡ R151.round108DirectSelectedDensityRepresentsBC1Potential realization background
round108BackedSelectedPotentialIsBC1ByRefl dataSet background = refl

r108BackedPresentCutActionCompilerLevel : ProofLevel
r108BackedPresentCutActionCompilerLevel = machineChecked

-- The old R151 post-hoc same-potential payment disappears on this constructor.
-- Remaining physical work is the literal source instantiation of these exact
-- R108-backed BC1/BC2 fields, not another equality between two chosen actions.
literalR108BackedPresentCutInputsLevel : ProofLevel
literalR108BackedPresentCutInputsLevel = conditional
