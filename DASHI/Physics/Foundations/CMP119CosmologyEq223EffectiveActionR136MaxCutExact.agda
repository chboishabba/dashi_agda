{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyEq223EffectiveActionR136MaxCutExact where

------------------------------------------------------------------------
-- PREFERRED EQ.(2.23) -> R136 GRAVITATIONAL SIGN ROOT.
--
-- R144 already fixes the one-point stress orientation:
--
--     D_Gamma = - D Z / Z = <D S>.
--
-- Therefore the R136 producer does not need a free logZ/Gamma orientation
-- choice.  Its one same-object leaf is only
--
--     Q_R136 = finite matter-effective-action Weyl response.
--
-- Together with the literal Eq.(2.23) dominance
--
--     N_E + N_R + N_B < -N_V,
--
-- the existing finite sign compiler gives Q_R136 < 0.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _<_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Foundations.CMP119CosmologyEq223NegativeSectorDominanceExact as Eq223Sign
import DASHI.Physics.Foundations.CMP119CosmologyEq223SourceMetricVariationExact as Eq223
import DASHI.Physics.Foundations.CMP119CosmologyFiniteWeylConventionFirewallExact as Convention
import DASHI.Physics.Foundations.CMP119CosmologyR136WeylSignMaxCutExact as Sign
import DASHI.Physics.Foundations.CMP119CosmologyPhysicalFinitePartitionAuthorityExact as Partition
import DASHI.Physics.Foundations.CMP119CosmologyPartitionStressFirstVariationExact as Source
import DASHI.Physics.Foundations.CMP119CosmologyContinuumWeylStressPairingExact as Continuum

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as StressLane
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionFirstVariationRound133Exact as R133
import DASHI.Physics.YangMills.BalabanPresentCutCanonicalMetricDomainRound134Exact as R134
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionStressScaleRound135Exact as R135
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionRecoveryRound136Exact as R136
import DASHI.Physics.YangMills.BalabanCanonicalMetricSelectedStressRound119Exact as R119
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact as Raw

module _
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {History Cell : Set}
    {cutoff : Nat}
    {present : Present.PresentCutPhysicalSourceInputs History Cell cutoff}
    {actionWeld : R132.UnifiedGeneratedActionDensity
      {trajectory = trajectory} {split = split} {inputs = inputs} present}
    {firstWeld : R133.UnifiedGeneratedActionFirstVariation actionWeld}
    {metricInputs : R134.PresentCutMetricSpecificInputs firstWeld}
    {representation : StressRep.CanonicalMetricStressRepresentation
      (R134.presentCutCanonicalMetricDomain metricInputs)}
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    {lane : StressLane.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      (R134.presentCutCanonicalMetricDomain metricInputs) representation}
    {scaleWeld : R135.UnifiedGeneratedActionStressScale lane}
    (recovery : R136.UnifiedGeneratedActionSectorRecovery scaleWeld)
    {coordinate : R114.LiteralStressCoordinate Y group}
    (selected :
      R119.CanonicalMetricSelectedStressWeld
        (R134.presentCutCanonicalMetricDomain metricInputs)
        representation coordinate)
    (directions :
      Continuum.FourAdmittedMetricDirections
        (R134.presentCutCanonicalMetricDomain metricInputs))
    {Density Background Fluctuation
     Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum
     Configuration : Set}
    {source :
      Raw.CMP119SourceNativeRawState
        Density Background Fluctuation
        Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum}
    {sourceScale : Nat}
    (sourceVariation :
      Eq223.Eq223SourceMetricVariationRealization
        source Configuration sourceScale)
  where

  d : Source.CompleteFiniteMetricVariation Configuration
  d = Eq223.sourceCompleteFiniteMetricVariation sourceVariation

  r136Response : ℚ
  r136Response = Continuum.continuumFourDiagonalResponse recovery selected directions

  record R136EffectiveActionResponseWeld
      (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
      (partition : Partition.PhysicalFinitePartitionAuthority measure)
      : Set₁ where
    field
      sameObjectEffectiveActionResponse :
        r136Response
        ≡ Convention.matterEffectiveActionWeylResponse measure partition d

  open R136EffectiveActionResponseWeld public

  literalDominanceForcesNegativeR136 :
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (partition : Partition.PhysicalFinitePartitionAuthority measure)
    (laws : Sign.RationalWeylSignIntegrationLaws measure)
    (referenceFixed :
      ∀ h x → Source.referenceMeasureLogVariation d h x ≡ 0ℚ)
    (weld : R136EffectiveActionResponseWeld measure partition) →
    Eq223Sign.LiteralNegativeSectorDominance sourceVariation measure →
    r136Response < 0ℚ
  literalDominanceForcesNegativeR136
      measure partition laws referenceFixed weld dominance =
    subst
      (λ value → value < 0ℚ)
      (sym (sameObjectEffectiveActionResponse weld))
      (Eq223Sign.literalDominanceForcesNegativeEffectiveActionWeyl
        sourceVariation measure partition laws referenceFixed dominance)

  gravitationalOrientationNoLongerFreeBranch : Bool
  gravitationalOrientationNoLongerFreeBranch = true

  remainingPreferredSignLeavesAreSameObjectResponseAndOneDominanceInequality : Bool
  remainingPreferredSignLeavesAreSameObjectResponseAndOneDominanceInequality = true
