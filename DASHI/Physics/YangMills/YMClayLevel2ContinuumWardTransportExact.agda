{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLevel2ContinuumWardTransportExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _-_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as StressLane
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionFirstVariationRound133Exact as R133
import DASHI.Physics.YangMills.BalabanPresentCutCanonicalMetricDomainRound134Exact as R134
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionStressScaleRound135Exact as R135
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionRecoveryRound136Exact as R136
import DASHI.Physics.YangMills.YangMillsLatticeStressWardSliceConservationExact as Ward
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

------------------------------------------------------------------------
-- LEVEL-2 D3: FINITE WARD CURRENT -> RECOVERED CONTINUUM STRESS TRANSPORT
--
-- The finite Ward theorem and the generated-action stress theorem live on
-- different scalar carriers:
--
--   finite periodic Ward slice charge : ℚ
--   continuum metric stress pairing   : StressRep.PairingScalar representation
--
-- Hence they must NOT be identified by type/name alone.
--
-- Existing machinery already pays:
--
--   * Ward: discrete balance -> exact finite slice-charge conservation;
--   * R132-R135: the selected stress insertion is a first-order view of the
--     SAME beta-driven generated action at the SAME scale;
--   * R136: the recovered continuum first variation equals the literal stress
--     metric pairing.
--
-- The remaining D3 theorem is precisely the representation/convergence weld
-- showing that the finite Ward charge/current from that generated-action family
-- is the finite representative whose continuum limit is the recovered stress
-- pairing.
------------------------------------------------------------------------

record ContinuumWardTransport
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {History Cell : Set} {cutoff : Nat}
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
    : Set₁ where
  field
    finiteWardChargeAt : Nat → Ward.LatticeStressWardCharge

    wardChargeToPairingScalar :
      ℚ → StressRep.PairingScalar representation

    -- The finite Ward charge is attached to the SAME generated-action stress
    -- family rather than to an unrelated conserved lattice current.
    FiniteWardChargeIsGeneratedActionStressCharge : Set
    finiteWardChargeIsGeneratedActionStressCharge :
      FiniteWardChargeIsGeneratedActionStressCharge

    -- Convergence/continuum meaning is kept explicit because the finite Ward
    -- value is rational while the stress pairing scalar is representation-
    -- dependent.
    WardChargeConvergesToStressPairing :
      (Domain.MetricPerturbation
        (R134.presentCutCanonicalMetricDomain metricInputs)) →
      Set

    finiteWardChargeConvergesToRecoveredStress :
      ∀ perturbation →
      Domain.AdmissibleMetricPerturbation
        (R134.presentCutCanonicalMetricDomain metricInputs) perturbation →
      WardChargeConvergesToStressPairing perturbation

    -- The target of the transport is exactly the already-recovered continuum
    -- first variation, which R136 proves equal to the literal stress pairing.
    transportedWardTargetIsRecoveredFirstVariation :
      ∀ perturbation →
      WardChargeConvergesToStressPairing perturbation →
      Set

    transportedWardTargetIsLiteralStressPairing :
      ∀ perturbation
        (transport : WardChargeConvergesToStressPairing perturbation) →
      transportedWardTargetIsRecoveredFirstVariation perturbation transport

open ContinuumWardTransport public

finiteSliceChargeConservationAlreadyCompilerOwned :
  ∀ {trajectory split inputs History Cell cutoff present actionWeld firstWeld
      metricInputs representation C S Y group lane scaleWeld recovery}
    (transport : ContinuumWardTransport
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {History = History} {Cell = Cell} {cutoff = cutoff}
      {present = present} {actionWeld = actionWeld} {firstWeld = firstWeld}
      {metricInputs = metricInputs} {representation = representation}
      {C = C} {S = S} {Y = Y} {group = group}
      {lane = lane} {scaleWeld = scaleWeld} recovery) →
  ∀ depth →
  Ward.chargeAfter (finiteWardChargeAt transport depth)
    - Ward.chargeBefore (finiteWardChargeAt transport depth) ≡ 0ℚ
finiteSliceChargeConservationAlreadyCompilerOwned transport depth =
  Ward.sliceChargeDifferenceZero (finiteWardChargeAt transport depth)

------------------------------------------------------------------------
-- Frontier classification.
------------------------------------------------------------------------

finiteWardAlgebraNewPhysicalTheoremInD3 : Bool
finiteWardAlgebraNewPhysicalTheoremInD3 = false

finiteWardAlgebraNewPhysicalTheoremInD3IsFalse :
  finiteWardAlgebraNewPhysicalTheoremInD3 ≡ false
finiteWardAlgebraNewPhysicalTheoremInD3IsFalse = refl

generatedActionStressProvenanceNewPhysicalTheoremInD3 : Bool
generatedActionStressProvenanceNewPhysicalTheoremInD3 = false

generatedActionStressProvenanceNewPhysicalTheoremInD3IsFalse :
  generatedActionStressProvenanceNewPhysicalTheoremInD3 ≡ false
generatedActionStressProvenanceNewPhysicalTheoremInD3IsFalse = refl

finiteToContinuumSameCurrentTransportStillPhysical : Bool
finiteToContinuumSameCurrentTransportStillPhysical = true

finiteToContinuumSameCurrentTransportStillPhysicalIsTrue :
  finiteToContinuumSameCurrentTransportStillPhysical ≡ true
finiteToContinuumSameCurrentTransportStillPhysicalIsTrue = refl

finiteWardCompilerLevel : ProofLevel
finiteWardCompilerLevel = Ward.periodicStressWardSliceConservationLevel

generatedActionStressRecoveryCompilerLevel : ProofLevel
generatedActionStressRecoveryCompilerLevel =
  R136.unifiedGeneratedActionRecoveryCompilerLevel

physicalContinuumWardTransportLevel : ProofLevel
physicalContinuumWardTransportLevel = conditional

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
