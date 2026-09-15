{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.BalabanRound131NativeSectorRecoveryTransportExact where

------------------------------------------------------------------------
-- PARETO / ROUND131 -> SHARED NATIVE SECTOR TRANSPORT
--
-- Round131 already proves the native continuum first-variation identity on the
-- canonical CMP116 metric/stress carrier.  The common-action consumer does not
-- need another continuum or stress theorem.  It needs only explicit transport
-- of perturbations, scalars, and the native stress object into the shared QFT
-- carriers.
--
-- This module therefore packages exactly that representation weld into the
-- existing `NativeBalabanSectorRecoveryTransport` interface.  No aggregation is
-- performed here; `BalabanTransportedSectorFamilyProducerExact` owns the
-- all-sector aggregation step.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.BalabanNativeSectorRecoveryTransportExact as Transport

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as R123
import DASHI.Physics.YangMills.BalabanCommonMetricSectorRecoveryRound131Exact as R131
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

record Round131SharedTransportData
    {U : Weld.UnifiedCandidate}
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {S : Top.LiteralYangMillsSemantics (Weld.qftCarriers U)}
    {Y : Top.LiteralYangMillsConstruction (Weld.qftCarriers U) S}
    {group : Top.CompactSimpleGroup (Weld.qftCarriers U)}
    {Scale Volume : Set}
    {activity : Chain.SubstitutedActivitySecondVariation}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = Weld.qftCarriers U} {S = S} {Y = Y} {group = group}
      domain representation}
    (recovery : R131.CommonMetricReadyBalabanSectorRecovery stressLane)
    (MetricPerturbation VariationScalar : Set) : Set₁ where
  field
    toNativeMetricPerturbation :
      MetricPerturbation → Domain.MetricPerturbation domain

    fromNativeVariationScalar :
      StressRep.PairingScalar representation → VariationScalar

    nativeStressToShared :
      StressRep.StressTensor representation → Weld.SharedStressEnergy U

    nativeLiteralStressIsActualSharedSectorStress :
      ∀ candidate regime →
      Weld.qftRegime U regime →
      nativeStressToShared (StressRep.stressTensor representation)
      ≡ Weld.actualQFTSectorStressShared U
          (Weld.coarseGrain U candidate regime) group

    sharedStressMetricPairing :
      Weld.SharedStressEnergy U → MetricPerturbation → VariationScalar

    nativePairingCommutes :
      ∀ stress perturbation →
      sharedStressMetricPairing (nativeStressToShared stress) perturbation
      ≡ fromNativeVariationScalar
          (StressRep.stressMetricPairing representation stress
            (toNativeMetricPerturbation perturbation))

open Round131SharedTransportData public

round131RecoveryToNativeSectorTransport :
  ∀ {U trajectory split inputs S Y group Scale Volume activity domain representation stressLane}
    {MetricPerturbation VariationScalar : Set}
    (recovery : R131.CommonMetricReadyBalabanSectorRecovery
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = Weld.qftCarriers U} {S = S} {Y = Y} {group = group}
      {Scale = Scale} {Volume = Volume} {activity = activity}
      {domain = domain} {representation = representation}
      stressLane) →
  Round131SharedTransportData recovery MetricPerturbation VariationScalar →
  Transport.NativeBalabanSectorRecoveryTransport
    {U = U} group MetricPerturbation VariationScalar
round131RecoveryToNativeSectorTransport
    {domain = domain} {representation = representation}
    recovery dataSet = record
  { Transport.NativeBalabanSectorRecoveryTransport.NativeMetricPerturbation =
      Domain.MetricPerturbation domain
  ; Transport.NativeBalabanSectorRecoveryTransport.NativeVariationScalar =
      StressRep.PairingScalar representation
  ; Transport.NativeBalabanSectorRecoveryTransport.NativeStress =
      StressRep.StressTensor representation
  ; Transport.NativeBalabanSectorRecoveryTransport.nativeLiteralStress =
      StressRep.stressTensor representation
  ; Transport.NativeBalabanSectorRecoveryTransport.nativeContinuumFirstVariation =
      R131.continuumSectorFirstVariation recovery
  ; Transport.NativeBalabanSectorRecoveryTransport.nativeStressMetricPairing =
      StressRep.stressMetricPairing representation
  ; Transport.NativeBalabanSectorRecoveryTransport.NativeAdmissibleMetricPerturbation =
      Domain.AdmissibleMetricPerturbation domain
  ; Transport.NativeBalabanSectorRecoveryTransport.nativeContinuumVariationIsLiteralStressPairing =
      R131.continuumSectorFirstVariationIsLiteralStressPairing recovery
  ; Transport.NativeBalabanSectorRecoveryTransport.toNativeMetricPerturbation =
      toNativeMetricPerturbation dataSet
  ; Transport.NativeBalabanSectorRecoveryTransport.fromNativeVariationScalar =
      fromNativeVariationScalar dataSet
  ; Transport.NativeBalabanSectorRecoveryTransport.nativeStressToShared =
      nativeStressToShared dataSet
  ; Transport.NativeBalabanSectorRecoveryTransport.nativeLiteralStressIsActualSharedSectorStress =
      nativeLiteralStressIsActualSharedSectorStress dataSet
  ; Transport.NativeBalabanSectorRecoveryTransport.sharedStressMetricPairing =
      sharedStressMetricPairing dataSet
  ; Transport.NativeBalabanSectorRecoveryTransport.nativePairingCommutes =
      nativePairingCommutes dataSet
  }

round131NativeSectorTransportCompilerLevel : ProofLevel
round131NativeSectorTransportCompilerLevel = machineChecked

record Round131NativeSectorTransportBoundary : Set where
  constructor round131-native-sector-transport-boundary
  field
    secondContinuumTheoremRequired : Bool
    secondContinuumTheoremRequiredIsFalse :
      secondContinuumTheoremRequired ≡ false

    secondStressConvergenceTheoremRequired : Bool
    secondStressConvergenceTheoremRequiredIsFalse :
      secondStressConvergenceTheoremRequired ≡ false

    explicitCarrierTransportStillRequired : Bool
    explicitCarrierTransportStillRequiredIsTrue :
      explicitCarrierTransportStillRequired ≡ true

    allSectorAggregationPaidHere : Bool
    allSectorAggregationPaidHereIsFalse :
      allSectorAggregationPaidHere ≡ false

canonicalRound131NativeSectorTransportBoundary :
  Round131NativeSectorTransportBoundary
canonicalRound131NativeSectorTransportBoundary =
  round131-native-sector-transport-boundary
    false refl
    false refl
    true refl
    false refl
