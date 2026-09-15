{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.BalabanRound131NativeSectorRecoveryTransportExact where

------------------------------------------------------------------------
-- PARETO / ROUND131 -> SHARED NATIVE SECTOR TRANSPORT
--
-- Round131 already proves the native continuum first-variation identity on the
-- canonical CMP116 metric/stress carrier.  The common-action consumer does not
-- need another continuum or stress theorem.
--
-- Pareto recut: the generic native transport consumes only the distinguished
-- literal stress.  The genuinely live same-object seams are therefore:
--
--   1. common perturbation/scalar transport;
--   2. attachment of Round131's fixed literal construction Y to the selected
--      QFT target qftTarget(coarseGrain candidate regime);
--   3. pairing coherence for the one literal sector stress.
--
-- The unification adapter also selects the UnifiedCandidate's own qftSemantics
-- by construction.  A separate arbitrary-S -> qftSemantics equality would be an
-- unnecessary representation obligation at this consumer.
--
-- Once (2) is supplied, the shared-stress identity is derived from the existing
-- UnifiedCandidate.qftSectorStressToShared map rather than restated opaquely.
-- No aggregation is performed here; BalabanTransportedSectorFamilyProducerExact
-- owns the all-sector aggregation step.
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
    {Y : Top.LiteralYangMillsConstruction
      (Weld.qftCarriers U) (Weld.qftSemantics U)}
    {group : Top.CompactSimpleGroup (Weld.qftCarriers U)}
    {Scale Volume : Set}
    {activity : Chain.SubstitutedActivitySecondVariation}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = Weld.qftCarriers U} {S = Weld.qftSemantics U}
      {Y = Y} {group = group}
      domain representation}
    (recovery : R131.CommonMetricReadyBalabanSectorRecovery stressLane)
    (MetricPerturbation VariationScalar : Set) : Set₁ where
  field
    toNativeMetricPerturbation :
      MetricPerturbation → Domain.MetricPerturbation domain

    fromNativeVariationScalar :
      StressRep.PairingScalar representation → VariationScalar

    -- Same-object construction attachment.  Round131 is proved for one fixed Y;
    -- the shared consumer is indexed by the selected coarse-grained QFT target.
    literalConstructionIsSelectedQFTTarget :
      ∀ candidate regime →
      Weld.qftRegime U regime →
      Y ≡ Weld.qftTarget U (Weld.coarseGrain U candidate regime)

    sharedStressMetricPairing :
      Weld.SharedStressEnergy U → MetricPerturbation → VariationScalar

    -- Only the distinguished literal sector stress is consumed downstream.
    literalStressPairingCommutes :
      ∀ perturbation →
      sharedStressMetricPairing
        (Weld.qftSectorStressToShared U group (Top.stressTensor Y group))
        perturbation
      ≡ fromNativeVariationScalar
          (StressRep.stressMetricPairing representation
            (StressRep.stressTensor representation)
            (toNativeMetricPerturbation perturbation))

open Round131SharedTransportData public

round131RecoveryToNativeSectorTransport :
  ∀ {U trajectory split inputs Y group Scale Volume activity domain representation stressLane}
    {MetricPerturbation VariationScalar : Set}
    (recovery : R131.CommonMetricReadyBalabanSectorRecovery
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = Weld.qftCarriers U} {S = Weld.qftSemantics U}
      {Y = Y} {group = group}
      {Scale = Scale} {Volume = Volume} {activity = activity}
      {domain = domain} {representation = representation}
      stressLane) →
  Round131SharedTransportData recovery MetricPerturbation VariationScalar →
  Transport.NativeBalabanSectorRecoveryTransport
    {U = U} group MetricPerturbation VariationScalar
round131RecoveryToNativeSectorTransport
    {U = U} {Y = Y} {group = group}
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
  ; Transport.NativeBalabanSectorRecoveryTransport.nativeLiteralStressShared =
      Weld.qftSectorStressToShared U group (Top.stressTensor Y group)
  ; Transport.NativeBalabanSectorRecoveryTransport.nativeLiteralStressIsActualSharedSectorStress =
      λ candidate regime qftAtRegime →
        cong
          (λ construction →
            Weld.qftSectorStressToShared U group
              (Top.stressTensor construction group))
          (literalConstructionIsSelectedQFTTarget
            dataSet candidate regime qftAtRegime)
  ; Transport.NativeBalabanSectorRecoveryTransport.sharedStressMetricPairing =
      sharedStressMetricPairing dataSet
  ; Transport.NativeBalabanSectorRecoveryTransport.nativeLiteralPairingCommutes =
      literalStressPairingCommutes dataSet
  }

round131NativeSectorTransportCompilerLevel : ProofLevel
round131NativeSectorTransportCompilerLevel = machineChecked

-- Alias required by the focused Pareto validation root.
round131LiteralSectorTransportCompilerLevel : ProofLevel
round131LiteralSectorTransportCompilerLevel =
  round131NativeSectorTransportCompilerLevel

record Round131NativeSectorTransportBoundary : Set where
  constructor round131-native-sector-transport-boundary
  field
    secondContinuumTheoremRequired : Bool
    secondContinuumTheoremRequiredIsFalse :
      secondContinuumTheoremRequired ≡ false

    secondStressConvergenceTheoremRequired : Bool
    secondStressConvergenceTheoremRequiredIsFalse :
      secondStressConvergenceTheoremRequired ≡ false

    arbitraryQFTSemanticsTransportRequired : Bool
    arbitraryQFTSemanticsTransportRequiredIsFalse :
      arbitraryQFTSemanticsTransportRequired ≡ false

    allNativeStressTransportRequired : Bool
    allNativeStressTransportRequiredIsFalse :
      allNativeStressTransportRequired ≡ false

    literalConstructionAttachmentStillRequired : Bool
    literalConstructionAttachmentStillRequiredIsTrue :
      literalConstructionAttachmentStillRequired ≡ true

    literalPairingCoherenceStillRequired : Bool
    literalPairingCoherenceStillRequiredIsTrue :
      literalPairingCoherenceStillRequired ≡ true

    allSectorAggregationPaidHere : Bool
    allSectorAggregationPaidHereIsFalse :
      allSectorAggregationPaidHere ≡ false

canonicalRound131NativeSectorTransportBoundary :
  Round131NativeSectorTransportBoundary
canonicalRound131NativeSectorTransportBoundary =
  round131-native-sector-transport-boundary
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
    false refl
