{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.BalabanNativeSectorRecoveryTransportExact where

------------------------------------------------------------------------
-- BIDI REPRESENTATION TRANSPORT FOR ONE NATIVE YM SECTOR
--
-- The source-native producer on YM PR #638 uses its canonical CMP116 metric
-- perturbation, native pairing scalar, and native literal stress carrier.
-- The TOE consumer uses one QFT-side perturbation/scalar convention and the
-- `SharedStressEnergy` carrier.  These are not identified by name.
--
-- This record isolates exactly the representation theorem needed to transport a
-- native endpoint identity into the shared sector identity consumed by
-- `BalabanAllSectorContinuumProducer`.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as QFT

record NativeBalabanSectorRecoveryTransport
    {U : Weld.UnifiedCandidate}
    (group : QFT.CompactSimpleGroup (Weld.qftCarriers U))
    (MetricPerturbation VariationScalar : Set) : Set₁ where
  field
    NativeMetricPerturbation NativeVariationScalar NativeStress : Set

    nativeLiteralStress : NativeStress
    nativeContinuumFirstVariation :
      NativeMetricPerturbation → NativeVariationScalar
    nativeStressMetricPairing :
      NativeStress → NativeMetricPerturbation → NativeVariationScalar
    NativeAdmissibleMetricPerturbation : NativeMetricPerturbation → Set

    nativeContinuumVariationIsLiteralStressPairing :
      ∀ perturbation →
      NativeAdmissibleMetricPerturbation perturbation →
      nativeContinuumFirstVariation perturbation
      ≡ nativeStressMetricPairing nativeLiteralStress perturbation

    toNativeMetricPerturbation :
      MetricPerturbation → NativeMetricPerturbation
    fromNativeVariationScalar :
      NativeVariationScalar → VariationScalar

    nativeStressToShared : NativeStress → Weld.SharedStressEnergy U

    nativeLiteralStressIsActualSharedSectorStress :
      ∀ candidate regime →
      Weld.qftRegime U regime →
      nativeStressToShared nativeLiteralStress
      ≡ Weld.actualQFTSectorStressShared U
          (Weld.coarseGrain U candidate regime) group

    sharedStressMetricPairing :
      Weld.SharedStressEnergy U → MetricPerturbation → VariationScalar

    nativePairingCommutes :
      ∀ stress perturbation →
      sharedStressMetricPairing (nativeStressToShared stress) perturbation
      ≡ fromNativeVariationScalar
          (nativeStressMetricPairing stress
            (toNativeMetricPerturbation perturbation))

open NativeBalabanSectorRecoveryTransport public

transportedSectorContinuumFirstVariation :
  ∀ {U : Weld.UnifiedCandidate}
    {group : QFT.CompactSimpleGroup (Weld.qftCarriers U)}
    {MetricPerturbation VariationScalar}
    (transport : NativeBalabanSectorRecoveryTransport
      group MetricPerturbation VariationScalar) →
  MetricPerturbation → VariationScalar
transportedSectorContinuumFirstVariation transport perturbation =
  fromNativeVariationScalar transport
    (nativeContinuumFirstVariation transport
      (toNativeMetricPerturbation transport perturbation))

TransportedAdmissibleMetricPerturbation :
  ∀ {U : Weld.UnifiedCandidate}
    {group : QFT.CompactSimpleGroup (Weld.qftCarriers U)}
    {MetricPerturbation VariationScalar} →
  NativeBalabanSectorRecoveryTransport
    group MetricPerturbation VariationScalar →
  MetricPerturbation → Set
TransportedAdmissibleMetricPerturbation transport perturbation =
  NativeAdmissibleMetricPerturbation transport
    (toNativeMetricPerturbation transport perturbation)

transportedSectorVariationIsActualSharedStressPairing :
  ∀ {U : Weld.UnifiedCandidate}
    {group : QFT.CompactSimpleGroup (Weld.qftCarriers U)}
    {MetricPerturbation VariationScalar}
    (transport : NativeBalabanSectorRecoveryTransport
      group MetricPerturbation VariationScalar)
    candidate regime perturbation →
  Weld.qftRegime U regime →
  TransportedAdmissibleMetricPerturbation transport perturbation →
  transportedSectorContinuumFirstVariation transport perturbation
  ≡ sharedStressMetricPairing transport
      (Weld.actualQFTSectorStressShared U
        (Weld.coarseGrain U candidate regime) group)
      perturbation
transportedSectorVariationIsActualSharedStressPairing
    transport candidate regime perturbation qftAtRegime admissible =
  let
    nativeIdentity = nativeContinuumVariationIsLiteralStressPairing transport
      (toNativeMetricPerturbation transport perturbation) admissible
    scalarIdentity = cong (fromNativeVariationScalar transport) nativeIdentity
    pairingIdentity = sym (nativePairingCommutes transport
      (nativeLiteralStress transport) perturbation)
    stressIdentity = nativeLiteralStressIsActualSharedSectorStress
      transport candidate regime qftAtRegime
    sharedStressIdentity = cong
      (λ stress → sharedStressMetricPairing transport stress perturbation)
      stressIdentity
  in
  trans scalarIdentity (trans pairingIdentity sharedStressIdentity)

nativeBalabanSectorRecoveryTransportCompilerLevel : ProofLevel
nativeBalabanSectorRecoveryTransportCompilerLevel = machineChecked

record NativeSectorTransportBoundary : Set where
  constructor nativeSectorTransportBoundary
  field
    nativeYMStressIsSharedStressByCarrierName : Bool
    nativeYMStressIsSharedStressByCarrierNameIsFalse :
      nativeYMStressIsSharedStressByCarrierName ≡ false

    nativeYMMetricPerturbationIsCommonPerturbationByName : Bool
    nativeYMMetricPerturbationIsCommonPerturbationByNameIsFalse :
      nativeYMMetricPerturbationIsCommonPerturbationByName ≡ false

    explicitStressPerturbationScalarTransportIsSufficient : Bool
    explicitStressPerturbationScalarTransportIsSufficientIsTrue :
      explicitStressPerturbationScalarTransportIsSufficient ≡ true

canonicalNativeSectorTransportBoundary : NativeSectorTransportBoundary
canonicalNativeSectorTransportBoundary =
  nativeSectorTransportBoundary false refl false refl true refl
