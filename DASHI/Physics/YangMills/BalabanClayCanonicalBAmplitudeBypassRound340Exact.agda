{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCanonicalBAmplitudeBypassRound340Exact where

------------------------------------------------------------------------
-- ROUND340 / KEEP THE CORRELATION PREFACTOR
--
-- Archaeology recovered the original B consumer: quantitative exponential
-- clustering on the same continuum family, followed by the standard OS/spectral
-- transfer.  That consumer never requires the clustering prefactor to be one.
--
-- R320/R304 choose the stronger convenient normalization
--
--   |D^2 log Z| <= rootedShell <= (1/4) 2^-distance.
--
-- This is a useful producer when available, but it is not the least-privilege
-- theorem required by the mass-gap consumer.  The older terminal/OS interface
-- already carries an observable-dependent correlation constant:
--
--   |Corr(A,B,t)| <= C(A,B) * physicalDecay(m*,t).
--
-- Therefore a source-native CMP109/CMP116 producer should retain its finite
-- amplitude constant rather than spend proof effort normalizing it to one.
-- This file makes that bypass explicit without replacing R320.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanTerminalScalePhysicalClustering as Terminal
import DASHI.Physics.YangMills.BalabanOSReconstructionMassGapProduction as OS
import DASHI.Physics.YangMills.BalabanT5DirectSelectedMarkedDecayRound320Exact as R320
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared

------------------------------------------------------------------------
-- Existing amplitude-aware compiler, re-exported at the current B cut.
------------------------------------------------------------------------

amplitudeAwareTerminalClusteringToOSDecay :
  ∀ {Observable Time Scalar Bound Hamiltonian} →
  Terminal.TerminalScalePhysicalClusteringData
    Observable Time Scalar Bound Hamiltonian →
  OS.UniformConnectedCorrelationDecayData
    Observable Time Scalar Bound Hamiltonian
amplitudeAwareTerminalClusteringToOSDecay =
  Terminal.terminalScaleToOSCorrelationDecayData

record Round340Boundary : Set where
  constructor round340-boundary
  field
    unitRootedShellNormalizationMandatoryForMassGap : Bool
    unitRootedShellNormalizationMandatoryForMassGapIsFalse :
      unitRootedShellNormalizationMandatoryForMassGap ≡ false

    observableDependentCorrelationPrefactorSupportedByExistingOSConsumer : Bool
    observableDependentCorrelationPrefactorSupportedByExistingOSConsumerIsTrue :
      observableDependentCorrelationPrefactorSupportedByExistingOSConsumer ≡ true

    r320RemainsValidStrongerProducer : Bool
    r320RemainsValidStrongerProducerIsTrue :
      r320RemainsValidStrongerProducer ≡ true

    sourceMarkedShellAlreadyCarriesExplicitAmplitudeConstant : Bool
    sourceMarkedShellAlreadyCarriesExplicitAmplitudeConstantIsTrue :
      sourceMarkedShellAlreadyCarriesExplicitAmplitudeConstant ≡ true

    physicalSourceMarkedShellInstantiationStillRequired : Bool
    physicalSourceMarkedShellInstantiationStillRequiredIsTrue :
      physicalSourceMarkedShellInstantiationStillRequired ≡ true

    physicalSelectedResponseSameObjectStillRequired : Bool
    physicalSelectedResponseSameObjectStillRequiredIsTrue :
      physicalSelectedResponseSameObjectStillRequired ≡ true

    freshDecayInequalityCreatedByThisBypass : Bool
    freshDecayInequalityCreatedByThisBypassIsFalse :
      freshDecayInequalityCreatedByThisBypass ≡ false

canonicalRound340Boundary : Round340Boundary
canonicalRound340Boundary =
  round340-boundary
    false refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl

round340AmplitudeAwareCompilerLevel : ProofLevel
round340AmplitudeAwareCompilerLevel = machineChecked

round340UnitNormalizedR320ProducerLevel : ProofLevel
round340UnitNormalizedR320ProducerLevel = R320.round320DirectSelectedMarkedDecayLevel

round340SourceMarkedShellInstantiationLevel : ProofLevel
round340SourceMarkedShellInstantiationLevel = Shared.physicalSharedMarkedAnalyticShellLevel

round340SelectedResponseIdentificationLevel : ProofLevel
round340SelectedResponseIdentificationLevel = Shared.physicalSharedMarkedResponseIdentificationLevel

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
