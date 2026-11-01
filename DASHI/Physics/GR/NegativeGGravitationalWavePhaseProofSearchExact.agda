module DASHI.Physics.GR.NegativeGGravitationalWavePhaseProofSearchExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.GR.NegativeGGravitationalWavePhaseIdentifiabilityBidiExact as Ident
import DASHI.Physics.GR.GravitationalWaveTheoryTestBidiExact as WaveTest
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- EXTRA PROOF SEARCH FOR A SIGNED-WAVEFORM -> SIGN(G) INTERPRETATION
--
-- The generic GW test owner remains responsible for calibrated observations,
-- attributed predictions, detector response, systematic budget, etc.  This
-- module schedules only the additional coordinates introduced by trying to use
-- waveform sign itself as a negative-G discriminator.
------------------------------------------------------------------------

data WaveSignInferenceStage : Set where
  independentPhaseAnchorStage : WaveSignInferenceStage
  signConditionedSourceSolutionsStage : WaveSignInferenceStage
  detectorResponseIdentityStage : WaveSignInferenceStage
  propagationConventionIdentityStage : WaveSignInferenceStage
  signedCouplingComparisonStage : WaveSignInferenceStage
  waveSignInferenceClosed : WaveSignInferenceStage

record WaveSignInferenceState : Set where
  constructor wave-sign-inference-state
  field
    phaseAnchorOwned : Bool
    signConditionedSourceSolutionsOwned : Bool
    detectorResponseIdentityOwned : Bool
    propagationConventionIdentityOwned : Bool
    signedCouplingComparisonOwned : Bool

open WaveSignInferenceState public

firstOpenWaveSignStage : WaveSignInferenceState → WaveSignInferenceStage
firstOpenWaveSignStage (wave-sign-inference-state false s d p c) = independentPhaseAnchorStage
firstOpenWaveSignStage (wave-sign-inference-state true false d p c) = signConditionedSourceSolutionsStage
firstOpenWaveSignStage (wave-sign-inference-state true true false p c) = detectorResponseIdentityStage
firstOpenWaveSignStage (wave-sign-inference-state true true true false c) = propagationConventionIdentityStage
firstOpenWaveSignStage (wave-sign-inference-state true true true true false) = signedCouplingComparisonStage
firstOpenWaveSignStage (wave-sign-inference-state true true true true true) = waveSignInferenceClosed

currentWaveSignInferenceState : WaveSignInferenceState
currentWaveSignInferenceState = wave-sign-inference-state false false false false false

currentFirstOpenWaveSignStage : WaveSignInferenceStage
currentFirstOpenWaveSignStage = firstOpenWaveSignStage currentWaveSignInferenceState

currentFirstStageIsIndependentPhaseAnchor :
  currentFirstOpenWaveSignStage ≡ independentPhaseAnchorStage
currentFirstStageIsIndependentPhaseAnchor = refl

producerForWaveSignStage : WaveSignInferenceStage → Search.ProducerClass
producerForWaveSignStage independentPhaseAnchorStage = Search.discriminatorProducer
producerForWaveSignStage signConditionedSourceSolutionsStage = Search.propositionSourceProducer
producerForWaveSignStage detectorResponseIdentityStage = Search.identityProducer
producerForWaveSignStage propagationConventionIdentityStage = Search.identityProducer
producerForWaveSignStage signedCouplingComparisonStage = Search.discriminatorProducer
producerForWaveSignStage waveSignInferenceClosed = Search.contradictionProducer

------------------------------------------------------------------------
-- Handoff target to the existing GW theory-test owner.
------------------------------------------------------------------------

record PhaseAnchoredSignedGWaveComparisonTarget : Set₁ where
  constructor phase-anchored-signed-g-wave-comparison-target
  field
    genericWaveTestFamily : WaveTest.WaveTestFamily
    phaseDiscriminator : Ident.NegativeGWaveSignDiscriminator

    SignedCouplingComparator : Set
    signedCouplingComparator : SignedCouplingComparator

    ExistingGWTheoryTestWeld : Set
    existingGWTheoryTestWeld : ExistingGWTheoryTestWeld

open PhaseAnchoredSignedGWaveComparisonTarget public

record NegativeGWaveSignProofSearchBoundary : Set where
  constructor negative-g-wave-sign-proof-search-boundary
  field
    signedWaveformSampleMaySkipPhaseAnchor : Bool
    currentFirstNewResidualIsIndependentPhaseAnchor : Bool
    phaseAnchorAloneClosesNegativeG : Bool
    signConditionedSourceSolutionsStillRequired : Bool
    detectorResponseIdentityStillRequired : Bool
    propagationConventionIdentityStillRequired : Bool
    genericGWTestOwnerRemainsUpstream : Bool

canonicalNegativeGWaveSignProofSearchBoundary : NegativeGWaveSignProofSearchBoundary
canonicalNegativeGWaveSignProofSearchBoundary =
  negative-g-wave-sign-proof-search-boundary
    false true false true true true true
