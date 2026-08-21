module DASHI.Cognition.PNF.PNFWaveAccessTraumaLearningRegression where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Biology.DynamicEffectiveTopology as Topology
import DASHI.Biology.ConsciousAccessNetworkSourceAtlas as Sources
import DASHI.Biology.WaveControlledCoalitionBridgeExact as Coalition
import DASHI.Biology.TraumaWaveAccessAttractorBridgeExact as Trauma
import DASHI.Biology.Levin.MillerTravelingWaveAccessProducerExact as Miller
import DASHI.Biology.Levin.CrossFrequencyEffectiveTopologyExact as CrossFrequency
import DASHI.Biology.Levin.WaveInterferenceRecruitmentExact as Interference
import DASHI.Biology.Levin.MixedSelectivityWaveAccessExact as Mixed
import DASHI.Cognition.PNF.FastAccessControlFieldExact as Access
import DASHI.Cognition.PNF.PNFFastAccessMemoryLearningBridgeExact as PNFMemory
import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Cognition.PNF.WaveAccessBraidOrderExact as Braid
import DASHI.Cognition.PNF.ContextWaveFibreSelectionExact as ContextWave
import DASHI.Cognition.PNF.MultiTimescaleAccessLearningExact as Timescale
import DASHI.Cognition.PNF.AccessibleCandidateReasoningPipelineExact as Pipeline
import DASHI.Cognition.PNF.AccessActuationOrthogonalityExact as Orthogonal
import DASHI.Reasoning.AccessBiasFallacySeparationExact as Bias
import DASHI.Reasoning.FallacyObstructionCatalogue as Fallacy
import DASHI.Interop.SensibLawResidualLattice as Residual

------------------------------------------------------------------------
-- Focused regression root.  Every field is an existing theorem/witness from
-- the tranche; no new semantics are introduced here.
------------------------------------------------------------------------

record PNFWaveAccessTraumaLearningRegression : Set₁ where
  field
    genericRetentionWithoutAccess :
      Access.RetentionWithoutAccessWitness Access.canonicalFastAccessControlField

    movingWaveActuallyMovesSupport :
      Miller.recruitedAt Miller.firstTick Miller.leftSite
      ≡ Miller.recruitedAt Miller.secondTick Miller.leftSite → ⊥

    crossFrequencySameGammaChangesReadout :
      CrossFrequency.gammaReadable CrossFrequency.betaHigh CrossFrequency.gammaBurst
      ≡
      CrossFrequency.gammaReadable CrossFrequency.betaLow CrossFrequency.gammaBurst
      → ⊥

    betaLowOpensFixedAnatomicalEdge :
      Topology.EffectiveEdge
        (CrossFrequency.betaState CrossFrequency.betaLow)
        Topology.associationNode Topology.planningNode

    betaHighClosesSameAnatomicalEdge :
      Topology.EffectiveEdge
        (CrossFrequency.betaState CrossFrequency.betaHigh)
        Topology.associationNode Topology.planningNode → ⊥

    phaseInterferenceChangesRecruitment :
      Interference.nonzeroRecruit
        (Interference.combinedAmplitude Interference.one Interference.inPhase)
      ≡
      Interference.nonzeroRecruit
        (Interference.combinedAmplitude Interference.one Interference.antiPhase)
      → ⊥

    accessFailureDoesNotForceNoTypedMeet :
      ((s : PNFMemory.AccessFormalState) →
        PNFMemory.accessSurface s ≡ false →
        PNFMemory.formalResidual s ≡ Residual.noTypedMeet) → ⊥

    phaseRealignmentKeepsRememberedPNF :
      (m : Memory.MemoryFibre) →
      (phase : Nat) →
      Memory.rememberedEvent (Memory.realignPhase m phase)
      ≡ Memory.rememberedEvent m

    extinctionKeepsRememberedPNF :
      (m : Memory.MemoryFibre) →
      Memory.rememberedEvent (Memory.extinguishActionDominance m)
      ≡ Memory.rememberedEvent m

    fastAccessOrderNoncommutes :
      Braid.primeThenReadout ≡ Braid.readoutThenPrime → ⊥

    learnedStateChangesWaveSupportedSafety :
      Trauma.waveSupportedSafetyAccess Trauma.threatBiasedControl Trauma.ambiguousCue
      ≡
      Trauma.waveSupportedSafetyAccess Trauma.flexibleControl Trauma.ambiguousCue
      → ⊥

    contextWaveChainChangesAccessibleFibre :
      ContextWave.fieldAccess ContextWave.firstControlContext Miller.leftSite
      ≡
      ContextWave.fieldAccess ContextWave.secondControlContext Miller.leftSite
      → ⊥

    sameBiasDoesNotDetermineFallacy :
      (decode : Bias.AccessBias → Fallacy.FallacyObstruction) →
      decode Bias.confirmationAccessBias ≡ Fallacy.missingPremiseSupport →
      decode Bias.confirmationAccessBias ≡ Fallacy.semanticEquivocation →
      ⊥

    sameFallacyDoesNotDetermineAccessCause :
      (decode : Fallacy.FallacyObstruction → Bias.AccessBias) →
      decode Fallacy.missingPremiseSupport ≡ Bias.threatAccessBias →
      decode Fallacy.missingPremiseSupport ≡ Bias.familiarityAccessBias →
      ⊥

    accessExpansionChangesLiveCandidateNotStorage :
      Pipeline.accessible Pipeline.narrowedAccess Pipeline.counterCandidate
      ≡ Pipeline.accessible Pipeline.broadenedAccess Pipeline.counterCandidate
      → ⊥

    accessibleCandidateStillNeedsAudit :
      Pipeline.actionable Pipeline.broadenedAccess Pipeline.counterCandidate
        (Pipeline.obstructedAudit Fallacy.missingPremiseSupport)
      ≡ false

    fastMediumSlowRemainDistinct :
      Timescale.fastStep Timescale.baseline
      ≡ Timescale.mediumStep Timescale.baseline → ⊥

    accessAndActuationExpansionRemainDistinct :
      Orthogonal.accessExpanded ≡ Orthogonal.actuationExpanded → ⊥

    sameStimulusContextChangesMixedParticipation :
      Mixed.Mixed.respond Mixed.waveMixedSelectivitySystem
        Miller.leftSite Miller.firstTick false
      ≡
      Mixed.Mixed.respond Mixed.waveMixedSelectivitySystem
        Miller.leftSite Miller.secondTick false → ⊥

    waveSupportedCoalition : Coalition.WaveSupportedAccessCandidate

    sourceAtlasNowHasSixteenRows :
      Sources.canonicalConsciousAccessSourceCount ≡ 16

open PNFWaveAccessTraumaLearningRegression public

canonicalPNFWaveAccessTraumaLearningRegression :
  PNFWaveAccessTraumaLearningRegression
canonicalPNFWaveAccessTraumaLearningRegression = record
  { genericRetentionWithoutAccess = Access.canonicalRetentionWithoutAccess
  ; movingWaveActuallyMovesSupport = Miller.movingSupportActuallyChanges
  ; crossFrequencySameGammaChangesReadout = CrossFrequency.sameGammaDifferentBeta
  ; betaLowOpensFixedAnatomicalEdge = CrossFrequency.betaLowOpensExistingAnatomicalEdge
  ; betaHighClosesSameAnatomicalEdge = CrossFrequency.betaHighClosesSameAnatomicalEdge
  ; phaseInterferenceChangesRecruitment = Interference.phaseDifferenceChangesRecruitment
  ; accessFailureDoesNotForceNoTypedMeet = PNFMemory.accessFailureCannotForceNoTypedMeet
  ; phaseRealignmentKeepsRememberedPNF = PNFMemory.phaseRealignmentPreservesRememberedPNF
  ; extinctionKeepsRememberedPNF = PNFMemory.extinctionPreservesRememberedPNF
  ; fastAccessOrderNoncommutes = Braid.ordersDiffer
  ; learnedStateChangesWaveSupportedSafety = Trauma.sameCueLearnedStateChangesWaveSupportedSafety
  ; contextWaveChainChangesAccessibleFibre = ContextWave.contextChangesAccessibleFibre
  ; sameBiasDoesNotDetermineFallacy = Bias.sameBiasCanFeedDifferentFallacies
  ; sameFallacyDoesNotDetermineAccessCause = Bias.sameFallacyCanHaveDifferentAccessCauses
  ; accessExpansionChangesLiveCandidateNotStorage = Pipeline.sameStoredCandidateDifferentLiveSurface
  ; accessibleCandidateStillNeedsAudit = Pipeline.accessDoesNotBypassFallacyAudit
  ; fastMediumSlowRemainDistinct = Timescale.fastNotMedium
  ; accessAndActuationExpansionRemainDistinct = Orthogonal.orthogonalExpansionsAreDistinct
  ; sameStimulusContextChangesMixedParticipation = Mixed.sameStimulusContextChangesParticipation
  ; waveSupportedCoalition = Coalition.canonicalWaveSupportedAccessCandidate
  ; sourceAtlasNowHasSixteenRows = Sources.canonicalConsciousAccessSourceCountIsSixteen
  }
