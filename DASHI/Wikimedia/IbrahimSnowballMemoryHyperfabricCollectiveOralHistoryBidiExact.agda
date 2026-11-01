module DASHI.Wikimedia.IbrahimSnowballMemoryHyperfabricCollectiveOralHistoryBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Wikimedia.IbrahimSnowballLearningMemoryTraumaReplicationConsensusBidiExact as Individual
import DASHI.Wikimedia.IbrahimSnowballSourceMonitoringCollectiveMemoryEpistemicInjusticeBidiExact as Collective
import DASHI.Wikimedia.IbrahimSnowballOralHistoryTraditionArchivalSilenceDigitalMemoryBidiExact as Oral
import DASHI.Cognition.PNF.DepthWheelMemoryHyperfabric as DepthMemory
import DASHI.Cognition.PNF.TraumaMemoryHypervoxelBridge as TraumaMemory

------------------------------------------------------------------------
-- THIN BIDI WELD: INDIVIDUAL MEMORY HYPERFABRIC <-> COLLECTIVE/ORAL MEMORY
--
-- Existing owners already cover memory-learning fibres, trauma authority,
-- source monitoring, collective memory, oral history and archival silence.
-- This file adds only the missing cross-level nonfactorability witnesses.
------------------------------------------------------------------------

learningQid = Individual.learningQid
memoryQid = Individual.memoryQid
psychologicalTraumaQid = Individual.psychologicalTraumaQid
collectiveMemoryQid = Collective.collectiveMemoryQid
oralHistoryDisciplineQid = Oral.oralHistoryDisciplineQid
oralHistoryRecordQid = Oral.oralHistoryRecordQid
oralTraditionQid = Oral.oralTraditionQid
forgettingQid = Oral.forgettingQid

learningDeweyPsychology = Individual.learningDeweyPsychology
learningDeweyEducation = Individual.learningDeweyEducation
collectiveMemoryDewey = Collective.collectiveMemoryDewey
oralHistoryDewey = Oral.oralHistoryDewey

sourceMonitoringSource = Collective.johnsonSourceMonitoringSource
collectiveMemorySource = Collective.wertschRoedigerCollectiveMemorySource
oralMemorySource = Oral.thomsonOralMemorySource

------------------------------------------------------------------------
-- Regression 1: a stable collective/public narrative cannot recover the latent
-- memory/learning state of an individual participant.
------------------------------------------------------------------------

data CollectiveIndividualCase : Set where
  sameNarrativeEarlierIndividualState sameNarrativeLaterIndividualState : CollectiveIndividualCase

data CollectiveNarrativeSurface : Set where samePublicNarrative : CollectiveNarrativeSurface
data IndividualMemoryState : Set where earlierMemoryState laterMemoryState : IndividualMemoryState

collectiveNarrativeSurface : CollectiveIndividualCase → CollectiveNarrativeSurface
collectiveNarrativeSurface _ = samePublicNarrative

individualMemoryState : CollectiveIndividualCase → IndividualMemoryState
individualMemoryState sameNarrativeEarlierIndividualState = earlierMemoryState
individualMemoryState sameNarrativeLaterIndividualState = laterMemoryState

collectiveIndividualDefect :
  INF.NonFactorabilityWitness collectiveNarrativeSurface individualMemoryState
collectiveIndividualDefect = INF.nonFactorabilityWitness
  sameNarrativeEarlierIndividualState sameNarrativeLaterIndividualState refl (λ ())

collectiveNarrativeCannotFactorIndividualMemoryState :
  INF.FactorsThrough collectiveNarrativeSurface individualMemoryState → ⊥
collectiveNarrativeCannotFactorIndividualMemoryState =
  INF.witnessRulesOutEveryFlatFactorisation collectiveIndividualDefect

------------------------------------------------------------------------
-- Regression 2: identical remembered semantic content cannot recover whether
-- that content was directly experienced or socially/collectively acquired.
------------------------------------------------------------------------

data OriginCase : Set where
  sameRememberedSurfaceDirect sameRememberedSurfaceSocial : OriginCase

data RememberedSurface : Set where sameRememberedSemanticContent : RememberedSurface
data MemoryOrigin : Set where directOrigin sociallyAcquiredOrigin : MemoryOrigin

rememberedSurface : OriginCase → RememberedSurface
rememberedSurface _ = sameRememberedSemanticContent

memoryOrigin : OriginCase → MemoryOrigin
memoryOrigin sameRememberedSurfaceDirect = directOrigin
memoryOrigin sameRememberedSurfaceSocial = sociallyAcquiredOrigin

originDefect : INF.NonFactorabilityWitness rememberedSurface memoryOrigin
originDefect = INF.nonFactorabilityWitness
  sameRememberedSurfaceDirect sameRememberedSurfaceSocial refl (λ ())

rememberedSurfaceCannotFactorSourceOrigin :
  INF.FactorsThrough rememberedSurface memoryOrigin → ⊥
rememberedSurfaceCannotFactorSourceOrigin =
  INF.witnessRulesOutEveryFlatFactorisation originDefect

------------------------------------------------------------------------
-- Regression 3: an oral-history record cannot recover the full latent
-- learning/body-memory hyperfabric of the speaker.
------------------------------------------------------------------------

data OralRecordCase : Set where
  sameOralRecordLatentStateA sameOralRecordLatentStateB : OralRecordCase

data OralRecordSurface : Set where sameOralRecord : OralRecordSurface
data LatentHyperfabricState : Set where latentStateA latentStateB : LatentHyperfabricState

oralRecordSurface : OralRecordCase → OralRecordSurface
oralRecordSurface _ = sameOralRecord

latentHyperfabricState : OralRecordCase → LatentHyperfabricState
latentHyperfabricState sameOralRecordLatentStateA = latentStateA
latentHyperfabricState sameOralRecordLatentStateB = latentStateB

oralLatentDefect : INF.NonFactorabilityWitness oralRecordSurface latentHyperfabricState
oralLatentDefect = INF.nonFactorabilityWitness
  sameOralRecordLatentStateA sameOralRecordLatentStateB refl (λ ())

oralHistoryRecordCannotFactorFullMemoryHyperfabric :
  INF.FactorsThrough oralRecordSurface latentHyperfabricState → ⊥
oralHistoryRecordCannotFactorFullMemoryHyperfabric =
  INF.witnessRulesOutEveryFlatFactorisation oralLatentDefect

------------------------------------------------------------------------
-- Existing boundaries reused exactly.
------------------------------------------------------------------------

individualBoundary : Individual.LearningMemoryTraumaReplicationConsensusBoundary
individualBoundary = Individual.canonicalLearningMemoryTraumaReplicationConsensusBoundary

collectiveBoundary : Collective.SourceMonitoringCollectiveMemoryEpistemicInjusticeBoundary
collectiveBoundary = Collective.canonicalSourceMonitoringCollectiveMemoryEpistemicInjusticeBoundary

oralBoundary : Oral.OralHistoryTraditionArchivalSilenceDigitalMemoryBoundary
oralBoundary = Oral.canonicalOralHistoryTraditionArchivalSilenceDigitalMemoryBoundary

depthMemoryBoundary : DepthMemory.DepthWheelMemoryHyperfabricBoundary
depthMemoryBoundary = DepthMemory.canonicalDepthWheelMemoryHyperfabricBoundary

traumaMemoryBoundary : TraumaMemory.TraumaMemoryHypervoxelAuthorityBoundary
traumaMemoryBoundary = TraumaMemory.canonicalTraumaMemoryHypervoxelAuthorityBoundary

------------------------------------------------------------------------
-- Reverse constraints.
------------------------------------------------------------------------

record MemoryScaleReverseConstraint : Set where
  constructor memory-scale-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open MemoryScaleReverseConstraint public

memoryConstraint : MemoryScaleReverseConstraint
memoryConstraint = memory-scale-reverse-constraint
  "Memory / cognition"
  "individual latent state, remembered semantic surface, remembered source and socially circulated narrative remain distinct"
  false

historyConstraint : MemoryScaleReverseConstraint
historyConstraint = memory-scale-reverse-constraint
  "History / oral history / collective memory"
  "participant recollection, interview record, collective narrative, archive survival and historical truth remain distinct"
  false

traumaConstraint : MemoryScaleReverseConstraint
traumaConstraint = memory-scale-reverse-constraint
  "Trauma / body-memory hyperfabric"
  "oral or collective narrative cannot recover typed body-memory channels, learning phase, residual state or clinical diagnosis"
  false

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data CollectiveNarrativeMeansSameIndividualMemory : Set where
data OralRecordMeansFullMemoryState : Set where
data CollectiveMemoryMeansTraumaDiagnosis : Set where
data SharedNarrativeMeansIndependentMemoryOrigins : Set where

collectiveNarrativeDoesNotMeanSameIndividualMemory :
  CollectiveNarrativeMeansSameIndividualMemory → ⊥
collectiveNarrativeDoesNotMeanSameIndividualMemory ()

oralRecordDoesNotMeanFullMemoryState : OralRecordMeansFullMemoryState → ⊥
oralRecordDoesNotMeanFullMemoryState ()

collectiveMemoryDoesNotMeanTraumaDiagnosis : CollectiveMemoryMeansTraumaDiagnosis → ⊥
collectiveMemoryDoesNotMeanTraumaDiagnosis ()

sharedNarrativeDoesNotMeanIndependentMemoryOrigins :
  SharedNarrativeMeansIndependentMemoryOrigins → ⊥
sharedNarrativeDoesNotMeanIndependentMemoryOrigins ()

record MemoryHyperfabricCollectiveOralBoundary : Set where
  constructor memory-hyperfabric-collective-oral-boundary
  field
    existingOwnersReused : Bool
    qidCoordinatesReused : Bool
    deweyCoordinatesReused : Bool
    doiSourceRolesReused : Bool
    collectiveNarrativeSeparatedFromIndividualLatentState : Bool
    rememberedContentSeparatedFromSourceOrigin : Bool
    oralRecordSeparatedFromFullMemoryHyperfabric : Bool
    traumaDiagnosisBoundaryRetained : Bool
    reverseBidiConstraintsPropagateUpward : Bool
    presentAxisVocabularyClaimedComplete : Bool
open MemoryHyperfabricCollectiveOralBoundary public

canonicalMemoryHyperfabricCollectiveOralBoundary :
  MemoryHyperfabricCollectiveOralBoundary
canonicalMemoryHyperfabricCollectiveOralBoundary =
  memory-hyperfabric-collective-oral-boundary
    true true true true true true true true true false
