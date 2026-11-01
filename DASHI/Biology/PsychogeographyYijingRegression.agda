module DASHI.Biology.PsychogeographyYijingRegression where

open import DASHI.Core.Prelude

import DASHI.Biology.DASHIYijingTernaryDivinationExact as Yijing
import DASHI.Reasoning.TypedHyperfabricCore as Hyperfabric
import DASHI.Biology.PsychogeographicFieldExact as Field
import DASHI.Biology.PsychogeographicHexagramObservationExact as Observation
import DASHI.Biology.TraumaPsychogeographicMetricExact as Metric
import DASHI.Biology.TraumaSensitiveDeriveExact as Derive
import DASHI.Biology.UrbanPolyphonyThoughtCabinetExact as Urban
import DASHI.Biology.RuinNarrativeReorganisationExact as Ruin
import DASHI.Biology.DiscoElysiumPsychogeographyExact as Disco
import DASHI.Biology.PsychogeographicFilteredScaleExact as Filtered
import DASHI.Biology.PsychogeographyYijingSourceAtlas as Sources

pathEndpointRegression :
  Field.site (Field.finalState Field.memoryRoute)
  ≡ Field.site (Field.finalState Field.reoccupationRoute)
pathEndpointRegression = Field.samePhysicalEndpoint

pathDependenceRegression :
  ¬ (Field.phase (Field.finalState Field.memoryRoute)
     ≡ Field.phase (Field.finalState Field.reoccupationRoute))
pathDependenceRegression = Field.sameEndpointDoesNotForceSamePhase

projectionLossRegression :
  Observation.coarseHexagram Observation.sameHexDifferentPathA
  ≡ Observation.coarseHexagram Observation.sameHexDifferentPathB
projectionLossRegression = Observation.projectionLosesPathInformation

hexagramDifferenceRegression :
  Observation.hexagramDifference
    Yijing.canonicalTernaryHexagram
    Yijing.canonicalResultingHexagram
  ≡ 2
hexagramDifferenceRegression =
  Observation.canonicalAnticipatedEncounteredDifferenceIsTwo

metricDeformationRegression :
  Metric.physicalDistance Metric.nearbyBlockedRelation ≡ 1
  × Metric.psychogeographicDistance Metric.nearbyBlockedRelation ≡ 9
metricDeformationRegression = Metric.nearbyCanBePsychogeographicallyDistant

productiveFailureRegression :
  Derive.outcomePosition Derive.productiveFailure
  ≡ Derive.outcomePosition Derive.withdrewSafely
productiveFailureRegression = Derive.productiveFailureKeepsPhysicalPosition

thoughtCapacityRegression :
  Urban.listCount (Urban.activeThoughts Urban.canonicalThoughtCabinet) ≡ 2
thoughtCapacityRegression = Urban.canonicalCabinetHasTwoActiveThoughts

ruinNonErasureRegression :
  Hyperfabric.stalkContentErased Ruin.ruinReorganisation
  ≡ false
ruinNonErasureRegression = Ruin.ruinReorganisationDeclaresNoStalkErasure

paleContentRetentionRegression :
  Disco.content (Disco.paleCrossTalk Disco.stableTrace)
  ≡ Disco.content Disco.stableTrace
paleContentRetentionRegression = proj₁ Disco.crossTalkPreservesContentWhileWeakeningProvenance

filteredTotalRegression : Filtered.profileTotal Filtered.canonicalProfile ≡ 21
filteredTotalRegression = Filtered.canonicalProfileTotalIsTwentyOne

sourceCountRegression : Sources.listCount Sources.allPsychogeographySources ≡ 10
sourceCountRegression = Sources.sourceAtlasHasTenRecords
