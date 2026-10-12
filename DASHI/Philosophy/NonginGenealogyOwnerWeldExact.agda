module DASHI.Philosophy.NonginGenealogyOwnerWeldExact where

------------------------------------------------------------------------
-- NONGIN GENEALOGY -> TYPED DESCENDANT OWNER WELD
--
-- DialecticOriginSourceAtlasExact is the canonical provenance map.  Several of
-- its phases already have concrete typed descendants elsewhere in the repo.
-- This module records those links without identifying the historical concepts
-- with the later mathematics.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Core.Prelude using (⊥)

import DASHI.Core.DialecticOriginSourceAtlasExact as Atlas
import DASHI.Core.NonginOnePointOneArmyRefinementExact as OnePointOne
import DASHI.Core.EpistemicSuspensionExact as Suspension
import DASHI.Core.ThresholdResidualTrajectoryGeometryExact as Threshold
import DASHI.Core.RelationalEpistemicProcessSourceBridgeExact as Relational
import DASHI.Core.DialecticStageMotifBridgeExact as StageMotif

metaPositionEntry : Atlas.OriginSourceEntry
metaPositionEntry = Atlas.entryForPhase Atlas.metaPositionPowerUp

hierarchicalRefinementEntry : Atlas.OriginSourceEntry
hierarchicalRefinementEntry =
  Atlas.entryForPhase Atlas.padicHierarchicalRefinement

thresholdGeometryEntry : Atlas.OriginSourceEntry
thresholdGeometryEntry = Atlas.entryForPhase Atlas.nonlinearThresholdGeometry

relationalEpistemologyEntry : Atlas.OriginSourceEntry
relationalEpistemologyEntry = Atlas.entryForPhase Atlas.relationalEpistemology

ethicalProcessEntry : Atlas.OriginSourceEntry
ethicalProcessEntry = Atlas.entryForPhase Atlas.ethicalProcessArchitecture

operationalStateTensorEntry : Atlas.OriginSourceEntry
operationalStateTensorEntry = Atlas.entryForPhase Atlas.operationalStateTensor

metaPositionEntryHasDeclaredPhase :
  Atlas.phase metaPositionEntry ≡ Atlas.metaPositionPowerUp
metaPositionEntryHasDeclaredPhase = refl

hierarchicalRefinementEntryHasDeclaredPhase :
  Atlas.phase hierarchicalRefinementEntry ≡ Atlas.padicHierarchicalRefinement
hierarchicalRefinementEntryHasDeclaredPhase = refl

thresholdGeometryEntryHasDeclaredPhase :
  Atlas.phase thresholdGeometryEntry ≡ Atlas.nonlinearThresholdGeometry
thresholdGeometryEntryHasDeclaredPhase = refl

relationalEpistemologyEntryHasDeclaredPhase :
  Atlas.phase relationalEpistemologyEntry ≡ Atlas.relationalEpistemology
relationalEpistemologyEntryHasDeclaredPhase = refl

ethicalProcessEntryHasDeclaredPhase :
  Atlas.phase ethicalProcessEntry ≡ Atlas.ethicalProcessArchitecture
ethicalProcessEntryHasDeclaredPhase = refl

operationalStateTensorEntryHasDeclaredPhase :
  Atlas.phase operationalStateTensorEntry ≡ Atlas.operationalStateTensor
operationalStateTensorEntryHasDeclaredPhase = refl

onePointOneBoundary : OnePointOne.NonginOnePointOneArmyBoundary
onePointOneBoundary = OnePointOne.canonicalNonginOnePointOneArmyBoundary

suspensionBoundary : Suspension.EpistemicSuspensionBoundary
suspensionBoundary = Suspension.canonicalEpistemicSuspensionBoundary

thresholdBoundary : Threshold.ThresholdTrajectoryBoundary
thresholdBoundary = Threshold.canonicalThresholdTrajectoryBoundary

relationalBoundary : Relational.RelationalEpistemicProcessBoundary
relationalBoundary = Relational.canonicalRelationalEpistemicProcessBoundary

stageMotifBoundary : StageMotif.DialecticStageMotifBoundary
stageMotifBoundary = StageMotif.canonicalDialecticStageMotifBoundary

onePointOneStrictRefinementOwnerPaid :
  OnePointOne.nontrivialFrameCanSplitOldFibre onePointOneBoundary ≡ true
onePointOneStrictRefinementOwnerPaid = refl

onePointOneUsefulnessRemainsConsumerRelative :
  OnePointOne.usefulnessRequiresFrameSensitiveConsumer onePointOneBoundary ≡ true
onePointOneUsefulnessRemainsConsumerRelative = refl

neutralRefinementOwnerPaid :
  Suspension.neutralRequiresFurtherResolution suspensionBoundary ≡ true
neutralRefinementOwnerPaid = refl

thresholdStatusDoesNotDetermineResidual :
  Threshold.thresholdStatusDeterminesResidualMagnitude thresholdBoundary ≡ false
thresholdStatusDoesNotDetermineResidual = refl

relationalActionCannotBypassPriorPhases :
  Relational.actionMayBypassContextRelationAndReflection relationalBoundary ≡ false
relationalActionCannotBypassPriorPhases = refl

stateTensorMotifIsNotHistoricalStageIdentity :
  StageMotif.stage10DefinitionIsMotifM10 stageMotifBoundary ≡ false
stateTensorMotifIsNotHistoricalStageIdentity = refl

data GenealogicalInfluenceEqualsMathematicalIdentity : Set where

genealogicalInfluenceDoesNotCreateIdentity :
  GenealogicalInfluenceEqualsMathematicalIdentity → ⊥
genealogicalInfluenceDoesNotCreateIdentity ()

record NonginGenealogyOwnerWeldBoundary : Set where
  constructor nongin-genealogy-owner-weld-boundary
  field
    allTypedDescendantOwnersLinked : Bool
    metaPositionTypedOwnerLinked : Bool
    hierarchicalRefinementTypedOwnerLinked : Bool
    thresholdResidualTypedOwnerLinked : Bool
    relationalProcessTypedOwnerLinked : Bool
    operationalStageMotifBoundaryLinked : Bool
    sourceGenealogyIdentifiedWithLaterMathematics : Bool

open NonginGenealogyOwnerWeldBoundary public

canonicalNonginGenealogyOwnerWeldBoundary : NonginGenealogyOwnerWeldBoundary
canonicalNonginGenealogyOwnerWeldBoundary =
  nongin-genealogy-owner-weld-boundary
    true true true true true true false
