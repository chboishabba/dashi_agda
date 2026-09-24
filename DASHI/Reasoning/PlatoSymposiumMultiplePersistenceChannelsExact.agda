module DASHI.Reasoning.PlatoSymposiumMultiplePersistenceChannelsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Core.AppendOnlyEvidenceResidualRevisionExact as Revision
import DASHI.Core.QueryFactorisationSufficiency as Query
import DASHI.Philosophy.PatternPreservingTeaching as Teaching
import DASHI.Philosophy.PlatoSymposiumPhilosophyBridgeExact as Plato
import DASHI.Reasoning.PlatoSymposiumResidualRevision369BridgeExact as Prior

------------------------------------------------------------------------
-- PLATO SYMPOSIUM / MULTIPLE PERSISTENCE CHANNELS
--
-- Diotima's source-bounded "same yet other" fixture motivates a question:
-- what carries continuity through change?  Existing DASHI owners already give
-- several answers with different formal grammars:
--
--   * MemoryFibre / VersionedMemory:
--       retained event/provenance and prior states under revaluation/action
--       change, with overwrite forbidden;
--   * PatternPreservingTeaching:
--       relational pattern continuity through participation, without equating
--       a local lesson with the whole tradition;
--   * AppendOnlyEvidenceResidualRevisionExact:
--       earlier evidence/history persists while the current consumer
--       conclusion may change.
--
-- This owner does not define a universal theory of identity or persistence.
-- It proves only that the coarse label "persists through change" cannot by
-- itself determine which continuity mechanism is in play.
------------------------------------------------------------------------

existingPersistenceOwnersReused : Bool
existingPersistenceOwnersReused = true

sourcePersistenceContract : Plato.LeanPhilosophyTheoremContract
sourcePersistenceContract = Plato.mortalPersistenceContract

priorCurrentSurfaceHistoryTheorem :
  Query.FactorsThrough
    Prior.persistenceHistoryQuestions
    Prior.currentPersistenceProjection
    Prior.persistenceHistoryQuestion → ⊥
priorCurrentSurfaceHistoryTheorem = Prior.currentSurfaceDoesNotDeterminePersistenceHistory

existingTeachingBoundary : Teaching.TeachingBoundary
existingTeachingBoundary = Teaching.canonicalTeachingBoundary

existingRevisionBoundary : Revision.AppendOnlyEvidenceRevisionBoundary
existingRevisionBoundary = Revision.canonicalAppendOnlyEvidenceRevisionBoundary

versionedMemoryCarrier : Set
versionedMemoryCarrier = Memory.VersionedMemory

------------------------------------------------------------------------
-- Same persistence label / different continuity mechanism.
------------------------------------------------------------------------

data PersistenceChannelWorld : Set where
  memoryChannelWorld : PersistenceChannelWorld
  teachingChannelWorld : PersistenceChannelWorld
  revisionChannelWorld : PersistenceChannelWorld

data PersistenceLabel : Set where
  persistsThroughChange : PersistenceLabel

data ContinuityMechanismQuery : Set where
  continuityMechanismQuestion : ContinuityMechanismQuery

data ContinuityMechanismAnswer : Set where
  retainedMemoryLineage : ContinuityMechanismAnswer
  relationalPatternTransmission : ContinuityMechanismAnswer
  appendOnlyRevisionLineage : ContinuityMechanismAnswer

persistenceLabelProjection : PersistenceChannelWorld → PersistenceLabel
persistenceLabelProjection memoryChannelWorld = persistsThroughChange
persistenceLabelProjection teachingChannelWorld = persistsThroughChange
persistenceLabelProjection revisionChannelWorld = persistsThroughChange

ContinuityMechanismAnswerFor : ContinuityMechanismQuery → Set
ContinuityMechanismAnswerFor continuityMechanismQuestion = ContinuityMechanismAnswer

askContinuityMechanism :
  (query : ContinuityMechanismQuery) →
  PersistenceChannelWorld →
  ContinuityMechanismAnswerFor query
askContinuityMechanism continuityMechanismQuestion memoryChannelWorld =
  retainedMemoryLineage
askContinuityMechanism continuityMechanismQuestion teachingChannelWorld =
  relationalPatternTransmission
askContinuityMechanism continuityMechanismQuestion revisionChannelWorld =
  appendOnlyRevisionLineage

continuityMechanismQuestions :
  Query.InquiryQuestionFamily PersistenceChannelWorld ContinuityMechanismQuery
continuityMechanismQuestions =
  Query.inquiryQuestionFamily ContinuityMechanismAnswerFor askContinuityMechanism

persistenceLabelDoesNotDetermineContinuityMechanism :
  Query.FactorsThrough
    continuityMechanismQuestions
    persistenceLabelProjection
    continuityMechanismQuestion → ⊥
persistenceLabelDoesNotDetermineContinuityMechanism factor = helper first second
  where
    first :
      retainedMemoryLineage ≡ Query.quotientAnswer factor persistsThroughChange
    first = Query.factorisation factor memoryChannelWorld

    second :
      relationalPatternTransmission ≡ Query.quotientAnswer factor persistsThroughChange
    second = Query.factorisation factor teachingChannelWorld

    helper :
      retainedMemoryLineage ≡ Query.quotientAnswer factor persistsThroughChange →
      relationalPatternTransmission ≡ Query.quotientAnswer factor persistsThroughChange →
      ⊥
    helper refl ()

------------------------------------------------------------------------
-- Concrete donor pins: these mechanisms preserve different coordinates.
------------------------------------------------------------------------

memoryRevaluationPreservesRememberedEvent :
  (memory : Memory.MemoryFibre) →
  (value : Nat) →
  Memory.rememberedEvent (Memory.revalue memory value) ≡
  Memory.rememberedEvent memory
memoryRevaluationPreservesRememberedEvent = Memory.revaluePreservesRememberedEvent

memoryExtinctionPreservesRememberedEvent :
  (memory : Memory.MemoryFibre) →
  Memory.rememberedEvent (Memory.extinguishActionDominance memory) ≡
  Memory.rememberedEvent memory
memoryExtinctionPreservesRememberedEvent = Memory.extinctionPreservesRememberedEvent

teachingLocalLessonIsNotWholeTradition :
  Teaching.localLessonEqualsWholeTradition Teaching.canonicalTeachingBoundary ≡ false
teachingLocalLessonIsNotWholeTradition = Teaching.canonicalLessonIsNotWholeTradition

revisionMayRetainOldEvidenceWhileConclusionChanges :
  Revision.oldEvidenceMayRemainValidWhileConsumerConclusionChanges
    Revision.canonicalAppendOnlyEvidenceRevisionBoundary ≡ true
revisionMayRetainOldEvidenceWhileConclusionChanges = refl

------------------------------------------------------------------------
-- Cross-domain firewall.
------------------------------------------------------------------------

record PlatoMultiplePersistenceBoundary : Set where
  constructor plato-multiple-persistence-boundary
  field
    persistenceLabelDeterminesContinuityMechanism : Bool
    memoryPersistenceDefinitionallyEqualsTeachingPersistence : Bool
    teachingPersistenceDefinitionallyEqualsAppendOnlyRevision : Bool
    diotimaPersistenceOwnsDashiContinuityMechanisms : Bool
    onePersistenceMechanismIsUniversallyPrivileged : Bool
    multiplePersistenceChannelsMayShareCoarseShape : Bool
    mechanismSpecificCoordinatesMustRemainVisible : Bool
    sourceFixtureMayMotivatePersistenceComparison : Bool
    semanticBridgeRequiredForEachCrossPollination : Bool

open PlatoMultiplePersistenceBoundary public

canonicalPlatoMultiplePersistenceBoundary : PlatoMultiplePersistenceBoundary
canonicalPlatoMultiplePersistenceBoundary =
  plato-multiple-persistence-boundary
    false
    false
    false
    false
    false
    true
    true
    true
    true

persistenceChannelSummary : String
persistenceChannelSummary =
  "Diotima's source-bounded same-yet-other fixture can motivate comparison among DASHI continuity mechanisms, but memory lineage, relational teaching, append-only revision and history-indexed computation remain different carriers with different retained coordinates; the coarse persistence label does not determine the mechanism."
