module DASHI.Law.CoerciveEncounterLawfulnessProductExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
import DASHI.Law.CoerciveEncounterLawfulnessBidiExact as Law

------------------------------------------------------------------------
-- Lawfulness is proof-relevant closure, not a label inferred from occurrence,
-- authority, outcome, or aggregate statistics.
------------------------------------------------------------------------

record AuthorityApplicable : Set where
  constructor authorityApplicable
  field authorityReference : String

record TriggerSatisfied : Set where
  constructor triggerSatisfied
  field triggerReference : String

record ScopeSatisfied : Set where
  constructor scopeSatisfied
  field scopeReference : String

record ProcedureSatisfied : Set where
  constructor procedureSatisfied
  field procedureReference : String

record TemporalPrioritySatisfied : Set where
  constructor temporalPrioritySatisfied
  field temporalReference : String

record SafeguardsSatisfied (edge : Law.LegalTransitionFibre) : Set where
  constructor safeguardsSatisfied
  field
    closure : Law.SafeguardClosure edge
    safeguardsReference : String

open SafeguardsSatisfied public

record LawfulEdge (edge : Law.LegalTransitionFibre) : Set where
  constructor lawfulEdge
  field
    occurredReceipt : Law.occurrence edge ≡ Law.occurred
    authorityReceipt : AuthorityApplicable
    triggerReceipt : TriggerSatisfied
    scopeReceipt : ScopeSatisfied
    procedureReceipt : ProcedureSatisfied
    safeguardsReceipt : SafeguardsSatisfied edge
    temporalReceipt : TemporalPrioritySatisfied
    positiveProducerReceipt : Law.evidence edge ≡ Law.positiveReceipt
    lawfulClassification : Law.lawfulness edge ≡ Law.lawful
    lawfulnessReference : String

open LawfulEdge public

lawfulEdgeHasOccurrence :
  ∀ {edge} → LawfulEdge edge → Law.occurrence edge ≡ Law.occurred
lawfulEdgeHasOccurrence = occurredReceipt

lawfulEdgeHasPositiveProducer :
  ∀ {edge} → LawfulEdge edge → Law.evidence edge ≡ Law.positiveReceipt
lawfulEdgeHasPositiveProducer = positiveProducerReceipt

------------------------------------------------------------------------
-- Fail-closed BIDI obligations.
------------------------------------------------------------------------

data LawfulnessCoordinate : Set where
  occurrenceCoordinate authorityCoordinate triggerCoordinate scopeCoordinate
  procedureCoordinate safeguardCoordinate temporalCoordinate evidenceCoordinate : LawfulnessCoordinate

data CoordinateState : Set where
  coordinateClosed coordinateOpen : CoordinateState

record LawfulnessObligationVector : Set where
  constructor lawfulnessObligationVector
  field
    occurrenceState authorityState triggerState scopeState : CoordinateState
    procedureState safeguardState temporalState evidenceState : CoordinateState

open LawfulnessObligationVector public

data LawfulnessReverseResult : Set where
  allLawfulnessCoordinatesClosed : LawfulnessReverseResult
  firstOpenLawfulnessCoordinate : LawfulnessCoordinate → LawfulnessReverseResult

firstOpenLawfulness : LawfulnessObligationVector → LawfulnessReverseResult
firstOpenLawfulness v with occurrenceState v
... | coordinateOpen = firstOpenLawfulnessCoordinate occurrenceCoordinate
... | coordinateClosed with authorityState v
...   | coordinateOpen = firstOpenLawfulnessCoordinate authorityCoordinate
...   | coordinateClosed with triggerState v
...     | coordinateOpen = firstOpenLawfulnessCoordinate triggerCoordinate
...     | coordinateClosed with scopeState v
...       | coordinateOpen = firstOpenLawfulnessCoordinate scopeCoordinate
...       | coordinateClosed with procedureState v
...         | coordinateOpen = firstOpenLawfulnessCoordinate procedureCoordinate
...         | coordinateClosed with safeguardState v
...           | coordinateOpen = firstOpenLawfulnessCoordinate safeguardCoordinate
...           | coordinateClosed with temporalState v
...             | coordinateOpen = firstOpenLawfulnessCoordinate temporalCoordinate
...             | coordinateClosed with evidenceState v
...               | coordinateOpen = firstOpenLawfulnessCoordinate evidenceCoordinate
...               | coordinateClosed = allLawfulnessCoordinatesClosed

missingSafeguardStopsClosure :
  firstOpenLawfulness
    (lawfulnessObligationVector
      coordinateClosed coordinateClosed coordinateClosed coordinateClosed
      coordinateClosed coordinateOpen coordinateClosed coordinateClosed)
  ≡ firstOpenLawfulnessCoordinate safeguardCoordinate
missingSafeguardStopsClosure = refl

missingTemporalPriorityStopsClosure :
  firstOpenLawfulness
    (lawfulnessObligationVector
      coordinateClosed coordinateClosed coordinateClosed coordinateClosed
      coordinateClosed coordinateClosed coordinateOpen coordinateClosed)
  ≡ firstOpenLawfulnessCoordinate temporalCoordinate
missingTemporalPriorityStopsClosure = refl

record LawfulnessProductBoundary : Set where
  constructor lawfulnessProductBoundary
  field
    powerExistenceAloneClosesLawfulness : Bool
    powerExistenceAloneClosesLawfulnessIsFalse :
      powerExistenceAloneClosesLawfulness ≡ false
    laterOutcomeClosesMissingSafeguard : Bool
    laterOutcomeClosesMissingSafeguardIsFalse :
      laterOutcomeClosesMissingSafeguard ≡ false
    everyRequiredCoordinateMustClose : Bool
    everyRequiredCoordinateMustCloseIsTrue :
      everyRequiredCoordinateMustClose ≡ true

canonicalLawfulnessProductBoundary : LawfulnessProductBoundary
canonicalLawfulnessProductBoundary =
  lawfulnessProductBoundary false refl false refl true refl
