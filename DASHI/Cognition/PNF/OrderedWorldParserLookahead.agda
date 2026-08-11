module DASHI.Cognition.PNF.OrderedWorldParserLookahead where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Cognition.PNF.ComplexityArithmetic

------------------------------------------------------------------------
-- Documents extend one accumulated world in authored order.  The next
-- semantic step is indexed by the world produced by the preceding step, so
-- two later documents cannot both inhabit the canonical fold against the same
-- stale prior world.
------------------------------------------------------------------------

data World : Set where
  world : Nat → World

data Document : Set where
  document : Nat → Document

data DocumentClosureEvidence : Set where
  documentFixedPoint : DocumentClosureEvidence

record WorldStep (prior : World) (source : Document) : Set where
  constructor worldStep
  field
    nextWorld : World
    closureEvidence : DocumentClosureEvidence

open WorldStep public

data OrderedWorldFold : World → Set where
  beginWorld : ∀ {w} → OrderedWorldFold w
  publishNext :
    ∀ {prior source}
    (prefix : OrderedWorldFold prior)
    (step : WorldStep prior source) →
    OrderedWorldFold (nextWorld step)

------------------------------------------------------------------------
-- Parser lookahead carries observation authority only.  It has no constructor
-- for WorldStep and therefore cannot publish a document or extend the world.
------------------------------------------------------------------------

data ParserObservation (source : Document) : Set where
  parsedObservation : ParserObservation source

data ParserAuthority : Set where
  parserObservationOnly : ParserAuthority

data SemanticAuthority : Set where
  closedDocumentPublication : SemanticAuthority

record ParserLookahead (source : Document) : Set where
  constructor parserLookahead
  field
    observation : ParserObservation source
    authority : ParserAuthority

open ParserLookahead public

canonicalParserLookahead : ∀ source → ParserLookahead source
canonicalParserLookahead source =
  parserLookahead parsedObservation parserObservationOnly

parserLookaheadHasObservationAuthority :
  ∀ source → authority (canonicalParserLookahead source) ≡ parserObservationOnly
parserLookaheadHasObservationAuthority source = refl

------------------------------------------------------------------------
-- The runtime has exactly one semantic frontier and at most one buffered
-- parser document.  The slot is physical lookahead, not a second semantic
-- compiler lane.
------------------------------------------------------------------------

data SemanticFrontier : Set where
  frontierIdle : World → SemanticFrontier
  frontierCompiling : World → Document → SemanticFrontier

data LookaheadSlot : Set where
  emptyLookahead : LookaheadSlot
  bufferedLookahead :
    (source : Document) → ParserLookahead source → LookaheadSlot

record OrderedExecutionState : Set where
  constructor orderedExecutionState
  field
    currentWorld : World
    semanticFrontier : SemanticFrontier
    parserSlot : LookaheadSlot

open OrderedExecutionState public

initialOrderedExecution : World → OrderedExecutionState
initialOrderedExecution prior =
  orderedExecutionState prior (frontierIdle prior) emptyLookahead

bufferOneParserDocument :
  ∀ {source} →
  ParserLookahead source →
  OrderedExecutionState →
  OrderedExecutionState
bufferOneParserDocument {source} parsed state =
  orderedExecutionState
    (currentWorld state)
    (semanticFrontier state)
    (bufferedLookahead source parsed)

------------------------------------------------------------------------
-- Parser and foreground lanes share one hard worker budget.  Worker counts
-- are execution parameters and have no semantic effect on the ordered fold.
------------------------------------------------------------------------

record WorkerAllocation : Set where
  constructor workerAllocation
  field
    totalWorkers : Nat
    foregroundWorkers : Nat
    parserLookaheadWorkers : Nat
    withinGlobalBudget :
      (foregroundWorkers +ᶜ parserLookaheadWorkers) ≤ᶜ totalWorkers

open WorkerAllocation public

twoWorkers : Nat
twoWorkers = suc (suc zero)

fourWorkers : Nat
fourWorkers = suc (suc (suc (suc zero)))

canonicalFourWorkerSplit : WorkerAllocation
canonicalFourWorkerSplit =
  workerAllocation
    fourWorkers
    twoWorkers
    twoWorkers
    (≤ᶜ-refl fourWorkers)

canonicalFourWorkerSplitUsesWholeBudget :
  (foregroundWorkers canonicalFourWorkerSplit +ᶜ
    parserLookaheadWorkers canonicalFourWorkerSplit)
  ≡ totalWorkers canonicalFourWorkerSplit
canonicalFourWorkerSplitUsesWholeBudget = refl

------------------------------------------------------------------------
-- Size classification selects only physical parser work.  In particular, a
-- large document may begin parser observation while earlier small documents
-- cross the semantic frontier, without changing publication order.
------------------------------------------------------------------------

data ParserWorkClass : Set where
  inlineParserWork partitionedParserWork : ParserWorkClass

selectForLookahead : ParserWorkClass → Bool
selectForLookahead inlineParserWork = false
selectForLookahead partitionedParserWork = true

record PhysicalSchedulingDeclaration : Set where
  constructor physicalSchedulingDeclaration
  field
    heavyDocumentLookaheadEnabled : Bool
    bufferedDocumentLimit : Nat
    parserSelectionChangesSemanticAuthority : Bool
    concurrentSemanticPublicationEnabled : Bool

open PhysicalSchedulingDeclaration public

currentPR470OrderedWorldStatus : PhysicalSchedulingDeclaration
currentPR470OrderedWorldStatus =
  physicalSchedulingDeclaration true (suc zero) false false

record OrderedWorldAuthorityBoundary : Set where
  constructor orderedWorldAuthorityBoundary
  field
    heavyParserLookaheadIsWired :
      heavyDocumentLookaheadEnabled currentPR470OrderedWorldStatus ≡ true
    exactlyOneParserDocumentMayBeBuffered :
      bufferedDocumentLimit currentPR470OrderedWorldStatus ≡ suc zero
    parserSelectionHasNoSemanticEffect :
      parserSelectionChangesSemanticAuthority currentPR470OrderedWorldStatus
        ≡ false
    semanticPublicationRemainsSerial :
      concurrentSemanticPublicationEnabled currentPR470OrderedWorldStatus
        ≡ false

canonicalOrderedWorldAuthorityBoundary : OrderedWorldAuthorityBoundary
canonicalOrderedWorldAuthorityBoundary =
  orderedWorldAuthorityBoundary refl refl refl refl
