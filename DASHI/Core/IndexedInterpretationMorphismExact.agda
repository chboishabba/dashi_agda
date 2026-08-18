module DASHI.Core.IndexedInterpretationMorphismExact where

open import DASHI.Core.Prelude

record InterpretationIndex
    (Operator Context Query Role : Set) : Set where
  constructor interpretationIndex
  field
    operator : Operator
    context : Context
    query : Query
    role : Role

open InterpretationIndex public

record IndexedInterpretation
    (State Output Operator Context Query Role : Set) : Set₁ where
  constructor indexedInterpretation
  field
    interpret :
      InterpretationIndex Operator Context Query Role →
      State → Output

open IndexedInterpretation public

-- Equality at one interpretation index is not globally transportable without a
-- theorem relating the two indices.  This is the common shape behind
-- action-indexed 369 quotients and inference-language-indexed ontology safety.
OutputEqualityTransfersAcrossIndices :
  ∀ {State Output Operator Context Query Role} →
  IndexedInterpretation State Output Operator Context Query Role → Set
OutputEqualityTransfersAcrossIndices system =
  ∀ leftIndex rightIndex x y →
  interpret system leftIndex x ≡ interpret system leftIndex y →
  interpret system rightIndex x ≡ interpret system rightIndex y

------------------------------------------------------------------------
-- Exact countermodel: the same carrier has one coarse operation and one fine
-- operation.  The coarse surface identifies two states that the fine query
-- separates.
------------------------------------------------------------------------

data DemoState : Set where
  state₀ state₁ : DemoState

data DemoOperator : Set where
  observeOperator : DemoOperator

data DemoContext : Set where
  sharedContext : DemoContext

data DemoQuery : Set where
  coarseQuery fineQuery : DemoQuery

data DemoRole : Set where
  observationRole : DemoRole

coarseIndex : InterpretationIndex DemoOperator DemoContext DemoQuery DemoRole
coarseIndex = interpretationIndex observeOperator sharedContext coarseQuery observationRole

fineIndex : InterpretationIndex DemoOperator DemoContext DemoQuery DemoRole
fineIndex = interpretationIndex observeOperator sharedContext fineQuery observationRole

demoInterpret :
  InterpretationIndex DemoOperator DemoContext DemoQuery DemoRole →
  DemoState → Bool
demoInterpret index state with query index
... | coarseQuery = false
... | fineQuery with state
...   | state₀ = false
...   | state₁ = true

demoSystem :
  IndexedInterpretation DemoState Bool DemoOperator DemoContext DemoQuery DemoRole
demoSystem = indexedInterpretation demoInterpret

coarseCollision :
  interpret demoSystem coarseIndex state₀ ≡ interpret demoSystem coarseIndex state₁
coarseCollision = refl

fineSeparation :
  interpret demoSystem fineIndex state₀ ≡ interpret demoSystem fineIndex state₁ → ⊥
fineSeparation ()

surfaceEqualityDoesNotSupplyCrossIndexLicence :
  OutputEqualityTransfersAcrossIndices demoSystem → ⊥
surfaceEqualityDoesNotSupplyCrossIndexLicence transfer =
  fineSeparation (transfer coarseIndex fineIndex state₀ state₁ coarseCollision)

record IndexedInterpretationBoundary : Set where
  constructor indexedInterpretationBoundary
  field
    sameCarrierMayAdmitDifferentInterpretations : Bool
    equalityAtOneIndexAutomaticallyTransfersToEveryIndex : Bool
    operatorContextQueryRoleArePartOfInterpretationLicence : Bool

canonicalIndexedInterpretationBoundary : IndexedInterpretationBoundary
canonicalIndexedInterpretationBoundary =
  indexedInterpretationBoundary true false true
