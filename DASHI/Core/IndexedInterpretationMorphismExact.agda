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

OutputEqualityTransfersAcrossIndices :
  ∀ {State Output Operator Context Query Role} →
  IndexedInterpretation State Output Operator Context Query Role → Set
OutputEqualityTransfersAcrossIndices system =
  ∀ leftIndex rightIndex x y →
  interpret system leftIndex x ≡ interpret system leftIndex y →
  interpret system rightIndex x ≡ interpret system rightIndex y

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
demoInterpret (interpretationIndex observeOperator sharedContext coarseQuery observationRole) state₀ = false
demoInterpret (interpretationIndex observeOperator sharedContext coarseQuery observationRole) state₁ = false
demoInterpret (interpretationIndex observeOperator sharedContext fineQuery observationRole) state₀ = false
demoInterpret (interpretationIndex observeOperator sharedContext fineQuery observationRole) state₁ = true

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
