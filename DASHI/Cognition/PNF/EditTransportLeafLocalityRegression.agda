module DASHI.Cognition.PNF.EditTransportLeafLocalityRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (suc)
open import Data.Empty using (⊥)
open import Data.List.Base using ([]; _∷_)
open import Data.Product using (_×_; _,_)

open import DASHI.Cognition.PNF.EditTransportLeafLocalityExact
open import DASHI.Cognition.PNF.EditTransportCompositionExact

identityTransport : EditTransport
identityTransport = identityEditTransport

sharedOccurrence : OccurrenceSignature
sharedOccurrence = occurrenceSignature 2 100 (100 ∷ 101 ∷ []) 7 9

beforeLeaf : AuditLeaf
beforeLeaf = auditLeaf sharedOccurrence 10

afterLeaf : AuditLeaf
afterLeaf = auditLeaf sharedOccurrence 11

competingAfterLeaf : AuditLeaf
competingAfterLeaf = auditLeaf sharedOccurrence 12

beforeMatchesAfter : TransportedOccurrenceMatch identityTransport beforeLeaf afterLeaf
beforeMatchesAfter = transportedOccurrenceMatch refl refl refl refl refl

beforeMatchesCompeting :
  TransportedOccurrenceMatch identityTransport beforeLeaf competingAfterLeaf
beforeMatchesCompeting = transportedOccurrenceMatch refl refl refl refl refl

semanticValueReallyChanged : SemanticValueChanged beforeLeaf afterLeaf
semanticValueReallyChanged ()

afterLeavesDistinct : afterLeaf ≡ competingAfterLeaf → ⊥
afterLeavesDistinct ()

transportedOccurrenceIdentityDoesNotAssumeSemanticEquality :
  TransportedOccurrenceMatch identityTransport beforeLeaf afterLeaf ×
  SemanticValueChanged beforeLeaf afterLeaf
transportedOccurrenceIdentityDoesNotAssumeSemanticEquality =
  beforeMatchesAfter , semanticValueReallyChanged

ambiguousTargetsBlockVerifiedCorrespondence :
  {Eligible : AuditLeaf → Set} →
  Eligible beforeLeaf →
  VerifiedLeafCorrespondence
    Eligible
    (TransportedOccurrenceMatch identityTransport) →
  ⊥
ambiguousTargetsBlockVerifiedCorrespondence eligible certificate =
  ambiguityRefutesVerifiedCorrespondence
    certificate
    beforeLeaf
    eligible
    afterLeaf
    competingAfterLeaf
    beforeMatchesAfter
    beforeMatchesCompeting
    afterLeavesDistinct

data TinyWitness : Set where
  tinyWitness : TinyWitness

data TinySource : Set where
  editedSource : TinySource

data TinyLeaf : Set where
  changedNode : TinyLeaf
  extraPredictedNode : TinyLeaf

tinyEdited : TinySource → Set
tinyEdited editedSource = TinyWitness

tinyReaches : TinySource → TinyLeaf → Set
tinyReaches editedSource changedNode = TinyWitness
tinyReaches editedSource extraPredictedNode = TinyWitness

tinyChanged : TinyLeaf → Set
tinyChanged changedNode = TinyWitness
tinyChanged extraPredictedNode = ⊥

tinyClosure : EditedDependencyClosure TinySource TinyLeaf
tinyClosure = editedDependencyClosure tinyEdited tinyReaches

tinyClosureIsSound : ClosureSound tinyClosure tinyChanged
tinyClosureIsSound changedNode tinyWitness =
  editedSource , tinyWitness , tinyWitness
tinyClosureIsSound extraPredictedNode ()

tinyClosureIsNotExact : ClosureExact tinyClosure tinyChanged → ⊥
tinyClosureIsNotExact exact with exact extraPredictedNode (editedSource , tinyWitness , tinyWitness)
... | ()

soundLocalityDoesNotByItselfProvePrecision :
  ClosureSound tinyClosure tinyChanged ×
  (ClosureExact tinyClosure tinyChanged → ⊥)
soundLocalityDoesNotByItselfProvePrecision =
  tinyClosureIsSound , tinyClosureIsNotExact

------------------------------------------------------------------------
-- Revision composition and edit-set monotonicity regressions.
------------------------------------------------------------------------

shiftOne : EditTransport
shiftOne = editTransport (λ coordinate → suc coordinate)

shiftTwo : EditTransport
shiftTwo = editTransport (λ coordinate → suc (suc coordinate))

composedShiftExample :
  transportCoordinate (composeEditTransport shiftOne shiftTwo) 5 ≡ 8
composedShiftExample = refl

identityCompositionExample :
  transportCoordinate (composeEditTransport identityEditTransport shiftOne) 5 ≡ 6
identityCompositionExample = refl

data SmallEditSource : Set where
  firstSource secondSource : SmallEditSource

data SmallEditLeaf : Set where
  firstLeaf secondLeaf : SmallEditLeaf

smallEdited : SmallEditSource → Set
smallEdited firstSource = TinyWitness
smallEdited secondSource = ⊥

largeEdited : SmallEditSource → Set
largeEdited firstSource = TinyWitness
largeEdited secondSource = TinyWitness

sharedReachability : SmallEditSource → SmallEditLeaf → Set
sharedReachability firstSource firstLeaf = TinyWitness
sharedReachability firstSource secondLeaf = ⊥
sharedReachability secondSource firstLeaf = ⊥
sharedReachability secondSource secondLeaf = TinyWitness

smallEditClosure : EditedDependencyClosure SmallEditSource SmallEditLeaf
smallEditClosure = editedDependencyClosure smallEdited sharedReachability

largeEditClosure : EditedDependencyClosure SmallEditSource SmallEditLeaf
largeEditClosure = editedDependencyClosure largeEdited sharedReachability

smallEditedSubsetLarge :
  (source : SmallEditSource) → smallEdited source → largeEdited source
smallEditedSubsetLarge firstSource tinyWitness = tinyWitness
smallEditedSubsetLarge secondSource ()

reachabilityPreserved :
  (source : SmallEditSource) → (leaf : SmallEditLeaf) →
  sharedReachability source leaf → sharedReachability source leaf
reachabilityPreserved source leaf witness = witness

largerEditCannotLosePredictedLeaf : ClosureSubset smallEditClosure largeEditClosure
largerEditCannotLosePredictedLeaf =
  closureMonotoneUnderEditedAndReachability
    smallEditedSubsetLarge
    reachabilityPreserved
