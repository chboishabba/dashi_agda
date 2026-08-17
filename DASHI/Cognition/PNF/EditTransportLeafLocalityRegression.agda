module DASHI.Cognition.PNF.EditTransportLeafLocalityRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.List.Base using ([]; _∷_)
open import Data.Product using (_×_; _,_)

open import DASHI.Cognition.PNF.EditTransportLeafLocalityExact

------------------------------------------------------------------------
-- Same transported occurrence, changed semantic value.
------------------------------------------------------------------------

identityTransport : EditTransport
identityTransport = editTransport (λ coordinate → coordinate)

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

------------------------------------------------------------------------
-- Two structurally indistinguishable target leaves block verified unique
-- correspondence.  The audit must remain indeterminate rather than guessing.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Sound reverse-dependency closure need not be precise/minimal.
------------------------------------------------------------------------

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
