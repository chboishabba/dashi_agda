{-# OPTIONS --safe #-}
module DASHI.Interop.JMDFormalWorldReconciliationExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Agda is golden. External QIDs, OEIS references, byte hashes, lexical
-- candidates and successful Python runs are NOT proofs of a proposition.
-- The only way to construct a certified transport below is to give
-- an actual Agda term of the corresponding function type.
------------------------------------------------------------------------

data LinkAuthority : Set where
  candidateOnly : LinkAuthority
  kernelWitness : LinkAuthority

candidateIsNotKernelWitness : candidateOnly ≡ kernelWitness → ⊥
candidateIsNotKernelWitness ()

record SourceIdentity : Set where
  constructor source-identity
  field
    repository : String
    sourceRevision : String
    declaration : String
    attribution : String

open SourceIdentity public

record CandidateLink : Set where
  constructor candidate-link
  field
    source : SourceIdentity
    target : SourceIdentity
    relationshipHint : String
    qidOrOeisCoordinate : String
    status : LinkAuthority
    statusIsOnlyCandidate : status ≡ candidateOnly

open CandidateLink public

-- Certificate = proof term, not a Boolean or a hash.
record CertifiedImplication (A B : Set) : Set where
  constructor certified-implication
  field
    sourceIdentity : SourceIdentity
    targetIdentity : SourceIdentity
    applyProof : A → B

open CertifiedImplication public

record CertifiedEquivalence (A B : Set) : Set where
  constructor certified-equivalence
  field
    leftSource : SourceIdentity
    rightSource : SourceIdentity
    forward : A → B
    backward : B → A

open CertifiedEquivalence public

reflTransport :
  {A : Set} →
  (origin : SourceIdentity) →
  CertifiedImplication A A
reflTransport origin = certified-implication origin origin (λ a → a)

composeVerifiedImplication :
  {A B C : Set} →
  CertifiedImplication A B →
  CertifiedImplication B C →
  CertifiedImplication A C
composeVerifiedImplication left right =
  certified-implication
    (sourceIdentity left)
    (targetIdentity right)
    (λ a → applyProof right (applyProof left a))

equivalenceToForward :
  {A B : Set} →
  CertifiedEquivalence A B →
  CertifiedImplication A B
equivalenceToForward e =
  certified-implication (leftSource e) (rightSource e) (forward e)

equivalenceToBackward :
  {A B : Set} →
  CertifiedEquivalence A B →
  CertifiedImplication B A
equivalenceToBackward e =
  certified-implication (rightSource e) (leftSource e) (backward e)

-- Worlding retains BOTH witnesses; equivalence never deletes provenance.
record WorldedPair (A B : Set) : Set where
  constructor worlded-pair
  field
    originalLeft : SourceIdentity
    originalRight : SourceIdentity
    proofEquivalence : CertifiedEquivalence A B
    leftIdentityPreserved : originalLeft ≡ leftSource proofEquivalence
    rightIdentityPreserved : originalRight ≡ rightSource proofEquivalence

open WorldedPair public

worldPair :
  {A B : Set} →
  (cert : CertifiedEquivalence A B) →
  WorldedPair A B
worldPair cert =
  worlded-pair (leftSource cert) (rightSource cert) cert refl refl

worldPairRetainsLeft :
  {A B : Set} →
  (cert : CertifiedEquivalence A B) →
  originalLeft (worldPair cert) ≡ leftSource cert
worldPairRetainsLeft cert = refl

worldPairRetainsRight :
  {A B : Set} →
  (cert : CertifiedEquivalence A B) →
  originalRight (worldPair cert) ≡ rightSource cert
worldPairRetainsRight cert = refl

-- Even a verified link creates no new claim until the required inhabitant
-- is actually supplied. This is the native proof-debt firewall.
dischargeWithCertifiedImplication :
  {A B : Set} →
  CertifiedImplication A B → A → B
dischargeWithCertifiedImplication relation = applyProof relation

candidateCanOnlyRemainCandidate :
  (link : CandidateLink) → status link ≡ candidateOnly
candidateCanOnlyRemainCandidate = statusIsOnlyCandidate

-- Generic negative control: the two authority constructors cannot collide.
candidateCannotBePromotedByStatusEquality :
  (link : CandidateLink) → status link ≡ kernelWitness → ⊥
candidateCannotBePromotedByStatusEquality link impossible =
  candidateIsNotKernelWitness
    (trans (sym (statusIsOnlyCandidate link)) impossible)
  where
    sym : {X : Set} {x y : X} → x ≡ y → y ≡ x
    sym refl = refl

    trans : {X : Set} {x y z : X} → x ≡ y → y ≡ z → x ≡ z
    trans refl refl = refl
