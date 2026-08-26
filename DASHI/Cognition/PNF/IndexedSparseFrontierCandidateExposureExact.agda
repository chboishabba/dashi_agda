module DASHI.Cognition.PNF.IndexedSparseFrontierCandidateExposureExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_; zero; suc)

------------------------------------------------------------------------
-- Sparse-frontier state is not enough: transition work must also avoid the
-- demand × candidate-carrier Cartesian product.
--
-- Runtime correspondence (SensibLaw migration 062): parent frontiers already
-- retain a bounded/exported boundary, but object-candidate generation can still
-- join every unresolved parent demand against every actor profile and filter
-- afterwards.  The exact replacement is constraint-indexed intersection:
-- each demand exposes its required key fibre; each actor profile exposes the
-- keys it satisfies; a candidate is admitted iff every required demand key is
-- witnessed by that profile.  This changes physical exposure, not authority.
------------------------------------------------------------------------

record CandidateAuthority (Demand Profile : Set) : Set₁ where
  field
    candidateWise : Demand → Profile → Set
    indexedIntersection : Demand → Profile → Set
    exact :
      ∀ demand profile →
      candidateWise demand profile ≡ indexedIntersection demand profile

open CandidateAuthority public

record ExposureReceipt : Set where
  constructor exposureReceipt
  field
    demandCount : Nat
    profileCount : Nat
    demandConstraintCount : Nat
    profileKeyCount : Nat
    matchedKeyCount : Nat
    candidateCount : Nat
    cartesianExposure : Nat
    indexedExposure : Nat

open ExposureReceipt public

-- The old physical realization must at least expose the full demand/profile
-- product before its predicates can reject pairs.
candidateWiseReceipt :
  (demands profiles constraints keys candidates : Nat) → ExposureReceipt
candidateWiseReceipt demands profiles constraints keys candidates =
  exposureReceipt
    demands profiles constraints keys zero candidates
    (demands * profiles)
    (demands * profiles)

-- The indexed realization charges construction of both sparse key carriers plus
-- only actual matched-key pairs.  It does not claim a universal asymptotic
-- theorem about PostgreSQL; it records the work surface the runtime is required
-- to realize if it is to call itself constraint-indexed.
indexedReceipt :
  (demands profiles constraints keys matches candidates : Nat) → ExposureReceipt
indexedReceipt demands profiles constraints keys matches candidates =
  exposureReceipt
    demands profiles constraints keys matches candidates
    (demands * profiles)
    (constraints + keys + matches)

record ExactIndexedSparseFrontierReduction
  (Demand Profile : Set) : Set₁ where
  field
    authority : CandidateAuthority Demand Profile
    legacyReceipt : ExposureReceipt
    indexedReceiptWitness : ExposureReceipt

    sameDemandPopulation :
      demandCount legacyReceipt ≡ demandCount indexedReceiptWitness
    sameProfilePopulation :
      profileCount legacyReceipt ≡ profileCount indexedReceiptWitness
    sameCandidateAuthorityCount :
      candidateCount legacyReceipt ≡ candidateCount indexedReceiptWitness

open ExactIndexedSparseFrontierReduction public

-- Consumer observations cannot distinguish candidate-wise from indexed
-- realization when the pointwise candidate relation is exact.
sameCandidateRelation :
  ∀ {Demand Profile : Set}
    (reduction : ExactIndexedSparseFrontierReduction Demand Profile)
    (demand : Demand)
    (profile : Profile) →
  candidateWise (authority reduction) demand profile
    ≡ indexedIntersection (authority reduction) demand profile
sameCandidateRelation reduction demand profile =
  exact (authority reduction) demand profile

------------------------------------------------------------------------
-- Conjunctive key semantics.
------------------------------------------------------------------------

record RequiredKeyFamily : Set where
  constructor requiredKeyFamily
  field
    requiredKeyCount : Nat

open RequiredKeyFamily public

record ProfileKeyFamily : Set where
  constructor profileKeyFamily
  field
    availableKeyCount : Nat

open ProfileKeyFamily public

record KeyIntersectionWitness
  (required : RequiredKeyFamily)
  (profile : ProfileKeyFamily) : Set where
  constructor keyIntersectionWitness
  field
    matchedRequiredKeyCount : Nat
    allRequiredKeysMatched :
      matchedRequiredKeyCount ≡ requiredKeyCount required

open KeyIntersectionWitness public

-- A zero-constraint demand is intentionally not rejected.  Its required-key
-- family is empty, so exact indexed execution must preserve its broad/wildcard
-- semantics rather than pretending absence of constraints is negative evidence.
emptyRequiredKeysAreSatisfied :
  (profile : ProfileKeyFamily) →
  KeyIntersectionWitness (requiredKeyFamily zero) profile
emptyRequiredKeysAreSatisfied profile =
  keyIntersectionWitness zero refl

------------------------------------------------------------------------
-- Complexity boundary.
--
-- State sparsity and transition sparsity are separate certificates.  A parent
-- frontier may be reductive in cardinality while its construction still has
-- cartesian exposure.  This record is the missing execution-side obligation.
------------------------------------------------------------------------

record SparseFrontierTransitionCertificate : Set where
  constructor sparseFrontierTransitionCertificate
  field
    retainedBoundaryCount : Nat
    unresolvedDemandCount : Nat
    actorProfileCount : Nat
    requiredConstraintCount : Nat
    actorProfileKeyCount : Nat
    matchedConstraintPairs : Nat
    retainedCandidateCount : Nat
    physicalExposure : Nat

    -- The certified indexed implementation must report its work in the sparse
    -- key/match carrier, not silently charge the entire demand × profile fibre.
    exposureFactorsThroughIndexedCarrier :
      physicalExposure
        ≡ requiredConstraintCount + actorProfileKeyCount + matchedConstraintPairs

open SparseFrontierTransitionCertificate public

canonicalEmptyTransitionCertificate : SparseFrontierTransitionCertificate
canonicalEmptyTransitionCertificate =
  sparseFrontierTransitionCertificate
    zero zero zero zero zero zero zero zero refl
