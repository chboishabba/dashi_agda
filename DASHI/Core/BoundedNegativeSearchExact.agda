module DASHI.Core.BoundedNegativeSearchExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- BOUNDED NEGATIVE SEARCH
--
-- A failed search is informative about the carrier that was actually searched.
-- It is not, by itself, a proof that no matching candidate exists globally.
-- Promotion to global absence requires an independent coverage witness saying
-- that every candidate in the declared universe lies inside the searched scope.
--
-- This is intentionally proof-valued rather than a Boolean search status.
------------------------------------------------------------------------

record BoundedNegativeSearch
    {Candidate : Set}
    (InScope : Candidate → Set)
    (Matches : Candidate → Set) : Set₁ where
  constructor bounded-negative-search
  field
    noMatchInScope :
      (candidate : Candidate) →
      InScope candidate →
      Matches candidate →
      ⊥
open BoundedNegativeSearch public

record SearchCoverage
    {Candidate : Set}
    (InScope : Candidate → Set) : Set₁ where
  constructor search-coverage
  field
    coversCandidate : (candidate : Candidate) → InScope candidate
open SearchCoverage public

boundedNegativeSearchWithCoverageProvesGlobalAbsence :
  ∀ {Candidate : Set}
    {InScope Matches : Candidate → Set} →
  BoundedNegativeSearch InScope Matches →
  SearchCoverage InScope →
  (candidate : Candidate) →
  Matches candidate →
  ⊥
boundedNegativeSearchWithCoverageProvesGlobalAbsence search coverage candidate match =
  noMatchInScope search candidate (coversCandidate coverage candidate) match

------------------------------------------------------------------------
-- Boundary: the no-match receipt and the universe-coverage receipt are distinct
-- obligations.  Domain-specific search metadata (query, date, repository,
-- register, accession, trial, etc.) remains downstream provenance.
------------------------------------------------------------------------

record BoundedNegativeSearchBoundary : Set where
  constructor bounded-negative-search-boundary
  field
    noMatchInsideDeclaredScopeIsInformation : Bool
    noMatchInsideDeclaredScopeIsInformationIsTrue :
      noMatchInsideDeclaredScopeIsInformation ≡ true

    globalAbsenceRequiresCoverage : Bool
    globalAbsenceRequiresCoverageIsTrue :
      globalAbsenceRequiresCoverage ≡ true

    searchNonLocationAloneCreatesGlobalAbsence : Bool
    searchNonLocationAloneCreatesGlobalAbsenceIsFalse :
      searchNonLocationAloneCreatesGlobalAbsence ≡ false

    broaderSearchMetadataCreatesSameObjectIdentity : Bool
    broaderSearchMetadataCreatesSameObjectIdentityIsFalse :
      broaderSearchMetadataCreatesSameObjectIdentity ≡ false

canonicalBoundedNegativeSearchBoundary : BoundedNegativeSearchBoundary
canonicalBoundedNegativeSearchBoundary =
  bounded-negative-search-boundary
    true refl
    true refl
    false refl
    false refl
