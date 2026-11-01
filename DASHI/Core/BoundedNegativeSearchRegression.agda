module DASHI.Core.BoundedNegativeSearchRegression where

open import DASHI.Core.Prelude

import DASHI.Core.BoundedNegativeSearchExact as Search

------------------------------------------------------------------------
-- RED regression: a bounded search can establish no match inside its searched
-- carrier while a matching candidate remains outside that carrier.  Global
-- absence is therefore available only after a separate coverage witness.
------------------------------------------------------------------------

data Candidate : Set where
  searchedCandidate outsideCandidate : Candidate

data InScope : Candidate → Set where
  searchedWasChecked : InScope searchedCandidate

data Matches : Candidate → Set where
  outsideActuallyMatches : Matches outsideCandidate

boundedSearch : Search.BoundedNegativeSearch InScope Matches
boundedSearch = Search.bounded-negative-search (λ
  { searchedCandidate searchedWasChecked ()
  ; outsideCandidate ()
  })

outsideNotInScope : InScope outsideCandidate → ⊥
outsideNotInScope ()

coverageImpossible : Search.SearchCoverage InScope → ⊥
coverageImpossible coverage =
  outsideNotInScope (Search.coversCandidate coverage outsideCandidate)

------------------------------------------------------------------------
-- Positive fixture: once every candidate is proved to lie in the searched
-- carrier, the same bounded no-match receipt may be promoted to global absence
-- for the declared predicate.
------------------------------------------------------------------------

data CompleteCandidate : Set where onlyCandidate : CompleteCandidate

data CompleteScope : CompleteCandidate → Set where
  onlyCandidateChecked : CompleteScope onlyCandidate

data CompleteMatch : CompleteCandidate → Set where

completeSearch : Search.BoundedNegativeSearch CompleteScope CompleteMatch
completeSearch = Search.bounded-negative-search (λ onlyCandidate onlyCandidateChecked ())

completeCoverage : Search.SearchCoverage CompleteScope
completeCoverage = Search.search-coverage (λ onlyCandidate → onlyCandidateChecked)

globalAbsencePaid :
  (candidate : CompleteCandidate) → CompleteMatch candidate → ⊥
globalAbsencePaid =
  Search.boundedNegativeSearchWithCoverageProvesGlobalAbsence
    completeSearch completeCoverage
