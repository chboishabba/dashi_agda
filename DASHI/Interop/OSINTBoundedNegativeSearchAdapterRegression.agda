module DASHI.Interop.OSINTBoundedNegativeSearchAdapterRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.BoundedNegativeSearchExact as Negative
import DASHI.Core.SnowballOSINTAcquisitionInvariantExact as OSINT
import DASHI.Interop.OSINTBoundedNegativeSearchAdapterExact as Adapter

-- The historical OSINT firewall remains the parent negative theorem.
parentSearchFailureFirewallRetained :
  OSINT.SearchNonLocationMeansKnownAbsence → ⊥
parentSearchFailureFirewallRetained =
  Adapter.osintSearchFailureDoesNotCreateKnownAbsence

-- The refinement adds the constructive promotion route when coverage is paid.
data Candidate : Set where
  onlyCandidate : Candidate

data InScope : Candidate → Set where
  onlyCandidateInScope : InScope onlyCandidate

data Matches : Candidate → Set where

boundedSearch : Negative.BoundedNegativeSearch InScope Matches
boundedSearch = Negative.bounded-negative-search (λ candidate inScope match → case match of λ ())

coverage : Negative.SearchCoverage InScope
coverage = Negative.search-coverage (λ { onlyCandidate → onlyCandidateInScope })

coveredSearchProvesAbsence :
  (candidate : Candidate) → Matches candidate → ⊥
coveredSearchProvesAbsence =
  Adapter.coveredBoundedSearchProvesGlobalAbsence boundedSearch coverage

osintObservationDoesNotSupplyCoverage :
  Adapter.osintObservationAloneSuppliesUniverseCoverage ≡ false
osintObservationDoesNotSupplyCoverage = refl

coverageIsAdditionalPayment :
  Adapter.coverageIsAdditionalPromotionPayment ≡ true
coverageIsAdditionalPayment = refl
