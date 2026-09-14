module DASHI.Interop.OSINTBoundedNegativeSearchAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.BoundedNegativeSearchExact as Negative
import DASHI.Core.SnowballOSINTAcquisitionInvariantExact as OSINT

------------------------------------------------------------------------
-- OSINT qualitative firewall -> proof-valued bounded negative search.
--
-- The older OSINT core already proves that search non-location does not itself
-- create known absence.  The bounded-negative-search spine is a strict
-- refinement: it retains that firewall and adds the constructive condition
-- under which a global-absence conclusion *is* licensed, namely an explicit
-- coverage witness for the declared candidate universe.
------------------------------------------------------------------------

osintSearchFailureDoesNotCreateKnownAbsence :
  OSINT.SearchNonLocationMeansKnownAbsence → ⊥
osintSearchFailureDoesNotCreateKnownAbsence =
  OSINT.searchFailureDoesNotCreateKnownAbsence

coveredBoundedSearchProvesGlobalAbsence :
  ∀ {Candidate : Set}
    {InScope Matches : Candidate → Set} →
  Negative.BoundedNegativeSearch InScope Matches →
  Negative.SearchCoverage InScope →
  (candidate : Candidate) →
  Matches candidate →
  ⊥
coveredBoundedSearchProvesGlobalAbsence =
  Negative.boundedNegativeSearchWithCoverageProvesGlobalAbsence

osintObservationAloneSuppliesUniverseCoverage : Bool
osintObservationAloneSuppliesUniverseCoverage = false

coverageIsAdditionalPromotionPayment : Bool
coverageIsAdditionalPromotionPayment = true

osintObservationAloneSuppliesUniverseCoverageIsFalse :
  osintObservationAloneSuppliesUniverseCoverage ≡ false
osintObservationAloneSuppliesUniverseCoverageIsFalse = refl

coverageIsAdditionalPromotionPaymentIsTrue :
  coverageIsAdditionalPromotionPayment ≡ true
coverageIsAdditionalPromotionPaymentIsTrue = refl

record OSINTNegativeSearchRefinementBoundary : Set where
  constructor osint-negative-search-refinement-boundary
  field
    historicalOSINTFirewallRetained : Bool
    historicalOSINTFirewallRetainedIsTrue :
      historicalOSINTFirewallRetained ≡ true
    boundedSearchAddsProofValuedScope : Bool
    boundedSearchAddsProofValuedScopeIsTrue :
      boundedSearchAddsProofValuedScope ≡ true
    coverageAddsConstructivePromotionRoute : Bool
    coverageAddsConstructivePromotionRouteIsTrue :
      coverageAddsConstructivePromotionRoute ≡ true
    osintObservationAutomaticallyPaysCoverage : Bool
    osintObservationAutomaticallyPaysCoverageIsFalse :
      osintObservationAutomaticallyPaysCoverage ≡ false
    refinementReplacesSourceIdentityDiscipline : Bool
    refinementReplacesSourceIdentityDisciplineIsFalse :
      refinementReplacesSourceIdentityDiscipline ≡ false

canonicalOSINTNegativeSearchRefinementBoundary :
  OSINTNegativeSearchRefinementBoundary
canonicalOSINTNegativeSearchRefinementBoundary =
  osint-negative-search-refinement-boundary
    true refl
    true refl
    true refl
    false refl
    false refl
