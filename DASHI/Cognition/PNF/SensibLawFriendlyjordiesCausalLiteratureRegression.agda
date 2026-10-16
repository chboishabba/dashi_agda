module DASHI.Cognition.PNF.SensibLawFriendlyjordiesCausalLiteratureRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Cognition.PNF.SensibLawFriendlyjordiesCausalLiteratureAcquisitionExact as Literature

syntheticControlCandidatePresent :
  Literature.australiaSyntheticControlCandidatePresent ≡ true
syntheticControlCandidatePresent = refl

southAustraliaCaseStudyCandidatePresent :
  Literature.southAustraliaCaseStudyCandidatePresent ≡ true
southAustraliaCaseStudyCandidatePresent = refl

carbonPriceAttributionCandidatePresent :
  Literature.carbonPriceAttributionCandidatePresent ≡ true
carbonPriceAttributionCandidatePresent = refl

exactPartyCausalIdentificationPaid :
  Literature.exactPartyCausalIdentificationPaid ≡ false
exactPartyCausalIdentificationPaid = refl

literatureCreatesUniversalPartyRanking :
  Literature.causalLiteratureCreatesUniversalPartyRanking ≡ false
literatureCreatesUniversalPartyRanking = refl
