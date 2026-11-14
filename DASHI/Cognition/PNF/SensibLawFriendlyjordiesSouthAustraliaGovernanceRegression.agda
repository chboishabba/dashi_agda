module DASHI.Cognition.PNF.SensibLawFriendlyjordiesSouthAustraliaGovernanceRegression where

------------------------------------------------------------------------
-- RED/GREEN regression surface for the South-Australia/governance max-cut.
--
-- This module is intentionally tiny: it imports the application owner and
-- demands the exact boundaries that distinguish source acquisition from world
-- truth and source-paid CPRS transitions from source-pending SA transitions.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Cognition.PNF.SensibLawFriendlyjordiesSouthAustraliaGovernanceWeldExact as Weld

southAustraliaIsNamedInMarchCase :
  Weld.southAustraliaNamedCase ≡ true
southAustraliaIsNamedInMarchCase = refl

southAustraliaPinnedFixturePaid :
  Weld.southAustraliaPinnedFixturePaid ≡ false
southAustraliaPinnedFixturePaid = refl

southAustraliaHasAcquisitionRoute :
  Weld.southAustraliaAcquisitionRoutePresent ≡ true
southAustraliaHasAcquisitionRoute = refl

cprsHasSourcePaidTransition :
  Weld.cprsSourcePaidTransitionPresent ≡ true
cprsHasSourcePaidTransition = refl

southAustraliaTransitionRequiresSourcePayment :
  Weld.southAustraliaTransitionBlockedBySourcePayment ≡ true
southAustraliaTransitionRequiresSourcePayment = refl

worldEvidenceCannotBeManufacturedByTransition :
  Weld.transitionCreatesWorldTruth ≡ false
worldEvidenceCannotBeManufacturedByTransition = refl

trajectoryComparisonCannotCreatePartyRanking :
  Weld.trajectoryCreatesUniversalPartyRanking ≡ false
trajectoryComparisonCannotCreatePartyRanking = refl
