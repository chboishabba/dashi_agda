module DASHI.Cognition.PNF.SensibLawCountryUniversalLegalAlgebraEverything where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawCountrySystemRealisedJusticeEverything as Country
import DASHI.Cognition.PNF.SensibLawCountrySystemRealisedJusticeBidiExact as System
import DASHI.Cognition.PNF.SensibLawRemedyUniversalLegalAlgebraBridgeExact as Bridge
import DASHI.Cognition.PNF.SensibLawUniversalLegalAlgebraEverything as Universal

------------------------------------------------------------------------
-- Legal derivability and operational realisation are sequential consumers.
------------------------------------------------------------------------

legalAvailabilityStillDoesNotEqualRealisation :
  Bridge.LegalAvailabilityAutomaticallyMeansRealisedRemedy → ⊥
legalAvailabilityStillDoesNotEqualRealisation = Bridge.availabilityDoesNotEqualRealisation

executionFailureDoesNotRewriteLegalAuthorityByDefault :
  Bridge.ExecutionFailureRefutesUnderlyingLegalRule → ⊥
executionFailureDoesNotRewriteLegalAuthorityByDefault =
  Bridge.executionFailureDoesNotAutomaticallyRefuteLaw

communityOutcomeFailureReopensCommunityEvidence :
  Bridge.reopenCommunityOutcomeEvidence Bridge.communityOutcomeFailureReopen ≡ true
communityOutcomeFailureReopensCommunityEvidence = refl

communityOutcomeFailureDoesNotReopenLegalGraphByDefault :
  Bridge.reopenLegalRuleGraph Bridge.communityOutcomeFailureReopen ≡ false
communityOutcomeFailureDoesNotReopenLegalGraphByDefault = refl

legalAuthorityFailureDoesReopenUniversalGraph :
  Bridge.reopenLegalRuleGraph Bridge.legalAuthorityFailureReopen ≡ true
legalAuthorityFailureDoesReopenUniversalGraph = refl

------------------------------------------------------------------------
-- Existing Country operational frontier remains unchanged by importing legal
-- derivation machinery; the two layers communicate through typed reopen routes.
------------------------------------------------------------------------

countryCompensationResidualStillOpen :
  Country.compensationState ≡ System.residualOpen
countryCompensationResidualStillOpen = refl

------------------------------------------------------------------------
-- Aggregate boundary.
------------------------------------------------------------------------

data CrossPollinationMeansAllRemediesLegallyAvailable : Set where
crossPollinationDoesNotCreateRemedyAuthority :
  CrossPollinationMeansAllRemediesLegallyAvailable → ⊥
crossPollinationDoesNotCreateRemedyAuthority ()
