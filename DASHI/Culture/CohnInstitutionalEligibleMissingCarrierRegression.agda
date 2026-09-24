module DASHI.Culture.CohnInstitutionalEligibleMissingCarrierRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Culture.CohnInstitutionalEligibleMissingCarrierExact as Carrier

realisedCarrierCannotRecoverMissingProfile :
  Carrier.realisedCarrierDeterminesMissingPopulation
    Carrier.canonicalEligibleMissingBoundary ≡ false
realisedCarrierCannotRecoverMissingProfile = refl

threeMissingnessMechanismsRetained :
  Carrier.nonDisclosureResponseConsentCollapsed
    Carrier.canonicalEligibleMissingBoundary ≡ false
threeMissingnessMechanismsRetained = refl

sourceAcquisitionDoesNotCreateWorldFact :
  Carrier.sourceAcquisitionCreatesCarrierObservation
    Carrier.canonicalEligibleMissingBoundary ≡ false
sourceAcquisitionDoesNotCreateWorldFact = refl

eligibilityStillDistinctFromRealisation :
  Carrier.eligiblePopulationEqualsRealisedCarrier
    Carrier.canonicalEligibleMissingBoundary ≡ false
eligibilityStillDistinctFromRealisation = refl

proofSearchMayQueryMissingPopulation :
  Carrier.missingPopulationIsConsumerRelevant
    Carrier.canonicalEligibleMissingBoundary ≡ true
proofSearchMayQueryMissingPopulation = refl
