module DASHI.Law.IsraeliDomesticSettlementLegalitySearchReceiptRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Law.IsraeliDomesticSettlementLegalitySearchReceiptExact as Domestic

parentInternationalFixtureReusedRegression :
  Domestic.parentIsraelOperationalLegalityReused
    Domestic.canonicalIsraeliDomesticSettlementSearchBoundary
  ≡ true
parentInternationalFixtureReusedRegression = refl

illegalOutpostLanguageLocatedRegression :
  Domestic.officialKnessetIllegalOutpostLanguageLocated
    Domestic.canonicalIsraeliDomesticSettlementSearchBoundary
  ≡ true
illegalOutpostLanguageLocatedRegression = refl

regularisationProposalLocatedRegression :
  Domestic.knessetRegularisationProposalLocated
    Domestic.canonicalIsraeliDomesticSettlementSearchBoundary
  ≡ true
regularisationProposalLocatedRegression = refl

governmentLegalPositionLocatedRegression :
  Domestic.officialGovernmentOsloAreaCPositionLocated
    Domestic.canonicalIsraeliDomesticSettlementSearchBoundary
  ≡ true
governmentLegalPositionLocatedRegression = refl

comprehensiveDomesticLegalityPaidRegression :
  Domestic.comprehensiveDomesticSettlementLegalityPaid
    Domestic.canonicalIsraeliDomesticSettlementSearchBoundary
  ≡ false
comprehensiveDomesticLegalityPaidRegression = refl

proposalAutomaticallyCurrentLawRegression :
  Domestic.legislativeProposalAutomaticallyCurrentLaw
    Domestic.canonicalIsraeliDomesticSettlementSearchBoundary
  ≡ false
proposalAutomaticallyCurrentLawRegression = refl

committeeLanguageJudicialHoldingRegression :
  Domestic.knessetCommitteeLanguageAutomaticallyJudicialHolding
    Domestic.canonicalIsraeliDomesticSettlementSearchBoundary
  ≡ false
committeeLanguageJudicialHoldingRegression = refl

governmentPositionIndependentAdjudicationRegression :
  Domestic.governmentLegalPositionAutomaticallyIndependentAdjudication
    Domestic.canonicalIsraeliDomesticSettlementSearchBoundary
  ≡ false
governmentPositionIndependentAdjudicationRegression = refl

allSettlerActionsDomesticLawfulRegression :
  Domestic.everySettlerActionAutomaticallyDomesticLawful
    Domestic.canonicalIsraeliDomesticSettlementSearchBoundary
  ≡ false
allSettlerActionsDomesticLawfulRegression = refl
