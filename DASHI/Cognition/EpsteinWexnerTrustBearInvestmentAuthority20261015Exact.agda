module DASHI.Cognition.EpsteinWexnerTrustBearInvestmentAuthority20261015Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinWexnerChildrenTrustCapitalMesh20261015Exact as TrustMesh
import DASHI.Cognition.EpsteinFinancialTrustBearCrisisAwarenessSettlement20261014Exact as Bear

------------------------------------------------------------------------
-- WEXNER CHILDREN'S TRUST II / EPSTEIN TRUSTEE / BEAR INVESTMENT AUTHORITY
-- 2026-10-15
--
-- Source discipline:
--   * investment amounts and trustee capacity below are statements made by
--     Bear Stearns respondents in their FINRA Statement of Answer;
--   * the discovery request independently identifies investments made by
--     claimants on behalf of / as trustee for Wexner Children's Trust II as a
--     document-production subject;
--   * a JPM-produced 25 Feb 1998 trust agreement is separately indexed in the
--     released corpus as naming Leslie Wexner grantor and Jeffrey Epstein
--     trustee, but this owner does not silently upgrade an index locator into
--     a fully inspected governing-instrument receipt.
------------------------------------------------------------------------

data AuthoritySourceClass : Set where
  adversarialRespondentPleading : AuthoritySourceClass
  adversarialDiscoveryRequest : AuthoritySourceClass
  releasedTrustInstrumentLocator : AuthoritySourceClass
  executedSubscriptionOrWire : AuthoritySourceClass

record TrusteeInvestmentReceipt : Set where
  constructor trustee-investment-receipt
  field
    label : String
    sourceClass : AuthoritySourceClass
    source : String
    boundedFinding : String
    amountUSD : Nat
    trusteeCapacityAsserted : Bool
    neutralTransactionRecordPaid : Bool
open TrusteeInvestmentReceipt public

wctIIABS2006 : TrusteeInvestmentReceipt
wctIIABS2006 = trustee-investment-receipt
  "Wexner Children's Trust II additional ABS investment"
  adversarialRespondentPleading
  "EFTA00294815..EFTA00294822 — Bear Stearns Respondents' FINRA Statement of Answer"
  "Bear respondents state that, simultaneously with FTC's additional ABS investment in about November 2006, Epstein, in his capacity as trustee of The Wexner Children's Trust II, invested an additional USD20m in the Bear Stearns ABS Fund. This pays the existence of a specific respondent assertion and its amount/capacity; it is not yet promoted to a neutral bank/subscription receipt in this owner."
  20000000 true false

wctEuropeLongShort2007 : TrusteeInvestmentReceipt
wctEuropeLongShort2007 = trustee-investment-receipt
  "Wexner children's trust Europe Long/Short investment"
  adversarialRespondentPleading
  "EFTA00294821 — Bear Stearns Respondents' FINRA Statement of Answer"
  "Bear respondents state that, at the same time as Epstein's personal April 2007 USD10m Europe Long/Short investment, Epstein in trustee capacity for the Wexner children's trust invested USD10m in the same fund. The pleading text pays the attributed assertion but not an independently inspected subscription/wire record."
  10000000 true false

wctIIDiscoverySubject : TrusteeInvestmentReceipt
wctIIDiscoverySubject = trustee-investment-receipt
  "Bear discovery request names Wexner Children's Trust II trustee investments"
  adversarialDiscoveryRequest
  "EFTA00724436..EFTA00724443 — Bear Stearns Respondents' First Request for Production"
  "Requests 6 and 7 demand all documents concerning investments by claimants in the disputed funds and any Bear Stearns fund on behalf of or as trustee for third parties, expressly including Wexner Children's Trust II. This corroborates that trustee-managed third-party investment activity was a concrete litigation subject, while a discovery request is not itself proof of each underlying transaction."
  0 true false

wctIITrustInstrumentLocator : TrusteeInvestmentReceipt
wctIITrustInstrumentLocator = trustee-investment-receipt
  "25 February 1998 Wexner Children's Trust II agreement locator"
  releasedTrustInstrumentLocator
  "EFTA01481286 / JPM-SDNY-00002596; execution/notary/schedule pages indexed as EFTA01480437..439"
  "The released-corpus index identifies a JPM-produced Wexner Children's Trust II agreement dated 25 February 1998, with Leslie Wexner as grantor and Jeffrey Epstein as trustee. The exact instrument pages are acquisition targets for direct inspection before this owner relies on governing powers, asset schedules or amendment terms."
  0 true false

record TrusteeAuthorityBoundary : Set where
  constructor trustee-authority-boundary
  field
    respondentPleadingTrusteeCapacityPaid : Bool
    respondentPleadingABSAmountPaid : Bool
    respondentPleadingEuropeFundAmountPaid : Bool
    discoveryRequestTrusteeInvestmentSurfacePaid : Bool
    trustInstrumentLocatorPaid : Bool
    governingTrustTermsDirectlyInspected : Bool
    neutralABSSubscriptionOrWirePaid : Bool
    neutralEuropeSubscriptionOrWirePaid : Bool
    trusteeRoleImpliesBeneficialOwnership : Bool
    trusteeInvestmentImpliesWexnerPersonalDirection : Bool
    litigationAssertionImpliesAdjudicatedFact : Bool
open TrusteeAuthorityBoundary public

canonicalTrusteeAuthorityBoundary : TrusteeAuthorityBoundary
canonicalTrusteeAuthorityBoundary = trustee-authority-boundary
  true true true true true false false false false false false

data TrusteeImpliesBeneficialOwnership : Set where
data TrusteeInvestmentImpliesGrantorDirection : Set where
data RespondentPleadingImpliesAdjudicatedFact : Set where

trusteeDoesNotCreateBeneficialOwnership : TrusteeImpliesBeneficialOwnership → ⊥
trusteeDoesNotCreateBeneficialOwnership ()

trusteeInvestmentDoesNotCreateGrantorDirection : TrusteeInvestmentImpliesGrantorDirection → ⊥
trusteeInvestmentDoesNotCreateGrantorDirection ()

pleadingDoesNotCreateAdjudicatedFact : RespondentPleadingImpliesAdjudicatedFact → ⊥
pleadingDoesNotCreateAdjudicatedFact ()

------------------------------------------------------------------------
-- Max-cut: transaction and governing-authority payment.
------------------------------------------------------------------------

data TrusteeAuthorityDebt : Set where
  inspect1998TrustAgreement : TrusteeAuthorityDebt
  trustAmendmentsAndRemoval : TrusteeAuthorityDebt
  absSubscriptionAndWire : TrusteeAuthorityDebt
  europeSubscriptionAndWire : TrusteeAuthorityDebt
  investmentDecisionCommunications : TrusteeAuthorityDebt
  trustCapitalAndBeneficiaryAccounts : TrusteeAuthorityDebt

record TrusteeAuthorityAcquisition : Set where
  constructor trustee-authority-acquisition
  field
    debt : TrusteeAuthorityDebt
    priority : Nat
    sameObjectRequired : Bool
    question : String
open TrusteeAuthorityAcquisition public

canonicalTrusteeAuthorityAcquisition : List TrusteeAuthorityAcquisition
canonicalTrusteeAuthorityAcquisition =
  trustee-authority-acquisition inspect1998TrustAgreement 100 true
    "Acquire and inspect the complete JPM-produced 25 Feb 1998 trust agreement, execution page, Schedule A and amendments to pay trustee powers, beneficiaries, contributed assets and investment authority from the governing instrument itself."
  ∷ trustee-authority-acquisition absSubscriptionAndWire 100 true
    "Acquire the executed 2006 ABS subscription, funding wire/account statement and capital-account record naming Wexner Children's Trust II to independently resolve the respondent pleading's USD20m assertion."
  ∷ trustee-authority-acquisition europeSubscriptionAndWire 99 true
    "Acquire the 2007 Europe Long/Short subscription and wire/redemption ledger for the Wexner trust investment separately from Epstein's personal investment."
  ∷ trustee-authority-acquisition trustAmendmentsAndRemoval 99 true
    "Trace amendments, successor trustee appointments and Epstein's removal/termination date rather than assuming trustee authority remained static through 2008."
  ∷ trustee-authority-acquisition investmentDecisionCommunications 98 true
    "Acquire contemporaneous trustee/adviser/beneficiary communications to distinguish formal trustee authority, investment recommendation and any grantor/beneficiary direction."
  ∷ trustee-authority-acquisition trustCapitalAndBeneficiaryAccounts 98 true
    "Reconstruct trust capital accounts, distributions and beneficiary incidence; trustee investment authority is not beneficial ownership."
  ∷ []
