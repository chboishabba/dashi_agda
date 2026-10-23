module DASHI.Cognition.EpsteinWexnerTrustInstrumentAuthority20261015Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinWexnerTrustBearInvestmentAuthority20261015Exact as BearAuthority

------------------------------------------------------------------------
-- WEXNER CHILDREN'S TRUST II — GOVERNING INSTRUMENT AUTHORITY RECEIPT
-- 2026-10-15
--
-- Primary/released JPMorgan production now pays the trust instrument itself.
-- The instrument establishes formal trustee authority; it does not establish
-- personal beneficial ownership, every later investment, or grantor direction
-- of any particular trade.
------------------------------------------------------------------------

record TrustInstrumentReceipt : Set where
  constructor trust-instrument-receipt
  field
    date : String
    source : String
    grantor : String
    trustee : String
    initialAsset : String
    initialAssetQuantity : Nat
    trusteeDiscretionPaid : Bool
    revocableByGrantorPaid : Bool
    executionByEpsteinAsTrusteePaid : Bool
    executionForGrantorAsAttorneyInFactPaid : Bool
    exactBeneficialOwnershipTransferredToTrustee : Bool
open TrustInstrumentReceipt public

wexnerTrust1998 : TrustInstrumentReceipt
wexnerTrust1998 = trust-instrument-receipt
  "1998-02-25"
  "JPMorgan-produced trust agreement: EFTA01481286 / duplicate EFTA01480436; execution EFTA01480437; Schedule A EFTA01480438; notary EFTA01480439"
  "Leslie H. Wexner"
  "Jeffrey E. Epstein"
  "The Limited, Inc. common stock"
  2500000
  true true true true false

record TrustAuthorityReading : Set where
  constructor trust-authority-reading
  field
    primaryInstrumentPaid : Bool
    grantorTrusteeIdentityPaid : Bool
    initialTwoPointFiveMillionLimitedSharesPaid : Bool
    discretionaryIncomePrincipalAuthorityPaid : Bool
    grantorRevocationPaid : Bool
    trusteeRoleCanSupportInvestmentAuthorityHypothesis : Bool
    bearTradeAmountsIndependentlyPaidByThisInstrument : Bool
    trusteeIsBeneficialOwner : Bool
    grantorPersonallyDirectedEachInvestment : Bool
open TrustAuthorityReading public

canonicalTrustAuthorityReading : TrustAuthorityReading
canonicalTrustAuthorityReading = trust-authority-reading
  true true true true true true false false false

data TrusteeAuthorityImpliesBeneficialOwnership : Set where
data GoverningAuthorityImpliesSpecificTrade : Set where
data RevocableTrustImpliesGrantorDirectedEveryTrade : Set where

trusteeAuthorityDoesNotCreateBeneficialOwnership : TrusteeAuthorityImpliesBeneficialOwnership → ⊥
trusteeAuthorityDoesNotCreateBeneficialOwnership ()

governingAuthorityDoesNotCreateSpecificTrade : GoverningAuthorityImpliesSpecificTrade → ⊥
governingAuthorityDoesNotCreateSpecificTrade ()

revocabilityDoesNotCreateTradeDirection : RevocableTrustImpliesGrantorDirectedEveryTrade → ⊥
revocabilityDoesNotCreateTradeDirection ()

------------------------------------------------------------------------
-- Remaining authority cut.
------------------------------------------------------------------------

data TrustAuthorityDebt : Set where
  amendmentsAndSuccessorTrustees : TrustAuthorityDebt
  bearABSSubscription : TrustAuthorityDebt
  bearEuropeSubscription : TrustAuthorityDebt
  investmentDecisionCommunications : TrustAuthorityDebt
  completeTrustAssetLedger : TrustAuthorityDebt
  beneficiaryDistributionLedger : TrustAuthorityDebt

record TrustAuthorityAcquisition : Set where
  constructor trust-authority-acquisition
  field
    debt : TrustAuthorityDebt
    priority : Nat
    question : String
open TrustAuthorityAcquisition public

canonicalTrustAuthorityAcquisition : List TrustAuthorityAcquisition
canonicalTrustAuthorityAcquisition =
  trust-authority-acquisition bearABSSubscription 100
    "Acquire the executed Wexner Children's Trust II ABS subscription/wire/capital-account record to promote Bear's USD20m respondent assertion to a neutral transaction receipt." ∷
  trust-authority-acquisition amendmentsAndSuccessorTrustees 100
    "Trace every amendment, revocation, successor trustee and Epstein-removal instrument; the 1998 authority cannot be assumed unchanged indefinitely." ∷
  trust-authority-acquisition bearEuropeSubscription 99
    "Acquire the trust's Europe Long/Short subscription, wire and redemption records independently of Epstein's personal position." ∷
  trust-authority-acquisition completeTrustAssetLedger 99
    "Reconstruct contributions, securities, sales, investment-fund positions and distributions through time rather than treating Schedule A as the complete later portfolio." ∷
  trust-authority-acquisition investmentDecisionCommunications 98
    "Resolve trustee recommendations, beneficiary/grantor communications and investment instructions to distinguish legal authority from actual decision provenance." ∷
  trust-authority-acquisition beneficiaryDistributionLedger 98
    "Resolve who received economic distributions and when; legal trustee authority is distinct from beneficiary incidence." ∷
  []
