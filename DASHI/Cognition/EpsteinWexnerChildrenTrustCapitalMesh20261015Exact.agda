module DASHI.Cognition.EpsteinWexnerChildrenTrustCapitalMesh20261015Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinFamilyInterestWexnerCapitalBridge20261014Exact as FamilyInterest

------------------------------------------------------------------------
-- WEXNER-FAMILY TRUST / FTC CAPITAL MESH — 2026-10-15
--
-- Two distinct source-paid surfaces are kept separate:
--   1. JPM due diligence: FTC as GP of Family Interest LP; a Wexner children's
--      trust described as LP.
--   2. EFTA00582930: Wexner Children's Trust II as creditor on a non-recourse
--      note to Darren Indyke, repaid through FTC -> Indyke attorney trust.
--
-- Similar naming does not silently identify the LP trust with Trust II without
-- a governing partnership/trust instrument.
------------------------------------------------------------------------

data WexnerCapitalSurface : Set where
  familyInterestLimitedPartner : WexnerCapitalSurface
  nonRecourseNoteCreditor : WexnerCapitalSurface
  ftcGeneralPartner : WexnerCapitalSurface
  ftcLoanAdvance : WexnerCapitalSurface
  nysgOwnershipFinance : WexnerCapitalSurface

record WexnerCapitalReceipt : Set where
  constructor wexner-capital-receipt
  field
    label : String
    date : String
    source : String
    boundedFinding : String
    surfaces : List WexnerCapitalSurface
    amountUSD : Nat
    paid : Bool
open WexnerCapitalReceipt public

familyInterestStructure : WexnerCapitalReceipt
familyInterestStructure = wexner-capital-receipt
  "FTC / Family Interest / Wexner children's trust structure"
  "2003-era JPM relationship record"
  "USVI v JPMorgan, Document 174-1 / JPM-SDNYLIT-00269656"
  "JPM due diligence describes Financial Trust Company as general partner of Family Interest LP and Leslie Wexner's children's trust as a limited partner. The record pays role identity but not partner percentages, allocations, fees or withdrawal/control terms."
  (ftcGeneralPartner ∷ familyInterestLimitedPartner ∷ [])
  0 true

wexnerTrustIINoteRepayment : WexnerCapitalReceipt
wexnerTrustIINoteRepayment = wexner-capital-receipt
  "FTC-funded repayment of Wexner Children's Trust II note"
  "2007-11-06"
  "EFTA00582930..EFTA00582934 — Summary of Outstanding Balances / transfer timeline"
  "An internal financial summary records USD3,458,416.55 transferred from Financial Trust Company to Darren Indyke's attorney trust account and then to Wexner Children's Trust II as repayment in full of a non-recourse promissory note owed by Indyke. It states that the Trust II loan had funded Indyke's purchase of the majority New York Strategy Group interest from Jeff Schantz and that FTC booked its advance as a loan payable from Indyke."
  (nonRecourseNoteCreditor ∷ ftcLoanAdvance ∷ nysgOwnershipFinance ∷ [])
  3458416 true

record WexnerCapitalBoundary : Set where
  constructor wexner-capital-boundary
  field
    familyInterestWexnerTrustLPPaid : Bool
    trustIINoteCreditorPaid : Bool
    ftcFundedTrustIINoteRepaymentPaid : Bool
    notePurposeNYSGPurchasePaid : Bool
    familyInterestLPTrustEqualsTrustIIPaid : Bool
    ftcAdvanceMakesTrustIIEpsteinOwned : Bool
    noteRepaymentImpliesImproperPayment : Bool
open WexnerCapitalBoundary public

canonicalWexnerCapitalBoundary : WexnerCapitalBoundary
canonicalWexnerCapitalBoundary = wexner-capital-boundary
  true true true true false false false

data SimilarTrustNameImpliesSameLegalTrust : Set where
data FTCAdvanceImpliesTrustOwnership : Set where
data NoteRepaymentImpliesWrongdoing : Set where

similarNameDoesNotCreateTrustIdentity : SimilarTrustNameImpliesSameLegalTrust → ⊥
similarNameDoesNotCreateTrustIdentity ()

ftcAdvanceDoesNotCreateTrustOwnership : FTCAdvanceImpliesTrustOwnership → ⊥
ftcAdvanceDoesNotCreateTrustOwnership ()

noteRepaymentDoesNotCreateWrongdoing : NoteRepaymentImpliesWrongdoing → ⊥
noteRepaymentDoesNotCreateWrongdoing ()

------------------------------------------------------------------------
-- Max-cut: move from network existence to governing economics and authority.
------------------------------------------------------------------------

data WexnerCapitalDebt : Set where
  familyInterestPartnershipAgreement : WexnerCapitalDebt
  familyInterestCapitalAccounts : WexnerCapitalDebt
  identifyFamilyInterestLPTrust : WexnerCapitalDebt
  trustIIPromissoryNote : WexnerCapitalDebt
  ftcToIndykeLoanTerms : WexnerCapitalDebt
  nysgPurchaseAgreementAndCapTable : WexnerCapitalDebt

record WexnerCapitalAcquisition : Set where
  constructor wexner-capital-acquisition
  field
    debt : WexnerCapitalDebt
    priority : Nat
    sameObjectRequired : Bool
    question : String
open WexnerCapitalAcquisition public

canonicalWexnerCapitalAcquisition : List WexnerCapitalAcquisition
canonicalWexnerCapitalAcquisition =
  wexner-capital-acquisition familyInterestPartnershipAgreement 100 true
    "Acquire the Family Interest LP agreement/amendments: GP powers, partner percentages, allocation/distribution rules, fees and withdrawal/control rights."
  ∷ wexner-capital-acquisition familyInterestCapitalAccounts 100 true
    "Acquire partner capital accounts and contribution/distribution history around the USD55.878m partnership wire so economic incidence can be assigned without treating GP agency as beneficial ownership."
  ∷ wexner-capital-acquisition identifyFamilyInterestLPTrust 99 true
    "Resolve the exact legal identity of the Wexner children's trust named as Family Interest LP limited partner and test whether it is or is not Wexner Children's Trust II."
  ∷ wexner-capital-acquisition trustIIPromissoryNote 99 true
    "Acquire the executed non-recourse promissory note, collateral and repayment terms between Wexner Children's Trust II and Indyke."
  ∷ wexner-capital-acquisition ftcToIndykeLoanTerms 98 true
    "Resolve FTC's USD3.458m advance/loan to Indyke, including authorization, interest, maturity, repayment and accounting treatment."
  ∷ wexner-capital-acquisition nysgPurchaseAgreementAndCapTable 98 true
    "Acquire the Schantz-to-Indyke New York Strategy Group purchase documents and cap table to quantify the ownership change funded by the trust note."
  ∷ []
