module DASHI.Cognition.EpsteinBearStructuredFundRecoveryRound20261015Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinFinancialTrustBearCrisisAwarenessSettlement20261014Exact as Prior

------------------------------------------------------------------------
-- BEAR STRUCTURED-CREDIT RECOVERY ROUND — 2026-10-15
--
-- The 2009 respondent answer pays attributed interim recovery amounts and
-- assignment chronology.  These are not substituted for final bank/administrator
-- statements, but they narrow the realised-loss calculation and prevent gross
-- contribution amounts from being treated as terminal losses.
------------------------------------------------------------------------

data RecoverySourceClass : Set where
  respondentPleading : RecoverySourceClass
  executedAssignment : RecoverySourceClass
  settlementAgreement : RecoverySourceClass
  neutralFundAdministrator : RecoverySourceClass

record RecoveryReceipt : Set where
  constructor recovery-receipt
  field
    label : String
    asOf : String
    sourceClass : RecoverySourceClass
    source : String
    boundedFinding : String
    amountUSD : Nat
    lowerBound : Bool
    finalRecoveryPaid : Bool
open RecoveryReceipt public

couqPreWinddownRedemption : RecoveryReceipt
couqPreWinddownRedemption = recovery-receipt
  "COUQ February 2007 ABS redemption"
  "2007-02"
  respondentPleading
  "EFTA00294820 — Bear Stearns Respondents' FINRA Statement of Answer"
  "Bear respondents state that COUQ redeemed USD3m of profits from its ABS Fund position in February 2007, when the investment had increased to about USD14.6m. This is an attributed transaction assertion and must be reconciled to the attached redemption request/fund statement before being treated as neutral settled cash."
  3000000 false false

ftcWinddownRecovery2009 : RecoveryReceipt
ftcWinddownRecovery2009 = recovery-receipt
  "FTC ABS wind-down proceeds by December 2009"
  "2009-12-04"
  respondentPleading
  "EFTA00294835 — Bear Stearns Respondents' FINRA Statement of Answer"
  "Bear respondents state that, by the answer date, FTC had been paid nearly USD3m from the ABS wind-down. The phrase 'nearly' makes USD3m an approximate ceiling rather than an exact receipt; final administrator statements remain required."
  3000000 false false

ylkWinddownRecovery2009 : RecoveryReceipt
ylkWinddownRecovery2009 = recovery-receipt
  "YLK post-assignment ABS wind-down proceeds by December 2009"
  "2009-12-04"
  respondentPleading
  "Bear respondents state that YLK, assignee of COUQ's ABS interest, had received over USD3m from the wind-down by December 2009. USD3m is therefore a lower bound on the pleaded YLK recovery, not the final amount."
  3000000 true false

couqToYLKAssignment2008 : RecoveryReceipt
couqToYLKAssignment2008 = recovery-receipt
  "COUQ assigns ABS interest to YLK"
  "2008-01-01"
  respondentPleading
  "EFTA00294821 and attached Exhibit K lineage"
  "The respondent answer states that COUQ entered an assignment agreement with YLK on January 1, 2008 transferring all right, title and interest in its ABS position. The executed assignment itself remains the preferred transaction receipt; this owner pays the pleading's description and acquisition target."
  0 false false

settlement2011 : RecoveryReceipt
settlement2011 = recovery-receipt
  "Bear arbitration collective settlement"
  "2011"
  settlementAgreement
  "EFTA00597963.. settlement agreement"
  "Bear/respondent parties agreed to a USD9.2m collective settlement with FTC/COUQ/Epstein claimants; allocation among claimants/counsel is not stated. Settlement is recovery/incidence evidence, not an admission of merits."
  9200000 false true

record RecoveryBoundary : Set where
  constructor recovery-boundary
  field
    grossContributionLedgerPaid : Bool
    interimWinddownRecoveryAssertionsPaid : Bool
    collectiveSettlementPaid : Bool
    finalFundAdministratorRecoveryLedgerPaid : Bool
    settlementAllocationPaid : Bool
    approximateThreeMillionMeansExactThreeMillion : Bool
    ylkRecoveryBelongsToCOUQAfterAssignment : Bool
    grossLossEqualsNetEconomicLoss : Bool
open RecoveryBoundary public

canonicalRecoveryBoundary : RecoveryBoundary
canonicalRecoveryBoundary = recovery-boundary
  true true true false false false false false

data ApproximateAmountImpliesExactAmount : Set where
data AssignmentImpliesAssignorOwnsLaterRecovery : Set where
data GrossContributionImpliesNetLoss : Set where

approximateDoesNotCreateExact : ApproximateAmountImpliesExactAmount → ⊥
approximateDoesNotCreateExact ()

assignmentDoesNotCreateLaterAssignorOwnership : AssignmentImpliesAssignorOwnsLaterRecovery → ⊥
assignmentDoesNotCreateLaterAssignorOwnership ()

grossContributionDoesNotCreateNetLoss : GrossContributionImpliesNetLoss → ⊥
grossContributionDoesNotCreateNetLoss ()

------------------------------------------------------------------------
-- Net-loss max-cut.
------------------------------------------------------------------------

data RecoveryDebt : Set where
  attachedCOUQRedemptionRequest : RecoveryDebt
  executedCOUQYLKAssignment : RecoveryDebt
  finalABSAdministratorLedger : RecoveryDebt
  ftcInKindRecoveryValuation : RecoveryDebt
  ylkFinalRecoveryLedger : RecoveryDebt
  settlementAllocationLedger : RecoveryDebt
  taxBasisRealisedLossJoin : RecoveryDebt

record RecoveryAcquisition : Set where
  constructor recovery-acquisition
  field
    debt : RecoveryDebt
    priority : Nat
    question : String
open RecoveryAcquisition public

canonicalRecoveryAcquisition : List RecoveryAcquisition
canonicalRecoveryAcquisition =
  recovery-acquisition finalABSAdministratorLedger 100
    "Acquire final fund-administrator cash/in-kind distribution statements for FTC and the COUQ->YLK interest through liquidation; respondent interim figures are not terminal recoveries." ∷
  recovery-acquisition settlementAllocationLedger 100
    "Allocate the USD9.2m settlement among FTC, COUQ/Epstein/counsel before computing claimant-specific net recovery." ∷
  recovery-acquisition executedCOUQYLKAssignment 99
    "Inspect Exhibit K or duplicate executed January 2008 assignment to pay the exact transferred interest, consideration and effective date from the instrument rather than the respondent description." ∷
  recovery-acquisition attachedCOUQRedemptionRequest 99
    "Inspect the February 2007 redemption request and matching fund statement/wire to promote the pleaded USD3m profit withdrawal to neutral transaction evidence." ∷
  recovery-acquisition ftcInKindRecoveryValuation 99
    "Resolve any FTC in-kind securities/trust interest received during ABS wind-down and subsequent cash flows/redemptions." ∷
  recovery-acquisition ylkFinalRecoveryLedger 98
    "Trace all post-assignment YLK distributions so recovery is attributed to the correct economic/legal holder." ∷
  recovery-acquisition taxBasisRealisedLossJoin 98
    "Join contributions, rollover, distributions, settlement and tax basis to compute realised economic loss without double counting rolled capital or transferred interests."
  ∷ []
