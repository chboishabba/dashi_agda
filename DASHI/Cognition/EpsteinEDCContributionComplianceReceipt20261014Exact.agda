module DASHI.Cognition.EpsteinEDCContributionComplianceReceipt20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinUSVIEDCTaxIncidence20261014Exact as EDC

record ContributionReceipt : Set where
  constructor contribution-receipt
  field
    period : String
    totalQualifyingUSD : Nat
    financialTrustUSD : Nat
    foundationUSD : Nat
    source : String
    primaryComplianceCarrier : Bool
open ContributionReceipt public

contributions2007to2008 : ContributionReceipt
contributions2007to2008 = contribution-receipt
  "2007-2008" 469980 108925 361055
  "USVI EDA/EDC compliance report, USVI v JPMorgan Document 186-34 / VI-JPM-000023086"
  true

record FinancialTrustContributionBreakdown : Set where
  constructor ftc-contribution-breakdown
  field
    educationalScholarshipsUSD : Nat
    charityUSD : Nat
    coopMarketingEDCUSD : Nat
    otherOrFoundationColumnUSD : Nat
    totalUSD : Nat
open FinancialTrustContributionBreakdown public

ftcContributionBreakdown2007to2008 : FinancialTrustContributionBreakdown
ftcContributionBreakdown2007to2008 = ftc-contribution-breakdown
  12800 33625 25000 37500 108925

record ComplianceClarificationReceipt : Set where
  constructor compliance-clarification-receipt
  field
    date : String
    source : String
    boundedFinding : String
    discrepancyFlagged : Bool
    finalViolationAdjudicated : Bool
open ComplianceClarificationReceipt public

employeeResidencyClarification2011 : ComplianceClarificationReceipt
employeeResidencyClarification2011 = compliance-clarification-receipt
  "2011-08-15"
  "EFTA01100223 — USVI EDA preliminary review letter"
  "EDA preliminary review flagged a mismatch between FTC certification pages reporting twelve employees and an affidavit listing eleven, and requested clarification of Darren Indyke's residency status/date. This pays a compliance-document discrepancy requiring clarification, not a final adjudication of noncompliance."
  true false

winddownAuditDispute2014 : ComplianceClarificationReceipt
winddownAuditDispute2014 = compliance-clarification-receipt
  "2014-02-04"
  "EFTA00717380 — Cecile de Jongh forwarding EDA compliance reports to Epstein"
  "De Jongh disputed the audit process and the report's treatment of a full 2012 year, stating FTC ceased operations in March 2012 and that requested documentation had stamped EDC receipts. This is the beneficiary-side response to the compliance review, not proof the agency report was wrong."
  true false

record ContributionComplianceBoundary : Set where
  constructor contribution-compliance-boundary
  field
    qualifyingContributionsPaid : Bool
    employeeResidencyDiscrepancyPaid : Bool
    beneficiaryAuditDisputePaid : Bool
    contributionAmountOffsetsTaxBenefitDollarForDollar : Bool
    preliminaryClarificationEqualsViolation : Bool
    beneficiaryDisputeEqualsAgencyError : Bool
open ContributionComplianceBoundary public

canonicalContributionComplianceBoundary : ContributionComplianceBoundary
canonicalContributionComplianceBoundary = contribution-compliance-boundary
  true true true false false false

data ContributionsEqualFullPublicBenefit : Set where
data ClarificationEqualsViolation : Set where
data BeneficiaryDisputeEqualsAgencyError : Set where

contributionsDoNotCreateFullPublicBenefit : ContributionsEqualFullPublicBenefit → ⊥
contributionsDoNotCreateFullPublicBenefit ()
clarificationDoesNotCreateViolation : ClarificationEqualsViolation → ⊥
clarificationDoesNotCreateViolation ()
beneficiaryDisputeDoesNotCreateAgencyError : BeneficiaryDisputeEqualsAgencyError → ⊥
beneficiaryDisputeDoesNotCreateAgencyError ()
