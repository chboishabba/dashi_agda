module DASHI.Cognition.EpsteinBlackApolloTrustStructure20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- EPSTEIN / BLACK / APOLLO-DERIVED WEALTH TRUST STRUCTURE
--
-- This owner separates:
--   (1) Apollo as an operating asset manager,
--   (2) Leon Black's personal/family ownership of Apollo-derived management,
--       advisory, partnership and co-investment interests,
--   (3) family trusts holding/transferring those interests, and
--   (4) Epstein's personal tax/estate advice concerning Black's wealth.
--
-- Touching Apollo-derived wealth in Black's estate plan is not the same claim
-- as Apollo retaining Epstein or an Apollo-managed fund taking Epstein money.
------------------------------------------------------------------------

data TrustObject : Set where
  judahInvestmentTrusts : TrustObject
  blackFamily2006Trust : TrustObject
  blackFamily1997Trust : TrustObject
  black2011FamilyTrusts : TrustObject
  blackFamilyPartners : TrustObject
  apProfessionalHoldings : TrustObject
  apo01 : TrustObject
  apo02 : TrustObject
  heritageTrustCandidate : TrustObject

record TrustReceipt : Set where
  constructor trust-receipt
  field
    label : String
    source : String
    boundedFinding : String
    apolloDerivedInterestsPresent : Bool
    epsteinAdvicePaid : Bool
    apolloRetainedEpsteinPaid : Bool
open TrustReceipt public

judahSchedulesReceipt : TrustReceipt
judahSchedulesReceipt = trust-receipt
  "Judah Investment Trust schedules"
  "EFTA00589418..424"
  "Released schedules enumerate transfers of Leon Black interests in Apollo Management III/IV/V/VI, Apollo Investment Management, Apollo Value Management, Apollo SVF Management, Apollo Asia Management, Apollo Europe Management, Apollo Alternative Assets and Apollo Advisors VI points into Judah Investment Trusts."
  true false false

apProfessionalStructureReceipt : TrustReceipt
apProfessionalStructureReceipt = trust-receipt
  "Black family/AP Professional Holdings structure"
  "EFTA00588975 and related valuation/organization charts"
  "Released charts place Black family trusts, Black Family Partners, BRH/LBF entities and Apollo management/co-investment interests in the AP Professional Holdings ownership structure."
  true false false

senateEpsteinTrustAdviceReceipt : TrustReceipt
senateEpsteinTrustAdviceReceipt = trust-receipt
  "Epstein advice on Apollo-derived trust wealth"
  "US Senate Finance Committee 2023 investigation statement; Dechert 2021 report"
  "Senate Finance states Epstein proposed a solution concerning excess income from Apollo partnership interests held in a trust and played a significant/instrumental role in another family-trust transaction. Dechert describes Epstein as advising Black on trust/estate/tax matters."
  true true false

estateInventoryReceipt : TrustReceipt
estateInventoryReceipt = trust-receipt
  "Black estate inventory includes Apollo-derived assets"
  "EFTA00617015..; EFTA01088190..; EFTA00299513.."
  "Released estate-planning inventories include Black Family Partners interests, Apollo co-investments, AP Alternative Assets, Apollo Credit Opportunity Fund, Apollo Investment Corp and other Apollo-related investments among trust/family-office assets."
  true false false

record ApolloTrustBoundary : Set where
  constructor apollo-trust-boundary
  field
    blackWealthContainsApolloDerivedInterests : Bool
    trustsHoldOrTransferApolloDerivedInterests : Bool
    epsteinAdvisedBlackOnTrustEstateTax : Bool
    epsteinAdviceTouchedApolloDerivedTrustInterests : Bool
    apolloCorporateRetentionOfEpsteinPaid : Bool
    epsteinInvestedInApolloManagedFundPaid : Bool
    epsteinBoughtApolloPublicStockPaid : Bool
open ApolloTrustBoundary public

canonicalApolloTrustBoundary : ApolloTrustBoundary
canonicalApolloTrustBoundary = apollo-trust-boundary
  true true true true false false true

data ApolloDerivedWealthImpliesApolloRetention : Set where
data TrustAdviceImpliesApolloCorporateRelationship : Set where
data ApolloStockImpliesApolloFundLP : Set where

apolloDerivedWealthDoesNotCreateApolloRetention : ApolloDerivedWealthImpliesApolloRetention → ⊥
apolloDerivedWealthDoesNotCreateApolloRetention ()

trustAdviceDoesNotCreateApolloCorporateRelationship : TrustAdviceImpliesApolloCorporateRelationship → ⊥
trustAdviceDoesNotCreateApolloCorporateRelationship ()

apolloStockDoesNotCreateApolloFundLP : ApolloStockImpliesApolloFundLP → ⊥
apolloStockDoesNotCreateApolloFundLP ()

------------------------------------------------------------------------
-- Remaining same-object acquisition.
------------------------------------------------------------------------

data ApolloTrustDebt : Set where
  exactEpsteinMemoOnApolloInterests : ApolloTrustDebt
  excessIncomeTrustTransaction : ApolloTrustDebt
  sixHundredMillionTaxTransaction : ApolloTrustDebt
  votingRightsAndConsideration : ApolloTrustDebt
  blackPaymentInvoiceJoin : ApolloTrustDebt
  familyOfficeAdvisorValidation : ApolloTrustDebt

record ApolloTrustAcquisition : Set where
  constructor apollo-trust-acquisition
  field
    debt : ApolloTrustDebt
    priority : Nat
    question : String
open ApolloTrustAcquisition public

canonicalApolloTrustAcquisition : List ApolloTrustAcquisition
canonicalApolloTrustAcquisition =
  apollo-trust-acquisition exactEpsteinMemoOnApolloInterests 100
    "Acquire Epstein-authored notes/memos/emails tied to the trust holding Apollo partnership interests, distinguishing Epstein's actual proposal from summaries by Dechert/Senate Finance."
  ∷ apollo-trust-acquisition excessIncomeTrustTransaction 100
    "Resolve the trust, Apollo-derived assets, excess-income amount, proposed consideration, implementation and tax treatment in the transaction Senate Finance describes."
  ∷ apollo-trust-acquisition sixHundredMillionTaxTransaction 99
    "Resolve the family-trust transaction for which Dechert/Senate Finance attribute a significant/instrumental Epstein role and approximately USD 600m future gift/estate-tax savings."
  ∷ apollo-trust-acquisition votingRightsAndConsideration 99
    "Resolve whether Black retained voting/economic rights in transferred Apollo-derived assets and the amount/nature of consideration proposed by Epstein."
  ∷ apollo-trust-acquisition blackPaymentInvoiceJoin 98
    "Join individual Black/Southern Trust payments to exact advisory work products and invoices instead of importing the aggregate USD 158m narrative onto every wire."
  ∷ apollo-trust-acquisition familyOfficeAdvisorValidation 97
    "Acquire Paul Weiss/accounting/family-office review materials showing which Epstein proposals were accepted, modified or rejected."
  ∷ []
