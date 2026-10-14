module DASHI.Cognition.EpsteinFamilyInterestWexnerCapitalBridge20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- FAMILY INTEREST / WEXNER CHILDREN TRUST / FINANCIAL TRUST CAPITAL BRIDGE
--
-- Source-local result:
--   * JPMorgan due diligence described Financial Trust Company as GP of
--     Family Interest LP and Leslie Wexner's children's trust as an LP.
--   * a court-filed transaction review records a USD55,878,270.01 Family
--     Interests LP wire from Bear Stearns through Citibank to a JPM account
--     styled FAMILY INTERESTS LP C/O FINANCIAL TRUST CO GP.
--
-- Partnership capital belongs to the partnership/partners according to the
-- governing agreement and capital accounts. GP agency/management does not make
-- the full LP capital Epstein's personal property.
------------------------------------------------------------------------

record FamilyInterestStructure : Set where
  constructor family-interest-structure
  field
    generalPartner : String
    limitedPartnerDescription : String
    source : String
    gpRelationshipPaid : Bool
    lpRelationshipPaid : Bool
    exactOwnershipPercentagesPaid : Bool
    gpBeneficiallyOwnsAllLPAssets : Bool
open FamilyInterestStructure public

canonicalFamilyInterestStructure : FamilyInterestStructure
canonicalFamilyInterestStructure = family-interest-structure
  "Financial Trust Company, Inc."
  "Leslie Wexner's children's trust, as described in JPMorgan due-diligence records"
  "USVI v JPMorgan, Document 174-1 / JPM-SDNYLIT-00269656"
  true true false false

record PartnershipWire : Set where
  constructor partnership-wire
  field
    date : String
    originator : String
    originBank : String
    intermediary : String
    beneficiary : String
    amountUSD : Nat
    source : String
    paymentPurposePaid : Bool
    economicOwnerSplitPaid : Bool
open PartnershipWire public

familyInterest20031212 : PartnershipWire
familyInterest20031212 = partnership-wire
  "2003-12-12"
  "FAMILY INTERESTS LP"
  "Bear Stearns & Company"
  "Citibank"
  "FAMILY INTERESTS LP C/O FINANCIAL TRUST CO GP — JPMorgan account"
  55878270
  "USVI v JPMorgan, Document 285-06, court-filed transaction review"
  false false

record FamilyInterestBoundary : Set where
  constructor family-interest-boundary
  field
    ftcGeneralPartnerPaid : Bool
    wexnerChildrenTrustLPPaid : Bool
    largePartnershipCapitalMovementPaid : Bool
    financialTrustOperationalRolePaid : Bool
    wireIsTransferToEpsteinPersonally : Bool
    gpStatusImpliesBeneficialOwnershipOfLPAssets : Bool
    partnershipWireIdentifiesPartnerEconomicSplit : Bool
    capitalMovementImpliesWrongdoing : Bool
open FamilyInterestBoundary public

canonicalFamilyInterestBoundary : FamilyInterestBoundary
canonicalFamilyInterestBoundary = family-interest-boundary
  true true true true false false false false

data GPImpliesLPBeneficialOwnership : Set where
data PartnershipWireImpliesEpsteinPersonalAsset : Set where
data PartnershipWireImpliesPartnerSplit : Set where
data CapitalMovementImpliesWrongdoing : Set where

gpDoesNotCreateLPBeneficialOwnership : GPImpliesLPBeneficialOwnership → ⊥
gpDoesNotCreateLPBeneficialOwnership ()

partnershipWireDoesNotCreateEpsteinPersonalAsset : PartnershipWireImpliesEpsteinPersonalAsset → ⊥
partnershipWireDoesNotCreateEpsteinPersonalAsset ()

partnershipWireDoesNotCreatePartnerSplit : PartnershipWireImpliesPartnerSplit → ⊥
partnershipWireDoesNotCreatePartnerSplit ()

capitalMovementDoesNotCreateWrongdoing : CapitalMovementImpliesWrongdoing → ⊥
capitalMovementDoesNotCreateWrongdoing ()

------------------------------------------------------------------------
-- Pareto: the remaining object is partnership economics and authority.
------------------------------------------------------------------------

data FamilyInterestDebt : Set where
  partnershipAgreement : FamilyInterestDebt
  capitalAccounts : FamilyInterestDebt
  wexnerChildrenTrustIdentityAndTerms : FamilyInterestDebt
  gpFeesAndCarry : FamilyInterestDebt
  investmentPortfolio : FamilyInterestDebt
  contributionDistributionHistory : FamilyInterestDebt

record FamilyInterestAcquisition : Set where
  constructor family-interest-acquisition
  field
    debt : FamilyInterestDebt
    priority : Nat
    question : String
open FamilyInterestAcquisition public

canonicalFamilyInterestAcquisition : FamilyInterestAcquisition
canonicalFamilyInterestAcquisition = family-interest-acquisition
  partnershipAgreement 100
  "Acquire the Family Interest LP agreement/amendments to resolve GP powers, LP percentages, allocation rules, fees, withdrawal rights and control; the bank's relationship summary does not pay those terms."
