module DASHI.Economics.TreasuryAuctionJapanFlow20261121Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

-- First 10Y primary auction: TreasuryDirect original, 2026-11-10.
-- Percent yields are in THOUSANDTHS of one percent: 5020 = 5.020%.
-- Values from source are not comparable to secondary CMT without tenor/date
-- alignment, nor to Japan's aggregate overseas securities purchases.
record AuctionResult : Set where
  constructor auctionResult
  field
    cusip : String
    auctionDate : String
    issueDate : String
    securityType : String
    offeringUSD : Nat
    highYieldThousandthPercent : Nat
    bidToCoverHundredths : Nat
    originalSource : String
    primaryVerified : Bool
open AuctionResult public

tenYearNovember : AuctionResult
tenYearNovember = auctionResult
  "91282CRX1" "2026-11-10" "2026-11-16" "10-year note"
  42000000000 5020 246
  "https://www.treasurydirect.gov/instit/annceresult/press/preanre/2026/R_20261110_1.pdf"
  true

-- Provisional secondary transcription; original 30Y TreasuryDirect auction
-- page has not been read and this row must NOT receive primary authority.
thirtyYearNovember : AuctionResult
thirtyYearNovember = auctionResult
  "912810UY2" "2026-11-12" "2026-11-16" "30-year bond"
  25000000000 5441 236
  "https://kresmion.com/tools/treasury-auctions/30-year-bond"
  false

tenYearHighYieldExact :
  highYieldThousandthPercent tenYearNovember ≡ 5020
tenYearHighYieldExact = refl

thirtyYearPrimaryStillOpen :
  primaryVerified thirtyYearNovember ≡ false
thirtyYearPrimaryStillOpen = refl

-- July/August resident foreign bonds and notes from MOF designated-major-
-- investor monthly series as reprinted by Dow Jones on 2026-09-08.
-- Units: 0.1 JPY billion. Net PLUS indicates net acquisitions.
-- August reported net differs by 0.1bn due to published rounding.
-- This is NOT US-Treasury-specific and not GPIF holdings or auction take-up.
record ResidentForeignBonds : Set where
  constructor residentForeignBonds
  field
    month : String
    purchasesTenthsBillionJPY : Nat
    salesTenthsBillionJPY : Nat
    reportedNetMagnitudeTenthsBillionJPY : Nat
    netPurchases : Bool
    source : String
    originalMOFBreakdownPaid : Bool
    unitedStatesTreasuryScopePaid : Bool
open ResidentForeignBonds public

julyResidentForeignDebt : ResidentForeignBonds
julyResidentForeignDebt = residentForeignBonds
  "2026-07" 373506 369849 3657 true
  "https://www.itiger.com/news/2665348737"
  false false

augustResidentForeignDebt : ResidentForeignBonds
augustResidentForeignDebt = residentForeignBonds
  "2026-08" 392691 394122 1430 false
  "https://www.itiger.com/news/2665348737"
  false false

julyNetExact :
  purchasesTenthsBillionJPY julyResidentForeignDebt ≡
  salesTenthsBillionJPY julyResidentForeignDebt + 3657
julyNetExact = refl

augustNetFromGross :
  salesTenthsBillionJPY augustResidentForeignDebt ≡
  purchasesTenthsBillionJPY augustResidentForeignDebt + 1431
augustNetFromGross = refl

augustReportedRoundingDifference :
  reportedNetMagnitudeTenthsBillionJPY augustResidentForeignDebt + 1 ≡ 1431
augustReportedRoundingDifference = refl

data AggregateForeignDebtIsUSTPosition : Set where
aggregateForeignDebtDoesNotIdentifyUST :
  AggregateForeignDebtIsUSTPosition → ⊥
aggregateForeignDebtDoesNotIdentifyUST ()

data AuctionIndirectBidsIdentifyJapan : Set where
indirectBiddersCannotIdentifyJapan :
  AuctionIndirectBidsIdentifyJapan → ⊥
indirectBiddersCannotIdentifyJapan ()

data EarlierAuctionYieldProvesJPYPolicyIntent : Set where
auctionYieldDoesNotEstablishIntent :
  EarlierAuctionYieldProvesJPYPolicyIntent → ⊥
auctionYieldDoesNotEstablishIntent ()
