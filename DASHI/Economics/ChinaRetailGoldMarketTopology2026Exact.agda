module DASHI.Economics.ChinaRetailGoldMarketTopology2026Exact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Economics.FinancialPhysicalBackingMarketControlExact as Backing

------------------------------------------------------------------------
-- SOURCE-BOUNDED 2026 CHINA RETAIL GOLD MARKET-TOPOLOGY FIXTURE
--
-- This fixture records specific bank service changes, not a theorem that China
-- enacted a blanket national ban on gold or all forms of paper exposure.
------------------------------------------------------------------------

record OfficialBankGoldServiceReceipt : Set where
  constructor officialBankGoldServiceReceipt
  field
    institution : String
    announcementDate : String
    serviceClosureDate : String
    serviceClass : String
    sourceReference : String

open OfficialBankGoldServiceReceipt public

icbc2026Closure : OfficialBankGoldServiceReceipt
icbc2026Closure =
  officialBankGoldServiceReceipt
    "Industrial and Commercial Bank of China"
    "2026-06-24"
    "2026-07-24 end-of-day settlement"
    "agency Shanghai Gold Exchange individual precious-metals auction trading"
    "ICBC official announcement: /page/1243135845339447296.html"

ccb2026Closure : OfficialBankGoldServiceReceipt
ccb2026Closure =
  officialBankGoldServiceReceipt
    "China Construction Bank"
    "2026-06-25"
    "2026-07-24 end-of-day settlement"
    "agency Shanghai Gold Exchange individual precious-metals trading"
    "CCB official gold notice: article_2026062514061012575.shtml"

psbc2026Closure : OfficialBankGoldServiceReceipt
psbc2026Closure =
  officialBankGoldServiceReceipt
    "Postal Savings Bank of China"
    "2026-03-17"
    "2026-03-27 residual-position handling"
    "agency Shanghai Gold Exchange individual precious-metals trading"
    "PSBC official announcement: 202603/t20260316_405396.html"

------------------------------------------------------------------------
-- The same PSBC public product surface continued to list physical precious
-- metals and gold accumulation.  Hence this fixture models selective channel
-- retrenchment, not physical-gold prohibition.
------------------------------------------------------------------------

china2026SelectiveRetrenchment : Backing.SelectiveFinancialRetrenchment
china2026SelectiveRetrenchment =
  Backing.selectiveFinancialRetrenchment
    Backing.deferredFinancialChannel
    true refl
    true refl
    "2026 bank SGE individual-service closures coexist with continuing physical precious-metals and gold-accumulation product surfaces."

record ChinaRetailGoldTopologyBoundary : Set where
  constructor chinaRetailGoldTopologyBoundary
  field
    fixtureProvesBlanketNationalGoldBan : Bool
    fixtureProvesBlanketNationalGoldBanIsFalse :
      fixtureProvesBlanketNationalGoldBan ≡ false

    fixtureProvesAllFinancialGoldExposureAbsent : Bool
    fixtureProvesAllFinancialGoldExposureAbsentIsFalse :
      fixtureProvesAllFinancialGoldExposureAbsent ≡ false

    fixtureSupportsSelectiveChannelRetrenchment : Bool
    fixtureSupportsSelectiveChannelRetrenchmentIsTrue :
      fixtureSupportsSelectiveChannelRetrenchment ≡ true

    physicalAndAccumulationChannelsRemainRepresented : Bool
    physicalAndAccumulationChannelsRemainRepresentedIsTrue :
      physicalAndAccumulationChannelsRemainRepresented ≡ true

canonicalChinaRetailGoldTopologyBoundary : ChinaRetailGoldTopologyBoundary
canonicalChinaRetailGoldTopologyBoundary =
  chinaRetailGoldTopologyBoundary
    false refl
    false refl
    true refl
    true refl
