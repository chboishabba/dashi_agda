module DASHI.Economics.ChinaOfficialEconomicSelfPosition2026Exact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)
import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- CHINA'S OFFICIAL ECONOMIC SELF-POSITION, 2026
--
-- Official self-description is an attributed political/economic claim surface,
-- not independent proof of comprehensive global economic leadership.
------------------------------------------------------------------------

xiManufacturingPowerhouse2026 : Source.AttributedSource
xiManufacturingPowerhouse2026 = Source.mkNoDOISource
  "State Council of the People's Republic of China / Xinhua"
  "Xi Focus: Steering China's strides toward manufacturing powerhouse"
  "english.gov.cn"
  "2026-09-19"
  "https://english.www.gov.cn/news/202609/19/content_WS6aaddce0c6d00ca5f9a0d418.html"
  Source.governmentSource
  "official Chinese carrier quoting Xi that China has become the world's largest manufacturing country with the most complete industrial sectors and categories"
  Source.publicAttribution

mfaEconomicSelfPosition2026 : Source.AttributedSource
mfaEconomicSelfPosition2026 = Source.mkNoDOISource
  "Ministry of Foreign Affairs of the People's Republic of China"
  "Remarks by Chinese Ambassador to Cyprus Yang Yundong"
  "Ministry of Foreign Affairs"
  "2026-09-18"
  "https://www.fmprc.gov.cn/eng/xw/zwbd/202609/t20260918_12025982.html"
  Source.governmentSource
  "official self-description: second-largest economy, largest manufacturing power, largest trader in goods, second-largest consumer market and extensive infrastructure leadership"
  Source.publicAttribution

data OfficialLeadershipClaim : Set where
  secondLargestEconomy : OfficialLeadershipClaim
  largestManufacturingPower : OfficialLeadershipClaim
  largestGoodsTrader : OfficialLeadershipClaim
  secondLargestConsumerMarket : OfficialLeadershipClaim
  globalGrowthEngineClaim : OfficialLeadershipClaim
  comprehensiveEconomicVictoryClaim : OfficialLeadershipClaim

record SelfPositionReceipt : Set where
  constructor self-position-receipt
  field
    claim : OfficialLeadershipClaim
    reading : String
    source : Source.AttributedSource
    officialSelfAssertion : Bool
    independentlyClosesComprehensiveLeadership : Bool
    independentlyClosesEconomicVictory : Bool

open SelfPositionReceipt public

manufacturingSelfPosition : SelfPositionReceipt
manufacturingSelfPosition = self-position-receipt
  largestManufacturingPower
  "China officially describes itself as the world's largest manufacturing country/power."
  xiManufacturingPowerhouse2026
  true false false

broadSelfPosition : SelfPositionReceipt
broadSelfPosition = self-position-receipt
  largestGoodsTrader
  "Chinese MFA materials describe China as the world's second-largest economy and largest goods trader/manufacturing power."
  mfaEconomicSelfPosition2026
  true false false

data OfficialSelfDescriptionMeansIndependentFact : Set where
data LargestManufacturingPowerMeansComprehensiveEconomicVictory : Set where

officialSelfDescriptionDoesNotByItselfCreateIndependentFact :
  OfficialSelfDescriptionMeansIndependentFact → ⊥
officialSelfDescriptionDoesNotByItselfCreateIndependentFact ()

manufacturingLeadershipDoesNotDefinitionallyMeanComprehensiveVictory :
  LargestManufacturingPowerMeansComprehensiveEconomicVictory → ⊥
manufacturingLeadershipDoesNotDefinitionallyMeanComprehensiveVictory ()
