module DASHI.Governance.AIInvestmentGradeCreditRepricing20261030Exact where

------------------------------------------------------------------------
-- POINT-IN-TIME MARKET MEASUREMENT / FIRST-SECOND-THIRD ORDER RISK
--
-- Independent original index provider:
-- Lydia Hamill and Paul Amery, "AI's borrowing boom: What it means for
-- bond indices", LSEG/FTSE Russell Insights, 2026-10-29.
-- https://www.lseg.com/en/insights/ftse-russell/
-- ais-borrowing-boom-what-it-means-for-bond-indices
-- Two different denominators: broad IG issuance 218.1bn early October
-- versus narrower USD index eligible 151.75bn 2 October; they must NOT
-- be silently equated. OAS as-of 2026-09-30; CDS as-of 2026-10-21.
--
-- FOMC ORIGINALS:
-- Federal Reserve, 2026-09-16: hike 25bp to 3.75-4%.
-- https://www.federalreserve.gov/newsevents/pressreleases/monetary20260916a.htm
-- Federal Reserve, 2026-10-28: HOLD, 10-2 vote, two dissents for hike.
-- https://www.federalreserve.gov/newsevents/pressreleases/monetary20261028a.htm
--
-- This is source-calibration / exact arithmetic on quoted observations,
-- NOT a pricing model, clinical proof or causal identification of losses.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Economics.AIFinancingReflexivityExact as Reflexive
import DASHI.Economics.ReflexiveFlowValidationExact as Econ
import DASHI.Governance.KnowledgeProcessingCaptureSourceAtlas20261101Exact as Sources

data Issuer : Set where
  microsoft alphabet amazon meta oracle : Issuer

data MeasureKind : Set where
  spreadOASSeptember30 cdsOctober21 issuedBroadEarlyOctober
    issuedIndexEligibleOctober2 outstandingAugust : MeasureKind

record IndexedMarketMeasure : Set where
  constructor indexedMarketMeasure
  field
    kind : MeasureKind
    date : String
    scope : String
    unit : String
    source : String
    pointInTimeNotCurrentRealTime : Bool
open IndexedMarketMeasure public

oasRecord : IndexedMarketMeasure
oasRecord = indexedMarketMeasure
  spreadOASSeptember30 "2026-09-30"
  "5 FTSE USBIG corporate index issuers, original Table 2"
  "basis points"
  "LSEG FTSE Russell 2026-10-29, Table 2"
  true

issuerOAS : Issuer → Nat
issuerOAS microsoft = 54
issuerOAS alphabet = 74
issuerOAS amazon = 75
issuerOAS meta = 123
issuerOAS oracle = 210

oracleMicrosoftPremium156 :
  issuerOAS oracle ≡ issuerOAS microsoft + 156
oracleMicrosoftPremium156 = refl

oracleMetaPremium87 :
  issuerOAS oracle ≡ issuerOAS meta + 87
oracleMetaPremium87 = refl

hyperscalerGroupOAS : Nat
hyperscalerGroupOAS = 119

broadIndexOAS : Nat
broadIndexOAS = 86

hyperscalerGroupPremium33 :
  hyperscalerGroupOAS ≡ broadIndexOAS + 33
hyperscalerGroupPremium33 = refl

-- No zero-filled missing CDS observations: only the three acquired
-- issuer-price records inhabit this indexed family.
data CDSObserved : Issuer → Nat → Set where
  microsoftOct21 : CDSObserved microsoft 56
  amazonOct21 : CDSObserved amazon 80
  oracleOct21 : CDSObserved oracle 331

oracleCDS : Nat
oracleCDS = 331

amazonCDS : Nat
amazonCDS = 80

microsoftCDS : Nat
microsoftCDS = 56

oracleCDSReceipt : CDSObserved oracle oracleCDS
oracleCDSReceipt = oracleOct21

oracleCdsVsAmazon251 :
  oracleCDS ≡ amazonCDS + 251
oracleCdsVsAmazon251 = refl

-- Fixed-point tenths of USD billions to avoid rounding and accidental
-- comparisons of otherwise incommensurable quantities.
igBroadIssued2026Tenths : Nat
igBroadIssued2026Tenths = 2181

igBroadIssued2025Tenths : Nat
igBroadIssued2025Tenths = 1073

broadIssuanceMoreThanDoubleWitness :
  igBroadIssued2026Tenths
  ≡ igBroadIssued2025Tenths + igBroadIssued2025Tenths + 35
broadIssuanceMoreThanDoubleWitness = refl

usdIndexEligible2026Tenths : Nat
usdIndexEligible2026Tenths = 1518

data BroadIssuanceSameAsIndexEligible : Set where
broadAndIndexEligibleAreDifferentObjects :
  BroadIssuanceSameAsIndexEligible → ⊥
broadAndIndexEligibleAreDifferentObjects ()

data RateAction : Set where
  raise25BasisPoints holdRate : RateAction

data FomcMeeting : Set where
  september16_2026 october28_2026 : FomcMeeting

fomcAction : FomcMeeting → RateAction
fomcAction september16_2026 = raise25BasisPoints
fomcAction october28_2026 = holdRate

septemberDidHike :
  fomcAction september16_2026 ≡ raise25BasisPoints
septemberDidHike = refl

octoberDidNotHike :
  fomcAction october28_2026 ≡ holdRate
octoberDidNotHike = refl

data OctoberFedHikeClaim : Set where
octoberHikeWrongType : OctoberFedHikeClaim → ⊥
octoberHikeWrongType ()

record MarketRiskResidual : Set where
  constructor marketRiskResidual
  field
    marketSpreadDifferentiationObserved : Bool
    cohortSpreadWideToBenchmarkObserved : Bool
    broadIssuedMoreThan2025TwiceObserved : Bool
    actualLabDefaultObservedByTheseSeries : Bool
    publicRescueObservedByTheseSeries : Bool
    regulatoryCaptureCausallyIdentifiedBySpreads : Bool
    sharedModelControlRightsObservedBySpreads : Bool
    dateAndPopulationAlignmentRequired : Bool
open MarketRiskResidual public

calibratedLSEGRiskSurface : MarketRiskResidual
calibratedLSEGRiskSurface =
  marketRiskResidual
    true true true
    false false false false true

-- Higher credit spreads can reflect issuer credit risk, prospective capex,
-- index supply, duration, liquidity, hedging and benchmark composition.
-- A CDS-derived risk-neutral default probability is not real-world frequency.

data CreditSpreadProvesBailout : Set where
data CreditSpreadProvesRiggedSafetyPolicy : Set where

spreadCannotPromoteBailout : CreditSpreadProvesBailout → ⊥
spreadCannotPromoteBailout ()

spreadCannotPromoteCaptureMotive :
  CreditSpreadProvesRiggedSafetyPolicy → ⊥
spreadCannotPromoteCaptureMotive ()

financingOriginalOwner :
  Econ.MarkedGainImpliesExternalCashPermission → ⊥
financingOriginalOwner =
  Reflexive.markedGainDoesNotCloseExternalCash

-- Better to use explicit Econ import instead of an inferred module alias.
sourceReference : Sources.SourceReceipt
sourceReference = Sources.rbaOct2026FinancialStability

marketAuditStatement : String
marketAuditStatement =
  "LSEG 2026-10-29: debt issuance and outstanding are different entities/dates; 2026-09-30 Microsoft/Alphabet/Amazon/Meta/Oracle OAS = 54/74/75/123/210 bp, group 119 vs benchmark 86, Oracle CDS 331 on 2026-10-21. FOMC hiked 2026-09-16 but held 2026-10-28. Credit market observes differential risk; this is not proof of sovereign capture or bailout."
