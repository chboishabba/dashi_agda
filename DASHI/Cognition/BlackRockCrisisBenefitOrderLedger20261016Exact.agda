module DASHI.Cognition.BlackRockCrisisBenefitOrderLedger20261016Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.SystemicLeverageBeneficiaryIncidenceParetoExact as Incidence
import DASHI.Cognition.BlackRockFinkCrisisStateAdvisoryIncidence20261016Exact as Crisis

------------------------------------------------------------------------
-- BLACKROCK / 2008-2020 CRISIS BENEFIT-ORDER LEDGER — 2026-10-16
--
-- The same intervention can create differently ordered benefits for different
-- actors. Benefit order is consequence distance, not motive, culpability or
-- authority. Direct cash, avoided loss, mark-to-market gain, option value,
-- institutional learning and later selection advantage are distinct objects.
--
-- In particular:
--   benefited != authored the crisis
--   benefited != selected oneself
--   managed assets != manager/CEO beneficial ownership
--   loss avoidance != cash transfer
--   later scale != caused by an earlier public mandate
--   asset-price support != uniform inflation benefit
------------------------------------------------------------------------

data Actor : Set where
  initialCPPInstitutions : Actor
  bankCreditorsDepositorsCounterparties : Actor
  bankCommonShareholders : Actor
  blackRockAdvisoryBusiness : Actor
  blackRockRelevantClientPortfolios : Actor
  usTreasuryPublic : Actor
  homeownersAtRisk : Actor
  workersRentersNonAssetHouseholds : Actor
  competingAssetManagers : Actor
  futurePublicCrisisInstitutions : Actor
  bankOfAmericaMerrill : Actor
  pncFinancial : Actor
  barclays : Actor

data BenefitKind : Set where
  directCapitalSupport : BenefitKind
  contractedFeeRevenue : BenefitKind
  publicPreferredReturn : BenefitKind
  homeownerModificationRelief : BenefitKind
  tailRiskLossAvoidance : BenefitKind
  markToMarketSupport : BenefitKind
  relationshipReputationCapital : BenefitKind
  institutionalLearning : BenefitKind
  scaleAndAcquisitionOption : BenefitKind
  futureSelectionProbability : BenefitKind
  modelDataOperationalAdvantage : BenefitKind
  capitalOwnershipExposure : BenefitKind
  heterogeneousAssetPriceEffect : BenefitKind

data PaymentState : Set where
  sourcePaid : PaymentState
  partiallyPaid : PaymentState
  acquisitionCandidate : PaymentState

record OrderedBenefit : Set where
  constructor ordered-benefit
  field
    actor : Actor
    order : Incidence.EffectOrder
    kind : BenefitKind
    source : String
    boundedFinding : String
    payment : PaymentState
    cashReceiptPaid : Bool
    avoidedLossPaid : Bool
    optionValuePaid : Bool
    causalAttributionPaid : Bool
open OrderedBenefit public

cppInstitutionCapital : OrderedBenefit
cppInstitutionCapital = ordered-benefit
  initialCPPInstitutions Incidence.firstOrder directCapitalSupport
  "US Treasury, 14 Oct 2008 CPP announcement"
  "Nine large financial organisations indicated subscriptions totalling USD125bn of Treasury preferred capital. This is direct institution-level capital support under government terms, not a BlackRock-selected transfer."
  sourcePaid true false false false

blackRockMaidenLaneMandate : OrderedBenefit
blackRockMaidenLaneMandate = ordered-benefit
  blackRockAdvisoryBusiness Incidence.firstOrder contractedFeeRevenue
  "Federal Reserve Bank of New York Maiden Lane vendor/transaction records"
  "BlackRock Financial Management was retained for advisory and day-to-day investment-management functions across Maiden Lane crisis vehicles. Contract existence and implementation role are paid; exact all-in fee incidence remains a separate acquisition object."
  sourcePaid true false false false

publicPreferredAndResidual : OrderedBenefit
publicPreferredAndResidual = ordered-benefit
  usTreasuryPublic Incidence.firstOrder publicPreferredReturn
  "Treasury CPP terms; Federal Reserve Bank of New York Maiden Lane repayment records"
  "CPP preferred securities carried dividends and taxpayer-protection terms; Maiden Lane vehicles used explicit repayment waterfalls and some portfolios generated residual public gains. Public intervention therefore cannot be represented as a one-way gift ledger."
  sourcePaid true false false false

homeownerReliefLater : OrderedBenefit
homeownerReliefLater = ordered-benefit
  homeownersAtRisk Incidence.firstOrder homeownerModificationRelief
  "Treasury/GAO TARP housing-program records"
  "HAMP/Hardest Hit and related TARP housing programmes supplied real foreclosure-mitigation assistance, but later timing, lower scale and incomplete reach remain distributional coordinates rather than evidence that no programme existed."
  sourcePaid true false false false

creditorTailRisk : OrderedBenefit
creditorTailRisk = ordered-benefit
  bankCreditorsDepositorsCounterparties Incidence.secondOrder tailRiskLossAvoidance
  "Treasury/Federal Reserve systemic-stability programme rationale"
  "Stabilising systemically important institutions can reduce default, run and counterparty tail risk for creditors, depositors and counterparties. Exact beneficiary magnitude depends on claim seniority, guarantees and exposure and is not yet fully allocated."
  partiallyPaid false true false false

shareholderAssetSupport : OrderedBenefit
shareholderAssetSupport = ordered-benefit
  bankCommonShareholders Incidence.secondOrder markToMarketSupport
  "crisis capital/liquidity and market-stability intervention surface"
  "Intervention can alter expected survival and security prices, creating mark-to-market or loss-avoidance effects for equity holders even when no cash is paid directly to them. Security-level magnitude and beneficial ownership remain open."
  acquisitionCandidate false false false false

blackRockClientAssetSupport : OrderedBenefit
blackRockClientAssetSupport = ordered-benefit
  blackRockRelevantClientPortfolios Incidence.secondOrder heterogeneousAssetPriceEffect
  "BlackRock client-asset exposure plus crisis-market intervention surface"
  "Relevant BlackRock-managed client portfolios may benefit where interventions support securities they hold. This must be resolved security-by-security; BlackRock AUM is client/fund property and does not become Larry Fink's personal wealth."
  acquisitionCandidate false false false false

blackRockInstitutionalLearning : OrderedBenefit
blackRockInstitutionalLearning = ordered-benefit
  blackRockAdvisoryBusiness Incidence.secondOrder institutionalLearning
  "2008 Maiden Lane mandates and repeated public crisis implementation history"
  "Large public crisis assignments can generate implementation experience, relationships and institutional learning. The existence of those assignments is paid; the magnitude of any later commercial/selection advantage requires separate evidence."
  partiallyPaid false false true false

postBGIScale : OrderedBenefit
postBGIScale = ordered-benefit
  blackRockAdvisoryBusiness Incidence.secondOrder scaleAndAcquisitionOption
  "BlackRock 2009 Form 10-K / Barclays Global Investors transaction"
  "At 31 Dec 2009 BlackRock reported USD3.346tn AUM, up USD2.039tn from 2008, with USD1.850tn of the increase attributed to the BGI transaction. This pays a post-crisis scale jump, not a theorem that crisis advisory mandates caused the acquisition."
  sourcePaid false false true false

boaBlackRockCapitalTopology : OrderedBenefit
boaBlackRockCapitalTopology = ordered-benefit
  bankOfAmericaMerrill Incidence.secondOrder capitalOwnershipExposure
  "BlackRock 2009 Form 10-K"
  "At year-end 2009 Merrill Lynch, then wholly owned by Bank of America, held approximately 34.2% of BlackRock capital stock while only about 3.7% of voting common stock. This is ownership topology, not proof of TARP-to-BlackRock causation."
  sourcePaid false false true false

pncBlackRockCapitalTopology : OrderedBenefit
pncBlackRockCapitalTopology = ordered-benefit
  pncFinancial Incidence.secondOrder capitalOwnershipExposure
  "BlackRock 2009 Form 10-K"
  "At year-end 2009 PNC held approximately 24.5% of BlackRock capital stock and approximately 35.2% of voting common stock. This pays reciprocal capital topology separately from BlackRock-managed holdings in PNC."
  sourcePaid false false true false

barclaysBlackRockCapitalTopology : OrderedBenefit
barclaysBlackRockCapitalTopology = ordered-benefit
  barclays Incidence.secondOrder capitalOwnershipExposure
  "BlackRock 2009 Form 10-K"
  "At year-end 2009 Barclays held approximately 19.8% of BlackRock capital stock following the BGI transaction. This is a concrete post-transaction ownership relation, not recipient-selection evidence."
  sourcePaid false false true false

repeatedMandateSelectionOption : OrderedBenefit
repeatedMandateSelectionOption = ordered-benefit
  blackRockAdvisoryBusiness Incidence.thirdOrder futureSelectionProbability
  "2008 Maiden Lane mandate lineage plus 2020 New York Fed BlackRock vendor selections"
  "BlackRock was selected again in 2020 for agency-CMBS and corporate-credit implementation based on stated expertise and operational capability. Repetition pays durable capability/reselection, but not the stronger causal claim that the 2008 mandates alone caused the 2020 selection."
  partiallyPaid false false true false

publicPrivateCapacityFeedback : OrderedBenefit
publicPrivateCapacityFeedback = ordered-benefit
  futurePublicCrisisInstitutions Incidence.thirdOrder modelDataOperationalAdvantage
  "cross-period crisis implementation lineage"
  "Repeated delegation can create a feedback loop in which private implementation capability becomes useful public crisis infrastructure while public institutions rely on that capability. Whether this crowds out public or competing private capacity is an empirical acquisition question."
  acquisitionCandidate false false true false

nonAssetHouseholdBurden : OrderedBenefit
nonAssetHouseholdBurden = ordered-benefit
  workersRentersNonAssetHouseholds Incidence.thirdOrder heterogeneousAssetPriceEffect
  "distributional-incidence hypothesis"
  "Asset-price stabilisation, unemployment, housing costs, deleveraging and later inflation can affect non-asset households differently. 'Inflation benefits asset holders' is not a uniform theorem: asset class, leverage, nominal liabilities, interest rates and timing matter."
  acquisitionCandidate false false false false

allOrderedBenefits : List OrderedBenefit
allOrderedBenefits =
  cppInstitutionCapital
  ∷ blackRockMaidenLaneMandate
  ∷ publicPreferredAndResidual
  ∷ homeownerReliefLater
  ∷ creditorTailRisk
  ∷ shareholderAssetSupport
  ∷ blackRockClientAssetSupport
  ∷ blackRockInstitutionalLearning
  ∷ postBGIScale
  ∷ boaBlackRockCapitalTopology
  ∷ pncBlackRockCapitalTopology
  ∷ barclaysBlackRockCapitalTopology
  ∷ repeatedMandateSelectionOption
  ∷ publicPrivateCapacityFeedback
  ∷ nonAssetHouseholdBurden
  ∷ []

------------------------------------------------------------------------
-- Non-collapse boundaries.
------------------------------------------------------------------------

data BenefitImpliesCrisisAuthorship : Set where
data BenefitImpliesSelfSelection : Set where
data ManagedExposureImpliesManagerOwnership : Set where
data PublicMandateImpliesLaterAcquisitionCausation : Set where
data RepeatedSelectionImpliesCapture : Set where
data AssetPriceSupportImpliesUniformInflationGain : Set where
data AvoidedLossImpliesCashReceipt : Set where

benefitDoesNotCreateCrisisAuthorship : BenefitImpliesCrisisAuthorship → ⊥
benefitDoesNotCreateCrisisAuthorship ()

benefitDoesNotCreateSelfSelection : BenefitImpliesSelfSelection → ⊥
benefitDoesNotCreateSelfSelection ()

managedExposureDoesNotCreateManagerOwnership : ManagedExposureImpliesManagerOwnership → ⊥
managedExposureDoesNotCreateManagerOwnership ()

mandateDoesNotCreateAcquisitionCausation : PublicMandateImpliesLaterAcquisitionCausation → ⊥
mandateDoesNotCreateAcquisitionCausation ()

repeatedSelectionDoesNotCreateCapture : RepeatedSelectionImpliesCapture → ⊥
repeatedSelectionDoesNotCreateCapture ()

assetSupportDoesNotCreateUniformInflationGain : AssetPriceSupportImpliesUniformInflationGain → ⊥
assetSupportDoesNotCreateUniformInflationGain ()

avoidedLossDoesNotCreateCashReceipt : AvoidedLossImpliesCashReceipt → ⊥
avoidedLossDoesNotCreateCashReceipt ()

------------------------------------------------------------------------
-- Refined E1 / E2 / E3 acquisition frontier.
------------------------------------------------------------------------

data BenefitDebt : Set where
  cppSecurityHolderIncidence : BenefitDebt
  nineInstitutionBlackRockExposure : BenefitDebt
  maidenLaneFeesAndClientConflicts : BenefitDebt
  homeownerVersusInstitutionTemporalLedger : BenefitDebt
  crisisToBGIFlowCausationBoundary : BenefitDebt
  mandateLearningAndReselectionMechanism : BenefitDebt
  fed2020SecurityLevelBeneficiaries : BenefitDebt
  publicPrivateCapacityConcentration : BenefitDebt

record BenefitAcquisition : Set where
  constructor benefit-acquisition
  field
    debt : BenefitDebt
    priority : Nat
    order : Incidence.EffectOrder
    instruction : String
open BenefitAcquisition public

canonicalBenefitAcquisition : List BenefitAcquisition
canonicalBenefitAcquisition =
  benefit-acquisition cppSecurityHolderIncidence 100 Incidence.secondOrder
    "For each initial CPP institution, resolve common equity, preferred, bonds, CDS/counterparty and depositor claims at announcement date and measure cash versus loss-avoidance versus mark-to-market benefit by beneficial owner." ∷
  benefit-acquisition nineInstitutionBlackRockExposure 100 Incidence.secondOrder
    "Resolve BlackRock-managed fund holdings and Larry Fink personal beneficial ownership separately across all nine initial institutions; do not convert manager AUM into personal ownership or selection causation." ∷
  benefit-acquisition homeownerVersusInstitutionTemporalLedger 100 Incidence.secondOrder
    "Put October-2008 institution support and 2009-onward homeowner programmes on one timing/obligation/disbursement/reach/loss-avoidance ledger so delayed relief and unequal reach are measured rather than rhetorically collapsed." ∷
  benefit-acquisition maidenLaneFeesAndClientConflicts 99 Incidence.firstOrder
    "Acquire BlackRock Maiden Lane fee letters, contemporaneous client exposures and conflict controls to quantify direct contractual gain and any same-security conflict surface." ∷
  benefit-acquisition mandateLearningAndReselectionMechanism 99 Incidence.thirdOrder
    "Join 2008 and 2020 mandates by staff, model/data assets, procurement rationale and capability lineage to test whether public crisis work produced a measurable later selection advantage without assuming capture." ∷
  benefit-acquisition fed2020SecurityLevelBeneficiaries 99 Incidence.secondOrder
    "Use CUSIP-level Fed purchase data and beneficial-ownership snapshots to identify who received direct sale proceeds, spread compression or mark-to-market benefit in 2020; separate this from generalized inflation claims." ∷
  benefit-acquisition publicPrivateCapacityConcentration 98 Incidence.thirdOrder
    "Measure whether repeated outsourcing changed public internal capability, competing-manager market access, model/data ownership or switching costs; repeated mandate is not itself proof of capture." ∷
  benefit-acquisition crisisToBGIFlowCausationBoundary 97 Incidence.thirdOrder
    "Keep the paid 2009 BGI scale jump and ownership topology separate from any claim that 2008 public mandates caused BlackRock's acquisition, fundraising or client flows unless same-object causal evidence is acquired."
  ∷ []
