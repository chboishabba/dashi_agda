module DASHI.Finance.TrumpFamilyTradeAcquisitionProgressRound4Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Finance.TrumpFamilyTradeAcquisitionProgressRound3Exact as Prior
import DASHI.Finance.TrumpFamilyTradePrimarySourceRound2Exact as Primary2
import DASHI.Finance.TrumpFamilyTradeSourceQualityRound4Exact as Quality4
import DASHI.Finance.TrumpFamilyPolicyMarketSourceAtlasExact as Policy
import DASHI.Finance.TruthAPISourceRoleTriangulationExact as TruthTriad
import DASHI.Finance.TrumpFamilyTradeSourceAtlasExact as Atlas

------------------------------------------------------------------------
-- ROUND-FOUR ACQUISITION PROGRESS
--
-- This round pays exact transaction-mechanism and policy-market triangulation
-- coordinates. It does not close the broader lane: decision-maker, ultimate
-- funding source, advance knowledge, policy influence, realized policy-derived
-- benefit, customer identity/contract terms, and causal market effects remain
-- explicit residual debt unless separately acquired.
------------------------------------------------------------------------

record TrumpFamilyTradeAcquisitionProgressRound4 : Set where
  constructor trump-family-trade-acquisition-progress-round4
  field
    priorProgress : Prior.TrumpFamilyTradeAcquisitionProgressRound3

    ericABTCTrustTransferPrimaryObserved : Bool
    ericABTCCashPurchasePrimaryObserved : Bool
    ericABTCCashPurchaseIndependentNarrowCorroborationObserved : Bool
    donJrPSQHPaidPurchasePrimaryObserved : Bool

    grabAGunPolicyPrimaryObserved : Bool
    grabAGunIndependentExposureAndCounterevidenceObserved : Bool
    truthAPICanonicalThreeRoleTriangulationRetained : Bool
    truthAPIIndependentCommercialTermsReportingObserved : Bool

    ericABTCUltimateFundingSourceDebtStillLive : Bool
    transactionDecisionMakerDebtStillLive : Bool
    grabAGunAdvanceKnowledgeDebtStillLive : Bool
    grabAGunPolicyInfluenceDebtStillLive : Bool
    grabAGunRealizedBenefitDebtStillLive : Bool
    truthAPICustomerIdentityDebtStillLive : Bool
    truthAPIContractTermsDebtStillLive : Bool
    marketCausationDebtStillLive : Bool

open TrumpFamilyTradeAcquisitionProgressRound4 public

currentTrumpFamilyTradeAcquisitionProgressRound4 :
  TrumpFamilyTradeAcquisitionProgressRound4
currentTrumpFamilyTradeAcquisitionProgressRound4 =
  trump-family-trade-acquisition-progress-round4
    Prior.currentTrumpFamilyTradeAcquisitionProgressRound3
    true true true true
    true true true true
    true true true true true true true true

ericCashPurchaseIndependentCorroboration : Atlas.TradeEvidenceClaim
ericCashPurchaseIndependentCorroboration =
  Quality4.ericCashPurchaseIndependentCorroboration

ericCashPurchasePrimaryPaid :
  Atlas.primarySourcePaid Primary2.ericAmericanBitcoinCashPurchase ≡ true
ericCashPurchasePrimaryPaid = refl

ericCashPurchaseIndependentPaid :
  Atlas.independentCorroborationPaid ericCashPurchaseIndependentCorroboration ≡ true
ericCashPurchaseIndependentPaid = refl

grabAGunPolicyPrimaryPaid :
  Policy.primarySourcePaid Policy.grabAGunATFNonOTCProposal ≡ true
grabAGunPolicyPrimaryPaid = refl

grabAGunIndependentPaid :
  Policy.independentCorroborationPaid Policy.grabAGunReutersPolicyExposure ≡ true
grabAGunIndependentPaid = refl

truthAPICanonicalTriangulationStillAvailable :
  TruthTriad.TruthAPITriangulatedEvidence
truthAPICanonicalTriangulationStillAvailable =
  TruthTriad.canonicalTruthAPITriangulation

------------------------------------------------------------------------
-- Residual locality.
------------------------------------------------------------------------

data NarrowCorroborationAutomaticallyClosesFundingSourceDebt : Set where
data PolicyExposureAutomaticallyClosesKnowledgeDebt : Set where
data PolicyExposureAutomaticallyClosesInfluenceDebt : Set where
data TriangulationAutomaticallyClosesLegalMerits : Set where

narrowCorroborationDoesNotCloseFundingSource :
  NarrowCorroborationAutomaticallyClosesFundingSourceDebt → ⊥
narrowCorroborationDoesNotCloseFundingSource ()

policyExposureDoesNotCloseKnowledge :
  PolicyExposureAutomaticallyClosesKnowledgeDebt → ⊥
policyExposureDoesNotCloseKnowledge ()

policyExposureDoesNotCloseInfluence :
  PolicyExposureAutomaticallyClosesInfluenceDebt → ⊥
policyExposureDoesNotCloseInfluence ()

triangulationDoesNotCloseLegalMerits :
  TriangulationAutomaticallyClosesLegalMerits → ⊥
triangulationDoesNotCloseLegalMerits ()

record AcquisitionProgressRound4Boundary : Set where
  constructor acquisition-progress-round4-boundary
  field
    transactionMechanismDebtReduced : Bool
    ericCashPurchaseHasPrimaryAndIndependentNarrowSupport : Bool
    grabAGunHasPrimaryPolicyAndIndependentExposureSources : Bool
    truthAPICanonicalTriangulationReused : Bool
    fundingKnowledgeInfluenceAndCausationDebtRemainExplicit : Bool
    acquisitionProgressDoesNotCreateTradeAuthority : Bool

canonicalAcquisitionProgressRound4Boundary : AcquisitionProgressRound4Boundary
canonicalAcquisitionProgressRound4Boundary =
  acquisition-progress-round4-boundary true true true true true true
