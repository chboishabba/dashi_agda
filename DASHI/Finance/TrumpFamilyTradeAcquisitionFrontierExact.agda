module DASHI.Finance.TrumpFamilyTradeAcquisitionFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Choice
import DASHI.Core.ExpectedFibreReductionCostExact as Reduction
import DASHI.Core.LiveSetParetoExperimentSchedulerExact as Live
import DASHI.Governance.ResidualIndexedEvidenceSchedulerExact as Scheduler
import DASHI.Governance.QuotientDefectResidualRouting as Residual

------------------------------------------------------------------------
-- SOURCE ACQUISITION FRONTIER FOR THE TRUMP-FAMILY TRADE LANE
--
-- This is deliberately an acquisition/search chart, not an accusation score.
-- It encodes the outstanding evidentiary work identified by the source atlas:
-- page-level annual-disclosure payment, fuller SEC event recovery, independent
-- corroboration, Truth-API contract/customer evidence, and market-timing data.
------------------------------------------------------------------------

data AcquisitionMove : Set where
  acquireAnnualDisclosurePages : AcquisitionMove
  acquireAdditionalSECFilings : AcquisitionMove
  acquireIndependentCorroboration : AcquisitionMove
  acquireTruthAPIContractEvidence : AcquisitionMove
  acquireMarketTimingEvidence : AcquisitionMove

moveReference : AcquisitionMove → String
moveReference acquireAnnualDisclosurePages =
  "page-level extraction from President Trump's certified 2026 annual financial disclosure"
moveReference acquireAdditionalSECFilings =
  "additional SEC Form 4 / Schedule 13D-G event-level recovery for Trump-family public-company interests"
moveReference acquireIndependentCorroboration =
  "independent reporting/court/regulatory corroboration for high-impact claims"
moveReference acquireTruthAPIContractEvidence =
  "Truth API customer/contract/latency evidence beyond issuer marketing statements"
moveReference acquireMarketTimingEvidence =
  "timestamped policy/post/market/trade observations for temporal analysis without causal promotion"

informationMove : AcquisitionMove → Choice.InformationMove
informationMove acquireAnnualDisclosurePages =
  Choice.informationMove Choice.takeMeasurement 2
    "extract annual-disclosure pages" "OGE certified annual report" "public disclosure authority"
informationMove acquireAdditionalSECFilings =
  Choice.informationMove Choice.takeMeasurement 2
    "recover SEC ownership-event filings" "SEC EDGAR" "primary securities filing authority"
informationMove acquireIndependentCorroboration =
  Choice.informationMove Choice.replicateMeasurement 3
    "independent corroboration" "independent reporting/regulatory record" "source diversity requirement"
informationMove acquireTruthAPIContractEvidence =
  Choice.informationMove Choice.increaseFidelity 4
    "recover Truth API contract/customer details" "TMTG/customer records" "currently unpaid contract-level authority"
informationMove acquireMarketTimingEvidence =
  Choice.informationMove Choice.increaseFidelity 4
    "build exact timestamped market-event sequence" "market/source timestamps" "timing is not causation"

reductionEnvelope : AcquisitionMove → Reduction.ReductionEnvelope
reductionEnvelope acquireAnnualDisclosurePages =
  Reduction.reductionEnvelope 2 4 "pays multiple component financial-disclosure claims"
reductionEnvelope acquireAdditionalSECFilings =
  Reduction.reductionEnvelope 2 5 "resolves ownership/transaction identity edges"
reductionEnvelope acquireIndependentCorroboration =
  Reduction.reductionEnvelope 1 4 "reduces single-source dependence"
reductionEnvelope acquireTruthAPIContractEvidence =
  Reduction.reductionEnvelope 1 5 "may separate issuer-marketing claims from realized customer access"
reductionEnvelope acquireMarketTimingEvidence =
  Reduction.reductionEnvelope 1 5 "may separate temporal coincidence from finer event ordering"

candidate : AcquisitionMove → Reduction.FibreReductionCostCandidate
candidate move =
  Reduction.fibreReductionCostCandidate
    (informationMove move)
    (reductionEnvelope move)
    true
    true
    (moveReference move)

liveProblem : Live.LiveExperimentProblem
liveProblem =
  Live.liveExperimentProblem AcquisitionMove candidate survivalPenalty moveReference
  where
    survivalPenalty : AcquisitionMove → Nat
    survivalPenalty acquireAnnualDisclosurePages = 2
    survivalPenalty acquireAdditionalSECFilings = 2
    survivalPenalty acquireIndependentCorroboration = 3
    survivalPenalty acquireTruthAPIContractEvidence = 4
    survivalPenalty acquireMarketTimingEvidence = 4

unpaidProvenance : AcquisitionMove → Nat
unpaidProvenance acquireAnnualDisclosurePages = 1
unpaidProvenance acquireAdditionalSECFilings = 1
unpaidProvenance acquireIndependentCorroboration = 2
unpaidProvenance acquireTruthAPIContractEvidence = 4
unpaidProvenance acquireMarketTimingEvidence = 3

redundantCoordinates : AcquisitionMove → Nat
redundantCoordinates acquireAnnualDisclosurePages = 0
redundantCoordinates acquireAdditionalSECFilings = 1
redundantCoordinates acquireIndependentCorroboration = 1
redundantCoordinates acquireTruthAPIContractEvidence = 0
redundantCoordinates acquireMarketTimingEvidence = 1

remainingGap : AcquisitionMove → Nat
remainingGap acquireAnnualDisclosurePages = 2
remainingGap acquireAdditionalSECFilings = 2
remainingGap acquireIndependentCorroboration = 3
remainingGap acquireTruthAPIContractEvidence = 1
remainingGap acquireMarketTimingEvidence = 1

targetsResidual : AcquisitionMove → Residual.ResidualKind → Bool
targetsResidual acquireAnnualDisclosurePages Residual.authority = true
targetsResidual acquireAnnualDisclosurePages Residual.historical = true
targetsResidual acquireAdditionalSECFilings Residual.identity = true
targetsResidual acquireAdditionalSECFilings Residual.authority = true
targetsResidual acquireIndependentCorroboration Residual.counterevidence = true
targetsResidual acquireIndependentCorroboration Residual.authority = true
targetsResidual acquireTruthAPIContractEvidence Residual.causal = true
targetsResidual acquireTruthAPIContractEvidence Residual.counterevidence = true
targetsResidual acquireMarketTimingEvidence Residual.causal = true
targetsResidual acquireMarketTimingEvidence Residual.historical = true
targetsResidual _ _ = false

residualUnresolved : Residual.ResidualKind → Bool
residualUnresolved Residual.historical = true
residualUnresolved Residual.causal = true
residualUnresolved Residual.identity = true
residualUnresolved Residual.authority = true
residualUnresolved Residual.counterevidence = true
residualUnresolved Residual.trauma = false

acquisitionProblem : Scheduler.ResidualEvidenceProblem
acquisitionProblem =
  Scheduler.residualEvidenceProblem
    liveProblem
    unpaidProvenance
    redundantCoordinates
    remainingGap
    targetsResidual
    residualUnresolved
    moveReference

annualPagesAdmitted : Live.Admitted liveProblem acquireAnnualDisclosurePages
annualPagesAdmitted = refl , refl

secFilingsAdmitted : Live.Admitted liveProblem acquireAdditionalSECFilings
secFilingsAdmitted = refl , refl

truthAPIContractTargetsCausalResidual :
  targetsResidual acquireTruthAPIContractEvidence Residual.causal ≡ true
truthAPIContractTargetsCausalResidual = refl

marketTimingDoesNotTargetTraumaResidual :
  targetsResidual acquireMarketTimingEvidence Residual.trauma ≡ false
marketTimingDoesNotTargetTraumaResidual = refl

------------------------------------------------------------------------
-- No source-acquisition action is itself evidence.  The scheduler chooses what
-- to seek; promotion remains downstream of the actually acquired artifact.
------------------------------------------------------------------------

data ScheduledAcquisitionAutomaticallyPaysClaim : Set where
data LowerAcquisitionCostMeansMoreTruth : Set where
data TimingAcquisitionAutomaticallyProvesCausation : Set where

scheduledMoveDoesNotPayClaim : ScheduledAcquisitionAutomaticallyPaysClaim → ⊥
scheduledMoveDoesNotPayClaim ()

lowerCostDoesNotMeanMoreTruth : LowerAcquisitionCostMeansMoreTruth → ⊥
lowerCostDoesNotMeanMoreTruth ()

timingAcquisitionDoesNotProveCausation : TimingAcquisitionAutomaticallyProvesCausation → ⊥
timingAcquisitionDoesNotProveCausation ()

record TrumpFamilyTradeAcquisitionBoundary : Set where
  constructor trump-family-trade-acquisition-boundary
  field
    sourceDebtIsResidualIndexed : Bool
    annualDisclosurePageDebtRemainsLive : Bool
    secEventIdentityDebtRemainsLive : Bool
    truthAPIContractDebtRemainsLive : Bool
    marketTimingDebtRemainsLive : Bool
    acquisitionMoveIsNotEvidence : Bool
    acquisitionCostIsNotTruthScore : Bool
    traumaResidualIsNotUsedForThisFinancialAcquisition : Bool

canonicalTrumpFamilyTradeAcquisitionBoundary : TrumpFamilyTradeAcquisitionBoundary
canonicalTrumpFamilyTradeAcquisitionBoundary =
  trump-family-trade-acquisition-boundary true true true true true true true true
