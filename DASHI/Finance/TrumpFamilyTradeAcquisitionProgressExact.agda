module DASHI.Finance.TrumpFamilyTradeAcquisitionProgressExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Finance.TrumpFamilyTradeAcquisitionFrontierExact as Frontier
import DASHI.Finance.TrumpFamilyTradePrimarySourceRound2Exact as Primary2
import DASHI.Finance.TrumpFamilyExternalCounterpartyPrimaryExact as CounterpartyPrimary
import DASHI.Governance.QuotientDefectResidualRouting as Residual

------------------------------------------------------------------------
-- ACQUISITION PROGRESS
--
-- Acquiring one or more high-value receipts does not close an acquisition lane
-- globally.  This record distinguishes paid coordinates from residual debt.
------------------------------------------------------------------------

record TrumpFamilyTradeAcquisitionProgress : Set where
  constructor trump-family-trade-acquisition-progress
  field
    annualDisclosurePageLevelPaymentObserved : Bool
    secEventLevelPaymentObserved : Bool
    externalCounterpartyPrimaryPaymentObserved : Bool
    independentCorroborationStillLive : Bool
    truthAPIContractCustomerDebtStillLive : Bool
    marketTimingCausalityDebtStillLive : Bool
    decisionMakerIdentityDebtStillLive : Bool
    policyCausationDebtStillLive : Bool

open TrumpFamilyTradeAcquisitionProgress public

currentTrumpFamilyTradeAcquisitionProgress : TrumpFamilyTradeAcquisitionProgress
currentTrumpFamilyTradeAcquisitionProgress =
  trump-family-trade-acquisition-progress
    true
    true
    true
    true
    true
    true
    true
    true

annualPagePaymentWitness :
  Frontier.targetsResidual Frontier.acquireAnnualDisclosurePages Residual.authority ≡ true
annualPagePaymentWitness = refl

------------------------------------------------------------------------
-- The new receipts pay concrete obligations but preserve the distinction
-- between transaction evidence and downstream causal/legal inference.
------------------------------------------------------------------------

data AcquiredReceiptAutomaticallyClosesLane : Set where
data PrimaryTransactionAutomaticallyPaysCausation : Set where

receiptDoesNotCloseWholeLane : AcquiredReceiptAutomaticallyClosesLane → ⊥
receiptDoesNotCloseWholeLane ()

primaryTransactionDoesNotPayCausation : PrimaryTransactionAutomaticallyPaysCausation → ⊥
primaryTransactionDoesNotPayCausation ()

record AcquisitionProgressBoundary : Set where
  constructor acquisition-progress-boundary
  field
    paidAndUnpaidCoordinatesCoexist : Bool
    eventLevelSECReceiptsNowObserved : Bool
    ogePageLevelReceiptsNowObserved : Bool
    primaryCounterpartyReceiptNowObserved : Bool
    causalAndDecisionMakerDebtStillExplicit : Bool

canonicalAcquisitionProgressBoundary : AcquisitionProgressBoundary
canonicalAcquisitionProgressBoundary =
  acquisition-progress-boundary true true true true true
