module DASHI.Economics.AIOpenAIContractRealisationTerminalCashNonDescent20261016Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ConsumerFibreRepairExact as Repair
import DASHI.Economics.AICoreWeaveOpenAIContractRealisationCure20261016Exact as Cure

------------------------------------------------------------------------
-- COVENANT-COMPLIANCE NON-DESCENT TO TERMINAL CUSTOMER CASH
--
-- Synthetic finite witness calibrated to the filed DDTL 3.0 amendment.
-- The empirical source pays only that CRR Cure Proceeds can enter the covenant
-- numerator. DASHI owns the finite 85-vs-(80+5) logical countermodel below.
------------------------------------------------------------------------

data RealisationWorld : Set where
  customer85 : RealisationWorld
  customer80Cure5 : RealisationWorld

data CovenantObservation : Set where
  compliantAt85 : CovenantObservation

data CustomerCashOutcome : Set where
  customerAtOrAbove85 : CustomerCashOutcome
  customerBelow85 : CustomerCashOutcome

covenantObserver : RealisationWorld → CovenantObservation
covenantObserver customer85 = compliantAt85
covenantObserver customer80Cure5 = compliantAt85

customerCashConsumer : RealisationWorld → CustomerCashOutcome
customerCashConsumer customer85 = customerAtOrAbove85
customerCashConsumer customer80Cure5 = customerBelow85

sameCompliantCovenantObservation :
  covenantObserver customer85 ≡ covenantObserver customer80Cure5
sameCompliantCovenantObservation = refl

differentCustomerCashRealisation :
  customerCashConsumer customer85 ≡ customerCashConsumer customer80Cure5 → ⊥
differentCustomerCashRealisation ()

crrTerminalCashCollision :
  Descent.ConsumerNonDescentWitness covenantObserver customerCashConsumer
crrTerminalCashCollision =
  Descent.consumerNonDescentWitness
    customer85
    customer80Cure5
    refl
    (λ ())

covenantObserverCannotDetermineTerminalCash :
  Descent.ConsumerSufficient covenantObserver customerCashConsumer → ⊥
covenantObserverCannotDetermineTerminalCash =
  Descent.nonDescentWitnessBlocksSufficiency crrTerminalCashCollision

covenantComplianceDoesNotFactorTerminalCash :
  Descent.FactorsThrough covenantObserver customerCashConsumer → ⊥
covenantComplianceDoesNotFactorTerminalCash =
  Descent.nonDescentWitnessBlocksFactorization crrTerminalCashCollision

everyRepairMustSeparateCustomerCashFromEquityCure :
  ∀ {Refinement : Set}
    (refine : RealisationWorld → Refinement) →
  Repair.RefinementRepairs covenantObserver refine customerCashConsumer →
  refine customer85 ≡ refine customer80Cure5 →
  ⊥
everyRepairMustSeparateCustomerCashFromEquityCure refine repaired sameRefinement =
  Repair.refinementRepairSeparatesWitness
    crrTerminalCashCollision repaired sameRefinement

filedEquityCureMechanismPaid :
  Cure.unlimitedEquityCuresBefore20261028 Cure.coreWeaveOpenAIContractRealisationCure ≡ true
filedEquityCureMechanismPaid = Cure.unlimitedEquityCuresThrough20261027Paid

boundary : String
boundary =
  "After the DDTL 3.0 amendment, covenant Contract Realization Ratio compliance cannot by itself identify OpenAI customer cash because CRR Cure Proceeds may enter the numerator. DASHI's finite witness compares an 85-customer/0-cure state with an 80-customer/5-equity-cure state: both expose the same compliant 0.85-style covenant observation while the customer-cash consumer differs. The canonical consumer-descent theorem therefore blocks covenant compliance from factoring terminal customer-cash sufficiency. The 85/80/5 witness is a DASHI logical countermodel, not a claim that those amounts occurred in the real facility; the source-paid empirical fact is only the amendment's cure mechanism."
