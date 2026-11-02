module DASHI.Biology.BH4ExchangeIdentifiabilityExact where

open import DASHI.Core.Prelude

import DASHI.Biology.BH4JointFluxFeasibilityExact as Flux
import DASHI.Biology.BH4OpenMetabolicNetworkAdapterExact as Open
import DASHI.Biology.Cell.MetabolicOpenSystemBalance as MetabolicBalance
import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- UNRESTRICTED EXCHANGE / NO IDENTIFIABILITY
--
-- Any internal signed stoichiometric total s = S*v can be cancelled
-- by a free exchange e = -s if exchange is unrestricted.
--
-- This is an *abstract additive-group* theorem, not an assertion that
-- any particular tissue allows the required exchange. In the actual
-- BH4 network the 29 exchange bounds and all physical context gates
-- must come from matched evidence. Exactly satisfying S*v+e=0 with
-- invented exchanges proves no simultaneous BH4 allocation hypothesis.
------------------------------------------------------------------------

record ExchangeCancellation (A : Set) : Set where
  field
    zero : A
    _⊕_ : A → A → A
    inverse : A → A
    rightInverse : (s : A) → _⊕_ s (inverse s) ≡ zero

open ExchangeCancellation public

unrestrictedExchangeBalance :
  ∀ {A : Set} →
  (C : ExchangeCancellation A) →
  (internalTotal : A) →
  Σ A (λ exchange → _⊕_ C internalTotal exchange ≡ zero C)
unrestrictedExchangeBalance C s =
  inverse C s , rightInverse C s

unrestrictedExchangeIsNotPhysicalEvidence :
  ∀ {A : Set} →
  (C : ExchangeCancellation A) →
  (s : A) →
  Σ A (λ e → _⊕_ C s e ≡ zero C)
unrestrictedExchangeIsNotPhysicalEvidence = unrestrictedExchangeBalance

-- Existing owners remain responsible for physical same-state balance
-- and context-indexed feasibility, not this abstract existence result.
existingMetabolicOpenBalanceOwner : Set₁
existingMetabolicOpenBalanceOwner = MetabolicBalance.MetabolicOpenBalanceBridge

existingFluxFeasibilityStatus : Set
existingFluxFeasibilityStatus = Flux.FluxFeasibilityStatus

existingBH4OpenExchangeKind : Set
existingBH4OpenExchangeKind = Open.BH4ExchangeKind

record ExchangeIdentifiabilityBoundary : Set where
  constructor exchange-identifiability-boundary
  field
    inventedExchangePaysMeasuredFlux : Bool
    inventedExchangePaysMeasuredFluxIsFalse :
      inventedExchangePaysMeasuredFlux ≡ false
    unrestrictedExchangeBalanceProvesJointDemandFeasible : Bool
    unrestrictedExchangeBalanceProvesJointDemandFeasibleIsFalse :
      unrestrictedExchangeBalanceProvesJointDemandFeasible ≡ false
    syntheticExchangeProvesSameCellCompartment : Bool
    syntheticExchangeProvesSameCellCompartmentIsFalse :
      syntheticExchangeProvesSameCellCompartment ≡ false
    numericCandidateIsExactRealWorldEquality : Bool
    numericCandidateIsExactRealWorldEqualityIsFalse :
      numericCandidateIsExactRealWorldEquality ≡ false

canonicalExchangeIdentifiabilityBoundary : ExchangeIdentifiabilityBoundary
canonicalExchangeIdentifiabilityBoundary =
  exchange-identifiability-boundary
    false refl false refl false refl false refl false refl

canonicalExchangeIdentifiabilityReceipt : Receipt.GenericReceipt
canonicalExchangeIdentifiabilityReceipt =
  Receipt.mkNonPromotingReceipt
    "BH4 unrestricted-exchange identifiability cut"
    "DASHI.Biology.BH4ExchangeIdentifiabilityExact"
    "abstract additive cancellation: any internal S*v has an e=-S*v if every exchange coordinate is unconstrained"
    "source-written parameterized existence proof; companion exact integer witness verifies cancellation on bounded matrices without a physical cell claim"
    "unrestricted exchange cannot certify simultaneous biological demand or enzyme allocation, and must not be used to mark 29 external rates as paid"
    "python3 scripts/check_bh4_exchange_identifiability.py"
