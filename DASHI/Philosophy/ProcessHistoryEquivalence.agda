module DASHI.Philosophy.ProcessHistoryEquivalence where

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Equality using (_≡_)

------------------------------------------------------------------------
-- Equal endpoints do not erase different histories.

record HistoricalProcess
       (State History Residual Authority : Set) : Set₁ where
  field
    start : State
    finish : State
    history : History
    residual : Residual
    authority : Authority

open HistoricalProcess public

record EndpointEquivalent
       {State History Residual Authority : Set}
       (p q : HistoricalProcess State History Residual Authority) : Set₁ where
  field
    sameStart : start p ≡ start q
    sameFinish : finish p ≡ finish q

open EndpointEquivalent public

record ProcessEquivalent
       {State History Residual Authority : Set}
       (p q : HistoricalProcess State History Residual Authority) : Set₁ where
  field
    endpoints : EndpointEquivalent p q
    historyTranslation : Set
    residualCompatibility : Set
    authorityCompatibility : Set

open ProcessEquivalent public

record ProcessIdentityBoundary : Set where
  field
    endpointEqualityImpliesProcessIdentity : Set
    processEquivalenceImpliesLiteralEquality : Set
    distinctHistoriesRemainVisible : Set

record SameEndpointDifferentHistory
       {State History Residual Authority : Set}
       (p q : HistoricalProcess State History Residual Authority) : Set₁ where
  field
    endpointsEqual : EndpointEquivalent p q
    historiesDistinguished : Set
    injuryDifferenceTracked : Set
    repairDifferenceTracked : Set
    authorityDifferenceTracked : Set

open SameEndpointDifferentHistory public
