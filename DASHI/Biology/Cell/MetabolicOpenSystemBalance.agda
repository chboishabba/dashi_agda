module DASHI.Biology.Cell.MetabolicOpenSystemBalance where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Analysis.StoichiometricConservation as SC
import DASHI.Analysis.OpenSystemBalance as OSB
import DASHI.Biology.Cell.OpenMetabolicNetwork as OMN
import DASHI.Biology.Cell.MetabolicStoichiometricConservation as MSC

------------------------------------------------------------------------
-- Internal reactions and environmental exchanges on one ordered event path.
--
-- Internal reaction increments are inherited from the stoichiometric system and
-- proved zero by its left-kernel certificate.  Exchange events carry explicit,
-- state-dependent increments and transitions.  The generic open-balance theorem
-- then yields the exact final quantity as initial quantity plus the ordered
-- accumulation of all event increments.
------------------------------------------------------------------------

data MetabolicBalanceEvent
    (Reaction Exchange : Set)
    : Set where
  internalReaction : Reaction → MetabolicBalanceEvent Reaction Exchange
  externalExchange : Exchange → MetabolicBalanceEvent Reaction Exchange

record MetabolicOpenBalanceBridge
    (N : OMN.OpenMetabolicNetwork)
    (S : MSC.MetabolicStoichiometricBridge N)
    : Set₁ where
  field
    Exchange : Set

    exchangeStep :
      Exchange →
      OMN.OpenMetabolicNetwork.NetworkState N →
      OMN.OpenMetabolicNetwork.NetworkState N

    exchangeIncrement :
      Exchange →
      OMN.OpenMetabolicNetwork.NetworkState N →
      MSC.Quantity S

    stoichiometricAssociative :
      (left middle right : MSC.Quantity S) →
      SC._⊕_ (SC.additive (MSC.stoichiometry S))
        (SC._⊕_ (SC.additive (MSC.stoichiometry S)) left middle)
        right
        ≡
      SC._⊕_ (SC.additive (MSC.stoichiometry S))
        left
        (SC._⊕_ (SC.additive (MSC.stoichiometry S)) middle right)

    exchangeQuantityUpdate :
      (exchange : Exchange) →
      (state : OMN.OpenMetabolicNetwork.NetworkState N) →
      SC.quantity (MSC.stoichiometry S) (exchangeStep exchange state)
        ≡
      SC._⊕_ (SC.additive (MSC.stoichiometry S))
        (SC.quantity (MSC.stoichiometry S) state)
        (exchangeIncrement exchange state)

open MetabolicOpenBalanceBridge public

metabolicBalanceAdditive :
  ∀ {N S} →
  MetabolicOpenBalanceBridge N S →
  OSB.AdditiveBalance (MSC.Quantity S)
metabolicBalanceAdditive {S = S} B = record
  { zero = SC.zero (SC.additive (MSC.stoichiometry S))
  ; _⊕_ = SC._⊕_ (SC.additive (MSC.stoichiometry S))
  ; rightIdentity = SC.rightIdentity (SC.additive (MSC.stoichiometry S))
  ; associative = stoichiometricAssociative B
  }

metabolicEventStep :
  ∀ {N S} →
  (B : MetabolicOpenBalanceBridge N S) →
  MetabolicBalanceEvent
    (OMN.OpenMetabolicNetwork.Reaction N)
    (Exchange B) →
  OMN.OpenMetabolicNetwork.NetworkState N →
  OMN.OpenMetabolicNetwork.NetworkState N
metabolicEventStep {N} {S} B (internalReaction reaction) state =
  OMN.OpenMetabolicNetwork.step N (MSC.environment S) reaction state
metabolicEventStep B (externalExchange exchange) state =
  exchangeStep B exchange state

metabolicEventIncrement :
  ∀ {N S} →
  (B : MetabolicOpenBalanceBridge N S) →
  MetabolicBalanceEvent
    (OMN.OpenMetabolicNetwork.Reaction N)
    (Exchange B) →
  OMN.OpenMetabolicNetwork.NetworkState N →
  MSC.Quantity S
metabolicEventIncrement {S = S} B (internalReaction reaction) state =
  SC.leftFunctional (MSC.stoichiometry S)
    (SC.stoichiometricColumn (MSC.stoichiometry S) reaction)
metabolicEventIncrement B (externalExchange exchange) state =
  exchangeIncrement B exchange state

internalMetabolicIncrementIsZero :
  ∀ {N S} →
  (B : MetabolicOpenBalanceBridge N S) →
  (reaction : OMN.OpenMetabolicNetwork.Reaction N) →
  (state : OMN.OpenMetabolicNetwork.NetworkState N) →
  metabolicEventIncrement B (internalReaction reaction) state
    ≡ SC.zero (SC.additive (MSC.stoichiometry S))
internalMetabolicIncrementIsZero {S = S} B reaction state =
  SC.annihilatesStoichiometry (MSC.leftKernel S) reaction

internalMetabolicQuantityUpdate :
  ∀ {N S} →
  (B : MetabolicOpenBalanceBridge N S) →
  (reaction : OMN.OpenMetabolicNetwork.Reaction N) →
  (state : OMN.OpenMetabolicNetwork.NetworkState N) →
  SC.quantity (MSC.stoichiometry S)
    (metabolicEventStep B (internalReaction reaction) state)
    ≡
  SC._⊕_ (SC.additive (MSC.stoichiometry S))
    (SC.quantity (MSC.stoichiometry S) state)
    (metabolicEventIncrement B (internalReaction reaction) state)
internalMetabolicQuantityUpdate {S = S} B reaction state =
  trans
    (sym
      (cong
        (SC.quantity (MSC.stoichiometry S))
        (MSC.stepMatchesNetwork S reaction state)))
    (SC.quantityUpdate (MSC.stoichiometry S) reaction state)

metabolicOpenBalanceSystem :
  ∀ {N S} →
  (B : MetabolicOpenBalanceBridge N S) →
  OSB.OpenBalanceSystem
    (MetabolicBalanceEvent
      (OMN.OpenMetabolicNetwork.Reaction N)
      (Exchange B))
    (OMN.OpenMetabolicNetwork.NetworkState N)
    (MSC.Quantity S)
metabolicOpenBalanceSystem {N} {S} B = record
  { additive = metabolicBalanceAdditive B
  ; quantity = SC.quantity (MSC.stoichiometry S)
  ; step = metabolicEventStep B
  ; increment = metabolicEventIncrement B
  ; quantityUpdate = update
  }
  where
  update :
    (event : MetabolicBalanceEvent
      (OMN.OpenMetabolicNetwork.Reaction N)
      (Exchange B)) →
    (state : OMN.OpenMetabolicNetwork.NetworkState N) →
    SC.quantity (MSC.stoichiometry S) (metabolicEventStep B event state)
      ≡
    SC._⊕_ (SC.additive (MSC.stoichiometry S))
      (SC.quantity (MSC.stoichiometry S) state)
      (metabolicEventIncrement B event state)
  update (internalReaction reaction) state =
    internalMetabolicQuantityUpdate B reaction state
  update (externalExchange exchange) state =
    exchangeQuantityUpdate B exchange state

record MetabolicOpenBalanceCertificate
    {N : OMN.OpenMetabolicNetwork}
    {S : MSC.MetabolicStoichiometricBridge N}
    (B : MetabolicOpenBalanceBridge N S)
    : Set₁ where
  field
    balanceCertificate :
      OSB.OpenBalanceCertificate (metabolicOpenBalanceSystem B)

    internalIncrementsVanish :
      (reaction : OMN.OpenMetabolicNetwork.Reaction N) →
      (state : OMN.OpenMetabolicNetwork.NetworkState N) →
      metabolicEventIncrement B (internalReaction reaction) state
        ≡ SC.zero (SC.additive (MSC.stoichiometry S))

open MetabolicOpenBalanceCertificate public

certifyMetabolicOpenBalance :
  ∀ {N S} →
  (B : MetabolicOpenBalanceBridge N S) →
  MetabolicOpenBalanceCertificate B
certifyMetabolicOpenBalance B = record
  { balanceCertificate =
      OSB.certifyOpenBalance (metabolicOpenBalanceSystem B)
  ; internalIncrementsVanish = internalMetabolicIncrementIsZero B
  }
