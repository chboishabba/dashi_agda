{-# OPTIONS --safe #-}
module DASHI.Reasoning.AristotleRequestedFibreObserverRefinementExact where

------------------------------------------------------------------------
-- ARISTOTLE x REQUESTED-FIBRE BIDI OBSERVER REFINEMENT
--
-- Aristotle already owns proof states, observer fibres, AND/OR proof semantics
-- and explicit quotient-sound proof reuse.  The contextual FRACTRAN lane owns
-- fine requested components whose SSP trit is only a coarse observation.
--
-- The highest-alpha cross-pollination is therefore same-object: use Aristotle
-- State itself as the requested component FineCarrier.  A new requested prime
-- may refine an existing observer fibre only when it actually distinguishes two
-- states which the old observer identifies.  No proof is manufactured by that
-- refinement; StateProved remains the sole proof authority.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Reasoning.AristotleMCGSHypergraphExact as Aristotle
import DASHI.Cognition.PNF.ContextualFractranOccurrenceHyperfabricExact as Context
import DASHI.Cognition.PNF.HypercomplexRequestedFractranComponentExact as Fine
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Foundations.SSPTritCarrier as Trit

record AristotleRequestedStateComponent
    (G : Aristotle.SearchHypergraph) : Set₁ where
  constructor aristotleRequestedStateComponent
  field
    requestedPrime : Signed.SSPPrime
    compileValuation : Aristotle.State G → Context.ContextualValuation

open AristotleRequestedStateComponent public

asRequestedComponent :
  ∀ {G} → AristotleRequestedStateComponent G → Fine.RequestedFractranComponent
asRequestedComponent {G} component = Fine.requestedFractranComponent
  (Aristotle.State G)
  (requestedPrime component)
  (compileValuation component)

observeRequestedState :
  ∀ {G} → AristotleRequestedStateComponent G → Aristotle.State G → Trit.SSPTrit
observeRequestedState component = Fine.observeFine (asRequestedComponent component)

refinedObserver :
  ∀ {G}
    (old : Aristotle.StateObserver G) →
    AristotleRequestedStateComponent G →
    Aristotle.StateObserver G
refinedObserver old component = record
  { Aristotle.StateObserver.Observable =
      Aristotle.Observable old × Trit.SSPTrit
  ; Aristotle.StateObserver.observe = λ state →
      Aristotle.observe old state , observeRequestedState component state
  }

record StrictRequestedSplit
    {G : Aristotle.SearchHypergraph}
    (old : Aristotle.StateObserver G)
    (component : AristotleRequestedStateComponent G) : Set₁ where
  constructor strictRequestedSplit
  field
    left right : Aristotle.State G
    oldObserverCollision : Aristotle.observe old left ≡ Aristotle.observe old right
    requestedObservationDifferent :
      observeRequestedState component left ≡ observeRequestedState component right → ⊥

open StrictRequestedSplit public

requestedSplitSeparatesRefinedObserver :
  ∀ {G old component}
    (split : StrictRequestedSplit {G} old component) →
  Aristotle.observe (refinedObserver old component) (left split)
  ≡ Aristotle.observe (refinedObserver old component) (right split) → ⊥
requestedSplitSeparatesRefinedObserver split refinedEqual =
  requestedObservationDifferent split (cong proj₂ refinedEqual)

-- The old observation is retained exactly as the first coordinate.  Thus the
-- refinement is information-preserving rather than a replacement observer.
record ObserverRefinementReceipt
    {G : Aristotle.SearchHypergraph}
    (old : Aristotle.StateObserver G)
    (component : AristotleRequestedStateComponent G) : Set₁ where
  constructor observerRefinementReceipt
  field
    refined : Aristotle.StateObserver G
    refinedIsCanonical : refined ≡ refinedObserver old component

open ObserverRefinementReceipt public

canonicalObserverRefinementReceipt :
  ∀ {G} (old : Aristotle.StateObserver G)
    (component : AristotleRequestedStateComponent G) →
  ObserverRefinementReceipt old component
canonicalObserverRefinementReceipt old component =
  observerRefinementReceipt (refinedObserver old component) refl

------------------------------------------------------------------------
-- Proof/search authority firewall.
------------------------------------------------------------------------

record AristotleRequestedFibreBoundary : Set where
  constructor aristotleRequestedFibreBoundary
  field
    newDiscriminatorMaySplitOldObserverFibre : Bool
    observerRefinementAutomaticallyProvesState : Bool
    sameOldObserverImpliesSameRequestedTrit : Bool
    refinedObserverRetainsOldObservation : Bool
    quotientProofTransportStillRequiresQuotientSound : Bool

canonicalAristotleRequestedFibreBoundary : AristotleRequestedFibreBoundary
canonicalAristotleRequestedFibreBoundary =
  aristotleRequestedFibreBoundary true false false true true
