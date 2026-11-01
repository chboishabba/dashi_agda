{-# OPTIONS --safe #-}
module DASHI.Reasoning.AristotleProofStateInvolutionFoldExact where

------------------------------------------------------------------------
-- ARISTOTLE x FINE-FIBRE FOLD
--
-- A proof-search phase reversal can be represented by an involution on the
-- actual Aristotle State carrier.  If one requested trit intertwines that state
-- involution with signed negation, fixed proof states land in the coarse zero
-- sector.  This is not a proof of the state and not a claim that every zero is
-- fixed: unresolved/collapsed states may also observe as zero.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Reasoning.AristotleMCGSHypergraphExact as Aristotle
import DASHI.Reasoning.AristotleRequestedFibreObserverRefinementExact as Requested
import DASHI.Cognition.PNF.RequestedFibreInvolutionFoldExact as Fold
import DASHI.Cognition.PNF.HypercomplexRequestedFractranComponentExact as Fine
import DASHI.Cognition.PNF.ContextualFractranOccurrenceHyperfabricExact as Context
import DASHI.Foundations.SSPTritCarrier as Trit

record AristotleStateInvolution
    {G : Aristotle.SearchHypergraph}
    (component : Requested.AristotleRequestedStateComponent G) : Set₁ where
  constructor aristotleStateInvolution
  field
    invertState : Aristotle.State G → Aristotle.State G
    involutive : ∀ state → invertState (invertState state) ≡ state
    requestedObservationIntertwines : ∀ state →
      Requested.observeRequestedState component (invertState state)
      ≡ Context.negateTrit (Requested.observeRequestedState component state)

open AristotleStateInvolution public

asRequestedComponentInvolution :
  ∀ {G component} →
  AristotleStateInvolution {G} component →
  Fold.RequestedComponentInvolution (Requested.asRequestedComponent component)
asRequestedComponentInvolution structure =
  Fold.requestedComponentInvolution
    (Fold.fineInvolution (invertState structure) (involutive structure))
    (requestedObservationIntertwines structure)

fixedAristotleStateObservesZero :
  ∀ {G component}
    (structure : AristotleStateInvolution {G} component)
    (state : Aristotle.State G) →
  invertState structure state ≡ state →
  Requested.observeRequestedState component state ≡ Trit.sspZero
fixedAristotleStateObservesZero structure state fixed =
  Fold.fixedFinePointObservesZero
    (asRequestedComponentInvolution structure)
    state fixed

record AristotleInvolutionFoldBoundary : Set where
  constructor aristotleInvolutionFoldBoundary
  field
    fixedSearchStateImpliesRequestedZero : Bool
    requestedZeroImpliesFixedSearchState : Bool
    fixedSearchStateImpliesStateProved : Bool
    proofStateFoldMayContainManyFineStates : Bool

canonicalAristotleInvolutionFoldBoundary : AristotleInvolutionFoldBoundary
canonicalAristotleInvolutionFoldBoundary =
  aristotleInvolutionFoldBoundary true false false true
