{-# OPTIONS --safe #-}
module DASHI.Reasoning.AristotleActualRequestedFibreBidiFrontierExact where

------------------------------------------------------------------------
-- HIGHEST-ALPHA ARISTOTLE BIDI FRONTIER
--
-- The repository already has a complete finite regression loop over BranchWorld:
-- collision -> discriminator -> experiment -> fibre refinement -> guarded merge
-- -> selective reopening.  The remaining high-alpha move is not another toy
-- scheduler.  It is to instantiate that discipline on the ACTUAL Aristotle
-- SearchHypergraph.State carrier.
--
-- This owner states the exact producer cut:
--
--   actual Aristotle state observer fibre
--     -> same-object requested ternary discriminator
--     -> strict split of a real old-observer collision
--     -> proof-bearing residual action on real hyperedge targets
--     -> quotient-soundness payment for the refined observer
--     -> only then proof reuse / continued AND-OR search.
--
-- StateProved remains the only terminal proof authority.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

import DASHI.Reasoning.AristotleMCGSHypergraphExact as Aristotle
import DASHI.Reasoning.AristotleResidualInformationSearchExact as Residual
import DASHI.Reasoning.AristotleRequestedFibreObserverRefinementExact as Requested

record ActualAristotleRequestedFibreProducer
    (G : Aristotle.SearchHypergraph)
    (oldObserver : Aristotle.StateObserver G) : Set₁ where
  field
    requestedComponent : Requested.AristotleRequestedStateComponent G

    strictSplit :
      Requested.StrictRequestedSplit oldObserver requestedComponent

    residualAction : Residual.AristotleResidualAction G

    refinedQuotientSound :
      Aristotle.QuotientSound G
        (Requested.refinedObserver oldObserver requestedComponent)

open ActualAristotleRequestedFibreProducer public

actualRequestedSplitIsStrict :
  ∀ {G oldObserver}
    (producer : ActualAristotleRequestedFibreProducer G oldObserver) →
  Aristotle.observe
      (Requested.refinedObserver oldObserver (requestedComponent producer))
      (Requested.left (strictSplit producer))
  ≡ Aristotle.observe
      (Requested.refinedObserver oldObserver (requestedComponent producer))
      (Requested.right (strictSplit producer))
  → ⊥
actualRequestedSplitIsStrict producer =
  Requested.requestedSplitSeparatesRefinedObserver (strictSplit producer)

record ActualAristotleBidiClosure
    {G : Aristotle.SearchHypergraph}
    {oldObserver : Aristotle.StateObserver G}
    (producer : ActualAristotleRequestedFibreProducer G oldObserver) : Set₁ where
  field
    solvedState : Aristotle.State G
    proof : Aristotle.StateProved G solvedState

open ActualAristotleBidiClosure public

record AristotleActualBidiFrontierBoundary : Set where
  constructor aristotleActualBidiFrontierBoundary
  field
    finiteBranchWorldRegressionAlreadyExists : Bool
    actualStateRequestedDiscriminatorIsHighestAlpha : Bool
    residualGainAutomaticallyMeansProof : Bool
    refinedObserverAutomaticallyQuotientSound : Bool
    actualStateProvedRemainsTerminalAuthority : Bool

canonicalAristotleActualBidiFrontierBoundary : AristotleActualBidiFrontierBoundary
canonicalAristotleActualBidiFrontierBoundary =
  aristotleActualBidiFrontierBoundary true true false false true
