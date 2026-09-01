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

import DASHI.Reasoning.AristotleMCGSHypergraphExact as Aristotle
import DASHI.Reasoning.AristotleResidualInformationSearchExact as Residual
import DASHI.Reasoning.AristotleRequestedFibreObserverRefinementExact as Requested

record ActualAristotleRequestedFibreProducer
    (G : Aristotle.SearchHypergraph)
    (oldObserver : Aristotle.StateObserver G) : Set₁ where
  field
    requestedComponent : Requested.AristotleRequestedStateComponent G

    -- A real collision in the old observer fibre is split by the requested
    -- component.  This is the exact observation-gain theorem.
    strictSplit :
      Requested.StrictRequestedSplit oldObserver requestedComponent

    -- A real Aristotle action carries a certified posterior residual fibre and
    -- keeps every explicit hyperedge target admissible.
    residualAction : Residual.AristotleResidualAction G

    -- Proof reuse after refining the observer is not inherited automatically.
    -- The actual refined observer must earn its own quotient-soundness witness.
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
  →
  DASHI.Core.Prelude.⊥
actualRequestedSplitIsStrict producer =
  Requested.requestedSplitSeparatesRefinedObserver (strictSplit producer)

-- Once a real proof is constructed, refinement machinery adds no alternative
-- notion of success: terminal authority is still the Aristotle AND/OR proof.
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
