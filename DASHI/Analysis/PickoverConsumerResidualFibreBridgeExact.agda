module DASHI.Analysis.PickoverConsumerResidualFibreBridgeExact where

------------------------------------------------------------------------
-- PICKOVER CONSUMER-INDEXED RETAINED-FIBRE BRIDGE
--
-- Source owner: DASHI.Core.ConsumerIndexedResidualRefinementExact.
-- Historical method precedents: David Blackwell (1953), Patrick and
-- Radhia Cousot (1977). No theorem here is attributed to Crenshaw.
-- Generic statements below do not assert a real pi-phase producer.
-- Source-written; no exact-head Agda kernel receipt.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Core.ConsumerIndexedResidualRefinementExact as Refine
import DASHI.Core.ObserverRefinementLatticeExact as Observe

-- A signed phase fibre retains the residual needed for the selected
-- terminal orientation consumer. This is stronger than an arbitrary
-- coarse chart and intentionally leaves the analytic carrier abstract.
record SignedPhaseFibre
    (Phase Sector Residual Sign : Set)
    (sector : Phase → Sector)
    (fine : Phase → Residual)
    (orientation : Phase → Sign) : Set where
  field
    signedRepair : Refine.ResidualRepair sector fine orientation

open SignedPhaseFibre public

-- This is the actual existing consumer-indexed necessity theorem, not
-- merely generic intersectionality/nonfactorability.
residualNeededForSignedCollision :
  ∀ {Phase Sector Residual Sign : Set}
    {sector : Phase → Sector}
    {fine : Phase → Residual}
    {orientation : Phase → Sign} →
  (collision : Refine.ConsumerRelevantCollision sector orientation) →
  (fibre : SignedPhaseFibre Phase Sector Residual Sign
             sector fine orientation) →
  fine (Refine.left collision) ≡ fine (Refine.right collision) → ⊥
residualNeededForSignedCollision collision fibre =
  Refine.residualMustSeparateRelevantCollision collision
    (signedRepair fibre)

-- A repaired fibre is provably a strict refinement of the coarse
-- signed-query-inadequate sector observer.
signedFibreStrictlyRefinesSector :
  ∀ {Phase Sector Residual Sign : Set}
    {sector : Phase → Sector}
    {fine : Phase → Residual}
    {orientation : Phase → Sign} →
  (collision : Refine.ConsumerRelevantCollision sector orientation) →
  (fibre : SignedPhaseFibre Phase Sector Residual Sign
             sector fine orientation) →
  Observe.StrictRefinement sector (Observe.pairObserver sector fine)
signedFibreStrictlyRefinesSector collision fibre =
  Refine.consumerRelevantResidualGivesStrictRefinement
    collision (signedRepair fibre)

-- OPEN: construct an inhabitant for Phase = the actual analytic
-- circle phase of 99^(9999!), AND pay its producer/runtime complexity.
