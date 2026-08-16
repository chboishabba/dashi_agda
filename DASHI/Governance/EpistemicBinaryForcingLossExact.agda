module DASHI.Governance.EpistemicBinaryForcingLossExact where

------------------------------------------------------------------------
-- CROSS-POLLINATION CALIBRATION
--
-- Existing DASHI.Ontology.EpistemicTrit already proves that forcing unresolved
-- evidence into either binary decision branch creates a collision:
--
--   unresolved -> accept collides with supported -> accept
--   unresolved -> reject collides with contradicted -> reject.
--
-- This governance bridge makes the information-loss consequence explicit and
-- composes it with the newer counterposition-diversity boundary.  It does not
-- claim that every binary policy decision is illegitimate: a downstream action
-- may genuinely require two outputs.  The theorem concerns the loss incurred
-- if the binary action is mistaken for the underlying epistemic state.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Ontology.EpistemicTrit as Epistemic
import DASHI.Governance.CounterpositionDiversityAutonomyExact as Counter
import DASHI.Governance.OpenWorldDisconfirmationBoundaryExact as OpenWorld

------------------------------------------------------------------------
-- Injectivity fails for both canonical binary-forcing policies.
------------------------------------------------------------------------

AcceptForcingInjective : Set
AcceptForcingInjective =
  ∀ {left right : Epistemic.EpistemicTrit} →
  Epistemic.forceUnresolvedToAccept left
    ≡ Epistemic.forceUnresolvedToAccept right →
  left ≡ right

RejectForcingInjective : Set
RejectForcingInjective =
  ∀ {left right : Epistemic.EpistemicTrit} →
  Epistemic.forceUnresolvedToReject left
    ≡ Epistemic.forceUnresolvedToReject right →
  left ≡ right

acceptForcingIsNotInjective : AcceptForcingInjective → ⊥
acceptForcingIsNotInjective injective =
  OpenWorld.unresolvedIsNotSupported
    (injective Epistemic.acceptPolicyCollision)

rejectForcingIsNotInjective : RejectForcingInjective → ⊥
rejectForcingIsNotInjective injective =
  OpenWorld.unresolvedIsNotContradicted
    (injective Epistemic.rejectPolicyCollision)

------------------------------------------------------------------------
-- A binary action projection can be legitimate as an action surface while
-- remaining insufficient to reconstruct the evidentiary state that produced
-- it.  Keep these two roles typed separately.
------------------------------------------------------------------------

record BinaryDecisionProjection : Set₁ where
  constructor binaryDecisionProjection
  field
    decide : Epistemic.EpistemicTrit → Epistemic.BinaryDecision

open BinaryDecisionProjection public

record DecisionWithEpistemicReceipt : Set where
  constructor decisionWithEpistemicReceipt
  field
    state : Epistemic.EpistemicTrit
    decision : Epistemic.BinaryDecision
    decisionExact :
      decision ≡ Epistemic.forceUnresolvedToAccept state

------------------------------------------------------------------------
-- Cross-check counterposition diversity: the reasoning space need not collapse
-- merely because a terminal operational action is binary.
------------------------------------------------------------------------

forcedBinaryDoesNotExhaustReasoningSpace :
  Counter.CounterpositionDiversityBoundary.forcedBinaryChoiceExhaustsCounterpositionSpace
    Counter.canonicalCounterpositionDiversityBoundary
  ≡ false
forcedBinaryDoesNotExhaustReasoningSpace = refl

record EpistemicBinaryForcingBoundary : Set where
  constructor epistemicBinaryForcingBoundary
  field
    binaryDecisionReconstructsEpistemicState : Bool
    unresolvedMayNeedTerminalAction : Bool
    terminalActionEqualsEvidenceState : Bool
    forcedBinaryExhaustsCounterpositionSpace : Bool
    retainingEpistemicReceiptAvoidsSemanticIdentification : Bool

canonicalEpistemicBinaryForcingBoundary : EpistemicBinaryForcingBoundary
canonicalEpistemicBinaryForcingBoundary =
  epistemicBinaryForcingBoundary false true false false true
