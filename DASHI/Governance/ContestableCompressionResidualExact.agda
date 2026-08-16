module DASHI.Governance.ContestableCompressionResidualExact where

------------------------------------------------------------------------
-- CROSS-POLLINATION CALIBRATION
--
-- Reuses the existing core distinction from FutureQuotientResidualExact:
--   * a canonical future-safe quotient may intentionally forget distinctions;
--   * an exact residual can reopen the original representative;
--   * a weaker relevant residual need only reopen a future-equivalent state.
--
-- Governance interpretation: a compressed score/classification can be safe for
-- a declared operational observation language while an appeal/correction path
-- may still need a residual sufficient to reopen the affected case.  This is a
-- formal contestability interface, not a claim that every deployment must
-- disclose every internal datum or that absence of such a residual is unlawful.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.FutureQuotientResidualExact as Residual
import DASHI.Core.TypedDependencyCore as Dependency

------------------------------------------------------------------------
-- Exact appeal packet: quotient class plus exact residual.
------------------------------------------------------------------------

record ExactAppealPacket
    {State Action Observation : Set}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation}
    {presentation : Future.FutureEquivalencePresentation system project}
    (receipt : Residual.ExactResidualOverFutureQuotient presentation)
    (state : State) : Set where
  constructor exactAppealPacket
  field
    classCode : Future.QuotientCode presentation
    residualCode : Residual.Residual receipt
    classExact : classCode ≡ Future.classOf presentation state
    residualExact : residualCode ≡ Residual.residual receipt state

open ExactAppealPacket public

canonicalExactAppealPacket :
  ∀ {State Action Observation}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation}
    {presentation : Future.FutureEquivalencePresentation system project}
    (receipt : Residual.ExactResidualOverFutureQuotient presentation)
    (state : State) →
  ExactAppealPacket receipt state
canonicalExactAppealPacket receipt state =
  exactAppealPacket
    (Future.classOf _ state)
    (Residual.residual receipt state)
    refl
    refl

------------------------------------------------------------------------
-- If two affected cases have the same quotient class AND the same exact
-- residual, then the original states are equal.  The theorem is inherited from
-- the existing core residual injectivity result.
------------------------------------------------------------------------

sameExactAppealCoordinatesDetermineCase :
  ∀ {State Action Observation}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation}
    {presentation : Future.FutureEquivalencePresentation system project}
    (receipt : Residual.ExactResidualOverFutureQuotient presentation)
    {left right : State} →
  Future.classOf presentation left ≡ Future.classOf presentation right →
  Residual.residual receipt left ≡ Residual.residual receipt right →
  left ≡ right
sameExactAppealCoordinatesDetermineCase =
  Residual.classAndResidualDetermineState

------------------------------------------------------------------------
-- Relevant reopening is strictly weaker as a contract: it returns a state in
-- the same declared future-observation class, not necessarily the identical
-- historical representative.
------------------------------------------------------------------------

exactAppealResidualIsFutureRelevant :
  ∀ {State Action Observation}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation}
    {presentation : Future.FutureEquivalencePresentation system project} →
  Residual.ExactResidualOverFutureQuotient presentation →
  Residual.RelevantResidualOverFutureQuotient presentation
exactAppealResidualIsFutureRelevant = Residual.exactResidualIsRelevant

------------------------------------------------------------------------
-- Contestability level keeps exact and future-relevant reopening distinct.
------------------------------------------------------------------------

data ReopeningStrength : Set where
  futureRelevantReopening exactRepresentativeReopening : ReopeningStrength

record ContestableCompressionReceipt : Set where
  constructor contestableCompressionReceipt
  field
    reopeningStrength : ReopeningStrength
    quotientSafetyAndExactReopeningAreDifferentRequirements : Bool
    exactResidualRestoresRepresentativeIdentity : Bool
    relevantResidualRestoresOnlyDeclaredFutureEquivalence : Bool
    quotientSafetyAloneImpliesExactReconstruction : Bool
    legalAdequacyAutomaticallyEstablished : Bool

canonicalExactContestabilityReceipt : ContestableCompressionReceipt
canonicalExactContestabilityReceipt =
  contestableCompressionReceipt
    exactRepresentativeReopening
    true
    true
    false
    false
    false

canonicalRelevantContestabilityReceipt : ContestableCompressionReceipt
canonicalRelevantContestabilityReceipt =
  contestableCompressionReceipt
    futureRelevantReopening
    true
    false
    true
    false
    false
