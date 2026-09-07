module DASHI.Core.AppendOnlyEvidenceResidualRevisionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.MechanismModelDiscriminationExact as Model
import DASHI.Core.ResidualActionPolicyExact as Action
import DASHI.Core.ReopenableHypothesisForestExact as Forest

------------------------------------------------------------------------
-- APPEND-ONLY EVIDENCE / NON-MONOTONE CONCLUSION
--
-- Evidence and provenance may grow monotonically while the currently justified
-- conclusion, residual class, hypothesis status, or next action changes.  New
-- evidence may satisfy a premise, activate a defeater, or expose a dependency
-- mismatch without deleting any earlier observation.
------------------------------------------------------------------------

record AppendOnlyEvidenceSystem : Set₂ where
  constructor appendOnlyEvidenceSystem
  field
    Evidence History Conclusion : Set
    append : History → Evidence → History
    Contains : Evidence → History → Set
    oldEvidencePersists :
      (history : History) →
      (old new : Evidence) →
      Contains old history →
      Contains old (append history new)
    conclusionAt : History → Conclusion
    evidenceReference : Evidence → String
    conclusionReference : Conclusion → String

open AppendOnlyEvidenceSystem public

record ConclusionRevision
    (system : AppendOnlyEvidenceSystem) : Set₁ where
  constructor conclusionRevision
  open AppendOnlyEvidenceSystem system
  field
    before : History
    newEvidence : Evidence
    oldEvidence : Evidence
    oldPresentBefore : Contains oldEvidence before
    oldStillPresentAfter : Contains oldEvidence (append before newEvidence)
    conclusionBefore : Conclusion
    conclusionAfter : Conclusion
    beforeMatches : conclusionAt before ≡ conclusionBefore
    afterMatches : conclusionAt (append before newEvidence) ≡ conclusionAfter
    conclusionsDiffer : conclusionBefore ≡ conclusionAfter → ⊥
    revisionReference : String

open ConclusionRevision public

------------------------------------------------------------------------
-- Exact finite fixture: one support observation remains present after a
-- defeater is appended, yet the consumer conclusion changes from promote to
-- hold.  No evidence deletion is involved.
------------------------------------------------------------------------

data FixtureEvidence : Set where
  supportObservation
  defeaterObservation
  : FixtureEvidence

data FixtureHistory : Set where
  supportOnly
  supportPlusDefeater
  : FixtureHistory

data FixtureConclusion : Set where
  promoteCandidate
  holdCandidate
  : FixtureConclusion

data FixtureContains : FixtureEvidence → FixtureHistory → Set where
  supportInSupportOnly : FixtureContains supportObservation supportOnly
  supportInExtended : FixtureContains supportObservation supportPlusDefeater
  defeaterInExtended : FixtureContains defeaterObservation supportPlusDefeater

appendFixture : FixtureHistory → FixtureEvidence → FixtureHistory
appendFixture supportOnly supportObservation = supportOnly
appendFixture supportOnly defeaterObservation = supportPlusDefeater
appendFixture supportPlusDefeater _ = supportPlusDefeater

persistFixture :
  (history : FixtureHistory) →
  (old new : FixtureEvidence) →
  FixtureContains old history →
  FixtureContains old (appendFixture history new)
persistFixture supportOnly supportObservation supportObservation supportInSupportOnly = supportInSupportOnly
persistFixture supportOnly supportObservation defeaterObservation supportInSupportOnly = supportInExtended
persistFixture supportPlusDefeater supportObservation _ supportInExtended = supportInExtended
persistFixture supportPlusDefeater defeaterObservation _ defeaterInExtended = defeaterInExtended

fixtureConclusion : FixtureHistory → FixtureConclusion
fixtureConclusion supportOnly = promoteCandidate
fixtureConclusion supportPlusDefeater = holdCandidate

fixtureSystem : AppendOnlyEvidenceSystem
fixtureSystem = appendOnlyEvidenceSystem
  FixtureEvidence
  FixtureHistory
  FixtureConclusion
  appendFixture
  FixtureContains
  persistFixture
  fixtureConclusion
  (λ { supportObservation → "support observation"
     ; defeaterObservation → "later defeater observation" })
  (λ { promoteCandidate → "candidate promoted for current consumer"
     ; holdCandidate → "candidate held after defeater activation" })

promoteIsNotHold : promoteCandidate ≡ holdCandidate → ⊥
promoteIsNotHold ()

supportPersistsAfterDefeater :
  FixtureContains supportObservation
    (appendFixture supportOnly defeaterObservation)
supportPersistsAfterDefeater = supportInExtended

conclusionChangesAfterAppend :
  fixtureConclusion supportOnly ≡
  fixtureConclusion (appendFixture supportOnly defeaterObservation) → ⊥
conclusionChangesAfterAppend ()

canonicalConclusionRevision : ConclusionRevision fixtureSystem
canonicalConclusionRevision = conclusionRevision
  supportOnly
  defeaterObservation
  supportObservation
  supportInSupportOnly
  supportInExtended
  promoteCandidate
  holdCandidate
  refl
  refl
  promoteIsNotHold
  "Appending a defeater preserves the earlier support carrier while changing the consumer conclusion."

------------------------------------------------------------------------
-- Bridges: residual classes and reopenable hypothesis states are explicitly
-- revision-capable rather than monotone confidence levels.
------------------------------------------------------------------------

record ResidualRevisionReceipt : Set where
  constructor residualRevisionReceipt
  field
    beforeResidual : Model.ModelResidual
    afterResidual : Model.ModelResidual
    oldEvidenceStillRetained : Bool
    newEvidenceReference : String
    recalculationReference : String

open ResidualRevisionReceipt public

record HypothesisReconsiderationReceipt : Set where
  constructor hypothesisReconsiderationReceipt
  field
    hypothesis : Model.ModelHypothesis
    priorStatus : Forest.HypothesisStatus
    revisedStatus : Forest.HypothesisStatus
    evidenceHistoryRetained : Bool
    reconsiderationReference : String

open HypothesisReconsiderationReceipt public

record AppendOnlyEvidenceRevisionBoundary : Set where
  constructor appendOnlyEvidenceRevisionBoundary
  field
    moreEvidenceImpliesSameConclusionOnlyStronger : Bool
    moreEvidenceImpliesSameConclusionOnlyStrongerIsFalse :
      moreEvidenceImpliesSameConclusionOnlyStronger ≡ false

    appendOnlyEvidenceImpliesMonotoneResidualAction : Bool
    appendOnlyEvidenceImpliesMonotoneResidualActionIsFalse :
      appendOnlyEvidenceImpliesMonotoneResidualAction ≡ false

    earlierEvidenceMustBeDeletedBeforeConclusionRevision : Bool
    earlierEvidenceMustBeDeletedBeforeConclusionRevisionIsFalse :
      earlierEvidenceMustBeDeletedBeforeConclusionRevision ≡ false

    oldEvidenceMayRemainValidWhileConsumerConclusionChanges : Bool
    oldEvidenceMayRemainValidWhileConsumerConclusionChangesIsTrue :
      oldEvidenceMayRemainValidWhileConsumerConclusionChanges ≡ true

    newEvidenceMayReopenPreviouslyAcceptedCarrier : Bool
    newEvidenceMayReopenPreviouslyAcceptedCarrierIsTrue :
      newEvidenceMayReopenPreviouslyAcceptedCarrier ≡ true

canonicalAppendOnlyEvidenceRevisionBoundary : AppendOnlyEvidenceRevisionBoundary
canonicalAppendOnlyEvidenceRevisionBoundary =
  appendOnlyEvidenceRevisionBoundary false refl false refl false refl true refl true refl

existingResidualActionBoundary : Action.ResidualActionBoundary
existingResidualActionBoundary = Action.canonicalResidualActionBoundary

existingHypothesisBoundary : Forest.ReopenableHypothesisBoundary
existingHypothesisBoundary = Forest.canonicalReopenableHypothesisBoundary
