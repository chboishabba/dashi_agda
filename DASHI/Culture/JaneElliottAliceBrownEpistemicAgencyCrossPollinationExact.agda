module DASHI.Culture.JaneElliottAliceBrownEpistemicAgencyCrossPollinationExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Culture.JaneElliottBlueEyesBrownEyesPluralLensExact as Elliott
import DASHI.Biology.StudentVoiceEpistemicAgencyBridge as Voice
import DASHI.Biology.BrownKimberGovernanceProfileBridge as BrownKimber
import DASHI.Biology.AliceBrownDissentGovernanceCrossPollinationExact as Dissent
import DASHI.Core.IntersectionalNonFactorability as INF

------------------------------------------------------------------------
-- JANE ELLIOTT x ALICE BROWN
--
-- Elliott supplies a bounded demonstration surface where an arbitrary assigned
-- category can acquire consequences under authority-backed differential
-- treatment. Alice Brown's lane supplies the reverse epistemic-governance
-- question: can affected participants contest the framing, coding, relevance,
-- interpretation and downstream use of what institutions observe about them?
--
-- Neither source family empirically proves the other.
------------------------------------------------------------------------

data ElliottAliceCoordinate : Set where
  assignedCategory authorityTreatment participantExperience peerResponse
  performanceAffect voice contestability framingPower interpretationPower
  downstreamUse revisionPower : ElliottAliceCoordinate

record ElliottAliceBridgeBoundary : Set where
  constructor elliott-alice-bridge-boundary
  field
    assignedCategoryIsParticipantVoice : Bool
    observedPerformanceIsAutonomousEndorsement : Bool
    feedbackEqualsConstitutiveAgency : Bool
    authorityTreatmentCanChangeObservedSurface : Bool
    affectedParticipantVoiceMustRemainDistinct : Bool
    framingAndInterpretationAreGovernanceCoordinates : Bool
    oneExerciseModelsRacismCompletely : Bool
    crossPollinationPreservesSourceFibres : Bool
open ElliottAliceBridgeBoundary public

canonicalElliottAliceBridgeBoundary : ElliottAliceBridgeBoundary
canonicalElliottAliceBridgeBoundary =
  elliott-alice-bridge-boundary false false false true true true false true

------------------------------------------------------------------------
-- Same visible treatment response need not recover whether the participant had
-- voice/contestability in the institution producing the observation.
------------------------------------------------------------------------

data ParticipationState : Set where
  sameSurfaceNoContestability sameSurfaceWithContestability : ParticipationState

data SurfaceObservation : Set where sameObservedResponse : SurfaceObservation
data ContestabilityAnswer : Set where noContestability hasContestability : ContestabilityAnswer

surfaceObservation : ParticipationState → SurfaceObservation
surfaceObservation _ = sameObservedResponse

contestabilityAnswer : ParticipationState → ContestabilityAnswer
contestabilityAnswer sameSurfaceNoContestability = noContestability
contestabilityAnswer sameSurfaceWithContestability = hasContestability

surfaceCannotRecoverContestability :
  INF.FactorsThrough surfaceObservation contestabilityAnswer → ⊥
surfaceCannotRecoverContestability =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      sameSurfaceNoContestability sameSurfaceWithContestability refl (λ ()))

feedbackStillHasNoConstitutiveAuthority :
  (coordinate : DASHI.Core.EpistemicInquiryGovernance.InquiryCoordinate) →
  DASHI.Core.EpistemicInquiryGovernance.authorityLevel
    BrownKimber.brownKimberAuthorityProfile
    Voice.feedbackSourceStage coordinate
  ≡ DASHI.Core.EpistemicInquiryGovernance.noAuthority
feedbackStillHasNoConstitutiveAuthority = BrownKimber.feedbackAuthorityLevelIsZero

data ExperimentalSubjectEqualsInstitutionalCoDesigner : Set where
data CategoryAssignmentEqualsIdentityTruth : Set where
data MeasuredResponseEqualsUnmediatedSubjectMeaning : Set where

experimentalSubjectDoesNotBecomeCoDesigner : ExperimentalSubjectEqualsInstitutionalCoDesigner → ⊥
experimentalSubjectDoesNotBecomeCoDesigner ()

categoryAssignmentDoesNotBecomeIdentityTruth : CategoryAssignmentEqualsIdentityTruth → ⊥
categoryAssignmentDoesNotBecomeIdentityTruth ()

measuredResponseDoesNotBecomeUnmediatedMeaning : MeasuredResponseEqualsUnmediatedSubjectMeaning → ⊥
measuredResponseDoesNotBecomeUnmediatedMeaning ()
