module DASHI.Culture.ChildReligiousEpistemicReopeningBidiExact where

------------------------------------------------------------------------
-- CHILD RELIGIOUS EPISTEMIC REOPENING BIDI
--
-- This owner continues the child religious-autonomy lane by separating
-- outward profession from the epistemic conditions under which a belief can
-- be encountered, challenged, revised or left.
--
-- Central distinctions:
--
--   professed belief != private belief
--   private belief != autonomous endorsement
--   access to one alternative != meaningful counter-evidence access
--   counter-evidence access != authority contestability
--   authority contestability != safe revision
--   safe revision != guaranteed belief change
--
-- It reuses the merged multidimensional autonomy owner and the existing
-- representation/subject-position nonfactorability theorem.  The finite
-- witness below is repository-native and is not attributed to any external
-- source as an empirical theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.DecisionAutonomyExact as Autonomy
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.RepresentationSubjectPositionNonfactorabilityExact as Subject
import DASHI.Culture.ChildReligiousAutonomyFormationBidiExact as Formation
import DASHI.Culture.JohnAnthonyBrownChildReligiousPowerBidiExact as Brown

------------------------------------------------------------------------
-- Epistemic reopening coordinates.
------------------------------------------------------------------------

record EpistemicReopeningState : Set where
  constructor epistemic-reopening-state
  field
    alternativeWorldviewsDiscoverable : Bool
    sourceDiversityAvailable : Bool
    counterEvidenceAccessible : Bool
    authorityClaimsContestable : Bool
    questionsPermitted : Bool
    doubtPermitted : Bool
    disagreementWithoutBelongingPenalty : Bool
    revisionWithoutMaterialPenalty : Bool
    exitWithoutEpistemicIsolation : Bool
    recognisedFirstPersonVoice : Bool
    provenanceVisible : Bool

open EpistemicReopeningState public

openEpistemicState : EpistemicReopeningState
openEpistemicState = epistemic-reopening-state
  true true true true true true true true true true true

closedEpistemicState : EpistemicReopeningState
closedEpistemicState = epistemic-reopening-state
  false false false false false false false false false false false

------------------------------------------------------------------------
-- Profession surface is deliberately coarse.
------------------------------------------------------------------------

data FineBeliefEpisode : Set where
  revisablyEndorsed inheritedClosedProfession : FineBeliefEpisode

data ProfessionSurface : Set where
  sameProfession : ProfessionSurface

data EpistemicRoute : Set where
  reopenedRoute closedInheritanceRoute : EpistemicRoute

professionSurface : FineBeliefEpisode → ProfessionSurface
professionSurface revisablyEndorsed = sameProfession
professionSurface inheritedClosedProfession = sameProfession

epistemicRoute : FineBeliefEpisode → EpistemicRoute
epistemicRoute revisablyEndorsed = reopenedRoute
epistemicRoute inheritedClosedProfession = closedInheritanceRoute

epistemicRouteDiffers :
  epistemicRoute revisablyEndorsed
  ≡ epistemicRoute inheritedClosedProfession → ⊥
epistemicRouteDiffers ()

professionCannotRecoverEpistemicRoute :
  INF.FactorsThrough professionSurface epistemicRoute → ⊥
professionCannotRecoverEpistemicRoute =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      revisablyEndorsed inheritedClosedProfession refl epistemicRouteDiffers)

------------------------------------------------------------------------
-- No surface-level promotion to autonomous endorsement.
------------------------------------------------------------------------

data ProfessionPromotesPrivateBelief : Set where

data ProfessionPromotesAutonomousEndorsement : Set where

data AlternativeAccessPromotesContestability : Set where

data CounterEvidenceAccessPromotesSafeRevision : Set where

data SafeRevisionPromotesBeliefChange : Set where

data AuthorityStatusPromotesTruth : Set where

professionDoesNotPromotePrivateBelief : ProfessionPromotesPrivateBelief → ⊥
professionDoesNotPromotePrivateBelief ()

professionDoesNotPromoteAutonomousEndorsement :
  ProfessionPromotesAutonomousEndorsement → ⊥
professionDoesNotPromoteAutonomousEndorsement ()

alternativeAccessDoesNotPromoteContestability :
  AlternativeAccessPromotesContestability → ⊥
alternativeAccessDoesNotPromoteContestability ()

counterEvidenceDoesNotPromoteSafeRevision :
  CounterEvidenceAccessPromotesSafeRevision → ⊥
counterEvidenceDoesNotPromoteSafeRevision ()

safeRevisionDoesNotPromoteBeliefChange : SafeRevisionPromotesBeliefChange → ⊥
safeRevisionDoesNotPromoteBeliefChange ()

authorityDoesNotPromoteTruth : AuthorityStatusPromotesTruth → ⊥
authorityDoesNotPromoteTruth ()

------------------------------------------------------------------------
-- Autonomy weld.
--
-- Epistemic reopening is not the whole autonomy object.  It supplies some of
-- the conditions needed for the merged autonomy axes, but does not replace
-- actuation, residual-alternative or decision-refinement requirements.
------------------------------------------------------------------------

record EpistemicAutonomyWeld : Set where
  constructor epistemic-autonomy-weld
  field
    epistemicState : EpistemicReopeningState
    autonomyAxes : Autonomy.AutonomyAxes
    alternativesCoordinateWeld :
      EpistemicReopeningState.alternativeWorldviewsDiscoverable epistemicState
      ≡ Autonomy.relevantAlternativesAccessible autonomyAxes
    revisionCoordinateWeld :
      EpistemicReopeningState.revisionWithoutMaterialPenalty epistemicState
      ≡ Autonomy.revisionOpportunity autonomyAxes
    noClaimEpistemicStateAloneEqualsFullAutonomy : Bool
    noClaimEpistemicStateAloneEqualsFullAutonomyIsTrue :
      noClaimEpistemicStateAloneEqualsFullAutonomy ≡ true

open EpistemicAutonomyWeld public

openEpistemicAutonomyWeld : EpistemicAutonomyWeld
openEpistemicAutonomyWeld = epistemic-autonomy-weld
  openEpistemicState
  Autonomy.freeAxes
  refl refl
  true refl

closedEpistemicAutonomyWeld : EpistemicAutonomyWeld
closedEpistemicAutonomyWeld = epistemic-autonomy-weld
  closedEpistemicState
  Autonomy.constrainedAxes
  refl refl
  true refl

------------------------------------------------------------------------
-- Longitudinal reopening receipt.
------------------------------------------------------------------------

record EpistemicReopeningReceipt : Set where
  constructor epistemic-reopening-receipt
  field
    earlier : EpistemicReopeningState
    later : EpistemicReopeningState
    alternativesReopened : Bool
    counterEvidenceReopened : Bool
    authorityContestabilityReopened : Bool
    doubtAndQuestionsReopened : Bool
    belongingPenaltyReduced : Bool
    revisionAndExitReopened : Bool
    firstPersonVoiceRecognised : Bool
    evidenceProvenance : String

open EpistemicReopeningReceipt public

canonicalReopeningReceipt : EpistemicReopeningReceipt
canonicalReopeningReceipt = epistemic-reopening-receipt
  closedEpistemicState openEpistemicState
  true true true true true true true
  "finite DASHI reopening witness; not a claim that any population follows this trajectory"

------------------------------------------------------------------------
-- Reverse audit: public profession cannot reconstruct the hidden route.
------------------------------------------------------------------------

data RecoveryStatus : Set where
  recovered bounded unresolved nonidentifiableFromProfession : RecoveryStatus

record EpistemicBackwardAudit : Set where
  constructor epistemic-backward-audit
  field
    publicProfession : RecoveryStatus
    privateBelief : RecoveryStatus
    counterEvidenceHistory : RecoveryStatus
    authorityContestabilityHistory : RecoveryStatus
    belongingPenaltyHistory : RecoveryStatus
    revisionHistory : RecoveryStatus
    autonomousEndorsement : RecoveryStatus
    uniqueEpistemicRoute : RecoveryStatus

canonicalProfessionOnlyAudit : EpistemicBackwardAudit
canonicalProfessionOnlyAudit = epistemic-backward-audit
  recovered
  nonidentifiableFromProfession
  unresolved
  unresolved
  unresolved
  unresolved
  nonidentifiableFromProfession
  nonidentifiableFromProfession

------------------------------------------------------------------------
-- Existing subject-position theorem is kept live as a structural analogue:
-- a speech surface cannot generically recover fine subject-position.
------------------------------------------------------------------------

existingSpeechNonfactorability :
  INF.FactorsThrough Subject.speechObserver Subject.finePosition → ⊥
existingSpeechNonfactorability = Subject.speechSurfaceCannotRecoverFinePosition

------------------------------------------------------------------------
-- BIDI paper weld.
------------------------------------------------------------------------

record ChildReligiousEpistemicReopeningBidi : Set where
  constructor child-religious-epistemic-reopening-bidi
  field
    paperSource : Brown.BrownPaperSource
    formationBoundary : Formation.ChildReligiousAutonomyFormationBoundary
    opening : EpistemicReopeningReceipt
    backwardAudit : EpistemicBackwardAudit
    autonomyBoundary : Autonomy.AutonomyBoundary
    subjectBoundary : Subject.RepresentationSubjectPositionBoundary

open ChildReligiousEpistemicReopeningBidi public

canonicalChildReligiousEpistemicReopeningBidi :
  ChildReligiousEpistemicReopeningBidi
canonicalChildReligiousEpistemicReopeningBidi =
  child-religious-epistemic-reopening-bidi
    Brown.johnAnthonyBrownPaper
    Formation.canonicalChildReligiousAutonomyFormationBoundary
    canonicalReopeningReceipt
    canonicalProfessionOnlyAudit
    Autonomy.canonicalAutonomyBoundary
    Subject.canonicalRepresentationSubjectPositionBoundary

------------------------------------------------------------------------
-- Final boundary.
------------------------------------------------------------------------

record ChildReligiousEpistemicReopeningBoundary : Set where
  constructor child-religious-epistemic-reopening-boundary
  field
    professionEqualsPrivateBelief : Bool
    professionEqualsAutonomousEndorsement : Bool
    counterEvidenceAccessEqualsAuthorityContestability : Bool
    authorityContestabilityEqualsSafeRevision : Bool
    safeRevisionEqualsBeliefChange : Bool
    reopeningCanMatterWithoutForcingBeliefChange : Bool
    belongingPenaltyIsIndependentCoordinate : Bool
    recognisedFirstPersonVoiceIsIndependentCoordinate : Bool
    epistemicReopeningAloneEqualsFullAutonomy : Bool
    publicProfessionRecoversUniqueEpistemicRoute : Bool
    inheritedBeliefCanLaterBeRevisablyEndorsed : Bool

canonicalChildReligiousEpistemicReopeningBoundary :
  ChildReligiousEpistemicReopeningBoundary
canonicalChildReligiousEpistemicReopeningBoundary =
  child-religious-epistemic-reopening-boundary
    false false false false false true true true false false true
