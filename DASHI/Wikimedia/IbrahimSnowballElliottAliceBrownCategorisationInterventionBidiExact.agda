module DASHI.Wikimedia.IbrahimSnowballElliottAliceBrownCategorisationInterventionBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballKinshipSocialisationEducationAuthorityBidiExact as Formation
import DASHI.Wikimedia.IbrahimSnowballChildhoodCategorisationConformityPsychologyBidiExact as ChildPsych
import DASHI.Wikimedia.IbrahimSnowballAliceBrownSocialPsychologyEthicsBidiExact as AliceSocial
import DASHI.Culture.JaneElliottBlueEyesBrownEyesPluralLensExact as Elliott
import DASHI.Culture.JaneElliottAliceBrownEpistemicAgencyCrossPollinationExact as ElliottAlice

------------------------------------------------------------------------
-- NAMED-INTERVENTION SPECIALISATION OF THE EXISTING BIDI GRAPH
--
-- This module deliberately does NOT introduce another general theory of
-- categorisation, social psychology, education, or ethics.  Those parent
-- surfaces are already owned by ChildPsych and AliceSocial.  The contribution
-- here is narrower:
--
--   * bind the Jane Elliott intervention lane to exact external work identities;
--   * retain the DOI-bounded Stewart et al. program-evaluation source;
--   * instantiate the existing nonfactorability/agency/ethics owners on this
--     named intervention;
--   * feed the surviving distinctions back into Education/Socialisation/
--     Institution/Community as reverse BIDI constraints.
--
-- External identity coordinates checked 2026-09-10:
--   Jane Elliott                  Q6152188
--   The Eye of the Storm (1970)  Q5422703
--   A Class Divided              Q4655946
--
-- No stand-alone QID for the blue-eyes/brown-eyes exercise is promoted unless
-- an exact same-entity receipt is recovered.
------------------------------------------------------------------------

janeElliottQid : Identity.ExternalIdentityDemand
janeElliottQid = Formation.janeElliottQid

eyeOfStormQid : Identity.ExternalIdentityDemand
eyeOfStormQid = Identity.mkOptionalIdentityDemand
  "Elliott named-intervention BIDI"
  "documentary-work identity"
  "The Eye of the Storm (1970 documentary)"
  Identity.wikidataQid
  (Identity.verified "Q5422703" "Wikidata work identity checked 2026-09-10")

aClassDividedQid : Identity.ExternalIdentityDemand
aClassDividedQid = Identity.mkOptionalIdentityDemand
  "Elliott named-intervention BIDI"
  "documentary-work identity"
  "A Class Divided"
  Identity.wikidataQid
  (Identity.verified "Q4655946" "Wikidata work identity checked 2026-09-10")

blueEyesExerciseQid : Identity.ExternalIdentityDemand
blueEyesExerciseQid = Identity.mkOptionalIdentityDemand
  "Elliott named-intervention BIDI"
  "named intervention identity"
  "blue-eyed/brown-eyed exercise"
  Identity.wikidataQid
  (Identity.unresolved "named intervention is source-linked to Elliott and documentary records, but no exact stand-alone QID is promoted in this pass")

stewartEvaluationSource : Attribution.AttributedSource
stewartEvaluationSource = Attribution.mkDOISource
  "Stewart et al."
  "Do the Eyes Have It? A Program Evaluation of Jane Elliott's Blue-Eyes/Brown-Eyes Diversity Training Exercise"
  "Journal of Applied Social Psychology 33(9):1898-1921"
  "2003"
  "10.1111/j.1559-1816.2003.tb02086.x"
  "https://doi.org/10.1111/j.1559-1816.2003.tb02086.x"
  Attribution.academicArticleSource
  "program-evaluation source for the named intervention; does not establish equivalence to historical racism, universal causal mechanism, or ethical legitimacy"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Existing exact regressions reused directly.
------------------------------------------------------------------------

namedInterventionCategoryPowerBoundary :
  INF.FactorsThrough Elliott.groupObserver Elliott.constraintOutcome → ⊥
namedInterventionCategoryPowerBoundary =
  ChildPsych.assignedCategoryCannotFactorPowerRelation

namedInterventionContestabilityBoundary :
  INF.FactorsThrough ElliottAlice.surfaceObservation ElliottAlice.contestabilityAnswer → ⊥
namedInterventionContestabilityBoundary =
  ChildPsych.elliottAliceContestabilityBoundary

namedInterventionEffectEthicsBoundary :
  INF.FactorsThrough AliceSocial.effectSurface AliceSocial.ethicalGovernanceReading → ⊥
namedInterventionEffectEthicsBoundary =
  AliceSocial.socialEffectCannotFactorEthicalGovernance

------------------------------------------------------------------------
-- Reverse BIDI constraints: leaf-specific failures constrain broad parents.
------------------------------------------------------------------------

record ReverseParentConstraint : Set where
  constructor reverse-parent-constraint
  field
    parentNode : String
    namedInterventionWitness : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open ReverseParentConstraint public

educationConstraint : ReverseParentConstraint
educationConstraint = reverse-parent-constraint
  "Education"
  "Jane Elliott intervention + Alice Brown voice/agency owners"
  "teacher/institution observation, participant voice, contestability, consent, ethics and historical context remain independently recoverable"
  false

socialisationConstraint : ReverseParentConstraint
socialisationConstraint = reverse-parent-constraint
  "Socialisation"
  "assigned category plus authority-backed treatment"
  "visible compliance or participation cannot be promoted to assent, private belief, autonomous endorsement or natural category truth"
  false

institutionConstraint : ReverseParentConstraint
institutionConstraint = reverse-parent-constraint
  "Institution"
  "institutionally organised intervention"
  "institutional record/effect does not replace participant meaning, constitutive voice, contestability or ethical governance"
  false

communityConstraint : ReverseParentConstraint
communityConstraint = reverse-parent-constraint
  "Community"
  "bounded classroom/training intervention"
  "one intervention cannot define a community, all race relations, all educational settings, or a universal social mechanism"
  false

------------------------------------------------------------------------
-- Composition receipt: broad owners remain authoritative for the general seam;
-- this owner is only the named/source-bound specialisation.
------------------------------------------------------------------------

record ElliottNamedInterventionBidiBoundary : Set where
  constructor elliott-named-intervention-bidi-boundary
  field
    reusesChildPsychologyParentOwner : Bool
    reusesAliceBrownEthicsParentOwner : Bool
    reusesExistingElliottAliceCrossPollination : Bool
    exactPersonAndWorkQidsRetained : Bool
    unresolvedExerciseQidRemainsExplicit : Bool
    evaluationDOIRetained : Bool
    assignedCategoryDoesNotDeterminePower : Bool
    observedResponseDoesNotDetermineContestability : Bool
    observedEffectDoesNotDetermineEthicalGovernance : Bool
    programEvaluationDoesNotEqualHistoricalRacism : Bool
    leafEvidenceConstrainsParentSemanticsBidi : Bool
    attributionTravelsWithNamedIntervention : Bool
    presentAxisVocabularyClaimedComplete : Bool
open ElliottNamedInterventionBidiBoundary public

canonicalElliottNamedInterventionBidiBoundary : ElliottNamedInterventionBidiBoundary
canonicalElliottNamedInterventionBidiBoundary =
  elliott-named-intervention-bidi-boundary
    true true true true true true true true true true true true false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data JaneElliottQidCreatesExerciseValidity : Set where
data DocumentaryIdentityCreatesEmpiricalTruth : Set where
data ProgramEvaluationCreatesRacismEquivalence : Set where
data ObservedEffectCreatesEthicalPermission : Set where
data ParticipantResponseCreatesConsent : Set where
data OneInterventionDefinesParentGraphNode : Set where

janeElliottQidDoesNotCreateExerciseValidity : JaneElliottQidCreatesExerciseValidity → ⊥
janeElliottQidDoesNotCreateExerciseValidity ()

documentaryIdentityDoesNotCreateEmpiricalTruth : DocumentaryIdentityCreatesEmpiricalTruth → ⊥
documentaryIdentityDoesNotCreateEmpiricalTruth ()

programEvaluationDoesNotCreateRacismEquivalence : ProgramEvaluationCreatesRacismEquivalence → ⊥
programEvaluationDoesNotCreateRacismEquivalence ()

observedEffectDoesNotCreateEthicalPermission : ObservedEffectCreatesEthicalPermission → ⊥
observedEffectDoesNotCreateEthicalPermission ()

participantResponseDoesNotCreateConsent : ParticipantResponseCreatesConsent → ⊥
participantResponseDoesNotCreateConsent ()

oneInterventionDoesNotDefineParentGraphNode : OneInterventionDefinesParentGraphNode → ⊥
oneInterventionDoesNotDefineParentGraphNode ()

formationBoundary : Formation.KinshipSocialisationEducationAuthorityBidiBoundary
formationBoundary = Formation.canonicalKinshipSocialisationEducationAuthorityBidiBoundary

childPsychBoundary : ChildPsych.ChildhoodCategorisationConformityPsychologyBidiBoundary
childPsychBoundary = ChildPsych.canonicalChildhoodCategorisationConformityPsychologyBidiBoundary

aliceSocialBoundary : AliceSocial.AliceBrownSocialPsychologyEthicsBidiBoundary
aliceSocialBoundary = AliceSocial.canonicalAliceBrownSocialPsychologyEthicsBidiBoundary
