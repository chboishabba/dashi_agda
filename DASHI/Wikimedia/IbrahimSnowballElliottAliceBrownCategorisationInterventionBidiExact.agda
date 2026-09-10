module DASHI.Wikimedia.IbrahimSnowballElliottAliceBrownCategorisationInterventionBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballKinshipSocialisationEducationAuthorityBidiExact as Prior
import DASHI.Culture.JaneElliottBlueEyesBrownEyesPluralLensExact as Elliott
import DASHI.Governance.AliceBrownInstitutionalAgencyChoiceBridgeExact as Alice
import DASHI.Biology.EducationCorpusSourceRegistry as EducationSources

------------------------------------------------------------------------
-- IBRAHIM / SNOWBALL BIDI CONTINUATION:
--
--   categorisation / intervention
--          <-> authority / treatment
--          <-> participant response / voice
--          <-> institutional interpretation
--          <-> education / socialisation / community
--
-- External parents nominate the seam; concrete intervention/agency witnesses
-- constrain the parent reading in return. A parent graph node therefore may
-- not erase the intervention, observer, consent, authority or historical axes
-- needed by a concrete downstream consumer.
--
-- External identity coordinates checked 2026-09-10:
--   Jane Elliott                  Q6152188
--   The Eye of the Storm (1970)  Q5422703
--   A Class Divided              Q4655946
--   education                    Q8434 (reused)
--   parent-child relationship    Q1334052 (reused)
--
-- The blue-eyes/brown-eyes exercise itself is retained as a named-work/source
-- relation exposed by Jane Elliott's QID, but no stand-alone exercise QID is
-- promoted here without an exact safe identity receipt.
------------------------------------------------------------------------

janeElliottQid : Identity.ExternalIdentityDemand
janeElliottQid = Prior.janeElliottQid

eyeOfStormQid : Identity.ExternalIdentityDemand
eyeOfStormQid = Identity.mkOptionalIdentityDemand
  "Elliott/Alice Brown categorisation-intervention BIDI"
  "documentary-work identity"
  "The Eye of the Storm (1970 documentary)"
  Identity.wikidataQid
  (Identity.verified "Q5422703" "Wikidata work identity checked 2026-09-10; main subject includes Jane Elliott and the blue-eyed/brown-eyed experiment")

aClassDividedQid : Identity.ExternalIdentityDemand
aClassDividedQid = Identity.mkOptionalIdentityDemand
  "Elliott/Alice Brown categorisation-intervention BIDI"
  "documentary-work identity"
  "A Class Divided"
  Identity.wikidataQid
  (Identity.verified "Q4655946" "Wikidata work identity checked 2026-09-10")

blueEyesExerciseQid : Identity.ExternalIdentityDemand
blueEyesExerciseQid = Identity.mkOptionalIdentityDemand
  "Elliott/Alice Brown categorisation-intervention BIDI"
  "named intervention identity"
  "blue-eyed/brown-eyed exercise"
  Identity.wikidataQid
  (Identity.unresolved "named as Jane Elliott notable work/main subject in current Wikimedia records; exact stand-alone QID not safely recovered in this pass")

------------------------------------------------------------------------
-- Attributed source: this program-evaluation source is already named in the
-- Elliott owner. It pays only source-bounded evaluation propositions, never a
-- universal racism mechanism or ethical endorsement of the exercise.
------------------------------------------------------------------------

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
-- BIDI regression 1: assigned category alone cannot recover treatment/power.
------------------------------------------------------------------------

data CategorisationCase : Set where
  sameAssignedCategoryLowConstraint : CategorisationCase
  sameAssignedCategoryHighConstraint : CategorisationCase

data CategorySurface : Set where sameAssignedCategory : CategorySurface
data TreatmentPowerReading : Set where lowConstraintReading highConstraintReading : TreatmentPowerReading

categorySurface : CategorisationCase → CategorySurface
categorySurface _ = sameAssignedCategory

treatmentPowerReading : CategorisationCase → TreatmentPowerReading
treatmentPowerReading sameAssignedCategoryLowConstraint = lowConstraintReading
treatmentPowerReading sameAssignedCategoryHighConstraint = highConstraintReading

categoryPowerDefect : INF.NonFactorabilityWitness categorySurface treatmentPowerReading
categoryPowerDefect = INF.nonFactorabilityWitness
  sameAssignedCategoryLowConstraint sameAssignedCategoryHighConstraint refl (λ ())

assignedCategoryCannotFactorTreatmentPower :
  INF.FactorsThrough categorySurface treatmentPowerReading → ⊥
assignedCategoryCannotFactorTreatmentPower =
  INF.witnessRulesOutEveryFlatFactorisation categoryPowerDefect

elliottExistingPowerBoundary :
  INF.FactorsThrough Elliott.groupObserver Elliott.constraintOutcome → ⊥
elliottExistingPowerBoundary = Elliott.groupCannotRecoverPowerRelation

------------------------------------------------------------------------
-- BIDI regression 2: observed response cannot recover participant voice.
------------------------------------------------------------------------

data ParticipantCase : Set where
  sameObservedResponseVoiceConstitutive : ParticipantCase
  sameObservedResponseVoiceExcluded : ParticipantCase

data ObservedResponseSurface : Set where sameObservedResponse : ObservedResponseSurface
data ParticipantVoiceReading : Set where voiceConstitutive voiceExcluded : ParticipantVoiceReading

observedResponse : ParticipantCase → ObservedResponseSurface
observedResponse _ = sameObservedResponse

participantVoice : ParticipantCase → ParticipantVoiceReading
participantVoice sameObservedResponseVoiceConstitutive = voiceConstitutive
participantVoice sameObservedResponseVoiceExcluded = voiceExcluded

responseVoiceDefect : INF.NonFactorabilityWitness observedResponse participantVoice
responseVoiceDefect = INF.nonFactorabilityWitness
  sameObservedResponseVoiceConstitutive sameObservedResponseVoiceExcluded refl (λ ())

observedResponseCannotFactorParticipantVoice :
  INF.FactorsThrough observedResponse participantVoice → ⊥
observedResponseCannotFactorParticipantVoice =
  INF.witnessRulesOutEveryFlatFactorisation responseVoiceDefect

parentReportStillCannotCreateChildVoice : Alice.ParentReportPromotesChildVoiceIdentity → ⊥
parentReportStillCannotCreateChildVoice = Alice.parentReportDoesNotPromoteChildVoiceIdentity

institutionRecordStillCannotCreateWholeSystem : Alice.InstitutionRecordPromotesWholeSystemView → ⊥
institutionRecordStillCannotCreateWholeSystem = Alice.institutionRecordDoesNotPromoteWholeSystemView

------------------------------------------------------------------------
-- BIDI regression 3: intervention participation does not recover endorsement.
------------------------------------------------------------------------

data InterventionParticipationCase : Set where
  sameParticipationContestable : InterventionParticipationCase
  sameParticipationNoncontestable : InterventionParticipationCase

data ParticipationSurface : Set where sameInterventionParticipation : ParticipationSurface
data AgencyReading : Set where contestableAgency noncontestableAgency : AgencyReading

participationSurface : InterventionParticipationCase → ParticipationSurface
participationSurface _ = sameInterventionParticipation

agencyReading : InterventionParticipationCase → AgencyReading
agencyReading sameParticipationContestable = contestableAgency
agencyReading sameParticipationNoncontestable = noncontestableAgency

participationAgencyDefect : INF.NonFactorabilityWitness participationSurface agencyReading
participationAgencyDefect = INF.nonFactorabilityWitness
  sameParticipationContestable sameParticipationNoncontestable refl (λ ())

participationCannotFactorAgency :
  INF.FactorsThrough participationSurface agencyReading → ⊥
participationCannotFactorAgency =
  INF.witnessRulesOutEveryFlatFactorisation participationAgencyDefect

formalOptionStillCannotCreateAgency : Alice.FormalOptionPromotesAgency → ⊥
formalOptionStillCannotCreateAgency = Alice.formalOptionDoesNotPromoteAgency

------------------------------------------------------------------------
-- Reverse parent constraints. Concrete failures below the graph feed back to
-- the broader Education/Socialisation/Institution/Community concepts.
------------------------------------------------------------------------

record ReverseParentConstraint : Set where
  constructor reverse-parent-constraint
  field
    parentNode : String
    childWitness : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open ReverseParentConstraint public

educationConstraint : ReverseParentConstraint
educationConstraint = reverse-parent-constraint
  "Education"
  "Elliott intervention + Alice Brown agency/voice corpus"
  "teacher/institution observation, participant voice, contestability, consent and historical context remain distinct"
  false

socialisationConstraint : ReverseParentConstraint
socialisationConstraint = reverse-parent-constraint
  "Socialisation"
  "assigned category acquires treatment/authority meaning only in situated relations"
  "social transmission cannot be read as private endorsement or autonomous consent"
  false

institutionConstraint : ReverseParentConstraint
institutionConstraint = reverse-parent-constraint
  "Institution"
  "same institutional exercise can be experienced/interpreted differently by participants"
  "institutional record cannot replace affected-subject voice or settle ethical meaning"
  false

communityConstraint : ReverseParentConstraint
communityConstraint = reverse-parent-constraint
  "Community"
  "one classroom/training setting"
  "local intervention observations cannot be promoted to all communities, identities or racism mechanisms"
  false

------------------------------------------------------------------------
-- Exact Alice Brown source fibres retained instead of paraphrased away.
------------------------------------------------------------------------

aliceVoicePaper : EducationSources.PaperReference
aliceVoicePaper = EducationSources.voiceAgencyPaper

aliceParentAllyshipPaper : EducationSources.PaperReference
aliceParentAllyshipPaper = EducationSources.parentalAllyshipLensPaper

aliceBarrierPaper : EducationSources.PaperReference
aliceBarrierPaper = EducationSources.partnershipBarriersPaper

------------------------------------------------------------------------
-- Snowball payment. The named axes below are local discoveries, not a closed
-- ontology. The reverse constraints are the important BIDI payload.
------------------------------------------------------------------------

record ElliottAliceBrownBidiBoundary : Set where
  constructor elliott-alice-brown-bidi-boundary
  field
    qidsAndLinksRequestedWhenSafelyAvailable : Bool
    exactExerciseIdentityMayRemainUnresolved : Bool
    assignedCategoryDoesNotDeterminePower : Bool
    observedResponseDoesNotDetermineVoice : Bool
    participationDoesNotDetermineAgency : Bool
    teacherObserverDoesNotReplaceParticipantObserver : Bool
    institutionalRecordDoesNotReplaceWholeSystem : Bool
    programEvaluationDoesNotEqualHistoricalRacism : Bool
    historicalInstitutionalRacismRemainsSeparateAxis : Bool
    reverseLeafEvidenceConstrainsParentSemantics : Bool
    parentLabelsCannotEraseRecoveredDistinctions : Bool
    attributionTravelsWithSourceProposition : Bool
    presentAxisVocabularyClaimedComplete : Bool
open ElliottAliceBrownBidiBoundary public

canonicalElliottAliceBrownBidiBoundary : ElliottAliceBrownBidiBoundary
canonicalElliottAliceBrownBidiBoundary =
  elliott-alice-brown-bidi-boundary
    true true true true true true true true true true true true false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data JaneElliottQidCreatesExerciseValidity : Set where
data ClassroomExerciseCreatesRacismEquivalence : Set where
data ParticipantResponseCreatesConsent : Set where
data InstitutionalObservationCreatesParticipantMeaning : Set where
data OneInterventionDefinesEducationOrSocialisation : Set where

data DocumentaryIdentityCreatesEmpiricalTruth : Set where

janeElliottQidDoesNotCreateExerciseValidity : JaneElliottQidCreatesExerciseValidity → ⊥
janeElliottQidDoesNotCreateExerciseValidity ()

classroomExerciseDoesNotCreateRacismEquivalence : ClassroomExerciseCreatesRacismEquivalence → ⊥
classroomExerciseDoesNotCreateRacismEquivalence ()

participantResponseDoesNotCreateConsent : ParticipantResponseCreatesConsent → ⊥
participantResponseDoesNotCreateConsent ()

institutionalObservationDoesNotCreateParticipantMeaning : InstitutionalObservationCreatesParticipantMeaning → ⊥
institutionalObservationDoesNotCreateParticipantMeaning ()

oneInterventionDoesNotDefineEducationOrSocialisation : OneInterventionDefinesEducationOrSocialisation → ⊥
oneInterventionDoesNotDefineEducationOrSocialisation ()

documentaryIdentityDoesNotCreateEmpiricalTruth : DocumentaryIdentityCreatesEmpiricalTruth → ⊥
documentaryIdentityDoesNotCreateEmpiricalTruth ()

priorFormationBoundary : Prior.KinshipSocialisationEducationAuthorityBidiBoundary
priorFormationBoundary = Prior.canonicalKinshipSocialisationEducationAuthorityBidiBoundary

elliottBoundary : Elliott.ElliottExerciseBoundary
elliottBoundary = Elliott.canonicalElliottExerciseBoundary

aliceBoundary : Alice.AliceInstitutionalChoiceBoundary
aliceBoundary = Alice.canonicalAliceInstitutionalChoiceBoundary
