module DASHI.Education.DigitalESDIntersectionalSourceAcquisitionParetoRound20Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.IntersectionalNonFactorability as Intersection
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity

------------------------------------------------------------------------
-- ROUND 20: SELECTION ON PRIOR DIGITAL PARTICIPATION.
--
-- Post-Round-19 Python recutting leaves `whoWasExcludedByDesign` as the sole
-- deepest pre-corpus absence residual. This round targets a distinct mechanism:
-- digital participation/use/activity becomes an inclusion condition for the
-- evidence carrier itself.
--
-- The selections below may be methodologically appropriate to the bounded
-- research questions. DASHI's claim is only that evidence conditioned on prior
-- use/activity cannot recover the states removed by that conditioning rule.
------------------------------------------------------------------------

data Round20Residual : Set where
  eTextbookUsersOnlyAffordanceEvidence : Round20Residual
  lowLMSOrMissingTargetCourseFilterBeforePrediction : Round20Residual

record Round20Candidate : Set where
  constructor round20-candidate
  field
    source : Attr.AttributedSource
    sourceRoleReceipt : Snowball.SourceRoleSnowballReceipt source
    qidDemand : Identity.ExternalIdentityDemand
    deweyState : String
    targetResidual : Round20Residual
    sourceBoundedReading : String
    limitation : String
    includedInFinalCorpus : Bool
    includedInFinalCorpusIsFalse : includedInFinalCorpus ≡ false

open Round20Candidate public

mkRound20Candidate :
  (source : Attr.AttributedSource) →
  Round20Residual → String → String →
  Round20Candidate
mkRound20Candidate source residual reading limitation =
  round20-candidate
    source
    (Snowball.canonicalSourceRoleSnowballReceipt source)
    (Identity.mkOptionalIdentityDemand
      "DigitalESDIntersectionalSourceAcquisitionParetoRound20Exact"
      (Attr.sourceTitle source)
      (Attr.sourceTitle source)
      Identity.wikidataQid
      (Identity.unresolved "no independently verified same-object publication QID recorded by round 20"))
    "Dewey classification unresolved; no nearest-label substitution"
    residual reading limitation false refl

------------------------------------------------------------------------
-- D'Ambra/Akter/Mariani 2022: e-textbook use is a participation condition for
-- the user-engagement/affordance evidence surface.
------------------------------------------------------------------------

dambraAkterMarianiSource : Attr.AttributedSource
dambraAkterMarianiSource = Attr.mkDOISource
  "John D'Ambra; Shahriar Akter; Marcello Mariani"
  "Digital transformation of higher education in Australia: Understanding affordance dynamics in E-Textbook engagement and use"
  "Journal of Business Research 149, 283-295"
  "2022"
  "10.1016/j.jbusres.2022.05.048"
  "https://doi.org/10.1016/j.jbusres.2022.05.048"
  Attr.academicArticleSource
  "Australian higher-education mixed-method study of e-textbook affordance actualisation and engagement using interviews, focus groups, pilot survey and a 344-student main survey. For the survey carrier, respondents were required to have used e-textbooks, making prior e-textbook use part of the source-bounded participation condition."
  Attr.publicAttribution

dambraCandidate : Round20Candidate
dambraCandidate = mkRound20Candidate
  dambraAkterMarianiSource
  eTextbookUsersOnlyAffordanceEvidence
  "Direct design-exclusion donor: evidence about affordance actualisation among e-textbook users cannot by itself recover students who do not use e-textbooks, cannot explain why they do not use them, and cannot turn user accessibility/engagement observations into whole-population digital-transformation adequacy."
  "The users-only carrier is appropriate to the paper's stated engagement/use question. The limitation concerns downstream generalisation only: nonusers may fall outside that bounded consumer, and their absence does not invalidate the reported user-level relationships."

------------------------------------------------------------------------
-- Santos/Henriques 2023: course inclusion is conditioned on LMS engagement and
-- presence of target outcome classes before course-agnostic model evaluation.
------------------------------------------------------------------------

santosHenriquesSource : Attr.AttributedSource
santosHenriquesSource = Attr.mkDOISource
  "Ricardo Miguel Santos; Roberto Henriques"
  "Accurate, timely, and portable: Course-agnostic early prediction of student performance from LMS logs"
  "Computers and Education: Artificial Intelligence 5, 100175"
  "2023"
  "10.1016/j.caeai.2023.100175"
  "https://doi.org/10.1016/j.caeai.2023.100175"
  Attr.academicArticleSource
  "Higher-education learning-analytics study using LMS logs for at-risk and high-performing prediction. The retained analysis excludes courses with low LMS engagement or without students in the outcome populations of interest; retained courses also satisfy minimum enrolment/activity and class-presence conditions before portability/prediction evaluation."
  Attr.publicAttribution

santosCandidate : Round20Candidate
santosCandidate = mkRound20Candidate
  santosHenriquesSource
  lowLMSOrMissingTargetCourseFilterBeforePrediction
  "High-alpha design-selection donor: a model evaluated on courses retained after activity/population filters cannot silently establish portability to courses removed by those filters. Low-interaction contexts are analytically relevant precisely because they may contain early dropout or other behaviour that the threshold can erase."
  "Course filtering may be necessary for stable supervised prediction and does not itself establish bias or harm. The source's reported portability remains valid only at its tested source ceiling; excluded course contexts require separate evidence rather than automatic negative inference."

canonicalRound20Frontier : List Round20Candidate
canonicalRound20Frontier = santosCandidate ∷ dambraCandidate ∷ []

------------------------------------------------------------------------
-- DASHI collision 1: same observed digital-user evidence surface can coexist
-- with different nonuser states. User-conditioned evidence cannot recover
-- whether nonuse reflects choice, access, affordability, usability, relevance,
-- availability or another unobserved condition.
------------------------------------------------------------------------

data ParticipationSelectionWorld : Set where
  sameObservedUsersNonusersUnconstrained : ParticipationSelectionWorld
  sameObservedUsersNonusersConstrained : ParticipationSelectionWorld

data ObservedDigitalUserSurface : Set where
  sameObservedDigitalUsers : ObservedDigitalUserSurface

observedDigitalUserProjection : ParticipationSelectionWorld → ObservedDigitalUserSurface
observedDigitalUserProjection sameObservedUsersNonusersUnconstrained = sameObservedDigitalUsers
observedDigitalUserProjection sameObservedUsersNonusersConstrained = sameObservedDigitalUsers

nonuserConstraintMaterial : ParticipationSelectionWorld → Bool
nonuserConstraintMaterial sameObservedUsersNonusersUnconstrained = false
nonuserConstraintMaterial sameObservedUsersNonusersConstrained = true

nonuserConstraintDiffers :
  nonuserConstraintMaterial sameObservedUsersNonusersUnconstrained ≡
  nonuserConstraintMaterial sameObservedUsersNonusersConstrained → ⊥
nonuserConstraintDiffers ()

participationSelectionWitness :
  Intersection.NonFactorabilityWitness observedDigitalUserProjection nonuserConstraintMaterial
participationSelectionWitness =
  Intersection.nonFactorabilityWitness
    sameObservedUsersNonusersUnconstrained
    sameObservedUsersNonusersConstrained
    refl nonuserConstraintDiffers

ParticipationSelectionFactorisation : Set
ParticipationSelectionFactorisation =
  Intersection.FactorsThrough observedDigitalUserProjection nonuserConstraintMaterial

participationSelectionDoesNotFactorThroughObservedDigitalUserSurface :
  ParticipationSelectionFactorisation → ⊥
participationSelectionDoesNotFactorThroughObservedDigitalUserSurface =
  Intersection.witnessRulesOutEveryFlatFactorisation participationSelectionWitness

------------------------------------------------------------------------
-- DASHI collision 2: same retained-course model surface can coexist with
-- materially different excluded low-activity course contexts. The retained set
-- alone cannot recover portability to the removed context.
------------------------------------------------------------------------

data CourseFilterWorld : Set where
  sameRetainedCoursesExcludedContextComparable : CourseFilterWorld
  sameRetainedCoursesExcludedContextDifferent : CourseFilterWorld

data RetainedCourseSurface : Set where
  sameRetainedCourseModelSurface : RetainedCourseSurface

retainedCourseProjection : CourseFilterWorld → RetainedCourseSurface
retainedCourseProjection sameRetainedCoursesExcludedContextComparable = sameRetainedCourseModelSurface
retainedCourseProjection sameRetainedCoursesExcludedContextDifferent = sameRetainedCourseModelSurface

excludedCoursePortabilityAdequate : CourseFilterWorld → Bool
excludedCoursePortabilityAdequate sameRetainedCoursesExcludedContextComparable = true
excludedCoursePortabilityAdequate sameRetainedCoursesExcludedContextDifferent = false

excludedCoursePortabilityDiffers :
  excludedCoursePortabilityAdequate sameRetainedCoursesExcludedContextComparable ≡
  excludedCoursePortabilityAdequate sameRetainedCoursesExcludedContextDifferent → ⊥
excludedCoursePortabilityDiffers ()

courseFilterWitness :
  Intersection.NonFactorabilityWitness retainedCourseProjection excludedCoursePortabilityAdequate
courseFilterWitness =
  Intersection.nonFactorabilityWitness
    sameRetainedCoursesExcludedContextComparable
    sameRetainedCoursesExcludedContextDifferent
    refl excludedCoursePortabilityDiffers

CourseFilterFactorisation : Set
CourseFilterFactorisation =
  Intersection.FactorsThrough retainedCourseProjection excludedCoursePortabilityAdequate

courseFilterDoesNotFactorThroughRetainedCourseSurface :
  CourseFilterFactorisation → ⊥
courseFilterDoesNotFactorThroughRetainedCourseSurface =
  Intersection.witnessRulesOutEveryFlatFactorisation courseFilterWitness

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data Round20CandidateCreatesIncludedStudy : Set where
data UsersOnlySampleCreatesWholeStudentPopulation : Set where
data PriorUseCreatesAdoptionOrAccessibilityTruth : Set where
data FilteredCourseSetCreatesUniversalCoursePortability : Set where
data LowLMSActivityCreatesNoLearningOrNeed : Set where

round20CandidateDoesNotCreateIncludedStudy : Round20CandidateCreatesIncludedStudy → ⊥
round20CandidateDoesNotCreateIncludedStudy ()

usersOnlySampleDoesNotCreateWholeStudentPopulation :
  UsersOnlySampleCreatesWholeStudentPopulation → ⊥
usersOnlySampleDoesNotCreateWholeStudentPopulation ()

priorUseDoesNotCreateAdoptionOrAccessibilityTruth :
  PriorUseCreatesAdoptionOrAccessibilityTruth → ⊥
priorUseDoesNotCreateAdoptionOrAccessibilityTruth ()

filteredCourseSetDoesNotCreateUniversalCoursePortability :
  FilteredCourseSetCreatesUniversalCoursePortability → ⊥
filteredCourseSetDoesNotCreateUniversalCoursePortability ()

lowLMSActivityDoesNotCreateNoLearningOrNeed :
  LowLMSActivityCreatesNoLearningOrNeed → ⊥
lowLMSActivityDoesNotCreateNoLearningOrNeed ()

round20Reading : String
round20Reading =
  "Round 20 pays the final pre-corpus excluded-by-design residual with selection on prior digital participation. D'Ambra/Akter/Mariani study e-textbook affordance/engagement in a carrier conditioned on prior e-textbook use; Santos/Henriques evaluate course-agnostic LMS prediction after filtering low-engagement courses and courses lacking target performance populations. DASHI separately owns finite witnesses showing that observed-user evidence cannot recover nonuser constraints and a retained-course model surface cannot recover portability to excluded course contexts. These selections may be appropriate to their source questions and create no automatic bias/harm verdict or final Digital-ESD corpus inclusion."
