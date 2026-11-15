# Digital-ESD hyperfabric — exact-source print, part 5 of 5

**Source ref:** `agent/digital-esd-source-crosspollination-20261101` (2026-11-01). **Role:** full-text snapshot of the independent EfS derivation, six candidate comparisons, seven principle-survival receipts, canonical reuse adapter, all sixteen additional-source candidate cases, regression checks and Digital-ESD aggregate import graph.

This is the **draft** PR #1237 + #1448 overlay; it has not been verified by a local Agda kernel in this session. Original external paper authors are credited in source data, but cross-paper/hyperfabric constructions remain DASHI-generated and do not automatically become those authors' results. Source admission and empirical effects remain separate.

1. `DASHI/Education/DigitalESDEfSIndependentDerivationExact.agda` — SHA `cb62f21bcadaf18b044fbbe5989c6a3838de2148`, 149 lines
2. `DASHI/Education/DigitalESDEfSIndependentChallengeExact.agda` — SHA `dc17eafa5eb94671649ec29d561e292b84eb63a2`, 99 lines
3. `DASHI/Education/DigitalESDPrincipleSurvivalAuditExact.agda` — SHA `bf455582611a3bd1dfc7efab721ddaec9ecce315`, 126 lines
4. `DASHI/Education/DigitalESDEfSCanonicalReuseAdapterExact.agda` — SHA `84695061dcd83eec8f8d2d6eedfb419cb8af87b3`, 93 lines
5. `DASHI/Education/DigitalESDEfSSourceCrossPollinationExact.agda` — SHA `043ba5f06233f13a29d4668766a2e3f58138dbfa`, 548 lines
6. `DASHI/Education/DigitalESDEfSSourceCrossPollinationRegression.agda` — SHA `aab9f58fcb55eadef5298b605b9165fabcfdd41a`, 105 lines
7. `DASHI/EverythingDigitalESDReciprocalBraid.agda` — SHA `f336e9ec0e5cfd84f3cdbdad6b6df2128eb50c7b`, 227 lines

## DASHI/Education/DigitalESDEfSIndependentDerivationExact.agda

Source: https://github.com/chboishabba/dashi_agda/blob/agent/digital-esd-source-crosspollination-20261101/DASHI/Education/DigitalESDEfSIndependentDerivationExact.agda

Blob SHA: `cb62f21bcadaf18b044fbbe5989c6a3838de2148`

```agda
module DASHI.Education.DigitalESDEfSIndependentDerivationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDEfSPedagogicalReciprocityExact as Prior

-- EfS-FIRST CARRIER. No import of the Digital seven-principle owner.
-- GreenComp is a policy/reference competency framework, not a causal study.
-- Elliott is a practitioner/theoretical EfS contribution.
-- Vikane/Hoydalsvik is situated Norwegian ECE empirical evidence.
-- None receives intervention-effect or cross-context authority.

data EfSSourceClass : Set where
  competenceReferenceFramework : EfSSourceClass
  practitionerTheory : EfSSourceClass
  situatedEmpiricalStudy : EfSSourceClass

data EfSTheme : Set where
  valuesAndJustice : EfSTheme
  systemsAndProblemFraming : EfSTheme
  possibleFutures : EfSTheme
  participationAndAction : EfSTheme
  ecologicalRelationships : EfSTheme
  educatorEnactmentGap : EfSTheme

data GreenCompArea : Set where
  embodyingSustainabilityValues : GreenCompArea
  embracingComplexity : GreenCompArea
  envisioningSustainableFutures : GreenCompArea
  actingForSustainability : GreenCompArea

data GreenCompCompetence : Set where
  valuingSustainability : GreenCompCompetence
  supportingFairness : GreenCompCompetence
  promotingNature : GreenCompCompetence
  systemsThinking : GreenCompCompetence
  criticalThinking : GreenCompCompetence
  problemFraming : GreenCompCompetence
  futuresLiteracy : GreenCompCompetence
  adaptability : GreenCompCompetence
  exploratoryThinking : GreenCompCompetence
  politicalAgency : GreenCompCompetence
  collectiveAction : GreenCompCompetence
  individualInitiative : GreenCompCompetence

area : GreenCompCompetence → GreenCompArea
area valuingSustainability = embodyingSustainabilityValues
area supportingFairness = embodyingSustainabilityValues
area promotingNature = embodyingSustainabilityValues
area systemsThinking = embracingComplexity
area criticalThinking = embracingComplexity
area problemFraming = embracingComplexity
area futuresLiteracy = envisioningSustainableFutures
area adaptability = envisioningSustainableFutures
area exploratoryThinking = envisioningSustainableFutures
area politicalAgency = actingForSustainability
area collectiveAction = actingForSustainability
area individualInitiative = actingForSustainability

greenCompCompetences : List GreenCompCompetence
greenCompCompetences =
  valuingSustainability ∷ supportingFairness ∷ promotingNature ∷
  systemsThinking ∷ criticalThinking ∷ problemFraming ∷
  futuresLiteracy ∷ adaptability ∷ exploratoryThinking ∷
  politicalAgency ∷ collectiveAction ∷ individualInitiative ∷ []

greenCompURL : String
greenCompURL =
  "https://joint-research-centre.ec.europa.eu/scientific-activities/key-competences-lifelong-learning/greencomp-european-sustainability-competence-framework/greencomp-conceptual-reference-model_en"

record IndependentThemeReceipt : Set where
  constructor independent-theme
  field
    theme : EfSTheme
    sourceReference : String
    sourceClass : EfSSourceClass
    basis : String
    limitation : String
    formulatedWithoutDigitalPrinciple : Bool
    independenceWitness : formulatedWithoutDigitalPrinciple ≡ true
open IndependentThemeReceipt public

valuesReceipt : IndependentThemeReceipt
valuesReceipt = independent-theme valuesAndJustice greenCompURL
  competenceReferenceFramework
  "GreenComp: valuing sustainability and supporting fairness; values are open to reflection."
  "Competence specification, not evidence that a given digital intervention teaches values."
  true refl

systemsReceipt : IndependentThemeReceipt
systemsReceipt = independent-theme systemsAndProblemFraming greenCompURL
  competenceReferenceFramework
  "GreenComp: systems thinking, critical thinking and problem framing."
  "Framework descriptors do not establish measured systems understanding."
  true refl

futureReceipt : IndependentThemeReceipt
futureReceipt = independent-theme possibleFutures greenCompURL
  competenceReferenceFramework
  "GreenComp: futures literacy, adaptability and exploratory thinking."
  "Futures scenario production does not imply future outcomes."
  true refl

collectiveReceipt : IndependentThemeReceipt
collectiveReceipt = independent-theme participationAndAction greenCompURL
  competenceReferenceFramework
  "GreenComp: political agency, collective action and individual initiative."
  "Participation and stated intention are not demonstrated agency or action."
  true refl

ecologicalReceipt : IndependentThemeReceipt
ecologicalReceipt = independent-theme ecologicalRelationships
  (Prior.EfSSource.exactLocator Prior.elliottEfS)
  practitionerTheory
  "Elliott: ecological relations, critical reflection and child participation in sustainability."
  "A practitioner-theoretical account is not an intervention or general prevalence estimate."
  true refl

enactmentReceipt : IndependentThemeReceipt
enactmentReceipt = independent-theme educatorEnactmentGap
  (Prior.EfSSource.exactLocator Prior.vikaneHoydalsvik)
  situatedEmpiricalStudy
  "Situated teacher-understanding versus transformative-practice problem in Norwegian ECE."
  "Neither causal explanation nor automatic transfer to other ages, countries, or digital delivery."
  true refl

independentlyNominatedThemes : List IndependentThemeReceipt
independentlyNominatedThemes =
  valuesReceipt ∷ systemsReceipt ∷ futureReceipt ∷ collectiveReceipt ∷
  ecologicalReceipt ∷ enactmentReceipt ∷ []

-- The source-derived competency labels, the grouping into our six candidate
-- study themes, and a digital crosswalk have different origins/claim ceilings.
data SixThemesAreUniquelyDeterminedBySources : Set where
data CompetencyFrameworkProvesEffect : Set where
data IndependentFormalDerivationIsIndependentHumanCoding : Set where

noUniqueSixThemeClaim : SixThemesAreUniquelyDeterminedBySources → ⊥
noUniqueSixThemeClaim ()
noCompetenceEffectPromotion : CompetencyFrameworkProvesEffect → ⊥
noCompetenceEffectPromotion ()
noHumanCodingPromotion : IndependentFormalDerivationIsIndependentHumanCoding → ⊥
noHumanCodingPromotion ()
```

## DASHI/Education/DigitalESDEfSIndependentChallengeExact.agda

Source: https://github.com/chboishabba/dashi_agda/blob/agent/digital-esd-source-crosspollination-20261101/DASHI/Education/DigitalESDEfSIndependentChallengeExact.agda

Blob SHA: `dc17eafa5eb94671649ec29d561e292b84eb63a2`

```agda
module DASHI.Education.DigitalESDEfSIndependentChallengeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDEfSIndependentDerivationExact as EfS
import DASHI.Education.DigitalESDTransferablePedagogicalPrinciplesExact as Digital

data ComparisonOutcome : Set where
  candidateConvergence : ComparisonOutcome
  candidateTension : ComparisonOutcome
  unmatchedEfSRequirement : ComparisonOutcome
  openEmpiricalComparison : ComparisonOutcome

data DigitalTarget : Set where
  matched : Digital.TransferablePedagogicalPrinciple → DigitalTarget
  noAssertedMatch : DigitalTarget

record ComparisonReceipt : Set where
  constructor comparison
  field
    independentEfS : EfS.IndependentThemeReceipt
    digitalTarget : DigitalTarget
    outcome : ComparisonOutcome
    interpretation : String
    challengeToDigitalFramework : String
    unresolvedEvidence : String
    authorReviewRequired : Bool
    reviewGate : authorReviewRequired ≡ true
open ComparisonReceipt public

systemsComparison : ComparisonReceipt
systemsComparison = comparison EfS.systemsReceipt
  (matched Digital.contextualCustodianship) candidateConvergence
  "Attention to relational context resembles systems thinking but is not yet a measured systems competence."
  "Assess feedback, boundaries, temporal effects and transfer rather than assuming relational vocabulary suffices."
  "Independent scoring of student systems reasoning and domain transfer."
  true refl

valuesComparison : ComparisonReceipt
valuesComparison = comparison EfS.valuesReceipt
  (matched Digital.feedbackAsRevisableSignal) candidateTension
  "Revisable feedback allows questioning classifications, but value negotiation and justice are not reducible to feedback."
  "Retain independently named normative/value reflection, rather than absorbing it into classification contestability."
  "Learner deliberation, justice-related reasoning, whose values shape evaluation criteria."
  true refl

futuresComparison : ComparisonReceipt
futuresComparison = comparison EfS.futureReceipt
  (matched Digital.iterativeEvidenceReturnAndRecharting) candidateConvergence
  "Iterative revision potentially supports futures literacy but is not identical to imagining alternative futures."
  "Explicitly test anticipatory thinking, alternatives, uncertainty and time horizons."
  "Independent prospective futures competence measurement."
  true refl

collectiveComparison : ComparisonReceipt
collectiveComparison = comparison EfS.collectiveReceipt
  (matched Digital.constitutiveLearnerAgency) candidateTension
  "Individual learner voice and authority need not amount to collaborative or political agency."
  "Open separate collective-action and political-agency obligations."
  "Observed group decision rights, real-world enactment, and collective outcomes."
  true refl

ecologicalComparison : ComparisonReceipt
ecologicalComparison = comparison EfS.ecologicalReceipt noAssertedMatch
  unmatchedEfSRequirement
  "Ecological relationships and more-than-human concerns have no complete same-purpose digital pedagogical counterpart among the seven."
  "Keep ecological orientation as a possible new educational principle rather than treating plural human observers as sufficient."
  "Ecological pedagogy sources, age/context transfer, ecological literacy/action observations."
  true refl

enactmentComparison : ComparisonReceipt
enactmentComparison = comparison EfS.enactmentReceipt
  (matched Digital.situatedRelationalEngagement) candidateTension
  "An engagement mechanism alone cannot establish teachers' EfS understanding or transformative enactment."
  "Add educator preparation/practice and institutional support as independently assessed conditions."
  "Longitudinal teaching-practice evidence outside source population."
  true refl

canonicalChallenges : List ComparisonReceipt
canonicalChallenges =
  systemsComparison ∷ valuesComparison ∷ futuresComparison ∷
  collectiveComparison ∷ ecologicalComparison ∷ enactmentComparison ∷ []

data TwoSidedAlignmentProvesEffect : Set where
data MatchedPrinciplesExhaustEfS : Set where
data UnmatchedThemeIsAutomaticallyNewPrinciple : Set where
twoSidedAlignmentDoesNotProveEffect : TwoSidedAlignmentProvesEffect → ⊥
twoSidedAlignmentDoesNotProveEffect ()
matchedPrinciplesDoNotExhaustEfS : MatchedPrinciplesExhaustEfS → ⊥
matchedPrinciplesDoNotExhaustEfS ()
unmatchedDoesNotAutomaticallyDemandNewPrinciple :
  UnmatchedThemeIsAutomaticallyNewPrinciple → ⊥
unmatchedDoesNotAutomaticallyDemandNewPrinciple ()
```

## DASHI/Education/DigitalESDPrincipleSurvivalAuditExact.agda

Source: https://github.com/chboishabba/dashi_agda/blob/agent/digital-esd-source-crosspollination-20261101/DASHI/Education/DigitalESDPrincipleSurvivalAuditExact.agda

Blob SHA: `bf455582611a3bd1dfc7efab721ddaec9ecce315`

```agda
module DASHI.Education.DigitalESDPrincipleSurvivalAuditExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDTransferablePedagogicalPrinciplesExact as Digital
import DASHI.Education.DigitalESDEfSIndependentChallengeExact as EfS
import DASHI.Education.DigitalESDEvidenceBraidTensionExact as Braid

-- A conceptual comparison is not a completed corpus adjudication. A source
-- register names potentially relevant papers; it does not prove source spans,
-- independent effect, representativeness, or admitted review inclusion.
data SurvivalVerdict : Set where
  provisionallyRetain : SurvivalVerdict
  provisionalRevisionNeeded : SurvivalVerdict
  provisionalSplitCandidate : SurvivalVerdict
  empiricalStatusUnresolved : SurvivalVerdict

data ReviewStage : Set where
  attributedPreSearchSynthesis : ReviewStage
  fullTextSpanReviewed : ReviewStage
  sourceAuditAdmitted : ReviewStage
  crossCorpusAdjudicated : ReviewStage

record PrincipleSurvivalReceipt : Set where
  constructor survival
  field
    principle : Digital.TransferablePedagogicalPrinciple
    sourceScope : String
    existingSupport : String
    counterEvidenceOrBlindSpot : String
    relevantContexts : String
    candidateVerdict : SurvivalVerdict
    currentReviewStage : ReviewStage
    nextDiscriminator : String
    actualCorpusAdjudicationObserved : Bool
    notYetAdjudicated : actualCorpusAdjudicationObserved ≡ true → ⊥
open PrincipleSurvivalReceipt public

engagement : PrincipleSurvivalReceipt
engagement = survival Digital.situatedRelationalEngagement
  "Online higher education, teacher-education support, humour pedagogy, ecology of data"
  "Source-attributed digital corpus supports the need to distinguish access from relational engagement; EfS educator-practice critique provides a challenge to mere topic coverage."
  "Engagement does not establish systems learning, ecological concern or collective action."
  "Higher education and regional teacher education; Norwegian ECE is a non-transferred challenge context."
  provisionalRevisionNeeded attributedPreSearchSynthesis
  "Retain situated engagement as mechanism, separately measure EfS understanding and transformative enactment."
  false (λ ())

feedback : PrincipleSurvivalReceipt
feedback = survival Digital.feedbackAsRevisableSignal
  "OEF/AI feedback feasibility and higher-education student voice"
  "Classification feasibility plus voice/agency and data-ecology critiques support provisional interpretive revisability."
  "Algorithmic feedback is not values reflection, ecological evaluation, student authority or outcome improvement."
  "Higher education; sustainability normative conflict still requires independent evidence."
  provisionalRevisionNeeded attributedPreSearchSynthesis
  "Find source spans for contested sustainability-value discussions and compare feedback-only versus deliberative activities."
  false (λ ())

agency : PrincipleSurvivalReceipt
agency = survival Digital.constitutiveLearnerAgency
  "Student-voice scholarship and student-identified online supports"
  "Epistemic expansion arguments support involving learners in interpretation and educational design."
  "Individual agency does not guarantee consequential collective decision rights or political efficacy."
  "Higher-education student voice; ECE collective action needs explicit context transfer."
  provisionalSplitCandidate attributedPreSearchSynthesis
  "Discriminate individual voice, co-design, group deliberation, decision authority and realised collective action."
  false (λ ())

support : PrincipleSurvivalReceipt
support = survival Digital.adaptiveSupportWithLocalChoice
  "Regional Australian teacher education: 584 student responses; feedback-support cross-paper inference"
  "Five candidate support families with locally selectable many-to-many routing."
  "No causal universal strategy table; personalisation could weaken or enable collective inquiry."
  "Australian regional teacher education; transfer to other cohorts and EfS projects remains open."
  provisionalRevisionNeeded attributedPreSearchSynthesis
  "Compare inclusive adaptive supports with sustained collective EfS participation and learner choice."
  false (λ ())

observers : PrincipleSurvivalReceipt
observers = survival Digital.pluralSituatedObservers
  "Disability allyship, parent-school partnerships, student voice and ecological observer formalism"
  "Distinct observers and different knowledge histories cannot be silently flattened."
  "Parent voice cannot replace child voice; scientific ecological indicators cannot impersonate non-human testimony or Indigenous authority."
  "Disability and student-voice contexts; ecological contexts require source-specific scope."
  provisionalRevisionNeeded attributedPreSearchSynthesis
  "Audit observer provenance, relevant non-human observations and community-specific authority."
  false (λ ())

custodianship : PrincipleSurvivalReceipt
custodianship = survival Digital.contextualCustodianship
  "Ecology-of-data qualitative methodology and situated cross-domain caution"
  "Person-place, value-flow, affordance and data-curation responsibilities motivate context-rich interpretation."
  "Context representation is not demonstrated systems-thinking competence or complete ecological interpretation."
  "Situated qualitative research; transfer to EfS field cases remains to be observed."
  provisionalRevisionNeeded attributedPreSearchSynthesis
  "Test when omitting ecological, intergenerational or authority coordinates changes the educational conclusion."
  false (λ ())

revision : PrincipleSurvivalReceipt
revision = survival Digital.iterativeEvidenceReturnAndRecharting
  "Cross-paper digital feedback, student voice, support and data ecology"
  "Evidence return and contestable revision form an attributable synthesis hypothesis."
  "Revision of interpretations is not futures literacy, longitudinal transformation or actual collective action."
  "Online higher education; future-oriented sustainability teaching requires separate outcome data."
  provisionalRevisionNeeded attributedPreSearchSynthesis
  "Compare counterfactual futures reasoning and observed institutional change across follow-up periods."
  false (λ ())

canonicalSurvivalReceipts : List PrincipleSurvivalReceipt
canonicalSurvivalReceipts =
  engagement ∷ feedback ∷ agency ∷ support ∷ observers ∷ custodianship ∷ revision ∷ []

-- Review-stage separation: none of the seven is marked as independently
-- screened, fully extracted and cross-corpus adjudicated on this source ledger.
data SevenPrinciplesEmpiricallyValidated : Set where
data SevenPrinciplesDefeatedByEfS : Set where
noPrematureValidation : SevenPrinciplesEmpiricallyValidated → ⊥
noPrematureValidation ()
noPrematureDefeat : SevenPrinciplesDefeatedByEfS → ⊥
noPrematureDefeat ()
```

## DASHI/Education/DigitalESDEfSCanonicalReuseAdapterExact.agda

Source: https://github.com/chboishabba/dashi_agda/blob/agent/digital-esd-source-crosspollination-20261101/DASHI/Education/DigitalESDEfSCanonicalReuseAdapterExact.agda

Blob SHA: `84695061dcd83eec8f8d2d6eedfb419cb8af87b3`

```agda
module DASHI.Education.DigitalESDEfSCanonicalReuseAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDEvidenceBraidTensionExact as Braid
import DASHI.Education.DigitalESDEfSIndependentChallengeExact as EfS
import DASHI.Education.DigitalESDEfSIndependentDerivationExact as Derivation
import DASHI.Biology.AliceBrownCorpusLoom as Alice
import DASHI.Core.RelationalEpistemicProcessSourceBridgeExact as Relational
import DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact as TwoEyed
import DASHI.Education.EducationSituatedInvestmentTrajectoryExact as Trajectory
import DASHI.Education.DigitalESDDBNativeAcademicWorldExecutionExact as World

-- Reuses existing typed epistemic-braid vocabulary rather than adding a new
-- conflict ontology. An outcome classification is an authored inference,
-- not an automatic verdict about the underlying source.
relationFor : EfS.ComparisonOutcome → Braid.BraidRelation
relationFor EfS.candidateConvergence = Braid.convergence
relationFor EfS.candidateTension = Braid.productiveTension
relationFor EfS.unmatchedEfSRequirement = Braid.scopeDifference
relationFor EfS.openEmpiricalComparison = Braid.unresolvedConflict

record EfSReuseReceipt : Set where
  constructor reuse-receipt
  field
    challenge : EfS.ComparisonReceipt
    braid : Braid.TensionReceipt
    braidMatchesChallenge : Braid.TensionReceipt.relation braid ≡
      relationFor (EfS.ComparisonReceipt.outcome challenge)
    sourceFibresRemainIndependent : Bool
    sourceFibresRemainIndependentIsTrue : sourceFibresRemainIndependent ≡ true
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

open EfSReuseReceipt public

reuse : (r : EfS.ComparisonReceipt) → EfSReuseReceipt
reuse r = reuse-receipt r
  (Braid.tension-receipt
    (Derivation.IndependentThemeReceipt.sourceReference
      (EfS.ComparisonReceipt.independentEfS r))
    "DASHI.Education.DigitalESDTransferablePedagogicalPrinciplesExact"
    (Derivation.IndependentThemeReceipt.sourceReference
      (EfS.ComparisonReceipt.independentEfS r))
    "DASHI.Biology.EducationCorpusSourceRegistry"
    (relationFor (EfS.ComparisonReceipt.outcome r))
    (EfS.ComparisonReceipt.challengeToDigitalFramework r))
  refl true refl true refl

canonicalReuse : List EfSReuseReceipt
canonicalReuse =
  reuse EfS.systemsComparison ∷
  reuse EfS.valuesComparison ∷
  reuse EfS.futuresComparison ∷
  reuse EfS.collectiveComparison ∷
  reuse EfS.ecologicalComparison ∷
  reuse EfS.enactmentComparison ∷ []

existingCorpus : Alice.AliceBrownCorpusLoom
existingCorpus = Alice.canonicalAliceBrownCorpusLoom

existingTwoEyedBoundary : TwoEyed.KimmererTwoEyedSeeingBoundary
existingTwoEyedBoundary = TwoEyed.canonicalKimmererTwoEyedSeeingBoundary

existingRelationalBoundary : Relational.RelationalEpistemicProcessBoundary
existingRelationalBoundary = Relational.canonicalRelationalEpistemicProcessBoundary

-- The 19+ coordinate learning/evidence trajectory and the DB-native
-- manuscript extraction are explicitly reused as owners, NOT flattened into
-- the 6 EfS themes or 7 digital principles.
educationTrajectoryCoordinates : List Trajectory.TrajectoryCoordinate
educationTrajectoryCoordinates = Trajectory.trajectoryCoordinates

dbNativeCoordinateCount : Nat
dbNativeCoordinateCount = World.extractionCoordinateCount

data SourcePairingIsEmpiricalEffect : Set where
data InterpretiveBridgeOverridesCommunityAuthority : Set where
data ParserNominationPaysEfSClaim : Set where

sourcePairingDoesNotProveEffect : SourcePairingIsEmpiricalEffect → ⊥
sourcePairingDoesNotProveEffect ()
interpretationDoesNotOverrideAuthority : InterpretiveBridgeOverridesCommunityAuthority → ⊥
interpretationDoesNotOverrideAuthority ()
parserNominationCannotPayClaim : ParserNominationPaysEfSClaim → ⊥
parserNominationCannotPayClaim ()
```

## DASHI/Education/DigitalESDEfSSourceCrossPollinationExact.agda

Source: https://github.com/chboishabba/dashi_agda/blob/agent/digital-esd-source-crosspollination-20261101/DASHI/Education/DigitalESDEfSSourceCrossPollinationExact.agda

Blob SHA: `043ba5f06233f13a29d4668766a2e3f58138dbfa`

```agda
module DASHI.Education.DigitalESDEfSSourceCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Education.DigitalESDEfSPedagogicalReciprocityExact as Prior
import DASHI.Education.DigitalESDTransferablePedagogicalPrinciplesExact as Digital
import DASHI.Education.DigitalESDEvidenceBraidTensionExact as Braid
import DASHI.Education.DigitalESDTilburySourceRoleExact as Tilbury

-- Supplied published sources plus direct reuse of the existing Tilbury atlas.
-- The bridges are new DASHI candidate interpretations, never paper findings.
-- No admission, independent EfS source-span review, or causal outcome is claimed.
-- Private manuscript drafts are deliberately absent from this public module.
-- All candidate claims retain the original source identity, role, and limit.

taimurOnukiSource : Attr.AttributedSource
taimurOnukiSource = Attr.mkDOISource
  "Sadaf Taimur; Motoharu Onuki"
  "Design thinking as digital transformative pedagogy in higher sustainability education: Cases from Japan and Germany"
  "International Journal of Educational Research 114, 101994"
  "2022"
  "10.1016/j.ijer.2022.101994"
  "https://doi.org/10.1016/j.ijer.2022.101994"
  Attr.academicArticleSource
  "Reported application of digital transformative pedagogy components in two cases and participant perceptions of learning conditions. BOUNDARY: No independent proof of durable personal transformation, ecological outcomes, general intervention effects or transfer to other institutions."
  Attr.publicAttribution

nilssonDahlstromSource : Attr.AttributedSource
nilssonDahlstromSource = Attr.mkDOISource
  "Åsa Nilsson Dahlström"
  "Challenges and opportunities for social sustainability in education: a scoping review"
  "Cogent Social Sciences 11(1), 2491706"
  "2025"
  "10.1080/23311886.2025.2491706"
  "https://doi.org/10.1080/23311886.2025.2491706"
  Attr.academicArticleSource
  "Documents differences and conceptual/assessment difficulties in definitions and enactment of social sustainability. BOUNDARY: The review's denominators and synthesis belong to its author; they cannot pay Digital-ESD's database, admission or outcome obligations."
  Attr.publicAttribution

adefilaEcoCOILSource : Attr.AttributedSource
adefilaEcoCOILSource = Attr.mkDOISource
  "Arinola Adefila; Osman Arrobbio; Geraldine Brown; Zoe Robinson; Gary Spolander; Ilkhom Soliev; Bret Willers; Luca Morini; Dario Padovan; Katherine Wimpenny"
  "Ecologized Collaborative Online International Learning: Tackling Wicked Sustainability Problems Through Education for Sustainable Development"
  "Journal of Teacher Education for Sustainability 23(1), 41-57"
  "2021"
  "10.2478/jtes-2021-0004"
  "https://doi.org/10.2478/jtes-2021-0004"
  Attr.academicArticleSource
  "Models participatory co-creation, intercultural participation, coalition building and sustainability problem inquiry in digital settings. BOUNDARY: Conceptual/model claims are not independent measurement of community authority, collective impacts or ecological outcomes."
  Attr.publicAttribution

singhCommunitySource : Attr.AttributedSource
singhCommunitySource = Attr.mkDOISource
  "Wafa Singh; Raisuyah Bhagwan; Manju Singh"
  "Leveraging community-engaged teaching and learning in higher education institutions for advancing sustainable development: a literature review"
  "International Journal of Sustainability in Higher Education 27(1), 114-131"
  "2026"
  "10.1108/IJSHE-01-2024-0066"
  "https://doi.org/10.1108/IJSHE-01-2024-0066"
  Attr.academicArticleSource
  "Reviews pedagogical arrangements, community partnerships, sustainability competencies and conditions that constrain enactment. BOUNDARY: Review-level reports do not demonstrate causal effects of a specific digital intervention or authorise a university to speak for community partners."
  Attr.publicAttribution

barthCompetenciesSource : Attr.AttributedSource
barthCompetenciesSource = Attr.mkDOISource
  "Matthias Barth; Jasmin Godemann; Marco Rieckmann; Ute Stoltenberg"
  "Developing key competencies for sustainable development in higher education"
  "International Journal of Sustainability in Higher Education 8(4), 416-430"
  "2007"
  "10.1108/14676370710823582"
  "https://doi.org/10.1108/14676370710823582"
  Attr.academicArticleSource
  "Identifies roles for cognitive and non-cognitive dispositions, multiple learning contexts and student responsibility in competence development. BOUNDARY: Original authors identify remaining uncertainty about interdependencies; no digital intervention comparison or universal causal mechanism."
  Attr.publicAttribution

giridharanCompetenciesSource : Attr.AttributedSource
giridharanCompetenciesSource = Attr.mkNoDOISource
  "Beena Giridharan"
  "Learning for a Sustainable Future: Developing Key Competencies"
  "Introduction to Sustainable Development Leadership and Strategies in Higher Education, chapter 8, Emerald, pp. 155-166"
  "2020"
  "https://ebookcentral.proquest.com/lib/usq/detail.action?docID=6238640"
  Attr.academicChapterSource
  "Develops a strategic account of future-facing competencies, flexible learning, digital provision and changing institutional models. BOUNDARY: Conceptual and policy-facing discussion does not supply measured evidence of sustainability competence, durability or employment benefit."
  Attr.publicAttribution

jepsenCookeAccessibilitySource : Attr.AttributedSource
jepsenCookeAccessibilitySource = Attr.mkNoDOISource
  "Thomas F. Jepsen; Theo Cooke"
  "Intentional Inclusion in HigherEd E-Learning: Embedding Universal Accessibility Through Digital Technology"
  "2nd Global Trends in E-learning Forum, pp. 61-65; SSRN 4320172"
  "2023"
  "https://ssrn.com/abstract=4320172"
  Attr.practitionerSource
  "Argues that design must accommodate conflicting access needs and context-specific learner constraints. BOUNDARY: Industry perspective and advocated outcomes do not establish audited disability accessibility, retention effects or causal employment outcomes."
  Attr.publicAttribution

ferreiraRyanTilburySource : Attr.AttributedSource
ferreiraRyanTilburySource = Attr.mkDOISource
  "Jo-Anne Ferreira; Lisa Ryan; Daniella Tilbury"
  "Mainstreaming education for sustainable development in initial teacher education in Australia: a review of existing professional development models"
  "Journal of Education for Teaching 33(2), 225-239"
  "2007"
  "10.1080/02607470701259515"
  "https://doi.org/10.1080/02607470701259515"
  Attr.academicArticleSource
  "Separates resource delivery, professional learning and more systemic change approaches in teacher education. BOUNDARY: Initial teacher education context and professional-development models do not independently establish effects in digital university teaching."
  Attr.publicAttribution

ferreiraRyanSystemSource : Attr.AttributedSource
ferreiraRyanSystemSource = Attr.mkDOISource
  "Jo-Anne Ferreira; Lisa Ryan"
  "Working the System: A Model for System-Wide Change in Pre-Service Teacher Education"
  "Australian Journal of Teacher Education 37(12)"
  "2013"
  "10.14221/ajte.2012v37n12.3"
  "https://doi.org/10.14221/ajte.2012v37n12.3"
  Attr.academicArticleSource
  "Studies organisational curriculum change and proposes an integrated Mainstreaming Change model across system levels. BOUNDARY: Proposed systems model is not proof of general digital-ESD or longitudinal intervention outcomes."
  Attr.publicAttribution

ferreiraRyanDavisSource : Attr.AttributedSource
ferreiraRyanDavisSource = Attr.mkDOISource
  "Jo-Anne Ferreira; Lisa Ryan; Julie Davis"
  "Developing Knowledge and Leadership in Pre-Service Teacher Education Systems"
  "Australian Journal of Environmental Education 31(2), 194-207"
  "2015"
  "10.1017/aee.2015.24"
  "https://doi.org/10.1017/aee.2015.24"
  Attr.academicArticleSource
  "Examines change through a wider institutional system and distinguishes professional knowledge from leadership for change. BOUNDARY: Authorship and studied context do not establish a universal digital higher-education intervention effect."
  Attr.publicAttribution

ryanFerreira2024Source : Attr.AttributedSource
ryanFerreira2024Source = Attr.mkDOISource
  "Lisa D. Ryan; Jo-Anne L. Ferreira"
  "Embedding Sustainability in Teacher Education in Australia"
  "Oxford Research Encyclopedia of Education"
  "2024"
  "10.1093/acrefore/9780190264093.013.1810"
  "https://doi.org/10.1093/acrefore/9780190264093.013.1810"
  Attr.academicArticleSource
  "Reviews policy, curriculum, educator preparation, accreditation and common-vision strategies in embedding EfS. BOUNDARY: A programme case and reference synthesis do not establish measured digital-EfS effects or direct transfer across countries and HE sectors."
  Attr.publicAttribution

blackRyanJiNatureSource : Attr.AttributedSource
blackRyanJiNatureSource = Attr.mkDOISource
  "Ali Black; Lisa Ryan; Okjong Ji (credited with)"
  "Listening to young children with/in nature: Relational, pedagogical and community approaches that work"
  "Young Children and the Environment: Early Education for Sustainability, 3rd ed., chapter 5, pp. 91-119, Cambridge University Press"
  "2024"
  "10.1017/9781009199971.008"
  "https://doi.org/10.1017/9781009199971.008"
  Attr.academicChapterSource
  "Early-childhood nature and community projects in Korea and Australia; relational listening, trust and partnerships. BOUNDARY: Children aged 3-10 and community settings cannot be treated as direct digital higher-education effectiveness evidence; source-specific participation rights must be retained."
  Attr.publicAttribution

ferreiraRyanDavisDeepDiveSource : Attr.AttributedSource
ferreiraRyanDavisDeepDiveSource = Attr.mkDOISource
  "Jo-Anne L. Ferreira; Lisa D. Ryan; Julie M. Davis"
  "A Deep Dive into Sustainability Leadership Through Education for Sustainability"
  "The Palgrave Handbook of Educational Leadership and Management Discourse, pp. 829-849"
  "2022"
  "10.1007/978-3-030-99097-8_68"
  "https://doi.org/10.1007/978-3-030-99097-8_68"
  Attr.academicChapterSource
  "Critically examines sustainability leadership and contested strong/weak sustainability assumptions. BOUNDARY: Scholarly critique and historical framing do not provide direct digital-intervention causal effects or complete authority over community values."
  Attr.publicAttribution

unescoTLSSFSource : Attr.AttributedSource
unescoTLSSFSource = Attr.mkNoDOISource
  "UNESCO (programme owner; Griffith University prepared initial materials with documented contributors)"
  "Teaching and Learning for a Sustainable Future: A Multimedia Teacher Education Programme"
  "UNESCO / Griffith University; multimedia teacher development programme, CD-ROM version 3.0"
  "2002"
  "http://www.unesco.org/education/tlsf/"
  Attr.institutionalSource
  "Institutional multimedia teacher-education programme with 25 modules and around 100 hours of designed professional learning. BOUNDARY: Tool/module availability does not establish observed teacher capacity or transformation. Project participation is not automatically individual authorship."
  Attr.publicAttribution

candidateEfSSources : Attr.AttributedSourceAtlas
candidateEfSSources = Attr.mkSourceAtlas
  "published independent EfS source candidates for cross-pollination"
  "DASHI.Education.DigitalESDEfSSourceCrossPollinationExact"
  (taimurOnukiSource ∷ nilssonDahlstromSource ∷ adefilaEcoCOILSource ∷ singhCommunitySource ∷ barthCompetenciesSource ∷ giridharanCompetenciesSource ∷ jepsenCookeAccessibilitySource ∷ ferreiraRyanTilburySource ∷ ferreiraRyanSystemSource ∷ ferreiraRyanDavisSource ∷ ryanFerreira2024Source ∷ blackRyanJiNatureSource ∷ ferreiraRyanDavisDeepDiveSource ∷ unescoTLSSFSource ∷ Tilbury.tilbury2002 ∷ Tilbury.tilburyWortman2004 ∷ [])
  "Acquisition and candidate interpretive challenge only; exact-study admission requires reviewed source spans, eligibility and claim ceilings."

record CrossPollinationCase : Set where
  constructor source-case
  field
    attributedSource : Attr.AttributedSource
    candidateBridge : Prior.ReciprocalPedagogicalBridge
    sameLocator :
      Prior.EfSSource.exactLocator (Prior.ReciprocalPedagogicalBridge.source candidateBridge)
      ≡ Attr.canonicalURL attributedSource
    admittedToFullReview : Bool
    notYetAdmitted : admittedToFullReview ≡ false
open CrossPollinationCase public

sourceRoleReceipt : (c : CrossPollinationCase) →
  Snowball.SourceRoleSnowballReceipt (attributedSource c)
sourceRoleReceipt c = Snowball.canonicalSourceRoleSnowballReceipt (attributedSource c)

taimurOnuki : CrossPollinationCase
taimurOnuki = source-case taimurOnukiSource
  (Prior.pedagogical-bridge
    Digital.situatedRelationalEngagement Prior.transformativeEducatorPraxis
    (Prior.efs-source (Attr.canonicalURL taimurOnukiSource) Prior.empiricalContextBound
      "Two university course cases in Japan and Germany; digital/hybrid design-thinking pedagogy; participants' accounts."
      "Reported application of digital transformative pedagogy components in two cases and participant perceptions of learning conditions."
      "No independent proof of durable personal transformation, ecological outcomes, general intervention effects or transfer to other institutions.")
    Prior.productiveTension
    "Digital design thinking is a candidate route to reflective sustainability inquiry, not an automatic transformative learning result."
    "Which observed learning and action indicators distinguish a digitally active design studio from a transformative EfS experience?"
    "Which values, institutional support and participant authority are required before digital design thinking can claim EfS contribution?"
    "Positive course experiences can coexist with unchanged sustainability competence or limited long-term action."
    "Independent competence measures, realised sample, timing, counterexamples, educator practice and ecological/social consequence follow-up."
    Prior.candidate refl)
  refl false refl

nilssonDahlstrom : CrossPollinationCase
nilssonDahlstrom = source-case nilssonDahlstromSource
  (Prior.pedagogical-bridge
    Digital.contextualCustodianship Prior.valuesAndCriticalReflection
    (Prior.efs-source (Attr.canonicalURL nilssonDahlstromSource) Prior.crossPaperInterpretation
      "Scoping review of social sustainability in education, publications 2018-2023; 42 articles in final analysis."
      "Documents differences and conceptual/assessment difficulties in definitions and enactment of social sustainability."
      "The review's denominators and synthesis belong to its author; they cannot pay Digital-ESD's database, admission or outcome obligations.")
    Prior.productiveTension
    "Explicit social-sustainability definitions must precede any translation of digital-learning research into sustainability impact."
    "What does the original study observe that can distinguish equity, belonging and participation from general digital activity?"
    "Which explicit meaning of social sustainability and whose normative authority controls the analytic categories?"
    "Different social-sustainability definitions can make a digital outcome positive under one reading and incomplete under another."
    "Independent review coding and source-span comparison; operational definitions, affected groups and empirical indicators."
    Prior.candidate refl)
  refl false refl

adefilaEcoCOIL : CrossPollinationCase
adefilaEcoCOIL = source-case adefilaEcoCOILSource
  (Prior.pedagogical-bridge
    Digital.constitutiveLearnerAgency Prior.participationAndCollectiveAction
    (Prior.efs-source (Attr.canonicalURL adefilaEcoCOILSource) Prior.practitionerTheoretical
      "EcoCOIL proposal for transnational digital collaboration involving students, community organisations and varied stakeholders."
      "Models participatory co-creation, intercultural participation, coalition building and sustainability problem inquiry in digital settings."
      "Conceptual/model claims are not independent measurement of community authority, collective impacts or ecological outcomes.")
    Prior.productiveTension
    "Digital collaboration may support collective EfS inquiry only if communities retain consequential roles in decisions and knowledge production."
    "Who can set the problem, contest its framing and change decisions in the shared online collaboration?"
    "Does an international digital collaboration create community benefit, or merely more institutional activity and visibility?"
    "Nominal partnership can conceal unequal decision rights, digital burden or extractive knowledge flows."
    "Source-specific enactment, community decision rights, benefit/burden distribution and long-term outcomes."
    Prior.candidate refl)
  refl false refl

singhCommunity : CrossPollinationCase
singhCommunity = source-case singhCommunitySource
  (Prior.pedagogical-bridge
    Digital.pluralSituatedObservers Prior.participationAndCollectiveAction
    (Prior.efs-source (Attr.canonicalURL singhCommunitySource) Prior.crossPaperInterpretation
      "Literature review of community-engaged teaching and learning and sustainable development in higher education."
      "Reviews pedagogical arrangements, community partnerships, sustainability competencies and conditions that constrain enactment."
      "Review-level reports do not demonstrate causal effects of a specific digital intervention or authorise a university to speak for community partners.")
    Prior.productiveTension
    "Community-engaged learning requires distinct knowledge owners and reciprocal partnership, not a single university observer."
    "Can digital teaching retain community-defined research problems and participation in interpreting the results?"
    "Which local stakeholders can refuse, revise or challenge a sustainability learning intervention?"
    "Institutionally assessed service learning can report student benefit while concealing community burdens."
    "Community-authored source spans, partnership authority, project outcomes and critical negative cases."
    Prior.candidate refl)
  refl false refl

barthCompetencies : CrossPollinationCase
barthCompetencies = source-case barthCompetenciesSource
  (Prior.pedagogical-bridge
    Digital.situatedRelationalEngagement Prior.systemsRelationships
    (Prior.efs-source (Attr.canonicalURL barthCompetenciesSource) Prior.empiricalContextBound
      "Exploratory qualitative focus groups about formal and informal learning in higher education."
      "Identifies roles for cognitive and non-cognitive dispositions, multiple learning contexts and student responsibility in competence development."
      "Original authors identify remaining uncertainty about interdependencies; no digital intervention comparison or universal causal mechanism.")
    Prior.mutuallyRefining
    "Formal and informal learner environments may jointly support competence but must not be inferred from visible platform engagement."
    "What learning evidence links digital participation to sustainability reasoning across contexts and time?"
    "Which informal community, interdisciplinary and practice contexts are absent from an institution's learning analytics?"
    "A digitally intensive course may generate activity without competence beyond the course setting."
    "Cross-context performance assessment, informal-learning measures and longitudinal study design."
    Prior.candidate refl)
  refl false refl

giridharanCompetencies : CrossPollinationCase
giridharanCompetencies = source-case giridharanCompetenciesSource
  (Prior.pedagogical-bridge
    Digital.iterativeEvidenceReturnAndRecharting Prior.futuresAndIntergenerationalThinking
    (Prior.efs-source (Attr.canonicalURL giridharanCompetenciesSource) Prior.practitionerTheoretical
      "Higher-education leadership and key-competency chapter concerning technological change and institutional sustainability."
      "Develops a strategic account of future-facing competencies, flexible learning, digital provision and changing institutional models."
      "Conceptual and policy-facing discussion does not supply measured evidence of sustainability competence, durability or employment benefit.")
    Prior.complementary
    "Future-facing competencies require repeated reinterpretation of contexts, not automatic extrapolation from new digital tools."
    "What evidence would show adaptable and context-sensitive competencies instead of digital skill claims alone?"
    "How are financial, social and temporal burdens included in prospective higher-education learning plans?"
    "Digital flexibility may relocate costs onto learners while appearing to improve institutional resilience."
    "Versioned policy framework, institutional finance and learner outcome evidence from the relevant setting."
    Prior.candidate refl)
  refl false refl

jepsenCookeAccessibility : CrossPollinationCase
jepsenCookeAccessibility = source-case jepsenCookeAccessibilitySource
  (Prior.pedagogical-bridge
    Digital.adaptiveSupportWithLocalChoice Prior.systemsRelationships
    (Prior.efs-source (Attr.canonicalURL jepsenCookeAccessibilitySource) Prior.practitionerTheoretical
      "Industry/conference paper on digital accessibility and heterogeneous higher-education disability contexts."
      "Argues that design must accommodate conflicting access needs and context-specific learner constraints."
      "Industry perspective and advocated outcomes do not establish audited disability accessibility, retention effects or causal employment outcomes.")
    Prior.productiveTension
    "Universal availability and a fixed accessibility setting cannot substitute for situated effective access and user choice."
    "Does a claimed accessible digital platform preserve assistive workflow and multiple conflicting access requirements?"
    "Who may choose adjustments, report harms and seek practical repair without being excluded?"
    "An accessibility change that benefits one person can impede another person."
    "Relevant disability and intersectionality perspectives, effective task completion, assistive tooling and adverse-event reports."
    Prior.candidate refl)
  refl false refl

ferreiraRyanTilbury : CrossPollinationCase
ferreiraRyanTilbury = source-case ferreiraRyanTilburySource
  (Prior.pedagogical-bridge
    Digital.situatedRelationalEngagement Prior.transformativeEducatorPraxis
    (Prior.efs-source (Attr.canonicalURL ferreiraRyanTilburySource) Prior.crossPaperInterpretation
      "Review and critique of professional development for EfS in Australian initial teacher education."
      "Separates resource delivery, professional learning and more systemic change approaches in teacher education."
      "Initial teacher education context and professional-development models do not independently establish effects in digital university teaching.")
    Prior.productiveTension
    "Pedagogical resources are necessary inputs but not the same as institutional EfS enactment."
    "How do digital-learning educators acquire capacity and decision rights to enact sustainability pedagogy?"
    "What enduring supports and professional-development conditions distinguish sustainability implementation from content availability?"
    "More digital resources can coexist with little pedagogical change."
    "Professional-development process, teaching-practice and cross-institutional transfer evidence."
    Prior.candidate refl)
  refl false refl

ferreiraRyanSystem : CrossPollinationCase
ferreiraRyanSystem = source-case ferreiraRyanSystemSource
  (Prior.pedagogical-bridge
    Digital.contextualCustodianship Prior.systemsRelationships
    (Prior.efs-source (Attr.canonicalURL ferreiraRyanSystemSource) Prior.empiricalContextBound
      "Australian pre-service teacher education systems; resource-development, action-research and contextual-change models."
      "Studies organisational curriculum change and proposes an integrated Mainstreaming Change model across system levels."
      "Proposed systems model is not proof of general digital-ESD or longitudinal intervention outcomes.")
    Prior.mutuallyRefining
    "Systemic change requires linked institutional, curricular and professional conditions rather than a successful isolated digital lesson."
    "Can a digital innovation change linked incentives, training, governance and curriculum beyond the local teaching activity?"
    "Which institutional dependencies make apparently successful digital EfS work fail to endure?"
    "An excellent course can coexist with unchanged structural incentives."
    "Policy-level actions, implementation trajectories, durability and contradictory cases."
    Prior.candidate refl)
  refl false refl

ferreiraRyanDavis : CrossPollinationCase
ferreiraRyanDavis = source-case ferreiraRyanDavisSource
  (Prior.pedagogical-bridge
    Digital.pluralSituatedObservers Prior.transformativeEducatorPraxis
    (Prior.efs-source (Attr.canonicalURL ferreiraRyanDavisSource) Prior.empiricalContextBound
      "Pre-service teacher education organisations and their interconnected leadership context."
      "Examines change through a wider institutional system and distinguishes professional knowledge from leadership for change."
      "Authorship and studied context do not establish a universal digital higher-education intervention effect.")
    Prior.productiveTension
    "Teacher expertise and distributed system leadership are separate conditions of institution-wide EfS enactment."
    "Which actors can alter digital-ESD curriculum, policy and professional learning beyond an individual teacher?"
    "Can a project survive after its initiating educator or funding arrangement changes?"
    "Individual teacher competence may improve while the system still blocks institution-wide action."
    "Leadership roles, decision rights, cross-level evidence and persistence over time."
    Prior.candidate refl)
  refl false refl

ryanFerreira2024 : CrossPollinationCase
ryanFerreira2024 = source-case ryanFerreira2024Source
  (Prior.pedagogical-bridge
    Digital.contextualCustodianship Prior.transformativeEducatorPraxis
    (Prior.efs-source (Attr.canonicalURL ryanFerreira2024Source) Prior.crossPaperInterpretation
      "Australian teacher education and decade-scale system-change case context; Oxford Research Encyclopedia reference article."
      "Reviews policy, curriculum, educator preparation, accreditation and common-vision strategies in embedding EfS."
      "A programme case and reference synthesis do not establish measured digital-EfS effects or direct transfer across countries and HE sectors.")
    Prior.productiveTension
    "Effective EfS integration depends on curricula, professional standards, shared purposes and institutional structures."
    "Are digital-ESD proposals embedded in governance and educator capacity, or restricted to one technology project?"
    "Which policy/accreditation and stakeholder conditions permit long-term transformative ESD?"
    "Programme-level adoption can exist without meaningful learner competence or equity."
    "Timeline, governance, implementation and outcomes under transparent study-specific evidence limits."
    Prior.candidate refl)
  refl false refl

tilburyIUCN2002 : CrossPollinationCase
tilburyIUCN2002 = source-case Tilbury.tilbury2002
  (Prior.pedagogical-bridge
    Digital.pluralSituatedObservers Prior.systemsRelationships
    (Prior.efs-source (Attr.canonicalURL Tilbury.tilbury2002) Prior.crossPaperInterpretation
      "Edited IUCN case collection about education and sustainability; chapter claims must be separately sourced."
      "Plural educational and community pathways for sustainability."
      "An edited case collection does not assign every case a common method or prove context-free impact.")
    Prior.complementary
    "Retain distinct routes to sustainability education without inventing an exhaustive ESD mechanism."
    "Which situated source and respondent support each distinct proposed digital-to-ESD pathway?"
    "Which cases have been left out of the digital comparison?"
    "A general book-level theme can conceal contradictory cases."
    "Chapter-level source spans, role attribution and review decisions."
    Prior.candidate refl)
  refl false refl

tilburyWortman2004 : CrossPollinationCase
tilburyWortman2004 = source-case Tilbury.tilburyWortman2004
  (Prior.pedagogical-bridge
    Digital.constitutiveLearnerAgency Prior.participationAndCollectiveAction
    (Prior.efs-source (Attr.canonicalURL Tilbury.tilburyWortman2004) Prior.practitionerTheoretical
      "IUCN sustainability engagement handbook; five documented practice themes."
      "Futures, critical reflection, participation in decisions, partnership and systemic thinking."
      "A practitioner framework is not a controlled effectiveness study or evidence of community consent.")
    Prior.mutuallyRefining
    "Collective decision roles need to be observed separately from learner voice and platform engagement."
    "Can participants revise the question and act on contested sustainability decisions?"
    "Whose power to decide, refuse or exit remains absent?"
    "Consultation may be labelled participation without actually changing decisions."
    "Decision-process evidence, community source roles and sustained action."
    Prior.candidate refl)
  refl false refl

blackRyanJiNature : CrossPollinationCase
blackRyanJiNature = source-case blackRyanJiNatureSource
  (Prior.pedagogical-bridge
    Digital.pluralSituatedObservers Prior.ecologicalAndMoreThanHumanRelations
    (Prior.efs-source (Attr.canonicalURL blackRyanJiNatureSource)
      Prior.empiricalContextBound
      "Early-childhood education for sustainability in Australian and Korean nature/community projects."
      "Source discusses relational listening to children, shared goals, partners and ecological/community participation."
      "No direct transfer to university digital learning, and adult interpretations cannot stand in for child voice or other-than-human testimony.")
    Prior.productiveTension
    "A situated learner/child/community observer may contest institutional assumptions about ecological education."
    "How could digital higher education retain participant/partner authority rather than treating engagement surveys as sufficient?"
    "What non-human ecological relationships and community decisions remain unobserved by an online course?"
    "Adult-led nature activities can be labelled participatory without granting consequential agency."
    "Participant voice, community decisions, ecological observations, population-transfer and outcome review."
    Prior.candidate refl)
  refl false refl

ferreiraRyanDavisDeepDive : CrossPollinationCase
ferreiraRyanDavisDeepDive = source-case ferreiraRyanDavisDeepDiveSource
  (Prior.pedagogical-bridge
    Digital.contextualCustodianship Prior.valuesAndCriticalReflection
    (Prior.efs-source (Attr.canonicalURL ferreiraRyanDavisDeepDiveSource)
      Prior.crossPaperInterpretation
      "Critical sustainability leadership chapter in a published handbook."
      "Examines the competing normative traditions and disrupted histories of education for sustainability."
      "Critical-theoretical genealogy does not itself prove learning, implementation or system change.")
    Prior.productiveTension
    "Historical, political and normative ESD distinctions constrain how a digital innovation can claim transformation."
    "Which sustainability vision and organisational interests are presupposed by the digital education evaluation?"
    "Can learners and communities contest weak or purely technocratic interpretations of sustainability?"
    "An apparently successful digital innovation can satisfy a narrow sustainability metric while reinforcing an inequitable governance structure."
    "Explicit normative frame, competing perspectives, participant authority, policy context and same-object observations."
    Prior.candidate refl)
  refl false refl

unescoTLSSF : CrossPollinationCase
unescoTLSSF = source-case unescoTLSSFSource
  (Prior.pedagogical-bridge
    Digital.iterativeEvidenceReturnAndRecharting Prior.transformativeEducatorPraxis
    (Prior.efs-source (Attr.canonicalURL unescoTLSSFSource)
      Prior.practitionerTheoretical
      "UNESCO institutional teacher-education multimedia programme of 25 modules, around 100 hours."
      "Programme design supports educator learning opportunities concerning ESD and multimedia methods."
      "The programme's existence, duration and activity descriptions do not establish competence, uptake, durable practice or impact.")
    Prior.complementary
    "An early institutional digital EfS programme provides a prior-art example of designed teacher capacity support."
    "Which observed teacher practices distinguish multimedia availability from sustained ESD enactment?"
    "Can educator professional learning retain values reflection and system transformation rather than only digital content delivery?"
    "A large module count is an implementation input and cannot be promoted to a sustainable learning outcome."
    "Training exposure, teacher practice changes, student outcomes, adoption across institutions and longitudinal follow-up."
    Prior.candidate refl)
  refl false refl

canonicalSourceCases : List CrossPollinationCase
canonicalSourceCases =
  taimurOnuki ∷
  nilssonDahlstrom ∷
  adefilaEcoCOIL ∷
  singhCommunity ∷
  barthCompetencies ∷
  giridharanCompetencies ∷
  jepsenCookeAccessibility ∷
  ferreiraRyanTilbury ∷
  ferreiraRyanSystem ∷
  ferreiraRyanDavis ∷
  ryanFerreira2024 ∷
  blackRyanJiNature ∷
  ferreiraRyanDavisDeepDive ∷
  unescoTLSSF ∷
  tilburyIUCN2002 ∷
  tilburyWortman2004 ∷ []

-- Reuse the existing evidence braid rather than manufacture a second
-- convergence / conflict / epistemic-authority ontology.
relationFor : Prior.BridgeStatus → Braid.BraidRelation
relationFor Prior.complementary = Braid.complementarity
relationFor Prior.mutuallyRefining = Braid.convergence
relationFor Prior.productiveTension = Braid.productiveTension
relationFor Prior.unresolved = Braid.unresolvedConflict

canonicalBraid : CrossPollinationCase → Braid.TensionReceipt
canonicalBraid c = Braid.tension-receipt
  (Attr.canonicalURL (attributedSource c))
  "DASHI.Education.DigitalESDTransferablePedagogicalPrinciplesExact"
  (Attr.canonicalURL (attributedSource c))
  "DASHI.Biology.EducationCorpusSourceRegistry"
  (relationFor (Prior.ReciprocalPedagogicalBridge.status (candidateBridge c)))
  (Prior.ReciprocalPedagogicalBridge.competingReading (candidateBridge c))

candidateEvidenceDebt : CrossPollinationCase → String
candidateEvidenceDebt c =
  Prior.ReciprocalPedagogicalBridge.evidenceDebt (candidateBridge c)

data CitationCreatesSourceAdmission : Set where
data SourceComparisonEstablishesInterventionEffect : Set where
data PreSearchCrosswalkEstablishesPublicationNovelty : Set where
data EditorInvitationCreatesScholarshipAuthority : Set where
data EarlierReviewPaysDigitalESDSearchExecution : Set where
data UniversityVoiceOverridesCommunityAuthority : Set where
data ContextFreeSustainabilityCompetence : Set where

citationDoesNotAdmitSource : CitationCreatesSourceAdmission → ⊥
citationDoesNotAdmitSource ()
comparisonDoesNotProveEffect : SourceComparisonEstablishesInterventionEffect → ⊥
comparisonDoesNotProveEffect ()
crosswalkDoesNotProveNovelty : PreSearchCrosswalkEstablishesPublicationNovelty → ⊥
crosswalkDoesNotProveNovelty ()
invitationDoesNotCreateAuthority : EditorInvitationCreatesScholarshipAuthority → ⊥
invitationDoesNotCreateAuthority ()
otherReviewDoesNotPaySearch : EarlierReviewPaysDigitalESDSearchExecution → ⊥
otherReviewDoesNotPaySearch ()
universityDoesNotOverrideCommunity : UniversityVoiceOverridesCommunityAuthority → ⊥
universityDoesNotOverrideCommunity ()
competenceIsNotContextFree : ContextFreeSustainabilityCompetence → ⊥
competenceIsNotContextFree ()
```

## DASHI/Education/DigitalESDEfSSourceCrossPollinationRegression.agda

Source: https://github.com/chboishabba/dashi_agda/blob/agent/digital-esd-source-crosspollination-20261101/DASHI/Education/DigitalESDEfSSourceCrossPollinationRegression.agda

Blob SHA: `aab9f58fcb55eadef5298b605b9165fabcfdd41a`

```agda
module DASHI.Education.DigitalESDEfSSourceCrossPollinationRegression where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Education.DigitalESDTilburySourceRoleExact as Tilbury
import DASHI.Education.DigitalESDEfSSourceCrossPollinationExact as Cases
import DASHI.Education.DigitalESDEfSPedagogicalReciprocityExact as Prior
import DASHI.Education.DigitalESDTransferablePedagogicalPrinciplesExact as Digital
import DASHI.Education.DigitalESDEvidenceBraidTensionExact as Braid

sourceCandidateCount : Attr.sourceCount
  (Attr.AttributedSourceAtlas.sources Cases.candidateEfSSources) ≡ 16
sourceCandidateCount = refl

firstLocatorPreserved : Cases.CrossPollinationCase.sameLocator Cases.taimurOnuki
  ≡ refl
firstLocatorPreserved = refl

lastLocatorPreserved : Cases.CrossPollinationCase.sameLocator Cases.tilburyWortman2004
  ≡ refl
lastLocatorPreserved = refl

twinCourseCaseStaysCandidate :
  Prior.ReciprocalPedagogicalBridge.promotion
    (Cases.CrossPollinationCase.candidateBridge Cases.taimurOnuki)
  ≡ Prior.candidate
twinCourseCaseStaysCandidate = refl

communityCaseStaysCandidate :
  Prior.ReciprocalPedagogicalBridge.promotion
    (Cases.CrossPollinationCase.candidateBridge Cases.singhCommunity)
  ≡ Prior.candidate
communityCaseStaysCandidate = refl

nonAdmissionRetained :
  Cases.CrossPollinationCase.admittedToFullReview Cases.nilssonDahlstrom ≡ false
nonAdmissionRetained = refl

tilburyReusesExistingSource :
  Cases.CrossPollinationCase.attributedSource Cases.tilburyWortman2004
  ≡ Tilbury.tilburyWortman2004
tilburyReusesExistingSource = refl

ecoCOILCollectiveChallenge :
  Prior.ReciprocalPedagogicalBridge.digitalPrinciple
    (Cases.CrossPollinationCase.candidateBridge Cases.adefilaEcoCOIL)
  ≡ Digital.constitutiveLearnerAgency
ecoCOILCollectiveChallenge = refl

accessibilityTensionUsesExistingBraid :
  Braid.TensionReceipt.relation (Cases.canonicalBraid Cases.jepsenCookeAccessibility)
  ≡ Braid.productiveTension
accessibilityTensionUsesExistingBraid = refl

leadershipChangeUsesExistingBraid :
  Braid.TensionReceipt.relation (Cases.canonicalBraid Cases.ferreiraRyanSystem)
  ≡ Braid.convergence
leadershipChangeUsesExistingBraid = refl

sourceCitationsDoNotImportProof :
  Attr.citationImportsProof Cases.taimurOnukiSource ≡ false
sourceCitationsDoNotImportProof = refl

sourceCitationsDoNotCreateAuthority :
  Attr.citationCreatesAuthority Cases.ryanFerreira2024Source ≡ false
sourceCitationsDoNotCreateAuthority = refl

candidateCaseDoesNotCreateReviewAdmission :
  Cases.CitationCreatesSourceAdmission → ⊥
candidateCaseDoesNotCreateReviewAdmission = Cases.citationDoesNotAdmitSource

crosswalkDoesNotProveEffects :
  Cases.SourceComparisonEstablishesInterventionEffect → ⊥
crosswalkDoesNotProveEffects = Cases.comparisonDoesNotProveEffect

crosswalkDoesNotClaimPublicationNovelty :
  Cases.PreSearchCrosswalkEstablishesPublicationNovelty → ⊥
crosswalkDoesNotClaimPublicationNovelty = Cases.crosswalkDoesNotProveNovelty

reviewCountDoesNotPayOurSearch :
  Cases.EarlierReviewPaysDigitalESDSearchExecution → ⊥
reviewCountDoesNotPayOurSearch = Cases.otherReviewDoesNotPaySearch

universityObserverCannotOverrideCommunity :
  Cases.UniversityVoiceOverridesCommunityAuthority → ⊥
universityObserverCannotOverrideCommunity = Cases.universityDoesNotOverrideCommunity

blackRyanJiCaseStaysCandidate :
  Prior.ReciprocalPedagogicalBridge.promotion
    (Cases.CrossPollinationCase.candidateBridge Cases.blackRyanJiNature)
  ≡ Prior.candidate
blackRyanJiCaseStaysCandidate = refl

unescoIsInstitutionalNotAcademicAuthority :
  Attr.sourceKind Cases.unescoTLSSFSource ≡ Attr.institutionalSource
unescoIsInstitutionalNotAcademicAuthority = refl

leadershipSourceStillUnadmitted :
  Cases.CrossPollinationCase.admittedToFullReview Cases.ferreiraRyanDavisDeepDive
  ≡ false
leadershipSourceStillUnadmitted = refl
```

## DASHI/EverythingDigitalESDReciprocalBraid.agda

Source: https://github.com/chboishabba/dashi_agda/blob/agent/digital-esd-source-crosspollination-20261101/DASHI/EverythingDigitalESDReciprocalBraid.agda

Blob SHA: `f336e9ec0e5cfd84f3cdbdad6b6df2128eb50c7b`

```agda
import DASHI.Education.DigitalInnovationESDSourceAtlas
import DASHI.Education.DigitalInnovationESDTransformationExact
import DASHI.Education.MDPISpecialIssueResearchGovernanceExact
import DASHI.Education.AliceBrownDigitalESDEpistemicGovernanceBridgeExact
import DASHI.Education.DigitalESDReciprocalBraidExact
import DASHI.Education.DigitalESDCrossRoundAttributionBoundaryExact
import DASHI.Education.DigitalESDAcquisitionSnowballParetoExact
import DASHI.Education.DigitalESDAcquisitionSnowballRegression
import DASHI.Education.DigitalESDSourceAttributionCorrectionExact
import DASHI.Education.DigitalESDSourceAttributionCorrectionRegression
import DASHI.Education.DigitalESDICTLifecycleCircularitySnowballExact
import DASHI.Education.DigitalESDICTLifecycleCircularitySnowballRegression
import DASHI.Education.DigitalESDSameObjectAcquisitionSchedulerExact
import DASHI.Education.DigitalESDSameObjectAcquisitionSchedulerRegression
import DASHI.Education.DigitalESDParticipantGovernanceContextTransferExact
import DASHI.Education.DigitalESDParticipantGovernanceContextTransferRegression
import DASHI.Education.DigitalESDOpenKnowledgeCommonsCollaborationExact
import DASHI.Education.DigitalESDOpenKnowledgeCommonsCollaborationRegression
import DASHI.Education.DigitalESDOpenCommonsSituatedMaterialExact
import DASHI.Education.DigitalESDOpenCommonsSituatedMaterialRegression
import DASHI.Education.DigitalESDEducationSustainabilityLiteratureMapExact
import DASHI.Education.DigitalESDEducationSustainabilityLiteratureMapRegression
import DASHI.Education.DigitalESDCurrentScholarlySnowballExact
import DASHI.Education.DigitalESDCurrentScholarlySnowballRegression
import DASHI.Education.DigitalESDEfSSourceCrossPollinationExact
import DASHI.Education.DigitalESDEfSSourceCrossPollinationRegression
import DASHI.Education.DigitalESDContributionPositioningExact
import DASHI.Education.DigitalESDContributionPositioningRegression
import DASHI.Education.DigitalESDTransferablePedagogicalPrinciplesExact
import DASHI.Education.DigitalESDTransferablePedagogicalPrinciplesRegression
import DASHI.Education.DigitalESDExternalityIncidenceAuditExact
import DASHI.Education.DigitalESDExternalityIncidenceAuditRegression
import DASHI.Education.EducationSituatedInvestmentTrajectoryExact
import DASHI.Education.EducationSituatedInvestmentTrajectoryRegression
import DASHI.Education.DigitalESDRelationalExternalityReturnBridgeExact
import DASHI.Education.DigitalESDRelationalExternalityReturnBridgeRegression
import DASHI.Education.DigitalESDSituatedCapabilityEvidenceCrossPollinationExact
import DASHI.Education.DigitalESDSituatedCapabilityEvidenceCrossPollinationRegression
import DASHI.Education.DigitalESDCandidateWorldExecutionExact
import DASHI.Education.DigitalESDCandidateWorldExecutionRegression
import DASHI.Education.DigitalESDAcademicCorpusWorldCrossPollinationExact
import DASHI.Education.DigitalESDAcademicCorpusWorldCrossPollinationRegression
import DASHI.Education.DigitalESDDBNativeAcademicWorldExecutionExact
import DASHI.Education.DigitalESDDBNativeAcademicWorldExecutionRegression
import DASHI.Education.DigitalESDStudyClaimCeilingExact
import DASHI.Education.DigitalESDStudyClaimCeilingRegression
import DASHI.Education.DigitalESDStudyClaimMethodBridgeExact
import DASHI.Education.DigitalESDStudyClaimMethodBridgeRegression
import DASHI.Education.DigitalESDStudyClaimPilotExact
import DASHI.Education.DigitalESDStudyClaimPilotRegression
import DASHI.Education.DigitalESDStudyClaimPilotExtensionExact
import DASHI.Education.DigitalESDStudyClaimPilotExtensionRegression
import DASHI.Education.DigitalESDStudyClaimQuantitativePilotExact
import DASHI.Education.DigitalESDStudyClaimQuantitativePilotRegression
import DASHI.Education.DigitalESDStudyAnalysisSetRefinementExact
import DASHI.Education.DigitalESDStudyAnalysisSetRefinementRegression
import DASHI.Education.DigitalESDColladoLongitudinalClaimExact
import DASHI.Education.DigitalESDColladoLongitudinalClaimRegression
import DASHI.Education.DigitalESDColladoAnalysisSetExact
import DASHI.Education.DigitalESDColladoAnalysisSetRegression
import DASHI.Education.DigitalESDQuantitativeUncertaintyAcquisitionExact
import DASHI.Education.DigitalESDQuantitativeUncertaintyAcquisitionRegression
import DASHI.Education.DigitalESDRandomizedCausalAcquisitionExact
import DASHI.Education.DigitalESDRandomizedCausalAcquisitionRegression
import DASHI.Education.DigitalESDStudyResultPNFProofSearchExact
import DASHI.Education.DigitalESDStudyResultPNFProofSearchRegression
import DASHI.Education.DigitalESDStudyEvidencePNFExtensionExact
import DASHI.Education.DigitalESDStudyEvidencePNFExtensionRegression
import DASHI.Education.DigitalESDDisabilityIntersectionalityAuditExact
import DASHI.Education.DigitalESDDisabilityIntersectionalityAuditRegression
import DASHI.Education.DigitalESDDisabilityStudyPNFExact
import DASHI.Education.DigitalESDDisabilityStudyPNFRegression
import DASHI.Education.DigitalESDStudyIntersectionalAbsenceAuditExact
import DASHI.Education.DigitalESDStudyIntersectionalAbsenceAuditRegression
import DASHI.Education.DigitalESDZhaoWhoMissingPNFExact
import DASHI.Education.DigitalESDZhaoWhoMissingPNFRegression
import DASHI.Education.DigitalESDIntersectionalDisabilityExtensionExact
import DASHI.Education.DigitalESDIntersectionalDisabilityExtensionRegression
import DASHI.Education.DigitalESDMaterialEnvironmentalSubstrateExact
import DASHI.Education.DigitalESDMaterialEnvironmentalSubstrateRegression
import DASHI.Education.DigitalESDMaterialImpactAllocationExact
import DASHI.Education.DigitalESDMaterialImpactAllocationRegression
import DASHI.Education.DigitalESDEducationAIEnvironmentalWorkloadExact
import DASHI.Education.DigitalESDEducationAIEnvironmentalWorkloadRegression
import DASHI.Education.DigitalESDAIInferenceScaleReboundExact
import DASHI.Education.DigitalESDAIInferenceReboundRegression
import DASHI.Education.DigitalESDInstitutionalEvaluationPilotExact
import DASHI.Education.DigitalESDInstitutionalEvaluationPilotRegression
import DASHI.Education.DigitalESDEmpiricalAuthorityFirewallExact
import DASHI.Education.DigitalESDEmpiricalAuthorityFirewallRegression
import DASHI.Education.DigitalESDTransformativePrincipleMatrixExact
import DASHI.Education.DigitalESDTransformativePrincipleMatrixRegression
import DASHI.Education.DigitalESDTransferablePrincipleDerivationMethodExact
import DASHI.Education.DigitalESDTransferablePrincipleDerivationMethodRegression
import DASHI.Education.DigitalESDPaperTypeRequirementParetoExact
import DASHI.Education.DigitalESDPaperTypeRequirementRegression
import DASHI.Education.DigitalESDConsumerRelativeLifecycleExact
import DASHI.Education.DigitalESDConsumerRelativeLifecycleRegression
import DASHI.Education.DigitalESDStructuredSearchExact
import DASHI.Education.DigitalESDManuscriptDependencyPaymentAdapterExact
import DASHI.Education.DigitalESDStructuredSearchRegression
import DASHI.Education.DigitalESDPrimarySourceMethodologyAtlasExact
import DASHI.Education.DigitalESDManuscriptMethodologyExact
import DASHI.Education.DigitalESDManuscriptMethodologyRegression
import DASHI.Education.DigitalESDPreScreenCandidateSourceScopeMatrixExact
import DASHI.Education.DigitalESDPreScreenCandidateSourceScopeMatrixRegression
import DASHI.Education.DigitalESDDatabaseSearchProtocolExact
import DASHI.Education.DigitalESDDatabaseSearchProtocolRegression
import DASHI.Education.DigitalESDDatabaseSearchProtocolV2Exact
import DASHI.Education.DigitalESDDatabaseSearchProtocolV2Regression
import DASHI.Education.DigitalESDDatabaseTranslationSyntaxExact
import DASHI.Education.DigitalESDDatabaseTranslationSyntaxRegression
import DASHI.Education.DigitalESDDatabaseTranslatedQueriesExact
import DASHI.Education.DigitalESDDatabaseTranslatedQueriesRegression
import DASHI.Education.DigitalESDDatabaseExecutionReceiptExact
import DASHI.Education.DigitalESDDatabaseExecutionReceiptRegression
import DASHI.Education.DigitalESDPoliticalEconomyProvisioningExact
import DASHI.Education.DigitalESDPoliticalEconomyProvisioningRegression
import DASHI.Education.DigitalESDSocialProvisioningContinuityExact
import DASHI.Education.DigitalESDSocialProvisioningContinuityRegression
import DASHI.Education.DigitalESDInstitutionalDurabilityMaintenanceExact
import DASHI.Education.DigitalESDInstitutionalDurabilityMaintenanceRegression
import DASHI.Education.DigitalESDSourceAuditScaleExact
import DASHI.Education.DigitalESDSourceAuditScaleRegression
import DASHI.Education.DigitalESDNormativeStandardsAtlasExact
import DASHI.Education.DigitalESDNormativeStandardsAtlasRegression
import DASHI.Education.DigitalESDSituatedAuditObserverExact
import DASHI.Education.DigitalESDSituatedAuditObserverRegression
import DASHI.Education.DigitalESDSourceAuditAdmissibilityExact
import DASHI.Education.DigitalESDSourceAuditAdmissibilityRegression
import DASHI.Education.DigitalESDAuditDomainBoundaryReceiptExact
import DASHI.Education.DigitalESDAuditDomainBoundaryReceiptRegression
import DASHI.Education.DigitalESDSourceIntersectionalAuditExact
import DASHI.Education.DigitalESDSourceIntersectionalAuditRegression
import DASHI.Education.DigitalESDEvidenceBraidTensionExact
import DASHI.Education.DigitalESDEvidenceBraidTensionRegression
import DASHI.Education.DigitalESDSourceAuditHyperfabricExact
import DASHI.Education.DigitalESDSourceAuditHyperfabricRegression
import DASHI.Education.DigitalESDSourceAuditAdmissionExact
import DASHI.Education.DigitalESDSourceAuditAdmissionRegression
import DASHI.Education.DigitalESDPhilosophySurveillanceAuditBoundaryExact
import DASHI.Education.DigitalESDPhilosophySurveillanceAuditBoundaryRegression
import DASHI.Education.DigitalESDPhilosophySeededAcquisitionProbeExact
import DASHI.Education.DigitalESDPhilosophySeededAcquisitionProbeRegression
import DASHI.Education.DigitalESDIntersectionalSourceAcquisitionParetoExact
import DASHI.Education.DigitalESDIntersectionalSourceAcquisitionParetoRegression
import DASHI.Education.DigitalESDIntersectionalSourceAcquisitionParetoRound2Exact
import DASHI.Education.DigitalESDIntersectionalSourceAcquisitionParetoRound2Regression
import DASHI.Education.DigitalESDIntersectionalSourceAcquisitionParetoRound3Exact
import DASHI.Education.DigitalESDIntersectionalSourceAcquisitionParetoRound3Regression
import DASHI.Education.DigitalESDIntersectionalSourceAcquisitionParetoRound4Exact
import DASHI.Education.DigitalESDIntersectionalSourceAcquisitionParetoRound4Regression
import DASHI.Education.DigitalESDIntersectionalSourceAcquisitionParetoRound5Exact
import DASHI.Education.DigitalESDIntersectionalSourceAcquisitionParetoRound5Regression
import DASHI.Education.DigitalESDIntersectionalSourceAcquisitionParetoRound6Exact
import DASHI.Education.DigitalESDIntersectionalSourceAcquisitionParetoRound6Regression
import DASHI.Education.DigitalESDIntersectionalSourceAcquisitionParetoRound7Exact
import DASHI.Education.DigitalESDIntersectionalSourceAcquisitionParetoRound7Regression
import DASHI.Education.DigitalESDIntersectionalSourceAcquisitionParetoRound8Exact
import DASHI.Education.DigitalESDIntersectionalSourceAcquisitionParetoRound8Regression
import DASHI.Education.DigitalESDIntersectionalSourceAcquisitionParetoRounds9To20Everything
import DASHI.Education.DigitalESDCanonicalOwnerRegression
import DASHI.Education.DigitalInnovationESDRegression
import DASHI.Education.DigitalESDEligibilityFrameExclusionExact
import DASHI.Education.DigitalESDEligibilityFrameExclusionRegression
import DASHI.Education.DigitalESDEligibilityFrameAcquisitionExact
import DASHI.Education.DigitalESDEligibilityFrameAcquisitionRegression
import DASHI.Education.DigitalESDSearchToSourceAuditAdmissionExact
import DASHI.Education.DigitalESDSearchToSourceAuditAdmissionRegression
import DASHI.Education.DigitalESDDatabaseExecutionStructuredSearchBridgeExact
import DASHI.Education.DigitalESDDatabaseExecutionStructuredSearchBridgeRegression
import DASHI.Education.DigitalESDSLRSourceReviewBridgeExact
import DASHI.Education.DigitalESDSLRSourceReviewBridgeRegression
import DASHI.Interop.SLRCanonicalEvidenceSubstrateExact
import DASHI.Interop.SLRCanonicalEvidenceSubstrateRegression
import DASHI.Education.DigitalESDTitleAbstractScreeningExact
import DASHI.Education.DigitalESDTitleAbstractScreeningRegression
import DASHI.Education.DigitalESDAdaptiveScreeningProgrammeExact
import DASHI.Education.DigitalESDAdaptiveScreeningProgrammeRegression
import DASHI.Education.DigitalESDSLRInteropWrapperExact
import DASHI.Education.DigitalESDSLRInteropWrapperRegression
import DASHI.Education.DigitalESDERICStudyInteropExact
import DASHI.Education.DigitalESDERICStudyInteropRegression
import DASHI.Education.DigitalESDERICStudyExecutionExact
import DASHI.Education.DigitalESDERICStudyExecutionRegression
import DASHI.Education.DigitalESDSelectiveFullTextMaterialisationExact
import DASHI.Education.DigitalESDSelectiveFullTextMaterialisationRegression
import DASHI.Education.DigitalESDStudyProcessingCensusExact
import DASHI.Education.DigitalESDStudyProcessingCensusRegression
import DASHI.Education.DigitalESDReviewedScreeningDecisionBridgeExact
import DASHI.Education.DigitalESDReviewedScreeningDecisionBridgeRegression
import DASHI.Education.DigitalESDFullTextSLRParseExact
import DASHI.Education.DigitalESDFullTextSLRParseRegression
import DASHI.Education.DigitalESDAdaptiveScreeningExecutionExact
import DASHI.Education.DigitalESDAdaptiveScreeningExecutionRegression
import DASHI.Education.DigitalESDAdaptiveScreeningControllerExact
import DASHI.Education.DigitalESDAdaptiveScreeningControllerRegression
import DASHI.Education.DigitalESDReviewedUnresolvedRoutingExact
import DASHI.Education.DigitalESDReviewedUnresolvedRoutingRegression
import DASHI.Education.DigitalESDStudyParseInteropExact
import DASHI.Education.DigitalESDStudyParseInteropRegression
import DASHI.Interop.DigitalESD.ScholarlyFullTextCrossPollinationExact
import DASHI.Interop.DigitalESD.ScholarlyFullTextCrossPollinationRegression
import DASHI.Interop.DigitalESD.ScholarlyFullTextInteropExecutionExact
import DASHI.Interop.DigitalESD.ScholarlyFullTextInteropExecutionRegression
import DASHI.Education.DigitalESDDocumentTextMaterialisationExact
import DASHI.Education.DigitalESDDocumentTextMaterialisationRegression
import DASHI.Education.DigitalESDStudyParseExecutionExact
import DASHI.Education.DigitalESDStudyParseExecutionRegression
import DASHI.Education.DigitalESDFirstRetainedStudyParseExact
import DASHI.Education.DigitalESDFirstRetainedStudyParseRegression




module DASHI.EverythingDigitalESDReciprocalBraid where

------------------------------------------------------------------------
-- Thin aggregate for the digital-ESD research-call tranche.
--
-- Import-only by design: the substantive owners retain their own provenance,
-- authority and non-promotion boundaries.
------------------------------------------------------------------------
```

