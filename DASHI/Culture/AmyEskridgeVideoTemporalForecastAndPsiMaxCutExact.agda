module DASHI.Culture.AmyEskridgeVideoTemporalForecastAndPsiMaxCutExact where

-- Same-source, same-experiment quantitative max-cut for edited video 17:42,
-- 18:35, 19:26, 23:01, 29:49 and original June-2007 Burisch prediction.
--
-- Original clip: Project Camelot / Dan Burisch, Stargate Secrets Part 1,
-- June 2007, transcript lines 629–679 (editorial-video ~29:49–32:04):
-- https://projectavalon.net/lang/en/dan_burisch_stargate_secrets_interview_transcript_1_en.html
-- Burisch said he "probably" expected three-part machines would be
-- reassembled ~2016/2017, with no signed event prediction, p, location,
-- unique apparatus ID, outcome record or preregistered score.
-- Source identity ≠ reality, accuracy, reactivation or agency custody.
--
-- Psychology and PAA must not be conflated:
-- Bem (2011) 9 cognitive-affective experiments DOI 10.1037/a0021524;
-- Kekecs et al (2023) Royal Society Open Science DOI 10.1098/rsos.191375
-- https://pmc.ncbi.nlm.nih.gov/articles/PMC9890107/
-- 10 labs/2115 valid people, 49.89% correct vs 53.07% in Bem Exp 1;
-- Walleczek et al (2025) PLOS ONE DOI 10.1371/journal.pone.0335330
-- Study 2 reported confirmatory below-chance guessing (49.65%, p=0.013); later Study 3 had 50.07%,
-- N=217800, p=0.496, failed to reproduce Study 2.
-- Distinct physiology families:
-- Mossbridge/Tressoldi/Utts (2012) DOI 10.3389/fpsyg.2012.00390;
-- Duggan/Tressoldi (2018) DOI 10.12688/f1000research.14330.2.
-- A cognitive forced-choice replication does NOT itself refute every
-- physiological pre-stimulus protocol or verify its postulated mechanism.
--
-- Reuse canonical original evidence route and its active obligations:
-- DASHI.Governance.AnomalousPhenomenonTemporalEvidenceTrajectoriesExact
-- DASHI.Governance.AnomalousTemporalProofSearchExperimentAdmissionExact
-- DASHI.Wikimedia.IbrahimSnowballMandelaReligionIndigenousMemoryBraidingBidiExact
-- Source and numerical checks are finite model-side admissions, never
-- new experimental observations.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import DASHI.Core.Prelude using (⊥)
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Culture.AmyEskridgeVideoOriginalClipLineageExact as Clips
import DASHI.Culture.AmyEskridgeVideoClaimAttributionLedgerExact as Video
import DASHI.Governance.AnomalousPhenomenonTemporalEvidenceTrajectoriesExact as Trajectory
import DASHI.Governance.AnomalousTemporalProofSearchExperimentAdmissionExact as Admission
import DASHI.Wikimedia.IbrahimSnowballMandelaReligionIndigenousMemoryBraidingBidiExact as Mandela

atMost : Nat → Nat → Bool
atMost zero _ = true
atMost (suc _) zero = false
atMost (suc n) (suc m) = atMost n m

natSub : Nat → Nat → Nat
natSub zero _ = zero
natSub n zero = n
natSub (suc n) (suc m) = natSub n m

and : Bool → Bool → Bool
and true b = b
and false _ = false

square : Nat → Nat
square x = x * x

data ReportModality : Set where
  quotedConditionalExpectation : ReportModality
  precommittedSpecificEvent : ReportModality

record ForecastProvenance : Set where
  constructor forecast-provenance
  field
    originalClip : Clips.ClipLineage
    originalPublishedYear : Nat
    predictedEarliestYear : Nat
    predictedLatestYear : Nat
    predictionKind : ReportModality
    frozenProbabilityPerThousand : Maybe Nat
    fixedEventDefinitionRecorded : Bool
    eventSourceIndependentlyAuthenticated : Bool
    originalPublicSource : String
open ForecastProvenance public

burischConditionalReassembly2007 : ForecastProvenance
burischConditionalReassembly2007 = forecast-provenance
  Clips.clip15
  2007 2016 2017
  quotedConditionalExpectation
  nothing false false
  "Burisch expected that separated alleged device components would probably be reassembled sometime around 2016/2017; no independent outcome record supplied"

precedesPredictionWindow :
  atMost (originalPublishedYear burischConditionalReassembly2007)
         (predictedEarliestYear burischConditionalReassembly2007)
    ≡ true
precedesPredictionWindow = refl

validProbability : Maybe Nat → Bool
validProbability nothing = false
validProbability (just p) = atMost p 1000

isScorable : ForecastProvenance → Bool
isScorable f =
  and (validProbability (frozenProbabilityPerThousand f))
  (and (fixedEventDefinitionRecorded f)
       (eventSourceIndependentlyAuthenticated f))

burischIsUnscorable : isScorable burischConditionalReassembly2007 ≡ false
burischIsUnscorable = refl

-- A synthetic fully frozen forecast illustrates a valid evidence contract;
-- its originalClip field is an EXAMPLE LOCATOR ONLY, not attributed testimony.
syntheticPrecommittedFixture : ForecastProvenance
syntheticPrecommittedFixture = forecast-provenance
  Clips.clip15 2007 2016 2017
  precommittedSpecificEvent
  (just 900) true true
  "SYNTHETIC unit test, not Dan Burisch or actual experimental evidence"

-- A mathematically proper Brier score applies ONLY AFTER a dated, frozen
-- probability and independently decided binary target are available.
-- Outcome 1=event; 0=non-event; integer probability p/1000.
-- This function is a scoring operator, not an imputed Burisch forecast.
brierMilliSquared : Nat → Bool → Nat
brierMilliSquared p true = square (natSub 1000 p)
brierMilliSquared p false = square p

-- Positive-control and penalty-control fixtures, clearly synthetic:
syntheticCalibratedPositive :
  brierMilliSquared 900 true ≡ 10000
syntheticCalibratedPositive = refl

syntheticWrongHighConfidence :
  brierMilliSquared 900 false ≡ 810000
syntheticWrongHighConfidence = refl

syntheticCoinFlip :
  brierMilliSquared 500 true ≡ 250000
syntheticCoinFlip = refl

-- Score application is uncallable with a raw unregistered claim: returning
-- nothing is a typed absence of scoring evidence, NOT an event nonoccurrence.
applyFrozenBrier :
  ForecastProvenance → Bool → Maybe Nat
applyFrozenBrier forecast observed with isScorable forecast | frozenProbabilityPerThousand forecast
... | true | just p = just (brierMilliSquared p observed)
... | _ | _ = nothing

burischOriginalCannotBeAssignedForecastScore :
  applyFrozenBrier burischConditionalReassembly2007 true ≡ nothing
burischOriginalCannotBeAssignedForecastScore = refl

syntheticFrozenForecastIsScoreable :
  applyFrozenBrier syntheticPrecommittedFixture true ≡ just 10000
syntheticFrozenForecastIsScoreable = refl

-- The score operator does not permit data-dependent cherry-picking.
data ScorableStatus : Set where
  notScorable : ScorableStatus
  precommittedAndObserved : ScorableStatus

reportScorableStatus : ForecastProvenance → ScorableStatus
reportScorableStatus f with isScorable f
... | true = precommittedAndObserved
... | false = notScorable

originalReassemblyForecastHasNoScore :
  reportScorableStatus burischConditionalReassembly2007 ≡ notScorable
originalReassemblyForecastHasNoScore = refl

-- Percentage rates are primary papers' reported aggregates, represented
-- in integer *one ten-thousandths*, NOT reconstructed trial counts.
data ExperimentFamily : Set where
  cognitiveForcedChoice : ExperimentFamily
  prestimulusPhysiology : ExperimentFamily
  mechanicalFutureViewing : ExperimentFamily
  collectiveVisualRecall : ExperimentFamily

record ReportedObservation : Set where
  constructor reported-observation
  field
    work : Attribution.AttributedSource
    paradigm : ExperimentFamily
    ratePerTenThousand : Nat
    participantCount : Nat
    numericalMeaning : String
open ReportedObservation public

bemOriginalSource : Attribution.AttributedSource
bemOriginalSource = Attribution.mkDOISource
  "Daryl J. Bem"
  "Feeling the Future: Experimental Evidence for Anomalous Retroactive Influences on Cognition and Affect"
  "Journal of Personality and Social Psychology 100(3):407-425"
  "2011"
  "10.1037/a0021524"
  "https://pubmed.ncbi.nlm.nih.gov/21280961/"
  Attribution.academicArticleSource
  "Claims time-reversed cognition tasks; not physiological presentiment replication or timeline manipulation"
  Attribution.publicAttribution

transparentPsi2023Source : Attribution.AttributedSource
transparentPsi2023Source = Attribution.mkDOISource
  "Zoltan Kekecs and collaborators"
  "Raising the value of research studies in psychological science by increasing the credibility of research reports: the transparent Psi project"
  "Royal Society Open Science 10(2):191375"
  "2023"
  "10.1098/rsos.191375"
  "https://pmc.ncbi.nlm.nih.gov/articles/PMC9890107/"
  Attribution.academicArticleSource
  "Multi-laboratory, preregistered Bem Experiment 1 replication: 10 labs, 2115 valid participants, 49.89% correct; original comparator 53.07%"
  Attribution.publicAttribution

walleczek2025Source : Attribution.AttributedSource
walleczek2025Source = Attribution.mkDOISource
  "Jan Walleczek and collaborators"
  "Metascientific replication project with the advanced meta-experimental protocol of the transparent psi project procedures for testing the precognitive effect claimed by Bem"
  "PLOS ONE 20(11):e0335330"
  "2025"
  "10.1371/journal.pone.0335330"
  "https://journals.plos.org/plosone/article?id=10.1371/journal.pone.0335330"
  Attribution.academicArticleSource
  "Study 2 reported 49.65% erotic-trial successes (below chance, p=0.013); Study 3 did not replicate: 50.07%, 217800 erotic trials, p=0.496"
  Attribution.publicAttribution

mossbridge2012Source : Attribution.AttributedSource
mossbridge2012Source = Attribution.mkDOISource
  "Julia Mossbridge; Patrizio Tressoldi; Jessica Utts"
  "Predictive Physiological Anticipation Preceding Seemingly Unpredictable Stimuli: A Meta-Analysis"
  "Frontiers in Psychology 3:390"
  "2012"
  "10.3389/fpsyg.2012.00390"
  "https://www.frontiersin.org/journals/psychology/articles/10.3389/fpsyg.2012.00390/full"
  Attribution.academicArticleSource
  "Meta-analysis of 26 reports' physiological pre-stimulus comparisons; critical experimental-family separation from Bem's cognition experiments"
  Attribution.publicAttribution

duggan2018Source : Attribution.AttributedSource
duggan2018Source = Attribution.mkDOISource
  "Michael Duggan; Patrizio Tressoldi"
  "Predictive physiological anticipatory activity preceding seemingly unpredictable stimuli: An update of Mossbridge et al.'s meta-analysis"
  "F1000Research 7:407"
  "2018"
  "10.12688/f1000research.14330.2"
  "https://f1000research.com/articles/7-407/v2"
  Attribution.academicArticleSource
  "2018 meta-analytic update retains a contested physiological-effects literature; not a verified mechanism"
  Attribution.publicAttribution

-- HISTORICAL SECONDARY COMPARATOR from Transparent Psi and subsequent
-- presentations: 53.07% ≈ 828/1560. It is NOT the original Bem 2011
-- participant-mean estimator. Direct uploaded EXP1.xlsx reproduces the
-- original 2011 53.1% participant mean as 53.1388889% and gives 826/1560
-- trial-pooled. Kept under legacy API name for older consumer stability.
originalBemExp1ReportedRate : Nat
originalBemExp1ReportedRate = 5307

originalExp1DirectParticipantMeanNumerator : Nat
originalExp1DirectParticipantMeanNumerator = 1913

originalExp1DirectParticipantMeanDenominator : Nat
originalExp1DirectParticipantMeanDenominator = 36

originalExp1DirectPooledSuccesses : Nat
originalExp1DirectPooledSuccesses = 826

transparentPsi2023ReportedRate : Nat
transparentPsi2023ReportedRate = 4989

walleczek2025Study3ReportedRate : Nat
walleczek2025Study3ReportedRate = 5007

fairChanceRate : Nat
fairChanceRate = 5000

bemVsTransparentPsi2023Difference :
  natSub originalBemExp1ReportedRate transparentPsi2023ReportedRate ≡ 318
bemVsTransparentPsi2023Difference = refl

transparentPsi2023BelowChance :
  atMost transparentPsi2023ReportedRate fairChanceRate ≡ true
transparentPsi2023BelowChance = refl

walleczek2025Study3AboveChanceNumerically :
  natSub walleczek2025Study3ReportedRate fairChanceRate ≡ 7
walleczek2025Study3AboveChanceNumerically = refl

-- Prevent an ecological/sample-size fallacy: N=2115 is *people*,
-- not the number of Bernoulli decisions in the original paper.
-- 217800 in 2025 Study 3 is its own study's trials, not 2023 people.
transparentPsiParticipantCount : Nat
transparentPsiParticipantCount = 2115

walleczek2025Study3TrialCount : Nat
walleczek2025Study3TrialCount = 217800

-- Existing evidence fibre remains *owner*: the 2025 failed replication does
-- not magically resolve post-stimulus physiology or a time machine.
reusedBemMoment :
  Trajectory.momentPhenomenon Trajectory.transparentPsi2025
    ≡ Trajectory.bemPrecognition
reusedBemMoment = refl

reusedPhysiologyMoment :
  Trajectory.momentPhenomenon Trajectory.presentimentUpdate2018
    ≡ Trajectory.presentimentPhysiology
reusedPhysiologyMoment = refl

reusedPreregisteredPhysiologyCandidate :
  Admission.experiment Admission.presentimentRoute
    ≡ Admission.presentimentPreregisteredReplication
reusedPreregisteredPhysiologyCandidate = refl

mandelaOriginalEmpiricalSource : Attribution.AttributedSource
mandelaOriginalEmpiricalSource = Mandela.prasadBainbridgeMandelaSource

data BemCognitiveNullSettlesAllPhysiologicalParadigms : Set where
data HistoricInterviewIsPrecommittedScorableMachineForecast : Set where
data TemporalPredictionDateAloneProvesReassembly : Set where
data SharedFalseMemoryEqualsChangedHistory : Set where
data TemporalEvidenceLadderCreatesTimeMachine : Set where

noCognitiveToAllPhysiologyShortcut :
  BemCognitiveNullSettlesAllPhysiologicalParadigms → ⊥
noCognitiveToAllPhysiologyShortcut ()
noInterviewForecastShortcut :
  HistoricInterviewIsPrecommittedScorableMachineForecast → ⊥
noInterviewForecastShortcut ()
noPredictionDateToEventShortcut :
  TemporalPredictionDateAloneProvesReassembly → ⊥
noPredictionDateToEventShortcut ()
noMemoryToChangedHistoryShortcut :
  SharedFalseMemoryEqualsChangedHistory → ⊥
noMemoryToChangedHistoryShortcut ()
noEvidenceFibreToMachineShortcut :
  TemporalEvidenceLadderCreatesTimeMachine → ⊥
noEvidenceFibreToMachineShortcut ()
