module DASHI.Wikimedia.IbrahimSnowballAtomicClaimIntentExperimentAdequacyBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Core.ConsumerIndexedTrajectoryFibreAdequacyExact as Consumer
import DASHI.Core.ConsumerFibreRefinementSchedulerExact as Scheduler
import DASHI.Core.ExperimentalCoordinateDesignExact as Experiment
import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as PNF
import DASHI.Reasoning.EvidenceDesignAdmissibilityExact as EvidenceDesign
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballSymbolicVerificationDeweyQidDoiBidiExact as Dewey
import DASHI.Wikimedia.IbrahimSnowballDependencyNDimLocalGlobalProofSearchBidiExact as Prior

------------------------------------------------------------------------
-- IBRAHIM / ATOMIC CLAIM / HUMAN INTENT / EXPERIMENT ADEQUACY BIDI
--
-- The recurrent failure mode addressed here is not merely missing evidence.
-- A human starts from ordinary language; the implementation chooses an atomic
-- claim/constructor/operationalisation; a study or test then answers some exact
-- consumer.  A green result is meaningful only when those contracts line up.
--
-- human intent
--   -> atomic claim decomposition
--   -> constructor/representation
--   -> operationalisation
--   -> design / executed test
--   -> exact consumer
--   -> result
--
-- Failure of any weld is retained as misspecification, not silently reported as
-- confirmation/refutation of the human's original intended question.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim atomic-claim/intent/experiment-adequacy BIDI"
  "verified external identity only"
  label Identity.wikidataQid
  (Identity.verified qid
    "Wikidata identity inspected 2026-09-11; identity does not create semantic adequacy, construct validity, design validity, claim truth or consumer alignment")

scientificHypothesisQid : Identity.ExternalIdentityDemand
scientificHypothesisQid = mkQid "scientific hypothesis" "Q3144351"

scientificMethodQid : Identity.ExternalIdentityDemand
scientificMethodQid = mkQid "scientific method" "Q46857"

operationalizationQid : Identity.ExternalIdentityDemand
operationalizationQid = mkQid "operationalization" "Q286017"

constructValidityQid : Identity.ExternalIdentityDemand
constructValidityQid = Identity.mkOptionalIdentityDemand
  "Ibrahim atomic-claim/intent/experiment-adequacy BIDI"
  "external concept identity"
  "construct validity"
  Identity.wikidataQid
  (Identity.unresolved
    "no exact broad construct-validity QID promoted in this pass; article QIDs and nearby test-validity concepts are not substituted for the concept itself")

------------------------------------------------------------------------
-- Dewey remains a navigation coordinate, not a semantics compiler.
------------------------------------------------------------------------

scientificHypothesisDewey : Dewey.DeweyCoordinate
scientificHypothesisDewey = Dewey.mkUnresolvedDewey
  "scientific hypothesis"
  "no exact inspected DDC value promoted in this pass"

operationalizationDewey : Dewey.DeweyCoordinate
operationalizationDewey = Dewey.mkUnresolvedDewey
  "operationalization / construct validity"
  "methodological concept retained without forcing one shelf"

------------------------------------------------------------------------
-- DOI-bounded methodological precedents.
------------------------------------------------------------------------

blackwellExperimentComparisonSource : Attribution.AttributedSource
blackwellExperimentComparisonSource = Attribution.mkDOISource
  "David Blackwell"
  "Equivalent Comparisons of Experiments"
  "The Annals of Mathematical Statistics 24(2), 265-272"
  "1953"
  "10.1214/aoms/1177729032"
  "https://doi.org/10.1214/aoms/1177729032"
  Attribution.academicArticleSource
  "conceptual precedent for comparing information supplied by experiments; DASHI's query-indexed consumer adequacy and FactorsThrough implementation remain repository-local constructions"
  Attribution.publicAttribution

cronbachMeehlConstructValiditySource : Attribution.AttributedSource
cronbachMeehlConstructValiditySource = Attribution.mkDOISource
  "Lee J. Cronbach; Paul E. Meehl"
  "Construct validity in psychological tests"
  "Psychological Bulletin 52(4), 281-302"
  "1955"
  "10.1037/h0040957"
  "https://doi.org/10.1037/h0040957"
  Attribution.academicArticleSource
  "classic construct-validity treatment: an observed test/operation does not become identical to the theoretical construct merely because it is named as its measure; validation depends on explicit interpretation and evidential relations"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Exact reuse of existing repository boundaries.
------------------------------------------------------------------------

pnfBoundary : PNF.PredicateNormalFormBoundary
pnfBoundary = PNF.canonicalPredicateNormalFormBoundary

queryAdequacyBoundary : Query.QueryIndexedProjectionAdequacyBoundary
queryAdequacyBoundary = Query.canonicalQueryIndexedProjectionAdequacyBoundary

consumerAdequacyBoundary : Consumer.ConsumerIndexedTrajectoryFibreBoundary
consumerAdequacyBoundary = Consumer.canonicalConsumerIndexedTrajectoryFibreBoundary

schedulerBoundary : Scheduler.ConsumerFibreRefinementSchedulerBoundary
schedulerBoundary = Scheduler.canonicalConsumerFibreRefinementSchedulerBoundary

evidenceDesignBoundary : EvidenceDesign.EvidenceDesignBoundary
evidenceDesignBoundary = EvidenceDesign.canonicalEvidenceDesignBoundary

experimentalCoordinateBoundary : Experiment.ExperimentalCoordinateBoundary
experimentalCoordinateBoundary = Experiment.canonicalExperimentalCoordinateBoundary

priorNDimBoundary : Prior.DependencyNDimLocalGlobalProofSearchBoundary
priorNDimBoundary = Prior.canonicalDependencyNDimLocalGlobalProofSearchBoundary

------------------------------------------------------------------------
-- Atomic claim contract.
------------------------------------------------------------------------

record AtomicClaimContract : Set where
  constructor atomicClaimContract
  field
    humanRequest : String
    atomicAssertion : PNF.PredicateNormalAssertion
    intendedConsumer : EvidenceDesign.EvidenceQuestion
    constructorReading : String
    operationalizationReading : String
    comparatorReading : String
    outcomeReading : String
    populationReading : String
    timeReading : String
    ambiguityAudit : String
    constructorMatchesIntendedClaim : Bool
    operationalizationMatchesConstruct : Bool
    designAffordsIntendedConsumer : Bool
    executedTestMatchesIntendedConsumer : Bool
open AtomicClaimContract public

-- A successful result is only downstream of the exact contract actually tested.
record ExecutedAtomicTest : Set where
  constructor executedAtomicTest
  field
    contract : AtomicClaimContract
    testedConsumer : EvidenceDesign.EvidenceQuestion
    testReading : String
    resultReading : String
    testExecutionSucceeded : Bool
    sameAsIntendedConsumerPaid : Bool
open ExecutedAtomicTest public

------------------------------------------------------------------------
-- Regression 1: plain language is not atomic by default.
-- The same sentence can be intended associationally or causally.
------------------------------------------------------------------------

data IntentCase : Set where
  sameSentenceAssociationalIntent sameSentenceCausalIntent : IntentCase

data PlainLanguageSurface : Set where sameHumanSentence : PlainLanguageSurface
data AtomicIntent : Set where associationalAtomicIntent causalAtomicIntent : AtomicIntent

plainLanguageSurface : IntentCase → PlainLanguageSurface
plainLanguageSurface _ = sameHumanSentence

atomicIntent : IntentCase → AtomicIntent
atomicIntent sameSentenceAssociationalIntent = associationalAtomicIntent
atomicIntent sameSentenceCausalIntent = causalAtomicIntent

plainLanguageIntentDefect : INF.NonFactorabilityWitness plainLanguageSurface atomicIntent
plainLanguageIntentDefect = INF.nonFactorabilityWitness
  sameSentenceAssociationalIntent sameSentenceCausalIntent refl (λ ())

plainLanguageCannotFactorAtomicIntent :
  INF.FactorsThrough plainLanguageSurface atomicIntent → ⊥
plainLanguageCannotFactorAtomicIntent =
  INF.witnessRulesOutEveryFlatFactorisation plainLanguageIntentDefect

------------------------------------------------------------------------
-- Regression 2: a well-typed constructor may still encode the wrong claim.
------------------------------------------------------------------------

data ConstructorCase : Set where
  sameWellTypedConstructorAdequate sameWellTypedConstructorMisSpecified : ConstructorCase

data ConstructorSurface : Set where sameWellTypedConstruction : ConstructorSurface
data ConstructorAdequacy : Set where constructorAdequate constructorWrongForIntent : ConstructorAdequacy

constructorSurface : ConstructorCase → ConstructorSurface
constructorSurface _ = sameWellTypedConstruction

constructorAdequacy : ConstructorCase → ConstructorAdequacy
constructorAdequacy sameWellTypedConstructorAdequate = constructorAdequate
constructorAdequacy sameWellTypedConstructorMisSpecified = constructorWrongForIntent

constructorAdequacyDefect : INF.NonFactorabilityWitness constructorSurface constructorAdequacy
constructorAdequacyDefect = INF.nonFactorabilityWitness
  sameWellTypedConstructorAdequate sameWellTypedConstructorMisSpecified refl (λ ())

wellTypedConstructorCannotFactorSemanticAdequacy :
  INF.FactorsThrough constructorSurface constructorAdequacy → ⊥
wellTypedConstructorCannotFactorSemanticAdequacy =
  INF.witnessRulesOutEveryFlatFactorisation constructorAdequacyDefect

------------------------------------------------------------------------
-- Regression 3: a green/passing test cannot recover whether the intended
-- consumer was actually tested.
------------------------------------------------------------------------

data TestCase : Set where
  sameGreenResultRightConsumer sameGreenResultDifferentConsumer : TestCase

data TestSurface : Set where samePassingExecution : TestSurface
data ConsumerMatch : Set where intendedConsumerTested differentConsumerTested : ConsumerMatch

testSurface : TestCase → TestSurface
testSurface _ = samePassingExecution

consumerMatch : TestCase → ConsumerMatch
consumerMatch sameGreenResultRightConsumer = intendedConsumerTested
consumerMatch sameGreenResultDifferentConsumer = differentConsumerTested

greenTestConsumerDefect : INF.NonFactorabilityWitness testSurface consumerMatch
greenTestConsumerDefect = INF.nonFactorabilityWitness
  sameGreenResultRightConsumer sameGreenResultDifferentConsumer refl (λ ())

greenTestCannotFactorIntendedConsumerMatch :
  INF.FactorsThrough testSurface consumerMatch → ⊥
greenTestCannotFactorIntendedConsumerMatch =
  INF.witnessRulesOutEveryFlatFactorisation greenTestConsumerDefect

------------------------------------------------------------------------
-- Regression 4: an operational measure cannot recover construct identity.
------------------------------------------------------------------------

data OperationalizationCase : Set where
  sameMeasureConstructA sameMeasureConstructB : OperationalizationCase

data MeasureSurface : Set where sameObservedMeasure : MeasureSurface
data ConstructInterpretation : Set where constructInterpretationA constructInterpretationB : ConstructInterpretation

measureSurface : OperationalizationCase → MeasureSurface
measureSurface _ = sameObservedMeasure

constructInterpretation : OperationalizationCase → ConstructInterpretation
constructInterpretation sameMeasureConstructA = constructInterpretationA
constructInterpretation sameMeasureConstructB = constructInterpretationB

operationalizationDefect : INF.NonFactorabilityWitness measureSurface constructInterpretation
operationalizationDefect = INF.nonFactorabilityWitness
  sameMeasureConstructA sameMeasureConstructB refl (λ ())

measureCannotFactorConstructInterpretation :
  INF.FactorsThrough measureSurface constructInterpretation → ⊥
measureCannotFactorConstructInterpretation =
  INF.witnessRulesOutEveryFlatFactorisation operationalizationDefect

------------------------------------------------------------------------
-- Regression 5: a design can answer one question without answering another.
-- This is the experiment-design form of consumer-indexed projection adequacy.
------------------------------------------------------------------------

data DesignConsumerCase : Set where
  sameDesignAssociationQuestion sameDesignCausalQuestion : DesignConsumerCase

data DesignSurface : Set where sameStudyDesignSurface : DesignSurface
data DesignAnswerability : Set where designAnswersQuestion designDoesNotAnswerQuestion : DesignAnswerability

designSurface : DesignConsumerCase → DesignSurface
designSurface _ = sameStudyDesignSurface

designAnswerability : DesignConsumerCase → DesignAnswerability
designAnswerability sameDesignAssociationQuestion = designAnswersQuestion
designAnswerability sameDesignCausalQuestion = designDoesNotAnswerQuestion

designConsumerDefect : INF.NonFactorabilityWitness designSurface designAnswerability
designConsumerDefect = INF.nonFactorabilityWitness
  sameDesignAssociationQuestion sameDesignCausalQuestion refl (λ ())

designIdentityCannotFactorQuestionAdequacy :
  INF.FactorsThrough designSurface designAnswerability → ⊥
designIdentityCannotFactorQuestionAdequacy =
  INF.witnessRulesOutEveryFlatFactorisation designConsumerDefect

------------------------------------------------------------------------
-- Mis-specification taxonomy.  These are different residuals because the repair
-- differs: clarify prose, split atoms, change constructor, change measure,
-- change design, change consumer, or reinterpret the test result narrowly.
------------------------------------------------------------------------

data SpecificationResidual : Set where
  plainLanguageAmbiguity : SpecificationResidual
  nonAtomicClaim : SpecificationResidual
  quantifierMismatch : SpecificationResidual
  populationMismatch : SpecificationResidual
  comparatorMismatch : SpecificationResidual
  outcomeMismatch : SpecificationResidual
  temporalMismatch : SpecificationResidual
  inferentialForceMismatch : SpecificationResidual
  constructOperationalizationMismatch : SpecificationResidual
  constructorConsumerMismatch : SpecificationResidual
  designConsumerMismatch : SpecificationResidual
  executedTestConsumerMismatch : SpecificationResidual
  transportMismatch : SpecificationResidual
  noSpecificationResidual : SpecificationResidual

record SpecificationRepair : Set where
  constructor specificationRepair
  field
    residual : SpecificationResidual
    repairReading : String
    requiresNewEvidence : Bool
    requiresNewExperiment : Bool
    requiresHumanIntentClarification : Bool
open SpecificationRepair public

clarifyAmbiguousIntent : SpecificationRepair
clarifyAmbiguousIntent = specificationRepair
  plainLanguageAmbiguity
  "make the intended atomic proposition, quantifier, scope, comparator, outcome and inferential force explicit before treating any test as responsive"
  false false true

repairWrongExperiment : SpecificationRepair
repairWrongExperiment = specificationRepair
  designConsumerMismatch
  "retain the existing result for the consumer it actually answers; select or design an experiment that affords the intended consumer instead"
  false true false

repairWrongConstructor : SpecificationRepair
repairWrongConstructor = specificationRepair
  constructorConsumerMismatch
  "retain the well-typed object but do not promote it; reconstruct the claim under a constructor whose semantics match the intended consumer"
  false false true

------------------------------------------------------------------------
-- Reverse BIDI constraints into Ibrahim parent nodes.
------------------------------------------------------------------------

record AtomicClaimReverseConstraint : Set where
  constructor atomic-claim-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open AtomicClaimReverseConstraint public

languageConstraint : AtomicClaimReverseConstraint
languageConstraint = atomic-claim-reverse-constraint
  "Natural language / knowledge representation"
  "surface sentence, intended atomic propositions, quantifier, scope, inferential force and ambiguity remain distinct"
  false

experimentConstraint : AtomicClaimReverseConstraint
experimentConstraint = atomic-claim-reverse-constraint
  "Experiment / study design"
  "hypothesis, construct, operationalization, design affordance, executed test and intended consumer remain separately witnessed"
  false

proofConstraint : AtomicClaimReverseConstraint
proofConstraint = atomic-claim-reverse-constraint
  "Proof search / verification"
  "well-typed constructor, proved local theorem, exact consumer, same-object applicability and programme claim remain distinct"
  false

humanMachineConstraint : AtomicClaimReverseConstraint
humanMachineConstraint = atomic-claim-reverse-constraint
  "Human-machine specification"
  "what the human meant, what the formal constructor denotes, what the executable test checks and what the returned result licenses remain distinct"
  false

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data PlainLanguageIsAtomic : Set where
data WellTypedMeansIntendedMeaning : Set where
data GreenTestMeansIntendedClaimTested : Set where
data OperationalizationEqualsConstruct : Set where
data DesignNameDeterminesConsumerAdequacy : Set where
data TestedDifferentQuestionRefutesIntendedClaim : Set where
data MoreFormalisationMeansBetterSpecification : Set where

plainLanguageDoesNotCreateAtomicity : PlainLanguageIsAtomic → ⊥
plainLanguageDoesNotCreateAtomicity ()

wellTypedDoesNotCreateIntendedMeaning : WellTypedMeansIntendedMeaning → ⊥
wellTypedDoesNotCreateIntendedMeaning ()

greenDoesNotMeanIntendedClaimWasTested : GreenTestMeansIntendedClaimTested → ⊥
greenDoesNotMeanIntendedClaimWasTested ()

operationalizationDoesNotEqualConstructByNaming : OperationalizationEqualsConstruct → ⊥
operationalizationDoesNotEqualConstructByNaming ()

designNameDoesNotDetermineConsumerAdequacy : DesignNameDeterminesConsumerAdequacy → ⊥
designNameDoesNotDetermineConsumerAdequacy ()

testingDifferentQuestionDoesNotRefuteIntendedClaim : TestedDifferentQuestionRefutesIntendedClaim → ⊥
testingDifferentQuestionDoesNotRefuteIntendedClaim ()

moreFormalisationDoesNotRepairMisSpecification : MoreFormalisationMeansBetterSpecification → ⊥
moreFormalisationDoesNotRepairMisSpecification ()

record AtomicClaimIntentExperimentAdequacyBoundary : Set where
  constructor atomic-claim-intent-experiment-adequacy-boundary
  field
    naturalLanguageIsNotAtomicByDefault : Bool
    claimDecompositionMustRetainQuantifierScopeAndForce : Bool
    constructorAdequacyIsConsumerIndexed : Bool
    operationalizationSeparatedFromConstruct : Bool
    designAdequacyIsQuestionIndexed : Bool
    greenExecutionSeparatedFromConsumerMatch : Bool
    wrongQuestionResultRetainedButNotPromoted : Bool
    specificationResidualDeterminesRepairKind : Bool
    qidsAttachedOrExplicitlyUnresolved : Bool
    deweyUnresolvedStateRetained : Bool
    doiMethodologySourcesAttached : Bool
    existingQueryAndConsumerAdequacyReused : Bool
    existingExperimentDesignAdmissibilityReused : Bool
    priorNDimDependencyOwnerReused : Bool
    presentSpecificationVocabularyClaimedComplete : Bool
open AtomicClaimIntentExperimentAdequacyBoundary public

canonicalAtomicClaimIntentExperimentAdequacyBoundary :
  AtomicClaimIntentExperimentAdequacyBoundary
canonicalAtomicClaimIntentExperimentAdequacyBoundary =
  atomic-claim-intent-experiment-adequacy-boundary
    true true true true true true true true true true true true true true false
