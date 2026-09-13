module DASHI.Wikimedia.IbrahimSnowballLearningMemoryTraumaReplicationConsensusBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballSymbolicVerificationDeweyQidDoiBidiExact as Dewey
import DASHI.Wikimedia.IbrahimSnowballTestimonyMemoryCredibilityCorroborationExpertBidiExact as Testimony
import DASHI.Cognition.PNF.DepthWheelMemoryHyperfabric as DepthMemory
import DASHI.Cognition.PNF.TraumaMemoryHypervoxelBridge as TraumaMemory
import DASHI.Education.EarlyLearningChoicePNFHyperfabricBridge as EarlyLearning

------------------------------------------------------------------------
-- IBRAHIM / LEARNING-MEMORY-TRAUMA / REPLICATION-CONSENSUS BIDI
--
-- The repo already carries a versioned memory/learning hyperfabric in which the
-- remembered public PNF may remain invariant while internal learning phase,
-- valuation/action weighting and contextual/body-memory fibres change.
--
-- This owner cross-pollinates that exact distinction with testimony,
-- corroboration, scientific reproducibility and consensus.  Repeated public
-- surfaces do not manufacture independence; replicated observations do not
-- collapse heterogeneous latent state; consensus does not become proposition
-- truth; and a trauma-labelled residual does not diagnose a person.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim learning/memory/trauma/replication/consensus BIDI"
  "verified external identity only"
  label Identity.wikidataQid
  (Identity.verified qid
    "Wikidata identity inspected 2026-09-11; identity does not create diagnosis, memory reliability, replication independence, consensus truth or causal authority")

learningQid : Identity.ExternalIdentityDemand
learningQid = mkQid "learning" "Q133500"

memoryQid : Identity.ExternalIdentityDemand
memoryQid = Testimony.memoryQid

psychologicalTraumaQid : Identity.ExternalIdentityDemand
psychologicalTraumaQid = mkQid "psychological trauma" "Q654426"

reproducibilityQid : Identity.ExternalIdentityDemand
reproducibilityQid = mkQid "reproducibility / replication in scientific method" "Q1425625"

scientificConsensusQid : Identity.ExternalIdentityDemand
scientificConsensusQid = mkQid "scientific consensus" "Q316748"

replicationIndependenceQid : Identity.ExternalIdentityDemand
replicationIndependenceQid = Identity.mkOptionalIdentityDemand
  "Ibrahim learning/memory/trauma/replication/consensus BIDI"
  "external concept identity"
  "replication independence / common-source dependence"
  Identity.wikidataQid
  (Identity.unresolved
    "no exact single QID promoted for provenance independence/common-source dependence in this pass; scientific reproducibility Q1425625 remains distinct")

------------------------------------------------------------------------
-- Dewey: retain only values explicitly inspected.
------------------------------------------------------------------------

learningDeweyPsychology : Dewey.DeweyCoordinate
learningDeweyPsychology = Dewey.mkVerifiedDewey
  "learning"
  "153.15"
  "Wikidata Q133500 DDC statement inspected 2026-09-11"

learningDeweyEducation : Dewey.DeweyCoordinate
learningDeweyEducation = Dewey.mkVerifiedDewey
  "learning"
  "370.1523"
  "Wikidata Q133500 DDC statement inspected 2026-09-11; multiple Dewey coordinates retained rather than collapsed"

psychologicalTraumaDewey : Dewey.DeweyCoordinate
psychologicalTraumaDewey = Dewey.mkUnresolvedDewey
  "psychological trauma"
  "no exact DDC statement observed on inspected Q654426 page"

reproducibilityDewey : Dewey.DeweyCoordinate
reproducibilityDewey = Dewey.mkUnresolvedDewey
  "scientific reproducibility"
  "no exact inspected DDC value promoted in this pass"

scientificConsensusDewey : Dewey.DeweyCoordinate
scientificConsensusDewey = Dewey.mkUnresolvedDewey
  "scientific consensus"
  "no exact DDC statement observed on inspected Q316748 page"

------------------------------------------------------------------------
-- DOI/source line already motivating the in-repo memory hyperfabric.
------------------------------------------------------------------------

naderReconsolidationSource : Attribution.AttributedSource
naderReconsolidationSource = Attribution.mkDOISource
  "Karim Nader; Glenn E. Schafe; Joseph E. LeDoux"
  "Fear memories require protein synthesis in the amygdala for reconsolidation after retrieval"
  "Nature 406, 722-726"
  "2000"
  "10.1038/35021052"
  "https://doi.org/10.1038/35021052"
  Attribution.academicArticleSource
  "experimental fear-memory reconsolidation result; motivates retrieval-sensitive updating but does not by itself establish a clinical trauma diagnosis or a universal theory of autobiographical memory"
  Attribution.publicAttribution

boutonExtinctionSource : Attribution.AttributedSource
boutonExtinctionSource = Attribution.mkDOISource
  "Mark E. Bouton"
  "Context and Behavioral Processes in Extinction"
  "Learning & Memory 11, 485-494"
  "2004"
  "10.1101/lm.78804"
  "https://doi.org/10.1101/lm.78804"
  Attribution.academicArticleSource
  "review supporting context-sensitive extinction/new learning rather than simple erasure of original learning; source role is empirical/theoretical motivation, not clinical diagnosis"
  Attribution.publicAttribution

schillerReconsolidationUpdateSource : Attribution.AttributedSource
schillerReconsolidationUpdateSource = Attribution.mkDOISource
  "Daniela Schiller; Marie-H. Monfils; Candace M. Raio; David C. Johnson; Joseph E. LeDoux; Elizabeth A. Phelps"
  "Preventing the return of fear in humans using reconsolidation update mechanisms"
  "Nature 463, 49-53"
  "2010"
  "10.1038/nature08637"
  "https://doi.org/10.1038/nature08637"
  Attribution.academicArticleSource
  "human fear-conditioning/reconsolidation-update study; represented together with its later addendum and not promoted to universal clinical efficacy"
  Attribution.publicAttribution

schillerAddendumSource : Attribution.AttributedSource
schillerAddendumSource = Attribution.mkDOISource
  "Daniela Schiller; Marie-H. Monfils; Candace M. Raio; David C. Johnson; Joseph E. LeDoux; Elizabeth A. Phelps"
  "Addendum: Preventing the return of fear in humans using reconsolidation update mechanisms"
  "Nature 562, E21"
  "2018"
  "10.1038/s41586-018-0405-7"
  "https://doi.org/10.1038/s41586-018-0405-7"
  Attribution.academicArticleSource
  "later methodological clarification of exclusion criteria/final dataset for replication; addendum supplements rather than silently rewriting provenance"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Exact reuse: the repo already says the public remembered PNF can stay equal
-- while full memory state advances/changes.
------------------------------------------------------------------------

depthMemoryBoundary : DepthMemory.DepthWheelMemoryHyperfabricBoundary
depthMemoryBoundary = DepthMemory.canonicalDepthWheelMemoryHyperfabricBoundary

traumaMemoryBoundary : TraumaMemory.TraumaMemoryHypervoxelAuthorityBoundary
traumaMemoryBoundary = TraumaMemory.canonicalTraumaMemoryHypervoxelAuthorityBoundary

earlyLearningBoundary : EarlyLearning.EarlyLearningPNFCrossPollination
earlyLearningBoundary = EarlyLearning.canonicalEarlyLearningPNFCrossPollination

testimonyBoundary : Testimony.TestimonyMemoryCredibilityBoundary
testimonyBoundary = Testimony.canonicalTestimonyMemoryCredibilityBoundary

------------------------------------------------------------------------
-- Regression 1: same remembered/reportable semantic surface cannot recover the
-- full learning-memory state.
------------------------------------------------------------------------

data MemoryStateCase : Set where
  samePublicMemoryEarlierPhase samePublicMemoryLaterPhase : MemoryStateCase

data PublicMemorySurface : Set where sameRememberedSemanticSurface : PublicMemorySurface
data LatentLearningState : Set where earlierLearningState laterLearningState : LatentLearningState

publicMemorySurface : MemoryStateCase → PublicMemorySurface
publicMemorySurface _ = sameRememberedSemanticSurface

latentLearningState : MemoryStateCase → LatentLearningState
latentLearningState samePublicMemoryEarlierPhase = earlierLearningState
latentLearningState samePublicMemoryLaterPhase = laterLearningState

memoryStateDefect : INF.NonFactorabilityWitness publicMemorySurface latentLearningState
memoryStateDefect = INF.nonFactorabilityWitness
  samePublicMemoryEarlierPhase samePublicMemoryLaterPhase refl (λ ())

publicRememberedSurfaceCannotFactorFullLearningState :
  INF.FactorsThrough publicMemorySurface latentLearningState → ⊥
publicRememberedSurfaceCannotFactorFullLearningState =
  INF.witnessRulesOutEveryFlatFactorisation memoryStateDefect

------------------------------------------------------------------------
-- Regression 2: extinction/non-expression cannot recover erasure status.
------------------------------------------------------------------------

data ExtinctionCase : Set where
  sameNonExpressionOriginalLearningRetained sameNonExpressionDifferentHistory : ExtinctionCase

data BehaviourSurface : Set where sameObservedNonExpression : BehaviourSurface
data LearningHistory : Set where originalLearningRetained alternativeHistory : LearningHistory

behaviourSurface : ExtinctionCase → BehaviourSurface
behaviourSurface _ = sameObservedNonExpression

learningHistory : ExtinctionCase → LearningHistory
learningHistory sameNonExpressionOriginalLearningRetained = originalLearningRetained
learningHistory sameNonExpressionDifferentHistory = alternativeHistory

extinctionHistoryDefect : INF.NonFactorabilityWitness behaviourSurface learningHistory
extinctionHistoryDefect = INF.nonFactorabilityWitness
  sameNonExpressionOriginalLearningRetained sameNonExpressionDifferentHistory refl (λ ())

observedNonExpressionCannotFactorMemoryErasure :
  INF.FactorsThrough behaviourSurface learningHistory → ⊥
observedNonExpressionCannotFactorMemoryErasure =
  INF.witnessRulesOutEveryFlatFactorisation extinctionHistoryDefect

------------------------------------------------------------------------
-- Regression 3: repeated/replicated result surface cannot recover provenance
-- independence.  This is the scientific analogue of generated testimony.
------------------------------------------------------------------------

data ReplicationCase : Set where
  sameReplicationCountIndependent sameReplicationCountCommonSource : ReplicationCase

data ReplicationSurface : Set where sameReplicationMultiplicity : ReplicationSurface
data ProvenanceIndependence : Set where independentlyProduced commonSourceDependent : ProvenanceIndependence

replicationSurface : ReplicationCase → ReplicationSurface
replicationSurface _ = sameReplicationMultiplicity

provenanceIndependence : ReplicationCase → ProvenanceIndependence
provenanceIndependence sameReplicationCountIndependent = independentlyProduced
provenanceIndependence sameReplicationCountCommonSource = commonSourceDependent

replicationIndependenceDefect : INF.NonFactorabilityWitness replicationSurface provenanceIndependence
replicationIndependenceDefect = INF.nonFactorabilityWitness
  sameReplicationCountIndependent sameReplicationCountCommonSource refl (λ ())

replicationMultiplicityCannotFactorIndependence :
  INF.FactorsThrough replicationSurface provenanceIndependence → ⊥
replicationMultiplicityCannotFactorIndependence =
  INF.witnessRulesOutEveryFlatFactorisation replicationIndependenceDefect

------------------------------------------------------------------------
-- Regression 4: consensus cannot recover proposition truth.
------------------------------------------------------------------------

data ConsensusCase : Set where
  sameConsensusClaimTrue sameConsensusClaimFalse : ConsensusCase

data ConsensusSurface : Set where sameScientificConsensusSurface : ConsensusSurface
data ClaimTruth : Set where claimTrue claimFalse : ClaimTruth

consensusSurface : ConsensusCase → ConsensusSurface
consensusSurface _ = sameScientificConsensusSurface

claimTruth : ConsensusCase → ClaimTruth
claimTruth sameConsensusClaimTrue = claimTrue
claimTruth sameConsensusClaimFalse = claimFalse

consensusTruthDefect : INF.NonFactorabilityWitness consensusSurface claimTruth
consensusTruthDefect = INF.nonFactorabilityWitness
  sameConsensusClaimTrue sameConsensusClaimFalse refl (λ ())

scientificConsensusCannotFactorTruth :
  INF.FactorsThrough consensusSurface claimTruth → ⊥
scientificConsensusCannotFactorTruth =
  INF.witnessRulesOutEveryFlatFactorisation consensusTruthDefect

------------------------------------------------------------------------
-- Regression 5: trauma-labelled residual/channel cannot recover diagnosis.
------------------------------------------------------------------------

data TraumaCarrierCase : Set where
  sameTraumaResidualNoDiagnosis sameTraumaResidualDiagnosisSeparatelyPaid : TraumaCarrierCase

data TraumaResidualSurface : Set where sameTraumaMemoryResidual : TraumaResidualSurface
data DiagnosticStatus : Set where diagnosisNotEstablished diagnosisEstablishedElsewhere : DiagnosticStatus

traumaResidualSurface : TraumaCarrierCase → TraumaResidualSurface
traumaResidualSurface _ = sameTraumaMemoryResidual

diagnosticStatus : TraumaCarrierCase → DiagnosticStatus
diagnosticStatus sameTraumaResidualNoDiagnosis = diagnosisNotEstablished
diagnosticStatus sameTraumaResidualDiagnosisSeparatelyPaid = diagnosisEstablishedElsewhere

traumaDiagnosisDefect : INF.NonFactorabilityWitness traumaResidualSurface diagnosticStatus
traumaDiagnosisDefect = INF.nonFactorabilityWitness
  sameTraumaResidualNoDiagnosis sameTraumaResidualDiagnosisSeparatelyPaid refl (λ ())

traumaMemoryResidualCannotFactorDiagnosis :
  INF.FactorsThrough traumaResidualSurface diagnosticStatus → ⊥
traumaMemoryResidualCannotFactorDiagnosis =
  INF.witnessRulesOutEveryFlatFactorisation traumaDiagnosisDefect

------------------------------------------------------------------------
-- Reverse BIDI constraints.
------------------------------------------------------------------------

record LearningMemoryReverseConstraint : Set where
  constructor learning-memory-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open LearningMemoryReverseConstraint public

memoryConstraint : LearningMemoryReverseConstraint
memoryConstraint = learning-memory-reverse-constraint
  "Memory / cognition"
  "remembered semantic identity, latent phase, valuation, action weight, context, retrieval/update history and report remain separately recoverable"
  false

learningConstraint : LearningMemoryReverseConstraint
learningConstraint = learning-memory-reverse-constraint
  "Learning / education"
  "observable performance, retained learning, extinction/new learning, contextual support, agency and developmental opportunity remain distinct"
  false

traumaConstraint : LearningMemoryReverseConstraint
traumaConstraint = learning-memory-reverse-constraint
  "Trauma / body-memory hyperfabric"
  "typed residual/channel, contextual memory, arousal/affect/body fibres, narrative access and clinical diagnosis remain distinct"
  false

replicationConstraint : LearningMemoryReverseConstraint
replicationConstraint = learning-memory-reverse-constraint
  "Replication / corroboration / consensus"
  "result multiplicity, methodological reproducibility, provenance independence, common-source dependence, uncertainty and consensus remain distinct"
  false

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data SameRememberedSurfaceMeansSameMemoryState : Set where
data ExtinctionMeansMemoryErasure : Set where
data TraumaResidualMeansDiagnosis : Set where
data RepetitionMeansIndependentReplication : Set where
data ReproducibilityMeansTruth : Set where
data ConsensusMeansTruth : Set where
data QidMeansDiagnosis : Set where

sameRememberedSurfaceDoesNotMeanSameMemoryState : SameRememberedSurfaceMeansSameMemoryState → ⊥
sameRememberedSurfaceDoesNotMeanSameMemoryState ()

extinctionDoesNotMeanMemoryErasure : ExtinctionMeansMemoryErasure → ⊥
extinctionDoesNotMeanMemoryErasure ()

traumaResidualDoesNotMeanDiagnosis : TraumaResidualMeansDiagnosis → ⊥
traumaResidualDoesNotMeanDiagnosis ()

repetitionDoesNotMeanIndependentReplication : RepetitionMeansIndependentReplication → ⊥
repetitionDoesNotMeanIndependentReplication ()

reproducibilityDoesNotMeanTruth : ReproducibilityMeansTruth → ⊥
reproducibilityDoesNotMeanTruth ()

consensusDoesNotMeanTruth : ConsensusMeansTruth → ⊥
consensusDoesNotMeanTruth ()

qidDoesNotMeanDiagnosis : QidMeansDiagnosis → ⊥
qidDoesNotMeanDiagnosis ()

record LearningMemoryTraumaReplicationConsensusBoundary : Set where
  constructor learning-memory-trauma-replication-consensus-boundary
  field
    qidsAttachedWhenSafelyResolved : Bool
    multipleDeweyCoordinatesRetainedWhenSourceSuppliesThem : Bool
    doiSourceRolesRetained : Bool
    publicRememberedSurfaceSeparatedFromFullMemoryState : Bool
    extinctionSeparatedFromErasure : Bool
    traumaResidualSeparatedFromDiagnosis : Bool
    replicationMultiplicitySeparatedFromIndependence : Bool
    reproducibilitySeparatedFromTruth : Bool
    consensusSeparatedFromTruth : Bool
    schillerAddendumRetainedAsSeparateProvenanceObject : Bool
    reverseBidiConstraintsPropagateUpward : Bool
    presentAxisVocabularyClaimedComplete : Bool
open LearningMemoryTraumaReplicationConsensusBoundary public

canonicalLearningMemoryTraumaReplicationConsensusBoundary :
  LearningMemoryTraumaReplicationConsensusBoundary
canonicalLearningMemoryTraumaReplicationConsensusBoundary =
  learning-memory-trauma-replication-consensus-boundary
    true true true true true true true true true true true false
