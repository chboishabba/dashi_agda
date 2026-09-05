module DASHI.Reasoning.JusticeLeeSensibLawExperimentSearchCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Interop.SensibLawResidualLattice as SL
import DASHI.Reasoning.AristotleActiveExperimentalProofSearchLoopExact as Aristotle
import DASHI.Reasoning.JusticeLeeSensibLawAdversarialProofGraphBidiExact as Legal

------------------------------------------------------------------------
-- JUSTICE LEE × SENSIBLAW × ARISTOTLE ACTIVE-EXPERIMENT CROSS-POLLINATION
--
-- Common loop:
-- live legal hypotheses -> controversy collision -> discriminator synthesis
-- -> targeted evidence/search probe -> proposition-fibre refinement
-- -> guarded common-ground merge -> selective reopening -> consumer closure.
--
-- This is a DASHI cross-domain construction. Lee motivates the proposition-
-- oriented, source-linked procedural target; Harmonic's Aristotle motivates
-- formal-feedback proof search; the adaptive experimental loop is already
-- explicitly owned by DASHI in AristotleActiveExperimentalProofSearchLoopExact.
------------------------------------------------------------------------

data LegalHypothesis : Set where
  applicantAccount respondentAccount sharedAccount alternativeAccount : LegalHypothesis

data EvidenceProbe : Set where
  inspectSourceSpan inspectAccountHistory inspectMessageThread inspectReport
  inspectWitness inspectCausalEdge inspectCharacterisation : EvidenceProbe

data ProbeOutcome : Set where
  supportsApplicant supportsRespondent supportsShared leavesUnderdetermined contradictsBoth : ProbeOutcome

record LegalExperiment : Set where
  constructor legalExperiment
  field
    residual : Legal.ControversyResidual
    probe : EvidenceProbe
    expectedDiscriminator : String
    evidenceTarget : String
    experimentReference : String
open LegalExperiment public

record LegalCollision : Set where
  constructor legalCollision
  field
    leftNode : Legal.PropositionFibre
    rightNode : Legal.PropositionFibre
    sameSurfacePNF : SL.ResidualLevel
    hiddenKind : Legal.DisagreementKind
    downstreamQuestion : String
open LegalCollision public

record DiscriminatorChoice : Set where
  constructor discriminatorChoice
  field
    collision : LegalCollision
    chosenProbe : EvidenceProbe
    choiceReference : String
open DiscriminatorChoice public

data LegalSearchStage : Set where
  liveControversy collisionLocated discriminatorSelected evidenceObserved
  controversyRefined commonGroundMerged obligationsReopened proceduralConsumerClosed : LegalSearchStage

record LegalSearchState : Set where
  constructor legalSearchState
  field
    graph : Legal.ProofGraph
    stage : LegalSearchStage
    liveResiduals : List Legal.ControversyResidual
    openObligations : List Legal.ProofObligation
    searchReference : String
open LegalSearchState public

record LegalObservationReceipt : Set where
  constructor legalObservationReceipt
  field
    experiment : LegalExperiment
    outcome : ProbeOutcome
    sourceReference : String
    observationReference : String
open LegalObservationReceipt public

record LegalRefinementReceipt : Set where
  constructor legalRefinementReceipt
  field
    before : LegalSearchState
    observation : LegalObservationReceipt
    after : LegalSearchState
    refinesOnlyAffectedFibre : Bool
    refinesOnlyAffectedFibreIsTrue : refinesOnlyAffectedFibre ≡ true
    refinementReference : String
open LegalRefinementReceipt public

record CommonGroundMerge : Set where
  constructor commonGroundMerge
  field
    applicantNode : Legal.PropositionFibre
    respondentNode : Legal.PropositionFibre
    residual : SL.ResidualLevel
    partyAdmissionOrTraceReceipt : String
    mergedAsProvedFactWithoutAdjudication : Bool
    mergedAsProvedFactWithoutAdjudicationIsFalse : mergedAsProvedFactWithoutAdjudication ≡ false
    mergeReference : String
open CommonGroundMerge public

data LegalArtifact : Set where
  sourceCertificate propositionCertificate relationCertificate residualCertificate
  discriminatorCertificate proceduralCertificate : LegalArtifact

data LegalDepends : LegalArtifact → LegalArtifact → Set where
  sourceAffectsProposition : LegalDepends sourceCertificate propositionCertificate
  propositionAffectsRelation : LegalDepends propositionCertificate relationCertificate
  relationAffectsResidual : LegalDepends relationCertificate residualCertificate
  residualAffectsDiscriminator : LegalDepends residualCertificate discriminatorCertificate
  discriminatorAffectsProcedure : LegalDepends discriminatorCertificate proceduralCertificate

record SelectiveLegalReopening : Set where
  constructor selectiveLegalReopening
  field
    changedArtifact : LegalArtifact
    reopen : List LegalArtifact
    reopensWholeCaseByDefault : Bool
    reopensWholeCaseByDefaultIsFalse : reopensWholeCaseByDefault ≡ false
    reopeningReference : String
open SelectiveLegalReopening public

canonicalSourceReopening : SelectiveLegalReopening
canonicalSourceReopening = selectiveLegalReopening sourceCertificate
  (propositionCertificate ∷ relationCertificate ∷ residualCertificate ∷ discriminatorCertificate ∷ proceduralCertificate ∷ [])
  false refl
  "changed source trace selectively reopens the proposition/relation/residual/discriminator/procedural dependency cone, not unrelated case material"

record LegalExperimentalBidi : Set where
  constructor legalExperimentalBidi
  field
    reverseSearch : Legal.ReverseProofSearch
    experiment : LegalExperiment
    observation : LegalObservationReceipt
    refinement : LegalRefinementReceipt
    targetedAtDeclaredResidual :
      LegalExperiment.residual experiment ≡
      LegalExperiment.residual (LegalObservationReceipt.experiment observation)
    bidiReference : String
open LegalExperimentalBidi public

record AristotleLegalLoopWeld : Set₂ where
  constructor aristotleLegalLoopWeld
  field
    arithmeticProofSearchOwner : Aristotle.ActiveExperimentalProofSearchLoop
    legalLoopHasLiveHypotheses : Bool
    legalLoopHasLiveHypothesesIsTrue : legalLoopHasLiveHypotheses ≡ true
    legalLoopHasConsumerRelevantCollision : Bool
    legalLoopHasConsumerRelevantCollisionIsTrue : legalLoopHasConsumerRelevantCollision ≡ true
    legalLoopHasDiscriminatorExperiment : Bool
    legalLoopHasDiscriminatorExperimentIsTrue : legalLoopHasDiscriminatorExperiment ≡ true
    legalLoopHasSelectiveReopening : Bool
    legalLoopHasSelectiveReopeningIsTrue : legalLoopHasSelectiveReopening ≡ true
    legalAdjudicationIsLeanKernelVerification : Bool
    legalAdjudicationIsLeanKernelVerificationIsFalse : legalAdjudicationIsLeanKernelVerification ≡ false
    weldReference : String
open AristotleLegalLoopWeld public

canonicalAristotleLegalLoopWeld : AristotleLegalLoopWeld
canonicalAristotleLegalLoopWeld = aristotleLegalLoopWeld
  Aristotle.canonicalActiveExperimentalProofSearchLoop
  true refl true refl true refl true refl false refl
  "structural cross-pollination only: Aristotle's verified proof-search loop supplies the active-experiment pattern; legal proof graphs preserve evidentiary/procedural status and do not convert judicial fact-finding into Lean kernel truth"

record RetrievalCrossPollinationBoundary : Set where
  constructor retrievalCrossPollinationBoundary
  field
    fixedKeywordBlacklistIsCompleteLegalSearch : Bool
    fixedKeywordBlacklistIsCompleteLegalSearchIsFalse : fixedKeywordBlacklistIsCompleteLegalSearch ≡ false
    heuristicSimilarityMayProposeCandidate : Bool
    heuristicSimilarityMayProposeCandidateIsTrue : heuristicSimilarityMayProposeCandidate ≡ true
    heuristicCandidateMayBypassSourceResolution : Bool
    heuristicCandidateMayBypassSourceResolutionIsFalse : heuristicCandidateMayBypassSourceResolution ≡ false
    residualIndexedDiscriminatorMayChangeAfterObservation : Bool
    residualIndexedDiscriminatorMayChangeAfterObservationIsTrue : residualIndexedDiscriminatorMayChangeAfterObservation ≡ true

canonicalRetrievalCrossPollinationBoundary : RetrievalCrossPollinationBoundary
canonicalRetrievalCrossPollinationBoundary = retrievalCrossPollinationBoundary
  false refl true refl false refl true refl

data ExperimentArm : Set where
  conventionalRetrievalSummary sensibLawProofGraph : ExperimentArm

data EvaluationMetric : Set where
  propositionRecall provenancePreservation commonGroundRecovery residualControversyPrecision
  contradictionGapRecovery irrelevantMaterialInspected partyCorrectionBurden : EvaluationMetric

record ComparativeProtocol : Set where
  constructor comparativeProtocol
  field
    baseline : ExperimentArm
    treatment : ExperimentArm
    sameCorpus : Bool
    sameCorpusIsTrue : sameCorpus ≡ true
    metrics : List EvaluationMetric
    treatmentMaySilentlyDropWeakArgument : Bool
    treatmentMaySilentlyDropWeakArgumentIsFalse : treatmentMaySilentlyDropWeakArgument ≡ false
    protocolReference : String
open ComparativeProtocol public

canonicalLeeSensibLawProtocol : ComparativeProtocol
canonicalLeeSensibLawProtocol = comparativeProtocol
  conventionalRetrievalSummary sensibLawProofGraph true refl
  (propositionRecall ∷ provenancePreservation ∷ commonGroundRecovery ∷ residualControversyPrecision ∷ contradictionGapRecovery ∷ irrelevantMaterialInspected ∷ partyCorrectionBurden ∷ [])
  false refl
  "controlled same-corpus comparison: ordinary retrieval/summarisation versus provenance-preserving adversarial proof graph with active residual-indexed evidence search"

record LeeSensibLawAristotleCrossPollination : Set₂ where
  constructor leeSensibLawAristotleCrossPollination
  field
    legalBidiBoundary : Legal.AuthorityBoundary
    searchBoundary : Legal.SearchAdmissionBoundary
    leeBoundary : Legal.JusticeLeeSourceBoundary
    aristotleWeld : AristotleLegalLoopWeld
    retrievalBoundary : RetrievalCrossPollinationBoundary
    comparativeExperiment : ComparativeProtocol
    capstoneReference : String
open LeeSensibLawAristotleCrossPollination public

canonicalLeeSensibLawAristotleCrossPollination : LeeSensibLawAristotleCrossPollination
canonicalLeeSensibLawAristotleCrossPollination = leeSensibLawAristotleCrossPollination
  Legal.canonicalAuthorityBoundary
  Legal.canonicalSearchAdmissionBoundary
  Legal.canonicalJusticeLeeSourceBoundary
  canonicalAristotleLegalLoopWeld
  canonicalRetrievalCrossPollinationBoundary
  canonicalLeeSensibLawProtocol
  "Lee procedural redesign × SensibLaw proposition fibres × Aristotle/DASHI active experimental proof search: parse and preserve source-linked claims, align shared structure, type the residual controversy, compile procedural goals backward into discriminating evidence probes, update only affected fibres, and keep synthesis/support/admission/proof/adjudication distinct"
