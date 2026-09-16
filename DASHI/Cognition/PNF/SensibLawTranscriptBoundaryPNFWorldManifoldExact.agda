module DASHI.Cognition.PNF.SensibLawTranscriptBoundaryPNFWorldManifoldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Cognition.PNF.SensibLawTranscriptBoundaryFibreClassifierExact as Legacy
import DASHI.Reasoning.SemanticCandidateResidualBidiExact as Residual
import DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact as Candidate
import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as EvidencePNF

------------------------------------------------------------------------
-- Transcript-boundary interpretation as a fibre/manifold, not one scalar.
--
-- The previous runtime emitted a useful local cut score and then five fibre
-- scores. Those are retained as observations, but they are not the semantic
-- carrier. Repo-native PNF reasoning keeps candidate alternatives live and
-- lets source/world constraints intersect/refine the residual fibre.
--
-- Runtime v2 also projects the parser dependency topology into the same PNF
-- fragment families already owned by SpacyDependencyToCandidateLogicalPNFExact:
-- actor/subject, patient/object, negation, modality, content clause, clause
-- attachment and coordination. The runtime counts are observations of those
-- structural families; they are not themselves resolved semantic formulae.
------------------------------------------------------------------------

data ManifoldCoordinate : Set where
  syntaxContinuity : ManifoldCoordinate
  pnfStructureCompatibility : ManifoldCoordinate
  pnfResidualCompatibility : ManifoldCoordinate
  attributionCompatibility : ManifoldCoordinate
  speakerContinuity : ManifoldCoordinate
  worldModelCompatibility : ManifoldCoordinate
  asrIntegrity : ManifoldCoordinate
  rhetoricalContinuity : ManifoldCoordinate

record CoordinateObservation : Set where
  constructor coordinateObservation
  field
    coordinate : ManifoldCoordinate
    valueReference : String
    evidenceReference : String
    producerReference : String

open CoordinateObservation public

------------------------------------------------------------------------
-- Sentence-level PNF topology retained separately from semantic resolution.
------------------------------------------------------------------------

record SentencePNFTopology : Set where
  constructor sentencePNFTopology
  field
    subjectCrossingCount : Nat
    objectCrossingCount : Nat
    clauseCrossingCount : Nat
    coordinationCrossingCount : Nat
    negationSideShift : Bool
    modalitySideShift : Bool
    parserObservationReference : String

open SentencePNFTopology public

record PNFTopologyInterpretationBoundary : Set where
  constructor pnfTopologyInterpretationBoundary
  field
    subjectCrossingProvesActorChange : Bool
    clauseCrossingChoosesDiscourseRole : Bool
    negationShiftDeterminesScope : Bool
    modalityShiftDeterminesSpeaker : Bool
    topologyMaySupportCandidateFibre : Bool

canonicalPNFTopologyInterpretationBoundary : PNFTopologyInterpretationBoundary
canonicalPNFTopologyInterpretationBoundary =
  pnfTopologyInterpretationBoundary false false false false true

record BoundaryWorldPoint : Set where
  constructor boundaryWorldPoint
  field
    fibreKind : Legacy.BoundaryFibreKind
    coordinates : List CoordinateObservation
    sentenceTopology : SentencePNFTopology
    pnfCandidateReference : String
    sentenceReference : String
    worldConstraintReference : String
    sourceConstraintReference : String
    residualReference : String

open BoundaryWorldPoint public

record BoundaryManifold : Set where
  constructor boundaryManifold
  field
    sourceSha256 : String
    sentenceReference : String
    splitReference : String
    points : List BoundaryWorldPoint
    paretoFrontReference : String
    retainedResidualReference : String
    legacyCutReceiptReference : String
    manifoldSchema : String

open BoundaryManifold public

------------------------------------------------------------------------
-- Ternary admission is consumer-relative and separate from coordinates.
------------------------------------------------------------------------

data ManifoldDisposition : Set where
  rejectPoint : ManifoldDisposition
  suspendPoint : ManifoldDisposition
  admitPoint : ManifoldDisposition

record ManifoldReview : Set where
  constructor manifoldReview
  field
    pointReference : String
    consumerReference : String
    disposition : ManifoldDisposition
    evidenceReference : String
    sourceOrWorldAuthorityReference : String
    alternativesStillOpenReference : String

open ManifoldReview public

------------------------------------------------------------------------
-- PNF/world intersection receipt.
--
-- This mirrors SemanticCandidateResidualBidiExact: a source/world constraint
-- may shrink a live semantic fibre, but does not manufacture truth.
------------------------------------------------------------------------

record BoundaryPNFWorldConstraintReceipt : Set where
  constructor boundaryPNFWorldConstraintReceipt
  field
    parserCandidateFibreReference : String
    evidencePNFAssertionReference : String
    worldIdentityReference : String
    sourceAuthorityReference : String
    scopeReference : String
    alternativesStillOpenReference : String

open BoundaryPNFWorldConstraintReceipt public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ScalarCutScoreDeterminesFibre : Set where
scalarCutScoreDoesNotDetermineFibre : ScalarCutScoreDeterminesFibre → ⊥
scalarCutScoreDoesNotDetermineFibre ()

data TopLegacyFibreDeletesResidual : Set where
topLegacyFibreDoesNotDeleteResidual : TopLegacyFibreDeletesResidual → ⊥
topLegacyFibreDoesNotDeleteResidual ()

data ParetoFrontDeterminesWorldTruth : Set where
paretoFrontDoesNotDetermineWorldTruth : ParetoFrontDeterminesWorldTruth → ⊥
paretoFrontDoesNotDetermineWorldTruth ()

data SpeakerCompatibilityDeterminesIdentity : Set where
speakerCompatibilityDoesNotDetermineIdentity : SpeakerCompatibilityDeterminesIdentity → ⊥
speakerCompatibilityDoesNotDetermineIdentity ()

data LowPNFResidualProvesCorrectSegmentation : Set where
lowPNFResidualDoesNotProveCorrectSegmentation : LowPNFResidualProvesCorrectSegmentation → ⊥
lowPNFResidualDoesNotProveCorrectSegmentation ()

data DependencyTopologyDeterminesSemanticFormula : Set where
dependencyTopologyDoesNotDetermineSemanticFormula : DependencyTopologyDeterminesSemanticFormula → ⊥
dependencyTopologyDoesNotDetermineSemanticFormula ()

------------------------------------------------------------------------
-- Existing PNF/residual owners are the semantic anchors.
------------------------------------------------------------------------

semanticResidualBoundaryAnchor : Residual.SemanticResidualBoundary
semanticResidualBoundaryAnchor = Residual.canonicalSemanticResidualBoundary

spacySemanticBoundaryAnchor : Candidate.SpacySemanticBoundary
spacySemanticBoundaryAnchor = Candidate.canonicalSpacySemanticBoundary

evidencePNFBoundaryAnchor : EvidencePNF.PredicateNormalFormBoundary
evidencePNFBoundaryAnchor = EvidencePNF.canonicalPredicateNormalFormBoundary

record PNFWorldManifoldBoundary : Set where
  constructor pnfWorldManifoldBoundary
  field
    legacyScalarRetainedAsObservation : Bool
    parserTopologyRetainedAsObservation : Bool
    fibrePointsRemainSimultaneouslyLive : Bool
    sourceWorldConstraintsMayRefineFibre : Bool
    sourceWorldConstraintsCreateTruth : Bool
    residualSurvivesSelection : Bool
    admissionIsConsumerRelative : Bool
    speakerIdentityRemainsIndependent : Bool
    fullEvidencePNFResolutionStillSeparate : Bool

canonicalPNFWorldManifoldBoundary : PNFWorldManifoldBoundary
canonicalPNFWorldManifoldBoundary =
  pnfWorldManifoldBoundary true true true true false true true true true

------------------------------------------------------------------------
-- ABC regression references.
------------------------------------------------------------------------

sentence45ManifoldExpectation : String
sentence45ManifoldExpectation =
  "45:7: speaker point should lie on/near the live frontier, while clause/coordination topology, ASR and rhetorical alternatives remain explicit residual coordinates"

sentence117ManifoldExpectation : String
sentence117ManifoldExpectation =
  "117:32: quote/nesting/rhetorical points should remain jointly visible; believes/content-clause structure must not be collapsed to a speaker scalar"

sentence118ManifoldExpectation : String
sentence118ManifoldExpectation =
  "118: according-to region: attribution/nesting point should survive source/world constraint intersection while speaker identity remains independently sourced"
