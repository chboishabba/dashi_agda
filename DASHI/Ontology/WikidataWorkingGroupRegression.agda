module DASHI.Ontology.WikidataWorkingGroupRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Data.Product using (proj₁)

import DASHI.Algebra.DisagreementFourViewBoundary as Four
import DASHI.Interop.WikidataDerivationSupportSquareExact as Square
import DASHI.Ontology.CrossOntologyContradictionAttributionExact as Attribution
import DASHI.Ontology.DisjointUnionLatticeJMDBridgeExact as Dun
import DASHI.Ontology.InferenceLanguageIndexedAlignmentSafetyExact as Language
import DASHI.Ontology.BFOContinuantOccurrentWikidataAttributionExact as BFO
import DASHI.Ontology.RdfViewInformationOrderJMDBridgeExact as RDF
import DASHI.Ontology.WikidataInterpretiveDiagnosticExact as Interpretive
import DASHI.Ontology.WikidataDiagnosticGovernanceExact as Governance
import DASHI.Ontology.WikidataRepairReopeningExact as Reopen
import DASHI.Ontology.WikidataCheckerResultAttributionExact as Checker
import DASHI.Core.ActiveObligationEvidenceFibreExact as Active
import DASHI.Core.IndexedInterpretationMorphismExact as Indexed
import DASHI.Core.EpistemicInquiryGovernance as CoreGovernance
import DASHI.Core.MinimalSufficientResidual as Minimal
import DASHI.Core.ReopenableProjectionComposition as Reopenable

conflictAndIgnoranceRemainDistinctBeforeTritCollapse :
  Square.conflictSquare ≡ Square.ignoranceSquare → ⊥
conflictAndIgnoranceRemainDistinctBeforeTritCollapse = Square.conflictIsNotIgnorance

alignmentLocalStressRetainsConflict :
  Attribution.pooledAttributionSquare Attribution.alignmentLocalStressFibre
  ≡ Four.assess true true
alignmentLocalStressRetainsConflict = Attribution.alignmentLocalStressPoolsToConflict

fullDisjointUnionNeedsKnownCoverage :
  Dun.finiteDunOk Dun.nonExhaustiveKnownUnion ≡ false
fullDisjointUnionNeedsKnownCoverage = Dun.unionExhaustivityFailureFails

pairwiseDisjointnessAloneIsInsufficient :
  Dun.pairwiseKnownDisjoint Dun.nonExhaustiveKnownUnion ≡ true
pairwiseDisjointnessAloneIsInsufficient = Dun.pairwiseDisjointAloneDoesNotEstablishDun

subclassSafetyDoesNotPromoteToDisjointnessSafety :
  Language.safeFor Language.subclassOnlyAlignment Language.disjointnessLanguage
  ≡ false
subclassSafetyDoesNotPromoteToDisjointnessSafety = Language.subclassOnlyIsNotSafeForDisjointness

literalBfoControlDoesNotManufactureDisjointnessTransport :
  Language.safeFor BFO.bfoMappingSubclassProfile Language.disjointnessLanguage
  ≡ false
literalBfoControlDoesNotManufactureDisjointnessTransport =
  BFO.bfoMappingNotYetLicensedForDisjointnessLanguage

reifiedRdfStrictlyRetainsRankInformation :
  RDF.directView RDF.normalRankStatement ≡ RDF.directView RDF.preferredRankStatement
reifiedRdfStrictlyRetainsRankInformation = RDF.sameDirectDifferentReification

directRdfCannotExactlyReconstructBothReifiedStates :
  RDF.ExactDirectReconstruction → ⊥
directRdfCannotExactlyReconstructBothReifiedStates = RDF.noExactDirectReconstruction

checkerFailureDoesNotIdentifyItsLayer :
  Checker.ExactCheckerOriginDecoder → ⊥
checkerFailureDoesNotIdentifyItsLayer = Checker.noExactCheckerOriginDecoder

missingEvidenceAndTargetFailureShareCheckerBit :
  Checker.checkerBit Checker.targetGraphFailure
  ≡ Checker.checkerBit Checker.missingRequiredEvidence
missingEvidenceAndTargetFailureShareCheckerBit = Checker.targetAndMissingShareFailBit

formalCheckerDoesNotSelfAuthoriseRevision :
  Governance.DiagnosticAuthorises Governance.formalChecker
    CoreGovernance.revisionCoordinate → ⊥
formalCheckerDoesNotSelfAuthoriseRevision = Governance.formalCheckerCannotSelfAuthoriseRevision

strongerInferenceLanguageActivatesMissingObligation :
  Active.ResolvedFor Active.demoFamily Active.disjointnessTransport Active.disjointnessQuery → ⊥
strongerInferenceLanguageActivatesMissingObligation = Active.disjointnessLanguageNotResolved

surfaceEqualityDoesNotTransferAcrossInterpretationIndices :
  Indexed.OutputEqualityTransfersAcrossIndices Indexed.demoSystem → ⊥
surfaceEqualityDoesNotTransferAcrossInterpretationIndices = Indexed.surfaceEqualityDoesNotSupplyCrossIndexLicence

repairRecommendationRetainsSourceResidual :
  (state : Minimal.FineBitState) →
  proj₁ (proj₁ (proj₁
    (Reopenable.receipt Reopen.fullOntologyDiagnosticRepairPipeline state)))
  ≡ Minimal.hiddenSecondBit state
repairRecommendationRetainsSourceResidual = Reopen.sourceResidualSurvivesRepairPipeline

interpretiveOutputIsCandidateOnly :
  Interpretive.outputCandidateOnly Interpretive.canonicalAlignmentStressDiagnostic ≡ true
interpretiveOutputIsCandidateOnly =
  Interpretive.outputCandidateOnlyIsTrue Interpretive.canonicalAlignmentStressDiagnostic
