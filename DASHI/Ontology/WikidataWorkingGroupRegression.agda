module DASHI.Ontology.WikidataWorkingGroupRegression where

open import Agda.Builtin.Bool using (Bool; false; true)
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
import DASHI.Ontology.DependentDefinitionFibreExact as Dependent
import DASHI.Core.ActiveObligationEvidenceFibreExact as Active
import DASHI.Core.IndexedInterpretationMorphismExact as Indexed
import DASHI.Core.EpistemicInquiryGovernance as CoreGovernance
import DASHI.Core.MinimalSufficientResidual as Minimal
import DASHI.Core.ReopenableProjectionComposition as Reopenable
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.TernaryNativeMinimalityExact as Native
import DASHI.Foundations.BalancedTernaryAntipodalOrbitExact as Orbit
import DASHI.Foundations.BalancedTernaryNineZeroFibreCountExact as ZeroCount
import DASHI.Foundations.Base369InteractionAntipodalFibreExact as Interaction
import DASHI.Foundations.Base369NineCoordinateAggregateBridgeExact as NineBridge
import DASHI.Cognition.PNF.BinaryBalancedTernaryAggregateLossExact as BinaryAggregate

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

------------------------------------------------------------------------
-- Native ternary / Boolean consumer boundary.
------------------------------------------------------------------------

oneBitCannotInjectivelyEncodeSignedCentre :
  (observer : SSP.SSPTrit → Bool) → Native.Injective observer → ⊥
oneBitCannotInjectivelyEncodeSignedCentre = Native.noOneBitInjection

positiveOnlyBooleanCollapsesInverseAndCentre :
  Native.positiveOnly SSP.sspNegOne ≡ Native.positiveOnly SSP.sspZero
positiveOnlyBooleanCollapsesInverseAndCentre =
  Native.positiveOnlyCollapsesNegativeAndCentre

positiveOnlyBooleanHasNoExactReconstruction :
  Native.ExactPositiveOnlyReconstruction → ⊥
positiveOnlyBooleanHasNoExactReconstruction = Native.noExactPositiveOnlyReconstruction

binaryCanSimulateWithoutChangingNativeGeometry :
  (x : SSP.SSPTrit) →
  Native.decodeBinary (Native.encodeBinary x) ≡ x
binaryCanSimulateWithoutChangingNativeGeometry = Native.binarySimulationRoundTrip

binarySimulationPreservesStrictAntipode :
  (x : SSP.SSPTrit) →
  Native.encodeBinary (Orbit.strictAntipode x)
  ≡ Native.binaryAntipode (Native.encodeBinary x)
binarySimulationPreservesStrictAntipode = Native.binarySimulationPreservesAntipode

------------------------------------------------------------------------
-- Repo-native 27^3 = 3^9 variable-rank residual geometry.
------------------------------------------------------------------------

repoNativeTwentySevenCubedIs19683 :
  Interaction.fineInteractionStateCount ≡ 19683
repoNativeTwentySevenCubedIs19683 = Interaction.fineInteractionStateCountIs19683

blockwiseAntipodalBaseIsFourteenCubed :
  Interaction.blockOrientationClassCount ≡ 2744
blockwiseAntipodalBaseIsFourteenCubed = Interaction.blockOrientationClassCountIs2744

allThreeNoncentralBlocksCarryEightOrientations :
  Interaction.allThreeNoncentralOrientationFibreSize ≡ 8
allThreeNoncentralBlocksCarryEightOrientations =
  Interaction.allThreeNoncentralOrientationFibreSizeIsEight

aggregateZeroFibreIsNontrivialAndCountedExactly :
  ZeroCount.aggregateZeroFibreCount ≡ 3139
aggregateZeroFibreIsNontrivialAndCountedExactly = ZeroCount.aggregateZeroFibreCountIs3139

threeSemanticBlocksAreExactlyNineLabelledTrits :
  Interaction.fineInteractionStateCount ≡ ZeroCount.sumList ZeroCount.row9
threeSemanticBlocksAreExactlyNineLabelledTrits = NineBridge.base369FineCountMatchesCoefficientRowTotal

binaryCountErasesDirectedDisagreement :
  BinaryAggregate.acceptCount
    (BinaryAggregate.binaryProjectPositiveOnly BinaryAggregate.forwardDisagreement)
  ≡ BinaryAggregate.acceptCount
    (BinaryAggregate.binaryProjectPositiveOnly BinaryAggregate.reverseDisagreement)
binaryCountErasesDirectedDisagreement = BinaryAggregate.aggregateErasesDisagreementDirection

------------------------------------------------------------------------
-- Fibred positive definitions remove invalid combinations from the type.
------------------------------------------------------------------------

flatPositiveProductAdmitsInvalidToyotaFiesta :
  Dependent.validFlat Dependent.flatToyotaFiestaExists ≡ false
flatPositiveProductAdmitsInvalidToyotaFiesta =
  Dependent.flatToyotaFiestaNeedsPostHocRejection

dependentVehicleCarrierAlwaysFlattensValid :
  (vehicle : Dependent.Vehicle) →
  Dependent.validFlat (Dependent.flattenVehicle vehicle) ≡ true
dependentVehicleCarrierAlwaysFlattensValid =
  Dependent.dependentCarrierOnlyFlattensToValidCombinations

retainedContextCanBeLocallyNonDeterminant :
  Dependent.retainedInContext Dependent.relevantButNonDeterminant ≡ true
retainedContextCanBeLocallyNonDeterminant = Dependent.relevantBundleIsRetained
