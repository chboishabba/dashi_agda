module DASHI.Law.AustralianContractsLandscapeControllerRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Law.AustralianContractsLegalFollowExact as Contracts
import DASHI.Law.AustralianContractsLandscapeControllerExact as Controller

boundaryExists : Set
boundaryExists =
  Controller.AustralianContractsLandscapeControllerBoundary

boundaryPaid : boundaryExists
boundaryPaid =
  Controller.canonicalAustralianContractsLandscapeControllerBoundary

fourFrontiersRemainSeparated :
  Controller.fourFrontiersAreSeparated
    Controller.canonicalAustralianContractsLandscapeControllerBoundary
    ≡ true
fourFrontiersRemainSeparated =
  Controller.fourFrontiersAreSeparatedIsTrue
    Controller.canonicalAustralianContractsLandscapeControllerBoundary

boundedSeedRemainsBounded :
  Controller.boundedSeedOnly
    Controller.canonicalAustralianContractsLandscapeControllerBoundary
    ≡ true
boundedSeedRemainsBounded =
  Controller.boundedSeedOnlyIsTrue
    Controller.canonicalAustralianContractsLandscapeControllerBoundary

controllerStillCannotCreateCurrentLaw :
  Controller.controllerCreatesCurrentLawConclusion
    Controller.canonicalAustralianContractsLandscapeControllerBoundary
    ≡ false
controllerStillCannotCreateCurrentLaw =
  Controller.controllerCreatesCurrentLawConclusionIsFalse
    Controller.canonicalAustralianContractsLandscapeControllerBoundary

qldAsAtAxisStillCannotBeFlattened :
  NF.FactorsThrough
    Contracts.coarsePrivityProjection
    Contracts.operativePrivityRoute
  → ⊥
qldAsAtAxisStillCannotBeFlattened =
  Controller.qldTemporalAlternativeMustRemainRepresentable


sourceAcquisitionMayRemainResidual :
  Controller.sourceAcquisitionMayLeaveResiduals
    Controller.canonicalAustralianContractsLandscapeControllerBoundary
    ≡ true
sourceAcquisitionMayRemainResidual =
  Controller.sourceAcquisitionMayLeaveResidualsIsTrue
    Controller.canonicalAustralianContractsLandscapeControllerBoundary

missingSourceStillIsNotNegativeEvidence :
  Controller.missingSourceIsNegativeLegalEvidence
    Controller.canonicalAustralianContractsLandscapeControllerBoundary
    ≡ false
missingSourceStillIsNotNegativeEvidence =
  Controller.missingSourceIsNegativeLegalEvidenceIsFalse
    Controller.canonicalAustralianContractsLandscapeControllerBoundary

actAcquisitionStillDoesNotPaySection :
  Controller.actAcquisitionPaysSectionReceipt
    Controller.canonicalAustralianContractsLandscapeControllerBoundary
    ≡ false
actAcquisitionStillDoesNotPaySection =
  Controller.actAcquisitionPaysSectionReceiptIsFalse
    Controller.canonicalAustralianContractsLandscapeControllerBoundary

sourceAcquisitionStillDoesNotPayTreatment :
  Controller.sourceAcquisitionPaysTreatmentReview
    Controller.canonicalAustralianContractsLandscapeControllerBoundary
    ≡ false
sourceAcquisitionStillDoesNotPayTreatment =
  Controller.sourceAcquisitionPaysTreatmentReviewIsFalse
    Controller.canonicalAustralianContractsLandscapeControllerBoundary


qld2026SuccessorIsActiveSourceWork :
  Controller.activeAtAsAt Controller.qld2026ActiveSourceWork ≡ true
qld2026SuccessorIsActiveSourceWork = refl

qld2026PredecessorIsTemporalAlternative :
  Controller.activeAtAsAt Controller.qld2026TemporalAlternativeWork ≡ false
qld2026PredecessorIsTemporalAlternative = refl

qld2026FixtureStillDoesNotCreateCurrentLaw :
  Controller.createsCurrentLawConclusion
    Controller.qld2026TemporalSliceFixture
    ≡ false
qld2026FixtureStillDoesNotCreateCurrentLaw =
  Controller.createsCurrentLawConclusionIsFalse
    Controller.qld2026TemporalSliceFixture


missingSeedDoctrinesRemainContextResiduals :
  Controller.missingSeedDoctrinesBecomeContextResiduals
    Controller.canonicalAustralianContractsLandscapeControllerBoundary
    ≡ true
missingSeedDoctrinesRemainContextResiduals =
  Controller.missingSeedDoctrinesBecomeContextResidualsIsTrue
    Controller.canonicalAustralianContractsLandscapeControllerBoundary

constructionIsResearchContextWork :
  Controller.frontierKind Controller.constructionExpansionWork
    ≡ Controller.researchContextExpansion
constructionIsResearchContextWork = refl

consumerLawIsResearchContextWork :
  Controller.frontierKind Controller.consumerLawExpansionWork
    ≡ Controller.researchContextExpansion
consumerLawIsResearchContextWork = refl


adaptiveExpansionStillRecomputesFrontier :
  Controller.adaptiveExpansionRecomputesFrontier
    Controller.canonicalAustralianContractsLandscapeControllerBoundary
    ≡ true
adaptiveExpansionStillRecomputesFrontier =
  Controller.adaptiveExpansionRecomputesFrontierIsTrue
    Controller.canonicalAustralianContractsLandscapeControllerBoundary

adaptiveExpansionStillPreservesHistory :
  Controller.adaptiveExpansionPreservesOldSourceHistory
    Controller.canonicalAustralianContractsLandscapeControllerBoundary
    ≡ true
adaptiveExpansionStillPreservesHistory =
  Controller.adaptiveExpansionPreservesOldSourceHistoryIsTrue
    Controller.canonicalAustralianContractsLandscapeControllerBoundary

adaptiveExpansionStillDoesNotFreezeOldConclusions :
  Controller.adaptiveExpansionFreezesOldConclusions
    Controller.canonicalAustralianContractsLandscapeControllerBoundary
    ≡ false
adaptiveExpansionStillDoesNotFreezeOldConclusions =
  Controller.adaptiveExpansionFreezesOldConclusionsIsFalse
    Controller.canonicalAustralianContractsLandscapeControllerBoundary
