module DASHI.Empirical.DarkDimensionSameKeyPredictionDebtExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SourceAcquisitionGeometryExact as Acquisition
import DASHI.Interop.SourceDiligenceProofSearchBridgeExact as SourceSearch
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search
import DASHI.Empirical.DarkDimensionBedroyaBackgroundReconstructionExact as BedroyaBackground
import DASHI.Empirical.DarkDimensionBedroyaBackgroundInputContractExact as BedroyaInput
import DASHI.Empirical.DarkDimensionBedroyaSameObjectAcquisitionExact as BedroyaAcquisition
import DASHI.Empirical.DarkDimensionCrossDomainEvidenceWeldExact as CrossDomain
import DASHI.Empirical.DarkDimensionDAOSameKeyExtractionRecipeExact as DAORecipe
import DASHI.Empirical.DarkDimensionDAOSameKeyReconstructionRunExact as DAORun
import DASHI.Empirical.DarkDimensionResidualDebtRoutingExact as DebtRouting
import DASHI.Empirical.DarkDimensionSharedBAOObservableExact as SharedBAO
import DASHI.Empirical.DarkDimensionSharedBAOObservationKeyExact as ObservationKey

daoIndependentTargetSource : Source.AttributedSource
daoIndependentTargetSource =
  Source.mkNoDOISource
    "Mathias Garny; Florian Niedermann; Martin S. Sloth"
    "Dark Acoustic Oscillations and the Hubble Tension"
    "arXiv:2602.23895"
    "2026"
    "https://arxiv.org/abs/2602.23895"
    Source.academicArticleSource
    "source for an inference independent of large-scale-structure data giving a concrete DAO sound-horizon/amplitude target; independence from LSS does not imply chronological preregistration before DESI DR2"
    Source.publicAttribution

daoDRMDClassSource : Source.AttributedSource
daoDRMDClassSource =
  Source.mkNoDOISource
    "NEDE-Cosmo collaboration repository"
    "DRMD-CLASS"
    "GitHub public source repository"
    "2026"
    "https://github.com/NEDE-Cosmo/DRMD-CLASS"
    Source.practitionerSource
    "public CLASS implementation of the Dark Radiation-Matter Decoupling model; revision/config provenance and same-key extraction recipe are pinned below, but no DASHI execution receipt or BAO prediction is imported by source existence"
    Source.publicAttribution

darkDimensionModelSource : Source.AttributedSource
darkDimensionModelSource =
  Source.mkNoDOISource
    "Alek Bedroya; Georges Obied; Cumrun Vafa; David H. Wu"
    "Evolving Dark Sector and the Dark Dimension Scenario"
    "arXiv:2507.03090 / Physical Review D accepted 2026"
    "2026"
    "https://arxiv.org/abs/2507.03090"
    Source.academicArticleSource
    "source for the evolving Dark-Dimension equations and DESI DR2 retrospective fit; no first-party public executable implementation is admitted by this tranche"
    Source.publicAttribution

record PublicExecutionSurface : Set where
  constructor publicExecutionSurface
  field
    repositoryLabel : String
    revision : String
    primaryInputSurface : String
    inferenceConfigSurface : String
    baoDragHorizonSurface : String
    modelSpecificDarkHorizonSurface : String
    sameKeyExtractionRecipeOwner : String
    executableRevisionPinned : Bool
    executionConfigSurfaceLocated : Bool
    executedByDASHI : Bool

open PublicExecutionSurface public

daoDRMDExecutionSurface : PublicExecutionSurface
daoDRMDExecutionSurface =
  publicExecutionSurface
    "NEDE-Cosmo/DRMD-CLASS"
    "aa2b61a0f1cf246672cdbd4634a4797d4cc654f9"
    "input/DRMD.ini"
    "cobaya/"
    "rs_drag"
    "rs_d_drmd"
    "DASHI.Empirical.DarkDimensionDAOSameKeyExtractionRecipeExact"
    true true false

daoDRMDClassRevision : String
daoDRMDClassRevision = "aa2b61a0f1cf246672cdbd4634a4797d4cc654f9"

record SameKeyPredictionDerivationDebt : Set where
  constructor sameKeyPredictionDerivationDebt
  field
    sharedBAOObservableLocated : Bool
    sameDESIObservationKeyLocated : Bool
    daoExecutableModelLocated : Bool
    darkDimensionExecutableModelLocated : Bool
    daoExecutableRevisionPinned : Bool
    daoExecutionConfigSurfaceLocated : Bool
    daoExecutedByDASHI : Bool
    daoLargeScaleStructureIndependentTargetLocated : Bool
    daoTargetChronologicallyHeldOutBeforeDESIDR2 : Bool
    daoSameKeyBAOVectorDerived : Bool
    darkDimensionSameKeyBAOVectorDerived : Bool
    commonCovarianceSurfaceAssembled : Bool
    analysisChoicesFrozenBeforeFutureData : Bool
    sameKeyLikelihoodLocked : Bool
    debtClosed : Bool

open SameKeyPredictionDerivationDebt public

canonicalSameKeyPredictionDerivationDebt : SameKeyPredictionDerivationDebt
canonicalSameKeyPredictionDerivationDebt =
  sameKeyPredictionDerivationDebt
    true true true false true true false true false false false false false false false

daoExecutableRevisionPinPaid :
  daoExecutableRevisionPinned canonicalSameKeyPredictionDerivationDebt ≡ true
daoExecutableRevisionPinPaid = refl

daoExecutionConfigSurfacePaid :
  daoExecutionConfigSurfaceLocated canonicalSameKeyPredictionDerivationDebt ≡ true
daoExecutionConfigSurfacePaid = refl

daoExecutionStillNotRun :
  daoExecutedByDASHI canonicalSameKeyPredictionDerivationDebt ≡ false
daoExecutionStillNotRun = refl

daoReconstructionRuntimeRequestLocated :
  DAORun.upstreamRevisionPinned DAORun.canonicalDAOSameKeyReconstructionRunStatus ≡ true
daoReconstructionRuntimeRequestLocated = refl

daoReconstructionRuntimeReceiptStillOpen :
  DAORun.executionReceiptPresent DAORun.canonicalDAOSameKeyReconstructionRunStatus ≡ false
daoReconstructionRuntimeReceiptStillOpen = DAORun.reconstructionRunStillOpen

daoReconstructionVectorStillOpen :
  DAORun.numericalVectorPresent DAORun.canonicalDAOSameKeyReconstructionRunStatus ≡ false
daoReconstructionVectorStillOpen = DAORun.numericalVectorStillOpen

darkDimensionExecutableStillOpen :
  darkDimensionExecutableModelLocated canonicalSameKeyPredictionDerivationDebt ≡ false
darkDimensionExecutableStillOpen = refl

darkDimensionBackgroundReconstructionStillOpen :
  BedroyaBackground.sixKeyBAOVectorDerived
    BedroyaBackground.canonicalBedroyaBackgroundReconstructionStatus
  ≡ false
darkDimensionBackgroundReconstructionStillOpen = BedroyaBackground.sixKeyVectorStillOpen

bedroyaSameObjectAcquisitionStillOpen :
  Acquisition.fullTextAcquired BedroyaAcquisition.bedroya2026SameObjectTarget ≡ false
bedroyaSameObjectAcquisitionStillOpen = BedroyaAcquisition.childSameObjectStillUnacquired

bedroyaPostIdentitySupportStageDefined :
  SourceSearch.producer BedroyaAcquisition.bedroyaPostIdentitySupportDemand
  ≡ Search.propositionSourceProducer
bedroyaPostIdentitySupportStageDefined = BedroyaAcquisition.postIdentitySupportStillRequiresSourcePayment

bedroyaBackgroundInputManifestStillOpen :
  BedroyaInput.completeBackgroundInputManifestLocated
    BedroyaInput.canonicalBedroyaBackgroundInputStatus
  ≡ false
bedroyaBackgroundInputManifestStillOpen = BedroyaInput.completeBackgroundInputStillOpen

bedroyaSameFitRDragStillOpen :
  BedroyaInput.exactRDragSameFitLocated
    BedroyaInput.canonicalBedroyaBackgroundInputStatus
  ≡ false
bedroyaSameFitRDragStillOpen = BedroyaInput.exactRDragSameFitStillOpen

daoExtractionRecipeLocatedButExecutionStillOpen :
  DAORecipe.recipeExecuted DAORecipe.daoPinnedExtractionRecipe ≡ false
daoExtractionRecipeLocatedButExecutionStillOpen = DAORecipe.recipeExecutionStillOpen

daoRecipeStillDoesNotPaySameKeyVector :
  DAORecipe.sameKeyBAOVectorDerived DAORecipe.daoPinnedExtractionRecipe ≡ false
daoRecipeStillDoesNotPaySameKeyVector = DAORecipe.sameKeyBAOVectorStillNotDerived

crossDomainEvidenceWeldStillBlocksPromotion :
  CrossDomain.ReconstructionReceiptEqualsHeldOutPrediction → ⊥
crossDomainEvidenceWeldStillBlocksPromotion = CrossDomain.reconstructionReceiptDoesNotBecomeHeldOutPrediction

residualDebtClassesRemainDistinct :
  DebtRouting.DAOExecutionPaysBedroyaAcquisitionGap → ⊥
residualDebtClassesRemainDistinct = DebtRouting.residualKindsRemainDistinct

sameKeyPredictionDebtStillOpen :
  debtClosed canonicalSameKeyPredictionDerivationDebt ≡ false
sameKeyPredictionDebtStillOpen = refl

sharedBAONumericalSeparationStillBlocked :
  SharedBAO.sharedObservableNumericalSeparationLocked SharedBAO.canonicalSharedBAOStatus ≡ false
sharedBAONumericalSeparationStillBlocked = SharedBAO.sharedObservableNumericalPredictionsStillOpen

data LargeScaleStructureIndependenceImpliesChronologicalHoldout : Set where

largeScaleStructureIndependentDoesNotMeanChronologicallyHeldOut :
  LargeScaleStructureIndependenceImpliesChronologicalHoldout → ⊥
largeScaleStructureIndependentDoesNotMeanChronologicallyHeldOut ()

record SameKeyPredictionRequest : Set where
  constructor sameKeyPredictionRequest
  field
    key : ObservationKey.SharedBAOObservationKey
    darkDimensionSource : Source.AttributedSource
    daoSource : Source.AttributedSource
    darkDimensionPredictionPresent : Bool
    daoPredictionPresent : Bool
    comparisonLocked : Bool

open SameKeyPredictionRequest public

mkOpenPredictionRequest : ObservationKey.SharedBAOObservationKey → SameKeyPredictionRequest
mkOpenPredictionRequest key =
  sameKeyPredictionRequest key darkDimensionModelSource daoIndependentTargetSource false false false

lrg1TransversePredictionRequest : SameKeyPredictionRequest
lrg1TransversePredictionRequest = mkOpenPredictionRequest ObservationKey.lrg1TransverseKey

lrg1RadialPredictionRequest : SameKeyPredictionRequest
lrg1RadialPredictionRequest = mkOpenPredictionRequest ObservationKey.lrg1RadialKey

lrg2TransversePredictionRequest : SameKeyPredictionRequest
lrg2TransversePredictionRequest = mkOpenPredictionRequest ObservationKey.lrg2TransverseKey

lrg2RadialPredictionRequest : SameKeyPredictionRequest
lrg2RadialPredictionRequest = mkOpenPredictionRequest ObservationKey.lrg2RadialKey

lrg3Elg1TransversePredictionRequest : SameKeyPredictionRequest
lrg3Elg1TransversePredictionRequest = mkOpenPredictionRequest ObservationKey.lrg3Elg1TransverseKey

lrg3Elg1RadialPredictionRequest : SameKeyPredictionRequest
lrg3Elg1RadialPredictionRequest = mkOpenPredictionRequest ObservationKey.lrg3Elg1RadialKey

elg2TransversePredictionRequest : SameKeyPredictionRequest
elg2TransversePredictionRequest = mkOpenPredictionRequest ObservationKey.elg2TransverseKey

elg2RadialPredictionRequest : SameKeyPredictionRequest
elg2RadialPredictionRequest = mkOpenPredictionRequest ObservationKey.elg2RadialKey

qsoTransversePredictionRequest : SameKeyPredictionRequest
qsoTransversePredictionRequest = mkOpenPredictionRequest ObservationKey.qsoTransverseKey

qsoRadialPredictionRequest : SameKeyPredictionRequest
qsoRadialPredictionRequest = mkOpenPredictionRequest ObservationKey.qsoRadialKey

lyaTransversePredictionRequest : SameKeyPredictionRequest
lyaTransversePredictionRequest = mkOpenPredictionRequest ObservationKey.lyaTransverseKey

lyaRadialPredictionRequest : SameKeyPredictionRequest
lyaRadialPredictionRequest = mkOpenPredictionRequest ObservationKey.lyaRadialKey

bedroyaArXiv : String
bedroyaArXiv = "2507.03090"

daoIndependentTargetArXiv : String
daoIndependentTargetArXiv = "2602.23895"

daoExecutableRepository : String
daoExecutableRepository = "DRMD-CLASS"
