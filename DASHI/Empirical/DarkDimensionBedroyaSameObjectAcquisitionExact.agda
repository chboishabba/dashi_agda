module DASHI.Empirical.DarkDimensionBedroyaSameObjectAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.SourceAcquisitionGeometryExact as Acquisition
import DASHI.Core.BidiResidualApproximationExact as Bidi
import DASHI.Interop.SourceDiligenceProofSearchBridgeExact as SourceSearch
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search
import DASHI.Empirical.DarkDimensionResidualDebtRoutingExact as DebtRouting
import DASHI.Empirical.DarkDimensionFadingDMParentLineageExact as ParentLineage

------------------------------------------------------------------------
-- BEDROYA 2026 SAME-OBJECT ACQUISITION ADAPTER
------------------------------------------------------------------------

bedroya2026SameObjectTarget : Acquisition.SourceAcquisitionTarget
bedroya2026SameObjectTarget =
  Acquisition.sourceAcquisitionTarget
    "2026 Bedroya-Obied-Vafa-Wu same-fit parameter manifest and normalization map"
    "DESI+CMB+Pantheon+ negative-c best-fit chain/config or machine-readable manifest"
    Acquisition.directDigitalArchive
    Acquisition.publisherBackfile
    false false false

bedroyaIdentitySearchDemand : SourceSearch.SourceDiligenceSearchDemand
bedroyaIdentitySearchDemand = DebtRouting.bedroyaManifestIdentitySearchDemand

data CandidateCustody : Set where
  childSpecificManifest : CandidateCustody
  parentOnlyImplementation : CandidateCustody
  ancestorParameterizationOnly : CandidateCustody

data CandidateAdmissible (candidate : CandidateCustody) : Set where
  candidate-admissible : CandidateAdmissible candidate

candidateCustodyPrior : Bidi.ResidualFibre CandidateCustody
candidateCustodyPrior candidate = CandidateAdmissible candidate

data SameObjectIdentityMeasurement : Set where
  exactChildSameObject : SameObjectIdentityMeasurement
  lineageOnlyEvidence : SameObjectIdentityMeasurement

sameObjectIdentityMeasurement : CandidateCustody → SameObjectIdentityMeasurement
sameObjectIdentityMeasurement childSpecificManifest = exactChildSameObject
sameObjectIdentityMeasurement parentOnlyImplementation = lineageOnlyEvidence
sameObjectIdentityMeasurement ancestorParameterizationOnly = lineageOnlyEvidence

bedroyaSameObjectSearchExperiment :
  Bidi.PartialInformationExperiment CandidateCustody SameObjectIdentityMeasurement
bedroyaSameObjectSearchExperiment =
  Bidi.partialInformationExperiment
    candidateCustodyPrior
    sameObjectIdentityMeasurement
    "locate child-specific same-fit 2026 manifest/normalization custody or retain lineage-only result"
    "same-object calibration requires explicit child linkage; author/model lineage alone is insufficient"
    "search useful even without exact closure: an observed result can shrink the custody fibre"
    false
    "no acquisition result has been promoted; source-diligence and same-object checks remain downstream"

exactChildObservationWouldRefineCustody :
  Bidi.FibreRefines
    (Bidi.MeasuredFibre candidateCustodyPrior sameObjectIdentityMeasurement exactChildSameObject)
    candidateCustodyPrior
exactChildObservationWouldRefineCustody =
  Bidi.partialMeasurementIsUsefulWithoutExactClosure
    bedroyaSameObjectSearchExperiment exactChildSameObject

lineageOnlyObservationWouldRefineCustody :
  Bidi.FibreRefines
    (Bidi.MeasuredFibre candidateCustodyPrior sameObjectIdentityMeasurement lineageOnlyEvidence)
    candidateCustodyPrior
lineageOnlyObservationWouldRefineCustody =
  Bidi.partialMeasurementIsUsefulWithoutExactClosure
    bedroyaSameObjectSearchExperiment lineageOnlyEvidence

parentOnlyLineageWitness :
  Bidi.MeasuredFibre candidateCustodyPrior sameObjectIdentityMeasurement lineageOnlyEvidence parentOnlyImplementation
parentOnlyLineageWitness = candidate-admissible , refl

ancestorLineageWitness :
  Bidi.MeasuredFibre candidateCustodyPrior sameObjectIdentityMeasurement lineageOnlyEvidence ancestorParameterizationOnly
ancestorLineageWitness = candidate-admissible , refl

parentOnlyNotAncestor : parentOnlyImplementation ≡ ancestorParameterizationOnly → ⊥
parentOnlyNotAncestor ()

lineageOnlyObservationDoesNotIdentifyCustody :
  Bidi.PointIdentifies
    (Bidi.MeasuredFibre candidateCustodyPrior sameObjectIdentityMeasurement lineageOnlyEvidence)
    (λ candidate → candidate) → ⊥
lineageOnlyObservationDoesNotIdentifyCustody identifies =
  parentOnlyNotAncestor
    (identifies parentOnlyImplementation ancestorParameterizationOnly
      parentOnlyLineageWitness ancestorLineageWitness)

------------------------------------------------------------------------
-- Attribution ladder after a hypothetical exact-child location.
------------------------------------------------------------------------

bedroyaPostIdentitySupportGap : SourceSearch.SourceDiligenceGap
bedroyaPostIdentitySupportGap = SourceSearch.propositionSupportUnresolved

bedroyaPostIdentitySupportDemand : SourceSearch.SourceDiligenceSearchDemand
bedroyaPostIdentitySupportDemand =
  SourceSearch.source-diligence-search-demand
    "2026 child manifest support for the exact standard tuple and normalization map"
    bedroyaPostIdentitySupportGap
    Search.propositionSourceProducer
    refl
    "DASHI.Empirical.DarkDimensionBedroyaBackgroundReconstructionExact"
    "bedroya-post-identity-proposition-support-demand"

postIdentitySupportStillRequiresSourcePayment :
  SourceSearch.producer bedroyaPostIdentitySupportDemand
  ≡ Search.propositionSourceProducer
postIdentitySupportStillRequiresSourcePayment = refl

bedroyaSampledDensityMappingDemand : SourceSearch.SourceDiligenceSearchDemand
bedroyaSampledDensityMappingDemand =
  SourceSearch.source-diligence-search-demand
    "rho_DM^0 to sampled Omega_FDM h^2 correspondence"
    SourceSearch.propositionSupportUnresolved
    Search.propositionSourceProducer
    refl
    "DASHI.Empirical.DarkDimensionBedroyaBackgroundReconstructionExact"
    "bedroya-rhoDM0-to-sampled-OmegaFDM-demand"

bedroyaV0NormalizationDemand : SourceSearch.SourceDiligenceSearchDemand
bedroyaV0NormalizationDemand =
  SourceSearch.source-diligence-search-demand
    "V0 to fitted dark-energy normalization correspondence"
    SourceSearch.propositionSupportUnresolved
    Search.propositionSourceProducer
    refl
    "DASHI.Empirical.DarkDimensionBedroyaBackgroundReconstructionExact"
    "bedroya-V0-normalization-demand"

bedroyaInitialScalarVelocityConventionDemand : SourceSearch.SourceDiligenceSearchDemand
bedroyaInitialScalarVelocityConventionDemand =
  SourceSearch.source-diligence-search-demand
    "initial scalar velocity convention used by the 2026 CLASS implementation"
    SourceSearch.propositionSupportUnresolved
    Search.propositionSourceProducer
    refl
    "DASHI.Empirical.DarkDimensionBedroyaBackgroundInputContractExact"
    "bedroya-initial-scalar-velocity-convention-demand"

data SampledDensitySupportEqualsV0Support : Set where

sampledDensityAndV0DemandsRemainDistinct :
  SampledDensitySupportEqualsV0Support → ⊥
sampledDensityAndV0DemandsRemainDistinct ()

data SameObjectLocationClosesPropositionSupport : Set where

sameObjectLocationDoesNotCloseSupport :
  SameObjectLocationClosesPropositionSupport → ⊥
sameObjectLocationDoesNotCloseSupport ()

childSameObjectStillUnacquired :
  Acquisition.fullTextAcquired bedroya2026SameObjectTarget ≡ false
childSameObjectStillUnacquired = refl

childPrimaryObjectStillUninspected :
  Acquisition.primaryTextInspected bedroya2026SameObjectTarget ≡ false
childPrimaryObjectStillUninspected = refl

childTranscriptionStillUnextracted :
  Acquisition.transcriptionExtracted bedroya2026SameObjectTarget ≡ false
childTranscriptionStillUnextracted = refl

parentLineageMayGuideSearchButCannotSubstitute :
  ParentLineage.exactImplementationInheritanceDemonstrated
    ParentLineage.canonicalFadingDMParentLineageStatus
  ≡ false
parentLineageMayGuideSearchButCannotSubstitute =
  ParentLineage.parentImplementationInheritanceStillOpen

data ParentImplementationPaysChildSameObjectDemand : Set where
data ParentNormalizationPaysChildSameObjectDemand : Set where

parentImplementationCannotPayChildSameObjectDemand :
  ParentImplementationPaysChildSameObjectDemand → ⊥
parentImplementationCannotPayChildSameObjectDemand ()

parentNormalizationCannotPayChildSameObjectDemand :
  ParentNormalizationPaysChildSameObjectDemand → ⊥
parentNormalizationCannotPayChildSameObjectDemand ()
