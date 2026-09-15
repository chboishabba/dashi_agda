module DASHI.Wikimedia.IbrahimCannabisWishartSampleAliquotIdentityParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimCannabisWishartArticleCCDDiscrepancyParetoExact as Discrepancy
import DASHI.Wikimedia.IbrahimCannabisWishartCCDCompoundRowIdentityParetoExact as RowIdentity
import DASHI.Wikimedia.IbrahimCannabisWishartPublicReviewContextParetoExact as Review
import DASHI.Governance.PhenomenonEvidenceFibreOverTimeExact as Temporal

------------------------------------------------------------------------
-- WISHART CANNABIS SAMPLE / HOMOGENATE / ALIQUOT IDENTITY HIERARCHY
--
-- Same cultivar label is not the same identity claim as same retail package,
-- same ground homogenate, same extraction aliquot, same analytical injection,
-- or same reported aggregate.  The Wishart paper pays one 3.5 g dry-weight
-- purchased sample per cultivar and three technical replicates, with plant
-- material ground to a fine powder before small analytical aliquots were taken.
--
-- This makes biological / sampling heterogeneity a high-prior explanation
-- class in cannabis generally, but grinding reduces the strength of a simple
-- "different region of the same bud" explanation for the exact Wishart
-- publication-side aliquots.  The CCD-side carrier remains unresolved.
------------------------------------------------------------------------

data SampleIdentityLevel : Set where
  cultivarLabel
  retailProductIdentity
  purchasedPackage
  grossPlantMaterial
  groundHomogenate
  extractionAliquot
  analyticalInjection
  technicalReplicate
  reportedAggregate : SampleIdentityLevel

record WishartSampleCarrier : Set where
  constructor wishart-sample-carrier
  field
    cultivarReference : String
    retailAcquisitionReference : String
    packageMassReference : String
    storageReference : String
    grindingReference : String
    assayAliquotReference : String
    extractionReference : String
    replicateReference : String
    reportSurfaceReference : String
    cultivarLabelPaid : Bool
    purchasedPackagePaid : Bool
    groundHomogenatePaid : Bool
    exactExtractionAliquotPaid : Bool
    exactInjectionPaid : Bool
    replicateAggregationPaid : Bool
open WishartSampleCarrier public

wishartPublicationCarrier : WishartSampleCarrier
wishartPublicationCarrier = wishart-sample-carrier
  "six named commercial cultivars: Alien Dawg, Tangerine Dream, Sensi Star, Quadra, Gabriola, Island Honey"
  "purchased from a licensed cannabis distributor in Edmonton, Canada"
  "one 3.5 g dry-weight sample per cultivar"
  "stored at room temperature until analysis"
  "dry cannabis plant material was ground via mortar and pestle to a fine powder for the reported analytical workflows"
  "small assay-specific masses were drawn after grinding; cannabinoid workflow inherited the 25 mg ground-cultivar extraction carrier described for the LC-MS workflow"
  "hexane/methanol extraction followed by cannabinoid-targeted LC-MS/MS preparation"
  "one sample per cultivar; three technical replicates analyzed"
  "publication prose/tables plus supporting Table S5 for per-cultivar cannabinoid values"
  true true true false false false

------------------------------------------------------------------------
-- Biological spatial heterogeneity is real and therefore should be tested
-- before database-error hypotheses, but it is not automatically the exact
-- Wishart explanation.
------------------------------------------------------------------------

record SpatialHeterogeneitySource : Set where
  constructor spatial-heterogeneity-source
  field
    authorsOrStudy : String
    title : String
    year : Nat
    doi : String
    directLink : String
    boundedReading : String
    exactWishartExplanationPaid : Bool
open SpatialHeterogeneitySource public

namdarEtAl2018 : SpatialHeterogeneitySource
namdarEtAl2018 = spatial-heterogeneity-source
  "Dvory Namdar; Moran Mazuz; Aurel Ion; Hinanit Koltai"
  "Variation in the compositions of cannabinoid and terpenoids in Cannabis sativa derived from inflorescence position along the stem and extraction methods"
  2018
  "10.1016/j.indcrop.2018.01.060"
  "https://doi.org/10.1016/j.indcrop.2018.01.060"
  "Cannabinoid and terpenoid amounts decreased with descending inflorescence position along the stem, and extraction choices also changed measured composition."
  false

bernsteinGorelickKoch2019 : SpatialHeterogeneitySource
bernsteinGorelickKoch2019 = spatial-heterogeneity-source
  "Nirit Bernstein; Jonathan Gorelick; Sraya Koch"
  "Interplay between chemistry and morphology in medical cannabis (Cannabis sativa L.)"
  2019
  "10.1016/j.indcrop.2018.11.039"
  "https://doi.org/10.1016/j.indcrop.2018.11.039"
  "Reports substantial spatial gradients in cannabinoid concentrations by plant height and organ identity."
  false

plantPositionReplicationReference : String
plantPositionReplicationReference =
  "Accumulation of bioactive metabolites in cultivated medical Cannabis reports upper flowers with substantially greater delta-9-THC than lower flowers across multiple strains; exact DOI retained externally pending local source-normalisation."

densityUniformityReference : String
densityUniformityReference =
  "Danziger/Bernstein medical-cannabis architecture work reports bottom inflorescences up to 90 percent lower in cannabinoids than apical inflorescences under some density/architecture conditions; this is contextual spatial-heterogeneity evidence, not Wishart same-object lineage."

------------------------------------------------------------------------
-- Identity refinement.  A coarser label does not create finer same-object
-- identity.  These are deliberate firewalls rather than probabilistic claims.
------------------------------------------------------------------------

data CultivarLabelCreatesPackageIdentity : Set where
data PackageIdentityCreatesHomogenateIdentity : Set where
data HomogenateIdentityCreatesAliquotIdentity : Set where
data AliquotIdentityCreatesInjectionIdentity : Set where
data TechnicalReplicateCreatesIndependentBiologicalSample : Set where
data SpatialHeterogeneityCreatesWishartDiscrepancy : Set where
data GrindingEliminatesAllHeterogeneity : Set where

cultivarLabelDoesNotCreatePackageIdentity : CultivarLabelCreatesPackageIdentity → ⊥
cultivarLabelDoesNotCreatePackageIdentity ()

packageIdentityDoesNotCreateHomogenateIdentity : PackageIdentityCreatesHomogenateIdentity → ⊥
packageIdentityDoesNotCreateHomogenateIdentity ()

homogenateIdentityDoesNotCreateAliquotIdentity : HomogenateIdentityCreatesAliquotIdentity → ⊥
homogenateIdentityDoesNotCreateAliquotIdentity ()

aliquotIdentityDoesNotCreateInjectionIdentity : AliquotIdentityCreatesInjectionIdentity → ⊥
aliquotIdentityDoesNotCreateInjectionIdentity ()

technicalReplicateDoesNotCreateIndependentBiologicalSample : TechnicalReplicateCreatesIndependentBiologicalSample → ⊥
technicalReplicateDoesNotCreateIndependentBiologicalSample ()

spatialHeterogeneityDoesNotCreateWishartDiscrepancy : SpatialHeterogeneityCreatesWishartDiscrepancy → ⊥
spatialHeterogeneityDoesNotCreateWishartDiscrepancy ()

grindingDoesNotEliminateAllHeterogeneity : GrindingEliminatesAllHeterogeneity → ⊥
grindingDoesNotEliminateAllHeterogeneity ()

------------------------------------------------------------------------
-- Current CCD carrier status.
------------------------------------------------------------------------

record CCDCarrierAdmission : Set where
  constructor ccd-carrier-admission
  field
    cultivarLabelReference : String
    sourceCitationReference : String
    concentrationRowReference : String
    samePurchasedPackageReference : String
    sameGroundHomogenateReference : String
    sameExtractionAliquotReference : String
    sameTechnicalReplicateReference : String
    sourceVersionReference : String
    samePackagePaid : Bool
    sameHomogenatePaid : Bool
    sameAliquotPaid : Bool
    sameReplicatePaid : Bool
    sameSourceVersionPaid : Bool
open CCDCarrierAdmission public

currentCCDCarrierResidual : CCDCarrierAdmission
currentCCDCarrierResidual = ccd-carrier-admission
  "CCD uses matching commercial cultivar labels on current concentration-detail surfaces"
  "CCD attributes relevant cannabinoid rows to Wishart et al., with a 2023 manuscript-submitted citation surface"
  "current CCD per-cultivar cannabinoid concentration rows"
  "unresolved: matching cultivar name does not identify the exact 3.5 g retail package used by the publication"
  "unresolved: no located CCD provenance identifies the publication's ground homogenate"
  "unresolved: no located CCD provenance identifies the exact extraction aliquot"
  "unresolved: no located CCD provenance identifies one of the publication's three technical replicates or their aggregate rule"
  "unresolved: submitted/manuscript versus final-publication data state not yet joined"
  false false false false false

------------------------------------------------------------------------
-- Investigative Pareto order.
------------------------------------------------------------------------

data SampleParetoTarget : Set where
  recoverTableS5
  identifyCCDSourceCarrier
  testSamePackageOrDifferentPackage
  testHomogenateAndAliquotLineage
  testReplicateAggregation
  testCompoundRowMapping
  testDeterministicTransforms
  resumeEntourageTranslation : SampleParetoTarget

record SampleParetoStep : Set where
  constructor sample-pareto-step
  field
    priority : Nat
    target : SampleParetoTarget
    action : String
    pays : String
    dominatedUntil : String
open SampleParetoStep public

samplePareto0 : SampleParetoStep
samplePareto0 = sample-pareto-step
  0 recoverTableS5
  "recover the final supporting Table S5 per-cultivar cannabinoid rows and analyte names"
  "publication-side exact value/analyte vector"
  "none"

samplePareto1 : SampleParetoStep
samplePareto1 = sample-pareto-step
  1 identifyCCDSourceCarrier
  "recover CCD ingestion/version metadata sufficient to say whether its rows came from the same final table, an earlier submitted table, or another analytical carrier"
  "database-side source-object identity"
  "publication vector should be recovered in parallel"

samplePareto2 : SampleParetoStep
samplePareto2 = sample-pareto-step
  2 testSamePackageOrDifferentPackage
  "test whether CCD and publication values refer to the same purchased 3.5 g package, another package of the same cultivar, or only the same commercial label"
  "biological/sample identity discriminator"
  "matching cultivar labels are insufficient"

samplePareto3 : SampleParetoStep
samplePareto3 = sample-pareto-step
  3 testHomogenateAndAliquotLineage
  "if same package is paid, determine whether values derive from the same ground homogenate and extraction aliquot"
  "within-package analytical identity"
  "package identity required first"

samplePareto4 : SampleParetoStep
samplePareto4 = sample-pareto-step
  4 testReplicateAggregation
  "recover the three technical-replicate values or aggregation rule before comparing an individual replicate with a publication mean"
  "replicate/mean semantics"
  "same assay carrier required"

samplePareto5 : SampleParetoStep
samplePareto5 = sample-pareto-step
  5 testCompoundRowMapping
  "only after source/sample identity checks, test THCA/THCA-A/delta-8-THCA row identity and mappings"
  "compound-row identity discriminator"
  "sample/source mismatch can dominate an apparent row defect"

samplePareto6 : SampleParetoStep
samplePareto6 = sample-pareto-step
  6 testDeterministicTransforms
  "test units, dry-weight basis, dilution, molecular-weight/decarboxylation and row/column permutations against exact paired vectors"
  "deterministic transformation discriminator"
  "exact source vectors required"

samplePareto9 : SampleParetoStep
samplePareto9 = sample-pareto-step
  9 resumeEntourageTranslation
  "resume batch-composition to interaction/exposure reasoning only from a carrier whose sample and source-version identity are explicit"
  "consumer-safe pharmacology admission"
  "dominated by unresolved sample/source lineage"

------------------------------------------------------------------------
-- Temporal evidence fibre.
------------------------------------------------------------------------

data SampleTime : Set where
  biologicalSpatialLiterature
  wishartAcquisition2023
  wishartPublication2024
  currentCCDObservation
  currentDashi : SampleTime

data SampleInterpretation : Set where
  spatialHeterogeneityPlausible
  publicationUsesOnePackagePerCultivar
  publicationGroundsPlantMaterial
  ccdSamePackagePaid
  discrepancyExplainedBySampling : SampleInterpretation

data SampleSummary : Set where
  sampleIdentityMustBeRefined : SampleSummary

SampleCompatible : SampleTime → SampleInterpretation → Set
SampleCompatible biologicalSpatialLiterature spatialHeterogeneityPlausible = ⊤
SampleCompatible biologicalSpatialLiterature publicationUsesOnePackagePerCultivar = ⊥
SampleCompatible biologicalSpatialLiterature publicationGroundsPlantMaterial = ⊥
SampleCompatible biologicalSpatialLiterature ccdSamePackagePaid = ⊥
SampleCompatible biologicalSpatialLiterature discrepancyExplainedBySampling = ⊥
SampleCompatible wishartAcquisition2023 spatialHeterogeneityPlausible = ⊤
SampleCompatible wishartAcquisition2023 publicationUsesOnePackagePerCultivar = ⊤
SampleCompatible wishartAcquisition2023 publicationGroundsPlantMaterial = ⊤
SampleCompatible wishartAcquisition2023 ccdSamePackagePaid = ⊥
SampleCompatible wishartAcquisition2023 discrepancyExplainedBySampling = ⊥
SampleCompatible wishartPublication2024 spatialHeterogeneityPlausible = ⊤
SampleCompatible wishartPublication2024 publicationUsesOnePackagePerCultivar = ⊤
SampleCompatible wishartPublication2024 publicationGroundsPlantMaterial = ⊤
SampleCompatible wishartPublication2024 ccdSamePackagePaid = ⊥
SampleCompatible wishartPublication2024 discrepancyExplainedBySampling = ⊥
SampleCompatible currentCCDObservation spatialHeterogeneityPlausible = ⊤
SampleCompatible currentCCDObservation publicationUsesOnePackagePerCultivar = ⊤
SampleCompatible currentCCDObservation publicationGroundsPlantMaterial = ⊤
SampleCompatible currentCCDObservation ccdSamePackagePaid = ⊥
SampleCompatible currentCCDObservation discrepancyExplainedBySampling = ⊥
SampleCompatible currentDashi spatialHeterogeneityPlausible = ⊤
SampleCompatible currentDashi publicationUsesOnePackagePerCultivar = ⊤
SampleCompatible currentDashi publicationGroundsPlantMaterial = ⊤
SampleCompatible currentDashi ccdSamePackagePaid = ⊥
SampleCompatible currentDashi discrepancyExplainedBySampling = ⊥

sampleTemporalSystem : Temporal.TemporalEvidenceSystem
sampleTemporalSystem = record
  { Time = SampleTime
  ; Interpretation = SampleInterpretation
  ; Compatible = SampleCompatible
  ; Summary = SampleSummary
  ; summarize = λ _ → sampleIdentityMustBeRefined
  ; timeReference = λ
      { biologicalSpatialLiterature → "Cannabis spatial-chemistry literature establishes within-plant heterogeneity as a real phenomenon"
      ; wishartAcquisition2023 → "Wishart commercial Cannabis acquisition/sample-preparation state: one 3.5 g dry sample per cultivar, ground plant material, three technical replicates"
      ; wishartPublication2024 → "Wishart et al. final publication DOI 10.1021/acs.jafc.3c06616"
      ; currentCCDObservation → "current CCD concentration surfaces attributed to Wishart et al."
      ; currentDashi → "current DASHI sample/source lineage frontier"
      }
  }

currentSampleLineageStillOpen : Temporal.EvidenceFibre sampleTemporalSystem currentDashi
currentSampleLineageStillOpen = Temporal.liveInterpretationAt spatialHeterogeneityPlausible tt

------------------------------------------------------------------------
-- Boundary summary.
------------------------------------------------------------------------

record WishartSampleIdentityBoundary : Set where
  constructor wishart-sample-identity-boundary
  field
    sameCultivarIsNotSamePackage : Bool
    samePackageIsNotSameAliquot : Bool
    technicalReplicateIsNotBiologicalReplicate : Bool
    spatialHeterogeneityIsRealContext : Bool
    grindingReducesSimpleSpatialConfounding : Bool
    grindingEliminatesAllHeterogeneity : Bool
    ccdSamePackageCurrentlyPaid : Bool
    samplingDifferenceCurrentlyExplainsDiscrepancy : Bool
open WishartSampleIdentityBoundary public

canonicalWishartSampleIdentityBoundary : WishartSampleIdentityBoundary
canonicalWishartSampleIdentityBoundary =
  wishart-sample-identity-boundary
    true true true true true false false false
