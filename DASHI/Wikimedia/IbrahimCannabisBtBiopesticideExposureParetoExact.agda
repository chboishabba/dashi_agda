module DASHI.Wikimedia.IbrahimCannabisBtBiopesticideExposureParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimCannabisCommonResiduePanelParetoExact as Residue
import DASHI.Wikimedia.IbrahimCannabisContaminantToxicantAssayParetoExact as Toxicant
import DASHI.Governance.PhenomenonEvidenceFibreOverTimeExact as Temporal

------------------------------------------------------------------------
-- BACILLUS THURINGIENSIS (Bt) BIOPESTICIDE / CANNABIS EXPOSURE OWNER
--
-- Bt is not one small molecule. A commercial Bt treatment can expose a plant
-- surface to a strain-specific microbial preparation containing viable spores,
-- vegetative cells, insecticidal crystal proteins (Cry family), formulation
-- ingredients and degradation products. Therefore a conventional LC/GC
-- small-molecule pesticide panel is not automatically an observer for Bt use.
------------------------------------------------------------------------

data BtObjectKind : Set where
  organism
  strain
  viableSpore
  vegetativeCell
  crystalProtein
  formulation
  formulationIngredient
  applicationEvent
  plantSurfaceResidue
  thermalTransformationProduct : BtObjectKind

record BtIdentityReceipt : Set where
  constructor bt-identity-receipt
  field
    objectKind : BtObjectKind
    canonicalReference : String
    strainReference : String
    proteinReference : String
    formulationReference : String
    exactObjectIdentityPaid : Bool
open BtIdentityReceipt public

btSpeciesIdentity : BtIdentityReceipt
btSpeciesIdentity = bt-identity-receipt
  organism
  "Bacillus thuringiensis; Gram-positive sporulating member of the Bacillus cereus group"
  "strain/subspecies unresolved at generic Bt level"
  "Cry/Vip protein identity unresolved at generic Bt level"
  "commercial formulation unresolved at generic Bt level"
  true

btkExampleIdentity : BtIdentityReceipt
btkExampleIdentity = bt-identity-receipt
  strain
  "Bacillus thuringiensis subsp. kurstaki (Btk)"
  "strain must be carried explicitly; California DPR product registry includes multiple Btk strain-labelled products"
  "Cry protein complement is strain/formulation specific and not inferred from the token Bt"
  "product label required for exact formulation"
  true

------------------------------------------------------------------------
-- Regulatory/source context.
------------------------------------------------------------------------

record BtRegulatorySource : Set where
  constructor bt-regulatory-source
  field
    jurisdiction : String
    source : String
    directLink : String
    boundedReading : String
    cannabisSpecificUsePaid : Bool
open BtRegulatorySource public

californiaBtRegistry : BtRegulatorySource
californiaBtRegistry = bt-regulatory-source
  "California"
  "California Department of Pesticide Regulation product registry and cannabis-use criteria"
  "https://www.cdpr.ca.gov/cac-letter/list-of-products-legal-to-use-on-cannabis/"
  "DPR states cannabis-use legality depends on residue-tolerance exemption and label compatibility. DPR separately lists active Bt products, including multiple B. thuringiensis subsp. kurstaki products. Product registration alone does not prove that every Bt product is legal on cannabis; exact product/label admission remains required."
  false

canadaCannabisPcpRule : BtRegulatorySource
canadaCannabisPcpRule = bt-regulatory-source
  "Canada"
  "Health Canada pest control products for use on cannabis"
  "https://www.canada.ca/en/health-canada/services/cannabis-regulations-licensed-producers/pest-control-products.html"
  "Only pest control products registered or otherwise authorized for use on cannabis may be used. Matching the generic active organism Bt is insufficient; exact PCP label/registration must be joined."
  false

australiaTgo93BtContext : BtRegulatorySource
australiaTgo93BtContext = bt-regulatory-source
  "Australia"
  "TGA medicinal cannabis quality requirements under TGO 93"
  "https://www.tga.gov.au/resources/guidance/complying-quality-requirements-medicinal-cannabis"
  "TGO 93 is a medicinal-cannabis product quality/testing standard. It does not itself establish a universal Bt cultivation-input permission or prohibition. Additional testing may be warranted where the specified monographs do not cover the relevant residual object."
  false

------------------------------------------------------------------------
-- Assay observability.
------------------------------------------------------------------------

data BtObserverKind : Set where
  smallMoleculeLCMS
  smallMoleculeGCMS
  viableCountCFU
  cultureIdentification
  strainPCR
  qPCR
  proteinImmunoassay
  targetedProteomics
  microscopy
  metagenomicSequence : BtObserverKind

record BtObservationAdmission : Set where
  constructor bt-observation-admission
  field
    target : BtObjectKind
    observer : BtObserverKind
    methodReference : String
    targetObservableByMethod : Bool
    cannabisMatrixValidated : Bool
    quantitationLimitReference : String
    sameSamplePaid : Bool
open BtObservationAdmission public

chemicalPanelDoesNotObserveBtUse : BtObservationAdmission
chemicalPanelDoesNotObserveBtUse = bt-observation-admission
  applicationEvent smallMoleculeLCMS
  "conventional pesticide LC-MS/MS small-molecule residue panel"
  false false
  "not applicable until an explicit molecular marker target is specified"
  false

btkSporePCRCandidate : BtObservationAdmission
btkSporePCRCandidate = bt-observation-admission
  viableSpore strainPCR
  "strain/subspecies-specific PCR can identify Bt genetic material; viability requires a separate culture/CFU observation"
  true false
  "method-specific detection/quantitation limit unresolved for cannabis flower"
  false

cryProteinCandidate : BtObservationAdmission
cryProteinCandidate = bt-observation-admission
  crystalProtein targetedProteomics
  "targeted protein assay/proteomics could observe selected Cry proteins if strain/protein identities are fixed"
  true false
  "protein-specific limit unresolved for cannabis flower"
  false

------------------------------------------------------------------------
-- Human-health evidence boundary.
------------------------------------------------------------------------

record BtHealthSource : Set where
  constructor bt-health-source
  field
    source : String
    year : Nat
    doiOrReference : String
    directLink : String
    boundedReading : String
    cannabisConsumerInhalationPaid : Bool
open BtHealthSource public

occupationalExposureReview : BtHealthSource
occupationalExposureReview = bt-health-source
  "Occupational exposure to microorganisms used as biocontrol agents in plant production"
  2011
  "PMID 21196399"
  "https://pubmed.ncbi.nlm.nih.gov/21196399/"
  "Documents aerosol/inhalation exposure to microbial biocontrol agents including B. thuringiensis; highest exposures occur among applicators. This is occupational application exposure, not smoking/vaporisation exposure from treated cannabis."
  false

btiGreenhouseExposure : BtHealthSource
btiGreenhouseExposure = bt-health-source
  "Exposure and preventive measure to reduce high and daily exposure to Bacillus thuringiensis in potted plant production"
  2014
  "10.1093/annhyg/meu030"
  "https://pubmed.ncbi.nlm.nih.gov/24863937/"
  "Measured airborne Bti by personal/stationary samplers and PCR/CFU in greenhouse workers, including median personal inhalable exposure around 3e5 CFU/m3 in a high-exposure propagation section. Does not establish cannabis-user dose."
  false

efsaBtkSA11 : BtHealthSource
efsaBtkSA11 = bt-health-source
  "EFSA peer review: Bacillus thuringiensis subsp. kurstaki strain SA-11"
  2020
  "10.2903/j.efsa.2020.6261"
  "https://efsa.onlinelibrary.wiley.com/doi/10.2903/j.efsa.2020.6261"
  "EFSA notes possible sensitising reactions and states repeated-exposure inhalation toxicity/infectivity and non-dietary Cry-protein genotoxic potential could not be concluded; this is an unresolved risk-assessment data gap, not proof of harm."
  false

efsaBtkPB54 : BtHealthSource
efsaBtkPB54 = bt-health-source
  "EFSA peer review: Bacillus thuringiensis subsp. kurstaki strain PB 54"
  2021
  "10.2903/j.efsa.2021.6498"
  "https://pmc.ncbi.nlm.nih.gov/articles/PMC8028025/"
  "Again leaves repeated inhalation toxicity/infectivity unresolved and does not complete a quantitative inhalation risk assessment."
  false

currentBtReview : BtHealthSource
currentBtReview = bt-health-source
  "Unintended effects of Bacillus thuringiensis spores and Cry toxins used as microbial insecticides on non-target organisms"
  2025
  "10.1016/j.coesh.2025.100598"
  "https://doi.org/10.1016/j.coesh.2025.100598"
  "Reviews persistence and unintended effects of Bt product components including spores, vegetative cells and Cry toxins. Supports decomposing the Bt product into multiple exposure objects rather than treating it as one chemical residue."
  false

------------------------------------------------------------------------
-- Cannabis route/exposure bridge.
------------------------------------------------------------------------

record BtCannabisExposureBridge : Set where
  constructor bt-cannabis-exposure-bridge
  field
    exactCommercialProductReference : String
    exactBtStrainReference : String
    applicationTimingReference : String
    preHarvestIntervalReference : String
    flowerResidueReference : String
    viableSporeBurdenReference : String
    cryProteinBurdenReference : String
    formulationResidueReference : String
    combustionTransformationReference : String
    vaporisationTransformationReference : String
    aerosolTransferReference : String
    inhaledDoseReference : String
    consumerToxicologyReference : String
    applicationPaid : Bool
    flowerResiduePaid : Bool
    thermalTransferPaid : Bool
    inhaledDosePaid : Bool
    clinicalRiskPaid : Bool
open BtCannabisExposureBridge public

currentBtCannabisResidual : BtCannabisExposureBridge
currentBtCannabisResidual = bt-cannabis-exposure-bridge
  "unpaid: exact Bt product applied to a concrete cannabis crop"
  "unpaid: product-specific Bt strain/subspecies"
  "unpaid: exact application date relative to harvest"
  "unpaid"
  "unpaid: same-batch cannabis flower measurement"
  "unpaid CFU/g or viable-count observation"
  "unpaid Cry/Vip protein mass/activity observation"
  "unpaid non-Bt formulation ingredients"
  "unpaid: thermal fate under smoking combustion"
  "unpaid: thermal fate under cannabis vaporisation temperatures"
  "unpaid aerosol/smoke transfer fraction"
  "unpaid delivered/absorbed dose"
  "unpaid route-specific human toxicology"
  false false false false false

------------------------------------------------------------------------
-- Firewalls and canonical boundaries.
------------------------------------------------------------------------

data BtIsOneSmallMolecule : Set where
data SmallMoleculePanelDetectsBtApplication : Set where
data BtLegalProductCreatesCannabisUseAuthority : Set where
data OrganicOrBiologicalCreatesNoRisk : Set where
data EFSADataGapCreatesDemonstratedHarm : Set where
data ApplicationCreatesConsumerExposure : Set where

btIsNotOneSmallMolecule : BtIsOneSmallMolecule → ⊥
btIsNotOneSmallMolecule ()

smallMoleculePanelDoesNotDetectBtApplication : SmallMoleculePanelDetectsBtApplication → ⊥
smallMoleculePanelDoesNotDetectBtApplication ()

legalProductDoesNotCreateCannabisUseAuthority : BtLegalProductCreatesCannabisUseAuthority → ⊥
legalProductDoesNotCreateCannabisUseAuthority ()

biologicalDoesNotCreateNoRisk : OrganicOrBiologicalCreatesNoRisk → ⊥
biologicalDoesNotCreateNoRisk ()

dataGapDoesNotCreateDemonstratedHarm : EFSADataGapCreatesDemonstratedHarm → ⊥
dataGapDoesNotCreateDemonstratedHarm ()

applicationDoesNotCreateConsumerExposure : ApplicationCreatesConsumerExposure → ⊥
applicationDoesNotCreateConsumerExposure ()

record BtOntologyBoundary : Set where
  constructor bt-ontology-boundary
  field
    btIsSingleSmallMolecule : Bool
    strainIdentityRequired : Bool
    cryProteinIdentitySeparate : Bool
    viableSporeIdentitySeparate : Bool
    formulationIdentitySeparate : Bool
open BtOntologyBoundary public

canonicalBtOntologyBoundary : BtOntologyBoundary
canonicalBtOntologyBoundary = bt-ontology-boundary false true true true true

record BtCoverageBoundary : Set where
  constructor bt-coverage-boundary
  field
    conventionalLCGCPanelAutomaticallyCoversBt : Bool
    organismObserverRequired : Bool
    proteinObserverMayBeRequired : Bool
    cannabisMatrixValidationRequired : Bool
    nonDetectionCreatesNoPriorUse : Bool
open BtCoverageBoundary public

canonicalBtCoverageBoundary : BtCoverageBoundary
canonicalBtCoverageBoundary = bt-coverage-boundary false true true true false

record BtExposureBoundary : Set where
  constructor bt-exposure-boundary
  field
    applicationCreatesFlowerResidue : Bool
    flowerResidueCreatesInhaledDose : Bool
    occupationalInhalationEqualsConsumerInhalation : Bool
    inhalationEvidenceComplete : Bool
    thermalFateCurrentlyPaid : Bool
open BtExposureBoundary public

canonicalBtExposureBoundary : BtExposureBoundary
canonicalBtExposureBoundary = bt-exposure-boundary false false false false false

------------------------------------------------------------------------
-- Pareto continuation.
------------------------------------------------------------------------

data BtParetoTarget : Set where
  exactCannabisBtProduct
  exactStrainAndProteinContent
  cannabisFlowerBtMeasurement
  smallMoleculePanelBlindSpotAudit
  combustionFate
  vaporisationFate
  inhaledDose
  clinicalRisk : BtParetoTarget

record BtParetoStep : Set where
  constructor bt-pareto-step
  field
    priority : Nat
    target : BtParetoTarget
    action : String
    pays : String
    dominatedUntil : String
open BtParetoStep public

pareto0 : BtParetoStep
pareto0 = bt-pareto-step
  0 exactCannabisBtProduct
  "identify an exact Bt product actually authorised/used on cannabis, including jurisdiction and label"
  "legal/product same-object admission"
  "generic Bt product registration is insufficient"

pareto1 : BtParetoStep
pareto1 = bt-pareto-step
  1 exactStrainAndProteinContent
  "resolve strain/subspecies, viable-spore specification, Cry/Vip protein complement and formulation ingredients for that product"
  "exposure-object identity"
  "exact product required"

pareto2 : BtParetoStep
pareto2 = bt-pareto-step
  2 cannabisFlowerBtMeasurement
  "find same-batch cannabis flower data using culture/CFU plus molecular/protein methods after labelled application"
  "residual organism/protein burden"
  "application and harvest timing required"

pareto3 : BtParetoStep
pareto3 = bt-pareto-step
  3 smallMoleculePanelBlindSpotAudit
  "diff cannabis compliance panels against microbial/protein observers and show explicitly which Bt objects are outside LC/GC small-molecule coverage"
  "assay-universe completeness boundary"
  "panel method definitions required"

pareto4 : BtParetoStep
pareto4 = bt-pareto-step
  4 combustionFate
  "measure or acquire thermal fate of spores, Cry proteins and formulation under smoking combustion"
  "smoke-stream transfer/transformation"
  "flower burden must be paid first"

pareto5 : BtParetoStep
pareto5 = bt-pareto-step
  5 vaporisationFate
  "separately acquire fate/transfer under cannabis vaporisation temperatures"
  "vape/aerosol route"
  "do not infer from combustion"

pareto6 : BtParetoStep
pareto6 = bt-pareto-step
  6 inhaledDose
  "combine residual burden, transfer fraction and consumption parameters into route-specific dose"
  "consumer exposure"
  "transfer required"

pareto9 : BtParetoStep
pareto9 = bt-pareto-step
  9 clinicalRisk
  "compare paid dose with route-appropriate human evidence; retain EFSA/occupational data gaps without converting them into a poisoning claim"
  "risk conclusion"
  "dominated by missing consumer exposure"

------------------------------------------------------------------------
-- Temporal evidence fibre.
------------------------------------------------------------------------

data BtTime : Set where
  occupationalEvidence
  efsaPeerReview2020
  currentReview2025
  currentCannabisDashi : BtTime

data BtInterpretation : Set where
  aerosolExposurePossible
  repeatedInhalationUnresolved
  btCannabisConsumerExposurePaid
  btDemonstratedConsumerHarm : BtInterpretation

data BtSummary : Set where btRequiresMultiObjectExposureModel : BtSummary

BtCompatible : BtTime → BtInterpretation → Set
BtCompatible occupationalEvidence aerosolExposurePossible = ⊤
BtCompatible occupationalEvidence repeatedInhalationUnresolved = ⊤
BtCompatible occupationalEvidence btCannabisConsumerExposurePaid = ⊥
BtCompatible occupationalEvidence btDemonstratedConsumerHarm = ⊥
BtCompatible efsaPeerReview2020 aerosolExposurePossible = ⊤
BtCompatible efsaPeerReview2020 repeatedInhalationUnresolved = ⊤
BtCompatible efsaPeerReview2020 btCannabisConsumerExposurePaid = ⊥
BtCompatible efsaPeerReview2020 btDemonstratedConsumerHarm = ⊥
BtCompatible currentReview2025 aerosolExposurePossible = ⊤
BtCompatible currentReview2025 repeatedInhalationUnresolved = ⊤
BtCompatible currentReview2025 btCannabisConsumerExposurePaid = ⊥
BtCompatible currentReview2025 btDemonstratedConsumerHarm = ⊥
BtCompatible currentCannabisDashi aerosolExposurePossible = ⊤
BtCompatible currentCannabisDashi repeatedInhalationUnresolved = ⊤
BtCompatible currentCannabisDashi btCannabisConsumerExposurePaid = ⊥
BtCompatible currentCannabisDashi btDemonstratedConsumerHarm = ⊥

btTemporalSystem : Temporal.TemporalEvidenceSystem
btTemporalSystem = record
  { Time = BtTime
  ; Interpretation = BtInterpretation
  ; Compatible = BtCompatible
  ; Summary = BtSummary
  ; summarize = λ _ → btRequiresMultiObjectExposureModel
  ; timeReference = λ
      { occupationalEvidence → "published occupational Bt aerosol/exposure literature"
      ; efsaPeerReview2020 → "EFSA Bt strain peer reviews beginning 2020"
      ; currentReview2025 → "2025 review of Bt spores/Cry toxins and unintended effects"
      ; currentCannabisDashi → "current DASHI cannabis Bt exposure frontier"
      }
  }

currentBtFibre : Temporal.EvidenceFibre btTemporalSystem currentCannabisDashi
currentBtFibre = Temporal.liveInterpretationAt repeatedInhalationUnresolved tt
