module DASHI.Wikimedia.IbrahimCannabisTerpeneCommercialSampleQuantitativeAssayExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimCannabisTerpeneIdentityInteractionParetoExact as Interaction
import DASHI.Wikimedia.IbrahimCannabisTerpenePubChemCIDAuthorityExact as PubChem
import DASHI.Wikimedia.IbrahimCannabisTerpeneChemotypeAssayBiosynthesisParetoExact as Composition
import DASHI.Governance.PhenomenonEvidenceFibreOverTimeExact as Temporal

------------------------------------------------------------------------
-- COMMERCIAL CANNABIS SAME-SAMPLE QUANTITATIVE TERPENE ASSAY
--
-- Pareto move: pay one concrete composition surface before broadening the
-- entourage literature.  Wishart et al. 2024 analysed six commercial cannabis
-- samples, one 3.5 g dry-weight sample per vendor-labelled cultivar, with three
-- technical replicates.  Targeted GC-MS quantified terpenoids and targeted
-- LC-MS/MS quantified cannabinoids on the same named sample set.
--
-- The source pays sample-labelled quantitative occurrence.  It does not prove
-- cultivar/genotype identity, pharmacokinetic exposure, molecular interaction,
-- synergy or clinical efficacy.
------------------------------------------------------------------------

record QuantitativeCompositionSource : Set where
  constructor quantitative-composition-source
  field
    authors : String
    title : String
    publication : String
    year : Nat
    doi : String
    directLink : String
    correctionDOI : String
    sourceRole : String
    boundedReading : String
    excludedPromotion : String
open QuantitativeCompositionSource public

wishart2024 : QuantitativeCompositionSource
wishart2024 = quantitative-composition-source
  "David S. Wishart; Mickel Hiebert-Giesbrecht; Gozal Inchehborouni; Xuan Cao; An Chi Guo; Marcia A. LeVatte; Claudia Torres-Calzada; Vasuk Gautam; Mathew Johnson; Jaanus Liigand; Fei Wang; Shirin Zahraei; Sudarshana Bhumireddy; Yilin Wang; Jiamin Zheng; Rupasri Mandal; Jason R. B. Dyck"
  "Chemical Composition of Commercial Cannabis"
  "Journal of Agricultural and Food Chemistry 72(25):14099-14113"
  2024
  "10.1021/acs.jafc.3c06616"
  "https://doi.org/10.1021/acs.jafc.3c06616"
  "10.1021/acs.jafc.4c01418"
  "primary multi-platform quantitative metabolomics study on six commercial cannabis samples"
  "Six named commercial samples were purchased from a licensed distributor in Edmonton, Canada. One 3.5 g dry-weight sample per label was used; three technical replicates were analysed. Targeted GC-MS quantified terpenoids and targeted LC-MS/MS quantified cannabinoids."
  "Vendor/cultivar label is not genotype proof; one sampled package is not a universal cultivar profile; co-occurrence is not interaction, exposure, synergy or efficacy."

------------------------------------------------------------------------
-- Sample identity is explicitly the assayed commercial sample, not a claim
-- about every product carrying the same cultivar/brand label.
------------------------------------------------------------------------

data CommercialSample : Set where
  alienDawg : CommercialSample
  tangerineDream : CommercialSample
  sensiStar : CommercialSample
  quadra : CommercialSample
  gabriola : CommercialSample
  islandHoney : CommercialSample

sampleLabel : CommercialSample → String
sampleLabel alienDawg = "Alien Dawg"
sampleLabel tangerineDream = "Tangerine Dream"
sampleLabel sensiStar = "Sensi Star"
sampleLabel quadra = "Quadra"
sampleLabel gabriola = "Gabriola (Frosty Monster)"
sampleLabel islandHoney = "Island Honey"

record SampleCustodyReceipt (sample : CommercialSample) : Set where
  constructor sample-custody-receipt
  field
    purchaseReference : String
    vendorLabelReference : String
    sampleMassReference : String
    storageReference : String
    technicalReplicateReference : String
    sameSampleAcrossAssaySurfaceReference : String
    genotypeIdentityPaid : Bool
    universalCultivarProfilePaid : Bool
open SampleCustodyReceipt public

canonicalSampleCustody : (sample : CommercialSample) → SampleCustodyReceipt sample
canonicalSampleCustody sample = sample-custody-receipt
  "purchased from a licensed cannabis distributor in Edmonton, Canada"
  (sampleLabel sample)
  "3.5 g dry-weight commercial sample"
  "stored at room temperature until analysis"
  "one sample per labelled cultivar; three technical replicates analysed"
  "Wishart et al. experimental metabolomics surface for the same six named samples"
  false false

------------------------------------------------------------------------
-- Quantitative terpene rows.
-- Values below are source-reported mg/g dry weight from Wishart et al. Table 2.
-- PubChem CIDs remain registry identifiers owned by PubChem Compound.  The CDB
-- identifiers belong to the Cannabis Compound Database and are not PubChem CIDs.
------------------------------------------------------------------------

data QuantifiedTerpene : Set where
  betaMyrcene : QuantifiedTerpene
  rPlusLimonene : QuantifiedTerpene
  linalool : QuantifiedTerpene
  transCaryophyllene : QuantifiedTerpene

record TerpeneRegistryJoin : Set where
  constructor terpene-registry-join
  field
    terpene : QuantifiedTerpene
    sourceLabel : String
    cannabisCompoundDatabaseId : String
    pubChemCID : String
    pubChemLink : String
    formula : String
    stereochemistryScope : String
    cdbIsPubChemCID : Bool
    pubChemOwnsCID : Bool
open TerpeneRegistryJoin public

myrceneRegistryJoin : TerpeneRegistryJoin
myrceneRegistryJoin = terpene-registry-join
  betaMyrcene "beta-myrcene" "CDB000573" "31253"
  "https://pubchem.ncbi.nlm.nih.gov/compound/31253" "C10H16"
  "achiral molecular identity at this registry layer"
  false true

rPlusLimoneneRegistryJoin : TerpeneRegistryJoin
rPlusLimoneneRegistryJoin = terpene-registry-join
  rPlusLimonene "R-(+)-limonene" "CDB000069" "440917"
  "https://pubchem.ncbi.nlm.nih.gov/compound/440917" "C10H16"
  "R/(+)-limonene; do not replace with racemic limonene CID 22311"
  false true

linaloolRegistryJoin : TerpeneRegistryJoin
linaloolRegistryJoin = terpene-registry-join
  linalool "linalool" "CDB000089" "6549"
  "https://pubchem.ncbi.nlm.nih.gov/compound/6549" "C10H18O"
  "source does not justify an enantiomer-specific abundance claim beyond its reported linalool analytical identity"
  false true

transCaryophylleneRegistryJoin : TerpeneRegistryJoin
transCaryophylleneRegistryJoin = terpene-registry-join
  transCaryophyllene "trans-caryophyllene" "CDB000712" "5281515"
  "https://pubchem.ncbi.nlm.nih.gov/compound/5281515" "C15H24"
  "PubChem CID 5281515 is (-)-beta-caryophyllene / (-)-trans-caryophyllene; source-to-registry stereochemical alignment is retained explicitly"
  false true

record QuantitativeTerpeneObservation : Set where
  constructor quantitative-terpene-observation
  field
    sample : CommercialSample
    registry : TerpeneRegistryJoin
    concentrationMgPerGDryWeight : String
    analyticalMethodReference : String
    sourceReference : String
    sameSampleOccurrencePaid : Bool
    quantitativeAbundancePaid : Bool
    humanExposurePaid : Bool
    interactionPaid : Bool
open QuantitativeTerpeneObservation public

mkObservation : CommercialSample → TerpeneRegistryJoin → String → QuantitativeTerpeneObservation
mkObservation sample registry concentration = quantitative-terpene-observation
  sample registry concentration
  "targeted quantitative GC-MS terpenoid assay; source reports mg/g dry weight"
  "Wishart et al. 2024 Table 2, DOI 10.1021/acs.jafc.3c06616"
  true true false false

-- beta-myrcene, mg/g dry weight
alienDawgMyrcene : QuantitativeTerpeneObservation
alienDawgMyrcene = mkObservation alienDawg myrceneRegistryJoin "1.17"

tangerineDreamMyrcene : QuantitativeTerpeneObservation
tangerineDreamMyrcene = mkObservation tangerineDream myrceneRegistryJoin "1.71"

sensiStarMyrcene : QuantitativeTerpeneObservation
sensiStarMyrcene = mkObservation sensiStar myrceneRegistryJoin "0.75"

quadraMyrcene : QuantitativeTerpeneObservation
quadraMyrcene = mkObservation quadra myrceneRegistryJoin "0.38"

gabriolaMyrcene : QuantitativeTerpeneObservation
gabriolaMyrcene = mkObservation gabriola myrceneRegistryJoin "0.42"

islandHoneyMyrcene : QuantitativeTerpeneObservation
islandHoneyMyrcene = mkObservation islandHoney myrceneRegistryJoin "0.44"

-- R-(+)-limonene, mg/g dry weight
alienDawgLimonene : QuantitativeTerpeneObservation
alienDawgLimonene = mkObservation alienDawg rPlusLimoneneRegistryJoin "0.86"

tangerineDreamLimonene : QuantitativeTerpeneObservation
tangerineDreamLimonene = mkObservation tangerineDream rPlusLimoneneRegistryJoin "0.26"

sensiStarLimonene : QuantitativeTerpeneObservation
sensiStarLimonene = mkObservation sensiStar rPlusLimoneneRegistryJoin "0.18"

quadraLimonene : QuantitativeTerpeneObservation
quadraLimonene = mkObservation quadra rPlusLimoneneRegistryJoin "1.38"

gabriolaLimonene : QuantitativeTerpeneObservation
gabriolaLimonene = mkObservation gabriola rPlusLimoneneRegistryJoin "2.48"

islandHoneyLimonene : QuantitativeTerpeneObservation
islandHoneyLimonene = mkObservation islandHoney rPlusLimoneneRegistryJoin "0.12"

-- linalool, mg/g dry weight. Sensi Star was reported ND.
alienDawgLinalool : QuantitativeTerpeneObservation
alienDawgLinalool = mkObservation alienDawg linaloolRegistryJoin "0.11"

tangerineDreamLinalool : QuantitativeTerpeneObservation
tangerineDreamLinalool = mkObservation tangerineDream linaloolRegistryJoin "0.29"

sensiStarLinalool : QuantitativeTerpeneObservation
sensiStarLinalool = mkObservation sensiStar linaloolRegistryJoin "ND"

quadraLinalool : QuantitativeTerpeneObservation
quadraLinalool = mkObservation quadra linaloolRegistryJoin "0.89"

gabriolaLinalool : QuantitativeTerpeneObservation
gabriolaLinalool = mkObservation gabriola linaloolRegistryJoin "0.70"

islandHoneyLinalool : QuantitativeTerpeneObservation
islandHoneyLinalool = mkObservation islandHoney linaloolRegistryJoin "0.19"

-- trans-caryophyllene, mg/g dry weight
alienDawgCaryophyllene : QuantitativeTerpeneObservation
alienDawgCaryophyllene = mkObservation alienDawg transCaryophylleneRegistryJoin "1.86"

tangerineDreamCaryophyllene : QuantitativeTerpeneObservation
tangerineDreamCaryophyllene = mkObservation tangerineDream transCaryophylleneRegistryJoin "0.85"

sensiStarCaryophyllene : QuantitativeTerpeneObservation
sensiStarCaryophyllene = mkObservation sensiStar transCaryophylleneRegistryJoin "0.78"

quadraCaryophyllene : QuantitativeTerpeneObservation
quadraCaryophyllene = mkObservation quadra transCaryophylleneRegistryJoin "1.02"

gabriolaCaryophyllene : QuantitativeTerpeneObservation
gabriolaCaryophyllene = mkObservation gabriola transCaryophylleneRegistryJoin "2.37"

islandHoneyCaryophyllene : QuantitativeTerpeneObservation
islandHoneyCaryophyllene = mkObservation islandHoney transCaryophylleneRegistryJoin "1.32"

------------------------------------------------------------------------
-- Same-sample cannabinoid bridge.
--
-- The same study quantified 16 cannabinoids in the same six-sample assay
-- programme.  The article reports exact THCA endpoints for some samples and a
-- six-sample mean/SD, but Table 3 is an across-sample summary.  Therefore this
-- module does not invent a per-sample cannabinoid vector where the currently
-- acquired source surface has not supplied it.
------------------------------------------------------------------------

record CannabinoidAssaySurface : Set where
  constructor cannabinoid-assay-surface
  field
    assayReference : String
    sampleSetReference : String
    quantifiedCannabinoidCountReference : String
    thcaRangeReference : String
    meanTHCAReference : String
    technicalPrecisionReference : String
    exactPerSampleCannabinoidVectorAcquired : Bool
open CannabinoidAssaySurface public

wishartCannabinoidSurface : CannabinoidAssaySurface
wishartCannabinoidSurface = cannabinoid-assay-surface
  "targeted LC-MS/MS cannabinoid assay in Wishart et al. 2024"
  "same six named commercial samples; one sample each, three technical replicates"
  "16 cannabinoids quantified"
  "THCA reported from 133 mg/g in Tangerine Dream and Gabriola to 162 mg/g in Sensi Star and Alien Dawg"
  "six-sample THCA mean 148.833 +/- 19.364 mg/g"
  "reported intra- and inter-day precision 20% CV; spike recovery 80-120%"
  false

------------------------------------------------------------------------
-- Interaction translation: dry-flower abundance is not an in-vitro receptor
-- concentration.  The next experiment must pay route/extraction/dose/exposure.
------------------------------------------------------------------------

record CompositionToMechanismBridge : Set where
  constructor composition-to-mechanism-bridge
  field
    sampleReference : String
    terpeneObservationReference : String
    cannabinoidObservationReference : String
    productPreparationReference : String
    administeredDoseReference : String
    routeReference : String
    bioavailabilityReference : String
    tissueConcentrationReference : String
    timeCourseReference : String
    inVitroComparatorReference : String
    compositionPaid : Bool
    administeredDosePaid : Bool
    exposurePaid : Bool
    concentrationMatchPaid : Bool
open CompositionToMechanismBridge public

currentMechanismBridgeResidual : CompositionToMechanismBridge
currentMechanismBridgeResidual = composition-to-mechanism-bridge
  "Wishart six-sample commercial cannabis panel"
  "source-paid mg/g dry-weight terpene observations above"
  "same-study cannabinoid assay exists; exact per-sample vector not yet acquired in this owner"
  "unpaid: combustion/vaporisation/extraction/decarboxylation/preparation transformation"
  "unpaid administered amount"
  "unpaid route"
  "unpaid bioavailability"
  "unpaid target-compartment concentration"
  "unpaid concentration-versus-time profile"
  "unpaid comparison to Finlay 2020 receptor-assay concentrations"
  true false false false

------------------------------------------------------------------------
-- Pareto frontier after this payment.
------------------------------------------------------------------------

data CommercialAssayParetoTarget : Set where
  quantitativeSameSampleTerpeneProfile : CommercialAssayParetoTarget
  exactPerSampleCannabinoidVector : CommercialAssayParetoTarget
  preparationTransformation : CommercialAssayParetoTarget
  exposureTranslation : CommercialAssayParetoTarget
  concentrationMatchedInteraction : CommercialAssayParetoTarget
  umbrellaEntourage : CommercialAssayParetoTarget

record CommercialAssayParetoStep : Set where
  constructor commercial-assay-pareto-step
  field
    priority : Nat
    target : CommercialAssayParetoTarget
    action : String
    pays : String
    dominatedUntil : String
open CommercialAssayParetoStep public

paidTerpeneStep : CommercialAssayParetoStep
paidTerpeneStep = commercial-assay-pareto-step
  0 quantitativeSameSampleTerpeneProfile
  "Wishart et al. Table 2 pays sample-labelled mg/g dry-weight abundance for multiple PubChem-resolved common terpenes"
  "same-sample quantitative terpene occurrence"
  "paid on this source surface"

nextCannabinoidStep : CommercialAssayParetoStep
nextCannabinoidStep = commercial-assay-pareto-step
  1 exactPerSampleCannabinoidVector
  "acquire the source's per-sample cannabinoid table/supporting data rather than substituting the across-six-sample mean"
  "same-sample cannabinoid + terpene vector needed for constituent interaction selection"
  "do not infer per-sample cannabinoid values from cultivar labels or summary statistics"

preparationStep : CommercialAssayParetoStep
preparationStep = commercial-assay-pareto-step
  2 preparationTransformation
  "model how the measured dry-flower composition changes under the actual preparation/administration route"
  "source composition -> administered composition"
  "exact per-sample constituent vector required first"

exposureStep : CommercialAssayParetoStep
exposureStep = commercial-assay-pareto-step
  3 exposureTranslation
  "pay dose, route, bioavailability, target-compartment concentration and time course"
  "administered composition -> physiological exposure"
  "dry-weight mg/g is not a receptor concentration"

interactionStep : CommercialAssayParetoStep
interactionStep = commercial-assay-pareto-step
  4 concentrationMatchedInteraction
  "compare physiologically justified constituent concentrations to an endpoint-indexed interaction assay with an explicit additive/null comparator"
  "mechanism-specific interaction discriminator"
  "exposure translation required"

umbrellaStep : CommercialAssayParetoStep
umbrellaStep = commercial-assay-pareto-step
  9 umbrellaEntourage
  "do not promote an umbrella entourage effect from composition alone"
  "nothing"
  "dominated by constituent-specific interaction and exposure payments"

------------------------------------------------------------------------
-- Firewalls and parent receipts.
------------------------------------------------------------------------

data CDBIdentifierIsPubChemCID : Set where
data MgPerGDryWeightIsReceptorConcentration : Set where
data VendorCultivarLabelIsGenotypeIdentity : Set where
data TechnicalReplicatesAreIndependentBiologicalReplicates : Set where
data CoOccurrenceCreatesSynergy : Set where
data SummaryMeanCreatesPerSampleVector : Set where

cdbIdentifierDoesNotBecomePubChemCID : CDBIdentifierIsPubChemCID → ⊥
cdbIdentifierDoesNotBecomePubChemCID ()

mgPerGDryWeightDoesNotBecomeReceptorConcentration : MgPerGDryWeightIsReceptorConcentration → ⊥
mgPerGDryWeightDoesNotBecomeReceptorConcentration ()

vendorLabelDoesNotCreateGenotypeIdentity : VendorCultivarLabelIsGenotypeIdentity → ⊥
vendorLabelDoesNotCreateGenotypeIdentity ()

technicalReplicatesDoNotCreateIndependentBiologicalReplicates : TechnicalReplicatesAreIndependentBiologicalReplicates → ⊥
technicalReplicatesDoNotCreateIndependentBiologicalReplicates ()

coOccurrenceDoesNotCreateSynergy : CoOccurrenceCreatesSynergy → ⊥
coOccurrenceDoesNotCreateSynergy ()

summaryMeanDoesNotCreatePerSampleVector : SummaryMeanCreatesPerSampleVector → ⊥
summaryMeanDoesNotCreatePerSampleVector ()

pubChemBoundary : PubChem.PubChemCIDAuthorityBoundary
pubChemBoundary = PubChem.canonicalPubChemCIDAuthorityBoundary

compositionBoundary : Composition.CannabisTerpeneCompositionBoundary
compositionBoundary = Composition.canonicalCannabisTerpeneCompositionBoundary

record CommercialCannabisQuantitativeAssayBoundary : Set where
  constructor commercial-cannabis-quantitative-assay-boundary
  field
    primaryQuantitativeSourceRetained : Bool
    pubChemOwnsCID : Bool
    cdbAndPubChemIdentifiersSeparated : Bool
    sampleLabelsRemainSampleLabels : Bool
    technicalAndBiologicalReplicationSeparated : Bool
    dryWeightAndExposureConcentrationsSeparated : Bool
    sameSampleTerpeneOccurrencePaid : Bool
    exactPerSampleCannabinoidVectorPaid : Bool
    interactionPaid : Bool
    clinicalEffectPaid : Bool
open CommercialCannabisQuantitativeAssayBoundary public

canonicalCommercialCannabisQuantitativeAssayBoundary : CommercialCannabisQuantitativeAssayBoundary
canonicalCommercialCannabisQuantitativeAssayBoundary =
  commercial-cannabis-quantitative-assay-boundary
    true true true true true true true false false false
