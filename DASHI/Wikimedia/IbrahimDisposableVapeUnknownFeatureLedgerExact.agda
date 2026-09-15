module DASHI.Wikimedia.IbrahimDisposableVapeUnknownFeatureLedgerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimDisposableVapeUnknownIngredientFibreExact as Fibre
import DASHI.Wikimedia.IbrahimDisposableVapeChemicalCensusExperimentExact as Census

------------------------------------------------------------------------
-- PURPOSE
--
-- Turn the broad chemical-census design into an explicit unknown-feature
-- ledger.  The unit of evidence is a stage-indexed analytical feature with
-- bounded identity confidence, not an informal ingredient name.
------------------------------------------------------------------------

data IdentityGrade : Set where
  featureOnly
  libraryCandidate
  orthogonalSupport
  standardConfirmed
  matrixQuantified : IdentityGrade

data OriginHypothesis : Set where
  formulationIngredient
  storageReaction
  thermalReaction
  deviceLeachable
  concentrationByDepletion
  unresolvedOrigin : OriginHypothesis

record UnknownFeatureReceipt : Set where
  constructor unknown-feature-receipt
  field
    specimen : String
    stage : Census.CensusStage
    featureKey : String
    analyticalMode : String
    blankSubtracted : Bool
    replicateReproducible : Bool
    identityGrade : IdentityGrade
    identity : String
    origin : OriginHypothesis
    abundanceOrConcentration : String
    sameFeatureAcrossStagesPaid : Bool
    sourceBound : String
open UnknownFeatureReceipt public

------------------------------------------------------------------------
-- SOURCE-BOUNDED PRECEDENTS
------------------------------------------------------------------------

record SourceReceipt : Set where
  constructor source-receipt
  field
    sourceLabel : String
    doi : String
    sampleScope : String
    analyticalScope : String
    supportedClaim : String
    excludedPromotion : String
open SourceReceipt public

australiaWide2025 : SourceReceipt
australiaWide2025 = source-receipt
  "Jenkins, Morgan, Kelso 2025 Comparison of electronic cigarette chemical composition across Australia"
  "10.1071/CH25027"
  "47 products purchased from six Australian states/territories and multiple retailer types"
  "GC-MS liquid chemistry"
  "nicotine detected in 35/47 with mean 42.7 mg/mL; nicotine labelling usually absent/inaccurate; WS-23 and acetals common; cinnamaldehyde detected in two samples"
  "does not establish aerosol composition, national prevalence, or complete chemical inventory"

nswSchoolsUnknown2025 : SourceReceipt
nswSchoolsUnknown2025 = source-receipt
  "Jenkins et al. Chemical Analysis and Flavor Distribution of Electronic Cigarettes in Australian Schools"
  "10.1093/ntr/ntae262"
  "410 chemically analysed NSW confiscated products from a 598-product collection"
  "targeted GC-MS plus tentative NIST-library matching of unknown chromatographic peaks"
  "unknown peaks were retained and tentative matches listed separately; PG/VG flavour acetals demonstrate chemistry beyond nominal ingredients"
  "library match does not create confirmed identity and confiscated school products do not represent all Australian products"

commercialLandscape2021 : SourceReceipt
commercialLandscape2021 = source-receipt
  "Characterizing the Chemical Landscape in Commercial E-Cigarette Liquids and Aerosols by LC-HRMS"
  "10.1021/acs.chemrestox.1c00253"
  "four commercial products including one disposable"
  "paired e-liquid and aerosol LC-HRMS non-target chemical fingerprinting"
  "compound count increased from liquid to aerosol in three of four products; additional homologous/decomposition-like series and unexpected additives/contaminants including caffeine and tributylphosphine oxide were identified"
  "not a modern disposable-bar market census and not Australian"

flavourCarrierAdducts2023 : SourceReceipt
flavourCarrierAdducts2023 = source-receipt
  "A Wide Range of Flavoring-Carrier Fluid Adducts Form in E-Cigarette Liquids"
  "10.1021/acs.chemrestox.2c00200"
  "36 flavour molecules challenged with PG/VG or methanol plus 142 commercial e-liquids"
  "GC-MS reaction-product discovery and confirmation"
  "multiple flavour molecules formed PG/VG acetals/adducts under storage conditions; confirmed acetals occurred in 32% of analysed commercial liquids"
  "reaction possibility does not prove every product contains the corresponding adduct"

usedDisposables2025 : SourceReceipt
usedDisposables2025 = source-receipt
  "Pennington, Hernandez Aldave 2025 Disposable electronic cigarettes: Chemical composition in new and used devices"
  "10.1016/j.chroma.2025.466178"
  "60 disposable devices across seven brands including Elfbar and Lost Mary"
  "HS-GC-MS new versus used liquid chemistry"
  "ethyl maltol present in 89%, benzoic acid in 87%, and both showed concentration changes over successive use cycles including increases around 40-80 puffs"
  "not paired same-device non-target aerosol chemistry"

highPuff2026 : SourceReceipt
highPuff2026 = source-receipt
  "Omaiye et al. 2026 Methylglyoxal and Glyoxal in High-Puff Disposable Electronic Cigarette Liquids"
  "10.1021/acsomega.5c13033"
  "77 used devices from 20 brands; unvaped counterparts purchased for most products"
  "GC-MS targeting PG, glycerol, nicotine, 178 flavour chemicals, two coolants and nine aldehydes"
  "MGO, glyoxal and formaldehyde increased in vaped fluids; glyceraldehyde and dihydroxyacetone were detected only in vaped fluids; chemistry varied by brand/use state"
  "used and unvaped fluids were not paired same-device specimens, so this does not prove a longitudinal trajectory for one physical device"

popularBars2025 : SourceReceipt
popularBars2025 = source-receipt
  "Robertson et al. 2025 E-Liquid and Aerosol Characterization of Popular Disposable E-Cigarettes"
  "10.1021/acsomega.5c03167"
  "25 Flum Pebble, Elf Bar, Esco Bars and Geek Bar products"
  "liquid GC/MS + LC accurate-mass chemistry and generated-aerosol carbonyl measurements"
  "nicotine, organic acids, flavour/coolant composition and aerosol carbonyl formation vary by product/device"
  "targeted/semistructured chemistry does not create a complete unknown-feature census"

------------------------------------------------------------------------
-- FEATURE-STATE SEMANTICS
------------------------------------------------------------------------

record StageTransitionFeature : Set where
  constructor stage-transition-feature
  field
    featureKey : String
    fromStage : Census.CensusStage
    toStage : Census.CensusStage
    fromStatus : String
    toStatus : String
    transitionInterpretation : String
    identityPreservedAcrossTransitionPaid : Bool
open StageTransitionFeature public

benzaldehydeAcetalPattern : StageTransitionFeature
benzaldehydeAcetalPattern = stage-transition-feature
  "benzaldehyde-PG-acetal-pattern"
  Census.virginLiquid Census.virginLiquid
  "parent benzaldehyde may be undetected"
  "benzaldehyde-PG acetal observed"
  "reaction product can persist even when parent is below detection; source ingredient list alone is not a complete state description"
  false

usedOnlyAldehydePattern : StageTransitionFeature
usedOnlyAldehydePattern = stage-transition-feature
  "use-generated-aldehyde-pattern"
  Census.virginLiquid Census.lateLifeLiquid
  "glyceraldehyde/dihydroxyacetone not observed in unvaped comparison fluids"
  "detected in vaped fluids in the 2026 high-puff study"
  "compatible with use-associated formation/accumulation; same-device longitudinal causality remains unpaid"
  false

------------------------------------------------------------------------
-- UNKNOWN FEATURE QUEUE
------------------------------------------------------------------------

record FeatureQueuePolicy : Set where
  constructor feature-queue-policy
  field
    retainFeatureWhen : String
    prioritizeConfirmationWhen : String
    mergeAcrossStagesWhen : String
    splitAcrossStagesWhen : String
    discardOnlyWhen : String
open FeatureQueuePolicy public

canonicalFeatureQueuePolicy : FeatureQueuePolicy
canonicalFeatureQueuePolicy = feature-queue-policy
  "feature is blank-subtracted and reproducible, even if chemical identity is unresolved"
  "feature recurs across products, rises with use, appears only in aerosol/used liquid, is abundant, or has plausible toxicological/device-material relevance"
  "retention/mobility, accurate mass or spectrum and orthogonal evidence support same chemical object"
  "identity correspondence is unproven or multiple isomers/adducts remain possible"
  "feature is explained by blank/carryover/artifact under predeclared QC rules"

------------------------------------------------------------------------
-- SAME-DEVICE EXPERIMENT CLOSURE TARGET
------------------------------------------------------------------------

record SameDeviceCensusTarget : Set where
  constructor same-device-census-target
  field
    specimenUnit : String
    requiredStages : String
    liquidModes : String
    aerosolModes : String
    materialModes : String
    featureMatching : String
    stageResiduals : String
    currentPublicReceiptPaid : Bool
open SameDeviceCensusTarget public

canonicalSameDeviceCensusTarget : SameDeviceCensusTarget
canonicalSameDeviceCensusTarget = same-device-census-target
  "one physically identified disposable plus independent sibling units from same model/flavour/lot where available"
  "virgin liquid; early aerosol; mid-life liquid+aerosol; late-life liquid+aerosol; spent coil/wick/materials"
  "targeted quantitative GC/LC plus GC-HRMS/LC-HRMS non-target feature map"
  "gas/particle collection with targeted carbonyls/nicotine/coolants/metals plus non-target GC/LC-HRMS"
  "elemental/material analysis of coil, solder/joints, wick and reservoir-contact components"
  "stage-to-stage feature correspondence requires orthogonal identity evidence; exact-mass proximity alone is insufficient"
  "R_label, R_age, R_emit and R_life retained separately"
  false

------------------------------------------------------------------------
-- HARD FIREWALLS
------------------------------------------------------------------------

data UnknownMeansHarmless : Set where
data UnknownMeansHarmful : Set where
data LibraryMatchCreatesIdentity : Set where
data UsedVersusNewCrossSectionCreatesSameDeviceTrajectory : Set where
data AbsenceInLiquidCreatesAbsenceInAerosol : Set where
data TargetedPanelCreatesCompleteInventory : Set where

unknownNotHarmless : UnknownMeansHarmless → ⊥
unknownNotHarmless ()

unknownNotHarmful : UnknownMeansHarmful → ⊥
unknownNotHarmful ()

libraryMatchNotIdentity : LibraryMatchCreatesIdentity → ⊥
libraryMatchNotIdentity ()

crossSectionNotSameDeviceTrajectory : UsedVersusNewCrossSectionCreatesSameDeviceTrajectory → ⊥
crossSectionNotSameDeviceTrajectory ()

liquidAbsenceNotAerosolAbsence : AbsenceInLiquidCreatesAbsenceInAerosol → ⊥
liquidAbsenceNotAerosolAbsence ()

targetedPanelNotComplete : TargetedPanelCreatesCompleteInventory → ⊥
targetedPanelNotComplete ()

record UnknownFeatureBoundary : Set where
  constructor unknown-feature-boundary
  field
    australiaWideLiquidReceiptPaid : Bool
    unknownFeatureRetentionPaid : Bool
    reactionProductReceiptPaid : Bool
    usedHighPuffReceiptPaid : Bool
    pairedLiquidAerosolNonTargetReceiptPaid : Bool
    sameDeviceLongitudinalNonTargetReceiptPaid : Bool
    completeChemicalUniversePaid : Bool
open UnknownFeatureBoundary public

canonicalUnknownFeatureBoundary : UnknownFeatureBoundary
canonicalUnknownFeatureBoundary = unknown-feature-boundary
  true true true true true false false
