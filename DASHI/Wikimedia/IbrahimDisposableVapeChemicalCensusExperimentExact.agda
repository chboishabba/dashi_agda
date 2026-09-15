module DASHI.Wikimedia.IbrahimDisposableVapeChemicalCensusExperimentExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimDisposableVapeUnknownIngredientFibreExact as Fibre

------------------------------------------------------------------------
-- CHEMICAL-CENSUS EXPERIMENT
--
-- Goal: answer the broad consumer the user actually cares about:
--   "what is really in a disposable nicotine vape, including undeclared and
--    newly formed chemistry, across the life of the device?"
--
-- This is not reducible to a banned-ingredient checklist.
------------------------------------------------------------------------

data CensusStage : Set where
  unopenedDevice
  virginLiquid
  earlyLifeAerosol
  midLifeLiquid
  midLifeAerosol
  lateLifeLiquid
  lateLifeAerosol
  spentDeviceMaterials : CensusStage

record ProductIdentity : Set where
  constructor product-identity
  field
    specimenId : String
    brand : String
    model : String
    labelledFlavor : String
    labelledNicotine : String
    batchOrLot : String
    acquisitionChannel : String
    jurisdiction : String
    packagePhotoReceipt : String
open ProductIdentity public

record ChemicalCensusArm : Set where
  constructor chemical-census-arm
  field
    stage : CensusStage
    destructiveSample : Bool
    targetedLiquid : Bool
    nonTargetLiquid : Bool
    targetedAerosol : Bool
    nonTargetAerosol : Bool
    metalsAndMaterials : Bool
    notes : String
open ChemicalCensusArm public

virginArm : ChemicalCensusArm
virginArm = chemical-census-arm virginLiquid true true true false false false
  "quantitative PG/VG, nicotine, acids, coolants, flavours, prohibited ingredients plus reproducible non-target feature map"

earlyAerosolArm : ChemicalCensusArm
earlyAerosolArm = chemical-census-arm earlyLifeAerosol false false false true true true
  "paired particle/gas aerosol: target carbonyls/nicotine/coolants/metals plus non-target GC-MS/LC-HRMS"

midLifeLiquidArm : ChemicalCensusArm
midLifeLiquidArm = chemical-census-arm midLifeLiquid true true true false false false
  "test whether reservoir chemistry drifts after controlled puff exposure"

midLifeAerosolArm : ChemicalCensusArm
midLifeAerosolArm = chemical-census-arm midLifeAerosol false false false true true true
  "repeat emitted chemical census at predeclared life fraction"

lateLifeLiquidArm : ChemicalCensusArm
lateLifeLiquidArm = chemical-census-arm lateLifeLiquid true true true false false false
  "late reservoir chemistry before depletion/dry-hit exclusion boundary"

lateLifeAerosolArm : ChemicalCensusArm
lateLifeAerosolArm = chemical-census-arm lateLifeAerosol false false false true true true
  "repeat emitted chemical census late in device life; retain coil/material state"

spentMaterialsArm : ChemicalCensusArm
spentMaterialsArm = chemical-census-arm spentDeviceMaterials true false false false false true
  "coil, wick, solder/joints, reservoir-contact metals/polymers and corrosion state"

------------------------------------------------------------------------
-- ACQUISITION PRECEDENTS
------------------------------------------------------------------------

record CensusPrecedent : Set where
  constructor census-precedent
  field
    sourceLabel : String
    doi : String
    scope : String
    supports : String
    doesNotSupport : String
open CensusPrecedent public

nswUnknownPeaksPrecedent : CensusPrecedent
nswUnknownPeaksPrecedent = census-precedent
  "Chemical Analysis and Flavor Distribution of Electronic Cigarettes in Australian Schools"
  "10.1093/ntr/ntae262"
  "410 chemically analysed NSW school-confiscated products"
  "targeted quantitative chemistry plus retention of NIST-library candidate peaks; acetals and prohibited compounds demonstrate off-label chemistry"
  "not a whole-aerosol non-target life-cycle census"

commercialLandscape2021 : CensusPrecedent
commercialLandscape2021 = census-precedent
  "Characterizing the Chemical Landscape in Commercial E-Cigarette Liquids and Aerosols by LC-HRMS"
  "10.1021/acs.chemrestox.1c00253"
  "four commercial products including a disposable; paired liquids and generated aerosols"
  "non-target LC-HRMS can reveal additional aerosol compounds, homologous decomposition series and unexpected additives/contaminants such as caffeine and tributylphosphine oxide"
  "not a large modern disposable-bar brand survey and not an Australian illicit-market census"

juulNonTargetPrecedent : CensusPrecedent
juulNonTargetPrecedent = census-precedent
  "Non-Targeted Chemical Characterization of JUUL Virginia Tobacco Flavored Aerosols"
  "10.3390/separations8090130"
  "paired GC-MS / LC-HRMS aerosol characterization across puffing regimens"
  "explicit categories for flavourants, HPHCs, extractables/leachables, reaction products and compounds that could not be identified or rationalized"
  "not a disposable-bar whole-life study"

newUsedDisposablePrecedent : CensusPrecedent
newUsedDisposablePrecedent = census-precedent
  "Disposable electronic cigarettes: Chemical composition in new and used devices"
  "10.1016/j.chroma.2025.466178"
  "60 disposable e-cigarettes across seven UK brands including Elfbar and Lost Mary"
  "new-versus-used liquid chemistry and successive-use-cycle changes; ethyl maltol and benzoic acid commonly present and concentrations can shift during use"
  "not paired non-target aerosol chemistry and not an Australian sample"

popularBars2025 : CensusPrecedent
popularBars2025 = census-precedent
  "E-Liquid and Aerosol Characterization of Popular Disposable E-Cigarettes"
  "10.1021/acsomega.5c03167"
  "25 Flum Pebble, Elf Bar, Esco Bars and Geek Bar products"
  "liquid nicotine/acids/flavours/coolants plus emitted aerosol carbonyls; product/device formulation affects emissions"
  "not a full untargeted chemical census"

------------------------------------------------------------------------
-- DISCOVERY LEDGER
------------------------------------------------------------------------

record FeatureLedger : Set where
  constructor feature-ledger
  field
    specimenId : String
    stage : CensusStage
    featureKey : String
    retentionOrMobility : String
    accurateMassOrSpectrum : String
    blankSubtracted : Bool
    reproducibleAcrossReplicates : Bool
    identityStatus : Fibre.ChemicalStatus
    identityText : String
    confidence : String
    quantitativeStatus : String
    sameFeatureAcrossStagesPaid : Bool
open FeatureLedger public

record ConfirmationLadder : Set where
  constructor confirmation-ladder
  field
    level0 : String
    level1 : String
    level2 : String
    level3 : String
    level4 : String
open ConfirmationLadder public

canonicalConfirmationLadder : ConfirmationLadder
canonicalConfirmationLadder = confirmation-ladder
  "L0 reproducible blank-subtracted feature only"
  "L1 formula / spectral-library / exact-mass candidate"
  "L2 orthogonal MS/MS or retention-index support"
  "L3 authentic-standard retention + spectrum match"
  "L4 quantitative calibration / recovery in the actual matrix"

------------------------------------------------------------------------
-- CROSS-STAGE RESIDUALS
------------------------------------------------------------------------

record CensusResidual : Set where
  constructor census-residual
  field
    name : String
    definition : String
    scientificQuestion : String
open CensusResidual public

labelResidual : CensusResidual
labelResidual = census-residual
  "R_label"
  "measured virgin-liquid inventory minus declared ingredient inventory"
  "what is present but undeclared, and what is declared but not confirmed?"

agingResidual : CensusResidual
agingResidual = census-residual
  "R_age"
  "mid/late liquid feature map minus virgin-liquid feature map after matched normalization"
  "what appears/disappears/concentrates during device use?"

aerosolFormationResidual : CensusResidual
aerosolFormationResidual = census-residual
  "R_emit"
  "emitted aerosol feature map minus source-liquid feature map, preserving phase and device-material attribution"
  "which chemicals are generated, enriched, depleted or device-derived during aerosolization?"

lifeCycleResidual : CensusResidual
lifeCycleResidual = census-residual
  "R_life"
  "late-life aerosol inventory minus early-life aerosol inventory from same product identity"
  "does exposure change as the disposable ages?"

------------------------------------------------------------------------
-- SAMPLE DESIGN
------------------------------------------------------------------------

record CensusSamplingFrame : Set where
  constructor census-sampling-frame
  field
    australianIllicitOrConfiscatedStratum : String
    pharmacyTherapeuticStratum : String
    internationalBarBrandStratum : String
    minimumIndependentUnitsPerProduct : Nat
    sameModelFlavorMultipleLots : Bool
    duplicateBrandModelNotSameBiologicalOrManufacturingReplicate : Bool
open CensusSamplingFrame public

canonicalSamplingFrame : CensusSamplingFrame
canonicalSamplingFrame = census-sampling-frame
  "IGET / HQD / Gunnpod and other currently encountered confiscated/illicit Australian disposables, exact specimen identity retained"
  "current Australian therapeutic/pharmacy products sampled separately; legal channel cannot be merged with illicit channel"
  "Elf Bar / Geek Bar / Lost Mary / Flum / Esco or successor products for external comparability, only if exact current products acquired"
  3 true true

------------------------------------------------------------------------
-- STOP / ESCALATE RULE
------------------------------------------------------------------------

record CensusEscalationPolicy : Set where
  constructor census-escalation-policy
  field
    cheapestFirst : String
    escalateWhen : String
    confirmationPriority : String
    stopWhen : String
open CensusEscalationPolicy public

canonicalCensusEscalation : CensusEscalationPolicy
canonicalCensusEscalation = census-escalation-policy
  "begin with label audit + broad targeted virgin-liquid screen"
  "run non-target liquid/aerosol whenever off-panel or stage-dependent chemical inventory matters to the declared consumer"
  "prioritize confirmation by abundance, reproducibility, aerosol-only emergence, toxicological plausibility and cross-product recurrence; do not discard low-confidence features"
  "stop only when the declared consumer is adequate for the requested scope; never reinterpret a finite analytical window as complete chemistry"

------------------------------------------------------------------------
-- HARD FIREWALLS
------------------------------------------------------------------------

data FiniteMethodsCreateCompleteChemistry : Set where
data UnidentifiedFeatureCreatesNoExposure : Set where
data SameNominalFlavorCreatesSameComposition : Set where
data SameBrandCreatesSameBatch : Set where
data OralFoodLimitCreatesInhalationLimit : Set where
data AbundanceCreatesToxicity : Set where
data UnknownCreatesDanger : Set where

finiteMethodsNotComplete : FiniteMethodsCreateCompleteChemistry → ⊥
finiteMethodsNotComplete ()

unidentifiedNotNoExposure : UnidentifiedFeatureCreatesNoExposure → ⊥
unidentifiedNotNoExposure ()

flavorNotSameComposition : SameNominalFlavorCreatesSameComposition → ⊥
flavorNotSameComposition ()

brandNotSameBatch : SameBrandCreatesSameBatch → ⊥
brandNotSameBatch ()

foodLimitNotInhalationLimit : OralFoodLimitCreatesInhalationLimit → ⊥
foodLimitNotInhalationLimit ()

abundanceNotToxicity : AbundanceCreatesToxicity → ⊥
abundanceNotToxicity ()

unknownNotDanger : UnknownCreatesDanger → ⊥
unknownNotDanger ()

record ChemicalCensusBoundary : Set where
  constructor chemical-census-boundary
  field
    targetedLiquidPrecedentPaid : Bool
    nonTargetLiquidAerosolPrecedentPaid : Bool
    newUsedDisposablePrecedentPaid : Bool
    australianBroadLiquidStudyPaid : Bool
    australianWholeLifeNonTargetAerosolStudyPaid : Bool
    exactCurrentProductSpecimensPaid : Bool
    completeChemistryPaid : Bool
    inhalationToxicologyForEveryFeaturePaid : Bool
open ChemicalCensusBoundary public

canonicalChemicalCensusBoundary : ChemicalCensusBoundary
canonicalChemicalCensusBoundary = chemical-census-boundary
  true true true true false false false false
