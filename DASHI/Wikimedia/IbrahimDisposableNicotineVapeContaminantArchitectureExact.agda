module DASHI.Wikimedia.IbrahimDisposableNicotineVapeContaminantArchitectureExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- PURPOSE
--
-- Extend the contaminant/observer architecture from cannabis+tobacco smoke to
-- contemporary disposable nicotine vapes (Elf Bar / Geek Bar / Esco Bar /
-- Flum Pebble / Lost Mary / Australian illicit disposables).  Keep e-liquid,
-- device material, emitted aerosol, product-age and user-dose coordinates
-- distinct.  Product-level studies do not create class-wide guarantees.
------------------------------------------------------------------------

data VapeObservationLayer : Set where
  labelAndDeclaredComposition
  virginELiquidComposition
  agedELiquidComposition
  deviceMaterialComposition
  emittedAerosolOrganicChemistry
  emittedAerosolElements
  productLifeCycle
  humanDose : VapeObservationLayer

record VapeStudyReceipt : Set where
  constructor vape-study-receipt
  field
    sourceLabel : String
    doi : String
    productClass : String
    sampleCount : Nat
    brands : String
    observationLayers : String
    keyFinding : String
    aerosolMeasured : Bool
    productSpecific : Bool
open VapeStudyReceipt public

robertson2025DisposableChemistry : VapeStudyReceipt
robertson2025DisposableChemistry = vape-study-receipt
  "Robertson et al. 2025 E-Liquid and Aerosol Characterization of Popular Disposable E-Cigarettes"
  "10.1021/acsomega.5c03167"
  "popular disposable nicotine e-cigarettes"
  25
  "Flum Pebble, Elf Bar, Esco Bars, Geek Bar"
  "e-liquid nicotine/acids/flavours/coolants plus generated aerosol mass and carbonyls"
  "nicotine label agreement and flavour/coolant burden varied substantially across products; aerosol carbonyl formation was product-dependent"
  true true

pinkerton2025ToxicElements : VapeStudyReceipt
pinkerton2025ToxicElements = vape-study-receipt
  "Elevated Toxic Element Emissions from Popular Disposable E-Cigarettes: Sources, Life Cycle, and Health Risks"
  "10.1021/acscentsci.5c00641"
  "disposable pod e-cigarettes"
  21
  "ELF Bar BC5000, Flum Pebble 6000, Esco Bar 2500"
  "device-component elemental composition; virgin/aged e-liquid; aerosol elements across product life"
  "Cr/Ni emissions often rose with device age; some products showed substantial Pb/Cu/Zn/Sb contamination; source components differed by product"
  true true

australiaContraband2024 : VapeStudyReceipt
australiaContraband2024 = vape-study-receipt
  "Labelling and composition of contraband electronic cigarettes: Analysis of products from Australia"
  "10.1016/j.drugpo.2024.104466"
  "NSW-confiscated disposable e-cigarettes and pods"
  428
  "multiple illicit-market products"
  "packaging plus e-liquid chemical composition"
  "98.8% contained nicotine; 89% were >30 mg/mL; 4.2% contained at least one TGO110-prohibited chemical"
  false true

australiaSchools2025 : VapeStudyReceipt
australiaSchools2025 = vape-study-receipt
  "Chemical Analysis and Flavor Distribution of Electronic Cigarettes in Australian Schools"
  "10.1093/ntr/ntae262"
  "school-confiscated e-cigarettes from NSW"
  410
  "mainly IGET, HQD and Gunnpod"
  "nicotine, coolants, flavour chemicals, prohibited ingredients"
  "97.3% of disposables contained nicotine with mean 40.0 mg/mL; WS-23 was widespread; prohibited chemicals were found in 3.4%"
  false true

record RegulatoryObserverReceipt : Set where
  constructor regulatory-observer-receipt
  field
    jurisdiction : String
    sourceLabel : String
    observerSurface : String
    aerosolContaminantPanelRequired : Bool
    routineMetalsInAerosolRequired : Bool
    nicotineContentObserved : Bool
open RegulatoryObserverReceipt public

australiaTherapeuticVapeObserver : RegulatoryObserverReceipt
australiaTherapeuticVapeObserver = regulatory-observer-receipt
  "Australia"
  "TGA TGO110 testing programme / 2025-2026 guidance"
  "nicotine identity/content, prohibited ingredient screen, labelling, plus strengthened ingredient/device standards"
  false false true

------------------------------------------------------------------------
-- Product-life collision: the same labelled product can expose a changing
-- aerosol as hardware ages.  Virgin e-liquid alone cannot answer the aerosol
-- consumer if coil/corrosion-derived emissions increase during use.
------------------------------------------------------------------------

record LifeCycleObserverCollision : Set where
  constructor life-cycle-observer-collision
  field
    coarseObserver : String
    worldA : String
    worldB : String
    sameCoarseObservation : Bool
    differentAerosolAnswer : Bool
    missingCoordinate : String
open LifeCycleObserverCollision public

metalAgeCollision : LifeCycleObserverCollision
metalAgeCollision = life-cycle-observer-collision
  "virgin e-liquid composition + label"
  "new device early in life"
  "same product later after coil/contact-material aging"
  true true
  "puff-indexed emitted-aerosol metals / device-life coordinate"

------------------------------------------------------------------------
-- Nicotine provenance collision: tobacco-derived versus synthetic nicotine is
-- not a sufficient clean/dirty classifier.  2026 impurity work found distinct
-- impurity burdens in both, including synthesis byproducts and nitrosamine-
-- related species.  The provenance coordinate is retained, but chemistry wins.
------------------------------------------------------------------------

data NicotineOrigin : Set where tobaccoDerived synthetic unresolved : NicotineOrigin

record NicotineFeedstockReceipt : Set where
  constructor nicotine-feedstock-receipt
  field
    sourceLabel : String
    doi : String
    comparison : String
    nonTargetImpuritiesObserved : Bool
    syntheticAutomaticallyCleaner : Bool
open NicotineFeedstockReceipt public

shin2026NicotineImpurities : NicotineFeedstockReceipt
shin2026NicotineImpurities = nicotine-feedstock-receipt
  "Identification and quantitative analysis of impurities in tobacco-derived and synthetic nicotine"
  "10.1016/j.jpba.2025.117221"
  "non-target plus quantitative comparison of tobacco-derived and synthetic nicotine impurities"
  true false

------------------------------------------------------------------------
-- Pesticide-specific state.
--
-- Current direct evidence is much thinner than for nicotine accuracy, flavour
-- chemicals, carbonyls or metals.  Queensland testing explicitly screened a
-- small market sample for pesticides/fungicides/herbicides, but current owner
-- does not promote that to a class-wide pesticide survey or aerosol result.
------------------------------------------------------------------------

record VapePesticideAcquisitionState : Set where
  constructor vape-pesticide-acquisition-state
  field
    directDisposableELiquidPesticideSurveyPaid : Bool
    directDisposableAerosolPesticideSurveyPaid : Bool
    australianGovernmentSmallSampleScreenLocated : Bool
    pesticideNonDetectionCreatesUniversalAbsence : Bool
    nextAcquisition : String
open VapePesticideAcquisitionState public

canonicalVapePesticideState : VapePesticideAcquisitionState
canonicalVapePesticideState = vape-pesticide-acquisition-state
  false false true false
  "acquire exact Queensland 17-sample analyte/results table; search nicotine-feedstock pesticide residues; then test paired virgin e-liquid and emitted aerosol in named bar products"

------------------------------------------------------------------------
-- HARD FIREWALLS
------------------------------------------------------------------------

data ELiquidCompositionCreatesAerosolComposition : Set where
data LabelCreatesELiquidTruth : Set where
data NewDeviceCreatesWholeLifeEmission : Set where
data OneBrandCreatesDisposableClass : Set where
data SyntheticNicotineCreatesPurity : Set where
data TherapeuticNotificationCreatesTGAApproval : Set where

liquidNotAerosol : ELiquidCompositionCreatesAerosolComposition → ⊥
liquidNotAerosol ()

labelNotTruth : LabelCreatesELiquidTruth → ⊥
labelNotTruth ()

newNotWholeLife : NewDeviceCreatesWholeLifeEmission → ⊥
newNotWholeLife ()

brandNotClass : OneBrandCreatesDisposableClass → ⊥
brandNotClass ()

syntheticNotPure : SyntheticNicotineCreatesPurity → ⊥
syntheticNotPure ()

notificationNotApproval : TherapeuticNotificationCreatesTGAApproval → ⊥
notificationNotApproval ()

------------------------------------------------------------------------
-- Experiment cross-pollination.
------------------------------------------------------------------------

record DisposableVapeExperimentLanguage : Set where
  constructor disposable-vape-experiment-language
  field
    sourceObject : String
    stageZero : String
    stageOne : String
    stageTwo : String
    stageThree : String
    escalationRule : String
open DisposableVapeExperimentLanguage public

canonicalDisposableVapeExperimentLanguage : DisposableVapeExperimentLanguage
canonicalDisposableVapeExperimentLanguage = disposable-vape-experiment-language
  "same named device + batch/lot where available, with virgin e-liquid aliquot and puff-indexed aerosol generated from that exact unit or matched same-lot units"
  "verify label, nicotine concentration, acids, flavours/coolants and prohibited ingredients"
  "measure virgin and aged e-liquid metals / non-target impurities"
  "measure emitted aerosol carbonyls + metals at early/mid/late life"
  "add targeted pesticide/feedstock impurity panel and non-target aerosol chemistry only where the declared consumer still has collisions"
  "do not escalate merely by adding analytes; escalate when the current observer cannot distinguish two worlds relevant to the consumer"

record DisposableVapeBoundary : Set where
  constructor disposable-vape-boundary
  field
    popularBrandELiquidEvidencePaid : Bool
    popularBrandAerosolCarbonylEvidencePaid : Bool
    popularBrandAerosolMetalEvidencePaid : Bool
    australianIllicitMarketCompositionPaid : Bool
    australianAerosolChemistryPaid : Bool
    directPesticideAerosolEvidencePaid : Bool
    productLifeCoordinateRequired : Bool
    liquidEqualsAerosol : Bool
open DisposableVapeBoundary public

canonicalDisposableVapeBoundary : DisposableVapeBoundary
canonicalDisposableVapeBoundary = disposable-vape-boundary
  true true true true false false true false
