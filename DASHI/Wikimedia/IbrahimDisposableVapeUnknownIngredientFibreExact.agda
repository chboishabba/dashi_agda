module DASHI.Wikimedia.IbrahimDisposableVapeUnknownIngredientFibreExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- DISPOSABLE-VAPE DECLARED / OBSERVED / UNKNOWN INGREDIENT FIBRE
--
-- The consumer here is not a fixed banned-ingredient checklist.  It is the
-- chemical universe carried from label -> virgin liquid -> aged liquid ->
-- device materials -> emitted aerosol, with unidentified features retained.
------------------------------------------------------------------------

data ChemicalStatus : Set where
  declared : ChemicalStatus
  confirmedTarget : ChemicalStatus
  confirmedNonTarget : ChemicalStatus
  tentativeLibraryMatch : ChemicalStatus
  reactionProduct : ChemicalStatus
  deviceDerived : ChemicalStatus
  unresolvedFeature : ChemicalStatus

data CarrierStage : Set where
  packageLabel : CarrierStage
  virginLiquid : CarrierStage
  agedLiquid : CarrierStage
  deviceMaterial : CarrierStage
  emittedParticlePhase : CarrierStage
  emittedGasPhase : CarrierStage

data ChemicalRole : Set where
  carrierSolvent : ChemicalRole
  nicotineOrSaltAcid : ChemicalRole
  flavourant : ChemicalRole
  coolant : ChemicalRole
  sweetener : ChemicalRole
  prohibitedIngredient : ChemicalRole
  extractableLeachable : ChemicalRole
  thermalOrStorageProduct : ChemicalRole
  metalOrMetalloid : ChemicalRole
  unknownRole : ChemicalRole

record ChemicalFeature : Set where
  constructor chemical-feature
  field
    featureId : String
    status : ChemicalStatus
    stage : CarrierStage
    role : ChemicalRole
    identity : String
    concentrationOrYield : String
    confidence : String
    sourceReference : String
    inhalationSafetyPaid : Bool
open ChemicalFeature public

------------------------------------------------------------------------
-- SOURCE-BOUNDED ACQUISITION RECEIPTS
------------------------------------------------------------------------

record StudyReceipt : Set where
  constructor study-receipt
  field
    sourceLabel : String
    doi : String
    productScope : String
    observer : String
    principalFinding : String
    targetedOnly : Bool
    aerosolMeasured : Bool
open StudyReceipt public

popularDisposable2025 : StudyReceipt
popularDisposable2025 = study-receipt
  "Robertson et al. E-Liquid and Aerosol Characterization of Popular Disposable E-Cigarettes"
  "10.1021/acsomega.5c03167"
  "25 Flum Pebble / Elf Bar / Esco Bars / Geek Bar products"
  "GC/MS plus LC accurate-mass analysis of liquid; generated-aerosol mass and carbonyls"
  "nicotine labels frequently disagreed with assay; benzoic/levulinic acids, WS-23/WS-3 and numerous flavourants were present; aerosol carbonyl yield depended on formulation and device"
  true true

nswSchools2025 : StudyReceipt
nswSchools2025 = study-receipt
  "Chemical Analysis and Flavor Distribution of Electronic Cigarettes in Australian Schools"
  "10.1093/ntr/ntae262"
  "598 confiscated NSW school products; 410 chemically analysed, mainly IGET/HQD/Gunnpod disposables"
  "targeted GC-MS for nicotine, coolants, flavour chemicals and prohibited ingredients plus NIST-library matching of unknown peaks"
  "97.3% of disposables contained nicotine; WS-23 in 99.5%; prohibited compounds in 3.4%; PG/VG acetals observed; unconfirmed library-matched unknown peaks were retained separately"
  false false

contrabandAustralia2024 : StudyReceipt
contrabandAustralia2024 = study-receipt
  "Labelling and composition of contraband electronic cigarettes: Analysis of products from Australia"
  "10.1016/j.drugpo.2024.104471"
  "428 confiscated NSW disposable/pod products"
  "packaging audit plus chemical composition against Australian product requirements"
  "98.8% contained nicotine, most above 30 mg/mL, while packaging commonly omitted nicotine; 4.2% contained at least one prohibited compound"
  true false

juulVirginiaNonTarget : StudyReceipt
juulVirginiaNonTarget = study-receipt
  "Non-Targeted Chemical Characterization of JUUL Virginia Tobacco Flavored Aerosols"
  "10.3390/separations8090130"
  "JUUL Virginia Tobacco aerosol under intense and non-intense puffing"
  "GC-MS plus LC-HRMS non-targeted aerosol characterization"
  "roughly 69-85 compounds were identified per formulation/regimen; reaction products were the largest class by count, with additional flavourants, HPHCs, leachables and unresolved/rationalization failures"
  false true

juulMentholNonTarget : StudyReceipt
juulMentholNonTarget = study-receipt
  "Non-Targeted Chemical Characterization of JUUL Menthol-Flavored Aerosols"
  "10.3390/separations9110367"
  "JUUL Menthol aerosol across nicotine strengths and puffing regimens"
  "GC-MS plus LC-HRMS with non-targeted identification and semi-quantification"
  "aerosol constituents were partitioned into flavourants, HPHCs, leachables, reaction products and unable-to-identify/rationalize features"
  false true

newUsedDisposable2025 : StudyReceipt
newUsedDisposable2025 = study-receipt
  "Disposable electronic cigarettes: Chemical composition in new and used devices"
  "10.1016/j.chroma.2025.466178"
  "60 disposable e-cigarettes across brands/flavours/nicotine contents"
  "HS-GC-MS over successive usage cycles"
  "more than 15 flavourings occurred across liquids; ethyl maltol and benzoic acid were common and some concentrations exceeded the paper's cited concern thresholds; chemistry changed across use cycles"
  false false

------------------------------------------------------------------------
-- CHEMICAL-UNIVERSE PARTITION
------------------------------------------------------------------------

record ChemicalUniversePartition : Set where
  constructor chemical-universe-partition
  field
    declaredSet : String
    confirmedTargetSet : String
    confirmedNonTargetSet : String
    tentativeSet : String
    reactionProductSet : String
    deviceDerivedSet : String
    unresolvedFeatureSet : String
    unionInterpretation : String
open ChemicalUniversePartition public

canonicalChemicalUniversePartition : ChemicalUniversePartition
canonicalChemicalUniversePartition = chemical-universe-partition
  "packaging / manufacturer declarations, often incomplete in illicit-market products"
  "predeclared analytes with authentic standards and quantitative calibration"
  "unexpected compounds confirmed after discovery using orthogonal evidence / authentic standards"
  "library or accurate-mass candidates not yet chemically confirmed"
  "new compounds formed by storage, solvent-flavour reactions or heating"
  "metals, polymers, additives, leachables or corrosion products contributed by the device"
  "chromatographic / accurate-mass features that remain unidentified"
  "the experimentally observed chemical universe is the union of these evidence-status sets, not just the declared or targeted subset"

------------------------------------------------------------------------
-- IMPORTANT EXEMPLARS
------------------------------------------------------------------------

ws23Feature : ChemicalFeature
ws23Feature = chemical-feature
  "AUS-WS23"
  confirmedTarget virginLiquid coolant "WS-23"
  "NSW school study: detected in 405 samples; mean reported 14.20 mg/mL among the analysed disposable set"
  "authentic-standard targeted GC-MS"
  "10.1093/ntr/ntae262"
  false

ethyleneGlycolFeature : ChemicalFeature
ethyleneGlycolFeature = chemical-feature
  "AUS-EG"
  confirmedTarget virginLiquid prohibitedIngredient "ethylene glycol"
  "observed up to 13.2 mg/mL in the NSW school study"
  "authentic-standard targeted GC-MS"
  "10.1093/ntr/ntae262"
  false

vanillinAcetalFeature : ChemicalFeature
vanillinAcetalFeature = chemical-feature
  "AUS-VAN-ACETAL"
  reactionProduct virginLiquid thermalOrStorageProduct "vanillin PG/VG acetal(s)"
  "detected in a minority of school-confiscated products together with precursor flavour molecule"
  "in-house synthesized-acetal retention time / mass-spectrum comparison"
  "10.1093/ntr/ntae262"
  false

unresolvedPeakFeature : ChemicalFeature
unresolvedPeakFeature = chemical-feature
  "AUS-UNKNOWN-PEAK"
  unresolvedFeature virginLiquid unknownRole "unidentified GC-MS feature"
  "not assigned a quantitative identity"
  "retain even if NIST library candidate exists until confirmed against stronger evidence"
  "10.1093/ntr/ntae262"
  false

juulReactionProductFeature : ChemicalFeature
juulReactionProductFeature = chemical-feature
  "NT-REACTION-CLASS"
  reactionProduct emittedParticlePhase thermalOrStorageProduct "non-target aerosol reaction-product class"
  "reaction products were the largest constituent class by count in JUUL Virginia Tobacco non-target characterization"
  "GC-MS + LC-HRMS non-target workflow"
  "10.3390/separations8090130"
  false

------------------------------------------------------------------------
-- OBSERVER COLLISIONS
------------------------------------------------------------------------

record VapeObserverCollision : Set where
  constructor vape-observer-collision
  field
    consumer : String
    coarseObserver : String
    worldA : String
    worldB : String
    sameCoarseObservation : Bool
    differentConsumerAnswer : Bool
    missingCoordinate : String
open VapeObserverCollision public

labelCollision : VapeObserverCollision
labelCollision = vape-observer-collision
  "actual liquid composition"
  "package/device label"
  "nicotine undeclared but present"
  "nicotine genuinely absent"
  true true
  "direct chemical assay"

targetPanelCollision : VapeObserverCollision
targetPanelCollision = vape-observer-collision
  "whole chemical inventory"
  "fixed targeted panel"
  "no off-panel chemicals"
  "additional off-panel flavourant/leachable/reaction product exists"
  true true
  "non-target analytical feature map"

liquidAerosolCollision : VapeObserverCollision
liquidAerosolCollision = vape-observer-collision
  "inhaled aerosol composition"
  "virgin-liquid assay"
  "device emits only carried liquid constituents"
  "heating/device interaction creates new reaction product or leachable"
  true true
  "generated-aerosol targeted + non-target analysis"

lifeCycleCollision : VapeObserverCollision
lifeCycleCollision = vape-observer-collision
  "whole-device-life exposure"
  "new-device liquid and early aerosol only"
  "composition stable through device life"
  "aged liquid / coil degradation / device leaching changes later emissions"
  true true
  "early/mid/late-life repeated liquid + aerosol observation"

------------------------------------------------------------------------
-- EXPERIMENT LADDER
------------------------------------------------------------------------

record DiscoveryExperiment : Set where
  constructor discovery-experiment
  field
    experimentId : String
    declaredConsumer : String
    targetLayer : String
    methods : String
    requiredControls : String
    admissionRule : String
    burdenRank : Nat
open DiscoveryExperiment public

e0LabelAudit : DiscoveryExperiment
e0LabelAudit = discovery-experiment
  "E0" "declaration mismatch" "packaging versus direct nicotine / major-solvent assay"
  "label transcription + targeted assay"
  "reference standards; duplicate assay"
  "only answers declared-versus-measured coordinates"
  0

e1TargetedLiquid : DiscoveryExperiment
e1TargetedLiquid = discovery-experiment
  "E1" "known ingredient burden" "virgin liquid"
  "quantitative GC-MS / LC-MS targeted panel for PG/VG, nicotine, organic acids, known coolants, known flavourants, prohibited ingredients"
  "blanks, spikes, authentic standards, LOD/LOQ and recovery"
  "non-detection is limited to the declared target panel"
  1

e2NonTargetLiquid : DiscoveryExperiment
e2NonTargetLiquid = discovery-experiment
  "E2" "unknown liquid composition" "virgin + aged liquid"
  "GC-MS plus LC-HRMS non-target acquisition, deconvolution, feature alignment, exact-mass / spectral-library annotation"
  "solvent/device blanks, pooled QC, batch randomisation, isotopic/internal standards where applicable"
  "retain every reproducible feature; report confirmed, tentative and unidentified counts separately"
  2

e3TargetedAerosol : DiscoveryExperiment
e3TargetedAerosol = discovery-experiment
  "E3" "known emitted toxicant/additive burden" "generated aerosol across device life"
  "targeted carbonyls, nicotine, acids, selected flavourants/coolants, metals and other predeclared constituents"
  "machine-puff metadata; aerosol blanks; early/mid/late-life blocks"
  "liquid concentration cannot substitute for emitted yield"
  3

e4NonTargetAerosol : DiscoveryExperiment
e4NonTargetAerosol = discovery-experiment
  "E4" "whole emitted chemical universe" "particle + gas aerosol across device life"
  "paired GC-MS / LC-HRMS non-target aerosol plus metals/materials characterization"
  "procedural blanks, device blanks, pooled QC, retention-time and accurate-mass alignment, confirmation subset"
  "unidentified reproducible features remain in the evidence fibre instead of being discarded"
  4

------------------------------------------------------------------------
-- HARD FIREWALLS
------------------------------------------------------------------------

data LabelCreatesComposition : Set where
data TargetPanelCreatesChemicalUniverse : Set where
data TentativeLibraryMatchCreatesConfirmedIdentity : Set where
data LiquidCreatesAerosolIdentity : Set where
data VirginDeviceCreatesWholeLifeComposition : Set where
data UnknownPeakCreatesZeroRisk : Set where
data FoodSafeCreatesInhalationSafe : Set where

labelNotComposition : LabelCreatesComposition → ⊥
labelNotComposition ()

targetPanelNotUniverse : TargetPanelCreatesChemicalUniverse → ⊥
targetPanelNotUniverse ()

tentativeNotConfirmed : TentativeLibraryMatchCreatesConfirmedIdentity → ⊥
tentativeNotConfirmed ()

liquidNotAerosol : LiquidCreatesAerosolIdentity → ⊥
liquidNotAerosol ()

virginNotWholeLife : VirginDeviceCreatesWholeLifeComposition → ⊥
virginNotWholeLife ()

unknownNotZeroRisk : UnknownPeakCreatesZeroRisk → ⊥
unknownNotZeroRisk ()

foodSafeNotInhalationSafe : FoodSafeCreatesInhalationSafe → ⊥
foodSafeNotInhalationSafe ()

record UnknownIngredientBoundary : Set where
  constructor unknown-ingredient-boundary
  field
    australianLabelMismatchPaid : Bool
    targetedIngredientDiversityPaid : Bool
    reactionProductsPaid : Bool
    nonTargetAerosolPrecedentPaid : Bool
    unresolvedFeaturesRetained : Bool
    agedDeviceCoordinateRequired : Bool
    fullAustralianDisposableNonTargetAerosolSurveyPaid : Bool
    completeChemicalUniversePaid : Bool
    humanDosePaid : Bool
open UnknownIngredientBoundary public

canonicalUnknownIngredientBoundary : UnknownIngredientBoundary
canonicalUnknownIngredientBoundary = unknown-ingredient-boundary
  true true true true true true false false false
