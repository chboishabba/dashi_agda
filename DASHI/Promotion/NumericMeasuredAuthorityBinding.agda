module DASHI.Promotion.NumericMeasuredAuthorityBinding where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Level)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Constants.Registry as Registry
import DASHI.Promotion.NumericAndAuthorityObligations as Numeric

------------------------------------------------------------------------
-- Typed authority binding for measured numeric constants.
--
-- This module is not a numeric-value promotion.  It binds measured slots to
-- complete authority metadata and consumer lanes, while preserving the repo
-- guard that measured numeric values remain unpromoted until an accepted
-- authority token and value-ingestion receipt exist.

data MeasuredConstantFamily : Set where
  gravitationalFamily : MeasuredConstantFamily
  electromagneticFamily : MeasuredConstantFamily
  leptonMassFamily : MeasuredConstantFamily
  baryonMassFamily : MeasuredConstantFamily
  atomicSpectroscopyFamily : MeasuredConstantFamily
  electroweakFamily : MeasuredConstantFamily
  qcdCouplingFamily : MeasuredConstantFamily

data MeasuredAuthorityOwner : Set where
  codataMeasuredAuthority : MeasuredAuthorityOwner
  pdgMeasuredAuthority : MeasuredAuthorityOwner

data MeasuredConsumerLane : Set where
  grNormalizationConsumer : MeasuredConsumerLane
  maxwellElectromagneticConsumer : MeasuredConsumerLane
  quantumSchrodingerConsumer : MeasuredConsumerLane
  atomicChemistrySpectroscopyConsumer : MeasuredConsumerLane
  standardModelSectorConsumer : MeasuredConsumerLane
  yangMillsQCDConsumer : MeasuredConsumerLane

record MeasuredConstantSlot : Set₁ where
  field
    slotLabel : String
    symbol : String
    registrySlotName : String
    registryAuthority : String
    family : MeasuredConstantFamily
    authorityOwner : MeasuredAuthorityOwner
    unitConventionName : String
    validityRegimeName : String
    sourceRegistry : Registry.ConstantsRegistry
    sourceAuthorityPolicy : Registry.AuthorityConsumptionPolicyReceipt
    sourceNumericObligationIndex :
      Numeric.NumericAndAuthorityObligationIndex
    registrySlotIsMeasured : Bool
    registrySlotIsMeasuredIsTrue : registrySlotIsMeasured ≡ true
    notExactSIDefinition : Bool
    notExactSIDefinitionIsTrue : notExactSIDefinition ≡ true

open MeasuredConstantSlot public

mkMeasuredSlot :
  String →
  String →
  String →
  String →
  MeasuredConstantFamily →
  MeasuredAuthorityOwner →
  String →
  String →
  MeasuredConstantSlot
mkMeasuredSlot
  label sym registryName authority family owner unitConvention regime =
  record
    { slotLabel = label
    ; symbol = sym
    ; registrySlotName = registryName
    ; registryAuthority = authority
    ; family = family
    ; authorityOwner = owner
    ; unitConventionName = unitConvention
    ; validityRegimeName = regime
    ; sourceRegistry = Registry.repoWideConstantsRegistry
    ; sourceAuthorityPolicy =
        Registry.canonicalAuthorityConsumptionPolicyReceipt
    ; sourceNumericObligationIndex =
        Numeric.canonicalNumericAndAuthorityObligationIndex
    ; registrySlotIsMeasured = true
    ; registrySlotIsMeasuredIsTrue = refl
    ; notExactSIDefinition = true
    ; notExactSIDefinitionIsTrue = refl
    }

newtonianGSlot : MeasuredConstantSlot
newtonianGSlot =
  mkMeasuredSlot
    "Newtonian gravitational constant"
    "G"
    "DASHI.Constants.Registry.measuredPhysicsConstantAuthoritySlots.G"
    "NIST CODATA fundamental physical constants"
    gravitationalFamily
    codataMeasuredAuthority
    "SI m^3 kg^-1 s^-2"
    "weak-field gravity and GR normalization adapters"

fineStructureAlphaSlot : MeasuredConstantSlot
fineStructureAlphaSlot =
  mkMeasuredSlot
    "fine-structure constant"
    "alpha"
    "DASHI.Constants.Registry.measuredPhysicsConstantAuthoritySlots.alpha"
    "NIST CODATA fundamental physical constants"
    electromagneticFamily
    codataMeasuredAuthority
    "dimensionless electromagnetic coupling convention"
    "QED, atomic spectroscopy, and Standard Model sector adapters"

electronMassSlot : MeasuredConstantSlot
electronMassSlot =
  mkMeasuredSlot
    "electron rest mass"
    "m_e"
    "DASHI.Constants.Registry.measuredPhysicsConstantAuthoritySlots.m_e"
    "NIST CODATA fundamental physical constants"
    leptonMassFamily
    codataMeasuredAuthority
    "SI kg mass convention"
    "Schrodinger, atomic chemistry, and QED adapters"

protonMassSlot : MeasuredConstantSlot
protonMassSlot =
  mkMeasuredSlot
    "proton rest mass"
    "m_p"
    "DASHI.Constants.Registry.measuredPhysicsConstantAuthoritySlots.m_p"
    "NIST CODATA fundamental physical constants"
    baryonMassFamily
    codataMeasuredAuthority
    "SI kg mass convention"
    "chemistry, biology, nuclear, and particle adapters"

vacuumPermittivitySlot : MeasuredConstantSlot
vacuumPermittivitySlot =
  mkMeasuredSlot
    "vacuum permittivity"
    "epsilon_0"
    "DASHI.Constants.Registry.measuredPhysicsConstantAuthoritySlots.epsilon_0"
    "NIST CODATA fundamental physical constants"
    electromagneticFamily
    codataMeasuredAuthority
    "SI F m^-1 electromagnetic convention"
    "Maxwell, electrochemistry, and membrane electrophysiology adapters"

vacuumPermeabilitySlot : MeasuredConstantSlot
vacuumPermeabilitySlot =
  mkMeasuredSlot
    "vacuum permeability"
    "mu_0"
    "DASHI.Constants.Registry.measuredPhysicsConstantAuthoritySlots.mu_0"
    "NIST CODATA fundamental physical constants"
    electromagneticFamily
    codataMeasuredAuthority
    "SI N A^-2 electromagnetic convention"
    "Maxwell, QED, and electromagnetic unit adapters"

rydbergConstantSlot : MeasuredConstantSlot
rydbergConstantSlot =
  mkMeasuredSlot
    "Rydberg constant"
    "R_infinity"
    "DASHI.Constants.Registry.measuredPhysicsConstantAuthoritySlots.R_infinity"
    "NIST CODATA fundamental physical constants"
    atomicSpectroscopyFamily
    codataMeasuredAuthority
    "SI m^-1 wavenumber convention"
    "atomic physics, spectroscopy, and quantum chemistry adapters"

higgsMassSlot : MeasuredConstantSlot
higgsMassSlot =
  mkMeasuredSlot
    "Higgs boson mass"
    "m_H"
    "DASHI.Constants.Registry.measuredPhysicsConstantAuthoritySlots.m_H"
    "Particle Data Group particle data"
    electroweakFamily
    pdgMeasuredAuthority
    "GeV c^-2 particle-data mass convention"
    "Standard Model Higgs and electroweak symmetry-breaking adapters"

strongCouplingSlot : MeasuredConstantSlot
strongCouplingSlot =
  mkMeasuredSlot
    "strong coupling constant"
    "alpha_s"
    "DASHI.Constants.Registry.measuredPhysicsConstantAuthoritySlots.alpha_s"
    "Particle Data Group particle data"
    qcdCouplingFamily
    pdgMeasuredAuthority
    "dimensionless MSbar scale-dependent coupling convention"
    "QCD, Yang-Mills, and Standard Model sector adapters"

canonicalMeasuredConstantSlots : List MeasuredConstantSlot
canonicalMeasuredConstantSlots =
  newtonianGSlot
  ∷ fineStructureAlphaSlot
  ∷ electronMassSlot
  ∷ protonMassSlot
  ∷ vacuumPermittivitySlot
  ∷ vacuumPermeabilitySlot
  ∷ rydbergConstantSlot
  ∷ higgsMassSlot
  ∷ strongCouplingSlot
  ∷ []

canonicalCODATABoundMeasuredSlots : List MeasuredConstantSlot
canonicalCODATABoundMeasuredSlots =
  newtonianGSlot
  ∷ fineStructureAlphaSlot
  ∷ electronMassSlot
  ∷ protonMassSlot
  ∷ vacuumPermittivitySlot
  ∷ vacuumPermeabilitySlot
  ∷ rydbergConstantSlot
  ∷ []

canonicalPDGBoundMeasuredSlots : List MeasuredConstantSlot
canonicalPDGBoundMeasuredSlots =
  higgsMassSlot
  ∷ strongCouplingSlot
  ∷ []

record AuthorityVersion : Set where
  field
    authorityVersionName : String
    authorityOwnerName : String
    versionScope : String

open AuthorityVersion public

record SourceUri : Set where
  field
    sourceUriName : String
    sourceUriValue : String
    sourceUriScope : String

open SourceUri public

record SourceChecksum : Set where
  field
    sourceChecksumName : String
    checksumAlgorithm : String
    checksumCoverage : String

open SourceChecksum public

record SourceAccessDate : Set where
  field
    sourceAccessDateName : String
    sourceAccessDateValue : String
    sourceAccessDateScope : String

open SourceAccessDate public

record ValueUncertainty : Set where
  field
    valueUncertaintyName : String
    uncertaintyConvention : String
    covariancePolicy : String

open ValueUncertainty public

record RoundingPolicy : Set where
  field
    roundingPolicyName : String
    roundingMode : String
    finiteTokenPolicy : String

open RoundingPolicy public

record UnitConvention : Set where
  field
    unitConventionName : String
    baseUnitSystem : String
    conversionPolicy : String

open UnitConvention public

record ValidityRegime : Set where
  field
    validityRegimeName : String
    regimeScope : String
    consumerBoundary : String

open ValidityRegime public

record AuthorityBindingMetadata : Set where
  field
    authorityVersion : AuthorityVersion
    sourceUri : SourceUri
    sourceChecksum : SourceChecksum
    sourceAccessDate : SourceAccessDate
    valueUncertainty : ValueUncertainty
    roundingPolicy : RoundingPolicy
    unitConvention : UnitConvention
    validityRegime : ValidityRegime

open AuthorityBindingMetadata public

record CompleteAuthorityMetadata
  (metadata : AuthorityBindingMetadata) : Set where
  field
    authorityVersionPresent : Bool
    authorityVersionPresentIsTrue :
      authorityVersionPresent ≡ true
    sourceUriPresent : Bool
    sourceUriPresentIsTrue :
      sourceUriPresent ≡ true
    sourceChecksumPresent : Bool
    sourceChecksumPresentIsTrue :
      sourceChecksumPresent ≡ true
    sourceAccessDatePresent : Bool
    sourceAccessDatePresentIsTrue :
      sourceAccessDatePresent ≡ true
    valueUncertaintyPresent : Bool
    valueUncertaintyPresentIsTrue :
      valueUncertaintyPresent ≡ true
    roundingPolicyPresent : Bool
    roundingPolicyPresentIsTrue :
      roundingPolicyPresent ≡ true
    unitConventionPresent : Bool
    unitConventionPresentIsTrue :
      unitConventionPresent ≡ true
    validityRegimePresent : Bool
    validityRegimePresentIsTrue :
      validityRegimePresent ≡ true

open CompleteAuthorityMetadata public

completeMetadata : (metadata : AuthorityBindingMetadata) →
  CompleteAuthorityMetadata metadata
completeMetadata metadata =
  record
    { authorityVersionPresent = true
    ; authorityVersionPresentIsTrue = refl
    ; sourceUriPresent = true
    ; sourceUriPresentIsTrue = refl
    ; sourceChecksumPresent = true
    ; sourceChecksumPresentIsTrue = refl
    ; sourceAccessDatePresent = true
    ; sourceAccessDatePresentIsTrue = refl
    ; valueUncertaintyPresent = true
    ; valueUncertaintyPresentIsTrue = refl
    ; roundingPolicyPresent = true
    ; roundingPolicyPresentIsTrue = refl
    ; unitConventionPresent = true
    ; unitConventionPresentIsTrue = refl
    ; validityRegimePresent = true
    ; validityRegimePresentIsTrue = refl
    }

codataAuthorityVersion : AuthorityVersion
codataAuthorityVersion = record
  { authorityVersionName = "NIST CODATA 2022 recommended-values authority"
  ; authorityOwnerName = "NIST CODATA"
  ; versionScope = "fundamental physical constants measured or adjusted values"
  }

pdgAuthorityVersion : AuthorityVersion
pdgAuthorityVersion = record
  { authorityVersionName = "PDG particle-data authority"
  ; authorityOwnerName = "Particle Data Group"
  ; versionScope = "particle masses and scale-dependent Standard Model inputs"
  }

codataSourceUri : SourceUri
codataSourceUri = record
  { sourceUriName = "NIST CODATA constants source URI"
  ; sourceUriValue = "https://physics.nist.gov/cuu/Constants/"
  ; sourceUriScope = "CODATA measured and adjusted constants authority surface"
  }

pdgSourceUri : SourceUri
pdgSourceUri = record
  { sourceUriName = "PDG particle-data source URI"
  ; sourceUriValue = "https://pdg.lbl.gov/"
  ; sourceUriScope = "PDG particle physics constants and review tables"
  }

codataSourceChecksum : SourceChecksum
codataSourceChecksum = record
  { sourceChecksumName = "NIST CODATA downloaded-source checksum"
  ; checksumAlgorithm = "SHA-256 over authority artifact selected by importer"
  ; checksumCoverage = "value, uncertainty, units, and authority-version table"
  }

pdgSourceChecksum : SourceChecksum
pdgSourceChecksum = record
  { sourceChecksumName = "PDG downloaded-source checksum"
  ; checksumAlgorithm = "SHA-256 over authority artifact selected by importer"
  ; checksumCoverage = "value, uncertainty, scheme, scale, and table version"
  }

canonicalSourceAccessDate : SourceAccessDate
canonicalSourceAccessDate = record
  { sourceAccessDateName = "authority source access date"
  ; sourceAccessDateValue = "2026-06-07"
  ; sourceAccessDateScope = "repo-side binding construction date"
  }

codataUncertaintyPolicy : ValueUncertainty
codataUncertaintyPolicy = record
  { valueUncertaintyName = "CODATA standard uncertainty policy"
  ; uncertaintyConvention = "standard uncertainty carried with adjusted value"
  ; covariancePolicy = "covariance unavailable until authority token imports it"
  }

pdgUncertaintyPolicy : ValueUncertainty
pdgUncertaintyPolicy = record
  { valueUncertaintyName = "PDG fit uncertainty policy"
  ; uncertaintyConvention = "PDG quoted uncertainty and fit convention"
  ; covariancePolicy = "fit covariance unavailable until authority token imports it"
  }

canonicalRoundingPolicy : RoundingPolicy
canonicalRoundingPolicy = record
  { roundingPolicyName = "authority significant-digit rounding policy"
  ; roundingMode = "preserve authority significant digits before finite-token conversion"
  ; finiteTokenPolicy = "finite numeric token must cite authority and rounding receipt"
  }

codataUnitConvention : UnitConvention
codataUnitConvention = record
  { unitConventionName = "CODATA SI unit convention"
  ; baseUnitSystem = "SI"
  ; conversionPolicy = "no natural-unit conversion without a separate adapter receipt"
  }

pdgUnitConvention : UnitConvention
pdgUnitConvention = record
  { unitConventionName = "PDG high-energy unit convention"
  ; baseUnitSystem = "particle-data GeV, MeV, c, and dimensionless conventions"
  ; conversionPolicy = "SI conversion requires explicit constants and unit adapter"
  }

codataValidityRegime : ValidityRegime
codataValidityRegime = record
  { validityRegimeName = "CODATA measured-constant validity regime"
  ; regimeScope = "metrology and physical-model adapters consuming CODATA constants"
  ; consumerBoundary = "not a theorem, law derivation, or empirical adequacy proof"
  }

pdgValidityRegime : ValidityRegime
pdgValidityRegime = record
  { validityRegimeName = "PDG particle-data validity regime"
  ; regimeScope = "Standard Model sector, collider, QCD, and Yang-Mills adapters"
  ; consumerBoundary = "not a Standard Model, QFT, or Yang-Mills promotion"
  }

codataBindingMetadata : AuthorityBindingMetadata
codataBindingMetadata = record
  { authorityVersion = codataAuthorityVersion
  ; sourceUri = codataSourceUri
  ; sourceChecksum = codataSourceChecksum
  ; sourceAccessDate = canonicalSourceAccessDate
  ; valueUncertainty = codataUncertaintyPolicy
  ; roundingPolicy = canonicalRoundingPolicy
  ; unitConvention = codataUnitConvention
  ; validityRegime = codataValidityRegime
  }

pdgBindingMetadata : AuthorityBindingMetadata
pdgBindingMetadata = record
  { authorityVersion = pdgAuthorityVersion
  ; sourceUri = pdgSourceUri
  ; sourceChecksum = pdgSourceChecksum
  ; sourceAccessDate = canonicalSourceAccessDate
  ; valueUncertainty = pdgUncertaintyPolicy
  ; roundingPolicy = canonicalRoundingPolicy
  ; unitConvention = pdgUnitConvention
  ; validityRegime = pdgValidityRegime
  }

canonicalAuthorityMetadataRows : List AuthorityBindingMetadata
canonicalAuthorityMetadataRows =
  codataBindingMetadata
  ∷ pdgBindingMetadata
  ∷ []

record MeasuredConstantConsumerBinding : Set₁ where
  field
    bindingLabel : String
    slot : MeasuredConstantSlot
    consumerLane : MeasuredConsumerLane
    metadata : AuthorityBindingMetadata
    metadataCompleteness : CompleteAuthorityMetadata metadata
    requiredAuthorityTokenName : String
    requiredValueIngestionReceiptName : String
    requiredValidationCommand : String
    metadataBoundForConsumer : Bool
    metadataBoundForConsumerIsTrue : metadataBoundForConsumer ≡ true
    consumerMayReadAuthorityMetadata : Bool
    consumerMayReadAuthorityMetadataIsTrue :
      consumerMayReadAuthorityMetadata ≡ true
    acceptedAuthorityTokenPresent : Bool
    acceptedAuthorityTokenPresentIsFalse :
      acceptedAuthorityTokenPresent ≡ false
    numericValuePromoted : Bool
    numericValuePromotedIsFalse :
      numericValuePromoted ≡ false

open MeasuredConstantConsumerBinding public

mkConsumerBinding :
  String →
  MeasuredConstantSlot →
  MeasuredConsumerLane →
  AuthorityBindingMetadata →
  String →
  String →
  String →
  MeasuredConstantConsumerBinding
mkConsumerBinding
  label slot lane metadata tokenName receiptName validationCommand =
  record
    { bindingLabel = label
    ; slot = slot
    ; consumerLane = lane
    ; metadata = metadata
    ; metadataCompleteness = completeMetadata metadata
    ; requiredAuthorityTokenName = tokenName
    ; requiredValueIngestionReceiptName = receiptName
    ; requiredValidationCommand = validationCommand
    ; metadataBoundForConsumer = true
    ; metadataBoundForConsumerIsTrue = refl
    ; consumerMayReadAuthorityMetadata = true
    ; consumerMayReadAuthorityMetadataIsTrue = refl
    ; acceptedAuthorityTokenPresent =
        Registry.AuthorityConsumptionPolicyReceipt.acceptedAuthorityTokenPresent
          Registry.canonicalAuthorityConsumptionPolicyReceipt
    ; acceptedAuthorityTokenPresentIsFalse =
        Registry.AuthorityConsumptionPolicyReceipt.acceptedAuthorityTokenPresentIsFalse
          Registry.canonicalAuthorityConsumptionPolicyReceipt
    ; numericValuePromoted =
        Registry.AuthorityConsumptionPolicyReceipt.numericValuePromoted
          Registry.canonicalAuthorityConsumptionPolicyReceipt
    ; numericValuePromotedIsFalse =
        Registry.AuthorityConsumptionPolicyReceipt.numericValuePromotedIsFalse
          Registry.canonicalAuthorityConsumptionPolicyReceipt
    }

gConsumerBinding : MeasuredConstantConsumerBinding
gConsumerBinding =
  mkConsumerBinding
    "G authority metadata bound for GR normalization"
    newtonianGSlot
    grNormalizationConsumer
    codataBindingMetadata
    "accepted-CODATA-G-authority-token"
    "G-numeric-value-ingestion-receipt"
    "agda -i . DASHI/Promotion/NumericMeasuredAuthorityBinding.agda"

alphaConsumerBinding : MeasuredConstantConsumerBinding
alphaConsumerBinding =
  mkConsumerBinding
    "alpha authority metadata bound for electromagnetic and SM consumers"
    fineStructureAlphaSlot
    maxwellElectromagneticConsumer
    codataBindingMetadata
    "accepted-CODATA-alpha-authority-token"
    "alpha-numeric-value-ingestion-receipt"
    "agda -i . DASHI/Promotion/NumericMeasuredAuthorityBinding.agda"

electronMassConsumerBinding : MeasuredConstantConsumerBinding
electronMassConsumerBinding =
  mkConsumerBinding
    "m_e authority metadata bound for Schrodinger consumers"
    electronMassSlot
    quantumSchrodingerConsumer
    codataBindingMetadata
    "accepted-CODATA-m_e-authority-token"
    "m_e-numeric-value-ingestion-receipt"
    "agda -i . DASHI/Promotion/NumericMeasuredAuthorityBinding.agda"

protonMassConsumerBinding : MeasuredConstantConsumerBinding
protonMassConsumerBinding =
  mkConsumerBinding
    "m_p authority metadata bound for chemistry and biology consumers"
    protonMassSlot
    atomicChemistrySpectroscopyConsumer
    codataBindingMetadata
    "accepted-CODATA-m_p-authority-token"
    "m_p-numeric-value-ingestion-receipt"
    "agda -i . DASHI/Promotion/NumericMeasuredAuthorityBinding.agda"

epsilonZeroConsumerBinding : MeasuredConstantConsumerBinding
epsilonZeroConsumerBinding =
  mkConsumerBinding
    "epsilon_0 authority metadata bound for Maxwell consumers"
    vacuumPermittivitySlot
    maxwellElectromagneticConsumer
    codataBindingMetadata
    "accepted-CODATA-epsilon_0-authority-token"
    "epsilon_0-numeric-value-ingestion-receipt"
    "agda -i . DASHI/Promotion/NumericMeasuredAuthorityBinding.agda"

muZeroConsumerBinding : MeasuredConstantConsumerBinding
muZeroConsumerBinding =
  mkConsumerBinding
    "mu_0 authority metadata bound for Maxwell consumers"
    vacuumPermeabilitySlot
    maxwellElectromagneticConsumer
    codataBindingMetadata
    "accepted-CODATA-mu_0-authority-token"
    "mu_0-numeric-value-ingestion-receipt"
    "agda -i . DASHI/Promotion/NumericMeasuredAuthorityBinding.agda"

rydbergConsumerBinding : MeasuredConstantConsumerBinding
rydbergConsumerBinding =
  mkConsumerBinding
    "R_infinity authority metadata bound for spectroscopy consumers"
    rydbergConstantSlot
    atomicChemistrySpectroscopyConsumer
    codataBindingMetadata
    "accepted-CODATA-R_infinity-authority-token"
    "R_infinity-numeric-value-ingestion-receipt"
    "agda -i . DASHI/Promotion/NumericMeasuredAuthorityBinding.agda"

higgsMassConsumerBinding : MeasuredConstantConsumerBinding
higgsMassConsumerBinding =
  mkConsumerBinding
    "m_H authority metadata bound for Standard Model consumers"
    higgsMassSlot
    standardModelSectorConsumer
    pdgBindingMetadata
    "accepted-PDG-m_H-authority-token"
    "m_H-numeric-value-ingestion-receipt"
    "agda -i . DASHI/Promotion/NumericMeasuredAuthorityBinding.agda"

alphaSConsumerBinding : MeasuredConstantConsumerBinding
alphaSConsumerBinding =
  mkConsumerBinding
    "alpha_s authority metadata bound for QCD and Yang-Mills consumers"
    strongCouplingSlot
    yangMillsQCDConsumer
    pdgBindingMetadata
    "accepted-PDG-alpha_s-authority-token"
    "alpha_s-numeric-value-ingestion-receipt"
    "agda -i . DASHI/Promotion/NumericMeasuredAuthorityBinding.agda"

canonicalMeasuredConsumerBindings :
  List MeasuredConstantConsumerBinding
canonicalMeasuredConsumerBindings =
  gConsumerBinding
  ∷ alphaConsumerBinding
  ∷ electronMassConsumerBinding
  ∷ protonMassConsumerBinding
  ∷ epsilonZeroConsumerBinding
  ∷ muZeroConsumerBinding
  ∷ rydbergConsumerBinding
  ∷ higgsMassConsumerBinding
  ∷ alphaSConsumerBinding
  ∷ []

canonicalCODATAConsumerBindings :
  List MeasuredConstantConsumerBinding
canonicalCODATAConsumerBindings =
  gConsumerBinding
  ∷ alphaConsumerBinding
  ∷ electronMassConsumerBinding
  ∷ protonMassConsumerBinding
  ∷ epsilonZeroConsumerBinding
  ∷ muZeroConsumerBinding
  ∷ rydbergConsumerBinding
  ∷ []

canonicalPDGConsumerBindings :
  List MeasuredConstantConsumerBinding
canonicalPDGConsumerBindings =
  higgsMassConsumerBinding
  ∷ alphaSConsumerBinding
  ∷ []

canonicalMetadataFieldNames : List String
canonicalMetadataFieldNames =
  "authorityVersion"
  ∷ "sourceUri"
  ∷ "sourceChecksum"
  ∷ "sourceAccessDate"
  ∷ "valueUncertainty"
  ∷ "roundingPolicy"
  ∷ "unitConvention"
  ∷ "validityRegime"
  ∷ []

record NumericMeasuredAuthorityBindingReceipt : Set₁ where
  field
    receiptLabel : String
    sourceRegistry : Registry.ConstantsRegistry
    sourceAuthorityPolicy :
      Registry.AuthorityConsumptionPolicyReceipt
    sourceNumericObligationIndex :
      Numeric.NumericAndAuthorityObligationIndex
    measuredSlots : List MeasuredConstantSlot
    codataMeasuredSlots : List MeasuredConstantSlot
    pdgMeasuredSlots : List MeasuredConstantSlot
    metadataFieldNames : List String
    authorityMetadataRows : List AuthorityBindingMetadata
    consumerBindings : List MeasuredConstantConsumerBinding
    codataConsumerBindings : List MeasuredConstantConsumerBinding
    pdgConsumerBindings : List MeasuredConstantConsumerBinding
    measuredSlotCount : Nat
    measuredSlotCountIs9 : measuredSlotCount ≡ 9
    codataMeasuredSlotCount : Nat
    codataMeasuredSlotCountIs7 : codataMeasuredSlotCount ≡ 7
    pdgMeasuredSlotCount : Nat
    pdgMeasuredSlotCountIs2 : pdgMeasuredSlotCount ≡ 2
    metadataFieldCount : Nat
    metadataFieldCountIs8 : metadataFieldCount ≡ 8
    authorityMetadataRowCount : Nat
    authorityMetadataRowCountIs2 : authorityMetadataRowCount ≡ 2
    consumerBindingCount : Nat
    consumerBindingCountIs9 : consumerBindingCount ≡ 9
    codataConsumerBindingCount : Nat
    codataConsumerBindingCountIs7 :
      codataConsumerBindingCount ≡ 7
    pdgConsumerBindingCount : Nat
    pdgConsumerBindingCountIs2 :
      pdgConsumerBindingCount ≡ 2
    everyBindingHasCompleteMetadata : Bool
    everyBindingHasCompleteMetadataIsTrue :
      everyBindingHasCompleteMetadata ≡ true
    everyBindingRequiresValueIngestionReceipt : Bool
    everyBindingRequiresValueIngestionReceiptIsTrue :
      everyBindingRequiresValueIngestionReceipt ≡ true
    acceptedAuthorityTokenPresent : Bool
    acceptedAuthorityTokenPresentIsFalse :
      acceptedAuthorityTokenPresent ≡ false
    numericValuePromoted : Bool
    numericValuePromotedIsFalse :
      numericValuePromoted ≡ false
    obligationIndexNumericValuePromoted : Bool
    obligationIndexNumericValuePromotedIsFalse :
      obligationIndexNumericValuePromoted ≡ false
    claimPromotionStillFalse : Bool
    claimPromotionStillFalseIsTrue :
      claimPromotionStillFalse ≡ true

open NumericMeasuredAuthorityBindingReceipt public

listCount : ∀ {a : Level} {A : Set a} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

canonicalNumericMeasuredAuthorityBindingReceipt :
  NumericMeasuredAuthorityBindingReceipt
canonicalNumericMeasuredAuthorityBindingReceipt = record
  { receiptLabel =
      "numeric measured constant authority metadata and consumer bindings"
  ; sourceRegistry =
      Registry.repoWideConstantsRegistry
  ; sourceAuthorityPolicy =
      Registry.canonicalAuthorityConsumptionPolicyReceipt
  ; sourceNumericObligationIndex =
      Numeric.canonicalNumericAndAuthorityObligationIndex
  ; measuredSlots =
      canonicalMeasuredConstantSlots
  ; codataMeasuredSlots =
      canonicalCODATABoundMeasuredSlots
  ; pdgMeasuredSlots =
      canonicalPDGBoundMeasuredSlots
  ; metadataFieldNames =
      canonicalMetadataFieldNames
  ; authorityMetadataRows =
      canonicalAuthorityMetadataRows
  ; consumerBindings =
      canonicalMeasuredConsumerBindings
  ; codataConsumerBindings =
      canonicalCODATAConsumerBindings
  ; pdgConsumerBindings =
      canonicalPDGConsumerBindings
  ; measuredSlotCount =
      listCount canonicalMeasuredConstantSlots
  ; measuredSlotCountIs9 =
      refl
  ; codataMeasuredSlotCount =
      listCount canonicalCODATABoundMeasuredSlots
  ; codataMeasuredSlotCountIs7 =
      refl
  ; pdgMeasuredSlotCount =
      listCount canonicalPDGBoundMeasuredSlots
  ; pdgMeasuredSlotCountIs2 =
      refl
  ; metadataFieldCount =
      listCount canonicalMetadataFieldNames
  ; metadataFieldCountIs8 =
      refl
  ; authorityMetadataRowCount =
      listCount canonicalAuthorityMetadataRows
  ; authorityMetadataRowCountIs2 =
      refl
  ; consumerBindingCount =
      listCount canonicalMeasuredConsumerBindings
  ; consumerBindingCountIs9 =
      refl
  ; codataConsumerBindingCount =
      listCount canonicalCODATAConsumerBindings
  ; codataConsumerBindingCountIs7 =
      refl
  ; pdgConsumerBindingCount =
      listCount canonicalPDGConsumerBindings
  ; pdgConsumerBindingCountIs2 =
      refl
  ; everyBindingHasCompleteMetadata =
      true
  ; everyBindingHasCompleteMetadataIsTrue =
      refl
  ; everyBindingRequiresValueIngestionReceipt =
      true
  ; everyBindingRequiresValueIngestionReceiptIsTrue =
      refl
  ; acceptedAuthorityTokenPresent =
      Registry.AuthorityConsumptionPolicyReceipt.acceptedAuthorityTokenPresent
        Registry.canonicalAuthorityConsumptionPolicyReceipt
  ; acceptedAuthorityTokenPresentIsFalse =
      Registry.AuthorityConsumptionPolicyReceipt.acceptedAuthorityTokenPresentIsFalse
        Registry.canonicalAuthorityConsumptionPolicyReceipt
  ; numericValuePromoted =
      Registry.AuthorityConsumptionPolicyReceipt.numericValuePromoted
        Registry.canonicalAuthorityConsumptionPolicyReceipt
  ; numericValuePromotedIsFalse =
      Registry.AuthorityConsumptionPolicyReceipt.numericValuePromotedIsFalse
        Registry.canonicalAuthorityConsumptionPolicyReceipt
  ; obligationIndexNumericValuePromoted =
      Numeric.NumericAndAuthorityObligationIndex.numericValuePromoted
        Numeric.canonicalNumericAndAuthorityObligationIndex
  ; obligationIndexNumericValuePromotedIsFalse =
      Numeric.NumericAndAuthorityObligationIndex.numericValuePromotedIsFalse
        Numeric.canonicalNumericAndAuthorityObligationIndex
  ; claimPromotionStillFalse =
      true
  ; claimPromotionStillFalseIsTrue =
      refl
  }

canonicalMeasuredAuthoritySlotCountIs9 :
  NumericMeasuredAuthorityBindingReceipt.measuredSlotCount
    canonicalNumericMeasuredAuthorityBindingReceipt
  ≡ 9
canonicalMeasuredAuthoritySlotCountIs9 = refl

canonicalCODATAMeasuredAuthoritySlotCountIs7 :
  NumericMeasuredAuthorityBindingReceipt.codataMeasuredSlotCount
    canonicalNumericMeasuredAuthorityBindingReceipt
  ≡ 7
canonicalCODATAMeasuredAuthoritySlotCountIs7 = refl

canonicalPDGMeasuredAuthoritySlotCountIs2 :
  NumericMeasuredAuthorityBindingReceipt.pdgMeasuredSlotCount
    canonicalNumericMeasuredAuthorityBindingReceipt
  ≡ 2
canonicalPDGMeasuredAuthoritySlotCountIs2 = refl

canonicalMeasuredAuthorityMetadataFieldCountIs8 :
  NumericMeasuredAuthorityBindingReceipt.metadataFieldCount
    canonicalNumericMeasuredAuthorityBindingReceipt
  ≡ 8
canonicalMeasuredAuthorityMetadataFieldCountIs8 = refl

canonicalMeasuredAuthorityMetadataRowCountIs2 :
  NumericMeasuredAuthorityBindingReceipt.authorityMetadataRowCount
    canonicalNumericMeasuredAuthorityBindingReceipt
  ≡ 2
canonicalMeasuredAuthorityMetadataRowCountIs2 = refl

canonicalMeasuredConsumerBindingCountIs9 :
  NumericMeasuredAuthorityBindingReceipt.consumerBindingCount
    canonicalNumericMeasuredAuthorityBindingReceipt
  ≡ 9
canonicalMeasuredConsumerBindingCountIs9 = refl

canonicalMeasuredCODATAConsumerBindingCountIs7 :
  NumericMeasuredAuthorityBindingReceipt.codataConsumerBindingCount
    canonicalNumericMeasuredAuthorityBindingReceipt
  ≡ 7
canonicalMeasuredCODATAConsumerBindingCountIs7 = refl

canonicalMeasuredPDGConsumerBindingCountIs2 :
  NumericMeasuredAuthorityBindingReceipt.pdgConsumerBindingCount
    canonicalNumericMeasuredAuthorityBindingReceipt
  ≡ 2
canonicalMeasuredPDGConsumerBindingCountIs2 = refl

canonicalMeasuredAuthorityAcceptedTokenPresentIsFalse :
  NumericMeasuredAuthorityBindingReceipt.acceptedAuthorityTokenPresent
    canonicalNumericMeasuredAuthorityBindingReceipt
  ≡ false
canonicalMeasuredAuthorityAcceptedTokenPresentIsFalse = refl

canonicalMeasuredAuthorityNumericValuePromotedIsFalse :
  NumericMeasuredAuthorityBindingReceipt.numericValuePromoted
    canonicalNumericMeasuredAuthorityBindingReceipt
  ≡ false
canonicalMeasuredAuthorityNumericValuePromotedIsFalse = refl

canonicalMeasuredAuthorityObligationIndexNumericValuePromotedIsFalse :
  NumericMeasuredAuthorityBindingReceipt.obligationIndexNumericValuePromoted
    canonicalNumericMeasuredAuthorityBindingReceipt
  ≡ false
canonicalMeasuredAuthorityObligationIndexNumericValuePromotedIsFalse = refl

canonicalMeasuredAuthorityClaimPromotionStillFalse :
  NumericMeasuredAuthorityBindingReceipt.claimPromotionStillFalse
    canonicalNumericMeasuredAuthorityBindingReceipt
  ≡ true
canonicalMeasuredAuthorityClaimPromotionStillFalse = refl
