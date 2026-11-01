module DASHI.Promotion.ChemistryAuthorityBinding where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Constants.Registry as Registry
import DASHI.Promotion.ChemistryFiniteRuleTargets as Finite
import DASHI.Promotion.ChemistryQuantitativeAdapter as Quant
import DASHI.Promotion.ChemistrySpectroscopyAuthorityIntake as Intake

------------------------------------------------------------------------
-- Chemistry spectroscopy/thermochemistry authority binding.
--
-- This module is disjoint from the finite-rule target module.  It binds the
-- already named registry, quantitative-adapter, and authority-intake slots to
-- finite receipt shapes for spectra and thermochemistry.  Every canonical row
-- remains fail-closed: external NIST/WebBook/CODATA tokens, calibration,
-- uncertainty, provenance, and wet-lab replication are required, not accepted.

data ChemistryBindingProvider : Set where
  nistAtomicSpectraDatabase : ChemistryBindingProvider
  nistChemistryWebBook : ChemistryBindingProvider
  nistCODATAFundamentalConstants : ChemistryBindingProvider

data BindingLane : Set where
  rydbergSpectralLineLane : BindingLane
  thermochemistryGibbsLane : BindingLane
  activityAndBindingLane : BindingLane
  instrumentCalibrationLane : BindingLane
  provenanceUncertaintyLane : BindingLane

record AuthorityTokenBinding : Set₁ where
  field
    tokenLabel : String
    provider : ChemistryBindingProvider
    registryAuthoritySlot : String
    consumedByAuthorityRequest : String
    consumedByAdapter : String
    sourceUri : String
    requiredTokenFields : List String
    checksumRequired : Bool
    checksumRequiredIsTrue : checksumRequired ≡ true
    uncertaintyRequired : Bool
    uncertaintyRequiredIsTrue : uncertaintyRequired ≡ true
    tokenAccepted : Bool
    tokenAcceptedIsFalse : tokenAccepted ≡ false
    promotesClaim : Bool
    promotesClaimIsFalse : promotesClaim ≡ false

open AuthorityTokenBinding public

mkAuthorityToken :
  String →
  ChemistryBindingProvider →
  String →
  String →
  String →
  String →
  List String →
  AuthorityTokenBinding
mkAuthorityToken label provider slot request adapter uri fields =
  record
    { tokenLabel = label
    ; provider = provider
    ; registryAuthoritySlot = slot
    ; consumedByAuthorityRequest = request
    ; consumedByAdapter = adapter
    ; sourceUri = uri
    ; requiredTokenFields = fields
    ; checksumRequired = true
    ; checksumRequiredIsTrue = refl
    ; uncertaintyRequired = true
    ; uncertaintyRequiredIsTrue = refl
    ; tokenAccepted = false
    ; tokenAcceptedIsFalse = refl
    ; promotesClaim = false
    ; promotesClaimIsFalse = refl
    }

authorityTokenCount : List AuthorityTokenBinding → Nat
authorityTokenCount [] = zero
authorityTokenCount (_ ∷ xs) = suc (authorityTokenCount xs)

canonicalAuthorityTokenBindings : List AuthorityTokenBinding
canonicalAuthorityTokenBindings =
  mkAuthorityToken
    "NIST ASD spectral-line token"
    nistAtomicSpectraDatabase
    "Registry authority source slot: NIST spectral line authority"
    "spectral-line or spectrum authority intake"
    "SpectroscopyObservableAdapter.spectralAuthoritySlot"
    "https://physics.nist.gov/asd"
    ( "sourceUri"
    ∷ "authorityVersion"
    ∷ "speciesAndChargeState"
    ∷ "transitionAssignment"
    ∷ "vacuumOrAirWavelengthConvention"
    ∷ "lineUncertaintyOrResolution"
    ∷ "sourceChecksum"
    ∷ []
    )
  ∷ mkAuthorityToken
    "NIST Chemistry WebBook thermochemistry token"
    nistChemistryWebBook
    "Registry authority source slot: NIST Chemistry WebBook"
    "thermochemistry authority intake"
    "SymbolicLawCarrier.measuredAuthorityInputs"
    "https://webbook.nist.gov/"
    ( "sourceUri"
    ∷ "authorityVersion"
    ∷ "compoundIdentity"
    ∷ "phase"
    ∷ "temperaturePressureConvention"
    ∷ "enthalpyEntropyFreeEnergyValues"
    ∷ "uncertaintyPolicy"
    ∷ "sourceChecksum"
    ∷ []
    )
  ∷ mkAuthorityToken
    "NIST CODATA Rydberg and atomic constants token"
    nistCODATAFundamentalConstants
    "Registry measured constants: R_infinity, alpha, m_e, isotope masses"
    "spectral-line or spectrum authority intake"
    "Rydberg formula slot and isotope/reduced-mass adapter"
    "https://www.nist.gov/pml/fundamental-physical-constants"
    ( "sourceUri"
    ∷ "CODATARelease"
    ∷ "constantSymbol"
    ∷ "numericValue"
    ∷ "unit"
    ∷ "standardUncertainty"
    ∷ "correlationOrAdjustmentPolicy"
    ∷ []
    )
  ∷ []

record SpectralLineAuthorityBinding : Set₁ where
  field
    lineBindingLabel : String
    lane : BindingLane
    authorityTokenLabel : String
    rydbergRegistrySlot : String
    symbolicRydbergForm : String
    lowerPrincipalLevel : Nat
    upperPrincipalLevel : Nat
    exactLevelCount : Nat
    exactLevelCountIs2 : exactLevelCount ≡ 2
    requiredMeasuredFields : List String
    isotopeReducedMassAdapterRequired : Bool
    isotopeReducedMassAdapterRequiredIsTrue :
      isotopeReducedMassAdapterRequired ≡ true
    instrumentCalibrationRequired : Bool
    instrumentCalibrationRequiredIsTrue :
      instrumentCalibrationRequired ≡ true
    spectralLineAuthorityAccepted : Bool
    spectralLineAuthorityAcceptedIsFalse :
      spectralLineAuthorityAccepted ≡ false
    promotesSpectroscopy : Bool
    promotesSpectroscopyIsFalse :
      promotesSpectroscopy ≡ false

open SpectralLineAuthorityBinding public

mkSpectralLineBinding :
  String →
  String →
  Nat →
  Nat →
  List String →
  SpectralLineAuthorityBinding
mkSpectralLineBinding label token lower upper fields =
  record
    { lineBindingLabel = label
    ; lane = rydbergSpectralLineLane
    ; authorityTokenLabel = token
    ; rydbergRegistrySlot =
        "R_infinity CODATA measured slot from constants registry"
    ; symbolicRydbergForm =
        "1 / lambda = R_infinity (1 / n_lower^2 - 1 / n_upper^2)"
    ; lowerPrincipalLevel = lower
    ; upperPrincipalLevel = upper
    ; exactLevelCount = 2
    ; exactLevelCountIs2 = refl
    ; requiredMeasuredFields = fields
    ; isotopeReducedMassAdapterRequired = true
    ; isotopeReducedMassAdapterRequiredIsTrue = refl
    ; instrumentCalibrationRequired = true
    ; instrumentCalibrationRequiredIsTrue = refl
    ; spectralLineAuthorityAccepted = false
    ; spectralLineAuthorityAcceptedIsFalse = refl
    ; promotesSpectroscopy = false
    ; promotesSpectroscopyIsFalse = refl
    }

spectralLineBindingCount : List SpectralLineAuthorityBinding → Nat
spectralLineBindingCount [] = zero
spectralLineBindingCount (_ ∷ xs) =
  suc (spectralLineBindingCount xs)

canonicalSpectralLineBindings : List SpectralLineAuthorityBinding
canonicalSpectralLineBindings =
  mkSpectralLineBinding
    "hydrogen Balmer-alpha Rydberg line authority binding"
    "NIST ASD spectral-line token"
    2
    3
    ( "observed wavelength"
    ∷ "vacuum/air wavelength convention"
    ∷ "frequency or wavenumber"
    ∷ "transition assignment n = 3 -> 2"
    ∷ "line uncertainty and calibration residual"
    ∷ []
    )
  ∷ mkSpectralLineBinding
    "hydrogen Lyman-alpha Rydberg line authority binding"
    "NIST ASD spectral-line token"
    1
    2
    ( "observed wavelength"
    ∷ "vacuum wavelength convention"
    ∷ "frequency or energy"
    ∷ "transition assignment n = 2 -> 1"
    ∷ "line uncertainty and calibration residual"
    ∷ []
    )
  ∷ mkSpectralLineBinding
    "Rydberg-series constant and reduced-mass authority binding"
    "NIST CODATA Rydberg and atomic constants token"
    1
    3
    ( "R_infinity value"
    ∷ "electron mass"
    ∷ "nuclear or isotope mass"
    ∷ "reduced-mass convention"
    ∷ "standard uncertainty"
    ∷ []
    )
  ∷ []

record GibbsThermochemistryBinding : Set₁ where
  field
    thermoBindingLabel : String
    lane : BindingLane
    authorityTokenLabel : String
    registryLawSlot : String
    symbolicGibbsForm : String
    exactReferenceInputs : List String
    requiredAuthorityFields : List String
    enthalpyAuthorityRequired : Bool
    enthalpyAuthorityRequiredIsTrue :
      enthalpyAuthorityRequired ≡ true
    entropyAuthorityRequired : Bool
    entropyAuthorityRequiredIsTrue :
      entropyAuthorityRequired ≡ true
    activityModelRequired : Bool
    activityModelRequiredIsTrue :
      activityModelRequired ≡ true
    thermochemistryAuthorityAccepted : Bool
    thermochemistryAuthorityAcceptedIsFalse :
      thermochemistryAuthorityAccepted ≡ false
    promotesPhysicalChemistry : Bool
    promotesPhysicalChemistryIsFalse :
      promotesPhysicalChemistry ≡ false

open GibbsThermochemistryBinding public

mkGibbsThermoBinding :
  String →
  BindingLane →
  String →
  String →
  List String →
  GibbsThermochemistryBinding
mkGibbsThermoBinding label lane token form fields =
  record
    { thermoBindingLabel = label
    ; lane = lane
    ; authorityTokenLabel = token
    ; registryLawSlot =
        "Registry chemistry law slot: Gibbs free energy relation"
    ; symbolicGibbsForm = form
    ; exactReferenceInputs =
        "R : exact derived expression N_A k_B"
        ∷ "temperature carrier T"
        ∷ []
    ; requiredAuthorityFields = fields
    ; enthalpyAuthorityRequired = true
    ; enthalpyAuthorityRequiredIsTrue = refl
    ; entropyAuthorityRequired = true
    ; entropyAuthorityRequiredIsTrue = refl
    ; activityModelRequired = true
    ; activityModelRequiredIsTrue = refl
    ; thermochemistryAuthorityAccepted = false
    ; thermochemistryAuthorityAcceptedIsFalse = refl
    ; promotesPhysicalChemistry = false
    ; promotesPhysicalChemistryIsFalse = refl
    }

thermochemistryBindingCount : List GibbsThermochemistryBinding → Nat
thermochemistryBindingCount [] = zero
thermochemistryBindingCount (_ ∷ xs) =
  suc (thermochemistryBindingCount xs)

canonicalThermochemistryBindings : List GibbsThermochemistryBinding
canonicalThermochemistryBindings =
  mkGibbsThermoBinding
    "standard Gibbs from enthalpy and entropy binding"
    thermochemistryGibbsLane
    "NIST Chemistry WebBook thermochemistry token"
    "Delta G = Delta H - T Delta S"
    ( "Delta H authority"
    ∷ "Delta S authority"
    ∷ "temperature"
    ∷ "phase and standard-state convention"
    ∷ "uncertainty propagation policy"
    ∷ []
    )
  ∷ mkGibbsThermoBinding
    "reaction Gibbs from activity quotient binding"
    activityAndBindingLane
    "NIST Chemistry WebBook thermochemistry token"
    "Delta G = Delta G0 + R T ln Q"
    ( "Delta G0 authority"
    ∷ "activity quotient Q"
    ∷ "activity coefficient model"
    ∷ "standard concentration or pressure convention"
    ∷ "uncertainty propagation policy"
    ∷ []
    )
  ∷ mkGibbsThermoBinding
    "binding free energy to equilibrium constant binding"
    activityAndBindingLane
    "NIST Chemistry WebBook thermochemistry token"
    "Delta G0 = - R T ln K"
    ( "Kd Ka or association constant authority"
    ∷ "assay temperature"
    ∷ "buffer and ionic-strength metadata"
    ∷ "activity/concentration convention"
    ∷ "confidence or uncertainty policy"
    ∷ []
    )
  ∷ mkGibbsThermoBinding
    "activity-corrected wet chemistry authority binding"
    activityAndBindingLane
    "NIST Chemistry WebBook thermochemistry token"
    "a_i = gamma_i x_i or declared activity convention"
    ( "activity coefficient authority"
    ∷ "composition variable"
    ∷ "solvent phase and ionic strength"
    ∷ "temperature"
    ∷ "model-validity range"
    ∷ []
    )
  ∷ []

record InstrumentCalibrationBinding : Set₁ where
  field
    calibrationLabel : String
    lane : BindingLane
    instrumentClass : String
    consumedBy : String
    requiredCalibrationFields : List String
    responseFunctionChecksumRequired : Bool
    responseFunctionChecksumRequiredIsTrue :
      responseFunctionChecksumRequired ≡ true
    driftPolicyRequired : Bool
    driftPolicyRequiredIsTrue :
      driftPolicyRequired ≡ true
    calibrationAccepted : Bool
    calibrationAcceptedIsFalse : calibrationAccepted ≡ false
    promotesWetLabValidation : Bool
    promotesWetLabValidationIsFalse :
      promotesWetLabValidation ≡ false

open InstrumentCalibrationBinding public

mkCalibrationBinding :
  String →
  BindingLane →
  String →
  String →
  List String →
  InstrumentCalibrationBinding
mkCalibrationBinding label lane instrument consumer fields =
  record
    { calibrationLabel = label
    ; lane = lane
    ; instrumentClass = instrument
    ; consumedBy = consumer
    ; requiredCalibrationFields = fields
    ; responseFunctionChecksumRequired = true
    ; responseFunctionChecksumRequiredIsTrue = refl
    ; driftPolicyRequired = true
    ; driftPolicyRequiredIsTrue = refl
    ; calibrationAccepted = false
    ; calibrationAcceptedIsFalse = refl
    ; promotesWetLabValidation = false
    ; promotesWetLabValidationIsFalse = refl
    }

calibrationBindingCount : List InstrumentCalibrationBinding → Nat
calibrationBindingCount [] = zero
calibrationBindingCount (_ ∷ xs) =
  suc (calibrationBindingCount xs)

canonicalCalibrationBindings : List InstrumentCalibrationBinding
canonicalCalibrationBindings =
  mkCalibrationBinding
    "spectrometer wavelength-axis calibration binding"
    instrumentCalibrationLane
    "spectrometer"
    "SpectroscopyObservableAdapter.instrumentResponseCarrier"
    ( "calibrationId"
    ∷ "instrumentId"
    ∷ "calibrationStandard"
    ∷ "wavelengthAxisResidual"
    ∷ "responseFunctionChecksum"
    ∷ "driftOrResolutionPolicy"
    ∷ []
    )
  ∷ mkCalibrationBinding
    "calorimetry and temperature calibration binding"
    instrumentCalibrationLane
    "calorimeter or thermal chemistry instrument"
    "GibbsThermochemistryBinding.requiredAuthorityFields"
    ( "calibrationId"
    ∷ "instrumentId"
    ∷ "temperatureScale"
    ∷ "enthalpyCalibrationStandard"
    ∷ "responseFunctionChecksum"
    ∷ "driftPolicy"
    ∷ []
    )
  ∷ []

record ProvenanceUncertaintyBinding : Set₁ where
  field
    provenanceLabel : String
    lane : BindingLane
    consumedBy : String
    requiredFields : List String
    sourceChecksumRequired : Bool
    sourceChecksumRequiredIsTrue :
      sourceChecksumRequired ≡ true
    unitConventionRequired : Bool
    unitConventionRequiredIsTrue :
      unitConventionRequired ≡ true
    uncertaintyPolicyRequired : Bool
    uncertaintyPolicyRequiredIsTrue :
      uncertaintyPolicyRequired ≡ true
    provenanceAccepted : Bool
    provenanceAcceptedIsFalse : provenanceAccepted ≡ false
    promotesClaim : Bool
    promotesClaimIsFalse : promotesClaim ≡ false

open ProvenanceUncertaintyBinding public

mkProvenanceBinding :
  String →
  BindingLane →
  String →
  List String →
  ProvenanceUncertaintyBinding
mkProvenanceBinding label lane consumer fields =
  record
    { provenanceLabel = label
    ; lane = lane
    ; consumedBy = consumer
    ; requiredFields = fields
    ; sourceChecksumRequired = true
    ; sourceChecksumRequiredIsTrue = refl
    ; unitConventionRequired = true
    ; unitConventionRequiredIsTrue = refl
    ; uncertaintyPolicyRequired = true
    ; uncertaintyPolicyRequiredIsTrue = refl
    ; provenanceAccepted = false
    ; provenanceAcceptedIsFalse = refl
    ; promotesClaim = false
    ; promotesClaimIsFalse = refl
    }

provenanceBindingCount : List ProvenanceUncertaintyBinding → Nat
provenanceBindingCount [] = zero
provenanceBindingCount (_ ∷ xs) =
  suc (provenanceBindingCount xs)

canonicalProvenanceBindings : List ProvenanceUncertaintyBinding
canonicalProvenanceBindings =
  mkProvenanceBinding
    "source identity and version provenance binding"
    provenanceUncertaintyLane
    "AuthorityTokenBinding.requiredTokenFields"
    ( "sourceUri"
    ∷ "authorityVersion"
    ∷ "accessDateOrRelease"
    ∷ "recordIdentifier"
    ∷ []
    )
  ∷ mkProvenanceBinding
    "source artifact checksum provenance binding"
    provenanceUncertaintyLane
    "ChemistryAuthorityRequestRow.requiredPayloadFields"
    ( "sourceChecksum"
    ∷ "parserVersion"
    ∷ "projectionDigest"
    ∷ []
    )
  ∷ mkProvenanceBinding
    "unit and convention provenance binding"
    provenanceUncertaintyLane
    "SpectralLineAuthorityBinding.requiredMeasuredFields"
    ( "unitSystem"
    ∷ "vacuumOrAirWavelengthConvention"
    ∷ "standardState"
    ∷ "temperaturePressureConvention"
    ∷ []
    )
  ∷ mkProvenanceBinding
    "uncertainty propagation provenance binding"
    provenanceUncertaintyLane
    "GibbsThermochemistryBinding.requiredAuthorityFields"
    ( "standardUncertainty"
    ∷ "coverageOrConfidence"
    ∷ "correlationPolicy"
    ∷ "propagationRule"
    ∷ []
    )
  ∷ []

record ChemistryAuthorityBinding : Set₁ where
  field
    registryReceipt :
      Registry.ChemistryKnownInputsReferenceReceipt
    quantitativeAdapter :
      Quant.ChemistryQuantitativeAdapter
    authorityIntake :
      Intake.ChemistrySpectroscopyAuthorityIntake
    finiteRuleTargets :
      Finite.ChemistryFiniteRuleTargets
    authorityTokens :
      List AuthorityTokenBinding
    authorityTokenCountField :
      Nat
    authorityTokenCountMatches :
      authorityTokenCountField ≡ authorityTokenCount authorityTokens
    spectralLineBindings :
      List SpectralLineAuthorityBinding
    spectralLineBindingCountField :
      Nat
    spectralLineBindingCountMatches :
      spectralLineBindingCountField ≡
      spectralLineBindingCount spectralLineBindings
    thermochemistryBindings :
      List GibbsThermochemistryBinding
    thermochemistryBindingCountField :
      Nat
    thermochemistryBindingCountMatches :
      thermochemistryBindingCountField ≡
      thermochemistryBindingCount thermochemistryBindings
    calibrationBindings :
      List InstrumentCalibrationBinding
    calibrationBindingCountField :
      Nat
    calibrationBindingCountMatches :
      calibrationBindingCountField ≡
      calibrationBindingCount calibrationBindings
    provenanceBindings :
      List ProvenanceUncertaintyBinding
    provenanceBindingCountField :
      Nat
    provenanceBindingCountMatches :
      provenanceBindingCountField ≡
      provenanceBindingCount provenanceBindings
    exactAuthorityBindingCounts :
      Bool
    exactAuthorityBindingCountsIsTrue :
      exactAuthorityBindingCounts ≡ true
    acceptedAuthorityTokenPresent :
      Bool
    acceptedAuthorityTokenPresentIsFalse :
      acceptedAuthorityTokenPresent ≡ false
    instrumentCalibrationAccepted :
      Bool
    instrumentCalibrationAcceptedIsFalse :
      instrumentCalibrationAccepted ≡ false
    uncertaintyProvenanceAccepted :
      Bool
    uncertaintyProvenanceAcceptedIsFalse :
      uncertaintyProvenanceAccepted ≡ false
    physicalChemistryPromoted :
      Bool
    physicalChemistryPromotedIsFalse :
      physicalChemistryPromoted ≡ false
    spectroscopyPromoted :
      Bool
    spectroscopyPromotedIsFalse :
      spectroscopyPromoted ≡ false
    wetLabValidationAccepted :
      Bool
    wetLabValidationAcceptedIsFalse :
      wetLabValidationAccepted ≡ false
    validationCommand :
      String

open ChemistryAuthorityBinding public

canonicalChemistryAuthorityBinding : ChemistryAuthorityBinding
canonicalChemistryAuthorityBinding = record
  { registryReceipt =
      Registry.canonicalChemistryKnownInputsReferenceReceipt
  ; quantitativeAdapter =
      Quant.canonicalChemistryQuantitativeAdapter
  ; authorityIntake =
      Intake.canonicalChemistrySpectroscopyAuthorityIntake
  ; finiteRuleTargets =
      Finite.canonicalChemistryFiniteRuleTargets
  ; authorityTokens =
      canonicalAuthorityTokenBindings
  ; authorityTokenCountField =
      3
  ; authorityTokenCountMatches =
      refl
  ; spectralLineBindings =
      canonicalSpectralLineBindings
  ; spectralLineBindingCountField =
      3
  ; spectralLineBindingCountMatches =
      refl
  ; thermochemistryBindings =
      canonicalThermochemistryBindings
  ; thermochemistryBindingCountField =
      4
  ; thermochemistryBindingCountMatches =
      refl
  ; calibrationBindings =
      canonicalCalibrationBindings
  ; calibrationBindingCountField =
      2
  ; calibrationBindingCountMatches =
      refl
  ; provenanceBindings =
      canonicalProvenanceBindings
  ; provenanceBindingCountField =
      4
  ; provenanceBindingCountMatches =
      refl
  ; exactAuthorityBindingCounts =
      true
  ; exactAuthorityBindingCountsIsTrue =
      refl
  ; acceptedAuthorityTokenPresent =
      false
  ; acceptedAuthorityTokenPresentIsFalse =
      refl
  ; instrumentCalibrationAccepted =
      false
  ; instrumentCalibrationAcceptedIsFalse =
      refl
  ; uncertaintyProvenanceAccepted =
      false
  ; uncertaintyProvenanceAcceptedIsFalse =
      refl
  ; physicalChemistryPromoted =
      false
  ; physicalChemistryPromotedIsFalse =
      refl
  ; spectroscopyPromoted =
      false
  ; spectroscopyPromotedIsFalse =
      refl
  ; wetLabValidationAccepted =
      false
  ; wetLabValidationAcceptedIsFalse =
      refl
  ; validationCommand =
      "agda -i . DASHI/Promotion/ChemistryAuthorityBinding.agda"
  }

canonicalAuthorityTokenBindingCountIs3 :
  authorityTokenCountField canonicalChemistryAuthorityBinding ≡ 3
canonicalAuthorityTokenBindingCountIs3 = refl

canonicalSpectralLineBindingCountIs3 :
  spectralLineBindingCountField canonicalChemistryAuthorityBinding ≡ 3
canonicalSpectralLineBindingCountIs3 = refl

canonicalThermochemistryBindingCountIs4 :
  thermochemistryBindingCountField canonicalChemistryAuthorityBinding ≡ 4
canonicalThermochemistryBindingCountIs4 = refl

canonicalCalibrationBindingCountIs2 :
  calibrationBindingCountField canonicalChemistryAuthorityBinding ≡ 2
canonicalCalibrationBindingCountIs2 = refl

canonicalProvenanceBindingCountIs4 :
  provenanceBindingCountField canonicalChemistryAuthorityBinding ≡ 4
canonicalProvenanceBindingCountIs4 = refl

canonicalAuthorityBindingCountsAreExact :
  exactAuthorityBindingCounts canonicalChemistryAuthorityBinding ≡ true
canonicalAuthorityBindingCountsAreExact = refl

canonicalAuthorityTokenStillMissing :
  acceptedAuthorityTokenPresent canonicalChemistryAuthorityBinding ≡ false
canonicalAuthorityTokenStillMissing = refl

canonicalCalibrationStillMissing :
  instrumentCalibrationAccepted canonicalChemistryAuthorityBinding ≡ false
canonicalCalibrationStillMissing = refl

canonicalUncertaintyProvenanceStillMissing :
  uncertaintyProvenanceAccepted canonicalChemistryAuthorityBinding ≡ false
canonicalUncertaintyProvenanceStillMissing = refl

canonicalAuthorityBindingPhysicalChemistryPromotionIsFalse :
  physicalChemistryPromoted canonicalChemistryAuthorityBinding ≡ false
canonicalAuthorityBindingPhysicalChemistryPromotionIsFalse = refl

canonicalAuthorityBindingSpectroscopyPromotionIsFalse :
  spectroscopyPromoted canonicalChemistryAuthorityBinding ≡ false
canonicalAuthorityBindingSpectroscopyPromotionIsFalse = refl

canonicalAuthorityBindingWetLabPromotionIsFalse :
  wetLabValidationAccepted canonicalChemistryAuthorityBinding ≡ false
canonicalAuthorityBindingWetLabPromotionIsFalse = refl
