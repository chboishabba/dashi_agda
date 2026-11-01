module DASHI.Promotion.RydbergSpectroscopyAuthorityPayloadRequest where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Promotion.ChemistryAuthorityBinding as Chemistry
import DASHI.Promotion.NumericAuthorityPayloadValidator as Payload
import DASHI.Promotion.NumericMeasuredAuthorityTokenNormalization as Tokens
import DASHI.Promotion.RydbergClockMetreBridge as Rydberg
import DASHI.Promotion.SIMetreFromSecondAndCAdapter as Metre

------------------------------------------------------------------------
-- Rydberg spectroscopy authority-payload request.
--
-- This is the fail-closed authority surface downstream of the SI metre
-- adapter.  The metre and wavenumber dimension routes are already typed by
-- SIMetreFromSecondAndCAdapter.  Spectroscopy still requires external
-- CODATA/NIST evidence:
--   * R_infinity measured payload;
--   * electron/proton mass payloads for reduced-mass adapters;
--   * NIST ASD line token with isotope, wavelength, and calibration fields;
--   * systematics/covariance receipts;
--   * a terminal promotion token.
--
-- No measured value is ingested here, no CODATA or NIST artifact is accepted,
-- and no chemistry/spectroscopy promotion is constructed.

data RydbergAuthorityPayloadField : Set where
  authorityArtifactField :
    RydbergAuthorityPayloadField

  authorityDigestField :
    RydbergAuthorityPayloadField

  authorityAccessDateField :
    RydbergAuthorityPayloadField

  rawNumericTextField :
    RydbergAuthorityPayloadField

  rawUncertaintyTextField :
    RydbergAuthorityPayloadField

  parsedNumericCarrierField :
    RydbergAuthorityPayloadField

  covarianceOrAdjustmentField :
    RydbergAuthorityPayloadField

  unitConventionField :
    RydbergAuthorityPayloadField

  dimensionVectorWitnessField :
    RydbergAuthorityPayloadField

  consumerIngestionReceiptField :
    RydbergAuthorityPayloadField

canonicalRydbergAuthorityPayloadFields :
  List RydbergAuthorityPayloadField
canonicalRydbergAuthorityPayloadFields =
  authorityArtifactField
  ∷ authorityDigestField
  ∷ authorityAccessDateField
  ∷ rawNumericTextField
  ∷ rawUncertaintyTextField
  ∷ parsedNumericCarrierField
  ∷ covarianceOrAdjustmentField
  ∷ unitConventionField
  ∷ dimensionVectorWitnessField
  ∷ consumerIngestionReceiptField
  ∷ []

fieldKeyCount : List RydbergAuthorityPayloadField → Nat
fieldKeyCount [] =
  zero
fieldKeyCount (_ ∷ xs) =
  suc (fieldKeyCount xs)

record AuthorityPayloadRequirementRow : Set₁ where
  field
    fieldKey :
      RydbergAuthorityPayloadField

    fieldName :
      String

    requiredEvidence :
      Payload.PayloadSchemaField

    providerFamily :
      String

    consumerSurface :
      String

    rowAccepted :
      Bool

    rowAcceptedIsFalse :
      rowAccepted ≡ false

    rowPromotesSpectroscopy :
      Bool

    rowPromotesSpectroscopyIsFalse :
      rowPromotesSpectroscopy ≡ false

open AuthorityPayloadRequirementRow public

authorityPayloadRowCount : List AuthorityPayloadRequirementRow → Nat
authorityPayloadRowCount [] =
  zero
authorityPayloadRowCount (_ ∷ xs) =
  suc (authorityPayloadRowCount xs)

mkOpenPayloadRow :
  RydbergAuthorityPayloadField →
  String →
  Payload.PayloadSchemaField →
  String →
  String →
  AuthorityPayloadRequirementRow
mkOpenPayloadRow key name evidence provider consumer =
  record
    { fieldKey =
        key
    ; fieldName =
        name
    ; requiredEvidence =
        evidence
    ; providerFamily =
        provider
    ; consumerSurface =
        consumer
    ; rowAccepted =
        false
    ; rowAcceptedIsFalse =
        refl
    ; rowPromotesSpectroscopy =
        false
    ; rowPromotesSpectroscopyIsFalse =
        refl
    }

record RInfinityCODATAPayloadRequest : Set₁ where
  field
    requestLabel :
      String

    normalizedToken :
      Tokens.NormalizedMeasuredAuthorityToken

    tokenSymbol :
      String

    tokenSymbolIsRInfinity :
      tokenSymbol ≡ "R_infinity"

    codataAuthorityFamily :
      Payload.PayloadSourceFamily

    wavenumberRoute :
      Metre.SIMetreDimensionRoute

    lengthExponentIsMinusOne :
      Rydberg.lengthExponent
        (Metre.SIMetreDimensionRoute.dimensionRoute wavenumberRoute)
      ≡
      Rydberg.minusOne

    timeExponentIsZero :
      Rydberg.timeExponent
        (Metre.SIMetreDimensionRoute.dimensionRoute wavenumberRoute)
      ≡
      Rydberg.zero

    payloadFields :
      List AuthorityPayloadRequirementRow

    payloadFieldCount :
      Nat

    payloadFieldCountIs10 :
      payloadFieldCount ≡ 10

    codataArtifactAccepted :
      Bool

    codataArtifactAcceptedIsFalse :
      codataArtifactAccepted ≡ false

    parsedNumericCarrierLoaded :
      Bool

    parsedNumericCarrierLoadedIsFalse :
      parsedNumericCarrierLoaded ≡ false

    payloadPromoted :
      Bool

    payloadPromotedIsFalse :
      payloadPromoted ≡ false

open RInfinityCODATAPayloadRequest public

canonicalRInfinityPayloadRows : List AuthorityPayloadRequirementRow
canonicalRInfinityPayloadRows =
  mkOpenPayloadRow
    authorityArtifactField
    "CODATA authority artifact"
    Payload.missingAuthorityArtifactField
    "NIST CODATA fundamental physical constants"
    "RInfinityCODATAPayloadRequest"
  ∷ mkOpenPayloadRow
    authorityDigestField
    "CODATA artifact SHA-256"
    Payload.missingArtifactDigestField
    "NIST CODATA fundamental physical constants"
    "RInfinityCODATAPayloadRequest"
  ∷ mkOpenPayloadRow
    authorityAccessDateField
    "CODATA access-date evidence"
    Payload.missingAccessEvidenceField
    "NIST CODATA fundamental physical constants"
    "RInfinityCODATAPayloadRequest"
  ∷ mkOpenPayloadRow
    rawNumericTextField
    "R_infinity raw numeric value text"
    Payload.missingRawValueTextField
    "NIST CODATA fundamental physical constants"
    "RInfinityCODATAPayloadRequest"
  ∷ mkOpenPayloadRow
    rawUncertaintyTextField
    "R_infinity raw uncertainty text"
    Payload.missingRawUncertaintyTextField
    "NIST CODATA fundamental physical constants"
    "RInfinityCODATAPayloadRequest"
  ∷ mkOpenPayloadRow
    parsedNumericCarrierField
    "R_infinity parsed numeric carrier"
    Payload.missingParsedCarrierField
    "NIST CODATA fundamental physical constants"
    "RInfinityCODATAPayloadRequest"
  ∷ mkOpenPayloadRow
    covarianceOrAdjustmentField
    "R_infinity covariance or adjustment receipt"
    Payload.missingCovarianceField
    "NIST CODATA fundamental physical constants"
    "RInfinityCODATAPayloadRequest"
  ∷ mkOpenPayloadRow
    unitConventionField
    "R_infinity m^-1 unit convention"
    Payload.missingUnitFactorizationReceiptField
    "NIST CODATA fundamental physical constants"
    "RInfinityCODATAPayloadRequest"
  ∷ mkOpenPayloadRow
    dimensionVectorWitnessField
    "R_infinity dimension-vector witness"
    Payload.missingDimensionVectorWitnessField
    "NIST CODATA fundamental physical constants"
    "RInfinityCODATAPayloadRequest"
  ∷ mkOpenPayloadRow
    consumerIngestionReceiptField
    "R_infinity spectroscopy consumer ingestion receipt"
    Payload.missingConsumerIngestionReceiptField
    "NIST CODATA fundamental physical constants"
    "RInfinityCODATAPayloadRequest"
  ∷ []

canonicalRInfinityCODATAPayloadRequest :
  RInfinityCODATAPayloadRequest
canonicalRInfinityCODATAPayloadRequest =
  record
    { requestLabel =
        "CODATA measured R_infinity payload request for Rydberg spectroscopy"
    ; normalizedToken =
        Tokens.rydbergNormalizedToken
    ; tokenSymbol =
        Tokens.NormalizedMeasuredAuthorityToken.normalizedSymbol
          Tokens.rydbergNormalizedToken
    ; tokenSymbolIsRInfinity =
        refl
    ; codataAuthorityFamily =
        Payload.codataPayloadFamily
    ; wavenumberRoute =
        Metre.wavenumberUnitDimensionRoute
    ; lengthExponentIsMinusOne =
        refl
    ; timeExponentIsZero =
        refl
    ; payloadFields =
        canonicalRInfinityPayloadRows
    ; payloadFieldCount =
        authorityPayloadRowCount canonicalRInfinityPayloadRows
    ; payloadFieldCountIs10 =
        refl
    ; codataArtifactAccepted =
        Tokens.NormalizedMeasuredAuthorityToken.acceptedAuthorityTokenPresent
          Tokens.rydbergNormalizedToken
    ; codataArtifactAcceptedIsFalse =
        Tokens.NormalizedMeasuredAuthorityToken.acceptedAuthorityTokenPresentIsFalse
          Tokens.rydbergNormalizedToken
    ; parsedNumericCarrierLoaded =
        Tokens.NormalizedMeasuredAuthorityToken.numericValueLoaded
          Tokens.rydbergNormalizedToken
    ; parsedNumericCarrierLoadedIsFalse =
        Tokens.NormalizedMeasuredAuthorityToken.numericValueLoadedIsFalse
          Tokens.rydbergNormalizedToken
    ; payloadPromoted =
        Tokens.NormalizedMeasuredAuthorityToken.numericValuePromoted
          Tokens.rydbergNormalizedToken
    ; payloadPromotedIsFalse =
        Tokens.NormalizedMeasuredAuthorityToken.numericValuePromotedIsFalse
          Tokens.rydbergNormalizedToken
    }

data ReducedMassDependencyKind : Set where
  electronMassDependency :
    ReducedMassDependencyKind

  protonMassDependency :
    ReducedMassDependencyKind

  isotopeNuclearMassDependency :
    ReducedMassDependencyKind

  reducedMassConventionDependency :
    ReducedMassDependencyKind

record ReducedMassDependencyRow : Set₁ where
  field
    dependencyKind :
      ReducedMassDependencyKind

    dependencyLabel :
      String

    normalizedToken :
      Tokens.NormalizedMeasuredAuthorityToken

    registrySlotRef :
      String

    unitConvention :
      String

    requiredForFormula :
      String

    acceptedAuthorityToken :
      Bool

    acceptedAuthorityTokenIsFalse :
      acceptedAuthorityToken ≡ false

    numericValueLoaded :
      Bool

    numericValueLoadedIsFalse :
      numericValueLoaded ≡ false

open ReducedMassDependencyRow public

mkMassDependencyRow :
  ReducedMassDependencyKind →
  String →
  Tokens.NormalizedMeasuredAuthorityToken →
  String →
  String →
  String →
  ReducedMassDependencyRow
mkMassDependencyRow kind label token slot unit formula =
  record
    { dependencyKind =
        kind
    ; dependencyLabel =
        label
    ; normalizedToken =
        token
    ; registrySlotRef =
        slot
    ; unitConvention =
        unit
    ; requiredForFormula =
        formula
    ; acceptedAuthorityToken =
        Tokens.NormalizedMeasuredAuthorityToken.acceptedAuthorityTokenPresent token
    ; acceptedAuthorityTokenIsFalse =
        Tokens.NormalizedMeasuredAuthorityToken.acceptedAuthorityTokenPresentIsFalse token
    ; numericValueLoaded =
        Tokens.NormalizedMeasuredAuthorityToken.numericValueLoaded token
    ; numericValueLoadedIsFalse =
        Tokens.NormalizedMeasuredAuthorityToken.numericValueLoadedIsFalse token
    }

electronMassReducedMassDependency :
  ReducedMassDependencyRow
electronMassReducedMassDependency =
  mkMassDependencyRow
    electronMassDependency
    "electron rest-mass authority for reduced-mass adapter"
    Tokens.electronMassNormalizedToken
    "DASHI.Constants.Registry.measuredPhysicsConstantAuthoritySlots.m_e"
    "kg"
    "mu = m_e * M_nucleus / (m_e + M_nucleus)"

protonMassReducedMassDependency :
  ReducedMassDependencyRow
protonMassReducedMassDependency =
  mkMassDependencyRow
    protonMassDependency
    "proton rest-mass authority for hydrogen isotope adapter"
    Tokens.protonMassNormalizedToken
    "DASHI.Constants.Registry.measuredPhysicsConstantAuthoritySlots.m_p"
    "kg"
    "R_H = R_infinity * m_p / (m_e + m_p)"

record IsotopeNuclearMassAuthorityRequest : Set₁ where
  field
    requestLabel :
      String

    isotopeSpeciesText :
      String

    nuclearMassAuthorityProvider :
      String

    nuclearMassRawValueRequired :
      Bool

    nuclearMassRawValueRequiredIsTrue :
      nuclearMassRawValueRequired ≡ true

    chargeStateAndMassModelRequired :
      Bool

    chargeStateAndMassModelRequiredIsTrue :
      chargeStateAndMassModelRequired ≡ true

    acceptedIsotopeMassToken :
      Bool

    acceptedIsotopeMassTokenIsFalse :
      acceptedIsotopeMassToken ≡ false

open IsotopeNuclearMassAuthorityRequest public

canonicalHydrogenIsotopeMassAuthorityRequest :
  IsotopeNuclearMassAuthorityRequest
canonicalHydrogenIsotopeMassAuthorityRequest =
  record
    { requestLabel =
        "hydrogen isotope nuclear-mass authority request"
    ; isotopeSpeciesText =
        "H-1 neutral hydrogen; isotope/nuclear mass policy still external"
    ; nuclearMassAuthorityProvider =
        "NIST CODATA or provider isotope-mass table"
    ; nuclearMassRawValueRequired =
        true
    ; nuclearMassRawValueRequiredIsTrue =
        refl
    ; chargeStateAndMassModelRequired =
        true
    ; chargeStateAndMassModelRequiredIsTrue =
        refl
    ; acceptedIsotopeMassToken =
        false
    ; acceptedIsotopeMassTokenIsFalse =
        refl
    }

record ReducedMassAdapterPayloadRequest : Set₁ where
  field
    adapterLabel :
      String

    electronMassDependencyRow :
      ReducedMassDependencyRow

    protonMassDependencyRow :
      ReducedMassDependencyRow

    isotopeMassAuthorityRequest :
      IsotopeNuclearMassAuthorityRequest

    reducedMassFormulaText :
      String

    hydrogenReducedRydbergFormulaText :
      String

    massRatioDimensionless :
      Bool

    massRatioDimensionlessIsTrue :
      massRatioDimensionless ≡ true

    reducedMassAdapterRequired :
      Bool

    reducedMassAdapterRequiredIsTrue :
      reducedMassAdapterRequired ≡ true

    reducedMassAdapterAccepted :
      Bool

    reducedMassAdapterAcceptedIsFalse :
      reducedMassAdapterAccepted ≡ false

open ReducedMassAdapterPayloadRequest public

canonicalReducedMassAdapterPayloadRequest :
  ReducedMassAdapterPayloadRequest
canonicalReducedMassAdapterPayloadRequest =
  record
    { adapterLabel =
        "reduced-mass adapter request for hydrogenic Rydberg lines"
    ; electronMassDependencyRow =
        electronMassReducedMassDependency
    ; protonMassDependencyRow =
        protonMassReducedMassDependency
    ; isotopeMassAuthorityRequest =
        canonicalHydrogenIsotopeMassAuthorityRequest
    ; reducedMassFormulaText =
        "mu = m_e * M_nucleus / (m_e + M_nucleus)"
    ; hydrogenReducedRydbergFormulaText =
        "R_H = R_infinity * m_p / (m_e + m_p)"
    ; massRatioDimensionless =
        true
    ; massRatioDimensionlessIsTrue =
        refl
    ; reducedMassAdapterRequired =
        Rydberg.isotopeReducedMassAdapterStillRequired
          Rydberg.canonicalRydbergClockMetreBridge
    ; reducedMassAdapterRequiredIsTrue =
        Rydberg.canonicalBridgeReducedMassAdapterStillRequired
    ; reducedMassAdapterAccepted =
        false
    ; reducedMassAdapterAcceptedIsFalse =
        refl
    }

record NISTASDSpectralLineTokenRequest : Set₁ where
  field
    requestLabel :
      String

    authorityBinding :
      Chemistry.AuthorityTokenBinding

    lineBinding :
      Chemistry.SpectralLineAuthorityBinding

    providerUri :
      String

    transitionAssignment :
      String

    wavelengthConventionRequired :
      Bool

    wavelengthConventionRequiredIsTrue :
      wavelengthConventionRequired ≡ true

    calibrationResidualRequired :
      Bool

    calibrationResidualRequiredIsTrue :
      calibrationResidualRequired ≡ true

    nistASDTokenRequired :
      Bool

    nistASDTokenRequiredIsTrue :
      nistASDTokenRequired ≡ true

    nistASDTokenAccepted :
      Bool

    nistASDTokenAcceptedIsFalse :
      nistASDTokenAccepted ≡ false

open NISTASDSpectralLineTokenRequest public

canonicalNISTASDSpectralLineTokenRequest :
  NISTASDSpectralLineTokenRequest
canonicalNISTASDSpectralLineTokenRequest =
  record
    { requestLabel =
        "NIST ASD spectral-line token request for Balmer-alpha"
    ; authorityBinding =
        Chemistry.mkAuthorityToken
          "NIST ASD spectral-line token"
          Chemistry.nistAtomicSpectraDatabase
          "Registry authority source slot: NIST spectral line authority"
          "RydbergSpectroscopyAuthorityPayloadRequest"
          "NISTASDSpectralLineTokenRequest"
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
    ; lineBinding =
        Chemistry.mkSpectralLineBinding
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
    ; providerUri =
        "https://physics.nist.gov/asd"
    ; transitionAssignment =
        "hydrogen Balmer-alpha; n = 3 -> 2; species and charge state required"
    ; wavelengthConventionRequired =
        true
    ; wavelengthConventionRequiredIsTrue =
        refl
    ; calibrationResidualRequired =
        true
    ; calibrationResidualRequiredIsTrue =
        refl
    ; nistASDTokenRequired =
        Rydberg.nistASDSpectralLineTokenStillRequired
          Rydberg.canonicalRydbergClockMetreBridge
    ; nistASDTokenRequiredIsTrue =
        Rydberg.canonicalBridgeNISTASDTokenStillRequired
    ; nistASDTokenAccepted =
        Chemistry.SpectralLineAuthorityBinding.spectralLineAuthorityAccepted
          (Chemistry.mkSpectralLineBinding
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
            ))
    ; nistASDTokenAcceptedIsFalse =
        refl
    }

record IsotopeAndSystematicsPayloadRequest : Set₁ where
  field
    requestLabel :
      String

    isotopeSpecies :
      String

    vacuumOrAirWavelengthConvention :
      String

    finiteNuclearMassCorrection :
      String

    isotopeShiftCorrection :
      String

    recoilAndFineStructurePolicy :
      String

    environmentalSystematics :
      List String

    systematicsBudgetRequired :
      Bool

    systematicsBudgetRequiredIsTrue :
      systematicsBudgetRequired ≡ true

    apparatusCalibrationRequired :
      Bool

    apparatusCalibrationRequiredIsTrue :
      apparatusCalibrationRequired ≡ true

    systematicsAccepted :
      Bool

    systematicsAcceptedIsFalse :
      systematicsAccepted ≡ false

open IsotopeAndSystematicsPayloadRequest public

canonicalIsotopeAndSystematicsPayloadRequest :
  IsotopeAndSystematicsPayloadRequest
canonicalIsotopeAndSystematicsPayloadRequest =
  record
    { requestLabel =
        "isotope and spectroscopy-systematics request for Rydberg line use"
    ; isotopeSpecies =
        "hydrogen isotope/species field required by NIST ASD line token"
    ; vacuumOrAirWavelengthConvention =
        "vacuum-or-air wavelength convention must be bound by the line token"
    ; finiteNuclearMassCorrection =
        "reduced-mass correction must consume m_e and nuclear-mass authority"
    ; isotopeShiftCorrection =
        "isotope shift, if used, requires provider value and uncertainty"
    ; recoilAndFineStructurePolicy =
        "recoil, fine-structure, and Lamb-shift model terms require explicit policy"
    ; environmentalSystematics =
        "pressure shift"
        ∷ "Zeeman shift"
        ∷ "Stark shift"
        ∷ "Doppler or recoil correction"
        ∷ "instrument line-shape calibration"
        ∷ []
    ; systematicsBudgetRequired =
        true
    ; systematicsBudgetRequiredIsTrue =
        refl
    ; apparatusCalibrationRequired =
        true
    ; apparatusCalibrationRequiredIsTrue =
        refl
    ; systematicsAccepted =
        false
    ; systematicsAcceptedIsFalse =
        refl
    }

record RydbergSpectroscopyPromotionGuards : Set₁ where
  field
    guardsLabel :
      String

    metreAdapter :
      Metre.SIMetreFromSecondAndCAdapter

    rydbergBridge :
      Rydberg.RydbergClockMetreBridge

    numericPayloadValidator :
      Payload.NumericAuthorityPayloadValidatorReceipt

    metreCarrierAvailable :
      Bool

    metreCarrierAvailableIsTrue :
      metreCarrierAvailable ≡ true

    rInfinityPayloadRequired :
      Bool

    rInfinityPayloadRequiredIsTrue :
      rInfinityPayloadRequired ≡ true

    reducedMassAdapterRequired :
      Bool

    reducedMassAdapterRequiredIsTrue :
      reducedMassAdapterRequired ≡ true

    nistASDTokenRequired :
      Bool

    nistASDTokenRequiredIsTrue :
      nistASDTokenRequired ≡ true

    codataAuthorityTokenPresent :
      Bool

    codataAuthorityTokenPresentIsFalse :
      codataAuthorityTokenPresent ≡ false

    nistASDTokenPresent :
      Bool

    nistASDTokenPresentIsFalse :
      nistASDTokenPresent ≡ false

    spectroscopyPromoted :
      Bool

    spectroscopyPromotedIsFalse :
      spectroscopyPromoted ≡ false

open RydbergSpectroscopyPromotionGuards public

canonicalRydbergSpectroscopyPromotionGuards :
  RydbergSpectroscopyPromotionGuards
canonicalRydbergSpectroscopyPromotionGuards =
  record
    { guardsLabel =
        "Rydberg spectroscopy remains fail-closed after metre/wavenumber typing"
    ; metreAdapter =
        Metre.canonicalSIMetreFromSecondAndCAdapter
    ; rydbergBridge =
        Rydberg.canonicalRydbergClockMetreBridge
    ; numericPayloadValidator =
        Payload.canonicalNumericAuthorityPayloadValidatorReceipt
    ; metreCarrierAvailable =
        Metre.SIMetreFromSecondAndCAdapter.derivedMetreCarrierAvailable
          Metre.canonicalSIMetreFromSecondAndCAdapter
    ; metreCarrierAvailableIsTrue =
        Metre.canonicalAdapterDerivedMetreCarrierAvailable
    ; rInfinityPayloadRequired =
        Rydberg.rInfinityCODATAMeasuredPayloadStillRequired
          Rydberg.canonicalRydbergClockMetreBridge
    ; rInfinityPayloadRequiredIsTrue =
        Rydberg.canonicalBridgeRydbergMeasuredPayloadStillRequired
    ; reducedMassAdapterRequired =
        Rydberg.isotopeReducedMassAdapterStillRequired
          Rydberg.canonicalRydbergClockMetreBridge
    ; reducedMassAdapterRequiredIsTrue =
        Rydberg.canonicalBridgeReducedMassAdapterStillRequired
    ; nistASDTokenRequired =
        Rydberg.nistASDSpectralLineTokenStillRequired
          Rydberg.canonicalRydbergClockMetreBridge
    ; nistASDTokenRequiredIsTrue =
        Rydberg.canonicalBridgeNISTASDTokenStillRequired
    ; codataAuthorityTokenPresent =
        Rydberg.acceptedAuthorityTokenPresent
          Rydberg.canonicalRydbergClockMetreBridge
    ; codataAuthorityTokenPresentIsFalse =
        Rydberg.canonicalBridgeAuthorityTokenStillMissing
    ; nistASDTokenPresent =
        Chemistry.SpectralLineAuthorityBinding.spectralLineAuthorityAccepted
          (NISTASDSpectralLineTokenRequest.lineBinding
            canonicalNISTASDSpectralLineTokenRequest)
    ; nistASDTokenPresentIsFalse =
        Chemistry.SpectralLineAuthorityBinding.spectralLineAuthorityAcceptedIsFalse
          (NISTASDSpectralLineTokenRequest.lineBinding
            canonicalNISTASDSpectralLineTokenRequest)
    ; spectroscopyPromoted =
        Rydberg.spectroscopyPromotion
          Rydberg.canonicalRydbergClockMetreBridge
    ; spectroscopyPromotedIsFalse =
        Rydberg.canonicalBridgeSpectroscopyPromotionIsFalse
    }

record RydbergSpectroscopyAuthorityPayloadRequestManifest : Set₁ where
  field
    manifestLabel :
      String

    sourceRefs :
      List String

    rInfinityPayloadRequest :
      RInfinityCODATAPayloadRequest

    reducedMassAdapterRequest :
      ReducedMassAdapterPayloadRequest

    nistASDLineTokenRequest :
      NISTASDSpectralLineTokenRequest

    isotopeSystematicsRequest :
      IsotopeAndSystematicsPayloadRequest

    promotionGuards :
      RydbergSpectroscopyPromotionGuards

    authorityPayloadRows :
      List AuthorityPayloadRequirementRow

    authorityPayloadFieldKeys :
      List RydbergAuthorityPayloadField

    authorityPayloadFieldKeyCount :
      Nat

    authorityPayloadFieldKeyCountIs10 :
      authorityPayloadFieldKeyCount ≡ 10

    downstreamOfMetreAdapter :
      Bool

    downstreamOfMetreAdapterIsTrue :
      downstreamOfMetreAdapter ≡ true

    constructsCODATAPayload :
      Bool

    constructsCODATAPayloadIsFalse :
      constructsCODATAPayload ≡ false

    constructsNISTASDToken :
      Bool

    constructsNISTASDTokenIsFalse :
      constructsNISTASDToken ≡ false

    spectroscopyPromotion :
      Bool

    spectroscopyPromotionIsFalse :
      spectroscopyPromotion ≡ false

open RydbergSpectroscopyAuthorityPayloadRequestManifest public

canonicalRydbergSpectroscopySourceRefs :
  List String
canonicalRydbergSpectroscopySourceRefs =
  "DASHI.Promotion.SIMetreFromSecondAndCAdapter"
  ∷ "DASHI.Promotion.RydbergClockMetreBridge"
  ∷ "DASHI.Promotion.NumericAuthorityPayloadValidator"
  ∷ "DASHI.Promotion.NumericMeasuredAuthorityTokenNormalization"
  ∷ "DASHI.Promotion.ChemistryAuthorityBinding"
  ∷ []

canonicalRydbergSpectroscopyAuthorityPayloadRequestManifest :
  RydbergSpectroscopyAuthorityPayloadRequestManifest
canonicalRydbergSpectroscopyAuthorityPayloadRequestManifest =
  record
    { manifestLabel =
        "fail-closed Rydberg spectroscopy authority-payload request manifest"
    ; sourceRefs =
        canonicalRydbergSpectroscopySourceRefs
    ; rInfinityPayloadRequest =
        canonicalRInfinityCODATAPayloadRequest
    ; reducedMassAdapterRequest =
        canonicalReducedMassAdapterPayloadRequest
    ; nistASDLineTokenRequest =
        canonicalNISTASDSpectralLineTokenRequest
    ; isotopeSystematicsRequest =
        canonicalIsotopeAndSystematicsPayloadRequest
    ; promotionGuards =
        canonicalRydbergSpectroscopyPromotionGuards
    ; authorityPayloadRows =
        canonicalRInfinityPayloadRows
    ; authorityPayloadFieldKeys =
        canonicalRydbergAuthorityPayloadFields
    ; authorityPayloadFieldKeyCount =
        fieldKeyCount canonicalRydbergAuthorityPayloadFields
    ; authorityPayloadFieldKeyCountIs10 =
        refl
    ; downstreamOfMetreAdapter =
        true
    ; downstreamOfMetreAdapterIsTrue =
        refl
    ; constructsCODATAPayload =
        false
    ; constructsCODATAPayloadIsFalse =
        refl
    ; constructsNISTASDToken =
        false
    ; constructsNISTASDTokenIsFalse =
        refl
    ; spectroscopyPromotion =
        RydbergSpectroscopyPromotionGuards.spectroscopyPromoted
          canonicalRydbergSpectroscopyPromotionGuards
    ; spectroscopyPromotionIsFalse =
        RydbergSpectroscopyPromotionGuards.spectroscopyPromotedIsFalse
          canonicalRydbergSpectroscopyPromotionGuards
    }

canonicalRydbergRequestFieldKeyCountIs10 :
  fieldKeyCount canonicalRydbergAuthorityPayloadFields ≡ 10
canonicalRydbergRequestFieldKeyCountIs10 =
  refl

canonicalRInfinityPayloadFieldCountIs10 :
  RInfinityCODATAPayloadRequest.payloadFieldCount
    canonicalRInfinityCODATAPayloadRequest
  ≡
  10
canonicalRInfinityPayloadFieldCountIs10 =
  refl

canonicalRInfinityPayloadPromotedIsFalse :
  RInfinityCODATAPayloadRequest.payloadPromoted
    canonicalRInfinityCODATAPayloadRequest
  ≡
  false
canonicalRInfinityPayloadPromotedIsFalse =
  RInfinityCODATAPayloadRequest.payloadPromotedIsFalse
    canonicalRInfinityCODATAPayloadRequest

canonicalReducedMassAdapterAcceptedIsFalse :
  ReducedMassAdapterPayloadRequest.reducedMassAdapterAccepted
    canonicalReducedMassAdapterPayloadRequest
  ≡
  false
canonicalReducedMassAdapterAcceptedIsFalse =
  refl

canonicalNISTASDTokenAcceptedIsFalse :
  NISTASDSpectralLineTokenRequest.nistASDTokenAccepted
    canonicalNISTASDSpectralLineTokenRequest
  ≡
  false
canonicalNISTASDTokenAcceptedIsFalse =
  NISTASDSpectralLineTokenRequest.nistASDTokenAcceptedIsFalse
    canonicalNISTASDSpectralLineTokenRequest

canonicalRydbergSpectroscopyPromotionIsFalse :
  RydbergSpectroscopyAuthorityPayloadRequestManifest.spectroscopyPromotion
    canonicalRydbergSpectroscopyAuthorityPayloadRequestManifest
  ≡
  false
canonicalRydbergSpectroscopyPromotionIsFalse =
  RydbergSpectroscopyAuthorityPayloadRequestManifest.spectroscopyPromotionIsFalse
    canonicalRydbergSpectroscopyAuthorityPayloadRequestManifest
