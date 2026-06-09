module DASHI.Physics.Closure.QuantumClockAuthorityReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.QuantumClockSuperpositionReceipt as R

------------------------------------------------------------------------
-- Quantum clock authority receipt surface.
--
-- This module records the concrete authority-facing surfaces needed to bind
-- an optical-ion quantum clock lane to an external measurement authority.  It
-- deliberately keeps the external measurement authority token constructorless:
-- symbolic phase, visibility, and squeezed-state surfaces are available, but
-- empirical promotion remains fail-closed until a provider supplies the
-- authority token and measurement payload.

data ⊥ : Set where

data _∈_ {A : Set} (x : A) : List A → Set where
  here :
    {xs : List A} →
    x ∈ (x ∷ xs)

  there :
    {y : A} →
    {xs : List A} →
    x ∈ xs →
    x ∈ (y ∷ xs)

data SqueezedStateClockPlatform : Set where
  opticalIonClockSqueezedStatePlatform :
    SqueezedStateClockPlatform

data SqueezedStateBindingField : Set where
  ionSpeciesAndClockTransition :
    SqueezedStateBindingField
  squeezedPreparationProtocol :
    SqueezedStateBindingField
  squeezingParameterConvention :
    SqueezedStateBindingField
  metrologicalGainCalibration :
    SqueezedStateBindingField
  noiseAndSystematicsBudget :
    SqueezedStateBindingField

canonicalSqueezedStateBindingFields :
  List SqueezedStateBindingField
canonicalSqueezedStateBindingFields =
  ionSpeciesAndClockTransition
  ∷ squeezedPreparationProtocol
  ∷ squeezingParameterConvention
  ∷ metrologicalGainCalibration
  ∷ noiseAndSystematicsBudget
  ∷ []

data PublicationAuthorityAnchor : Set where
  physicalReviewLettersQuantumClockRecord :
    PublicationAuthorityAnchor
  arxivQuantumClockPreprintRecord :
    PublicationAuthorityAnchor
  nistOpticalIonClockInstitutionRecord :
    PublicationAuthorityAnchor

canonicalPublicationAuthorityAnchors :
  List PublicationAuthorityAnchor
canonicalPublicationAuthorityAnchors =
  physicalReviewLettersQuantumClockRecord
  ∷ arxivQuantumClockPreprintRecord
  ∷ nistOpticalIonClockInstitutionRecord
  ∷ []

data QuantumClockLawSymbol : Set where
  DeltaPhi :
    QuantumClockLawSymbol
  Omega0 :
    QuantumClockLawSymbol
  DeltaTau :
    QuantumClockLawSymbol
  Visibility :
    QuantumClockLawSymbol
  VisibilityBaseline :
    QuantumClockLawSymbol
  VisibilityEnvelope :
    QuantumClockLawSymbol

data ExternalMeasurementAuthorityToken : Set where

externalMeasurementAuthorityTokenUnavailable :
  ExternalMeasurementAuthorityToken →
  ⊥
externalMeasurementAuthorityTokenUnavailable ()

data ExternalMeasurementBindingState : Set where
  failClosedAwaitingExternalMeasurementAuthority :
    ExternalMeasurementBindingState

record SqueezedStatePlatformBinding : Set where
  field
    platform :
      SqueezedStateClockPlatform

    bindingFields :
      List SqueezedStateBindingField

    bindingFieldsAreCanonical :
      bindingFields ≡ canonicalSqueezedStateBindingFields

    preparedClockReceipt :
      R.QuantumClockSuperpositionReceipt

    preparedClockReceiptIsCanonical :
      preparedClockReceipt ≡ R.canonicalQuantumClockSuperpositionReceipt

    platformBindingRequired :
      Bool

    platformBindingRequiredIsTrue :
      platformBindingRequired ≡ true

    bindingReading :
      String

open SqueezedStatePlatformBinding public

canonicalSqueezedStatePlatformBinding :
  SqueezedStatePlatformBinding
canonicalSqueezedStatePlatformBinding =
  record
    { platform =
        opticalIonClockSqueezedStatePlatform
    ; bindingFields =
        canonicalSqueezedStateBindingFields
    ; bindingFieldsAreCanonical =
        refl
    ; preparedClockReceipt =
        R.canonicalQuantumClockSuperpositionReceipt
    ; preparedClockReceiptIsCanonical =
        refl
    ; platformBindingRequired =
        true
    ; platformBindingRequiredIsTrue =
        refl
    ; bindingReading =
        "squeezed-state clock preparation must be bound to ion species, transition, squeezing convention, gain calibration, and systematics budget"
    }

record PRLArxivAuthorityBinding : Set where
  field
    anchors :
      List PublicationAuthorityAnchor

    anchorsAreCanonical :
      anchors ≡ canonicalPublicationAuthorityAnchors

    prlAnchorListed :
      physicalReviewLettersQuantumClockRecord ∈ anchors

    arxivAnchorListed :
      arxivQuantumClockPreprintRecord ∈ anchors

    stableCitationOrDigestRequired :
      Bool

    stableCitationOrDigestRequiredIsTrue :
      stableCitationOrDigestRequired ≡ true

    authorityReading :
      String

open PRLArxivAuthorityBinding public

canonicalPRLArxivAuthorityBinding :
  PRLArxivAuthorityBinding
canonicalPRLArxivAuthorityBinding =
  record
    { anchors =
        canonicalPublicationAuthorityAnchors
    ; anchorsAreCanonical =
        refl
    ; prlAnchorListed =
        here
    ; arxivAnchorListed =
        there here
    ; stableCitationOrDigestRequired =
        true
    ; stableCitationOrDigestRequiredIsTrue =
        refl
    ; authorityReading =
        "PRL peer-reviewed record and arXiv preprint record are authority anchors, but neither constructs the external measurement token locally"
    }

record PhaseLawBinding : Set where
  field
    leftHandSide :
      QuantumClockLawSymbol

    rightHandSide :
      List QuantumClockLawSymbol

    deltaPhiEqualsOmega0DeltaTau :
      String

    phaseLawExternalCalibrationRequired :
      Bool

    phaseLawExternalCalibrationRequiredIsTrue :
      phaseLawExternalCalibrationRequired ≡ true

open PhaseLawBinding public

canonicalPhaseLawBinding :
  PhaseLawBinding
canonicalPhaseLawBinding =
  record
    { leftHandSide =
        DeltaPhi
    ; rightHandSide =
        Omega0 ∷ DeltaTau ∷ []
    ; deltaPhiEqualsOmega0DeltaTau =
        "Delta phi = omega0 Delta tau"
    ; phaseLawExternalCalibrationRequired =
        true
    ; phaseLawExternalCalibrationRequiredIsTrue =
        refl
    }

record VisibilityModulationBinding : Set where
  field
    visibilityObservable :
      QuantumClockLawSymbol

    modulationTerms :
      List QuantumClockLawSymbol

    visibilityExternalReadoutRequired :
      Bool

    visibilityExternalReadoutRequiredIsTrue :
      visibilityExternalReadoutRequired ≡ true

    visibilityReading :
      String

open VisibilityModulationBinding public

canonicalVisibilityModulationBinding :
  VisibilityModulationBinding
canonicalVisibilityModulationBinding =
  record
    { visibilityObservable =
        Visibility
    ; modulationTerms =
        VisibilityBaseline ∷ VisibilityEnvelope ∷ DeltaTau ∷ []
    ; visibilityExternalReadoutRequired =
        true
    ; visibilityExternalReadoutRequiredIsTrue =
        refl
    ; visibilityReading =
        "visibility modulation is an externally read out contrast/envelope surface over proper-time branch separation"
    }

record FailClosedExternalMeasurementBinding : Set where
  field
    bindingState :
      ExternalMeasurementBindingState

    externalMeasurementBound :
      Bool

    externalMeasurementBoundIsFalse :
      externalMeasurementBound ≡ false

    authorityTokenConstructedHere :
      Bool

    authorityTokenConstructedHereIsFalse :
      authorityTokenConstructedHere ≡ false

    promotedEmpiricalClaim :
      Bool

    promotedEmpiricalClaimIsFalse :
      promotedEmpiricalClaim ≡ false

    noLocalExternalMeasurementAuthorityToken :
      ExternalMeasurementAuthorityToken →
      ⊥

    failClosedReading :
      String

open FailClosedExternalMeasurementBinding public

canonicalFailClosedExternalMeasurementBinding :
  FailClosedExternalMeasurementBinding
canonicalFailClosedExternalMeasurementBinding =
  record
    { bindingState =
        failClosedAwaitingExternalMeasurementAuthority
    ; externalMeasurementBound =
        false
    ; externalMeasurementBoundIsFalse =
        refl
    ; authorityTokenConstructedHere =
        false
    ; authorityTokenConstructedHereIsFalse =
        refl
    ; promotedEmpiricalClaim =
        false
    ; promotedEmpiricalClaimIsFalse =
        refl
    ; noLocalExternalMeasurementAuthorityToken =
        externalMeasurementAuthorityTokenUnavailable
    ; failClosedReading =
        "external measurement binding is fail-closed until a provider supplies an authority token and bound measurement payload"
    }

record QuantumClockAuthorityReceipt : Set where
  field
    squeezedStatePlatformBinding :
      SqueezedStatePlatformBinding

    prlArxivAuthorityBinding :
      PRLArxivAuthorityBinding

    phaseLawBinding :
      PhaseLawBinding

    visibilityModulationBinding :
      VisibilityModulationBinding

    failClosedExternalMeasurementBinding :
      FailClosedExternalMeasurementBinding

    receiptReading :
      String

open QuantumClockAuthorityReceipt public

canonicalQuantumClockAuthorityReceipt :
  QuantumClockAuthorityReceipt
canonicalQuantumClockAuthorityReceipt =
  record
    { squeezedStatePlatformBinding =
        canonicalSqueezedStatePlatformBinding
    ; prlArxivAuthorityBinding =
        canonicalPRLArxivAuthorityBinding
    ; phaseLawBinding =
        canonicalPhaseLawBinding
    ; visibilityModulationBinding =
        canonicalVisibilityModulationBinding
    ; failClosedExternalMeasurementBinding =
        canonicalFailClosedExternalMeasurementBinding
    ; receiptReading =
        "quantum clock authority receipt binds squeezed-state platform fields, PRL/arXiv authority anchors, phase law, visibility modulation, and fail-closed external measurement authority"
    }

canonicalAuthorityReceiptPhaseLaw :
  deltaPhiEqualsOmega0DeltaTau
    (phaseLawBinding canonicalQuantumClockAuthorityReceipt)
  ≡
  "Delta phi = omega0 Delta tau"
canonicalAuthorityReceiptPhaseLaw = refl

canonicalAuthorityReceiptFailsClosed :
  externalMeasurementBound
    (failClosedExternalMeasurementBinding
      canonicalQuantumClockAuthorityReceipt)
  ≡
  false
canonicalAuthorityReceiptFailsClosed = refl
