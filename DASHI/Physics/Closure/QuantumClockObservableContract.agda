module DASHI.Physics.Closure.QuantumClockObservableContract where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.QuantumClockSuperpositionReceipt as R
import DASHI.Physics.Closure.QuantumClockAuthorityReceipt as A

------------------------------------------------------------------------
-- Optical-ion-clock empirical contact contract.
--
-- This module keeps the quantum-clock receipt prediction/contact-ready:
-- it records symbolic observables for a proper-time superposition lane, but
-- constructs no external empirical authority token and claims no observed
-- result.  Promotion remains fail-closed until an external NIST/PRL binding
-- supplies the required measurement authority fields.

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

data QuantumClockObservableContractStatus : Set where
  opticalIonClockProperTimeSuperpositionContactReadyNoPromotion :
    QuantumClockObservableContractStatus

data OpticalClockAuthorityLane : Set where
  nistOpticalIonClockAuthorityLane :
    OpticalClockAuthorityLane
  prlPeerReviewedAuthorityLane :
    OpticalClockAuthorityLane
  externalProviderBindingLane :
    OpticalClockAuthorityLane

canonicalAuthorityLanes :
  List OpticalClockAuthorityLane
canonicalAuthorityLanes =
  nistOpticalIonClockAuthorityLane
  ∷ prlPeerReviewedAuthorityLane
  ∷ externalProviderBindingLane
  ∷ []

nistAuthorityLaneListed :
  nistOpticalIonClockAuthorityLane ∈ canonicalAuthorityLanes
nistAuthorityLaneListed = here

prlAuthorityLaneListed :
  prlPeerReviewedAuthorityLane ∈ canonicalAuthorityLanes
prlAuthorityLaneListed = there here

data QuantumClockObservableKind : Set where
  phaseProperTimeShift :
    QuantumClockObservableKind
  visibilityModulation :
    QuantumClockObservableKind
  squeezedStateEnhancement :
    QuantumClockObservableKind

canonicalObservableKinds :
  List QuantumClockObservableKind
canonicalObservableKinds =
  phaseProperTimeShift
  ∷ visibilityModulation
  ∷ squeezedStateEnhancement
  ∷ []

data SymbolicTerm : Set where
  deltaPhi :
    SymbolicTerm
  omega0 :
    SymbolicTerm
  deltaTau :
    SymbolicTerm
  visibility :
    SymbolicTerm
  visibilityBaseline :
    SymbolicTerm
  visibilityModulationEnvelope :
    SymbolicTerm
  squeezingParameter :
    SymbolicTerm
  metrologicalEnhancementFactor :
    SymbolicTerm

data SymbolicMeasurementLaw : Set where
  phaseEqualsCarrierFrequencyTimesProperTimeDifference :
    SymbolicMeasurementLaw
  visibilityDependsOnProperTimeBranchCoherence :
    SymbolicMeasurementLaw
  squeezedStateParameterMustBeExternallyCalibrated :
    SymbolicMeasurementLaw

observableLaw :
  QuantumClockObservableKind →
  SymbolicMeasurementLaw
observableLaw phaseProperTimeShift =
  phaseEqualsCarrierFrequencyTimesProperTimeDifference
observableLaw visibilityModulation =
  visibilityDependsOnProperTimeBranchCoherence
observableLaw squeezedStateEnhancement =
  squeezedStateParameterMustBeExternallyCalibrated

record SymbolicObservableDescriptor : Set where
  constructor mkSymbolicObservableDescriptor
  field
    observableKind :
      QuantumClockObservableKind

    law :
      SymbolicMeasurementLaw

    lawMatchesKind :
      law ≡ observableLaw observableKind

    leftHandSide :
      SymbolicTerm

    rightHandSideTerms :
      List SymbolicTerm

    equationLabel :
      String

    unitConvention :
      String

    externalBindingRequired :
      Bool

    externalBindingRequiredIsTrue :
      externalBindingRequired ≡ true

open SymbolicObservableDescriptor public

phaseObservableDescriptor :
  SymbolicObservableDescriptor
phaseObservableDescriptor =
  mkSymbolicObservableDescriptor
    phaseProperTimeShift
    phaseEqualsCarrierFrequencyTimesProperTimeDifference
    refl
    deltaPhi
    (omega0 ∷ deltaTau ∷ [])
    "Delta phi = omega0 * Delta tau"
    "phase in radians from optical transition angular frequency times proper-time difference"
    true
    refl

visibilityObservableDescriptor :
  SymbolicObservableDescriptor
visibilityObservableDescriptor =
  mkSymbolicObservableDescriptor
    visibilityModulation
    visibilityDependsOnProperTimeBranchCoherence
    refl
    visibility
    (visibilityBaseline ∷ visibilityModulationEnvelope ∷ deltaTau ∷ [])
    "visibility modulation as a coherence/readout envelope over proper-time branch separation"
    "dimensionless interferometric contrast or fringe visibility"
    true
    refl

squeezedStateEnhancementDescriptor :
  SymbolicObservableDescriptor
squeezedStateEnhancementDescriptor =
  mkSymbolicObservableDescriptor
    squeezedStateEnhancement
    squeezedStateParameterMustBeExternallyCalibrated
    refl
    metrologicalEnhancementFactor
    (squeezingParameter ∷ omega0 ∷ deltaTau ∷ [])
    "squeezed-state enhancement parameter obligation for clock phase sensitivity"
    "dimensionless enhancement/calibration factor with declared squeezing convention"
    true
    refl

canonicalObservableDescriptors :
  List SymbolicObservableDescriptor
canonicalObservableDescriptors =
  phaseObservableDescriptor
  ∷ visibilityObservableDescriptor
  ∷ squeezedStateEnhancementDescriptor
  ∷ []

descriptorForKind :
  QuantumClockObservableKind →
  SymbolicObservableDescriptor
descriptorForKind phaseProperTimeShift =
  phaseObservableDescriptor
descriptorForKind visibilityModulation =
  visibilityObservableDescriptor
descriptorForKind squeezedStateEnhancement =
  squeezedStateEnhancementDescriptor

descriptorForKindMatches :
  (kind : QuantumClockObservableKind) →
  observableKind (descriptorForKind kind) ≡ kind
descriptorForKindMatches phaseProperTimeShift = refl
descriptorForKindMatches visibilityModulation = refl
descriptorForKindMatches squeezedStateEnhancement = refl

data SqueezedStateEnhancementObligation : Set where
  declareSqueezingParameterConvention :
    SqueezedStateEnhancementObligation
  bindPreparedClockStateToSqueezingWitness :
    SqueezedStateEnhancementObligation
  providePhaseSensitivityImprovementModel :
    SqueezedStateEnhancementObligation
  provideNoiseBudgetAndUncertaintyModel :
    SqueezedStateEnhancementObligation

canonicalSqueezedStateObligations :
  List SqueezedStateEnhancementObligation
canonicalSqueezedStateObligations =
  declareSqueezingParameterConvention
  ∷ bindPreparedClockStateToSqueezingWitness
  ∷ providePhaseSensitivityImprovementModel
  ∷ provideNoiseBudgetAndUncertaintyModel
  ∷ []

data ExternalAuthorityField : Set where
  authorityInstitution :
    ExternalAuthorityField
  peerReviewedRecord :
    ExternalAuthorityField
  opticalIonSpeciesAndTransition :
    ExternalAuthorityField
  preparationAndInterferometerProtocol :
    ExternalAuthorityField
  properTimeDifferenceCalibration :
    ExternalAuthorityField
  phaseReadoutConvention :
    ExternalAuthorityField
  visibilityReadoutConvention :
    ExternalAuthorityField
  squeezedStateCalibration :
    ExternalAuthorityField
  uncertaintyAndSystematicsBudget :
    ExternalAuthorityField
  stableCitationOrDigest :
    ExternalAuthorityField

canonicalAuthorityFields :
  List ExternalAuthorityField
canonicalAuthorityFields =
  authorityInstitution
  ∷ peerReviewedRecord
  ∷ opticalIonSpeciesAndTransition
  ∷ preparationAndInterferometerProtocol
  ∷ properTimeDifferenceCalibration
  ∷ phaseReadoutConvention
  ∷ visibilityReadoutConvention
  ∷ squeezedStateCalibration
  ∷ uncertaintyAndSystematicsBudget
  ∷ stableCitationOrDigest
  ∷ []

canonicalAuthorityFieldNames :
  List String
canonicalAuthorityFieldNames =
  "authorityInstitution"
  ∷ "peerReviewedRecord"
  ∷ "opticalIonSpeciesAndTransition"
  ∷ "preparationAndInterferometerProtocol"
  ∷ "properTimeDifferenceCalibration"
  ∷ "phaseReadoutConvention"
  ∷ "visibilityReadoutConvention"
  ∷ "squeezedStateCalibration"
  ∷ "uncertaintyAndSystematicsBudget"
  ∷ "stableCitationOrDigest"
  ∷ []

data AuthorityAnchor : Set where
  nistAnchor :
    AuthorityAnchor
  physicalReviewLettersAnchor :
    AuthorityAnchor
  externalBoundMeasurementAnchor :
    AuthorityAnchor

canonicalAuthorityAnchors :
  List AuthorityAnchor
canonicalAuthorityAnchors =
  nistAnchor
  ∷ physicalReviewLettersAnchor
  ∷ externalBoundMeasurementAnchor
  ∷ []

canonicalAuthorityAnchorLabels :
  List String
canonicalAuthorityAnchorLabels =
  "NIST optical ion clock authority anchor"
  ∷ "Physical Review Letters peer-reviewed record authority anchor"
  ∷ "externally bound measurement payload authority anchor"
  ∷ []

data EmpiricalClaimState : Set where
  predictionContactReady :
    EmpiricalClaimState
  externallyBoundMeasurementClaim :
    EmpiricalClaimState
  promotedEmpiricalResult :
    EmpiricalClaimState

data QuantumClockPromotionToken : Set where

promotionTokenImpossibleHere :
  QuantumClockPromotionToken →
  ⊥
promotionTokenImpossibleHere ()

record QuantumClockObservableContract : Set where
  field
    status :
      QuantumClockObservableContractStatus

    superpositionReceipt :
      R.QuantumClockSuperpositionReceipt

    receiptIsCanonical :
      superpositionReceipt ≡ R.canonicalQuantumClockSuperpositionReceipt

    preparationIsProperTimeSuperposition :
      R.preparation superpositionReceipt ≡
      R.coherentProperTimeSuperposition

    observableSurfaceIsQuantumCarried :
      R.observableSurface superpositionReceipt ≡
      R.quantumCarriedProperTimeObservable

    readoutQuotientIsInterferometric :
      R.readoutQuotient superpositionReceipt ≡
      R.interferometricPhaseQuotient

    authorityLanes :
      List OpticalClockAuthorityLane

    authorityLanesAreCanonical :
      authorityLanes ≡ canonicalAuthorityLanes

    observableKinds :
      List QuantumClockObservableKind

    observableKindsAreCanonical :
      observableKinds ≡ canonicalObservableKinds

    observableDescriptors :
      List SymbolicObservableDescriptor

    observableDescriptorsAreCanonical :
      observableDescriptors ≡ canonicalObservableDescriptors

    descriptorLookup :
      QuantumClockObservableKind →
      SymbolicObservableDescriptor

    descriptorLookupMatchesKind :
      (kind : QuantumClockObservableKind) →
      observableKind (descriptorLookup kind) ≡ kind

    phaseLaw :
      SymbolicMeasurementLaw

    phaseLawIsDeltaPhiEqualsOmega0DeltaTau :
      phaseLaw ≡ phaseEqualsCarrierFrequencyTimesProperTimeDifference

    visibilityLaw :
      SymbolicMeasurementLaw

    visibilityLawIsModulationObservable :
      visibilityLaw ≡ visibilityDependsOnProperTimeBranchCoherence

    squeezedStateObligations :
      List SqueezedStateEnhancementObligation

    squeezedStateObligationsAreCanonical :
      squeezedStateObligations ≡ canonicalSqueezedStateObligations

    authorityAnchors :
      List AuthorityAnchor

    authorityAnchorsAreCanonical :
      authorityAnchors ≡ canonicalAuthorityAnchors

    authorityAnchorLabels :
      List String

    authorityAnchorLabelsAreCanonical :
      authorityAnchorLabels ≡ canonicalAuthorityAnchorLabels

    authorityFields :
      List ExternalAuthorityField

    authorityFieldsAreCanonical :
      authorityFields ≡ canonicalAuthorityFields

    authorityFieldNames :
      List String

    authorityFieldNamesAreCanonical :
      authorityFieldNames ≡ canonicalAuthorityFieldNames

    authorityReceiptSurface :
      A.QuantumClockAuthorityReceipt

    authorityReceiptSurfaceIsCanonical :
      authorityReceiptSurface ≡ A.canonicalQuantumClockAuthorityReceipt

    authorityReceiptFailsClosed :
      A.externalMeasurementBound
        (A.failClosedExternalMeasurementBinding authorityReceiptSurface)
      ≡
      false

    externalMeasurementBound :
      Bool

    externalMeasurementBoundIsFalse :
      externalMeasurementBound ≡ false

    experimentalResultClaimedHere :
      Bool

    experimentalResultClaimedHereIsFalse :
      experimentalResultClaimedHere ≡ false

    empiricalClaimState :
      EmpiricalClaimState

    empiricalClaimStateIsPredictionContactReady :
      empiricalClaimState ≡ predictionContactReady

    promoted :
      Bool

    promotedIsFalse :
      promoted ≡ false

    promotionTokenBlocked :
      QuantumClockPromotionToken →
      ⊥

    contractReading :
      String

open QuantumClockObservableContract public

canonicalQuantumClockObservableContract :
  QuantumClockObservableContract
canonicalQuantumClockObservableContract =
  record
    { status =
        opticalIonClockProperTimeSuperpositionContactReadyNoPromotion
    ; superpositionReceipt =
        R.canonicalQuantumClockSuperpositionReceipt
    ; receiptIsCanonical =
        refl
    ; preparationIsProperTimeSuperposition =
        refl
    ; observableSurfaceIsQuantumCarried =
        refl
    ; readoutQuotientIsInterferometric =
        refl
    ; authorityLanes =
        canonicalAuthorityLanes
    ; authorityLanesAreCanonical =
        refl
    ; observableKinds =
        canonicalObservableKinds
    ; observableKindsAreCanonical =
        refl
    ; observableDescriptors =
        canonicalObservableDescriptors
    ; observableDescriptorsAreCanonical =
        refl
    ; descriptorLookup =
        descriptorForKind
    ; descriptorLookupMatchesKind =
        descriptorForKindMatches
    ; phaseLaw =
        phaseEqualsCarrierFrequencyTimesProperTimeDifference
    ; phaseLawIsDeltaPhiEqualsOmega0DeltaTau =
        refl
    ; visibilityLaw =
        visibilityDependsOnProperTimeBranchCoherence
    ; visibilityLawIsModulationObservable =
        refl
    ; squeezedStateObligations =
        canonicalSqueezedStateObligations
    ; squeezedStateObligationsAreCanonical =
        refl
    ; authorityAnchors =
        canonicalAuthorityAnchors
    ; authorityAnchorsAreCanonical =
        refl
    ; authorityAnchorLabels =
        canonicalAuthorityAnchorLabels
    ; authorityAnchorLabelsAreCanonical =
        refl
    ; authorityFields =
        canonicalAuthorityFields
    ; authorityFieldsAreCanonical =
        refl
    ; authorityFieldNames =
        canonicalAuthorityFieldNames
    ; authorityFieldNamesAreCanonical =
        refl
    ; authorityReceiptSurface =
        A.canonicalQuantumClockAuthorityReceipt
    ; authorityReceiptSurfaceIsCanonical =
        refl
    ; authorityReceiptFailsClosed =
        refl
    ; externalMeasurementBound =
        false
    ; externalMeasurementBoundIsFalse =
        refl
    ; experimentalResultClaimedHere =
        false
    ; experimentalResultClaimedHereIsFalse =
        refl
    ; empiricalClaimState =
        predictionContactReady
    ; empiricalClaimStateIsPredictionContactReady =
        refl
    ; promoted =
        false
    ; promotedIsFalse =
        refl
    ; promotionTokenBlocked =
        promotionTokenImpossibleHere
    ; contractReading =
        "Optical ion clock proper-time superposition contact contract: symbolic Delta phi = omega0 * Delta tau phase readout, visibility modulation, and squeezed-state enhancement obligations are ready for external NIST/PRL authority binding; no experimental result or promotion is claimed here."
    }

canonicalContractUsesQuantumClockReceipt :
  superpositionReceipt canonicalQuantumClockObservableContract ≡
  R.canonicalQuantumClockSuperpositionReceipt
canonicalContractUsesQuantumClockReceipt = refl

canonicalPhaseObservableIsDeltaPhiLaw :
  phaseLaw canonicalQuantumClockObservableContract ≡
  phaseEqualsCarrierFrequencyTimesProperTimeDifference
canonicalPhaseObservableIsDeltaPhiLaw = refl

canonicalVisibilityObservableIsModulationLaw :
  visibilityLaw canonicalQuantumClockObservableContract ≡
  visibilityDependsOnProperTimeBranchCoherence
canonicalVisibilityObservableIsModulationLaw = refl

canonicalContractIsNotExternallyBound :
  externalMeasurementBound canonicalQuantumClockObservableContract ≡
  false
canonicalContractIsNotExternallyBound = refl

canonicalContractClaimsNoExperimentalResult :
  experimentalResultClaimedHere canonicalQuantumClockObservableContract ≡
  false
canonicalContractClaimsNoExperimentalResult = refl

canonicalContractDoesNotPromote :
  promoted canonicalQuantumClockObservableContract ≡ false
canonicalContractDoesNotPromote = refl
