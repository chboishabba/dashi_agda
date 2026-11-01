module DASHI.Promotion.ChemistrySpectroscopyAuthorityIntake where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

open import DASHI.Constants.Registry as Registry
open import DASHI.Promotion.ChemistryBiologyObligations as ChemBio
open import DASHI.Promotion.ChemistryQuantitativeAdapter as Quant

------------------------------------------------------------------------
-- Chemistry and spectroscopy authority intake.
--
-- This module turns the quantitative chemistry/spectroscopy blockers into
-- typed authority-intake rows.  It is deliberately fail-closed: rows can be
-- requested, accepted, and validated only through explicit fields, and the
-- canonical surface records every authority as still missing/unvalidated.

data ChemistryAuthorityKind : Set where
  spectraAuthority : ChemistryAuthorityKind
  thermochemistryAuthority : ChemistryAuthorityKind
  pKaAuthority : ChemistryAuthorityKind
  rateAuthority : ChemistryAuthorityKind
  diffusionAuthority : ChemistryAuthorityKind
  bindingAuthority : ChemistryAuthorityKind
  activityAuthority : ChemistryAuthorityKind
  instrumentCalibrationAuthority : ChemistryAuthorityKind
  wetLabProtocolAuthority : ChemistryAuthorityKind
  replicationAuthority : ChemistryAuthorityKind

data ChemistryAuthorityRequestState : Set where
  requested : ChemistryAuthorityRequestState
  missing : ChemistryAuthorityRequestState
  acceptedButUnvalidated : ChemistryAuthorityRequestState
  acceptedAndValidated : ChemistryAuthorityRequestState

data ChemistryAuthorityBlocker : Set where
  spectraAuthorityMissing : ChemistryAuthorityBlocker
  thermochemistryAuthorityMissing : ChemistryAuthorityBlocker
  pKaAuthorityMissing : ChemistryAuthorityBlocker
  rateAuthorityMissing : ChemistryAuthorityBlocker
  diffusionAuthorityMissing : ChemistryAuthorityBlocker
  bindingAuthorityMissing : ChemistryAuthorityBlocker
  activityAuthorityMissing : ChemistryAuthorityBlocker
  instrumentCalibrationAuthorityMissing : ChemistryAuthorityBlocker
  wetLabProtocolAuthorityMissing : ChemistryAuthorityBlocker
  replicationAuthorityMissing : ChemistryAuthorityBlocker
  authorityAcceptedButUnvalidated : ChemistryAuthorityBlocker
  authorityRequestOnly : ChemistryAuthorityBlocker
  noAuthorityBlocker : ChemistryAuthorityBlocker

data ChemistryAuthorityTargetGuard : Set where
  targetPhysicalChemistry : ChemistryAuthorityTargetGuard
  targetSpectroscopy : ChemistryAuthorityTargetGuard
  targetBondingInterpretation : ChemistryAuthorityTargetGuard
  targetWetLabValidation : ChemistryAuthorityTargetGuard

record ChemistryAuthorityRequestRow : Set₁ where
  field
    requestLabel : String
    authorityKind : ChemistryAuthorityKind
    requestState : ChemistryAuthorityRequestState
    targetGuard : ChemistryAuthorityTargetGuard
    authoritySourceClass : String
    authoritySlotOrProvider : String
    consumedByAdapterField : String
    consumedByObligation : String
    requiredPayloadFields : List String
    validationCriterion : String
    nextBlockerIfMissing : ChemistryAuthorityBlocker
    requestedByCanonicalIntake : Bool
    requestedByCanonicalIntakeIsTrue :
      requestedByCanonicalIntake ≡ true
    acceptedAuthorityTokenPresent : Bool
    acceptedAuthorityTokenPresentIsFalse :
      acceptedAuthorityTokenPresent ≡ false
    validationAccepted : Bool
    validationAcceptedIsFalse :
      validationAccepted ≡ false
    promotesClaim : Bool
    promotesClaimIsFalse :
      promotesClaim ≡ false

open ChemistryAuthorityRequestRow public

mkMissingRequest :
  String →
  ChemistryAuthorityKind →
  ChemistryAuthorityTargetGuard →
  String →
  String →
  String →
  String →
  List String →
  String →
  ChemistryAuthorityBlocker →
  ChemistryAuthorityRequestRow
mkMissingRequest label kind guard source provider adapterField obligation
  payloadFields criterion blocker =
  record
    { requestLabel = label
    ; authorityKind = kind
    ; requestState = missing
    ; targetGuard = guard
    ; authoritySourceClass = source
    ; authoritySlotOrProvider = provider
    ; consumedByAdapterField = adapterField
    ; consumedByObligation = obligation
    ; requiredPayloadFields = payloadFields
    ; validationCriterion = criterion
    ; nextBlockerIfMissing = blocker
    ; requestedByCanonicalIntake = true
    ; requestedByCanonicalIntakeIsTrue = refl
    ; acceptedAuthorityTokenPresent = false
    ; acceptedAuthorityTokenPresentIsFalse = refl
    ; validationAccepted = false
    ; validationAcceptedIsFalse = refl
    ; promotesClaim = false
    ; promotesClaimIsFalse = refl
    }

requestCount : List ChemistryAuthorityRequestRow → Nat
requestCount [] = zero
requestCount (_ ∷ xs) = suc (requestCount xs)

missingRequestCount : List ChemistryAuthorityRequestRow → Nat
missingRequestCount [] = zero
missingRequestCount (row ∷ xs) with requestState row
... | missing = suc (missingRequestCount xs)
... | requested = missingRequestCount xs
... | acceptedButUnvalidated = missingRequestCount xs
... | acceptedAndValidated = missingRequestCount xs

acceptedButUnvalidatedRequestCount :
  List ChemistryAuthorityRequestRow → Nat
acceptedButUnvalidatedRequestCount [] = zero
acceptedButUnvalidatedRequestCount (row ∷ xs) with requestState row
... | acceptedButUnvalidated =
  suc (acceptedButUnvalidatedRequestCount xs)
... | requested = acceptedButUnvalidatedRequestCount xs
... | missing = acceptedButUnvalidatedRequestCount xs
... | acceptedAndValidated = acceptedButUnvalidatedRequestCount xs

acceptedAndValidatedRequestCount :
  List ChemistryAuthorityRequestRow → Nat
acceptedAndValidatedRequestCount [] = zero
acceptedAndValidatedRequestCount (row ∷ xs) with requestState row
... | acceptedAndValidated =
  suc (acceptedAndValidatedRequestCount xs)
... | requested = acceptedAndValidatedRequestCount xs
... | missing = acceptedAndValidatedRequestCount xs
... | acceptedButUnvalidated = acceptedAndValidatedRequestCount xs

blockerForRequestedRow :
  ChemistryAuthorityRequestRow → ChemistryAuthorityBlocker
blockerForRequestedRow row with requestState row
... | missing = nextBlockerIfMissing row
... | acceptedButUnvalidated = authorityAcceptedButUnvalidated
... | requested = authorityRequestOnly
... | acceptedAndValidated = noAuthorityBlocker

nextBlockerSelector :
  List ChemistryAuthorityRequestRow → ChemistryAuthorityBlocker
nextBlockerSelector [] = noAuthorityBlocker
nextBlockerSelector (row ∷ rows) with blockerForRequestedRow row
... | noAuthorityBlocker = nextBlockerSelector rows
... | blocker = blocker

canonicalChemistryAuthorityRequestRows :
  List ChemistryAuthorityRequestRow
canonicalChemistryAuthorityRequestRows =
  mkMissingRequest
    "spectral-line or spectrum authority intake"
    spectraAuthority
    targetSpectroscopy
    "NIST Chemistry WebBook, NIST ASD, or lane-specific spectrum provider"
    "spectra"
    "SpectroscopyObservableAdapter.spectralAuthoritySlot"
    "Hamiltonian to spectral observable map"
    ( "sourceUri"
    ∷ "authorityVersion"
    ∷ "spectrumChecksum"
    ∷ "transitionAssignment"
    ∷ "wavelengthFrequencyEnergyUnits"
    ∷ "uncertaintyOrResolution"
    ∷ []
    )
    "source spectrum checksum, unit convention, and comparison residual accepted"
    spectraAuthorityMissing
  ∷ mkMissingRequest
    "thermochemistry authority intake"
    thermochemistryAuthority
    targetPhysicalChemistry
    "NIST Chemistry WebBook or equivalent thermochemistry provider"
    "thermochemistry"
    "SymbolicLawCarrier.measuredAuthorityInputs"
    "physical chemistry scale-setting"
    ( "sourceUri"
    ∷ "authorityVersion"
    ∷ "stateVariables"
    ∷ "temperaturePressureConvention"
    ∷ "enthalpyEntropyFreeEnergyValues"
    ∷ "uncertaintyPolicy"
    ∷ []
    )
    "thermochemical state, uncertainty, and unit policy accepted by consuming law carrier"
    thermochemistryAuthorityMissing
  ∷ mkMissingRequest
    "pKa authority intake"
    pKaAuthority
    targetPhysicalChemistry
    "domain pKa table or curated chemistry provider"
    "pKa"
    "ChemistryKnownInputsReferenceReceipt.measuredChemistryInputs"
    "acid/base quantitative adapter"
    ( "sourceUri"
    ∷ "authorityVersion"
    ∷ "compoundIdentity"
    ∷ "solvent"
    ∷ "temperature"
    ∷ "ionicStrength"
    ∷ "uncertaintyOrCurationGrade"
    ∷ []
    )
    "pKa value bound to compound identity, conditions, and uncertainty policy"
    pKaAuthorityMissing
  ∷ mkMissingRequest
    "reaction-rate authority intake"
    rateAuthority
    targetPhysicalChemistry
    "kinetics provider, publication, or curated reaction database"
    "reaction-rates"
    "SymbolicLawCarrier.measuredAuthorityInputs"
    "Arrhenius and mass-action quantitative adapters"
    ( "sourceUri"
    ∷ "authorityVersion"
    ∷ "reactionIdentity"
    ∷ "rateLaw"
    ∷ "temperatureRange"
    ∷ "concentrationConvention"
    ∷ "uncertaintyPolicy"
    ∷ []
    )
    "rate law and parameter range accepted under stated concentration and temperature convention"
    rateAuthorityMissing
  ∷ mkMissingRequest
    "diffusion authority intake"
    diffusionAuthority
    targetPhysicalChemistry
    "diffusion measurement provider or curated transport database"
    "diffusion"
    "ChemistryKnownInputsReferenceReceipt.measuredChemistryInputs"
    "transport and wet-lab quantitative adapter"
    ( "sourceUri"
    ∷ "authorityVersion"
    ∷ "speciesIdentity"
    ∷ "medium"
    ∷ "temperature"
    ∷ "diffusionCoefficient"
    ∷ "uncertaintyPolicy"
    ∷ []
    )
    "diffusion coefficient bound to species, medium, temperature, and uncertainty"
    diffusionAuthorityMissing
  ∷ mkMissingRequest
    "binding-constant authority intake"
    bindingAuthority
    targetPhysicalChemistry
    "binding assay provider, publication, or curated biochemical database"
    "binding"
    "ChemistryKnownInputsReferenceReceipt.measuredChemistryInputs"
    "mass-action and wet-lab quantitative adapters"
    ( "sourceUri"
    ∷ "authorityVersion"
    ∷ "ligandTargetIdentity"
    ∷ "assayProtocol"
    ∷ "temperatureBufferConditions"
    ∷ "KdKaKiValue"
    ∷ "uncertaintyOrConfidence"
    ∷ []
    )
    "binding value accepted under assay, buffer, identity, and uncertainty conditions"
    bindingAuthorityMissing
  ∷ mkMissingRequest
    "activity-data authority intake"
    activityAuthority
    targetPhysicalChemistry
    "activity coefficient, assay activity, or curated activity provider"
    "activity-data"
    "ChemistryKnownInputsReferenceReceipt.measuredChemistryInputs"
    "Nernst, mass-action, and wet-lab quantitative adapters"
    ( "sourceUri"
    ∷ "authorityVersion"
    ∷ "activityDefinition"
    ∷ "sampleOrSpeciesIdentity"
    ∷ "conditionMetadata"
    ∷ "activityValue"
    ∷ "uncertaintyPolicy"
    ∷ []
    )
    "activity value accepted with definition, identity, conditions, and uncertainty"
    activityAuthorityMissing
  ∷ mkMissingRequest
    "instrument-calibration authority intake"
    instrumentCalibrationAuthority
    targetSpectroscopy
    "instrument calibration provider or lab calibration certificate"
    "instrument-calibration"
    "WetLabProtocolReplicationReceipt.instrumentCalibrationField"
    "instrument calibration obligation"
    ( "calibrationId"
    ∷ "instrumentId"
    ∷ "calibrationDate"
    ∷ "calibrationStandard"
    ∷ "responseFunctionChecksum"
    ∷ "driftOrResolutionPolicy"
    ∷ "operatorOrAutomationMetadata"
    ∷ []
    )
    "instrument response, calibration standard, and drift policy accepted"
    instrumentCalibrationAuthorityMissing
  ∷ mkMissingRequest
    "wet-lab protocol authority intake"
    wetLabProtocolAuthority
    targetWetLabValidation
    "protocol registry, ELN export, or lab provenance provider"
    "wet-lab-protocol"
    "WetLabProtocolReplicationReceipt.protocolIdField"
    "wet-lab protocol replication obligation"
    ( "protocolId"
    ∷ "sampleProvenance"
    ∷ "reagentLots"
    ∷ "environmentMetadata"
    ∷ "rawDataChecksum"
    ∷ "analysisPipelineChecksum"
    ∷ "acceptanceCriterion"
    ∷ []
    )
    "protocol provenance complete and raw/analysis checksums accepted"
    wetLabProtocolAuthorityMissing
  ∷ mkMissingRequest
    "independent replication authority intake"
    replicationAuthority
    targetWetLabValidation
    "independent replication provider or accepted replication package"
    "replication"
    "WetLabProtocolReplicationReceipt.independentReplicationField"
    "wet-lab protocol replication obligation"
    ( "replicateSetId"
    ∷ "independentLabOrAutomationId"
    ∷ "protocolVersion"
    ∷ "rawDataChecksum"
    ∷ "analysisPipelineChecksum"
    ∷ "passFailCriterion"
    ∷ "replicationVerdict"
    ∷ []
    )
    "independent replication satisfies the stated acceptance criterion"
    replicationAuthorityMissing
  ∷ []

record ChemistrySpectroscopyAuthorityIntake : Set₁ where
  field
    registryReceipt :
      Registry.ChemistryKnownInputsReferenceReceipt
    quantitativeAdapter :
      Quant.ChemistryQuantitativeAdapter
    chemistryBiologyObligationIndex :
      ChemBio.ChemistryBiologyPromotionObligationIndex
    requestRows :
      List ChemistryAuthorityRequestRow
    requestRowCount :
      Nat
    requestRowCountMatches :
      requestRowCount ≡ requestCount requestRows
    missingRowCount :
      Nat
    missingRowCountMatches :
      missingRowCount ≡ missingRequestCount requestRows
    acceptedButUnvalidatedRowCount :
      Nat
    acceptedButUnvalidatedRowCountMatches :
      acceptedButUnvalidatedRowCount ≡
      acceptedButUnvalidatedRequestCount requestRows
    acceptedAndValidatedRowCount :
      Nat
    acceptedAndValidatedRowCountMatches :
      acceptedAndValidatedRowCount ≡
      acceptedAndValidatedRequestCount requestRows
    nextBlocker :
      ChemistryAuthorityBlocker
    nextBlockerMatches :
      nextBlocker ≡ nextBlockerSelector requestRows
    physicalChemistryPromoted :
      Bool
    physicalChemistryPromotedIsFalse :
      physicalChemistryPromoted ≡ false
    spectroscopyPromoted :
      Bool
    spectroscopyPromotedIsFalse :
      spectroscopyPromoted ≡ false
    bondingInterpretationPromoted :
      Bool
    bondingInterpretationPromotedIsFalse :
      bondingInterpretationPromoted ≡ false
    wetLabValidationAccepted :
      Bool
    wetLabValidationAcceptedIsFalse :
      wetLabValidationAccepted ≡ false

open ChemistrySpectroscopyAuthorityIntake public

canonicalChemistrySpectroscopyAuthorityIntake :
  ChemistrySpectroscopyAuthorityIntake
canonicalChemistrySpectroscopyAuthorityIntake = record
  { registryReceipt =
      Registry.canonicalChemistryKnownInputsReferenceReceipt
  ; quantitativeAdapter =
      Quant.canonicalChemistryQuantitativeAdapter
  ; chemistryBiologyObligationIndex =
      ChemBio.canonicalChemistryBiologyPromotionObligationIndex
  ; requestRows =
      canonicalChemistryAuthorityRequestRows
  ; requestRowCount = 10
  ; requestRowCountMatches = refl
  ; missingRowCount = 10
  ; missingRowCountMatches = refl
  ; acceptedButUnvalidatedRowCount = 0
  ; acceptedButUnvalidatedRowCountMatches = refl
  ; acceptedAndValidatedRowCount = 0
  ; acceptedAndValidatedRowCountMatches = refl
  ; nextBlocker = spectraAuthorityMissing
  ; nextBlockerMatches = refl
  ; physicalChemistryPromoted =
      Registry.ChemistryKnownInputsReferenceReceipt.physicalChemistryPromoted
        Registry.canonicalChemistryKnownInputsReferenceReceipt
  ; physicalChemistryPromotedIsFalse =
      Registry.ChemistryKnownInputsReferenceReceipt.physicalChemistryPromotedIsFalse
        Registry.canonicalChemistryKnownInputsReferenceReceipt
  ; spectroscopyPromoted =
      Registry.ChemistryKnownInputsReferenceReceipt.spectroscopyPromoted
        Registry.canonicalChemistryKnownInputsReferenceReceipt
  ; spectroscopyPromotedIsFalse =
      Registry.ChemistryKnownInputsReferenceReceipt.spectroscopyPromotedIsFalse
        Registry.canonicalChemistryKnownInputsReferenceReceipt
  ; bondingInterpretationPromoted =
      Registry.ChemistryKnownInputsReferenceReceipt.bondingInterpretationPromoted
        Registry.canonicalChemistryKnownInputsReferenceReceipt
  ; bondingInterpretationPromotedIsFalse =
      Registry.ChemistryKnownInputsReferenceReceipt.bondingInterpretationPromotedIsFalse
        Registry.canonicalChemistryKnownInputsReferenceReceipt
  ; wetLabValidationAccepted =
      Registry.ChemistryKnownInputsReferenceReceipt.wetLabValidationAccepted
        Registry.canonicalChemistryKnownInputsReferenceReceipt
  ; wetLabValidationAcceptedIsFalse =
      Registry.ChemistryKnownInputsReferenceReceipt.wetLabValidationAcceptedIsFalse
        Registry.canonicalChemistryKnownInputsReferenceReceipt
  }

canonicalChemistryAuthorityRequestCountIs10 :
  requestRowCount canonicalChemistrySpectroscopyAuthorityIntake ≡ 10
canonicalChemistryAuthorityRequestCountIs10 = refl

canonicalChemistryAuthorityMissingCountIs10 :
  missingRowCount canonicalChemistrySpectroscopyAuthorityIntake ≡ 10
canonicalChemistryAuthorityMissingCountIs10 = refl

canonicalChemistryAuthorityAcceptedButUnvalidatedCountIs0 :
  acceptedButUnvalidatedRowCount
    canonicalChemistrySpectroscopyAuthorityIntake ≡ 0
canonicalChemistryAuthorityAcceptedButUnvalidatedCountIs0 = refl

canonicalChemistryAuthorityAcceptedAndValidatedCountIs0 :
  acceptedAndValidatedRowCount
    canonicalChemistrySpectroscopyAuthorityIntake ≡ 0
canonicalChemistryAuthorityAcceptedAndValidatedCountIs0 = refl

canonicalChemistryAuthorityNextBlockerIsSpectra :
  nextBlocker canonicalChemistrySpectroscopyAuthorityIntake ≡
  spectraAuthorityMissing
canonicalChemistryAuthorityNextBlockerIsSpectra = refl

canonicalChemistryAuthorityPhysicalChemistryPromotedIsFalse :
  physicalChemistryPromoted
    canonicalChemistrySpectroscopyAuthorityIntake ≡ false
canonicalChemistryAuthorityPhysicalChemistryPromotedIsFalse = refl

canonicalChemistryAuthoritySpectroscopyPromotedIsFalse :
  spectroscopyPromoted
    canonicalChemistrySpectroscopyAuthorityIntake ≡ false
canonicalChemistryAuthoritySpectroscopyPromotedIsFalse = refl

canonicalChemistryAuthorityBondingPromotedIsFalse :
  bondingInterpretationPromoted
    canonicalChemistrySpectroscopyAuthorityIntake ≡ false
canonicalChemistryAuthorityBondingPromotedIsFalse = refl

canonicalChemistryAuthorityWetLabAcceptedIsFalse :
  wetLabValidationAccepted
    canonicalChemistrySpectroscopyAuthorityIntake ≡ false
canonicalChemistryAuthorityWetLabAcceptedIsFalse = refl
