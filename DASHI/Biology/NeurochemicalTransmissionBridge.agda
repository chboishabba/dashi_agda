module DASHI.Biology.NeurochemicalTransmissionBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Biology.BioactiveMolecularRecognitionBridge as Bioactive
import DASHI.Biology.NeurochemicalVocabularyReceipt as Vocabulary
import DASHI.Core.AuthorityNonPromotionCore as Authority
import DASHI.Core.CandidateFunctionalCore as Functional
import DASHI.Core.CandidateOnlyCore as CandidateOnly
import DASHI.Core.FormalLensQualificationCore as FormalLens
import DASHI.Core.OperatorShapeNonAuthorityCore as OperatorShape
import DASHI.Promotion.NeurochemicalAuthorityBoundary as Boundary

------------------------------------------------------------------------
-- Neurochemical transmission bridge.
--
-- This module records neurotransmission as candidate symbolic-rational
-- carrier infrastructure.  It is not a pharmacology, clinical, disease,
-- diagnosis, dose-response, biomarker, or behavior theorem.  The bridge
-- connects named neurochemical vocabulary, molecular-recognition structure,
-- concentration/timecourse and receptor-context carriers, neural-encoding
-- candidates, plasticity modulation candidates, and behavior-quotient
-- residuals while every authority-bearing route stays fail-closed.

data Never : Set where

data NeurochemicalTransmissionCarrier : Set where
  transmitterCandidateCarrier :
    NeurochemicalTransmissionCarrier

  receptorContextCarrier :
    NeurochemicalTransmissionCarrier

  synapticTransmissionCarrier :
    NeurochemicalTransmissionCarrier

  volumeTransmissionCarrier :
    NeurochemicalTransmissionCarrier

  transporterClearanceCarrier :
    NeurochemicalTransmissionCarrier

  enzymaticDegradationCarrier :
    NeurochemicalTransmissionCarrier

  concentrationTimecourseCarrier :
    NeurochemicalTransmissionCarrier

  receptorOccupancyCarrier :
    NeurochemicalTransmissionCarrier

  neuralEncodingCarrier :
    NeurochemicalTransmissionCarrier

  plasticityModulationCarrier :
    NeurochemicalTransmissionCarrier

  behaviorQuotientResidualCarrier :
    NeurochemicalTransmissionCarrier

data NeurochemicalTransmissionMode : Set where
  synapticVesicularMode :
    NeurochemicalTransmissionMode

  extrasynapticVolumeMode :
    NeurochemicalTransmissionMode

  transporterReuptakeMode :
    NeurochemicalTransmissionMode

  enzymeClearanceMode :
    NeurochemicalTransmissionMode

  endocrineAdjacentMode :
    NeurochemicalTransmissionMode

  peripheralCentralBoundaryMode :
    NeurochemicalTransmissionMode

data NeurochemicalTransmissionGuard : Set where
  NoClinicalAuthorityClaim :
    NeurochemicalTransmissionGuard

  NoTherapeuticAuthorityClaim :
    NeurochemicalTransmissionGuard

  NoDoseResponseAuthorityClaim :
    NeurochemicalTransmissionGuard

  NoDiseaseCausationClaim :
    NeurochemicalTransmissionGuard

  NoBehaviorCausationClaim :
    NeurochemicalTransmissionGuard

  NoPsychiatricDiagnosisClaim :
    NeurochemicalTransmissionGuard

  NoBiomarkerAuthorityClaim :
    NeurochemicalTransmissionGuard

  NoBrainStateRecoveryClaim :
    NeurochemicalTransmissionGuard

  NoTransmitterOperatorIdentityClaim :
    NeurochemicalTransmissionGuard

  NoFolkTransmitterEquivalenceClaim :
    NeurochemicalTransmissionGuard

data NeurochemicalTransmissionRoute : Set where
  boundedNeurochemicalTransmissionRoute :
    NeurochemicalTransmissionRoute

  clinicalPromotionRoute :
    NeurochemicalTransmissionRoute

  therapeuticPromotionRoute :
    NeurochemicalTransmissionRoute

  doseResponsePromotionRoute :
    NeurochemicalTransmissionRoute

  diseaseCausationRoute :
    NeurochemicalTransmissionRoute

  behaviorCausationRoute :
    NeurochemicalTransmissionRoute

  diagnosisRoute :
    NeurochemicalTransmissionRoute

  biomarkerPromotionRoute :
    NeurochemicalTransmissionRoute

  brainStateRecoveryRoute :
    NeurochemicalTransmissionRoute

  transmitterOperatorIdentityRoute :
    NeurochemicalTransmissionRoute

AdmissibleNeurochemicalTransmissionRoute :
  NeurochemicalTransmissionRoute →
  Set
AdmissibleNeurochemicalTransmissionRoute
  boundedNeurochemicalTransmissionRoute =
  ⊤
AdmissibleNeurochemicalTransmissionRoute clinicalPromotionRoute =
  Never
AdmissibleNeurochemicalTransmissionRoute therapeuticPromotionRoute =
  Never
AdmissibleNeurochemicalTransmissionRoute doseResponsePromotionRoute =
  Never
AdmissibleNeurochemicalTransmissionRoute diseaseCausationRoute =
  Never
AdmissibleNeurochemicalTransmissionRoute behaviorCausationRoute =
  Never
AdmissibleNeurochemicalTransmissionRoute diagnosisRoute =
  Never
AdmissibleNeurochemicalTransmissionRoute biomarkerPromotionRoute =
  Never
AdmissibleNeurochemicalTransmissionRoute brainStateRecoveryRoute =
  Never
AdmissibleNeurochemicalTransmissionRoute transmitterOperatorIdentityRoute =
  Never

clinicalPromotionRejected :
  AdmissibleNeurochemicalTransmissionRoute clinicalPromotionRoute →
  Never
clinicalPromotionRejected impossible =
  impossible

therapeuticPromotionRejected :
  AdmissibleNeurochemicalTransmissionRoute therapeuticPromotionRoute →
  Never
therapeuticPromotionRejected impossible =
  impossible

doseResponsePromotionRejected :
  AdmissibleNeurochemicalTransmissionRoute doseResponsePromotionRoute →
  Never
doseResponsePromotionRejected impossible =
  impossible

diseaseCausationRejected :
  AdmissibleNeurochemicalTransmissionRoute diseaseCausationRoute →
  Never
diseaseCausationRejected impossible =
  impossible

behaviorCausationRejected :
  AdmissibleNeurochemicalTransmissionRoute behaviorCausationRoute →
  Never
behaviorCausationRejected impossible =
  impossible

diagnosisRejected :
  AdmissibleNeurochemicalTransmissionRoute diagnosisRoute →
  Never
diagnosisRejected impossible =
  impossible

biomarkerPromotionRejected :
  AdmissibleNeurochemicalTransmissionRoute biomarkerPromotionRoute →
  Never
biomarkerPromotionRejected impossible =
  impossible

brainStateRecoveryRejected :
  AdmissibleNeurochemicalTransmissionRoute brainStateRecoveryRoute →
  Never
brainStateRecoveryRejected impossible =
  impossible

transmitterOperatorIdentityRejected :
  AdmissibleNeurochemicalTransmissionRoute
    transmitterOperatorIdentityRoute →
  Never
transmitterOperatorIdentityRejected impossible =
  impossible

canonicalNeurochemicalTransmissionCarriers :
  List NeurochemicalTransmissionCarrier
canonicalNeurochemicalTransmissionCarriers =
  transmitterCandidateCarrier
  ∷ receptorContextCarrier
  ∷ synapticTransmissionCarrier
  ∷ volumeTransmissionCarrier
  ∷ transporterClearanceCarrier
  ∷ enzymaticDegradationCarrier
  ∷ concentrationTimecourseCarrier
  ∷ receptorOccupancyCarrier
  ∷ neuralEncodingCarrier
  ∷ plasticityModulationCarrier
  ∷ behaviorQuotientResidualCarrier
  ∷ []

canonicalNeurochemicalTransmissionModes :
  List NeurochemicalTransmissionMode
canonicalNeurochemicalTransmissionModes =
  synapticVesicularMode
  ∷ extrasynapticVolumeMode
  ∷ transporterReuptakeMode
  ∷ enzymeClearanceMode
  ∷ endocrineAdjacentMode
  ∷ peripheralCentralBoundaryMode
  ∷ []

canonicalNeurochemicalTransmissionGuards :
  List NeurochemicalTransmissionGuard
canonicalNeurochemicalTransmissionGuards =
  NoClinicalAuthorityClaim
  ∷ NoTherapeuticAuthorityClaim
  ∷ NoDoseResponseAuthorityClaim
  ∷ NoDiseaseCausationClaim
  ∷ NoBehaviorCausationClaim
  ∷ NoPsychiatricDiagnosisClaim
  ∷ NoBiomarkerAuthorityClaim
  ∷ NoBrainStateRecoveryClaim
  ∷ NoTransmitterOperatorIdentityClaim
  ∷ NoFolkTransmitterEquivalenceClaim
  ∷ []

canonicalNeurochemicalFormalLenses :
  List FormalLens.FormalLens
canonicalNeurochemicalFormalLenses =
  FormalLens.NamedFormalLens "chemical"
  ∷ FormalLens.NamedFormalLens "receptor binding"
  ∷ FormalLens.GradientFlow
  ∷ FormalLens.ResistiveTransport
  ∷ FormalLens.Operator
  ∷ FormalLens.Functional
  ∷ FormalLens.Probabilistic
  ∷ FormalLens.Graph
  ∷ FormalLens.Category
  ∷ FormalLens.SymbolicRational
  ∷ []

neurochemicalCandidateOnlyCoreRow :
  CandidateOnly.CandidateOnlyRow
neurochemicalCandidateOnlyCoreRow =
  CandidateOnly.mkCandidateOnlyRow
    "neurochemical transmission candidate"
    "DASHI.Biology.NeurochemicalTransmissionBridge"
    "neurochemicalCandidateOnlyCoreRow"
    CandidateOnly.bridgeCandidateKind
    CandidateOnly.bridgeCandidateOnlyStatus
    "neurochemical transmission is recorded as candidate carrier infrastructure only"
    "clinical, pharmacological, disease, dose-response, diagnostic, biomarker, behavior, and brain-state authority remain external"

neurochemicalCandidateOnlyCoreReceipt :
  CandidateOnly.CandidateOnlyReceipt neurochemicalCandidateOnlyCoreRow
neurochemicalCandidateOnlyCoreReceipt =
  CandidateOnly.mkCandidateOnlyReceipt
    neurochemicalCandidateOnlyCoreRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

neurochemicalAuthorityBundle :
  Authority.AuthorityNonPromotionBundle
neurochemicalAuthorityBundle =
  Authority.mkClosedAuthorityNonPromotionBundle
    "neurochemical transmission authority non-promotion"

neurochemicalFunctionalTerms :
  List Functional.FunctionalTerm
neurochemicalFunctionalTerms =
  Functional.positiveStrainTerm
    "unvalidated concentration excursion"
    Functional.strainSymbolicWeight
  ∷ Functional.positiveStrainTerm
    "unvalidated receptor occupancy"
    Functional.strainSymbolicWeight
  ∷ Functional.positiveStrainTerm
    "unvalidated behavior attribution"
    Functional.strainSymbolicWeight
  ∷ Functional.negativeSupportTerm
    "bounded receptor context"
    Functional.supportSymbolicWeight
  ∷ Functional.negativeSupportTerm
    "bounded clearance context"
    Functional.supportSymbolicWeight
  ∷ Functional.neutralFunctionalTerm
    "neural encoding residual"
    Functional.neutralSymbolicWeight
  ∷ []

neurochemicalFunctionalSurface :
  Functional.CandidateFunctionalSurface
neurochemicalFunctionalSurface =
  Functional.candidateFunctionalSurface
    "neurochemical carrier"
    "candidate transmission state"
    (Functional.NamedFunctionalKind "neurochemical transmission balance")
    neurochemicalFunctionalTerms
    Functional.candidateWeightedSymbolicSum
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl

neurochemicalOperatorShapeReceipt :
  OperatorShape.OperatorShapeCandidateReceipt
neurochemicalOperatorShapeReceipt =
  OperatorShape.mkOperatorShapeCandidateReceipt
    OperatorShape.receiptDomainCarrier
    OperatorShape.receiptCodomainCarrier
    OperatorShape.observationOperatorTag
    OperatorShape.diagnosticCompositionHint
    OperatorShape.boundednessCandidateRequiresProof
    OperatorShape.contractionCandidateUnwitnessed
    OperatorShape.dissipativeCandidateUnwitnessed
    OperatorShape.spectralDiagnosticShape
    "neurochemical intervention wording is operator-shaped only; no bounded-linear, spectrum, PDE, generator, or theorem authority is supplied"

record NeurochemicalTransmissionBridge : Set₁ where
  field
    vocabularyRows :
      List CandidateOnly.CandidateOnlyRow

    vocabularyRowsAreCanonical :
      vocabularyRows ≡ Vocabulary.canonicalNeurochemicalVocabularyRows

    vocabularyRowsCandidateOnly :
      CandidateOnly.AllRowsCandidateOnly vocabularyRows

    vocabularyRowsPromotedFalse :
      CandidateOnly.AllRowsPromotedFalse vocabularyRows

    bioactiveRecognitionBridge :
      Bioactive.BioactiveMolecularRecognitionBridge

    bioactiveRecognitionBridgeIsCanonical :
      bioactiveRecognitionBridge
      ≡
      Bioactive.canonicalBioactiveMolecularRecognitionBridge

    bioactiveClinicalAuthorityFalse :
      Bioactive.BioactiveMolecularRecognitionBridge.clinicalAuthorityClaimFlag
        bioactiveRecognitionBridge
      ≡
      false

    authorityBoundary :
      Boundary.NeurochemicalAuthorityBoundary

    authorityBoundaryIsCanonical :
      authorityBoundary
      ≡
      Boundary.canonicalNeurochemicalAuthorityBoundary

    authorityBoundaryClinicalFalse :
      Boundary.NeurochemicalAuthorityBoundary.clinicalValidityAccepted
        authorityBoundary
      ≡
      false

    authorityBoundaryBrainStateRecoveryFalse :
      Boundary.NeurochemicalAuthorityBoundary.brainStateRecoveryPromoted
        authorityBoundary
      ≡
      false

    candidateOnlyCoreRow :
      CandidateOnly.CandidateOnlyRow

    candidateOnlyCoreRowIsCanonical :
      candidateOnlyCoreRow ≡ neurochemicalCandidateOnlyCoreRow

    candidateOnlyCoreReceipt :
      CandidateOnly.CandidateOnlyReceipt candidateOnlyCoreRow

    candidateOnlyCoreReceiptCandidateOnlyTrue :
      CandidateOnly.candidateOnly candidateOnlyCoreRow ≡ true

    candidateOnlyCoreReceiptPromotedFalse :
      CandidateOnly.promoted candidateOnlyCoreRow ≡ false

    authorityNonPromotionBundle :
      Authority.AuthorityNonPromotionBundle

    authorityNonPromotionBundleIsCanonical :
      authorityNonPromotionBundle ≡ neurochemicalAuthorityBundle

    authorityNonPromotionClinicalFalse :
      Authority.clinicalAuthorityFlag authorityNonPromotionBundle ≡ false

    authorityNonPromotionEmpiricalFalse :
      Authority.empiricalAuthorityFlag authorityNonPromotionBundle ≡ false

    authorityNonPromotionPromotesAnyFalse :
      Authority.promotesAnyAuthority authorityNonPromotionBundle ≡ false

    functionalSurface :
      Functional.CandidateFunctionalSurface

    functionalSurfaceIsCanonical :
      functionalSurface ≡ neurochemicalFunctionalSurface

    functionalSurfaceClinicalAuthorityFalse :
      Functional.clinicalAuthority functionalSurface ≡ false

    functionalSurfaceNumericAuthorityFalse :
      Functional.numericAuthority functionalSurface ≡ false

    operatorShapeReceipt :
      OperatorShape.OperatorShapeCandidateReceipt

    operatorShapeReceiptIsCanonical :
      operatorShapeReceipt ≡ neurochemicalOperatorShapeReceipt

    operatorShapeTheoremAuthorityFalse :
      OperatorShape.actualTheoremAuthority operatorShapeReceipt ≡ false

    carriers :
      List NeurochemicalTransmissionCarrier

    carriersAreCanonical :
      carriers ≡ canonicalNeurochemicalTransmissionCarriers

    modes :
      List NeurochemicalTransmissionMode

    modesAreCanonical :
      modes ≡ canonicalNeurochemicalTransmissionModes

    guards :
      List NeurochemicalTransmissionGuard

    guardsAreCanonical :
      guards ≡ canonicalNeurochemicalTransmissionGuards

    formalLenses :
      List FormalLens.FormalLens

    formalLensesAreCanonical :
      formalLenses ≡ canonicalNeurochemicalFormalLenses

    TransmitterCandidate :
      Set

    ReceptorContext :
      Set

    SynapticTransmission :
      Set

    VolumeTransmission :
      Set

    TransporterContext :
      Set

    EnzymeClearanceContext :
      Set

    ConcentrationTimecourse :
      Set

    ReceptorOccupancyCandidate :
      Set

    NeuralEncodingCandidate :
      Set

    PlasticityModulationCandidate :
      Set

    BehaviorQuotientResidual :
      Set

    TransmissionObservation :
      Set

    TransmissionReceipt :
      Set

    observeTransmission :
      TransmitterCandidate →
      ReceptorContext →
      SynapticTransmission →
      VolumeTransmission →
      TransmissionObservation

    concentrationFromObservation :
      TransmissionObservation →
      ConcentrationTimecourse

    occupancyFromObservation :
      TransmissionObservation →
      ReceptorOccupancyCandidate

    neuralEncodingFromObservation :
      TransmissionObservation →
      NeuralEncodingCandidate

    plasticityFromObservation :
      TransmissionObservation →
      PlasticityModulationCandidate

    behaviorResidualFromObservation :
      TransmissionObservation →
      BehaviorQuotientResidual

    transmissionReceipt :
      TransmissionObservation →
      TransmissionReceipt

    receiptGate :
      TransmissionObservation →
      TransmissionReceipt →
      Set

    route :
      NeurochemicalTransmissionRoute

    routeIsBounded :
      route ≡ boundedNeurochemicalTransmissionRoute

    routeAdmissible :
      AdmissibleNeurochemicalTransmissionRoute route

    clinicalAuthority :
      Bool

    clinicalAuthorityIsFalse :
      clinicalAuthority ≡ false

    therapeuticAuthority :
      Bool

    therapeuticAuthorityIsFalse :
      therapeuticAuthority ≡ false

    doseResponseAuthority :
      Bool

    doseResponseAuthorityIsFalse :
      doseResponseAuthority ≡ false

    diseaseCausationAuthority :
      Bool

    diseaseCausationAuthorityIsFalse :
      diseaseCausationAuthority ≡ false

    behaviorCausationAuthority :
      Bool

    behaviorCausationAuthorityIsFalse :
      behaviorCausationAuthority ≡ false

    diagnosisAuthority :
      Bool

    diagnosisAuthorityIsFalse :
      diagnosisAuthority ≡ false

    biomarkerAuthority :
      Bool

    biomarkerAuthorityIsFalse :
      biomarkerAuthority ≡ false

    brainStateRecoveryAuthority :
      Bool

    brainStateRecoveryAuthorityIsFalse :
      brainStateRecoveryAuthority ≡ false

    transmitterOperatorIdentityAuthority :
      Bool

    transmitterOperatorIdentityAuthorityIsFalse :
      transmitterOperatorIdentityAuthority ≡ false

    bridgeReading :
      String

open NeurochemicalTransmissionBridge public

canonicalNeurochemicalTransmissionBridge :
  NeurochemicalTransmissionBridge
canonicalNeurochemicalTransmissionBridge =
  record
    { vocabularyRows =
        Vocabulary.canonicalNeurochemicalVocabularyRows
    ; vocabularyRowsAreCanonical =
        refl
    ; vocabularyRowsCandidateOnly =
        Vocabulary.canonicalNeurochemicalVocabularyRowsCandidateOnly
    ; vocabularyRowsPromotedFalse =
        Vocabulary.canonicalNeurochemicalVocabularyRowsPromotedFalse
    ; bioactiveRecognitionBridge =
        Bioactive.canonicalBioactiveMolecularRecognitionBridge
    ; bioactiveRecognitionBridgeIsCanonical =
        refl
    ; bioactiveClinicalAuthorityFalse =
        refl
    ; authorityBoundary =
        Boundary.canonicalNeurochemicalAuthorityBoundary
    ; authorityBoundaryIsCanonical =
        refl
    ; authorityBoundaryClinicalFalse =
        refl
    ; authorityBoundaryBrainStateRecoveryFalse =
        refl
    ; candidateOnlyCoreRow =
        neurochemicalCandidateOnlyCoreRow
    ; candidateOnlyCoreRowIsCanonical =
        refl
    ; candidateOnlyCoreReceipt =
        neurochemicalCandidateOnlyCoreReceipt
    ; candidateOnlyCoreReceiptCandidateOnlyTrue =
        refl
    ; candidateOnlyCoreReceiptPromotedFalse =
        refl
    ; authorityNonPromotionBundle =
        neurochemicalAuthorityBundle
    ; authorityNonPromotionBundleIsCanonical =
        refl
    ; authorityNonPromotionClinicalFalse =
        refl
    ; authorityNonPromotionEmpiricalFalse =
        refl
    ; authorityNonPromotionPromotesAnyFalse =
        refl
    ; functionalSurface =
        neurochemicalFunctionalSurface
    ; functionalSurfaceIsCanonical =
        refl
    ; functionalSurfaceClinicalAuthorityFalse =
        refl
    ; functionalSurfaceNumericAuthorityFalse =
        refl
    ; operatorShapeReceipt =
        neurochemicalOperatorShapeReceipt
    ; operatorShapeReceiptIsCanonical =
        refl
    ; operatorShapeTheoremAuthorityFalse =
        refl
    ; carriers =
        canonicalNeurochemicalTransmissionCarriers
    ; carriersAreCanonical =
        refl
    ; modes =
        canonicalNeurochemicalTransmissionModes
    ; modesAreCanonical =
        refl
    ; guards =
        canonicalNeurochemicalTransmissionGuards
    ; guardsAreCanonical =
        refl
    ; formalLenses =
        canonicalNeurochemicalFormalLenses
    ; formalLensesAreCanonical =
        refl
    ; TransmitterCandidate =
        ⊤
    ; ReceptorContext =
        ⊤
    ; SynapticTransmission =
        ⊤
    ; VolumeTransmission =
        ⊤
    ; TransporterContext =
        ⊤
    ; EnzymeClearanceContext =
        ⊤
    ; ConcentrationTimecourse =
        ⊤
    ; ReceptorOccupancyCandidate =
        ⊤
    ; NeuralEncodingCandidate =
        ⊤
    ; PlasticityModulationCandidate =
        ⊤
    ; BehaviorQuotientResidual =
        ⊤
    ; TransmissionObservation =
        ⊤
    ; TransmissionReceipt =
        ⊤
    ; observeTransmission =
        λ _ _ _ _ → tt
    ; concentrationFromObservation =
        λ _ → tt
    ; occupancyFromObservation =
        λ _ → tt
    ; neuralEncodingFromObservation =
        λ _ → tt
    ; plasticityFromObservation =
        λ _ → tt
    ; behaviorResidualFromObservation =
        λ _ → tt
    ; transmissionReceipt =
        λ _ → tt
    ; receiptGate =
        λ _ _ → ⊤
    ; route =
        boundedNeurochemicalTransmissionRoute
    ; routeIsBounded =
        refl
    ; routeAdmissible =
        tt
    ; clinicalAuthority =
        false
    ; clinicalAuthorityIsFalse =
        refl
    ; therapeuticAuthority =
        false
    ; therapeuticAuthorityIsFalse =
        refl
    ; doseResponseAuthority =
        false
    ; doseResponseAuthorityIsFalse =
        refl
    ; diseaseCausationAuthority =
        false
    ; diseaseCausationAuthorityIsFalse =
        refl
    ; behaviorCausationAuthority =
        false
    ; behaviorCausationAuthorityIsFalse =
        refl
    ; diagnosisAuthority =
        false
    ; diagnosisAuthorityIsFalse =
        refl
    ; biomarkerAuthority =
        false
    ; biomarkerAuthorityIsFalse =
        refl
    ; brainStateRecoveryAuthority =
        false
    ; brainStateRecoveryAuthorityIsFalse =
        refl
    ; transmitterOperatorIdentityAuthority =
        false
    ; transmitterOperatorIdentityAuthorityIsFalse =
        refl
    ; bridgeReading =
        "Neurochemical transmission is represented as candidate-only carrier infrastructure over transmitter, receptor, synaptic, volume, clearance, timecourse, occupancy, neural-encoding, plasticity, and behavior-residual carriers; clinical, therapeutic, dose-response, disease, behavior, diagnosis, biomarker, brain-state, and transmitter-operator identity authority remain blocked."
    }

canonicalNeurochemicalTransmissionClinicalAuthorityFalse :
  NeurochemicalTransmissionBridge.clinicalAuthority
    canonicalNeurochemicalTransmissionBridge
  ≡
  false
canonicalNeurochemicalTransmissionClinicalAuthorityFalse =
  refl

canonicalNeurochemicalTransmissionDoseResponseAuthorityFalse :
  NeurochemicalTransmissionBridge.doseResponseAuthority
    canonicalNeurochemicalTransmissionBridge
  ≡
  false
canonicalNeurochemicalTransmissionDoseResponseAuthorityFalse =
  refl

canonicalNeurochemicalTransmissionBehaviorCausationAuthorityFalse :
  NeurochemicalTransmissionBridge.behaviorCausationAuthority
    canonicalNeurochemicalTransmissionBridge
  ≡
  false
canonicalNeurochemicalTransmissionBehaviorCausationAuthorityFalse =
  refl

canonicalNeurochemicalTransmissionBrainStateRecoveryAuthorityFalse :
  NeurochemicalTransmissionBridge.brainStateRecoveryAuthority
    canonicalNeurochemicalTransmissionBridge
  ≡
  false
canonicalNeurochemicalTransmissionBrainStateRecoveryAuthorityFalse =
  refl

canonicalNeurochemicalTransmissionTransmitterOperatorIdentityAuthorityFalse :
  NeurochemicalTransmissionBridge.transmitterOperatorIdentityAuthority
    canonicalNeurochemicalTransmissionBridge
  ≡
  false
canonicalNeurochemicalTransmissionTransmitterOperatorIdentityAuthorityFalse =
  refl
