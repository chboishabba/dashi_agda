module DASHI.Biology.EmbodiedMotorMultisensoryBridge where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

open import DASHI.Biology.AnimalexicAnimalUtteranceSurface
import DASHI.Core.AuthorityNonPromotionCore as AuthorityNA
import DASHI.Core.CandidateOnlyCore as CandidateOnly

------------------------------------------------------------------------
-- Embodied motor / nociception / proprioception / vestibular vocabulary.
--
-- This module is a bounded Animalexic biology-stack surface.  It treats
-- movement, nociception, proprioception, vestibular readout, and multisensory
-- integration as receipt-gated observation channels, not as intent recovery,
-- pain qualia identity, a full motor policy, or sensor-fusion closure.

data EmbodiedObservationChannel : Set where
  motorControlChannel : EmbodiedObservationChannel
  nociceptionChannel : EmbodiedObservationChannel
  proprioceptionChannel : EmbodiedObservationChannel
  vestibularChannel : EmbodiedObservationChannel
  multisensoryContextChannel : EmbodiedObservationChannel
  behaviourEnvelopeChannel : EmbodiedObservationChannel

data EmbodiedIntegrationLayer : Set where
  efferentCommandLayer : EmbodiedIntegrationLayer
  spinalReflexLayer : EmbodiedIntegrationLayer
  nociceptorTransductionLayer : EmbodiedIntegrationLayer
  proprioceptorFeedbackLayer : EmbodiedIntegrationLayer
  vestibularReadoutLayer : EmbodiedIntegrationLayer
  multisensoryBindingLayer : EmbodiedIntegrationLayer
  behaviourConstraintLayer : EmbodiedIntegrationLayer
  animalexicReceiptLayer : EmbodiedIntegrationLayer

data EmbodiedNonPromotionGuard : Set where
  NoIntentRecoveryClaim : EmbodiedNonPromotionGuard
  NoPainQualiaIdentityClaim : EmbodiedNonPromotionGuard
  NoFullMotorPolicyClaim : EmbodiedNonPromotionGuard
  NoSensorFusionClosureClaim : EmbodiedNonPromotionGuard
  NoSingleChannelDiagnosisClaim : EmbodiedNonPromotionGuard
  NoSpeciesUniversalMotorLexiconClaim : EmbodiedNonPromotionGuard

data MotorEvidenceKind : Set where
  postureChangeEvidence : MotorEvidenceKind
  gaitPhaseEvidence : MotorEvidenceKind
  limbTrajectoryEvidence : MotorEvidenceKind
  contactForceEvidence : MotorEvidenceKind
  reflexWithdrawalEvidence : MotorEvidenceKind
  balanceCorrectionEvidence : MotorEvidenceKind
  contextCouplingEvidence : MotorEvidenceKind

defaultEmbodiedChannels : List EmbodiedObservationChannel
defaultEmbodiedChannels =
  motorControlChannel
  ∷ nociceptionChannel
  ∷ proprioceptionChannel
  ∷ vestibularChannel
  ∷ multisensoryContextChannel
  ∷ behaviourEnvelopeChannel
  ∷ []

defaultEmbodiedIntegrationLayers : List EmbodiedIntegrationLayer
defaultEmbodiedIntegrationLayers =
  efferentCommandLayer
  ∷ spinalReflexLayer
  ∷ nociceptorTransductionLayer
  ∷ proprioceptorFeedbackLayer
  ∷ vestibularReadoutLayer
  ∷ multisensoryBindingLayer
  ∷ behaviourConstraintLayer
  ∷ animalexicReceiptLayer
  ∷ []

defaultEmbodiedNonPromotionGuards : List EmbodiedNonPromotionGuard
defaultEmbodiedNonPromotionGuards =
  NoIntentRecoveryClaim
  ∷ NoPainQualiaIdentityClaim
  ∷ NoFullMotorPolicyClaim
  ∷ NoSensorFusionClosureClaim
  ∷ NoSingleChannelDiagnosisClaim
  ∷ NoSpeciesUniversalMotorLexiconClaim
  ∷ []

------------------------------------------------------------------------
-- Bounded surface over an Animalexic observation stack.

record EmbodiedMotorMultisensorySurface
    (animalexic : AnimalexicAnimalUtteranceSurface) : Set₁ where
  field
    MotorCommandTrace : Set
    MotorEffectorState : Set
    NociceptiveSignal : Set
    PainBehaviourClass : Set
    ProprioceptiveSignal : Set
    VestibularSignal : Set
    MultisensoryBodyEstimate : Set
    BehaviourEnvelope : Set
    MotorPolicyConstraint : Set
    EmbodiedReceipt : Set

    motorCommandFromTrace :
      ObservationTrace animalexic →
      MotorCommandTrace

    effectorFromMotor :
      MotorCommandTrace →
      MotorEffectorState

    nociceptionFromTrace :
      ObservationTrace animalexic →
      NociceptiveSignal

    painBehaviourClass :
      NociceptiveSignal →
      PainBehaviourClass

    proprioceptionFromTrace :
      ObservationTrace animalexic →
      ProprioceptiveSignal

    vestibularFromTrace :
      ObservationTrace animalexic →
      VestibularSignal

    integrateBodyEstimate :
      MotorEffectorState →
      NociceptiveSignal →
      ProprioceptiveSignal →
      VestibularSignal →
      MultisensoryBodyEstimate

    behaviourEnvelopeFromEstimate :
      MultisensoryBodyEstimate →
      PainBehaviourClass →
      BehaviourEnvelope

    constrainMotorPolicy :
      BehaviourEnvelope →
      MotorPolicyConstraint

    animalexicReceipt :
      ObservationTrace animalexic →
      BehaviourEnvelope →
      EmbodiedReceipt

    receiptEvidence :
      EmbodiedReceipt →
      List MotorEvidenceKind

    receiptAdmissible :
      EmbodiedReceipt →
      Set

    surfaceReading :
      String

open EmbodiedMotorMultisensorySurface public

record EmbodiedMultisensoryObservation
    {animalexic : AnimalexicAnimalUtteranceSurface}
    (surface : EmbodiedMotorMultisensorySurface animalexic) : Set where
  field
    trace :
      ObservationTrace animalexic

    motorCommand :
      MotorCommandTrace surface

    motorCommandMatches :
      motorCommand ≡ motorCommandFromTrace surface trace

    effectorState :
      MotorEffectorState surface

    effectorStateMatches :
      effectorState ≡ effectorFromMotor surface motorCommand

    nociceptiveSignal :
      NociceptiveSignal surface

    nociceptiveSignalMatches :
      nociceptiveSignal ≡ nociceptionFromTrace surface trace

    painClass :
      PainBehaviourClass surface

    painClassMatches :
      painClass ≡ painBehaviourClass surface nociceptiveSignal

    proprioceptiveSignal :
      ProprioceptiveSignal surface

    proprioceptiveSignalMatches :
      proprioceptiveSignal ≡ proprioceptionFromTrace surface trace

    vestibularSignal :
      VestibularSignal surface

    vestibularSignalMatches :
      vestibularSignal ≡ vestibularFromTrace surface trace

open EmbodiedMultisensoryObservation public

record MultisensoryBodyIntegration
    {animalexic : AnimalexicAnimalUtteranceSurface}
    {surface : EmbodiedMotorMultisensorySurface animalexic}
    (observation : EmbodiedMultisensoryObservation surface) : Set where
  field
    bodyEstimate :
      MultisensoryBodyEstimate surface

    bodyEstimateMatches :
      bodyEstimate ≡
        integrateBodyEstimate
          surface
          (effectorState observation)
          (nociceptiveSignal observation)
          (proprioceptiveSignal observation)
          (vestibularSignal observation)

    behaviourEnvelope :
      BehaviourEnvelope surface

    behaviourEnvelopeMatches :
      behaviourEnvelope ≡
        behaviourEnvelopeFromEstimate
          surface
          bodyEstimate
          (painClass observation)

    policyConstraint :
      MotorPolicyConstraint surface

    policyConstraintMatches :
      policyConstraint ≡
        constrainMotorPolicy surface behaviourEnvelope

open MultisensoryBodyIntegration public

record EmbodiedMotorMultisensoryBridge
    (animalexic : AnimalexicAnimalUtteranceSurface) : Set₁ where
  field
    surface :
      EmbodiedMotorMultisensorySurface animalexic

    channels :
      List EmbodiedObservationChannel

    layers :
      List EmbodiedIntegrationLayer

    guards :
      List EmbodiedNonPromotionGuard

    bridgeReading :
      String

    candidateOnlyCoreAdapter :
      CandidateOnly.CandidateOnlyRow

    candidateOnlyCoreAdapterReceipt :
      CandidateOnly.CandidateOnlyReceipt candidateOnlyCoreAdapter

    candidateOnlyCoreAdapterCandidateOnly :
      CandidateOnly.candidateOnly candidateOnlyCoreAdapter ≡ true

    candidateOnlyCoreAdapterPromotedFalse :
      CandidateOnly.promoted candidateOnlyCoreAdapter ≡ false

    candidateOnlyCoreAdapterTruthAuthorityFalse :
      CandidateOnly.carriesTruthAuthority candidateOnlyCoreAdapter ≡ false

    candidateOnlyCoreAdapterRuntimeAuthorityFalse :
      CandidateOnly.carriesRuntimeAuthority candidateOnlyCoreAdapter ≡ false

    candidateOnlyCoreAdapterTheoremAuthorityFalse :
      CandidateOnly.carriesTheoremAuthority candidateOnlyCoreAdapter ≡ false

    authorityNonPromotionCoreAdapter :
      AuthorityNA.AuthorityNonPromotionBundle

    authorityNonPromotionCoreAdapterCanonicalKindsFalse :
      AuthorityNA.AllAuthorityKindsFalse
        authorityNonPromotionCoreAdapter
        AuthorityNA.canonicalAuthorityKinds

    authorityNonPromotionCoreAdapterClinicalAuthorityFalse :
      AuthorityNA.clinicalAuthorityFlag authorityNonPromotionCoreAdapter
      ≡ false

    authorityNonPromotionCoreAdapterScientificAuthorityFalse :
      AuthorityNA.scientificAuthorityFlag authorityNonPromotionCoreAdapter
      ≡ false

    authorityNonPromotionCoreAdapterEmpiricalAuthorityFalse :
      AuthorityNA.empiricalAuthorityFlag authorityNonPromotionCoreAdapter
      ≡ false

    authorityNonPromotionCoreAdapterExternalAuthorityFalse :
      AuthorityNA.externalAuthorityFlag authorityNonPromotionCoreAdapter
      ≡ false

    authorityNonPromotionCoreAdapterPromotesAnyAuthorityFalse :
      AuthorityNA.promotesAnyAuthority authorityNonPromotionCoreAdapter
      ≡ false

    intentRecoveryClaim :
      Bool

    intentRecoveryClaimIsFalse :
      intentRecoveryClaim ≡ false

    painQualiaIdentityClaim :
      Bool

    painQualiaIdentityClaimIsFalse :
      painQualiaIdentityClaim ≡ false

    fullMotorPolicyClaim :
      Bool

    fullMotorPolicyClaimIsFalse :
      fullMotorPolicyClaim ≡ false

    sensorFusionClosureClaim :
      Bool

    sensorFusionClosureClaimIsFalse :
      sensorFusionClosureClaim ≡ false

open EmbodiedMotorMultisensoryBridge public

record EmbodiedAnimalexicPromotionGate
    {animalexic : AnimalexicAnimalUtteranceSurface}
    (bridge : EmbodiedMotorMultisensoryBridge animalexic)
    (observation : EmbodiedMultisensoryObservation (surface bridge))
    (integration : MultisensoryBodyIntegration observation) : Set where
  field
    embodiedReceipt :
      EmbodiedReceipt (surface bridge)

    embodiedReceiptMatches :
      embodiedReceipt ≡
        animalexicReceipt
          (surface bridge)
          (trace observation)
          (behaviourEnvelope integration)

    embodiedReceiptAdmissible :
      receiptAdmissible (surface bridge) embodiedReceipt

    evidenceKinds :
      List MotorEvidenceKind

    evidenceKindsMatch :
      evidenceKinds ≡ receiptEvidence (surface bridge) embodiedReceipt

    promotedBehaviourOnly :
      Bool

    promotedBehaviourOnlyIsTrue :
      promotedBehaviourOnly ≡ true

open EmbodiedAnimalexicPromotionGate public

record EmbodiedNonPromotionCertificate
    {animalexic : AnimalexicAnimalUtteranceSurface}
    (bridge : EmbodiedMotorMultisensoryBridge animalexic) : Set where
  field
    guardsPresent :
      guards bridge ≡ defaultEmbodiedNonPromotionGuards

    intentRecoveryBlocked :
      intentRecoveryClaim bridge ≡ false

    painQualiaIdentityBlocked :
      painQualiaIdentityClaim bridge ≡ false

    fullMotorPolicyBlocked :
      fullMotorPolicyClaim bridge ≡ false

    sensorFusionClosureBlocked :
      sensorFusionClosureClaim bridge ≡ false

    certificateReading :
      String

open EmbodiedNonPromotionCertificate public

canonicalEmbodiedNonPromotionCertificate :
  {animalexic : AnimalexicAnimalUtteranceSurface} →
  (bridge : EmbodiedMotorMultisensoryBridge animalexic) →
  guards bridge ≡ defaultEmbodiedNonPromotionGuards →
  EmbodiedNonPromotionCertificate bridge
canonicalEmbodiedNonPromotionCertificate bridge guardsProof =
  record
    { guardsPresent =
        guardsProof
    ; intentRecoveryBlocked =
        intentRecoveryClaimIsFalse bridge
    ; painQualiaIdentityBlocked =
        painQualiaIdentityClaimIsFalse bridge
    ; fullMotorPolicyBlocked =
        fullMotorPolicyClaimIsFalse bridge
    ; sensorFusionClosureBlocked =
        sensorFusionClosureClaimIsFalse bridge
    ; certificateReading =
        "Embodied motor and multisensory channels constrain behavioural interpretation only; they do not recover intent, identify pain qualia, close a full motor policy, or close sensor fusion."
    }

------------------------------------------------------------------------
-- Canonical toy inhabitant.

canonicalEmbodiedAnimalexicSurface :
  AnimalexicAnimalUtteranceSurface
canonicalEmbodiedAnimalexicSurface =
  record
    { Animal = ⊤
    ; Context = ⊤
    ; UtteranceEvent = ⊤
    ; ObservationTrace = ⊤
    ; BodyStateCandidate = ⊤
    ; SocialStateCandidate = ⊤
    ; LatentCandidate = ⊤
    ; BehaviouralMeaning = ⊤
    ; Receipt = ⊤
    ; ProvenanceNode = ⊤
    ; ObserverProtocol = ⊤
    ; observe = λ _ _ _ → tt
    ; observedModalities =
        λ _ →
          motionTrace
          ∷ postureTrace
          ∷ contactTrace
          ∷ physiologicalTrace
          ∷ []
    ; candidateBodyState = λ _ → tt
    ; candidateSocialState = λ _ → tt
    ; candidateLatentState = λ _ _ _ → tt
    ; latentAspects =
        λ _ →
          bodyArousal
          ∷ painOrDiscomfort
          ∷ environmentalAttention
          ∷ []
    ; admissibilityReceipt = λ _ _ → tt
    ; provenanceTrail = λ _ → tt ∷ []
    ; observerProtocol = λ _ → tt
    ; promoteBehaviouralMeaning = λ _ _ _ → tt
    ; multimodalReceiptComplete = λ _ _ _ → ⊤
    ; provenanceAdmissible = λ _ → ⊤
    ; boundaryReading =
        noDirectQualiaClaim
        ∷ noSingleChannelCertainty
        ∷ noSpeciesUniversalDictionary
        ∷ []
    }

canonicalEmbodiedMotorMultisensorySurface :
  EmbodiedMotorMultisensorySurface
    canonicalEmbodiedAnimalexicSurface
canonicalEmbodiedMotorMultisensorySurface =
  record
    { MotorCommandTrace = ⊤
    ; MotorEffectorState = ⊤
    ; NociceptiveSignal = ⊤
    ; PainBehaviourClass = ⊤
    ; ProprioceptiveSignal = ⊤
    ; VestibularSignal = ⊤
    ; MultisensoryBodyEstimate = ⊤
    ; BehaviourEnvelope = ⊤
    ; MotorPolicyConstraint = ⊤
    ; EmbodiedReceipt = ⊤
    ; motorCommandFromTrace = λ _ → tt
    ; effectorFromMotor = λ _ → tt
    ; nociceptionFromTrace = λ _ → tt
    ; painBehaviourClass = λ _ → tt
    ; proprioceptionFromTrace = λ _ → tt
    ; vestibularFromTrace = λ _ → tt
    ; integrateBodyEstimate = λ _ _ _ _ → tt
    ; behaviourEnvelopeFromEstimate = λ _ _ → tt
    ; constrainMotorPolicy = λ _ → tt
    ; animalexicReceipt = λ _ _ → tt
    ; receiptEvidence =
        λ _ →
          postureChangeEvidence
          ∷ gaitPhaseEvidence
          ∷ reflexWithdrawalEvidence
          ∷ balanceCorrectionEvidence
          ∷ contextCouplingEvidence
          ∷ []
    ; receiptAdmissible = λ _ → ⊤
    ; surfaceReading =
        "Toy embodied surface constrains behaviour envelopes from motor, pain-behaviour, proprioceptive, vestibular, and contextual traces."
    }

canonicalEmbodiedCandidateOnlyCoreAdapter :
  CandidateOnly.CandidateOnlyRow
canonicalEmbodiedCandidateOnlyCoreAdapter =
  CandidateOnly.mkCandidateOnlyRow
    "embodied motor multisensory candidate-only adapter"
    "DASHI.Biology.EmbodiedMotorMultisensoryBridge"
    "canonicalEmbodiedMotorMultisensoryBridge"
    CandidateOnly.bridgeCandidateKind
    CandidateOnly.bridgeCandidateOnlyStatus
    "Embodied motor and multisensory bridge receipts constrain candidate behavioural interpretation only."
    "Intent recovery, pain-qualia identity, full motor-policy closure, and sensor-fusion closure remain blocked."

canonicalEmbodiedCandidateOnlyCoreAdapterReceipt :
  CandidateOnly.CandidateOnlyReceipt
    canonicalEmbodiedCandidateOnlyCoreAdapter
canonicalEmbodiedCandidateOnlyCoreAdapterReceipt =
  CandidateOnly.canonicalCandidateOnlyReceipt
    canonicalEmbodiedCandidateOnlyCoreAdapter
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalEmbodiedCandidateOnlyCoreAdapterCandidateOnly :
  CandidateOnly.candidateOnly canonicalEmbodiedCandidateOnlyCoreAdapter
  ≡
  true
canonicalEmbodiedCandidateOnlyCoreAdapterCandidateOnly =
  CandidateOnly.candidateOnlyIsTrue
    canonicalEmbodiedCandidateOnlyCoreAdapterReceipt

canonicalEmbodiedCandidateOnlyCoreAdapterPromotedFalse :
  CandidateOnly.promoted canonicalEmbodiedCandidateOnlyCoreAdapter
  ≡
  false
canonicalEmbodiedCandidateOnlyCoreAdapterPromotedFalse =
  CandidateOnly.candidatePromotedIsFalse
    canonicalEmbodiedCandidateOnlyCoreAdapterReceipt

canonicalEmbodiedCandidateOnlyCoreAdapterTruthAuthorityFalse :
  CandidateOnly.carriesTruthAuthority canonicalEmbodiedCandidateOnlyCoreAdapter
  ≡
  false
canonicalEmbodiedCandidateOnlyCoreAdapterTruthAuthorityFalse =
  CandidateOnly.candidateNoTruthAuthority
    canonicalEmbodiedCandidateOnlyCoreAdapterReceipt

canonicalEmbodiedCandidateOnlyCoreAdapterRuntimeAuthorityFalse :
  CandidateOnly.carriesRuntimeAuthority canonicalEmbodiedCandidateOnlyCoreAdapter
  ≡
  false
canonicalEmbodiedCandidateOnlyCoreAdapterRuntimeAuthorityFalse =
  CandidateOnly.candidateNoRuntimeAuthority
    canonicalEmbodiedCandidateOnlyCoreAdapterReceipt

canonicalEmbodiedCandidateOnlyCoreAdapterTheoremAuthorityFalse :
  CandidateOnly.carriesTheoremAuthority canonicalEmbodiedCandidateOnlyCoreAdapter
  ≡
  false
canonicalEmbodiedCandidateOnlyCoreAdapterTheoremAuthorityFalse =
  CandidateOnly.candidateNoTheoremAuthority
    canonicalEmbodiedCandidateOnlyCoreAdapterReceipt

canonicalEmbodiedAuthorityNonPromotionCoreAdapter :
  AuthorityNA.AuthorityNonPromotionBundle
canonicalEmbodiedAuthorityNonPromotionCoreAdapter =
  AuthorityNA.mkClosedAuthorityNonPromotionBundle
    "embodied motor multisensory authority non-promotion adapter"

canonicalEmbodiedAuthorityNonPromotionCoreAdapterCanonicalKindsFalse :
  AuthorityNA.AllAuthorityKindsFalse
    canonicalEmbodiedAuthorityNonPromotionCoreAdapter
    AuthorityNA.canonicalAuthorityKinds
canonicalEmbodiedAuthorityNonPromotionCoreAdapterCanonicalKindsFalse =
  AuthorityNA.proveAllAuthorityKindsFalse
    canonicalEmbodiedAuthorityNonPromotionCoreAdapter
    AuthorityNA.canonicalAuthorityKinds

canonicalEmbodiedAuthorityNonPromotionCoreAdapterClinicalAuthorityFalse :
  AuthorityNA.clinicalAuthorityFlag
    canonicalEmbodiedAuthorityNonPromotionCoreAdapter
  ≡
  false
canonicalEmbodiedAuthorityNonPromotionCoreAdapterClinicalAuthorityFalse =
  AuthorityNA.bundleClinicalAuthorityIsFalse
    canonicalEmbodiedAuthorityNonPromotionCoreAdapter

canonicalEmbodiedAuthorityNonPromotionCoreAdapterScientificAuthorityFalse :
  AuthorityNA.scientificAuthorityFlag
    canonicalEmbodiedAuthorityNonPromotionCoreAdapter
  ≡
  false
canonicalEmbodiedAuthorityNonPromotionCoreAdapterScientificAuthorityFalse =
  AuthorityNA.bundleScientificAuthorityIsFalse
    canonicalEmbodiedAuthorityNonPromotionCoreAdapter

canonicalEmbodiedAuthorityNonPromotionCoreAdapterEmpiricalAuthorityFalse :
  AuthorityNA.empiricalAuthorityFlag
    canonicalEmbodiedAuthorityNonPromotionCoreAdapter
  ≡
  false
canonicalEmbodiedAuthorityNonPromotionCoreAdapterEmpiricalAuthorityFalse =
  AuthorityNA.bundleEmpiricalAuthorityIsFalse
    canonicalEmbodiedAuthorityNonPromotionCoreAdapter

canonicalEmbodiedAuthorityNonPromotionCoreAdapterExternalAuthorityFalse :
  AuthorityNA.externalAuthorityFlag
    canonicalEmbodiedAuthorityNonPromotionCoreAdapter
  ≡
  false
canonicalEmbodiedAuthorityNonPromotionCoreAdapterExternalAuthorityFalse =
  AuthorityNA.bundleExternalAuthorityIsFalse
    canonicalEmbodiedAuthorityNonPromotionCoreAdapter

canonicalEmbodiedAuthorityNonPromotionCoreAdapterPromotesAnyAuthorityFalse :
  AuthorityNA.promotesAnyAuthority
    canonicalEmbodiedAuthorityNonPromotionCoreAdapter
  ≡
  false
canonicalEmbodiedAuthorityNonPromotionCoreAdapterPromotesAnyAuthorityFalse =
  AuthorityNA.bundlePromotesAnyAuthorityIsFalse
    canonicalEmbodiedAuthorityNonPromotionCoreAdapter

canonicalEmbodiedMotorMultisensoryBridge :
  EmbodiedMotorMultisensoryBridge
    canonicalEmbodiedAnimalexicSurface
canonicalEmbodiedMotorMultisensoryBridge =
  record
    { surface = canonicalEmbodiedMotorMultisensorySurface
    ; channels = defaultEmbodiedChannels
    ; layers = defaultEmbodiedIntegrationLayers
    ; guards = defaultEmbodiedNonPromotionGuards
    ; bridgeReading =
        "Embodied motor and multisensory channels are receipt-gated constraints on Animalexic behavioural interpretation."
    ; candidateOnlyCoreAdapter =
        canonicalEmbodiedCandidateOnlyCoreAdapter
    ; candidateOnlyCoreAdapterReceipt =
        canonicalEmbodiedCandidateOnlyCoreAdapterReceipt
    ; candidateOnlyCoreAdapterCandidateOnly =
        canonicalEmbodiedCandidateOnlyCoreAdapterCandidateOnly
    ; candidateOnlyCoreAdapterPromotedFalse =
        canonicalEmbodiedCandidateOnlyCoreAdapterPromotedFalse
    ; candidateOnlyCoreAdapterTruthAuthorityFalse =
        canonicalEmbodiedCandidateOnlyCoreAdapterTruthAuthorityFalse
    ; candidateOnlyCoreAdapterRuntimeAuthorityFalse =
        canonicalEmbodiedCandidateOnlyCoreAdapterRuntimeAuthorityFalse
    ; candidateOnlyCoreAdapterTheoremAuthorityFalse =
        canonicalEmbodiedCandidateOnlyCoreAdapterTheoremAuthorityFalse
    ; authorityNonPromotionCoreAdapter =
        canonicalEmbodiedAuthorityNonPromotionCoreAdapter
    ; authorityNonPromotionCoreAdapterCanonicalKindsFalse =
        canonicalEmbodiedAuthorityNonPromotionCoreAdapterCanonicalKindsFalse
    ; authorityNonPromotionCoreAdapterClinicalAuthorityFalse =
        canonicalEmbodiedAuthorityNonPromotionCoreAdapterClinicalAuthorityFalse
    ; authorityNonPromotionCoreAdapterScientificAuthorityFalse =
        canonicalEmbodiedAuthorityNonPromotionCoreAdapterScientificAuthorityFalse
    ; authorityNonPromotionCoreAdapterEmpiricalAuthorityFalse =
        canonicalEmbodiedAuthorityNonPromotionCoreAdapterEmpiricalAuthorityFalse
    ; authorityNonPromotionCoreAdapterExternalAuthorityFalse =
        canonicalEmbodiedAuthorityNonPromotionCoreAdapterExternalAuthorityFalse
    ; authorityNonPromotionCoreAdapterPromotesAnyAuthorityFalse =
        canonicalEmbodiedAuthorityNonPromotionCoreAdapterPromotesAnyAuthorityFalse
    ; intentRecoveryClaim = false
    ; intentRecoveryClaimIsFalse = refl
    ; painQualiaIdentityClaim = false
    ; painQualiaIdentityClaimIsFalse = refl
    ; fullMotorPolicyClaim = false
    ; fullMotorPolicyClaimIsFalse = refl
    ; sensorFusionClosureClaim = false
    ; sensorFusionClosureClaimIsFalse = refl
    }

canonicalEmbodiedMultisensoryObservation :
  EmbodiedMultisensoryObservation
    canonicalEmbodiedMotorMultisensorySurface
canonicalEmbodiedMultisensoryObservation =
  record
    { trace = tt
    ; motorCommand = tt
    ; motorCommandMatches = refl
    ; effectorState = tt
    ; effectorStateMatches = refl
    ; nociceptiveSignal = tt
    ; nociceptiveSignalMatches = refl
    ; painClass = tt
    ; painClassMatches = refl
    ; proprioceptiveSignal = tt
    ; proprioceptiveSignalMatches = refl
    ; vestibularSignal = tt
    ; vestibularSignalMatches = refl
    }

canonicalMultisensoryBodyIntegration :
  MultisensoryBodyIntegration
    canonicalEmbodiedMultisensoryObservation
canonicalMultisensoryBodyIntegration =
  record
    { bodyEstimate = tt
    ; bodyEstimateMatches = refl
    ; behaviourEnvelope = tt
    ; behaviourEnvelopeMatches = refl
    ; policyConstraint = tt
    ; policyConstraintMatches = refl
    }

canonicalEmbodiedAnimalexicPromotionGate :
  EmbodiedAnimalexicPromotionGate
    canonicalEmbodiedMotorMultisensoryBridge
    canonicalEmbodiedMultisensoryObservation
    canonicalMultisensoryBodyIntegration
canonicalEmbodiedAnimalexicPromotionGate =
  record
    { embodiedReceipt = tt
    ; embodiedReceiptMatches = refl
    ; embodiedReceiptAdmissible = tt
    ; evidenceKinds =
        postureChangeEvidence
        ∷ gaitPhaseEvidence
        ∷ reflexWithdrawalEvidence
        ∷ balanceCorrectionEvidence
        ∷ contextCouplingEvidence
        ∷ []
    ; evidenceKindsMatch = refl
    ; promotedBehaviourOnly = true
    ; promotedBehaviourOnlyIsTrue = refl
    }

canonicalEmbodiedNonPromotionCertificateForToy :
  EmbodiedNonPromotionCertificate
    canonicalEmbodiedMotorMultisensoryBridge
canonicalEmbodiedNonPromotionCertificateForToy =
  canonicalEmbodiedNonPromotionCertificate
    canonicalEmbodiedMotorMultisensoryBridge
    refl
