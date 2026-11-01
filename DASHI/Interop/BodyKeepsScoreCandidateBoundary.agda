module DASHI.Interop.BodyKeepsScoreCandidateBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AuthorityNonPromotionCore as Authority
import DASHI.Crypto.RSAPlusOneIdentitySection as RSAPlusOne
import DASHI.Interop.MeditationQiBridge as MeditationQi

------------------------------------------------------------------------
-- Body Keeps the Score candidate boundary.
--
-- This module records a trauma/body-memory formal lens only.  It is not a
-- clinical model, diagnosis, treatment prescription, proof of therapeutic
-- efficacy, or authority surface.  The intended analogy is the same thin
-- shape as the RSA +1 identity-section adapter:
--
--   public composite surface  / hidden charts / +1 identity handle
--
-- For RSA, the public modulus does not reveal the hidden CRT charts.  For
-- the body-score reading, public symptom/narrative surfaces do not reveal
-- all body-state fibres.  A safety/agency +1 seed may provide a candidate
-- identity handle over selected fibres, but it does not factor, cure, or
-- promote the state.

------------------------------------------------------------------------
-- Carrier vocabulary.

data BodyStateFibre : Set where
  breathFibre : BodyStateFibre
  postureFibre : BodyStateFibre
  arousalFibre : BodyStateFibre
  affectFibre : BodyStateFibre
  sensoryFibre : BodyStateFibre
  memoryFibre : BodyStateFibre
  relationFibre : BodyStateFibre
  agencyFibre : BodyStateFibre
  painTensionFibre : BodyStateFibre
  motorImpulseFibre : BodyStateFibre

canonicalBodyStateFibres : List BodyStateFibre
canonicalBodyStateFibres =
  breathFibre
  ∷ postureFibre
  ∷ arousalFibre
  ∷ affectFibre
  ∷ sensoryFibre
  ∷ memoryFibre
  ∷ relationFibre
  ∷ agencyFibre
  ∷ painTensionFibre
  ∷ motorImpulseFibre
  ∷ []

data ObservedBodySurface : Set where
  behaviourSurface : ObservedBodySurface
  affectSurface : ObservedBodySurface
  postureSurface : ObservedBodySurface
  breathSurface : ObservedBodySurface
  startleSurface : ObservedBodySurface
  painTensionSurface : ObservedBodySurface
  memoryFragmentSurface : ObservedBodySurface
  relationalTriggerSurface : ObservedBodySurface
  narrativeGapSurface : ObservedBodySurface

canonicalObservedSurfaces : List ObservedBodySurface
canonicalObservedSurfaces =
  behaviourSurface
  ∷ affectSurface
  ∷ postureSurface
  ∷ breathSurface
  ∷ startleSurface
  ∷ painTensionSurface
  ∷ memoryFragmentSurface
  ∷ relationalTriggerSurface
  ∷ narrativeGapSurface
  ∷ []

data SafetyAgencySeed : Set where
  breathSeed : SafetyAgencySeed
  orientingSeed : SafetyAgencySeed
  feltBoundarySeed : SafetyAgencySeed
  trustedWitnessSeed : SafetyAgencySeed
  pauseSeed : SafetyAgencySeed
  bodyLocationLabelSeed : SafetyAgencySeed
  permissionToStopSeed : SafetyAgencySeed
  nonForcedChoiceSeed : SafetyAgencySeed

canonicalSafetyAgencySeeds : List SafetyAgencySeed
canonicalSafetyAgencySeeds =
  breathSeed
  ∷ orientingSeed
  ∷ feltBoundarySeed
  ∷ trustedWitnessSeed
  ∷ pauseSeed
  ∷ bodyLocationLabelSeed
  ∷ permissionToStopSeed
  ∷ nonForcedChoiceSeed
  ∷ []

------------------------------------------------------------------------
-- Compiled inverse vocabulary.

data WorldChart : Set where
  oldThreatWorldChart : WorldChart
  currentWorldChart : WorldChart
  candidateNextWorldChart : WorldChart


data InverseChart : Set where
  oldCompiledWorldInverse : InverseChart
  currentCandidateWorldInverse : InverseChart


data InverseResidualStatus : Set where
  inverseStillLocal : InverseResidualStatus
  inverseNearSeam : InverseResidualStatus
  inverseFailsToGlue : InverseResidualStatus


data BodyScoreStage : Set where
  unmarkedBodyGroundStage : BodyScoreStage
  firstFeltMarkStage : BodyScoreStage
  selfWorldDyadStage : BodyScoreStage
  compiledInverseTriadStage : BodyScoreStage
  survivalCycleStage : BodyScoreStage
  decisionThresholdStage : BodyScoreStage
  oldInverseCurrentWorldTensionStage : BodyScoreStage
  maximumBoundaryPressureStage : BodyScoreStage
  failedGluingStage : BodyScoreStage
  localIntegrationReceiptStage : BodyScoreStage
  newSafetyConventionStage : BodyScoreStage
  manifoldChartGluingStage : BodyScoreStage

canonicalBodyScoreStages : List BodyScoreStage
canonicalBodyScoreStages =
  unmarkedBodyGroundStage
  ∷ firstFeltMarkStage
  ∷ selfWorldDyadStage
  ∷ compiledInverseTriadStage
  ∷ survivalCycleStage
  ∷ decisionThresholdStage
  ∷ oldInverseCurrentWorldTensionStage
  ∷ maximumBoundaryPressureStage
  ∷ failedGluingStage
  ∷ localIntegrationReceiptStage
  ∷ newSafetyConventionStage
  ∷ manifoldChartGluingStage
  ∷ []

------------------------------------------------------------------------
-- Body-state records.

record BodyStateCarrier : Set where
  constructor mkBodyStateCarrier
  field
    breathField : BodyStateFibre
    postureField : BodyStateFibre
    arousalField : BodyStateFibre
    affectField : BodyStateFibre
    sensoryField : BodyStateFibre
    memoryField : BodyStateFibre
    relationField : BodyStateFibre
    agencyField : BodyStateFibre

open BodyStateCarrier public

canonicalBodyStateCarrier : BodyStateCarrier
canonicalBodyStateCarrier =
  mkBodyStateCarrier
    breathFibre
    postureFibre
    arousalFibre
    affectFibre
    sensoryFibre
    memoryFibre
    relationFibre
    agencyFibre

record CompiledWorldInverse : Set where
  constructor mkCompiledWorldInverse
  field
    learnedWorldChart : WorldChart
    activeWorldChart : WorldChart
    inverseChart : InverseChart
    compiledOperatorLabel : String
    liveQuotientLabel : String
    compiledProductLabel : String
    residualStatus : InverseResidualStatus
    jPlusOneRequired : Bool

open CompiledWorldInverse public

canonicalCompiledWorldInverse : CompiledWorldInverse
canonicalCompiledWorldInverse =
  mkCompiledWorldInverse
    oldThreatWorldChart
    currentWorldChart
    oldCompiledWorldInverse
    "self / world"
    "expensive live quotient"
    "self * world^-1"
    inverseFailsToGlue
    true

record BodyScoreResidual : Set₁ where
  constructor mkBodyScoreResidual
  field
    observedSurface : ObservedBodySurface
    hiddenFibres : List BodyStateFibre
    bodyCarrier : BodyStateCarrier
    compiledInverse : CompiledWorldInverse
    residualLabel : String
    safetySeed : SafetyAgencySeed
    stageReading : BodyScoreStage
    authorityBundle : Authority.AuthorityNonPromotionBundle
    clinicalAuthorityIsFalse :
      Authority.authorityFlag Authority.clinicalAuthority authorityBundle ≡ false
    scientificAuthorityIsFalse :
      Authority.authorityFlag Authority.scientificAuthority authorityBundle ≡ false
    empiricalAuthorityIsFalse :
      Authority.authorityFlag Authority.empiricalAuthority authorityBundle ≡ false
    metaphysicalAuthorityIsFalse :
      Authority.authorityFlag Authority.metaphysicalAuthority authorityBundle ≡ false

open BodyScoreResidual public

bodyKeepsScoreAuthorityBundle : Authority.AuthorityNonPromotionBundle
bodyKeepsScoreAuthorityBundle =
  Authority.mkClosedAuthorityNonPromotionBundle
    "body-score candidate boundary: no clinical, scientific, empirical, or metaphysical promotion"

canonicalBodyScoreResidual : BodyScoreResidual
canonicalBodyScoreResidual =
  mkBodyScoreResidual
    narrativeGapSurface
    canonicalBodyStateFibres
    canonicalBodyStateCarrier
    canonicalCompiledWorldInverse
    "world_now * world_old^-1 fails to reduce to identity inside the current chart"
    permissionToStopSeed
    failedGluingStage
    bodyKeepsScoreAuthorityBundle
    (Authority.authorityFlagIsFalse Authority.clinicalAuthority bodyKeepsScoreAuthorityBundle)
    (Authority.authorityFlagIsFalse Authority.scientificAuthority bodyKeepsScoreAuthorityBundle)
    (Authority.authorityFlagIsFalse Authority.empiricalAuthority bodyKeepsScoreAuthorityBundle)
    (Authority.authorityFlagIsFalse Authority.metaphysicalAuthority bodyKeepsScoreAuthorityBundle)

------------------------------------------------------------------------
-- +1 identity/safety handle.

record BodyPlusOneIdentitySection : Set₁ where
  constructor mkBodyPlusOneIdentitySection
  field
    residualState : BodyScoreResidual
    plusOneSeed : SafetyAgencySeed
    selectedFibres : List BodyStateFibre
    candidateIdentityWitnessLabel : String
    nextChart : WorldChart
    noForcedDisclosure : Bool
    noForcedDisclosureIsTrue : noForcedDisclosure ≡ true
    revealsAllHiddenFibres : Bool
    revealsAllHiddenFibresIsFalse : revealsAllHiddenFibres ≡ false
    curesTrauma : Bool
    curesTraumaIsFalse : curesTrauma ≡ false
    clinicalPromotion : Bool
    clinicalPromotionIsFalse : clinicalPromotion ≡ false

open BodyPlusOneIdentitySection public

canonicalBodyPlusOneIdentitySection : BodyPlusOneIdentitySection
canonicalBodyPlusOneIdentitySection =
  mkBodyPlusOneIdentitySection
    canonicalBodyScoreResidual
    permissionToStopSeed
    (breathFibre ∷ agencyFibre ∷ relationFibre ∷ [])
    "safe +1 identity/agency handle over selected body-state fibres"
    candidateNextWorldChart
    true
    refl
    false
    refl
    false
    refl
    false
    refl

------------------------------------------------------------------------
-- RSA analogy receipt.

record BodyKeepsScoreRSAAnalogyReceipt : Set₁ where
  constructor mkBodyKeepsScoreRSAAnalogyReceipt
  field
    rsaPlusOneReference :
      RSAPlusOne.RSAPlusOneIdentitySectionReceipt
    bodyResidual :
      BodyScoreResidual
    bodyPlusOneSection :
      BodyPlusOneIdentitySection
    rsaAnalogyLabel :
      String
    publicSurfaceDoesNotRevealHiddenCharts :
      Bool
    publicSurfaceDoesNotRevealHiddenChartsIsTrue :
      publicSurfaceDoesNotRevealHiddenCharts ≡ true
    plusOneDoesNotFactorOrCure :
      Bool
    plusOneDoesNotFactorOrCureIsTrue :
      plusOneDoesNotFactorOrCure ≡ true
    candidateOnly :
      Bool
    candidateOnlyIsTrue :
      candidateOnly ≡ true

open BodyKeepsScoreRSAAnalogyReceipt public

canonicalBodyKeepsScoreRSAAnalogyReceipt : BodyKeepsScoreRSAAnalogyReceipt
canonicalBodyKeepsScoreRSAAnalogyReceipt =
  mkBodyKeepsScoreRSAAnalogyReceipt
    RSAPlusOne.rsaPlusOneIdentitySectionReceipt
    canonicalBodyScoreResidual
    canonicalBodyPlusOneIdentitySection
    "RSA hides factor charts behind N; body-score reading hides body-state charts behind public symptom/narrative surfaces"
    true
    refl
    true
    refl
    true
    refl

------------------------------------------------------------------------
-- Meditation/Qi bridge receipt.

record BodyKeepsScoreQiBridgeReceipt : Set₁ where
  constructor mkBodyKeepsScoreQiBridgeReceipt
  field
    meditationStateReference :
      MeditationQi.MeditationState
    bodyResidual :
      BodyScoreResidual
    plusOneSection :
      BodyPlusOneIdentitySection
    qiCarrierReadingLabel :
      String
    taoNonForcingReadingLabel :
      String
    practiceInstruction :
      Bool
    practiceInstructionIsFalse :
      practiceInstruction ≡ false
    clinicalInstruction :
      Bool
    clinicalInstructionIsFalse :
      clinicalInstruction ≡ false

open BodyKeepsScoreQiBridgeReceipt public

canonicalBodyKeepsScoreQiBridgeReceipt : BodyKeepsScoreQiBridgeReceipt
canonicalBodyKeepsScoreQiBridgeReceipt =
  mkBodyKeepsScoreQiBridgeReceipt
    MeditationQi.canonicalMeditationState
    canonicalBodyScoreResidual
    canonicalBodyPlusOneIdentitySection
    "Qi/body carrier reading: breath, posture, arousal, affect, memory, relation, and agency fibres"
    "Tao/non-forcing reading: do not force disclosure; add a small safe +1 handle for re-charting"
    false
    refl
    false
    refl

------------------------------------------------------------------------
-- Master receipt.

record BodyKeepsScoreCandidateBoundary : Set₁ where
  constructor mkBodyKeepsScoreCandidateBoundary
  field
    residual :
      BodyScoreResidual
    plusOneIdentitySection :
      BodyPlusOneIdentitySection
    rsaAnalogy :
      BodyKeepsScoreRSAAnalogyReceipt
    qiBridge :
      BodyKeepsScoreQiBridgeReceipt
    nonPromotionBundle :
      Authority.AuthorityNonPromotionBundle
    noDiagnosis :
      Bool
    noDiagnosisIsFalse :
      noDiagnosis ≡ false
    noTreatmentPrescription :
      Bool
    noTreatmentPrescriptionIsFalse :
      noTreatmentPrescription ≡ false
    noClinicalAuthority :
      Authority.authorityFlag Authority.clinicalAuthority nonPromotionBundle ≡ false
    noScientificAuthority :
      Authority.authorityFlag Authority.scientificAuthority nonPromotionBundle ≡ false
    noMetaphysicalAuthority :
      Authority.authorityFlag Authority.metaphysicalAuthority nonPromotionBundle ≡ false

open BodyKeepsScoreCandidateBoundary public

canonicalBodyKeepsScoreCandidateBoundary : BodyKeepsScoreCandidateBoundary
canonicalBodyKeepsScoreCandidateBoundary =
  mkBodyKeepsScoreCandidateBoundary
    canonicalBodyScoreResidual
    canonicalBodyPlusOneIdentitySection
    canonicalBodyKeepsScoreRSAAnalogyReceipt
    canonicalBodyKeepsScoreQiBridgeReceipt
    bodyKeepsScoreAuthorityBundle
    false
    refl
    false
    refl
    (Authority.authorityFlagIsFalse Authority.clinicalAuthority bodyKeepsScoreAuthorityBundle)
    (Authority.authorityFlagIsFalse Authority.scientificAuthority bodyKeepsScoreAuthorityBundle)
    (Authority.authorityFlagIsFalse Authority.metaphysicalAuthority bodyKeepsScoreAuthorityBundle)

------------------------------------------------------------------------
-- Boundary theorem-style accessors.

bodyScoreNoDiagnosis :
  noDiagnosis canonicalBodyKeepsScoreCandidateBoundary ≡ false
bodyScoreNoDiagnosis = refl

bodyScoreNoTreatmentPrescription :
  noTreatmentPrescription canonicalBodyKeepsScoreCandidateBoundary ≡ false
bodyScoreNoTreatmentPrescription = refl

bodyPlusOneNoForcedDisclosure :
  noForcedDisclosure canonicalBodyPlusOneIdentitySection ≡ true
bodyPlusOneNoForcedDisclosure = refl

bodyPlusOneDoesNotRevealAllHiddenFibres :
  revealsAllHiddenFibres canonicalBodyPlusOneIdentitySection ≡ false
bodyPlusOneDoesNotRevealAllHiddenFibres = refl

bodyPlusOneDoesNotCure :
  curesTrauma canonicalBodyPlusOneIdentitySection ≡ false
bodyPlusOneDoesNotCure = refl

bodyScoreClinicalAuthorityBlocked :
  Authority.authorityFlag Authority.clinicalAuthority bodyKeepsScoreAuthorityBundle ≡ false
bodyScoreClinicalAuthorityBlocked =
  Authority.authorityFlagIsFalse Authority.clinicalAuthority bodyKeepsScoreAuthorityBundle
