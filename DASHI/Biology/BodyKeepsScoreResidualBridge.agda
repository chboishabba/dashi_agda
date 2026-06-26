module DASHI.Biology.BodyKeepsScoreResidualBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.CandidateOnlyCore as CandidateOnly

------------------------------------------------------------------------
-- Body Keeps the Score as a body-state residual bridge.
--
-- This module treats the phrase as a candidate-only residual vocabulary:
-- it tracks breath, posture, arousal, sensory, memory, relation, agency,
-- and a plus-one safety seed identity handle as body-state residual fibres.
-- It does not promote diagnosis, treatment, cure, forced disclosure, or
-- clinical authority.

data BodyKeepsScoreResidualFibre : Set where
  breathResidualFibre :
    BodyKeepsScoreResidualFibre

  postureResidualFibre :
    BodyKeepsScoreResidualFibre

  arousalResidualFibre :
    BodyKeepsScoreResidualFibre

  sensoryResidualFibre :
    BodyKeepsScoreResidualFibre

  memoryResidualFibre :
    BodyKeepsScoreResidualFibre

  relationResidualFibre :
    BodyKeepsScoreResidualFibre

  agencyResidualFibre :
    BodyKeepsScoreResidualFibre

  plusOneSafetySeedIdentityHandleFibre :
    BodyKeepsScoreResidualFibre

canonicalBodyKeepsScoreResidualFibres :
  List BodyKeepsScoreResidualFibre
canonicalBodyKeepsScoreResidualFibres =
  breathResidualFibre
  ∷ postureResidualFibre
  ∷ arousalResidualFibre
  ∷ sensoryResidualFibre
  ∷ memoryResidualFibre
  ∷ relationResidualFibre
  ∷ agencyResidualFibre
  ∷ plusOneSafetySeedIdentityHandleFibre
  ∷ []

bodyKeepsScoreResidualFibreName :
  BodyKeepsScoreResidualFibre →
  String
bodyKeepsScoreResidualFibreName breathResidualFibre =
  "breath residual fibre"
bodyKeepsScoreResidualFibreName postureResidualFibre =
  "posture residual fibre"
bodyKeepsScoreResidualFibreName arousalResidualFibre =
  "arousal residual fibre"
bodyKeepsScoreResidualFibreName sensoryResidualFibre =
  "sensory residual fibre"
bodyKeepsScoreResidualFibreName memoryResidualFibre =
  "memory residual fibre"
bodyKeepsScoreResidualFibreName relationResidualFibre =
  "relation residual fibre"
bodyKeepsScoreResidualFibreName agencyResidualFibre =
  "agency residual fibre"
bodyKeepsScoreResidualFibreName
  plusOneSafetySeedIdentityHandleFibre =
  "plus-one safety seed identity handle"

bodyKeepsScoreResidualFibreStatement :
  BodyKeepsScoreResidualFibre →
  String
bodyKeepsScoreResidualFibreStatement breathResidualFibre =
  "Breath is tracked as a candidate body-state residual fibre."
bodyKeepsScoreResidualFibreStatement postureResidualFibre =
  "Posture is tracked as a candidate body-state residual fibre."
bodyKeepsScoreResidualFibreStatement arousalResidualFibre =
  "Arousal is tracked as a candidate body-state residual fibre."
bodyKeepsScoreResidualFibreStatement sensoryResidualFibre =
  "Sensory load is tracked as a candidate body-state residual fibre."
bodyKeepsScoreResidualFibreStatement memoryResidualFibre =
  "Memory trace is tracked as a candidate body-state residual fibre."
bodyKeepsScoreResidualFibreStatement relationResidualFibre =
  "Relation is tracked as a candidate body-state residual fibre."
bodyKeepsScoreResidualFibreStatement agencyResidualFibre =
  "Agency is tracked as a candidate body-state residual fibre."
bodyKeepsScoreResidualFibreStatement
  plusOneSafetySeedIdentityHandleFibre =
  "The plus-one safety seed is tracked as a candidate identity handle."

bodyKeepsScoreResidualFibreRemainingGap :
  BodyKeepsScoreResidualFibre →
  String
bodyKeepsScoreResidualFibreRemainingGap breathResidualFibre =
  "Breath does not become diagnosis, treatment, cure, or clinical authority."
bodyKeepsScoreResidualFibreRemainingGap postureResidualFibre =
  "Posture does not become diagnosis, treatment, cure, or clinical authority."
bodyKeepsScoreResidualFibreRemainingGap arousalResidualFibre =
  "Arousal does not become diagnosis, treatment, cure, or clinical authority."
bodyKeepsScoreResidualFibreRemainingGap sensoryResidualFibre =
  "Sensory load does not become diagnosis, treatment, cure, or clinical authority."
bodyKeepsScoreResidualFibreRemainingGap memoryResidualFibre =
  "Memory trace does not become diagnosis, treatment, cure, or clinical authority."
bodyKeepsScoreResidualFibreRemainingGap relationResidualFibre =
  "Relation does not become diagnosis, treatment, cure, or clinical authority."
bodyKeepsScoreResidualFibreRemainingGap agencyResidualFibre =
  "Agency does not become diagnosis, treatment, cure, or clinical authority."
bodyKeepsScoreResidualFibreRemainingGap
  plusOneSafetySeedIdentityHandleFibre =
  "The safety seed stays candidate-only and does not trigger forced disclosure."

------------------------------------------------------------------------
-- Governance guards.

record BodyKeepsScoreGovernance : Set where
  field
    noDiagnosisClaim :
      Bool

    noDiagnosisClaimIsFalse :
      noDiagnosisClaim ≡ false

    noTreatmentClaim :
      Bool

    noTreatmentClaimIsFalse :
      noTreatmentClaim ≡ false

    noCureClaim :
      Bool

    noCureClaimIsFalse :
      noCureClaim ≡ false

    noForcedDisclosureClaim :
      Bool

    noForcedDisclosureClaimIsFalse :
      noForcedDisclosureClaim ≡ false

    noClinicalAuthorityClaim :
      Bool

    noClinicalAuthorityClaimIsFalse :
      noClinicalAuthorityClaim ≡ false

    governanceReading :
      String

open BodyKeepsScoreGovernance public

canonicalBodyKeepsScoreGovernance : BodyKeepsScoreGovernance
canonicalBodyKeepsScoreGovernance =
  record
    { noDiagnosisClaim = false
    ; noDiagnosisClaimIsFalse = refl
    ; noTreatmentClaim = false
    ; noTreatmentClaimIsFalse = refl
    ; noCureClaim = false
    ; noCureClaimIsFalse = refl
    ; noForcedDisclosureClaim = false
    ; noForcedDisclosureClaimIsFalse = refl
    ; noClinicalAuthorityClaim = false
    ; noClinicalAuthorityClaimIsFalse = refl
    ; governanceReading =
        "Body-state residual fibres remain candidate-only and do not carry diagnosis, treatment, cure, forced disclosure, or clinical authority."
    }

canonicalNoDiagnosisClaimIsFalse :
  noDiagnosisClaim canonicalBodyKeepsScoreGovernance ≡ false
canonicalNoDiagnosisClaimIsFalse =
  noDiagnosisClaimIsFalse canonicalBodyKeepsScoreGovernance

canonicalNoTreatmentClaimIsFalse :
  noTreatmentClaim canonicalBodyKeepsScoreGovernance ≡ false
canonicalNoTreatmentClaimIsFalse =
  noTreatmentClaimIsFalse canonicalBodyKeepsScoreGovernance

canonicalNoCureClaimIsFalse :
  noCureClaim canonicalBodyKeepsScoreGovernance ≡ false
canonicalNoCureClaimIsFalse =
  noCureClaimIsFalse canonicalBodyKeepsScoreGovernance

canonicalNoForcedDisclosureClaimIsFalse :
  noForcedDisclosureClaim canonicalBodyKeepsScoreGovernance ≡ false
canonicalNoForcedDisclosureClaimIsFalse =
  noForcedDisclosureClaimIsFalse canonicalBodyKeepsScoreGovernance

canonicalNoClinicalAuthorityClaimIsFalse :
  noClinicalAuthorityClaim canonicalBodyKeepsScoreGovernance ≡ false
canonicalNoClinicalAuthorityClaimIsFalse =
  noClinicalAuthorityClaimIsFalse canonicalBodyKeepsScoreGovernance

------------------------------------------------------------------------
-- Candidate-only bridge rows.

bodyKeepsScoreBridgeOwner : String
bodyKeepsScoreBridgeOwner =
  "DASHI.Biology.BodyKeepsScoreResidualBridge"

mkBodyKeepsScoreResidualRow :
  String →
  String →
  BodyKeepsScoreResidualFibre →
  CandidateOnly.CandidateOnlyRow
mkBodyKeepsScoreResidualRow label surface fibre =
  CandidateOnly.mkCandidateOnlyRow
    label
    bodyKeepsScoreBridgeOwner
    surface
    CandidateOnly.bridgeCandidateKind
    CandidateOnly.bridgeCandidateOnlyStatus
    (bodyKeepsScoreResidualFibreStatement fibre)
    (bodyKeepsScoreResidualFibreRemainingGap fibre)

canonicalBreathResidualCandidateRow :
  CandidateOnly.CandidateOnlyRow
canonicalBreathResidualCandidateRow =
  mkBodyKeepsScoreResidualRow
    (bodyKeepsScoreResidualFibreName breathResidualFibre)
    "breathResidualFibre"
    breathResidualFibre

canonicalPostureResidualCandidateRow :
  CandidateOnly.CandidateOnlyRow
canonicalPostureResidualCandidateRow =
  mkBodyKeepsScoreResidualRow
    (bodyKeepsScoreResidualFibreName postureResidualFibre)
    "postureResidualFibre"
    postureResidualFibre

canonicalArousalResidualCandidateRow :
  CandidateOnly.CandidateOnlyRow
canonicalArousalResidualCandidateRow =
  mkBodyKeepsScoreResidualRow
    (bodyKeepsScoreResidualFibreName arousalResidualFibre)
    "arousalResidualFibre"
    arousalResidualFibre

canonicalSensoryResidualCandidateRow :
  CandidateOnly.CandidateOnlyRow
canonicalSensoryResidualCandidateRow =
  mkBodyKeepsScoreResidualRow
    (bodyKeepsScoreResidualFibreName sensoryResidualFibre)
    "sensoryResidualFibre"
    sensoryResidualFibre

canonicalMemoryResidualCandidateRow :
  CandidateOnly.CandidateOnlyRow
canonicalMemoryResidualCandidateRow =
  mkBodyKeepsScoreResidualRow
    (bodyKeepsScoreResidualFibreName memoryResidualFibre)
    "memoryResidualFibre"
    memoryResidualFibre

canonicalRelationResidualCandidateRow :
  CandidateOnly.CandidateOnlyRow
canonicalRelationResidualCandidateRow =
  mkBodyKeepsScoreResidualRow
    (bodyKeepsScoreResidualFibreName relationResidualFibre)
    "relationResidualFibre"
    relationResidualFibre

canonicalAgencyResidualCandidateRow :
  CandidateOnly.CandidateOnlyRow
canonicalAgencyResidualCandidateRow =
  mkBodyKeepsScoreResidualRow
    (bodyKeepsScoreResidualFibreName agencyResidualFibre)
    "agencyResidualFibre"
    agencyResidualFibre

canonicalPlusOneSafetySeedIdentityHandleCandidateRow :
  CandidateOnly.CandidateOnlyRow
canonicalPlusOneSafetySeedIdentityHandleCandidateRow =
  mkBodyKeepsScoreResidualRow
    (bodyKeepsScoreResidualFibreName
      plusOneSafetySeedIdentityHandleFibre)
    "plusOneSafetySeedIdentityHandleFibre"
    plusOneSafetySeedIdentityHandleFibre

canonicalBodyKeepsScoreBridgeCoreRow :
  CandidateOnly.CandidateOnlyRow
canonicalBodyKeepsScoreBridgeCoreRow =
  CandidateOnly.mkCandidateOnlyRow
    "body-keeps-score residual bridge"
    bodyKeepsScoreBridgeOwner
    "BodyKeepsScoreResidualBridge"
    CandidateOnly.bridgeCandidateKind
    CandidateOnly.bridgeCandidateOnlyStatus
    "A candidate-only bridge carries residual body-state fibres without diagnosis, treatment, cure, forced disclosure, or clinical authority."
    "The bridge remains candidate-only and does not collapse residual fibres into a clinical reading."

canonicalBreathResidualCandidateReceipt :
  CandidateOnly.CandidateOnlyReceipt
    canonicalBreathResidualCandidateRow
canonicalBreathResidualCandidateReceipt =
  CandidateOnly.canonicalCandidateOnlyReceipt
    canonicalBreathResidualCandidateRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalPostureResidualCandidateReceipt :
  CandidateOnly.CandidateOnlyReceipt
    canonicalPostureResidualCandidateRow
canonicalPostureResidualCandidateReceipt =
  CandidateOnly.canonicalCandidateOnlyReceipt
    canonicalPostureResidualCandidateRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalArousalResidualCandidateReceipt :
  CandidateOnly.CandidateOnlyReceipt
    canonicalArousalResidualCandidateRow
canonicalArousalResidualCandidateReceipt =
  CandidateOnly.canonicalCandidateOnlyReceipt
    canonicalArousalResidualCandidateRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalSensoryResidualCandidateReceipt :
  CandidateOnly.CandidateOnlyReceipt
    canonicalSensoryResidualCandidateRow
canonicalSensoryResidualCandidateReceipt =
  CandidateOnly.canonicalCandidateOnlyReceipt
    canonicalSensoryResidualCandidateRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalMemoryResidualCandidateReceipt :
  CandidateOnly.CandidateOnlyReceipt
    canonicalMemoryResidualCandidateRow
canonicalMemoryResidualCandidateReceipt =
  CandidateOnly.canonicalCandidateOnlyReceipt
    canonicalMemoryResidualCandidateRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalRelationResidualCandidateReceipt :
  CandidateOnly.CandidateOnlyReceipt
    canonicalRelationResidualCandidateRow
canonicalRelationResidualCandidateReceipt =
  CandidateOnly.canonicalCandidateOnlyReceipt
    canonicalRelationResidualCandidateRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalAgencyResidualCandidateReceipt :
  CandidateOnly.CandidateOnlyReceipt
    canonicalAgencyResidualCandidateRow
canonicalAgencyResidualCandidateReceipt =
  CandidateOnly.canonicalCandidateOnlyReceipt
    canonicalAgencyResidualCandidateRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalPlusOneSafetySeedIdentityHandleCandidateReceipt :
  CandidateOnly.CandidateOnlyReceipt
    canonicalPlusOneSafetySeedIdentityHandleCandidateRow
canonicalPlusOneSafetySeedIdentityHandleCandidateReceipt =
  CandidateOnly.canonicalCandidateOnlyReceipt
    canonicalPlusOneSafetySeedIdentityHandleCandidateRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalBodyKeepsScoreBridgeCoreReceipt :
  CandidateOnly.CandidateOnlyReceipt
    canonicalBodyKeepsScoreBridgeCoreRow
canonicalBodyKeepsScoreBridgeCoreReceipt =
  CandidateOnly.canonicalCandidateOnlyReceipt
    canonicalBodyKeepsScoreBridgeCoreRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalBodyKeepsScoreResidualRows :
  List CandidateOnly.CandidateOnlyRow
canonicalBodyKeepsScoreResidualRows =
  canonicalBreathResidualCandidateRow
  ∷ canonicalPostureResidualCandidateRow
  ∷ canonicalArousalResidualCandidateRow
  ∷ canonicalSensoryResidualCandidateRow
  ∷ canonicalMemoryResidualCandidateRow
  ∷ canonicalRelationResidualCandidateRow
  ∷ canonicalAgencyResidualCandidateRow
  ∷ canonicalPlusOneSafetySeedIdentityHandleCandidateRow
  ∷ []

canonicalBodyKeepsScoreResidualFibresAreCanonical :
  canonicalBodyKeepsScoreResidualFibres ≡
  canonicalBodyKeepsScoreResidualFibres
canonicalBodyKeepsScoreResidualFibresAreCanonical =
  refl

canonicalBodyKeepsScoreResidualRowsAreCanonical :
  canonicalBodyKeepsScoreResidualRows ≡
  canonicalBodyKeepsScoreResidualRows
canonicalBodyKeepsScoreResidualRowsAreCanonical =
  refl

------------------------------------------------------------------------
-- Bridge record.

record BodyKeepsScoreResidualBridge : Set₁ where
  field
    bridgeReading :
      String

    residualFibres :
      List BodyKeepsScoreResidualFibre

    residualFibresAreCanonical :
      residualFibres ≡ canonicalBodyKeepsScoreResidualFibres

    bridgeCoreRow :
      CandidateOnly.CandidateOnlyRow

    bridgeCoreRowIsCanonical :
      bridgeCoreRow ≡ canonicalBodyKeepsScoreBridgeCoreRow

    bridgeCoreReceipt :
      CandidateOnly.CandidateOnlyReceipt
        canonicalBodyKeepsScoreBridgeCoreRow

    bridgeCoreReceiptIsCanonical :
      bridgeCoreReceipt ≡ canonicalBodyKeepsScoreBridgeCoreReceipt

    breathResidualRow :
      CandidateOnly.CandidateOnlyRow

    breathResidualRowIsCanonical :
      breathResidualRow ≡ canonicalBreathResidualCandidateRow

    breathResidualReceipt :
      CandidateOnly.CandidateOnlyReceipt
        canonicalBreathResidualCandidateRow

    breathResidualReceiptIsCanonical :
      breathResidualReceipt ≡ canonicalBreathResidualCandidateReceipt

    postureResidualRow :
      CandidateOnly.CandidateOnlyRow

    postureResidualRowIsCanonical :
      postureResidualRow ≡ canonicalPostureResidualCandidateRow

    postureResidualReceipt :
      CandidateOnly.CandidateOnlyReceipt
        canonicalPostureResidualCandidateRow

    postureResidualReceiptIsCanonical :
      postureResidualReceipt ≡ canonicalPostureResidualCandidateReceipt

    arousalResidualRow :
      CandidateOnly.CandidateOnlyRow

    arousalResidualRowIsCanonical :
      arousalResidualRow ≡ canonicalArousalResidualCandidateRow

    arousalResidualReceipt :
      CandidateOnly.CandidateOnlyReceipt
        canonicalArousalResidualCandidateRow

    arousalResidualReceiptIsCanonical :
      arousalResidualReceipt ≡ canonicalArousalResidualCandidateReceipt

    sensoryResidualRow :
      CandidateOnly.CandidateOnlyRow

    sensoryResidualRowIsCanonical :
      sensoryResidualRow ≡ canonicalSensoryResidualCandidateRow

    sensoryResidualReceipt :
      CandidateOnly.CandidateOnlyReceipt
        canonicalSensoryResidualCandidateRow

    sensoryResidualReceiptIsCanonical :
      sensoryResidualReceipt ≡ canonicalSensoryResidualCandidateReceipt

    memoryResidualRow :
      CandidateOnly.CandidateOnlyRow

    memoryResidualRowIsCanonical :
      memoryResidualRow ≡ canonicalMemoryResidualCandidateRow

    memoryResidualReceipt :
      CandidateOnly.CandidateOnlyReceipt
        canonicalMemoryResidualCandidateRow

    memoryResidualReceiptIsCanonical :
      memoryResidualReceipt ≡ canonicalMemoryResidualCandidateReceipt

    relationResidualRow :
      CandidateOnly.CandidateOnlyRow

    relationResidualRowIsCanonical :
      relationResidualRow ≡ canonicalRelationResidualCandidateRow

    relationResidualReceipt :
      CandidateOnly.CandidateOnlyReceipt
        canonicalRelationResidualCandidateRow

    relationResidualReceiptIsCanonical :
      relationResidualReceipt ≡ canonicalRelationResidualCandidateReceipt

    agencyResidualRow :
      CandidateOnly.CandidateOnlyRow

    agencyResidualRowIsCanonical :
      agencyResidualRow ≡ canonicalAgencyResidualCandidateRow

    agencyResidualReceipt :
      CandidateOnly.CandidateOnlyReceipt
        canonicalAgencyResidualCandidateRow

    agencyResidualReceiptIsCanonical :
      agencyResidualReceipt ≡ canonicalAgencyResidualCandidateReceipt

    plusOneSafetySeedIdentityHandleRow :
      CandidateOnly.CandidateOnlyRow

    plusOneSafetySeedIdentityHandleRowIsCanonical :
      plusOneSafetySeedIdentityHandleRow ≡
      canonicalPlusOneSafetySeedIdentityHandleCandidateRow

    plusOneSafetySeedIdentityHandleReceipt :
      CandidateOnly.CandidateOnlyReceipt
        canonicalPlusOneSafetySeedIdentityHandleCandidateRow

    plusOneSafetySeedIdentityHandleReceiptIsCanonical :
      plusOneSafetySeedIdentityHandleReceipt ≡
      canonicalPlusOneSafetySeedIdentityHandleCandidateReceipt

    residualRows :
      List CandidateOnly.CandidateOnlyRow

    residualRowsAreCanonical :
      residualRows ≡ canonicalBodyKeepsScoreResidualRows

    governance :
      BodyKeepsScoreGovernance

    governanceIsCanonical :
      governance ≡ canonicalBodyKeepsScoreGovernance

open BodyKeepsScoreResidualBridge public

canonicalBodyKeepsScoreResidualBridge :
  BodyKeepsScoreResidualBridge
canonicalBodyKeepsScoreResidualBridge =
  record
    { bridgeReading =
        "Body Keeps the Score is represented here as a candidate-only residual bridge over breath, posture, arousal, sensory, memory, relation, agency, and a plus-one safety seed identity handle."
    ; residualFibres =
        canonicalBodyKeepsScoreResidualFibres
    ; residualFibresAreCanonical =
        refl
    ; bridgeCoreRow =
        canonicalBodyKeepsScoreBridgeCoreRow
    ; bridgeCoreRowIsCanonical =
        refl
    ; bridgeCoreReceipt =
        canonicalBodyKeepsScoreBridgeCoreReceipt
    ; bridgeCoreReceiptIsCanonical =
        refl
    ; breathResidualRow =
        canonicalBreathResidualCandidateRow
    ; breathResidualRowIsCanonical =
        refl
    ; breathResidualReceipt =
        canonicalBreathResidualCandidateReceipt
    ; breathResidualReceiptIsCanonical =
        refl
    ; postureResidualRow =
        canonicalPostureResidualCandidateRow
    ; postureResidualRowIsCanonical =
        refl
    ; postureResidualReceipt =
        canonicalPostureResidualCandidateReceipt
    ; postureResidualReceiptIsCanonical =
        refl
    ; arousalResidualRow =
        canonicalArousalResidualCandidateRow
    ; arousalResidualRowIsCanonical =
        refl
    ; arousalResidualReceipt =
        canonicalArousalResidualCandidateReceipt
    ; arousalResidualReceiptIsCanonical =
        refl
    ; sensoryResidualRow =
        canonicalSensoryResidualCandidateRow
    ; sensoryResidualRowIsCanonical =
        refl
    ; sensoryResidualReceipt =
        canonicalSensoryResidualCandidateReceipt
    ; sensoryResidualReceiptIsCanonical =
        refl
    ; memoryResidualRow =
        canonicalMemoryResidualCandidateRow
    ; memoryResidualRowIsCanonical =
        refl
    ; memoryResidualReceipt =
        canonicalMemoryResidualCandidateReceipt
    ; memoryResidualReceiptIsCanonical =
        refl
    ; relationResidualRow =
        canonicalRelationResidualCandidateRow
    ; relationResidualRowIsCanonical =
        refl
    ; relationResidualReceipt =
        canonicalRelationResidualCandidateReceipt
    ; relationResidualReceiptIsCanonical =
        refl
    ; agencyResidualRow =
        canonicalAgencyResidualCandidateRow
    ; agencyResidualRowIsCanonical =
        refl
    ; agencyResidualReceipt =
        canonicalAgencyResidualCandidateReceipt
    ; agencyResidualReceiptIsCanonical =
        refl
    ; plusOneSafetySeedIdentityHandleRow =
        canonicalPlusOneSafetySeedIdentityHandleCandidateRow
    ; plusOneSafetySeedIdentityHandleRowIsCanonical =
        refl
    ; plusOneSafetySeedIdentityHandleReceipt =
        canonicalPlusOneSafetySeedIdentityHandleCandidateReceipt
    ; plusOneSafetySeedIdentityHandleReceiptIsCanonical =
        refl
    ; residualRows =
        canonicalBodyKeepsScoreResidualRows
    ; residualRowsAreCanonical =
        refl
    ; governance =
        canonicalBodyKeepsScoreGovernance
    ; governanceIsCanonical =
        refl
    }

canonicalBodyKeepsScoreResidualBridgeIsCandidateOnly :
  CandidateOnly.candidateOnly
    (bridgeCoreRow canonicalBodyKeepsScoreResidualBridge) ≡ true
canonicalBodyKeepsScoreResidualBridgeIsCandidateOnly =
  CandidateOnly.candidateOnlyIsTrue
    (bridgeCoreReceipt canonicalBodyKeepsScoreResidualBridge)

canonicalBodyKeepsScoreResidualBridgeIsNotPromoted :
  CandidateOnly.promoted
    (bridgeCoreRow canonicalBodyKeepsScoreResidualBridge) ≡ false
canonicalBodyKeepsScoreResidualBridgeIsNotPromoted =
  CandidateOnly.candidatePromotedIsFalse
    (bridgeCoreReceipt canonicalBodyKeepsScoreResidualBridge)
