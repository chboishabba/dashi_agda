module DASHI.Physics.Closure.GravitationalAnomalyCancellationReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Integer.Base using (ℤ; +_; -[1+_]; 0ℤ; _+_)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.AnomalyCancellationVerificationReceipt as Anomaly
import DASHI.Physics.Closure.U1YChargeAssignmentTableReceipt as U1YTable
import DASHI.Physics.QFT.HyperchargeNormalisationAnomalyReceipt as HAnomaly

------------------------------------------------------------------------
-- Gravitational-U(1)_Y anomaly cancellation.
--
-- Per generation, in the same all-left-handed convention:
--
--   6*(+1/6) + 3*(-2/3) + 3*(+1/3)
--   + 2*(-1/2) + 1*(+1) + 1*0
--
-- Numerator over 6: 6 - 12 + 6 - 6 + 6 + 0 = 0.
--
-- The right-handed neutrino / nu^c has Y=0.  It is included in the
-- carrier's 48-Weyl-state count, but it is not numerically required for
-- the hypercharge gravitational anomaly cancellation.

gravitationalU1PerGenerationNumeratorOver6 :
  ℤ
gravitationalU1PerGenerationNumeratorOver6 =
  + 6
  + -[1+ 11 ]
  + + 6
  + -[1+ 5 ]
  + + 6
  + + 0

gravitationalU1PerGenerationNumeratorIsZero :
  gravitationalU1PerGenerationNumeratorOver6 ≡ 0ℤ
gravitationalU1PerGenerationNumeratorIsZero =
  refl

gravitationalVerificationStatement :
  String
gravitationalVerificationStatement =
  "gravitational-U(1)_Y per generation, denominator 6: 6 - 12 + 6 - 6 + 6 + 0 = 0"

nuRRoleStatement :
  String
nuRRoleStatement =
  "nu_R / nu^c has Y=0; it is included for the 48-Weyl carrier count, not because it is numerically needed in the hypercharge anomaly sum"

record GravitationalAnomalyCancellationReceipt : Setω where
  field
    chargeTableReceipt :
      U1YTable.U1YChargeAssignmentTableReceipt

    chargeTableHas48States :
      U1YTable.totalWeylCount chargeTableReceipt ≡ 48

    anomalyReceipt :
      Anomaly.AnomalyCancellationVerificationReceipt

    cubicAndMixedAnomalyReceiptPromotesSM :
      Anomaly.exactStandardModelPromoted anomalyReceipt ≡ false

    hyperchargeAuthorityReceipt :
      HAnomaly.HyperchargeNormalisationAnomalyReceipt

    authorityGravitationalNumeratorZero :
      HAnomaly.gravitationalNumerator hyperchargeAuthorityReceipt
      ≡
      0ℤ

    gravitationalNumeratorOver6 :
      ℤ

    gravitationalNumeratorOver6IsStandard :
      gravitationalNumeratorOver6
      ≡
      gravitationalU1PerGenerationNumeratorOver6

    gravitationalNumeratorOver6IsZero :
      gravitationalNumeratorOver6 ≡ 0ℤ

    gravitationalAnomalyCancels :
      Bool

    gravitationalAnomalyCancelsIsTrue :
      gravitationalAnomalyCancels ≡ true

    nuRHasZeroHypercharge :
      U1YTable.physicalSignedSixths U1YTable.nuR ≡ + 0

    nuRIncludedFor48Count :
      Bool

    nuRIncludedFor48CountIsTrue :
      nuRIncludedFor48Count ≡ true

    nuRNeededNumericallyForHyperchargeSum :
      Bool

    nuRNeededNumericallyForHyperchargeSumIsFalse :
      nuRNeededNumericallyForHyperchargeSum ≡ false

    gravitationalStatement :
      String

    gravitationalStatementIsCanonical :
      gravitationalStatement ≡ gravitationalVerificationStatement

    nuRStatement :
      String

    nuRStatementIsCanonical :
      nuRStatement ≡ nuRRoleStatement

    exactStandardModelPromoted :
      Bool

    exactStandardModelPromotedIsFalse :
      exactStandardModelPromoted ≡ false

    inheritedCandidateStatus :
      Bool

    inheritedCandidateStatusIsTrue :
      inheritedCandidateStatus ≡ true

    gDHREqualsGSM :
      Bool

    gDHREqualsGSMIsFalse :
      gDHREqualsGSM ≡ false

    anomalyCancellationInherited :
      Bool

    anomalyCancellationInheritedIsTrue :
      anomalyCancellationInherited ≡ true

    carrierSMHyperchargeMatch :
      Bool

    carrierSMHyperchargeMatchIsTrue :
      carrierSMHyperchargeMatch ≡ true

    exactDHRPromoted :
      Bool

    exactDHRPromotedIsFalse :
      exactDHRPromoted ≡ false

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    auditTrail :
      List String

open GravitationalAnomalyCancellationReceipt public

canonicalGravitationalAnomalyCancellationReceipt :
  GravitationalAnomalyCancellationReceipt
canonicalGravitationalAnomalyCancellationReceipt =
  record
    { chargeTableReceipt =
        U1YTable.canonicalU1YChargeAssignmentTableReceipt
    ; chargeTableHas48States =
        refl
    ; anomalyReceipt =
        Anomaly.canonicalAnomalyCancellationVerificationReceipt
    ; cubicAndMixedAnomalyReceiptPromotesSM =
        refl
    ; hyperchargeAuthorityReceipt =
        HAnomaly.canonicalHyperchargeNormalisationAnomalyReceipt
    ; authorityGravitationalNumeratorZero =
        refl
    ; gravitationalNumeratorOver6 =
        gravitationalU1PerGenerationNumeratorOver6
    ; gravitationalNumeratorOver6IsStandard =
        refl
    ; gravitationalNumeratorOver6IsZero =
        refl
    ; gravitationalAnomalyCancels =
        true
    ; gravitationalAnomalyCancelsIsTrue =
        refl
    ; nuRHasZeroHypercharge =
        refl
    ; nuRIncludedFor48Count =
        true
    ; nuRIncludedFor48CountIsTrue =
        refl
    ; nuRNeededNumericallyForHyperchargeSum =
        false
    ; nuRNeededNumericallyForHyperchargeSumIsFalse =
        refl
    ; gravitationalStatement =
        gravitationalVerificationStatement
    ; gravitationalStatementIsCanonical =
        refl
    ; nuRStatement =
        nuRRoleStatement
    ; nuRStatementIsCanonical =
        refl
    ; exactStandardModelPromoted =
        false
    ; exactStandardModelPromotedIsFalse =
        refl
    ; inheritedCandidateStatus =
        true
    ; inheritedCandidateStatusIsTrue =
        refl
    ; gDHREqualsGSM =
        false
    ; gDHREqualsGSMIsFalse =
        refl
    ; anomalyCancellationInherited =
        true
    ; anomalyCancellationInheritedIsTrue =
        refl
    ; carrierSMHyperchargeMatch =
        true
    ; carrierSMHyperchargeMatchIsTrue =
        refl
    ; exactDHRPromoted =
        false
    ; exactDHRPromotedIsFalse =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; auditTrail =
        "The gravitational-U1 hypercharge sum vanishes per generation in the left-handed convention"
        ∷ "nu_R is neutral; it matters for the carrier's 48-count but contributes zero to this anomaly"
        ∷ "anomalyCancellationInherited=true is conditional on carrierSMHyperchargeMatch=true"
        ∷ "No exact SM, DHR, Clay, or terminal promotion is issued"
        ∷ []
    }

gravitationalAnomalyNumeratorZero :
  gravitationalNumeratorOver6 canonicalGravitationalAnomalyCancellationReceipt
  ≡
  0ℤ
gravitationalAnomalyNumeratorZero =
  refl

gravitationalAnomalyNuRNeutral :
  nuRHasZeroHypercharge canonicalGravitationalAnomalyCancellationReceipt
  ≡
  refl
gravitationalAnomalyNuRNeutral =
  refl

gravitationalAnomalyStandardModelPromotionFalse :
  exactStandardModelPromoted canonicalGravitationalAnomalyCancellationReceipt
  ≡
  false
gravitationalAnomalyStandardModelPromotionFalse =
  refl

gravitationalAnomalyInheritedCandidate :
  inheritedCandidateStatus canonicalGravitationalAnomalyCancellationReceipt
  ≡
  true
gravitationalAnomalyInheritedCandidate =
  refl

gravitationalAnomalyKeepsGDHRGSMFalse :
  gDHREqualsGSM canonicalGravitationalAnomalyCancellationReceipt
  ≡
  false
gravitationalAnomalyKeepsGDHRGSMFalse =
  refl

gravitationalAnomalyTerminalPromotionFalse :
  terminalClaimPromoted canonicalGravitationalAnomalyCancellationReceipt
  ≡
  false
gravitationalAnomalyTerminalPromotionFalse =
  refl
