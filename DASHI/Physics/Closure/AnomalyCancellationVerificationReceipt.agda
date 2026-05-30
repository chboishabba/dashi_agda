module DASHI.Physics.Closure.AnomalyCancellationVerificationReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Integer.Base using (ℤ; +_; -[1+_]; 0ℤ; _+_)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.U1YChargeAssignmentTableReceipt as U1YTable
import DASHI.Physics.QFT.HyperchargeNormalisationAnomalyReceipt as HAnomaly

------------------------------------------------------------------------
-- Standard anomaly cancellation verification.
--
-- Convention: all anomaly sums are per generation and use left-handed Weyl
-- fermions only.  Physical u_R, d_R, e_R are replaced by u^c, d^c, e^c,
-- so their U(1)_Y signs are reversed:
--
--   Q_L : 3 colours x 2 weak states, Y=+1/6
--   u^c : 3 anti-colours,           Y=-2/3
--   d^c : 3 anti-colours,           Y=+1/3
--   L_L : 2 weak states,            Y=-1/2
--   e^c : 1 state,                  Y=+1
--   nu^c: 1 state,                  Y=0
--
-- Mixed SU(3)^2-U(1)_Y uses the Dynkin index of 3 and anti-3 with the
-- same positive index; the cancellation is 2*(+1/6) + (-2/3) + (+1/3)=0.

cubicAnomalyPerGenerationNumeratorOver216 :
  ℤ
cubicAnomalyPerGenerationNumeratorOver216 =
  + 6
  + -[1+ 191 ]
  + + 24
  + -[1+ 53 ]
  + + 216
  + + 0

su2SquaredU1PerGenerationNumeratorOver6 :
  ℤ
su2SquaredU1PerGenerationNumeratorOver6 =
  + 3 + -[1+ 2 ]

su3SquaredU1PerGenerationNumeratorOver6 :
  ℤ
su3SquaredU1PerGenerationNumeratorOver6 =
  + 2 + -[1+ 3 ] + + 2

cubicAnomalyPerGenerationNumeratorIsZero :
  cubicAnomalyPerGenerationNumeratorOver216 ≡ 0ℤ
cubicAnomalyPerGenerationNumeratorIsZero =
  refl

su2SquaredU1PerGenerationNumeratorIsZero :
  su2SquaredU1PerGenerationNumeratorOver6 ≡ 0ℤ
su2SquaredU1PerGenerationNumeratorIsZero =
  refl

su3SquaredU1PerGenerationNumeratorIsZero :
  su3SquaredU1PerGenerationNumeratorOver6 ≡ 0ℤ
su3SquaredU1PerGenerationNumeratorIsZero =
  refl

cubicVerificationStatement :
  String
cubicVerificationStatement =
  "[U(1)_Y]^3 per generation, denominator 216: 6 - 192 + 24 - 54 + 216 + 0 = 0"

su2VerificationStatement :
  String
su2VerificationStatement =
  "SU(2)^2 U(1)_Y per generation, denominator 6: 3 colours of Q_L give +3 and L_L gives -3, so 3 - 3 = 0"

su3VerificationStatement :
  String
su3VerificationStatement =
  "SU(3)^2 U(1)_Y per generation, denominator 6: Q_L gives +2, u^c gives -4, d^c gives +2, so 2 - 4 + 2 = 0"

record AnomalyCancellationVerificationReceipt : Setω where
  field
    chargeTableReceipt :
      U1YTable.U1YChargeAssignmentTableReceipt

    chargeTableHas48States :
      U1YTable.totalWeylCount chargeTableReceipt ≡ 48

    leftHandedConvention :
      String

    leftHandedConventionIsCanonical :
      leftHandedConvention ≡ U1YTable.leftHandedAnomalyConvention

    hyperchargeAuthorityReceipt :
      HAnomaly.HyperchargeNormalisationAnomalyReceipt

    authorityLedgerIsCanonical :
      HAnomaly.hyperchargeLedger hyperchargeAuthorityReceipt
      ≡
      HAnomaly.canonicalHyperchargeLedger

    cubicNumeratorOver216 :
      ℤ

    cubicNumeratorOver216IsStandard :
      cubicNumeratorOver216
      ≡
      cubicAnomalyPerGenerationNumeratorOver216

    cubicNumeratorOver216IsZero :
      cubicNumeratorOver216 ≡ 0ℤ

    su2MixedNumeratorOver6 :
      ℤ

    su2MixedNumeratorOver6IsStandard :
      su2MixedNumeratorOver6
      ≡
      su2SquaredU1PerGenerationNumeratorOver6

    su2MixedNumeratorOver6IsZero :
      su2MixedNumeratorOver6 ≡ 0ℤ

    su3MixedNumeratorOver6 :
      ℤ

    su3MixedNumeratorOver6IsStandard :
      su3MixedNumeratorOver6
      ≡
      su3SquaredU1PerGenerationNumeratorOver6

    su3MixedNumeratorOver6IsZero :
      su3MixedNumeratorOver6 ≡ 0ℤ

    cubicAnomalyCancels :
      Bool

    cubicAnomalyCancelsIsTrue :
      cubicAnomalyCancels ≡ true

    su2MixedAnomalyCancels :
      Bool

    su2MixedAnomalyCancelsIsTrue :
      su2MixedAnomalyCancels ≡ true

    su3MixedAnomalyCancels :
      Bool

    su3MixedAnomalyCancelsIsTrue :
      su3MixedAnomalyCancels ≡ true

    cubicStatement :
      String

    cubicStatementIsCanonical :
      cubicStatement ≡ cubicVerificationStatement

    su2Statement :
      String

    su2StatementIsCanonical :
      su2Statement ≡ su2VerificationStatement

    su3Statement :
      String

    su3StatementIsCanonical :
      su3Statement ≡ su3VerificationStatement

    anomalyCancellationInherited :
      Bool

    anomalyCancellationInheritedIsTrue :
      anomalyCancellationInherited ≡ true

    carrierSMHyperchargeMatch :
      Bool

    carrierSMHyperchargeMatchIsTrue :
      carrierSMHyperchargeMatch ≡ true

    inheritedCandidateStatus :
      Bool

    inheritedCandidateStatusIsTrue :
      inheritedCandidateStatus ≡ true

    carrierDerivesAssignmentPromoted :
      Bool

    carrierDerivesAssignmentPromotedIsFalse :
      carrierDerivesAssignmentPromoted ≡ false

    exactStandardModelPromoted :
      Bool

    exactStandardModelPromotedIsFalse :
      exactStandardModelPromoted ≡ false

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

open AnomalyCancellationVerificationReceipt public

canonicalAnomalyCancellationVerificationReceipt :
  AnomalyCancellationVerificationReceipt
canonicalAnomalyCancellationVerificationReceipt =
  record
    { chargeTableReceipt =
        U1YTable.canonicalU1YChargeAssignmentTableReceipt
    ; chargeTableHas48States =
        refl
    ; leftHandedConvention =
        U1YTable.leftHandedAnomalyConvention
    ; leftHandedConventionIsCanonical =
        refl
    ; hyperchargeAuthorityReceipt =
        HAnomaly.canonicalHyperchargeNormalisationAnomalyReceipt
    ; authorityLedgerIsCanonical =
        refl
    ; cubicNumeratorOver216 =
        cubicAnomalyPerGenerationNumeratorOver216
    ; cubicNumeratorOver216IsStandard =
        refl
    ; cubicNumeratorOver216IsZero =
        refl
    ; su2MixedNumeratorOver6 =
        su2SquaredU1PerGenerationNumeratorOver6
    ; su2MixedNumeratorOver6IsStandard =
        refl
    ; su2MixedNumeratorOver6IsZero =
        refl
    ; su3MixedNumeratorOver6 =
        su3SquaredU1PerGenerationNumeratorOver6
    ; su3MixedNumeratorOver6IsStandard =
        refl
    ; su3MixedNumeratorOver6IsZero =
        refl
    ; cubicAnomalyCancels =
        true
    ; cubicAnomalyCancelsIsTrue =
        refl
    ; su2MixedAnomalyCancels =
        true
    ; su2MixedAnomalyCancelsIsTrue =
        refl
    ; su3MixedAnomalyCancels =
        true
    ; su3MixedAnomalyCancelsIsTrue =
        refl
    ; cubicStatement =
        cubicVerificationStatement
    ; cubicStatementIsCanonical =
        refl
    ; su2Statement =
        su2VerificationStatement
    ; su2StatementIsCanonical =
        refl
    ; su3Statement =
        su3VerificationStatement
    ; su3StatementIsCanonical =
        refl
    ; anomalyCancellationInherited =
        true
    ; anomalyCancellationInheritedIsTrue =
        refl
    ; carrierSMHyperchargeMatch =
        true
    ; carrierSMHyperchargeMatchIsTrue =
        refl
    ; inheritedCandidateStatus =
        true
    ; inheritedCandidateStatusIsTrue =
        refl
    ; carrierDerivesAssignmentPromoted =
        false
    ; carrierDerivesAssignmentPromotedIsFalse =
        refl
    ; exactStandardModelPromoted =
        false
    ; exactStandardModelPromotedIsFalse =
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
        "The prompt's physical right-handed signs are not used directly in anomaly sums"
        ∷ "Left-handed conjugates give the standard cancellations: cubic, SU2 mixed, and SU3 mixed"
        ∷ "SU3 mixed cancellation is 2 - 4 + 2 = 0; no erroneous residual is preserved"
        ∷ "anomalyCancellationInherited=true is conditional on carrierSMHyperchargeMatch=true"
        ∷ "No exact SM, DHR, Clay, or terminal promotion is issued"
        ∷ []
    }

anomalyVerificationCubicZero :
  cubicNumeratorOver216 canonicalAnomalyCancellationVerificationReceipt
  ≡
  0ℤ
anomalyVerificationCubicZero =
  refl

anomalyVerificationSU2MixedZero :
  su2MixedNumeratorOver6 canonicalAnomalyCancellationVerificationReceipt
  ≡
  0ℤ
anomalyVerificationSU2MixedZero =
  refl

anomalyVerificationSU3MixedZero :
  su3MixedNumeratorOver6 canonicalAnomalyCancellationVerificationReceipt
  ≡
  0ℤ
anomalyVerificationSU3MixedZero =
  refl

anomalyVerificationStandardModelPromotionFalse :
  exactStandardModelPromoted canonicalAnomalyCancellationVerificationReceipt
  ≡
  false
anomalyVerificationStandardModelPromotionFalse =
  refl

anomalyVerificationInheritedCandidate :
  inheritedCandidateStatus canonicalAnomalyCancellationVerificationReceipt
  ≡
  true
anomalyVerificationInheritedCandidate =
  refl

anomalyVerificationTerminalPromotionFalse :
  terminalClaimPromoted canonicalAnomalyCancellationVerificationReceipt
  ≡
  false
anomalyVerificationTerminalPromotionFalse =
  refl
