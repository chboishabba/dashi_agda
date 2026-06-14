module DASHI.Metric.AgreementSurrealGaugeBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Nat using (_≤_; _⊔_)
open import Data.Vec using (Vec)

open import Ultrametric as UMetric
open import DASHI.Algebra.Trit using (Trit)
open import DASHI.Metric.AgreementUltrametric as AM
open import DASHI.Metric.FineAgreementUltrametric as FAM

------------------------------------------------------------------------
-- Checked metric bridge.

record MetricAuthorityReceipt (n : Nat) : Set₁ where
  field
    prefixMetric :
      UMetric.Ultrametric (Vec Trit n)

    prefixDistance :
      Vec Trit n →
      Vec Trit n →
      Nat

    prefixDistanceIsAgreementDistance :
      prefixDistance ≡ AM.dNat

    prefixDepth :
      Vec Trit n →
      Vec Trit n →
      Nat

    prefixDepthIsAgreeDepth :
      prefixDepth ≡ AM.agreeDepth

    prefixIdentityConsumed :
      Bool

    prefixIdentityConsumedIsTrue :
      prefixIdentityConsumed ≡ true

    prefixIdentityReceipt :
      ∀ x →
      prefixDistance x x ≡ 0

    prefixSymmetryConsumed :
      Bool

    prefixSymmetryConsumedIsTrue :
      prefixSymmetryConsumed ≡ true

    prefixSymmetryReceipt :
      ∀ x y →
      prefixDistance x y ≡ prefixDistance y x

    prefixUltraConsumed :
      Bool

    prefixUltraConsumedIsTrue :
      prefixUltraConsumed ≡ true

    prefixUltraReceipt :
      ∀ x y z →
      prefixDistance x z ≤
      (prefixDistance x y ⊔ prefixDistance y z)

    suffixFineMetric :
      UMetric.Ultrametric (Vec Trit n)

    suffixFineDistance :
      Vec Trit n →
      Vec Trit n →
      Nat

    suffixFineDistanceIsFineAgreementDistance :
      suffixFineDistance ≡ FAM.dNatFine

    suffixFineDepth :
      Vec Trit n →
      Vec Trit n →
      Nat

    suffixFineDepthIsFineAgreeDepth :
      suffixFineDepth ≡ FAM.agreeDepthFine

    suffixFineIdentityConsumed :
      Bool

    suffixFineIdentityConsumedIsTrue :
      suffixFineIdentityConsumed ≡ true

    suffixFineIdentityReceipt :
      ∀ x →
      suffixFineDistance x x ≡ 0

    suffixFineSymmetryConsumed :
      Bool

    suffixFineSymmetryConsumedIsTrue :
      suffixFineSymmetryConsumed ≡ true

    suffixFineSymmetryReceipt :
      ∀ x y →
      suffixFineDistance x y ≡ suffixFineDistance y x

    suffixFineUltraConsumed :
      Bool

    suffixFineUltraConsumedIsTrue :
      suffixFineUltraConsumed ≡ true

    suffixFineUltraReceipt :
      ∀ x y z →
      suffixFineDistance x z ≤
      (suffixFineDistance x y ⊔ suffixFineDistance y z)

open MetricAuthorityReceipt public

canonicalMetricAuthorityReceipt :
  ∀ n →
  MetricAuthorityReceipt n
canonicalMetricAuthorityReceipt n =
  record
    { prefixMetric =
        AM.ultrametricVec
    ; prefixDistance =
        AM.dNat
    ; prefixDistanceIsAgreementDistance =
        refl
    ; prefixDepth =
        AM.agreeDepth
    ; prefixDepthIsAgreeDepth =
        refl
    ; prefixIdentityConsumed =
        true
    ; prefixIdentityConsumedIsTrue =
        refl
    ; prefixIdentityReceipt =
        UMetric.Ultrametric.id-zero AM.ultrametricVec
    ; prefixSymmetryConsumed =
        true
    ; prefixSymmetryConsumedIsTrue =
        refl
    ; prefixSymmetryReceipt =
        UMetric.Ultrametric.symmetric AM.ultrametricVec
    ; prefixUltraConsumed =
        true
    ; prefixUltraConsumedIsTrue =
        refl
    ; prefixUltraReceipt =
        UMetric.Ultrametric.ultratriangle AM.ultrametricVec
    ; suffixFineMetric =
        FAM.ultrametricVec
    ; suffixFineDistance =
        FAM.dNatFine
    ; suffixFineDistanceIsFineAgreementDistance =
        refl
    ; suffixFineDepth =
        FAM.agreeDepthFine
    ; suffixFineDepthIsFineAgreeDepth =
        refl
    ; suffixFineIdentityConsumed =
        true
    ; suffixFineIdentityConsumedIsTrue =
        refl
    ; suffixFineIdentityReceipt =
        UMetric.Ultrametric.id-zero FAM.ultrametricVec
    ; suffixFineSymmetryConsumed =
        true
    ; suffixFineSymmetryConsumedIsTrue =
        refl
    ; suffixFineSymmetryReceipt =
        UMetric.Ultrametric.symmetric FAM.ultrametricVec
    ; suffixFineUltraConsumed =
        true
    ; suffixFineUltraConsumedIsTrue =
        refl
    ; suffixFineUltraReceipt =
        UMetric.Ultrametric.ultratriangle FAM.ultrametricVec
    }

------------------------------------------------------------------------
-- Symbolic No/surreal gauge slot.

data GaugeAuthorityScope : Set where
  externalChangeOfGaugeAuthoritySlot :
    GaugeAuthorityScope

data SurrealGaugeBlocker : Set where
  missingNoSurrealGaugeAuthority :
    SurrealGaugeBlocker

data GaugeAntitoneDirection : Set where
  depthIncreasesGaugeDoesNotIncrease :
    GaugeAntitoneDirection

data GaugeLawShapeKind : Set where
  agreeDepthVariableLawShape :
    GaugeLawShapeKind

  symbolicThreePowerMinusDepthGaugeLawShape :
    GaugeLawShapeKind

  antitoneDirectionLawShape :
    GaugeLawShapeKind

  ultrametricInheritancePrerequisiteLawShape :
    GaugeLawShapeKind

record GaugeIsometryVariableRows (n : Nat) : Set₁ where
  field
    metricPrerequisites :
      MetricAuthorityReceipt n

    requiredAgreeDepthVariable :
      Vec Trit n →
      Vec Trit n →
      Nat

    requiredAgreeDepthVariableIsPrefixAgreeDepth :
      requiredAgreeDepthVariable ≡ AM.agreeDepth

    requiredSymbolicGaugeVariable :
      String

    requiredSymbolicGaugeVariableIsThreePowerMinusDepth :
      requiredSymbolicGaugeVariable ≡ "3^-agreeDepth"

    requiredAntitoneDirection :
      GaugeAntitoneDirection

    requiredAntitoneDirectionIsDepthToGauge :
      requiredAntitoneDirection ≡ depthIncreasesGaugeDoesNotIncrease

    requiredPrefixUltrametricPrerequisite :
      UMetric.Ultrametric (Vec Trit n)

    requiredPrefixUltrametricPrerequisiteIsCanonical :
      requiredPrefixUltrametricPrerequisite ≡ AM.ultrametricVec

    requiredSuffixFineUltrametricPrerequisite :
      UMetric.Ultrametric (Vec Trit n)

    requiredSuffixFineUltrametricPrerequisiteIsCanonical :
      requiredSuffixFineUltrametricPrerequisite ≡ FAM.ultrametricVec

    prefixIdentityPrerequisiteConsumed :
      Bool

    prefixIdentityPrerequisiteConsumedIsTrue :
      prefixIdentityPrerequisiteConsumed ≡ true

    prefixSymmetryPrerequisiteConsumed :
      Bool

    prefixSymmetryPrerequisiteConsumedIsTrue :
      prefixSymmetryPrerequisiteConsumed ≡ true

    prefixUltraPrerequisiteConsumed :
      Bool

    prefixUltraPrerequisiteConsumedIsTrue :
      prefixUltraPrerequisiteConsumed ≡ true

    suffixFineIdentityPrerequisiteConsumed :
      Bool

    suffixFineIdentityPrerequisiteConsumedIsTrue :
      suffixFineIdentityPrerequisiteConsumed ≡ true

    suffixFineSymmetryPrerequisiteConsumed :
      Bool

    suffixFineSymmetryPrerequisiteConsumedIsTrue :
      suffixFineSymmetryPrerequisiteConsumed ≡ true

    suffixFineUltraPrerequisiteConsumed :
      Bool

    suffixFineUltraPrerequisiteConsumedIsTrue :
      suffixFineUltraPrerequisiteConsumed ≡ true

    gaugeIsometryLawShapeRecorded :
      Bool

    gaugeIsometryLawShapeRecordedIsTrue :
      gaugeIsometryLawShapeRecorded ≡ true

    antitoneLawShapeRecorded :
      Bool

    antitoneLawShapeRecordedIsTrue :
      antitoneLawShapeRecorded ≡ true

    ultrametricInheritancePrerequisitesRecorded :
      Bool

    ultrametricInheritancePrerequisitesRecordedIsTrue :
      ultrametricInheritancePrerequisitesRecorded ≡ true

    gaugeIsometryPromoted :
      Bool

    gaugeIsometryPromotedIsFalse :
      gaugeIsometryPromoted ≡ false

    surrealArithmeticAuthorityAccepted :
      Bool

    surrealArithmeticAuthorityAcceptedIsFalse :
      surrealArithmeticAuthorityAccepted ≡ false

open GaugeIsometryVariableRows public

canonicalGaugeIsometryVariableRows :
  ∀ n →
  GaugeIsometryVariableRows n
canonicalGaugeIsometryVariableRows n =
  record
    { metricPrerequisites =
        canonicalMetricAuthorityReceipt n
    ; requiredAgreeDepthVariable =
        AM.agreeDepth
    ; requiredAgreeDepthVariableIsPrefixAgreeDepth =
        refl
    ; requiredSymbolicGaugeVariable =
        "3^-agreeDepth"
    ; requiredSymbolicGaugeVariableIsThreePowerMinusDepth =
        refl
    ; requiredAntitoneDirection =
        depthIncreasesGaugeDoesNotIncrease
    ; requiredAntitoneDirectionIsDepthToGauge =
        refl
    ; requiredPrefixUltrametricPrerequisite =
        AM.ultrametricVec
    ; requiredPrefixUltrametricPrerequisiteIsCanonical =
        refl
    ; requiredSuffixFineUltrametricPrerequisite =
        FAM.ultrametricVec
    ; requiredSuffixFineUltrametricPrerequisiteIsCanonical =
        refl
    ; prefixIdentityPrerequisiteConsumed =
        true
    ; prefixIdentityPrerequisiteConsumedIsTrue =
        refl
    ; prefixSymmetryPrerequisiteConsumed =
        true
    ; prefixSymmetryPrerequisiteConsumedIsTrue =
        refl
    ; prefixUltraPrerequisiteConsumed =
        true
    ; prefixUltraPrerequisiteConsumedIsTrue =
        refl
    ; suffixFineIdentityPrerequisiteConsumed =
        true
    ; suffixFineIdentityPrerequisiteConsumedIsTrue =
        refl
    ; suffixFineSymmetryPrerequisiteConsumed =
        true
    ; suffixFineSymmetryPrerequisiteConsumedIsTrue =
        refl
    ; suffixFineUltraPrerequisiteConsumed =
        true
    ; suffixFineUltraPrerequisiteConsumedIsTrue =
        refl
    ; gaugeIsometryLawShapeRecorded =
        true
    ; gaugeIsometryLawShapeRecordedIsTrue =
        refl
    ; antitoneLawShapeRecorded =
        true
    ; antitoneLawShapeRecordedIsTrue =
        refl
    ; ultrametricInheritancePrerequisitesRecorded =
        true
    ; ultrametricInheritancePrerequisitesRecordedIsTrue =
        refl
    ; gaugeIsometryPromoted =
        false
    ; gaugeIsometryPromotedIsFalse =
        refl
    ; surrealArithmeticAuthorityAccepted =
        false
    ; surrealArithmeticAuthorityAcceptedIsFalse =
        refl
    }

record NonPromotingGaugeLawShapeRow (n : Nat) : Set₁ where
  field
    lawShapeKind :
      GaugeLawShapeKind

    lawShapeVariables :
      GaugeIsometryVariableRows n

    lawShapeRecorded :
      Bool

    lawShapeRecordedIsTrue :
      lawShapeRecorded ≡ true

    lawShapePromoted :
      Bool

    lawShapePromotedIsFalse :
      lawShapePromoted ≡ false

    rowReading :
      String

open NonPromotingGaugeLawShapeRow public

canonicalNonPromotingGaugeLawShapeRow :
  ∀ n →
  GaugeLawShapeKind →
  String →
  NonPromotingGaugeLawShapeRow n
canonicalNonPromotingGaugeLawShapeRow n kind reading =
  record
    { lawShapeKind =
        kind
    ; lawShapeVariables =
        canonicalGaugeIsometryVariableRows n
    ; lawShapeRecorded =
        true
    ; lawShapeRecordedIsTrue =
        refl
    ; lawShapePromoted =
        false
    ; lawShapePromotedIsFalse =
        refl
    ; rowReading =
        reading
    }

record AgreementSurrealGaugeSlot (n : Nat) : Set₁ where
  field
    metricReceipt :
      MetricAuthorityReceipt n

    gaugeIsometryVariables :
      GaugeIsometryVariableRows n

    agreeDepthVariableLawRow :
      NonPromotingGaugeLawShapeRow n

    symbolicGaugeVariableLawRow :
      NonPromotingGaugeLawShapeRow n

    antitoneDirectionLawRow :
      NonPromotingGaugeLawShapeRow n

    ultrametricInheritancePrerequisiteLawRow :
      NonPromotingGaugeLawShapeRow n

    gaugeScope :
      GaugeAuthorityScope

    gaugeScopeIsExternal :
      gaugeScope ≡ externalChangeOfGaugeAuthoritySlot

    gaugeFormula :
      String

    gaugeDepth :
      Vec Trit n →
      Vec Trit n →
      Nat

    gaugeDepthIsPrefixAgreeDepth :
      gaugeDepth ≡ AM.agreeDepth

    gaugeDependsOnPrefixMetric :
      Bool

    gaugeDependsOnPrefixMetricIsTrue :
      gaugeDependsOnPrefixMetric ≡ true

    suffixFineMetricAlsoRecorded :
      Bool

    suffixFineMetricAlsoRecordedIsTrue :
      suffixFineMetricAlsoRecorded ≡ true

    surrealGaugeAuthorityAccepted :
      Bool

    surrealGaugeAuthorityAcceptedIsFalse :
      surrealGaugeAuthorityAccepted ≡ false

    surrealMetricClaimPromoted :
      Bool

    surrealMetricClaimPromotedIsFalse :
      surrealMetricClaimPromoted ≡ false

    firstSurrealGaugeBlocker :
      SurrealGaugeBlocker

    firstSurrealGaugeBlockerIsMissingAuthority :
      firstSurrealGaugeBlocker ≡ missingNoSurrealGaugeAuthority

    bridgeReading :
      String

open AgreementSurrealGaugeSlot public

canonicalAgreementSurrealGaugeSlot :
  ∀ n →
  AgreementSurrealGaugeSlot n
canonicalAgreementSurrealGaugeSlot n =
  record
    { metricReceipt =
        canonicalMetricAuthorityReceipt n
    ; gaugeIsometryVariables =
        canonicalGaugeIsometryVariableRows n
    ; agreeDepthVariableLawRow =
        canonicalNonPromotingGaugeLawShapeRow n
          agreeDepthVariableLawShape
          "Law-shape row records agreeDepth as the required source variable for the symbolic gauge; no gauge isometry theorem is promoted."
    ; symbolicGaugeVariableLawRow =
        canonicalNonPromotingGaugeLawShapeRow n
          symbolicThreePowerMinusDepthGaugeLawShape
          "Law-shape row records 3^-agreeDepth as symbolic No/surreal target notation only; no No/surreal arithmetic authority is accepted."
    ; antitoneDirectionLawRow =
        canonicalNonPromotingGaugeLawShapeRow n
          antitoneDirectionLawShape
          "Law-shape row records the required antitone direction from greater agreement depth to non-increasing symbolic gauge value; no ordered No/surreal proof is promoted."
    ; ultrametricInheritancePrerequisiteLawRow =
        canonicalNonPromotingGaugeLawShapeRow n
          ultrametricInheritancePrerequisiteLawShape
          "Law-shape row records prefix and suffix ultrametric inheritance prerequisites as consumed local receipts; the external gauge inheritance theorem remains unpromoted."
    ; gaugeScope =
        externalChangeOfGaugeAuthoritySlot
    ; gaugeScopeIsExternal =
        refl
    ; gaugeFormula =
        "No/surreal gauge slot: 3^-agreeDepth"
    ; gaugeDepth =
        AM.agreeDepth
    ; gaugeDepthIsPrefixAgreeDepth =
        refl
    ; gaugeDependsOnPrefixMetric =
        true
    ; gaugeDependsOnPrefixMetricIsTrue =
        refl
    ; suffixFineMetricAlsoRecorded =
        true
    ; suffixFineMetricAlsoRecordedIsTrue =
        refl
    ; surrealGaugeAuthorityAccepted =
        false
    ; surrealGaugeAuthorityAcceptedIsFalse =
        refl
    ; surrealMetricClaimPromoted =
        false
    ; surrealMetricClaimPromotedIsFalse =
        refl
    ; firstSurrealGaugeBlocker =
        missingNoSurrealGaugeAuthority
    ; firstSurrealGaugeBlockerIsMissingAuthority =
        refl
    ; bridgeReading =
        "Prefix agreeDepth and suffix fine agreement are checked locally; 3^-agreeDepth is only a symbolic external change-of-gauge slot, with No/surreal claims fail-closed."
    }

canonicalSurrealGaugeAuthorityStillFalse :
  ∀ {n : Nat} →
  surrealGaugeAuthorityAccepted (canonicalAgreementSurrealGaugeSlot n) ≡ false
canonicalSurrealGaugeAuthorityStillFalse = refl

canonicalSurrealMetricClaimStillFalse :
  ∀ {n : Nat} →
  surrealMetricClaimPromoted (canonicalAgreementSurrealGaugeSlot n) ≡ false
canonicalSurrealMetricClaimStillFalse = refl
