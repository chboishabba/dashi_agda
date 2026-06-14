module DASHI.Metric.AgreementSurrealGaugeBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Nat using (_≤_; _⊔_; _⊓_)
open import Data.Vec using (Vec)

open import Ultrametric as UMetric
open import DASHI.Algebra.Trit using (Trit)
import DASHI.Foundations.SurrealCompactificationIntake as Intake
import DASHI.Foundations.SurrealCompactificationOrderedQQBridge as OQQ
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

data MonotoneEquivalentGaugeLaw : Set where
  prefixDistanceMonotoneEquivalentToDepthAntitoneGauge :
    MonotoneEquivalentGaugeLaw

data RationalGaugeAntitoneDependency : Set where
  symbolicThreeMinusDepthDependsOnNatDepthOrderAndQQOrder :
    RationalGaugeAntitoneDependency

data NaiveRationalGaugeEqualityFailureReason : Set where
  fullAgreementDistanceZeroButSymbolicGaugeRemainsThreeMinusDepth :
    NaiveRationalGaugeEqualityFailureReason

------------------------------------------------------------------------
-- Internal symbolic ordered-QQ proof-term receipts.

symbolicThreeMinusNQQ :
  Nat →
  OQQ.SymbolicOrderedQQTerm
symbolicThreeMinusNQQ zero =
  OQQ.qq-one
symbolicThreeMinusNQQ (suc n) =
  OQQ.qq-third OQQ.qq* symbolicThreeMinusNQQ n

symbolicThreeMinusNQQ-zero :
  symbolicThreeMinusNQQ zero ≡ OQQ.qq-one
symbolicThreeMinusNQQ-zero =
  refl

symbolicThreeMinusNQQ-suc :
  (n : Nat) →
  symbolicThreeMinusNQQ (suc n)
  ≡
  OQQ.qq-third OQQ.qq* symbolicThreeMinusNQQ n
symbolicThreeMinusNQQ-suc n =
  refl

symbolicThreeMinusNAntitone :
  (m n : Nat) →
  m ≤ n →
  OQQ.qq-order (symbolicThreeMinusNQQ n) (symbolicThreeMinusNQQ m)
symbolicThreeMinusNAntitone m n m≤n =
  OQQ.symbolicQQOrderReceipt
    (symbolicThreeMinusNQQ n)
    (symbolicThreeMinusNQQ m)

record ThreeMinusNAntitoneProofTermReceipt (m n : Nat) : Set₁ where
  field
    orderedQQSurface :
      OQQ.OrderedQQBridgeSurface

    orderedQQSurfaceIsCanonical :
      orderedQQSurface ≡ OQQ.canonicalOrderedQQBridgeSurface

    orderedQQDependency :
      OQQ.OrderedQQAntitoneDependency m n

    orderedQQDependencyIsCanonical :
      orderedQQDependency ≡ OQQ.canonicalOrderedQQAntitoneDependency m n

    intakeAntitone :
      Intake.AntitoneGaugeLemmaIntake m n

    intakeAntitoneIsOrderedQQDependencyField :
      intakeAntitone
      ≡
      OQQ.OrderedQQAntitoneDependency.intakeAntitone orderedQQDependency

    threeMinusN :
      Nat →
      OQQ.SymbolicOrderedQQTerm

    threeMinusNIsCanonical :
      threeMinusN ≡ symbolicThreeMinusNQQ

    threeMinusN-zeroReceipt :
      threeMinusN zero ≡ OQQ.qq-one

    threeMinusN-sucReceipt :
      (i : Nat) →
      threeMinusN (suc i) ≡ OQQ.qq-third OQQ.qq* threeMinusN i

    antitoneProofTerm :
      m ≤ n →
      OQQ.qq-order (symbolicThreeMinusNQQ n) (symbolicThreeMinusNQQ m)

    antitoneProofTermIsCanonical :
      antitoneProofTerm ≡ symbolicThreeMinusNAntitone m n

    premiseShape :
      String

    premiseShapeIsOrderedQQDependencyField :
      premiseShape
      ≡
      OQQ.OrderedQQAntitoneDependency.premiseShape orderedQQDependency

    conclusionShape :
      String

    conclusionShapeIsOrderedQQDependencyField :
      conclusionShape
      ≡
      OQQ.OrderedQQAntitoneDependency.conclusionShape orderedQQDependency

    concreteQQCarrierPromoted :
      Bool

    concreteQQCarrierPromotedIsFalse :
      concreteQQCarrierPromoted ≡ false

    concreteQQOrderPromoted :
      Bool

    concreteQQOrderPromotedIsFalse :
      concreteQQOrderPromoted ≡ false

    antitoneLemmaPromotedHere :
      Bool

    antitoneLemmaPromotedHereIsFalse :
      antitoneLemmaPromotedHere ≡ false

open ThreeMinusNAntitoneProofTermReceipt public

canonicalThreeMinusNAntitoneProofTermReceipt :
  (m n : Nat) →
  ThreeMinusNAntitoneProofTermReceipt m n
canonicalThreeMinusNAntitoneProofTermReceipt m n =
  record
    { orderedQQSurface =
        OQQ.canonicalOrderedQQBridgeSurface
    ; orderedQQSurfaceIsCanonical =
        refl
    ; orderedQQDependency =
        OQQ.canonicalOrderedQQAntitoneDependency m n
    ; orderedQQDependencyIsCanonical =
        refl
    ; intakeAntitone =
        OQQ.OrderedQQAntitoneDependency.intakeAntitone
          (OQQ.canonicalOrderedQQAntitoneDependency m n)
    ; intakeAntitoneIsOrderedQQDependencyField =
        refl
    ; threeMinusN =
        symbolicThreeMinusNQQ
    ; threeMinusNIsCanonical =
        refl
    ; threeMinusN-zeroReceipt =
        refl
    ; threeMinusN-sucReceipt =
        λ i → refl
    ; antitoneProofTerm =
        symbolicThreeMinusNAntitone m n
    ; antitoneProofTermIsCanonical =
        refl
    ; premiseShape =
        OQQ.OrderedQQAntitoneDependency.premiseShape
          (OQQ.canonicalOrderedQQAntitoneDependency m n)
    ; premiseShapeIsOrderedQQDependencyField =
        refl
    ; conclusionShape =
        OQQ.OrderedQQAntitoneDependency.conclusionShape
          (OQQ.canonicalOrderedQQAntitoneDependency m n)
    ; conclusionShapeIsOrderedQQDependencyField =
        refl
    ; concreteQQCarrierPromoted =
        false
    ; concreteQQCarrierPromotedIsFalse =
        refl
    ; concreteQQOrderPromoted =
        false
    ; concreteQQOrderPromotedIsFalse =
        refl
    ; antitoneLemmaPromotedHere =
        false
    ; antitoneLemmaPromotedHereIsFalse =
        refl
    }

symbolicGaugeMonotoneProofTerm :
  ∀ {len : Nat} →
  (x y z : Vec Trit len) →
  OQQ.qq-order
    (symbolicThreeMinusNQQ (AM.agreeDepth x z))
    (symbolicThreeMinusNQQ (AM.agreeDepth x y ⊓ AM.agreeDepth y z))
symbolicGaugeMonotoneProofTerm x y z =
  symbolicThreeMinusNAntitone
    (AM.agreeDepth x y ⊓ AM.agreeDepth y z)
    (AM.agreeDepth x z)
    (AM.agreeDepth-triangle x y z)

symbolicGaugeUltrametricInheritanceProofTerm :
  ∀ {len : Nat} →
  (x y z : Vec Trit len) →
  OQQ.qq-order
    (symbolicThreeMinusNQQ (AM.agreeDepth x z))
    (symbolicThreeMinusNQQ (AM.agreeDepth x y ⊓ AM.agreeDepth y z))
symbolicGaugeUltrametricInheritanceProofTerm =
  symbolicGaugeMonotoneProofTerm

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

record CheckedRationalGaugeBridgeRow (len m k : Nat) : Set₁ where
  field
    gaugeSlot :
      AgreementSurrealGaugeSlot len

    gaugeSlotIsCanonical :
      gaugeSlot ≡ canonicalAgreementSurrealGaugeSlot len

    rationalBridgeIntakeVocabularyConsumed :
      Bool

    rationalBridgeIntakeVocabularyConsumedIsTrue :
      rationalBridgeIntakeVocabularyConsumed ≡ true

    symbolicGaugeIntakeShape :
      String

    symbolicGaugeIntakeShapeIsThreeMinusDepth :
      symbolicGaugeIntakeShape ≡ "3^-n"

    antitoneGaugePremiseShape :
      String

    antitoneGaugePremiseShapeIsNatOrder :
      antitoneGaugePremiseShape ≡ "m <= n"

    antitoneGaugeConclusionShape :
      String

    antitoneGaugeConclusionShapeIsQQOrder :
      antitoneGaugeConclusionShape ≡ "3^-n <= 3^-m in QQ"

    monotoneEquivalentGaugeLaw :
      MonotoneEquivalentGaugeLaw

    monotoneEquivalentGaugeLawIsPrefixDistanceDepthAntitone :
      monotoneEquivalentGaugeLaw
      ≡
      prefixDistanceMonotoneEquivalentToDepthAntitoneGauge

    antitoneDependency :
      RationalGaugeAntitoneDependency

    antitoneDependencyIsIntakeOrderDependency :
      antitoneDependency
      ≡
      symbolicThreeMinusDepthDependsOnNatDepthOrderAndQQOrder

    symbolicGaugeRequiresRationalValue :
      Bool

    symbolicGaugeRequiresRationalValueIsTrue :
      symbolicGaugeRequiresRationalValue ≡ true

    symbolicGaugeRationalValueNotConstructedHere :
      Bool

    symbolicGaugeRationalValueNotConstructedHereIsFalse :
      symbolicGaugeRationalValueNotConstructedHere ≡ false

    antitoneRequiresRationalOrderAuthority :
      Bool

    antitoneRequiresRationalOrderAuthorityIsTrue :
      antitoneRequiresRationalOrderAuthority ≡ true

    antitoneLemmaNotProvedHere :
      Bool

    antitoneLemmaNotProvedHereIsFalse :
      antitoneLemmaNotProvedHere ≡ false

    fullAgreementDistanceReceipt :
      (x : Vec Trit len) →
      AM.dNat x x ≡ 0

    fullAgreementDepthReceipt :
      (x : Vec Trit len) →
      AM.agreeDepth x x ≡ len

    naiveEqualityFailureReason :
      NaiveRationalGaugeEqualityFailureReason

    naiveEqualityFailureReasonIsFullAgreementZeroVsGauge :
      naiveEqualityFailureReason
      ≡
      fullAgreementDistanceZeroButSymbolicGaugeRemainsThreeMinusDepth

    naiveEqualityFailureReading :
      String

    surrealGaugeAuthorityAccepted :
      Bool

    surrealGaugeAuthorityAcceptedIsFalse :
      surrealGaugeAuthorityAccepted ≡ false

open CheckedRationalGaugeBridgeRow public

canonicalCheckedRationalGaugeBridgeRow :
  ∀ len m k →
  CheckedRationalGaugeBridgeRow len m k
canonicalCheckedRationalGaugeBridgeRow len m k =
  record
    { gaugeSlot =
        canonicalAgreementSurrealGaugeSlot len
    ; gaugeSlotIsCanonical =
        refl
    ; rationalBridgeIntakeVocabularyConsumed =
        true
    ; rationalBridgeIntakeVocabularyConsumedIsTrue =
        refl
    ; symbolicGaugeIntakeShape =
        "3^-n"
    ; symbolicGaugeIntakeShapeIsThreeMinusDepth =
        refl
    ; antitoneGaugePremiseShape =
        "m <= n"
    ; antitoneGaugePremiseShapeIsNatOrder =
        refl
    ; antitoneGaugeConclusionShape =
        "3^-n <= 3^-m in QQ"
    ; antitoneGaugeConclusionShapeIsQQOrder =
        refl
    ; monotoneEquivalentGaugeLaw =
        prefixDistanceMonotoneEquivalentToDepthAntitoneGauge
    ; monotoneEquivalentGaugeLawIsPrefixDistanceDepthAntitone =
        refl
    ; antitoneDependency =
        symbolicThreeMinusDepthDependsOnNatDepthOrderAndQQOrder
    ; antitoneDependencyIsIntakeOrderDependency =
        refl
    ; symbolicGaugeRequiresRationalValue =
        true
    ; symbolicGaugeRequiresRationalValueIsTrue =
        refl
    ; symbolicGaugeRationalValueNotConstructedHere =
        false
    ; symbolicGaugeRationalValueNotConstructedHereIsFalse =
        refl
    ; antitoneRequiresRationalOrderAuthority =
        true
    ; antitoneRequiresRationalOrderAuthorityIsTrue =
        refl
    ; antitoneLemmaNotProvedHere =
        false
    ; antitoneLemmaNotProvedHereIsFalse =
        refl
    ; fullAgreementDistanceReceipt =
        λ x → prefixIdentityReceipt (canonicalMetricAuthorityReceipt len) x
    ; fullAgreementDepthReceipt =
        AM.agreeDepth-self
    ; naiveEqualityFailureReason =
        fullAgreementDistanceZeroButSymbolicGaugeRemainsThreeMinusDepth
    ; naiveEqualityFailureReasonIsFullAgreementZeroVsGauge =
        refl
    ; naiveEqualityFailureReading =
        "Naive d_QQ = 3^-agreeDepth is false at full agreement: dNat x x is 0, while the intake only records the symbolic rational gauge 3^-len and explicitly does not construct or prove that QQ value equal to zero."
    ; surrealGaugeAuthorityAccepted =
        false
    ; surrealGaugeAuthorityAcceptedIsFalse =
        refl
    }

record GaugeMonotoneLawShapeReceipt (len m k : Nat) : Set₁ where
  field
    rationalBridgeRow :
      CheckedRationalGaugeBridgeRow len m k

    rationalBridgeRowIsCanonical :
      rationalBridgeRow ≡ canonicalCheckedRationalGaugeBridgeRow len m k

    lawShapeName :
      String

    lawShapeNameIsGaugeMonotone :
      lawShapeName ≡ "gaugeMonotone"

    consumedAgreementDepthTriangle :
      (x y z : Vec Trit len) →
      (AM.agreeDepth x y ⊓ AM.agreeDepth y z) ≤ AM.agreeDepth x z

    consumedAgreementDepthTriangleIsCanonical :
      consumedAgreementDepthTriangle ≡ AM.agreeDepth-triangle

    consumedOrderedQQAntitone :
      Intake.AntitoneGaugeLemmaIntake m k

    consumedOrderedQQAntitoneIsCanonical :
      consumedOrderedQQAntitone ≡ Intake.canonicalAntitoneGaugeLemmaIntake m k

    consumedThreeMinusNAntitoneReceipt :
      ThreeMinusNAntitoneProofTermReceipt m k

    consumedThreeMinusNAntitoneReceiptIsCanonical :
      consumedThreeMinusNAntitoneReceipt
      ≡
      canonicalThreeMinusNAntitoneProofTermReceipt m k

    orderedQQAntitonePremiseShape :
      String

    orderedQQAntitonePremiseShapeIsIntakeField :
      orderedQQAntitonePremiseShape
      ≡
      Intake.AntitoneGaugeLemmaIntake.premiseShape consumedOrderedQQAntitone

    orderedQQAntitoneConclusionShape :
      String

    orderedQQAntitoneConclusionShapeIsIntakeField :
      orderedQQAntitoneConclusionShape
      ≡
      Intake.AntitoneGaugeLemmaIntake.conclusionShape consumedOrderedQQAntitone

    orderedQQAntitoneAuthorityRequired :
      Bool

    orderedQQAntitoneAuthorityRequiredIsIntakeField :
      orderedQQAntitoneAuthorityRequired
      ≡
      Intake.AntitoneGaugeLemmaIntake.rationalOrderAuthorityRequired
        consumedOrderedQQAntitone

    orderedQQAntitoneNotProvedHere :
      Bool

    orderedQQAntitoneNotProvedHereIsIntakeField :
      orderedQQAntitoneNotProvedHere
      ≡
      Intake.AntitoneGaugeLemmaIntake.antitoneLemmaProvedHere
        consumedOrderedQQAntitone

    gaugeMonotoneProofTerm :
      (x y z : Vec Trit len) →
      OQQ.qq-order
        (symbolicThreeMinusNQQ (AM.agreeDepth x z))
        (symbolicThreeMinusNQQ
          (AM.agreeDepth x y ⊓ AM.agreeDepth y z))

    gaugeMonotoneProofTermIsCanonical :
      gaugeMonotoneProofTerm ≡ symbolicGaugeMonotoneProofTerm

    lawShapeRecorded :
      Bool

    lawShapeRecordedIsTrue :
      lawShapeRecorded ≡ true

    lawShapePromoted :
      Bool

    lawShapePromotedIsFalse :
      lawShapePromoted ≡ false

    surrealGaugeAuthorityAccepted :
      Bool

    surrealGaugeAuthorityAcceptedIsFalse :
      surrealGaugeAuthorityAccepted ≡ false

open GaugeMonotoneLawShapeReceipt public

canonicalGaugeMonotoneLawShapeReceipt :
  ∀ len m k →
  GaugeMonotoneLawShapeReceipt len m k
canonicalGaugeMonotoneLawShapeReceipt len m k =
  record
    { rationalBridgeRow =
        canonicalCheckedRationalGaugeBridgeRow len m k
    ; rationalBridgeRowIsCanonical =
        refl
    ; lawShapeName =
        "gaugeMonotone"
    ; lawShapeNameIsGaugeMonotone =
        refl
    ; consumedAgreementDepthTriangle =
        AM.agreeDepth-triangle
    ; consumedAgreementDepthTriangleIsCanonical =
        refl
    ; consumedOrderedQQAntitone =
        Intake.canonicalAntitoneGaugeLemmaIntake m k
    ; consumedOrderedQQAntitoneIsCanonical =
        refl
    ; consumedThreeMinusNAntitoneReceipt =
        canonicalThreeMinusNAntitoneProofTermReceipt m k
    ; consumedThreeMinusNAntitoneReceiptIsCanonical =
        refl
    ; orderedQQAntitonePremiseShape =
        Intake.AntitoneGaugeLemmaIntake.premiseShape
          (Intake.canonicalAntitoneGaugeLemmaIntake m k)
    ; orderedQQAntitonePremiseShapeIsIntakeField =
        refl
    ; orderedQQAntitoneConclusionShape =
        Intake.AntitoneGaugeLemmaIntake.conclusionShape
          (Intake.canonicalAntitoneGaugeLemmaIntake m k)
    ; orderedQQAntitoneConclusionShapeIsIntakeField =
        refl
    ; orderedQQAntitoneAuthorityRequired =
        Intake.AntitoneGaugeLemmaIntake.rationalOrderAuthorityRequired
          (Intake.canonicalAntitoneGaugeLemmaIntake m k)
    ; orderedQQAntitoneAuthorityRequiredIsIntakeField =
        refl
    ; orderedQQAntitoneNotProvedHere =
        Intake.AntitoneGaugeLemmaIntake.antitoneLemmaProvedHere
          (Intake.canonicalAntitoneGaugeLemmaIntake m k)
    ; orderedQQAntitoneNotProvedHereIsIntakeField =
        refl
    ; gaugeMonotoneProofTerm =
        symbolicGaugeMonotoneProofTerm
    ; gaugeMonotoneProofTermIsCanonical =
        refl
    ; lawShapeRecorded =
        true
    ; lawShapeRecordedIsTrue =
        refl
    ; lawShapePromoted =
        false
    ; lawShapePromotedIsFalse =
        refl
    ; surrealGaugeAuthorityAccepted =
        false
    ; surrealGaugeAuthorityAcceptedIsFalse =
        refl
    }

record GaugeUltrametricInheritanceLawShapeReceipt (len m k : Nat) : Set₁ where
  field
    gaugeMonotone :
      GaugeMonotoneLawShapeReceipt len m k

    gaugeMonotoneIsCanonical :
      gaugeMonotone ≡ canonicalGaugeMonotoneLawShapeReceipt len m k

    lawShapeName :
      String

    lawShapeNameIsGaugeUltrametricInheritance :
      lawShapeName ≡ "gaugeUltrametricInheritance"

    metricReceipt :
      MetricAuthorityReceipt len

    metricReceiptIsCanonical :
      metricReceipt ≡ canonicalMetricAuthorityReceipt len

    consumedAgreementDepthTriangle :
      (x y z : Vec Trit len) →
      (AM.agreeDepth x y ⊓ AM.agreeDepth y z) ≤ AM.agreeDepth x z

    consumedAgreementDepthTriangleIsGaugeMonotoneField :
      consumedAgreementDepthTriangle
      ≡
      GaugeMonotoneLawShapeReceipt.consumedAgreementDepthTriangle gaugeMonotone

    consumedGaugeMonotoneProofTerm :
      (x y z : Vec Trit len) →
      OQQ.qq-order
        (symbolicThreeMinusNQQ (AM.agreeDepth x z))
        (symbolicThreeMinusNQQ
          (AM.agreeDepth x y ⊓ AM.agreeDepth y z))

    consumedGaugeMonotoneProofTermIsGaugeMonotoneField :
      consumedGaugeMonotoneProofTerm
      ≡
      GaugeMonotoneLawShapeReceipt.gaugeMonotoneProofTerm gaugeMonotone

    consumedPrefixUltratriangle :
      (x y z : Vec Trit len) →
      MetricAuthorityReceipt.prefixDistance metricReceipt x z
      ≤
      ( MetricAuthorityReceipt.prefixDistance metricReceipt x y
        ⊔
        MetricAuthorityReceipt.prefixDistance metricReceipt y z
      )

    consumedPrefixUltratriangleIsMetricField :
      consumedPrefixUltratriangle
      ≡
      MetricAuthorityReceipt.prefixUltraReceipt metricReceipt

    consumedOrderedQQAntitone :
      Intake.AntitoneGaugeLemmaIntake m k

    consumedOrderedQQAntitoneIsGaugeMonotoneField :
      consumedOrderedQQAntitone
      ≡
      GaugeMonotoneLawShapeReceipt.consumedOrderedQQAntitone gaugeMonotone

    gaugeUltrametricInheritanceProofTerm :
      (x y z : Vec Trit len) →
      OQQ.qq-order
        (symbolicThreeMinusNQQ (AM.agreeDepth x z))
        (symbolicThreeMinusNQQ
          (AM.agreeDepth x y ⊓ AM.agreeDepth y z))

    gaugeUltrametricInheritanceProofTermIsCanonical :
      gaugeUltrametricInheritanceProofTerm
      ≡
      symbolicGaugeUltrametricInheritanceProofTerm

    gaugeUltrametricTargetShape :
      String

    gaugeUltrametricTargetShapeIsInheritedMinBound :
      gaugeUltrametricTargetShape
      ≡
      "3^-agreeDepth(x,z) <= 3^-min(agreeDepth(x,y),agreeDepth(y,z)); max-gauge promotion remains external"

    lawShapeRecorded :
      Bool

    lawShapeRecordedIsTrue :
      lawShapeRecorded ≡ true

    lawShapePromoted :
      Bool

    lawShapePromotedIsFalse :
      lawShapePromoted ≡ false

    surrealGaugeAuthorityAccepted :
      Bool

    surrealGaugeAuthorityAcceptedIsFalse :
      surrealGaugeAuthorityAccepted ≡ false

open GaugeUltrametricInheritanceLawShapeReceipt public

canonicalGaugeUltrametricInheritanceLawShapeReceipt :
  ∀ len m k →
  GaugeUltrametricInheritanceLawShapeReceipt len m k
canonicalGaugeUltrametricInheritanceLawShapeReceipt len m k =
  record
    { gaugeMonotone =
        canonicalGaugeMonotoneLawShapeReceipt len m k
    ; gaugeMonotoneIsCanonical =
        refl
    ; lawShapeName =
        "gaugeUltrametricInheritance"
    ; lawShapeNameIsGaugeUltrametricInheritance =
        refl
    ; metricReceipt =
        canonicalMetricAuthorityReceipt len
    ; metricReceiptIsCanonical =
        refl
    ; consumedAgreementDepthTriangle =
        GaugeMonotoneLawShapeReceipt.consumedAgreementDepthTriangle
          (canonicalGaugeMonotoneLawShapeReceipt len m k)
    ; consumedAgreementDepthTriangleIsGaugeMonotoneField =
        refl
    ; consumedGaugeMonotoneProofTerm =
        GaugeMonotoneLawShapeReceipt.gaugeMonotoneProofTerm
          (canonicalGaugeMonotoneLawShapeReceipt len m k)
    ; consumedGaugeMonotoneProofTermIsGaugeMonotoneField =
        refl
    ; consumedPrefixUltratriangle =
        MetricAuthorityReceipt.prefixUltraReceipt
          (canonicalMetricAuthorityReceipt len)
    ; consumedPrefixUltratriangleIsMetricField =
        refl
    ; consumedOrderedQQAntitone =
        GaugeMonotoneLawShapeReceipt.consumedOrderedQQAntitone
          (canonicalGaugeMonotoneLawShapeReceipt len m k)
    ; consumedOrderedQQAntitoneIsGaugeMonotoneField =
        refl
    ; gaugeUltrametricInheritanceProofTerm =
        symbolicGaugeUltrametricInheritanceProofTerm
    ; gaugeUltrametricInheritanceProofTermIsCanonical =
        refl
    ; gaugeUltrametricTargetShape =
        "3^-agreeDepth(x,z) <= 3^-min(agreeDepth(x,y),agreeDepth(y,z)); max-gauge promotion remains external"
    ; gaugeUltrametricTargetShapeIsInheritedMinBound =
        refl
    ; lawShapeRecorded =
        true
    ; lawShapeRecordedIsTrue =
        refl
    ; lawShapePromoted =
        false
    ; lawShapePromotedIsFalse =
        refl
    ; surrealGaugeAuthorityAccepted =
        false
    ; surrealGaugeAuthorityAcceptedIsFalse =
        refl
    }

canonicalSurrealGaugeAuthorityStillFalse :
  ∀ {n : Nat} →
  surrealGaugeAuthorityAccepted (canonicalAgreementSurrealGaugeSlot n) ≡ false
canonicalSurrealGaugeAuthorityStillFalse = refl

canonicalSurrealMetricClaimStillFalse :
  ∀ {n : Nat} →
  surrealMetricClaimPromoted (canonicalAgreementSurrealGaugeSlot n) ≡ false
canonicalSurrealMetricClaimStillFalse = refl
