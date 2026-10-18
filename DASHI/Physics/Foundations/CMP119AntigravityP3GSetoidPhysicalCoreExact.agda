{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityP3GSetoidPhysicalCoreExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

import Real as Bishop
import RealProperties as BishopP

import DASHI.Physics.Closure.NSTriadKNMurrayBishopDirectCanonicalCarrier as Carrier
import DASHI.Physics.Foundations.CMP119AntigravityCMP109TrajectoryPlaquetteConstructorExact as Constructor
import DASHI.Physics.Foundations.CMP119AntigravityP3UVAnchorFromSharedCouplingExact as UVAnchor
import DASHI.Physics.Foundations.CMP119AntigravityRichBrillouinRationalGaussianProjectionExact as Projection
import DASHI.Physics.Foundations.CMP119AntigravitySourceHistoryBishopUVViewExact as UV
import DASHI.Physics.YangMills.Balaban1989BetaSplitInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinBoxReceiptFamilyExact as Rich
import DASHI.Physics.YangMills.BalabanYM4LiteralPlaquetteBetaEstimateExact as Literal
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- SETOID-NATIVE P3G PHYSICAL CORE
--
-- The legacy P3 RunningCouplingRecursion asks for Agda propositional equality
-- between Bishop reals.  The vendored Bishop carrier intentionally exposes
-- its field laws through the extensional setoid _≃_.  Do not strengthen that
-- boundary merely to populate the legacy record.
--
-- This module constructs the actual physical P3G state and one-step split
-- directly from the two already-coherent source objects:
--
--   * CMP109 supplies the node-indexed inverse-coupling history u_k;
--   * the rich/literal T4 coefficient supplies the edge decomposition.
--
-- Hence no cross-edge nextInverseCouplingSq/inverseCouplingSq weld is needed.
------------------------------------------------------------------------

record P3GSetoidPhysicalGeometry
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    (weld : Constructor.CMP109LiteralPlaquetteCoefficientWeld trajectory)
    (rich : Rich.LiteralBrillouinIntegralPhysicalData Nat Bishop.ℝ) : Set₁ where
  field
    richAddIsBishopAdd :
      ∀ left right →
      Bishop._≃_
        (Rich.add rich left right)
        (Bishop._+_ left right)

    gaussianProjection :
      Projection.RichBrillouinRationalGaussianProjection
        (Constructor.asPhysicalRunningCouplingData weld)
        rich

open P3GSetoidPhysicalGeometry public

physicalState :
  Flow.SourceNormalizedCouplingTrajectory → Nat → Bishop.ℝ
physicalState = UV.uvInverseCoupling

physicalBetaLog :
  ∀ {trajectory}
    {weld : Constructor.CMP109LiteralPlaquetteCoefficientWeld trajectory}
    {rich : Rich.LiteralBrillouinIntegralPhysicalData Nat Bishop.ℝ} →
  P3GSetoidPhysicalGeometry weld rich →
  Nat → Bishop.ℝ
physicalBetaLog geometry zero = Bishop.0ℝ
physicalBetaLog {rich = rich} geometry (suc depth) =
  Rich.scalarIntegral rich depth

physicalRemainder :
  ∀ {trajectory}
    {weld : Constructor.CMP109LiteralPlaquetteCoefficientWeld trajectory}
    {rich : Rich.LiteralBrillouinIntegralPhysicalData Nat Bishop.ℝ} →
  P3GSetoidPhysicalGeometry weld rich →
  Nat → Bishop.ℝ
physicalRemainder geometry zero = Bishop.0ℝ
physicalRemainder {weld = weld} {rich = rich} geometry (suc depth) =
  Rich.add rich
    (Rich.regularRemainder rich depth)
    (UV.embed
      (Literal.literalBetaInt
        (Constructor.asPhysicalRunningCouplingData weld)
        depth))

physicalTotalIncrement :
  ∀ {trajectory}
    {weld : Constructor.CMP109LiteralPlaquetteCoefficientWeld trajectory}
    {rich : Rich.LiteralBrillouinIntegralPhysicalData Nat Bishop.ℝ} →
  P3GSetoidPhysicalGeometry weld rich →
  Nat → Bishop.ℝ
physicalTotalIncrement geometry depth =
  Bishop._+_
    (physicalBetaLog geometry depth)
    (physicalRemainder geometry depth)

equalityAsBishopSetoid :
  ∀ {left right : Bishop.ℝ} →
  left ≡ right → Bishop._≃_ left right
equalityAsBishopSetoid {left} equality =
  subst (λ selected → Bishop._≃_ left selected) equality BishopP.≃-refl

richCoefficientAsShellPlusRegular :
  ∀ {trajectory weld rich}
    (geometry : P3GSetoidPhysicalGeometry
      {trajectory = trajectory} weld rich)
    depth →
  Bishop._≃_
    (Bishop._+_
      (Rich.scalarIntegral rich depth)
      (Rich.regularRemainder rich depth))
    (Rich.coefficient rich depth)
richCoefficientAsShellPlusRegular {rich = rich} geometry depth =
  BishopP.≃-trans
    (BishopP.≃-symm
      (richAddIsBishopAdd geometry
        (Rich.scalarIntegral rich depth)
        (Rich.regularRemainder rich depth)))
    (BishopP.≃-symm
      (equalityAsBishopSetoid
        (Rich.coefficientDefinition rich depth)))

positiveEdgeRemainderIsPhysicalByConstruction :
  ∀ {trajectory weld rich}
    (geometry : P3GSetoidPhysicalGeometry
      {trajectory = trajectory} weld rich)
    depth →
  Bishop._≃_
    (physicalRemainder geometry (suc depth))
    (Rich.add rich
      (Rich.regularRemainder rich depth)
      (UV.embed
        (Literal.literalBetaInt
          (Constructor.asPhysicalRunningCouplingData weld)
          depth)))
positiveEdgeRemainderIsPhysicalByConstruction geometry depth =
  BishopP.≃-refl

positiveEdgeTotalIncrementSameLiteral :
  ∀ {trajectory weld rich}
    (geometry : P3GSetoidPhysicalGeometry
      {trajectory = trajectory} weld rich)
    depth →
  Bishop._≃_
    (physicalTotalIncrement geometry (suc depth))
    (UV.embed
      (Literal.literalBetaStep
        (Constructor.asPhysicalRunningCouplingData weld)
        depth))
positiveEdgeTotalIncrementSameLiteral
    {weld = weld} {rich = rich} geometry depth =
  BishopP.≃-trans
    (BishopP.+-cong
      BishopP.≃-refl
      (richAddIsBishopAdd geometry
        (Rich.regularRemainder rich depth)
        (UV.embed
          (Literal.literalBetaInt
            (Constructor.asPhysicalRunningCouplingData weld)
            depth))))
    (BishopP.≃-trans
      (BishopP.≃-symm
        (BishopP.+-assoc
          (Rich.scalarIntegral rich depth)
          (Rich.regularRemainder rich depth)
          (UV.embed
            (Literal.literalBetaInt
              (Constructor.asPhysicalRunningCouplingData weld)
              depth))))
      (BishopP.≃-trans
        (BishopP.+-cong
          (richCoefficientAsShellPlusRegular geometry depth)
          BishopP.≃-refl)
        (BishopP.≃-trans
          (BishopP.+-cong
            (Projection.coefficientSameLiteralGaussian
              (gaussianProjection geometry)
              depth)
            BishopP.≃-refl)
          (BishopP.≃-symm
            (Carrier.bishopEmbedAdd
              (Literal.literalBetaZ
                (Constructor.asPhysicalRunningCouplingData weld)
                depth)
              (Literal.literalBetaInt
                (Constructor.asPhysicalRunningCouplingData weld)
                depth))))))

positiveEdgeTotalIncrementSameSource :
  ∀ {trajectory weld rich}
    (geometry : P3GSetoidPhysicalGeometry
      {trajectory = trajectory} weld rich)
    depth →
  Bishop._≃_
    (physicalTotalIncrement geometry (suc depth))
    (UV.embed (Flow.beta trajectory (suc depth)))
positiveEdgeTotalIncrementSameSource
    {weld = weld} geometry depth =
  BishopP.≃-trans
    (positiveEdgeTotalIncrementSameLiteral geometry depth)
    (equalityAsBishopSetoid
      (cong UV.embed
        (Constructor.constructedLiteralBetaIsSourceBeta weld depth)))

zeroTotalIncrementIsZero :
  ∀ {trajectory weld rich}
    (geometry : P3GSetoidPhysicalGeometry
      {trajectory = trajectory} weld rich) →
  Bishop._≃_ (physicalTotalIncrement geometry zero) Bishop.0ℝ
zeroTotalIncrementIsZero geometry =
  BishopP.≃-trans
    (BishopP.+-cong BishopP.≃-refl BishopP.≃-refl)
    (BishopP.+-identityʳ Bishop.0ℝ)

physicalRecurrenceSetoid :
  ∀ {trajectory weld rich}
    (geometry : P3GSetoidPhysicalGeometry
      {trajectory = trajectory} weld rich)
    depth →
  Bishop._≃_
    (physicalState trajectory (UV.uvNext depth))
    (Bishop._+_
      (physicalState trajectory depth)
      (physicalTotalIncrement geometry depth))
physicalRecurrenceSetoid {trajectory} geometry zero =
  BishopP.≃-trans
    (UV.uvRecurrenceSetoid trajectory zero)
    (BishopP.+-cong
      BishopP.≃-refl
      (BishopP.≃-symm (zeroTotalIncrementIsZero geometry)))
physicalRecurrenceSetoid {trajectory} geometry (suc depth) =
  BishopP.≃-trans
    (UV.uvRecurrenceSetoid trajectory (suc depth))
    (BishopP.+-cong
      BishopP.≃-refl
      (BishopP.≃-symm
        (positiveEdgeTotalIncrementSameSource geometry depth)))

initialInverseSquareUsesSameCouplingByConstruction :
  ∀ {trajectory split}
    (history : History.BetaSplitInverseSquareTerminalHistoryData
      trajectory split) →
  Bishop._≃_
    (Bishop._*_
      (physicalState trajectory zero)
      (UVAnchor.square
        (UV.embed (History.couplingAt history zero))))
    Bishop.1ℝ
initialInverseSquareUsesSameCouplingByConstruction =
  UVAnchor.embeddedSourceInverseCancelsCouplingSquare

directInitialSharedCouplingPaymentRequired : Bool
directInitialSharedCouplingPaymentRequired = false

directLocalRemainderSameObjectPaymentRequired : Bool
directLocalRemainderSameObjectPaymentRequired = false

crossEdgeT4StateCoherenceRequired : Bool
crossEdgeT4StateCoherenceRequired = false

legacyP3PropositionalEqualityRealizationStillRequired : Bool
legacyP3PropositionalEqualityRealizationStillRequired = true

directInitialSharedCouplingPaymentRequiredIsFalse :
  directInitialSharedCouplingPaymentRequired ≡ false
directInitialSharedCouplingPaymentRequiredIsFalse = refl

directLocalRemainderSameObjectPaymentRequiredIsFalse :
  directLocalRemainderSameObjectPaymentRequired ≡ false
directLocalRemainderSameObjectPaymentRequiredIsFalse = refl

crossEdgeT4StateCoherenceRequiredIsFalse :
  crossEdgeT4StateCoherenceRequired ≡ false
crossEdgeT4StateCoherenceRequiredIsFalse = refl

legacyP3PropositionalEqualityRealizationStillRequiredIsTrue :
  legacyP3PropositionalEqualityRealizationStillRequired ≡ true
legacyP3PropositionalEqualityRealizationStillRequiredIsTrue = refl

p3GSetoidPhysicalCoreCompilerLevel : ProofLevel
p3GSetoidPhysicalCoreCompilerLevel = machineChecked

p3GLegacyRunningCouplingRealizationLevel : ProofLevel
p3GLegacyRunningCouplingRealizationLevel = conditional
