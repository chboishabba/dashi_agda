{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityP3GPhysicalSignedQuarticReceiptExact where

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _*_; -_)
import Real as Bishop

import DASHI.Physics.Closure.NSTriadKNMurrayBishopDirectCanonicalCarrier as Carrier
import DASHI.Physics.Foundations.CMP119AntigravityP3GSetoidPhysicalCoreExact as Core
import DASHI.Physics.Foundations.CMP119AntigravityP3GPhysicalReceiptIntervalExact as Interval
import DASHI.Physics.Foundations.CMP119AntigravityCMP109TrajectoryPlaquetteConstructorExact as Constructor
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinBoxReceiptFamilyExact as Rich
import DASHI.Physics.YangMills.BalabanYM4LiteralPlaquetteBetaEstimateExact as Literal
import DASHI.Physics.YangMills.BalabanYM4FiniteLatticeBetaEstimateExact as Estimate
import DASHI.Physics.YangMills.BalabanP33PrimitiveAbsoluteOperatorAdapterExact as Absolute
import DASHI.Physics.YangMills.BalabanP33PrimitiveOperatorNormLocalBoundsExact as TwoSided

------------------------------------------------------------------------
-- ACTUAL SIGNED quartic receipt, not only the positive interaction bound.
-- The literal finite beta certificate already supplies |beta_int| <= C*g^4.
-- Reuse the existing rational two-sided absolute-to-order compiler, then
-- transport each endpoint by the Murray/Bishop ordered embedding.
------------------------------------------------------------------------

record PhysicalSignedQuarticSource
    {trajectory weld rich}
    (geometry : Core.P3GSetoidPhysicalGeometry
      {trajectory = trajectory} weld rich) : Set₁ where
  field
    richOrderSound :
      ∀ left right →
      Rich.LessEqual rich left right →
      Bishop._≤_ left right

    certificate :
      ∀ k →
      Literal.LiteralFiniteBetaCertificate
        (Constructor.asPhysicalRunningCouplingData weld) k

open PhysicalSignedQuarticSource public

quarticBudget :
  ∀ {trajectory weld rich}
    {geometry : Core.P3GSetoidPhysicalGeometry
      {trajectory = trajectory} weld rich} →
  PhysicalSignedQuarticSource geometry → Nat → ℚ
quarticBudget source k =
  Literal.interactionConstant (certificate source k)
    * Estimate.fourthPower (Literal.coupling (certificate source k))

signedInteraction :
  ∀ {trajectory weld rich}
    {geometry : Core.P3GSetoidPhysicalGeometry
      {trajectory = trajectory} weld rich}
    (source : PhysicalSignedQuarticSource geometry)
    k →
  TwoSided.TwoSided
    (Literal.literalBetaInt
      (Constructor.asPhysicalRunningCouplingData weld) k)
    (quarticBudget source k)
signedInteraction {weld = weld} source k =
  Absolute.operatorNormDominatesCoordinate
    (Literal.literalBetaInt
      (Constructor.asPhysicalRunningCouplingData weld) k)
    (quarticBudget source k)
    (Literal.signedQuarticRemainder (certificate source k))

asPhysicalReceiptInterval :
  ∀ {trajectory weld rich}
    {geometry : Core.P3GSetoidPhysicalGeometry
      {trajectory = trajectory} weld rich} →
  PhysicalSignedQuarticSource geometry →
  Interval.PhysicalReceiptOrderAndInteractionInterval geometry
asPhysicalReceiptInterval {weld = weld} source = record
  { Interval.PhysicalReceiptOrderAndInteractionInterval.richLessEqualIsBishopOrder =
      richOrderSound source
  ; Interval.PhysicalReceiptOrderAndInteractionInterval.interactionLower =
      λ k → Carrier.bishopRationalEmbed (- quarticBudget source k)
  ; Interval.PhysicalReceiptOrderAndInteractionInterval.interactionUpper =
      λ k → Carrier.bishopRationalEmbed (quarticBudget source k)
  ; Interval.PhysicalReceiptOrderAndInteractionInterval.interactionLowerCorrect =
      λ k → Carrier.bishopEmbedOrder
        (TwoSided.lower (signedInteraction source k))
  ; Interval.PhysicalReceiptOrderAndInteractionInterval.interactionUpperCorrect =
      λ k → Carrier.bishopEmbedOrder
        (TwoSided.upper (signedInteraction source k))
  }
