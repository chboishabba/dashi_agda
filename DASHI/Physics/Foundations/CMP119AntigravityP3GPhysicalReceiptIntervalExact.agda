{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityP3GPhysicalReceiptIntervalExact where

open import Agda.Builtin.Nat using (Nat; suc)
import Real as Bishop
import RealProperties as BishopP

import DASHI.Physics.Foundations.CMP119AntigravityP3GSetoidPhysicalCoreExact as Core
import DASHI.Physics.Foundations.CMP119AntigravityCMP109TrajectoryPlaquetteConstructorExact as Constructor
import DASHI.Physics.Foundations.CMP119AntigravitySourceHistoryBishopUVViewExact as UV
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinBoxReceiptFamilyExact as Rich
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinIntegralCertificateExact as Integral
import DASHI.Physics.YangMills.BalabanYM4LiteralPlaquetteBetaEstimateExact as Literal

------------------------------------------------------------------------
-- Quantitative interval for the literal positive-edge P3G remainder.
-- Rich provides actual lower/upper REGULAR-box receipt sums. The interaction
-- needs genuinely signed bounds; a one-sided quartic estimate alone does not
-- supply the lower bound. Do not replace it with |R| <= |R|.
------------------------------------------------------------------------

record PhysicalReceiptOrderAndInteractionInterval
    {trajectory weld rich}
    (geometry : Core.P3GSetoidPhysicalGeometry
      {trajectory = trajectory} weld rich) : Set₁ where
  field
    richLessEqualIsBishopOrder :
      ∀ left right →
      Rich.LessEqual rich left right →
      Bishop._≤_ left right

    interactionLower interactionUpper : Nat → Bishop.ℝ

    interactionLowerCorrect : ∀ k →
      Bishop._≤_
        (interactionLower k)
        (UV.embed (Literal.literalBetaInt
          (Constructor.asPhysicalRunningCouplingData weld) k))

    interactionUpperCorrect : ∀ k →
      Bishop._≤_
        (UV.embed (Literal.literalBetaInt
          (Constructor.asPhysicalRunningCouplingData weld) k))
        (interactionUpper k)

open PhysicalReceiptOrderAndInteractionInterval public

regularLower :
  ∀ {trajectory weld rich} →
  Core.P3GSetoidPhysicalGeometry {trajectory = trajectory} weld rich →
  Nat → Bishop.ℝ
regularLower {rich = rich} geometry k =
  Rich.rational rich
    (Integral.boxLowerSum
      (Rich.regularBoxReceipts (Rich.partition rich k)))

regularUpper :
  ∀ {trajectory weld rich} →
  Core.P3GSetoidPhysicalGeometry {trajectory = trajectory} weld rich →
  Nat → Bishop.ℝ
regularUpper {rich = rich} geometry k =
  Rich.rational rich
    (Integral.boxUpperSum
      (Rich.regularBoxReceipts (Rich.partition rich k)))

positiveEdgePhysicalLower :
  ∀ {trajectory weld rich}
    {geometry : Core.P3GSetoidPhysicalGeometry
      {trajectory = trajectory} weld rich} →
  PhysicalReceiptOrderAndInteractionInterval geometry →
  Nat → Bishop.ℝ
positiveEdgePhysicalLower {geometry = geometry} receipt k =
  Bishop._+_ (regularLower geometry k) (interactionLower receipt k)

positiveEdgePhysicalUpper :
  ∀ {trajectory weld rich}
    {geometry : Core.P3GSetoidPhysicalGeometry
      {trajectory = trajectory} weld rich} →
  PhysicalReceiptOrderAndInteractionInterval geometry →
  Nat → Bishop.ℝ
positiveEdgePhysicalUpper {geometry = geometry} receipt k =
  Bishop._+_ (regularUpper geometry k) (interactionUpper receipt k)

positiveEdgeLowerBound :
  ∀ {trajectory weld rich}
    {geometry : Core.P3GSetoidPhysicalGeometry
      {trajectory = trajectory} weld rich}
    (receipt : PhysicalReceiptOrderAndInteractionInterval geometry)
    k →
  Bishop._≤_
    (positiveEdgePhysicalLower receipt k)
    (Core.physicalRemainder geometry (suc k))
positiveEdgeLowerBound {rich = rich} {geometry = geometry} receipt k =
  BishopP.≤-respʳ-≃
    (BishopP.≃-symm
      (Core.richAddIsBishopAdd geometry
        (Rich.regularRemainder rich k)
        (UV.embed (Literal.literalBetaInt
          (Constructor.asPhysicalRunningCouplingData _ ) k))))
    (BishopP.+-mono-≤
      (richLessEqualIsBishopOrder receipt _ _
        (Rich.regularRemainderBetweenReceiptSums rich k))
      (interactionLowerCorrect receipt k))

positiveEdgeUpperBound :
  ∀ {trajectory weld rich}
    {geometry : Core.P3GSetoidPhysicalGeometry
      {trajectory = trajectory} weld rich}
    (receipt : PhysicalReceiptOrderAndInteractionInterval geometry)
    k →
  Bishop._≤_
    (Core.physicalRemainder geometry (suc k))
    (positiveEdgePhysicalUpper receipt k)
positiveEdgeUpperBound {rich = rich} {geometry = geometry} receipt k =
  BishopP.≤-respˡ-≃
    (Core.richAddIsBishopAdd geometry
      (Rich.regularRemainder rich k)
      (UV.embed (Literal.literalBetaInt
        (Constructor.asPhysicalRunningCouplingData _) k)))
    (BishopP.+-mono-≤
      (richLessEqualIsBishopOrder receipt _ _
        (Rich.regularRemainderBelowReceiptSum rich k))
      (interactionUpperCorrect receipt k))
