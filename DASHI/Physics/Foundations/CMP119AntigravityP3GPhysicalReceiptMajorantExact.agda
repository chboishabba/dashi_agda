{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityP3GPhysicalReceiptMajorantExact where

open import Agda.Builtin.Nat using (Nat; zero; suc)
import Real as Bishop
import RealProperties as BishopP

import DASHI.Analysis.MurrayBishopSetoidBackend as Backend
import DASHI.Physics.Foundations.CMP119AntigravityP3GSetoidPhysicalCoreExact as Core
import DASHI.Physics.Foundations.CMP119AntigravityP3GSetoidRunningRecursionExact as Running
import DASHI.Physics.Foundations.CMP119AntigravityP3GPhysicalReceiptIntervalExact as Interval
import DASHI.Physics.Foundations.CMP119AntigravityP3GPhysicalSignedQuarticReceiptExact as Signed

------------------------------------------------------------------------
-- Explicit non-tautological quantitative remainder majorant:
--
--   L_k = actual regular-box lower receipt - C_k g_k^4
--   U_k = actual regular-box upper receipt + C_k g_k^4
--   M_(k+1) = |L_k| + |U_k|
--
-- M depends ONLY on certified external enclosures, never on |R_(k+1)|.
-- This proves -M <= R <= M; sharpness or scale-uniform smallness of M is a
-- separate analytical matter, not fabricated from the interval theorem.
------------------------------------------------------------------------

physicalReceiptMajorant :
  ∀ {trajectory weld rich}
    {geometry : Core.P3GSetoidPhysicalGeometry
      {trajectory = trajectory} weld rich} →
  Signed.PhysicalSignedQuarticSource geometry →
  Nat → Bishop.ℝ
physicalReceiptMajorant source zero = Bishop.∣_∣ Bishop.0ℝ
physicalReceiptMajorant source (suc k) =
  let interval = Signed.asPhysicalReceiptInterval source in
  Bishop._+_
    (Bishop.∣_∣ (Interval.positiveEdgePhysicalLower interval k))
    (Bishop.∣_∣ (Interval.positiveEdgePhysicalUpper interval k))

nonnegativeMajorant :
  ∀ {trajectory weld rich}
    {geometry : Core.P3GSetoidPhysicalGeometry
      {trajectory = trajectory} weld rich}
    (source : Signed.PhysicalSignedQuarticSource geometry)
    n →
  Bishop._≤_ Bishop.0ℝ (physicalReceiptMajorant source n)
nonnegativeMajorant source zero = BishopP.0≤∣x∣
nonnegativeMajorant source (suc k) =
  BishopP.≤-respˡ-≃
    (BishopP.≃-symm (BishopP.+-identityʳ Bishop.0ℝ))
    (BishopP.+-mono-≤ BishopP.0≤∣x∣ BishopP.0≤∣x∣)

absoluteLowerBelowMajorant :
  ∀ {trajectory weld rich}
    {geometry : Core.P3GSetoidPhysicalGeometry
      {trajectory = trajectory} weld rich}
    (source : Signed.PhysicalSignedQuarticSource geometry)
    k →
  Bishop._≤_
    (Bishop.∣_∣
      (Interval.positiveEdgePhysicalLower
        (Signed.asPhysicalReceiptInterval source) k))
    (physicalReceiptMajorant source (suc k))
absoluteLowerBelowMajorant source k =
  BishopP.≤-respˡ-≃
    (BishopP.≃-symm
      (BishopP.+-identityʳ
        (Bishop.∣_∣ (Interval.positiveEdgePhysicalLower
          (Signed.asPhysicalReceiptInterval source) k))))
    (BishopP.+-mono-≤ BishopP.≤-refl BishopP.0≤∣x∣)

absoluteUpperBelowMajorant :
  ∀ {trajectory weld rich}
    {geometry : Core.P3GSetoidPhysicalGeometry
      {trajectory = trajectory} weld rich}
    (source : Signed.PhysicalSignedQuarticSource geometry)
    k →
  Bishop._≤_
    (Bishop.∣_∣
      (Interval.positiveEdgePhysicalUpper
        (Signed.asPhysicalReceiptInterval source) k))
    (physicalReceiptMajorant source (suc k))
absoluteUpperBelowMajorant source k =
  BishopP.≤-respˡ-≃
    (BishopP.≃-symm
      (BishopP.+-identityˡ
        (Bishop.∣_∣ (Interval.positiveEdgePhysicalUpper
          (Signed.asPhysicalReceiptInterval source) k))))
    (BishopP.+-mono-≤ BishopP.0≤∣x∣ BishopP.≤-refl)

lowerBound :
  ∀ {trajectory weld rich}
    {geometry : Core.P3GSetoidPhysicalGeometry
      {trajectory = trajectory} weld rich}
    (source : Signed.PhysicalSignedQuarticSource geometry)
    n →
  Bishop._≤_
    (Bishop.-_ (physicalReceiptMajorant source n))
    (Core.physicalRemainder geometry n)
lowerBound source zero =
  Backend.negativeAbsoluteBelow Bishop.0ℝ
lowerBound source (suc k) =
  let interval = Signed.asPhysicalReceiptInterval source in
  BishopP.≤-trans
    (BishopP.neg-mono-≤
      (absoluteLowerBelowMajorant source k))
    (BishopP.≤-trans
      (Backend.negativeAbsoluteBelow
        (Interval.positiveEdgePhysicalLower interval k))
      (Interval.positiveEdgeLowerBound interval k))

upperBound :
  ∀ {trajectory weld rich}
    {geometry : Core.P3GSetoidPhysicalGeometry
      {trajectory = trajectory} weld rich}
    (source : Signed.PhysicalSignedQuarticSource geometry)
    n →
  Bishop._≤_
    (Core.physicalRemainder geometry n)
    (physicalReceiptMajorant source n)
upperBound source zero = BishopP.x≤∣x∣
upperBound source (suc k) =
  let interval = Signed.asPhysicalReceiptInterval source in
  BishopP.≤-trans
    (Interval.positiveEdgeUpperBound interval k)
    (BishopP.≤-trans
      BishopP.x≤∣x∣
      (absoluteUpperBelowMajorant source k))

asPhysicalRemainderMajorant :
  ∀ {trajectory weld rich}
    {geometry : Core.P3GSetoidPhysicalGeometry
      {trajectory = trajectory} weld rich}
    (source : Signed.PhysicalSignedQuarticSource geometry) →
  Running.PhysicalRemainderMajorant
    (Running.fromPhysicalCore geometry)
    (physicalReceiptMajorant source)
asPhysicalRemainderMajorant source = record
  { Running.PhysicalRemainderMajorant.majorantNonnegative =
      nonnegativeMajorant source
  ; Running.PhysicalRemainderMajorant.controlledLower =
      lowerBound source
  ; Running.PhysicalRemainderMajorant.controlledUpper =
      upperBound source
  }
