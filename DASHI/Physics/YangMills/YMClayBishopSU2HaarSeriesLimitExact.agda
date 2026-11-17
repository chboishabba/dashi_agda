{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayBishopSU2HaarSeriesLimitExact where

-- YM.REAL: use the ACTUAL Murray/Csimma Bishop series limit, rather than
-- selecting an opaque real or postulating a limit functional.
--
-- This is the completed Cauchy-limit *consumer*. The effective sequence
-- and its absolute dyadic telescope certificate still need the concrete
-- b_n / Fejer finite cubature source. No Wilson/Haar closure is claimed.
--
-- Attribution: Bishop/Bridges, Murray/Csimma, original DASHI
-- BishopConstructiveRealBridgeExact, Fejer, Stroud, Wilson/Balaban.

open import Agda.Builtin.Nat using (Nat; zero; suc)
import Real as B
import Sequence as Seq
open import Data.Product.Base using (proj₂)
-- Direct pinned Bishop Sequence backend: intentionally bypasses the
-- legacy-real-axiom-importing BishopConstructiveRealBridgeExact.


record EffectiveHaarApproximation (Sphere : Set) : Set₁ where
  field
    -- Actual finite polynomial integral approximations, indexed by an
    -- effective dyadic schedule. This function has no arbitrary limit.
    finiteApproximation : (Sphere → B.ℝ) → Nat → B.ℝ

  difference : (Sphere → B.ℝ) → Nat → B.ℝ
  difference f zero = finiteApproximation f zero
  difference f (suc n) =
    B._-_ (finiteApproximation f (suc n))
           (finiteApproximation f n)

  field
    -- Concrete source obligation: from the already developed b_n bound,
    -- prove the dyadic series of successive differences absolutely
    -- converges. This must NOT be treated as a free Haar integral law.
    absoluteDyadicTelescope : ∀ f →
      Seq.SeriesOf_ConvergesAbsolutely (difference f)

  completedIntegral : (Sphere → B.ℝ) → B.ℝ
  completedIntegral f =
    Seq.lim
      (Seq.absolute⇒isConvergent (absoluteDyadicTelescope f))


  completedIntegralConvergence : ∀ f →
    Seq._ConvergesTo_
      (Seq.SeriesOf (difference f))
      (completedIntegral f)
  completedIntegralConvergence f =
    proj₂ (Seq.absolute⇒isConvergent (absoluteDyadicTelescope f))

  completedIntegralUnique : ∀ f {candidate : B.ℝ} →
    Seq._ConvergesTo_
      (Seq.SeriesOf (difference f)) candidate →
    B._≃_ (completedIntegral f) candidate
  completedIntegralUnique f candidateConverges =
    Seq.uniqueness-of-limits
      (completedIntegralConvergence f)
      candidateConverges

open EffectiveHaarApproximation public
