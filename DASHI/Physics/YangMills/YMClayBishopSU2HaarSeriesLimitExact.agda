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
import DASHI.Foundations.BishopConstructiveRealBridgeExact as Bridge

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
      Bridge.BishopAbsoluteSeriesConvergent (difference f)

  completedIntegral : (Sphere → B.ℝ) → B.ℝ
  completedIntegral f =
    Bridge.bishopSeriesLimit
      (difference f)
      (absoluteDyadicTelescope f)


  completedIntegralConvergence : ∀ f →
    Bridge.BishopConvergesTo
      (Seq.SeriesOf (difference f))
      (completedIntegral f)
  completedIntegralConvergence f =
    Bridge.bishopSeriesLimitConvergence
      (difference f)
      (absoluteDyadicTelescope f)

  completedIntegralUnique : ∀ f {candidate : B.ℝ} →
    Bridge.BishopConvergesTo
      (Seq.SeriesOf (difference f)) candidate →
    Bridge.BishopEquivalent (completedIntegral f) candidate
  completedIntegralUnique f candidateConverges =
    Bridge.bishopSeriesLimitUnique
      (difference f)
      (absoluteDyadicTelescope f)
      candidateConverges

open EffectiveHaarApproximation public
