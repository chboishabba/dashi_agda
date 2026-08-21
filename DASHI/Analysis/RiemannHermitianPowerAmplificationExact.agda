module DASHI.Analysis.RiemannHermitianPowerAmplificationExact where

------------------------------------------------------------------------
-- PURPOSE / AUTHORITY BOUNDARY
--
-- Exact finite algebra for one possible way to beat the nonzero second-moment
-- error floor identified in `RiemannHermitianDetectabilityGapExact`.
--
-- Analytic calibration:
-- Levent Alpöge and Ralph Furman,
-- "More than two thirds of the zeta zeros are simple and on the critical line",
-- arXiv:2608.13637 (2026), DOI: 10.48550/arXiv.2608.13637.
--
-- If a reflection pair has a Hermitian channel H=C+delta with delta>0, then
-- positive tensor / higher-moment powers amplify the separation.  We construct
-- the exact residual D_n satisfying
--
--   (C + suc(delta))^n = C^n + D_n.
--
-- This module proves that decomposition for every n.  It does NOT claim that
-- the current zeta prime-side machinery controls tr(G^n) for arbitrary n, nor
-- that the analytic Hermitian channel is literally a scalar power.  Those are
-- separate source-facing producer obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)

pow : Nat → Nat → Nat
pow x zero = 1
pow x (suc n) = x * pow x n

-- D_0 = 0,
-- D_{n+1} = C D_n + delta (C^n + D_n), with delta represented as suc d.
powerGap : Nat → Nat → Nat → Nat
powerGap C d zero = zero
powerGap C d (suc n) =
  C * powerGap C d n
  + suc d * (pow C n + powerGap C d n)

------------------------------------------------------------------------
-- Exact all-level expansion.
------------------------------------------------------------------------

powerGapDecomposition :
  (C d n : Nat) →
  pow (C + suc d) n ≡ pow C n + powerGap C d n
powerGapDecomposition C d zero = refl
powerGapDecomposition C d (suc n)
  rewrite powerGapDecomposition C d n =
  solve 4
    (λ C delta p g →
      (C :+ delta) :* (p :+ g)
      :=
      (C :* p) :+
      ((C :* g) :+ (delta :* (p :+ g))))
    refl
    C (suc d) (pow C n) (powerGap C d n)

------------------------------------------------------------------------
-- First levels make the amplification visible without any analytic input.
------------------------------------------------------------------------

unitGapLevel1 :
  pow (1 + suc 0) 1 ≡ pow 1 1 + 1
unitGapLevel1 = refl

unitGapLevel2 :
  pow (1 + suc 0) 2 ≡ pow 1 2 + 3
unitGapLevel2 = refl

unitGapLevel3 :
  pow (1 + suc 0) 3 ≡ pow 1 3 + 7
unitGapLevel3 = refl

unitGapLevel4 :
  pow (1 + suc 0) 4 ≡ pow 1 4 + 15
unitGapLevel4 = refl

unitGapResidualLevel1 : powerGap 1 0 1 ≡ 1
unitGapResidualLevel1 = refl

unitGapResidualLevel2 : powerGap 1 0 2 ≡ 3
unitGapResidualLevel2 = refl

unitGapResidualLevel3 : powerGap 1 0 3 ≡ 7
unitGapResidualLevel3 = refl

unitGapResidualLevel4 : powerGap 1 0 4 ≡ 15
unitGapResidualLevel4 = refl

------------------------------------------------------------------------
-- Certificate surface for analytic instantiation.
------------------------------------------------------------------------

record PowerAmplificationCertificate : Set where
  constructor powerAmplificationCertificate
  field
    baseline : Nat
    positiveGapPredecessor : Nat
    level : Nat
    amplified : Nat
    residual : Nat
    amplifiedIsPower :
      amplified ≡ pow (baseline + suc positiveGapPredecessor) level
    residualIsCanonicalGap :
      residual ≡ powerGap baseline positiveGapPredecessor level
    residualDecomposition :
      amplified ≡ pow baseline level + residual

canonicalPowerAmplificationCertificate :
  (C d n : Nat) → PowerAmplificationCertificate
canonicalPowerAmplificationCertificate C d n = record
  { baseline = C
  ; positiveGapPredecessor = d
  ; level = n
  ; amplified = pow (C + suc d) n
  ; residual = powerGap C d n
  ; amplifiedIsPower = refl
  ; residualIsCanonicalGap = refl
  ; residualDecomposition = powerGapDecomposition C d n
  }

------------------------------------------------------------------------
-- Source-facing boundary.
------------------------------------------------------------------------

record HigherMomentArithmeticControl : Set₁ where
  field
    MomentLevel : Set
    arithmeticMainTerm : MomentLevel → Nat
    arithmeticErrorBudget : MomentLevel → Nat
    hermitianAmplifiedDefect : MomentLevel → Nat

record HermitianPowerAmplificationBoundary : Set where
  field
    allLevelScalarPowerDecompositionProved : Bool
    concreteNonlinearGrowthChecksConstructed : Bool
    analyticHermitianPowerIdentificationProvedHere : Bool
    primeSideHigherTraceControlProvedHere : Bool
    rhDetectabilityViaAmplificationProvedHere : Bool

hermitianPowerAmplificationBoundary : HermitianPowerAmplificationBoundary
hermitianPowerAmplificationBoundary = record
  { allLevelScalarPowerDecompositionProved = true
  ; concreteNonlinearGrowthChecksConstructed = true
  ; analyticHermitianPowerIdentificationProvedHere = false
  ; primeSideHigherTraceControlProvedHere = false
  ; rhDetectabilityViaAmplificationProvedHere = false
  }
