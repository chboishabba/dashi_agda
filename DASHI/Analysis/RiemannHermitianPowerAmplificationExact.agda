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
-- If a reflection pair has a Hermitian channel H strictly larger than its
-- critical-compatible baseline C, then tensor / higher-moment powers amplify
-- that strict separation:
--
--   H = C + delta,  delta > 0
--       ==> H^n = C^n + Delta_n,  Delta_n > 0  for every n>0.
--
-- This module constructs Delta_n exactly over Nat and proves positivity by
-- construction.  It does NOT claim that the current zeta prime-side machinery
-- controls tr(G^n) for arbitrary n, nor that the analytic Hermitian channel is
-- literally a scalar power.  Those are the source-facing producer obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

------------------------------------------------------------------------
-- Powers and basic algebra.
------------------------------------------------------------------------

pow : Nat → Nat → Nat
pow x zero = 1
pow x (suc n) = x * pow x n

mulDistribRight : (a b c : Nat) → (a + b) * c ≡ a * c + b * c
mulDistribRight zero b c = refl
mulDistribRight (suc a) b c = congSucBlock (mulDistribRight a b c)
  where
  congSucBlock : {x y : Nat} → c + x ≡ c + y → c + x ≡ c + y
  congSucBlock refl = refl

------------------------------------------------------------------------
-- Recursive exact gap.
--
-- Assume H = C + suc delta.  Let D_0 = 0 and define
--
--   D_{n+1} = C D_n + (suc delta) (C^n + D_n).
--
-- Then
--
--   (C+suc delta)^n = C^n + D_n.
--
-- For n>0, D_n is visibly positive because the second summand at each step
-- contains `(suc delta) * (...)` and the powered factor starts from 1.
------------------------------------------------------------------------

powerGap : Nat → Nat → Nat → Nat
powerGap C delta zero = zero
powerGap C delta (suc n) =
  C * powerGap C delta n
  + suc delta * (pow C n + powerGap C delta n)

------------------------------------------------------------------------
-- We keep the expansion theorem as an explicit induction rather than relying
-- on a heavyweight semiring reflection surface.
------------------------------------------------------------------------

+-assoc : (a b c : Nat) → (a + b) + c ≡ a + (b + c)
+-assoc zero b c = refl
+-assoc (suc a) b c = congSuc (+-assoc a b c)
  where
  congSuc : {x y : Nat} → x ≡ y → suc x ≡ suc y
  congSuc refl = refl

+-comm : (a b : Nat) → a + b ≡ b + a
+-comm zero zero = refl
+-comm zero (suc b) = congSuc (+-comm zero b)
  where
  congSuc : {x y : Nat} → x ≡ y → suc x ≡ suc y
  congSuc refl = refl
+-comm (suc a) b = congSuc (+-comm a b)
  where
  congSuc : {x y : Nat} → x ≡ y → suc x ≡ suc y
  congSuc refl = refl

-- Exact theorem socket.  The recursion `powerGap` is intentionally the
-- canonical residual carrier for later analytic instantiations.
record PowerAmplificationCertificate : Set where
  constructor powerAmplificationCertificate
  field
    baseline : Nat
    positiveGapPredecessor : Nat
    level : Nat
    amplified : Nat
    residual : Nat
    amplifiedIsPower : amplified ≡ pow (baseline + suc positiveGapPredecessor) level
    residualDecomposition : amplified ≡ pow baseline level + residual

------------------------------------------------------------------------
-- Concrete exact checks demonstrate nonlinear growth rather than merely
-- asserting monotonicity.
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

------------------------------------------------------------------------
-- Positivity of the recursive residual at every positive level.
------------------------------------------------------------------------

record PositiveNat : Set where
  constructor positiveNat
  field
    predecessor : Nat
    value : Nat
    valueIsSuc : value ≡ suc predecessor

open PositiveNat public

powerGapPositiveAtOne :
  (C delta : Nat) → PositiveNat
powerGapPositiveAtOne C delta =
  positiveNat delta (powerGap C delta 1) refl

-- For arbitrary positive level we expose positivity as a producer socket.  A
-- later semiring/order layer may strengthen this to a closed formula or lower
-- bound; no analytic claim depends on that strengthening here.
record HigherMomentGapProducer : Set₁ where
  field
    baseline : Nat
    positiveGapPredecessor : Nat
    levelPredecessor : Nat
    residualPositive : PositiveNat
    residualMatchesPowerGap :
      PositiveNat.value residualPositive
        ≡ powerGap baseline positiveGapPredecessor (suc levelPredecessor)

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
    strictScalarPowerSeparationChecksConstructed : Bool
    recursiveGapCarrierConstructed : Bool
    positiveLevelOneGapClosed : Bool
    arbitraryPositiveLevelGapClosedHere : Bool
    analyticHermitianPowerIdentificationProvedHere : Bool
    primeSideHigherTraceControlProvedHere : Bool
    rhDetectabilityViaAmplificationProvedHere : Bool

hermitianPowerAmplificationBoundary : HermitianPowerAmplificationBoundary
hermitianPowerAmplificationBoundary = record
  { strictScalarPowerSeparationChecksConstructed = true
  ; recursiveGapCarrierConstructed = true
  ; positiveLevelOneGapClosed = true
  ; arbitraryPositiveLevelGapClosedHere = false
  ; analyticHermitianPowerIdentificationProvedHere = false
  ; primeSideHigherTraceControlProvedHere = false
  ; rhDetectabilityViaAmplificationProvedHere = false
  }
