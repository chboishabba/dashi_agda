module DASHI.Physics.Closure.NSTriadKNHHBadHeadroomRound53Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- Freeze the Round-52 recurrence architecture and expose the physically useful
-- variable as HEADROOM below one common HH-bad ceiling C_*.
--
-- For a uniform shell barrier M_q <= C_* define
--
--   d_q = C_* - M_q >= 0.
--
-- The supersolution inequality
--
--   alpha_q M_q + beta_q <= M_(q+1)
--
-- is then exactly the shell budget
--
--   beta_q + d_(q+1)
--     <= (1-alpha_q) C_* + alpha_q d_q.
--
-- Thus nonlinear forcing can be paid by fresh depletion plus previously stored
-- headroom.  No alpha_q <= 1 hypothesis is used: alpha_q > 1 simply consumes
-- headroom rather than invalidating the recurrence algebra.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNHHBadShellBarrierRound52Exact as Barrier
import DASHI.Physics.Closure.NSTriadKNHHBadBarrierToOwnerRound52Exact as OwnerBarrier

-- Elementary ordered-ring conversion used below.  Keeping it local avoids
-- relying on a particular stdlib name for the order/difference equivalence.
differenceNonnegative :
  ∀ {a b : ℚ} → a ≤ b → 0ℚ ≤ b - a
differenceNonnegative {a} {b} a≤b =
  let
    shifted : a + (0ℚ - a) ≤ b + (0ℚ - a)
    shifted = ℚP.+-mono-≤ a≤b ℚP.≤-refl

    leftZero : a + (0ℚ - a) ≡ 0ℚ
    leftZero = solve (a ∷ [])

    rightDifference : b + (0ℚ - a) ≡ b - a
    rightDifference = solve (a ∷ b ∷ [])

    zeroBelowShifted : 0ℚ ≤ b + (0ℚ - a)
    zeroBelowShifted =
      subst (λ left → left ≤ b + (0ℚ - a)) leftZero shifted
  in
  subst (0ℚ ≤_) rightDifference zeroBelowShifted

differenceNonnegativeToLe :
  ∀ {a b : ℚ} → 0ℚ ≤ b - a → a ≤ b
differenceNonnegativeToLe {a} {b} zero≤difference =
  let
    shifted : 0ℚ + a ≤ (b - a) + a
    shifted = ℚP.+-mono-≤ zero≤difference ℚP.≤-refl

    leftMeaning : 0ℚ + a ≡ a
    leftMeaning = solve (a ∷ [])

    rightMeaning : (b - a) + a ≡ b
    rightMeaning = solve (a ∷ b ∷ [])

    aBelowShifted : a ≤ (b - a) + a
    aBelowShifted =
      subst (λ left → left ≤ (b - a) + a) leftMeaning shifted
  in
  subst (a ≤_) rightMeaning aBelowShifted

headroom :
  ∀ {input} →
  OwnerBarrier.UniformShellBarrier input →
  Nat → ℚ
headroom uniform q =
  OwnerBarrier.ceiling uniform
  - Barrier.barrier (OwnerBarrier.supersolution uniform) q

headroomNonnegative :
  ∀ {input}
    (uniform : OwnerBarrier.UniformShellBarrier input) q →
  0ℚ ≤ headroom uniform q
headroomNonnegative uniform q =
  differenceNonnegative
    (OwnerBarrier.everyBarrierBelowCeiling uniform q)

headroomPaymentRHS :
  ∀ {input} →
  OwnerBarrier.UniformShellBarrier input →
  Nat → ℚ
headroomPaymentRHS {input} uniform q =
  (1ℚ - Barrier.alpha input q) * OwnerBarrier.ceiling uniform
  + Barrier.alpha input q * headroom uniform q

barrierSlack :
  ∀ {input} →
  OwnerBarrier.UniformShellBarrier input →
  Nat → ℚ
barrierSlack {input} uniform q =
  Barrier.barrier (OwnerBarrier.supersolution uniform) (suc q)
  - (Barrier.alpha input q
      * Barrier.barrier (OwnerBarrier.supersolution uniform) q
      + Barrier.forcing input q)

headroomSlack :
  ∀ {input} →
  OwnerBarrier.UniformShellBarrier input →
  Nat → ℚ
headroomSlack {input} uniform q =
  headroomPaymentRHS uniform q
  - (Barrier.forcing input q + headroom uniform (suc q))

headroomSlackIsBarrierSlack :
  ∀ {input}
    (uniform : OwnerBarrier.UniformShellBarrier input) q →
  headroomSlack uniform q ≡ barrierSlack uniform q
headroomSlackIsBarrierSlack {input} uniform q =
  solve
    ( OwnerBarrier.ceiling uniform
    ∷ Barrier.alpha input q
    ∷ Barrier.barrier (OwnerBarrier.supersolution uniform) q
    ∷ Barrier.barrier (OwnerBarrier.supersolution uniform) (suc q)
    ∷ Barrier.forcing input q
    ∷ [])

barrierSlackNonnegative :
  ∀ {input}
    (uniform : OwnerBarrier.UniformShellBarrier input) q →
  0ℚ ≤ barrierSlack uniform q
barrierSlackNonnegative uniform q =
  differenceNonnegative
    (Barrier.barrierSupersolution
      (OwnerBarrier.supersolution uniform) q)

headroomSlackNonnegative :
  ∀ {input}
    (uniform : OwnerBarrier.UniformShellBarrier input) q →
  0ℚ ≤ headroomSlack uniform q
headroomSlackNonnegative uniform q =
  subst
    (0ℚ ≤_)
    (sym (headroomSlackIsBarrierSlack uniform q))
    (barrierSlackNonnegative uniform q)

headroomEvolution :
  ∀ {input}
    (uniform : OwnerBarrier.UniformShellBarrier input) q →
  Barrier.forcing input q + headroom uniform (suc q)
  ≤ headroomPaymentRHS uniform q
headroomEvolution uniform q =
  differenceNonnegativeToLe (headroomSlackNonnegative uniform q)

headroomFormAllowsTransientAmplification : Bool
headroomFormAllowsTransientAmplification = true

headroomIsTheRemainingUniformGateCurrency : Bool
headroomIsTheRemainingUniformGateCurrency = true

headroomFormAllowsTransientAmplificationIsTrue :
  headroomFormAllowsTransientAmplification ≡ true
headroomFormAllowsTransientAmplificationIsTrue = refl
