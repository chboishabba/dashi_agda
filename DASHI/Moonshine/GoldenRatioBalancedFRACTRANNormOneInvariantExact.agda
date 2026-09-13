module DASHI.Moonshine.GoldenRatioBalancedFRACTRANNormOneInvariantExact where

------------------------------------------------------------------------
-- NORM-ONE CASSINI INVARIANT FOR THE BALANCED-FRACTRAN TWO-STEP MACRO
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)

import DASHI.Moonshine.GoldenRatioBalancedFRACTRANBishopRatioCarrierExact as Ratio

------------------------------------------------------------------------
-- 1. Nat-valued norm-one predicate.
------------------------------------------------------------------------

NormOne : Nat → Nat → Set
NormOne p q = p * p ≡ p * q + q * q + 1

startNormOne : NormOne 2 1
startNormOne = refl

------------------------------------------------------------------------
-- 2. Algebraic two-step preservation on arbitrary Nat pairs.
------------------------------------------------------------------------

twoStepLeftExpand :
  (p q : Nat) →
  (p + p + q) * (p + p + q)
  ≡ 4 * (p * p) + 4 * (p * q) + q * q
twoStepLeftExpand =
  solve 2
    (λ p q →
      ((p :+ p) :+ q) :* ((p :+ p) :+ q)
      :=
      (con 4 :* (p :* p)) :+
      ((con 4 :* (p :* q)) :+ (q :* q)))
    refl

twoStepRightExpand :
  (p q : Nat) →
  (p + p + q) * (p + q) + (p + q) * (p + q) + 1
  ≡ 3 * (p * p) + 5 * (p * q) + 2 * (q * q) + 1
twoStepRightExpand =
  solve 2
    (λ p q →
      ((((p :+ p) :+ q) :* (p :+ q)) :+
       ((p :+ q) :* (p :+ q))) :+ con 1
      :=
      (((con 3 :* (p :* p)) :+
        (con 5 :* (p :* q))) :+
       (con 2 :* (q :* q))) :+ con 1)
    refl

substitutedNormOneBalance :
  (p q : Nat) →
  4 * (p * q + q * q + 1) + 4 * (p * q) + q * q
  ≡
  3 * (p * q + q * q + 1) + 5 * (p * q) + 2 * (q * q) + 1
substitutedNormOneBalance =
  solve 2
    (λ p q →
      (con 4 :* (((p :* q) :+ (q :* q)) :+ con 1)) :+
      ((con 4 :* (p :* q)) :+ (q :* q))
      :=
      (((con 3 :* (((p :* q) :+ (q :* q)) :+ con 1)) :+
        (con 5 :* (p :* q))) :+
       (con 2 :* (q :* q))) :+ con 1)
    refl

twoStepPreservesNormOne :
  (p q : Nat) →
  NormOne p q →
  NormOne (p + p + q) (p + q)
twoStepPreservesNormOne p q norm =
  trans
    (twoStepLeftExpand p q)
    (trans
      (cong
        (λ x → 4 * x + 4 * (p * q) + q * q)
        norm)
      (trans
        (substitutedNormOneBalance p q)
        (trans
          (cong
            (λ x → 3 * x + 5 * (p * q) + 2 * (q * q) + 1)
            (sym norm))
          (sym (twoStepRightExpand p q)))))

------------------------------------------------------------------------
-- 3. The PositiveFibPair macro is exactly that two-step polynomial map.
------------------------------------------------------------------------

twoStepHiFormula :
  (pair : Ratio.PositiveFibPair) →
  Ratio.positiveHi (Ratio.positiveFibTwoStep pair)
  ≡ Ratio.positiveHi pair + Ratio.positiveHi pair + Ratio.positiveLo pair
twoStepHiFormula (Ratio.positiveFibPair a b) =
  solve 2
    (λ a b →
      con 1 :+ ((a :+ (con 1 :+ b)) :+ (con 1 :+ a))
      :=
      ((con 1 :+ a) :+ (con 1 :+ a)) :+ (con 1 :+ b))
    refl

twoStepLoFormula :
  (pair : Ratio.PositiveFibPair) →
  Ratio.positiveLo (Ratio.positiveFibTwoStep pair)
  ≡ Ratio.positiveHi pair + Ratio.positiveLo pair
twoStepLoFormula (Ratio.positiveFibPair a b) =
  solve 2
    (λ a b →
      con 1 :+ (a :+ (con 1 :+ b))
      :=
      (con 1 :+ a) :+ (con 1 :+ b))
    refl

positiveMacroPreservesNormOne :
  (pair : Ratio.PositiveFibPair) →
  NormOne (Ratio.positiveHi pair) (Ratio.positiveLo pair) →
  NormOne
    (Ratio.positiveHi (Ratio.positiveFibTwoStep pair))
    (Ratio.positiveLo (Ratio.positiveFibTwoStep pair))
positiveMacroPreservesNormOne pair norm
  rewrite twoStepHiFormula pair
        | twoStepLoFormula pair =
  twoStepPreservesNormOne
    (Ratio.positiveHi pair)
    (Ratio.positiveLo pair)
    norm

------------------------------------------------------------------------
-- 4. Every state of the balanced-FRACTRAN macro sequence is norm one.
------------------------------------------------------------------------

balancedMacroNormOne :
  (n : Nat) →
  NormOne
    (Ratio.positiveHi (Ratio.iteratePositiveMacro n))
    (Ratio.positiveLo (Ratio.iteratePositiveMacro n))
balancedMacroNormOne zero = startNormOne
balancedMacroNormOne (suc n) =
  positiveMacroPreservesNormOne
    (Ratio.iteratePositiveMacro n)
    (balancedMacroNormOne n)

normOne0 : NormOne 2 1
normOne0 = balancedMacroNormOne 0

normOne1 : NormOne 5 3
normOne1 = balancedMacroNormOne 1

normOne2 : NormOne 13 8
normOne2 = balancedMacroNormOne 2

normOne3 : NormOne 34 21
normOne3 = balancedMacroNormOne 3

------------------------------------------------------------------------
-- 5. Frontier.
------------------------------------------------------------------------

record NormOneInvariantFrontier : Set where
  constructor norm-one-invariant-frontier
  field
    twoStepPreservationGeneric : Bool
    positivePairMacroIdentified : Bool
    allBalancedMacroStatesNormOne : Bool
    bishopReciprocalSquareWelded : Bool

canonicalNormOneInvariantFrontier : NormOneInvariantFrontier
canonicalNormOneInvariantFrontier =
  norm-one-invariant-frontier true true true false
