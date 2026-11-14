module DASHI.Mathematics.Arithmetic.EllipticCubicValuationParityExact where

------------------------------------------------------------------------
-- BSD K1 ORIGINAL E:y²=x(x-1)(x+1): INTEGER VALUATION PARITY CORE
--
-- At any finite local place p, a NON-TORSION affine point has x,y!=0.
-- The ultrametric valuation rules for x-1 and x+1 give:
--   v_p(x)>0 : v_p(x-1)=v_p(x+1)=0, so 2v_p(y)=v_p(x).
--   v_p(x)<0 : v_p(x-1)=v_p(x+1)=v_p(x),
--              so 2v_p(y)=3v_p(x).
--   v_p(x)=0 : parity is immediate.
--
-- This file PAYS the complete parity algebra in original Agda ℤ,
-- using the repo's existing integer ring solver. It does NOT claim to
-- have built Q₂, its valuation, E(Q₂) or the H¹/E[2] Kummer map.
-- Those genuine source-carrier and local-image constructors remain
-- named separate K1 obligations on PR #1500.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; _+_; _-_; _*_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import Data.Integer.Tactic.RingSolver as IntRS
import Tactic.RingSolver.NonReflective as NR

module RingZ = NR IntRS.ring
open RingZ using (Κ; _⊕_; _⊗_; ⊝_; solve)

record EvenValuation (v : ℤ) : Set where
  constructor even-valuation
  field
    halfValuation : ℤ
    valuationIsTwiceHalf : v ≡ (+ 2) * halfValuation

open EvenValuation public

unitValuationEven :
  (vx : ℤ) → vx ≡ (+ 0) → EvenValuation vx
unitValuationEven vx h rewrite h =
  even-valuation (+ 0) refl

positiveValuationBalanceEven :
  (vx vy : ℤ) →
  (+ 2) * vy ≡ vx →
  EvenValuation vx
positiveValuationBalanceEven vx vy h =
  even-valuation vy (sym h)

-- The only nontrivial parity step is
--   vx = 3vx - 2vx = 2vy - 2vx = 2(vy-vx).
tripleMinusDouble :
  (x : ℤ) →
  x ≡ ((+ 3) * x) - ((+ 2) * x)
tripleMinusDouble x =
  RingZ.solve 1
    (λ x → (x ,
      ((Κ (+ 3) ⊗ x) ⊕ (⊝ (Κ (+ 2) ⊗ x)))))
    refl x

doubleDifference :
  (vx vy : ℤ) →
  ((+ 2) * vy) - ((+ 2) * vx)
  ≡ (+ 2) * (vy - vx)
doubleDifference vx vy =
  RingZ.solve 2
    (λ vx vy →
      (((Κ (+ 2) ⊗ vy) ⊕ (⊝ (Κ (+ 2) ⊗ vx))) ,
       (Κ (+ 2) ⊗ (vy ⊕ (⊝ vx)))))
    refl vx vy

negativeValuationBalanceEven :
  (vx vy : ℤ) →
  (+ 2) * vy ≡ (+ 3) * vx →
  EvenValuation vx
negativeValuationBalanceEven vx vy h =
  even-valuation (vy - vx)
    (trans
      (tripleMinusDouble vx)
      (trans
        (cong (λ z → z - ((+ 2) * vx)) (sym h))
        (doubleDifference vx vy)))

-- Actual local E(Q_p) producers should return ONE of these regimes,
-- from concrete valuation rules on x,x-1,x+1 and y²=x(x-1)(x+1).
-- Until then, no invented local Kummer image or sign classifier.
data OriginalCubicValuationRegime (vx vy : ℤ) : Set where
  zeroXValuation :
    vx ≡ (+ 0) →
    OriginalCubicValuationRegime vx vy
  positiveXValuationBalance :
    (+ 2) * vy ≡ vx →
    OriginalCubicValuationRegime vx vy
  negativeXValuationBalance :
    (+ 2) * vy ≡ (+ 3) * vx →
    OriginalCubicValuationRegime vx vy

originalCubicValuationRegimeEven :
  (vx vy : ℤ) →
  OriginalCubicValuationRegime vx vy →
  EvenValuation vx
originalCubicValuationRegimeEven vx vy
    (zeroXValuation zero) =
  unitValuationEven vx zero
originalCubicValuationRegimeEven vx vy
    (positiveXValuationBalance balance) =
  positiveValuationBalanceEven vx vy balance
originalCubicValuationRegimeEven vx vy
    (negativeXValuationBalance balance) =
  negativeValuationBalanceEven vx vy balance
