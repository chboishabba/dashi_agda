module DASHI.Foundations.BishopChudnovskyDyadicRootExact where

-- SOURCE-WRITTEN, UNCOMPILED. The original reference interval is
-- unchanged. A bit-by-bit evaluator is proved equal to it at every k.
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NP
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:*_; con; _:=_)
open import Relation.Binary.PropositionalEquality using (trans; sym; cong; subst)
open import Relation.Nullary.Decidable.Core using (from-yes)
import DASHI.Mathematics.NumberTheory.FiniteNatFloorSquareRootExact as F
import DASHI.Foundations.BishopNatSquareRootFloorApproximationExact as R
import DASHI.Foundations.BishopChudnovskyRationalMidpointExact as CH
import DASHI.Foundations.BishopChudnovskyRationalOverlapExact as O

target : Nat → Nat
target k = R.scaledSquareTarget 10005 (CH.rootScale k)

scaleStep : (k : Nat) → CH.rootScale (suc k) ≡ 2 * CH.rootScale k
scaleStep k = refl

targetStep : (k : Nat) → target (suc k) ≡ 4 * target k
targetStep k rewrite scaleStep k =
  solve 1 (λ s → (con 10005 :* (con 2 :* s)) :* (con 2 :* s)
                 := con 4 :* ((con 10005 :* s) :* s))
    refl (CH.rootScale k)

rootZero : CH.rootNumerator zero ≡ 400
rootZero = sym (F.floorSquareRootUnique 160080 400
  (from-yes (160000 NP.≤? 160080))
  (from-yes (160081 NP.≤? 160801)))

rootStep : (k : Nat) →
  F.doubleFloorBit (target k) (CH.rootNumerator k) ≡ CH.rootNumerator (suc k)
rootStep k = trans
  (F.doubleFloorCorrect (target k) (CH.rootNumerator k)
    (CH.rootLowerSquare k) (F.floorSquareRootNextSquareStrict (target k)))
  (cong F.floorSquareRoot (sym (targetStep k)))

rootLowerRefines : (k : Nat) → 2 * CH.rootNumerator k ≤ CH.rootNumerator (suc k)
rootLowerRefines k = subst (2 * CH.rootNumerator k ≤_) (rootStep k)
  (F.doubleFloorLower (target k) (CH.rootNumerator k))

rootUpperRefines : (k : Nat) →
  suc (CH.rootNumerator (suc k)) ≤ 2 * suc (CH.rootNumerator k)
rootUpperRefines k = subst (λ r → suc r ≤ 2 * suc (CH.rootNumerator k))
  (rootStep k) (F.doubleFloorUpper (target k) (CH.rootNumerator k))

-- Compute both target and root in a single traversal, preserving the
-- reference zero mode, and avoiding recomputation of powers.
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)

rootState : Nat → Nat × Nat
rootState zero = 160080 , 400
rootState (suc k) with rootState k
... | t , r = 4 * t , F.doubleFloorBit t r

stateTarget : (k : Nat) → proj₁ (rootState k) ≡ target k
stateTarget zero = refl
stateTarget (suc k) with rootState k | stateTarget k
... | t , r | eq = trans (cong (4 *_) eq) (sym (targetStep k))

fastRoot : Nat → Nat
fastRoot k = proj₂ (rootState k)

fastRootCorrect : (k : Nat) → fastRoot k ≡ CH.rootNumerator k
fastRootCorrect zero = sym rootZero
fastRootCorrect (suc k) with rootState k | stateTarget k | fastRootCorrect k
... | t , r | te | re rewrite te | re = rootStep k

-- Exact same evaluator with only the root computation changed.
fastIntervalAt : Nat → Maybe CH.Interval
fastIntervalAt k with CH.rootScale k | CH.positiveView (CH.sourcePrefix (CH.cutoff k))
  | CH.positiveView (CH.sourcePrefix (suc (CH.cutoff k)))
... | suc sp | just x | just y = just (CH.orderedInterval sp (fastRoot k) x y)
... | _ | _ | _ = nothing

fastIntervalCorrect : (k : Nat) → fastIntervalAt k ≡ CH.intervalAt k
fastIntervalCorrect k with CH.rootScale k | CH.positiveView (CH.sourcePrefix (CH.cutoff k))
  | CH.positiveView (CH.sourcePrefix (suc (CH.cutoff k)))
... | suc sp | just x | just y rewrite fastRootCorrect k = refl
... | zero | _ | _ = refl
... | suc sp | nothing | _ = refl
... | suc sp | just x | nothing = refl

fastComputed : (k : Nat) → fastIntervalAt k ≡ just (O.window k)
fastComputed k = trans (fastIntervalCorrect k) (O.computed k)
