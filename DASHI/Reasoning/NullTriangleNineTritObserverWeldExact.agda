module DASHI.Reasoning.NullTriangleNineTritObserverWeldExact where

-- Source-written, not kernel accepted. Reuse literal observer chart and
-- existing two-coordinate cube. The last two row-major entries are selected;
-- arbitrary ordered selections are handled in the companion executable.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import Data.Vec using (Vec; []; _∷_)
open import DASHI.Algebra.Trit using (Trit)
import DASHI.Metric.AgreementUltrametric as U
import DASHI.Reasoning.NullTriangleOrderedUltrametricCubeExact as P
import DASHI.Reasoning.Trialectic369HypervoxelUltrametricExact as V

depth : Nat → Nat
depth zero = 2
depth (suc n) = suc (depth n)

attach : ∀ {n : Nat} → Vec Trit n → P.Point → Vec Trit (depth n)
attach [] p = p
attach (t ∷ h) p = t ∷ attach h p

attachIsometry : ∀ {n : Nat} (h : Vec Trit n) (p q : P.Point) →
  U.dNat (attach h p) (attach h q) ≡ U.dNat p q
attachIsometry [] p q = refl
attachIsometry (t ∷ h) p q =
  trans (P.prependIsometry t (attach h p) (attach h q))
        (attachIsometry h p q)

-- Lift the native XY face on the unchanged spectator context.
attachedXY : ∀ {n : Nat} (h : Vec Trit n) (p : P.Point) →
  attach h (P.stepY (P.stepX p)) ≡ attach h (P.stepX (P.stepY p))
attachedXY h p = cong (attach h) (P.xyCommute p)

attachedXInverse : ∀ {n : Nat} (h : Vec Trit n) (p : P.Point) →
  attach h (P.undoX (P.stepX p)) ≡ attach h p
attachedXInverse h p = cong (attach h) (P.xRoundTrip p)

attachedYInverse : ∀ {n : Nat} (h : Vec Trit n) (p : P.Point) →
  attach h (P.undoY (P.stepY p)) ≡ attach h p
attachedYInverse h p = cong (attach h) (P.yRoundTrip p)

attachedQuarterIsometry : ∀ {n : Nat} (h : Vec Trit n) (p q : P.Point) →
  U.dNat (attach h (P.swapOrder (P.quarter p)))
         (attach h (P.swapOrder (P.quarter q)))
  ≡ U.dNat p q
attachedQuarterIsometry h p q =
  trans (attachIsometry h (P.swapOrder (P.quarter p)) (P.swapOrder (P.quarter q)))
        (P.orderedQuarterIsometry p q)

-- Actual existing row-major observer chart, no substitute observer record.
literalNineRoundTrip : (v : Vec Trit 9) →
  V.observerToTritVec9 (V.tritVec9ToObserver v) ≡ v
literalNineRoundTrip = V.vecObserverRoundTrip

literalNineAttach : (h : Vec Trit 7) (p : P.Point) →
  V.observerToTritVec9 (V.tritVec9ToObserver (attach h p)) ≡ attach h p
literalNineAttach h p = literalNineRoundTrip (attach h p)

literalNineDistance : (h : Vec Trit 7) (p q : P.Point) →
  V.trialecticDistance (V.tritVec9ToObserver (attach h p))
                      (V.tritVec9ToObserver (attach h q))
  ≡ U.dNat p q
literalNineDistance h p q
  rewrite literalNineAttach h p | literalNineAttach h q =
  attachIsometry h p q
