module DASHI.Reasoning.NullTriangleOrderedUltrametricCubeExact where

-- Source-written adapter: reuse the canonical agreement distance, not a new
-- metric. Integer signed representative Q and modular analytic J remain
-- distinct consumers; this file proves the finite ordered-address seam.
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym)
open import Data.Nat using (_≤_; _⊔_; s≤s; z≤n)
open import Data.Vec using (Vec; []; _∷_; map)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos; inv)
import DASHI.Metric.AgreementUltrametric as U

Point : Set
Point = Vec Trit 2

A B C D : Point
A = zer ∷ zer ∷ []
B = pos ∷ zer ∷ []
C = pos ∷ pos ∷ []
D = zer ∷ pos ∷ []

AB : U.dNat A B ≡ 2
AB = refl
BC : U.dNat B C ≡ 1
BC = refl
AC : U.dNat A C ≡ 2
AC = refl
AD : U.dNat A D ≡ 1
AD = refl
DC : U.dNat D C ≡ 2
DC = refl

-- Invoke the existing general strict-leg theorem in each orientation.
firstStrict : U.dNat B A ≡ U.dNat C A
firstStrict = U.strictLegForcesLongSideEquality B C A (s≤s (s≤s z≤n))

secondStrict : U.dNat A C ≡ U.dNat D C
secondStrict = U.strictLegForcesLongSideEquality A D C (s≤s (s≤s z≤n))

firstBottleneck : U.dNat A C ≡ (U.dNat A B ⊔ U.dNat B C)
firstBottleneck = refl
secondBottleneck : U.dNat A C ≡ (U.dNat A D ⊔ U.dNat D C)
secondBottleneck = refl

-- Same-prefix extension preserves the existing reversed-depth distance,
-- for arbitrary depth (not just the finite executable sample).
prependIsometry :
  ∀ {n : Nat} (t : Trit) (p q : Vec Trit n) →
  U.dNat (t ∷ p) (t ∷ q) ≡ U.dNat p q
prependIsometry neg p q = refl
prependIsometry zer p q = refl
prependIsometry pos p q = refl

-- Cyclic address translations are F3 digit operations, NOT integer
-- translation beyond the balanced representative boundary.
next prev : Trit → Trit
next neg = zer
next zer = pos
next pos = neg
prev neg = pos
prev zer = neg
prev pos = zer

prevNext : ∀ t → prev (next t) ≡ t
prevNext neg = refl
prevNext zer = refl
prevNext pos = refl

nextPrev : ∀ t → next (prev t) ≡ t
nextPrev neg = refl
nextPrev zer = refl
nextPrev pos = refl

stepX stepY undoX undoY : Point → Point
stepX (x ∷ y ∷ []) = next x ∷ y ∷ []
stepY (x ∷ y ∷ []) = x ∷ next y ∷ []
undoX (x ∷ y ∷ []) = prev x ∷ y ∷ []
undoY (x ∷ y ∷ []) = x ∷ prev y ∷ []

xyCommute : ∀ p → stepY (stepX p) ≡ stepX (stepY p)
xyCommute (x ∷ y ∷ []) = refl

xRoundTrip : ∀ p → undoX (stepX p) ≡ p
xRoundTrip (x ∷ y ∷ []) rewrite prevNext x = refl
yRoundTrip : ∀ p → undoY (stepY p) ≡ p
yRoundTrip (x ∷ y ∷ []) rewrite prevNext y = refl
xReverseRoundTrip : ∀ p → stepX (undoX p) ≡ p
xReverseRoundTrip (x ∷ y ∷ []) rewrite nextPrev x = refl
yReverseRoundTrip : ∀ p → stepY (undoY p) ≡ p
yReverseRoundTrip (x ∷ y ∷ []) rewrite nextPrev y = refl

liftX liftY : Vec Trit 3 → Vec Trit 3
liftX (t ∷ p) = t ∷ stepX p
liftY (t ∷ p) = t ∷ stepY p

-- All six faces: XY bottom/top, X/refine at both Y levels,
-- Y/refine at both X levels. Generic p includes the opposite edges.
xyTop : ∀ t p → liftY (liftX (t ∷ p)) ≡ liftX (liftY (t ∷ p))
xyTop t p = cong (t ∷_) (xyCommute p)
xRefine : ∀ t p → liftX (t ∷ p) ≡ t ∷ stepX p
xRefine t p = refl
yRefine : ∀ t p → liftY (t ∷ p) ≡ t ∷ stepY p
yRefine t p = refl

-- Quarter turn with fixed coordinate order is NOT an isometry.
quarter : Point → Point
quarter (x ∷ y ∷ []) = inv y ∷ x ∷ []

rotationBefore : U.dNat A B ≡ 2
rotationBefore = refl
rotationAfter : U.dNat (quarter A) (quarter B) ≡ 1
rotationAfter = refl

-- Transport the order with the rotation (swap target coordinate order).
swapOrder : Point → Point
swapOrder (x ∷ y ∷ []) = y ∷ x ∷ []

orderedQuarterIsometry :
  ∀ p q → U.dNat (swapOrder (quarter p)) (swapOrder (quarter q)) ≡ U.dNat p q
orderedQuarterIsometry (neg ∷ y ∷ []) (neg ∷ z ∷ [])
  rewrite U.agreeDepth-inv (y ∷ []) (z ∷ []) = refl
orderedQuarterIsometry (neg ∷ y ∷ []) (zer ∷ z ∷ []) = refl
orderedQuarterIsometry (neg ∷ y ∷ []) (pos ∷ z ∷ []) = refl
orderedQuarterIsometry (zer ∷ y ∷ []) (neg ∷ z ∷ []) = refl
orderedQuarterIsometry (zer ∷ y ∷ []) (zer ∷ z ∷ [])
  rewrite U.agreeDepth-inv (y ∷ []) (z ∷ []) = refl
orderedQuarterIsometry (zer ∷ y ∷ []) (pos ∷ z ∷ []) = refl
orderedQuarterIsometry (pos ∷ y ∷ []) (neg ∷ z ∷ []) = refl
orderedQuarterIsometry (pos ∷ y ∷ []) (zer ∷ z ∷ []) = refl
orderedQuarterIsometry (pos ∷ y ∷ []) (pos ∷ z ∷ [])
  rewrite U.agreeDepth-inv (y ∷ []) (z ∷ []) = refl
