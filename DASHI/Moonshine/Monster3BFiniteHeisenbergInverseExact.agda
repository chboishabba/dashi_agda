module DASHI.Moonshine.Monster3BFiniteHeisenbergInverseExact where

------------------------------------------------------------------------
-- EXACT INVERSES FOR THE FINITE HEISENBERG CENTRAL EXTENSION
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as G
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as H
import DASHI.Moonshine.Monster3BFiniteHeisenbergDotBilinearityExact as Dot
import DASHI.Moonshine.Monster3BF3AlgebraExact as F3

infixl 6 _⊕_
_⊕_ : Trit → Trit → Trit
_⊕_ = G._+3_

------------------------------------------------------------------------
-- 1. Negation compatibility with scalar multiplication and six-term sums.
------------------------------------------------------------------------

mulNegRight : (a b : Trit) →
  H._*3_ a (G.negate3 b) ≡ G.negate3 (H._*3_ a b)
mulNegRight neg neg = refl
mulNegRight neg zer = refl
mulNegRight neg pos = refl
mulNegRight zer neg = refl
mulNegRight zer zer = refl
mulNegRight zer pos = refl
mulNegRight pos neg = refl
mulNegRight pos zer = refl
mulNegRight pos pos = refl

mulNegLeft : (a b : Trit) →
  H._*3_ (G.negate3 a) b ≡ G.negate3 (H._*3_ a b)
mulNegLeft neg neg = refl
mulNegLeft neg zer = refl
mulNegLeft neg pos = refl
mulNegLeft zer neg = refl
mulNegLeft zer zer = refl
mulNegLeft zer pos = refl
mulNegLeft pos neg = refl
mulNegLeft pos zer = refl
mulNegLeft pos pos = refl

negSum2 : (a b : Trit) →
  G.negate3 (Dot.sum2 a b) ≡ Dot.sum2 (G.negate3 a) (G.negate3 b)
negSum2 = F3.negateAdd

negSum3 : (a b c : Trit) →
  G.negate3 (Dot.sum3 a b c)
  ≡ Dot.sum3 (G.negate3 a) (G.negate3 b) (G.negate3 c)
negSum3 a b c
  rewrite F3.negateAdd a (Dot.sum2 b c) | negSum2 b c = refl

negSum4 : (a b c d : Trit) →
  G.negate3 (Dot.sum4 a b c d)
  ≡ Dot.sum4 (G.negate3 a) (G.negate3 b) (G.negate3 c) (G.negate3 d)
negSum4 a b c d
  rewrite F3.negateAdd a (Dot.sum3 b c d) | negSum3 b c d = refl

negSum5 : (a b c d e : Trit) →
  G.negate3 (Dot.sum5 a b c d e)
  ≡ Dot.sum5 (G.negate3 a) (G.negate3 b) (G.negate3 c)
              (G.negate3 d) (G.negate3 e)
negSum5 a b c d e
  rewrite F3.negateAdd a (Dot.sum4 b c d e) | negSum4 b c d e = refl

negSum6 : (a b c d e f : Trit) →
  G.negate3 (Dot.sum6 a b c d e f)
  ≡ Dot.sum6 (G.negate3 a) (G.negate3 b) (G.negate3 c)
              (G.negate3 d) (G.negate3 e) (G.negate3 f)
negSum6 a b c d e f
  rewrite F3.negateAdd a (Dot.sum5 b c d e f) | negSum5 b c d e f = refl

dotNegRight : (x y : G.X6) →
  H.dot6 x (H.negX6 y) ≡ G.negate3 (H.dot6 x y)
dotNegRight
  (G.x6 a0 a1 a2 a3 a4 a5)
  (G.x6 b0 b1 b2 b3 b4 b5)
  rewrite mulNegRight a0 b0 | mulNegRight a1 b1 | mulNegRight a2 b2
        | mulNegRight a3 b3 | mulNegRight a4 b4 | mulNegRight a5 b5
  = sym (negSum6
      (H._*3_ a0 b0) (H._*3_ a1 b1) (H._*3_ a2 b2)
      (H._*3_ a3 b3) (H._*3_ a4 b4) (H._*3_ a5 b5))

dotNegLeft : (x y : G.X6) →
  H.dot6 (H.negX6 x) y ≡ G.negate3 (H.dot6 x y)
dotNegLeft
  (G.x6 a0 a1 a2 a3 a4 a5)
  (G.x6 b0 b1 b2 b3 b4 b5)
  rewrite mulNegLeft a0 b0 | mulNegLeft a1 b1 | mulNegLeft a2 b2
        | mulNegLeft a3 b3 | mulNegLeft a4 b4 | mulNegLeft a5 b5
  = sym (negSum6
      (H._*3_ a0 b0) (H._*3_ a1 b1) (H._*3_ a2 b2)
      (H._*3_ a3 b3) (H._*3_ a4 b4) (H._*3_ a5 b5))

------------------------------------------------------------------------
-- 2. Additive inverses of X6.
------------------------------------------------------------------------

addNegRight : (x : G.X6) → H.addX6 x (H.negX6 x) ≡ H.zeroX6
addNegRight (G.x6 a b c d e f)
  rewrite F3.plusInverseRight a | F3.plusInverseRight b
        | F3.plusInverseRight c | F3.plusInverseRight d
        | F3.plusInverseRight e | F3.plusInverseRight f = refl

addNegLeft : (x : G.X6) → H.addX6 (H.negX6 x) x ≡ H.zeroX6
addNegLeft (G.x6 a b c d e f)
  rewrite F3.plusInverseLeft a | F3.plusInverseLeft b
        | F3.plusInverseLeft c | F3.plusInverseLeft d
        | F3.plusInverseLeft e | F3.plusInverseLeft f = refl

------------------------------------------------------------------------
-- 3. Central phase cancellation and the actual inverse formula.
------------------------------------------------------------------------

rightPhaseInverse : (c p : Trit) →
  c ⊕ ((G.negate3 c ⊕ p) ⊕ G.negate3 p) ≡ zer
rightPhaseInverse c p
  rewrite F3.plusAssoc (G.negate3 c) p (G.negate3 p)
        | F3.plusInverseRight p
        | F3.plusRightZero (G.negate3 c)
  = F3.plusInverseRight c

leftPhaseInverse : (c p : Trit) →
  (G.negate3 c ⊕ p) ⊕ (c ⊕ G.negate3 p) ≡ zer
leftPhaseInverse c p
  rewrite Dot.mergePairs (G.negate3 c) p c (G.negate3 p)
        | F3.plusInverseLeft c | F3.plusInverseRight p = refl

inverseH : H.Heisenberg6 → H.Heisenberg6
inverseH (H.heisenberg6 (H.symplectic12 x ξ) c) =
  H.heisenberg6
    (H.symplectic12 (H.negX6 x) (H.negX6 ξ))
    (G.negate3 c ⊕ H.dot6 ξ x)

rightInverse : (g : H.Heisenberg6) →
  H.compose g (inverseH g) ≡ H.identityH
rightInverse (H.heisenberg6 (H.symplectic12 x ξ) c)
  rewrite addNegRight x | addNegRight ξ | dotNegRight ξ x
        | rightPhaseInverse c (H.dot6 ξ x) = refl

leftInverse : (g : H.Heisenberg6) →
  H.compose (inverseH g) g ≡ H.identityH
leftInverse (H.heisenberg6 (H.symplectic12 x ξ) c)
  rewrite addNegLeft x | addNegLeft ξ | dotNegLeft ξ x
        | leftPhaseInverse c (H.dot6 ξ x) = refl

record HeisenbergInverseBoundary : Set where
  constructor heisenbergInverseBoundary
  field
    vectorAdditiveInversesProved : Bool
    dotNegationCompatibilityProved : Bool
    centralPhaseCancellationProved : Bool
    leftInverseProved : Bool
    rightInverseProved : Bool
open HeisenbergInverseBoundary public

canonicalHeisenbergInverseBoundary : HeisenbergInverseBoundary
canonicalHeisenbergInverseBoundary =
  heisenbergInverseBoundary true true true true true
