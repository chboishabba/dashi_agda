module DASHI.Moonshine.Monster3BFiniteHeisenbergDotBilinearityExact where

------------------------------------------------------------------------
-- EXACT BILINEARITY OF THE SIX-COORDINATE F_3 DOT PRODUCT
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import DASHI.Algebra.Trit using (Trit)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as G
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as H
import DASHI.Moonshine.Monster3BF3AlgebraExact as F3

infixl 6 _⊕_
_⊕_ : Trit → Trit → Trit
_⊕_ = G._+3_

------------------------------------------------------------------------
-- 1. Rebracketing in the concrete additive commutative group.
------------------------------------------------------------------------

moveMiddle : (a b c : Trit) → a ⊕ (b ⊕ c) ≡ b ⊕ (a ⊕ c)
moveMiddle a b c =
  trans
    (sym (F3.plusAssoc a b c))
    (trans
      (cong (λ x → x ⊕ c) (F3.plusComm a b))
      (F3.plusAssoc b a c))

mergePairs : (a b c d : Trit) →
  (a ⊕ b) ⊕ (c ⊕ d) ≡ (a ⊕ c) ⊕ (b ⊕ d)
mergePairs a b c d =
  trans
    (F3.plusAssoc a b (c ⊕ d))
    (trans
      (cong (λ x → a ⊕ x) (moveMiddle b c d))
      (sym (F3.plusAssoc a c (b ⊕ d))))

pairwiseStep :
  (a b ra rb rp : Trit) →
  rp ≡ ra ⊕ rb →
  (a ⊕ b) ⊕ rp ≡ (a ⊕ ra) ⊕ (b ⊕ rb)
pairwiseStep a b ra rb rp eq =
  trans
    (cong (λ x → (a ⊕ b) ⊕ x) eq)
    (mergePairs a b ra rb)

sum2 : Trit → Trit → Trit
sum2 a b = a ⊕ b

sum3 : Trit → Trit → Trit → Trit
sum3 a b c = a ⊕ sum2 b c

sum4 : Trit → Trit → Trit → Trit → Trit
sum4 a b c d = a ⊕ sum3 b c d

sum5 : Trit → Trit → Trit → Trit → Trit → Trit
sum5 a b c d e = a ⊕ sum4 b c d e

sum6 : Trit → Trit → Trit → Trit → Trit → Trit → Trit
sum6 a b c d e f = a ⊕ sum5 b c d e f

pairwise2 : (a0 a1 b0 b1 : Trit) →
  sum2 (a0 ⊕ b0) (a1 ⊕ b1) ≡ sum2 a0 a1 ⊕ sum2 b0 b1
pairwise2 a0 a1 b0 b1 = pairwiseStep a0 b0 a1 b1 (a1 ⊕ b1) refl

pairwise3 : (a0 a1 a2 b0 b1 b2 : Trit) →
  sum3 (a0 ⊕ b0) (a1 ⊕ b1) (a2 ⊕ b2)
  ≡ sum3 a0 a1 a2 ⊕ sum3 b0 b1 b2
pairwise3 a0 a1 a2 b0 b1 b2 =
  pairwiseStep a0 b0
    (sum2 a1 a2) (sum2 b1 b2)
    (sum2 (a1 ⊕ b1) (a2 ⊕ b2))
    (pairwise2 a1 a2 b1 b2)

pairwise4 : (a0 a1 a2 a3 b0 b1 b2 b3 : Trit) →
  sum4 (a0 ⊕ b0) (a1 ⊕ b1) (a2 ⊕ b2) (a3 ⊕ b3)
  ≡ sum4 a0 a1 a2 a3 ⊕ sum4 b0 b1 b2 b3
pairwise4 a0 a1 a2 a3 b0 b1 b2 b3 =
  pairwiseStep a0 b0
    (sum3 a1 a2 a3) (sum3 b1 b2 b3)
    (sum3 (a1 ⊕ b1) (a2 ⊕ b2) (a3 ⊕ b3))
    (pairwise3 a1 a2 a3 b1 b2 b3)

pairwise5 : (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Trit) →
  sum5 (a0 ⊕ b0) (a1 ⊕ b1) (a2 ⊕ b2) (a3 ⊕ b3) (a4 ⊕ b4)
  ≡ sum5 a0 a1 a2 a3 a4 ⊕ sum5 b0 b1 b2 b3 b4
pairwise5 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 =
  pairwiseStep a0 b0
    (sum4 a1 a2 a3 a4) (sum4 b1 b2 b3 b4)
    (sum4 (a1 ⊕ b1) (a2 ⊕ b2) (a3 ⊕ b3) (a4 ⊕ b4))
    (pairwise4 a1 a2 a3 a4 b1 b2 b3 b4)

pairwise6 : (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : Trit) →
  sum6 (a0 ⊕ b0) (a1 ⊕ b1) (a2 ⊕ b2)
       (a3 ⊕ b3) (a4 ⊕ b4) (a5 ⊕ b5)
  ≡ sum6 a0 a1 a2 a3 a4 a5 ⊕ sum6 b0 b1 b2 b3 b4 b5
pairwise6 a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 =
  pairwiseStep a0 b0
    (sum5 a1 a2 a3 a4 a5) (sum5 b1 b2 b3 b4 b5)
    (sum5 (a1 ⊕ b1) (a2 ⊕ b2) (a3 ⊕ b3) (a4 ⊕ b4) (a5 ⊕ b5))
    (pairwise5 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5)

------------------------------------------------------------------------
-- 2. Bilinearity of the actual dot6 used by the central extension.
------------------------------------------------------------------------

dotAddRight : (x y z : G.X6) →
  H.dot6 x (H.addX6 y z) ≡ H.dot6 x y ⊕ H.dot6 x z
dotAddRight
  (G.x6 a0 a1 a2 a3 a4 a5)
  (G.x6 b0 b1 b2 b3 b4 b5)
  (G.x6 c0 c1 c2 c3 c4 c5)
  rewrite F3.leftDistrib a0 b0 c0
        | F3.leftDistrib a1 b1 c1
        | F3.leftDistrib a2 b2 c2
        | F3.leftDistrib a3 b3 c3
        | F3.leftDistrib a4 b4 c4
        | F3.leftDistrib a5 b5 c5
  = pairwise6
      (H._*3_ a0 b0) (H._*3_ a1 b1) (H._*3_ a2 b2)
      (H._*3_ a3 b3) (H._*3_ a4 b4) (H._*3_ a5 b5)
      (H._*3_ a0 c0) (H._*3_ a1 c1) (H._*3_ a2 c2)
      (H._*3_ a3 c3) (H._*3_ a4 c4) (H._*3_ a5 c5)

dotAddLeft : (x y z : G.X6) →
  H.dot6 (H.addX6 x y) z ≡ H.dot6 x z ⊕ H.dot6 y z
dotAddLeft
  (G.x6 a0 a1 a2 a3 a4 a5)
  (G.x6 b0 b1 b2 b3 b4 b5)
  (G.x6 c0 c1 c2 c3 c4 c5)
  rewrite F3.rightDistrib a0 b0 c0
        | F3.rightDistrib a1 b1 c1
        | F3.rightDistrib a2 b2 c2
        | F3.rightDistrib a3 b3 c3
        | F3.rightDistrib a4 b4 c4
        | F3.rightDistrib a5 b5 c5
  = pairwise6
      (H._*3_ a0 c0) (H._*3_ a1 c1) (H._*3_ a2 c2)
      (H._*3_ a3 c3) (H._*3_ a4 c4) (H._*3_ a5 c5)
      (H._*3_ b0 c0) (H._*3_ b1 c1) (H._*3_ b2 c2)
      (H._*3_ b3 c3) (H._*3_ b4 c4) (H._*3_ b5 c5)

record DotBilinearityBoundary : Set where
  constructor dotBilinearityBoundary
  field
    additiveRebracketingProved : Bool
    rightLinearityProved : Bool
    leftLinearityProved : Bool
open DotBilinearityBoundary public

canonicalDotBilinearityBoundary : DotBilinearityBoundary
canonicalDotBilinearityBoundary = dotBilinearityBoundary true true true
