module DASHI.ComputerScience.TekumFixedWidthBalancedArithmeticExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)
open import Data.Nat.Base using (_<_; _⊔_)
import Data.Nat.Properties as NatP
open import Data.Nat.DivMod using (_%_; m%n<n)
open import Data.Fin.Base as Fin using (Fin; toℕ; fromℕ<; cast; opposite)
import Data.Fin.Properties as FinP
open import Data.Vec using (Vec)
open import Data.Vec.Base using (replicate)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Algebra.Trit as Trit
import DASHI.Algebra.BalancedTernaryIntegerExact as BT
import DASHI.Algebra.BalancedTernaryPositionalInjectiveExact as Positional
import DASHI.Algebra.BalancedTernaryRankReconstructionExact as Rank
import DASHI.Algebra.BalancedTernaryCenteredReconstructionExact as Centered
import DASHI.ComputerScience.TekumAnchorArithmeticExact as Anchor

------------------------------------------------------------------------
-- Cyclic rank arithmetic for Hunhold's fixed-width int_n.
--
-- The centered rank r encodes value r-A_n in Z/(3^n).  Therefore adding two
-- centered values corresponds to the rank formula
--
--   r ⊞ s = r + s + (A_n + 1)  (mod 3^n),
--
-- since -(A_n) ≡ A_n+1 modulo 2*A_n+1.
------------------------------------------------------------------------

modulusSize : Nat → Nat
modulusSize n = suc (2 * Positional.center n)

wrapRank :
  ∀ {n} → Nat → Fin (Rank.pow3Right n)
wrapRank {n} k =
  cast
    (sym (Centered.pow3RightIsSucTwiceCenter n))
    (fromℕ< (m%n<n k (modulusSize n)))

negateCentered :
  ∀ {n} → Centered.CenteredInteger n → Centered.CenteredInteger n
negateCentered (Centered.centeredInteger r) =
  Centered.centeredInteger (opposite r)

addCentered :
  ∀ {n} →
  Centered.CenteredInteger n →
  Centered.CenteredInteger n →
  Centered.CenteredInteger n
addCentered {n} x y =
  Centered.centeredInteger
    (wrapRank
      (toℕ (Centered.rank x)
       + toℕ (Centered.rank y)
       + suc (Positional.center n)))

subtractCentered :
  ∀ {n} →
  Centered.CenteredInteger n →
  Centered.CenteredInteger n →
  Centered.CenteredInteger n
subtractCentered x y = addCentered x (negateCentered y)

------------------------------------------------------------------------
-- Symmetric absolute-value rank.
--
-- rank r and opposite r represent v and -v.  Their larger centered rank is
-- precisely the nonnegative magnitude representative.
------------------------------------------------------------------------

maxRank : ∀ {n} → Fin n → Fin n → Fin n
maxRank r s =
  fromℕ< (NatP.⊔-mono-< (FinP.toℕ<n r) (FinP.toℕ<n s))

maxRankToNat :
  ∀ {n} (r s : Fin n) →
  toℕ (maxRank r s) ≡ toℕ r ⊔ toℕ s
maxRankToNat r s = FinP.toℕ-fromℕ< _

maxRankCommutative :
  ∀ {n} (r s : Fin n) → maxRank r s ≡ maxRank s r
maxRankCommutative r s =
  FinP.toℕ-injective
    (trans
      (maxRankToNat r s)
      (trans (NatP.⊔-comm (toℕ r) (toℕ s))
             (sym (maxRankToNat s r))))

modulusCentered :
  ∀ {n} → Centered.CenteredInteger n → Centered.CenteredInteger n
modulusCentered (Centered.centeredInteger r) =
  Centered.centeredInteger (maxRank r (opposite r))

modulusNegateCentered :
  ∀ {n} (x : Centered.CenteredInteger n) →
  modulusCentered (negateCentered x) ≡ modulusCentered x
modulusNegateCentered (Centered.centeredInteger r)
  rewrite FinP.opposite-involutive r =
  cong Centered.centeredInteger (maxRankCommutative (opposite r) r)

------------------------------------------------------------------------
-- Actual balanced-trit word operations, all routed through the centered
-- bijection.  No host-language overflow or second positional semantics.
------------------------------------------------------------------------

negateWord : ∀ {n} → Vec Trit.Trit n → Vec Trit.Trit n
negateWord x =
  Centered.decodeCentered (negateCentered (Centered.encodeCentered x))

addWord : ∀ {n} → Vec Trit.Trit n → Vec Trit.Trit n → Vec Trit.Trit n
addWord x y =
  Centered.decodeCentered
    (addCentered (Centered.encodeCentered x) (Centered.encodeCentered y))

subtractWord : ∀ {n} → Vec Trit.Trit n → Vec Trit.Trit n → Vec Trit.Trit n
subtractWord x y =
  Centered.decodeCentered
    (subtractCentered (Centered.encodeCentered x) (Centered.encodeCentered y))

modulusWord : ∀ {n} → Vec Trit.Trit n → Vec Trit.Trit n
modulusWord x =
  Centered.decodeCentered (modulusCentered (Centered.encodeCentered x))

modulusNegateWord :
  ∀ {n} (x : Vec Trit.Trit n) →
  modulusWord (negateWord x) ≡ modulusWord x
modulusNegateWord x
  rewrite Centered.encodeDecodeCentered
            (negateCentered (Centered.encodeCentered x))
        | modulusNegateCentered (Centered.encodeCentered x) = refl

allPositiveWord : (n : Nat) → Vec Trit.Trit n
allPositiveWord n = replicate n Trit.pos

tekumBalancedArithmetic :
  (n : Nat) → Anchor.FixedWidthBalancedArithmetic n
tekumBalancedArithmetic n = record
  { Word = Vec Trit.Trit n
  ; negate = negateWord
  ; modulus = modulusWord
  ; subtract = subtractWord
  ; allOnes = allPositiveWord n
  ; modulusNegate = modulusNegateWord
  }

concreteAnchor :
  ∀ {n} → Vec Trit.Trit n → Vec Trit.Trit n
concreteAnchor {n} = Anchor.anchor (tekumBalancedArithmetic n)

concreteAnchorNegationInvariant :
  ∀ {n} (x : Vec Trit.Trit n) →
  concreteAnchor (negateWord x) ≡ concreteAnchor x
concreteAnchorNegationInvariant {n} x =
  Anchor.anchorNegationInvariant (tekumBalancedArithmetic n) x

------------------------------------------------------------------------
-- Small fixed-width regressions.
------------------------------------------------------------------------

oneTritPositivePlusPositiveWrapsNegative :
  addWord
    (Trit.pos Data.Vec.∷ Data.Vec.[])
    (Trit.pos Data.Vec.∷ Data.Vec.[])
  ≡ (Trit.neg Data.Vec.∷ Data.Vec.[])
oneTritPositivePlusPositiveWrapsNegative = refl
