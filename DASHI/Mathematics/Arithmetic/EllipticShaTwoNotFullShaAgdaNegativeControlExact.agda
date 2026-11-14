module DASHI.Mathematics.Arithmetic.EllipticShaTwoNotFullShaAgdaNegativeControlExact where

------------------------------------------------------------------------
-- BSD K5 LOGICAL FIREWALL IN THE AGDA GOLDEN KERNEL
--
-- A nontrivial finite abelian group can have zero 2-torsion.
-- C₃ supplies a fully finite constructive counterexample:
--   C₃[2] = {0}, but C₃ ≠ {0}.
--
-- Thus a genuine Sha(E)[2]=0 proof (even when K1/K2 have been
-- paid) cannot imply full Sha(E)=0 without an odd-primary
-- arithmetic theorem. This construction does NOT identify C₃
-- with Sha of the original selected conductor-32 elliptic curve.
--
-- No postulates, divisibility assumptions, or hidden group laws.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≢_)

data Three : Set where
  e : Three
  a : Three
  b : Three

infixl 6 _⊞_

_⊞_ : Three → Three → Three
e ⊞ x = x
a ⊞ e = a
a ⊞ a = b
a ⊞ b = e
b ⊞ e = b
b ⊞ a = e
b ⊞ b = a

zeroLeft : ∀ x → e ⊞ x ≡ x
zeroLeft e = refl
zeroLeft a = refl
zeroLeft b = refl

zeroRight : ∀ x → x ⊞ e ≡ x
zeroRight e = refl
zeroRight a = refl
zeroRight b = refl

addCommutative : ∀ x y → x ⊞ y ≡ y ⊞ x
addCommutative e e = refl
addCommutative e a = refl
addCommutative e b = refl
addCommutative a e = refl
addCommutative a a = refl
addCommutative a b = refl
addCommutative b e = refl
addCommutative b a = refl
addCommutative b b = refl

addAssociative : ∀ x y z →
  (x ⊞ y) ⊞ z ≡ x ⊞ (y ⊞ z)
addAssociative e y z = refl
addAssociative a e z = refl
addAssociative b e z = refl
addAssociative a a e = refl
addAssociative a a a = refl
addAssociative a a b = refl
addAssociative a b e = refl
addAssociative a b a = refl
addAssociative a b b = refl
addAssociative b a e = refl
addAssociative b a a = refl
addAssociative b a b = refl
addAssociative b b e = refl
addAssociative b b a = refl
addAssociative b b b = refl

negThree : Three → Three
negThree e = e
negThree a = b
negThree b = a

leftInverse : ∀ x → negThree x ⊞ x ≡ e
leftInverse e = refl
leftInverse a = refl
leftInverse b = refl

rightInverse : ∀ x → x ⊞ negThree x ≡ e
rightInverse e = refl
rightInverse a = refl
rightInverse b = refl

doubleThree : Three → Three
doubleThree x = x ⊞ x

doubleE : doubleThree e ≡ e
doubleE = refl

doubleA : doubleThree a ≡ b
doubleA = refl

doubleB : doubleThree b ≡ a
doubleB = refl

-- C₃ has no nonzero element killed by 2.
threeTwoTorsionTrivial :
  (x : Three) → doubleThree x ≡ e → x ≡ e
threeTwoTorsionTrivial e refl = refl
threeTwoTorsionTrivial a ()
threeTwoTorsionTrivial b ()

-- Nevertheless C₃ is not the zero group.
threeNontrivial : a ≢ e
threeNontrivial ()

-- The combined countermodel is a real inhabited Agda proof.
-- It prevents upgrading a Sha[2] theorem to ALL Sha.
vanishingTwoTorsionDoesNotForceGroupTrivial :
  ((x : Three) → doubleThree x ≡ e → x ≡ e)
  × (a ≢ e)
vanishingTwoTorsionDoesNotForceGroupTrivial =
  threeTwoTorsionTrivial , threeNontrivial
