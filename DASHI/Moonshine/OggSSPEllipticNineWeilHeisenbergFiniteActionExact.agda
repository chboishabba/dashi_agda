module DASHI.Moonshine.OggSSPEllipticNineWeilHeisenbergFiniteActionExact where

------------------------------------------------------------------------
-- FINITE F3^2 WEIL-FORM / HEISENBERG ACTION TEST
--
-- CLASSICAL MATHEMATICS: alternating Weil pairing on prime-to-p torsion,
-- symplectic similitudes and the finite Heisenberg central extension.
--
-- DASHI RECONSTRUCTION: explicit 3-element field tables and finite proofs.
-- NO elliptic curve group isomorphism, intrinsic Weil-pairing identification,
-- theta-line-bundle representation, VOA intertwiner, or RH trace implication
-- is asserted by this owner.  Those require independent source maps.
--
-- The crucial distinction is:
--   shear       (a,b) -> (a+b,b):  multiplier +1; centre fixed;
--   F2-reflect  (a,b) -> (a,-b):   multiplier -1; centre inverted;
--   inversion   (a,b) -> (-a,-b): multiplier +1.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

data F3 : Set where
  z p m : F3

infixl 6 _⊕_
infixl 7 _⊗_

_⊕_ : F3 → F3 → F3
z ⊕ b = b
p ⊕ z = p
p ⊕ p = m
p ⊕ m = z
m ⊕ z = m
m ⊕ p = z
m ⊕ m = p

_⊗_ : F3 → F3 → F3
z ⊗ b = z
p ⊗ b = b
m ⊗ z = z
m ⊗ p = m
m ⊗ m = p

neg : F3 → F3
neg z = z
neg p = m
neg m = p

plusAssoc : (a b c : F3) → (a ⊕ b) ⊕ c ≡ a ⊕ (b ⊕ c)
plusAssoc z z z = refl
plusAssoc z z p = refl
plusAssoc z z m = refl
plusAssoc z p z = refl
plusAssoc z p p = refl
plusAssoc z p m = refl
plusAssoc z m z = refl
plusAssoc z m p = refl
plusAssoc z m m = refl
plusAssoc p z z = refl
plusAssoc p z p = refl
plusAssoc p z m = refl
plusAssoc p p z = refl
plusAssoc p p p = refl
plusAssoc p p m = refl
plusAssoc p m z = refl
plusAssoc p m p = refl
plusAssoc p m m = refl
plusAssoc m z z = refl
plusAssoc m z p = refl
plusAssoc m z m = refl
plusAssoc m p z = refl
plusAssoc m p p = refl
plusAssoc m p m = refl
plusAssoc m m z = refl
plusAssoc m m p = refl
plusAssoc m m m = refl

negPlus : (a b : F3) → neg (a ⊕ b) ≡ neg a ⊕ neg b
negPlus z z = refl
negPlus z p = refl
negPlus z m = refl
negPlus p z = refl
negPlus p p = refl
negPlus p m = refl
negPlus m z = refl
negPlus m p = refl
negPlus m m = refl

negNeg : (a : F3) → neg (neg a) ≡ a
negNeg z = refl
negNeg p = refl
negNeg m = refl

negTriple :
  (a b c : F3) →
  neg ((a ⊕ b) ⊕ c) ≡ (neg a ⊕ neg b) ⊕ neg c
negTriple a b c
  rewrite negPlus (a ⊕ b) c | negPlus a b = refl

half : F3 → F3
half x = m ⊗ x

halfNeg : (x : F3) → neg (half x) ≡ half (neg x)
halfNeg z = refl
halfNeg p = refl
halfNeg m = refl

V : Set
V = F3 × F3

vadd : V → V → V
vadd (a , b) (c , d) = (a ⊕ c) , (b ⊕ d)

vneg : V → V
vneg (a , b) = neg a , neg b

omega : V → V → F3
omega (a , b) (c , d) = (a ⊗ d) ⊕ neg (b ⊗ c)

shear : V → V
shear (a , b) = (a ⊕ b) , b

reflect : V → V
reflect (a , b) = a , neg b

inversion : V → V
inversion = vneg

shearPreservesSum :
  (v w : V) → shear (vadd v w) ≡ vadd (shear v) (shear w)
shearPreservesSum (z , z) (z , z) = refl
shearPreservesSum (z , z) (z , p) = refl
shearPreservesSum (z , z) (z , m) = refl
shearPreservesSum (z , z) (p , z) = refl
shearPreservesSum (z , z) (p , p) = refl
shearPreservesSum (z , z) (p , m) = refl
shearPreservesSum (z , z) (m , z) = refl
shearPreservesSum (z , z) (m , p) = refl
shearPreservesSum (z , z) (m , m) = refl
shearPreservesSum (z , p) (z , z) = refl
shearPreservesSum (z , p) (z , p) = refl
shearPreservesSum (z , p) (z , m) = refl
shearPreservesSum (z , p) (p , z) = refl
shearPreservesSum (z , p) (p , p) = refl
shearPreservesSum (z , p) (p , m) = refl
shearPreservesSum (z , p) (m , z) = refl
shearPreservesSum (z , p) (m , p) = refl
shearPreservesSum (z , p) (m , m) = refl
shearPreservesSum (z , m) (z , z) = refl
shearPreservesSum (z , m) (z , p) = refl
shearPreservesSum (z , m) (z , m) = refl
shearPreservesSum (z , m) (p , z) = refl
shearPreservesSum (z , m) (p , p) = refl
shearPreservesSum (z , m) (p , m) = refl
shearPreservesSum (z , m) (m , z) = refl
shearPreservesSum (z , m) (m , p) = refl
shearPreservesSum (z , m) (m , m) = refl
shearPreservesSum (p , z) (z , z) = refl
shearPreservesSum (p , z) (z , p) = refl
shearPreservesSum (p , z) (z , m) = refl
shearPreservesSum (p , z) (p , z) = refl
shearPreservesSum (p , z) (p , p) = refl
shearPreservesSum (p , z) (p , m) = refl
shearPreservesSum (p , z) (m , z) = refl
shearPreservesSum (p , z) (m , p) = refl
shearPreservesSum (p , z) (m , m) = refl
shearPreservesSum (p , p) (z , z) = refl
shearPreservesSum (p , p) (z , p) = refl
shearPreservesSum (p , p) (z , m) = refl
shearPreservesSum (p , p) (p , z) = refl
shearPreservesSum (p , p) (p , p) = refl
shearPreservesSum (p , p) (p , m) = refl
shearPreservesSum (p , p) (m , z) = refl
shearPreservesSum (p , p) (m , p) = refl
shearPreservesSum (p , p) (m , m) = refl
shearPreservesSum (p , m) (z , z) = refl
shearPreservesSum (p , m) (z , p) = refl
shearPreservesSum (p , m) (z , m) = refl
shearPreservesSum (p , m) (p , z) = refl
shearPreservesSum (p , m) (p , p) = refl
shearPreservesSum (p , m) (p , m) = refl
shearPreservesSum (p , m) (m , z) = refl
shearPreservesSum (p , m) (m , p) = refl
shearPreservesSum (p , m) (m , m) = refl
shearPreservesSum (m , z) (z , z) = refl
shearPreservesSum (m , z) (z , p) = refl
shearPreservesSum (m , z) (z , m) = refl
shearPreservesSum (m , z) (p , z) = refl
shearPreservesSum (m , z) (p , p) = refl
shearPreservesSum (m , z) (p , m) = refl
shearPreservesSum (m , z) (m , z) = refl
shearPreservesSum (m , z) (m , p) = refl
shearPreservesSum (m , z) (m , m) = refl
shearPreservesSum (m , p) (z , z) = refl
shearPreservesSum (m , p) (z , p) = refl
shearPreservesSum (m , p) (z , m) = refl
shearPreservesSum (m , p) (p , z) = refl
shearPreservesSum (m , p) (p , p) = refl
shearPreservesSum (m , p) (p , m) = refl
shearPreservesSum (m , p) (m , z) = refl
shearPreservesSum (m , p) (m , p) = refl
shearPreservesSum (m , p) (m , m) = refl
shearPreservesSum (m , m) (z , z) = refl
shearPreservesSum (m , m) (z , p) = refl
shearPreservesSum (m , m) (z , m) = refl
shearPreservesSum (m , m) (p , z) = refl
shearPreservesSum (m , m) (p , p) = refl
shearPreservesSum (m , m) (p , m) = refl
shearPreservesSum (m , m) (m , z) = refl
shearPreservesSum (m , m) (m , p) = refl
shearPreservesSum (m , m) (m , m) = refl

reflectionPreservesSum :
  (v w : V) → reflect (vadd v w) ≡ vadd (reflect v) (reflect w)
reflectionPreservesSum (z , z) (z , z) = refl
reflectionPreservesSum (z , z) (z , p) = refl
reflectionPreservesSum (z , z) (z , m) = refl
reflectionPreservesSum (z , z) (p , z) = refl
reflectionPreservesSum (z , z) (p , p) = refl
reflectionPreservesSum (z , z) (p , m) = refl
reflectionPreservesSum (z , z) (m , z) = refl
reflectionPreservesSum (z , z) (m , p) = refl
reflectionPreservesSum (z , z) (m , m) = refl
reflectionPreservesSum (z , p) (z , z) = refl
reflectionPreservesSum (z , p) (z , p) = refl
reflectionPreservesSum (z , p) (z , m) = refl
reflectionPreservesSum (z , p) (p , z) = refl
reflectionPreservesSum (z , p) (p , p) = refl
reflectionPreservesSum (z , p) (p , m) = refl
reflectionPreservesSum (z , p) (m , z) = refl
reflectionPreservesSum (z , p) (m , p) = refl
reflectionPreservesSum (z , p) (m , m) = refl
reflectionPreservesSum (z , m) (z , z) = refl
reflectionPreservesSum (z , m) (z , p) = refl
reflectionPreservesSum (z , m) (z , m) = refl
reflectionPreservesSum (z , m) (p , z) = refl
reflectionPreservesSum (z , m) (p , p) = refl
reflectionPreservesSum (z , m) (p , m) = refl
reflectionPreservesSum (z , m) (m , z) = refl
reflectionPreservesSum (z , m) (m , p) = refl
reflectionPreservesSum (z , m) (m , m) = refl
reflectionPreservesSum (p , z) (z , z) = refl
reflectionPreservesSum (p , z) (z , p) = refl
reflectionPreservesSum (p , z) (z , m) = refl
reflectionPreservesSum (p , z) (p , z) = refl
reflectionPreservesSum (p , z) (p , p) = refl
reflectionPreservesSum (p , z) (p , m) = refl
reflectionPreservesSum (p , z) (m , z) = refl
reflectionPreservesSum (p , z) (m , p) = refl
reflectionPreservesSum (p , z) (m , m) = refl
reflectionPreservesSum (p , p) (z , z) = refl
reflectionPreservesSum (p , p) (z , p) = refl
reflectionPreservesSum (p , p) (z , m) = refl
reflectionPreservesSum (p , p) (p , z) = refl
reflectionPreservesSum (p , p) (p , p) = refl
reflectionPreservesSum (p , p) (p , m) = refl
reflectionPreservesSum (p , p) (m , z) = refl
reflectionPreservesSum (p , p) (m , p) = refl
reflectionPreservesSum (p , p) (m , m) = refl
reflectionPreservesSum (p , m) (z , z) = refl
reflectionPreservesSum (p , m) (z , p) = refl
reflectionPreservesSum (p , m) (z , m) = refl
reflectionPreservesSum (p , m) (p , z) = refl
reflectionPreservesSum (p , m) (p , p) = refl
reflectionPreservesSum (p , m) (p , m) = refl
reflectionPreservesSum (p , m) (m , z) = refl
reflectionPreservesSum (p , m) (m , p) = refl
reflectionPreservesSum (p , m) (m , m) = refl
reflectionPreservesSum (m , z) (z , z) = refl
reflectionPreservesSum (m , z) (z , p) = refl
reflectionPreservesSum (m , z) (z , m) = refl
reflectionPreservesSum (m , z) (p , z) = refl
reflectionPreservesSum (m , z) (p , p) = refl
reflectionPreservesSum (m , z) (p , m) = refl
reflectionPreservesSum (m , z) (m , z) = refl
reflectionPreservesSum (m , z) (m , p) = refl
reflectionPreservesSum (m , z) (m , m) = refl
reflectionPreservesSum (m , p) (z , z) = refl
reflectionPreservesSum (m , p) (z , p) = refl
reflectionPreservesSum (m , p) (z , m) = refl
reflectionPreservesSum (m , p) (p , z) = refl
reflectionPreservesSum (m , p) (p , p) = refl
reflectionPreservesSum (m , p) (p , m) = refl
reflectionPreservesSum (m , p) (m , z) = refl
reflectionPreservesSum (m , p) (m , p) = refl
reflectionPreservesSum (m , p) (m , m) = refl
reflectionPreservesSum (m , m) (z , z) = refl
reflectionPreservesSum (m , m) (z , p) = refl
reflectionPreservesSum (m , m) (z , m) = refl
reflectionPreservesSum (m , m) (p , z) = refl
reflectionPreservesSum (m , m) (p , p) = refl
reflectionPreservesSum (m , m) (p , m) = refl
reflectionPreservesSum (m , m) (m , z) = refl
reflectionPreservesSum (m , m) (m , p) = refl
reflectionPreservesSum (m , m) (m , m) = refl

shearPreservesOmega :
  (v w : V) → omega (shear v) (shear w) ≡ omega v w
shearPreservesOmega (z , z) (z , z) = refl
shearPreservesOmega (z , z) (z , p) = refl
shearPreservesOmega (z , z) (z , m) = refl
shearPreservesOmega (z , z) (p , z) = refl
shearPreservesOmega (z , z) (p , p) = refl
shearPreservesOmega (z , z) (p , m) = refl
shearPreservesOmega (z , z) (m , z) = refl
shearPreservesOmega (z , z) (m , p) = refl
shearPreservesOmega (z , z) (m , m) = refl
shearPreservesOmega (z , p) (z , z) = refl
shearPreservesOmega (z , p) (z , p) = refl
shearPreservesOmega (z , p) (z , m) = refl
shearPreservesOmega (z , p) (p , z) = refl
shearPreservesOmega (z , p) (p , p) = refl
shearPreservesOmega (z , p) (p , m) = refl
shearPreservesOmega (z , p) (m , z) = refl
shearPreservesOmega (z , p) (m , p) = refl
shearPreservesOmega (z , p) (m , m) = refl
shearPreservesOmega (z , m) (z , z) = refl
shearPreservesOmega (z , m) (z , p) = refl
shearPreservesOmega (z , m) (z , m) = refl
shearPreservesOmega (z , m) (p , z) = refl
shearPreservesOmega (z , m) (p , p) = refl
shearPreservesOmega (z , m) (p , m) = refl
shearPreservesOmega (z , m) (m , z) = refl
shearPreservesOmega (z , m) (m , p) = refl
shearPreservesOmega (z , m) (m , m) = refl
shearPreservesOmega (p , z) (z , z) = refl
shearPreservesOmega (p , z) (z , p) = refl
shearPreservesOmega (p , z) (z , m) = refl
shearPreservesOmega (p , z) (p , z) = refl
shearPreservesOmega (p , z) (p , p) = refl
shearPreservesOmega (p , z) (p , m) = refl
shearPreservesOmega (p , z) (m , z) = refl
shearPreservesOmega (p , z) (m , p) = refl
shearPreservesOmega (p , z) (m , m) = refl
shearPreservesOmega (p , p) (z , z) = refl
shearPreservesOmega (p , p) (z , p) = refl
shearPreservesOmega (p , p) (z , m) = refl
shearPreservesOmega (p , p) (p , z) = refl
shearPreservesOmega (p , p) (p , p) = refl
shearPreservesOmega (p , p) (p , m) = refl
shearPreservesOmega (p , p) (m , z) = refl
shearPreservesOmega (p , p) (m , p) = refl
shearPreservesOmega (p , p) (m , m) = refl
shearPreservesOmega (p , m) (z , z) = refl
shearPreservesOmega (p , m) (z , p) = refl
shearPreservesOmega (p , m) (z , m) = refl
shearPreservesOmega (p , m) (p , z) = refl
shearPreservesOmega (p , m) (p , p) = refl
shearPreservesOmega (p , m) (p , m) = refl
shearPreservesOmega (p , m) (m , z) = refl
shearPreservesOmega (p , m) (m , p) = refl
shearPreservesOmega (p , m) (m , m) = refl
shearPreservesOmega (m , z) (z , z) = refl
shearPreservesOmega (m , z) (z , p) = refl
shearPreservesOmega (m , z) (z , m) = refl
shearPreservesOmega (m , z) (p , z) = refl
shearPreservesOmega (m , z) (p , p) = refl
shearPreservesOmega (m , z) (p , m) = refl
shearPreservesOmega (m , z) (m , z) = refl
shearPreservesOmega (m , z) (m , p) = refl
shearPreservesOmega (m , z) (m , m) = refl
shearPreservesOmega (m , p) (z , z) = refl
shearPreservesOmega (m , p) (z , p) = refl
shearPreservesOmega (m , p) (z , m) = refl
shearPreservesOmega (m , p) (p , z) = refl
shearPreservesOmega (m , p) (p , p) = refl
shearPreservesOmega (m , p) (p , m) = refl
shearPreservesOmega (m , p) (m , z) = refl
shearPreservesOmega (m , p) (m , p) = refl
shearPreservesOmega (m , p) (m , m) = refl
shearPreservesOmega (m , m) (z , z) = refl
shearPreservesOmega (m , m) (z , p) = refl
shearPreservesOmega (m , m) (z , m) = refl
shearPreservesOmega (m , m) (p , z) = refl
shearPreservesOmega (m , m) (p , p) = refl
shearPreservesOmega (m , m) (p , m) = refl
shearPreservesOmega (m , m) (m , z) = refl
shearPreservesOmega (m , m) (m , p) = refl
shearPreservesOmega (m , m) (m , m) = refl

reflectionReversesOmega :
  (v w : V) → omega (reflect v) (reflect w) ≡ neg (omega v w)
reflectionReversesOmega (z , z) (z , z) = refl
reflectionReversesOmega (z , z) (z , p) = refl
reflectionReversesOmega (z , z) (z , m) = refl
reflectionReversesOmega (z , z) (p , z) = refl
reflectionReversesOmega (z , z) (p , p) = refl
reflectionReversesOmega (z , z) (p , m) = refl
reflectionReversesOmega (z , z) (m , z) = refl
reflectionReversesOmega (z , z) (m , p) = refl
reflectionReversesOmega (z , z) (m , m) = refl
reflectionReversesOmega (z , p) (z , z) = refl
reflectionReversesOmega (z , p) (z , p) = refl
reflectionReversesOmega (z , p) (z , m) = refl
reflectionReversesOmega (z , p) (p , z) = refl
reflectionReversesOmega (z , p) (p , p) = refl
reflectionReversesOmega (z , p) (p , m) = refl
reflectionReversesOmega (z , p) (m , z) = refl
reflectionReversesOmega (z , p) (m , p) = refl
reflectionReversesOmega (z , p) (m , m) = refl
reflectionReversesOmega (z , m) (z , z) = refl
reflectionReversesOmega (z , m) (z , p) = refl
reflectionReversesOmega (z , m) (z , m) = refl
reflectionReversesOmega (z , m) (p , z) = refl
reflectionReversesOmega (z , m) (p , p) = refl
reflectionReversesOmega (z , m) (p , m) = refl
reflectionReversesOmega (z , m) (m , z) = refl
reflectionReversesOmega (z , m) (m , p) = refl
reflectionReversesOmega (z , m) (m , m) = refl
reflectionReversesOmega (p , z) (z , z) = refl
reflectionReversesOmega (p , z) (z , p) = refl
reflectionReversesOmega (p , z) (z , m) = refl
reflectionReversesOmega (p , z) (p , z) = refl
reflectionReversesOmega (p , z) (p , p) = refl
reflectionReversesOmega (p , z) (p , m) = refl
reflectionReversesOmega (p , z) (m , z) = refl
reflectionReversesOmega (p , z) (m , p) = refl
reflectionReversesOmega (p , z) (m , m) = refl
reflectionReversesOmega (p , p) (z , z) = refl
reflectionReversesOmega (p , p) (z , p) = refl
reflectionReversesOmega (p , p) (z , m) = refl
reflectionReversesOmega (p , p) (p , z) = refl
reflectionReversesOmega (p , p) (p , p) = refl
reflectionReversesOmega (p , p) (p , m) = refl
reflectionReversesOmega (p , p) (m , z) = refl
reflectionReversesOmega (p , p) (m , p) = refl
reflectionReversesOmega (p , p) (m , m) = refl
reflectionReversesOmega (p , m) (z , z) = refl
reflectionReversesOmega (p , m) (z , p) = refl
reflectionReversesOmega (p , m) (z , m) = refl
reflectionReversesOmega (p , m) (p , z) = refl
reflectionReversesOmega (p , m) (p , p) = refl
reflectionReversesOmega (p , m) (p , m) = refl
reflectionReversesOmega (p , m) (m , z) = refl
reflectionReversesOmega (p , m) (m , p) = refl
reflectionReversesOmega (p , m) (m , m) = refl
reflectionReversesOmega (m , z) (z , z) = refl
reflectionReversesOmega (m , z) (z , p) = refl
reflectionReversesOmega (m , z) (z , m) = refl
reflectionReversesOmega (m , z) (p , z) = refl
reflectionReversesOmega (m , z) (p , p) = refl
reflectionReversesOmega (m , z) (p , m) = refl
reflectionReversesOmega (m , z) (m , z) = refl
reflectionReversesOmega (m , z) (m , p) = refl
reflectionReversesOmega (m , z) (m , m) = refl
reflectionReversesOmega (m , p) (z , z) = refl
reflectionReversesOmega (m , p) (z , p) = refl
reflectionReversesOmega (m , p) (z , m) = refl
reflectionReversesOmega (m , p) (p , z) = refl
reflectionReversesOmega (m , p) (p , p) = refl
reflectionReversesOmega (m , p) (p , m) = refl
reflectionReversesOmega (m , p) (m , z) = refl
reflectionReversesOmega (m , p) (m , p) = refl
reflectionReversesOmega (m , p) (m , m) = refl
reflectionReversesOmega (m , m) (z , z) = refl
reflectionReversesOmega (m , m) (z , p) = refl
reflectionReversesOmega (m , m) (z , m) = refl
reflectionReversesOmega (m , m) (p , z) = refl
reflectionReversesOmega (m , m) (p , p) = refl
reflectionReversesOmega (m , m) (p , m) = refl
reflectionReversesOmega (m , m) (m , z) = refl
reflectionReversesOmega (m , m) (m , p) = refl
reflectionReversesOmega (m , m) (m , m) = refl

inversionPreservesOmega :
  (v w : V) → omega (inversion v) (inversion w) ≡ omega v w
inversionPreservesOmega (z , z) (z , z) = refl
inversionPreservesOmega (z , z) (z , p) = refl
inversionPreservesOmega (z , z) (z , m) = refl
inversionPreservesOmega (z , z) (p , z) = refl
inversionPreservesOmega (z , z) (p , p) = refl
inversionPreservesOmega (z , z) (p , m) = refl
inversionPreservesOmega (z , z) (m , z) = refl
inversionPreservesOmega (z , z) (m , p) = refl
inversionPreservesOmega (z , z) (m , m) = refl
inversionPreservesOmega (z , p) (z , z) = refl
inversionPreservesOmega (z , p) (z , p) = refl
inversionPreservesOmega (z , p) (z , m) = refl
inversionPreservesOmega (z , p) (p , z) = refl
inversionPreservesOmega (z , p) (p , p) = refl
inversionPreservesOmega (z , p) (p , m) = refl
inversionPreservesOmega (z , p) (m , z) = refl
inversionPreservesOmega (z , p) (m , p) = refl
inversionPreservesOmega (z , p) (m , m) = refl
inversionPreservesOmega (z , m) (z , z) = refl
inversionPreservesOmega (z , m) (z , p) = refl
inversionPreservesOmega (z , m) (z , m) = refl
inversionPreservesOmega (z , m) (p , z) = refl
inversionPreservesOmega (z , m) (p , p) = refl
inversionPreservesOmega (z , m) (p , m) = refl
inversionPreservesOmega (z , m) (m , z) = refl
inversionPreservesOmega (z , m) (m , p) = refl
inversionPreservesOmega (z , m) (m , m) = refl
inversionPreservesOmega (p , z) (z , z) = refl
inversionPreservesOmega (p , z) (z , p) = refl
inversionPreservesOmega (p , z) (z , m) = refl
inversionPreservesOmega (p , z) (p , z) = refl
inversionPreservesOmega (p , z) (p , p) = refl
inversionPreservesOmega (p , z) (p , m) = refl
inversionPreservesOmega (p , z) (m , z) = refl
inversionPreservesOmega (p , z) (m , p) = refl
inversionPreservesOmega (p , z) (m , m) = refl
inversionPreservesOmega (p , p) (z , z) = refl
inversionPreservesOmega (p , p) (z , p) = refl
inversionPreservesOmega (p , p) (z , m) = refl
inversionPreservesOmega (p , p) (p , z) = refl
inversionPreservesOmega (p , p) (p , p) = refl
inversionPreservesOmega (p , p) (p , m) = refl
inversionPreservesOmega (p , p) (m , z) = refl
inversionPreservesOmega (p , p) (m , p) = refl
inversionPreservesOmega (p , p) (m , m) = refl
inversionPreservesOmega (p , m) (z , z) = refl
inversionPreservesOmega (p , m) (z , p) = refl
inversionPreservesOmega (p , m) (z , m) = refl
inversionPreservesOmega (p , m) (p , z) = refl
inversionPreservesOmega (p , m) (p , p) = refl
inversionPreservesOmega (p , m) (p , m) = refl
inversionPreservesOmega (p , m) (m , z) = refl
inversionPreservesOmega (p , m) (m , p) = refl
inversionPreservesOmega (p , m) (m , m) = refl
inversionPreservesOmega (m , z) (z , z) = refl
inversionPreservesOmega (m , z) (z , p) = refl
inversionPreservesOmega (m , z) (z , m) = refl
inversionPreservesOmega (m , z) (p , z) = refl
inversionPreservesOmega (m , z) (p , p) = refl
inversionPreservesOmega (m , z) (p , m) = refl
inversionPreservesOmega (m , z) (m , z) = refl
inversionPreservesOmega (m , z) (m , p) = refl
inversionPreservesOmega (m , z) (m , m) = refl
inversionPreservesOmega (m , p) (z , z) = refl
inversionPreservesOmega (m , p) (z , p) = refl
inversionPreservesOmega (m , p) (z , m) = refl
inversionPreservesOmega (m , p) (p , z) = refl
inversionPreservesOmega (m , p) (p , p) = refl
inversionPreservesOmega (m , p) (p , m) = refl
inversionPreservesOmega (m , p) (m , z) = refl
inversionPreservesOmega (m , p) (m , p) = refl
inversionPreservesOmega (m , p) (m , m) = refl
inversionPreservesOmega (m , m) (z , z) = refl
inversionPreservesOmega (m , m) (z , p) = refl
inversionPreservesOmega (m , m) (z , m) = refl
inversionPreservesOmega (m , m) (p , z) = refl
inversionPreservesOmega (m , m) (p , p) = refl
inversionPreservesOmega (m , m) (p , m) = refl
inversionPreservesOmega (m , m) (m , z) = refl
inversionPreservesOmega (m , m) (m , p) = refl
inversionPreservesOmega (m , m) (m , m) = refl

shearThree :
  (v : V) → shear (shear (shear v)) ≡ v
shearThree (z , z) = refl
shearThree (z , p) = refl
shearThree (z , m) = refl
shearThree (p , z) = refl
shearThree (p , p) = refl
shearThree (p , m) = refl
shearThree (m , z) = refl
shearThree (m , p) = refl
shearThree (m , m) = refl

reflectTwice :
  (v : V) → reflect (reflect v) ≡ v
reflectTwice (z , z) = refl
reflectTwice (z , p) = refl
reflectTwice (z , m) = refl
reflectTwice (p , z) = refl
reflectTwice (p , p) = refl
reflectTwice (p , m) = refl
reflectTwice (m , z) = refl
reflectTwice (m , p) = refl
reflectTwice (m , m) = refl

inversionTwice :
  (v : V) → inversion (inversion v) ≡ v
inversionTwice (z , z) = refl
inversionTwice (z , p) = refl
inversionTwice (z , m) = refl
inversionTwice (p , z) = refl
inversionTwice (p , p) = refl
inversionTwice (p , m) = refl
inversionTwice (m , z) = refl
inversionTwice (m , p) = refl
inversionTwice (m , m) = refl

shearInverse : V → V
shearInverse (a , b) = (a ⊕ neg b) , b

reflectionConjugatesShearToInverse :
  (v : V) → reflect (shear (reflect v)) ≡ shearInverse v
reflectionConjugatesShearToInverse (z , z) = refl
reflectionConjugatesShearToInverse (z , p) = refl
reflectionConjugatesShearToInverse (z , m) = refl
reflectionConjugatesShearToInverse (p , z) = refl
reflectionConjugatesShearToInverse (p , p) = refl
reflectionConjugatesShearToInverse (p , m) = refl
reflectionConjugatesShearToInverse (m , z) = refl
reflectionConjugatesShearToInverse (m , p) = refl
reflectionConjugatesShearToInverse (m , m) = refl

pairingBasisNonzero :
  omega (p , z) (z , p) ≡ p
pairingBasisNonzero = refl

shearMovesBasis :
  shear (z , p) ≡ (p , p)
shearMovesBasis = refl

reflectionMovesBasis :
  reflect (z , p) ≡ (z , m)
reflectionMovesBasis = refl

data ReflectionEqualsShear : Set where
data ReflectionEqualsInversion : Set where

-- These specific witnesses distinguish maps and their centre actions.
reflectionNotShear :
  reflect (z , p) ≡ shear (z , p) → ⊥
reflectionNotShear ()

reflectionNotInversion :
  reflect (p , z) ≡ inversion (p , z) → ⊥
reflectionNotInversion ()

------------------------------------------------------------------------
-- 27-element Heisenberg carrier, with the alternating cocycle 1/2 omega.
------------------------------------------------------------------------

data H3 : Set where
  heis : F3 → V → H3

hprod : H3 → H3 → H3
hprod (heis a v) (heis b w) =
  heis ((a ⊕ b) ⊕ half (omega v w)) (vadd v w)

shearLift : H3 → H3
shearLift (heis a v) = heis a (shear v)

reflectionLift : H3 → H3
reflectionLift (heis a v) = heis (neg a) (reflect v)

shearLiftPreservesProduct :
  (x y : H3) →
  shearLift (hprod x y) ≡ hprod (shearLift x) (shearLift y)
shearLiftPreservesProduct (heis a v) (heis b w)
  rewrite shearPreservesSum v w | shearPreservesOmega v w = refl

reflectionLiftPreservesProduct :
  (x y : H3) →
  reflectionLift (hprod x y)
  ≡ hprod (reflectionLift x) (reflectionLift y)
reflectionLiftPreservesProduct (heis a v) (heis b w)
  rewrite reflectionPreservesSum v w
        | reflectionReversesOmega v w
        | negTriple a b (half (omega v w))
        | halfNeg (omega v w) = refl

centre : F3 → H3
centre a = heis a (z , z)

shearFixesCentre : (a : F3) → shearLift (centre a) ≡ centre a
shearFixesCentre a = refl

reflectionInvertsCentre :
  (a : F3) → reflectionLift (centre a) ≡ centre (neg a)
reflectionInvertsCentre a = refl

reflectionMovesNontrivialCentralCharacter :
  reflectionLift (centre p) ≡ centre m
reflectionMovesNontrivialCentralCharacter = refl

data FiniteHeisenbergActionIsActualEllipticWeilPairing : Set where
data FiniteHeisenbergActionProvidesVOAIntertwiner : Set where
data FiniteHeisenbergTraceProvesRHPositivity : Set where

pairingRecognitionStillRequired :
  FiniteHeisenbergActionIsActualEllipticWeilPairing → ⊥
pairingRecognitionStillRequired ()

voaIntertwinerStillRequired :
  FiniteHeisenbergActionProvidesVOAIntertwiner → ⊥
voaIntertwinerStillRequired ()

analyticTraceRealizationStillRequired :
  FiniteHeisenbergTraceProvesRHPositivity → ⊥
analyticTraceRealizationStillRequired ()

record FiniteWeilHeisenbergBoundary : Set where
  field
    explicitAlternatingForm : Bool
    shearSymplectic : Bool
    frobeniusReflectionAntiSymplectic : Bool
    ellipticInversionSymplectic : Bool
    shearLiftCentreFixed : Bool
    reflectionLiftCentreInverted : Bool
    ellipticWeilPairingIdentified : Bool
    actualVOAIntertwinerConstructed : Bool
    actualRHTraceRealizationConstructed : Bool

canonicalFiniteWeilHeisenbergBoundary : FiniteWeilHeisenbergBoundary
canonicalFiniteWeilHeisenbergBoundary =
  record
    { explicitAlternatingForm = true
    ; shearSymplectic = true
    ; frobeniusReflectionAntiSymplectic = true
    ; ellipticInversionSymplectic = true
    ; shearLiftCentreFixed = true
    ; reflectionLiftCentreInverted = true
    ; ellipticWeilPairingIdentified = false
    ; actualVOAIntertwinerConstructed = false
    ; actualRHTraceRealizationConstructed = false
    }
