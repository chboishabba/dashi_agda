module DASHI.Algebra.TriadicFiniteArithmetic where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.Closure.BalancedTernaryContinuousEnvelope
  using (Trit; neg; zer; pos; involution; TritPrefix; []; _∷_)

import DASHI.Foundations.TriadicFiniteQuotient as Q
import DASHI.Algebra.TriadicFiniteIrrep as Irrep

------------------------------------------------------------------------
-- Pair carrier.

data Pair (A B : Set) : Set where
  _,_ : A → B → Pair A B

infixr 4 _,_

------------------------------------------------------------------------
-- Balanced ternary half-adder.
--
-- The result (digit , carry) represents x + y = digit + 3 carry.

addPair : Trit → Trit → Pair Trit Trit
addPair neg neg = pos , neg
addPair neg zer = neg , zer
addPair neg pos = zer , zer
addPair zer neg = neg , zer
addPair zer zer = zer , zer
addPair zer pos = pos , zer
addPair pos neg = zer , zer
addPair pos zer = pos , zer
addPair pos pos = neg , pos

mergeCarry : Trit → Trit → Trit
mergeCarry neg neg = neg
mergeCarry neg zer = neg
mergeCarry neg pos = zer
mergeCarry zer neg = neg
mergeCarry zer zer = zer
mergeCarry zer pos = pos
mergeCarry pos neg = zer
mergeCarry pos zer = pos
mergeCarry pos pos = pos

------------------------------------------------------------------------
-- Full adder with incoming carry.

fullAdd : Trit → Trit → Trit → Pair Trit Trit
fullAdd carry x y with addPair x y
... | digit , carry₁ with addPair digit carry
...   | output , carry₂ = output , mergeCarry carry₁ carry₂

------------------------------------------------------------------------
-- Addition modulo 3^n. Overflow beyond the highest retained trit is dropped.

addWithCarry :
  ∀ {n : Nat} →
  Trit →
  Q.Residue3Pow n →
  Q.Residue3Pow n →
  Q.Residue3Pow n
addWithCarry carry [] [] = []
addWithCarry carry (x ∷ xs) (y ∷ ys) with fullAdd carry x y
... | output , nextCarry =
  output ∷ addWithCarry nextCarry xs ys

addResidue :
  ∀ {n : Nat} →
  Q.Residue3Pow n →
  Q.Residue3Pow n →
  Q.Residue3Pow n
addResidue = addWithCarry zer

zeroResidue : (n : Nat) → Q.Residue3Pow n
zeroResidue zero = []
zeroResidue (suc n) = zer ∷ zeroResidue n

negateResidue :
  ∀ {n : Nat} →
  Q.Residue3Pow n →
  Q.Residue3Pow n
negateResidue [] = []
negateResidue (x ∷ xs) = involution x ∷ negateResidue xs

------------------------------------------------------------------------
-- Checked identity and inverse laws.

leftIdentity :
  ∀ {n : Nat} →
  (x : Q.Residue3Pow n) →
  addResidue (zeroResidue n) x ≡ x
leftIdentity [] = refl
leftIdentity (neg ∷ xs) rewrite leftIdentity xs = refl
leftIdentity (zer ∷ xs) rewrite leftIdentity xs = refl
leftIdentity (pos ∷ xs) rewrite leftIdentity xs = refl

leftInverse :
  ∀ {n : Nat} →
  (x : Q.Residue3Pow n) →
  addResidue (negateResidue x) x ≡ zeroResidue n
leftInverse [] = refl
leftInverse (neg ∷ xs) rewrite leftInverse xs = refl
leftInverse (zer ∷ xs) rewrite leftInverse xs = refl
leftInverse (pos ∷ xs) rewrite leftInverse xs = refl

------------------------------------------------------------------------
-- Projection compatibility of finite addition is the exact inverse-system law.
-- This remains an explicit receipt because its proof requires a carry-locality
-- induction across the dropped highest digit.

record TriadicArithmeticLawReceipt (n : Nat) : Set where
  field
    associativity :
      (x y z : Q.Residue3Pow n) →
      addResidue (addResidue x y) z
      ≡ addResidue x (addResidue y z)

    commutative :
      (x y : Q.Residue3Pow n) →
      addResidue x y ≡ addResidue y x

open TriadicArithmeticLawReceipt public

finiteAdditiveGroup :
  (n : Nat) →
  TriadicArithmeticLawReceipt n →
  Irrep.FiniteAdditiveGroup n
finiteAdditiveGroup n laws =
  record
    { Irrep.zeroᵍ = zeroResidue n
    ; Irrep._+ᵍ_ = addResidue
    ; Irrep.negateᵍ = negateResidue
    ; Irrep.leftIdentityᵍ = leftIdentity
    ; Irrep.associativityᵍ = associativity laws
    ; Irrep.leftInverseᵍ = leftInverse
    ; Irrep.commutativeᵍ = commutative laws
    }

------------------------------------------------------------------------
-- Explicit claim boundary.

arithmeticStatement : String
arithmeticStatement =
  "Balanced-ternary addition modulo 3^n is implemented by a carry full-adder with overflow discarded at depth n; zero identity and digitwise additive inverse are checked."

arithmeticBoundary : String
arithmeticBoundary =
  "Associativity, commutativity, and reduction/addition compatibility remain named TriadicArithmeticLawReceipt obligations until their carry-locality inductions are discharged in the active Agda toolchain."
