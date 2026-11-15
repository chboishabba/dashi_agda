module DASHI.Moonshine.JInvariant369BraidModularTernaryTowerExact where

-- A concrete naturality theorem for the SAME B3 modular word at every
-- 3-adic finite level, using the preexisting balanced-ternary arithmetic.
-- Unlike scalar j, these fine-level coordinates retain monodromy.
-- No full modular-curve or physical VOA construction is assumed.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import DASHI.Physics.Closure.BalancedTernaryContinuousEnvelope
  using (Trit; []; _∷_)

import DASHI.Foundations.TriadicFiniteQuotient as Q
import DASHI.Algebra.TriadicFiniteArithmetic as Arithmetic

record ModularVectorAt (n : Nat) : Set where
  constructor modular-vector
  field
    x y : Q.Residue3Pow n
open ModularVectorAt public

reduceVector : ∀ {n : Nat} →
  ModularVectorAt (suc n) → ModularVectorAt n
reduceVector (modular-vector x y) =
  modular-vector (Q.reduce x) (Q.reduce y)

-- The existing negation is digitwise, so it commutes with dropping
-- the highest digit. This is not a new residue arithmetic system.
reduceNegate : ∀ {n : Nat} (v : Q.Residue3Pow (suc n)) →
  Q.reduce (Arithmetic.negateResidue v)
  ≡ Arithmetic.negateResidue (Q.reduce v)
reduceNegate {zero} (_ ∷ []) = refl
reduceNegate {suc n} (_ ∷ vs)
  rewrite reduceNegate vs = refl

-- Column vector convention:
-- U = [[1,0],[-1,1]] sends (x,y) -> (x,y-x)
-- T^-1 = [[1,-1],[0,1]] sends (x,y) -> (x-y,y).
lowerInverse : ∀ {n : Nat} → ModularVectorAt n → ModularVectorAt n
lowerInverse (modular-vector x y) =
  modular-vector x
    (Arithmetic.addResidue y (Arithmetic.negateResidue x))

upperInverse : ∀ {n : Nat} → ModularVectorAt n → ModularVectorAt n
upperInverse (modular-vector x y) =
  modular-vector
    (Arithmetic.addResidue x (Arithmetic.negateResidue y)) y

lowerInverseReduces :
  ∀ {n : Nat} (v : ModularVectorAt (suc n)) →
  reduceVector (lowerInverse v) ≡ lowerInverse (reduceVector v)
lowerInverseReduces (modular-vector x y)
  rewrite Arithmetic.reduce-addResidue y (Arithmetic.negateResidue x)
        | reduceNegate x = refl

upperInverseReduces :
  ∀ {n : Nat} (v : ModularVectorAt (suc n)) →
  reduceVector (upperInverse v) ≡ upperInverse (reduceVector v)
upperInverseReduces (modular-vector x y)
  rewrite Arithmetic.reduce-addResidue x (Arithmetic.negateResidue y)
        | reduceNegate y = refl

-- The previously recorded three-strand braid word is
-- (sigma1^-1 sigma2)^3. Its matrix = (T^-1 U)^3.
wordStep : ∀ {n : Nat} → ModularVectorAt n → ModularVectorAt n
wordStep v = upperInverse (lowerInverse v)

wordStepReduces :
  ∀ {n : Nat} (v : ModularVectorAt (suc n)) →
  reduceVector (wordStep v) ≡ wordStep (reduceVector v)
wordStepReduces v =
  trans (upperInverseReduces (lowerInverse v))
        (cong upperInverse (lowerInverseReduces v))

iterateWord : ∀ {n : Nat} → Nat → ModularVectorAt n → ModularVectorAt n
iterateWord zero v = v
iterateWord (suc k) v = wordStep (iterateWord k v)

iterateWordReduces :
  ∀ {n : Nat} (k : Nat) (v : ModularVectorAt (suc n)) →
  reduceVector (iterateWord k v) ≡
  iterateWord k (reduceVector v)
iterateWordReduces zero v = refl
iterateWordReduces (suc k) v =
  trans (wordStepReduces (iterateWord k v))
        (cong wordStep (iterateWordReduces k v))

braidWord : ∀ {n : Nat} → ModularVectorAt n → ModularVectorAt n
braidWord = iterateWord 3

braidWordReduces :
  ∀ {n : Nat} (v : ModularVectorAt (suc n)) →
  reduceVector (braidWord v) ≡ braidWord (reduceVector v)
braidWordReduces = iterateWordReduces 3

-- These are the actual commuting 27->9 and 9->3 reductions,
-- not an illicit C3 identification with the physical 3x3 sheet.
braidLevel27To9 :
  (v : ModularVectorAt 3) →
  reduceVector (braidWord v) ≡ braidWord (reduceVector v)
braidLevel27To9 = braidWordReduces

braidLevel9To3 :
  (v : ModularVectorAt 2) →
  reduceVector (braidWord v) ≡ braidWord (reduceVector v)
braidLevel9To3 = braidWordReduces
