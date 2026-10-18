module DASHI.Algebra.BalancedTernaryRankReconstructionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
import Data.Nat.Properties as NatP
open import Data.Fin.Base as Fin using (Fin; combine; remQuot; toℕ)
import Data.Fin.Properties as FinP
open import Data.Product using (_,_)
open import Function.Base using (uncurry)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Algebra.Trit as Trit
import DASHI.Algebra.BalancedTernaryIntegerExact as BT
import DASHI.Algebra.BalancedTernaryFiniteCarrierExact as Carrier
import DASHI.Algebra.BalancedTernaryPositionalInjectiveExact as Positional

------------------------------------------------------------------------
-- Right-associated 3^n matches Fin.combine's product orientation exactly.
------------------------------------------------------------------------

pow3Right : Nat → Nat
pow3Right zero = 1
pow3Right (suc n) = pow3Right n * 3

pow3RightMatchesPow3 : (n : Nat) → pow3Right n ≡ BT.pow3 n
pow3RightMatchesPow3 zero = refl
pow3RightMatchesPow3 (suc n) =
  trans
    (cong (_* 3) (pow3RightMatchesPow3 n))
    (NatP.*-comm (BT.pow3 n) 3)

------------------------------------------------------------------------
-- Exact finite rank.  Because combine q r has natural value 3*q+r,
-- its orientation is exactly the repository's LST-first positional code.
------------------------------------------------------------------------

rankWord : ∀ {n} → Vec Trit.Trit n → Fin (pow3Right n)
rankWord [] = Fin.zero
rankWord (t ∷ ts) =
  combine (rankWord ts) (Carrier.tritToFin3 t)

unrankWord : (n : Nat) → Fin (pow3Right n) → Vec Trit.Trit n
unrankWord zero i = []
unrankWord (suc n) i with remQuot 3 i
... | q , r = Carrier.fin3ToTrit r ∷ unrankWord n q

------------------------------------------------------------------------
-- Both finite-rank roundtrips are inherited from combine/remQuot.
------------------------------------------------------------------------

unrankRankWord :
  ∀ {n} (ts : Vec Trit.Trit n) →
  unrankWord n (rankWord ts) ≡ ts
unrankRankWord [] = refl
unrankRankWord {suc n} (t ∷ ts)
  rewrite FinP.remQuot-combine (rankWord ts) (Carrier.tritToFin3 t)
        | Carrier.finTritRoundTrip t
        | unrankRankWord ts = refl

rankUnrankWord :
  (n : Nat) (i : Fin (pow3Right n)) →
  rankWord (unrankWord n i) ≡ i
rankUnrankWord zero Fin.zero = refl
rankUnrankWord (suc n) i with remQuot 3 i in eq
... | q , r
  rewrite rankUnrankWord n q
        | Carrier.tritFinRoundTrip r =
  trans
    (cong (uncurry combine) (sym eq))
    (FinP.combine-remQuot 3 i)

------------------------------------------------------------------------
-- Rank is the same natural number as the shifted positional normal form.
------------------------------------------------------------------------

tritFinToNat :
  (t : Trit.Trit) →
  toℕ (Carrier.tritToFin3 t) ≡ Positional.digitNat t
tritFinToNat Trit.neg = refl
tritFinToNat Trit.zer = refl
tritFinToNat Trit.pos = refl

rankToNatCode :
  ∀ {n} (ts : Vec Trit.Trit n) →
  toℕ (rankWord ts) ≡ Positional.natCode ts
rankToNatCode [] = refl
rankToNatCode (t ∷ ts) =
  trans
    (FinP.toℕ-combine (rankWord ts) (Carrier.tritToFin3 t))
    (trans
      (cong₂ _+_
        (cong (3 *_) (rankToNatCode ts))
        (tritFinToNat t))
      (NatP.+-comm (3 * Positional.natCode ts) (Positional.digitNat t)))
  where
  cong₂ : ∀ {A B C : Set} (f : A → B → C)
    {x x′ : A} {y y′ : B} →
    x ≡ x′ → y ≡ y′ → f x y ≡ f x′ y′
  cong₂ f refl refl = refl

natCodeStrictBoundRight :
  ∀ {n} (ts : Vec Trit.Trit n) →
  Positional.natCode ts < pow3Right n
natCodeStrictBoundRight ts
  rewrite sym (rankToNatCode ts) = FinP.toℕ<n (rankWord ts)

natCodeStrictBound :
  ∀ {n} (ts : Vec Trit.Trit n) →
  Positional.natCode ts < BT.pow3 n
natCodeStrictBound {n} ts
  rewrite sym (pow3RightMatchesPow3 n) =
  natCodeStrictBoundRight ts

------------------------------------------------------------------------
-- This pays constructive reconstruction of the finite rank.  The next owner
-- shifts this rank by A003462(n) and packages the actual centered ℤ interval.
------------------------------------------------------------------------
