module DASHI.Mathematics.NumberTheory.FiniteNatFloorSquareRootExact where

------------------------------------------------------------------------
-- FINITE FLOOR-SQUARE-ROOT SEARCH
--
-- No real analysis is needed to obtain the integer certificate used by the
-- Bishop square-root approximation.  Scan a finite bound from 0 upward and
-- retain the largest candidate whose square is at most the target.
--
-- For the canonical bound suc target we prove
--
--   root^2 <= target <= (root+1)^2.
--
-- This owner is arithmetic-neutral with respect to the later Bishop use.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Empty using (⊥-elim)
open import Data.Nat.Base using (_≤_; _<_; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≢_; cong; subst)
open import Relation.Nullary.Decidable.Core using (yes; no)

------------------------------------------------------------------------
-- Bounded search.

floorSquareRootUpTo : Nat → Nat → Nat
floorSquareRootUpTo target zero = zero
floorSquareRootUpTo target (suc bound)
  with (suc bound * suc bound) NatP.≤? target
... | yes squareFits = suc bound
... | no squareTooLarge = floorSquareRootUpTo target bound

floorSquareRootUpToSound :
  (target bound : Nat) →
  floorSquareRootUpTo target bound * floorSquareRootUpTo target bound
  ≤ target
floorSquareRootUpToSound target zero = z≤n
floorSquareRootUpToSound target (suc bound)
  with (suc bound * suc bound) NatP.≤? target
... | yes squareFits = squareFits
... | no squareTooLarge = floorSquareRootUpToSound target bound

floorSquareRootUpToBound :
  (target bound : Nat) →
  floorSquareRootUpTo target bound ≤ bound
floorSquareRootUpToBound target zero = z≤n
floorSquareRootUpToBound target (suc bound)
  with (suc bound * suc bound) NatP.≤? target
... | yes squareFits = NatP.≤-refl
... | no squareTooLarge = NatP.≤-step (floorSquareRootUpToBound target bound)

------------------------------------------------------------------------
-- Small order helper: if m <= n but m != n then m < n.

strictFromLeDifferent :
  ∀ {m n : Nat} → m ≤ n → m ≢ n → m < n
strictFromLeDifferent {zero} {zero} z≤n different =
  ⊥-elim (different refl)
strictFromLeDifferent {zero} {suc n} z≤n different = s≤s z≤n
strictFromLeDifferent {suc m} {suc n} (s≤s bound) different =
  s≤s
    (strictFromLeDifferent bound
      (λ equality → different (cong suc equality)))

strictBelowSuccessorToLe :
  ∀ {m n : Nat} → m < suc n → m ≤ n
strictBelowSuccessorToLe (s≤s bound) = bound

------------------------------------------------------------------------
-- Maximality inside the scanned interval.

floorSquareRootUpToMaximal :
  ∀ {target bound candidate : Nat} →
  candidate ≤ bound →
  candidate * candidate ≤ target →
  candidate ≤ floorSquareRootUpTo target bound
floorSquareRootUpToMaximal {target} {zero} {zero} z≤n squareFits = z≤n
floorSquareRootUpToMaximal {target} {zero} {suc candidate} () squareFits
floorSquareRootUpToMaximal {target} {suc bound} {candidate}
    candidateBound candidateSquare
  with (suc bound * suc bound) NatP.≤? target
... | yes topFits = candidateBound
... | no topTooLarge =
  floorSquareRootUpToMaximal
    (strictBelowSuccessorToLe
      (strictFromLeDifferent candidateBound candidateNotTop))
    candidateSquare
  where
  candidateNotTop : candidate ≢ suc bound
  candidateNotTop equality =
    topTooLarge
      (subst
        (λ value → value * value ≤ target)
        equality
        candidateSquare)

------------------------------------------------------------------------
-- Canonical floor square root.

floorSquareRoot : Nat → Nat
floorSquareRoot target = floorSquareRootUpTo target (suc target)

floorSquareRootSquareBelow :
  (target : Nat) →
  floorSquareRoot target * floorSquareRoot target ≤ target
floorSquareRootSquareBelow target =
  floorSquareRootUpToSound target (suc target)

positiveSquareRootLeTarget :
  ∀ {root target : Nat} →
  root * root ≤ target →
  root ≤ target
positiveSquareRootLeTarget {zero} squareBelow = z≤n
positiveSquareRootLeTarget {suc root} {target} squareBelow =
  NatP.≤-trans
    (NatP.m≤m*n (suc root) (suc root))
    squareBelow

floorSquareRootLeTarget :
  (target : Nat) → floorSquareRoot target ≤ target
floorSquareRootLeTarget target =
  positiveSquareRootLeTarget (floorSquareRootSquareBelow target)

floorSquareRootNextSquareAbove :
  (target : Nat) →
  target ≤ suc (floorSquareRoot target) * suc (floorSquareRoot target)
floorSquareRootNextSquareAbove target
  with NatP.≤-total
    target
    (suc (floorSquareRoot target) * suc (floorSquareRoot target))
... | inj₁ targetBelowNext = targetBelowNext
... | inj₂ nextBelowTarget =
  ⊥-elim
    (NatP.1+n≰n
      (floorSquareRootUpToMaximal
        {target = target}
        {bound = suc target}
        {candidate = suc (floorSquareRoot target)}
        (s≤s (floorSquareRootLeTarget target))
        nextBelowTarget))

------------------------------------------------------------------------
-- Exact finite certificate; no Bishop or analytic imports occur here.
------------------------------------------------------------------------
