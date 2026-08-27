module DASHI.Mathematics.NumberTheory.FiniteNatVectorZeroPaddingExact where

------------------------------------------------------------------------
-- EXACT ZERO PADDING UNDER A FINITE DIMENSION BOUND
--
-- A vector of dimension r embeds canonically into any ambient dimension n
-- once r ≤ n, by preserving the prefix and filling the remaining coordinates
-- with zero.  The same order witness widens Fin indices without changing their
-- natural coordinate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Fin.Base using (Fin; toℕ)
  renaming (zero to fzero; suc to fsuc)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Mathematics.NumberTheory.PartitionMultiplicityCarrierExact as Partition

zeroVec : (n : Nat) → Vec Nat n
zeroVec zero = []
zeroVec (suc n) = zero ∷ zeroVec n

padNatVector :
  ∀ {r n : Nat} → r ≤ n → Vec Nat r → Vec Nat n
padNatVector {zero} {n} z≤n [] = zeroVec n
padNatVector {suc r} {suc n} (s≤s bound) (x ∷ xs) =
  x ∷ padNatVector bound xs

widenFin :
  ∀ {r n : Nat} → r ≤ n → Fin r → Fin n
widenFin (s≤s bound) fzero = fzero
widenFin (s≤s bound) (fsuc index) = fsuc (widenFin bound index)

widenFinToNat :
  ∀ {r n : Nat} (bound : r ≤ n) (index : Fin r) →
  toℕ (widenFin bound index) ≡ toℕ index
widenFinToNat (s≤s bound) fzero = refl
widenFinToNat (s≤s bound) (fsuc index) =
  cong suc (widenFinToNat bound index)

zeroVecMassFrom :
  (first n : Nat) →
  Partition.weightedMassFrom first (zeroVec n) ≡ zero
zeroVecMassFrom first zero = refl
zeroVecMassFrom first (suc n) =
  trans
    (cong (first * zero +_)
      (zeroVecMassFrom (suc first) n))
    refl

padWeightedMassFrom :
  ∀ {r n : Nat}
    (first : Nat) (bound : r ≤ n) (vector : Vec Nat r) →
  Partition.weightedMassFrom first (padNatVector bound vector)
  ≡ Partition.weightedMassFrom first vector
padWeightedMassFrom first z≤n [] = zeroVecMassFrom first _
padWeightedMassFrom first (s≤s bound) (x ∷ xs) =
  cong
    (first * x +_)
    (padWeightedMassFrom (suc first) bound xs)

padWeightedMass :
  ∀ {r n : Nat}
    (bound : r ≤ n) (vector : Vec Nat r) →
  Partition.weightedMass (padNatVector bound vector)
  ≡ Partition.weightedMass vector
padWeightedMass = padWeightedMassFrom 1

widenPartValue :
  ∀ {r n : Nat} (bound : r ≤ n) (index : Fin r) →
  Partition.partValue (widenFin bound index)
  ≡ Partition.partValue index
widenPartValue bound index = cong suc (widenFinToNat bound index)

------------------------------------------------------------------------
-- Pure finite representation machinery; no partition admissibility is assumed.
------------------------------------------------------------------------
