module DASHI.Algebra.BalancedTernaryFiniteCarrierExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Vec using (Vec; []; _∷_)

import DASHI.Algebra.Trit as Trit
import DASHI.Mathematics.NumberTheory.FiniteProductEnumerationExact as Product
import DASHI.Mathematics.NumberTheory.FiniteProductCardinalityExact as Cardinality
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex
import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact as Hecke

------------------------------------------------------------------------
-- Exact finite-carrier normal form:
--
--   Trit^n ≃ (Fin 3)^n
--
-- This pays the cardinality / enumeration side of the balanced-integer
-- reconstruction frontier using the repository's canonical finite-product
-- enumerator.  It does not by itself identify the positional integer map.

tritToFin3 : Trit.Trit → Fin 3
tritToFin3 Trit.neg = zero
tritToFin3 Trit.zer = suc zero
tritToFin3 Trit.pos = suc (suc zero)

fin3ToTrit : Fin 3 → Trit.Trit
fin3ToTrit zero = Trit.neg
fin3ToTrit (suc zero) = Trit.zer
fin3ToTrit (suc (suc zero)) = Trit.pos

finTritRoundTrip : (t : Trit.Trit) → fin3ToTrit (tritToFin3 t) ≡ t
finTritRoundTrip Trit.neg = refl
finTritRoundTrip Trit.zer = refl
finTritRoundTrip Trit.pos = refl

tritFinRoundTrip : (i : Fin 3) → tritToFin3 (fin3ToTrit i) ≡ i
tritFinRoundTrip zero = refl
tritFinRoundTrip (suc zero) = refl
tritFinRoundTrip (suc (suc zero)) = refl

mapToFin3 : ∀ {n} → Vec Trit.Trit n → Vec (Fin 3) n
mapToFin3 [] = []
mapToFin3 (t ∷ ts) = tritToFin3 t ∷ mapToFin3 ts

mapFromFin3 : ∀ {n} → Vec (Fin 3) n → Vec Trit.Trit n
mapFromFin3 [] = []
mapFromFin3 (i ∷ is) = fin3ToTrit i ∷ mapFromFin3 is

fromToFin3 :
  ∀ {n} (ts : Vec Trit.Trit n) →
  mapFromFin3 (mapToFin3 ts) ≡ ts
fromToFin3 [] = refl
fromToFin3 (t ∷ ts)
  rewrite finTritRoundTrip t
        | fromToFin3 ts = refl

toFromFin3 :
  ∀ {n} (is : Vec (Fin 3) n) →
  mapToFin3 (mapFromFin3 is) ≡ is
toFromFin3 [] = refl
toFromFin3 (i ∷ is)
  rewrite tritFinRoundTrip i
        | toFromFin3 is = refl

canonicalFin3VectorEnumeration :
  (n : Nat) → List (Vec (Fin 3) n)
canonicalFin3VectorEnumeration n =
  Product.uniqueFinVectorPower 3 n

canonicalFin3VectorEnumerationComplete :
  ∀ {n} (v : Vec (Fin 3) n) →
  v ∈ canonicalFin3VectorEnumeration n
canonicalFin3VectorEnumerationComplete =
  Product.uniqueFinVectorPowerComplete

canonicalFin3VectorEnumerationLength :
  (n : Nat) →
  Reindex.listLength (canonicalFin3VectorEnumeration n)
  ≡ Hecke.powNat 3 n
canonicalFin3VectorEnumerationLength =
  Cardinality.uniqueFinVectorPowerLength 3

record BalancedTernaryFiniteCarrierBoundary : Set where
  constructor balancedTernaryFiniteCarrierBoundary
  field
    tritFin3BijectionPaid : Bool
    vectorBijectionPaid : Bool
    canonicalUniqueEnumerationReused : Bool
    exactPowerThreeCardinalityPaid : Bool
    positionalIntegerInjectivityPaidByCardinalityAlone : Bool

canonicalBalancedTernaryFiniteCarrierBoundary :
  BalancedTernaryFiniteCarrierBoundary
canonicalBalancedTernaryFiniteCarrierBoundary =
  balancedTernaryFiniteCarrierBoundary true true true true false
