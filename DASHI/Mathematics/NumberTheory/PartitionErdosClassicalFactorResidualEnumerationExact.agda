module DASHI.Mathematics.NumberTheory.PartitionErdosClassicalFactorResidualEnumerationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- P. Erdos,
-- "On an Elementary Proof of Some Asymptotic Formulas in the Theory of
-- Partitions", Annals of Mathematics (2) 43 (1942), 437--450.
-- DOI: 10.2307/1968802.
--
-- CLASSICAL r = k*v RESIDUAL ENUMERATION
--
-- Build the conventional finite residual list by increasing r=1,...,n.  Each
-- r-block consists of
--
--   positive factor pair r = k*v
--   × canonical partition of n-r
--   × unit u : Fin(v).
--
-- Canonical grade-(n-r) vectors are zero-padded into ambient dimension n.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Fin.Base using (Fin; fromℕ<)
import Data.Fin.Properties as FinP
open import Data.List.Base using (map; _++_)
open import Data.Nat.Base using (_≤_; _∸_; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Data.Vec.Base using (Vec)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Mathematics.NumberTheory.FiniteAllFinEnumerationExact as Finite
import DASHI.Mathematics.NumberTheory.FiniteNatVectorZeroPaddingExact as Pad
import DASHI.Mathematics.NumberTheory.FinitePositiveFactorPairExact as Factor
import DASHI.Mathematics.NumberTheory.FiniteProductEnumerationExact as Product
import DASHI.Mathematics.NumberTheory.PartitionErdosFiniteKeyEnumerationExact as Key
import DASHI.Mathematics.NumberTheory.PartitionMultiplicityCarrierExact as Partition
import DASHI.Mathematics.NumberTheory.PartitionMultiplicityEnumerationExact as Enumeration

------------------------------------------------------------------------
-- Elementary subtraction/order receipts.

differenceBound : (n r : Nat) → n ∸ r ≤ n
differenceBound zero r = z≤n
differenceBound (suc n) zero = NatP.≤-refl
differenceBound (suc n) (suc r) =
  NatP.≤-step (differenceBound n r)

differencePlus :
  ∀ {r n : Nat} → r ≤ n → (n ∸ r) + r ≡ n
differencePlus {zero} {n} z≤n = NatP.+-identityʳ n
differencePlus {suc r} {suc n} (s≤s bound) =
  trans
    (NatP.+-suc (n ∸ r) r)
    (cong suc (differencePlus bound))

dropPositiveBound :
  ∀ {r n : Nat} → suc r ≤ n → r ≤ n
dropPositiveBound {r} {zero} ()
dropPositiveBound {r} {suc n} (s≤s bound) =
  NatP.≤-step bound

------------------------------------------------------------------------
-- Turn the positive divisor v into a literal Fin r part coordinate.

divisorIndex :
  ∀ {r : Nat} → Factor.PositiveFactorPair r → Fin r
divisorIndex (Factor.positiveFactorPair zero () bound predecessor exact)
divisorIndex
  (Factor.positiveFactorPair (suc divisorPredecessor)
    positive bound predecessor exact) =
  fromℕ< bound

divisorIndexPartValue :
  ∀ {r : Nat} (pair : Factor.PositiveFactorPair r) →
  Partition.partValue (divisorIndex pair) ≡ Factor.divisor pair
divisorIndexPartValue
  (Factor.positiveFactorPair zero () bound predecessor exact)
divisorIndexPartValue
  (Factor.positiveFactorPair (suc divisorPredecessor)
    positive bound predecessor exact) =
  cong suc (FinP.toℕ-fromℕ< bound)

ambientDivisorIndex :
  ∀ {n r : Nat} →
  r ≤ n → Factor.PositiveFactorPair r → Fin n
ambientDivisorIndex bound pair =
  Pad.widenFin bound (divisorIndex pair)

ambientDivisorPartValue :
  ∀ {n r : Nat}
    (bound : r ≤ n) (pair : Factor.PositiveFactorPair r) →
  Partition.partValue (ambientDivisorIndex bound pair)
  ≡ Factor.divisor pair
ambientDivisorPartValue bound pair =
  trans
    (Pad.widenPartValue bound (divisorIndex pair))
    (divisorIndexPartValue pair)

------------------------------------------------------------------------
-- Residual key construction for one classical factor/partition/unit datum.

padResidualVector :
  (n r : Nat) → Vec Nat (n ∸ r) → Vec Nat n
padResidualVector n r =
  Pad.padNatVector (differenceBound n r)

classicalResidualKey :
  ∀ {n r : Nat}
    (bound : r ≤ n)
    (pair : Factor.PositiveFactorPair r)
    (vector : Vec Nat (n ∸ r)) →
  Fin (Partition.partValue (ambientDivisorIndex bound pair)) →
  Key.ResidualKey n
classicalResidualKey bound pair vector unit =
  padResidualVector _ _ vector
  , ambientDivisorIndex bound pair
  , Factor.predecessor pair
  , unit

------------------------------------------------------------------------
-- Exact grade equation for every classical datum whose residual vector has
-- canonical mass n-r.

classicalResidualTotalExact :
  ∀ {n r : Nat}
    (bound : r ≤ n)
    (pair : Factor.PositiveFactorPair r)
    (vector : Vec Nat (n ∸ r)) →
  Partition.weightedMass vector ≡ n ∸ r →
  (unit : Fin (Partition.partValue (ambientDivisorIndex bound pair))) →
  Partition.weightedMass
      (Key.residualVector (classicalResidualKey bound pair vector unit))
    + Key.residualCopies (classicalResidualKey bound pair vector unit)
      * Partition.partValue
          (Key.residualIndex (classicalResidualKey bound pair vector unit))
  ≡ n
classicalResidualTotalExact {n} {r} bound pair vector vectorMass unit =
  trans
    (cong
      (λ mass →
        mass
        + suc (Factor.predecessor pair)
          * Partition.partValue (ambientDivisorIndex bound pair))
      (trans
        (Pad.padWeightedMass (differenceBound n r) vector)
        vectorMass))
    (trans
      (cong
        ((n ∸ r) +_)
        (trans
          (cong
            (suc (Factor.predecessor pair) *_)
            (ambientDivisorPartValue bound pair))
          (sym (Factor.productExact pair))))
      (differencePlus bound))

------------------------------------------------------------------------
-- Executable nested list construction.

residualsForVector :
  ∀ {n r : Nat}
    (bound : r ≤ n)
    (pair : Factor.PositiveFactorPair r)
    (vector : Vec Nat (n ∸ r)) →
  List (Key.ResidualKey n)
residualsForVector bound pair vector =
  map
    (classicalResidualKey bound pair vector)
    (Finite.allFin
      (Partition.partValue (ambientDivisorIndex bound pair)))

residualsForPair :
  ∀ {n r : Nat}
    (bound : r ≤ n)
    (pair : Factor.PositiveFactorPair r) →
  List (Key.ResidualKey n)
residualsForPair {n} {r} bound pair =
  Product.concatMap
    (residualsForVector bound pair)
    (Enumeration.partitionMultiplicityVectors (n ∸ r))

residualBlock :
  ∀ {n r : Nat} →
  suc zero ≤ r → r ≤ n → List (Key.ResidualKey n)
residualBlock {n} {r} positive bound =
  Product.concatMap
    (residualsForPair bound)
    (Factor.positiveFactorPairs r positive)

classicalResidualsUpTo :
  (n current : Nat) → current ≤ n → List (Key.ResidualKey n)
classicalResidualsUpTo n zero z≤n = []
classicalResidualsUpTo n (suc current) bound =
  classicalResidualsUpTo n current (dropPositiveBound bound)
  ++ residualBlock
       (s≤s z≤n)
       bound

classicalFactorResidualEnumeration :
  (n : Nat) → List (Key.ResidualKey n)
classicalFactorResidualEnumeration n =
  classicalResidualsUpTo n n NatP.≤-refl

------------------------------------------------------------------------
-- This owner constructs the conventional finite list.  Its fold evaluation and
-- exact permutation with the admissible residual normal form are downstream.
------------------------------------------------------------------------
