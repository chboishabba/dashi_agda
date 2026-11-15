module DASHI.Information.PNFFiniteSumExchangeExact where

-- Finite Fubini identity: only commutative additive structure and
-- explicit Fin-indexed sums; no probability or limiting argument.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Ring

finiteSumExchange :
  (K : Ring.ExactOrderedCommutativeRing) →
  {n m : Nat} →
  (f : Fin n → Fin m →
     Scalar.Scalar (Ring.orderedScalar K)) →
  Ring.sumFin (Ring.orderedScalar K)
    (λ i → Ring.sumFin (Ring.orderedScalar K) (λ j → f i j))
  ≡
  Ring.sumFin (Ring.orderedScalar K)
    (λ j → Ring.sumFin (Ring.orderedScalar K) (λ i → f i j))
finiteSumExchange K {zero} {m} f =
  sym (Ring.sumFinAllZero K {m})
finiteSumExchange K {suc n} {m} f =
  trans
    (cong (Scalar._+_ (Ring.orderedScalar K)
      (Ring.sumFin (Ring.orderedScalar K) (λ j → f zero j)))
      (finiteSumExchange K (λ i j → f (suc i) j)))
    (sym (Ring.sumFinAdd K
      (λ j → f zero j)
      (λ j → Ring.sumFin (Ring.orderedScalar K)
        (λ i → f (suc i) j))))
