module DASHI.Information.PNFFiniteBilinearExpansionExact where

-- Reusable finite distributive algebra used by the covariance and
-- equicorrelation proof lanes; depends on the existing exact ring laws.
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Fin.Base using (Fin)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Ring
import DASHI.Information.PNFFiniteSumExchangeExact as Exchange

sumFinMulRight :
  (K : Ring.ExactOrderedCommutativeRing) →
  {n : Nat} →
  (f : Fin n → Scalar.Scalar (Ring.orderedScalar K)) →
  (a : Scalar.Scalar (Ring.orderedScalar K)) →
  Ring.sumFin (Ring.orderedScalar K)
    (λ i → Scalar._*_ (Ring.orderedScalar K) (f i) a)
  ≡ Scalar._*_ (Ring.orderedScalar K)
      (Ring.sumFin (Ring.orderedScalar K) f) a
sumFinMulRight K f a =
  trans
    (Ring.sumFinCong (Ring.orderedScalar K)
      (λ i → Ring.mulCommutative K (f i) a))
    (trans
      (Ring.sumFinMulLeft K a f)
      (Ring.mulCommutative K a
        (Ring.sumFin (Ring.orderedScalar K) f)))

-- One matrix column contracted with a vector is a linear functional.
-- Pulling a fixed scalar through it is an exact finite lemma.
rowProjectionScale :
  (K : Ring.ExactOrderedCommutativeRing) →
  {p : Nat} →
  (a : Scalar.Scalar (Ring.orderedScalar K)) →
  (x v : Fin p → Scalar.Scalar (Ring.orderedScalar K)) →
  Ring.sumFin (Ring.orderedScalar K)
    (λ i → Scalar._*_ (Ring.orderedScalar K)
      a (Scalar._*_ (Ring.orderedScalar K) (x i) (v i)))
  ≡
  Scalar._*_ (Ring.orderedScalar K) a
    (Ring.sumFin (Ring.orderedScalar K)
      (λ i → Scalar._*_ (Ring.orderedScalar K) (x i) (v i)))
rowProjectionScale K a x v =
  Ring.sumFinMulLeft K a
    (λ i → Scalar._*_ (Ring.orderedScalar K) (x i) (v i))

-- A completely source-independent two-axis Fubini fact,
-- useful for time/predicate and time/asset index exchange.
finiteCovarianceSumExchange :
  (K : Ring.ExactOrderedCommutativeRing) →
  {n p : Nat} →
  (term : Fin n → Fin p →
    Scalar.Scalar (Ring.orderedScalar K)) →
  Ring.sumFin (Ring.orderedScalar K)
    (λ t → Ring.sumFin (Ring.orderedScalar K) (λ i → term t i))
  ≡
  Ring.sumFin (Ring.orderedScalar K)
    (λ i → Ring.sumFin (Ring.orderedScalar K) (λ t → term t i))
finiteCovarianceSumExchange K = Exchange.finiteSumExchange K
