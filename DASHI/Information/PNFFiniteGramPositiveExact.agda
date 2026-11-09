module DASHI.Information.PNFFiniteGramPositiveExact where

-- Genuine finite sum-of-squares positivity for PNF or returns matrices.
-- The ordered-ring positive-cone axioms are explicit; no empirical/null
-- model or eigen-decomposition theorem is assumed.

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc)
import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Ring
import DASHI.Information.PNFFiniteCovarianceEconomicsExact as Matrix

record PositiveCone (K : Ring.ExactOrderedCommutativeRing) : Set₁ where
  private
    S = Ring.orderedScalar K
  field
    zeroNonnegative : Scalar._≤_ S (Scalar.zero S) (Scalar.zero S)
    addNonnegative :
      {a b : Scalar.Scalar S} →
      Scalar._≤_ S (Scalar.zero S) a →
      Scalar._≤_ S (Scalar.zero S) b →
      Scalar._≤_ S (Scalar.zero S) (Scalar._+_ S a b)
    squareNonnegative :
      (a : Scalar.Scalar S) →
      Scalar._≤_ S (Scalar.zero S) (Scalar._*_ S a a)

open PositiveCone public

sumFinNonnegative :
  (K : Ring.ExactOrderedCommutativeRing) →
  (P : PositiveCone K) → {n : Nat} →
  (f : Fin n → Scalar.Scalar (Ring.orderedScalar K)) →
  ((i : Fin n) →
    Scalar._≤_ (Ring.orderedScalar K)
      (Scalar.zero (Ring.orderedScalar K)) (f i)) →
  Scalar._≤_ (Ring.orderedScalar K)
    (Scalar.zero (Ring.orderedScalar K))
    (Ring.sumFin (Ring.orderedScalar K) f)
sumFinNonnegative K P {zero} f pointwise =
  PositiveCone.zeroNonnegative P
sumFinNonnegative K P {suc n} f pointwise =
  PositiveCone.addNonnegative P
    (pointwise zero)
    (sumFinNonnegative K P (λ i → f (suc i))
      (λ i → pointwise (suc i)))

projection :
  (K : Ring.ExactOrderedCommutativeRing) →
  {n p : Nat} → (X : Matrix.FiniteMatrix K n p) →
  (Fin p → Scalar.Scalar (Ring.orderedScalar K)) →
  Fin n → Scalar.Scalar (Ring.orderedScalar K)
projection K X v r =
  Ring.sumFin (Ring.orderedScalar K)
    (λ i → Scalar._*_ (Ring.orderedScalar K)
      (Matrix.entry X r i) (v i))

gramQuadratic :
  (K : Ring.ExactOrderedCommutativeRing) →
  {n p : Nat} → (X : Matrix.FiniteMatrix K n p) →
  (Fin p → Scalar.Scalar (Ring.orderedScalar K)) →
  Scalar.Scalar (Ring.orderedScalar K)
gramQuadratic K X v =
  Ring.sumFin (Ring.orderedScalar K)
    (λ r → Scalar._*_ (Ring.orderedScalar K)
      (projection K X v r) (projection K X v r))

finiteMatrixGramPositiveSemidefinite :
  (K : Ring.ExactOrderedCommutativeRing) →
  (P : PositiveCone K) →
  {n p : Nat} → (X : Matrix.FiniteMatrix K n p) →
  (v : Fin p → Scalar.Scalar (Ring.orderedScalar K)) →
  Scalar._≤_ (Ring.orderedScalar K)
    (Scalar.zero (Ring.orderedScalar K))
    (gramQuadratic K X v)
finiteMatrixGramPositiveSemidefinite K P X v =
  sumFinNonnegative K P
    (λ r → Scalar._*_ (Ring.orderedScalar K)
      (projection K X v r) (projection K X v r))
    (λ r → PositiveCone.squareNonnegative P (projection K X v r))
