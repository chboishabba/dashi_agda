module DASHI.Information.PNFEquicorrelationPositiveExact where

-- Economics: an exact positive-correlation parameter region. The full
-- negative-rho admissible range requires the zero-sum dimension theorem.
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Fin.Base using (Fin)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Ring
import DASHI.Information.PNFFiniteGramPositiveExact as PSD
import DASHI.Information.PNFFiniteCovarianceEconomicsExact as Econ
import DASHI.Information.PNFFiniteBilinearExpansionExact as Bilinear

private
  SOf : Ring.ExactOrderedCommutativeRing → Set
  SOf K = Scalar.Scalar (Ring.orderedScalar K)

switchFirstFactors :
  (K : Ring.ExactOrderedCommutativeRing) →
  (x a b : SOf K) →
  Scalar._*_ (Ring.orderedScalar K) x
    (Scalar._*_ (Ring.orderedScalar K) a b)
  ≡
  Scalar._*_ (Ring.orderedScalar K) a
    (Scalar._*_ (Ring.orderedScalar K) x b)
switchFirstFactors K x a b =
  let S = Ring.orderedScalar K in
  trans
    (Ring.mulCommutative K x (Scalar._*_ S a b))
    (trans
      (sym (Ring.mulAssociative K a b x))
      (cong (Scalar._*_ S a)
        (Ring.mulCommutative K b x)))

equiQuadratic :
  (K : Ring.ExactOrderedCommutativeRing) →
  {p : Nat} → (rho : SOf K) →
  (v : Fin p → SOf K) → SOf K
equiQuadratic K rho v =
  Ring.sumFin (Ring.orderedScalar K)
    (λ i → Scalar._*_ (Ring.orderedScalar K)
      (v i) (Econ.equiOperator K rho v i))

equiQuadraticDecomposition :
  (K : Ring.ExactOrderedCommutativeRing) →
  {p : Nat} → (rho : SOf K) →
  (v : Fin p → SOf K) →
  equiQuadratic K rho v ≡
  Scalar._+_ (Ring.orderedScalar K)
    (Scalar._*_ (Ring.orderedScalar K)
      (Scalar._+_ (Ring.orderedScalar K)
        (Scalar.one (Ring.orderedScalar K))
        (Scalar.neg (Ring.orderedScalar K) rho))
      (Ring.sumFin (Ring.orderedScalar K)
        (λ i → Scalar._*_ (Ring.orderedScalar K) (v i) (v i))))
    (Scalar._*_ (Ring.orderedScalar K) rho
      (Scalar._*_ (Ring.orderedScalar K)
        (Ring.sumFin (Ring.orderedScalar K) v)
        (Ring.sumFin (Ring.orderedScalar K) v)))
equiQuadraticDecomposition K rho v =
  let S = Ring.orderedScalar K
      alpha = Scalar._+_ S (Scalar.one S) (Scalar.neg S rho)
      total = Ring.sumFin S v
  in
  trans
    (Ring.sumFinCong S
      (λ i → Ring.mulDistributesOverAdditionRight K
        (v i) (Scalar._*_ S alpha (v i))
        (Scalar._*_ S rho total)))
    (trans
      (Ring.sumFinAdd K
        (λ i → Scalar._*_ S (v i) (Scalar._*_ S alpha (v i)))
        (λ i → Scalar._*_ S (v i) (Scalar._*_ S rho total)))
      (cong₂ (Scalar._+_ S)
        (trans
          (Ring.sumFinCong S
            (λ i → switchFirstFactors K (v i) alpha (v i)))
          (Ring.sumFinMulLeft K alpha
            (λ i → Scalar._*_ S (v i) (v i))))
        (trans
          (Ring.sumFinCong S
            (λ i → switchFirstFactors K (v i) rho total))
          (trans
            (Ring.sumFinMulLeft K rho
              (λ i → Scalar._*_ S (v i) total))
            (cong (Scalar._*_ S rho)
              (Bilinear.sumFinMulRight K v total))))))
