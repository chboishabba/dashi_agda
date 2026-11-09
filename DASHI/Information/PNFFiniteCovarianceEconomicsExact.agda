module DASHI.Information.PNFFiniteCovarianceEconomicsExact where

-- Shared finite matrix mathematics.  The PNF and financial interpretations
-- require separate empirical and semantic receipts.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Ring

private
  SOf : Ring.ExactOrderedCommutativeRing → Set
  SOf K = Scalar.Scalar (Ring.orderedScalar K)

-- Source-bound *finite* row/column geometry: n observations, p predicates
-- or assets. Centering and unbiased 1/(n-1) normalization are later gates.
record FiniteMatrix (K : Ring.ExactOrderedCommutativeRing)
                    (n p : Nat) : Set where
  field
    entry : Fin n → Fin p → SOf K

open FiniteMatrix public

gram :
  (K : Ring.ExactOrderedCommutativeRing) →
  {n p : Nat} → FiniteMatrix K n p →
  Fin p → Fin p → SOf K
gram K X i j =
  Ring.sumFin (Ring.orderedScalar K)
    (λ r → Scalar._*_ (Ring.orderedScalar K)
      (entry X r i) (entry X r j))

sampleGramSymmetric :
  (K : Ring.ExactOrderedCommutativeRing) →
  {n p : Nat} → (X : FiniteMatrix K n p) →
  (i j : Fin p) → gram K X i j ≡ gram K X j i
sampleGramSymmetric K X i j =
  Ring.sumFinCong (Ring.orderedScalar K)
    (λ r → Ring.mulCommutative K (entry X r i) (entry X r j))

-- Exact equicorrelation / rank-one population operator.
-- This is *not* an estimate from a finite observed return matrix.
equiOperator :
  (K : Ring.ExactOrderedCommutativeRing) → {p : Nat} →
  (rho : SOf K) → (v : Fin p → SOf K) →
  Fin p → SOf K
equiOperator K rho v i =
  let S = Ring.orderedScalar K in
  Scalar._+_ S
    (Scalar._*_ S (Scalar._+_ S (Scalar.one S) (Scalar.neg S rho)) (v i))
    (Scalar._*_ S rho (Ring.sumFin S v))

-- The entire sum-zero subspace is an eigenspace with eigenvalue 1-rho.
equiZeroSumEigen :
  (K : Ring.ExactOrderedCommutativeRing) → {p : Nat} →
  (rho : SOf K) → (v : Fin p → SOf K) →
  Ring.sumFin (Ring.orderedScalar K) v ≡
    Scalar.zero (Ring.orderedScalar K) →
  (i : Fin p) →
  equiOperator K rho v i ≡
  Scalar._*_ (Ring.orderedScalar K)
    (Scalar._+_ (Ring.orderedScalar K)
      (Scalar.one (Ring.orderedScalar K))
      (Scalar.neg (Ring.orderedScalar K) rho))
    (v i)
equiZeroSumEigen K rho v zeroSum i
  rewrite zeroSum
        | Ring.mulZeroRight K rho =
  Ring.addZeroRight K
    (Scalar._*_ (Ring.orderedScalar K)
      (Scalar._+_ (Ring.orderedScalar K)
        (Scalar.one (Ring.orderedScalar K))
        (Scalar.neg (Ring.orderedScalar K) rho))
      (v i))

-- A concrete scalar corresponding to the number of coordinates.
dimensionScalar :
  (K : Ring.ExactOrderedCommutativeRing) →
  Nat → SOf K
dimensionScalar K zero = Scalar.zero (Ring.orderedScalar K)
dimensionScalar K (suc n) =
  Scalar._+_ (Ring.orderedScalar K)
    (Scalar.one (Ring.orderedScalar K)) (dimensionScalar K n)

sumConstantOne :
  (K : Ring.ExactOrderedCommutativeRing) →
  {p : Nat} →
  Ring.sumFin (Ring.orderedScalar K)
    (λ (_ : Fin p) → Scalar.one (Ring.orderedScalar K))
  ≡ dimensionScalar K p
sumConstantOne K {zero} = refl
sumConstantOne K {suc p} =
  cong (Scalar._+_ (Ring.orderedScalar K)
    (Scalar.one (Ring.orderedScalar K))) (sumConstantOne K {p})

-- The all-ones vector is an eigenvector. The eigenvalue here is given as
-- (1-rho) + rho * p. Its simplification to 1+(p-1)rho is the next algebraic
-- normal-form lemma; the statement has no division or asymptotic hypothesis.
equiMarketEigen :
  (K : Ring.ExactOrderedCommutativeRing) → {p : Nat} →
  (rho : SOf K) → (i : Fin p) →
  equiOperator K rho
    (λ (_ : Fin p) → Scalar.one (Ring.orderedScalar K)) i
  ≡
  Scalar._+_ (Ring.orderedScalar K)
    (Scalar._+_ (Ring.orderedScalar K)
      (Scalar.one (Ring.orderedScalar K))
      (Scalar.neg (Ring.orderedScalar K) rho))
    (Scalar._*_ (Ring.orderedScalar K) rho (dimensionScalar K p))
equiMarketEigen K {p} rho i
  rewrite sumConstantOne K {p} =
  cong (λ a → Scalar._+_ (Ring.orderedScalar K) a
      (Scalar._*_ (Ring.orderedScalar K) rho (dimensionScalar K p)))
    (trans
      (Ring.mulCommutative K
        (Scalar._+_ (Ring.orderedScalar K)
          (Scalar.one (Ring.orderedScalar K))
          (Scalar.neg (Ring.orderedScalar K) rho))
        (Scalar.one (Ring.orderedScalar K)))
      (Ring.mulOneLeft K
        (Scalar._+_ (Ring.orderedScalar K)
          (Scalar.one (Ring.orderedScalar K))
          (Scalar.neg (Ring.orderedScalar K) rho))))

-- The *population* equicorrelation operator becomes the identity at rho=0,
-- independent of the sample-size / MP asymptotic regime.
equiZeroCorrelationIsIdentity :
  (K : Ring.ExactOrderedCommutativeRing) → {p : Nat} →
  (v : Fin p → SOf K) → (i : Fin p) →
  equiOperator K (Scalar.zero (Ring.orderedScalar K)) v i ≡ v i
equiZeroCorrelationIsIdentity K v i
  rewrite Ring.negZero K
        | Ring.addZeroRight K (Scalar.one (Ring.orderedScalar K))
        | Ring.mulOneLeft K (v i)
        | Ring.mulZeroLeft K (Ring.sumFin (Ring.orderedScalar K) v) =
  Ring.addZeroRight K (v i)
