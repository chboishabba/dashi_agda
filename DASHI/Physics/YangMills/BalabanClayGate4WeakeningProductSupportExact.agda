module DASHI.Physics.YangMills.BalabanClayGate4WeakeningProductSupportExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Product-local weakening support.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
--
-- A cluster activity is assembled from local weakened factors. If every
-- factor in a selected cluster has zero derivative with respect to a boundary
-- parameter, the Leibniz recursion forces the whole product derivative to be
-- zero. Thus cluster local influence reduces to the literal support theorem
-- for one local factor.
------------------------------------------------------------------------

data _∈_ {A : Set} (value : A) : List A → Set where
  here : ∀ {values} → value ∈ (value ∷ values)
  there : ∀ {other values} → value ∈ values → value ∈ (other ∷ values)

record ProductDerivativeAlgebra (Value : Set) : Set₁ where
  field
    zero one : Value
    add multiply : Value → Value → Value

    addZeroLeft : ∀ value → add zero value ≡ value
    multiplyZeroLeft : ∀ value → multiply zero value ≡ zero
    multiplyZeroRight : ∀ value → multiply value zero ≡ zero

open ProductDerivativeAlgebra public

record FiniteProductDerivative
    (Index Parameter Value : Set) : Set₁ where
  field
    algebra : ProductDerivativeAlgebra Value
    factor derivativeFactor : Index → Parameter → Value

    product : List Index → Parameter → Value
    derivativeProduct : List Index → Parameter → Value

    productNil : ∀ parameter → product [] parameter ≡ one algebra
    productCons : ∀ index indices parameter →
      product (index ∷ indices) parameter
      ≡ multiply algebra (factor index parameter)
          (product indices parameter)

    derivativeNil : ∀ parameter →
      derivativeProduct [] parameter ≡ zero algebra

    derivativeCons : ∀ index indices parameter →
      derivativeProduct (index ∷ indices) parameter
      ≡ add algebra
          (multiply algebra (derivativeFactor index parameter)
            (product indices parameter))
          (multiply algebra (factor index parameter)
            (derivativeProduct indices parameter))

open FiniteProductDerivative public

allFactorDerivativesZeroImpliesProductDerivativeZero :
  ∀ {Index Parameter Value}
    (dataSet : FiniteProductDerivative Index Parameter Value)
    indices parameter →
  (∀ index → index ∈ indices →
    derivativeFactor dataSet index parameter ≡ zero (algebra dataSet)) →
  derivativeProduct dataSet indices parameter ≡ zero (algebra dataSet)
allFactorDerivativesZeroImpliesProductDerivativeZero dataSet [] parameter allZero =
  derivativeNil dataSet parameter
allFactorDerivativesZeroImpliesProductDerivativeZero
    dataSet (index ∷ indices) parameter allZero =
  trans
    (derivativeCons dataSet index indices parameter)
    (trans
      (cong
        (λ selected →
          add (algebra dataSet)
            (multiply (algebra dataSet) selected
              (product dataSet indices parameter))
            (multiply (algebra dataSet)
              (factor dataSet index parameter)
              (derivativeProduct dataSet indices parameter)))
        (allZero index here))
      (trans
        (cong
          (λ selected →
            add (algebra dataSet)
              (multiply (algebra dataSet) (zero (algebra dataSet))
                (product dataSet indices parameter))
              (multiply (algebra dataSet)
                (factor dataSet index parameter) selected))
          (allFactorDerivativesZeroImpliesProductDerivativeZero
            dataSet indices parameter
            (λ selected membership → allZero selected (there membership))))
        (trans
          (cong
            (λ selected →
              add (algebra dataSet) selected
                (multiply (algebra dataSet)
                  (factor dataSet index parameter) (zero (algebra dataSet))))
            (multiplyZeroLeft (algebra dataSet)
              (product dataSet indices parameter)))
          (trans
            (cong (add (algebra dataSet) (zero (algebra dataSet)))
              (multiplyZeroRight (algebra dataSet)
                (factor dataSet index parameter)))
            (addZeroLeft (algebra dataSet) (zero (algebra dataSet)))))))

weakeningProductLocalInfluenceLevel : ProofLevel
weakeningProductLocalInfluenceLevel = machineChecked

physicalWeakeningLocalFactorSupportInputsLevel : ProofLevel
physicalWeakeningLocalFactorSupportInputsLevel = conditional
