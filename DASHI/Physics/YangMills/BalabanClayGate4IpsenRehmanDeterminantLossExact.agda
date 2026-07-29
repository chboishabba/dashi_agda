module DASHI.Physics.YangMills.BalabanClayGate4IpsenRehmanDeterminantLossExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong₂; subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Primary provenance.
--
-- Ilse C. F. Ipsen and Rizwana Rehman,
-- "Perturbation Bounds for Determinants and Characteristic Polynomials",
-- SIAM Journal on Matrix Analysis and Applications 30 (2008), 762--776.
-- DOI: 10.1137/070704770.
--
-- The paper proves finite-dimensional absolute and relative determinant
-- perturbation bounds. The physical Hessian application below uses only a
-- finite matrix/operator carrier; no continuum or zeta-regularized determinant
-- is imported.
--
-- The exact physical specialization still has to establish invertibility of the
-- reference Hessian, identify the perturbation matrix, and bound
-- ||A^{-1}|| ||B|| in the selected operator norm.
------------------------------------------------------------------------

record FiniteRelativeDeterminantPerturbation
    (Matrix Scalar : Set) : Set₁ where
  field
    referenceMatrix perturbationMatrix perturbedMatrix : Matrix
    dimension : Nat

    determinant : Matrix → Scalar
    inverseReferenceNorm perturbationNorm relativePerturbation : Scalar

    one : Scalar
    add multiply power exponential : Scalar → Scalar → Scalar
    naturalScalar : Nat → Scalar
    LessEqual : Scalar → Scalar → Set
    Nonnegative : Scalar → Set

    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    referenceDeterminantNonnegative :
      Nonnegative (determinant referenceMatrix)

    multiplyMonotoneLeft : ∀ {left lower upper} →
      Nonnegative left → LessEqual lower upper →
      LessEqual (multiply left lower) (multiply left upper)

    perturbedMatrixMeaning : Set

    relativePerturbationMeaning :
      relativePerturbation
      ≡ multiply inverseReferenceNorm perturbationNorm

    -- Finite-dimensional relative determinant theorem in the selected norm.
    ipsenRehmanRelativeBound :
      LessEqual
        (determinant perturbedMatrix)
        (multiply (determinant referenceMatrix)
          (power (add one relativePerturbation)
            (naturalScalar dimension)))

    -- Standard scalar estimate (1+x)^n <= exp(nx), x >= 0.
    binomialPowerBelowExponential :
      LessEqual
        (power (add one relativePerturbation)
          (naturalScalar dimension))
        (exponential
          (multiply (naturalScalar dimension) relativePerturbation)
          one)

open FiniteRelativeDeterminantPerturbation public

-- The final multiplicative loss used by the compensated T-operation budget.
determinantPerturbationBelowExponentialLoss :
  ∀ {Matrix Scalar}
    (dataSet : FiniteRelativeDeterminantPerturbation Matrix Scalar) →
  LessEqual dataSet
    (determinant dataSet (perturbedMatrix dataSet))
    (multiply dataSet
      (determinant dataSet (referenceMatrix dataSet))
      (exponential dataSet
        (multiply dataSet
          (naturalScalar dataSet (dimension dataSet))
          (relativePerturbation dataSet))
        (one dataSet)))
determinantPerturbationBelowExponentialLoss dataSet =
  transitive dataSet
    (ipsenRehmanRelativeBound dataSet)
    (multiplyMonotoneLeft dataSet
      (referenceDeterminantNonnegative dataSet)
      (binomialPowerBelowExponential dataSet))

record PhysicalRelativeHessianDeterminantMeaning
    (Scale Traversal Matrix Scalar : Set) : Set₁ where
  field
    determinantData : Scale → Traversal →
      FiniteRelativeDeterminantPerturbation Matrix Scalar

    physicalDeterminant referenceDeterminant determinantMultiplier :
      Scale → Traversal → Scalar

    physicalDeterminantMeaning : ∀ scale traversal →
      physicalDeterminant scale traversal
      ≡ determinant (determinantData scale traversal)
          (perturbedMatrix (determinantData scale traversal))

    referenceDeterminantMeaning : ∀ scale traversal →
      referenceDeterminant scale traversal
      ≡ determinant (determinantData scale traversal)
          (referenceMatrix (determinantData scale traversal))

    determinantMultiplierMeaning : ∀ scale traversal →
      determinantMultiplier scale traversal
      ≡ exponential (determinantData scale traversal)
          (multiply (determinantData scale traversal)
            (naturalScalar (determinantData scale traversal)
              (dimension (determinantData scale traversal)))
            (relativePerturbation (determinantData scale traversal)))
          (one (determinantData scale traversal))

open PhysicalRelativeHessianDeterminantMeaning public

physicalDeterminantBelowIpsenRehmanMultiplier :
  ∀ {Scale Traversal Matrix Scalar}
    (meaning : PhysicalRelativeHessianDeterminantMeaning
      Scale Traversal Matrix Scalar)
    scale traversal →
  let dataSet = determinantData meaning scale traversal
  in LessEqual dataSet
      (physicalDeterminant meaning scale traversal)
      (multiply dataSet
        (referenceDeterminant meaning scale traversal)
        (determinantMultiplier meaning scale traversal))
physicalDeterminantBelowIpsenRehmanMultiplier meaning scale traversal =
  let dataSet = determinantData meaning scale traversal
      physicalEq = physicalDeterminantMeaning meaning scale traversal
      referenceEq = referenceDeterminantMeaning meaning scale traversal
      multiplierEq = determinantMultiplierMeaning meaning scale traversal
      rightEq = cong₂ (multiply dataSet) referenceEq multiplierEq
      base = determinantPerturbationBelowExponentialLoss dataSet
  in subst
      (λ upper → LessEqual dataSet
        (physicalDeterminant meaning scale traversal) upper)
      (sym rightEq)
      (subst
        (λ lower → LessEqual dataSet lower
          (multiply dataSet
            (determinant dataSet (referenceMatrix dataSet))
            (exponential dataSet
              (multiply dataSet
                (naturalScalar dataSet (dimension dataSet))
                (relativePerturbation dataSet))
              (one dataSet))))
        (sym physicalEq)
        base)

ipsenRehmanStatementProvenanceLevel : ProofLevel
ipsenRehmanStatementProvenanceLevel = standardImported

finiteDeterminantExponentialLossAssemblyLevel : ProofLevel
finiteDeterminantExponentialLossAssemblyLevel = machineChecked

physicalDeterminantMultiplierAssemblyLevel : ProofLevel
physicalDeterminantMultiplierAssemblyLevel = machineChecked

physicalReferenceHessianInvertibilityInputsLevel : ProofLevel
physicalReferenceHessianInvertibilityInputsLevel = conditional

physicalHessianPerturbationNormInputsLevel : ProofLevel
physicalHessianPerturbationNormInputsLevel = conditional

physicalIpsenRehmanNormIdentificationInputsLevel : ProofLevel
physicalIpsenRehmanNormIdentificationInputsLevel = conditional
