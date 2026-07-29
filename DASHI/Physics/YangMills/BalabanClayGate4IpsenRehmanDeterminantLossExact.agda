module DASHI.Physics.YangMills.BalabanClayGate4IpsenRehmanDeterminantLossExact where

open import Agda.Builtin.Nat using (Nat)

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
-- perturbation bounds.  The physical Hessian application below uses only a
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
    add multiply natScale power exponential : Scalar → Scalar → Scalar
    LessEqual Nonnegative : Scalar → Scalar → Set

    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    referenceDeterminantNonnegative :
      Nonnegative one (determinant referenceMatrix)

    multiplyMonotoneLeft : ∀ {left lower upper} →
      Nonnegative one left → LessEqual lower upper →
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
            (natScale one (recordNat dimension))))

    -- Standard scalar estimate (1+x)^n <= exp(nx), x >= 0.
    binomialPowerBelowExponential :
      LessEqual
        (power (add one relativePerturbation)
          (natScale one (recordNat dimension)))
        (exponential
          (natScale relativePerturbation (recordNat dimension)) one)

  where
  recordNat : Nat → Scalar
  recordNat zero = one
  recordNat (suc n) = add one (recordNat n)

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
        (natScale dataSet (relativePerturbation dataSet)
          (recordNat dataSet (dimension dataSet)))
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
          (natScale (determinantData scale traversal)
            (relativePerturbation (determinantData scale traversal))
            (recordNat (determinantData scale traversal)
              (dimension (determinantData scale traversal))))
          (one (determinantData scale traversal))

open PhysicalRelativeHessianDeterminantMeaning public

ipsenRehmanStatementProvenanceLevel : ProofLevel
ipsenRehmanStatementProvenanceLevel = standardImported

finiteDeterminantExponentialLossAssemblyLevel : ProofLevel
finiteDeterminantExponentialLossAssemblyLevel = machineChecked

physicalReferenceHessianInvertibilityInputsLevel : ProofLevel
physicalReferenceHessianInvertibilityInputsLevel = conditional

physicalHessianPerturbationNormInputsLevel : ProofLevel
physicalHessianPerturbationNormInputsLevel = conditional

physicalIpsenRehmanNormIdentificationInputsLevel : ProofLevel
physicalIpsenRehmanNormIdentificationInputsLevel = conditional
