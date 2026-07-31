module DASHI.Physics.YangMills.BalabanClayGate4IpsenRehmanPrimaryCorollary214Exact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4IpsenRehmanDeterminantLossExact as Existing

------------------------------------------------------------------------
-- Exact primary form of Ipsen--Rehman Corollary 2.14.
--
-- Ilse C. F. Ipsen and Rizwana Rehman,
-- "Perturbation Bounds for Determinants and Characteristic Polynomials",
-- SIAM Journal on Matrix Analysis and Applications 30 (2008), 762--776.
-- DOI: 10.1137/070704770.
--
-- For A nonsingular,
--
-- |det(A+E)-det(A)| / |det(A)|
--   <= (1 + ||A^-1||_2 ||E||_2)^n - 1.
--
-- The multiplicative determinant bound and its exponential weakening are
-- derived consequences.  Corollary 2.14 itself does not require
-- ||A^-1|| ||E|| < 1 for a fixed finite n; such a smallness condition is needed
-- separately when the RG requires a uniformly controlled multiplier.
------------------------------------------------------------------------

data Truth : Set where
  truth : Truth

record IpsenRehmanCorollary214Data
    (Matrix Scalar : Set) : Set₁ where
  field
    referenceMatrix perturbationMatrix perturbedMatrix : Matrix
    dimension : Nat

    determinant : Matrix → Scalar
    inverseReferenceNorm perturbationNorm relativeSize : Scalar

    zero one : Scalar
    add subtract multiply power exponential absolute : Scalar → Scalar → Scalar
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

    relativeSizeMeaning :
      relativeSize ≡ multiply inverseReferenceNorm perturbationNorm

    perturbedMatrixMeaning : Truth

    -- Literal relative-difference statement of Corollary 2.14 after clearing
    -- the nonnegative reference determinant denominator.
    primaryRelativeDifferenceBound :
      LessEqual
        (absolute
          (subtract
            (determinant perturbedMatrix)
            (determinant referenceMatrix))
          one)
        (multiply
          (determinant referenceMatrix)
          (subtract
            (power (add one relativeSize)
              (naturalScalar dimension))
            one))

    determinantBelowReferencePlusAbsoluteDifference :
      LessEqual
        (determinant perturbedMatrix)
        (add
          (determinant referenceMatrix)
          (absolute
            (subtract
              (determinant perturbedMatrix)
              (determinant referenceMatrix))
            one))

    addRelativeDifferenceRegroups :
      add
        (determinant referenceMatrix)
        (multiply
          (determinant referenceMatrix)
          (subtract
            (power (add one relativeSize)
              (naturalScalar dimension))
            one))
      ≡ multiply
          (determinant referenceMatrix)
          (power (add one relativeSize)
            (naturalScalar dimension))

    addMonotoneRight : ∀ {lower upper} common →
      LessEqual lower upper →
      LessEqual (add common lower) (add common upper)

    binomialPowerBelowExponential :
      LessEqual
        (power (add one relativeSize)
          (naturalScalar dimension))
        (exponential
          (multiply (naturalScalar dimension) relativeSize)
          one)

open IpsenRehmanCorollary214Data public

primaryRelativeDifferenceImpliesMultiplicativeBound :
  ∀ {Matrix Scalar}
    (dataSet : IpsenRehmanCorollary214Data Matrix Scalar) →
  LessEqual dataSet
    (determinant dataSet (perturbedMatrix dataSet))
    (multiply dataSet
      (determinant dataSet (referenceMatrix dataSet))
      (power dataSet
        (add dataSet (one dataSet) (relativeSize dataSet))
        (naturalScalar dataSet (dimension dataSet))))
primaryRelativeDifferenceImpliesMultiplicativeBound dataSet =
  transitive dataSet
    (determinantBelowReferencePlusAbsoluteDifference dataSet)
    (subst
      (λ upper → LessEqual dataSet
        (add dataSet
          (determinant dataSet (referenceMatrix dataSet))
          (absolute dataSet
            (subtract dataSet
              (determinant dataSet (perturbedMatrix dataSet))
              (determinant dataSet (referenceMatrix dataSet)))
            (one dataSet)))
        upper)
      (addRelativeDifferenceRegroups dataSet)
      (addMonotoneRight dataSet
        (determinant dataSet (referenceMatrix dataSet))
        (primaryRelativeDifferenceBound dataSet)))

asExistingFiniteRelativeDeterminantPerturbation :
  ∀ {Matrix Scalar}
    (dataSet : IpsenRehmanCorollary214Data Matrix Scalar) →
  Existing.FiniteRelativeDeterminantPerturbation Matrix Scalar
asExistingFiniteRelativeDeterminantPerturbation dataSet = record
  { referenceMatrix = referenceMatrix dataSet
  ; perturbationMatrix = perturbationMatrix dataSet
  ; perturbedMatrix = perturbedMatrix dataSet
  ; dimension = dimension dataSet
  ; determinant = determinant dataSet
  ; inverseReferenceNorm = inverseReferenceNorm dataSet
  ; perturbationNorm = perturbationNorm dataSet
  ; relativePerturbation = relativeSize dataSet
  ; one = one dataSet
  ; add = add dataSet
  ; multiply = multiply dataSet
  ; power = power dataSet
  ; exponential = exponential dataSet
  ; naturalScalar = naturalScalar dataSet
  ; LessEqual = LessEqual dataSet
  ; Nonnegative = Nonnegative dataSet
  ; transitive = transitive dataSet
  ; referenceDeterminantNonnegative = referenceDeterminantNonnegative dataSet
  ; multiplyMonotoneLeft = multiplyMonotoneLeft dataSet
  ; perturbedMatrixMeaning = Truth
  ; relativePerturbationMeaning = relativeSizeMeaning dataSet
  ; ipsenRehmanRelativeBound =
      primaryRelativeDifferenceImpliesMultiplicativeBound dataSet
  ; binomialPowerBelowExponential = binomialPowerBelowExponential dataSet
  }

primaryCorollary214DifferenceLevel : ProofLevel
primaryCorollary214DifferenceLevel = standardImported

relativeDifferenceToMultiplicativeBoundLevel : ProofLevel
relativeDifferenceToMultiplicativeBoundLevel = machineChecked

primaryCorollaryToExistingDeterminantCarrierLevel : ProofLevel
primaryCorollaryToExistingDeterminantCarrierLevel = machineChecked

finiteDeterminantExponentialWeakeningLevel : ProofLevel
finiteDeterminantExponentialWeakeningLevel = machineChecked

relativePerturbationBelowOneRequiredByCorollary214 : ProofLevel
relativePerturbationBelowOneRequiredByCorollary214 = conjectural

physicalFiniteMatrixAndNormInputsLevel : ProofLevel
physicalFiniteMatrixAndNormInputsLevel = conditional

physicalUniformDeterminantMultiplierSmallnessInputsLevel : ProofLevel
physicalUniformDeterminantMultiplierSmallnessInputsLevel = conditional
