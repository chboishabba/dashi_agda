module DASHI.Physics.YangMills.BalabanClayGate4FiniteMatrixSpectrumDeterminantAssemblyExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4FiniteTangentMatrixRepresentationExact as Matrix
import DASHI.Physics.YangMills.BalabanClayGate4FiniteHermitianRayleighSpectrumExact as Spectrum
import DASHI.Physics.YangMills.BalabanClayGate4IpsenRehmanPrimaryCorollary214Exact as Determinant

------------------------------------------------------------------------
-- End-to-end finite Hessian assembly.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press (2012).
-- DOI: 10.1017/CBO9781139020411.
--
-- Ilse C. F. Ipsen and Rizwana Rehman,
-- "Perturbation Bounds for Determinants and Characteristic Polynomials",
-- SIAM Journal on Matrix Analysis and Applications 30 (2008), 762--776.
-- DOI: 10.1137/070704770.
--
-- This module composes the already-proved finite layers:
--
--   restricted operator split -> finite matrix split,
--   Hermitian coercivity -> spectral lower bound -> inverse norm,
--   Ipsen--Rehman relative difference -> multiplicative determinant bound.
--
-- It does not construct the physical tangent basis or prove coercivity. Those
-- remain explicit representation inputs.
------------------------------------------------------------------------

record FiniteMatrixSpectrumDeterminantAssembly
    (Index Operator MatrixCarrier Vector Scalar : Set) : Set₁ where
  field
    matrixRepresentation :
      Matrix.RestrictedHessianMatrixRepresentation
        Operator MatrixCarrier Vector

    inverseMeaning :
      Spectrum.FiniteHermitianInverseNormInstantiation
        Index Vector Scalar
    selectedIndex : Index

    determinantData :
      Determinant.IpsenRehmanCorollary214Data MatrixCarrier Scalar

    determinantReferenceMatrixExact :
      Determinant.referenceMatrix determinantData
      ≡ Matrix.referenceMatrix matrixRepresentation

    determinantPerturbationMatrixExact :
      Determinant.perturbationMatrix determinantData
      ≡ Matrix.remainderMatrix matrixRepresentation

    determinantPhysicalMatrixExact :
      Determinant.perturbedMatrix determinantData
      ≡ Matrix.physicalMatrix matrixRepresentation

    determinantInverseNormExact :
      Determinant.inverseReferenceNorm determinantData
      ≡ Spectrum.inverseOperatorNorm inverseMeaning selectedIndex

    ReferenceCoercivityMeaning : Set
    referenceCoercivityMeaning : ReferenceCoercivityMeaning

    MatrixSpectrumMeaning : Set
    matrixSpectrumMeaning : MatrixSpectrumMeaning

open FiniteMatrixSpectrumDeterminantAssembly public

assembledPhysicalMatrixSplit :
  ∀ {Index Operator MatrixCarrier Vector Scalar}
    (assembly : FiniteMatrixSpectrumDeterminantAssembly
      Index Operator MatrixCarrier Vector Scalar) →
  Matrix.physicalMatrix (matrixRepresentation assembly)
  ≡ Matrix.addMatrix (matrixRepresentation assembly)
      (Matrix.referenceMatrix (matrixRepresentation assembly))
      (Matrix.remainderMatrix (matrixRepresentation assembly))
assembledPhysicalMatrixSplit assembly =
  Matrix.physicalMatrixSplitsExactly (matrixRepresentation assembly)

assembledInverseNormBelowCoercivityReciprocal :
  ∀ {Index Operator MatrixCarrier Vector Scalar}
    (assembly : FiniteMatrixSpectrumDeterminantAssembly
      Index Operator MatrixCarrier Vector Scalar) →
  Spectrum.LessEqual (Spectrum.rayleigh (inverseMeaning assembly))
    (Spectrum.inverseOperatorNorm
      (inverseMeaning assembly) (selectedIndex assembly))
    (Spectrum.reciprocal (inverseMeaning assembly)
      (Spectrum.coercivityConstant
        (Spectrum.rayleigh (inverseMeaning assembly))
        (selectedIndex assembly)))
assembledInverseNormBelowCoercivityReciprocal assembly =
  Spectrum.finiteHermitianInverseNormBelowCoercivityReciprocal
    (inverseMeaning assembly) (selectedIndex assembly)

assembledPhysicalDeterminantBelowPrimaryMultiplier :
  ∀ {Index Operator MatrixCarrier Vector Scalar}
    (assembly : FiniteMatrixSpectrumDeterminantAssembly
      Index Operator MatrixCarrier Vector Scalar) →
  Determinant.LessEqual (determinantData assembly)
    (Determinant.determinant (determinantData assembly)
      (Matrix.physicalMatrix (matrixRepresentation assembly)))
    (Determinant.multiply (determinantData assembly)
      (Determinant.determinant (determinantData assembly)
        (Matrix.referenceMatrix (matrixRepresentation assembly)))
      (Determinant.power (determinantData assembly)
        (Determinant.add (determinantData assembly)
          (Determinant.one (determinantData assembly))
          (Determinant.relativeSize (determinantData assembly)))
        (Determinant.naturalScalar (determinantData assembly)
          (Determinant.dimension (determinantData assembly)))))
assembledPhysicalDeterminantBelowPrimaryMultiplier assembly =
  let
    dataSet = determinantData assembly
    base = Determinant.primaryRelativeDifferenceImpliesMultiplicativeBound dataSet
    physicalEquality = cong (Determinant.determinant dataSet)
      (determinantPhysicalMatrixExact assembly)
    referenceEquality = cong (Determinant.determinant dataSet)
      (determinantReferenceMatrixExact assembly)
    multiplier = Determinant.power dataSet
      (Determinant.add dataSet
        (Determinant.one dataSet)
        (Determinant.relativeSize dataSet))
      (Determinant.naturalScalar dataSet
        (Determinant.dimension dataSet))
  in
  subst
    (λ lower → Determinant.LessEqual dataSet lower
      (Determinant.multiply dataSet
        (Determinant.determinant dataSet
          (Matrix.referenceMatrix (matrixRepresentation assembly)))
        multiplier))
    physicalEquality
    (subst
      (λ referenceDeterminant → Determinant.LessEqual dataSet
        (Determinant.determinant dataSet
          (Determinant.perturbedMatrix dataSet))
        (Determinant.multiply dataSet referenceDeterminant multiplier))
      referenceEquality
      base)

finiteMatrixSpectrumDeterminantAssemblyLevel : ProofLevel
finiteMatrixSpectrumDeterminantAssemblyLevel = machineChecked

assembledPhysicalMatrixSplitLevel : ProofLevel
assembledPhysicalMatrixSplitLevel = machineChecked

assembledInverseNormBoundLevel : ProofLevel
assembledInverseNormBoundLevel = machineChecked

assembledPrimaryDeterminantMultiplierLevel : ProofLevel
assembledPrimaryDeterminantMultiplierLevel = machineChecked

physicalTangentMatrixAssemblyInputsLevel : ProofLevel
physicalTangentMatrixAssemblyInputsLevel = conditional

physicalCoercivitySpectrumIdentificationInputsLevel : ProofLevel
physicalCoercivitySpectrumIdentificationInputsLevel = conditional

physicalDeterminantMatrixIdentificationInputsLevel : ProofLevel
physicalDeterminantMatrixIdentificationInputsLevel = conditional

physicalInverseNormIdentificationInputsLevel : ProofLevel
physicalInverseNormIdentificationInputsLevel = conditional
