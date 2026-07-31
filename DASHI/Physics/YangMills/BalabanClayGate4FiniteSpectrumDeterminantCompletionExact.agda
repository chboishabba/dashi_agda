module DASHI.Physics.YangMills.BalabanClayGate4FiniteSpectrumDeterminantCompletionExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4FiniteCoordinateMatrixEquivalenceExact as Coordinate
import DASHI.Physics.YangMills.BalabanClayGate4FiniteHermitianRayleighSpectrumExact as Spectrum
import DASHI.Physics.YangMills.BalabanClayGate4FiniteCoercivityInverseNormExact as Inverse
import DASHI.Physics.YangMills.BalabanClayGate4FiniteDeterminantFactorizationExact as Determinant

------------------------------------------------------------------------
-- Coherent finite spectrum/determinant completion on one coordinate carrier.
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
-- One record owns the literal coordinate matrices, the Hermitian Rayleigh
-- spectrum, and the determinant algebra.  The conclusions below therefore
-- cannot silently switch bases or perturbation matrices.
------------------------------------------------------------------------

record FiniteSpectrumDeterminantCompletion
    (Scalar : Set) (n : Nat) (SpectralIndex : Set) : Set₁ where
  field
    coordinates : Coordinate.ExactRestrictedCoordinateRepresentation Scalar n

    rayleigh : Spectrum.FiniteHermitianRayleighData
      SpectralIndex (Coordinate.Vec Scalar n) Scalar
    selectedIndex : SpectralIndex

    determinantAlgebra : Determinant.DeterminantMatrixAlgebra
      (Coordinate.FiniteMatrix Scalar n) Scalar
    perturbationData :
      Determinant.InvertibleReferencePerturbation determinantAlgebra

    determinantReferenceExact :
      Determinant.reference perturbationData
      ≡ Coordinate.referenceMatrix coordinates
    determinantPerturbationExact :
      Determinant.perturbation perturbationData
      ≡ Coordinate.remainderMatrix coordinates

    SpectrumIsCoordinateReference : Set
    spectrumIsCoordinateReference : SpectrumIsCoordinateReference

open FiniteSpectrumDeterminantCompletion public

completionCoercivityLowerBoundsSpectrum :
  ∀ {Scalar n SpectralIndex}
    (completion : FiniteSpectrumDeterminantCompletion
      Scalar n SpectralIndex) →
  Inverse.All
    (λ eigenvalue →
      Spectrum.LessEqual (rayleigh completion)
        (Spectrum.coercivityConstant (rayleigh completion)
          (selectedIndex completion))
        eigenvalue)
    (Spectrum.finiteEigenvalues (rayleigh completion)
      (selectedIndex completion))
completionCoercivityLowerBoundsSpectrum completion =
  Spectrum.coercivityLowerBoundsSpectrum
    (rayleigh completion) (selectedIndex completion)

completionSpectrumPositive :
  ∀ {Scalar n SpectralIndex}
    (completion : FiniteSpectrumDeterminantCompletion
      Scalar n SpectralIndex) →
  Inverse.All
    (Spectrum.Positive (rayleigh completion))
    (Spectrum.finiteEigenvalues (rayleigh completion)
      (selectedIndex completion))
completionSpectrumPositive completion =
  Spectrum.spectrumPositiveFromCoercivity
    (rayleigh completion) (selectedIndex completion)

completionDeterminantFactorization :
  ∀ {Scalar n SpectralIndex}
    (completion : FiniteSpectrumDeterminantCompletion
      Scalar n SpectralIndex) →
  Determinant.determinant (determinantAlgebra completion)
    (Determinant.addMatrix (determinantAlgebra completion)
      (Coordinate.referenceMatrix (coordinates completion))
      (Coordinate.remainderMatrix (coordinates completion)))
  ≡ Determinant.multiplyScalar (determinantAlgebra completion)
      (Determinant.determinant (determinantAlgebra completion)
        (Coordinate.referenceMatrix (coordinates completion)))
      (Determinant.determinant (determinantAlgebra completion)
        (Determinant.addMatrix (determinantAlgebra completion)
          (Determinant.identityMatrix (determinantAlgebra completion))
          (Determinant.multiplyMatrix (determinantAlgebra completion)
            (Determinant.inverseReference (perturbationData completion))
            (Coordinate.remainderMatrix (coordinates completion)))))
completionDeterminantFactorization completion =
  subst
    (λ referenceMatrix →
      Determinant.determinant (determinantAlgebra completion)
        (Determinant.addMatrix (determinantAlgebra completion)
          referenceMatrix
          (Coordinate.remainderMatrix (coordinates completion)))
      ≡ Determinant.multiplyScalar (determinantAlgebra completion)
          (Determinant.determinant (determinantAlgebra completion)
            referenceMatrix)
          (Determinant.determinant (determinantAlgebra completion)
            (Determinant.addMatrix (determinantAlgebra completion)
              (Determinant.identityMatrix (determinantAlgebra completion))
              (Determinant.multiplyMatrix (determinantAlgebra completion)
                (Determinant.inverseReference (perturbationData completion))
                (Coordinate.remainderMatrix (coordinates completion))))))
    (determinantReferenceExact completion)
    (subst
      (λ perturbationMatrix →
        Determinant.determinant (determinantAlgebra completion)
          (Determinant.addMatrix (determinantAlgebra completion)
            (Determinant.reference (perturbationData completion))
            perturbationMatrix)
        ≡ Determinant.multiplyScalar (determinantAlgebra completion)
            (Determinant.determinant (determinantAlgebra completion)
              (Determinant.reference (perturbationData completion)))
            (Determinant.determinant (determinantAlgebra completion)
              (Determinant.addMatrix (determinantAlgebra completion)
                (Determinant.identityMatrix (determinantAlgebra completion))
                (Determinant.multiplyMatrix (determinantAlgebra completion)
                  (Determinant.inverseReference (perturbationData completion))
                  perturbationMatrix))))
      (determinantPerturbationExact completion)
      (Determinant.determinantPerturbationFactorization
        (perturbationData completion)))

finiteSpectrumCoercivityCompletionLevel : ProofLevel
finiteSpectrumCoercivityCompletionLevel = machineChecked

finiteSpectrumPositivityCompletionLevel : ProofLevel
finiteSpectrumPositivityCompletionLevel = machineChecked

finiteDeterminantIdentityCompletionLevel : ProofLevel
finiteDeterminantIdentityCompletionLevel = machineChecked

physicalSpectrumCoordinateIdentificationInputsLevel : ProofLevel
physicalSpectrumCoordinateIdentificationInputsLevel = conditional
