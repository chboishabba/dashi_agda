module DASHI.Physics.YangMills.BalabanClayGate4FiniteCoercivityInverseNormExact where

open import Agda.Builtin.List using (List; []; _∷_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Primary provenance.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press (2012).
-- DOI: 10.1017/CBO9781139020411.
--
-- For a finite positive self-adjoint Hessian with spectrum lambda_i >= c > 0,
-- the inverse spectrum is lambda_i^{-1} <= c^{-1}; hence
-- ||A^{-1}|| <= c^{-1}.  The physical spectral representation and the transfer
-- from DASHI's quadratic-form coercivity to the eigenvalue lower bound remain
-- explicit inputs.
------------------------------------------------------------------------

data All {A : Set} (Predicate : A → Set) : List A → Set where
  allNil : All Predicate []
  allCons : ∀ {value values} →
    Predicate value → All Predicate values → All Predicate (value ∷ values)

mapAll :
  ∀ {A : Set} {P Q : A → Set} {values} →
  (∀ value → P value → Q value) →
  All P values → All Q values
mapAll implication allNil = allNil
mapAll implication (allCons property rest) =
  allCons (implication _ property) (mapAll implication rest)

record FiniteSpectralCoercivityInverseNorm
    (Index Scalar : Set) : Set₁ where
  field
    eigenvalues : Index → List Scalar
    coercivityConstant inverseOperatorNorm : Index → Scalar

    reciprocal : Scalar → Scalar
    LessEqual : Scalar → Scalar → Set
    Positive : Scalar → Set

    coercivityPositive : ∀ index → Positive (coercivityConstant index)

    eigenvaluePositive : ∀ index →
      All Positive (eigenvalues index)

    coercivityLowerBoundsSpectrum : ∀ index →
      All (λ eigenvalue → LessEqual (coercivityConstant index) eigenvalue)
        (eigenvalues index)

    reciprocalAntitoneOnPositive : ∀ {lower upper} →
      Positive lower → Positive upper → LessEqual lower upper →
      LessEqual (reciprocal upper) (reciprocal lower)

    inverseOperatorNormFromReciprocalSpectrum :
      ∀ index bound →
      All (λ eigenvalue → LessEqual (reciprocal eigenvalue) bound)
        (eigenvalues index) →
      LessEqual (inverseOperatorNorm index) bound

open FiniteSpectralCoercivityInverseNorm public

reciprocalSpectrumBelowCoercivityReciprocal :
  ∀ {Index Scalar}
    (dataSet : FiniteSpectralCoercivityInverseNorm Index Scalar)
    index →
  All
    (λ eigenvalue →
      LessEqual dataSet
        (reciprocal dataSet eigenvalue)
        (reciprocal dataSet (coercivityConstant dataSet index)))
    (eigenvalues dataSet index)
reciprocalSpectrumBelowCoercivityReciprocal dataSet index =
  combine
    (eigenvaluePositive dataSet index)
    (coercivityLowerBoundsSpectrum dataSet index)
  where
  combine : ∀ {values} →
    All (Positive dataSet) values →
    All (λ eigenvalue →
      LessEqual dataSet (coercivityConstant dataSet index) eigenvalue) values →
    All (λ eigenvalue →
      LessEqual dataSet
        (reciprocal dataSet eigenvalue)
        (reciprocal dataSet (coercivityConstant dataSet index))) values
  combine allNil allNil = allNil
  combine (allCons positive restPositive) (allCons lowerBound restLower) =
    allCons
      (reciprocalAntitoneOnPositive dataSet
        (coercivityPositive dataSet index)
        positive
        lowerBound)
      (combine restPositive restLower)

inverseNormBelowReciprocalCoercivity :
  ∀ {Index Scalar}
    (dataSet : FiniteSpectralCoercivityInverseNorm Index Scalar)
    index →
  LessEqual dataSet
    (inverseOperatorNorm dataSet index)
    (reciprocal dataSet (coercivityConstant dataSet index))
inverseNormBelowReciprocalCoercivity dataSet index =
  inverseOperatorNormFromReciprocalSpectrum dataSet index
    (reciprocal dataSet (coercivityConstant dataSet index))
    (reciprocalSpectrumBelowCoercivityReciprocal dataSet index)

finiteSpectralInverseNormReductionLevel : ProofLevel
finiteSpectralInverseNormReductionLevel = machineChecked

coercivityReciprocalInverseBoundLevel : ProofLevel
coercivityReciprocalInverseBoundLevel = machineChecked

physicalCoercivityToSpectrumLowerBoundInputsLevel : ProofLevel
physicalCoercivityToSpectrumLowerBoundInputsLevel = conditional

physicalInverseHessianSpectralNormMeaningInputsLevel : ProofLevel
physicalInverseHessianSpectralNormMeaningInputsLevel = conditional
