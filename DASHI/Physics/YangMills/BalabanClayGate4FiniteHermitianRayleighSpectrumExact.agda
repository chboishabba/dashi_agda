module DASHI.Physics.YangMills.BalabanClayGate4FiniteHermitianRayleighSpectrumExact where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4FiniteCoercivityInverseNormExact as Inverse

------------------------------------------------------------------------
-- Finite Hermitian Rayleigh/coercivity bridge.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press (2012).
-- DOI: 10.1017/CBO9781139020411.
--
-- An explicit finite eigenpair list is enough.  If every listed eigenvector is
-- normalized and the quadratic form is bounded below by c ||x||^2, then every
-- eigenvalue is at least c.  The result feeds the existing reciprocal-spectrum
-- inverse-norm theorem without introducing a second spectral convention.
------------------------------------------------------------------------

record Pair (A B : Set) : Set where
  constructor pair
  field
    first : A
    second : B

open Pair public

mapList : ∀ {A B : Set} → (A → B) → List A → List B
mapList function [] = []
mapList function (value ∷ values) =
  function value ∷ mapList function values

record FiniteHermitianRayleighData
    (Index Vector Scalar : Set) : Set₁ where
  field
    eigenpairs : Index → List (Pair Scalar Vector)

    quadraticForm : Index → Vector → Scalar
    normSq : Vector → Scalar
    scale : Scalar → Scalar → Scalar
    LessEqual : Scalar → Scalar → Set
    Positive : Scalar → Set

    one : Scalar
    coercivityConstant : Index → Scalar
    coercivityPositive : ∀ index → Positive (coercivityConstant index)

    scaleOne : ∀ scalar → scale scalar one ≡ scalar

    eigenvectorsNormalized : ∀ index →
      Inverse.All
        (λ eigenpair → normSq (second eigenpair) ≡ one)
        (eigenpairs index)

    eigenpairQuadraticForm : ∀ index →
      Inverse.All
        (λ eigenpair →
          quadraticForm index (second eigenpair) ≡ first eigenpair)
        (eigenpairs index)

    referenceQuadraticFormCoercive : ∀ index vector →
      LessEqual
        (scale (coercivityConstant index) (normSq vector))
        (quadraticForm index vector)

    positiveAbovePositive : ∀ {lower upper} →
      Positive lower → LessEqual lower upper → Positive upper

open FiniteHermitianRayleighData public

coercivityLowerBoundsEigenpairs :
  ∀ {Index Vector Scalar}
    (dataSet : FiniteHermitianRayleighData Index Vector Scalar)
    index →
  Inverse.All
    (λ eigenpair →
      LessEqual dataSet
        (coercivityConstant dataSet index)
        (first eigenpair))
    (eigenpairs dataSet index)
coercivityLowerBoundsEigenpairs dataSet index =
  combine
    (eigenvectorsNormalized dataSet index)
    (eigenpairQuadraticForm dataSet index)
  where
  combine : ∀ {pairs} →
    Inverse.All
      (λ eigenpair → normSq dataSet (second eigenpair) ≡ one dataSet)
      pairs →
    Inverse.All
      (λ eigenpair →
        quadraticForm dataSet index (second eigenpair) ≡ first eigenpair)
      pairs →
    Inverse.All
      (λ eigenpair →
        LessEqual dataSet
          (coercivityConstant dataSet index)
          (first eigenpair))
      pairs
  combine Inverse.allNil Inverse.allNil = Inverse.allNil
  combine
      (Inverse.allCons {value = eigenpair} normalized restNormalized)
      (Inverse.allCons formMeaning restForms) =
    Inverse.allCons
      (subst
        (λ upper →
          LessEqual dataSet (coercivityConstant dataSet index) upper)
        formMeaning
        (subst
          (λ lower →
            LessEqual dataSet lower
              (quadraticForm dataSet index (second eigenpair)))
          (trans
            (cong
              (scale dataSet (coercivityConstant dataSet index))
              normalized)
            (scaleOne dataSet (coercivityConstant dataSet index)))
          (referenceQuadraticFormCoercive dataSet
            index (second eigenpair))))
      (combine restNormalized restForms)

mapFirstAll :
  ∀ {A B : Set} {Predicate : A → Set} {values : List (Pair A B)} →
  Inverse.All (λ value → Predicate (first value)) values →
  Inverse.All Predicate (mapList first values)
mapFirstAll Inverse.allNil = Inverse.allNil
mapFirstAll (Inverse.allCons property rest) =
  Inverse.allCons property (mapFirstAll rest)

finiteEigenvalues :
  ∀ {Index Vector Scalar} →
  FiniteHermitianRayleighData Index Vector Scalar →
  Index → List Scalar
finiteEigenvalues dataSet index =
  mapList first (eigenpairs dataSet index)

coercivityLowerBoundsSpectrum :
  ∀ {Index Vector Scalar}
    (dataSet : FiniteHermitianRayleighData Index Vector Scalar)
    index →
  Inverse.All
    (λ eigenvalue →
      LessEqual dataSet (coercivityConstant dataSet index) eigenvalue)
    (finiteEigenvalues dataSet index)
coercivityLowerBoundsSpectrum dataSet index =
  mapFirstAll (coercivityLowerBoundsEigenpairs dataSet index)

spectrumPositiveFromCoercivity :
  ∀ {Index Vector Scalar}
    (dataSet : FiniteHermitianRayleighData Index Vector Scalar)
    index →
  Inverse.All (Positive dataSet) (finiteEigenvalues dataSet index)
spectrumPositiveFromCoercivity dataSet index =
  promote (coercivityLowerBoundsSpectrum dataSet index)
  where
  promote : ∀ {values} →
    Inverse.All
      (λ eigenvalue →
        LessEqual dataSet (coercivityConstant dataSet index) eigenvalue)
      values →
    Inverse.All (Positive dataSet) values
  promote Inverse.allNil = Inverse.allNil
  promote (Inverse.allCons lower rest) =
    Inverse.allCons
      (positiveAbovePositive dataSet
        (coercivityPositive dataSet index) lower)
      (promote rest)

record FiniteHermitianInverseNormInstantiation
    (Index Vector Scalar : Set) : Set₁ where
  field
    rayleigh : FiniteHermitianRayleighData Index Vector Scalar

    reciprocal : Scalar → Scalar
    inverseOperatorNorm : Index → Scalar

    reciprocalAntitoneOnPositive : ∀ {lower upper} →
      Positive rayleigh lower → Positive rayleigh upper →
      LessEqual rayleigh lower upper →
      LessEqual rayleigh (reciprocal upper) (reciprocal lower)

    inverseOperatorNormFromReciprocalSpectrum :
      ∀ index bound →
      Inverse.All
        (λ eigenvalue →
          LessEqual rayleigh (reciprocal eigenvalue) bound)
        (finiteEigenvalues rayleigh index) →
      LessEqual rayleigh (inverseOperatorNorm index) bound

open FiniteHermitianInverseNormInstantiation public

asFiniteSpectralCoercivityInverseNorm :
  ∀ {Index Vector Scalar}
    (meaning : FiniteHermitianInverseNormInstantiation
      Index Vector Scalar) →
  Inverse.FiniteSpectralCoercivityInverseNorm Index Scalar
asFiniteSpectralCoercivityInverseNorm meaning = record
  { eigenvalues = finiteEigenvalues (rayleigh meaning)
  ; coercivityConstant = coercivityConstant (rayleigh meaning)
  ; inverseOperatorNorm = inverseOperatorNorm meaning
  ; reciprocal = reciprocal meaning
  ; LessEqual = LessEqual (rayleigh meaning)
  ; Positive = Positive (rayleigh meaning)
  ; coercivityPositive = coercivityPositive (rayleigh meaning)
  ; eigenvaluePositive = spectrumPositiveFromCoercivity (rayleigh meaning)
  ; coercivityLowerBoundsSpectrum =
      coercivityLowerBoundsSpectrum (rayleigh meaning)
  ; reciprocalAntitoneOnPositive = reciprocalAntitoneOnPositive meaning
  ; inverseOperatorNormFromReciprocalSpectrum =
      inverseOperatorNormFromReciprocalSpectrum meaning
  }

finiteHermitianInverseNormBelowCoercivityReciprocal :
  ∀ {Index Vector Scalar}
    (meaning : FiniteHermitianInverseNormInstantiation
      Index Vector Scalar)
    index →
  LessEqual (rayleigh meaning)
    (inverseOperatorNorm meaning index)
    (reciprocal meaning
      (coercivityConstant (rayleigh meaning) index))
finiteHermitianInverseNormBelowCoercivityReciprocal meaning index =
  Inverse.inverseNormBelowReciprocalCoercivity
    (asFiniteSpectralCoercivityInverseNorm meaning) index

finiteRayleighCoercivityToSpectrumLevel : ProofLevel
finiteRayleighCoercivityToSpectrumLevel = machineChecked

finiteSpectrumPositivityFromCoercivityLevel : ProofLevel
finiteSpectrumPositivityFromCoercivityLevel = machineChecked

finiteHermitianInverseNormAssemblyLevel : ProofLevel
finiteHermitianInverseNormAssemblyLevel = machineChecked

rayleighMinMaxProvenanceLevel : ProofLevel
rayleighMinMaxProvenanceLevel = standardImported

physicalFiniteEigenbasisInputsLevel : ProofLevel
physicalFiniteEigenbasisInputsLevel = conditional

physicalHermitianMatrixRepresentationInputsLevel : ProofLevel
physicalHermitianMatrixRepresentationInputsLevel = conditional

physicalInverseSpectralNormMeaningInputsLevel : ProofLevel
physicalInverseSpectralNormMeaningInputsLevel = conditional
