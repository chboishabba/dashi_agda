module DASHI.Information.PNFSpectralCleaningPSDExact where

-- Reusable finite spectral cleaning theorem for PNF covariance and
-- financial risk covariance. A nonnegative eigenvalue filter produces a
-- nonnegative quadratic form. Real matrix reconstruction and source-specific
-- diagonal normalisation remain separate obligations.
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Fin.Base using (Fin)

import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Ring
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffOrbitGramAssembly as ExistingPSD
import DASHI.Information.PNFFiniteGramPositiveExact as Positive

record FilteredFiniteSpectrum
  (K : Ring.ExactOrderedCommutativeRing)
  (m : Nat) : Set₁ where
  private
    S = Ring.orderedScalar K
  field
    Vector : Set
    coefficient : Vector → Fin m → Scalar.Scalar S
    filteredEigenvalue : Fin m → Scalar.Scalar S
    filteredEigenvalueNonnegative :
      (i : Fin m) → Scalar._≤_ S (Scalar.zero S) (filteredEigenvalue i)

open FilteredFiniteSpectrum public

spectrallyCleanedQuadratic :
  (K : Ring.ExactOrderedCommutativeRing) →
  {m : Nat} → (F : FilteredFiniteSpectrum K m) →
  FilteredFiniteSpectrum.Vector F →
  Scalar.Scalar (Ring.orderedScalar K)
spectrallyCleanedQuadratic K F v =
  Ring.sumFin (Ring.orderedScalar K)
    (λ i → Scalar._*_ (Ring.orderedScalar K)
      (FilteredFiniteSpectrum.filteredEigenvalue F i)
      (Scalar._*_ (Ring.orderedScalar K)
        (FilteredFiniteSpectrum.coefficient F v i)
        (FilteredFiniteSpectrum.coefficient F v i)))

nonnegativeSpectralFilterPreservesPSD :
  (K : Ring.ExactOrderedCommutativeRing) →
  (O : ExistingPSD.FiniteGramOrderAuthority K) →
  {m : Nat} → (F : FilteredFiniteSpectrum K m) →
  (v : FilteredFiniteSpectrum.Vector F) →
  Scalar._≤_ (Ring.orderedScalar K)
    (Scalar.zero (Ring.orderedScalar K))
    (spectrallyCleanedQuadratic K F v)
nonnegativeSpectralFilterPreservesPSD K O F v =
  Positive.sumFinNonnegative K
    (Positive.positiveConeFromExistingPSD K O)
    (λ i → Scalar._*_ (Ring.orderedScalar K)
      (filteredEigenvalue F i)
      (Scalar._*_ (Ring.orderedScalar K)
        (coefficient F v i) (coefficient F v i)))
    (λ i →
      Scalar.multiplicationPreservesNonnegative (Ring.orderedScalar K)
        (filteredEigenvalueNonnegative F i)
        (ExistingPSD.squareNonnegative O (coefficient F v i)))

-- A concretely reconstructed linear operator may consume this theorem
-- after exhibiting the quadratic-form identity below. This is an explicit
-- equality predicate, not an arbitrary Set-valued surrogate.
record CleanedOperatorEquality
  (K : Ring.ExactOrderedCommutativeRing)
  {m : Nat}
  (F : FilteredFiniteSpectrum K m) : Set₁ where
  private
    S = Ring.orderedScalar K
  field
    operatorQuadratic : Vector F → Scalar.Scalar S
    quadraticEqualsFiltered :
      (v : Vector F) →
      operatorQuadratic v ≡ spectrallyCleanedQuadratic K F v

open CleanedOperatorEquality public

cleanedOperatorPositiveSemidefinite :
  (K : Ring.ExactOrderedCommutativeRing) →
  (O : ExistingPSD.FiniteGramOrderAuthority K) →
  {m : Nat} → (F : FilteredFiniteSpectrum K m) →
  (E : CleanedOperatorEquality K F) →
  (v : FilteredFiniteSpectrum.Vector F) →
  Scalar._≤_ (Ring.orderedScalar K)
    (Scalar.zero (Ring.orderedScalar K))
    (CleanedOperatorEquality.operatorQuadratic E v)
cleanedOperatorPositiveSemidefinite K O F E v
  rewrite CleanedOperatorEquality.quadraticEqualsFiltered E v =
  nonnegativeSpectralFilterPreservesPSD K O F v

-- PSD survives any linear congruence map represented as a vector
-- transformation T: the new quadratic is Q(Tv). This is the algebraic
-- foundation for positive diagonal covariance/correlation rescaling;
-- the concrete diagonal roots/inverses and reconstruction are not assumed.
diagonalCongruencePreservesPSD :
  (K : Ring.ExactOrderedCommutativeRing) →
  (O : ExistingPSD.FiniteGramOrderAuthority K) →
  {m : Nat} → (F : FilteredFiniteSpectrum K m) →
  (E : CleanedOperatorEquality K F) →
  (transform : FilteredFiniteSpectrum.Vector F →
               FilteredFiniteSpectrum.Vector F) →
  (v : FilteredFiniteSpectrum.Vector F) →
  Scalar._≤_ (Ring.orderedScalar K)
    (Scalar.zero (Ring.orderedScalar K))
    (CleanedOperatorEquality.operatorQuadratic E (transform v))
diagonalCongruencePreservesPSD K O F E transform v =
  cleanedOperatorPositiveSemidefinite K O F E (transform v)
