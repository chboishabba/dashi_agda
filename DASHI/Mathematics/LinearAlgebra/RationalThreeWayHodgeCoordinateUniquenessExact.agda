module DASHI.Mathematics.LinearAlgebra.RationalThreeWayHodgeCoordinateUniquenessExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Jozef Dodziuk,
-- "Finite-Difference Approach to the Hodge Theory of Harmonic Forms",
-- American Journal of Mathematics 98 (1976), 79--104.
-- DOI: 10.2307/2373615.
--
-- DASHI CONTRIBUTION
--
-- Complete the inhabited Q^3 Hodge model with a ring-normalized uniqueness
-- theorem.  If a vector is assembled from exact, harmonic and coexact axis
-- coordinates in two ways, then all three coordinates agree.  Rational zero
-- additions are normalized explicitly rather than treated as definitional.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Rational.Base using (ℚ; 0ℚ)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Mathematics.LinearAlgebra.RationalThreeWayHodgeDecompositionExact as Hodge

exactAxis : ℚ → Hodge.HodgeTriple
exactAxis exact = Hodge.hodgeTriple exact 0ℚ 0ℚ

harmonicAxis : ℚ → Hodge.HodgeTriple
harmonicAxis harmonic = Hodge.hodgeTriple 0ℚ harmonic 0ℚ

coexactAxis : ℚ → Hodge.HodgeTriple
coexactAxis coexact = Hodge.hodgeTriple 0ℚ 0ℚ coexact

assembleHodgeCoordinates : ℚ → ℚ → ℚ → Hodge.HodgeTriple
assembleHodgeCoordinates exact harmonic coexact =
  Hodge.addTriple
    (exactAxis exact)
    (Hodge.addTriple (harmonicAxis harmonic) (coexactAxis coexact))

assembledCoordinatesReduce : ∀ exact harmonic coexact →
  assembleHodgeCoordinates exact harmonic coexact
  ≡ Hodge.hodgeTriple exact harmonic coexact
assembledCoordinatesReduce exact harmonic coexact =
  Hodge.tripleExtensionality
    (solve (exact ∷ harmonic ∷ coexact ∷ []))
    (solve (exact ∷ harmonic ∷ coexact ∷ []))
    (solve (exact ∷ harmonic ∷ coexact ∷ []))

record HodgeCoordinateEquality
    (exact harmonic coexact exact' harmonic' coexact' : ℚ) : Set where
  constructor hodgeCoordinateEquality
  field
    exactCoordinatesEqual : exact ≡ exact'
    harmonicCoordinatesEqual : harmonic ≡ harmonic'
    coexactCoordinatesEqual : coexact ≡ coexact'

open HodgeCoordinateEquality public

normalizedAssemblyEquality :
  ∀ exact harmonic coexact exact' harmonic' coexact' →
  assembleHodgeCoordinates exact harmonic coexact
  ≡ assembleHodgeCoordinates exact' harmonic' coexact' →
  Hodge.hodgeTriple exact harmonic coexact
  ≡ Hodge.hodgeTriple exact' harmonic' coexact'
normalizedAssemblyEquality
    exact harmonic coexact exact' harmonic' coexact' equality =
  trans
    (sym (assembledCoordinatesReduce exact harmonic coexact))
    (trans equality
      (assembledCoordinatesReduce exact' harmonic' coexact'))

hodgeCoordinateUniqueness :
  ∀ exact harmonic coexact exact' harmonic' coexact' →
  assembleHodgeCoordinates exact harmonic coexact
  ≡ assembleHodgeCoordinates exact' harmonic' coexact' →
  HodgeCoordinateEquality
    exact harmonic coexact exact' harmonic' coexact'
hodgeCoordinateUniqueness
    exact harmonic coexact exact' harmonic' coexact' equality =
  let normalized =
        normalizedAssemblyEquality
          exact harmonic coexact exact' harmonic' coexact' equality
  in hodgeCoordinateEquality
      (cong Hodge.exactCoordinate normalized)
      (cong Hodge.harmonicCoordinate normalized)
      (cong Hodge.coexactCoordinate normalized)

canonicalProjectionDecomposition : ∀ vector →
  vector
  ≡ assembleHodgeCoordinates
      (Hodge.exactCoordinate vector)
      (Hodge.harmonicCoordinate vector)
      (Hodge.coexactCoordinate vector)
canonicalProjectionDecomposition
    (Hodge.hodgeTriple exact harmonic coexact) =
  sym (assembledCoordinatesReduce exact harmonic coexact)

projectionCoordinatesAreUnique : ∀ vector exact harmonic coexact →
  vector ≡ assembleHodgeCoordinates exact harmonic coexact →
  exact ≡ Hodge.exactCoordinate vector
  × harmonic ≡ Hodge.harmonicCoordinate vector
  × coexact ≡ Hodge.coexactCoordinate vector
projectionCoordinatesAreUnique
    (Hodge.hodgeTriple vectorExact vectorHarmonic vectorCoexact)
    exact harmonic coexact equality =
  let normalized =
        trans (sym equality)
          (assembledCoordinatesReduce exact harmonic coexact)
  in sym (cong Hodge.exactCoordinate normalized)
     , sym (cong Hodge.harmonicCoordinate normalized)
     , sym (cong Hodge.coexactCoordinate normalized)

record HodgeDirectSumCertificate : Set where
  field
    canonicalDecomposition : ∀ vector →
      vector
      ≡ assembleHodgeCoordinates
          (Hodge.exactCoordinate vector)
          (Hodge.harmonicCoordinate vector)
          (Hodge.coexactCoordinate vector)
    coordinateUniqueness :
      ∀ exact harmonic coexact exact' harmonic' coexact' →
      assembleHodgeCoordinates exact harmonic coexact
      ≡ assembleHodgeCoordinates exact' harmonic' coexact' →
      HodgeCoordinateEquality
        exact harmonic coexact exact' harmonic' coexact'

canonicalHodgeDirectSumCertificate : HodgeDirectSumCertificate
canonicalHodgeDirectSumCertificate = record
  { canonicalDecomposition = canonicalProjectionDecomposition
  ; coordinateUniqueness = hodgeCoordinateUniqueness
  }
