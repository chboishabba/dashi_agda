module DASHI.Mathematics.LinearAlgebra.RationalThreeWayHodgeCoordinateUniquenessFinalExact where

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
-- Final ring-normalized uniqueness theorem for the inhabited Q^3 Hodge split.
-- If exact, harmonic and coexact axis coordinates assemble to the same vector,
-- then the three coordinates agree.  All rational zero additions are
-- normalized by checked ring identities.
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

assemble : ℚ → ℚ → ℚ → Hodge.HodgeTriple
assemble exact harmonic coexact =
  Hodge.addTriple
    (exactAxis exact)
    (Hodge.addTriple (harmonicAxis harmonic) (coexactAxis coexact))

assembleNormalForm : ∀ exact harmonic coexact →
  assemble exact harmonic coexact
  ≡ Hodge.hodgeTriple exact harmonic coexact
assembleNormalForm exact harmonic coexact =
  Hodge.tripleExtensionality
    (solve (exact ∷ harmonic ∷ coexact ∷ []))
    (solve (exact ∷ harmonic ∷ coexact ∷ []))
    (solve (exact ∷ harmonic ∷ coexact ∷ []))

record CoordinateEquality
    (exact harmonic coexact exact' harmonic' coexact' : ℚ) : Set where
  constructor coordinateEquality
  field
    exactEqual : exact ≡ exact'
    harmonicEqual : harmonic ≡ harmonic'
    coexactEqual : coexact ≡ coexact'

open CoordinateEquality public

assemblyEqualityNormalizes :
  ∀ exact harmonic coexact exact' harmonic' coexact' →
  assemble exact harmonic coexact
  ≡ assemble exact' harmonic' coexact' →
  Hodge.hodgeTriple exact harmonic coexact
  ≡ Hodge.hodgeTriple exact' harmonic' coexact'
assemblyEqualityNormalizes
    exact harmonic coexact exact' harmonic' coexact' equality =
  trans
    (sym (assembleNormalForm exact harmonic coexact))
    (trans equality (assembleNormalForm exact' harmonic' coexact'))

coordinateUniqueness :
  ∀ exact harmonic coexact exact' harmonic' coexact' →
  assemble exact harmonic coexact
  ≡ assemble exact' harmonic' coexact' →
  CoordinateEquality exact harmonic coexact exact' harmonic' coexact'
coordinateUniqueness
    exact harmonic coexact exact' harmonic' coexact' equality =
  let normalized =
        assemblyEqualityNormalizes
          exact harmonic coexact exact' harmonic' coexact' equality
  in coordinateEquality
      (cong Hodge.exactCoordinate normalized)
      (cong Hodge.harmonicCoordinate normalized)
      (cong Hodge.coexactCoordinate normalized)

canonicalDecomposition : ∀ vector →
  vector
  ≡ assemble
      (Hodge.exactCoordinate vector)
      (Hodge.harmonicCoordinate vector)
      (Hodge.coexactCoordinate vector)
canonicalDecomposition
    (Hodge.hodgeTriple exact harmonic coexact) =
  sym (assembleNormalForm exact harmonic coexact)

coordinatesOfAnyDecomposition : ∀ vector exact harmonic coexact →
  vector ≡ assemble exact harmonic coexact →
  exact ≡ Hodge.exactCoordinate vector
  × harmonic ≡ Hodge.harmonicCoordinate vector
  × coexact ≡ Hodge.coexactCoordinate vector
coordinatesOfAnyDecomposition
    (Hodge.hodgeTriple vectorExact vectorHarmonic vectorCoexact)
    exact harmonic coexact equality =
  let normalized =
        trans equality (assembleNormalForm exact harmonic coexact)
  in sym (cong Hodge.exactCoordinate normalized)
     , sym (cong Hodge.harmonicCoordinate normalized)
     , sym (cong Hodge.coexactCoordinate normalized)

record FinalHodgeDirectSumCertificate : Set where
  field
    decomposition : ∀ vector →
      vector
      ≡ assemble
          (Hodge.exactCoordinate vector)
          (Hodge.harmonicCoordinate vector)
          (Hodge.coexactCoordinate vector)
    uniqueness :
      ∀ exact harmonic coexact exact' harmonic' coexact' →
      assemble exact harmonic coexact
      ≡ assemble exact' harmonic' coexact' →
      CoordinateEquality exact harmonic coexact exact' harmonic' coexact'

canonicalFinalHodgeDirectSumCertificate : FinalHodgeDirectSumCertificate
canonicalFinalHodgeDirectSumCertificate = record
  { decomposition = canonicalDecomposition
  ; uniqueness = coordinateUniqueness
  }
