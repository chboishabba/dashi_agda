module DASHI.Mathematics.LinearAlgebra.RationalThreeWayHodgeDecompositionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jozef Dodziuk,
-- "Finite-Difference Approach to the Hodge Theory of Harmonic Forms",
-- American Journal of Mathematics 98 (1976), 79--104.
-- DOI: 10.2307/2373615.
--
-- DASHI CONTRIBUTION
--
-- Construct an inhabited finite Hodge model rather than only an interface.
-- The carrier Q^3 is split into exact, harmonic and coexact coordinate axes.
-- The three projections are idempotent, pairwise annihilating, orthogonal for
-- the standard rational inner product, sum to the identity, and give a unique
-- decomposition.  The model Laplacian has eigenvalues 1,0,1 and kernel equal
-- to the harmonic axis.
--
-- This is a finite algebraic model.  It is not a continuum Hodge theorem and
-- is not identified with a specific cell complex until an adapter supplies
-- that comparison.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

record HodgeTriple : Set where
  constructor hodgeTriple
  field
    exactCoordinate : ℚ
    harmonicCoordinate : ℚ
    coexactCoordinate : ℚ

open HodgeTriple public

tripleExtensionality : ∀ {left right} →
  exactCoordinate left ≡ exactCoordinate right →
  harmonicCoordinate left ≡ harmonicCoordinate right →
  coexactCoordinate left ≡ coexactCoordinate right →
  left ≡ right
tripleExtensionality {hodgeTriple _ _ _} {hodgeTriple _ _ _}
  refl refl refl = refl

zeroTriple : HodgeTriple
zeroTriple = hodgeTriple 0ℚ 0ℚ 0ℚ

addTriple : HodgeTriple → HodgeTriple → HodgeTriple
addTriple (hodgeTriple e h c) (hodgeTriple e' h' c') =
  hodgeTriple (e + e') (h + h') (c + c')

scaleTriple : ℚ → HodgeTriple → HodgeTriple
scaleTriple scalar (hodgeTriple e h c) =
  hodgeTriple (scalar * e) (scalar * h) (scalar * c)

innerTriple : HodgeTriple → HodgeTriple → ℚ
innerTriple (hodgeTriple e h c) (hodgeTriple e' h' c') =
  e * e' + h * h' + c * c'

exactProjection : HodgeTriple → HodgeTriple
exactProjection (hodgeTriple e h c) = hodgeTriple e 0ℚ 0ℚ

harmonicProjection : HodgeTriple → HodgeTriple
harmonicProjection (hodgeTriple e h c) = hodgeTriple 0ℚ h 0ℚ

coexactProjection : HodgeTriple → HodgeTriple
coexactProjection (hodgeTriple e h c) = hodgeTriple 0ℚ 0ℚ c

hodgeLaplacian : HodgeTriple → HodgeTriple
hodgeLaplacian triple =
  addTriple (exactProjection triple) (coexactProjection triple)

exactProjectionIdempotent : ∀ x →
  exactProjection (exactProjection x) ≡ exactProjection x
exactProjectionIdempotent (hodgeTriple e h c) = refl

harmonicProjectionIdempotent : ∀ x →
  harmonicProjection (harmonicProjection x) ≡ harmonicProjection x
harmonicProjectionIdempotent (hodgeTriple e h c) = refl

coexactProjectionIdempotent : ∀ x →
  coexactProjection (coexactProjection x) ≡ coexactProjection x
coexactProjectionIdempotent (hodgeTriple e h c) = refl

exactKillsHarmonic : ∀ x →
  exactProjection (harmonicProjection x) ≡ zeroTriple
exactKillsHarmonic (hodgeTriple e h c) = refl

exactKillsCoexact : ∀ x →
  exactProjection (coexactProjection x) ≡ zeroTriple
exactKillsCoexact (hodgeTriple e h c) = refl

harmonicKillsExact : ∀ x →
  harmonicProjection (exactProjection x) ≡ zeroTriple
harmonicKillsExact (hodgeTriple e h c) = refl

harmonicKillsCoexact : ∀ x →
  harmonicProjection (coexactProjection x) ≡ zeroTriple
harmonicKillsCoexact (hodgeTriple e h c) = refl

coexactKillsExact : ∀ x →
  coexactProjection (exactProjection x) ≡ zeroTriple
coexactKillsExact (hodgeTriple e h c) = refl

coexactKillsHarmonic : ∀ x →
  coexactProjection (harmonicProjection x) ≡ zeroTriple
coexactKillsHarmonic (hodgeTriple e h c) = refl

hodgeDecomposition : ∀ x →
  x ≡ addTriple (exactProjection x)
        (addTriple (harmonicProjection x) (coexactProjection x))
hodgeDecomposition (hodgeTriple e h c) =
  tripleExtensionality (solve []) (solve []) (solve [])

exactOrthogonalHarmonic : ∀ x y →
  innerTriple (exactProjection x) (harmonicProjection y) ≡ 0ℚ
exactOrthogonalHarmonic (hodgeTriple e h c) (hodgeTriple e' h' c') =
  solve []

exactOrthogonalCoexact : ∀ x y →
  innerTriple (exactProjection x) (coexactProjection y) ≡ 0ℚ
exactOrthogonalCoexact (hodgeTriple e h c) (hodgeTriple e' h' c') =
  solve []

harmonicOrthogonalCoexact : ∀ x y →
  innerTriple (harmonicProjection x) (coexactProjection y) ≡ 0ℚ
harmonicOrthogonalCoexact (hodgeTriple e h c) (hodgeTriple e' h' c') =
  solve []

hodgeEnergyIdentity : ∀ x →
  innerTriple (hodgeLaplacian x) x
  ≡ innerTriple (exactProjection x) (exactProjection x)
    + innerTriple (coexactProjection x) (coexactProjection x)
hodgeEnergyIdentity (hodgeTriple e h c) = solve []

laplacianKillsHarmonic : ∀ x →
  hodgeLaplacian (harmonicProjection x) ≡ zeroTriple
laplacianKillsHarmonic (hodgeTriple e h c) = refl

laplacianFixesExact : ∀ x →
  hodgeLaplacian (exactProjection x) ≡ exactProjection x
laplacianFixesExact (hodgeTriple e h c) =
  tripleExtensionality (solve []) refl refl

laplacianFixesCoexact : ∀ x →
  hodgeLaplacian (coexactProjection x) ≡ coexactProjection x
laplacianFixesCoexact (hodgeTriple e h c) =
  tripleExtensionality refl refl (solve [])

laplacianKernelIsHarmonic : ∀ x →
  hodgeLaplacian x ≡ zeroTriple → x ≡ harmonicProjection x
laplacianKernelIsHarmonic (hodgeTriple e h c) equality =
  tripleExtensionality eIsZero refl cIsZero
  where
    exactCoordinateEquation : e + 0ℚ ≡ 0ℚ
    exactCoordinateEquation = cong exactCoordinate equality

    coexactCoordinateEquation : 0ℚ + c ≡ 0ℚ
    coexactCoordinateEquation = cong coexactCoordinate equality

    eIsZero : e ≡ 0ℚ
    eIsZero = trans (sym (solve (e ∷ []))) exactCoordinateEquation

    cIsZero : c ≡ 0ℚ
    cIsZero = trans (sym (solve (c ∷ []))) coexactCoordinateEquation

record HodgeDecompositionCertificate : Set where
  field
    decomposition : ∀ x →
      x ≡ addTriple (exactProjection x)
            (addTriple (harmonicProjection x) (coexactProjection x))
    exactIdempotent : ∀ x →
      exactProjection (exactProjection x) ≡ exactProjection x
    harmonicIdempotent : ∀ x →
      harmonicProjection (harmonicProjection x) ≡ harmonicProjection x
    coexactIdempotent : ∀ x →
      coexactProjection (coexactProjection x) ≡ coexactProjection x
    energy : ∀ x →
      innerTriple (hodgeLaplacian x) x
      ≡ innerTriple (exactProjection x) (exactProjection x)
        + innerTriple (coexactProjection x) (coexactProjection x)
    harmonicKernel : ∀ x →
      hodgeLaplacian x ≡ zeroTriple → x ≡ harmonicProjection x

canonicalHodgeDecompositionCertificate : HodgeDecompositionCertificate
canonicalHodgeDecompositionCertificate = record
  { decomposition = hodgeDecomposition
  ; exactIdempotent = exactProjectionIdempotent
  ; harmonicIdempotent = harmonicProjectionIdempotent
  ; coexactIdempotent = coexactProjectionIdempotent
  ; energy = hodgeEnergyIdentity
  ; harmonicKernel = laplacianKernelIsHarmonic
  }
