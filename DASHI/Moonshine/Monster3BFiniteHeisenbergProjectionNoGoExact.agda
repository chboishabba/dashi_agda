module DASHI.Moonshine.Monster3BFiniteHeisenbergProjectionNoGoExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Audrey Terras,
-- "Fourier Analysis on Finite Groups and Applications",
-- Cambridge University Press, 1999.
-- DOI: 10.1017/CBO9780511626265.
--
-- I. M. Isaacs,
-- "Character Theory of Finite Groups",
-- Dover Publications, 1994 reprint of the 1976 edition.
-- ISBN: 978-0-486-68014-9; no DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- Consume the proved scalar-commutant theorem and close the projector no-go at
-- matrix-coefficient level.  Over any scalar algebra whose only idempotents
-- are zero and one, a matrix commuting with every finite Heisenberg
-- translation and modulation and satisfying the projector scalar equation is
-- either literally the zero matrix or literally the identity matrix.
--
-- The remaining representation-theoretic bridge is sharply isolated:
-- construct the orthogonal projector of an invariant subspace and prove it
-- satisfies the coefficient hypotheses below.  No invariant-subspace receipt
-- is hidden in this module.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import Relation.Nullary using (Dec; yes; no)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Monster3BFiniteHeisenbergCommutantExact as Commutant

------------------------------------------------------------------------
-- Equality on the six-trit basis.
------------------------------------------------------------------------

x6DecidableEquality : (left right : H.X6) → Dec (left ≡ right)
x6DecidableEquality
  (H.x6 l0 l1 l2 l3 l4 l5)
  (H.x6 r0 r1 r2 r3 r4 r5)
  with Commutant.tritDecidableEquality l0 r0
... | no differs = no (λ equality → differs (cong H.x0 equality))
... | yes refl with Commutant.tritDecidableEquality l1 r1
...   | no differs = no (λ equality → differs (cong H.x1 equality))
...   | yes refl with Commutant.tritDecidableEquality l2 r2
...     | no differs = no (λ equality → differs (cong H.x2 equality))
...     | yes refl with Commutant.tritDecidableEquality l3 r3
...       | no differs = no (λ equality → differs (cong H.x3 equality))
...       | yes refl with Commutant.tritDecidableEquality l4 r4
...         | no differs = no (λ equality → differs (cong H.x4 equality))
...         | yes refl with Commutant.tritDecidableEquality l5 r5
...           | no differs = no (λ equality → differs (cong H.x5 equality))
...           | yes refl = yes refl

------------------------------------------------------------------------
-- Scalar algebra and the no-nontrivial-idempotent property.
------------------------------------------------------------------------

record IdempotentScalarAlgebra
  (matrix : Commutant.SchrodingerCommutantMatrix) : Set₁ where
  field
    oneScalar : Commutant.Scalar matrix
    multiplyScalar :
      Commutant.Scalar matrix →
      Commutant.Scalar matrix →
      Commutant.Scalar matrix

    idempotentDichotomy :
      (scalar : Commutant.Scalar matrix) →
      multiplyScalar scalar scalar ≡ scalar →
      scalar ≡ Commutant.zeroScalar matrix
      ⊎ scalar ≡ oneScalar

open IdempotentScalarAlgebra public

------------------------------------------------------------------------
-- A commuting projection needs only one remaining coefficient equation after
-- scalarization: its common diagonal scalar is idempotent.
------------------------------------------------------------------------

record HeisenbergCommutingProjection : Set₁ where
  field
    matrix : Commutant.SchrodingerCommutantMatrix
    scalarAlgebra : IdempotentScalarAlgebra matrix
    scalarIdempotent :
      multiplyScalar scalarAlgebra
        (Commutant.entry matrix Commutant.origin Commutant.origin)
        (Commutant.entry matrix Commutant.origin Commutant.origin)
      ≡ Commutant.entry matrix Commutant.origin Commutant.origin

open HeisenbergCommutingProjection public

identityCoefficient :
  (projection : HeisenbergCommutingProjection) →
  H.X6 → H.X6 → Commutant.Scalar (matrix projection)
identityCoefficient projection left right
  with x6DecidableEquality left right
... | yes _ = oneScalar (scalarAlgebra projection)
... | no _ = Commutant.zeroScalar (matrix projection)

record ProjectionIsZero
  (projection : HeisenbergCommutingProjection) : Set where
  constructor projection-is-zero
  field
    everyCoefficientZero :
      (left right : H.X6) →
      Commutant.entry (matrix projection) left right
      ≡ Commutant.zeroScalar (matrix projection)

open ProjectionIsZero public

record ProjectionIsIdentity
  (projection : HeisenbergCommutingProjection) : Set where
  constructor projection-is-identity
  field
    everyCoefficientIdentity :
      (left right : H.X6) →
      Commutant.entry (matrix projection) left right
      ≡ identityCoefficient projection left right

open ProjectionIsIdentity public

------------------------------------------------------------------------
-- Zero and identity branches.
------------------------------------------------------------------------

projectionIsZeroFromScalarZero :
  (projection : HeisenbergCommutingProjection) →
  Commutant.entry (matrix projection) Commutant.origin Commutant.origin
  ≡ Commutant.zeroScalar (matrix projection) →
  ProjectionIsZero projection
projectionIsZeroFromScalarZero projection scalarZero =
  projection-is-zero coefficientZero
  where
    conclusion = Commutant.schrodingerCommutantIsScalar (matrix projection)

    coefficientZero :
      (left right : H.X6) →
      Commutant.entry (matrix projection) left right
      ≡ Commutant.zeroScalar (matrix projection)
    coefficientZero left right with x6DecidableEquality left right
    ... | yes refl =
      trans
        (Commutant.everyDiagonalCoefficientIsScalar conclusion left)
        scalarZero
    ... | no distinct =
      Commutant.everyOffDiagonalCoefficientVanishes
        conclusion left right distinct

projectionIsIdentityFromScalarOne :
  (projection : HeisenbergCommutingProjection) →
  Commutant.entry (matrix projection) Commutant.origin Commutant.origin
  ≡ oneScalar (scalarAlgebra projection) →
  ProjectionIsIdentity projection
projectionIsIdentityFromScalarOne projection scalarOne =
  projection-is-identity coefficientIdentity
  where
    conclusion = Commutant.schrodingerCommutantIsScalar (matrix projection)

    coefficientIdentity :
      (left right : H.X6) →
      Commutant.entry (matrix projection) left right
      ≡ identityCoefficient projection left right
    coefficientIdentity left right with x6DecidableEquality left right
    ... | yes refl =
      trans
        (Commutant.everyDiagonalCoefficientIsScalar conclusion left)
        scalarOne
    ... | no distinct =
      Commutant.everyOffDiagonalCoefficientVanishes
        conclusion left right distinct

------------------------------------------------------------------------
-- Terminal projector no-go.
------------------------------------------------------------------------

heisenbergCommutingProjectionDichotomy :
  (projection : HeisenbergCommutingProjection) →
  ProjectionIsZero projection ⊎ ProjectionIsIdentity projection
heisenbergCommutingProjectionDichotomy projection
  with idempotentDichotomy
    (scalarAlgebra projection)
    (Commutant.entry (matrix projection) Commutant.origin Commutant.origin)
    (scalarIdempotent projection)
... | inj₁ scalarZero =
  inj₁ (projectionIsZeroFromScalarZero projection scalarZero)
... | inj₂ scalarOne =
  inj₂ (projectionIsIdentityFromScalarOne projection scalarOne)
