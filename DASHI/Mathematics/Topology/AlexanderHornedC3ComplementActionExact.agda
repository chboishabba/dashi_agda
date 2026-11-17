module DASHI.Mathematics.Topology.AlexanderHornedC3ComplementActionExact where

------------------------------------------------------------------------
-- EXACT C3 ACTION ON A COMPLEMENT, FROM A SET-INVARIANT AMBIENT
-- ORDER-THREE AUTOMORPHISM.
--
-- No topology imported/claimed: the underlying point-set assertion
-- is general and can be instantiated with S3, R3 or any carrier.
-- To claim a CONTINUOUS geometric action on the exterior requires
-- an explicit topological structure and continuity certificate.
-- Likewise, an ambient C3 action alone does not prove invariance
-- of an actual Alexander horned ball or the induced pi1 action.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

record InvariantSubsetC3 : Set₁ where
  field
    Point : Set
    InSolid : Point → Set
    rotate : Point → Point
    rotateCubed : ∀ p → rotate (rotate (rotate p)) ≡ p
    solidForward : ∀ p → InSolid p → InSolid (rotate p)
    solidBackward : ∀ p → InSolid (rotate p) → InSolid p

open InvariantSubsetC3 public

record ExteriorPoint (S : InvariantSubsetC3) : Set where
  constructor exteriorPoint
  field
    point : Point S
    outside : InSolid S point → ⊥

open ExteriorPoint public

rotateExterior : (S : InvariantSubsetC3) →
  ExteriorPoint S → ExteriorPoint S
rotateExterior S (exteriorPoint p proof) =
  exteriorPoint
    (rotate S p)
    (λ membership → proof (solidBackward S p membership))

rotateExteriorPoint : (S : InvariantSubsetC3) →
  ∀ x → point (rotateExterior S x) ≡ rotate S (point x)
rotateExteriorPoint S (exteriorPoint p proof) = refl

-- Avoid proof irrelevance: equality of the spatial points, rather
-- than of records carrying different proofs of nonmembership.
rotateExteriorCubedOnPoints : (S : InvariantSubsetC3) →
  ∀ x →
    point (rotateExterior S
      (rotateExterior S (rotateExterior S x))) ≡ point x
rotateExteriorCubedOnPoints S (exteriorPoint p proof) =
  rotateCubed S p

rotationCannotSendExteriorIntoSolid : (S : InvariantSubsetC3) →
  ∀ x → InSolid S (point (rotateExterior S x)) → ⊥
rotationCannotSendExteriorIntoSolid S (exteriorPoint p proof) membership =
  proof (solidBackward S p membership)

-- The complement is invariant, but no statement about pi1 or wild
-- embedding follows without an actual topological realization.
