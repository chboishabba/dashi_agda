module DASHI.Mathematics.Topology.AlexanderHornedC3OrbitSolidExact where

------------------------------------------------------------------------
-- CONSTRUCT AN INVARIANT THREE-COPY SOLID FROM ANY ORDER-THREE
-- AMBIENT POINT ACTION AND ONE SELECTED SEED REGION.
--
-- ORIGINAL EXACT THEOREM: OrbitSolid is the union of the seed and
-- its two cyclic translates.  The order-three equation alone
-- provides BOTH forward and backward membership invariance, so the
-- complement action interface is actually inhabited rather than
-- having invariance assumed separately.
--
-- NOT A THEOREM ABOUT EMBEDDINGS OR MANIFOLDS: the seed must still be
-- a concrete Hatcher horned ball plus tame gluing tube, and its union
-- must still be shown homeomorphic to a 3-ball by geometric arguments.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Mathematics.Topology.AlexanderHornedC3ComplementActionExact as Exterior

record AmbientRotation3 : Set₁ where
  field
    Position : Set
    rotate : Position → Position
    rotateCubed : ∀ p → rotate (rotate (rotate p)) ≡ p

open AmbientRotation3 public

-- The dependent predicate is stored in a record so Agda can infer
-- the seed parameter unambiguously when proving membership laws.
record OrbitSeed (A : AmbientRotation3) : Set₁ where
  field
    Seed : Position A → Set

open OrbitSeed public

data OrbitSolid (A : AmbientRotation3)
    (S : OrbitSeed A) (p : Position A) : Set where
  phase0 : Seed S p → OrbitSolid A S p
  phase1 : Seed S (rotate A p) → OrbitSolid A S p
  phase2 : Seed S (rotate A (rotate A p)) → OrbitSolid A S p

substPredicate : ∀ {P : Set} {x y : P}
  (f : P → Set) → x ≡ y → f x → f y
substPredicate f refl value = value

orbitSolidForward : (A : AmbientRotation3) →
  (S : OrbitSeed A) → ∀ p →
  OrbitSolid A S p → OrbitSolid A S (rotate A p)
orbitSolidForward A S p (phase0 member) =
  phase2 (substPredicate (Seed S) (sym (rotateCubed A p)) member)
orbitSolidForward A S p (phase1 member) = phase0 member
orbitSolidForward A S p (phase2 member) = phase1 member

orbitSolidBackward : (A : AmbientRotation3) →
  (S : OrbitSeed A) → ∀ p →
  OrbitSolid A S (rotate A p) → OrbitSolid A S p
orbitSolidBackward A S p (phase0 member) = phase1 member
orbitSolidBackward A S p (phase1 member) = phase2 member
orbitSolidBackward A S p (phase2 member) =
  phase0 (substPredicate (Seed S) (rotateCubed A p) member)

threeCopySolidInvariant :
  (A : AmbientRotation3) → (S : OrbitSeed A) →
  Exterior.InvariantSubsetC3
threeCopySolidInvariant A S = record
  { Exterior.Point = Position A
  ; Exterior.InSolid = OrbitSolid A S
  ; Exterior.rotate = rotate A
  ; Exterior.rotateCubed = rotateCubed A
  ; Exterior.solidForward = orbitSolidForward A S
  ; Exterior.solidBackward = orbitSolidBackward A S
  }

threeCopyExteriorRotation :
  (A : AmbientRotation3) → (S : OrbitSeed A) →
  Exterior.ExteriorPoint (threeCopySolidInvariant A S) →
  Exterior.ExteriorPoint (threeCopySolidInvariant A S)
threeCopyExteriorRotation A S =
  Exterior.rotateExterior (threeCopySolidInvariant A S)

threeCopyExteriorCubedOnPoints :
  (A : AmbientRotation3) → (S : OrbitSeed A) →
  ∀ x →
  Exterior.point
    (threeCopyExteriorRotation A S
      (threeCopyExteriorRotation A S
        (threeCopyExteriorRotation A S x)))
    ≡ Exterior.point x
threeCopyExteriorCubedOnPoints A S =
  Exterior.rotateExteriorCubedOnPoints (threeCopySolidInvariant A S)
