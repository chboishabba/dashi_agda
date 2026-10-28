module DASHI.Mathematics.Topology.AlexanderHornedC3AmbientRotationExact where

------------------------------------------------------------------------
-- EXACT 120-DEGREE ROTATION CARRIER FOR THE AMBIENT 3-SPACE
--
-- The cyclic coordinate permutation (x,y,z) -> (z,x,y) is an
-- orientation-preserving linear order-three isometry of Euclidean R3:
-- its matrix is a three-cycle permutation matrix, determinant +1,
-- fixing the diagonal line x=y=z.  This module proves its order,
-- axis equivariance, and pointwise one-point-extension equations on
-- generic coordinate carriers.  Continuity, Euclidean metric facts,
-- and the topology of the compactification are NOT internalised here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Core.FiniteC3OrbitStabilizerExact as C3

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

record Triple (A : Set) : Set where
  constructor xyz
  field
    first second third : A

open Triple public

rotateXYZ : ∀ {A : Set} → Triple A → Triple A
rotateXYZ (xyz a b c) = xyz c a b

rotateXYZCubed : ∀ {A : Set} → (p : Triple A) →
  rotateXYZ (rotateXYZ (rotateXYZ p)) ≡ p
rotateXYZCubed (xyz a b c) = refl

diagonalFixed : ∀ {A : Set} → (a : A) →
  rotateXYZ (xyz a a a) ≡ xyz a a a
diagonalFixed a = refl

-- The basis axes are marked by the same C3 phase carrier as the
-- finite horn-address tree.  No choice of real constants is needed
-- for the group-theoretic intertwining theorem.
basis : C3.C3 → Triple Nat
basis C3.c0 = xyz 1 0 0
basis C3.c1 = xyz 0 1 0
basis C3.c2 = xyz 0 0 1

axisRotationIsC3Action : ∀ g →
  rotateXYZ (basis g) ≡ basis (C3.act C3.c1 g)
axisRotationIsC3Action C3.c0 = refl
axisRotationIsC3Action C3.c1 = refl
axisRotationIsC3Action C3.c2 = refl

markedAxisReallyMoves : rotateXYZ (basis C3.c0) ≢ basis C3.c0
markedAxisReallyMoves ()

-- Point-set extension of rotation by a fixed infinity point.
-- This is only the underlying carrier of a one-point compactification.
data PointAtInfinity (A : Set) : Set where
  finite : Triple A → PointAtInfinity A
  infinity : PointAtInfinity A

rotateCompact : ∀ {A : Set} → PointAtInfinity A → PointAtInfinity A
rotateCompact (finite p) = finite (rotateXYZ p)
rotateCompact infinity = infinity

rotateCompactCubed : ∀ {A : Set} → (p : PointAtInfinity A) →
  rotateCompact (rotateCompact (rotateCompact p)) ≡ p
rotateCompactCubed (finite (xyz a b c)) = refl
rotateCompactCubed infinity = refl

infinityFixed : ∀ {A : Set} → rotateCompact {A} infinity ≡ infinity
infinityFixed = refl
