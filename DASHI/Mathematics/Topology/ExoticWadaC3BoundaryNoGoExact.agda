module DASHI.Mathematics.Topology.ExoticWadaC3BoundaryNoGoExact where

------------------------------------------------------------------------
-- EXACT C3-EQUIVARIANT BOUNDARY-INCIDENCE COUNTEREXAMPLE
--
-- Reuses DASHI.Core.FiniteC3OrbitStabilizerExact.  Three regions may
-- be cyclically permuted while their boundaries are NOT identical.
-- This is a 3-ray combinatorial model (ordinary planar sectors),
-- NOT a verified planar-domain embedding or a Lakes-of-Wada continuum.
-- Thus C3 equivariance alone cannot certify the Wada property.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.FiniteC3OrbitStabilizerExact as C3

-- Regions and boundary-ray labels share the EXACT pre-existing C3 carrier.
Region : Set
Region = C3.C3

Ray : Set
Ray = C3.C3

-- Three successive sectors; each sector has two bounding rays.
onBoundary : Region → Ray → Bool
onBoundary C3.c0 C3.c0 = true
onBoundary C3.c0 C3.c1 = true
onBoundary C3.c0 C3.c2 = false
onBoundary C3.c1 C3.c0 = false
onBoundary C3.c1 C3.c1 = true
onBoundary C3.c1 C3.c2 = true
onBoundary C3.c2 C3.c0 = true
onBoundary C3.c2 C3.c1 = false
onBoundary C3.c2 C3.c2 = true

rotate : C3.C3 → C3.C3
rotate = C3.act C3.c1

boundaryIncidenceEquivariant :
  (region : Region) (ray : Ray) →
  onBoundary (rotate region) (rotate ray) ≡ onBoundary region ray
boundaryIncidenceEquivariant C3.c0 C3.c0 = refl
boundaryIncidenceEquivariant C3.c0 C3.c1 = refl
boundaryIncidenceEquivariant C3.c0 C3.c2 = refl
boundaryIncidenceEquivariant C3.c1 C3.c0 = refl
boundaryIncidenceEquivariant C3.c1 C3.c1 = refl
boundaryIncidenceEquivariant C3.c1 C3.c2 = refl
boundaryIncidenceEquivariant C3.c2 C3.c0 = refl
boundaryIncidenceEquivariant C3.c2 C3.c1 = refl
boundaryIncidenceEquivariant C3.c2 C3.c2 = refl

SameBoundary : Region → Region → Set
SameBoundary a b = (ray : Ray) → onBoundary a ray ≡ onBoundary b ray

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

firstSecondDoNotShareBoundary : SameBoundary C3.c0 C3.c1 → ⊥
firstSecondDoNotShareBoundary proposedEquality =
  trueNotFalse (proposedEquality C3.c0)

-- Existence of a cyclic action and incidence equivariance does not
-- imply the ALL-THREE frontier equality required by Lakes of Wada.
