module DASHI.Mathematics.Topology.AlexanderHornedC3R3HodgeEquivarianceExact where

------------------------------------------------------------------------
-- R3 / HODGE / SU2 BRIDGE ON THE SAME GEOMETRIC C3 ROTATION
--
-- Reuses the actual repo proof owner
--   Physics.Foundations.R3HodgeCrossExact
-- which already establishes star(wedge(u,v))=cross(u,v) and
-- [u,v]_su2 = 2 cross(u,v) in Euclidean coordinates.
--
-- We prove these structures are C3-EQUIVARIANT under the
-- same coordinate permutation as
--   AlexanderHornedC3AmbientRotationExact.rotateXYZ.
-- This is more than matching three or nine dimensions:
-- the polynomial maps themselves intertwine.
--
-- DIFFERENT CARRIERS: Existing R3HodgeCrossExact is over the
-- repository's axiomatic real ℝ, whereas the exact quaternion
-- rotor is over rational ℚ. The coefficient-extension / real
-- spin-cover theorem remains distinct, not faked by a Bool.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.List.Base using ([]; _∷_)
import Tactic.RingSolver as Solver

import DASHI.Physics.Foundations.R3HodgeCrossExact as Hodge
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as V3
import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier as Ring
import DASHI.Foundations.RealAnalysisAxioms as Real
import DASHI.Mathematics.Topology.AlexanderHornedC3AmbientRotationExact as Ambient

rotateV3 : V3.SU2LieAlgebra → V3.SU2LieAlgebra
rotateV3 (V3.su2Lie x y z) = V3.su2Lie z x y

rotateBivector : Hodge.Bivector3 → Hodge.Bivector3
rotateBivector (Hodge.bivector3 xy yz zx) =
  Hodge.bivector3 zx xy yz

rotateV3Cubed : ∀ v →
  rotateV3 (rotateV3 (rotateV3 v)) ≡ v
rotateV3Cubed (V3.su2Lie x y z) = refl

-- Mapping the actual ambient R3 triple into SU2's 3-axis
-- Lie-coordinate carrier is compatible with the SAME rotation.
asLieVector : Ambient.Triple Real.ℝ → V3.SU2LieAlgebra
asLieVector (Ambient.xyz x y z) = V3.su2Lie x y z

sameAmbientRotation : ∀ v →
  asLieVector (Ambient.rotateXYZ v) ≡
    rotateV3 (asLieVector v)
sameAmbientRotation (Ambient.xyz x y z) = refl

hodgeStarEquivariant : ∀ bivector →
  Hodge.hodgeStar3 (rotateBivector bivector)
    ≡ rotateV3 (Hodge.hodgeStar3 bivector)
hodgeStarEquivariant (Hodge.bivector3 xy yz zx) = refl

wedgeEquivariant : ∀ u v →
  Hodge.wedge3 (rotateV3 u) (rotateV3 v)
  ≡ rotateBivector (Hodge.wedge3 u v)
wedgeEquivariant
  (V3.su2Lie x y z) (V3.su2Lie a b c) =
  bivectorExt
    (Solver.solve (x ∷ y ∷ z ∷ a ∷ b ∷ c ∷ []) Ring.realSolverRing)
    (Solver.solve (x ∷ y ∷ z ∷ a ∷ b ∷ c ∷ []) Ring.realSolverRing)
    (Solver.solve (x ∷ y ∷ z ∷ a ∷ b ∷ c ∷ []) Ring.realSolverRing)
  where
    bivectorExt :
      ∀ {x y z x' y' z'} →
      x ≡ x' → y ≡ y' → z ≡ z' →
      Hodge.bivector3 x y z ≡ Hodge.bivector3 x' y' z'
    bivectorExt refl refl refl = refl

crossEquivariant : ∀ u v →
  Hodge.cross3 (rotateV3 u) (rotateV3 v)
  ≡ rotateV3 (Hodge.cross3 u v)
crossEquivariant
  (V3.su2Lie x y z) (V3.su2Lie a b c) =
  V3.su2LieExt
    (Solver.solve (x ∷ y ∷ z ∷ a ∷ b ∷ c ∷ []) Ring.realSolverRing)
    (Solver.solve (x ∷ y ∷ z ∷ a ∷ b ∷ c ∷ []) Ring.realSolverRing)
    (Solver.solve (x ∷ y ∷ z ∷ a ∷ b ∷ c ∷ []) Ring.realSolverRing)

-- These are finite polynomial covariance laws on the real
-- Lie-coordinate carrier. Spinor fields and E_n operads /
-- exceptional Lie groups are NOT identified by this theorem.
