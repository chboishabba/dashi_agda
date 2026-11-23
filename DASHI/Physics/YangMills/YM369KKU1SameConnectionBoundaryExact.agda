module DASHI.Physics.YangMills.YM369KKU1SameConnectionBoundaryExact where

------------------------------------------------------------------------
-- ORIGINAL ATTRIBUTION AND SCOPE (2026-11-18)
-- Classical: Cartan U1 inside SU2, Lie bracket and BPST instanton
-- (Belavin, Polyakov, Schwartz, Tyupkin 1975); the KK monopole of
-- Gross-Perry and Sorkin (1983) has a circle connection.
-- Existing DASHI owners:
-- * U1SU2GroupTorusExact: literal U1 group, SU2 inclusion homomorphism.
-- * BalabanSU2LieBracket and SU2Bracket369OrientationBridgeExact:
--   quaternion bracket [X,Y] = 2 X cross Y.
-- * BalabanCMP109SpatialC3ActionExact: exact source x-y-z cycle.
-- * FiniteQuaternionDoubleCover: finite quaternion multiplication.
-- New bounded result: exact commuting U1 source, finite quaternion
-- noncommuting witness, and preexisting subgroup morphism transported
-- together. The BPST-specific no-go is checked separately with
-- the exact symbolic curvature in check_kk_ym369_same_connection_obstruction.py.
-- User-proposed target: actual same-field 369 YM / KK identity.
-- This source DOES NOT establish a curved 5D Einstein-YM soliton,
-- YM continuum limit, physical gauge bundle equivalence or spin-1/2.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.List.Base using ([]; _∷_)
import Tactic.RingSolver as Solver

import DASHI.Physics.Electromagnetism.U1SU2GroupTorusExact as U1
import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier as SU2
import DASHI.Algebra.FiniteQuaternionDoubleCover as Q8
import DASHI.Physics.YangMills.SU2Bracket369OrientationBridgeExact as YM369
import DASHI.Physics.YangMills.BalabanCMP109SpatialC3ActionExact as Spatial
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid

-- The very same U1 circle included in the existing unit-quaternion SU2
-- carrier is abelian; this uses concrete source multiplication, not an
-- assumed "gauge field is abelian" Boolean.
u1MultiplyCommutative :
  (u v : U1.U1TorusElement) →
  U1.u1Multiply u v ≡ U1.u1Multiply v u
u1MultiplyCommutative
  (U1.u1-torus a b _) (U1.u1-torus c d _) =
  U1.u1Ext
    (Solver.solve (a ∷ b ∷ c ∷ d ∷ []) SU2.realSolverRing)
    (Solver.solve (a ∷ b ∷ c ∷ d ∷ []) SU2.realSolverRing)

-- Positive Cartan-subgroup bridge: this is exactly the pre-existing
-- group homomorphism, restated at its original source type.
u1CartanSU2Multiply :
  (u v : U1.U1TorusElement) →
  U1.includeU1InSU2 (U1.u1Multiply u v)
    ≡ SU2.su2Multiply (U1.includeU1InSU2 u) (U1.includeU1InSU2 v)
u1CartanSU2Multiply = U1.includePreservesMultiply

-- A finite nonabelian witness from the literal Q8 quaternion group.
-- No claim that its finite quotient is the full continuous SU2 bundle.
quaternionIJ : Q8.q8Multiply Q8.plusI Q8.plusJ ≡ Q8.plusK
quaternionIJ = refl

quaternionJI : Q8.q8Multiply Q8.plusJ Q8.plusI ≡ Q8.minusK
quaternionJI = refl

quaternionKSignsDistinct : Q8.plusK ≡ Q8.minusK → ⊥
quaternionKSignsDistinct ()

quaternionNoncommuting :
  Q8.q8Multiply Q8.plusI Q8.plusJ
    ≡ Q8.q8Multiply Q8.plusJ Q8.plusI → ⊥
quaternionNoncommuting ()

-- Reuse actual SOURCE XYZ spatial symmetry (time coordinate fixed);
-- no identification between this grid and a KK nut is assumed.
nativeYM369SpatialCycleCubed :
  (cell : Grid.GridCell4) →
  Spatial.spatialCycle123
    (Spatial.spatialCycle123 (Spatial.spatialCycle123 cell)) ≡ cell
nativeYM369SpatialCycleCubed = Spatial.spatialCycle123Cubed

-- Open: actual continuum connection equality, transition-function
-- matching, gauge-equivariant pullback, G5 Einstein/YM field equations,
-- physical source, all-curvature abelian reduction, and exchange topology.
