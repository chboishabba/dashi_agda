module DASHI.Reasoning.Dialectic27S3PresentationVsGridAutomorphismExact where

------------------------------------------------------------------------
-- #1414 INSPIRED / WOOGAROO-RELEVANT CRITICAL MAX-CUT
--
-- S3 relabellings are legitimate invertible PRESENTATION charts on the
-- three dialectical positions. They do NOT all preserve strict nearest-
-- neighbour GRID adjacency of X/Y/Z interaction cubes!
--
-- The ordered 3-site path -1 <-> 0 <-> +1 has exactly C2 graph
-- automorphisms: identity and endpoint reflection. The C3 root
-- monodromy action and arbitrary S3 palette action from unmerged
-- polynomial PR #1414 MUST NOT be welded into grid automorphisms.
--
-- Exact owner: Base369Ternary27HypervoxelFabricGeometryExact's
-- TritGridStep and noDirect{Neg,Pos}To{Pos,Neg}.
-- Source/project evidence and pants glue additionally require distinct
-- typed witnesses, even for an actual grid automorphism.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Foundations.SSPTritCarrier as Trit
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Perm
import DASHI.Reasoning.DialecticXYInteractionZTransportExact as XY

-- These charts correspond exactly to existing S3 permutation codes
-- under the user's thesis/antithesis/synthesis role interpretation.
rotatePosition : Trit.SSPTrit → Trit.SSPTrit
rotatePosition Trit.sspNegOne = Trit.sspZero
rotatePosition Trit.sspZero = Trit.sspPosOne
rotatePosition Trit.sspPosOne = Trit.sspNegOne

reflectPosition : Trit.SSPTrit → Trit.SSPTrit
reflectPosition Trit.sspNegOne = Trit.sspPosOne
reflectPosition Trit.sspZero = Trit.sspZero
reflectPosition Trit.sspPosOne = Trit.sspNegOne

swapFirstTwo : Trit.SSPTrit → Trit.SSPTrit
swapFirstTwo Trit.sspNegOne = Trit.sspZero
swapFirstTwo Trit.sspZero = Trit.sspNegOne
swapFirstTwo Trit.sspPosOne = Trit.sspPosOne

swapLastTwo : Trit.SSPTrit → Trit.SSPTrit
swapLastTwo Trit.sspNegOne = Trit.sspNegOne
swapLastTwo Trit.sspZero = Trit.sspPosOne
swapLastTwo Trit.sspPosOne = Trit.sspZero

-- Identity and endpoint reflection preserve every directed grid step.
reflectIsInvolution : (t : Trit.SSPTrit) →
  reflectPosition (reflectPosition t) ≡ t
reflectIsInvolution Trit.sspNegOne = refl
reflectIsInvolution Trit.sspZero = refl
reflectIsInvolution Trit.sspPosOne = refl

reflectPreservesGridStep :
  ∀ {a b : Trit.SSPTrit} →
  Cube.TritGridStep a b →
  Cube.TritGridStep (reflectPosition a) (reflectPosition b)
reflectPreservesGridStep Cube.negToZero = Cube.posToZero
reflectPreservesGridStep Cube.zeroToNeg = Cube.zeroToPos
reflectPreservesGridStep Cube.zeroToPos = Cube.zeroToNeg
reflectPreservesGridStep Cube.posToZero = Cube.negToZero

reflectCube : Cube.Ternary27Point → Cube.Ternary27Point
reflectCube (Cube.ternary27Point x y z) =
  Cube.ternary27Point
    (reflectPosition x) (reflectPosition y) (reflectPosition z)

reflectCubeInvolution : (v : Cube.Ternary27Point) →
  reflectCube (reflectCube v) ≡ v
reflectCubeInvolution (Cube.ternary27Point x y z)
  rewrite reflectIsInvolution x
        | reflectIsInvolution y
        | reflectIsInvolution z = refl

reflectCubePreservesGrid :
  ∀ {left right : Cube.Ternary27Point} →
  Cube.HypervoxelAdjacent left right →
  Cube.HypervoxelAdjacent (reflectCube left) (reflectCube right)
reflectCubePreservesGrid (Cube.adjacentX step) =
  Cube.adjacentX (reflectPreservesGridStep step)
reflectCubePreservesGrid (Cube.adjacentY step) =
  Cube.adjacentY (reflectPreservesGridStep step)
reflectCubePreservesGrid (Cube.adjacentZ step) =
  Cube.adjacentZ (reflectPreservesGridStep step)

-- FAIL of the C3 action as an adjacency-preserving coordinate map:
-- on the 0 -> +1 edge, cyclic shift yields +1 -> -1, which is a
-- prohibited *two-hop* jump. The paint palette may still rotate!
cyclicChartIsNotStrictGridGraphHom :
  (preserves : ∀ {a b} →
    Cube.TritGridStep a b →
    Cube.TritGridStep (rotatePosition a) (rotatePosition b)) →
  ⊥
cyclicChartIsNotStrictGridGraphHom preserves =
  Cube.noDirectPosToNeg (preserves Cube.zeroToPos)

swapFirstTwoIsNotStrictGridGraphHom :
  (preserves : ∀ {a b} →
    Cube.TritGridStep a b →
    Cube.TritGridStep (swapFirstTwo a) (swapFirstTwo b)) →
  ⊥
swapFirstTwoIsNotStrictGridGraphHom preserves =
  Cube.noDirectNegToPos (preserves Cube.zeroToPos)

swapLastTwoIsNotStrictGridGraphHom :
  (preserves : ∀ {a b} →
    Cube.TritGridStep a b →
    Cube.TritGridStep (swapLastTwo a) (swapLastTwo b)) →
  ⊥
swapLastTwoIsNotStrictGridGraphHom preserves =
  Cube.noDirectNegToPos (preserves Cube.negToZero)

-- Direct connection to the actual X/Y/Z role chart. When three
-- labels are recoloured with S3, their *semantics* require the
-- accompanying inverse legend. Only the two C2 grid maps above
-- are valid uniform geometric reorientations of strict adjacency.
roleEndpointReflection : XY.DialecticPosition → XY.DialecticPosition
roleEndpointReflection XY.thesis = XY.synthesis
roleEndpointReflection XY.antithesis = XY.antithesis
roleEndpointReflection XY.synthesis = XY.thesis

roleEndpointReflectionInvolutive : (role : XY.DialecticPosition) →
  roleEndpointReflection (roleEndpointReflection role) ≡ role
roleEndpointReflectionInvolutive XY.thesis = refl
roleEndpointReflectionInvolutive XY.antithesis = refl
roleEndpointReflectionInvolutive XY.synthesis = refl
