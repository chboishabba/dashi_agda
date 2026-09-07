{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Device.BishopTwoCellSparsePopulationResponseExact where

------------------------------------------------------------------------
-- TWO-CELL SPARSE POPULATION RESPONSE
--
-- The SG face block is exactly linear in carrier populations at the fixed
-- thermal-normalized drop.  This owner assembles those face blocks through the
-- two-cell incidence graph.  One perturbation value is owned per node, so the
-- internal node and face remain same-object across neighbouring cells.
------------------------------------------------------------------------

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Physics.Semiconductor.Device.ComputedFiniteDeviceCellExact as Cell
import DASHI.Physics.Semiconductor.Device.FiniteScharfetterGummelFluxExact as Mesh
import DASHI.Physics.Semiconductor.Device.BishopThermalNormalizedDropExact as Thermal
import DASHI.Physics.Semiconductor.Device.BishopSameObjectComputedFaceFluxExact as Base
import DASHI.Physics.Semiconductor.Device.BishopSGPopulationJacobianExact as FaceJ

record NodePerturbation : Set where
  constructor nodePerturbation
  field
    delta0 : BishopReal.ℝ
    delta1 : BishopReal.ℝ
    delta2 : BishopReal.ℝ
    delta3 : BishopReal.ℝ

open NodePerturbation public

nodeDelta : NodePerturbation → Mesh.SGNode → BishopReal.ℝ
nodeDelta p Mesh.node0 = delta0 p
nodeDelta p Mesh.node1 = delta1 p
nodeDelta p Mesh.node2 = delta2 p
nodeDelta p Mesh.node3 = delta3 p

facePerturbation :
  (basePopulation : Mesh.SGNode → BishopReal.ℝ) →
  NodePerturbation →
  Mesh.SGFace →
  FaceJ.FixedDropPopulationPerturbation
    Thermal.normalizedDrop
    Thermal.normalizedDropPositiveUnitPoint
facePerturbation basePopulation p face =
  FaceJ.fixedDropPopulationPerturbation
    (basePopulation (Mesh.leftNode face))
    (basePopulation (Mesh.rightNode face))
    (nodeDelta p (Mesh.leftNode face))
    (nodeDelta p (Mesh.rightNode face))

faceResponse :
  (basePopulation : Mesh.SGNode → BishopReal.ℝ) →
  NodePerturbation →
  Mesh.SGFace → BishopReal.ℝ
faceResponse basePopulation p face =
  FaceJ.populationJacobianAction (facePerturbation basePopulation p face)

------------------------------------------------------------------------
-- Sparse continuity incidence.  G/R are held fixed in this partial Jacobian.
------------------------------------------------------------------------

electronCellAResponse :
  (basePopulation : Mesh.SGNode → BishopReal.ℝ) →
  NodePerturbation → BishopReal.ℝ
electronCellAResponse basePopulation p =
  BishopReal._-_
    (faceResponse basePopulation p Mesh.face01)
    (faceResponse basePopulation p Mesh.face12)

electronCellBResponse :
  (basePopulation : Mesh.SGNode → BishopReal.ℝ) →
  NodePerturbation → BishopReal.ℝ
electronCellBResponse basePopulation p =
  BishopReal._-_
    (faceResponse basePopulation p Mesh.face12)
    (faceResponse basePopulation p Mesh.face23)

holeCellAResponse :
  (basePopulation : Mesh.SGNode → BishopReal.ℝ) →
  NodePerturbation → BishopReal.ℝ
holeCellAResponse basePopulation p =
  BishopReal._-_
    (faceResponse basePopulation p Mesh.face12)
    (faceResponse basePopulation p Mesh.face01)

holeCellBResponse :
  (basePopulation : Mesh.SGNode → BishopReal.ℝ) →
  NodePerturbation → BishopReal.ℝ
holeCellBResponse basePopulation p =
  BishopReal._-_
    (faceResponse basePopulation p Mesh.face23)
    (faceResponse basePopulation p Mesh.face12)

------------------------------------------------------------------------
-- Exact opposite-orientation identities for a single carrier family.
------------------------------------------------------------------------

cellAOppositeOrientation :
  (basePopulation : Mesh.SGNode → BishopReal.ℝ) →
  (p : NodePerturbation) →
  BishopReal._≃_
    (holeCellAResponse basePopulation p)
    (BishopReal.- (electronCellAResponse basePopulation p))
cellAOppositeOrientation basePopulation p =
  let
    left = faceResponse basePopulation p Mesh.face01
    right = faceResponse basePopulation p Mesh.face12
    open BishopP.ℝ-Solver
  in
  solve 2
    (λ l r → (r ⊖ l) ⊜ (⊝ (l ⊖ r)))
    BishopP.≃-refl left right

cellBOppositeOrientation :
  (basePopulation : Mesh.SGNode → BishopReal.ℝ) →
  (p : NodePerturbation) →
  BishopReal._≃_
    (holeCellBResponse basePopulation p)
    (BishopReal.- (electronCellBResponse basePopulation p))
cellBOppositeOrientation basePopulation p =
  let
    left = faceResponse basePopulation p Mesh.face12
    right = faceResponse basePopulation p Mesh.face23
    open BishopP.ℝ-Solver
  in
  solve 2
    (λ l r → (r ⊖ l) ⊜ (⊝ (l ⊖ r)))
    BishopP.≃-refl left right

------------------------------------------------------------------------
-- Same-object specializations to the currently computed electron/hole profiles.
------------------------------------------------------------------------

electronBasePopulation : Cell.SourceCharge → Mesh.SGNode → BishopReal.ℝ
electronBasePopulation q node = Base.embedPopulationCode (Mesh.electronPopulationAt q node)

holeBasePopulation : Cell.SourceCharge → Mesh.SGNode → BishopReal.ℝ
holeBasePopulation q node = Base.embedPopulationCode (Mesh.holePopulationAt q node)

electronFaceDifferenceExact :
  (q : Cell.SourceCharge) →
  (p : NodePerturbation) →
  (face : Mesh.SGFace) →
  BishopReal._≃_
    (BishopReal._-_
      (DASHI.Physics.Semiconductor.Device.BishopConcreteScharfetterGummelFaceFluxExact.concreteBishopSGFaceFlux
        (FaceJ.perturbedFace (facePerturbation (electronBasePopulation q) p face)))
      (DASHI.Physics.Semiconductor.Device.BishopConcreteScharfetterGummelFaceFluxExact.concreteBishopSGFaceFlux
        (FaceJ.baseFace (facePerturbation (electronBasePopulation q) p face))))
    (faceResponse (electronBasePopulation q) p face)
electronFaceDifferenceExact q p face =
  FaceJ.populationFiniteDifferenceIsJacobianAction
    (facePerturbation (electronBasePopulation q) p face)

------------------------------------------------------------------------
-- Sparsity boundary.
------------------------------------------------------------------------

data TwoCellResponseResidualLeaf : Set where
  PotentialJacobianBlock : TwoCellResponseResidualLeaf
  PoissonToPopulationDerivative : TwoCellResponseResidualLeaf
  GenerationRecombinationDerivative : TwoCellResponseResidualLeaf
  PhysicalDensityScaling : TwoCellResponseResidualLeaf
  DimensionalCurrentScaling : TwoCellResponseResidualLeaf
  InverseSparseResponse : TwoCellResponseResidualLeaf

-- This is an exact partial Jacobian block, not the full coupled Gummel/Newton
-- Jacobian.  It owns population-coordinate response at fixed thermal drop and
-- fixed G/R only.
