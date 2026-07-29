module DASHI.Codec.DNADeBruijnGeometry where

open import Agda.Builtin.List using (List; []; _∷_)

open import DASHI.Codec.DNAFirstFormalism using
  ( Base
  ; Axis3; axis0; axis1; axis2
  ; Line3; Voxel9; Cube27
  )
open import DASHI.Codec.DNAProductionConstraints using (ProductionState)
open import DASHI.Codec.DNAProductionDeBruijn using (LabelledWalk)

------------------------------------------------------------------------
-- Geometry and stream order are distinct carriers. A Traversal is explicit
-- data supplied by the caller; no field is definitionally a graph walk.

record Traversal (Shape : Set) : Set₁ where
  field
    serialise : Shape → List Base
open Traversal public

lineOrder012 : Traversal Line3
lineOrder012 = record
  { serialise = λ line →
      line axis0 ∷ line axis1 ∷ line axis2 ∷ []
  }

voxelRowMajor : Traversal Voxel9
voxelRowMajor = record
  { serialise = λ voxel →
      voxel axis0 axis0 ∷ voxel axis0 axis1 ∷ voxel axis0 axis2 ∷
      voxel axis1 axis0 ∷ voxel axis1 axis1 ∷ voxel axis1 axis2 ∷
      voxel axis2 axis0 ∷ voxel axis2 axis1 ∷ voxel axis2 axis2 ∷ []
  }

voxelColumnMajor : Traversal Voxel9
voxelColumnMajor = record
  { serialise = λ voxel →
      voxel axis0 axis0 ∷ voxel axis1 axis0 ∷ voxel axis2 axis0 ∷
      voxel axis0 axis1 ∷ voxel axis1 axis1 ∷ voxel axis2 axis1 ∷
      voxel axis0 axis2 ∷ voxel axis1 axis2 ∷ voxel axis2 axis2 ∷ []
  }

cubeLayerMajor : Traversal Cube27
cubeLayerMajor = record
  { serialise = λ cube →
      cube axis0 axis0 axis0 ∷ cube axis0 axis1 axis0 ∷ cube axis0 axis2 axis0 ∷
      cube axis1 axis0 axis0 ∷ cube axis1 axis1 axis0 ∷ cube axis1 axis2 axis0 ∷
      cube axis2 axis0 axis0 ∷ cube axis2 axis1 axis0 ∷ cube axis2 axis2 axis0 ∷
      cube axis0 axis0 axis1 ∷ cube axis0 axis1 axis1 ∷ cube axis0 axis2 axis1 ∷
      cube axis1 axis0 axis1 ∷ cube axis1 axis1 axis1 ∷ cube axis1 axis2 axis1 ∷
      cube axis2 axis0 axis1 ∷ cube axis2 axis1 axis1 ∷ cube axis2 axis2 axis1 ∷
      cube axis0 axis0 axis2 ∷ cube axis0 axis1 axis2 ∷ cube axis0 axis2 axis2 ∷
      cube axis1 axis0 axis2 ∷ cube axis1 axis1 axis2 ∷ cube axis1 axis2 axis2 ∷
      cube axis2 axis0 axis2 ∷ cube axis2 axis1 axis2 ∷ cube axis2 axis2 axis2 ∷ []
  }

------------------------------------------------------------------------
-- Stream legality and geometric legality remain independent predicates.

record GeometryPolicy (Shape : Set) : Set₁ where
  field
    GeometryLegal : Shape → Set
open GeometryPolicy public

record AdmissibleField
  (Shape : Set)
  (traversal : Traversal Shape)
  (geometry : GeometryPolicy Shape)
  (field : Shape)
  (start end : ProductionState) : Set where
  constructor admissibleField
  field
    streamLegal : LabelledWalk start (serialise traversal field) end
    geometryLegal : GeometryLegal geometry field
open AdmissibleField public

------------------------------------------------------------------------
-- A serialized geometric block is a finite-state transfer only relative to its
-- explicit traversal and incoming production state.

record Transfer (Shape : Set) (traversal : Traversal Shape) : Set₁ where
  constructor transfer
  field
    sourceField : Shape
    incoming : ProductionState
    outgoing : ProductionState
    path : LabelledWalk incoming (serialise traversal sourceField) outgoing
open Transfer public

LineTransfer : Set₁
LineTransfer = Transfer Line3 lineOrder012

RowMajorVoxelTransfer : Set₁
RowMajorVoxelTransfer = Transfer Voxel9 voxelRowMajor

ColumnMajorVoxelTransfer : Set₁
ColumnMajorVoxelTransfer = Transfer Voxel9 voxelColumnMajor

LayerMajorCubeTransfer : Set₁
LayerMajorCubeTransfer = Transfer Cube27 cubeLayerMajor

------------------------------------------------------------------------
-- This record makes the non-identification an explicit API boundary.

record GeometryStreamBoundary : Set₁ where
  field
    Geometry : Set
    traversal : Traversal Geometry
    streamWord : Geometry → List Base
    streamWordIsTraversal : ∀ g → streamWord g ≡ serialise traversal g

lineGeometryStreamBoundary : GeometryStreamBoundary
lineGeometryStreamBoundary = record
  { Geometry = Line3
  ; traversal = lineOrder012
  ; streamWord = serialise lineOrder012
  ; streamWordIsTraversal = λ line → refl
  }
