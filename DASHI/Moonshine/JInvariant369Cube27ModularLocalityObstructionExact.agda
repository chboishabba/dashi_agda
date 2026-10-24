module DASHI.Moonshine.JInvariant369Cube27ModularLocalityObstructionExact where

-- Actual spatial 3x3x3 cube: selected modular braid cannot preserve
-- every native nearest-neighbour edge. No new "27-cycle" is invented.
-- Reuses the existing Cube27 graph and existing M modular slice map.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Empty using (⊥)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Moonshine.JInvariant369Cube27ModularSliceActionExact as Slice

positiveXSite : Cube.Ternary27Point
positiveXSite =
  Cube.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero

nativePositiveXEdge :
  Cube.HypervoxelAdjacent Cube.origin positiveXSite
nativePositiveXEdge = Cube.originAdjacentPositiveX

-- A mathematical candidate for a *strictly local* lattice coupling
-- that is invariant under the chosen braid modular map.
record BraidInvariantLocalCoupling
  (Bond : Cube.Ternary27Point → Cube.Ternary27Point → Set) : Set where
  field
    nativeSupport : (p q : Cube.Ternary27Point) →
      Bond p q → Cube.HypervoxelAdjacent p q
    braidInvariant : (p q : Cube.Ternary27Point) →
      Bond p q →
      Bond (Slice.modularSheetAction p) (Slice.modularSheetAction q)
open BraidInvariantLocalCoupling public

-- Exact no-go for any proposed native bond covering the origin -> x
-- edge: the M image is a diagonal and hence NOT a native cube edge.
cannotPreservePositiveXBond :
  ∀ {Bond} →
  (W : BraidInvariantLocalCoupling Bond) →
  Bond Cube.origin positiveXSite →
  ⊥
cannotPreservePositiveXBond W bond =
  Slice.modularImageOfNativeEdgeNotAnEdge
    (nativeSupport W
      (Slice.modularSheetAction Cube.origin)
      (Slice.modularSheetAction positiveXSite)
      (braidInvariant W Cube.origin positiveXSite bond))

-- In particular a full nearest-neighbour cube interaction is NOT
-- invariant under this selected modular braid action.
notFullCubeAdjacencyModularInvariant :
  ((p q : Cube.Ternary27Point) →
   Cube.HypervoxelAdjacent p q →
   Cube.HypervoxelAdjacent
     (Slice.modularSheetAction p)
     (Slice.modularSheetAction q)) → ⊥
notFullCubeAdjacencyModularInvariant preserves =
  Slice.modularImageOfNativeEdgeNotAnEdge
    (preserves Cube.origin positiveXSite nativePositiveXEdge)

-- Native graph degree is also the diagonal matrix element of its
-- combinatorial graph Laplacian. This is a concrete single-site
-- *conditional* Hamiltonian observable, not a Monster VOA claim.
axisDegree : SSP.SSPTrit → Nat
axisDegree SSP.sspNegOne = 1
axisDegree SSP.sspZero = 2
axisDegree SSP.sspPosOne = 1

cubeDegree : Cube.Ternary27Point → Nat
cubeDegree (Cube.ternary27Point x y z) =
  axisDegree x + axisDegree y + axisDegree z

degreeBefore :
  cubeDegree positiveXSite ≡ 5
degreeBefore = refl

degreeAfter :
  cubeDegree (Slice.modularSheetAction positiveXSite) ≡ 4
degreeAfter = refl

degreesNotPreserved :
  ((p : Cube.Ternary27Point) →
   cubeDegree (Slice.modularSheetAction p) ≡ cubeDegree p)
  → ⊥
degreesNotPreserved preserve with preserve positiveXSite
... | ()

-- Extrapolation remains conditional:
-- if a source implements H=J times this graph Laplacian and actually
-- implements the permutation, the local excitation at +x changes
-- diagonal expectation 5J -> 4J. An action on sector labels, a
-- Monster order-27 element, or a KK metric does not by itself
-- implement this source-dependent Hamiltonian.
