module DASHI.Physics.YangMills.BalabanCMP109SpatialC3ActionExact where

------------------------------------------------------------------------
-- SOURCE-EXACT BALABAN C3 RECOVERY ON THE CMP109 VACUUM-POLARIZATION CARRIER
--
-- Balaban CMP109 §5, Eq. (5.6) gives coordinate-permutation covariance of the
-- literal vacuum-polarization tensor.  The repository already formalizes the
-- adjacent coordinate transpositions on the generated four-dimensional grid.
--
-- Two genuine order-three subgroups are useful and must not be conflated:
--   * cycle012: rotates coordinates 0,1,2 and fixes 3;
--   * cycle123: fixes coordinate 0 and rotates 1,2,3.
--
-- The first was the initially recovered Euclidean C3.  The second is the
-- physically aligned x/y/z spatial C3 for downstream Lorentzian consumers,
-- where axis 0 is the time coordinate.  Both come from the same source-backed
-- hypercubic permutation covariance; neither is manufactured from Base369.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Rational.Base using (ℚ)

import DASHI.Core.ThreeChannelC3EquivarianceGateExact as C3
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4HypercubicGeneratedActionExact as Action
import DASHI.Physics.YangMills.BalabanCMP109VacuumPolarizationHypercubicSourceSymmetryExact as Source

------------------------------------------------------------------------
-- Euclidean cycle on coordinates 0,1,2.
------------------------------------------------------------------------

spatialCycle012 : Grid.GridCell4 → Grid.GridCell4
spatialCycle012 cell =
  Action.act Action.swap01 (Action.act Action.swap12 cell)

spatialCycle012Meaning : ∀ a b c d →
  spatialCycle012 (Grid.gridCell4 a b c d)
  ≡ Grid.gridCell4 c a b d
spatialCycle012Meaning a b c d = refl

spatialCycle012Cubed : ∀ cell →
  spatialCycle012 (spatialCycle012 (spatialCycle012 cell)) ≡ cell
spatialCycle012Cubed (Grid.gridCell4 a b c d) = refl

cmp109SpatialC3Action : C3.OrderThreeAction Grid.GridCell4
cmp109SpatialC3Action = record
  { rotate = spatialCycle012
  ; rotateCubed = spatialCycle012Cubed
  }

cycleInvariant : ∀ {contribution}
  (symmetry : Source.CMP109ScalarEuclideanSymmetry contribution)
  (cell : Grid.GridCell4) →
  contribution cell ≡ contribution (spatialCycle012 cell)
cycleInvariant symmetry cell =
  trans
    (Source.permutationInvariant symmetry Source.permute12 cell)
    (Source.permutationInvariant symmetry Source.permute01
      (Action.act Action.swap12 cell))

------------------------------------------------------------------------
-- Lorentzian-spatial cycle: coordinate 0 fixed, x/y/z = 1,2,3 cycled.
------------------------------------------------------------------------

spatialCycle123 : Grid.GridCell4 → Grid.GridCell4
spatialCycle123 cell =
  Action.act Action.swap12 (Action.act Action.swap23 cell)

spatialCycle123Meaning : ∀ a b c d →
  spatialCycle123 (Grid.gridCell4 a b c d)
  ≡ Grid.gridCell4 a d b c
spatialCycle123Meaning a b c d = refl

spatialCycle123Cubed : ∀ cell →
  spatialCycle123 (spatialCycle123 (spatialCycle123 cell)) ≡ cell
spatialCycle123Cubed (Grid.gridCell4 a b c d) = refl

cmp109SpatialXYZC3Action : C3.OrderThreeAction Grid.GridCell4
cmp109SpatialXYZC3Action = record
  { rotate = spatialCycle123
  ; rotateCubed = spatialCycle123Cubed
  }

cycle123Invariant : ∀ {contribution}
  (symmetry : Source.CMP109ScalarEuclideanSymmetry contribution)
  (cell : Grid.GridCell4) →
  contribution cell ≡ contribution (spatialCycle123 cell)
cycle123Invariant symmetry cell =
  trans
    (Source.permutationInvariant symmetry Source.permute23 cell)
    (Source.permutationInvariant symmetry Source.permute12
      (Action.act Action.swap23 cell))

identityRationalC3Action : C3.OrderThreeAction ℚ
identityRationalC3Action = record
  { rotate = λ value → value
  ; rotateCubed = λ value → refl
  }

identityGridC3Equivariant :
  C3.EquivariantMap cmp109SpatialC3Action cmp109SpatialC3Action (λ cell → cell)
identityGridC3Equivariant = record
  { intertwines = λ cell → refl }

identityGridXYZC3Equivariant :
  C3.EquivariantMap cmp109SpatialXYZC3Action cmp109SpatialXYZC3Action (λ cell → cell)
identityGridXYZC3Equivariant = record
  { intertwines = λ cell → refl }

cmp109ContributionC3Equivariant : ∀ {contribution}
  (symmetry : Source.CMP109ScalarEuclideanSymmetry contribution) →
  C3.EquivariantMap cmp109SpatialC3Action identityRationalC3Action contribution
cmp109ContributionC3Equivariant symmetry = record
  { intertwines = λ cell → sym (cycleInvariant symmetry cell) }

cmp109ContributionXYZC3Equivariant : ∀ {contribution}
  (symmetry : Source.CMP109ScalarEuclideanSymmetry contribution) →
  C3.EquivariantMap cmp109SpatialXYZC3Action identityRationalC3Action contribution
cmp109ContributionXYZC3Equivariant symmetry = record
  { intertwines = λ cell → sym (cycle123Invariant symmetry cell) }

cmp109ThreeChannelC3Weld : ∀ {contribution}
  (symmetry : Source.CMP109ScalarEuclideanSymmetry contribution) →
  C3.ThreeChannelC3Weld Grid.GridCell4 Grid.GridCell4 ℚ
cmp109ThreeChannelC3Weld {contribution} symmetry = record
  { inputAction = cmp109SpatialC3Action
  ; midAction = cmp109SpatialC3Action
  ; outputAction = identityRationalC3Action
  ; forward = λ cell → cell
  ; consumer = contribution
  ; forwardEquivariant = identityGridC3Equivariant
  ; consumerEquivariant = cmp109ContributionC3Equivariant symmetry
  }

cmp109SpatialXYZThreeChannelC3Weld : ∀ {contribution}
  (symmetry : Source.CMP109ScalarEuclideanSymmetry contribution) →
  C3.ThreeChannelC3Weld Grid.GridCell4 Grid.GridCell4 ℚ
cmp109SpatialXYZThreeChannelC3Weld {contribution} symmetry = record
  { inputAction = cmp109SpatialXYZC3Action
  ; midAction = cmp109SpatialXYZC3Action
  ; outputAction = identityRationalC3Action
  ; forward = λ cell → cell
  ; consumer = contribution
  ; forwardEquivariant = identityGridXYZC3Equivariant
  ; consumerEquivariant = cmp109ContributionXYZC3Equivariant symmetry
  }

cmp109LiteralSpatialC3Recovered : Bool
cmp109LiteralSpatialC3Recovered = true

cmp109Spatial123C3Recovered : Bool
cmp109Spatial123C3Recovered = true

cycle012IsLorentzSpatialXYZ : Bool
cycle012IsLorentzSpatialXYZ = false

cmp109C3SourceBacked : Bool
cmp109C3SourceBacked = true

cmp109C3ActsOnLiteralGeneratedGrid : Bool
cmp109C3ActsOnLiteralGeneratedGrid = true

cmp109ScalarProjectionEquivarianceAvailable : Bool
cmp109ScalarProjectionEquivarianceAvailable = true

cmp109ThreeChannelWeldClosed : Bool
cmp109ThreeChannelWeldClosed = true

cmp109SpatialXYZThreeChannelWeldClosed : Bool
cmp109SpatialXYZThreeChannelWeldClosed = true

unifiedRecoveryC3TransportClosed : Bool
unifiedRecoveryC3TransportClosed = false

base369AnalogyNeededForThisAction : Bool
base369AnalogyNeededForThisAction = false

record BalabanCMP109C3Boundary : Set where
  constructor balaban-cmp109-c3-boundary
  field
    sourceCoordinatePermutationCovarianceUsed : Bool
    literalOrderThreeEuclidean012ActionConstructed : Bool
    literalOrderThreeSpatialXYZ123ActionConstructed : Bool
    sameGridScalarEquivarianceConstructed : Bool
    spatialXYZThreeChannelC3WeldConstructed : Bool
    actionManufacturedFrom369Analogy : Bool
    unifiedSchwingerRecoveryIntertwinerClosed : Bool

canonicalBalabanCMP109C3Boundary : BalabanCMP109C3Boundary
canonicalBalabanCMP109C3Boundary =
  balaban-cmp109-c3-boundary true true true true true false false
