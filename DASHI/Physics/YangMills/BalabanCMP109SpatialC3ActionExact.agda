module DASHI.Physics.YangMills.BalabanCMP109SpatialC3ActionExact where

------------------------------------------------------------------------
-- SOURCE-EXACT BALABAN C3 RECOVERY ON THE CMP109 VACUUM-POLARIZATION CARRIER
--
-- Balaban CMP109 §5, Eq. (5.6) gives coordinate-permutation covariance of the
-- literal vacuum-polarization tensor.  The repository already formalizes the
-- adjacent coordinate transpositions on the generated four-dimensional grid.
-- Their composition below cycles coordinates 0,1,2 while leaving coordinate 3
-- fixed.  This is a genuine order-three subgroup of the source-backed
-- hypercubic action, not a C3 action inferred from the Base369 labels.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Rational.Base using (ℚ)

import DASHI.Core.ThreeChannelC3EquivarianceGateExact as C3
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4HypercubicGeneratedActionExact as Action
import DASHI.Physics.YangMills.BalabanCMP109VacuumPolarizationHypercubicSourceSymmetryExact as Source

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

identityRationalC3Action : C3.OrderThreeAction ℚ
identityRationalC3Action = record
  { rotate = λ value → value
  ; rotateCubed = λ value → refl
  }

identityGridC3Equivariant :
  C3.EquivariantMap cmp109SpatialC3Action cmp109SpatialC3Action (λ cell → cell)
identityGridC3Equivariant = record
  { intertwines = λ cell → refl }

cmp109ContributionC3Equivariant : ∀ {contribution}
  (symmetry : Source.CMP109ScalarEuclideanSymmetry contribution) →
  C3.EquivariantMap cmp109SpatialC3Action identityRationalC3Action contribution
cmp109ContributionC3Equivariant symmetry = record
  { intertwines = λ cell → sym (cycleInvariant symmetry cell) }

cmp109ThreeChannelC3Weld : ∀ {contribution}
  (symmetry : Source.CMP109ScalarEuclideanSymmetry contribution) →
  C3.ThreeChannelC3Weld Grid.GridCell4 Grid.GridCell4 ℚ
cmp109ThreeChannelC3Weld symmetry = record
  { inputAction = cmp109SpatialC3Action
  ; midAction = cmp109SpatialC3Action
  ; outputAction = identityRationalC3Action
  ; forward = λ cell → cell
  ; consumer = _
  ; forwardEquivariant = identityGridC3Equivariant
  ; consumerEquivariant = cmp109ContributionC3Equivariant symmetry
  }
  where
  contribution = Source.CMP109ScalarEuclideanSymmetry.contribution symmetry

cmp109LiteralSpatialC3Recovered : Bool
cmp109LiteralSpatialC3Recovered = true

cmp109C3SourceBacked : Bool
cmp109C3SourceBacked = true

cmp109C3ActsOnLiteralGeneratedGrid : Bool
cmp109C3ActsOnLiteralGeneratedGrid = true

cmp109ScalarProjectionEquivarianceAvailable : Bool
cmp109ScalarProjectionEquivarianceAvailable = true

cmp109ThreeChannelWeldClosed : Bool
cmp109ThreeChannelWeldClosed = true

unifiedRecoveryC3TransportClosed : Bool
unifiedRecoveryC3TransportClosed = false

base369AnalogyNeededForThisAction : Bool
base369AnalogyNeededForThisAction = false

record BalabanCMP109C3Boundary : Set where
  constructor balaban-cmp109-c3-boundary
  field
    sourceCoordinatePermutationCovarianceUsed : Bool
    literalOrderThreeSpatialActionConstructed : Bool
    sameGridScalarEquivarianceConstructed : Bool
    threeChannelC3WeldConstructed : Bool
    actionManufacturedFrom369Analogy : Bool
    unifiedSchwingerRecoveryIntertwinerClosed : Bool

canonicalBalabanCMP109C3Boundary : BalabanCMP109C3Boundary
canonicalBalabanCMP109C3Boundary =
  balaban-cmp109-c3-boundary true true true true false false
