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

------------------------------------------------------------------------
-- 1. Literal spatial three-cycle on the same generated grid carrier.
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

------------------------------------------------------------------------
-- 2. Eq. (5.6) pays invariance/equivariance of the scalar projection under
-- this C3 subgroup whenever the already-defined CMP109 source symmetry is
-- instantiated for that same contribution.
------------------------------------------------------------------------

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

cmp109ContributionC3Equivariant : ∀ {contribution}
  (symmetry : Source.CMP109ScalarEuclideanSymmetry contribution) →
  C3.EquivariantMap cmp109SpatialC3Action identityRationalC3Action contribution
cmp109ContributionC3Equivariant symmetry = record
  { intertwines = λ cell → sym (cycleInvariant symmetry cell) }

------------------------------------------------------------------------
-- 3. Recovery status.  This closes the old categorical statement that Balaban
-- had no source-exact C3 action at all.  The broader R132--R144 unified
-- density/action/stress/Schwinger recovery compiler still needs explicit
-- transport of this spatial action across each same-object seam.
------------------------------------------------------------------------

cmp109LiteralSpatialC3Recovered : Bool
cmp109LiteralSpatialC3Recovered = true

cmp109C3SourceBacked : Bool
cmp109C3SourceBacked = true

cmp109C3ActsOnLiteralGeneratedGrid : Bool
cmp109C3ActsOnLiteralGeneratedGrid = true

cmp109ScalarProjectionEquivarianceAvailable : Bool
cmp109ScalarProjectionEquivarianceAvailable = true

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
    actionManufacturedFrom369Analogy : Bool
    unifiedSchwingerRecoveryIntertwinerClosed : Bool

canonicalBalabanCMP109C3Boundary : BalabanCMP109C3Boundary
canonicalBalabanCMP109C3Boundary =
  balaban-cmp109-c3-boundary true true true false false
