module DASHI.Physics.YangMills.BalabanClayGate4CMP109SmallDiameterFromSwapsExact where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embedding
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredExecutableGeometryExact as Executable
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PeriodicContourFamilyInstantiationExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4CMP109MinimalAdmissibleRepositoryScaleExact as Minimal
import DASHI.Physics.YangMills.BalabanClayGate4CMP109MinimalContourFamilyExact as Contour
import DASHI.Physics.YangMills.BalabanClayGate4CMP109MinimalAveragedContourExact as MinimalAverage
import DASHI.Physics.YangMills.BalabanClayGate4CMP109GroupAverageAxiomsExact as Average
import DASHI.Physics.YangMills.BalabanClayGate4ContourSwapDiameterExact as Swaps
import DASHI.Physics.YangMills.BalabanClayGate4DimockLargeFieldSuppressionExact as Additive

------------------------------------------------------------------------
-- Feed the adjacent-swap curvature estimate into CMP109 equation (0.11).
--
-- The group-average source theorem only asks for a sufficiently small-diameter
-- finite family.  The physical proof is now split into:
--
--   adjacent plaquette swaps -> six-swap diameter bound,
--   six-swap bound inside the selected group-average/log domain.
------------------------------------------------------------------------

record MinimalContourSwapGaugeData
    (Field Group Lie Scalar Bound : Set)
    (geometry : Executable.CenteredExecutableGeometry Minimal.radius)
    (point : Centered.CenteredBlockPoint4 Minimal.radius)
    (averageAxioms : Average.CMP109GroupAverageAxioms Group Lie Scalar)
    : Set₁ where
  field
    holonomy transformedHolonomy :
      Field →
      Periodic.ExecutablePeriodicContour
        (Embedding.centeredTorusParameter Minimal.radius)
        (Contour.minimalContourStart geometry) →
      Group

    leftGauge rightGauge : Field → Group

    pathHolonomyGaugeCovariant : ∀ field path →
      transformedHolonomy field path
      ≡ Average.multiply averageAxioms (leftGauge field)
          (Average.multiply averageAxioms
            (holonomy field path) (rightGauge field))

    swapCostAt : Field → Swaps.AdjacentSwapCurvatureCost Bound
    diameterBudgetAt : (field : Field) →
      Swaps.PrincipalLogDiameterBudget (swapCostAt field)

    smallDiameterFromSixSwapBound : ∀ field →
      Additive.LessEqual (Swaps.algebra (swapCostAt field))
        (Swaps.pairwiseContourDistance
          (Swaps.diameter (diameterBudgetAt field)))
        (Swaps.principalLogRadius (diameterBudgetAt field)) →
      Average.SmallDiameter averageAxioms
        (Average.mapList (holonomy field)
          (Contour.minimalContourFamily geometry point))

open MinimalContourSwapGaugeData public

asMinimalContourGaugeData :
  ∀ {Field Group Lie Scalar Bound}
    {geometry : Executable.CenteredExecutableGeometry Minimal.radius}
    {point : Centered.CenteredBlockPoint4 Minimal.radius}
    {averageAxioms : Average.CMP109GroupAverageAxioms Group Lie Scalar} →
  MinimalContourSwapGaugeData
    Field Group Lie Scalar Bound geometry point averageAxioms →
  MinimalAverage.MinimalContourGaugeData
    Field Group Lie Scalar geometry point averageAxioms
asMinimalContourGaugeData dataSet = record
  { MinimalAverage.MinimalContourGaugeData.holonomy = holonomy dataSet
  ; MinimalAverage.MinimalContourGaugeData.transformedHolonomy =
      transformedHolonomy dataSet
  ; MinimalAverage.MinimalContourGaugeData.leftGauge = leftGauge dataSet
  ; MinimalAverage.MinimalContourGaugeData.rightGauge = rightGauge dataSet
  ; MinimalAverage.MinimalContourGaugeData.pathHolonomyGaugeCovariant =
      pathHolonomyGaugeCovariant dataSet
  ; MinimalAverage.MinimalContourGaugeData.contourHolonomiesSmallDiameter =
      λ field →
        smallDiameterFromSixSwapBound dataSet field
          (Swaps.contourFamilyInsidePrincipalLogDiameter
            (diameterBudgetAt dataSet field))
  }

cmp109SmallDiameterFromSwapAssemblyLevel : ProofLevel
cmp109SmallDiameterFromSwapAssemblyLevel = machineChecked

physicalCMP109AdjacentSwapCostInputsLevel : ProofLevel
physicalCMP109AdjacentSwapCostInputsLevel = conditional

physicalCMP109SmallDiameterSemanticBridgeInputsLevel : ProofLevel
physicalCMP109SmallDiameterSemanticBridgeInputsLevel = conditional
