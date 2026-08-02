module DASHI.Physics.YangMills.BalabanClayGate4ContourSwapDiameterExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4DimockLargeFieldSuppressionExact as Additive

------------------------------------------------------------------------
-- Curvature control of the CMP109 contour-family diameter.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Two coordinate-ordering contours with the same endpoints are compared by
-- adjacent coordinate swaps. With at most four active coordinate directions,
-- the maximum inversion count is six. The analytic input is therefore a
-- one-swap rectangular-curvature estimate; the finite assembly below converts
-- it into a diameter estimate for the whole contour family.
------------------------------------------------------------------------

maximumFourAxisInversions : Nat
maximumFourAxisInversions = 6

maximumFourAxisInversionsMeaning : maximumFourAxisInversions ≡ 6
maximumFourAxisInversionsMeaning = refl

record AdjacentSwapCurvatureCost (Scalar : Set) : Set₁ where
  field
    algebra : Additive.OrderedAdditiveBudget Scalar

    rectangleArea curvatureAmplitude rectangleCurvatureCost : Scalar
    nonlinearCorrection oneSwapCost : Scalar

    RectangleCurvatureProductMeaning : Set
    rectangleCurvatureProductMeaning :
      RectangleCurvatureProductMeaning

    oneSwapCostMeaning :
      oneSwapCost
      ≡ Additive.add algebra
          rectangleCurvatureCost nonlinearCorrection

    rectangularCurvatureContribution : Set
    rectangularCurvatureContributionEvidence :
      rectangularCurvatureContribution

open AdjacentSwapCurvatureCost public

record ContourSwapChainDiameter
    {Scalar : Set}
    (cost : AdjacentSwapCurvatureCost Scalar) : Set₁ where
  field
    swapCount : Nat
    pairwiseContourDistance : Scalar

    pairwiseDistanceBelowCountedSwaps :
      Additive.LessEqual (algebra cost)
        pairwiseContourDistance
        (Additive.natScale (algebra cost)
          (oneSwapCost cost) swapCount)

    countedSwapsBelowSix :
      Additive.LessEqual (algebra cost)
        (Additive.natScale (algebra cost)
          (oneSwapCost cost) swapCount)
        (Additive.natScale (algebra cost)
          (oneSwapCost cost) maximumFourAxisInversions)

open ContourSwapChainDiameter public

contourFamilyDiameterBelowSixSwapCosts :
  ∀ {Scalar}
    {cost : AdjacentSwapCurvatureCost Scalar} →
  (diameter : ContourSwapChainDiameter cost) →
  Additive.LessEqual (algebra cost)
    (pairwiseContourDistance diameter)
    (Additive.natScale (algebra cost)
      (oneSwapCost cost) maximumFourAxisInversions)
contourFamilyDiameterBelowSixSwapCosts {cost = cost} diameter =
  Additive.transitive (algebra cost)
    (pairwiseDistanceBelowCountedSwaps diameter)
    (countedSwapsBelowSix diameter)

record PrincipalLogDiameterBudget
    {Scalar : Set}
    (cost : AdjacentSwapCurvatureCost Scalar) : Set₁ where
  field
    diameter : ContourSwapChainDiameter cost
    principalLogRadius : Scalar

    sixSwapCostsInsideLogRadius :
      Additive.LessEqual (algebra cost)
        (Additive.natScale (algebra cost)
          (oneSwapCost cost) maximumFourAxisInversions)
        principalLogRadius

open PrincipalLogDiameterBudget public

contourFamilyInsidePrincipalLogDiameter :
  ∀ {Scalar}
    {cost : AdjacentSwapCurvatureCost Scalar} →
  (budget : PrincipalLogDiameterBudget cost) →
  Additive.LessEqual (algebra cost)
    (pairwiseContourDistance (diameter budget))
    (principalLogRadius budget)
contourFamilyInsidePrincipalLogDiameter {cost = cost} budget =
  Additive.transitive (algebra cost)
    (contourFamilyDiameterBelowSixSwapCosts (diameter budget))
    (sixSwapCostsInsideLogRadius budget)

fourAxisInversionCapLevel : ProofLevel
fourAxisInversionCapLevel = computed

contourSwapDiameterAssemblyLevel : ProofLevel
contourSwapDiameterAssemblyLevel = machineChecked

principalLogDiameterTransportLevel : ProofLevel
principalLogDiameterTransportLevel = machineChecked

physicalRectangleCurvatureProductInputsLevel : ProofLevel
physicalRectangleCurvatureProductInputsLevel = conditional

physicalAdjacentSwapCurvatureEstimateInputsLevel : ProofLevel
physicalAdjacentSwapCurvatureEstimateInputsLevel = conditional

physicalPrincipalLogRadiusComparisonInputsLevel : ProofLevel
physicalPrincipalLogRadiusComparisonInputsLevel = conditional
