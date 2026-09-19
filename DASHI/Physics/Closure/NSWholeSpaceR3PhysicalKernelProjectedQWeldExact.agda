module DASHI.Physics.Closure.NSWholeSpaceR3PhysicalKernelProjectedQWeldExact where

------------------------------------------------------------------------
-- A / PHYSICAL RESOLVENT-KERNEL GRAM -> CANONICAL PROJECTED q BUDGET
--
-- EuclideanPhysicalResolventKernel intentionally permits a general Gram scalar.
-- The canonical NS realization, however, wants that scalar to be the energy of
-- the actual Leray-projected nonlinear cell selected by the kernel.
--
-- This owner isolates exactly that same-object statement:
--
--   gramScalar(kernel,I) ~= || cell(kernel,I).projected ||^2.
--
-- Once supplied, no further Gram inequality is required.  The already-proved
-- continuous Leray contraction and divergence-form Cauchy theorem give
--
--   gramScalar(kernel,I)
--      <= |xi|^2 ||u_eta||^2 ||u_zeta||^2,
--
-- and the directional second-moment theorem supplies the second q factor.
-- The result is the exact R3RadialFactorBudget used by the inverse-cube and
-- radial-Lebesgue compilers.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Physics.Closure.NSCanonicalEuclideanPeriodicSemanticCarriersExact as Canonical
import DASHI.Physics.Closure.NSTriadKNEuclideanSignedFrequencyCarrierRealizationExact as Euclidean
import DASHI.Physics.Closure.NSTriadKNEuclideanPhysicalFourierNSExact as Physical
import DASHI.Physics.Closure.NSTriadKNEuclideanViscousHeatRateExact as Heat
import DASHI.Physics.Closure.NSTriadKNEuclideanBishopLerayPythagorasExact as Leray
import DASHI.Physics.Closure.NSTriadKNEuclideanProjectedCellOutputQExact as Projected
import DASHI.Physics.Closure.NSTriadKNEuclideanProjectedInteractionQWeldExact as Formula
import DASHI.Physics.Closure.NSWholeSpaceR3DirectionalSecondMomentQGainExact as Directional
import DASHI.Physics.Closure.NSWholeSpaceR3PhysicalQBudgetCompilerExact as Budget
import DASHI.Physics.Closure.NSWholeSpaceR3CanonicalRadialDataExact as CanonicalRadial
import DASHI.Physics.Closure.NSWholeSpaceR3RadialFactorBudgetExact as RadialBudget

record PhysicalKernelProjectedQWeld
    {S : Canonical.CanonicalNSSemantics}
    {trajectory : Physical.EuclideanFourierTrajectory S}
    (kernel : Physical.EuclideanPhysicalResolventKernel trajectory)
    (point : Heat.PuncturedEuclideanFrequency)
    (I : Euclidean.EuclideanInteraction) : Set₁ where
  constructor physical-kernel-projected-q-weld
  field
    formulaWeld :
      Formula.ProjectedInteractionFormulaWeld
        point
        (Physical.cell kernel I)

    gramScalarIsProjectedCellEnergy :
      BishopReal._≃_
        (Physical.gramScalar kernel I)
        (Leray.complex3NormSquared
          (Physical.lerayProjectedCell
            (Physical.cell kernel I)))

open PhysicalKernelProjectedQWeld public

kernelProjectedGramNonnegative :
  ∀ {S trajectory kernel point I} →
  (weld :
    PhysicalKernelProjectedQWeld
      {S} {trajectory} kernel point I) →
  BishopReal.NonNegative
    (Physical.gramScalar kernel I)
kernelProjectedGramNonnegative {kernel = kernel} {I = I} weld =
  BishopP.0≤x⇒nonNegx
    (BishopP.≤-respʳ-≃
      (gramScalarIsProjectedCellEnergy weld)
      (BishopP.nonNegx⇒0≤x
        (Leray.complex3NormSquaredNonnegative
          (Physical.lerayProjectedCell
            (Physical.cell kernel I)))))

kernelProjectedGramOutputQBound :
  ∀ {S trajectory kernel point I} →
  (weld :
    PhysicalKernelProjectedQWeld
      {S} {trajectory} kernel point I) →
  BishopReal._≤_
    (Physical.gramScalar kernel I)
    (BishopReal._*_
      (Heat.frequencyNormSquared (Heat.frequency point))
      (Projected.projectedCellMajorant
        (Physical.uEta (Physical.cell kernel I))
        (Physical.uZeta (Physical.cell kernel I))))
kernelProjectedGramOutputQBound {kernel = kernel} {I = I} weld =
  BishopP.≤-respˡ-≃
    (gramScalarIsProjectedCellEnergy weld)
    (Formula.physicalProjectedCellOutputQBound
      (formulaWeld weld))

kernelProjectedGramMajorantNonnegative :
  ∀ {S trajectory kernel point I} →
  PhysicalKernelProjectedQWeld
    {S} {trajectory} kernel point I →
  BishopReal.NonNegative
    (Projected.projectedCellMajorant
      (Physical.uEta (Physical.cell kernel I))
      (Physical.uZeta (Physical.cell kernel I)))
kernelProjectedGramMajorantNonnegative
    {kernel = kernel} {I = I} weld =
  BishopP.nonNegx,y⇒nonNegx*y
    (Leray.complex3NormSquaredNonnegative
      (Physical.uEta (Physical.cell kernel I)))
    (Leray.complex3NormSquaredNonnegative
      (Physical.uZeta (Physical.cell kernel I)))

record PhysicalKernelProjectedQBudgetInputs
    {S : Canonical.CanonicalNSSemantics}
    {trajectory : Physical.EuclideanFourierTrajectory S}
    (kernel : Physical.EuclideanPhysicalResolventKernel trajectory)
    (fluid : Heat.PositiveViscosity)
    (point : Heat.PuncturedEuclideanFrequency)
    (I : Euclidean.EuclideanInteraction)
    (secondMoment : BishopReal.ℝ) : Set₁ where
  constructor physical-kernel-projected-q-budget-inputs
  field
    projectedGramWeld :
      PhysicalKernelProjectedQWeld kernel point I

    directionalSecondMoment :
      Directional.DirectionalSecondMomentSlot
        (Heat.frequency point)
        secondMoment

open PhysicalKernelProjectedQBudgetInputs public

kernelInputsToPhysicalQBudget :
  ∀ {S trajectory kernel fluid point I secondMoment} →
  (inputs :
    PhysicalKernelProjectedQBudgetInputs
      {S} {trajectory}
      kernel fluid point I secondMoment) →
  Budget.CanonicalPhysicalQBudgetInputs
    fluid
    point
    (Physical.gramScalar kernel I)
    secondMoment
    (Projected.projectedCellMajorant
      (Physical.uEta (Physical.cell kernel I))
      (Physical.uZeta (Physical.cell kernel I)))
kernelInputsToPhysicalQBudget inputs =
  Budget.canonical-physical-q-budget-inputs
    (kernelProjectedGramNonnegative
      (projectedGramWeld inputs))
    (kernelProjectedGramMajorantNonnegative
      (projectedGramWeld inputs))
    (kernelProjectedGramOutputQBound
      (projectedGramWeld inputs))
    (directionalSecondMoment inputs)

kernelInputsBuildRadialFactorBudget :
  ∀ {S trajectory kernel fluid point I secondMoment} →
  (inputs :
    PhysicalKernelProjectedQBudgetInputs
      {S} {trajectory}
      kernel fluid point I secondMoment) →
  RadialBudget.R3RadialFactorBudget
    (CanonicalRadial.canonicalRadialData fluid point)
    (Physical.gramScalar kernel I)
    secondMoment
    (Projected.projectedCellMajorant
      (Physical.uEta (Physical.cell kernel I))
      (Physical.uZeta (Physical.cell kernel I)))
    (Budget.derivativeMajorant
      (Budget.canonicalInputsToPhysicalQBudget
        (kernelInputsToPhysicalQBudget inputs)))
kernelInputsBuildRadialFactorBudget inputs =
  Budget.canonicalInputsBuildRadialFactorBudget
    (kernelInputsToPhysicalQBudget inputs)

kernelGramQEstimateDerivedFromSameObjectWeld : Bool
kernelGramQEstimateDerivedFromSameObjectWeld = true

kernelGramQEstimateAcceptedAsIndependentHypothesis : Bool
kernelGramQEstimateAcceptedAsIndependentHypothesis = false

kernelProjectedQBudgetCompilerClosed : Bool
kernelProjectedQBudgetCompilerClosed = true

clayPromotion : Bool
clayPromotion = false

kernelGramQEstimateDerivedFromSameObjectWeldIsTrue :
  kernelGramQEstimateDerivedFromSameObjectWeld ≡ true
kernelGramQEstimateDerivedFromSameObjectWeldIsTrue = refl

kernelGramQEstimateAcceptedAsIndependentHypothesisIsFalse :
  kernelGramQEstimateAcceptedAsIndependentHypothesis ≡ false
kernelGramQEstimateAcceptedAsIndependentHypothesisIsFalse = refl

kernelProjectedQBudgetCompilerClosedIsTrue :
  kernelProjectedQBudgetCompilerClosed ≡ true
kernelProjectedQBudgetCompilerClosedIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
