module DASHI.Physics.Closure.NSWholeSpaceR3CanonicalProjectedQBudgetExact where

------------------------------------------------------------------------
-- A / CANONICAL PROJECTED q x q BUDGET
--
-- For one physical Euclidean projected interaction, define the Gram-side
-- nonnegative factor to be the squared norm of its actual projected nonlinear
-- cell.  The previous owner proves
--
--   ||P_xi N_raw||^2
--      <= |xi|^2 (||u_eta||^2 ||u_zeta||^2).
--
-- Pair that with a directional second-moment slot
--
--   secondMoment = (xi . Dg)^2
--
-- whose |xi|^2 gain is theorem-derived by R^3 Cauchy.  This constructs the
-- canonical radial factor budget directly.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Physics.Closure.NSCanonicalEuclideanPeriodicSemanticCarriersExact as Canonical
import DASHI.Physics.Closure.NSTriadKNEuclideanPhysicalFourierNSExact as Physical
import DASHI.Physics.Closure.NSTriadKNEuclideanViscousHeatRateExact as Heat
import DASHI.Physics.Closure.NSTriadKNEuclideanBishopLerayPythagorasExact as Leray
import DASHI.Physics.Closure.NSTriadKNEuclideanProjectedCellOutputQExact as Projected
import DASHI.Physics.Closure.NSTriadKNEuclideanProjectedInteractionQWeldExact as Weld
import DASHI.Physics.Closure.NSWholeSpaceR3DirectionalSecondMomentQGainExact as Directional
import DASHI.Physics.Closure.NSWholeSpaceR3PhysicalQBudgetCompilerExact as Budget
import DASHI.Physics.Closure.NSWholeSpaceR3CanonicalRadialDataExact as CanonicalRadial
import DASHI.Physics.Closure.NSWholeSpaceR3RadialFactorBudgetExact as RadialBudget

projectedCellEnergy :
  ∀ {S trajectory} →
  Physical.EuclideanProjectedInteraction
    {S} (trajectory : Physical.EuclideanFourierTrajectory S) →
  BishopReal.ℝ
projectedCellEnergy cell =
  Leray.complex3NormSquared
    (Physical.lerayProjectedCell cell)

projectedCellMajorant :
  ∀ {S trajectory} →
  Physical.EuclideanProjectedInteraction
    {S} (trajectory : Physical.EuclideanFourierTrajectory S) →
  BishopReal.ℝ
projectedCellMajorant cell =
  Projected.projectedCellMajorant
    (Physical.uEta cell)
    (Physical.uZeta cell)

record CanonicalProjectedQBudgetInputs
    {S : Canonical.CanonicalNSSemantics}
    {trajectory : Physical.EuclideanFourierTrajectory S}
    (fluid : Heat.PositiveViscosity)
    (point : Heat.PuncturedEuclideanFrequency)
    (cell : Physical.EuclideanProjectedInteraction trajectory)
    (secondMoment : BishopReal.ℝ) : Set where
  constructor canonical-projected-q-budget-inputs
  field
    formulaWeld :
      Weld.ProjectedInteractionFormulaWeld point cell

    directionalSecondMoment :
      Directional.DirectionalSecondMomentSlot
        (Heat.frequency point)
        secondMoment

open CanonicalProjectedQBudgetInputs public

canonicalProjectedInputsToPhysicalQBudget :
  ∀ {S trajectory fluid point cell secondMoment} →
  (inputs :
    CanonicalProjectedQBudgetInputs
      {S} {trajectory}
      fluid point cell secondMoment) →
  Budget.CanonicalPhysicalQBudgetInputs
    fluid
    point
    (projectedCellEnergy cell)
    secondMoment
    (projectedCellMajorant cell)
canonicalProjectedInputsToPhysicalQBudget
    {point = point} {cell = cell} inputs =
  Budget.canonical-physical-q-budget-inputs
    (Leray.complex3NormSquaredNonnegative
      (Physical.lerayProjectedCell cell))
    (BishopP.nonNegx,y⇒nonNegx*y
      (Leray.complex3NormSquaredNonnegative
        (Physical.uEta cell))
      (Leray.complex3NormSquaredNonnegative
        (Physical.uZeta cell)))
    (Weld.physicalProjectedCellOutputQBound
      (formulaWeld inputs))
    (directionalSecondMoment inputs)
canonicalProjectedInputsBuildRadialBudget :
  ∀ {S trajectory fluid point cell secondMoment} →
  (inputs :
    CanonicalProjectedQBudgetInputs
      {S} {trajectory}
      fluid point cell secondMoment) →
  RadialBudget.R3RadialFactorBudget
    (CanonicalRadial.canonicalRadialData fluid point)
    (projectedCellEnergy cell)
    secondMoment
    (projectedCellMajorant cell)
    (Budget.derivativeMajorant
      (Budget.canonicalInputsToPhysicalQBudget
        (canonicalProjectedInputsToPhysicalQBudget inputs)))
canonicalProjectedInputsBuildRadialBudget inputs =
  Budget.canonicalInputsBuildRadialFactorBudget
    (canonicalProjectedInputsToPhysicalQBudget inputs)

projectedQTimesDirectionalQBudgetClosed : Bool
projectedQTimesDirectionalQBudgetClosed = true

projectedGramQHypothesisRequiredAtThisLayer : Bool
projectedGramQHypothesisRequiredAtThisLayer = false

physicalKernelGramScalarSameObjectClosedHere : Bool
physicalKernelGramScalarSameObjectClosedHere = false

physicalSignedSecondMomentSlotWeldClosedHere : Bool
physicalSignedSecondMomentSlotWeldClosedHere = false

clayPromotion : Bool
clayPromotion = false

projectedQTimesDirectionalQBudgetClosedIsTrue :
  projectedQTimesDirectionalQBudgetClosed ≡ true
projectedQTimesDirectionalQBudgetClosedIsTrue = refl

projectedGramQHypothesisRequiredAtThisLayerIsFalse :
  projectedGramQHypothesisRequiredAtThisLayer ≡ false
projectedGramQHypothesisRequiredAtThisLayerIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
