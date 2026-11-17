module DASHI.Physics.Closure.NSTriadKNEuclideanProjectedInteractionQWeldExact where

------------------------------------------------------------------------
-- A / SAME-OBJECT WELD FOR THE PHYSICAL PROJECTED INTERACTION
--
-- The EuclideanProjectedInteraction record deliberately kept the concrete
-- Fourier/Leray formula behind meaning fields.  The analytic q-bound now owns
-- an explicit formula, so the remaining representation task is just to identify
-- the selected physical raw/projected cells with those formulas.
--
-- Once those two equalities are supplied, the projected-cell |xi|^2 majorant
-- follows automatically from the already-proved divergence-form Cauchy bound
-- and canonical Leray contraction.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl; sym; subst)

import Real as BishopReal

import DASHI.Physics.Closure.NSCanonicalEuclideanPeriodicSemanticCarriersExact as Canonical
import DASHI.Physics.Closure.NSTriadKNEuclideanSignedFrequencyCarrierRealizationExact as Euclidean
import DASHI.Physics.Closure.NSTriadKNEuclideanPhysicalFourierNSExact as Physical
import DASHI.Physics.Closure.NSTriadKNEuclideanDivergenceFormOutputFactorExact as Output
import DASHI.Physics.Closure.NSTriadKNEuclideanViscousHeatRateExact as Heat
import DASHI.Physics.Closure.NSTriadKNEuclideanBishopLerayPythagorasExact as Leray
import DASHI.Physics.Closure.NSTriadKNEuclideanCanonicalLerayProjectionExact as CanonicalLeray
import DASHI.Physics.Closure.NSTriadKNEuclideanProjectedCellOutputQExact as Projected

record ProjectedInteractionFormulaWeld
    {S : Canonical.CanonicalNSSemantics}
    {trajectory : Physical.EuclideanFourierTrajectory S}
    (point : Heat.PuncturedEuclideanFrequency)
    (cell : Physical.EuclideanProjectedInteraction trajectory) : Set where
  constructor projected-interaction-formula-weld
  field
    outputIsPointFrequency :
      Euclidean.xi (Physical.interaction cell)
      ≡ Heat.frequency point

    rawCellIsDivergenceForm :
      Physical.rawConvolutionCell cell
      ≡
      Output.divergenceFormRawCell
        (Heat.frequency point)
        (Physical.uEta cell)
        (Physical.uZeta cell)

    projectedCellIsCanonicalLeray :
      Physical.lerayProjectedCell cell
      ≡
      Leray.lerayProject
        (Heat.frequency point)
        (CanonicalLeray.canonicalLerayInverse point)
        (Output.divergenceFormRawCell
          (Heat.frequency point)
          (Physical.uEta cell)
          (Physical.uZeta cell))

open ProjectedInteractionFormulaWeld public

physicalProjectedCellOutputQBound :
  ∀ {S trajectory point cell} →
  (weld :
    ProjectedInteractionFormulaWeld
      {S} {trajectory} point cell) →
  BishopReal._≤_
    (Leray.complex3NormSquared
      (Physical.lerayProjectedCell cell))
    (BishopReal._*_
      (Heat.frequencyNormSquared (Heat.frequency point))
      (Projected.projectedCellMajorant
        (Physical.uEta cell)
        (Physical.uZeta cell)))
physicalProjectedCellOutputQBound {point = point} {cell = cell} weld =
  subst
    (λ projected →
      BishopReal._≤_
        (Leray.complex3NormSquared projected)
        (BishopReal._*_
          (Heat.frequencyNormSquared (Heat.frequency point))
          (Projected.projectedCellMajorant
            (Physical.uEta cell)
            (Physical.uZeta cell))))
    (sym (projectedCellIsCanonicalLeray weld))
    (Projected.projectedCellOutputQBound
      (Heat.frequency point)
      (CanonicalLeray.canonicalLerayInverse point)
      (Physical.uEta cell)
      (Physical.uZeta cell))

projectedInteractionQWeldCompilerClosed : Bool
projectedInteractionQWeldCompilerClosed = true

projectedInteractionFormulaSameObjectClosedHere : Bool
projectedInteractionFormulaSameObjectClosedHere = false

projectedCellQEstimateNeedsNewInequality : Bool
projectedCellQEstimateNeedsNewInequality = false

clayPromotion : Bool
clayPromotion = false

projectedInteractionQWeldCompilerClosedIsTrue :
  projectedInteractionQWeldCompilerClosed ≡ true
projectedInteractionQWeldCompilerClosedIsTrue = refl

projectedCellQEstimateNeedsNewInequalityIsFalse :
  projectedCellQEstimateNeedsNewInequality ≡ false
projectedCellQEstimateNeedsNewInequalityIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
