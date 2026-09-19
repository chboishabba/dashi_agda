module DASHI.Physics.Closure.NSWholeSpaceR3PhysicalQBudgetCompilerExact where

------------------------------------------------------------------------
-- A / PHYSICAL q-BUDGET COMPILER
--
-- Combine the two legitimate low-output factors:
--
--   Gram <= |xi|^2 G                         (physical projected-Gram input)
--   secondMoment <= |xi|^2 |Dg|^2            (derived by R^3 Cauchy)
--
-- with the radial data q = |xi|^2.
--
-- The second line is NOT accepted as an inequality input: it is produced by
-- NSWholeSpaceR3DirectionalSecondMomentQGainExact once the selected physical
-- second-moment scalar is identified with a directional derivative square.
--
-- This constructs the exact R3RadialFactorBudget consumed by the radial
-- inverse-cube and Lebesgue compilers.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopSquareNonnegativeExact as SquareNN
import DASHI.Physics.Closure.NSTriadKNEuclideanSignedFrequencyCarrierRealizationExact as Euclidean
import DASHI.Physics.Closure.NSTriadKNEuclideanViscousHeatRateExact as Heat
import DASHI.Physics.Closure.NSWholeSpaceR3RadialOriginCancellationExact as Radial
import DASHI.Physics.Closure.NSWholeSpaceR3RadialFactorBudgetExact as Budget
import DASHI.Physics.Closure.NSWholeSpaceR3DirectionalSecondMomentQGainExact as Directional
import DASHI.Physics.Closure.NSWholeSpaceR3CanonicalRadialDataExact as CanonicalRadial

record PhysicalQBudgetInputs
    (dataSet : Radial.PositiveViscosityRadiusSquare)
    (output : Euclidean.R3Frequency)
    (gramFactor secondMoment gramMajorant : BishopReal.ℝ) : Set where
  constructor physical-q-budget-inputs
  field
    radialQIsOutputNormSquared :
      BishopReal._≃_
        (Radial.radiusSquared dataSet)
        (Heat.frequencyNormSquared output)

    gramFactorNonnegative :
      BishopReal.NonNegative gramFactor

    gramMajorantNonnegative :
      BishopReal.NonNegative gramMajorant

    gramCarriesOutputQ :
      BishopReal._≤_
        gramFactor
        (BishopReal._*_
          (Heat.frequencyNormSquared output)
          gramMajorant)

    directionalSecondMoment :
      Directional.DirectionalSecondMomentSlot
        output secondMoment

open PhysicalQBudgetInputs public

derivativeMajorant :
  ∀ {dataSet output gramFactor secondMoment gramMajorant} →
  PhysicalQBudgetInputs
    dataSet output gramFactor secondMoment gramMajorant →
  BishopReal.ℝ
derivativeMajorant inputs =
  Heat.frequencyNormSquared
    (Directional.derivativeVector
      (directionalSecondMoment inputs))

derivativeMajorantNonnegative :
  ∀ {dataSet output gramFactor secondMoment gramMajorant} →
  (inputs :
    PhysicalQBudgetInputs
      dataSet output gramFactor secondMoment gramMajorant) →
  BishopReal.NonNegative (derivativeMajorant inputs)
derivativeMajorantNonnegative inputs =
  BishopP.nonNegx,y⇒nonNegx+y
    (SquareNN.bishopSquareNonnegative
      (Euclidean.x
        (Directional.derivativeVector
          (directionalSecondMoment inputs))))
    (BishopP.nonNegx,y⇒nonNegx+y
      (SquareNN.bishopSquareNonnegative
        (Euclidean.y
          (Directional.derivativeVector
            (directionalSecondMoment inputs))))
      (SquareNN.bishopSquareNonnegative
        (Euclidean.z
          (Directional.derivativeVector
            (directionalSecondMoment inputs)))))

secondMomentNonnegative :
  ∀ {dataSet output gramFactor secondMoment gramMajorant} →
  (inputs :
    PhysicalQBudgetInputs
      dataSet output gramFactor secondMoment gramMajorant) →
  BishopReal.NonNegative secondMoment
secondMomentNonnegative {output = output} inputs =
  BishopP.0≤x⇒nonNegx
    (BishopP.≤-respˡ-≃
      (Directional.secondMomentIsDirectionalSquare
        (directionalSecondMoment inputs))
      (BishopP.nonNegx⇒0≤x
        (SquareNN.bishopSquareNonnegative
          (Directional.dot
            output
            (Directional.derivativeVector
              (directionalSecondMoment inputs))))))

gramCarriesRadialQ :
  ∀ {dataSet output gramFactor secondMoment gramMajorant} →
  (inputs :
    PhysicalQBudgetInputs
      dataSet output gramFactor secondMoment gramMajorant) →
  BishopReal._≤_
    gramFactor
    (BishopReal._*_
      (Radial.radiusSquared dataSet)
      gramMajorant)
gramCarriesRadialQ inputs =
  BishopP.≤-respʳ-≃
    (BishopP.*-congʳ
      (BishopP.≃-symm
        (radialQIsOutputNormSquared inputs)))
    (gramCarriesOutputQ inputs)

secondMomentCarriesRadialQ :
  ∀ {dataSet output gramFactor secondMoment gramMajorant} →
  (inputs :
    PhysicalQBudgetInputs
      dataSet output gramFactor secondMoment gramMajorant) →
  BishopReal._≤_
    secondMoment
    (BishopReal._*_
      (Radial.radiusSquared dataSet)
      (derivativeMajorant inputs))
secondMomentCarriesRadialQ inputs =
  BishopP.≤-respʳ-≃
    (BishopP.*-congʳ
      (BishopP.≃-symm
        (radialQIsOutputNormSquared inputs)))
    (Directional.directionalSlotCarriesOutputQ
      (directionalSecondMoment inputs))

physicalInputsBuildRadialFactorBudget :
  ∀ {dataSet output gramFactor secondMoment gramMajorant} →
  (inputs :
    PhysicalQBudgetInputs
      dataSet output gramFactor secondMoment gramMajorant) →
  Budget.R3RadialFactorBudget
    dataSet
    gramFactor
    secondMoment
    gramMajorant
    (derivativeMajorant inputs)
physicalInputsBuildRadialFactorBudget inputs =
  Budget.r3-radial-factor-budget
    (gramFactorNonnegative inputs)
    (secondMomentNonnegative inputs)
    (gramMajorantNonnegative inputs)
    (derivativeMajorantNonnegative inputs)
    (gramCarriesRadialQ inputs)
    (secondMomentCarriesRadialQ inputs)

------------------------------------------------------------------------
-- Canonical constructor: q = |xi|^2 is now definitional.
------------------------------------------------------------------------

record CanonicalPhysicalQBudgetInputs
    (fluid : Heat.PositiveViscosity)
    (point : Heat.PuncturedEuclideanFrequency)
    (gramFactor secondMoment gramMajorant : BishopReal.ℝ) : Set where
  constructor canonical-physical-q-budget-inputs
  field
    gramFactorNonnegativeCanonical :
      BishopReal.NonNegative gramFactor

    gramMajorantNonnegativeCanonical :
      BishopReal.NonNegative gramMajorant

    gramCarriesOutputQCanonical :
      BishopReal._≤_
        gramFactor
        (BishopReal._*_
          (Heat.frequencyNormSquared (Heat.frequency point))
          gramMajorant)

    directionalSecondMomentCanonical :
      Directional.DirectionalSecondMomentSlot
        (Heat.frequency point)
        secondMoment

open CanonicalPhysicalQBudgetInputs public

canonicalInputsToPhysicalQBudget :
  ∀ {fluid point gramFactor secondMoment gramMajorant} →
  CanonicalPhysicalQBudgetInputs
    fluid point gramFactor secondMoment gramMajorant →
  PhysicalQBudgetInputs
    (CanonicalRadial.canonicalRadialData fluid point)
    (Heat.frequency point)
    gramFactor secondMoment gramMajorant
canonicalInputsToPhysicalQBudget inputs =
  physical-q-budget-inputs
    (CanonicalRadial.canonicalRadialQEquivalent _ _)
    (gramFactorNonnegativeCanonical inputs)
    (gramMajorantNonnegativeCanonical inputs)
    (gramCarriesOutputQCanonical inputs)
    (directionalSecondMomentCanonical inputs)

canonicalInputsBuildRadialFactorBudget :
  ∀ {fluid point gramFactor secondMoment gramMajorant} →
  (inputs :
    CanonicalPhysicalQBudgetInputs
      fluid point gramFactor secondMoment gramMajorant) →
  Budget.R3RadialFactorBudget
    (CanonicalRadial.canonicalRadialData fluid point)
    gramFactor
    secondMoment
    gramMajorant
    (derivativeMajorant (canonicalInputsToPhysicalQBudget inputs))
canonicalInputsBuildRadialFactorBudget inputs =
  physicalInputsBuildRadialFactorBudget
    (canonicalInputsToPhysicalQBudget inputs)

------------------------------------------------------------------------
-- Exact remaining physical boundary:
--
--  1. identify q in radial coordinates with |xi|^2 (representation);
--  2. prove the projected physical Gram <= |xi|^2 G;
--  3. identify the selected signed state-variation square with an output
--     directional derivative square.
--
-- After those three same-object/analytic inputs, the low-frequency q-budget,
-- inverse-cube payment, and radial Lebesgue domination are already compiled.
------------------------------------------------------------------------

directionalQGainDerivedNotAssumed : Bool
directionalQGainDerivedNotAssumed = true

physicalRadialFactorBudgetCompilerClosed : Bool
physicalRadialFactorBudgetCompilerClosed = true

projectedGramOutputQClosedHere : Bool
projectedGramOutputQClosedHere = false

physicalDerivativeSlotWeldClosedHere : Bool
physicalDerivativeSlotWeldClosedHere = false

radialCoordinateSameObjectClosedHere : Bool
radialCoordinateSameObjectClosedHere = true

clayPromotion : Bool
clayPromotion = false

directionalQGainDerivedNotAssumedIsTrue :
  directionalQGainDerivedNotAssumed ≡ true
directionalQGainDerivedNotAssumedIsTrue = refl

physicalRadialFactorBudgetCompilerClosedIsTrue :
  physicalRadialFactorBudgetCompilerClosed ≡ true
physicalRadialFactorBudgetCompilerClosedIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
