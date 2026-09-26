{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650RateKernelCrossGradientNormalFormRound681Exact where

------------------------------------------------------------------------
-- ROUND681 / LITERAL PHYSICAL RATE-WEIGHTED WORK -> OUTPUT-HEAT SELF WORK
--            MINUS CROSS-GRADIENT WORK
--
-- R680 rules out treating the physical cell rates as arbitrary positive
-- weights.  On one literal fixed-output fibre they are not arbitrary:
--
--   r_tau = nu (|p_tau|^2 + |q_tau|^2)
--         = (nu/2)|k|^2 + (nu/2)|p_tau-q_tau|^2.
--
-- Resonance p+q=k also gives
--
--   |p_tau-q_tau|^2 = |k|^2 - 4 (p_tau . q_tau).
--
-- Summing against the exact coherent cell work w_tau = W(M,A_tau) yields
--
--   sum_tau r_tau w_tau
--     = nu |k|^2 W(M,M)
--       - 2 nu sum_tau (p_tau.q_tau) w_tau.
--
-- This uses literal triad/frequency geometry unavailable in R680's arbitrary
-- positive-rate witness.  The only sign-indefinite coordinate is now an
-- actual cross-gradient correlation on the physical output fibre.
--
-- No estimate, pair-count factor, fibre mean, absolute value, or new Clay leaf
-- is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedCommutatorDampedTangentExact as D1a
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair
import DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredCovarianceFactorExact as Centered
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalRateDifferenceExact as PhysicalRate
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalOutputRateNormalFormExact as RateNormal
import DASHI.Physics.Closure.NSTriadKNFixedOutputCrossGradientCovarianceExact as Cross
import DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredMultiplierVectorCovarianceExact as Vector

F : C3.RealField _
F = Rational.rationalRealField

crossMultiplier :
  C3.IntegerEmbedding F →
  Physical.PhysicalTriadIncidence → ℚ
crossMultiplier E tau =
  Cross.crossDot E (Physical.p tau) (Physical.q tau)

centeredWeightedWorkIsOutputMinusFourCross :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (work : Physical.PhysicalTriadIncidence → ℚ) →
  {output : Z3.FourierMode} →
  (items : List Physical.PhysicalTriadIncidence) →
  Centered.OutputHomogeneous output items →
  Pair.weightedWorkSum
    (Vector.centeredFrequencyMultiplier E) work items
  ≡
  C3.normSquared I output * Pair.workSum work items
    - Cross.four *
        Pair.weightedWorkSum (crossMultiplier E) work items
centeredWeightedWorkIsOutputMinusFourCross E I work [] homogeneous =
  solve []
centeredWeightedWorkIsOutputMinusFourCross
    E I work {output} (tau ∷ rest) homogeneous =
  let
    headOutput : Physical.k tau ≡ output
    headOutput = Centered.headOutput homogeneous

    headCentered :
      Vector.centeredFrequencyMultiplier E tau
      ≡ C3.normSquared I output
        - Cross.four * crossMultiplier E tau
    headCentered =
      trans
        (Cross.incidenceCenteredSquareIsOutputMinusFourCross E I tau)
        (cong
          (λ square → square - Cross.four * crossMultiplier E tau)
          (cong (C3.normSquared I) headOutput))

    tail =
      centeredWeightedWorkIsOutputMinusFourCross
        E I work rest (Centered.tailHomogeneous homogeneous)
  in
  trans
    (cong
      (λ multiplier →
        multiplier * work tau
          + Pair.weightedWorkSum
              (Vector.centeredFrequencyMultiplier E) work rest)
      headCentered)
    (trans
      (cong
        ((C3.normSquared I output
            - Cross.four * crossMultiplier E tau) * work tau +_)
        tail)
      (solve
        ( C3.normSquared I output
        ∷ Cross.four
        ∷ crossMultiplier E tau
        ∷ work tau
        ∷ Pair.workSum work rest
        ∷ Pair.weightedWorkSum (crossMultiplier E) work rest
        ∷ [])))

fixedOutputPhysicalRateWeightedWorkCrossGradientNormalForm :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (nu : ℚ) →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) →
  (output : Z3.FourierMode) →
  let
    items = Output.physicalOutputFiber cutoff output
    value = D1a.mixedProductCell S velocity
    mixed = R224.foldVector value items
    work = Pair.cellWork mixed value
    rate = Pair.cellRate (Centered.modalViscousRate nu I)
    cross = crossMultiplier E
  in
  Pair.weightedWorkSum rate work items
  ≡
  nu * C3.normSquared I output * Work.coherentWork mixed mixed
    - (Cross.two * nu) *
        Pair.weightedWorkSum cross work items
fixedOutputPhysicalRateWeightedWorkCrossGradientNormalForm
    E I nu S velocity cutoff output =
  let
    items = Output.physicalOutputFiber cutoff output
    value = D1a.mixedProductCell S velocity
    mixed = R224.foldVector value items
    work = Pair.cellWork mixed value
    centered = Vector.centeredFrequencyMultiplier E
    cross = crossMultiplier E
    outputSquare = C3.normSquared I output
    halfNu = RateNormal.halfViscosity nu

    rateSplit :
      Pair.weightedWorkSum
        (Pair.cellRate (Centered.modalViscousRate nu I)) work items
      ≡
      RateNormal.outputHeatRate nu I output * Pair.workSum work items
        + halfNu * Pair.weightedWorkSum centered work items
    rateSplit =
      RateNormal.literalWeightedRateWorkSplit
        E I nu work cutoff output

    centeredSplit :
      Pair.weightedWorkSum centered work items
      ≡
      outputSquare * Pair.workSum work items
        - Cross.four * Pair.weightedWorkSum cross work items
    centeredSplit =
      centeredWeightedWorkIsOutputMinusFourCross
        E I work items (Centered.literalOutputFibreHomogeneous cutoff output)

    workMeaning :
      Pair.workSum work items ≡ Work.coherentWork mixed mixed
    workMeaning =
      Pair.workSumAgainstFold mixed value items
  in
  trans rateSplit
    (trans
      (cong₂ _+_
        (cong
          (RateNormal.outputHeatRate nu I output *_)
          workMeaning)
        (cong
          (halfNu *_)
          centeredSplit))
      (solve
        ( nu
        ∷ RateNormal.half
        ∷ outputSquare
        ∷ Work.coherentWork mixed mixed
        ∷ Cross.two
        ∷ Cross.four
        ∷ Pair.weightedWorkSum cross work items
        ∷ [])))

physicalSystemRateWeightedWorkCrossGradientNormalForm :
  (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F) →
  (S : Helical.HelicalModeScalars F) →
  (output : Z3.FourierMode) →
  let
    system = Field30.finiteSystem physicalSystem
    cutoff = Audit.cutoff system
    E = Field30.physicalEmbedding physicalSystem
    I = Field30.physicalInverseSquare physicalSystem
    nu = Field30.viscosity physicalSystem
    velocity = Audit.velocityAt system
    items = Output.physicalOutputFiber cutoff output
    value = D1a.mixedProductCell S velocity
    mixed = R224.foldVector value items
    work = Pair.cellWork mixed value
  in
  Pair.weightedWorkSum
      (PhysicalRate.physicalCellRate physicalSystem) work items
  ≡
  nu * C3.normSquared I output * Work.coherentWork mixed mixed
    - (Cross.two * nu) *
        Pair.weightedWorkSum (crossMultiplier E) work items
physicalSystemRateWeightedWorkCrossGradientNormalForm
    physicalSystem S output =
  fixedOutputPhysicalRateWeightedWorkCrossGradientNormalForm
    (Field30.physicalEmbedding physicalSystem)
    (Field30.physicalInverseSquare physicalSystem)
    (Field30.viscosity physicalSystem)
    S
    (Audit.velocityAt (Field30.finiteSystem physicalSystem))
    (Audit.cutoff (Field30.finiteSystem physicalSystem))
    output

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round681PhysicalRateWeightedWorkCrossGradientNormalFormClosed : Bool
round681PhysicalRateWeightedWorkCrossGradientNormalFormClosed = true

round681UsesArbitraryPositiveRates : Bool
round681UsesArbitraryPositiveRates = false

round681UsesLiteralTriadResonance : Bool
round681UsesLiteralTriadResonance = true

round681UsesFibreMean : Bool
round681UsesFibreMean = false

round681UsesCardinalityTax : Bool
round681UsesCardinalityTax = false

round681IntroducesAbsoluteValue : Bool
round681IntroducesAbsoluteValue = false

round681RemainingLocalCoordinateIsCrossGradientWork : Bool
round681RemainingLocalCoordinateIsCrossGradientWork = true

round681CrossGradientQuantitativePaymentClosed : Bool
round681CrossGradientQuantitativePaymentClosed = false

round681IntroducesNewClayLeaf : Bool
round681IntroducesNewClayLeaf = false

round681C2Closed : Bool
round681C2Closed = false

round681ClayPromotion : Bool
round681ClayPromotion = false

round681PhysicalRateWeightedWorkCrossGradientNormalFormClosedIsTrue :
  round681PhysicalRateWeightedWorkCrossGradientNormalFormClosed ≡ true
round681PhysicalRateWeightedWorkCrossGradientNormalFormClosedIsTrue = refl

round681UsesArbitraryPositiveRatesIsFalse :
  round681UsesArbitraryPositiveRates ≡ false
round681UsesArbitraryPositiveRatesIsFalse = refl

round681UsesLiteralTriadResonanceIsTrue :
  round681UsesLiteralTriadResonance ≡ true
round681UsesLiteralTriadResonanceIsTrue = refl

round681UsesFibreMeanIsFalse :
  round681UsesFibreMean ≡ false
round681UsesFibreMeanIsFalse = refl

round681UsesCardinalityTaxIsFalse :
  round681UsesCardinalityTax ≡ false
round681UsesCardinalityTaxIsFalse = refl

round681IntroducesAbsoluteValueIsFalse :
  round681IntroducesAbsoluteValue ≡ false
round681IntroducesAbsoluteValueIsFalse = refl

round681RemainingLocalCoordinateIsCrossGradientWorkIsTrue :
  round681RemainingLocalCoordinateIsCrossGradientWork ≡ true
round681RemainingLocalCoordinateIsCrossGradientWorkIsTrue = refl

round681CrossGradientQuantitativePaymentClosedIsFalse :
  round681CrossGradientQuantitativePaymentClosed ≡ false
round681CrossGradientQuantitativePaymentClosedIsFalse = refl

round681IntroducesNewClayLeafIsFalse :
  round681IntroducesNewClayLeaf ≡ false
round681IntroducesNewClayLeafIsFalse = refl

round681C2ClosedIsFalse :
  round681C2Closed ≡ false
round681C2ClosedIsFalse = refl

round681ClayPromotionIsFalse :
  round681ClayPromotion ≡ false
round681ClayPromotionIsFalse = refl
