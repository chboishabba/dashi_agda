{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650RateKernelCrossGradientVectorRound683Exact where

------------------------------------------------------------------------
-- ROUND683 / R681 CROSS-GRADIENT SCALAR -> ONE SIGNED VECTOR CONVOLUTION
--
-- R681 leaves
--
--   sum_tau (p_tau.q_tau) W(M,A_tau).
--
-- By exact Hermitian linearity this is one coherent work:
--
--   W(M, sum_tau (p_tau.q_tau) A_tau).
--
-- Hence the literal physical rate-weighted work is
--
--   nu |k|^2 W(M,M)
--     - 2 nu W(M, CrossGradientVector).
--
-- This is the preferred object for the next physical step: helicity,
-- transversality, Leray, and derivative placement act naturally on the vector
-- convolution before any absolute value.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _-_; _*_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

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
import DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredMultiplierVectorCovarianceExact as Vector
import DASHI.Physics.Closure.NSTriadKNFixedOutputCrossGradientCovarianceExact as Cross
import DASHI.Physics.Closure.NSTriadKNR650RateKernelCrossGradientNormalFormRound681Exact as R681

F : C3.RealField _
F = Rational.rationalRealField

crossGradientVector :
  (E : C3.IntegerEmbedding F) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  Nat → Z3.FourierMode → C3.Complex3 F
crossGradientVector E value cutoff output =
  Vector.weightedVectorSum
    (R681.crossMultiplier E)
    value
    (Output.physicalOutputFiber cutoff output)

crossGradientWorkIsVectorWork :
  (E : C3.IntegerEmbedding F) →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) →
  (output : Z3.FourierMode) →
  let
    items = Output.physicalOutputFiber cutoff output
    value = D1a.mixedProductCell S velocity
    mixed = R224.foldVector value items
    work = Pair.cellWork mixed value
  in
  Pair.weightedWorkSum (R681.crossMultiplier E) work items
  ≡ Work.coherentWork mixed
      (crossGradientVector E value cutoff output)
crossGradientWorkIsVectorWork E S velocity cutoff output =
  let
    items = Output.physicalOutputFiber cutoff output
    value = D1a.mixedProductCell S velocity
    mixed = R224.foldVector value items
  in
  sym
    (Vector.weightedVectorWorkMeaning
      mixed (R681.crossMultiplier E) value items)

fixedOutputPhysicalRateKernelVectorNormalForm :
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
    rate = Pair.cellRate
      (DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalRateDifferenceExact.physicalModalRate
        physicalSystem)
  in
  Pair.weightedWorkSum rate work items
  ≡
  nu * C3.normSquared I output * Work.coherentWork mixed mixed
    - (Cross.two * nu) *
        Work.coherentWork mixed
          (crossGradientVector E value cutoff output)
fixedOutputPhysicalRateKernelVectorNormalForm physicalSystem S output =
  let
    system = Field30.finiteSystem physicalSystem
    cutoff = Audit.cutoff system
    E = Field30.physicalEmbedding physicalSystem
    velocity = Audit.velocityAt system
    items = Output.physicalOutputFiber cutoff output
    value = D1a.mixedProductCell S velocity
    mixed = R224.foldVector value items
    scalar =
      Pair.weightedWorkSum (R681.crossMultiplier E)
        (Pair.cellWork mixed value) items
    vectorWork =
      Work.coherentWork mixed
        (crossGradientVector E value cutoff output)

    base =
      R681.physicalSystemRateWeightedWorkCrossGradientNormalForm
        physicalSystem S output

    weld : scalar ≡ vectorWork
    weld = crossGradientWorkIsVectorWork E S velocity cutoff output
  in
  trans base
    (cong
      (λ selected →
        Field30.viscosity physicalSystem
          * C3.normSquared (Field30.physicalInverseSquare physicalSystem) output
          * Work.coherentWork mixed mixed
          - (Cross.two * Field30.viscosity physicalSystem) * selected)
      weld)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round683CrossGradientScalarCollapsedToOneVectorWork : Bool
round683CrossGradientScalarCollapsedToOneVectorWork = true

round683PhysicalRateKernelVectorNormalFormClosed : Bool
round683PhysicalRateKernelVectorNormalFormClosed = true

round683VectorNormalFormUsesAbsoluteValue : Bool
round683VectorNormalFormUsesAbsoluteValue = false

round683VectorNormalFormAddsCardinalityFactor : Bool
round683VectorNormalFormAddsCardinalityFactor = false

round683HelicalCrossGradientPaymentClosed : Bool
round683HelicalCrossGradientPaymentClosed = false

round683IntroducesEstimate : Bool
round683IntroducesEstimate = false

round683IntroducesNewClayLeaf : Bool
round683IntroducesNewClayLeaf = false

round683C2Closed : Bool
round683C2Closed = false

round683ClayPromotion : Bool
round683ClayPromotion = false

round683CrossGradientScalarCollapsedToOneVectorWorkIsTrue :
  round683CrossGradientScalarCollapsedToOneVectorWork ≡ true
round683CrossGradientScalarCollapsedToOneVectorWorkIsTrue = refl

round683PhysicalRateKernelVectorNormalFormClosedIsTrue :
  round683PhysicalRateKernelVectorNormalFormClosed ≡ true
round683PhysicalRateKernelVectorNormalFormClosedIsTrue = refl

round683VectorNormalFormUsesAbsoluteValueIsFalse :
  round683VectorNormalFormUsesAbsoluteValue ≡ false
round683VectorNormalFormUsesAbsoluteValueIsFalse = refl

round683VectorNormalFormAddsCardinalityFactorIsFalse :
  round683VectorNormalFormAddsCardinalityFactor ≡ false
round683VectorNormalFormAddsCardinalityFactorIsFalse = refl

round683HelicalCrossGradientPaymentClosedIsFalse :
  round683HelicalCrossGradientPaymentClosed ≡ false
round683HelicalCrossGradientPaymentClosedIsFalse = refl

round683IntroducesEstimateIsFalse :
  round683IntroducesEstimate ≡ false
round683IntroducesEstimateIsFalse = refl

round683IntroducesNewClayLeafIsFalse :
  round683IntroducesNewClayLeaf ≡ false
round683IntroducesNewClayLeafIsFalse = refl

round683C2ClosedIsFalse :
  round683C2Closed ≡ false
round683C2ClosedIsFalse = refl

round683ClayPromotionIsFalse :
  round683ClayPromotion ≡ false
round683ClayPromotionIsFalse = refl
