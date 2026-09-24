{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650RateKernelInputLaplacianCollapseRound684Exact where

------------------------------------------------------------------------
-- ROUND684 / THE R683 PHYSICAL RATE KERNEL IS EXACTLY INPUT-LAPLACIAN WORK
--
-- The physical cell rate is not merely geometrically related to the input
-- Laplacian multiplier.  It is literally
--
--   r_tau = nu (|p_tau|^2 + |q_tau|^2).
--
-- Therefore on one complete physical output fibre,
--
--   sum_tau r_tau W(M,A_tau)
--     = nu sum_tau (|p_tau|^2+|q_tau|^2) W(M,A_tau)
--     = nu W(M,L_in),
--
-- where
--
--   L_in = sum_tau (|p_tau|^2+|q_tau|^2) A_tau.
--
-- Combining this with R681/R683 proves that the output-heat/cross-gradient
-- expression collapses exactly to one input-Laplacian vector work:
--
--   nu |k|^2 W(M,M) - 2nu W(M,G_k) = nu W(M,L_in).
--
-- No estimate, absolute value, division, fibre mean, or cutoff factor enters.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

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
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalRateDifferenceExact as PhysicalRate
import DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredInputLaplacianVectorResidualExact as Input
import DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredMultiplierVectorCovarianceExact as Vector
import DASHI.Physics.Closure.NSTriadKNFixedOutputCrossGradientCovarianceExact as Cross
import DASHI.Physics.Closure.NSTriadKNR650RateKernelCrossGradientVectorRound683Exact as R683

F : C3.RealField _
F = Rational.rationalRealField

physicalCellRateIsViscosityInputMass :
  (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F) →
  (tau : Physical.PhysicalTriadIncidence) →
  PhysicalRate.physicalCellRate physicalSystem tau
  ≡
  Field30.viscosity physicalSystem
    * Input.inputMultiplier (Field30.physicalInverseSquare physicalSystem) tau
physicalCellRateIsViscosityInputMass physicalSystem tau =
  let
    nu = Field30.viscosity physicalSystem
    I = Field30.physicalInverseSquare physicalSystem
    p2 = C3.normSquared I (Physical.p tau)
    q2 = C3.normSquared I (Physical.q tau)
  in
  trans
    (PhysicalRate.physicalCellRateIsLiteralViscousRate physicalSystem tau)
    (solve (nu ∷ p2 ∷ q2 ∷ []))

weightedPhysicalRateIsViscosityInputMass :
  (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F) →
  (work : Physical.PhysicalTriadIncidence → ℚ) →
  (items : List Physical.PhysicalTriadIncidence) →
  Pair.weightedWorkSum
    (PhysicalRate.physicalCellRate physicalSystem) work items
  ≡
  Field30.viscosity physicalSystem
    * Pair.weightedWorkSum
        (Input.inputMultiplier (Field30.physicalInverseSquare physicalSystem))
        work items
weightedPhysicalRateIsViscosityInputMass physicalSystem work [] =
  solve (Field30.viscosity physicalSystem ∷ [])
weightedPhysicalRateIsViscosityInputMass physicalSystem work (tau ∷ rest) =
  let
    nu = Field30.viscosity physicalSystem
    input = Input.inputMultiplier (Field30.physicalInverseSquare physicalSystem)
    head =
      physicalCellRateIsViscosityInputMass physicalSystem tau
    tail =
      weightedPhysicalRateIsViscosityInputMass
        physicalSystem work rest
  in
  trans
    (cong₂ _+_
      (cong (_* work tau) head)
      tail)
    (solve
      ( nu
      ∷ input tau
      ∷ work tau
      ∷ Pair.weightedWorkSum input work rest
      ∷ []))

inputLaplacianVector :
  ∀ {E : C3.IntegerEmbedding F} →
  (I : C3.ModeInverseSquare F E) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  Nat → Z3.FourierMode → C3.Complex3 F
inputLaplacianVector I value cutoff output =
  Vector.weightedVectorSum
    (Input.inputMultiplier I)
    value
    (Output.physicalOutputFiber cutoff output)

fixedOutputPhysicalRateKernelIsInputLaplacianWork :
  (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F) →
  (S : Helical.HelicalModeScalars F) →
  (output : Z3.FourierMode) →
  let
    system = Field30.finiteSystem physicalSystem
    cutoff = Audit.cutoff system
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
  nu * Work.coherentWork mixed
    (inputLaplacianVector I value cutoff output)
fixedOutputPhysicalRateKernelIsInputLaplacianWork physicalSystem S output =
  let
    system = Field30.finiteSystem physicalSystem
    cutoff = Audit.cutoff system
    I = Field30.physicalInverseSquare physicalSystem
    velocity = Audit.velocityAt system
    items = Output.physicalOutputFiber cutoff output
    value = D1a.mixedProductCell S velocity
    mixed = R224.foldVector value items
    work = Pair.cellWork mixed value
    input = Input.inputMultiplier I
    weightedScalar = Pair.weightedWorkSum input work items
    weightedVector = inputLaplacianVector I value cutoff output

    rateCollapse :
      Pair.weightedWorkSum
        (PhysicalRate.physicalCellRate physicalSystem) work items
      ≡ Field30.viscosity physicalSystem * weightedScalar
    rateCollapse =
      weightedPhysicalRateIsViscosityInputMass physicalSystem work items

    vectorMeaning :
      Work.coherentWork mixed weightedVector ≡ weightedScalar
    vectorMeaning =
      Vector.weightedVectorWorkMeaning mixed input value items
  in
  trans rateCollapse
    (cong (Field30.viscosity physicalSystem *_) (sym vectorMeaning))

r683OutputHeatCrossGradientIsInputLaplacianWork :
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
  in
  nu * C3.normSquared I output * Work.coherentWork mixed mixed
    - (Cross.two * nu)
        * Work.coherentWork mixed
            (R683.crossGradientVector E value cutoff output)
  ≡
  nu * Work.coherentWork mixed
      (inputLaplacianVector I value cutoff output)
r683OutputHeatCrossGradientIsInputLaplacianWork physicalSystem S output =
  trans
    (sym (R683.fixedOutputPhysicalRateKernelVectorNormalForm
      physicalSystem S output))
    (fixedOutputPhysicalRateKernelIsInputLaplacianWork
      physicalSystem S output)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round684PhysicalRateKernelIsInputLaplacianWork : Bool
round684PhysicalRateKernelIsInputLaplacianWork = true

round684R683CrossGradientExpressionCollapsesToInputLaplacian : Bool
round684R683CrossGradientExpressionCollapsesToInputLaplacian = true

round684IntroducesEstimate : Bool
round684IntroducesEstimate = false

round684InputLaplacianQuantitativePaymentClosed : Bool
round684InputLaplacianQuantitativePaymentClosed = false

round684IntroducesNewClayLeaf : Bool
round684IntroducesNewClayLeaf = false

round684C2Closed : Bool
round684C2Closed = false

round684ClayPromotion : Bool
round684ClayPromotion = false

round684PhysicalRateKernelIsInputLaplacianWorkIsTrue :
  round684PhysicalRateKernelIsInputLaplacianWork ≡ true
round684PhysicalRateKernelIsInputLaplacianWorkIsTrue = refl

round684R683CrossGradientExpressionCollapsesToInputLaplacianIsTrue :
  round684R683CrossGradientExpressionCollapsesToInputLaplacian ≡ true
round684R683CrossGradientExpressionCollapsesToInputLaplacianIsTrue = refl

round684IntroducesEstimateIsFalse :
  round684IntroducesEstimate ≡ false
round684IntroducesEstimateIsFalse = refl

round684InputLaplacianQuantitativePaymentClosedIsFalse :
  round684InputLaplacianQuantitativePaymentClosed ≡ false
round684InputLaplacianQuantitativePaymentClosedIsFalse = refl

round684IntroducesNewClayLeafIsFalse :
  round684IntroducesNewClayLeaf ≡ false
round684IntroducesNewClayLeafIsFalse = refl

round684C2ClosedIsFalse :
  round684C2Closed ≡ false
round684C2ClosedIsFalse = refl

round684ClayPromotionIsFalse :
  round684ClayPromotion ≡ false
round684ClayPromotionIsFalse = refl
