{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650RateKernelCommutatorEndpointRound685Exact where

------------------------------------------------------------------------
-- ROUND685 / THE PHYSICAL RATE KERNEL = COMMUTATOR WORK - TANGENT WORK
--
-- For one literal fixed-output fibre:
--
--   tangent = decay + commutator,
--
-- and the physical variable-decay work is exactly
--
--   W(M,decay) = - sum_tau r_tau W(M,A_tau).
--
-- Therefore the R665/R684 kernel satisfies
--
--   sum_tau r_tau W(M,A_tau)
--     = W(M,commutator) - W(M,tangent).
--
-- After time integration the tangent term is an endpoint self-energy
-- difference, so C2's local kernel is on the SAME forcing/commutator currency
-- that feeds the global R568 lane, modulo an exact endpoint term.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinWaleffeAmplitudeTangentRound94Exact as R94
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedCommutatorDampedTangentExact as D1a
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalRateDifferenceExact as PhysicalRate
import DASHI.Physics.Closure.NSTriadKNR650RateKernelInputLaplacianCollapseRound684Exact as R684

F : C3.RealField _
F = Rational.rationalRealField

fixedOutputPhysicalRateKernelIsCommutatorMinusTangent :
  (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F) →
  (S : Helical.HelicalModeScalars F) →
  (output : Z3.FourierMode) →
  let
    system = Field30.finiteSystem physicalSystem
    cutoff = Audit.cutoff system
    velocity = Audit.velocityAt system
    forcing = Audit.projectedNonlinearity system
    rho = R94.physicalDecayRate physicalSystem
    items = Output.physicalOutputFiber cutoff output
    value = D1a.mixedProductCell S velocity
    mixed = R224.foldVector value items
    work = Pair.cellWork mixed value
    weighted =
      Pair.weightedWorkSum
        (PhysicalRate.physicalCellRate physicalSystem) work items
    tangent =
      Work.fixedOutputDampedTangent rho S velocity forcing cutoff output
    commutator =
      Work.fixedOutputCommutator S velocity forcing cutoff output
  in
  weighted
  ≡ Work.coherentWork mixed commutator
      - Work.coherentWork mixed tangent
fixedOutputPhysicalRateKernelIsCommutatorMinusTangent
    physicalSystem S output =
  let
    system = Field30.finiteSystem physicalSystem
    cutoff = Audit.cutoff system
    velocity = Audit.velocityAt system
    forcing = Audit.projectedNonlinearity system
    rho = R94.physicalDecayRate physicalSystem
    items = Output.physicalOutputFiber cutoff output
    value = D1a.mixedProductCell S velocity
    mixed = R224.foldVector value items
    work = Pair.cellWork mixed value
    weighted =
      Pair.weightedWorkSum
        (PhysicalRate.physicalCellRate physicalSystem) work items
    decay =
      Work.fixedOutputVariableDecay rho S velocity cutoff output
    tangent =
      Work.fixedOutputDampedTangent rho S velocity forcing cutoff output
    commutator =
      Work.fixedOutputCommutator S velocity forcing cutoff output

    decayMeaning :
      Work.coherentWork mixed decay ≡ 0ℚ - weighted
    decayMeaning =
      Pair.variableDecayWorkSum mixed rho S velocity items

    commutatorMeaning :
      Work.coherentWork mixed commutator
      ≡ Work.coherentWork mixed tangent - Work.coherentWork mixed decay
    commutatorMeaning =
      Work.fixedOutputCommutatorWorkIsTangentMinusDecay
        rho S velocity forcing cutoff output
    weightedIsNegativeDecay :
      weighted ≡ 0ℚ - Work.coherentWork mixed decay
    weightedIsNegativeDecay
      rewrite decayMeaning =
      solve (weighted ∷ [])

    commutatorMinusTangentIsNegativeDecay :
      Work.coherentWork mixed commutator
        - Work.coherentWork mixed tangent
      ≡ 0ℚ - Work.coherentWork mixed decay
    commutatorMinusTangentIsNegativeDecay
      rewrite commutatorMeaning =
      solve
        ( Work.coherentWork mixed tangent
        ∷ Work.coherentWork mixed decay
        ∷ [])
  in
  trans weightedIsNegativeDecay
    (sym commutatorMinusTangentIsNegativeDecay)

------------------------------------------------------------------------
-- R684 and R685 are the SAME kernel, now in two physical coordinates.
------------------------------------------------------------------------

inputLaplacianWorkIsCommutatorMinusTangent :
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
    forcing = Audit.projectedNonlinearity system
    rho = R94.physicalDecayRate physicalSystem
  in
  nu * Work.coherentWork mixed
      (R684.inputLaplacianVector I value cutoff output)
  ≡
  Work.coherentWork mixed
      (Work.fixedOutputCommutator S velocity forcing cutoff output)
    -
  Work.coherentWork mixed
      (Work.fixedOutputDampedTangent rho S velocity forcing cutoff output)
inputLaplacianWorkIsCommutatorMinusTangent physicalSystem S output =
  trans
    (sym (R684.fixedOutputPhysicalRateKernelIsInputLaplacianWork
      physicalSystem S output))
    (fixedOutputPhysicalRateKernelIsCommutatorMinusTangent
      physicalSystem S output)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round685RateKernelIsCommutatorMinusTangent : Bool
round685RateKernelIsCommutatorMinusTangent = true

round685InputLaplacianWorkIsCommutatorMinusTangent : Bool
round685InputLaplacianWorkIsCommutatorMinusTangent = true

round685C2NowOnForcingCommutatorCurrencyModuloEndpoint : Bool
round685C2NowOnForcingCommutatorCurrencyModuloEndpoint = true

round685IntroducesEstimate : Bool
round685IntroducesEstimate = false

round685CommutatorSpacetimePaymentClosed : Bool
round685CommutatorSpacetimePaymentClosed = false

round685C2Closed : Bool
round685C2Closed = false

round685IntroducesNewClayLeaf : Bool
round685IntroducesNewClayLeaf = false

round685ClayPromotion : Bool
round685ClayPromotion = false

round685RateKernelIsCommutatorMinusTangentIsTrue :
  round685RateKernelIsCommutatorMinusTangent ≡ true
round685RateKernelIsCommutatorMinusTangentIsTrue = refl

round685InputLaplacianWorkIsCommutatorMinusTangentIsTrue :
  round685InputLaplacianWorkIsCommutatorMinusTangent ≡ true
round685InputLaplacianWorkIsCommutatorMinusTangentIsTrue = refl

round685C2NowOnForcingCommutatorCurrencyModuloEndpointIsTrue :
  round685C2NowOnForcingCommutatorCurrencyModuloEndpoint ≡ true
round685C2NowOnForcingCommutatorCurrencyModuloEndpointIsTrue = refl

round685IntroducesEstimateIsFalse :
  round685IntroducesEstimate ≡ false
round685IntroducesEstimateIsFalse = refl

round685CommutatorSpacetimePaymentClosedIsFalse :
  round685CommutatorSpacetimePaymentClosed ≡ false
round685CommutatorSpacetimePaymentClosedIsFalse = refl

round685C2ClosedIsFalse :
  round685C2Closed ≡ false
round685C2ClosedIsFalse = refl

round685IntroducesNewClayLeafIsFalse :
  round685IntroducesNewClayLeaf ≡ false
round685IntroducesNewClayLeafIsFalse = refl

round685ClayPromotionIsFalse :
  round685ClayPromotion ≡ false
round685ClayPromotionIsFalse = refl
