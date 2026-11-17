module DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceLiveExact where

------------------------------------------------------------------------
-- S2b2d1b2 / LIVE PHYSICAL FIXED-OUTPUT COHERENT COVARIANCE
--
-- This is the direct composition of the exact centering identity with the
-- physical quantitative pair budget.
--
-- On the ACTUAL mixed-helicity physical output fibre, let
--
--   A_tau = mixedProductCell(tau),
--   M     = sum_tau A_tau,
--   r_tau = nu (|p_tau|^2 + |q_tau|^2),
--   D     = sum_tau variableDecayCell(tau).
--
-- The existing exact centering theorem states
--
--   n W(M,D) + (sum r_tau) W(M,M)
--     = - sum_{alpha<beta}
--         (r_alpha-r_beta)(w_alpha-w_beta).
--
-- The new physical pair theorem therefore yields
--
--   n W(M,D) + (sum r_tau) W(M,M)
--     <= sum_{alpha<beta}
--        |nu (|d_alpha|^2-|d_beta|^2)|
--        ( ||M||^2 + ||A_alpha-A_beta||^2 ).
--
-- Every object in this statement is the literal d1a/d1b physical carrier.
-- This closes the quantitative signed-covariance REDUCTION.  It does not yet
-- prove a cutoff-uniform bound for the positive right-hand family; that is now
-- the remaining analytic payment.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List)
open import Data.List.Base using (length)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinWaleffeAmplitudeTangentRound94Exact as R94
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedCommutatorDampedTangentExact as D1a
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceBudgetExact as Budget

F : C3.RealField _
F = Rational.rationalRealField

module Live
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F) where

  system = Field30.finiteSystem physicalSystem
  cutoff = Audit.cutoff system
  velocity = Audit.velocity system
  rho = R94.physicalDecayRate physicalSystem

  value : Physical.PhysicalTriadIncidence → C3.Complex3 F
  value = D1a.mixedProductCell S velocity

  fibre : Z3.FourierMode → List Physical.PhysicalTriadIncidence
  fibre output = Output.physicalOutputFiber cutoff output

  mixed : Z3.FourierMode → C3.Complex3 F
  mixed output =
    Work.fixedOutputMixedProduct S velocity cutoff output

  decay : Z3.FourierMode → C3.Complex3 F
  decay output =
    Work.fixedOutputVariableDecay rho S velocity cutoff output

  rate : Physical.PhysicalTriadIncidence → ℚ
  rate = Pair.cellRate rho

  work :
    (output : Z3.FourierMode) →
    Physical.PhysicalTriadIncidence → ℚ
  work output = Pair.cellWork (mixed output) value

  coherentCovarianceNumerator : Z3.FourierMode → ℚ
  coherentCovarianceNumerator output =
    Pair.natAsRational (length (fibre output))
      * Work.coherentWork (mixed output) (decay output)
    + Pair.rateSum rate (fibre output)
      * Work.coherentWork (mixed output) (mixed output)

  exactCentering :
    (output : Z3.FourierMode) →
    coherentCovarianceNumerator output
    ≡
    0ℚ - Pair.pairDifferenceWorkSum
      rate (work output) (fibre output)
  exactCentering output =
    Pair.fixedOutputCovariancePairDifference
      rho S velocity cutoff output

  livePhysicalCoherentCovarianceBound :
    (output : Z3.FourierMode) →
    coherentCovarianceNumerator output
    ≤ Budget.physicalCenteredPairSum
        physicalSystem (mixed output) value (fibre output)
  livePhysicalCoherentCovarianceBound output =
    let
      paid :
        0ℚ - Pair.pairDifferenceWorkSum
          rate (work output) (fibre output)
        ≤ Budget.physicalCenteredPairSum
            physicalSystem (mixed output) value (fibre output)
      paid =
        Budget.literalPhysicalOutputFibreNegativeBound
          physicalSystem (mixed output) value cutoff output
    in
    subst
      (λ lower →
        lower
        ≤ Budget.physicalCenteredPairSum
            physicalSystem (mixed output) value (fibre output))
      (sym (exactCentering output))
      paid

------------------------------------------------------------------------
-- Status / sharpened min-cut.
------------------------------------------------------------------------

livePhysicalCoherentCovarianceExactCenteringClosed : Bool
livePhysicalCoherentCovarianceExactCenteringClosed = true

livePhysicalCoherentCovarianceQuantitativeReductionClosed : Bool
livePhysicalCoherentCovarianceQuantitativeReductionClosed = true

livePhysicalCoherentCovarianceIntroducesCardinalityTax : Bool
livePhysicalCoherentCovarianceIntroducesCardinalityTax = false

centeredPhysicalPairFamilyCutoffUniformPaymentClosedHere : Bool
centeredPhysicalPairFamilyCutoffUniformPaymentClosedHere = false

integratedD1b2PaymentClosedHere : Bool
integratedD1b2PaymentClosedHere = false

clayPromotion : Bool
clayPromotion = false

livePhysicalCoherentCovarianceQuantitativeReductionClosedIsTrue :
  livePhysicalCoherentCovarianceQuantitativeReductionClosed ≡ true
livePhysicalCoherentCovarianceQuantitativeReductionClosedIsTrue = refl

livePhysicalCoherentCovarianceIntroducesCardinalityTaxIsFalse :
  livePhysicalCoherentCovarianceIntroducesCardinalityTax ≡ false
livePhysicalCoherentCovarianceIntroducesCardinalityTaxIsFalse = refl
