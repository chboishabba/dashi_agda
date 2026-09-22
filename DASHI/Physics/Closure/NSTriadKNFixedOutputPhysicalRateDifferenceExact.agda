module DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalRateDifferenceExact where

------------------------------------------------------------------------
-- S2b2d1b2 / A2 EXACT PHYSICAL VISCOUS RATE DIFFERENCE
--
-- The covariance carrier uses
--
--   cellRate rho tau = rho(p_tau) + rho(q_tau).
--
-- The live physical Galerkin owner already defines, on the SAME rational
-- carrier,
--
--   physicalDecayRate(mode) = nu * normSquared(mode).
--
-- This module performs only that same-object specialization and subtraction.
-- No sign, lower bound, Pluecker estimate, absolute value, or payment is added.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _-_)
open import Relation.Binary.PropositionalEquality using (cong₂)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as PhysicalField
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinWaleffeAmplitudeTangentRound94Exact as R94
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair

F : C3.RealField _
F = Rational.rationalRealField

physicalModalRate :
  PhysicalField.PhysicalFiniteComplex3GalerkinSystem F →
  Z3.FourierMode → ℚ
physicalModalRate = R94.physicalDecayRate

physicalCellRate :
  PhysicalField.PhysicalFiniteComplex3GalerkinSystem F →
  Physical.PhysicalTriadIncidence → ℚ
physicalCellRate system = Pair.cellRate (physicalModalRate system)

literalViscousCellRate :
  PhysicalField.PhysicalFiniteComplex3GalerkinSystem F →
  Physical.PhysicalTriadIncidence → ℚ
literalViscousCellRate system tau =
  C3.multiply F
    (PhysicalField.viscosity system)
    (C3.normSquared
      (Audit.inverseSquare (PhysicalField.finiteSystem system))
      (Physical.p tau))
  +
  C3.multiply F
    (PhysicalField.viscosity system)
    (C3.normSquared
      (Audit.inverseSquare (PhysicalField.finiteSystem system))
      (Physical.q tau))

physicalCellRateIsLiteralViscousRate :
  (system : PhysicalField.PhysicalFiniteComplex3GalerkinSystem F) →
  (tau : Physical.PhysicalTriadIncidence) →
  physicalCellRate system tau ≡ literalViscousCellRate system tau
physicalCellRateIsLiteralViscousRate system tau = refl

physicalRateDifference :
  PhysicalField.PhysicalFiniteComplex3GalerkinSystem F →
  Physical.PhysicalTriadIncidence →
  Physical.PhysicalTriadIncidence → ℚ
physicalRateDifference system alpha beta =
  literalViscousCellRate system alpha - literalViscousCellRate system beta

physicalCellRateDifference :
  (system : PhysicalField.PhysicalFiniteComplex3GalerkinSystem F) →
  (alpha beta : Physical.PhysicalTriadIncidence) →
  Pair.cellRate (R94.physicalDecayRate system) alpha
    - Pair.cellRate (R94.physicalDecayRate system) beta
  ≡ physicalRateDifference system alpha beta
physicalCellRateDifference system alpha beta =
  cong₂ _-_
    (physicalCellRateIsLiteralViscousRate system alpha)
    (physicalCellRateIsLiteralViscousRate system beta)

------------------------------------------------------------------------
-- Trust boundary.
------------------------------------------------------------------------

physicalCellRateSameObjectWeldClosed : Bool
physicalCellRateSameObjectWeldClosed = true

physicalCellRateDifferenceSameObjectWeldClosed : Bool
physicalCellRateDifferenceSameObjectWeldClosed = true

physicalCellRateDifferenceAddsSignClaim : Bool
physicalCellRateDifferenceAddsSignClaim = false

physicalCellRateDifferenceAddsQuantitativePayment : Bool
physicalCellRateDifferenceAddsQuantitativePayment = false

physicalCellRateDifferenceSameObjectWeldClosedIsTrue :
  physicalCellRateDifferenceSameObjectWeldClosed ≡ true
physicalCellRateDifferenceSameObjectWeldClosedIsTrue = refl

physicalCellRateDifferenceAddsSignClaimIsFalse :
  physicalCellRateDifferenceAddsSignClaim ≡ false
physicalCellRateDifferenceAddsSignClaimIsFalse = refl

physicalCellRateDifferenceAddsQuantitativePaymentIsFalse :
  physicalCellRateDifferenceAddsQuantitativePayment ≡ false
physicalCellRateDifferenceAddsQuantitativePaymentIsFalse = refl
