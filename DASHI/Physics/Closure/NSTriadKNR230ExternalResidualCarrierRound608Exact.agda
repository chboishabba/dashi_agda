{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR230ExternalResidualCarrierRound608Exact where

------------------------------------------------------------------------
-- ROUND608 / R230 EXTERNAL PRODUCT-RULE CELL ON THE LITERAL R112 RESIDUALS
--
-- R605 splits the actual R230 product-rule forcing into selected-triad self
-- forcing and external-network forcing.  R112 separately identifies the
-- external p/q modal forcing slots with literal output-fibre residual vectors
-- after deleting the selected self swap-orbit.
--
-- Given exactly R112's existing ThreeLegResidualMembership witness, this owner
-- rewrites the R605 external product-rule cell to those SAME residual vectors:
--
--   ExternalR230Cell(tau)
--     =
--   P^+(Residual_p) x P^-(u_q)
--     + P^+(u_p) x P^-(Residual_q).
--
-- This is representation only.  It does not identify the vector R230 cell with
-- R112's scalar Waleffe amplitude functional, does not create a Bony estimate,
-- and does not pay the R607 external-network mismatch.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNExternalWaleffeResidualCarrierRound112Exact as R112
import DASHI.Physics.Closure.NSTriadKNR230SelfExternalNetworkSplitRound605Exact as R605

F : C3.RealField _
F = Rational.rationalRealField

module FixedSystem
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F) where

  module Net = R605.FixedSystem physicalSystem S

  E = Field30.physicalEmbedding physicalSystem
  I = Field30.physicalInverseSquare physicalSystem
  system = Field30.finiteSystem physicalSystem
  velocity = Audit.velocityAt system

  externalResidualProductRuleCell :
    (tau : Physical.PhysicalTriadIncidence) →
    R112.ThreeLegResidualMembership system tau →
    C3.Complex3 F
  externalResidualProductRuleCell tau M =
    C3.complex3Add
      (Cross.complex3Cross
        (Helical.helicalProjectorPlus E I S
          (Physical.p tau)
          (R112.externalResidualP system tau M))
        (Helical.helicalProjectorMinus E I S
          (Physical.q tau)
          (velocity (Physical.q tau))))
      (Cross.complex3Cross
        (Helical.helicalProjectorPlus E I S
          (Physical.p tau)
          (velocity (Physical.p tau)))
        (Helical.helicalProjectorMinus E I S
          (Physical.q tau)
          (R112.externalResidualQ system tau M)))

  externalProductRuleCellIsResidualCarrier :
    (tau : Physical.PhysicalTriadIncidence) →
    (M : R112.ThreeLegResidualMembership system tau) →
    Net.externalProductRuleCell tau
    ≡ externalResidualProductRuleCell tau M
  externalProductRuleCellIsResidualCarrier tau M
    rewrite R112.externalForcingPIsResidual system tau M
          | R112.externalForcingQIsResidual system tau M =
    refl

------------------------------------------------------------------------
-- Status / trust boundary.
------------------------------------------------------------------------

round608R230ExternalCellOnLiteralResidualCarrierClosed : Bool
round608R230ExternalCellOnLiteralResidualCarrierClosed = true

round608UsesExistingThreeLegResidualWitnessExactly : Bool
round608UsesExistingThreeLegResidualWitnessExactly = true

round608IdentifiesVectorCellWithScalarWaleffeFunctional : Bool
round608IdentifiesVectorCellWithScalarWaleffeFunctional = false

round608ExternalNetworkMismatchPaid : Bool
round608ExternalNetworkMismatchPaid = false

round608IntroducesEstimate : Bool
round608IntroducesEstimate = false

round608ClayPromotion : Bool
round608ClayPromotion = false

round608R230ExternalCellOnLiteralResidualCarrierClosedIsTrue :
  round608R230ExternalCellOnLiteralResidualCarrierClosed ≡ true
round608R230ExternalCellOnLiteralResidualCarrierClosedIsTrue = refl

round608UsesExistingThreeLegResidualWitnessExactlyIsTrue :
  round608UsesExistingThreeLegResidualWitnessExactly ≡ true
round608UsesExistingThreeLegResidualWitnessExactlyIsTrue = refl

round608IdentifiesVectorCellWithScalarWaleffeFunctionalIsFalse :
  round608IdentifiesVectorCellWithScalarWaleffeFunctional ≡ false
round608IdentifiesVectorCellWithScalarWaleffeFunctionalIsFalse = refl

round608ExternalNetworkMismatchPaidIsFalse :
  round608ExternalNetworkMismatchPaid ≡ false
round608ExternalNetworkMismatchPaidIsFalse = refl

round608IntroducesEstimateIsFalse :
  round608IntroducesEstimate ≡ false
round608IntroducesEstimateIsFalse = refl

round608ClayPromotionIsFalse :
  round608ClayPromotion ≡ false
round608ClayPromotionIsFalse = refl
