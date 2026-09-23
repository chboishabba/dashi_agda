{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNA3WeightedForcingSameObjectFrontierExact where

------------------------------------------------------------------------
-- A3 / R567 ONE-FIBRE SAME-OBJECT FRONTIER
--
-- R567 already proves on one literal physical output fibre
--
--   FactoredFull_k = 4 * ForcingFull_k.
--
-- A3 carries on that same output a signed pair-difference scalar C_k together
-- with the genuinely new inequality C_k <= B_k.
--
-- Therefore the smallest representation weld needed to feed A3 into the
-- weighted R547/R557/R572 consumer is NOT covariance = R406.  It is:
--
--   ForcingFull_k = C_k.
--
-- This module freezes that one-fibre equality as the exact remaining
-- same-object theorem and compiles it immediately to
--
--   FactoredFull_k = 4 * C_k.
--
-- No estimate is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _*_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNFullSquareDiagonalOffDiagonalRound543Exact as R543
import DASHI.Physics.Closure.NSTriadKNFixedOutputSignedCrossAggregationRound432Exact as R432
import DASHI.Physics.Closure.NSTriadKNFactoredFullCommutatorOnlyRound567Exact as R567
import DASHI.Physics.Closure.NSTriadKNSignedRateVectorPaymentToR503Exact as A3

F : C3.RealField _
F = Rational.rationalRealField

module FixedOutput
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode)
    (payment : A3.FixedOutputSignedRateVectorPayment physicalSystem S output) where

  module C = R567.CommutatorOnly physicalSystem S

  items = Output.physicalOutputFiber
    (Audit.cutoff (Field30.finiteSystem physicalSystem)) output

  forcingFull : ℚ
  forcingFull = R543.fullSquareSum C.T.forcingPair items

  a3SignedCross : ℚ
  a3SignedCross =
    R432.signedCross (A3.a3PaymentToR432 payment)

  record WeightedForcingA3SameObjectWeld : Set where
    field
      forcingFullIsA3SignedCross :
        forcingFull ≡ a3SignedCross

  open WeightedForcingA3SameObjectWeld public

  weldBuildsFactoredFullEquality :
    WeightedForcingA3SameObjectWeld →
    C.NF.factoredFull output items
    ≡ R567.four567 * a3SignedCross
  weldBuildsFactoredFullEquality W =
    trans
      (C.factoredFullIsFourForcingFull output)
      (cong (R567.four567 *_) (forcingFullIsA3SignedCross W))

------------------------------------------------------------------------
-- Frontier status.
------------------------------------------------------------------------

a3WeightedForcingSameObjectSocketConstructed : Bool
a3WeightedForcingSameObjectSocketConstructed = true

a3WeightedForcingSameObjectWeldClosed : Bool
a3WeightedForcingSameObjectWeldClosed = false

a3WeightedForcingWeldIsNewNonlinearEstimate : Bool
a3WeightedForcingWeldIsNewNonlinearEstimate = false

a3WeightedForcingWeldIsRepresentationTheorem : Bool
a3WeightedForcingWeldIsRepresentationTheorem = true

directA3CovarianceEqualsR406Required : Bool
directA3CovarianceEqualsR406Required = false

a3WeightedForcingSameObjectSocketConstructedIsTrue :
  a3WeightedForcingSameObjectSocketConstructed ≡ true
a3WeightedForcingSameObjectSocketConstructedIsTrue = refl

a3WeightedForcingSameObjectWeldClosedIsFalse :
  a3WeightedForcingSameObjectWeldClosed ≡ false
a3WeightedForcingSameObjectWeldClosedIsFalse = refl

a3WeightedForcingWeldIsNewNonlinearEstimateIsFalse :
  a3WeightedForcingWeldIsNewNonlinearEstimate ≡ false
a3WeightedForcingWeldIsNewNonlinearEstimateIsFalse = refl

a3WeightedForcingWeldIsRepresentationTheoremIsTrue :
  a3WeightedForcingWeldIsRepresentationTheorem ≡ true
a3WeightedForcingWeldIsRepresentationTheoremIsTrue = refl

directA3CovarianceEqualsR406RequiredIsFalse :
  directA3CovarianceEqualsR406Required ≡ false
directA3CovarianceEqualsR406RequiredIsFalse = refl
