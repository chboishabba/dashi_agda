module DASHI.Physics.Closure.NSTriadKNViscousCenteredCovarianceM2PaymentExact where

------------------------------------------------------------------------
-- PERIODIC B / ACTUAL VISCOUS COVARIANCE NUMERATOR -> R571 M2 BUDGET
--
-- The exact physical normal form is
--
--   2 CovNum = - nu * CenteredDefect.
--
-- The literal fixed-output covariance theorem now gives the TWO-SIDED bound
--
--   |CenteredDefect| <= M2Budget.
--
-- Therefore for nonnegative viscosity
--
--   2 CovNum <= nu * M2Budget.
--
-- This is the correctly oriented physical d1b2 consumer theorem.  In
-- particular we do not use a one-sided upper bound on CenteredDefect to control
-- its negative multiple.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ
  using (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; ∣_∣; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedCommutatorDampedTangentExact as D1a
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Cov
import DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredCovarianceFactorExact as Centered
import DASHI.Physics.Closure.NSTriadKNFixedOutputViscousCenteredCovarianceExact as Viscous
import DASHI.Physics.Closure.NSTriadKNLiteralFixedOutputCovarianceM2PaymentExact as M2

F : C3.RealField _
F = Rational.rationalRealField

module PhysicalViscousCovarianceM2
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (nu : ℚ)
    (nuNonnegative : 0ℚ ≤ nu)
    (S : Helical.HelicalModeScalars F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (cutoff : Nat)
    (output : Z3.FourierMode) where

  module P = M2.LiteralFixedOutputCovarianceM2
    {E = E} {I = I} S velocity cutoff output

  items = P.items
  value = P.value
  mixed = P.mixed
  work = P.work

  rho = Centered.modalViscousRate nu I
  rate = Cov.cellRate rho

  decay =
    R224.foldVector (D1a.variableDecayCell rho S velocity) items

  covarianceNumerator : ℚ
  covarianceNumerator =
    Cov.natAsRational (Data.List.Base.length items)
      * Work.coherentWork mixed decay
    + Cov.rateSum rate items * Work.coherentWork mixed mixed

  centeredDefect : ℚ
  centeredDefect =
    Centered.centeredPairDifferenceWorkSum E work items

  exactViscousCenteredNormalForm :
    Centered.Rate.two * covarianceNumerator
    ≡ 0ℚ - nu * centeredDefect
  exactViscousCenteredNormalForm =
    Viscous.literalFixedOutputViscousCenteredCovariance
      E I nu S velocity cutoff output

  negativeDefectBelowAbsolute :
    0ℚ - centeredDefect ≤ ∣ centeredDefect ∣
  negativeDefectBelowAbsolute =
    let
      asNeg : 0ℚ - centeredDefect ≡ - centeredDefect
      asNeg = solve (centeredDefect ∷ [])
    in
    subst
      (_≤ ∣ centeredDefect ∣)
      (sym asNeg)
      (trans
        (ℚP.p≤∣p∣ (- centeredDefect))
        (subst
          ((- centeredDefect) ≤_)
          (ℚP.∣-p∣≡∣p∣ centeredDefect)
          ℚP.≤-refl))

  negativeDefectBelowM2 :
    0ℚ - centeredDefect ≤ P.totalM2Budget items
  negativeDefectBelowM2 =
    ℚP.≤-trans
      negativeDefectBelowAbsolute
      P.literalFixedOutputCenteredCovarianceAbsoluteBelowM2

  scaledNegativeDefectBelowM2 :
    nu * (0ℚ - centeredDefect)
    ≤ nu * P.totalM2Budget items
  scaledNegativeDefectBelowM2 =
    let instance nuNN = nonNegative nuNonnegative
    in ℚP.*-monoˡ-≤-nonNeg nu negativeDefectBelowM2

  physicalViscousCovarianceBelowM2 :
    Centered.Rate.two * covarianceNumerator
    ≤ nu * P.totalM2Budget items
  physicalViscousCovarianceBelowM2 =
    let
      rightForm :
        0ℚ - nu * centeredDefect
        ≡ nu * (0ℚ - centeredDefect)
      rightForm = solve (nu ∷ centeredDefect ∷ [])
    in
    subst
      (λ left → left ≤ nu * P.totalM2Budget items)
      (sym exactViscousCenteredNormalForm)
      (subst
        (_≤ nu * P.totalM2Budget items)
        (sym rightForm)
        scaledNegativeDefectBelowM2)

viscousCenteredCovarianceM2PaymentClosed : Bool
viscousCenteredCovarianceM2PaymentClosed = true

viscousCenteredCovarianceM2UsesCorrectNegativeSign : Bool
viscousCenteredCovarianceM2UsesCorrectNegativeSign = true

viscousCenteredCovarianceM2AddsCardinalityFactor : Bool
viscousCenteredCovarianceM2AddsCardinalityFactor = false

clayPromotion : Bool
clayPromotion = false
