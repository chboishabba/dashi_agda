module DASHI.Physics.Closure.NSTriadKNFixedOutputViscousCenteredCovarianceExact where

------------------------------------------------------------------------
-- CANONICAL PHYSICAL COVARIANCE NORMAL FORM
--
-- Compose the exact d1b2 covariance centering identity with the physical
-- fixed-output viscous-rate factorization.
--
-- On one literal output fibre:
--
--   2 * [ n W(M,decay) + (sum lambda_i) W(M,M) ]
--
--     = - nu * sum_{i<j}
--         ( C_i - C_j ) ( w_i - w_j ),
--
-- where
--
--   C_i = |p_i-q_i|^2,
--   w_i = 2 Re <M,A_i>,
--   lambda_i = nu (|p_i|^2+|q_i|^2).
--
-- Hence the physical d1b2 leaf is not a generic covariance-sign theorem and
-- not a generic partner-separation theorem.  It is a signed centered Fourier
-- multiplier commutator on the exact physical output fibre.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (length)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedCommutatorDampedTangentExact as D1a
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Cov
import DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredCovarianceFactorExact as Centered
import DASHI.Physics.Closure.NSTriadKNFixedOutputViscousRateDifferenceFactorizationExact as Rate

F : C3.RealField _
F = Rational.rationalRealField

literalFixedOutputViscousCenteredCovariance :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (nu : ℚ) →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) (output : Z3.FourierMode) →
  let
    items = Output.physicalOutputFiber cutoff output
    value = D1a.mixedProductCell S velocity
    mixed = R224.foldVector value items
    rho = Centered.modalViscousRate nu I
    rate = Cov.cellRate rho
    work = Cov.cellWork mixed value
    decay = R224.foldVector (D1a.variableDecayCell rho S velocity) items
    covarianceNumerator =
      Cov.natAsRational (length items) * Work.coherentWork mixed decay
        + Cov.rateSum rate items * Work.coherentWork mixed mixed
    centeredDefect =
      Centered.centeredPairDifferenceWorkSum E work items
  in
  Rate.two * covarianceNumerator
  ≡ 0ℚ - nu * centeredDefect
literalFixedOutputViscousCenteredCovariance
    E I nu S velocity cutoff output =
  let
    items = Output.physicalOutputFiber cutoff output
    value = D1a.mixedProductCell S velocity
    mixed = R224.foldVector value items
    rho = Centered.modalViscousRate nu I
    rate = Cov.cellRate rho
    work = Cov.cellWork mixed value
    decay = R224.foldVector (D1a.variableDecayCell rho S velocity) items
    covarianceNumerator =
      Cov.natAsRational (length items) * Work.coherentWork mixed decay
        + Cov.rateSum rate items * Work.coherentWork mixed mixed
    pairDifference = Cov.pairDifferenceWorkSum rate work items
    centeredDefect =
      Centered.centeredPairDifferenceWorkSum E work items

    covariance :
      covarianceNumerator ≡ 0ℚ - pairDifference
    covariance =
      Cov.fixedOutputCovariancePairDifference
        rho S velocity cutoff output

    centered :
      Rate.two * pairDifference ≡ nu * centeredDefect
    centered =
      Centered.literalFixedOutputCenteredCovarianceFactor
        E I nu work cutoff output

    scaleCovariance :
      Rate.two * covarianceNumerator
      ≡ Rate.two * (0ℚ - pairDifference)
    scaleCovariance = cong (Rate.two *_) covariance

    exposePairDifference :
      Rate.two * (0ℚ - pairDifference)
      ≡ 0ℚ - (Rate.two * pairDifference)
    exposePairDifference = solve (pairDifference ∷ [])

    replaceCentered :
      0ℚ - (Rate.two * pairDifference)
      ≡ 0ℚ - (nu * centeredDefect)
    replaceCentered = cong (0ℚ -_) centered
  in
  trans scaleCovariance
    (trans exposePairDifference replaceCentered)

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

physicalCovarianceCanonicalCenteredFormClosed : Bool
physicalCovarianceCanonicalCenteredFormClosed = true

genericCovarianceSignTheoremStillCanonical : Bool
genericCovarianceSignTheoremStillCanonical = false

genericPartnerLowerSeparationStillCanonical : Bool
genericPartnerLowerSeparationStillCanonical = false

centeredMultiplierWorkEstimateClosed : Bool
centeredMultiplierWorkEstimateClosed = false

clayPromotion : Bool
clayPromotion = false

physicalCovarianceCanonicalCenteredFormClosedIsTrue :
  physicalCovarianceCanonicalCenteredFormClosed ≡ true
physicalCovarianceCanonicalCenteredFormClosedIsTrue = refl

genericCovarianceSignTheoremStillCanonicalIsFalse :
  genericCovarianceSignTheoremStillCanonical ≡ false
genericCovarianceSignTheoremStillCanonicalIsFalse = refl

genericPartnerLowerSeparationStillCanonicalIsFalse :
  genericPartnerLowerSeparationStillCanonical ≡ false
genericPartnerLowerSeparationStillCanonicalIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
