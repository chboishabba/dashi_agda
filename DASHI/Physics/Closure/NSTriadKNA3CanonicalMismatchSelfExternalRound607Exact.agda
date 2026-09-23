{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNA3CanonicalMismatchSelfExternalRound607Exact where

------------------------------------------------------------------------
-- ROUND607 / CANONICAL A3-CAUCHY MISMATCH = SELF MISMATCH + NETWORK DEFECT
--
-- R604 isolates the literal fixed-output mismatch
--
--   M = rateTotal * ForcingFull - 4 * A3.
--
-- R606 proves on that SAME R567 forcing full square
--
--   ForcingFull = SelfForcingFull + ExternalForcingFull.
--
-- Therefore exact scalar algebra gives
--
--   M
--     =
--   (rateTotal * SelfForcingFull - 4 * A3)
--     + rateTotal * ExternalForcingFull.
--
-- This is the useful physical recut:
--
--   * the selected-triad SELF term is the only place where cyclic/helicity
--     conservation could produce an exact cancellation;
--   * the EXTERNAL term is the genuine network interaction that must either
--     cancel only after a larger aggregation or be estimated.
--
-- No estimate, sign assumption, absolute value, norm, or Clay promotion is
-- introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; Positive; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNA3CenteredKernelNormalFormExact as Kernel
import DASHI.Physics.Closure.NSTriadKNA3CauchyForcingMismatchRound604Exact as R604
import DASHI.Physics.Closure.NSTriadKNR567ForcingFullSelfExternalSplitRound606Exact as R606

F : C3.RealField _
F = Rational.rationalRealField

module FixedOutput
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (P : R225.PhysicalFixedOutputHelicityData
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem)
      S L H
      (Audit.velocityAt (Field30.finiteSystem physicalSystem)))
    (viscosityPositive : Positive (Field30.viscosity physicalSystem))
    (output : Z3.FourierMode)
    (outputNonzero : Z3.NonZeroMode output) where

  module M = R604.FixedOutput
    physicalSystem S L H P viscosityPositive output outputNonzero

  module Net = R606.FixedOutput physicalSystem S output

  rateTotal : ℚ
  rateTotal = M.R.Base.rateTotal

  signedA3 : ℚ
  signedA3 = M.R.Base.A3.signedA3

  forcingFullAgreement :
    M.R.Mismatch.forcingFull ≡ Net.forcingFull
  forcingFullAgreement = refl

  selfMismatch : ℚ
  selfMismatch =
    rateTotal * Net.selfForcingFull
      - Kernel.four * signedA3

  externalNetworkContribution : ℚ
  externalNetworkContribution =
    rateTotal * Net.externalForcingFull

  canonicalMismatchSelfExternal :
    M.canonicalPhysicalMismatch
    ≡ selfMismatch + externalNetworkContribution
  canonicalMismatchSelfExternal =
    trans
      (cong
        (λ forcing →
          rateTotal * forcing - Kernel.four * signedA3)
        forcingFullAgreement)
      (trans
        (cong
          (λ forcing →
            rateTotal * forcing - Kernel.four * signedA3)
          Net.forcingFullSplitsSelfExternal)
        (solve
          ( rateTotal
          ∷ Net.selfForcingFull
          ∷ Net.externalForcingFull
          ∷ Kernel.four
          ∷ signedA3
          ∷ [])))

------------------------------------------------------------------------
-- Status / exact new search boundary.
------------------------------------------------------------------------

round607CanonicalMismatchSelfExternalSplitClosed : Bool
round607CanonicalMismatchSelfExternalSplitClosed = true

round607SelfMismatchIsExactSelectedTriadTarget : Bool
round607SelfMismatchIsExactSelectedTriadTarget = true

round607ExternalNetworkContributionExposed : Bool
round607ExternalNetworkContributionExposed = true

round607SelfMismatchClosed : Bool
round607SelfMismatchClosed = false

round607ExternalNetworkContributionPaid : Bool
round607ExternalNetworkContributionPaid = false

round607IntroducesEstimate : Bool
round607IntroducesEstimate = false

round607ClayPromotion : Bool
round607ClayPromotion = false

round607CanonicalMismatchSelfExternalSplitClosedIsTrue :
  round607CanonicalMismatchSelfExternalSplitClosed ≡ true
round607CanonicalMismatchSelfExternalSplitClosedIsTrue = refl

round607SelfMismatchIsExactSelectedTriadTargetIsTrue :
  round607SelfMismatchIsExactSelectedTriadTarget ≡ true
round607SelfMismatchIsExactSelectedTriadTargetIsTrue = refl

round607ExternalNetworkContributionExposedIsTrue :
  round607ExternalNetworkContributionExposed ≡ true
round607ExternalNetworkContributionExposedIsTrue = refl

round607SelfMismatchClosedIsFalse :
  round607SelfMismatchClosed ≡ false
round607SelfMismatchClosedIsFalse = refl

round607ExternalNetworkContributionPaidIsFalse :
  round607ExternalNetworkContributionPaid ≡ false
round607ExternalNetworkContributionPaidIsFalse = refl

round607IntroducesEstimateIsFalse :
  round607IntroducesEstimate ≡ false
round607IntroducesEstimateIsFalse = refl

round607ClayPromotionIsFalse :
  round607ClayPromotion ≡ false
round607ClayPromotionIsFalse = refl
