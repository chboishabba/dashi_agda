{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNA3CauchyMismatchNetworkSplitRound607Exact where

------------------------------------------------------------------------
-- ROUND607 / CANONICAL A3-CAUCHY MISMATCH = SELF MISMATCH + EXTERNAL NETWORK
--
-- R604 isolates the exact fixed-output mismatch
--
--   rateTotal * ForcingFull - 4 * A3.
--
-- R606 proves on the SAME R567 forcing full square
--
--   ForcingFull = SelfForcingFull + ExternalForcingFull.
--
-- Therefore pure rational algebra gives
--
--   rateTotal * ForcingFull - 4 * A3
--     =
--   (rateTotal * SelfForcingFull - 4 * A3)
--     + rateTotal * ExternalForcingFull.
--
-- This is only owner/provenance separation.  In particular:
--   * selected-triad cyclic energy conservation does NOT by itself prove the
--     self mismatch vanishes, because the scalar carriers differ;
--   * the external-network term is retained explicitly.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_)
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
    (viscosityPositive : Data.Rational.Base.Positive
      (Field30.viscosity physicalSystem))
    (output : Z3.FourierMode)
    (outputNonzero : Z3.NonZeroMode output) where

  module M = R604.FixedOutput
    physicalSystem S L H P viscosityPositive output outputNonzero
  module Split = R606.FixedOutput physicalSystem S output

  rateTotal : ℚ
  rateTotal = M.R.Base.rateTotal

  signedA3 : ℚ
  signedA3 = M.R.Base.A3.signedA3

  selfMismatch : ℚ
  selfMismatch =
    rateTotal * Split.selfForcingFull
      - Kernel.four * signedA3

  externalNetworkContribution : ℚ
  externalNetworkContribution =
    rateTotal * Split.externalForcingFull

  forcingFullSameObject :
    M.R.Mismatch.forcingFull ≡ Split.forcingFull
  forcingFullSameObject = refl

  canonicalMismatchSplitsSelfExternal :
    M.canonicalPhysicalMismatch
    ≡ selfMismatch + externalNetworkContribution
  canonicalMismatchSplitsSelfExternal =
    trans
      (cong
        (λ forcingFull →
          rateTotal * forcingFull - Kernel.four * signedA3)
        forcingFullSameObject)
      (trans
        (cong
          (λ forcingFull →
            rateTotal * forcingFull - Kernel.four * signedA3)
          Split.forcingFullSplitsSelfExternal)
        (solve
          ( rateTotal
          ∷ Split.selfForcingFull
          ∷ Split.externalForcingFull
          ∷ Kernel.four
          ∷ signedA3
          ∷ [])))

------------------------------------------------------------------------
-- Status / exact research split.
------------------------------------------------------------------------

round607CanonicalMismatchSelfExternalSplitClosed : Bool
round607CanonicalMismatchSelfExternalSplitClosed = true

round607SelectedSelfMismatchClosed : Bool
round607SelectedSelfMismatchClosed = false

round607ExternalNetworkContributionClosed : Bool
round607ExternalNetworkContributionClosed = false

round607CyclicSelfEnergyConservationDirectlyClosesSelfMismatch : Bool
round607CyclicSelfEnergyConservationDirectlyClosesSelfMismatch = false

round607IntroducesEstimate : Bool
round607IntroducesEstimate = false

round607CanonicalMismatchSelfExternalSplitClosedIsTrue :
  round607CanonicalMismatchSelfExternalSplitClosed ≡ true
round607CanonicalMismatchSelfExternalSplitClosedIsTrue = refl

round607SelectedSelfMismatchClosedIsFalse :
  round607SelectedSelfMismatchClosed ≡ false
round607SelectedSelfMismatchClosedIsFalse = refl

round607ExternalNetworkContributionClosedIsFalse :
  round607ExternalNetworkContributionClosed ≡ false
round607ExternalNetworkContributionClosedIsFalse = refl

round607CyclicSelfEnergyConservationDirectlyClosesSelfMismatchIsFalse :
  round607CyclicSelfEnergyConservationDirectlyClosesSelfMismatch ≡ false
round607CyclicSelfEnergyConservationDirectlyClosesSelfMismatchIsFalse = refl

round607IntroducesEstimateIsFalse :
  round607IntroducesEstimate ≡ false
round607IntroducesEstimateIsFalse = refl
