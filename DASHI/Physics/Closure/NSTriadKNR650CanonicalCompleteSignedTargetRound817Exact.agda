{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650CanonicalCompleteSignedTargetRound817Exact where

------------------------------------------------------------------------
-- ROUND817 / CANONICAL COMPLETE SIGNED TARGET
--
-- R813:
--   D_sep = 2 (9 N_sep - Q_sep).
--
-- R815:
--   D_sep + D_CC + 6 (2nu-delta) d
--     = 6 (Combined - Packet_delta).
--
-- R816 chooses the canonical retained margin delta = nu, so
--
--   2nu-delta = nu > 0.
--
-- This owner installs the exact live analytic target
--
--   Target_N(t)
--     = 2 (9 N_sep(t) - Q_sep(t))
--       + D_CC(t)
--       + 6 nu d_N(t)
--
-- and proves, on the SAME live physical packet,
--
--   Target_N(t) = R815.orbitPaymentRate_nu(t).
--
-- Therefore a single integrated nonnegativity theorem for Target_N builds
-- R742 directly via R816.  No cancellation of the separated family and no
-- separate uniform-margin theorem are required.
--
-- The nonnegativity itself remains open.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxFiniteDerivativeCompilerRound412Exact as R412
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyCalculusExact as Energy
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedEndpointCompilerExact as Endpoint
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffModeCarrierExact as ModeCarrier
import DASHI.Physics.Closure.NSTriadKNLiteralFiniteCriticalObservableFoldExact as Fold
import DASHI.Physics.Closure.NSTriadKNR650SeparatedNestedFourHelicityWallRound813Exact as R813
import DASHI.Physics.Closure.NSTriadKNR650SignedOrbitPacketWeldRound815Exact as R815
import DASHI.Physics.Closure.NSTriadKNR650CanonicalViscosityMarginPaymentRound816Exact as R816
import DASHI.Physics.Closure.NSTriadKNR650IntegratedW2PhysicalPacketCombinedRound742Exact as R742

F : C3.RealField _
F = Rational.rationalRealField

module CanonicalCompleteSignedTarget
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (VectorDerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf :
      (Time → ℚ) → (Time → ℚ) → Set)
    (projectedCross :
      R426.ProjectedCrossDerivativeCalculus Time VectorDerivativeOf)
    (vectorAlgebra :
      R425.VectorDerivativeAlgebra Time VectorDerivativeOf)
    (zeroCalculus :
      Endpoint.VectorZeroDerivative Time VectorDerivativeOf)
    (hermitianCalculus :
      R417.HermitianDerivativeCalculus Time VectorDerivativeOf ScalarDerivativeOf)
    (constantScaleCalculus :
      R416.ScalarConstantDerivativeCalculus Time ScalarDerivativeOf)
    (scalarDerivativeAlgebra :
      R412.ScalarDerivativeAlgebra Time ScalarDerivativeOf)
    (FTC :
      R564.ScalarFundamentalTheorem564
        Time initialTime integrateTo ScalarDerivativeOf)
    (integrationLinearity :
      Energy.ScalarIntegrationLinearity Time integrateTo)
    (integrationTransport :
      R495.IntegrationTransportAuthority Time integrateTo)
    (D :
      R408.LiteralDynamics.LiteralRHSTrajectoryData
        Time initialTime integrateTo VectorDerivativeOf)
    (C :
      ModeCarrier.LiteralModeCarrier.LiteralCutoffModeCarrier
        Time initialTime integrateTo VectorDerivativeOf
        (R408.LiteralDynamics.literalPhysicalTrajectory
          Time initialTime integrateTo VectorDerivativeOf D))
    (R :
      R405.LiteralCutoffSupport.LiteralNonzeroCutoffTrajectory
        Time initialTime integrateTo VectorDerivativeOf
        (R408.LiteralDynamics.literalPhysicalTrajectory
          Time initialTime integrateTo VectorDerivativeOf D)) where

  module Weld =
    R815.SignedOrbitPacketWeld
      Time initialTime integrateTo
      VectorDerivativeOf ScalarDerivativeOf
      projectedCross vectorAlgebra zeroCalculus
      hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
      FTC integrationLinearity integrationTransport D C R

  module Sep =
    R813.SeparatedNestedFourHelicityWall
      Time initialTime integrateTo
      VectorDerivativeOf ScalarDerivativeOf
      projectedCross vectorAlgebra zeroCalculus
      hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
      FTC integrationLinearity integrationTransport D C R

  module Canon =
    R816.CanonicalViscosityMarginPayment
      Time initialTime integrateTo
      VectorDerivativeOf ScalarDerivativeOf
      projectedCross vectorAlgebra zeroCalculus
      hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
      FTC integrationLinearity integrationTransport D C R

  module W2 = Canon.W2
  module Packet = Weld.Packet

  module At
      (cutoff : Nat)
      (time : Time)
      (S : Packet.LivePhysicalPacketStructure D C cutoff) where

    module W = Weld.At cutoff time S
    module H = Sep.At cutoff time S

    nested : ℚ
    nested = H.globalNestedFourHelicityWork

    quotient : ℚ
    quotient = H.Qsep

    touched : ℚ
    touched = W.touched

    dissipation : ℚ
    dissipation = W.dissipation

    completeTargetRate : ℚ
    completeTargetRate =
      Fold.two * (R813.nine * nested - quotient)
        + touched
        + Weld.six * Canon.nu * dissipation

    separatedSameObject :
      W.separated ≡ H.Dsep
    separatedSameObject = refl

    canonicalOrbitRateIsCompleteTarget :
      W.signedOrbitPaymentRate Canon.nu
      ≡ completeTargetRate
    canonicalOrbitRateIsCompleteTarget =
      let
        sep = H.Dsep
        nestedValue = nested
        q = quotient
        cc = touched
        diss = dissipation

        separatedNormal :
          sep ≡ Fold.two * (R813.nine * nestedValue - q)
        separatedNormal = H.separatedNestedFourHelicityNormalForm

        coeff :
          W.coefficient Canon.nu ≡ Canon.nu
        coeff = Canon.canonicalCoefficient cutoff time S
      in
      trans
        (cong
          (λ value →
            value + cc
              + Weld.six * W.coefficient Canon.nu * diss)
          separatedSameObject)
        (trans
          (cong
            (λ value →
              value + cc
                + Weld.six * W.coefficient Canon.nu * diss)
            separatedNormal)
          (cong
            (λ value →
              Fold.two * (R813.nine * nestedValue - q)
                + cc
                + Weld.six * value * diss)
            coeff))

  completeTargetRate :
    (cutoff : Nat) →
    Packet.LivePhysicalPacketStructure D C cutoff →
    Time → ℚ
  completeTargetRate cutoff S time =
    At.completeTargetRate cutoff time S

  completeTargetIntegral :
    (cutoff : Nat) →
    Packet.LivePhysicalPacketStructure D C cutoff →
    Time → ℚ
  completeTargetIntegral cutoff S terminal =
    integrateTo (completeTargetRate cutoff S) terminal

  completeTargetIntegralIsCanonicalOrbitIntegral :
    (cutoff : Nat) →
    (S : Packet.LivePhysicalPacketStructure D C cutoff) →
    (terminal : Time) →
    completeTargetIntegral cutoff S terminal
    ≡ Canon.canonicalOrbitIntegral cutoff S terminal
  completeTargetIntegralIsCanonicalOrbitIntegral cutoff S terminal =
    Energy.integrationCongruent integrationLinearity
      (λ time →
        sym (At.canonicalOrbitRateIsCompleteTarget cutoff time S))
      terminal

  completeTargetNonnegativeBuildsR742 :
    (cutoff : Nat) →
    (S : Packet.LivePhysicalPacketStructure D C cutoff) →
    (terminal : Time) →
    0ℚ ≤ completeTargetIntegral cutoff S terminal →
    W2.IntegratedPhysicalPacketCombinedPayment cutoff terminal
  completeTargetNonnegativeBuildsR742 cutoff S terminal payment =
    Canon.signedPaymentBuildsPacketCombined
      cutoff S terminal
      (subst
        (0ℚ ≤_)
        (completeTargetIntegralIsCanonicalOrbitIntegral cutoff S terminal)
        payment)

  completeTargetNonnegativeBuildsAugmentedW2 :
    (cutoff : Nat) →
    (S : Packet.LivePhysicalPacketStructure D C cutoff) →
    (terminal : Time) →
    0ℚ ≤ completeTargetIntegral cutoff S terminal →
    W2.Aug.AugmentedCriticalWeightedPayment cutoff terminal
  completeTargetNonnegativeBuildsAugmentedW2 cutoff S terminal payment =
    W2.packetCombinedBuildsAugmentedW2 cutoff terminal
      (completeTargetNonnegativeBuildsR742 cutoff S terminal payment)

round817CompleteTargetSameObjectInstalled : Bool
round817CompleteTargetSameObjectInstalled = true

round817CanonicalViscousTermIsSixNuDissipation : Bool
round817CanonicalViscousTermIsSixNuDissipation = true

round817OneIntegratedNonnegativeTargetBuildsR742 : Bool
round817OneIntegratedNonnegativeTargetBuildsR742 = true

round817OneIntegratedNonnegativeTargetBuildsAugmentedW2 : Bool
round817OneIntegratedNonnegativeTargetBuildsAugmentedW2 = true

round817AnalyticNonnegativityClosed : Bool
round817AnalyticNonnegativityClosed = false

round817IntroducesEstimate : Bool
round817IntroducesEstimate = false

round817ClayPromotion : Bool
round817ClayPromotion = false
