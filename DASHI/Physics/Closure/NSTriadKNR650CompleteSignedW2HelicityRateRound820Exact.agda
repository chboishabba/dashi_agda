{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650CompleteSignedW2HelicityRateRound820Exact where

------------------------------------------------------------------------
-- ROUND820 / R813 SEPARATED FOUR-HELICITY NORMAL FORM INTO ACTUAL R815
--            SIGNED PHYSICAL RATE, SAME CUTOFF/TIME/PACKET
--
-- The R813 separated Dsep is definitionally R781's fullySeparatedFold,
-- after the R796/R797/R801 aliases are unfolded.
--
-- R815's full signed rate can therefore be rewritten without introducing
-- a new equality premise:
--
--    2*(9*Nsep-Qsep) + Dcc + six*(2nu-margin)*d.
--
-- The same selected rate transports through R815 integration authority.
-- This is one source-written actual physical W2 analytic target, no estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
import DASHI.Physics.Closure.NSTriadKNPhysicalScaleTrichotomy as Scale
import DASHI.Physics.Closure.NSTriadKNPhysicalBonySwapEquivarianceRound129Exact as R129
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
import DASHI.Physics.Closure.NSTriadKNR650SwapPairedResidualCarrierRound760Exact as R760
import DASHI.Physics.Closure.NSTriadKNR650EnergyOrbitBonyProfileRound775Exact as R775
import DASHI.Physics.Closure.NSTriadKNR650OrbitProfileTwoFamilyResidualRound781Exact as R781
import DASHI.Physics.Closure.NSTriadKNLiteralFiniteCriticalObservableFoldExact as Fold
import DASHI.Physics.Closure.NSTriadKNR650CriticalProductionIncidenceCarrierRound744Exact as R744
import DASHI.Physics.Closure.NSTriadKNR650SignedOrbitPacketWeldRound815Exact as R815
import DASHI.Physics.Closure.NSTriadKNR650SeparatedNestedFourHelicityWallRound813Exact as R813

F : C3.RealField _
F = Rational.rationalRealField

module CompleteSignedW2HelicityRate
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
      R417.HermitianDerivativeCalculus
        Time VectorDerivativeOf ScalarDerivativeOf)
    (constantScaleCalculus :
      R416.ScalarConstantDerivativeCalculus
        Time ScalarDerivativeOf)
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



  module Physical = R815.SignedOrbitPacketWeld
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module Nested = R813.SeparatedNestedFourHelicityWall
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module Packet = Physical.Packet

  module At
      (cutoff : Nat)
      (time : Time)
      (S : Packet.LivePhysicalPacketStructure D C cutoff) where

    module P = Physical.At cutoff time S
    module N = Nested.At cutoff time S

    sameSeparatedSelectedScalar :
      P.separated ≡ N.Dsep
    sameSeparatedSelectedScalar = refl

    completeFourHelicityPaymentRate : ℚ → ℚ
    completeFourHelicityPaymentRate margin =
      Fold.two *
        (R813.nine * N.globalNestedFourHelicityWork - N.Qsep)
      + P.touched
      + Physical.six * P.coefficient margin * P.dissipation

    actualR815RateIsFullR813CCTouchedViscousRate :
      (margin : ℚ) →
      P.signedOrbitPaymentRate margin
      ≡ completeFourHelicityPaymentRate margin
    actualR815RateIsFullR813CCTouchedViscousRate margin =
      let
        tail : ℚ
        tail =
          Physical.six * P.coefficient margin * P.dissipation
      in
      trans
        (cong
          (λ selected → selected + P.touched + tail)
          sameSeparatedSelectedScalar)
        (cong
          (λ selected → selected + P.touched + tail)
          N.separatedNestedFourHelicityNormalForm)

  integratedActualFullFourHelicityPayment :
    (cutoff : Nat)
    (margin : ℚ)
    (terminal : Time)
    (S : Packet.LivePhysicalPacketStructure D C cutoff) →
    integrateTo
      (λ time →
        Physical.At.signedOrbitPaymentRate cutoff time S margin)
      terminal
    ≡
    integrateTo
      (λ time →
        At.completeFourHelicityPaymentRate cutoff time S margin)
      terminal
  integratedActualFullFourHelicityPayment cutoff margin terminal S =
    Energy.integrationCongruent integrationLinearity
      (λ time →
        At.actualR815RateIsFullR813CCTouchedViscousRate
          cutoff time S margin)
      terminal

round820R813DsepIsActualR781SelectedFold : Bool
round820R813DsepIsActualR781SelectedFold = true

round820FullR813CCViscousRateMatchesR815 : Bool
round820FullR813CCViscousRateMatchesR815 = true

round820IntegratedSameObjectPaymentRateIdentified : Bool
round820IntegratedSameObjectPaymentRateIdentified = true

round820CompleteSignedInequalityClosed : Bool
round820CompleteSignedInequalityClosed = false

round820W1Closed : Bool
round820W1Closed = false

round820ClayPromotion : Bool
round820ClayPromotion = false

round820CompleteSignedInequalityClosedIsFalse :
  round820CompleteSignedInequalityClosed ≡ false
round820CompleteSignedInequalityClosedIsFalse = refl
