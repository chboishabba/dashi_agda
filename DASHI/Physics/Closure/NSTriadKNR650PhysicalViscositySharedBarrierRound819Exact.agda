{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650PhysicalViscositySharedBarrierRound819Exact where

------------------------------------------------------------------------
-- ROUND819 / SIGNED SPACETIME ORBIT + W1 -> R735 CRITICAL BARRIER
--
-- This module attaches the actual physical viscosity delta = nu, furnished
-- by R818 under explicit nu > 0, to R735's pre-existing shared weighted
-- barrier. The TWO analytic leaves remain genuinely independent:
--
--   (1) signed integrated R815 orbit payment >= 0, giving W2 via R816;
--   (2) cutoff-independent R735 W1, on its literal quartic weighted carrier.
--
-- No double count of the viscous budget: R818 consumes nu once in W2, and
-- R735's barrier consumes exactly the same retained nu.
--
-- ν is a single R408 LiteralStateSupport field, fixed for every cutoff/time.
-- Thus the dissipative margin in the barrier is uniform in cutoff without
-- manufacturing a positive infimum from cutoff-wise delta_N > 0.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)
import Data.Rational.Properties as ℚP

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
import DASHI.Physics.Closure.NSTriadKNR650PhysicalViscosityMarginRound818Exact as R818
import DASHI.Physics.Closure.NSTriadKNR650SharedWeightedQuarticCutRound735Exact as R735
import DASHI.Physics.Closure.NSTriadKNR650NestedFourHelicityTriadOrbitRound700Exact as R700
import DASHI.Physics.Closure.NSTriadKNR650IntegratedW2PhysicalPacketCombinedRound742Exact as R742
import DASHI.Physics.Closure.NSTriadKNR650IntegratedSignedOrbitPaymentRound816Exact as R816
import DASHI.Physics.Closure.NSTriadKNR650SignedOrbitPacketWeldRound815Exact as R815

F : C3.RealField _
F = Rational.rationalRealField

module PhysicalViscositySharedBarrier
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





  module Margin = R818.PhysicalViscosityMargin
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module Shared = R735.SharedWeightedCut
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module Packet = Margin.Packet

  nu : ℚ
  nu = Margin.nu

  signedOrbitAndW1BuildCriticalBarrier :
    0ℚ < nu →
    (cutoff : Nat) (terminal : Time) →
    (S : Packet.LivePhysicalPacketStructure D C cutoff) →
    (W1 : Shared.CutoffUniformWeightedPlusTerminalPayment) →
    0ℚ ≤ Margin.Signed.At.integratedOrbitPayment
      cutoff nu S terminal →
    Shared.Obs.criticalEnergyAt Shared.T cutoff terminal
      + nu * Shared.Obs.integratedCriticalDissipation
          Shared.T cutoff terminal
    ≤
    Shared.Obs.criticalEnergyAt Shared.T cutoff initialTime
      + R700.twelve * Shared.cutoffIndependentBound W1 terminal
  signedOrbitAndW1BuildCriticalBarrier positive cutoff terminal S W1 payment =
    Shared.sharedWeightedInputsBuildBarrier cutoff terminal
      (record
        { Shared.weightedPlusTerminal = W1
        ; Shared.augmentedCritical =
            Margin.selectPhysicalMarginBuildsR734
              positive cutoff terminal S payment
        })

  allCutoffsPhysicalViscosityBarrier :
    0ℚ < nu →
    (structures : (cutoff : Nat) →
      Packet.LivePhysicalPacketStructure D C cutoff) →
    (W1 : Shared.CutoffUniformWeightedPlusTerminalPayment) →
    ((cutoff : Nat) (terminal : Time) →
      0ℚ ≤ Margin.Signed.At.integratedOrbitPayment cutoff nu
        (structures cutoff) terminal) →
    (cutoff : Nat) (terminal : Time) →
    Shared.Obs.criticalEnergyAt Shared.T cutoff terminal
      + nu * Shared.Obs.integratedCriticalDissipation
          Shared.T cutoff terminal
    ≤
    Shared.Obs.criticalEnergyAt Shared.T cutoff initialTime
      + R700.twelve * Shared.cutoffIndependentBound W1 terminal
  allCutoffsPhysicalViscosityBarrier positive structures W1 signed cutoff terminal =
    signedOrbitAndW1BuildCriticalBarrier
      positive cutoff terminal
      (structures cutoff)
      W1
      (signed cutoff terminal)

round819UsesSamePhysicalNuAtEveryCutoff : Bool
round819UsesSamePhysicalNuAtEveryCutoff = true

round819SignedOrbitPaysExactR742W2 : Bool
round819SignedOrbitPaysExactR742W2 = true

round819W1IndependentAnalyticInput : Bool
round819W1IndependentAnalyticInput = true

round819UniformCriticalBarrierCompilerAvailable : Bool
round819UniformCriticalBarrierCompilerAvailable = true

round819SignedOrbitPaid : Bool
round819SignedOrbitPaid = false

round819W1Paid : Bool
round819W1Paid = false

round819SmoothContinuationClosed : Bool
round819SmoothContinuationClosed = false

round819ClayPromotion : Bool
round819ClayPromotion = false
