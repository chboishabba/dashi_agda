{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650CompleteSignedFourHelicityBarrierRound821Exact where

------------------------------------------------------------------------
-- ROUND821 / EXACT PHYSICAL SIGNED W2 RATE AS THE R735 BARRIER INPUT
--
-- The genuine analytic input is the integrated nonnegativity of the
-- R820 rate:
--
--   2*(9*N_sep-Q_sep) + D_cc + 6*(2nu-delta)*d.
--
-- At delta=nu>0 (chosen from one R408 physical viscosity), R820 proves
-- this is exactly the R815 signed packet gap, not an independent surrogate.
-- The rest is the existing R816/R818/R819/R735 compiler.
--
-- This is a typed SAME-OBJECT conditional theorem with only W1 and the
-- complete signed inequality as analytic premises; no independent
-- separated cancellation, ad hoc uniform margin, or proof of W2 is assumed.
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
import DASHI.Physics.Closure.NSTriadKNR650PhysicalViscositySharedBarrierRound819Exact as R819
import DASHI.Physics.Closure.NSTriadKNR650CompleteSignedW2HelicityRateRound820Exact as R820
import DASHI.Physics.Closure.NSTriadKNR650IntegratedW2PhysicalPacketCombinedRound742Exact as R742
import DASHI.Physics.Closure.NSTriadKNR650IntegratedSignedOrbitPaymentRound816Exact as R816
import DASHI.Physics.Closure.NSTriadKNR650SignedOrbitPacketWeldRound815Exact as R815

F : C3.RealField _
F = Rational.rationalRealField

module CompleteSignedFourHelicityBarrier
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






  module Barrier = R819.PhysicalViscositySharedBarrier
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module Four = R820.CompleteSignedW2HelicityRate
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module Shared = Barrier.Shared
  module Packet = Barrier.Packet

  nu : ℚ
  nu = Barrier.nu

  completeFourHelicitySignedPayment :
    (cutoff : Nat)
    (terminal : Time)
    (S : Packet.LivePhysicalPacketStructure D C cutoff) →
    Set
  completeFourHelicitySignedPayment cutoff terminal S =
    0ℚ ≤ integrateTo
      (λ time →
        Four.At.completeFourHelicityPaymentRate cutoff time S nu)
      terminal

  fourHelicitySignedPaymentIsR815Payment :
    (cutoff : Nat) (terminal : Time) →
    (S : Packet.LivePhysicalPacketStructure D C cutoff) →
    completeFourHelicitySignedPayment cutoff terminal S →
    0ℚ ≤ Barrier.Margin.Signed.At.integratedOrbitPayment
      cutoff nu S terminal
  fourHelicitySignedPaymentIsR815Payment cutoff terminal S payment =
    subst
      (0ℚ ≤_)
      (sym (Four.integratedActualFullFourHelicityPayment
        cutoff nu terminal S))
      payment

  completeSignedFourHelicityAndW1BuildBarrier :
    0ℚ < nu →
    (cutoff : Nat) (terminal : Time) →
    (S : Packet.LivePhysicalPacketStructure D C cutoff) →
    (W1 : Shared.CutoffUniformWeightedPlusTerminalPayment) →
    completeFourHelicitySignedPayment cutoff terminal S →
    Shared.Obs.criticalEnergyAt Shared.T cutoff terminal
      + nu * Shared.Obs.integratedCriticalDissipation
          Shared.T cutoff terminal
    ≤
    Shared.Obs.criticalEnergyAt Shared.T cutoff initialTime
      + R700.twelve * Shared.cutoffIndependentBound W1 terminal
  completeSignedFourHelicityAndW1BuildBarrier
      positive cutoff terminal S W1 signed =
    Barrier.signedOrbitAndW1BuildCriticalBarrier
      positive cutoff terminal S W1
      (fourHelicitySignedPaymentIsR815Payment
        cutoff terminal S signed)

  allCutoffsCompleteSignedFourHelicityBarrier :
    0ℚ < nu →
    (structures : (cutoff : Nat) →
      Packet.LivePhysicalPacketStructure D C cutoff) →
    (W1 : Shared.CutoffUniformWeightedPlusTerminalPayment) →
    ((cutoff : Nat) (terminal : Time) →
      completeFourHelicitySignedPayment
        cutoff terminal (structures cutoff)) →
    (cutoff : Nat) (terminal : Time) →
    Shared.Obs.criticalEnergyAt Shared.T cutoff terminal
      + nu * Shared.Obs.integratedCriticalDissipation
          Shared.T cutoff terminal
    ≤
    Shared.Obs.criticalEnergyAt Shared.T cutoff initialTime
      + R700.twelve * Shared.cutoffIndependentBound W1 terminal
  allCutoffsCompleteSignedFourHelicityBarrier
      positive structures W1 signed cutoff terminal =
    completeSignedFourHelicityAndW1BuildBarrier
      positive cutoff terminal
      (structures cutoff)
      W1
      (signed cutoff terminal)

round821UsesActualR813R815SameObjectSignedRate : Bool
round821UsesActualR813R815SameObjectSignedRate = true

round821SelectedNuIsUniformAcrossCutoffs : Bool
round821SelectedNuIsUniformAcrossCutoffs = true

round821BuildsExistingR735BarrierGivenPhysicalPayments : Bool
round821BuildsExistingR735BarrierGivenPhysicalPayments = true

round821SignedAnalyticPaymentClosed : Bool
round821SignedAnalyticPaymentClosed = false

round821W1AnalyticPaymentClosed : Bool
round821W1AnalyticPaymentClosed = false

round821SmoothContinuationClosed : Bool
round821SmoothContinuationClosed = false

round821ClayPromotion : Bool
round821ClayPromotion = false

round821SignedAnalyticPaymentClosedIsFalse :
  round821SignedAnalyticPaymentClosed ≡ false
round821SignedAnalyticPaymentClosedIsFalse = refl
