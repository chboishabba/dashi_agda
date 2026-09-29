{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SignedComparableReserveRound823Exact where

------------------------------------------------------------------------
-- R823 / EXACT SIGNED CC+VISCOSITY RESERVE AGAINST CUBIC/QUINTIC DEMAND
--
-- R821's complete payment at the single physical margin delta = nu is
--
--    18 N_sep - 2 Q_sep + D_CC + 6 nu d.
--
-- R822 re-presents D_CC as the sum of ORIGINAL signed R760 cells decorated
-- with actual R818/R204 comparable-localization certificates. No cell is
-- re-evaluated at its p/q representative.
--
-- Define, on that exact same physical cutoff/time packet:
--
--     Reserve  = signedCCRows + 6 nu d
--     Demand   = 2 (Q_sep - 9 N_sep).
--
-- Then R821's exact rate = Reserve - Demand.
-- Through its actual integration authority:
--
--   integratedPayment = integratedReserve - integratedDemand.
--
-- Thus a *single integrated reserve >= demand* estimate pays R821; no
-- cellwise positivity, CC Gram sign, or isolated cancellation is assumed.
-- The estimate is an analytic LEAF, not a proved result of this file.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
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
import DASHI.Physics.Closure.NSTriadKNR650CompleteSignedFourHelicityBarrierRound821Exact as R821
import DASHI.Physics.Closure.NSTriadKNR650CCTouchedSignedRowsRound822Exact as R822
import DASHI.Physics.Closure.NSTriadKNR650NestedFourHelicityTriadOrbitRound700Exact as R700

F : C3.RealField _
F = Rational.rationalRealField

module SignedComparableReserve
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







  module Barrier = R821.CompleteSignedFourHelicityBarrier
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module CC = R822.CCTouchedSignedRows
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module Packet = Barrier.Packet
  module Four = Barrier.Four
  module Shared = Barrier.Shared

  nu : ℚ
  nu = Barrier.nu

  module At
      (cutoff : Nat)
      (time : Time)
      (S : Packet.LivePhysicalPacketStructure D C cutoff) where

    module H = Four.At cutoff time S
    module Cc = CC.At cutoff time S

    signedComparableCC : ℚ
    signedComparableCC = Cc.comparableSignedFold

    viscousReserve : ℚ
    viscousReserve = Four.Physical.six * nu * H.P.dissipation

    signedReserve : ℚ
    signedReserve = signedComparableCC + viscousReserve

    cubicQuinticDemand : ℚ
    cubicQuinticDemand =
      Fold.two * (H.N.Qsep - R813.nine *
        H.N.globalNestedFourHelicityWork)

    completePhysicalRate : ℚ
    completePhysicalRate = H.completeFourHelicityPaymentRate nu

    ccIsSameSignedRows :
      H.P.touched ≡ signedComparableCC
    ccIsSameSignedRows = Cc.actualCCTouchedFoldIsComparableRows

    canonicalCoefficient :
      H.P.coefficient nu ≡ nu
    canonicalCoefficient = solve (Fold.two ∷ nu ∷ [])

    actualFullRateIsReserveMinusDemand :
      completePhysicalRate ≡ signedReserve - cubicQuinticDemand
    actualFullRateIsReserveMinusDemand =
      trans
        (cong
          (λ touched →
             Fold.two *
               (R813.nine * H.N.globalNestedFourHelicityWork - H.N.Qsep)
               + touched
               + Four.Physical.six * H.P.coefficient nu * H.P.dissipation)
          ccIsSameSignedRows)
        (trans
          (cong
            (λ coefficient →
              Fold.two *
                (R813.nine * H.N.globalNestedFourHelicityWork - H.N.Qsep)
              + signedComparableCC
              + Four.Physical.six * coefficient * H.P.dissipation)
            canonicalCoefficient)
          (solve
            ( Fold.two
            ∷ R813.nine
            ∷ H.N.globalNestedFourHelicityWork
            ∷ H.N.Qsep
            ∷ signedComparableCC
            ∷ Four.Physical.six
            ∷ nu
            ∷ H.P.dissipation
            ∷ [])))

  reserveRate :
    (cutoff : Nat) →
    Packet.LivePhysicalPacketStructure D C cutoff →
    Time → ℚ
  reserveRate cutoff S time = At.signedReserve cutoff time S

  demandRate :
    (cutoff : Nat) →
    Packet.LivePhysicalPacketStructure D C cutoff →
    Time → ℚ
  demandRate cutoff S time = At.cubicQuinticDemand cutoff time S

  integratedReserve :
    (cutoff : Nat) →
    Packet.LivePhysicalPacketStructure D C cutoff →
    Time → ℚ
  integratedReserve cutoff S terminal =
    integrateTo (reserveRate cutoff S) terminal

  integratedDemand :
    (cutoff : Nat) →
    Packet.LivePhysicalPacketStructure D C cutoff →
    Time → ℚ
  integratedDemand cutoff S terminal =
    integrateTo (demandRate cutoff S) terminal

  integratedCompleteRate :
    (cutoff : Nat) →
    Packet.LivePhysicalPacketStructure D C cutoff →
    Time → ℚ
  integratedCompleteRate cutoff S terminal =
    integrateTo
      (λ time → At.completePhysicalRate cutoff time S)
      terminal

  integratedReserveMinusDemand :
    (cutoff : Nat)
    (S : Packet.LivePhysicalPacketStructure D C cutoff)
    (terminal : Time) →
    integratedCompleteRate cutoff S terminal
      ≡ integratedReserve cutoff S terminal
          - integratedDemand cutoff S terminal
  integratedReserveMinusDemand cutoff S terminal =
    let
      reserve = integratedReserve cutoff S terminal
      demand = integratedDemand cutoff S terminal

      matched =
        Energy.integrationCongruent integrationLinearity
          (λ time →
            At.actualFullRateIsReserveMinusDemand cutoff time S)
          terminal

      split =
        Energy.integrationAdditive integrationLinearity
          (reserveRate cutoff S)
          (λ time → - demandRate cutoff S time)
          terminal

      negative =
        Energy.integrationConstantScale integrationLinearity
          (- 1ℚ)
          (demandRate cutoff S)
          terminal
    in
    trans matched
      (trans
        (Energy.integrationCongruent integrationLinearity
          (λ time →
            solve (reserveRate cutoff S time ∷ demandRate cutoff S time ∷ []))
          terminal)
        (trans split
          (trans
            (cong (reserve +_) negative)
            (solve (reserve ∷ demand ∷ [])))))

  integratedReservePaysCompleteSignedRate :
    (cutoff : Nat)
    (S : Packet.LivePhysicalPacketStructure D C cutoff)
    (terminal : Time) →
    integratedDemand cutoff S terminal
      ≤ integratedReserve cutoff S terminal →
    0ℚ ≤ integratedCompleteRate cutoff S terminal
  integratedReservePaysCompleteSignedRate cutoff S terminal reserveBound =
    let
      reserve = integratedReserve cutoff S terminal
      demand = integratedDemand cutoff S terminal

      shifted :
        demand + (- demand) ≤ reserve + (- demand)
      shifted = ℚP.+-mono-≤ reserveBound ℚP.≤-refl

      normalized : 0ℚ ≤ reserve - demand
      normalized =
        subst
          (λ left → left ≤ reserve - demand)
          (solve (demand ∷ []))
          (subst
            (λ right → demand + (- demand) ≤ right)
            (solve (reserve ∷ demand ∷ []))
            shifted)
    in
    subst (0ℚ ≤_)
      (sym (integratedReserveMinusDemand cutoff S terminal))
      normalized

  reservePlusW1BuildBarrier :
    0ℚ < nu →
    (cutoff : Nat) (terminal : Time) →
    (S : Packet.LivePhysicalPacketStructure D C cutoff) →
    (W1 : Shared.CutoffUniformWeightedPlusTerminalPayment) →
    integratedDemand cutoff S terminal
      ≤ integratedReserve cutoff S terminal →
    Shared.Obs.criticalEnergyAt Shared.T cutoff terminal
      + nu * Shared.Obs.integratedCriticalDissipation
          Shared.T cutoff terminal
    ≤
    Shared.Obs.criticalEnergyAt Shared.T cutoff initialTime
      + R700.twelve * Shared.cutoffIndependentBound W1 terminal
  reservePlusW1BuildBarrier positive cutoff terminal S W1 reserveBound =
    Barrier.completeSignedFourHelicityAndW1BuildBarrier
      positive cutoff terminal S W1
      (integratedReservePaysCompleteSignedRate
        cutoff S terminal reserveBound)

  -- Shared physical nu and ONE R735 W1 source. The integrated reserve
  -- estimate is required at every cutoff/terminal, with no presumption of
  -- pointwise CC positivity or arbitrarily adjustable margins.
  allCutoffsSignedReserveBarrier :
    0ℚ < nu →
    (structures : (cutoff : Nat) →
      Packet.LivePhysicalPacketStructure D C cutoff) →
    (W1 : Shared.CutoffUniformWeightedPlusTerminalPayment) →
    ((cutoff : Nat) (terminal : Time) →
      integratedDemand cutoff (structures cutoff) terminal
        ≤ integratedReserve cutoff (structures cutoff) terminal) →
    (cutoff : Nat) (terminal : Time) →
    Shared.Obs.criticalEnergyAt Shared.T cutoff terminal
      + nu * Shared.Obs.integratedCriticalDissipation
          Shared.T cutoff terminal
    ≤
    Shared.Obs.criticalEnergyAt Shared.T cutoff initialTime
      + R700.twelve * Shared.cutoffIndependentBound W1 terminal
  allCutoffsSignedReserveBarrier
      positive structures W1 reserves cutoff terminal =
    reservePlusW1BuildBarrier
      positive cutoff terminal (structures cutoff) W1
      (reserves cutoff terminal)

round823SameOriginalCCSignedRows : Bool
round823SameOriginalCCSignedRows = true

round823CCPlusViscosityIsExactReserve : Bool
round823CCPlusViscosityIsExactReserve = true

round823CubicQuinticDemandIsExact : Bool
round823CubicQuinticDemandIsExact = true

round823IntegratedReserveMinusDemandExact : Bool
round823IntegratedReserveMinusDemandExact = true

round823ReserveBoundProvedFromLocalizationAlone : Bool
round823ReserveBoundProvedFromLocalizationAlone = false

round823IntegratedSignedEstimateClosed : Bool
round823IntegratedSignedEstimateClosed = false

round823W1Closed : Bool
round823W1Closed = false

round823ClayPromotion : Bool
round823ClayPromotion = false
