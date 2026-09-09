module DASHI.Physics.Closure.NSTriadKNLiveCommutatorOnlyLeafABoundaryRound568Exact where

------------------------------------------------------------------------
-- ROUND568 / LIVE GLOBAL LEAF-A WALL AFTER TRANSPOSE + DIAGONAL REDUCTIONS
--
-- R567 removes the independent amplitude half:
--
--   factoredFull = 4 * forcingFull.
--
-- R557 gives on the literal live R406 trajectory
--
--   2 ∫R406 = ∫factoredFull - ∫selfGram - ∫selfFluxTangent.
--
-- R565 isolates the only ordinary-analysis receipt still needed for the
-- diagonal endpoint. R553 then drops the nonnegative selfGram and terminal
-- selfFlux terms, leaving the initial selfFlux only.
--
-- Therefore, modulo that standard scalar FTC receipt and the already-isolated
-- endpoint calibration, the sole new PDE estimate on this direct route is a
-- cutoff-uniform spacetime upper bound for the LIVE global sum of R567's
-- forcing/commutator full squares.
--
-- This owner deliberately does not claim that bound. It makes the consumer
-- exact so future work cannot substitute a Schur proxy, absolute-value envelope,
-- heat-separable proxy, or cross-domain theorem without an explicit same-object
-- weld.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Canonical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNFixedOutputLiveGlobalFluxRound406Exact as R406
import DASHI.Physics.Closure.NSTriadKNLiteralNonzeroCutoffSupportRound404Exact as R404
import DASHI.Physics.Closure.NSTriadKNFullSquareDiagonalOffDiagonalRound543Exact as R543
import DASHI.Physics.Closure.NSTriadKNFactoredFullCommutatorOnlyRound567Exact as R567
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNDirectResolventIntegratedCompanionRound500Exact as R500
import DASHI.Physics.Closure.NSTriadKNDirectResolventSignedCrossToR415Round503Exact as R503
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

F : C3.RealField _
F = Rational.rationalRealField

module LiveCommutatorOnly
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (integration : R495.IntegrationTransportAuthority Time integrateTo) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Flux = R406.FixedLiveFlux
    Time initialTime integrateTo DerivativeOf
  module Direct = R500.IntegratedDirect
    Time initialTime integrateTo DerivativeOf integration
  module Budget = R503.DirectSignedCross
    Time initialTime integrateTo DerivativeOf integration

  outputForcingFull :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) → Time → Z3.FourierMode → ℚ
  outputForcingFull T R cutoff time output =
    let
      module Slice = Flux.At T R cutoff time
      S = Dyn.Base.S (Dyn.forgetDynamics T)
      module C = R567.CommutatorOnly Slice.PS S
      items = DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber.physicalOutputFiber
        cutoff output
    in
    R543.fullSquareSum C.T.forcingPair items

  globalForcingFull :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) → Time → ℚ
  globalForcingFull T R cutoff time =
    sumOutputs (Canonical.nonzeroCutoffModes cutoff)
    where
    sumOutputs : List Z3.FourierMode → ℚ
    sumOutputs [] = 0ℚ
    sumOutputs (output ∷ rest) =
      outputForcingFull T R cutoff time output + sumOutputs rest

  integratedGlobalForcingFull :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → ℚ
  integratedGlobalForcingFull T R cutoff terminal =
    integrateTo (globalForcingFull T R cutoff) terminal

  record CommutatorOnlySpacetimeBudget568
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T) : Set₁ where
    field
      cutoffIndependentCommutatorBound568 : Time → ℚ
      liveCommutatorOnlyBudget568 :
        (cutoff : Nat) (terminal : Time) →
        R567.four567 * integratedGlobalForcingFull T R cutoff terminal
        ≤ cutoffIndependentCommutatorBound568 terminal

  open CommutatorOnlySpacetimeBudget568 public

------------------------------------------------------------------------
-- Exact relationship to the R503 consumer remains a two-step compiler:
--
--   commutator budget
--     + scalar FTC / favourable diagonal drop
--     + initial self-flux endpoint
--       -> bound on literal R406 remainder integral
--       -> R500 same-object identity
--       -> R503 DirectOffDiagonalBudget.
--
-- R568 freezes the genuinely new PDE coordinate but does not fabricate those
-- standard-analysis / endpoint receipts here.
------------------------------------------------------------------------

data R568Residual : Set where
  missingConcreteScalarFTC568 : R568Residual
  missingInitialSelfFluxLiveCalibration568 : R568Residual
  missingCutoffUniformLiveCommutatorSpacetimeBudget568 : R568Residual
  directR503BudgetClosed568 : R568Residual

currentR568Residual : R568Residual
currentR568Residual = missingConcreteScalarFTC568

-- Once ordinary FTC and endpoint calibration are treated as standard sourced
-- analysis/representation receipts, this is the sole NEW NS estimate.
newNSAnalyticResidual568 : R568Residual
newNSAnalyticResidual568 = missingCutoffUniformLiveCommutatorSpacetimeBudget568

round568AmplitudeSpacetimeLeafEliminated : Bool
round568AmplitudeSpacetimeLeafEliminated = true

round568NonseparableResolventStillBlocksR294 : Bool
round568NonseparableResolventStillBlocksR294 = false

round568DiagonalNonlinearEstimateStillIndependent : Bool
round568DiagonalNonlinearEstimateStillIndependent = false

round568NewNSAnalyticLeafIsLiveCommutatorSpacetimeBudget : Bool
round568NewNSAnalyticLeafIsLiveCommutatorSpacetimeBudget = true

round568LiveCommutatorSpacetimeBudgetClosed : Bool
round568LiveCommutatorSpacetimeBudgetClosed = false

round568DirectR503BudgetClosed : Bool
round568DirectR503BudgetClosed = false

round568CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round568CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round568ClayPromotion : Bool
round568ClayPromotion = false

round568AmplitudeSpacetimeLeafEliminatedIsTrue :
  round568AmplitudeSpacetimeLeafEliminated ≡ true
round568AmplitudeSpacetimeLeafEliminatedIsTrue = refl

round568NewNSAnalyticLeafIsLiveCommutatorSpacetimeBudgetIsTrue :
  round568NewNSAnalyticLeafIsLiveCommutatorSpacetimeBudget ≡ true
round568NewNSAnalyticLeafIsLiveCommutatorSpacetimeBudgetIsTrue = refl

round568LiveCommutatorSpacetimeBudgetClosedIsFalse :
  round568LiveCommutatorSpacetimeBudgetClosed ≡ false
round568LiveCommutatorSpacetimeBudgetClosedIsFalse = refl

round568ClayPromotionIsFalse : round568ClayPromotion ≡ false
round568ClayPromotionIsFalse = refl
