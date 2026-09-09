module DASHI.Physics.Closure.NSTriadKNFactoredFullCommutatorBudgetBidiRound570Exact where

------------------------------------------------------------------------
-- ROUND570 / BIDI: EXISTING LITERAL FACTORED-FULL A1 CONSUMER
--                    = FOUR TIMES THE COMMUTATOR-ONLY FULL SQUARE
--
-- The concurrent R567 consumer freezes the theorem-facing analytic debt as
--
--   ∫ factoredFull(N,t) dt <= B(T).
--
-- Our R567 proves, at one fixed output and one live physical slice,
--
--   factoredFull_k = 4 * forcingFull_k,
--
-- after the amplitude half is removed by exact square transposition (R566).
-- R228 already proves that the stored cutoff of `systemAt N t` is literally N,
-- so no hidden cutoff-reindexing premise is required.
--
-- This owner lifts the fixed-output identity over the canonical output list,
-- transports it through the existing R495 integration authority, and proves
-- that a commutator-only spacetime budget inhabits the PRE-EXISTING literal
-- factored-full budget record.  Hence there is one A1 consumer, not two.
--
-- No analytic estimate is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNFixedOutputLiveGlobalFluxRound406Exact as R406
import DASHI.Physics.Closure.NSTriadKNLiveR406DiagonalReducedNormalFormRound556Exact as R556
import DASHI.Physics.Closure.NSTriadKNLiveIntegratedDiagonalReducedNormalFormRound557Exact as R557
import DASHI.Physics.Closure.NSTriadKNFactoredFullCommutatorOnlyRound567Exact as C567
import DASHI.Physics.Closure.NSTriadKNLiveCommutatorOnlyLeafABoundaryRound568Exact as C568
import DASHI.Physics.Closure.NSTriadKNLiteralFactoredFullSpacetimeBudgetRound567Exact as B567
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNDirectResolventIntegratedCompanionRound500Exact as R500
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

F : C3.RealField _
F = Rational.rationalRealField

module Bidi
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
  module Reduced = R556.LiveReduced
    Time initialTime integrateTo DerivativeOf
  module Live = R557.LiveIntegrated
    Time initialTime integrateTo DerivativeOf integration
  module Comm = C568.LiveCommutatorOnly
    Time initialTime integrateTo DerivativeOf integration
  module Existing = B567.ExactFactoredBudget
    Time initialTime integrateTo DerivativeOf integration
  module Int = R500.IntegratedDirect
    Time initialTime integrateTo DerivativeOf integration

  ----------------------------------------------------------------------
  -- 1. One live output: external cutoff N = system's stored cutoff.
  ----------------------------------------------------------------------

  outputFactoredIsFourForcing :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) (time : Time) (output : Z3.FourierMode) →
    let
      module At = Reduced.At T R cutoff time
      module C = C567.CommutatorOnly At.Slice.PS At.S
    in
    C.NF.factoredFull output (Output.physicalOutputFiber cutoff output)
    ≡ C567.four567 * Comm.outputForcingFull T R cutoff time output
  outputFactoredIsFourForcing T R cutoff time output =
    let
      module At = Reduced.At T R cutoff time
      module C = C567.CommutatorOnly At.Slice.PS At.S

      cutoffExact :
        Audit.cutoff (AuditSystem At.Slice.PS) ≡ cutoff
      cutoffExact =
        Dyn.Base.systemCutoffAgreement (Dyn.forgetDynamics T) cutoff time

      atStoredCutoff :
        C.NF.factoredFull output
          (Output.physicalOutputFiber (Audit.cutoff (AuditSystem At.Slice.PS)) output)
        ≡ C567.four567 *
          DASHI.Physics.Closure.NSTriadKNFullSquareDiagonalOffDiagonalRound543Exact.fullSquareSum
            C.T.forcingPair
            (Output.physicalOutputFiber (Audit.cutoff (AuditSystem At.Slice.PS)) output)
      atStoredCutoff = C.factoredFullIsFourForcingFull output
    in
    subst
      (λ selectedCutoff →
        C.NF.factoredFull output
          (Output.physicalOutputFiber selectedCutoff output)
        ≡ C567.four567 *
          DASHI.Physics.Closure.NSTriadKNFullSquareDiagonalOffDiagonalRound543Exact.fullSquareSum
            C.T.forcingPair
            (Output.physicalOutputFiber selectedCutoff output))
      cutoffExact
      atStoredCutoff
    where
    AuditSystem :
      DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact.PhysicalFiniteComplex3GalerkinSystem F →
      Audit.FiniteComplex3GalerkinSystem F
        (Dyn.Base.E (Dyn.forgetDynamics T))
        (Dyn.Base.I (Dyn.forgetDynamics T))
    AuditSystem PS =
      DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact.finiteSystem PS

  ----------------------------------------------------------------------
  -- 2. Lift over exactly the canonical output list used by R556/R557.
  ----------------------------------------------------------------------

  factoredListIsFourForcing :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) (time : Time) →
    (selected : List Z3.FourierMode) →
    let module At = Reduced.At T R cutoff time in
    (nonzero : At.GR.OutputsNonzero selected) →
    At.GR.globalFactoredFull cutoff selected nonzero
    ≡ C567.four567 * Comm.sumOutputForcingFull T R cutoff time selected
  factoredListIsFourForcing T R cutoff time [] nonzero = refl
  factoredListIsFourForcing T R cutoff time (output ∷ rest)
      (R556.LiveReduced.At.GR.nonzeroCons outputNonzero tailNonzero) =
    let
      module At = Reduced.At T R cutoff time
      head = outputFactoredIsFourForcing T R cutoff time output
      tail = factoredListIsFourForcing T R cutoff time rest tailNonzero
    in
    trans
      (congAdd head tail)
      (solve
        ( Comm.outputForcingFull T R cutoff time output
        ∷ Comm.sumOutputForcingFull T R cutoff time rest
        ∷ []))
    where
    congAdd : ∀ {a b c d : ℚ} → a ≡ b → c ≡ d → a + c ≡ b + d
    congAdd refl refl = refl

  liveFactoredIsFourGlobalForcing :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) (time : Time) →
    Live.factoredFull T R cutoff time
    ≡ C567.four567 * Comm.globalForcingFull T R cutoff time
  liveFactoredIsFourGlobalForcing T R cutoff time =
    let
      module At = Reduced.At T R cutoff time
    in
    factoredListIsFourForcing T R cutoff time
      At.Slice.outputs At.canonicalOutputsNonzero

  ----------------------------------------------------------------------
  -- 3. Same-object identity after integration.
  ----------------------------------------------------------------------

  integratedFactoredIsFourIntegratedForcing :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) (terminal : Time) →
    integrateTo (Live.factoredFull T R cutoff) terminal
    ≡ C567.four567 * Comm.integratedGlobalForcingFull T R cutoff terminal
  integratedFactoredIsFourIntegratedForcing T R cutoff terminal =
    trans
      (R495.integrateCongruent integration
        (Live.factoredFull T R cutoff)
        (λ time → C567.four567 * Comm.globalForcingFull T R cutoff time)
        (liveFactoredIsFourGlobalForcing T R cutoff)
        terminal)
      (Int.integrateFour (Comm.globalForcingFull T R cutoff) terminal)

  ----------------------------------------------------------------------
  -- 4. BIDI consumer compiler: commutator-only budget pays existing A1.
  ----------------------------------------------------------------------

  commutatorBudgetBuildsExistingFactoredBudget :
    ∀ {T R} →
    Comm.CommutatorOnlySpacetimeBudget568 T R →
    Existing.LiteralFactoredFullSpacetimeBudget567 T R
  commutatorBudgetBuildsExistingFactoredBudget {T} {R} P =
    B567.literal-factored-full-spacetime-budget-567
      (Comm.cutoffIndependentCommutatorBound568 P)
      (λ cutoff terminal →
        subst
          (λ lhs →
            lhs ≤ Comm.cutoffIndependentCommutatorBound568 P terminal)
          (sym (integratedFactoredIsFourIntegratedForcing T R cutoff terminal))
          (Comm.liveCommutatorOnlyBudget568 P cutoff terminal))

------------------------------------------------------------------------
-- Status / proof-search reconciliation.
------------------------------------------------------------------------

round570CutoffSameObjectReceiptReused : Bool
round570CutoffSameObjectReceiptReused = true

round570LiteralFactoredFullIsFourCommutatorOnlyPointwise : Bool
round570LiteralFactoredFullIsFourCommutatorOnlyPointwise = true

round570LiteralFactoredFullIsFourCommutatorOnlyIntegrated : Bool
round570LiteralFactoredFullIsFourCommutatorOnlyIntegrated = true

round570CommutatorBudgetPaysExistingFactoredConsumer : Bool
round570CommutatorBudgetPaysExistingFactoredConsumer = true

round570ParallelA1ConsumersRemain : Bool
round570ParallelA1ConsumersRemain = false

round570IntroducesNewAnalyticEstimate : Bool
round570IntroducesNewAnalyticEstimate = false

round570LiveCommutatorSpacetimeBudgetClosed : Bool
round570LiveCommutatorSpacetimeBudgetClosed = false

round570CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round570CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round570ClayPromotion : Bool
round570ClayPromotion = false

round570CommutatorBudgetPaysExistingFactoredConsumerIsTrue :
  round570CommutatorBudgetPaysExistingFactoredConsumer ≡ true
round570CommutatorBudgetPaysExistingFactoredConsumerIsTrue = refl

round570ParallelA1ConsumersRemainIsFalse :
  round570ParallelA1ConsumersRemain ≡ false
round570ParallelA1ConsumersRemainIsFalse = refl

round570ClayPromotionIsFalse : round570ClayPromotion ≡ false
round570ClayPromotionIsFalse = refl
