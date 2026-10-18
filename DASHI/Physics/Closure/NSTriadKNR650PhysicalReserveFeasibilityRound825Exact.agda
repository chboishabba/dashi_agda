{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650PhysicalReserveFeasibilityRound825Exact where

------------------------------------------------------------------------
-- R825 / COMPLETE PHYSICAL INTEGRATED FEASIBILITY AND FALSIFIER
--
-- Carries the exact R824 original-incidence CC split and R823 rate through
-- R823's SAME rational integration authority:
--   signed integral = quadratic + high - low.
-- At a concrete live packet and terminal, rational <= decision yields either
-- an actual payment certificate or its negation. This alone does NOT construct
-- a concrete bad datum or discharge the universal B-RESERVE inequality.
-- No new abstract payment token or new B barrier compiler is introduced.
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

import DASHI.Physics.Closure.NSTriadKNR650SignedComparableReserveRound823Exact as R823
import DASHI.Physics.Closure.NSTriadKNR650SwapPairedResidualCarrierRound760Exact as R760
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNR650CriticalProductionIncidenceCarrierRound744Exact as R744
import DASHI.Physics.Closure.NSTriadKNR650OrbitProfileTwoFamilyResidualRound781Exact as R781

import DASHI.Physics.Closure.NSTriadKNR650PhysicalCCGradedReserveRound824Exact as R824

module PhysicalReserveFeasibility
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








  module Graded =
    R824.PhysicalCCGradedReserve
      Time initialTime integrateTo
      VectorDerivativeOf ScalarDerivativeOf
      projectedCross vectorAlgebra zeroCalculus
      hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
      FTC integrationLinearity integrationTransport D C R

  module Live = Graded.Live
  module Packet = Live.Packet

  quadraticIntegral :
    (cutoff : Nat) →
    Packet.LivePhysicalPacketStructure D C cutoff →
    Time → ℚ
  quadraticIntegral cutoff S terminal =
    integrateTo
      (λ time → Graded.At.fullQuadratic cutoff time S)
      terminal

  highIntegral :
    (cutoff : Nat) →
    Packet.LivePhysicalPacketStructure D C cutoff →
    Time → ℚ
  highIntegral cutoff S terminal =
    integrateTo
      (λ time → Graded.At.fullHigh cutoff time S)
      terminal

  lowIntegral :
    (cutoff : Nat) →
    Packet.LivePhysicalPacketStructure D C cutoff →
    Time → ℚ
  lowIntegral cutoff S terminal =
    integrateTo
      (λ time → Graded.At.fullLow cutoff time S)
      terminal

  -- The full three-way decomposition is on the same R823 packet and
  -- integration authority. The CC contribution has NOT been given a
  -- synthetic sign or re-evaluated on a comparable representative.
  integratedCompleteGraded :
    (cutoff : Nat) →
    (S : Packet.LivePhysicalPacketStructure D C cutoff) →
    (terminal : Time) →
    Live.integratedCompleteRate cutoff S terminal
      ≡
      quadraticIntegral cutoff S terminal
        + highIntegral cutoff S terminal
        - lowIntegral cutoff S terminal
  integratedCompleteGraded cutoff S terminal =
    let
      v = quadraticIntegral cutoff S terminal
      h = highIntegral cutoff S terminal
      l = lowIntegral cutoff S terminal
      matched =
        Energy.integrationCongruent integrationLinearity
          (λ time → Graded.At.actualCompleteRateGraded cutoff time S)
          terminal
      linear =
        Energy.integrationAdditive integrationLinearity
          (λ time →
            Graded.At.fullQuadratic cutoff time S
              + Graded.At.fullHigh cutoff time S)
          (λ time → - Graded.At.fullLow cutoff time S)
          terminal
      inner =
        Energy.integrationAdditive integrationLinearity
          (λ time → Graded.At.fullQuadratic cutoff time S)
          (λ time → Graded.At.fullHigh cutoff time S)
          terminal
      neg =
        Energy.integrationConstantScale integrationLinearity
          (- 1ℚ)
          (λ time → Graded.At.fullLow cutoff time S)
          terminal
    in
    trans matched
      (trans
        (Energy.integrationCongruent integrationLinearity
          (λ time →
            solve
              ( Graded.At.fullQuadratic cutoff time S
              ∷ Graded.At.fullHigh cutoff time S
              ∷ Graded.At.fullLow cutoff time S
              ∷ []))
          terminal)
        (trans linear
          (trans
            (cong₂ _+_ inner neg)
            (solve (v ∷ h ∷ l ∷ [])))))

  -- One direction of the exact feasible-payment equivalence. R823 already
  -- owns the terminal compiler;
  -- this theorem does not produce either side of the required inequality.
  gradedReservePaysComplete :
    (cutoff : Nat) →
    (S : Packet.LivePhysicalPacketStructure D C cutoff) →
    (terminal : Time) →
    lowIntegral cutoff S terminal
      ≤ quadraticIntegral cutoff S terminal
          + highIntegral cutoff S terminal →
    0ℚ ≤ Live.integratedCompleteRate cutoff S terminal
  gradedReservePaysComplete cutoff S terminal bound =
    let
      v = quadraticIntegral cutoff S terminal
      h = highIntegral cutoff S terminal
      l = lowIntegral cutoff S terminal
      shifted =
        ℚP.+-mono-≤ bound ℚP.≤-refl
      normalized :
        0ℚ ≤ v + h - l
      normalized =
        subst
          (λ left → left ≤ v + h - l)
          (solve (l ∷ []))
          (subst
            (λ right → l + (- l) ≤ right)
            (solve (v ∷ h ∷ l ∷ []))
            shifted)
    in
    subst (0ℚ ≤_)
      (sym (integratedCompleteGraded cutoff S terminal))
      normalized

  -- Converse: the graded inequality is not a gratuitously stronger
  -- sufficient condition. It is equivalent to the very same R823 payment.
  completePaymentRequiresGradedReserve :
    (cutoff : Nat) →
    (S : Packet.LivePhysicalPacketStructure D C cutoff) →
    (terminal : Time) →
    0ℚ ≤ Live.integratedCompleteRate cutoff S terminal →
    lowIntegral cutoff S terminal
      ≤ quadraticIntegral cutoff S terminal
          + highIntegral cutoff S terminal
  completePaymentRequiresGradedReserve cutoff S terminal payment =
    let
      v = quadraticIntegral cutoff S terminal
      h = highIntegral cutoff S terminal
      l = lowIntegral cutoff S terminal

      gradedNonnegative : 0ℚ ≤ v + h - l
      gradedNonnegative =
        subst (0ℚ ≤_)
          (integratedCompleteGraded cutoff S terminal)
          payment

      shifted =
        ℚP.+-mono-≤ gradedNonnegative ℚP.≤-refl
    in
    subst
      (λ right → l ≤ right)
      (solve (v ∷ h ∷ l ∷ []))
      (subst
        (λ left → left ≤ (v + h - l) + l)
        (solve (l ∷ []))
        shifted)

  -- A concrete strict graded counterexample *on the live physical packet*
  -- would rule out the claimed nonnegative complete integrated rate. This is
  -- a falsification implication, not a produced counterexample.
  physicalGradedFailureRefutesCompletePayment :
    (cutoff : Nat) →
    (S : Packet.LivePhysicalPacketStructure D C cutoff) →
    (terminal : Time) →
    quadraticIntegral cutoff S terminal
      + highIntegral cutoff S terminal
      < lowIntegral cutoff S terminal →
    ¬ (0ℚ ≤ Live.integratedCompleteRate cutoff S terminal)
  physicalGradedFailureRefutesCompletePayment cutoff S terminal strict payment =
    ℚP.<⇒≱ strict
      (completePaymentRequiresGradedReserve cutoff S terminal payment)

  -- Rational integration here is an input of the SAME actual R408
  -- integration authority.  Once the caller supplies an evaluated physical
  -- packet and terminal, the result is a decidable certificate, not a
  -- synthetic boolean or a replacement integral.
  data PhysicalReserveVerdict
      (cutoff : Nat)
      (S : Packet.LivePhysicalPacketStructure D C cutoff)
      (terminal : Time) : Set where
    paid :
      Live.integratedDemand cutoff S terminal
        ≤ Live.integratedReserve cutoff S terminal →
      PhysicalReserveVerdict cutoff S terminal
    refuted :
      ¬ (Live.integratedDemand cutoff S terminal
        ≤ Live.integratedReserve cutoff S terminal) →
      PhysicalReserveVerdict cutoff S terminal

  decideActualReserve :
    (cutoff : Nat) →
    (S : Packet.LivePhysicalPacketStructure D C cutoff) →
    (terminal : Time) →
    PhysicalReserveVerdict cutoff S terminal
  decideActualReserve cutoff S terminal
    with ℚP._≤?_
      (Live.integratedDemand cutoff S terminal)
      (Live.integratedReserve cutoff S terminal)
  ... | yes payment = paid payment
  ... | no counterexample = refuted counterexample

  -- A concrete *physical* finite-Galerkin witness satisfying this strict
  -- reverse inequality would refute the universal R823 reserve claim.
  -- No such witness is assumed or asserted to exist.
  physicalReserveFalsifier :
    (cutoff : Nat) →
    (S : Packet.LivePhysicalPacketStructure D C cutoff) →
    (terminal : Time) →
    Live.integratedReserve cutoff S terminal
      < Live.integratedDemand cutoff S terminal →
    ¬ (Live.integratedDemand cutoff S terminal
      ≤ Live.integratedReserve cutoff S terminal)
  physicalReserveFalsifier cutoff S terminal bad =
    ℚP.<⇒≱ bad

round825OriginalCCAndSeparatedCompleteGrading : Bool
round825OriginalCCAndSeparatedCompleteGrading = true

round825IntegratedPhysicalFeasibilityShape : Bool
round825IntegratedPhysicalFeasibilityShape = true

round825StrictPhysicalCounterexampleConstructed : Bool
round825StrictPhysicalCounterexampleConstructed = false

round825SignedReserveProved : Bool
round825SignedReserveProved = false

round825W1Proved : Bool
round825W1Proved = false

round825ContinuumContinuationProved : Bool
round825ContinuumContinuationProved = false

round825ClayPromotion : Bool
round825ClayPromotion = false
