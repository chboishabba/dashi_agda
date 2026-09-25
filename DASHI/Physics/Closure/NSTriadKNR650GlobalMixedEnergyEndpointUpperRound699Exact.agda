{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650GlobalMixedEnergyEndpointUpperRound699Exact where

------------------------------------------------------------------------
-- ROUND699 / R691 ENDPOINT UPPER BOUND = INITIAL MIXED MASS ONLY
--
-- R691 gives
--
--   Weighted_N(T) = C_N(T) - [E_M,N(T) - E_M,N(0)].
--
-- Each fixed-output E_M,k(t) is the self-Hermitian mass
--
--   Re <M_k(t), M_k(t)> >= 0.
--
-- Therefore the terminal term has the favorable sign:
--
--   Weighted_N(T) <= C_N(T) + E_M,N(0).
--
-- Combining an R698 cutoff-uniform commutator payment with a cutoff-uniform
-- INITIAL mixed-mass ceiling gives a cutoff-uniform bound for the global
-- input-Laplacian / weighted-work side.  The initial ceiling is kept as a
-- standard-data receipt; no new nonlinear PDE estimate is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Canonical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyCalculusExact as Energy
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedEndpointCompilerExact as Endpoint
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNPhysicalDiagonalR298WeldRound451Exact as R451
import DASHI.Physics.Closure.NSTriadKNR650TriadOrbitSpacetimePaymentRound698Exact as R698

F : C3.RealField _
F = Rational.rationalRealField

module EndpointUpper
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
    (scalarScaleCalculus :
      R416.ScalarConstantDerivativeCalculus
        Time ScalarDerivativeOf)
    (FTC :
      R564.ScalarFundamentalTheorem564
        Time initialTime integrateTo ScalarDerivativeOf)
    (integrationLinearity :
      Energy.ScalarIntegrationLinearity Time integrateTo)
    (integrationTransport :
      R495.IntegrationTransportAuthority Time integrateTo)
    (D :
      R408.LiteralDynamics.LiteralRHSTrajectoryData
        Time initialTime integrateTo VectorDerivativeOf) where

  module Pay = R698.OrbitPayment
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus scalarScaleCalculus
    FTC integrationLinearity integrationTransport D

  module Balance = Pay.Balance

  sumSelfEnergy :
    Nat → Time → List Z3.FourierMode → ℚ
  sumSelfEnergy cutoff time [] = 0ℚ
  sumSelfEnergy cutoff time (output ∷ rest) =
    Balance.Local.End.selfEnergy cutoff output time
      + sumSelfEnergy cutoff time rest

  globalSelfEnergy :
    Nat → Time → ℚ
  globalSelfEnergy cutoff time =
    sumSelfEnergy cutoff time
      (Canonical.nonzeroCutoffModes cutoff)

  fixedOutputSelfEnergyNonnegative :
    (cutoff : Nat) (output : Z3.FourierMode) (time : Time) →
    0ℚ ≤ Balance.Local.End.selfEnergy cutoff output time
  fixedOutputSelfEnergyNonnegative cutoff output time =
    R451.selfHermitianNonnegative
      (Balance.Local.End.fixedOutputMixedCurve cutoff output time)

  sumSelfEnergyNonnegative :
    (cutoff : Nat) (time : Time) (outputs : List Z3.FourierMode) →
    0ℚ ≤ sumSelfEnergy cutoff time outputs
  sumSelfEnergyNonnegative cutoff time [] = ℚP.≤-refl
  sumSelfEnergyNonnegative cutoff time (output ∷ rest) =
    ℚP.+-mono-≤
      (fixedOutputSelfEnergyNonnegative cutoff output time)
      (sumSelfEnergyNonnegative cutoff time rest)

  endpointDeltaIsTerminalMinusInitial :
    (cutoff : Nat) (outputs : List Z3.FourierMode) (terminal : Time) →
    Balance.sumEndpointDelta cutoff outputs terminal
    ≡
    sumSelfEnergy cutoff terminal outputs
      - sumSelfEnergy cutoff initialTime outputs
  endpointDeltaIsTerminalMinusInitial cutoff [] terminal =
    solve []
  endpointDeltaIsTerminalMinusInitial
      cutoff (output ∷ rest) terminal =
    trans
      (cong₂ _+_
        refl
        (endpointDeltaIsTerminalMinusInitial cutoff rest terminal))
      (solve
        ( Balance.Local.End.selfEnergy cutoff output terminal
        ∷ Balance.Local.End.selfEnergy cutoff output initialTime
        ∷ sumSelfEnergy cutoff terminal rest
        ∷ sumSelfEnergy cutoff initialTime rest
        ∷ []))

  globalEndpointDeltaIsTerminalMinusInitial :
    (cutoff : Nat) (terminal : Time) →
    Balance.globalMixedEnergyEndpoint cutoff terminal
    ≡ globalSelfEnergy cutoff terminal - globalSelfEnergy cutoff initialTime
  globalEndpointDeltaIsTerminalMinusInitial cutoff terminal =
    endpointDeltaIsTerminalMinusInitial
      cutoff (Canonical.nonzeroCutoffModes cutoff) terminal

  globalWeightedBelowCommutatorPlusInitial :
    (cutoff : Nat) (terminal : Time) →
    Balance.globalIntegratedWeighted cutoff terminal
    ≤ Balance.globalIntegratedCommutator cutoff terminal
        + globalSelfEnergy cutoff initialTime
  globalWeightedBelowCommutatorPlusInitial cutoff terminal =
    let
      weighted = Balance.globalIntegratedWeighted cutoff terminal
      comm = Balance.globalIntegratedCommutator cutoff terminal
      terminalMass = globalSelfEnergy cutoff terminal
      initialMass = globalSelfEnergy cutoff initialTime

      exact :
        weighted ≡ comm - (terminalMass - initialMass)
      exact =
        trans
          (Balance.globalMixedEnergyBalance cutoff terminal)
          (cong₂ _-_
            refl
            (globalEndpointDeltaIsTerminalMinusInitial cutoff terminal))

      terminalNN : 0ℚ ≤ terminalMass
      terminalNN =
        sumSelfEnergyNonnegative
          cutoff terminal (Canonical.nonzeroCutoffModes cutoff)

      algebraicUpper :
        comm - (terminalMass - initialMass)
        ≤ comm + initialMass
      algebraicUpper =
        let
          cancelTerminal :
            comm + initialMass - terminalMass ≤ comm + initialMass
          cancelTerminal =
            ℚP.+-monoʳ-≤
              (comm + initialMass)
              (ℚP.neg-antimono-≤ terminalNN)
        in
        subst
          (λ left → left ≤ comm + initialMass)
          (solve (comm ∷ terminalMass ∷ initialMass ∷ []))
          cancelTerminal
    in
    subst
      (λ left → left ≤ comm + initialMass)
      (sym exact)
      algebraicUpper

  record CutoffUniformInitialMixedMassCeiling : Set₁ where
    field
      initialMixedMassBound : ℚ
      initialMixedMassCeiling :
        (cutoff : Nat) →
        globalSelfEnergy cutoff initialTime ≤ initialMixedMassBound

  open CutoffUniformInitialMixedMassCeiling public

  record CutoffUniformGlobalWeightedPayment : Set₁ where
    field
      cutoffIndependentBound : Time → ℚ
      globalWeightedPayment :
        (cutoff : Nat) (terminal : Time) →
        Balance.globalIntegratedWeighted cutoff terminal
        ≤ cutoffIndependentBound terminal

  open CutoffUniformGlobalWeightedPayment public

  commutatorAndInitialCeilingBuildGlobalWeightedPayment :
    Pay.CutoffUniformGlobalCommutatorPayment →
    CutoffUniformInitialMixedMassCeiling →
    CutoffUniformGlobalWeightedPayment
  commutatorAndInitialCeilingBuildGlobalWeightedPayment C I = record
    { CutoffUniformGlobalWeightedPayment.cutoffIndependentBound =
        λ terminal →
          Pay.CutoffUniformGlobalCommutatorPayment.cutoffIndependentBound
            C terminal
          + initialMixedMassBound I
    ; CutoffUniformGlobalWeightedPayment.globalWeightedPayment =
        λ cutoff terminal →
          ℚP.≤-trans
            (globalWeightedBelowCommutatorPlusInitial cutoff terminal)
            (ℚP.+-mono-≤
              (Pay.globalCommutatorPayment C cutoff terminal)
              (initialMixedMassCeiling I cutoff))
    }

  orbitAndInitialCeilingBuildGlobalWeightedPayment :
    Pay.CutoffUniformTriadOrbitSpacetimePayment →
    CutoffUniformInitialMixedMassCeiling →
    CutoffUniformGlobalWeightedPayment
  orbitAndInitialCeilingBuildGlobalWeightedPayment O I =
    commutatorAndInitialCeilingBuildGlobalWeightedPayment
      (Pay.orbitPaymentBuildsGlobalCommutatorPayment O) I

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round699TerminalMixedEnergyHasFavorableNonnegativeSign : Bool
round699TerminalMixedEnergyHasFavorableNonnegativeSign = true

round699R691EndpointReducesToInitialMixedMassForUpperBounds : Bool
round699R691EndpointReducesToInitialMixedMassForUpperBounds = true

round699OrbitPaymentPlusInitialCeilingPaysGlobalWeightedWork : Bool
round699OrbitPaymentPlusInitialCeilingPaysGlobalWeightedWork = true

round699InitialMixedMassCeilingIsNewNonlinearPDEEstimate : Bool
round699InitialMixedMassCeilingIsNewNonlinearPDEEstimate = false

round699CutoffUniformInitialMixedMassCeilingClosed : Bool
round699CutoffUniformInitialMixedMassCeilingClosed = false

round699IntroducesNSEstimate : Bool
round699IntroducesNSEstimate = false

round699C1Closed : Bool
round699C1Closed = false

round699C2Closed : Bool
round699C2Closed = false

round699ClayPromotion : Bool
round699ClayPromotion = false

round699TerminalMixedEnergyHasFavorableNonnegativeSignIsTrue :
  round699TerminalMixedEnergyHasFavorableNonnegativeSign ≡ true
round699TerminalMixedEnergyHasFavorableNonnegativeSignIsTrue = refl

round699R691EndpointReducesToInitialMixedMassForUpperBoundsIsTrue :
  round699R691EndpointReducesToInitialMixedMassForUpperBounds ≡ true
round699R691EndpointReducesToInitialMixedMassForUpperBoundsIsTrue = refl

round699OrbitPaymentPlusInitialCeilingPaysGlobalWeightedWorkIsTrue :
  round699OrbitPaymentPlusInitialCeilingPaysGlobalWeightedWork ≡ true
round699OrbitPaymentPlusInitialCeilingPaysGlobalWeightedWorkIsTrue = refl

round699InitialMixedMassCeilingIsNewNonlinearPDEEstimateIsFalse :
  round699InitialMixedMassCeilingIsNewNonlinearPDEEstimate ≡ false
round699InitialMixedMassCeilingIsNewNonlinearPDEEstimateIsFalse = refl

round699IntroducesNSEstimateIsFalse :
  round699IntroducesNSEstimate ≡ false
round699IntroducesNSEstimateIsFalse = refl

round699C1ClosedIsFalse :
  round699C1Closed ≡ false
round699C1ClosedIsFalse = refl

round699C2ClosedIsFalse :
  round699C2Closed ≡ false
round699C2ClosedIsFalse = refl

round699ClayPromotionIsFalse :
  round699ClayPromotion ≡ false
round699ClayPromotionIsFalse = refl
