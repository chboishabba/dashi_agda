{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650IntegratedNestedFourHelicityOrbitRound701Exact where

------------------------------------------------------------------------
-- ROUND701 / SPACETIME PAYMENT ON THE FULLY EXPANDED NESTED FOUR-HELICITY
--            COMPLETE-TRIAD ORBIT
--
-- R700 is instantaneous:
--
--   NestedOrbit_N(t) = 12 * C_N(t).
--
-- This owner instantiates that identity on the literal R408 trajectory, uses
-- R697's already-proved static-to-live global commutator identification, and
-- transports only the resulting GLOBAL scalar through time integration:
--
--   integral NestedOrbit_N(t) dt = 12 * C_N(T).
--
-- Hence the Clay-facing analytic theorem may be stated directly as
--
--   integral NestedOrbit_N(t) dt <= 12 * B(T),
--
-- with B independent of N.  Positivity of 12 cancels the fixed factor and
-- yields the exact R691 global commutator budget.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
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
import DASHI.Physics.Closure.NSTriadKNR650IntegratedTriadOrbitResidueRound697Exact as R697
import DASHI.Physics.Closure.NSTriadKNR650NestedFourHelicityTriadOrbitRound700Exact as R700

F : C3.RealField _
F = Rational.rationalRealField

twelvePositive : 0ℚ < R700.twelve
twelvePositive = ℚP.positive⁻¹ R700.twelve

module IntegratedNestedOrbit
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

  module Live = R408.LiteralDynamics
    Time initialTime integrateTo VectorDerivativeOf

  module Orbit = R697.IntegratedOrbit
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus scalarScaleCalculus
    FTC integrationLinearity integrationTransport D

  module Balance = Orbit.Balance

  state = Live.stateTrajectory (Live.support D)
  S = Live.Base.S state
  L = Live.Base.L state
  H = Live.Base.H state

  module At
      (cutoff : Nat)
      (time : Time) where

    physicalSystem =
      Live.physicalSystemAt (Live.support D) cutoff time

    allModeTransverse :
      (mode : Z3.FourierMode) →
      _
    allModeTransverse mode =
      Live.Base.velocityTransverse state cutoff time mode

    module Nested =
      R700.NestedOrbit physicalSystem S L H allModeTransverse

    nestedOrbitResidue : ℚ
    nestedOrbitResidue =
      R38.foldPower Nested.nestedTriadOrbitResidue
        (Physical.physicalTriadEnumeration cutoff)

    nestedOrbitResidueIsTwelveLiveCommutator :
      nestedOrbitResidue
      ≡
      R700.twelve * Orbit.sumCommutatorAt cutoff
        (DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact.nonzeroCutoffModes cutoff)
        time
    nestedOrbitResidueIsTwelveLiveCommutator =
      trans
        Nested.completeNestedTriadOrbitResidueIsTwelveCoherentCommutator
        (cong
          (R700.twelve *_)
          (Orbit.At.selectedStaticGlobalIsLive cutoff time))

  nestedOrbitResidueAt :
    Nat → Time → ℚ
  nestedOrbitResidueAt cutoff time =
    At.nestedOrbitResidue cutoff time

  integratedNestedOrbitResidue :
    Nat → Time → ℚ
  integratedNestedOrbitResidue cutoff terminal =
    integrateTo (nestedOrbitResidueAt cutoff) terminal

  integratedNestedOrbitResidueIsTwelveR691Commutator :
    (cutoff : Nat) (terminal : Time) →
    integratedNestedOrbitResidue cutoff terminal
    ≡ R700.twelve * Balance.globalIntegratedCommutator cutoff terminal
  integratedNestedOrbitResidueIsTwelveR691Commutator cutoff terminal =
    let
      outputs =
        DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact.nonzeroCutoffModes cutoff
      liveSum = Orbit.sumCommutatorAt cutoff outputs
    in
    trans
      (Energy.integrationCongruent integrationLinearity
        (At.nestedOrbitResidueIsTwelveLiveCommutator cutoff)
        terminal)
      (trans
        (Energy.integrationConstantScale integrationLinearity
          R700.twelve liveSum terminal)
        (cong
          (R700.twelve *_)
          (Orbit.sumCommutatorAtIntegratesToR691
            cutoff outputs terminal)))

  record CutoffUniformNestedFourHelicityOrbitPayment : Set₁ where
    field
      cutoffIndependentBound : Time → ℚ
      nestedOrbitSpacetimePayment :
        (cutoff : Nat) (terminal : Time) →
        integratedNestedOrbitResidue cutoff terminal
        ≤ R700.twelve * cutoffIndependentBound terminal

  open CutoffUniformNestedFourHelicityOrbitPayment public

  record CutoffUniformGlobalCommutatorPayment : Set₁ where
    field
      cutoffIndependentBound : Time → ℚ
      globalCommutatorPayment :
        (cutoff : Nat) (terminal : Time) →
        Balance.globalIntegratedCommutator cutoff terminal
        ≤ cutoffIndependentBound terminal

  open CutoffUniformGlobalCommutatorPayment public

  nestedOrbitPaymentBuildsR691GlobalCommutatorPayment :
    CutoffUniformNestedFourHelicityOrbitPayment →
    CutoffUniformGlobalCommutatorPayment
  nestedOrbitPaymentBuildsR691GlobalCommutatorPayment P = record
    { CutoffUniformGlobalCommutatorPayment.cutoffIndependentBound =
        CutoffUniformNestedFourHelicityOrbitPayment.cutoffIndependentBound P
    ; CutoffUniformGlobalCommutatorPayment.globalCommutatorPayment =
        λ cutoff terminal →
          let
            comm = Balance.globalIntegratedCommutator cutoff terminal
            bound =
              CutoffUniformNestedFourHelicityOrbitPayment.cutoffIndependentBound
                P terminal

            twelveCommUpper :
              R700.twelve * comm ≤ R700.twelve * bound
            twelveCommUpper =
              subst
                (λ left → left ≤ R700.twelve * bound)
                (integratedNestedOrbitResidueIsTwelveR691Commutator
                  cutoff terminal)
                (nestedOrbitSpacetimePayment P cutoff terminal)
          in
          ℚP.*-cancelˡ-≤-pos
            R700.twelve twelveCommUpper
    }

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round701LiteralNestedFourHelicityOrbitIntegratedBeforeEstimate : Bool
round701LiteralNestedFourHelicityOrbitIntegratedBeforeEstimate = true

round701IntegratedNestedOrbitIsTwelveR691Commutator : Bool
round701IntegratedNestedOrbitIsTwelveR691Commutator = true

round701ClayFacingPaymentLivesOnFullyExpandedIncidenceKernel : Bool
round701ClayFacingPaymentLivesOnFullyExpandedIncidenceKernel = true

round701NestedOrbitPaymentCompilesToR691GlobalCommutator : Bool
round701NestedOrbitPaymentCompilesToR691GlobalCommutator = true

round701IntroducesEstimate : Bool
round701IntroducesEstimate = false

round701CutoffUniformNestedFourHelicityOrbitPaymentClosed : Bool
round701CutoffUniformNestedFourHelicityOrbitPaymentClosed = false

round701ClayPromotion : Bool
round701ClayPromotion = false

round701LiteralNestedFourHelicityOrbitIntegratedBeforeEstimateIsTrue :
  round701LiteralNestedFourHelicityOrbitIntegratedBeforeEstimate ≡ true
round701LiteralNestedFourHelicityOrbitIntegratedBeforeEstimateIsTrue = refl

round701IntegratedNestedOrbitIsTwelveR691CommutatorIsTrue :
  round701IntegratedNestedOrbitIsTwelveR691Commutator ≡ true
round701IntegratedNestedOrbitIsTwelveR691CommutatorIsTrue = refl

round701ClayFacingPaymentLivesOnFullyExpandedIncidenceKernelIsTrue :
  round701ClayFacingPaymentLivesOnFullyExpandedIncidenceKernel ≡ true
round701ClayFacingPaymentLivesOnFullyExpandedIncidenceKernelIsTrue = refl

round701NestedOrbitPaymentCompilesToR691GlobalCommutatorIsTrue :
  round701NestedOrbitPaymentCompilesToR691GlobalCommutator ≡ true
round701NestedOrbitPaymentCompilesToR691GlobalCommutatorIsTrue = refl

round701IntroducesEstimateIsFalse :
  round701IntroducesEstimate ≡ false
round701IntroducesEstimateIsFalse = refl

round701CutoffUniformNestedFourHelicityOrbitPaymentClosedIsFalse :
  round701CutoffUniformNestedFourHelicityOrbitPaymentClosed ≡ false
round701CutoffUniformNestedFourHelicityOrbitPaymentClosedIsFalse = refl

round701ClayPromotionIsFalse :
  round701ClayPromotion ≡ false
round701ClayPromotionIsFalse = refl
