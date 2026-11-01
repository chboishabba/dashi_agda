module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406EndpointSplitMaxCutExact where

------------------------------------------------------------------------
-- POSITIVE B7 Q4+E / ENDPOINT-INCREMENT SPLIT
--
-- The Q4+E endpoint leaf is
--
--   F_N(T) - F_N(0) <= E(T).
--
-- It is not necessary to estimate that increment as a single opaque object.
-- If, on the SAME literal R406 off-diagonal flux curve,
--
--   F_N(T)       <= E_plus(T),
--   -F_N(0)      <= E_minus,
--
-- then
--
--   F_N(T)-F_N(0) <= E_plus(T)+E_minus.
--
-- This file compiles those one-sided bounds together with the already-built
-- literal derivative/FTC compiler.  Existing source R463 supplies a
-- cutoff-cardinality-free NEGATIVE-orientation Cauchy/energy-square producer;
-- R461 reduces the POSITIVE orientation to a finite amplitude-square producer.
-- Thus the genuinely new endpoint analysis is concentrated on a uniform
-- positive terminal amplitude/flux bound, not on the subtraction algebra.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxFiniteDerivativeCompilerRound412Exact as R412
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNDirectResolventGramFluxNormalFormExact as Q4E
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406Q4EFTCCompilerMaxCutExact as FTCCompiler
import DASHI.Physics.Closure.NSTriadKNGlobalCauchyTerminalEndpointRound463Exact as R463
import DASHI.Physics.Closure.NSTriadKNCauchyInitialAmplitudeEndpointRound461Exact as R461

F : C3.RealField _
F = Rational.rationalRealField

module EndpointSplit
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (VectorDerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf : (Time → ℚ) → (Time → ℚ) → Set)
    (projectedCross : R426.ProjectedCrossDerivativeCalculus Time VectorDerivativeOf)
    (vectorAlgebra : R425.VectorDerivativeAlgebra Time VectorDerivativeOf)
    (hermitianCalculus :
      R417.HermitianDerivativeCalculus
        Time VectorDerivativeOf ScalarDerivativeOf)
    (constantCalculus :
      R416.ScalarConstantDerivativeCalculus Time ScalarDerivativeOf)
    (scalarAlgebra :
      R412.ScalarDerivativeAlgebra Time ScalarDerivativeOf)
    (integration : R495.IntegrationTransportAuthority Time integrateTo)
    (FTC : R564.ScalarFundamentalTheorem564
      Time initialTime integrateTo ScalarDerivativeOf)
    (D : R408.LiteralDynamics.LiteralRHSTrajectoryData
      Time initialTime integrateTo VectorDerivativeOf)
    (R : R405.LiteralCutoffSupport.LiteralNonzeroCutoffTrajectory
      Time initialTime integrateTo VectorDerivativeOf
      (R408.LiteralDynamics.literalPhysicalTrajectory
        Time initialTime integrateTo VectorDerivativeOf D)) where

  module Literal = R408.LiteralDynamics
    Time initialTime integrateTo VectorDerivativeOf

  module C = FTCCompiler.Q4EFTCCompiler
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra hermitianCalculus
    constantCalculus scalarAlgebra integration FTC D R

  module LiveQ4E = Q4E.LiveNormalForm
    Time initialTime integrateTo VectorDerivativeOf integration

  T = Literal.literalPhysicalTrajectory D

  record SplitQ4EAnalyticBounds : Set₁ where
    field
      cutoffIndependentGramBound : Time → ℚ
      integratedGramBudget :
        (cutoff : Nat) (terminal : Time) →
        LiveQ4E.integratedOffDiagonalGram T R cutoff terminal
        ≤ cutoffIndependentGramBound terminal

      positiveTerminalFluxBound : Time → ℚ
      negativeInitialFluxBound : ℚ

      positiveTerminalFluxBudget :
        (cutoff : Nat) (terminal : Time) →
        LiveQ4E.offDiagonalFluxAt T R cutoff terminal
        ≤ positiveTerminalFluxBound terminal

      negativeInitialFluxBudget :
        (cutoff : Nat) →
        0ℚ - LiveQ4E.offDiagonalFluxAt T R cutoff initialTime
        ≤ negativeInitialFluxBound

  open SplitQ4EAnalyticBounds public

  endpointBound : SplitQ4EAnalyticBounds → Time → ℚ
  endpointBound B terminal =
    positiveTerminalFluxBound B terminal + negativeInitialFluxBound B

  endpointIncrementPaid :
    (B : SplitQ4EAnalyticBounds) →
    (cutoff : Nat) (terminal : Time) →
    LiveQ4E.offDiagonalFluxAt T R cutoff terminal
      - LiveQ4E.offDiagonalFluxAt T R cutoff initialTime
    ≤ endpointBound B terminal
  endpointIncrementPaid B cutoff terminal =
    let
      terminalFlux = LiveQ4E.offDiagonalFluxAt T R cutoff terminal
      initialFlux = LiveQ4E.offDiagonalFluxAt T R cutoff initialTime

      added :
        terminalFlux + (0ℚ - initialFlux)
        ≤ positiveTerminalFluxBound B terminal + negativeInitialFluxBound B
      added = ℚP.+-mono-≤
        (positiveTerminalFluxBudget B cutoff terminal)
        (negativeInitialFluxBudget B cutoff)

      lhsMeaning :
        terminalFlux - initialFlux
        ≡ terminalFlux + (0ℚ - initialFlux)
      lhsMeaning = solve (terminalFlux ∷ initialFlux ∷ [])
    in
    subst
      (_≤ endpointBound B terminal)
      (symEq lhsMeaning)
      added
    where
    symEq : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
    symEq refl = refl

  splitBoundsBuildQ4EAnalyticBounds :
    SplitQ4EAnalyticBounds → C.Q4EAnalyticBounds
  splitBoundsBuildQ4EAnalyticBounds B = record
    { C.cutoffIndependentGramBound = cutoffIndependentGramBound B
    ; C.integratedGramBudget = integratedGramBudget B
    ; C.cutoffIndependentFluxEndpointBound = endpointBound B
    ; C.fluxEndpointBudget = endpointIncrementPaid B
    }

  splitBoundsBuildDirectGramFluxBudget :
    SplitQ4EAnalyticBounds → LiveQ4E.DirectGramFluxBudget T R
  splitBoundsBuildDirectGramFluxBudget B =
    C.analyticBoundsBuildDirectGramFluxBudget
      (splitBoundsBuildQ4EAnalyticBounds B)

------------------------------------------------------------------------
-- Status / cross-pollination boundary.
------------------------------------------------------------------------

q4eEndpointIncrementSplitCompilerClosed : Bool
q4eEndpointIncrementSplitCompilerClosed = true

q4eNegativeEndpointOrientationProducerExists : Bool
q4eNegativeEndpointOrientationProducerExists =
  R463.round463GlobalR398NegativeFluxEndpointPaid

q4ePositiveEndpointReducedToAmplitudeSquare : Bool
q4ePositiveEndpointReducedToAmplitudeSquare =
  R461.round461LiteralR447PositiveEndpointReducedToAmplitudeSquare

q4ePositiveTerminalFluxUniformBoundClosedHere : Bool
q4ePositiveTerminalFluxUniformBoundClosedHere = false

q4eEndpointSplitIntroducesEstimate : Bool
q4eEndpointSplitIntroducesEstimate = false

clayPromotion : Bool
clayPromotion = false

q4eEndpointIncrementSplitCompilerClosedIsTrue :
  q4eEndpointIncrementSplitCompilerClosed ≡ true
q4eEndpointIncrementSplitCompilerClosedIsTrue = refl

q4eNegativeEndpointOrientationProducerExistsIsTrue :
  q4eNegativeEndpointOrientationProducerExists ≡ true
q4eNegativeEndpointOrientationProducerExistsIsTrue = refl

q4ePositiveEndpointReducedToAmplitudeSquareIsTrue :
  q4ePositiveEndpointReducedToAmplitudeSquare ≡ true
q4ePositiveEndpointReducedToAmplitudeSquareIsTrue = refl

q4ePositiveTerminalFluxUniformBoundClosedHereIsFalse :
  q4ePositiveTerminalFluxUniformBoundClosedHere ≡ false
q4ePositiveTerminalFluxUniformBoundClosedHereIsFalse = refl
