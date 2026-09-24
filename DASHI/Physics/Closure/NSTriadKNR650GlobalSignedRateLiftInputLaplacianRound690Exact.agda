{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650GlobalSignedRateLiftInputLaplacianRound690Exact where

------------------------------------------------------------------------
-- ROUND690 / GLOBALIZE R689 BEFORE ESTIMATING
--
-- R689 is fixed-output:
--
--   RateLiftedFull_k - 8 W(M_k,T_k)
--     = 8 nu W(M_k,L_in,k).
--
-- The remaining theorem is cutoff-uniform and spacetime-global, so do NOT
-- estimate the fixed-output terms separately.  This owner first sums the SAME
-- signed identity over the literal nonzero cutoff outputs and only then
-- integrates in time:
--
--   integral sum_k [RateLiftedFull_k - 8 W(M_k,T_k)]
--     =
--   integral sum_k [8 nu W(M_k,L_in,k)].
--
-- This is exact finite summation + integration transport.  No absolute value,
-- norm, Cauchy estimate, output-cardinality factor, or new analytic assumption
-- is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_)
open import Relation.Binary.PropositionalEquality using (cong₂)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Canonical
import DASHI.Physics.Closure.NSTriadKNLiteralNonzeroCutoffSupportRound404Exact as R404
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNPhysicalTrajectoryRetainedGlobalFluxRound403Exact as R403
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNR650RateLiftedR568ToC2CommutatorRound687Exact as R687
import DASHI.Physics.Closure.NSTriadKNR650RateLiftedInputLaplacianCancellationRound689Exact as R689

F : C3.RealField _
F = Rational.rationalRealField

module GlobalSignedCancellation
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
  module Live = R403.LiveTrajectoryFlux
    Time initialTime integrateTo DerivativeOf

  module At
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T)
      (cutoff : Nat)
      (time : Time) where

    retained =
      Support.toRetainedSupportRealization T R

    physicalSystem =
      Live.physicalSystemAt T retained cutoff time

    viscosityPositive =
      Live.stateViscosityPositive T retained cutoff time

    S = Dyn.Base.S (Dyn.forgetDynamics T)

    signedTerm :
      (output : Z3.FourierMode) →
      Z3.NonZeroMode output → ℚ
    signedTerm output outputNonzero =
      let
        module One =
          R689.FixedOutput
            physicalSystem S viscosityPositive output outputNonzero
      in
      One.Cancel.rateLiftedFull
        - R687.eight * One.Cancel.tangentWork

    inputLaplacianTerm :
      (output : Z3.FourierMode) →
      Z3.NonZeroMode output → ℚ
    inputLaplacianTerm output outputNonzero =
      let
        module One =
          R689.FixedOutput
            physicalSystem S viscosityPositive output outputNonzero
      in
      R687.eight * One.inputLaplacianWork

    sumSigned :
      (outputs : List Z3.FourierMode) →
      ((output : Z3.FourierMode) →
        output Cube.∈ outputs → Z3.NonZeroMode output) →
      ℚ
    sumSigned [] allNonzero = 0
    sumSigned (output ∷ rest) allNonzero =
      signedTerm output (allNonzero output (Cube.here refl))
        +
      sumSigned rest
        (λ selected member →
          allNonzero selected (Cube.there member))

    sumInputLaplacian :
      (outputs : List Z3.FourierMode) →
      ((output : Z3.FourierMode) →
        output Cube.∈ outputs → Z3.NonZeroMode output) →
      ℚ
    sumInputLaplacian [] allNonzero = 0
    sumInputLaplacian (output ∷ rest) allNonzero =
      inputLaplacianTerm output (allNonzero output (Cube.here refl))
        +
      sumInputLaplacian rest
        (λ selected member →
          allNonzero selected (Cube.there member))

    sumIdentity :
      (outputs : List Z3.FourierMode) →
      (allNonzero :
        (output : Z3.FourierMode) →
        output Cube.∈ outputs → Z3.NonZeroMode output) →
      sumSigned outputs allNonzero
      ≡ sumInputLaplacian outputs allNonzero
    sumIdentity [] allNonzero = refl
    sumIdentity (output ∷ rest) allNonzero =
      let
        outputNZ = allNonzero output (Cube.here refl)
        module One =
          R689.FixedOutput
            physicalSystem S viscosityPositive output outputNZ
        tailNonzero =
          λ selected member →
            allNonzero selected (Cube.there member)
      in
      cong₂ _+_
        One.rateLiftedMinusTangentIsEightInputLaplacianWork
        (sumIdentity rest tailNonzero)

    outputs : List Z3.FourierMode
    outputs = Canonical.nonzeroCutoffModes cutoff

    allOutputsNonzero :
      (output : Z3.FourierMode) →
      output Cube.∈ outputs → Z3.NonZeroMode output
    allOutputsNonzero output member =
      R404.nonzeroCutoffMemberNonzero member

    globalSignedCancellation : ℚ
    globalSignedCancellation =
      sumSigned outputs allOutputsNonzero

    globalInputLaplacianWork : ℚ
    globalInputLaplacianWork =
      sumInputLaplacian outputs allOutputsNonzero

    globalPointwiseIdentity :
      globalSignedCancellation ≡ globalInputLaplacianWork
    globalPointwiseIdentity =
      sumIdentity outputs allOutputsNonzero

  globalSignedCancellation :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → ℚ
  globalSignedCancellation T R cutoff time =
    At.globalSignedCancellation T R cutoff time

  globalInputLaplacianWork :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → ℚ
  globalInputLaplacianWork T R cutoff time =
    At.globalInputLaplacianWork T R cutoff time

  globalPointwiseIdentity :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) (time : Time) →
    globalSignedCancellation T R cutoff time
    ≡ globalInputLaplacianWork T R cutoff time
  globalPointwiseIdentity T R cutoff time =
    At.globalPointwiseIdentity T R cutoff time

  integratedGlobalSignedCancellation :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → ℚ
  integratedGlobalSignedCancellation T R cutoff terminal =
    integrateTo (globalSignedCancellation T R cutoff) terminal

  integratedGlobalInputLaplacianWork :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → ℚ
  integratedGlobalInputLaplacianWork T R cutoff terminal =
    integrateTo (globalInputLaplacianWork T R cutoff) terminal

  integratedGlobalIdentity :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) (terminal : Time) →
    integratedGlobalSignedCancellation T R cutoff terminal
    ≡ integratedGlobalInputLaplacianWork T R cutoff terminal
  integratedGlobalIdentity T R cutoff terminal =
    R495.integrateCongruent integration
      (globalSignedCancellation T R cutoff)
      (globalInputLaplacianWork T R cutoff)
      (globalPointwiseIdentity T R cutoff)
      terminal

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round690R689SummedOverLiteralNonzeroOutputs : Bool
round690R689SummedOverLiteralNonzeroOutputs = true

round690R689IntegratedOnlyAfterGlobalOutputSum : Bool
round690R689IntegratedOnlyAfterGlobalOutputSum = true

round690IntroducesOutputCardinalityFactor : Bool
round690IntroducesOutputCardinalityFactor = false

round690IntroducesAbsoluteValueOrNorm : Bool
round690IntroducesAbsoluteValueOrNorm = false

round690IntroducesEstimate : Bool
round690IntroducesEstimate = false

round690GlobalInputLaplacianSpacetimePaymentClosed : Bool
round690GlobalInputLaplacianSpacetimePaymentClosed = false

round690C1Closed : Bool
round690C1Closed = false

round690C2Closed : Bool
round690C2Closed = false

round690ClayPromotion : Bool
round690ClayPromotion = false

round690R689SummedOverLiteralNonzeroOutputsIsTrue :
  round690R689SummedOverLiteralNonzeroOutputs ≡ true
round690R689SummedOverLiteralNonzeroOutputsIsTrue = refl

round690R689IntegratedOnlyAfterGlobalOutputSumIsTrue :
  round690R689IntegratedOnlyAfterGlobalOutputSum ≡ true
round690R689IntegratedOnlyAfterGlobalOutputSumIsTrue = refl

round690IntroducesOutputCardinalityFactorIsFalse :
  round690IntroducesOutputCardinalityFactor ≡ false
round690IntroducesOutputCardinalityFactorIsFalse = refl

round690IntroducesAbsoluteValueOrNormIsFalse :
  round690IntroducesAbsoluteValueOrNorm ≡ false
round690IntroducesAbsoluteValueOrNormIsFalse = refl

round690IntroducesEstimateIsFalse :
  round690IntroducesEstimate ≡ false
round690IntroducesEstimateIsFalse = refl

round690GlobalInputLaplacianSpacetimePaymentClosedIsFalse :
  round690GlobalInputLaplacianSpacetimePaymentClosed ≡ false
round690GlobalInputLaplacianSpacetimePaymentClosedIsFalse = refl

round690C1ClosedIsFalse :
  round690C1Closed ≡ false
round690C1ClosedIsFalse = refl

round690C2ClosedIsFalse :
  round690C2Closed ≡ false
round690C2ClosedIsFalse = refl

round690ClayPromotionIsFalse :
  round690ClayPromotion ≡ false
round690ClayPromotionIsFalse = refl
