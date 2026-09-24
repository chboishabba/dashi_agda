{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNLiveExternalHelicityCommutatorSpacetimeRound637Exact where

------------------------------------------------------------------------
-- ROUND637 / LIVE CANONICAL EXTERNAL CHANNEL = HELICITY COMMUTATOR IN SPACETIME
--
-- R636 proves on one physical slice / one spectator weight that the canonical
-- external R573 scalar is exactly the literal external R306 helicity-
-- commutator scalar.
--
-- R624 already aggregates the canonical external scalar through
--   spectator beta -> output k -> canonical nonzero output list -> time.
--
-- This owner transports the R636 same-object equality through precisely those
-- existing finite folds and the existing integration authority.  The result is
-- a literal live spacetime carrier for the external analytic leaf:
--
--   integral canonicalExternal
--     = integral externalHelicityCommutator.
--
-- No estimate, norm, absolute value, shell split, positivity replacement, or
-- new PDE theorem is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (cong₂)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Canonical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventR294WeightRound541Exact as R541
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventRowFactorizationRound545Exact as R545
import DASHI.Physics.Closure.NSTriadKNLiveNestedSelfCanonicalExternalSpacetimeRound624Exact as R624
import DASHI.Physics.Closure.NSTriadKNCanonicalExternalHelicityCommutatorRound636Exact as R636

F : C3.RealField _
F = Rational.rationalRealField

module LiveExternalHelicity637
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (integration : R495.IntegrationTransportAuthority Time integrateTo) where

  module Old = R624.LiveCanonicalSplit
    Time initialTime integrateTo DerivativeOf integration

  module Dyn = Old.Dyn
  module Support = Old.Support

  module At
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T)
      (cutoff : Nat) (time : Time) where

    module B = Old.At T R cutoff time
    physicalSystem = B.B.Slice.PS
    system = Field30.finiteSystem physicalSystem

    module Spec = R541.Spectator physicalSystem B.B.S
    module Row = R545.Row physicalSystem B.B.S

    module HelicityAt
        (beta : Physical.PhysicalTriadIncidence) =
      R636.CanonicalExternalHelicity636
        (Field30.physicalEmbedding physicalSystem)
        (Field30.physicalInverseSquare physicalSystem)
        (Spec.spectatorWeight beta)
        B.B.S B.B.L B.B.H system B.B.velocityTransverse

    helicityExternalRow :
      Z3.FourierMode →
      Physical.PhysicalTriadIncidence → ℚ
    helicityExternalRow output beta =
      let module H = HelicityAt beta in
      H.totalExternalHelicityScalar output (Row.doubleCell beta)

    canonicalExternalRowIsHelicity :
      (output : Z3.FourierMode) →
      (beta : Physical.PhysicalTriadIncidence) →
      B.Rows.canonicalExternalNestedForcingRow output beta
      ≡ helicityExternalRow output beta
    canonicalExternalRowIsHelicity output beta =
      let module H = HelicityAt beta in
      H.canonicalExternalScalarIsHelicityCommutatorScalar
        output (Row.doubleCell beta)

    helicityExternalRows :
      Z3.FourierMode →
      List Physical.PhysicalTriadIncidence → ℚ
    helicityExternalRows output [] = 0ℚ
    helicityExternalRows output (beta ∷ rest) =
      helicityExternalRow output beta
        + helicityExternalRows output rest

    canonicalExternalRowsAreHelicity :
      (output : Z3.FourierMode) →
      (betas : List Physical.PhysicalTriadIncidence) →
      B.canonicalExternalRows output betas
      ≡ helicityExternalRows output betas
    canonicalExternalRowsAreHelicity output [] = refl
    canonicalExternalRowsAreHelicity output (beta ∷ rest) =
      cong₂ _+_
        (canonicalExternalRowIsHelicity output beta)
        (canonicalExternalRowsAreHelicity output rest)

    helicityExternalOutputForcingFull :
      Z3.FourierMode → ℚ
    helicityExternalOutputForcingFull output =
      helicityExternalRows output
        (Output.physicalOutputFiber cutoff output)

    canonicalExternalOutputIsHelicity :
      (output : Z3.FourierMode) →
      B.canonicalExternalNestedOutputForcingFull output
      ≡ helicityExternalOutputForcingFull output
    canonicalExternalOutputIsHelicity output =
      canonicalExternalRowsAreHelicity output
        (Output.physicalOutputFiber cutoff output)

  helicityExternalSumOutputs :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) → Time → List Z3.FourierMode → ℚ
  helicityExternalSumOutputs T R cutoff time [] = 0ℚ
  helicityExternalSumOutputs T R cutoff time (output ∷ rest) =
    let module A = At T R cutoff time in
    A.helicityExternalOutputForcingFull output
      + helicityExternalSumOutputs T R cutoff time rest

  canonicalExternalSumOutputsIsHelicity :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) (time : Time) →
    (outputs : List Z3.FourierMode) →
    Old.canonicalExternalNestedSumOutputs T R cutoff time outputs
    ≡ helicityExternalSumOutputs T R cutoff time outputs
  canonicalExternalSumOutputsIsHelicity T R cutoff time [] = refl
  canonicalExternalSumOutputsIsHelicity
      T R cutoff time (output ∷ rest) =
    let module A = At T R cutoff time in
    cong₂ _+_
      (A.canonicalExternalOutputIsHelicity output)
      (canonicalExternalSumOutputsIsHelicity
        T R cutoff time rest)

  helicityExternalGlobalForcingFull :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → ℚ
  helicityExternalGlobalForcingFull T R cutoff time =
    helicityExternalSumOutputs T R cutoff time
      (Canonical.nonzeroCutoffModes cutoff)

  canonicalExternalGlobalIsHelicity :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) (time : Time) →
    Old.canonicalExternalNestedGlobalForcingFull T R cutoff time
    ≡ helicityExternalGlobalForcingFull T R cutoff time
  canonicalExternalGlobalIsHelicity T R cutoff time =
    canonicalExternalSumOutputsIsHelicity
      T R cutoff time (Canonical.nonzeroCutoffModes cutoff)

  integratedHelicityExternalGlobalForcingFull :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → ℚ
  integratedHelicityExternalGlobalForcingFull T R cutoff terminal =
    integrateTo
      (helicityExternalGlobalForcingFull T R cutoff)
      terminal

  integratedCanonicalExternalIsHelicity :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) (terminal : Time) →
    Old.integratedCanonicalExternalNestedGlobalForcingFull
      T R cutoff terminal
    ≡ integratedHelicityExternalGlobalForcingFull
        T R cutoff terminal
  integratedCanonicalExternalIsHelicity T R cutoff terminal =
    R495.integrateCongruent integration
      (Old.canonicalExternalNestedGlobalForcingFull T R cutoff)
      (helicityExternalGlobalForcingFull T R cutoff)
      (canonicalExternalGlobalIsHelicity T R cutoff)
      terminal

------------------------------------------------------------------------
-- Status / trust boundary.
------------------------------------------------------------------------

round637SpectatorRowsOnHelicityCommutatorClosed : Bool
round637SpectatorRowsOnHelicityCommutatorClosed = true

round637OutputAggregationOnHelicityCommutatorClosed : Bool
round637OutputAggregationOnHelicityCommutatorClosed = true

round637LiveExternalSpacetimeOnHelicityCommutatorClosed : Bool
round637LiveExternalSpacetimeOnHelicityCommutatorClosed = true

round637IntroducesEstimate : Bool
round637IntroducesEstimate = false

round637HelicityCommutatorSignedSpacetimePaymentClosed : Bool
round637HelicityCommutatorSignedSpacetimePaymentClosed = false

round637SpectatorRowsOnHelicityCommutatorClosedIsTrue :
  round637SpectatorRowsOnHelicityCommutatorClosed ≡ true
round637SpectatorRowsOnHelicityCommutatorClosedIsTrue = refl

round637OutputAggregationOnHelicityCommutatorClosedIsTrue :
  round637OutputAggregationOnHelicityCommutatorClosed ≡ true
round637OutputAggregationOnHelicityCommutatorClosedIsTrue = refl

round637LiveExternalSpacetimeOnHelicityCommutatorClosedIsTrue :
  round637LiveExternalSpacetimeOnHelicityCommutatorClosed ≡ true
round637LiveExternalSpacetimeOnHelicityCommutatorClosedIsTrue = refl

round637IntroducesEstimateIsFalse :
  round637IntroducesEstimate ≡ false
round637IntroducesEstimateIsFalse = refl

round637HelicityCommutatorSignedSpacetimePaymentClosedIsFalse :
  round637HelicityCommutatorSignedSpacetimePaymentClosed ≡ false
round637HelicityCommutatorSignedSpacetimePaymentClosedIsFalse = refl
