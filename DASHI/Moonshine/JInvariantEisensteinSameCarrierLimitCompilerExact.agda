module DASHI.Moonshine.JInvariantEisensteinSameCarrierLimitCompilerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConstructiveSeries as Convergence
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.ConcreteComplexSequenceConvergenceExact as ComplexConvergence
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as Eisenstein

------------------------------------------------------------------------
-- SAME-CARRIER LIMIT COMPILER FOR THE ACTUAL FINITE E4/E6 RECURRENCES
--
-- DASHI CONTRIBUTION / REPO CROSS-POLLINATION
--
-- `JInvariantEisensteinFiniteQSeriesExact` already gives the literal finite
-- truncations on `ConcreteComplex.ComplexPair`.  The new
-- `ConcreteComplexSequenceConvergenceExact` owner gives componentwise Cauchy
-- completeness on that exact carrier.  This module composes those two existing
-- theorem-bearing surfaces without changing complex representation.
--
-- The input remains intentionally quantitative and proof-relevant: consumers
-- must supply Cauchy evidence for the real and imaginary truncation sequences.
-- This file does NOT prove that evidence, does NOT infer it from finite-prefix
-- parity/OEIS observations, and does NOT identify the resulting limit with the
-- analytic lattice-sum Eisenstein object.
--
-- Source attribution is inherited rather than reassigned:
-- * finite E4/E6 recurrence: DASHI J-invariant owners, with Serre/Miyake source
--   atlas elsewhere in this branch;
-- * constructive completeness architecture: DASHI's constructed-real spine;
-- * Bishop/Murray/Csimma provenance belongs to the separate vendored-Bishop
--   convergence owners and is not claimed as the source of this composition.
------------------------------------------------------------------------

private
  Carrier : Complex.ConstructedComplexPackage -> Set
  Carrier C = Real.Real (Real.real (Complex.realPackage C))

------------------------------------------------------------------------
-- Exact truncation sequences, realized through the repository's explicit
-- function -> admitted-sequence bridge.
------------------------------------------------------------------------

e4TruncationSequence :
  (C : Complex.ConstructedComplexPackage) ->
  Convergence.FunctionSequenceRealization
    (Real.real (Complex.realPackage C)) ->
  Eisenstein.DivisorPowerKernel ->
  Complex.ComplexPair (Real.real (Complex.realPackage C)) ->
  ComplexConvergence.ComplexSequence
    (Real.real (Complex.realPackage C))
e4TruncationSequence C S kernel tau =
  ComplexConvergence.complex-sequence
    (Convergence.fromFunction S
      (λ n -> Complex.re (Eisenstein.e4Truncated C kernel n tau)))
    (Convergence.fromFunction S
      (λ n -> Complex.im (Eisenstein.e4Truncated C kernel n tau)))

e6TruncationSequence :
  (C : Complex.ConstructedComplexPackage) ->
  Convergence.FunctionSequenceRealization
    (Real.real (Complex.realPackage C)) ->
  Eisenstein.DivisorPowerKernel ->
  Complex.ComplexPair (Real.real (Complex.realPackage C)) ->
  ComplexConvergence.ComplexSequence
    (Real.real (Complex.realPackage C))
e6TruncationSequence C S kernel tau =
  ComplexConvergence.complex-sequence
    (Convergence.fromFunction S
      (λ n -> Complex.re (Eisenstein.e6Truncated C kernel n tau)))
    (Convergence.fromFunction S
      (λ n -> Complex.im (Eisenstein.e6Truncated C kernel n tau)))

------------------------------------------------------------------------
-- The sequence really is the existing finite recurrence, componentwise.
------------------------------------------------------------------------

e4RealSequenceAtTruncation :
  (C : Complex.ConstructedComplexPackage) ->
  (S : Convergence.FunctionSequenceRealization
         (Real.real (Complex.realPackage C))) ->
  (kernel : Eisenstein.DivisorPowerKernel) ->
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) ->
  (n : Nat) ->
  Real.sequenceAt
    (Real.real (Complex.realPackage C))
    (ComplexConvergence.realSequence
      (e4TruncationSequence C S kernel tau)) n
  ≡ Complex.re (Eisenstein.e4Truncated C kernel n tau)
e4RealSequenceAtTruncation C S kernel tau n =
  Convergence.sequenceAtFromFunction S
    (λ index -> Complex.re (Eisenstein.e4Truncated C kernel index tau)) n

e4ImagSequenceAtTruncation :
  (C : Complex.ConstructedComplexPackage) ->
  (S : Convergence.FunctionSequenceRealization
         (Real.real (Complex.realPackage C))) ->
  (kernel : Eisenstein.DivisorPowerKernel) ->
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) ->
  (n : Nat) ->
  Real.sequenceAt
    (Real.real (Complex.realPackage C))
    (ComplexConvergence.imagSequence
      (e4TruncationSequence C S kernel tau)) n
  ≡ Complex.im (Eisenstein.e4Truncated C kernel n tau)
e4ImagSequenceAtTruncation C S kernel tau n =
  Convergence.sequenceAtFromFunction S
    (λ index -> Complex.im (Eisenstein.e4Truncated C kernel index tau)) n

e6RealSequenceAtTruncation :
  (C : Complex.ConstructedComplexPackage) ->
  (S : Convergence.FunctionSequenceRealization
         (Real.real (Complex.realPackage C))) ->
  (kernel : Eisenstein.DivisorPowerKernel) ->
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) ->
  (n : Nat) ->
  Real.sequenceAt
    (Real.real (Complex.realPackage C))
    (ComplexConvergence.realSequence
      (e6TruncationSequence C S kernel tau)) n
  ≡ Complex.re (Eisenstein.e6Truncated C kernel n tau)
e6RealSequenceAtTruncation C S kernel tau n =
  Convergence.sequenceAtFromFunction S
    (λ index -> Complex.re (Eisenstein.e6Truncated C kernel index tau)) n

e6ImagSequenceAtTruncation :
  (C : Complex.ConstructedComplexPackage) ->
  (S : Convergence.FunctionSequenceRealization
         (Real.real (Complex.realPackage C))) ->
  (kernel : Eisenstein.DivisorPowerKernel) ->
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) ->
  (n : Nat) ->
  Real.sequenceAt
    (Real.real (Complex.realPackage C))
    (ComplexConvergence.imagSequence
      (e6TruncationSequence C S kernel tau)) n
  ≡ Complex.im (Eisenstein.e6Truncated C kernel n tau)
e6ImagSequenceAtTruncation C S kernel tau n =
  Convergence.sequenceAtFromFunction S
    (λ index -> Complex.im (Eisenstein.e6Truncated C kernel index tau)) n

------------------------------------------------------------------------
-- The actual payment: explicit Cauchy evidence now produces literal limits on
-- exactly the same `ConcreteComplex.ComplexPair` carrier used by the finite
-- recurrence.
------------------------------------------------------------------------

e4TruncationLimit :
  (C : Complex.ConstructedComplexPackage) ->
  (S : Convergence.FunctionSequenceRealization
         (Real.real (Complex.realPackage C))) ->
  (kernel : Eisenstein.DivisorPowerKernel) ->
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) ->
  ComplexConvergence.ComplexIsCauchy
    (e4TruncationSequence C S kernel tau) ->
  Σ (Complex.ComplexPair (Real.real (Complex.realPackage C)))
    (ComplexConvergence.ComplexConvergesTo
      (e4TruncationSequence C S kernel tau))
e4TruncationLimit C S kernel tau cauchy =
  ComplexConvergence.complexCauchyLimit
    (e4TruncationSequence C S kernel tau) cauchy

e6TruncationLimit :
  (C : Complex.ConstructedComplexPackage) ->
  (S : Convergence.FunctionSequenceRealization
         (Real.real (Complex.realPackage C))) ->
  (kernel : Eisenstein.DivisorPowerKernel) ->
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) ->
  ComplexConvergence.ComplexIsCauchy
    (e6TruncationSequence C S kernel tau) ->
  Σ (Complex.ComplexPair (Real.real (Complex.realPackage C)))
    (ComplexConvergence.ComplexConvergesTo
      (e6TruncationSequence C S kernel tau))
e6TruncationLimit C S kernel tau cauchy =
  ComplexConvergence.complexCauchyLimit
    (e6TruncationSequence C S kernel tau) cauchy

------------------------------------------------------------------------
-- Authority firewalls.
------------------------------------------------------------------------

data LimitCompilerCreatesCauchyProof : Set where
data LimitCompilerIdentifiesAnalyticEisenstein : Set where
data LimitCompilerCreatesModularity : Set where
data LimitCompilerCreatesKleinJ : Set where

limitCompilerDoesNotCreateCauchyProof :
  LimitCompilerCreatesCauchyProof -> ⊥
limitCompilerDoesNotCreateCauchyProof ()

limitCompilerDoesNotIdentifyAnalyticEisenstein :
  LimitCompilerIdentifiesAnalyticEisenstein -> ⊥
limitCompilerDoesNotIdentifyAnalyticEisenstein ()

limitCompilerDoesNotCreateModularity :
  LimitCompilerCreatesModularity -> ⊥
limitCompilerDoesNotCreateModularity ()

limitCompilerDoesNotCreateKleinJ :
  LimitCompilerCreatesKleinJ -> ⊥
limitCompilerDoesNotCreateKleinJ ()

record EisensteinSameCarrierLimitBoundary : Set where
  constructor eisenstein-same-carrier-limit-boundary
  field
    actualFiniteRecurrenceConsumed : Bool
    exactConcreteComplexCarrierPreserved : Bool
    functionSequenceRealizationExplicit : Bool
    componentwiseCauchyLimitCompilerReused : Bool
    quantitativeCauchyEstimatePaidHere : Bool
    analyticLatticeSumIdentityPaidHere : Bool
    modularityPaidHere : Bool
    analyticKleinJPaidHere : Bool
    nextResidual : String
open EisensteinSameCarrierLimitBoundary public

canonicalEisensteinSameCarrierLimitBoundary : EisensteinSameCarrierLimitBoundary
canonicalEisensteinSameCarrierLimitBoundary =
  eisenstein-same-carrier-limit-boundary
    true true true true
    false false false false
    "prove componentwise Cauchy/absolute convergence for the actual E4/E6 truncations (e.g. by q-majorants), then identify those same-carrier limits with the analytic Eisenstein lattice-sum objects"
