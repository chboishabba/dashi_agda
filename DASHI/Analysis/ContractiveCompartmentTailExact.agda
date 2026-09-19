module DASHI.Analysis.ContractiveCompartmentTailExact where

------------------------------------------------------------------------
-- APPLICATION-NEUTRAL CONTRACTIVE COMPARTMENT TAIL COMPILER
--
-- DASHI CONTRIBUTION / CROSS-POLLINATION
--
-- This owner packages the reusable mathematical shape extracted in the
-- Moonshine convergence lane and makes it explicit for any discrete transport,
-- compartment or successive-increment application:
--
--   actualContribution(n) <= majorantContribution(n)
--                  +
--        majorant finite tails vanish
--                  |
--                  v
--          actual finite tails vanish.
--
-- If a selected complete-real backend additionally supplies the already
-- canonical TailVanishesToCauchyBridge for the cumulative trajectory, the same
-- receipt compiles to that backend's IsCauchy predicate.
--
-- Nothing here says that an empirical system is literally geometric,
-- polynomial-geometric, linear, stationary, or closed.  The application owns
-- the pointwise majorant and the interpretation of the sequence.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ)
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.PolynomialGeometricTailDominationExact as Tail
import DASHI.Analysis.TailModulusCauchyBridgeExact as Bridge

record ContractiveCompartmentProblem
    {Scalar : Set}
    (K : Tail.OrderedTailKernel Scalar)
    (S : Tail.TailSmallness K) : Set₁ where
  field
    actualContribution : Nat → Scalar
    majorantContribution : Nat → Scalar

    actualBelowMajorant :
      ∀ index →
      Tail.LessEqual K
        (actualContribution index)
        (majorantContribution index)

    majorantTailVanishes :
      Tail.TailVanishes K S majorantContribution

open ContractiveCompartmentProblem public

actualFiniteTailBelowMajorant :
  ∀ {Scalar : Set}
    {K : Tail.OrderedTailKernel Scalar}
    {S : Tail.TailSmallness K} →
  (problem : ContractiveCompartmentProblem K S) →
  ∀ start count →
  Tail.LessEqual K
    (Tail.finiteTail K
      (actualContribution problem) start count)
    (Tail.finiteTail K
      (majorantContribution problem) start count)
actualFiniteTailBelowMajorant {K = K} problem =
  Tail.finiteTailDomination
    K
    (actualContribution problem)
    (majorantContribution problem)
    (actualBelowMajorant problem)

actualTailVanishes :
  ∀ {Scalar : Set}
    {K : Tail.OrderedTailKernel Scalar}
    {S : Tail.TailSmallness K} →
  (problem : ContractiveCompartmentProblem K S) →
  Tail.TailVanishes K S
    (actualContribution problem)
actualTailVanishes {K = K} {S = S} problem =
  Tail.dominatedTailVanishes
    K
    (actualContribution problem)
    (majorantContribution problem)
    S
    (actualBelowMajorant problem)
    (majorantTailVanishes problem)


consumerDecisionHorizon :
  ∀ {Scalar : Set}
    {K : Tail.OrderedTailKernel Scalar}
    {S : Tail.TailSmallness K} →
  (problem : ContractiveCompartmentProblem K S) →
  (precision : Nat) →
  Σ Nat (λ start →
    ∀ count →
    Tail.SmallAt S precision
      (Tail.finiteTail K
        (actualContribution problem)
        start count))
consumerDecisionHorizon problem precision =
  actualTailVanishes problem precision

compileContractiveCompartmentCauchy :
  ∀ {Scalar : Set}
    {K : Tail.OrderedTailKernel Scalar}
    {S : Tail.TailSmallness K}
    {R : Real.ConstructedOrderedCompleteReal}
    {sequence : Real.Sequence R} →
  (problem : ContractiveCompartmentProblem K S) →
  Bridge.TailVanishesToCauchyBridge
    R K S (actualContribution problem) sequence →
  Real.IsCauchy R sequence
compileContractiveCompartmentCauchy problem bridge =
  Bridge.compileTailVanishesToCauchy
    bridge
    (actualTailVanishes problem)

------------------------------------------------------------------------
-- Explicit interpretation firewall.
------------------------------------------------------------------------

record ContractiveCompartmentBoundary : Set where
  field
    dominationCompilerOwned : Bool
    tailTransferCompilerOwned : Bool
    cauchyCompositionCompilerOwned : Bool
    empiricalPointwiseMajorantStillApplicationOwned : Bool
    empiricalSystemLiterallyPolynomialGeometric : Bool
    finiteObservationWindowEqualsAsymptoticStabilisation : Bool

open ContractiveCompartmentBoundary public

canonicalContractiveCompartmentBoundary : ContractiveCompartmentBoundary
canonicalContractiveCompartmentBoundary = record
  { dominationCompilerOwned = true
  ; tailTransferCompilerOwned = true
  ; cauchyCompositionCompilerOwned = true
  ; empiricalPointwiseMajorantStillApplicationOwned = true
  ; empiricalSystemLiterallyPolynomialGeometric = false
  ; finiteObservationWindowEqualsAsymptoticStabilisation = false
  }
