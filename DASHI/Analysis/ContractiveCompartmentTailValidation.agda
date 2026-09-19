module DASHI.Analysis.ContractiveCompartmentTailValidation where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.PolynomialGeometricTailDominationExact as Tail
import DASHI.Analysis.TailModulusCauchyBridgeExact as Bridge
import DASHI.Analysis.ContractiveCompartmentTailExact as P

compartmentTailRegression :
  ∀ {Scalar : Set}
    {K : Tail.OrderedTailKernel Scalar}
    {S : Tail.TailSmallness K} →
  (problem : P.ContractiveCompartmentProblem K S) →
  Tail.TailVanishes K S (P.actualContribution problem)
compartmentTailRegression = P.actualTailVanishes

compartmentCauchyRegression :
  ∀ {Scalar : Set}
    {K : Tail.OrderedTailKernel Scalar}
    {S : Tail.TailSmallness K}
    {R : Real.ConstructedOrderedCompleteReal}
    {sequence : Real.Sequence R} →
  (problem : P.ContractiveCompartmentProblem K S) →
  Bridge.TailVanishesToCauchyBridge
    R K S (P.actualContribution problem) sequence →
  Real.IsCauchy R sequence
compartmentCauchyRegression = P.compileContractiveCompartmentCauchy


decisionHorizonRegression :
  ∀ {Scalar : Set}
    {K : Tail.OrderedTailKernel Scalar}
    {S : Tail.TailSmallness K} →
  (problem : P.ContractiveCompartmentProblem K S) →
  (precision : Nat) →
  Σ Nat (λ start →
    ∀ count →
    Tail.SmallAt S precision
      (Tail.finiteTail K
        (P.actualContribution problem)
        start count))
decisionHorizonRegression = P.consumerDecisionHorizon
