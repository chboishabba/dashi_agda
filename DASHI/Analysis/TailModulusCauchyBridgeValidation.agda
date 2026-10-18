module DASHI.Analysis.TailModulusCauchyBridgeValidation where

open import Agda.Builtin.Nat using (Nat)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.PolynomialGeometricTailDominationExact as Tail
import DASHI.Analysis.TailModulusCauchyBridgeExact as P

compileTailCauchyRegression :
  ∀ {Scalar : Set}
    {R : Real.ConstructedOrderedCompleteReal}
    {K : Tail.OrderedTailKernel Scalar}
    {S : Tail.TailSmallness K}
    {term : Nat → Scalar}
    {sequence : Real.Sequence R} →
  P.TailVanishesToCauchyBridge R K S term sequence →
  Tail.TailVanishes K S term →
  Real.IsCauchy R sequence
compileTailCauchyRegression = P.compileTailVanishesToCauchy
