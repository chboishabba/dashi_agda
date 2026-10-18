module DASHI.Analysis.TailModulusCauchyBridgeExact where

------------------------------------------------------------------------
-- GENERIC QUANTITATIVE-TAIL -> BACKEND IsCauchy BRIDGE
--
-- DASHI CONTRIBUTION / CROSS-POLLINATION
--
-- Several repository lanes now share the same final analytic seam:
--
--   quantitative vanishing of a finite-tail majorant
--        ->
--   the selected completion backend's opaque IsCauchy predicate.
--
-- ConstructedOrderedCompleteReal intentionally leaves IsCauchy abstract, so
-- this implication cannot be proved from the spine alone.  This owner makes
-- that single backend-specific compiler explicit and reusable rather than
-- re-declaring application-specific versions in Moonshine, Casimir, etc.
--
-- The record is deliberately one-way and fail-closed.  It does not infer a
-- metric, epsilon semantics, completeness, or a physical interpretation.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.PolynomialGeometricTailDominationExact as Tail

record TailVanishesToCauchyBridge
    {Scalar : Set}
    (R : Real.ConstructedOrderedCompleteReal)
    (K : Tail.OrderedTailKernel Scalar)
    (S : Tail.TailSmallness K)
    (term : Nat → Scalar)
    (sequence : Real.Sequence R) : Set₁ where
  field
    tailVanishesImpliesCauchy :
      Tail.TailVanishes K S term →
      Real.IsCauchy R sequence

open TailVanishesToCauchyBridge public

compileTailVanishesToCauchy :
  ∀ {Scalar : Set}
    {R : Real.ConstructedOrderedCompleteReal}
    {K : Tail.OrderedTailKernel Scalar}
    {S : Tail.TailSmallness K}
    {term : Nat → Scalar}
    {sequence : Real.Sequence R} →
  TailVanishesToCauchyBridge R K S term sequence →
  Tail.TailVanishes K S term →
  Real.IsCauchy R sequence
compileTailVanishesToCauchy bridge =
  tailVanishesImpliesCauchy bridge
