module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound21Validation where

------------------------------------------------------------------------
-- Focused validation root for the literal Hessian cancellation tranche.
--
-- Importing this module elaborates the complete round-twenty finite
-- Combes--Thomas endgame together with:
--
--   * positivity of the literal gauge and CMP109 first-derivative squares;
--   * exact cancellation of those squares against the matched Hodge reference;
--   * reduction of the 1/32 Hessian theorem to Wilson-minus-difference;
--   * exact promotion of the sharp sixteen-atom Wilson budget;
--   * a non-phantom producer model binding field, jets and physical scalars to
--     the same physical perturbation h.
--
-- This root does not assert the remaining physical Wilson atom estimate, the
-- literal stencil/row-mass producer, or a Clay completion.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound20Validation
open import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintCancellationExact
open import DASHI.Physics.YangMills.BalabanP33WilsonSharpBudgetCoercivityExact
open import DASHI.Physics.YangMills.BalabanP33LiteralPhysicalPerturbationAdapterExact
