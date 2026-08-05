module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound21Validation where

------------------------------------------------------------------------
-- Compatibility validation root for the corrected exact-background tranche.
--
-- Round twenty-two discovered that the former Wilson-minus-full-gradient
-- shortcut was not the physical Hodge decomposition: gauge divergence was
-- counted inside the full gradient and then cancelled a second time.  The
-- imported modules now expose the corrected statements:
--
--   * only the independent CMP109 constraint square cancels;
--   * gauge remains paired with flat divergence;
--   * Wilson remains paired with flat curl;
--   * all values are generated from the same full three-component perturbation.
--
-- The complete periodic Hodge, boundary and rational Wilson constructions are
-- validated by the round-twenty-two root.  This root remains as a compatibility
-- import for downstream branches and makes no claim of the superseded shortcut.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound20Validation
open import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintCancellationExact
open import DASHI.Physics.YangMills.BalabanP33WilsonSharpBudgetCoercivityExact
open import DASHI.Physics.YangMills.BalabanP33LiteralPhysicalPerturbationAdapterExact
