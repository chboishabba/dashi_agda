module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound26Validation where

------------------------------------------------------------------------
-- Focused validation root for the round-twenty-six highest-alpha tranche.
--
-- This root imports the round-twenty-five projection/leakage continuation and
-- then checks the new concrete mathematics:
--
--   * the parameterized physical gauge Young inequality
--       -16 (eta + eta^-1 delta) ||h||^2;
--   * the relaxed radius delta = 4 rho^2 sufficient for the configured
--       -64 rho gauge budget;
--   * exact dyadic physical-gap scale invariance from simultaneous lattice-gap
--       and lattice-spacing doubling;
--   * the loss-corrected normalized Feshbach cross-product inequality;
--   * finite conversion of an entrywise decay/stencil majorant into row,
--       column and Schur bounds;
--   * the composed B C^-1 B^T coefficient from coupling and inverse decay
--       majorants;
--   * the corrected Stage-I / Stage-II boundary in which scale algebra is
--       checked but physical transfer/Hessian compatibility remains conditional.
--
-- The root does not assert the selected-background radius, W-local, terminal
-- physical coercivity, a scale-uniform physical C^-1 or B estimate, the actual
-- effective-action Hessian identity, transfer-matrix compatibility, an
-- infinite-volume gap, continuum OS reconstruction, or a Clay completion.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound25CrossPollinationValidation
open import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact
open import DASHI.Physics.YangMills.BalabanP33PhysicalGapScaleInvarianceExact
open import DASHI.Physics.YangMills.BalabanP33KernelDecayToSchurExact
open import DASHI.Physics.YangMills.BalabanP33UniformSchurFeedbackFromDecayExact
open import DASHI.Physics.YangMills.BalabanP33StageIStageIISpectralBoundaryExact
