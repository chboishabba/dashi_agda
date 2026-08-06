module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound23Validation where

------------------------------------------------------------------------
-- Focused validation root for the fixed-volume/terminal-scale correction.
--
-- Importing this module elaborates the round-twenty-two physical Wilson/Hodge
-- stack together with:
--
--   * the concrete half-period square-wave obstruction on unscaled even cycles;
--   * the exact proof that a bare uniform 1/32 Poincare constant is impossible;
--   * the exact one-step RG gap pullback inequality;
--   * finite-chain discounted terminal-gap and loss aggregation;
--   * the separation of terminal Combes--Thomas decay from physical RG gap
--     transfer.
--
-- The root does not assert the remaining local Wilson atom inequality, the
-- background gauge defect estimate, a physical one-step RG gap theorem,
-- terminal-scale curvature/LSI, a continuum limit, or a Clay completion.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound22Validation
open import DASHI.Physics.YangMills.BalabanP33UnscaledCyclePoincareWallExact
open import DASHI.Physics.YangMills.BalabanP33TerminalScaleGapPullbackExact
open import DASHI.Physics.YangMills.BalabanP33FixedVolumeTerminalScaleSeparationExact
