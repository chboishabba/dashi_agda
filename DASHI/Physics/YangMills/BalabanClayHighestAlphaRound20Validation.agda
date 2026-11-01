module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound20Validation where

------------------------------------------------------------------------
-- Focused validation root for the square-root-free Schur/Combes--Thomas lane.
--
-- Importing this module forces Agda to elaborate the complete round-nineteen
-- conjugation development together with:
--
--   * weighted finite Cauchy and Schur bounds;
--   * exact same-vector tilt decomposition;
--   * squared half-gap survival and inverse factor 4096;
--   * literal 3072-coordinate row/column promotion;
--   * exact Kronecker basis and norm-to-entry extraction;
--   * quadratic-to-squared coercivity;
--   * tilted inverse entry 64 and physical Green-kernel decay.
--
-- This root does not assert the still-open physical five-channel Hessian
-- estimate or a Clay completion.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound19Validation
open import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact
open import DASHI.Physics.YangMills.BalabanP33CombesThomasSquaredHalfGapExact
open import DASHI.Physics.YangMills.BalabanP33PhysicalCombesThomasSchurExact
open import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact
open import DASHI.Physics.YangMills.BalabanP33PhysicalQuadraticToSquaredCoercivityExact
open import DASHI.Physics.YangMills.BalabanP33PhysicalCombesThomasEntryDecayExact
open import DASHI.Physics.YangMills.BalabanP33PhysicalCombesThomasQuadraticEndgameExact
