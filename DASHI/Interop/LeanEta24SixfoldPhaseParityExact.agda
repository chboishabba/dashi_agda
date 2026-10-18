module DASHI.Interop.LeanEta24SixfoldPhaseParityExact where

------------------------------------------------------------------------
-- LEAN / MATHLIB v4.28 ETA^24 SIXFOLD PHASE PARITY
--
-- Lean owner:
--   chboishabba/dashi_lean4
--   branch agent/moonshine-eisenstein-analytic-20260922
--   Integration.MoonshineEta24SixfoldPhase
--
-- Dependency:
--   Mathlib v4.28.0 (existing dashi_lean4 pin; no bump).
--
-- The Lean owner proves a branch-safe general compiler:
--
--   normSq z = 1
--   v != 0
--   v = conj(z^12 * v)
--
--      =>
--
--   exp(i(2 arg v + 12 arg z)) = 1
--
--      =>
--
--   exists k : Z,
--     arg v + 6 arg z = k*pi.
--
-- It then specializes this theorem to the pinned eta^24 object, using:
--
--   * eta nonvanishing;
--   * the independently proved eta^24 unit-circle fixed-value identity.
--
-- Hence on normSq(tau)=1:
--
--   exists k : Z,
--     arg(eta(tau)^24) + 6 arg(tau) = k*pi
--
-- equivalently
--
--   arg(eta(tau)^24)
--     = -6 arg(tau) + k*pi.
--
-- FIREWALL:
--
-- * no continuous argument branch is chosen;
-- * the integer multiple of pi carries the exact branch ambiguity;
-- * this receipt does not identify eta^24 with DASHI's normalized E4/E6 Delta;
-- * no Lean theorem is automatically promoted onto an Agda carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

record LeanEta24SixfoldPhaseParity : Set where
  constructor lean-eta24-sixfold-phase-parity
  field
    repository : String
    branch : String
    moduleName : String
    mathlibPin : String

    generalBranchFreePhaseExponentialProved : Bool
    generalIntegerPiCongruenceProved : Bool

    eta24NonvanishingConsumed : Bool
    eta24UnitCircleFixedIdentityConsumed : Bool
    eta24SixfoldPhaseProved : Bool
    eta24ArgCongruentNegativeSixProved : Bool

    continuousArgumentBranchChosen : Bool
    dependencyBumpUsed : Bool
    eta24SameObjectAsNormalizedE4E6Delta : Bool
    automaticallyPromotesAgdaDeltaPhase : Bool

open LeanEta24SixfoldPhaseParity public

canonicalLeanEta24SixfoldPhaseParity :
  LeanEta24SixfoldPhaseParity
canonicalLeanEta24SixfoldPhaseParity =
  lean-eta24-sixfold-phase-parity
    "chboishabba/dashi_lean4"
    "agent/moonshine-eisenstein-analytic-20260922"
    "Integration.MoonshineEta24SixfoldPhase"
    "v4.28.0"
    true true
    true true true true
    false false false false
