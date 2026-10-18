module DASHI.Interop.LeanDeltaFinalMinCutParityExact where

------------------------------------------------------------------------
-- FINAL DELTA SAME-OBJECT MIN-CUT PARITY
--
-- Lean owner:
--   chboishabba/dashi_lean4
--   branch agent/moonshine-eisenstein-analytic-20260922
--   Integration.MoonshineDeltaFinalMinCut
--
-- Dependency:
--   Mathlib v4.28.0 (existing pin; no bump).
--
-- All downstream classical Delta consequences now compile from ONE remaining
-- proposition:
--
--   eta(tau)^24 = (E4(tau)^3 - E6(tau)^2) / 1728
--
-- pointwise on the upper half-plane.
--
-- Given exactly this same-object input, Lean derives:
--
--   * nonvanishing of normalized (E4^3-E6^2)/1728;
--   * unconditional sixfold phase for that normalized Delta target;
--   * arg Delta = -6 arg tau + k*pi on the unit-circle fixed locus;
--   * collapse of the two independently proved reflection/fixed-locus owners;
--   * an inhabitant of the pre-existing typed DeltaEta24SameObjectWeld.
--
-- Conversely, inhabiting that typed eta24 weld on the canonical normalized
-- E4/E6 target is equivalent to the single min-cut proposition.
--
-- FIREWALL
--
-- This receipt does NOT mark the proposition itself proved at Mathlib v4.28.
-- It records only that every downstream theorem is compiler-owned once this
-- single identity is supplied.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

record LeanDeltaFinalMinCutParity : Set where
  constructor lean-delta-final-min-cut-parity
  field
    repository : String
    branch : String
    moduleName : String
    mathlibPin : String

    oneLoadBearingSameObjectProposition : Bool
    normalizedDeltaNonvanishingCompilerOwned : Bool
    normalizedDeltaUnconditionalSixfoldCompilerOwned : Bool
    normalizedDeltaArgCongruenceCompilerOwned : Bool
    reflectionOwnerCollapseCompilerOwned : Bool
    typedEta24WeldEquivalentToMinCut : Bool

    eta24NormalizedDeltaSameObjectProvedAtPinnedMathlib : Bool
    dependencyBumpUsed : Bool
    automaticAgdaPromotion : Bool

open LeanDeltaFinalMinCutParity public

canonicalLeanDeltaFinalMinCutParity :
  LeanDeltaFinalMinCutParity
canonicalLeanDeltaFinalMinCutParity =
  lean-delta-final-min-cut-parity
    "chboishabba/dashi_lean4"
    "agent/moonshine-eisenstein-analytic-20260922"
    "Integration.MoonshineDeltaFinalMinCut"
    "v4.28.0"
    true true true true true true
    false false false
