module DASHI.Interop.LeanEta24PinnedReflectionParityExact where

------------------------------------------------------------------------
-- LEAN / MATHLIB v4.28 ETA^24 REFLECTION PARITY
--
-- Lean owner:
--   chboishabba/dashi_lean4
--   branch agent/moonshine-eisenstein-analytic-20260922
--   Integration.MoonshineEta24Pinned
--
-- Dependency:
--   Mathlib v4.28.0 (the repository's existing pin; no bump).
--
-- The Lean owner derives, rather than postulates:
--
--   eta24(S tau) = tau^12 eta24(tau)
--   eta24(T tau) = eta24(tau)
--   eta(-conj tau) = conj(eta(tau))
--   eta24(S(-conj tau))
--     = conj(tau^12 eta24(tau))
--
-- and on normSq(tau)=1:
--
--   eta24(tau)
--     = conj(tau^12 eta24(tau)).
--
-- The S law is obtained at the old Mathlib pin without the later
-- Discriminant/SqrtDeriv package: equality of logarithmic derivatives is
-- derived from the already-pinned eta log derivative and E2 S-transform, and
-- the multiplicative constant is fixed at i.
--
-- FIREWALL:
-- This does NOT prove here that eta^24 is the same object as DASHI's normalized
-- E4/E6 Delta target.  Both targets now independently satisfy the desired
-- reflection identity; their same-object identification remains separate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

record LeanEta24PinnedReflectionParity : Set where
  constructor lean-eta24-pinned-reflection-parity
  field
    repository : String
    branch : String
    moduleName : String
    mathlibPin : String

    etaNonvanishingReused : Bool
    etaLogDerivativeReused : Bool
    e2STransformationReused : Bool

    eta24Weight12SProved : Bool
    eta24TInvariantProved : Bool
    etaRealStructureConjugationProved : Bool
    eta24InverseConjugationReflectionProved : Bool
    eta24UnitCircleFixedLocusProved : Bool

    dependencyBumpUsed : Bool
    eta24SameObjectAsNormalizedE4E6Delta : Bool

open LeanEta24PinnedReflectionParity public

canonicalLeanEta24PinnedReflectionParity :
  LeanEta24PinnedReflectionParity
canonicalLeanEta24PinnedReflectionParity =
  lean-eta24-pinned-reflection-parity
    "chboishabba/dashi_lean4"
    "agent/moonshine-eisenstein-analytic-20260922"
    "Integration.MoonshineEta24Pinned"
    "v4.28.0"
    true true true
    true true true true true
    false false
