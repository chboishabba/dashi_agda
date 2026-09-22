module DASHI.Interop.LeanMoonshineEisensteinAnalyticParityExact where

------------------------------------------------------------------------
-- LEAN/MATHLIB ANALYTIC PARITY RECEIPT FOR THE EISENSTEIN ENDGAME
--
-- External formal source:
--   repository: chboishabba/dashi_lean4
--   branch: agent/moonshine-eisenstein-analytic-20260922
--   modules:
--     Integration.MoonshineEisensteinAnalytic
--     Integration.MoonshineEisensteinWeld
--   Mathlib pin: v4.28.0
--
-- Source authority in that Lean module is Mathlib:
--   Analysis.Complex.UpperHalfPlane.Exp
--   NumberTheory.ModularForms.EisensteinSeries.QExpansion
--   NumberTheory.ModularForms.DedekindEta
--
-- The Lean side proves, on Mathlib's ordinary complex/upper-half-plane carrier:
--
--   Re(2*pi*i*tau) = -2*pi*Im(tau),
--   Im(2*pi*i*tau) =  2*pi*Re(tau),
--   |exp(2*pi*i*tau)| = exp(-2*pi*Im(tau)),
--   |q(tau)| < 1,
--   summability of n^4 q^n and n^6 q^n,
--   converged normalized E4 and E6 q-expansions,
--   nonvanishing of eta(tau)^24.
--
-- DASHI FIREWALL
--
-- This receipt does NOT transport those theorems automatically to Agda's
-- ConstructedOrderedCompleteReal / ConcreteComplex carrier.  It records that
-- the classical analytic theorem is already machine-formalized independently,
-- so the remaining Agda obligation is a same-object/representation weld rather
-- than a fresh proof of standard complex analysis.
--
-- At the pinned Mathlib v4.28.0 the later theorem
--
--   Delta = (E4^3 - E6^2) / 1728
--
-- is not available under the modern 2026 Mathlib module used by newer pins.
-- No dependency bump or theorem import is inferred here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

record LeanMoonshineEisensteinAnalyticParity : Set where
  constructor lean-moonshine-eisenstein-analytic-parity
  field
    leanRepository : String
    leanBranch : String
    leanAnalyticModule : String
    leanWeldModule : String
    mathlibPin : String

    qCartesianTheoremOwnedInLean : Bool
    qNormFormulaOwnedInLean : Bool
    qDiskTheoremOwnedInLean : Bool
    quarticGeometricSummabilityOwnedInLean : Bool
    sexticGeometricSummabilityOwnedInLean : Bool
    sigma3QSeriesSummabilityOwnedInLean : Bool
    sigma5QSeriesSummabilityOwnedInLean : Bool
    literal240Sigma3SummabilityOwnedInLean : Bool
    literal504Sigma5SummabilityOwnedInLean : Bool
    e4ConvergedQExpansionOwnedInLean : Bool
    e6ConvergedQExpansionOwnedInLean : Bool
    eta24NonvanishingOwnedInLean : Bool
    typedQE4E6SameObjectTransportCompilerOwnedInLean : Bool
    typedDeltaEta24TransportCompilerOwnedInLean : Bool

    extractedAgdaSurfaceInhabitedInLean : Bool
    agdaLeanCarrierSameObjectProved : Bool
    leanTheoremAutomaticallyPromotesAgdaAnalyticLeaf : Bool
    deltaE4E6IdentityAvailableAtPinnedMathlib : Bool
    mathlibDependencyBumpedByThisReceipt : Bool

    remainingAgdaMeaning : String

open LeanMoonshineEisensteinAnalyticParity public

canonicalLeanMoonshineEisensteinAnalyticParity :
  LeanMoonshineEisensteinAnalyticParity
canonicalLeanMoonshineEisensteinAnalyticParity =
  lean-moonshine-eisenstein-analytic-parity
    "chboishabba/dashi_lean4"
    "agent/moonshine-eisenstein-analytic-20260922"
    "Integration.MoonshineEisensteinAnalytic"
    "Integration.MoonshineEisensteinWeld"
    "v4.28.0"
    true true true true true true true true true true true true true true
    false false false false false
    "Lean/Mathlib already machine-formalizes the standard q-disk and Eisenstein convergence facts on ordinary complex numbers, including literal sigma3/sigma5 q-series summability at the 240/504 coefficient scales used by the Agda finite recurrences. The Lean companion now also owns a typed transport compiler: once an extracted surface supplies exact pointwise q/E4/E6 identities, q-disk, quartic/sextic summability and converged q-expansions transport automatically; eta^24 nonvanishing is similarly gated behind a separate Delta weld. The remaining Agda endgame should therefore target the extracted carrier/same-object weld, the four coordinate term identifications and the Delta normalization/object identification rather than reproving classical convergence from scratch."
