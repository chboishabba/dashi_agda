module DASHI.Analysis.RiemannG2Vendored8889SourceAuditExact where

------------------------------------------------------------------------
-- VENDORED 8889 THEOREM BYTES LOCATED IN dashi_lean4
--
-- The companion repository vendors the theorem-bearing Zeta23Bridge files
-- previously represented in Agda mostly by status/provenance receipts.
--
-- The important correction is semantic:
--
-- * PoleQuotientClusterMargin does NOT primarily provide an absolute
--   cCluster/t^2 lower bound.
-- * It provides a positive height-free baseline plus an explicit quadratic
--   off-line surplus
--
--       baselineCluster
--         + (sqrt(2)/2) * a^2 * secondMoment(g)
--       <= actual cluster value,
--
--   together with an O(a^2/t^2)-relative window.
-- * PoleQuotientGammaBudget proves a uniform strip-constant budget, but its own
--   header explicitly says that bound is too coarse for the required window.
--
-- This file records exact source custody only.  No Lean proof is transported
-- into the Agda kernel here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

record Vendored8889SourceReceipt : Set where
  constructor vendored-8889-source-receipt
  field
    repository : String
    branch : String

    clusterPath : String
    clusterLowerTheorem : String
    clusterQuadraticWindowTheorem : String
    clusterPinnedChannelsTheorem : String

    gammaPath : String
    gammaExactEnvelopeTheorem : String
    gammaStripBudgetTheorem : String

    farPath : String
    farEveryCutoffTheorem : String

open Vendored8889SourceReceipt public

currentVendored8889SourceReceipt : Vendored8889SourceReceipt
currentVendored8889SourceReceipt =
  vendored-8889-source-receipt
    "chboishabba/dashi_lean4"
    "agent/rh-farshell-quartic-bypass"
    "Imported/Zeta23Bridge/Zeta23Bridge/PoleQuotientClusterMargin.lean"
    "Zeta23Bridge.PoleQuotientClusterMargin.clusterValue_ge_baseline_add_margin"
    "Zeta23Bridge.PoleQuotientClusterMargin.poleQuotientMarginWindow_quantitative"
    "Zeta23Bridge.PoleQuotientComplementMargin.complementChannels_pinned"
    "Imported/Zeta23Bridge/Zeta23Bridge/PoleQuotientGammaBudget.lean"
    "Zeta23Bridge.LiteralWeilGammaConeBound.gammaConeEnvelope"
    "Zeta23Bridge.PoleQuotientGammaBudget.exists_gamma_budget_linear_in_stripConst"
    "Imported/Zeta23Bridge/Zeta23Bridge/FarShellCutoffTailBound.lean"
    "Zeta23Bridge.FarShellCutoffTailBound.tsum_tailTermFrom_le"

record Vendored8889AuditBoundary : Set where
  constructor vendored-8889-audit-boundary
  field
    theoremBytesLocated : Bool
    clusterFreshDerivationRequiredBeforeTransport : Bool
    clusterNaturalScaleIsAbsoluteInverseSquare : Bool
    clusterNaturalScaleUsesBaselineAndHorizontalSquare : Bool
    coarseGammaBoundExists : Bool
    coarseGammaBoundClosesSharpWindow : Bool
    sourceTransportIntoAgdaOwned : Bool
    rhDerivedHere : Bool

open Vendored8889AuditBoundary public

canonicalVendored8889AuditBoundary : Vendored8889AuditBoundary
canonicalVendored8889AuditBoundary =
  vendored-8889-audit-boundary
    true
    false
    false
    true
    true
    false
    false
    false
