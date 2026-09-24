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
--     Integration.MoonshineEta24CuspPinned
--     Integration.MoonshineWeight12Eta24ScalarPinned
--     Integration.MoonshineDeltaIdentityPinned
--     Integration.MoonshineDeltaFinalMinCut
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
-- Upstream Mathlib v4.28.0 predates the later packaged discriminant theorem.
-- The Lean companion now reconstructs only the needed pin-local tranche:
-- eta^24 cusp form + first q coefficient, weight-zero constancy, specialized
-- weight-12 scalar rigidity, and finally
--
--   eta^24 = (E4^3 - E6^2) / 1728.
--
-- This is a local theorem proved against the v4.28.0 dependency; it does not
-- mean the later upstream Mathlib Discriminant/DimensionFormula package exists
-- at that pin, and no dependency bump is inferred.
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
    leanEta24PinnedModule : String
    leanEta24SixfoldPhaseModule : String
    leanAgdaTargetModule : String
    agdaExtractionModule : String
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
    leanLiteralAgdaQTargetOwned : Bool
    leanLiteralAgdaE4E6RecurrencesOwned : Bool
    leanLiteralAgdaFiniteSumNormalFormsOwned : Bool
    leanLiteralAgdaFiniteToInfiniteConvergenceOwned : Bool
    leanLiteralInfiniteLimitsIdentifiedWithMathlibE4E6 : Bool
    leanDiscriminantNumeratorLimitCompilerOwned : Bool
    leanNormalizedDeltaLimitCompilerOwned : Bool
    leanPrimitiveRealExtractionCompilerOwned : Bool

    agdaActualQOfTransportCompilerOwned : Bool
    agdaActualE4TruncatedTransportCompilerOwned : Bool
    agdaActualE6TruncatedTransportCompilerOwned : Bool
    agdaTransportDerivedFromPrimitiveComplexLaws : Bool
    agdaPrimitiveRealExtractionCompilerOwned : Bool
    agdaComplexExtractionDerivedFromRealLaws : Bool
    agdaDiscriminantNumeratorTransportDerived : Bool

    bishopVendoredEvaluatorOwnedInLean : Bool
    bishopEvaluatorFaithfulOnSetoidClasses : Bool
    bishopExpSemanticCompilerOwnedInLean : Bool
    bishopSinCosSemanticCompilerOwnedInLean : Bool
    bishopMachinPiSemanticCompilerOwnedInLean : Bool
    round11MachinSourceBindingCompilerOwnedInLean : Bool
    round11RouteBCapstoneOwnedInLean : Bool
    eta24PinnedWeight12ReflectionOwnedInLean : Bool
    eta24PinnedFixedLocusOwnedInLean : Bool
    eta24BranchFreePhaseExponentialOwnedInLean : Bool
    eta24IntegerPiCongruenceOwnedInLean : Bool
    eta24ConcreteSixfoldPhaseOwnedInLean : Bool

    agdaBishopSetoidComplexOwned : Bool
    agdaBishopSetoidEisensteinRecurrenceOwned : Bool
    agdaRound11MachinSourceCapstoneOwned : Bool

    extractedAgdaSurfaceInhabitedInLean : Bool
    actualRound11MachinSourceBindingInLean : Bool
    agdaLeanCarrierSameObjectProved : Bool
    leanTheoremAutomaticallyPromotesAgdaAnalyticLeaf : Bool
    deltaE4E6IdentityAvailableAtPinnedMathlib : Bool
    eta24NormalizedDeltaSameObjectProved : Bool
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
    "Integration.MoonshineEta24Pinned"
    "Integration.MoonshineEta24SixfoldPhase"
    "Integration.MoonshineEisensteinAgdaTarget"
    "DASHI.Moonshine.JInvariantEisensteinAgdaLeanExtractionExact"
    "v4.28.0"
    true true true true true true true true true true true true true true
    true true true true true true true true
    true true true true true true true
    true true true true true true true
    true true true true true
    true true true
    false false false false false true false
    "Route B is source-pinned and setoid-native. Lean owns the faithful evaluator for the vendored Bishop regular-rational reals, derives the vendored arithmetic operations and Bishop exp/sin/cos/Machin-pi classical semantics from the repository's concrete convergence witnesses, and compiles one Round11MachinSourceBinding through the literal source q/E4/E6/normalized-Delta sequence to Mathlib E4/E6 and the canonical normalized Delta target. Agda owns the sibling Bishop setoid complex package, literal sigma3/sigma5 recurrences, normalized source Delta and the Round11+Machin source capstone. Independently, at the existing Mathlib v4.28.0 pin, Lean now proves eta^24 weight-12 reflection/fixed-locus identities and a branch-safe sixfold phase theorem: on normSq(tau)=1, arg(eta^24(tau)) + 6 arg(tau) = k*pi for some integer k, equivalently arg(eta^24(tau)) = -6 arg(tau) + k*pi. No continuous argument branch is chosen. The cross-language source gate remains inhabiting the exact Lean binding from the Agda receipt. The formerly independent same-object seam eta^24 = normalized(E4^3-E6^2)/1728 is now source-written closed in the pinned Lean companion: eta^24 is packaged as a weight-12 cusp form with first q coefficient 1; every level-one weight-12 cusp form is proved to be a scalar multiple of eta^24 using the pin-local weight-zero constancy theorem; the normalized E4/E6 target is packaged as a cusp form with first q coefficient 1; and coefficient comparison forces the scalar to 1. Upstream Mathlib's later Discriminant/DimensionFormula package is still absent at v4.28.0 and no dependency bump or automatic Agda theorem promotion is inferred. The remaining cross-language gate is the exact Round11Machin source replay/binding receipt, not a classical Delta identity."
