module DASHI.Interop.LeanRound11MachinCanonicalRouteBParityExact where

------------------------------------------------------------------------
-- LEAN ROUND11 / MACHIN CANONICAL ROUTE-B PARITY CAPSTONE
--
-- Lean source lane:
--   chboishabba/dashi_lean4
--   branch: agent/moonshine-eisenstein-analytic-20260922
--
-- This receipt records the current cross-prover state after the vendored
-- Bishop route was completed on the Lean side.
--
-- Important distinction:
--
--   mathematical inhabitance / same-object compilation
--     != generated replay of named Agda declarations
--     != an observed exact-head Lean kernel/Actions receipt.
--
-- The first is now owned.  The latter two remain explicit false gates until
-- an actual provenance replay / CI run is observed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

record LeanRound11MachinCanonicalRouteBParity : Set where
  constructor lean-round11-machin-canonical-route-b-parity
  field
    leanRepository : String
    leanBranch : String
    mathlibPin : String

    bishopSubmoduleCommitPinned : Bool
    bishopRegularRealEvaluatorOwned : Bool
    bishopSetoidRepresentativeIndependenceOwned : Bool
    bishopCompletionEquivalentToLeanReal : Bool
    concreteVendoredArithmeticMirrorOwned : Bool
    exactResampledAdditionPreserved : Bool
    exactCanonicalBoundMultiplicationPreserved : Bool

    bishopQuantitativeConvergenceTransportOwned : Bool
    bishopExponentialClassicalSemanticsOwned : Bool
    bishopSineClassicalSemanticsOwned : Bool
    bishopCosineClassicalSemanticsOwned : Bool
    bishopMachinPiClassicalSemanticsOwned : Bool

    canonicalRound11MachinBindingInhabited : Bool
    everyAdmissibleBindingUniqueUpToBishopEquivalence : Bool
    mappedSemanticsIndependentOfAdmissibleReplay : Bool

    literalSourceQTransportOwned : Bool
    literalSourceE4TransportOwned : Bool
    literalSourceE6TransportOwned : Bool
    mappedSourceE4ConvergesToMathlibE4 : Bool
    mappedSourceE6ConvergesToMathlibE6 : Bool
    mappedSourceDiscriminantConverges : Bool
    mappedSourceNormalizedDeltaConverges : Bool

    eta24SameObjectWithNormalizedE4E6Delta : Bool
    normalizedDeltaNonvanishingOwned : Bool
    normalizedDeltaInverseConjugationOwned : Bool
    normalizedDeltaUnitCircleFixedValueOwned : Bool
    normalizedDeltaSixfoldPhaseOwned : Bool
    normalizedDeltaArgModuloPiOwned : Bool

    contentAddressedAgdaManifestOwned : Bool
    recursiveAgdaImportClosureVerifierSourceOwned : Bool
    generatedReplayCertificateSourceOwned : Bool
    focusedRouteBKernelProbeSourceOwned : Bool
    focusedRouteBAxiomAuditSourceOwned : Bool
    focusedRouteBWorkflowSourceOwned : Bool

    generatedAgdaReplayObserved : Bool
    exactHeadLeanKernelReceiptObserved : Bool

    remainingBoundary : String

open LeanRound11MachinCanonicalRouteBParity public

canonicalLeanRound11MachinCanonicalRouteBParity :
  LeanRound11MachinCanonicalRouteBParity
canonicalLeanRound11MachinCanonicalRouteBParity =
  lean-round11-machin-canonical-route-b-parity
    "chboishabba/dashi_lean4"
    "agent/moonshine-eisenstein-analytic-20260922"
    "v4.28.0"

    true true true true true true true
    true true true true true
    true true true
    true true true true true true true
    true true true true true true
    true true true true true true

    false false

    "The mathematical route-B seam is closed on the Lean side: vendored Bishop regular reals are completion-equivalent to Lean Real; the source arithmetic and exp/sin/cos/Machin-pi semantics compile; the canonical Round11 binding is inhabited and unique up to Bishop equivalence; literal source q/E4/E6/Delta truncations map to the Mathlib targets; eta^24 equals the normalized E4/E6 Delta at the pinned Mathlib version; inverse-conjugation, fixed-locus, nonvanishing and sixfold phase are theorem-owned. Remaining evidence is operational provenance only: run the content-addressed Agda replay verifier and focused Lean kernel/axiom workflow at an exact head, then record those observed receipts. No generated replay or exact-head kernel receipt is inferred from source presence alone."
