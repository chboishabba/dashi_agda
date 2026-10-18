module DASHI.Interop.BishopMachinPiLeanSemanticReceiptExact where

------------------------------------------------------------------------
-- BISHOP MACHIN PI: LEAN <-> AGDA CROSS-PROVER RECEIPT
--
-- This is a provenance/status owner, not an Agda proof of the Lean theorem.
--
-- Agda source objects:
--   DASHI.Foundations.BishopMachinArctanConstructionExact
--     bishopAtanOneFifth
--     bishopAtanOneTwoHundredThirtyNinth
--     bishopMachinPi
--
-- Agda convergence receipts:
--   DASHI.Moonshine.BishopRound11MachinSetoidComplexInstanceExact
--     round11MachinAtanOneFifthConverges
--     round11MachinAtanOneTwoHundredThirtyNinthConverges
--
-- Lean semantic compiler:
--   chboishabba/dashi_lean4
--   Integration/BishopVendoredMachinPiSemantics.lean
--     eval_atan_eq_real_arctan
--     eval_atanOneFifth
--     eval_atanOneTwoHundredThirtyNinth
--     eval_machinPi_eq_real_pi
--
-- Lean source head carrying the direct route-B convergence->extraction wrapper:
--   126aaa72dbb7353be42f913122de1b36f2475a46
--
-- Firewalls:
-- * source-written Lean theorem != observed Lean kernel receipt;
-- * Lean theorem != Agda kernel theorem;
-- * matching formulas/names != cross-prover same-object transport;
-- * this receipt does not fabricate a serialized Agda->Lean witness.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

record BishopMachinPiLeanSemanticReceipt : Set where
  constructor bishop-machin-pi-lean-semantic-receipt
  field
    leanRepository : String
    leanIntegratedHead : String
    leanSourcePath : String

    agdaMachinSourcePath : String
    agdaRouteBSourceInstancePath : String

    leanAtanSemanticTheorem : String
    leanOneFifthSemanticTheorem : String
    leanOne239SemanticTheorem : String
    leanMachinPiSemanticTheorem : String
    leanDirectExtractionCompiler : String

    agdaOneFifthSourceObject : String
    agdaOne239SourceObject : String
    agdaMachinPiSourceObject : String
    agdaOneFifthConvergenceTheorem : String
    agdaOne239ConvergenceTheorem : String

    leanTheoremSourceWritten : Bool
    leanKernelReceiptObserved : Bool
    agdaKernelReceiptForLeanTheoremObserved : Bool
    serializedCrossProverSameObjectWitnessObserved : Bool

open BishopMachinPiLeanSemanticReceipt public

currentBishopMachinPiLeanSemanticReceipt :
  BishopMachinPiLeanSemanticReceipt
currentBishopMachinPiLeanSemanticReceipt =
  bishop-machin-pi-lean-semantic-receipt
    "chboishabba/dashi_lean4"
    "126aaa72dbb7353be42f913122de1b36f2475a46"
    "Integration/BishopVendoredMachinPiSemantics.lean"
    "DASHI/Foundations/BishopMachinArctanConstructionExact.agda"
    "DASHI/Moonshine/BishopRound11MachinSetoidComplexInstanceExact.agda"
    "Integration.BishopVendoredMachinPiSemantics.eval_atan_eq_real_arctan"
    "Integration.BishopVendoredMachinPiSemantics.eval_atanOneFifth"
    "Integration.BishopVendoredMachinPiSemantics.eval_atanOneTwoHundredThirtyNinth"
    "Integration.BishopVendoredMachinPiSemantics.eval_machinPi_eq_real_pi"
    "Integration.BishopVendoredTranscendentalExtraction.primitiveExtractionFromConvergence"
    "DASHI.Foundations.BishopMachinArctanConstructionExact.bishopAtanOneFifth"
    "DASHI.Foundations.BishopMachinArctanConstructionExact.bishopAtanOneTwoHundredThirtyNinth"
    "DASHI.Foundations.BishopMachinArctanConstructionExact.bishopMachinPi"
    "DASHI.Moonshine.BishopRound11MachinSetoidComplexInstanceExact.round11MachinAtanOneFifthConverges"
    "DASHI.Moonshine.BishopRound11MachinSetoidComplexInstanceExact.round11MachinAtanOneTwoHundredThirtyNinthConverges"
    true
    false
    false
    false

record BishopMachinPiCrossProverBoundary : Set where
  constructor bishop-machin-pi-cross-prover-boundary
  field
    agdaMachinConstructionOwned : Bool
    agdaMachinConvergenceOwned : Bool
    leanClassicalArctanSemanticCompilerSourceOwned : Bool
    leanMachinPiSemanticCompilerSourceOwned : Bool
    leanConvergenceToPrimitiveExtractionSourceOwned : Bool

    leanKernelReceiptOwnedHere : Bool
    agdaImportsLeanProof : Bool
    sameObjectCrossProverSerializationOwned : Bool

canonicalBishopMachinPiCrossProverBoundary :
  BishopMachinPiCrossProverBoundary
canonicalBishopMachinPiCrossProverBoundary =
  bishop-machin-pi-cross-prover-boundary
    true true true true true
    false false false
