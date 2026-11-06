{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21CompilerRepairGovernanceExact where

------------------------------------------------------------------------
-- KARP21 O / R / C / S / L / P / G / F: CONCRETE REPAIR PROVENANCE.
--
-- This is a source-native status/diagnostic ledger, not an Agda
-- compiler receipt. The Agda grammar must accept this file before
-- even its small propositions can be called kernel-checked.
--
-- In-repo reuse/authority boundaries:
--   DASHI.Core.AuthorityBoundary: source citation != artifact authority.
--   DASHI.Core.SequentialConsumerExperimentPlannerExact: observation
--     -> discriminating repair -> checked consumer.
--   dashi_lean4 AgdaMirror.AuthorityBoundary and LoomRelationAlgebra
--     are downstream parallels, not Golden authorities for this lane.
--
-- The O/R/C/S/L/P/G/F address records original observed failures;
-- source edits do not mutate the historical diagnostic record.
-- Promotion requires an EXTERNAL genuine compiler receipt. No claim
-- below constructs one from a Boolean flag or a textual SHA alone.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Empty using (⊥)

data RepairIssue : Set where
  reservedCookConstructor : RepairIssue
  gammaAdditionMissing : RepairIssue
  finImplicitArgument : RepairIssue
  cliqueRefinementMissing : RepairIssue
  refereeSelfRecursion : RepairIssue

-- The initial F is a historical five-issue observation, not a
-- representation of the present number of remaining compiler errors.
reportedGaps : List RepairIssue
reportedGaps =
  reservedCookConstructor ∷
  gammaAdditionMissing ∷
  finImplicitArgument ∷
  cliqueRefinementMissing ∷
  refereeSelfRecursion ∷ []

reportedGapCountExactlyFive : length reportedGaps ≡ suc (suc (suc (suc (suc zero))))
reportedGapCountExactlyFive = refl

data VerificationStage : Set where
  compilerObserved : VerificationStage
  sourcePatched : VerificationStage
  pythonPreflightPassed : VerificationStage
  agdaKernelAccepted : VerificationStage

-- A stage tag is a status coordinate, NEVER a compiler receipt.
canPromoteWithoutReceipt : VerificationStage → Bool
canPromoteWithoutReceipt compilerObserved = false
canPromoteWithoutReceipt sourcePatched = false
canPromoteWithoutReceipt pythonPreflightPassed = false
canPromoteWithoutReceipt agdaKernelAccepted = false

sourcePatchDoesNotPromote :
  canPromoteWithoutReceipt sourcePatched ≡ false
sourcePatchDoesNotPromote = refl

pythonPreflightDoesNotPromote :
  canPromoteWithoutReceipt pythonPreflightPassed ≡ false
pythonPreflightDoesNotPromote = refl

evenKernelTagDoesNotPromote :
  canPromoteWithoutReceipt agdaKernelAccepted ≡ false
evenKernelTagDoesNotPromote = refl

record LocalEnvironment : Set where
  constructor localEnvironment
  field
    observedHead : String
    agdaVersion : String
    pythonVersion : String
    parallelRunner : String
    pythonEnvironment : String

record CompilerRepairLane : Set where
  constructor compilerRepairLane
  field
    O-organization : String
    R-request : String
    C-sourcePaths : List String
    S-observation : LocalEnvironment
    L-verificationLattice : List VerificationStage
    P-proposal : String
    G-failClosed : Bool
    F-observedGaps : List RepairIssue

-- Exact original reported coordinates. The branch's current head must
-- be obtained from GitHub/git after repairs; do not replace observedHead.
reportedKarp21RepairLane : CompilerRepairLane
reportedKarp21RepairLane =
  compilerRepairLane
    "DASHI / Karp-21 Formalization Lane"
    "PR #1445 chatgpt/karp21-reduction-transport"
    ("DASHI/Mathematics/Complexity/CookLevinCircuitGCTBoundary.agda" ∷
     "DASHI/Mathematics/Complexity/BooleanFormulaSATSelfReductionExact.agda" ∷
     "DASHI/Mathematics/Complexity/Karp21GammaBinaryRoundTripExact.agda" ∷
     "DASHI/Mathematics/Complexity/Karp21BinaryFinMaterializationCostExact.agda" ∷
     "DASHI/Mathematics/Complexity/Karp21CliqueVertexCoverExact.agda" ∷
     "scripts/referee_karp21_maxcut.sh" ∷
     "scripts/check_karp21_referee_no_agda.py" ∷ [])
    (localEnvironment
      "2340ed9374f825af7e61d38a7319da5901e2dded"
      "Agda 2.9.0" "Python 3.14.8"
      "scripts/run_agda29_parallel_check.sh"
      ".venv")
    (compilerObserved ∷ sourcePatched ∷
     pythonPreflightPassed ∷ agdaKernelAccepted ∷ [])
    "Repair five concrete diagnostics on PR #1445 and re-run exact-head checks"
    true
    reportedGaps

failClosedGovernanceIsDeclared :
  CompilerRepairLane.G-failClosed reportedKarp21RepairLane ≡ true
failClosedGovernanceIsDeclared = refl

-- An Agda-side promotion contract parametrized by a trusted external
-- receipt carrier. The carrier must be supplied by the actual referee;
-- this module has NO constructor that turns source/status data into it.
record KernelPromotion (TrustedReceipt : Set) : Set where
  constructor kernelPromotion
  field
    trustedReceipt : TrustedReceipt
    compiledModule : String
    checkedHead : String

-- The compilation witness is intentionally absent at the historical
-- failed head. This is a schema to consume future receipts, not a
-- constructed successful compilation.
