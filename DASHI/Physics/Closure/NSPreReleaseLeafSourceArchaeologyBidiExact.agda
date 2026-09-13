module DASHI.Physics.Closure.NSPreReleaseLeafSourceArchaeologyBidiExact where

------------------------------------------------------------------------
-- PRE-RELEASE SOURCE-TERM ARCHAEOLOGY FOR THE R504 TERMINAL LEAVES
--
-- Purpose:
--   distinguish an unrun/OOM certification state from actual source
--   inhabitation of the two decisive analytic leaves identified before the
--   2026-09-08 external release.
--
-- Inspected historical snapshot:
--   67831b2b1ada78f08c5ad092637afeb9e2a80180
--
-- Leaf A source fact:
--   R503 defines DirectOffDiagonalBudget and proves directBudgetBuildsR415.
--   The compiler is real source code, but the decisive cutoff-uniform bound is
--   a FIELD of DirectOffDiagonalBudget.  Thus the compiler alone does not
--   construct the analytic bound.
--
-- Leaf B source fact:
--   R414 defines CriticalSliceOnLiteralR406 and proves the algebraic transport
--   to the uniform critical barrier.  The phase-sensitive estimate
--   signedProductionEstimateByLiteralRemainder is a FIELD of that source record.
--   Thus the downstream algebra is implemented, while this inequality remains
--   an input unless a concrete source inhabitant is found elsewhere.
--
-- Repository-wide symbol search at the current indexed head finds the exact
-- analytic constructor names only in their defining modules.  This is evidence
-- against, but not a proof of absence from every deleted/unmerged historical
-- branch.  Therefore historical priority remains source-archaeology-pending,
-- not mathematically disproved merely because old closure booleans were false.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

data SourceLeafStatus : Set where
  compilerPresentAnalyticInputField : SourceLeafStatus
  concreteInhabitantLocated : SourceLeafStatus
  historicalBranchSearchPending : SourceLeafStatus

leafASourceStatus : SourceLeafStatus
leafASourceStatus = compilerPresentAnalyticInputField

leafBSourceStatus : SourceLeafStatus
leafBSourceStatus = compilerPresentAnalyticInputField

currentPrioritySourceStatus : SourceLeafStatus
currentPrioritySourceStatus = historicalBranchSearchPending

roundPreReleaseLeafACompilerPresent : Bool
roundPreReleaseLeafACompilerPresent = true

roundPreReleaseLeafBCompilerPresent : Bool
roundPreReleaseLeafBCompilerPresent = true

roundPreReleaseLeafAConcreteInhabitantLocated : Bool
roundPreReleaseLeafAConcreteInhabitantLocated = false

roundPreReleaseLeafBConcreteInhabitantLocated : Bool
roundPreReleaseLeafBConcreteInhabitantLocated = false

roundFalseLedgerMeansMathematicalNegation : Bool
roundFalseLedgerMeansMathematicalNegation = false

roundHistoricalBranchSearchComplete : Bool
roundHistoricalBranchSearchComplete = false

roundPreReleaseLeafACompilerPresentIsTrue :
  roundPreReleaseLeafACompilerPresent ≡ true
roundPreReleaseLeafACompilerPresentIsTrue = refl

roundPreReleaseLeafBCompilerPresentIsTrue :
  roundPreReleaseLeafBCompilerPresent ≡ true
roundPreReleaseLeafBCompilerPresentIsTrue = refl

roundFalseLedgerMeansMathematicalNegationIsFalse :
  roundFalseLedgerMeansMathematicalNegation ≡ false
roundFalseLedgerMeansMathematicalNegationIsFalse = refl
