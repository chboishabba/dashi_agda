module DASHI.Reasoning.ExceptionalE8AlbertF4IrreducibleFrontierExact where

------------------------------------------------------------------------
-- IRREDUCIBLE ORIGINAL-Q EXCEPTIONAL CLASSIFICATION FRONTIER
--
-- The historical exceptional max-cut lists the three still-unpaid named
-- conclusions (Der(J):F4-form, Aut(J):F4-group, cubic structure:E6-group).
-- Companion Lean #52 now sharpens their dependency structure: they are NOT
-- three independent research leaves.  All three compile from one dependent
-- SAME-object descent/classification witness.
--
-- This owner supersedes only the roadmap shape, not proof authority.  The final
-- classification witness remains unpaid; Lean source is retained as a
-- cross-prover receipt and does not become an Agda theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.ExceptionalE8AlbertF4ClassificationMaxCutExact as Previous
import DASHI.Reasoning.AlbertF4LeanIrreducibleClassificationFrontierReceiptExact as LeanFrontier

record Boundary : Set where
  constructor boundary
  field
    previousLocalExceptionalStructureExhausted : Bool
    nativeQAlbertInternalHypothesesPaid : Bool
    originalQFrontierIsOneDependentInput : Bool
    oneInputCompilesAllThreeNamedConclusionsInLeanSource : Bool
    threeNamedClassificationConclusionsStillUnpaid : Bool
    threeNamedConclusionsAreIndependentResearchLeaves : Bool
    finalDependentClassificationWitnessPaid : Bool
    leanClassificationProofAuthorityImportedIntoAgda : Bool
    nextResidual : String
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary = boundary
  true true
  (LeanFrontier.terminalResidualReducedToSingleDependentWitness LeanFrontier.canonicalBoundary)
  (LeanFrontier.singleWitnessCompilesThreeNamedConclusions LeanFrontier.canonicalBoundary)
  true false false
  (LeanFrontier.leanProofAuthorityImportedIntoAgda LeanFrontier.canonicalBoundary)
  "Obtain one actual formal characteristic-zero Albert/F4/E6 classification theorem together with a proof-relevant SAME-object descent payment for the native rational H3(O_Q) carrier/actions. That single dependent witness discharges all three named original-Q conclusions. Do not schedule more root counts, Q(i) splitting diagnostics, real-place signatures, dimensions or source inventories as substitutes for the witness."

previousBoundary : Previous.ExceptionalClassificationBoundary
previousBoundary = Previous.canonicalExceptionalClassificationBoundary
