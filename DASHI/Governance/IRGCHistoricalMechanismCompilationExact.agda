module DASHI.Governance.IRGCHistoricalMechanismCompilationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.HistoricalMechanismCompilerExact as Compiler
import DASHI.Governance.IRGCOpenLetter2026PrimarySpanReceiptsExact as Spans
import DASHI.Governance.IRGCReviewedEventDualChronologyPacketExact as Packet
import DASHI.Governance.IranianRevolutionaryGenealogyReviewedJoinExact as Joins

------------------------------------------------------------------------
-- IRGC HISTORICAL-MECHANISM COMPILER INSTANCE
--
-- Current state:
--   source totality / selected source spans : paid
--   reviewed genealogy join basis           : paid
--   event-time / knowledge-time separation  : paid
--   causal mechanism into the 2026 letter   : NOT PAID
--
-- Therefore the compiler must abstain.
------------------------------------------------------------------------

irgcSourceTotalReceipt : Compiler.SourceTotalReceipt
irgcSourceTotalReceipt =
  Compiler.source-total-receipt
    "packet:irgc:selected-primary-spans"
    true refl
    false refl

irgcReviewedJoinReceipt : Compiler.ReviewedJoinReceipt
irgcReviewedJoinReceipt =
  Joins.khomeiniJoinCompilerReceipt

irgcDualChronologyReceipt : Compiler.DualChronologyReceipt
irgcDualChronologyReceipt =
  Compiler.dual-chronology-receipt
    "chronology:irgc:historical-knowledge-vs-2026-letter"
    "event-time:2026-09-29:irgc-letter"
    "knowledge-time:2000/2014/2017/2018 scholarship plus 2026 reporting"
    false refl

irgcCausalResidual : Compiler.MechanismResidual
irgcCausalResidual =
  Compiler.mechanism-residual
    Compiler.causalMechanismResidual
    "residual:iranian-revolutionary-grammar-to-irgc-2026"
    "a reviewed mechanism receipt showing which historically inherited relation is actually instantiated in the 2026 letter, including a counter-hypothesis and provenance chain"
    "compare the paid primary spans against the reviewed genealogy relations and test alternative explanations such as independent Quranic/theological derivation, generic anti-imperial rhetoric, strategic wartime messaging, and convergent elite/populist framing"
    false refl

currentCompilation : Compiler.MechanismCompilation
currentCompilation =
  Compiler.abstain (irgcCausalResidual ∷ [])

record IRGCCompilationState : Set where
  constructor irgc-compilation-state
  field
    selectedPrimarySpansPaid : Bool
    reviewedGenealogyJoinPaid : Bool
    dualChronologyPaid : Bool
    causalMechanismPaid : Bool
    historicalMechanismClosed : Bool
    politicalVerdictCreated : Bool

canonicalIRGCCompilationState : IRGCCompilationState
canonicalIRGCCompilationState =
  irgc-compilation-state
    true true true false false false

closedWitnessRequiresFutureCausalReceipt :
  Compiler.CausalMechanismReceipt →
  Compiler.HistoricalMechanismWitness
closedWitnessRequiresFutureCausalReceipt causal =
  Compiler.compileHistoricalMechanism
    "mechanism:iranian-revolutionary-grammar-to-irgc-2026"
    irgcSourceTotalReceipt
    irgcReviewedJoinReceipt
    irgcDualChronologyReceipt
    causal
