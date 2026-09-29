module DASHI.Mathematics.Complexity.PNotEqualsNPQ1RootedWorkGateExact where

------------------------------------------------------------------------
-- ROOT-REACHABLE CONSTRUCTION: EXECUTABLE WORK LEDGER + STRICT GATE
--
-- Three concrete charges are combined:
--
--   * root-generated Shannon enumeration + truth-table deduplication;
--   * eager Boolean syntax visits on EVERY raw truth-table row;
--   * two indexed-key transitions for each merged source, with actual
--     finite-key scanner comparisons and table restriction output widths.
--
-- The builder may return nothing when its strict limit is exhausted.
--
-- IMPORTANT: this accounting counts declared high-level operations.
-- Assignment access, allocation/copying, proof normalization, concrete tape
-- machine execution, and Q1's ALL-overhead recurrence are not certified here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.List.Base using (length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (_<_)
import Data.Nat.Properties as NatP
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Data.Product using (Σ; _,_; proj₁; proj₂)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPExactResidualSummaryBitLowerBoundExact as Bits
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1CanonicalTruthTableMergeExact as Merge
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1RootedExhaustiveMergeExact as Root
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1TruthTableRepairGeneratorExact as Truth
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ReachableKeySearchExact as Search
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1InstrumentedKeySearchExact as Instrumented
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1InstrumentedFormulaEvaluationExact as Eval

------------------------------------------------------------------------
-- Actual key-only transition comparison charge on one source key.
------------------------------------------------------------------------

transitionLookupCharge :
  ∀ {remaining : Nat} →
  Bool →
  Merge.SemanticKey (suc remaining) →
  List (Merge.SemanticKey remaining) →
  Nat
transitionLookupCharge {remaining} action source targetKeys =
  Bits.bitCardinality remaining
  +
  Instrumented.scanKeyBitEnvelope
    (Truth.restrictTruthTable action source)
    targetKeys

------------------------------------------------------------------------
-- The gate now charges THE SAME recursion used by the instrumented scanner.
-- The old independent declaration is recovered as a proved equation.
------------------------------------------------------------------------

transitionLookupChargeMatchesDeclared :
  ∀ {remaining : Nat}
    (action : Bool)
    (source : Merge.SemanticKey (suc remaining))
    (targetKeys : List (Merge.SemanticKey remaining)) →
  transitionLookupCharge action source targetKeys
  ≡
  Bits.bitCardinality remaining
    +
  Search.findKeyFullWidthCharge
    (Truth.restrictTruthTable action source)
    targetKeys
transitionLookupChargeMatchesDeclared
    {remaining = remaining} action source targetKeys =
  cong
    (λ count → Bits.bitCardinality remaining + count)
    (Instrumented.scanKeyBitEnvelopeMatchesDeclared
      (Truth.restrictTruthTable action source)
      targetKeys)

sourceTransitionCharge :
  ∀ {remaining : Nat} →
  Merge.SemanticKey (suc remaining) →
  List (Merge.SemanticKey remaining) →
  Nat
sourceTransitionCharge source targetKeys =
  transitionLookupCharge false source targetKeys
  +
  transitionLookupCharge true source targetKeys

mergedLayerTransitionCharge :
  ∀ {remaining : Nat} →
  List (Merge.SemanticKey (suc remaining)) →
  List (Merge.SemanticKey remaining) →
  Nat
mergedLayerTransitionCharge [] targets = zero
mergedLayerTransitionCharge (source ∷ rest) targets =
  sourceTransitionCharge source targets
  +
  mergedLayerTransitionCharge rest targets

------------------------------------------------------------------------
-- Work over the ACTUAL root-generated layers, without postulated inputs.
------------------------------------------------------------------------

rootedAllLayerEvaluationWork :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  Root.DescentPath root remaining →
  Nat
rootedAllLayerEvaluationWork Root.atRoot =
  Eval.rootedLayerEvaluationWork Root.atRoot
rootedAllLayerEvaluationWork (Root.descend previous) =
  rootedAllLayerEvaluationWork previous
  +
  Eval.rootedLayerEvaluationWork (Root.descend previous)

rootedAllLayerTransitionWork :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  Root.DescentPath root remaining →
  Nat
rootedAllLayerTransitionWork Root.atRoot =
  zero
rootedAllLayerTransitionWork (Root.descend previous) =
  rootedAllLayerTransitionWork previous
  +
  mergedLayerTransitionCharge
    (Root.rootedMergedSemanticKeys previous)
    (Root.rootedMergedSemanticKeys (Root.descend previous))

rootedDeclaredOperationalWork :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  Root.DescentPath root remaining →
  Nat
rootedDeclaredOperationalWork path =
  Root.rootedDeclaredWork path
  +
  rootedAllLayerEvaluationWork path
  +
  rootedAllLayerTransitionWork path

------------------------------------------------------------------------
-- Distinguish termination of exhaustive enumeration from strict fit.
------------------------------------------------------------------------

budgetedRootedKeys :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (path : Root.DescentPath root remaining)
    (budget : Nat) →
  Maybe
    (Σ
      (List (Merge.SemanticKey remaining))
      (λ keys →
        rootedDeclaredOperationalWork path < budget))
budgetedRootedKeys path budget
    with NatP._<?_ (rootedDeclaredOperationalWork path) budget
... | yes fits =
  just (Root.rootedMergedSemanticKeys path , fits)
... | no doesNotFit =
  nothing

rootedSuccessCarriesStrictReceipt :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {path : Root.DescentPath root remaining}
    {budget : Nat}
    {result :
      Σ
        (List (Merge.SemanticKey remaining))
        (λ keys →
          rootedDeclaredOperationalWork path < budget)} →
  budgetedRootedKeys path budget ≡ just result →
  rootedDeclaredOperationalWork path < budget
rootedSuccessCarriesStrictReceipt {result = result} successful =
  proj₂ result

------------------------------------------------------------------------
-- This is a genuine decidable budget guard on executable rooted-layer data,
-- but it is NOT yet the Q1 direct-DP constructor with its charged machine
-- semantics or a theorem that the guard passes on the candidate root.
------------------------------------------------------------------------
