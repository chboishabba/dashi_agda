module DASHI.Mathematics.Complexity.PNotEqualsNPRewrittenRepresentativeCandidateExact where

------------------------------------------------------------------------
-- REPAIRED Q1 REPRESENTATIVE CARRIER
--
-- RawRestrictionRepresentativeNoGoExact proves that a raw Shannon restriction
-- never has smaller Cook syntax-node count than its root.  Therefore the old
-- carrier
--
--   reachable raw restriction + strictly-smaller raw restriction
--
-- is empty.
--
-- Repair:
--   raw reachable restriction = provenance / state-membership witness
--   RewriteProgram           = answer-blind normalization witness
--   literal terminal constant = strict semantic representative
--
-- The only global strictness premise is that the root has more than one Cook
-- syntax node.  Every normalized representative is a literal constant of node
-- count one.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (_<_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as Size
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family
import DASHI.Mathematics.Complexity.PNotEqualsNPTransitionGeneratedRestrictionQuotientExact as Generated
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingRestrictionQuotientExact as Quotient
import DASHI.Mathematics.Complexity.PNotEqualsNPStrictSemanticRepresentativeQuotientExact as Strict
import DASHI.Mathematics.Complexity.PNotEqualsNPAnswerBlindStructuralRewriteMachineExact as Rewrite
import DASHI.Mathematics.Complexity.PNotEqualsNPRewriteGeneratedQ1DiscoveryExact as RewriteGenerated

------------------------------------------------------------------------
-- Equivalence composition.
------------------------------------------------------------------------

composeCookEquivalent :
  ∀ {left middle right : Cook.BooleanFormula} →
  Strict.CookSatisfiabilityEquivalent left middle →
  Strict.CookSatisfiabilityEquivalent middle right →
  Strict.CookSatisfiabilityEquivalent left right
composeCookEquivalent leftMiddle middleRight =
  (λ leftSat →
    proj₁ middleRight
      (proj₁ leftMiddle leftSat))
  ,
  (λ rightSat →
    proj₂ leftMiddle
      (proj₂ middleRight rightSat))

------------------------------------------------------------------------
-- A RewriteProgram proves equivalence to its literal terminal constant.
------------------------------------------------------------------------

rewriteProgramEquivalentToTerminal :
  ∀ {formula : Cook.BooleanFormula}
    (program : Rewrite.RewriteProgram formula) →
  Strict.CookSatisfiabilityEquivalent
    formula
    (Cook.constant
      (Rewrite.rewriteProgramTruth program))
rewriteProgramEquivalentToTerminal
    (Rewrite.halt value) =
  (λ satisfiable → satisfiable)
  ,
  (λ satisfiable → satisfiable)
rewriteProgramEquivalentToTerminal
    (Rewrite.step rewrite rest) =
  composeCookEquivalent
    (Rewrite.rewriteSatisfiabilityEquivalent rewrite)
    (rewriteProgramEquivalentToTerminal rest)

------------------------------------------------------------------------
-- Indexed semantic equivalence -> Cook semantic equivalence.
------------------------------------------------------------------------

indexedEquivalentToCookEquivalent :
  ∀ {leftVariables rightVariables : Nat}
    {left : SAT.BooleanFormula leftVariables}
    {right : SAT.BooleanFormula rightVariables} →
  Quotient.SatisfiabilityEquivalent left right →
  Strict.CookSatisfiabilityEquivalent
    (Bridge.indexedToCook left)
    (Bridge.indexedToCook right)
indexedEquivalentToCookEquivalent
    {left = left}
    {right = right}
    equivalent =
  forward , backward
  where
    forward :
      Cook.Satisfiable (Bridge.indexedToCook left) →
      Cook.Satisfiable (Bridge.indexedToCook right)
    forward leftCook =
      Bridge.indexedSatisfyingGivesCookSatisfiable
        right
        (proj₁ equivalent
          (Bridge.cookSatisfiableIndexedFormulaGivesIndexedSatisfying
            left
            leftCook))

    backward :
      Cook.Satisfiable (Bridge.indexedToCook right) →
      Cook.Satisfiable (Bridge.indexedToCook left)
    backward rightCook =
      Bridge.indexedSatisfyingGivesCookSatisfiable
        left
        (proj₂ equivalent
          (Bridge.cookSatisfiableIndexedFormulaGivesIndexedSatisfying
            right
            rightCook))

------------------------------------------------------------------------
-- One state: reachable raw provenance + normalization program.
------------------------------------------------------------------------

record NormalizedReachableState
    {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (generated : Generated.TransitionGeneratedRestrictionQuotient root)
    (state : Fin (Generated.stateCount generated)) : Set₁ where
  constructor normalized-reachable-state
  field
    currentVariables : Nat
    rawFormula : SAT.BooleanFormula currentVariables

    rawDerivation :
      Family.RestrictionDerivation root rawFormula

    rawSelectsState :
      Generated.generatedSelect
        (Generated.rootState generated)
        (Generated.step generated)
        rawDerivation
      ≡
      state

    normalization :
      Rewrite.RewriteProgram
        (Bridge.indexedToCook rawFormula)

open NormalizedReachableState public

------------------------------------------------------------------------
-- Repaired whole quotient.
------------------------------------------------------------------------

record RewrittenRepresentativeCandidate
    {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables) : Set₁ where
  constructor rewritten-representative-candidate
  field
    generatedQuotient :
      Generated.TransitionGeneratedRestrictionQuotient root

    rootNontrivial :
      suc zero
      <
      Size.formulaNodeCount
        (Bridge.indexedToCook root)

    normalizedState :
      (state : Fin (Generated.stateCount generatedQuotient)) →
      NormalizedReachableState generatedQuotient state

open RewrittenRepresentativeCandidate public

normalizedTruth :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : RewrittenRepresentativeCandidate root)
    (state : Fin (Generated.stateCount (generatedQuotient candidate))) →
  Agda.Builtin.Bool.Bool
normalizedTruth candidate state =
  Rewrite.rewriteProgramTruth
    (normalization
      (normalizedState candidate state))

rewrittenRepresentative :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : RewrittenRepresentativeCandidate root) →
  Fin (Generated.stateCount (generatedQuotient candidate)) →
  Cook.BooleanFormula
rewrittenRepresentative candidate state =
  Cook.constant (normalizedTruth candidate state)

------------------------------------------------------------------------
-- Every reachable formula factors semantically through the rewritten constant
-- of its generated state.
------------------------------------------------------------------------

rewrittenRepresentativeEquivalent :
  ∀ {rootVariables currentVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : RewrittenRepresentativeCandidate root)
    {current : SAT.BooleanFormula currentVariables}
    (derivation : Family.RestrictionDerivation root current) →
  Strict.CookSatisfiabilityEquivalent
    (Bridge.indexedToCook current)
    (rewrittenRepresentative
      candidate
      (Generated.generatedSelect
        (Generated.rootState (generatedQuotient candidate))
        (Generated.step (generatedQuotient candidate))
        derivation))
rewrittenRepresentativeEquivalent candidate derivation =
  composeCookEquivalent
    currentToRaw
    rawToTerminal
  where
    generated :
      Generated.TransitionGeneratedRestrictionQuotient root
    generated =
      generatedQuotient candidate

    state :
      Fin (Generated.stateCount generated)
    state =
      Generated.generatedSelect
        (Generated.rootState generated)
        (Generated.step generated)
        derivation

    source :
      NormalizedReachableState generated state
    source =
      normalizedState candidate state

    sameGenerated :
      Generated.generatedSelect
        (Generated.rootState generated)
        (Generated.step generated)
        derivation
      ≡
      Generated.generatedSelect
        (Generated.rootState generated)
        (Generated.step generated)
        (rawDerivation source)
    sameGenerated =
      Agda.Builtin.Equality.sym
        (rawSelectsState source)

    currentToRaw :
      Strict.CookSatisfiabilityEquivalent
        (Bridge.indexedToCook current)
        (Bridge.indexedToCook (rawFormula source))
    currentToRaw =
      indexedEquivalentToCookEquivalent
        (Generated.sameGeneratedStateImpliesSatisfiabilityEquivalent
          generated
          derivation
          (rawDerivation source)
          sameGenerated)

    rawToTerminal :
      Strict.CookSatisfiabilityEquivalent
        (Bridge.indexedToCook (rawFormula source))
        (Cook.constant
          (Rewrite.rewriteProgramTruth
            (normalization source)))
    rawToTerminal =
      rewriteProgramEquivalentToTerminal
        (normalization source)

------------------------------------------------------------------------
-- Constants are strictly below every admitted nontrivial root.
------------------------------------------------------------------------

rewrittenRepresentativeStrict :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : RewrittenRepresentativeCandidate root)
    (state : Fin (Generated.stateCount (generatedQuotient candidate))) →
  Size.formulaNodeCount
    (rewrittenRepresentative candidate state)
  <
  Size.formulaNodeCount
    (Bridge.indexedToCook root)
rewrittenRepresentativeStrict candidate state =
  rootNontrivial candidate

------------------------------------------------------------------------
-- Compile to the existing rewrite-generated closed carrier.
------------------------------------------------------------------------

toRewriteGeneratedClosedRepresentativeQuotient :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  RewrittenRepresentativeCandidate root →
  RewriteGenerated.RewriteGeneratedClosedRepresentativeQuotient root
toRewriteGeneratedClosedRepresentativeQuotient candidate =
  RewriteGenerated.rewrite-generated-closed-representative-quotient
    (generatedQuotient candidate)
    (rewrittenRepresentative candidate)
    (rewrittenRepresentativeEquivalent candidate)
    (rewrittenRepresentativeStrict candidate)
    (λ state →
      Rewrite.halt
        (normalizedTruth candidate state))

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- Raw restriction strictness is gone.
--
-- Remaining constructive obligation per state:
--   actual reachable raw restriction + answer-blind RewriteProgram to a
--   literal constant.
--
-- Strict semantic representative and representative-equivalence are then
-- derived.  This is compatible with the raw-node-count no-go rather than
-- contradicting it.
------------------------------------------------------------------------
