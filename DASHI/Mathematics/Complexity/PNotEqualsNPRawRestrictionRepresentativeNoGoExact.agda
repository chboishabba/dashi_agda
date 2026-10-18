module DASHI.Mathematics.Complexity.PNotEqualsNPRawRestrictionRepresentativeNoGoExact where

------------------------------------------------------------------------
-- RAW SHANNON RESTRICTIONS DO NOT SHRINK FORMULA NODE COUNT
--
-- The current FiniteQ1Candidate asks every state representative to be BOTH
--
--   * an actual reachable raw Shannon restriction of the root; and
--   * strictly smaller than the root by Cook syntax-node count.
--
-- That conjunction is impossible. restrictHead substitutes a variable by a
-- constant and reindexes the other variables, but never removes a syntax node.
-- Therefore every RestrictionDerivation preserves formulaNodeCount exactly.
--
-- This is an architectural no-go in the current Q1 carrier, NOT a P != NP
-- theorem. Strictness must live on the rewritten semantic representative or
-- compiled authority, not on the raw reachable Shannon node.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin)
import Data.Fin.Base as FinBase
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (subst; trans)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as Size
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1FiniteCandidateSemanticAdmissionExact as Candidate
import DASHI.Mathematics.Complexity.PNotEqualsNPArityTrackedTerminalSemanticAdmissionExact as ArityTerminal

restrictHeadPreservesCookNodeCount :
  ∀ {variables : Nat}
    (bit : Bool)
    (formula : SAT.BooleanFormula (suc variables)) →
  Size.formulaNodeCount
      (Bridge.indexedToCook
        (SAT.restrictHead bit formula))
  ≡
  Size.formulaNodeCount
      (Bridge.indexedToCook formula)
restrictHeadPreservesCookNodeCount bit (SAT.variable FinBase.zero) =
  refl
restrictHeadPreservesCookNodeCount bit (SAT.variable (FinBase.suc index)) =
  refl
restrictHeadPreservesCookNodeCount bit (SAT.constant value) =
  refl
restrictHeadPreservesCookNodeCount bit (SAT.negate formula)
    rewrite restrictHeadPreservesCookNodeCount bit formula =
  refl
restrictHeadPreservesCookNodeCount bit (SAT.conjunction left right)
    rewrite restrictHeadPreservesCookNodeCount bit left
          | restrictHeadPreservesCookNodeCount bit right =
  refl
restrictHeadPreservesCookNodeCount bit (SAT.disjunction left right)
    rewrite restrictHeadPreservesCookNodeCount bit left
          | restrictHeadPreservesCookNodeCount bit right =
  refl

restrictionDerivationPreservesCookNodeCount :
  ∀ {rootVariables currentVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {current : SAT.BooleanFormula currentVariables} →
  Family.RestrictionDerivation root current →
  Size.formulaNodeCount
      (Bridge.indexedToCook current)
  ≡
  Size.formulaNodeCount
      (Bridge.indexedToCook root)
restrictionDerivationPreservesCookNodeCount Family.restrictionRoot =
  refl
restrictionDerivationPreservesCookNodeCount
    (Family.restrictionFalse {current = current} derivation) =
  trans
    (restrictHeadPreservesCookNodeCount false current)
    (restrictionDerivationPreservesCookNodeCount derivation)
restrictionDerivationPreservesCookNodeCount
    (Family.restrictionTrue {current = current} derivation) =
  trans
    (restrictHeadPreservesCookNodeCount true current)
    (restrictionDerivationPreservesCookNodeCount derivation)

candidateStateRepresentativeImpossible :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : Candidate.TransitionTableCandidate root)
    (state : Fin (Candidate.stateCount candidate)) →
  Candidate.CandidateStateRepresentative candidate state →
  ⊥
candidateStateRepresentativeImpossible
    {root = root}
    candidate
    state
    representative =
  NatP.<-irrefl
    (Size.formulaNodeCount
      (Bridge.indexedToCook root))
    contradiction
  where
    sameCount :
      Size.formulaNodeCount
          (Bridge.indexedToCook
            (Candidate.formula representative))
      ≡
      Size.formulaNodeCount
          (Bridge.indexedToCook root)
    sameCount =
      restrictionDerivationPreservesCookNodeCount
        (Candidate.derivation representative)

    contradiction :
      Size.formulaNodeCount
          (Bridge.indexedToCook root)
      <
      Size.formulaNodeCount
          (Bridge.indexedToCook root)
    contradiction =
      subst
        (λ count →
          count
          <
          Size.formulaNodeCount
            (Bridge.indexedToCook root))
        sameCount
        (Candidate.strictlySmallerThanRoot representative)

finiteQ1CandidateImpossible :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  Candidate.FiniteQ1Candidate root →
  ⊥
finiteQ1CandidateImpossible candidate =
  candidateStateRepresentativeImpossible
    (Candidate.transitionCandidate candidate)
    (Candidate.rootState
      (Candidate.transitionCandidate candidate))
    (Candidate.stateRepresentative
      candidate
      (Candidate.rootState
        (Candidate.transitionCandidate candidate)))

finiteCandidateConstructionRunImpossible :
  ∀ {state} →
  Candidate.FiniteCandidateConstructionRun state →
  ⊥
finiteCandidateConstructionRunImpossible run =
  finiteQ1CandidateImpossible
    (Candidate.finiteCandidate run)

arityTerminalAdmittedConstructionRunImpossible :
  ∀ {state} →
  ArityTerminal.ArityTerminalAdmittedConstructionRun state →
  ⊥
arityTerminalAdmittedConstructionRunImpossible run =
  finiteCandidateConstructionRunImpossible
    (ArityTerminal.construction run)

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- The residual-width inequalities for successful arity-terminal runs are valid
-- implications but currently have an empty antecedent. Repair the carrier:
--
--   raw restriction      = same-size provenance witness
--   verified rewrite     = strict semantic representative
--   compiled authority   = recursive descent payload.
------------------------------------------------------------------------
