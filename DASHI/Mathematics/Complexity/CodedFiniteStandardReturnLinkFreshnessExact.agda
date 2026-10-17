module DASHI.Mathematics.Complexity.CodedFiniteStandardReturnLinkFreshnessExact where

------------------------------------------------------------------------
-- SAFE-LINK NECESSITY AT THE CANDIDATE RETURN BOUNDARY
--
-- A SafeLinkExtension is deterministic because every appended link dispatch key
-- is disjoint from every resident rule key.  Therefore an embedded candidate
-- configuration that still has a resident transition on its current
-- (state,scanned-symbol) key cannot also carry a direct cross-mode return rule.
--
-- This is the exact obstruction hidden by the phrase "return after T steps":
-- StandardFiniteCandidateCode fixes the T-step endpoint, but does not assert
-- that this endpoint is quiescent/halting.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; trans)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeRuleTableInterpreterExact as Interpreter
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.CodedFiniteStandardModeSumExact as Mode
import DASHI.Mathematics.Complexity.CodedFiniteStandardLinkExtensionExact as Link
import DASHI.Mathematics.Complexity.CodedFiniteStandardLinkedStructuralSimulationExact as Linked
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented

residentCandidateRuleBlocksReturnLink :
  ∀ {source : Coded.CodedFiniteStandardTM}
    {right : Mode.CodedModeFragment (Coded.symbolCount source)}
    (extension : Link.SafeLinkExtension (Linked.baseCombined source right))
    {q : Fin.Fin (Coded.stateCount source)}
    {a : Fin.Fin (Coded.symbolCount source)}
    (matched : Interpreter.MatchedRule
      (Presented.finitePresentedStandardToConcrete
        (Coded.decodeCodedStandardTM source))
      q a
      (Coded.rules source))
    {returnRule : Local.TapeRule
      (Fin.Fin (Mode.stateCount (Linked.baseCombined source right)))
      (Fin.Fin (Coded.symbolCount source))} →
  Local.RuleOccurs returnRule (Link.links extension) →
  Linked.sourceStateMap source right q
    ≡ Local.sourceState returnRule →
  a ≡ Local.readSymbol returnRule →
  ⊥
residentCandidateRuleBlocksReturnLink
    {source} {right} extension matched returnOccurs sourceKey readKey =
  Link.residentLinkKeyDisjoint extension
    (Linked.mappedFetchedRuleResidentOccurs matched)
    returnOccurs
    mappedSourceKey
    mappedReadKey
  where
    mappedSourceKey :
      Local.sourceState
        (Mode.mapStateRule
          (Linked.sourceStateMap source right)
          (Interpreter.rule matched))
      ≡ Local.sourceState returnRule
    mappedSourceKey =
      trans
        (cong
          (Linked.sourceStateMap source right)
          (Interpreter.sourceExact matched))
        sourceKey

    mappedReadKey :
      Local.readSymbol
        (Mode.mapStateRule
          (Linked.sourceStateMap source right)
          (Interpreter.rule matched))
      ≡ Local.readSymbol returnRule
    mappedReadKey =
      trans
        (Interpreter.readExact matched)
        readKey

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- Direct return from the embedded candidate mode is valid only on a fresh
-- dispatch key.  In particular, the existence of an exact T-step endpoint does
-- not imply that a SafeLinkExtension may leave that endpoint immediately.  A
-- compiler must additionally provide one of:
--
--   * a proof that the endpoint key has no resident rule;
--   * a halting/quiescent normal form for polynomial candidates; or
--   * a genuine clock/phase wrapper whose return state is outside the resident
--     candidate dispatch region.
--
-- This theorem does not choose among those constructions; it prevents a direct
-- return link from silently overriding the candidate's actual transition table.
------------------------------------------------------------------------
