module DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinStreamingClauseExact where

------------------------------------------------------------------------
-- STREAM ONE ACTUAL GLOBAL COOK--LEVIN CLAUSE BY INDEX
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (sym; trans)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTransitionConjunctionExact as Transition
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinCNFExact as Global
import DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact as Endpoint
import DASHI.Mathematics.Complexity.CNFVariableRenamingExact as Rename
import DASHI.Mathematics.Complexity.CNFPlacedConstraintConjunctionExact as Placed
import DASHI.Mathematics.Complexity.CNFStreamingSeekExact as Seek
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

------------------------------------------------------------------------
-- Transition section: direct placed-predicate seek, then one-clause lift.
------------------------------------------------------------------------

transitionClauseSeek :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols index : Nat) →
  Seek.SeekResult (CNF.Clause (Endpoint.ExtendedGlobalWidth machine steps cols))
transitionClauseSeek stateCoverage symbolCoverage nonempty steps cols index =
  Seek.mapSeek
    (Rename.renameClause Endpoint.liftBaseIndex)
    (Seek.seekPlacedAll
      (Transition.allGlobalTransitionPredicates
        stateCoverage symbolCoverage nonempty steps cols)
      index)

transitionClauseSeekExact :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols index : Nat) →
  transitionClauseSeek
      stateCoverage symbolCoverage nonempty steps cols index
  ≡
  Seek.seekList index
    (Global.liftTransitionCNF
      stateCoverage symbolCoverage nonempty steps cols)
transitionClauseSeekExact
    stateCoverage symbolCoverage nonempty steps cols index =
  trans
    (congMap
      (Seek.seekPlacedAllExact
        (Transition.allGlobalTransitionPredicates
          stateCoverage symbolCoverage nonempty steps cols)
        index))
    (Seek.seekRenameCNFExact
      Endpoint.liftBaseIndex
      (Transition.globalTransitionCNF
        stateCoverage symbolCoverage nonempty steps cols)
      index)
  where
    congMap :
      ∀ {A : Set}
        {left right : Seek.SeekResult A} →
      left ≡ right →
      Seek.mapSeek
        (Rename.renameClause Endpoint.liftBaseIndex)
        left
      ≡
      Seek.mapSeek
        (Rename.renameClause Endpoint.liftBaseIndex)
        right
    congMap refl = refl

------------------------------------------------------------------------
-- Initial section: direct unit-clause seek over the target Bits vector.
------------------------------------------------------------------------

seekInitialUnits :
  ∀ {local global : Nat} →
  (Fin.Fin local → Fin.Fin global) →
  CNF.Bits local →
  Nat →
  Seek.SeekResult (CNF.Clause global)
seekInitialUnits rename CNF.[]ᵇ index = Seek.exhausted index
seekInitialUnits rename (bit CNF.∷ᵇ bits) zero =
  Seek.found (Endpoint.unitClauseForBit (rename Fin.zero) bit)
seekInitialUnits rename (bit CNF.∷ᵇ bits) (suc index) =
  seekInitialUnits
    (λ i → rename (Fin.suc i))
    bits
    index

seekInitialUnitsExact :
  ∀ {local global : Nat}
    (rename : Fin.Fin local → Fin.Fin global)
    (bits : CNF.Bits local)
    (index : Nat) →
  seekInitialUnits rename bits index
  ≡ Seek.seekList index (Endpoint.unitClausesForTarget rename bits)
seekInitialUnitsExact rename CNF.[]ᵇ index = refl
seekInitialUnitsExact rename (bit CNF.∷ᵇ bits) zero = refl
seekInitialUnitsExact rename (bit CNF.∷ᵇ bits) (suc index) =
  seekInitialUnitsExact (λ i → rename (Fin.suc i)) bits index

initialClauseSeek :
  ∀ {machine : Local.ConcreteTapeMachine} {steps cols : Nat} →
  CNF.Bits (Decode.RowBitsWidth machine cols) →
  Nat →
  Seek.SeekResult (CNF.Clause (Endpoint.ExtendedGlobalWidth machine steps cols))
initialClauseSeek target =
  seekInitialUnits Endpoint.initialRowExtendedRename target

initialClauseSeekExact :
  ∀ {machine : Local.ConcreteTapeMachine} {steps cols : Nat}
    (target : CNF.Bits (Decode.RowBitsWidth machine cols))
    (index : Nat) →
  initialClauseSeek {steps = steps} target index
  ≡ Seek.seekList index (Endpoint.initialEndpointCNF target)
initialClauseSeekExact target index =
  seekInitialUnitsExact Endpoint.initialRowExtendedRename target index

------------------------------------------------------------------------
-- Accepting section: head witness clause, then streamed placed implications.
------------------------------------------------------------------------

acceptingClauseSeek :
  ∀ {machine : Local.ConcreteTapeMachine} {steps cols : Nat}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  Nat →
  Seek.SeekResult (CNF.Clause (Endpoint.ExtendedGlobalWidth machine steps cols))
acceptingClauseSeek stateCoverage symbolCoverage zero =
  Seek.found Endpoint.someAcceptanceWitnessClause
acceptingClauseSeek {cols = cols}
    stateCoverage symbolCoverage (suc index) =
  Seek.seekPlacedAll
    (Endpoint.acceptanceImplicationPredicatesFin
      stateCoverage symbolCoverage (Endpoint.finList cols))
    index

acceptingClauseSeekExact :
  ∀ {machine : Local.ConcreteTapeMachine} {steps cols : Nat}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (index : Nat) →
  acceptingClauseSeek {steps = steps} {cols = cols}
      stateCoverage symbolCoverage index
  ≡
  Seek.seekList index
    (Endpoint.acceptingEndpointCNF
      stateCoverage symbolCoverage)
acceptingClauseSeekExact stateCoverage symbolCoverage zero = refl
acceptingClauseSeekExact {cols = cols}
    stateCoverage symbolCoverage (suc index) =
  Seek.seekPlacedAllExact
    (Endpoint.acceptanceImplicationPredicatesFin
      stateCoverage symbolCoverage (Endpoint.finList cols))
    index

------------------------------------------------------------------------
-- Compose residual indices across transition -> initial -> accepting.
------------------------------------------------------------------------

continueInitialAccepting :
  ∀ {machine : Local.ConcreteTapeMachine} {steps cols : Nat}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols)) →
  Seek.SeekResult (CNF.Clause (Endpoint.ExtendedGlobalWidth machine steps cols)) →
  Seek.SeekResult (CNF.Clause (Endpoint.ExtendedGlobalWidth machine steps cols))
continueInitialAccepting stateCoverage symbolCoverage initialTarget
    (Seek.found clause) = Seek.found clause
continueInitialAccepting stateCoverage symbolCoverage initialTarget
    (Seek.exhausted index)
    with initialClauseSeek initialTarget index
... | Seek.found clause = Seek.found clause
... | Seek.exhausted remaining =
  acceptingClauseSeek stateCoverage symbolCoverage remaining

globalClauseSeek :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols)) →
  Nat →
  Seek.SeekResult (CNF.Clause (Endpoint.ExtendedGlobalWidth machine steps cols))
globalClauseSeek
    stateCoverage symbolCoverage nonempty steps cols initialTarget index =
  continueInitialAccepting
    stateCoverage symbolCoverage initialTarget
    (transitionClauseSeek
      stateCoverage symbolCoverage nonempty steps cols index)

------------------------------------------------------------------------
-- Extensional global equality.
------------------------------------------------------------------------

continueInitialAcceptingExact :
  ∀ {machine : Local.ConcreteTapeMachine} {steps cols : Nat}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols))
    (transitionResult : Seek.SeekResult
      (CNF.Clause (Endpoint.ExtendedGlobalWidth machine steps cols))) →
  continueInitialAccepting
      stateCoverage symbolCoverage initialTarget transitionResult
  ≡
  Seek.continueSeek transitionResult
    (Placed.append
      (Endpoint.initialEndpointCNF initialTarget)
      (Endpoint.acceptingEndpointCNF stateCoverage symbolCoverage))
continueInitialAcceptingExact
    stateCoverage symbolCoverage initialTarget (Seek.found clause) = refl
continueInitialAcceptingExact
    stateCoverage symbolCoverage initialTarget (Seek.exhausted index)
    with initialClauseSeek initialTarget index
       | initialClauseSeekExact initialTarget index
... | Seek.found clause | refl = refl
... | Seek.exhausted remaining | initialExact
    with acceptingClauseSeek stateCoverage symbolCoverage remaining
       | acceptingClauseSeekExact stateCoverage symbolCoverage remaining
... | result | acceptingExact
    with Seek.seekAppendExact
      (Endpoint.initialEndpointCNF initialTarget)
      (Endpoint.acceptingEndpointCNF stateCoverage symbolCoverage)
      index
... | appendExact
    rewrite initialExact | acceptingExact | appendExact = refl

globalClauseSeekExact :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols))
    (index : Nat) →
  globalClauseSeek
      stateCoverage symbolCoverage nonempty steps cols initialTarget index
  ≡
  Seek.seekList index
    (Global.globalCookLevinCNF
      stateCoverage symbolCoverage nonempty steps cols initialTarget)
globalClauseSeekExact
    stateCoverage symbolCoverage nonempty steps cols initialTarget index
    rewrite transitionClauseSeekExact
      stateCoverage symbolCoverage nonempty steps cols index =
  trans
    (continueInitialAcceptingExact
      stateCoverage symbolCoverage initialTarget
      (Seek.seekList index
        (Global.liftTransitionCNF
          stateCoverage symbolCoverage nonempty steps cols)))
    (Seek.seekAppendExact
      (Global.liftTransitionCNF
        stateCoverage symbolCoverage nonempty steps cols)
      (Placed.append
        (Endpoint.initialEndpointCNF initialTarget)
        (Endpoint.acceptingEndpointCNF stateCoverage symbolCoverage))
      index)

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- Clause-level random access for the ACTUAL global Cook--Levin CNF is now an
-- executable streaming function whose correctness is against the existing
-- literal constructor.  It never needs a precomputed section length and never
-- constructs the tableau-wide transition CNF.
------------------------------------------------------------------------
