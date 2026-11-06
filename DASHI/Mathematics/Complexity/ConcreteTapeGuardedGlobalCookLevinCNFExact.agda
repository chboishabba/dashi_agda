module DASHI.Mathematics.Complexity.ConcreteTapeGuardedGlobalCookLevinCNFExact where

------------------------------------------------------------------------
-- SAME-OBJECT GUARDED COOK--LEVIN CNF:
--
-- original GlobalCNF.globalCookLevinCNF (unchanged)
--     AND CanonicalEndcap.globalAllRowsEndcapsCNF.
--
-- The latter uses the ORIGINAL extended bits, row slots, column slots,
-- and cell decoder. This owner proves both directions of SAT formula
-- decomposition and produces a per-row endcap evaluation certificate.
-- It does not silently assert an unchanged SAT language: a bounded,
-- padded accepting-run completeness proof must still demonstrate that
-- its actual encoded run satisfies the added endcap clauses.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)
open import Agda.Builtin.Nat using (Nat; suc)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact as Endpoint
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinCNFExact as GlobalCNF
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalEndcapCNFExact as Endcap
import DASHI.Mathematics.Complexity.CNFPlacedConstraintConjunctionExact as Placed
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

guardedGlobalCookLevinCNF :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps colsMinusOne : Nat) →
  CNF.Bits (Decode.RowBitsWidth machine (suc colsMinusOne)) →
  CNF.CNF (Endpoint.ExtendedGlobalWidth machine steps (suc colsMinusOne))
guardedGlobalCookLevinCNF
    stateCoverage symbolCoverage nonempty steps colsMinusOne initialTarget =
  Placed.append
    (GlobalCNF.globalCookLevinCNF
      stateCoverage symbolCoverage nonempty steps
      (suc colsMinusOne) initialTarget)
    (Endcap.globalAllRowsEndcapsCNF colsMinusOne)

record GuardedGlobalFormulaPartsTrue
    {machine : Local.ConcreteTapeMachine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps colsMinusOne : Nat)
    (initialTarget :
      CNF.Bits (Decode.RowBitsWidth machine (suc colsMinusOne)))
    (assignment :
      CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps (suc colsMinusOne))) :
    Set where
  field
    originalFormulaTrue :
      CNF.evaluateCNF
        (GlobalCNF.globalCookLevinCNF
          stateCoverage symbolCoverage nonempty steps
          (suc colsMinusOne) initialTarget)
        assignment ≡ true

    globalEndcapCNFTrue :
      CNF.evaluateCNF
        (Endcap.globalAllRowsEndcapsCNF colsMinusOne)
        assignment ≡ true

open GuardedGlobalFormulaPartsTrue public

guardedGlobalCookLevinCNFSound :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps colsMinusOne : Nat)
    (initialTarget :
      CNF.Bits (Decode.RowBitsWidth machine (suc colsMinusOne)))
    (assignment :
      CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps (suc colsMinusOne))) →
  CNF.evaluateCNF
    (guardedGlobalCookLevinCNF
      stateCoverage symbolCoverage nonempty
      steps colsMinusOne initialTarget) assignment ≡ true →
  GuardedGlobalFormulaPartsTrue
    stateCoverage symbolCoverage nonempty
    steps colsMinusOne initialTarget assignment
guardedGlobalCookLevinCNFSound
    stateCoverage symbolCoverage nonempty steps colsMinusOne
    initialTarget assignment accepted =
  record
    { originalFormulaTrue =
        GlobalCNF.andTrueLeft left right split
    ; globalEndcapCNFTrue =
        GlobalCNF.andTrueRight left right split
    }
  where
    original = GlobalCNF.globalCookLevinCNF
      stateCoverage symbolCoverage nonempty steps
      (suc colsMinusOne) initialTarget

    endcaps = Endcap.globalAllRowsEndcapsCNF colsMinusOne

    left = CNF.evaluateCNF original assignment
    right = CNF.evaluateCNF endcaps assignment

    split : CNF.andBool left right ≡ true
    split with Placed.evaluateCNFAppend original endcaps assignment
    ... | refl = accepted

guardedGlobalCookLevinCNFComplete :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps colsMinusOne : Nat)
    (initialTarget :
      CNF.Bits (Decode.RowBitsWidth machine (suc colsMinusOne)))
    (assignment :
      CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps (suc colsMinusOne))) →
  GuardedGlobalFormulaPartsTrue
    stateCoverage symbolCoverage nonempty
    steps colsMinusOne initialTarget assignment →
  CNF.evaluateCNF
    (guardedGlobalCookLevinCNF
      stateCoverage symbolCoverage nonempty
      steps colsMinusOne initialTarget) assignment ≡ true
guardedGlobalCookLevinCNFComplete
    stateCoverage symbolCoverage nonempty steps colsMinusOne
    initialTarget assignment parts
  with Placed.evaluateCNFAppend
    (GlobalCNF.globalCookLevinCNF
      stateCoverage symbolCoverage nonempty steps
      (suc colsMinusOne) initialTarget)
    (Endcap.globalAllRowsEndcapsCNF colsMinusOne)
    assignment
... | equality =
  trans equality
    (cong₂ CNF.andBool
      (originalFormulaTrue parts)
      (globalEndcapCNFTrue parts))

record GuardedGlobalSATConsequences
    {machine : Local.ConcreteTapeMachine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps colsMinusOne : Nat)
    (initialTarget :
      CNF.Bits (Decode.RowBitsWidth machine (suc colsMinusOne)))
    (assignment :
      CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps (suc colsMinusOne))) :
    Set where
  field
    originalParts :
      GlobalCNF.GlobalFormulaPartsTrue
        stateCoverage symbolCoverage nonempty steps
        (suc colsMinusOne) initialTarget assignment

    allRowEndcaps :
      Endcap.AllPhysicalRowEndcapsTrue colsMinusOne assignment
        (Endcap.allPhysicalRows (suc steps))

open GuardedGlobalSATConsequences public

guardedGlobalCNFToOriginalAndAllEndcaps :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps colsMinusOne : Nat)
    (initialTarget :
      CNF.Bits (Decode.RowBitsWidth machine (suc colsMinusOne)))
    (assignment :
      CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps (suc colsMinusOne))) →
  CNF.evaluateCNF
    (guardedGlobalCookLevinCNF
      stateCoverage symbolCoverage nonempty
      steps colsMinusOne initialTarget) assignment ≡ true →
  GuardedGlobalSATConsequences
    stateCoverage symbolCoverage nonempty
    steps colsMinusOne initialTarget assignment
guardedGlobalCNFToOriginalAndAllEndcaps
    stateCoverage symbolCoverage nonempty steps colsMinusOne
    initialTarget assignment accepted = record
  { originalParts =
      GlobalCNF.globalCookLevinCNFSoundParts
        stateCoverage symbolCoverage nonempty
        steps (suc colsMinusOne) initialTarget
        assignment (originalFormulaTrue parts)
  ; allRowEndcaps =
      Endcap.globalAllRowsEndcapsSound
        colsMinusOne assignment (globalEndcapCNFTrue parts)
  }
  where
    parts = guardedGlobalCookLevinCNFSound
      stateCoverage symbolCoverage nonempty
      steps colsMinusOne initialTarget assignment accepted
