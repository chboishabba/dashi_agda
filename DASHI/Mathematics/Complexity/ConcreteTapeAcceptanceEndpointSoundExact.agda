module DASHI.Mathematics.Complexity.ConcreteTapeAcceptanceEndpointSoundExact where

------------------------------------------------------------------------
-- ACCEPTING ENDPOINT CNF -> AN ACTUAL DECODED ACCEPTING FINAL CELL
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product using (Σ; _,_)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTraceDecodeExact as Trace
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTracePlacementExact as Global
import DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact as Endpoint
import DASHI.Mathematics.Complexity.CNFPlacedConstraintConjunctionExact as Placed
import DASHI.Mathematics.Complexity.CNFVariableRenamingExact as Rename
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

record DecodedAcceptingCell
    {machine : Local.ConcreteTapeMachine}
    {steps cols : Agda.Builtin.Nat.Nat}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (assignment :
      CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps cols)) : Set where
  field
    index : Fin.Fin cols
    witnessTrue :
      CNF.lookupBit assignment (Endpoint.witnessIndex index) ≡ true
    cellBits :
      CNF.Bits (Canonical.CellWidth machine)
    cellBitsExact :
      cellBits ≡ Rename.pullbackBits
        (λ i →
          Endpoint.liftBaseIndex
            (Global.globalRowRename
              (Endpoint.finalRowSlot steps)
              (Global.blockRename (Endpoint.finToSlot index) i)))
        assignment
    decodedSymbol : Local.Symbol machine
    decodedAccepting :
      Canonical.decodeCell stateCoverage symbolCoverage cellBits
      ≡ Local.headed (Local.acceptingState machine) decodedSymbol

open DecodedAcceptingCell public

orPositiveWitness :
  ∀ {global}
    (literalIndex : ∀ {n} → Fin.Fin n → Fin.Fin global)
    {n : Agda.Builtin.Nat.Nat}
    (indices : List (Fin.Fin n))
    (assignment : CNF.Bits global) →
  CNF.evaluateClause
    (Endpoint.allWitnessPositiveLiterals
      (λ i → CNF.positive (literalIndex i))
      indices)
    assignment
  ≡ true →
  Σ (Fin.Fin n) (λ i →
    CNF.lookupBit assignment (literalIndex i) ≡ true)
orPositiveWitness literalIndex [] assignment ()
orPositiveWitness literalIndex (i ∷ rest) assignment accepted
    with CNF.lookupBit assignment (literalIndex i)
... | true =
  i , refl
... | false =
  orPositiveWitness literalIndex rest assignment accepted

acceptancePredicateTrueWithWitness :
  ∀ {machine steps cols}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (assignment :
      CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps cols))
    (i : Fin.Fin cols) →
  CNF.lookupBit assignment (Endpoint.witnessIndex i) ≡ true →
  Placed.predicate
    (Endpoint.acceptancePlacedPredicate
      stateCoverage symbolCoverage (Endpoint.finToSlot i))
    (Rename.pullbackBits
      (Placed.rename
        (Endpoint.acceptancePlacedPredicate
          stateCoverage symbolCoverage (Endpoint.finToSlot i)))
      assignment)
  ≡ true →
  Σ (Local.Symbol machine) (λ symbol →
    Canonical.decodeCell stateCoverage symbolCoverage
      (Canonical.dropBits 1
        (Rename.pullbackBits
          (Placed.rename
            (Endpoint.acceptancePlacedPredicate
              stateCoverage symbolCoverage (Endpoint.finToSlot i)))
          assignment))
    ≡ Local.headed (Local.acceptingState machine) symbol)
acceptancePredicateTrueWithWitness
    {machine} stateCoverage symbolCoverage assignment i
    witnessTrue accepted
    with Rename.pullbackBits
      (Placed.rename
        (Endpoint.acceptancePlacedPredicate
          stateCoverage symbolCoverage (Endpoint.finToSlot i)))
      assignment
... | false CNF.∷ᵇ cellBits
    with Rename.pullbackLookup
      (Placed.rename
        (Endpoint.acceptancePlacedPredicate
          stateCoverage symbolCoverage (Endpoint.finToSlot i)))
      assignment Fin.zero
... | lookupEq =
  absurd witnessTrue lookupEq
  where
    absurd : false ≡ true → false ≡ false → _
    absurd () _
... | true CNF.∷ᵇ cellBits
    with Canonical.decodeCell stateCoverage symbolCoverage cellBits
... | Local.plain symbol
    with accepted
... | ()
... | Local.headed state symbol
    with Local.decideEqual (Local.finiteState machine)
      state (Local.acceptingState machine)
      | accepted
... | false | ()
... | true | refl =
  symbol ,
  cong (λ q → Local.headed q symbol)
    (Local.decideEqualSound
      (Local.finiteState machine) refl)

data AllAcceptancePredicatesSatisfied
    {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    {steps cols}
    (assignment :
      CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps cols)) :
    List (Fin.Fin cols) → Set where
  acceptDone :
    AllAcceptancePredicatesSatisfied
      stateCoverage symbolCoverage assignment []
  acceptStep :
    ∀ {i rest} →
    Placed.predicate
      (Endpoint.acceptancePlacedPredicate
        stateCoverage symbolCoverage (Endpoint.finToSlot i))
      (Rename.pullbackBits
        (Placed.rename
          (Endpoint.acceptancePlacedPredicate
            stateCoverage symbolCoverage (Endpoint.finToSlot i)))
        assignment)
    ≡ true →
    AllAcceptancePredicatesSatisfied
      stateCoverage symbolCoverage assignment rest →
    AllAcceptancePredicatesSatisfied
      stateCoverage symbolCoverage assignment (i ∷ rest)

allPlacedToAcceptanceSatisfied :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    {steps cols}
    (assignment :
      CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps cols))
    (indices : List (Fin.Fin cols)) →
  Placed.AllPlacedSatisfied assignment
    (Endpoint.acceptanceImplicationPredicatesFin
      stateCoverage symbolCoverage indices) →
  AllAcceptancePredicatesSatisfied
    stateCoverage symbolCoverage assignment indices
allPlacedToAcceptanceSatisfied
    stateCoverage symbolCoverage assignment
    [] Placed.allPlacedDone =
  acceptDone
allPlacedToAcceptanceSatisfied
    stateCoverage symbolCoverage assignment
    (i ∷ rest)
    (Placed.allPlacedStep current remainder) =
  acceptStep current
    (allPlacedToAcceptanceSatisfied
      stateCoverage symbolCoverage assignment rest remainder)

findAcceptingFromWitness :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    {steps cols}
    (assignment :
      CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps cols))
    (indices : List (Fin.Fin cols)) →
  (Σ (Fin.Fin cols) (λ i →
    CNF.lookupBit assignment (Endpoint.witnessIndex i) ≡ true)) →
  AllAcceptancePredicatesSatisfied
    stateCoverage symbolCoverage assignment indices →
  DecodedAcceptingCell
    stateCoverage symbolCoverage assignment
findAcceptingFromWitness
    stateCoverage symbolCoverage assignment
    [] (i , witness) acceptDone =
  impossible i
  where
    impossible : Fin.Fin 0 → _
    impossible ()
findAcceptingFromWitness
    stateCoverage symbolCoverage assignment
    (i ∷ rest) (chosen , witness)
    (acceptStep current remainder)
    with Fin.decEq chosen i
... | true
    with Fin.eq_of_val_eq (Fin.decEq_eq_true_iff.mp refl)
... | refl
    with acceptancePredicateTrueWithWitness
      stateCoverage symbolCoverage assignment i witness current
... | symbol , decoded =
  record
    { index = i
    ; witnessTrue = witness
    ; cellBits =
        Canonical.dropBits 1
          (Rename.pullbackBits
            (Placed.rename
              (Endpoint.acceptancePlacedPredicate
                stateCoverage symbolCoverage
                (Endpoint.finToSlot i)))
            assignment)
    ; cellBitsExact = refl
    ; decodedSymbol = symbol
    ; decodedAccepting = decoded
    }
... | false =
  findAcceptingFromWitness
    stateCoverage symbolCoverage assignment
    rest (chosen , witness) remainder

acceptingEndpointCNF_sound :
  ∀ {machine steps cols}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (assignment :
      CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps cols)) →
  CNF.evaluateCNF
    (Endpoint.acceptingEndpointCNF
      stateCoverage symbolCoverage)
    assignment
  ≡ true →
  DecodedAcceptingCell
    stateCoverage symbolCoverage assignment
acceptingEndpointCNF_sound
    stateCoverage symbolCoverage assignment accepted =
  findAcceptingFromWitness
    stateCoverage symbolCoverage assignment
    (Endpoint.finList _)
    witness
    allSatisfied
  where
    witnessClauseValue =
      CNF.evaluateClause
        Endpoint.someAcceptanceWitnessClause assignment

    implicationCNF =
      Placed.compilePlacedAll
        (Endpoint.acceptanceImplicationPredicatesFin
          stateCoverage symbolCoverage (Endpoint.finList _))

    implicationValue =
      CNF.evaluateCNF implicationCNF assignment

    witnessClauseTrue : witnessClauseValue ≡ true
    witnessClauseTrue =
      Endpoint.andTrueLeft witnessClauseValue implicationValue accepted

    implicationTrue : implicationValue ≡ true
    implicationTrue =
      Endpoint.andTrueRight witnessClauseValue implicationValue accepted

    witness :
      Σ (Fin.Fin _) (λ i →
        CNF.lookupBit assignment (Endpoint.witnessIndex i) ≡ true)
    witness =
      orPositiveWitness Endpoint.witnessIndex
        (Endpoint.finList _) assignment witnessClauseTrue

    allSatisfied =
      allPlacedToAcceptanceSatisfied
        stateCoverage symbolCoverage assignment
        (Endpoint.finList _)
        (Placed.compilePlacedAllSound
          (Endpoint.acceptanceImplicationPredicatesFin
            stateCoverage symbolCoverage (Endpoint.finList _))
          assignment implicationTrue)
