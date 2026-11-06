module DASHI.Mathematics.Complexity.ConcreteTapeAcceptanceEndpointSoundExact where

------------------------------------------------------------------------
-- ACCEPTING ENDPOINT CNF -> AN ACTUAL DECODED ACCEPTING FINAL CELL
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product using (Σ; _,_)
import Data.Fin.Base as Fin
open import Relation.Binary.PropositionalEquality using (cong; sym; trans; subst)

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
    {steps cols : Nat}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (assignment :
      CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps cols)) : Set where
  field
    index : Fin.Fin cols
    witnessTrue :
      CNF.lookupBit assignment (Endpoint.witnessIndex {machine} {steps} {cols} index) ≡ true
    cellBits :
      CNF.Bits (Canonical.CellWidth machine)
    cellBitsExact :
      cellBits ≡ Rename.pullbackBits
        (λ i →
          Endpoint.liftBaseIndex {machine} {steps} {cols}
            (Global.globalRowRename {machine} {steps} {cols}
              (Endpoint.finalRowSlot steps)
              (Global.blockRename (Endpoint.finToSlot index) i)))
        assignment
    decodedSymbol : Local.Symbol machine
    decodedAccepting :
      Canonical.decodeCell {machine} stateCoverage symbolCoverage cellBits
      ≡ Local.headed (Local.acceptingState machine) decodedSymbol

open DecodedAcceptingCell public

data Member {A : Set} (x : A) : List A → Set where
  here : ∀ {xs} → Member x (x ∷ xs)
  there : ∀ {y xs} → Member x xs → Member x (y ∷ xs)

record TrueWitnessIn
    {global n : Nat}
    (literalIndex : Fin.Fin n → Fin.Fin global)
    (indices : List (Fin.Fin n))
    (assignment : CNF.Bits global) : Set where
  field
    index : Fin.Fin n
    member : Member index indices
    witnessTrue :
      CNF.lookupBit assignment (literalIndex index) ≡ true

open TrueWitnessIn public

orPositiveWitness :
  ∀ {global n}
    (literalIndex : Fin.Fin n → Fin.Fin global)
    (indices : List (Fin.Fin n))
    (assignment : CNF.Bits global) →
  CNF.evaluateClause
    (Endpoint.allWitnessPositiveLiterals
      (λ i → CNF.positive (literalIndex i))
      indices)
    assignment
  ≡ true →
  TrueWitnessIn literalIndex indices assignment
orPositiveWitness literalIndex [] assignment ()
orPositiveWitness literalIndex (i ∷ rest) assignment accepted
    with CNF.lookupBit assignment (literalIndex i) in bitEq
... | true =
  record { index = i ; member = here ; witnessTrue = bitEq }
... | false =
  let tail =
        orPositiveWitness literalIndex rest assignment accepted
  in record
      { index = index tail
      ; member = there (member tail)
      ; witnessTrue = witnessTrue tail
      }


acceptancePredicateTrueWithWitness :
  ∀ {machine steps cols}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (assignment :
      CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps cols))
    (i : Fin.Fin cols) →
  CNF.lookupBit assignment (Endpoint.witnessIndex {machine} {steps} {cols} i) ≡ true →
  Placed.predicate
    (Endpoint.acceptancePlacedPredicate {machine} {steps} {cols}
      stateCoverage symbolCoverage (Endpoint.finToSlot i))
    (Rename.pullbackBits
      (Placed.rename
        (Endpoint.acceptancePlacedPredicate {machine} {steps} {cols}
          stateCoverage symbolCoverage (Endpoint.finToSlot i)))
      assignment)
  ≡ true →
  Σ (Local.Symbol machine) (λ symbol →
    Canonical.decodeCell stateCoverage symbolCoverage
      (Canonical.dropBits 1
        (Rename.pullbackBits
          (Placed.rename
            (Endpoint.acceptancePlacedPredicate {machine} {steps} {cols}
              stateCoverage symbolCoverage (Endpoint.finToSlot i)))
          assignment))
    ≡ Local.headed (Local.acceptingState machine) symbol)
acceptancePredicateTrueWithWitness
    {machine} {steps} {cols} stateCoverage symbolCoverage assignment i
    witnessTrue accepted
    with Rename.pullbackBits
      (Placed.rename
        (Endpoint.acceptancePlacedPredicate {machine} {steps} {cols}
          stateCoverage symbolCoverage (Endpoint.finToSlot i)))
      assignment in bitsEq | accepted
... | false CNF.∷ᵇ cellBits | _ =
  absurd
    (trans
      (trans
        (trans
          (sym (cong (λ b → CNF.lookupBit b Fin.zero) bitsEq))
          (Rename.pullbackLookup
            (Placed.rename
              (Endpoint.acceptancePlacedPredicate {machine} {steps} {cols}
                stateCoverage symbolCoverage (Endpoint.finToSlot i)))
            assignment Fin.zero))
        (cong (CNF.lookupBit assignment)
          (Endpoint.acceptanceLocalRename_zero_eq_witnessIndex {machine} {steps} {cols} i)))
      witnessTrue)
  where
    absurd : false ≡ true → _
    absurd ()
... | true CNF.∷ᵇ cellBits | accepted'
    with Canonical.decodeCell {machine} stateCoverage symbolCoverage cellBits in cellEq
      | accepted'
... | Local.plain symbol | ()
... | Local.headed state symbol | stateEq =
  symbol ,
  trans
    (cong (λ b → Canonical.decodeCell {machine} stateCoverage symbolCoverage (Canonical.dropBits 1 b)) bitsEq)
    (trans
      cellEq
      (cong (λ q → Local.headed q symbol)
        (Local.decideEqualSound
          (Local.finiteState machine) stateEq)))

data AllAcceptancePredicatesSatisfied
    {machine : Local.ConcreteTapeMachine}
    {steps cols : Nat}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (assignment :
      CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps cols)) :
    List (Fin.Fin cols) → Set where
  acceptDone :
    AllAcceptancePredicatesSatisfied {machine} {steps} {cols}
      stateCoverage symbolCoverage assignment []
  acceptStep :
    ∀ {i rest} →
    Placed.predicate
      (Endpoint.acceptancePlacedPredicate {machine} {steps} {cols}
        stateCoverage symbolCoverage (Endpoint.finToSlot i))
      (Rename.pullbackBits
        (Placed.rename
          (Endpoint.acceptancePlacedPredicate {machine} {steps} {cols}
            stateCoverage symbolCoverage (Endpoint.finToSlot i)))
        assignment)
    ≡ true →
    AllAcceptancePredicatesSatisfied {machine} {steps} {cols}
      stateCoverage symbolCoverage assignment rest →
    AllAcceptancePredicatesSatisfied {machine} {steps} {cols}
      stateCoverage symbolCoverage assignment (i ∷ rest)

allPlacedToAcceptanceSatisfied :
  ∀ {machine steps cols}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (assignment :
      CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps cols))
    (indices : List (Fin.Fin cols)) →
  Placed.AllPlacedSatisfied assignment
    (Endpoint.acceptanceImplicationPredicatesFin {machine} {steps} {cols}
      stateCoverage symbolCoverage indices) →
  AllAcceptancePredicatesSatisfied {machine} {steps} {cols}
    stateCoverage symbolCoverage assignment indices
allPlacedToAcceptanceSatisfied
    stateCoverage symbolCoverage assignment
    [] Placed.allPlacedDone =
  acceptDone
allPlacedToAcceptanceSatisfied {machine} {steps} {cols}
    stateCoverage symbolCoverage assignment
    (i ∷ rest)
    (Placed.allPlacedStep current remainder) =
  acceptStep current
    (allPlacedToAcceptanceSatisfied {machine} {steps} {cols}
      stateCoverage symbolCoverage assignment rest remainder)

findAcceptingFromWitness :
  ∀ {machine steps cols}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (assignment :
      CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps cols))
    (indices : List (Fin.Fin cols))
    (witness :
      TrueWitnessIn (Endpoint.witnessIndex {machine} {steps} {cols}) indices assignment) →
  AllAcceptancePredicatesSatisfied {machine} {steps} {cols}
    stateCoverage symbolCoverage assignment indices →
  DecodedAcceptingCell {machine} {steps} {cols}
    stateCoverage symbolCoverage assignment
findAcceptingFromWitness {machine} {steps} {cols}
    stateCoverage symbolCoverage assignment
    [] (record { member = () }) acceptDone
findAcceptingFromWitness {machine} {steps} {cols}
    stateCoverage symbolCoverage assignment
    (i ∷ rest)
    (record { index = .i ; member = here ; witnessTrue = wTrue })
    (acceptStep current remainder)
    with acceptancePredicateTrueWithWitness {machine} {steps} {cols}
      stateCoverage symbolCoverage assignment i
      wTrue current
... | symbol , decoded =
  record
    { index = i
    ; witnessTrue = wTrue
    ; cellBits =
        Canonical.dropBits 1 {Canonical.CellWidth machine}
          (Rename.pullbackBits
            (Placed.rename
              (Endpoint.acceptancePlacedPredicate {machine} {steps} {cols}
                stateCoverage symbolCoverage
                (Endpoint.finToSlot i)))
            assignment)
    ; cellBitsExact = refl
    ; decodedSymbol = symbol
    ; decodedAccepting = decoded
    }
findAcceptingFromWitness {machine} {steps} {cols}
    stateCoverage symbolCoverage assignment
    (i ∷ rest)
    (record { index = wIndex ; member = there m ; witnessTrue = wTrue })
    (acceptStep current remainder) =
  findAcceptingFromWitness {machine} {steps} {cols}
    stateCoverage symbolCoverage assignment
    rest
    (record
      { index = wIndex
      ; member = m
      ; witnessTrue = wTrue
      })
    remainder

acceptingEndpointCNF_sound :
  ∀ {machine steps cols}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (assignment :
      CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps cols)) →
  CNF.evaluateCNF
    (Endpoint.acceptingEndpointCNF {machine} {steps} {cols}
      stateCoverage symbolCoverage)
    assignment
  ≡ true →
  DecodedAcceptingCell {machine} {steps} {cols}
    stateCoverage symbolCoverage assignment
acceptingEndpointCNF_sound {machine} {steps} {cols}
    stateCoverage symbolCoverage assignment accepted =
  findAcceptingFromWitness {machine} {steps} {cols}
    stateCoverage symbolCoverage assignment
    (Endpoint.finList cols)
    witness
    allSatisfied
  where
    witnessClauseValue =
      CNF.evaluateClause
        (Endpoint.someAcceptanceWitnessClause {machine} {steps} {cols}) assignment

    implicationCNF =
      Placed.compilePlacedAll
        (Endpoint.acceptanceImplicationPredicatesFin {machine} {steps} {cols}
          stateCoverage symbolCoverage (Endpoint.finList cols))

    implicationValue =
      CNF.evaluateCNF implicationCNF assignment

    witnessClauseTrue : witnessClauseValue ≡ true
    witnessClauseTrue =
      Endpoint.andTrueLeft witnessClauseValue implicationValue accepted

    implicationTrue : implicationValue ≡ true
    implicationTrue =
      Endpoint.andTrueRight witnessClauseValue implicationValue accepted

    witness =
      orPositiveWitness (Endpoint.witnessIndex {machine} {steps} {cols})
        (Endpoint.finList cols) assignment witnessClauseTrue

    allSatisfied =
      allPlacedToAcceptanceSatisfied
        stateCoverage symbolCoverage assignment
        (Endpoint.finList cols)
        (Placed.compilePlacedAllSound
          (Endpoint.acceptanceImplicationPredicatesFin {machine} {steps} {cols}
            stateCoverage symbolCoverage (Endpoint.finList cols))
          assignment implicationTrue)
