module DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunAcceptCompleteExact where

------------------------------------------------------------------------
-- REVERSE COOK--LEVIN: ACTUAL ACCEPTING RUN SATISFIES ACCEPTING ENDPOINT
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.ConcreteTapeRunCNFWeldExact as Run
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunCNFExact as Accepting
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunAssignmentExact as Assignment
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunInitialCompleteExact as Ends
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalFormulaSemanticsExact as FormulaSem
import DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact as Endpoint
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptanceDecodedFinalRowExact as Final
import DASHI.Mathematics.Complexity.ConcreteTapeDecodedWindowSameObjectExact as Same
import DASHI.Mathematics.Complexity.ConcreteTapeIndexedWindowExact as Indexed
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTracePlacementExact as Global
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalBlockSliceConsistencyExact as Slice
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalWindowPlacementExact as Placement
import DASHI.Mathematics.Complexity.CNFVariableRenamingExact as Rename
import DASHI.Mathematics.Complexity.CNFPlacedConstraintConjunctionExact as Placed
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

------------------------------------------------------------------------
-- One-hot structural facts
------------------------------------------------------------------------

zerosLookupFalse :
  ∀ n (i : Fin.Fin n) →
  CNF.lookupBit (DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact.zeros n) i
  ≡ false
zerosLookupFalse (suc n) Fin.zero = refl
zerosLookupFalse (suc n) (Fin.suc i) =
  zerosLookupFalse n i

oneHotTrueImpliesOccurrence :
  ∀ {A : Set} {n : Nat} {x : A} {xs : List A}
    (occurrence : Indexed.At n x xs)
    (i : Fin.Fin (Canonical.listLength xs)) →
  CNF.lookupBit (Assignment.oneHotAtOccurrence occurrence) i
  ≡ true →
  Indexed.At (Fin.toℕ i) x xs
oneHotTrueImpliesOccurrence Indexed.here Fin.zero accepted =
  Indexed.here
oneHotTrueImpliesOccurrence {xs = x ∷ xs}
    Indexed.here (Fin.suc i) accepted
    with zerosLookupFalse (Canonical.listLength xs) i
... | refl
    with accepted
... | ()
oneHotTrueImpliesOccurrence
    (Indexed.there occurrence) Fin.zero ()
oneHotTrueImpliesOccurrence
    (Indexed.there occurrence) (Fin.suc i) accepted =
  Indexed.there
    (oneHotTrueImpliesOccurrence occurrence i accepted)

atValueUnique :
  ∀ {A : Set} {n : Nat} {x y : A} {xs : List A} →
  Indexed.At n x xs →
  Indexed.At n y xs →
  x ≡ y
atValueUnique Indexed.here Indexed.here =
  refl
atValueUnique
    (Indexed.there left)
    (Indexed.there right) =
  atValueUnique left right

------------------------------------------------------------------------
-- Witness suffix lookup
------------------------------------------------------------------------

witnessLookup :
  ∀ {machine start rows finish}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (certificate :
      Accepting.AcceptingWellFormedRun
        machine start rows finish)
    (i : Fin.Fin (Canonical.listLength (Local.cells start))) →
  CNF.lookupBit
    (Assignment.encodeAcceptingRunAssignment
      stateCoverage symbolCoverage certificate)
    (Endpoint.witnessIndex i)
  ≡
  CNF.lookupBit
    (Assignment.castBits
      (sym (Assignment.runFinishCanonicalLength
        (Accepting.run certificate)))
      (Assignment.acceptingWitnessBits
        (Accepting.accepting certificate)))
    i
witnessLookup
    stateCoverage symbolCoverage certificate i =
  trans
    (sym
      (Slice.lookupDropBits
        (Assignment.encodeAcceptingRunAssignment
          stateCoverage symbolCoverage certificate)
        i))
    (cong
      (λ bits → CNF.lookupBit bits i)
      (Assignment.encodeAcceptingRunAssignment_witness
        stateCoverage symbolCoverage certificate))

acceptanceLocalHeadLookup :
  ∀ {machine steps cols}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (assignment :
      CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps cols))
    (i : Fin.Fin cols) →
  CNF.lookupBit
    (Rename.pullbackBits
      (Endpoint.acceptanceLocalRename (Endpoint.finToSlot i))
      assignment)
    Fin.zero
  ≡
  CNF.lookupBit assignment (Endpoint.witnessIndex i)
acceptanceLocalHeadLookup
    stateCoverage symbolCoverage assignment Fin.zero =
  Rename.pullbackLookup
    (Endpoint.acceptanceLocalRename (Endpoint.finToSlot Fin.zero))
    assignment Fin.zero
acceptanceLocalHeadLookup
    stateCoverage symbolCoverage assignment (Fin.suc i) =
  Rename.pullbackLookup
    (Endpoint.acceptanceLocalRename (Endpoint.finToSlot (Fin.suc i)))
    assignment Fin.zero

acceptanceLocalTail :
  ∀ {machine steps cols}
    (assignment :
      CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps cols))
    (i : Fin.Fin cols) →
  Canonical.dropBits 1
    (Rename.pullbackBits
      (Endpoint.acceptanceLocalRename (Endpoint.finToSlot i))
      assignment)
  ≡
  Final.extendedFinalCellBits i assignment
acceptanceLocalTail assignment i =
  Placement.bitsExt λ j →
    trans
      (Slice.lookupDropBits
        (Rename.pullbackBits
          (Endpoint.acceptanceLocalRename (Endpoint.finToSlot i))
          assignment)
        j)
      (trans
        (Rename.pullbackLookup
          (Endpoint.acceptanceLocalRename (Endpoint.finToSlot i))
          assignment
          (Fin.suc j))
        (sym
          (Rename.pullbackLookup
            (λ k →
              Endpoint.liftBaseIndex
                (Global.globalRowRename
                  (Endpoint.finalRowSlot _)
                  (Global.blockRename
                    (Endpoint.finToSlot i) k)))
            assignment j)))

------------------------------------------------------------------------
-- Local accepting implication is true for the constructed one-hot witness
------------------------------------------------------------------------

witnessPredicateFalse :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (bits : CNF.Bits (Endpoint.AcceptanceLocalWidth machine)) →
  CNF.lookupBit bits Fin.zero ≡ false →
  Endpoint.witnessAcceptingPredicate
    stateCoverage symbolCoverage bits
  ≡ true
witnessPredicateFalse
    stateCoverage symbolCoverage
    (false CNF.∷ᵇ bits) refl =
  refl
witnessPredicateFalse
    stateCoverage symbolCoverage
    (true CNF.∷ᵇ bits) ()

witnessPredicateTrueAccepting :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (bits : CNF.Bits (Endpoint.AcceptanceLocalWidth machine))
    (symbol : Local.Symbol machine) →
  CNF.lookupBit bits Fin.zero ≡ true →
  Canonical.decodeCell stateCoverage symbolCoverage
    (Canonical.dropBits 1 bits)
  ≡ Local.headed (Local.acceptingState machine) symbol →
  Endpoint.witnessAcceptingPredicate
    stateCoverage symbolCoverage bits
  ≡ true
witnessPredicateTrueAccepting
    {machine} stateCoverage symbolCoverage
    (true CNF.∷ᵇ bits) symbol refl decoded
    rewrite decoded
          | Local.decideEqualRefl
              (Local.finiteState machine)
              (Local.acceptingState machine) =
  refl
witnessPredicateTrueAccepting
    stateCoverage symbolCoverage
    (false CNF.∷ᵇ bits) symbol ()

------------------------------------------------------------------------
-- Fin-list coverage and witness clause
------------------------------------------------------------------------

data Member {A : Set} (x : A) : List A → Set where
  here : ∀ {xs} → Member x (x ∷ xs)
  there : ∀ {y xs} → Member x xs → Member x (y ∷ xs)

mapFinSucMember :
  ∀ {n} {i : Fin.Fin n} {xs : List (Fin.Fin n)} →
  Member i xs →
  Member (Fin.suc i) (Endpoint.mapFinSuc xs)
mapFinSucMember here =
  here
mapFinSucMember (there member) =
  there (mapFinSucMember member)

finListComplete :
  ∀ {n} (i : Fin.Fin n) →
  Member i (Endpoint.finList n)
finListComplete {suc n} Fin.zero =
  here
finListComplete {suc n} (Fin.suc i) =
  there (mapFinSucMember (finListComplete i))

positiveWitnessClauseTrue :
  ∀ {machine steps cols}
    (assignment :
      CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps cols))
    {i : Fin.Fin cols}
    (indices : List (Fin.Fin cols)) →
  Member i indices →
  CNF.lookupBit assignment (Endpoint.witnessIndex i) ≡ true →
  CNF.evaluateClause
    (Endpoint.allWitnessPositiveLiterals
      (λ j → CNF.positive (Endpoint.witnessIndex j))
      indices)
    assignment
  ≡ true
positiveWitnessClauseTrue assignment
    (i ∷ rest) here witnessTrue
    rewrite witnessTrue =
  refl
positiveWitnessClauseTrue assignment
    (j ∷ rest) (there membership) witnessTrue
    with CNF.lookupBit assignment (Endpoint.witnessIndex j)
... | true = refl
... | false =
  positiveWitnessClauseTrue
    assignment rest membership witnessTrue

------------------------------------------------------------------------
-- The accepting endpoint is complete for the canonical run assignment
------------------------------------------------------------------------

acceptingEndpointCNF_complete_for_run :
  ∀ {machine start rows finish}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (certificate :
      Accepting.AcceptingWellFormedRun
        machine start rows finish) →
  CNF.evaluateCNF
    (Endpoint.acceptingEndpointCNF
      stateCoverage symbolCoverage)
    (Assignment.encodeAcceptingRunAssignment
      stateCoverage symbolCoverage certificate)
  ≡ true
acceptingEndpointCNF_complete_for_run
    stateCoverage symbolCoverage certificate
    with Assignment.runFinishCanonicalLength
      (Accepting.run certificate)
... | refl
    with Assignment.acceptingHeadOccurrence
      (Accepting.accepting certificate)
... | n , symbol , acceptingOccurrence =
  endpointComplete
  where
    assignment =
      Assignment.encodeAcceptingRunAssignment
        stateCoverage symbolCoverage certificate

    witnessBits =
      Assignment.oneHotAtOccurrence acceptingOccurrence

    acceptingIndex :
      Fin.Fin (Canonical.listLength
        (Local.cells _))
    acceptingIndex =
      atFin acceptingOccurrence
      where
        atFin :
          ∀ {A : Set} {k : Nat} {x : A} {xs : List A} →
          Indexed.At k x xs →
          Fin.Fin (Canonical.listLength xs)
        atFin Indexed.here =
          Fin.zero
        atFin (Indexed.there occurrence) =
          Fin.suc (atFin occurrence)

    acceptingIndexTrue :
      CNF.lookupBit assignment
        (Endpoint.witnessIndex acceptingIndex)
      ≡ true
    acceptingIndexTrue =
      trans
        (witnessLookup
          stateCoverage symbolCoverage certificate
          acceptingIndex)
        oneHotSelf
      where
        oneHotSelf :
          CNF.lookupBit witnessBits acceptingIndex ≡ true
        oneHotSelf =
          prove acceptingOccurrence
          where
            prove :
              ∀ {A : Set} {k : Nat} {x : A} {xs : List A}
                (occurrence : Indexed.At k x xs) →
              CNF.lookupBit
                (Assignment.oneHotAtOccurrence occurrence)
                (let
                  atFin :
                    ∀ {m : Nat} {y : A} {ys : List A} →
                    Indexed.At m y ys →
                    Fin.Fin (Canonical.listLength ys)
                  atFin Indexed.here = Fin.zero
                  atFin (Indexed.there p) = Fin.suc (atFin p)
                in atFin occurrence)
              ≡ true
            prove Indexed.here = refl
            prove (Indexed.there occurrence) =
              prove occurrence

    witnessClauseTrue :
      CNF.evaluateClause
        (Endpoint.someAcceptanceWitnessClause)
        assignment
      ≡ true
    witnessClauseTrue =
      positiveWitnessClauseTrue
        assignment
        (Endpoint.finList _)
        (finListComplete acceptingIndex)
        acceptingIndexTrue

    localPredicateTrue :
      ∀ (i : Fin.Fin (Canonical.listLength (Local.cells _))) →
      Placed.predicate
        (Endpoint.acceptancePlacedPredicate
          stateCoverage symbolCoverage (Endpoint.finToSlot i))
        (Rename.pullbackBits
          (Placed.rename
            (Endpoint.acceptancePlacedPredicate
              stateCoverage symbolCoverage (Endpoint.finToSlot i)))
          assignment)
      ≡ true
    localPredicateTrue i
      with CNF.lookupBit witnessBits i
    ... | false =
      witnessPredicateFalse
        stateCoverage symbolCoverage localBits
        headFalse
      where
        localBits =
          Rename.pullbackBits
            (Endpoint.acceptanceLocalRename (Endpoint.finToSlot i))
            assignment
        headFalse :
          CNF.lookupBit localBits Fin.zero ≡ false
        headFalse =
          trans
            (acceptanceLocalHeadLookup
              stateCoverage symbolCoverage assignment i)
            (trans
              (witnessLookup
                stateCoverage symbolCoverage certificate i)
              refl)
    ... | true =
      witnessPredicateTrueAccepting
        stateCoverage symbolCoverage localBits symbol
        headTrue decodedAccepting
      where
        localBits =
          Rename.pullbackBits
            (Endpoint.acceptanceLocalRename (Endpoint.finToSlot i))
            assignment

        headTrue :
          CNF.lookupBit localBits Fin.zero ≡ true
        headTrue =
          trans
            (acceptanceLocalHeadLookup
              stateCoverage symbolCoverage assignment i)
            (trans
              (witnessLookup
                stateCoverage symbolCoverage certificate i)
              refl)

        acceptingAtI :
          Indexed.At (Fin.toℕ i)
            (Local.headed
              (Local.acceptingState machine) symbol)
            (Local.cells finish)
        acceptingAtI =
          oneHotTrueImpliesOccurrence
            acceptingOccurrence i refl

        decodedFinalOccurrence =
          Same.decodeCellsAtBlockSlice
            stateCoverage symbolCoverage
            (Endpoint.finToSlot i)
            (Global.rowSliceBits
              (Endpoint.finalRowSlot
                (Accepting.acceptingRunLength certificate))
              (FormulaSem.baseTraceBits assignment))

        decodedFinalEq =
          Ends.decodedAcceptingAssignment_finalRow
            stateCoverage symbolCoverage certificate

        decodedCellEq :
          Canonical.decodeCell stateCoverage symbolCoverage
            (Slice.blockSliceBits
              (Endpoint.finToSlot i)
              (Global.rowSliceBits
                (Endpoint.finalRowSlot
                  (Accepting.acceptingRunLength certificate))
                (FormulaSem.baseTraceBits assignment)))
          ≡ Local.headed
              (Local.acceptingState machine) symbol
        decodedCellEq =
          atValueUnique
            (transportList decodedFinalEq decodedFinalOccurrence)
            acceptingAtI
          where
            transportList :
              ∀ {A : Set} {m : Nat} {x : A}
                {left right : List A} →
              left ≡ right →
              Indexed.At m x left →
              Indexed.At m x right
            transportList refl occurrence =
              occurrence

        decodedAccepting :
          Canonical.decodeCell stateCoverage symbolCoverage
            (Canonical.dropBits 1 localBits)
          ≡ Local.headed
              (Local.acceptingState machine) symbol
        decodedAccepting =
          trans
            (cong
              (Canonical.decodeCell
                stateCoverage symbolCoverage)
              (trans
                (acceptanceLocalTail assignment i)
                (Final.extendedFinalCellBits_eq_finalRowBlock
                  i assignment)))
            decodedCellEq

    allPlaced :
      Placed.AllPlacedSatisfied assignment
        (Endpoint.acceptanceImplicationPredicatesFin
          stateCoverage symbolCoverage
          (Endpoint.finList _))
    allPlaced =
      build (Endpoint.finList _)
      where
        build :
          ∀ indices →
          Placed.AllPlacedSatisfied assignment
            (Endpoint.acceptanceImplicationPredicatesFin
              stateCoverage symbolCoverage indices)
        build [] =
          Placed.allPlacedDone
        build (i ∷ rest) =
          Placed.allPlacedStep
            (localPredicateTrue i)
            (build rest)

    implicationsTrue :
      CNF.evaluateCNF
        (Placed.compilePlacedAll
          (Endpoint.acceptanceImplicationPredicatesFin
            stateCoverage symbolCoverage
            (Endpoint.finList _)))
        assignment
      ≡ true
    implicationsTrue =
      Placed.compilePlacedAllComplete
        (Endpoint.acceptanceImplicationPredicatesFin
          stateCoverage symbolCoverage
          (Endpoint.finList _))
        assignment allPlaced

    endpointComplete :
      CNF.evaluateCNF
        (Endpoint.acceptingEndpointCNF
          stateCoverage symbolCoverage)
        assignment
      ≡ true
    endpointComplete
      rewrite witnessClauseTrue
            | implicationsTrue =
      refl
