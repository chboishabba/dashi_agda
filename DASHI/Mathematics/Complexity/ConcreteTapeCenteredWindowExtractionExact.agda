module DASHI.Mathematics.Complexity.ConcreteTapeCenteredWindowExtractionExact where

------------------------------------------------------------------------
-- CENTERED SCAN WITNESS -> ALIGNED GLOBAL ROW DECOMPOSITION
--
-- A centered rule witness inside the recursive sliding-window scan is not an
-- unlocated existential: recursion determines one aligned coordinate in both
-- rows.  This module extracts exact before/after list decompositions with
-- prefixes of the same length.
--
-- It deliberately does NOT yet identify the two prefixes or two suffixes.
-- That is the remaining compatibility theorem supplied by the surrounding
-- legal-window scan plus unique-head well-formedness.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeOccurrenceCoordinateExact as Coordinate
import DASHI.Mathematics.Complexity.ConcreteTapeWholeRowLocalityExact as Whole

record AlignedCenteredOccurrence
    (machine : Local.ConcreteTapeMachine)
    (rule : Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine))
    (beforeCells afterCells :
      List (Local.TapeCell
        (Local.State machine)
        (Local.Symbol machine))) : Set where
  field
    beforePrefix afterPrefix :
      List (Local.TapeCell
        (Local.State machine)
        (Local.Symbol machine))

    beforeSuffix afterSuffix :
      List (Local.TapeCell
        (Local.State machine)
        (Local.Symbol machine))

    window :
      Local.SixCellWindow machine

    configured :
      Local.RuleRealizesWindow machine rule window

    alignedPrefixLength :
      Coordinate.listLength beforePrefix
      ≡ Coordinate.listLength afterPrefix

    beforeDecomposition :
      beforeCells
      ≡ Local.append beforePrefix
          (Local.oldLeft window
            ∷ Local.oldCenter window
            ∷ Local.oldRight window
            ∷ beforeSuffix)

    afterDecomposition :
      afterCells
      ≡ Local.append afterPrefix
          (Local.newLeft window
            ∷ Local.newCenter window
            ∷ Local.newRight window
            ∷ afterSuffix)

open AlignedCenteredOccurrence public

prependAligned :
  ∀ {machine rule beforeTail afterTail}
    (beforeHead afterHead :
      Local.TapeCell
        (Local.State machine)
        (Local.Symbol machine)) →
  AlignedCenteredOccurrence
    machine rule beforeTail afterTail →
  AlignedCenteredOccurrence
    machine rule
    (beforeHead ∷ beforeTail)
    (afterHead ∷ afterTail)
prependAligned beforeHead afterHead occurrence = record
  { beforePrefix =
      beforeHead ∷ beforePrefix occurrence
  ; afterPrefix =
      afterHead ∷ afterPrefix occurrence
  ; beforeSuffix =
      beforeSuffix occurrence
  ; afterSuffix =
      afterSuffix occurrence
  ; window =
      window occurrence
  ; configured =
      configured occurrence
  ; alignedPrefixLength =
      congSuc (alignedPrefixLength occurrence)
  ; beforeDecomposition =
      congCons beforeHead (beforeDecomposition occurrence)
  ; afterDecomposition =
      congCons afterHead (afterDecomposition occurrence)
  }
  where
    congSuc : ∀ {m n : Nat} → m ≡ n → suc m ≡ suc n
    congSuc refl = refl

    congCons :
      ∀ {A : Set} (head : A) {xs ys : List A} →
      xs ≡ ys → head ∷ xs ≡ head ∷ ys
    congCons head refl = refl

centeredScanExtract :
  ∀ {machine rule beforeCells afterCells} →
  Whole.ContainsCenteredRuleWindow machine rule
    (Whole.scanWindowsCells machine beforeCells afterCells) →
  AlignedCenteredOccurrence
    machine rule beforeCells afterCells

centeredScanExtract {beforeCells = []} ()
centeredScanExtract {beforeCells = _ ∷ []} ()
centeredScanExtract {beforeCells = _ ∷ _ ∷ []} ()
centeredScanExtract
    {beforeCells = _ ∷ _ ∷ _ ∷ _}
    {afterCells = []} ()
centeredScanExtract
    {beforeCells = _ ∷ _ ∷ _ ∷ _}
    {afterCells = _ ∷ []} ()
centeredScanExtract
    {beforeCells = _ ∷ _ ∷ _ ∷ _}
    {afterCells = _ ∷ _ ∷ []} ()

centeredScanExtract
    {beforeCells =
      oldLeft ∷ oldCenter ∷ oldRight ∷ oldRest}
    {afterCells =
      newLeft ∷ newCenter ∷ newRight ∷ newRest}
    (Whole.centeredHere configured) =
  record
    { beforePrefix = []
    ; afterPrefix = []
    ; beforeSuffix = oldRest
    ; afterSuffix = newRest
    ; window =
        Local.six-cell-window
          oldLeft oldCenter oldRight
          newLeft newCenter newRight
    ; configured = configured
    ; alignedPrefixLength = refl
    ; beforeDecomposition = refl
    ; afterDecomposition = refl
    }

centeredScanExtract
    {beforeCells =
      beforeHead ∷ beforeSecond ∷ beforeThird ∷ beforeRest}
    {afterCells =
      afterHead ∷ afterSecond ∷ afterThird ∷ afterRest}
    (Whole.centeredThere later) =
  prependAligned beforeHead afterHead
    (centeredScanExtract later)

centeredOccurrenceFromGlobalScan :
  ∀ {machine rule before after} →
  Whole.GlobalTransitionScan machine rule before after →
  AlignedCenteredOccurrence
    machine rule (Local.cells before) (Local.cells after)
centeredOccurrenceFromGlobalScan scan =
  centeredScanExtract (Whole.centeredTransitionOccurs scan)

centeredOccurrenceCoordinate :
  ∀ {machine rule before after}
    (scan : Whole.GlobalTransitionScan machine rule before after) →
  Nat
centeredOccurrenceCoordinate scan =
  Coordinate.listLength
    (beforePrefix (centeredOccurrenceFromGlobalScan scan))

record ConcreteTapeCenteredWindowExtractionBoundary : Set where
  constructor concrete-tape-centered-window-extraction-boundary
  field
    recursiveCenteredExtractionPaid : Bool
    exactRowDecompositionsPaid : Bool
    alignedPrefixLengthPaid : Bool
    centeredScanGlobalExtractionPaid : Bool
    legalContextForcesCommonPrefixPaid : Bool
    legalContextForcesCommonSuffixPaid : Bool
    legalContextForcesCommonOutsidePaid : Bool
    globalTransitionScanToUniqueRewritePaid : Bool
    canonicalSATWeldPaid : Bool
    pVsNPResolved : Bool

canonicalConcreteTapeCenteredWindowExtractionBoundary :
  ConcreteTapeCenteredWindowExtractionBoundary
canonicalConcreteTapeCenteredWindowExtractionBoundary =
  concrete-tape-centered-window-extraction-boundary
    true true true true false false false false false false
