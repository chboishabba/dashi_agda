module DASHI.Mathematics.Complexity.ConcreteTapeAfterUniqueFromLocalityExact where

------------------------------------------------------------------------
-- BEFORE INTERIOR + LEGAL WHOLE-ROW SCAN + NO-GHOST ENDCAPS
--   -> AFTER EXACTLY ONE HEAD (CONDITIONAL, PROOF RELEVANT)
--
-- Original unrestricted scan-to-afterUnique is FALSE: boundary overlap
-- windows can introduce phantom heads. The repaired theorem consumes
-- explicit FrontPlain/EndPlain witnesses for the *same* extracted center
-- and proves plain contexts by genuine inward inductions. The original
-- SAT compiler must still construct these boundary witnesses.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeLocalWindowPatternsExact as Pattern
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeWholeRowLocalityExact as Whole
import DASHI.Mathematics.Complexity.ConcreteTapeCenteredWindowExtractionExact as Center
import DASHI.Mathematics.Complexity.ConcreteTapeCenteredRewriteReconstructionExact as Reconstruct
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalPrefixAgreementExact as Prefix
import DASHI.Mathematics.Complexity.ConcreteTapeOccurrenceCoordinateExact as Coordinate
import DASHI.Mathematics.Complexity.ConcreteTapeLocalityCharacterizationExact as Character

------------------------------------------------------------------------
-- Aligned old-plain prefix forces the new prefix plain.
------------------------------------------------------------------------

-- The preconditions are minimal *end-cell* guards. The old theorem
-- without them is false (see ConcreteTapeBoundaryGhostCounterexampleExact).
-- An initial new prefix head can otherwise be fabricated by a
-- right-overlap-plus-two pattern at column zero; the symmetric
-- left-overlap-minus-two can fabricate a head at the final column.
--
-- This is an actual induction on the original sliding-window list,
-- not an assumption that every new context cell is already plain.

afterPrefixPlainFromLegalScan :
  ∀ {machine rule oldLeft oldCenter oldRight newLeft newCenter newRight
      oldSuffix newSuffix}
    (beforePrefix afterPrefix :
      List (Local.TapeCell
        (Local.State machine)
        (Local.Symbol machine))) →
  WF.PlainCells beforePrefix →
  Pattern.IsPlainCell oldLeft →
  Pattern.FrontPlain afterPrefix →
  Coordinate.listLength beforePrefix
    ≡ Coordinate.listLength afterPrefix →
  Whole.All
    (Pattern.LegalWindowForRule machine rule)
    (Whole.scanWindowsCells machine
      (Local.append beforePrefix
        (oldLeft ∷ oldCenter ∷ oldRight ∷ oldSuffix))
      (Local.append afterPrefix
        (newLeft ∷ newCenter ∷ newRight ∷ newSuffix))) →
  WF.PlainCells afterPrefix

afterPrefixPlainFromLegalScan
    [] [] WF.plainNil oldLeftPlain Pattern.frontNil lengthEq legal =
  WF.plainNil

afterPrefixPlainFromLegalScan
    [] (_ ∷ afterPrefix) WF.plainNil
    oldLeftPlain newFront () legal

afterPrefixPlainFromLegalScan
    (Local.plain oldSymbol ∷ beforePrefix) []
    (WF.plainCons beforePlain)
    oldLeftPlain Pattern.frontNil () legal

afterPrefixPlainFromLegalScan
    (Local.plain oldSymbol ∷ [])
    (Local.plain newSymbol ∷ [])
    (WF.plainCons WF.plainNil)
    oldLeftPlain Pattern.frontCons lengthEq legal =
  WF.plainCons WF.plainNil

afterPrefixPlainFromLegalScan
    (Local.plain oldSymbol ∷ [])
    (Local.plain newSymbol ∷ newNext ∷ restAfter)
    (WF.plainCons WF.plainNil)
    oldLeftPlain Pattern.frontCons () legal

afterPrefixPlainFromLegalScan
    (Local.plain oldFirst ∷ Local.plain oldSecond ∷ beforeRest)
    (Local.plain newFirst ∷ [])
    (WF.plainCons (WF.plainCons restPlain))
    oldLeftPlain Pattern.frontCons () legal

afterPrefixPlainFromLegalScan
    (Local.plain oldFirst ∷ Local.plain oldSecond ∷ [])
    (Local.plain newFirst ∷ newSecond ∷ afterRest)
    (WF.plainCons (WF.plainCons WF.plainNil))
    Pattern.is-plain Pattern.frontCons lengthEq
    (Whole.allCons firstLegal restLegal)
  with Pattern.legalPlainTripleNewLeftPlainForcesMiddlePlain
    firstLegal Pattern.is-plain
... | Pattern.is-plain =
  WF.plainCons
    (afterPrefixPlainFromLegalScan
      (Local.plain oldSecond ∷ [])
      (Local.plain newSecond ∷ afterRest)
      (WF.plainCons WF.plainNil)
      Pattern.is-plain
      Pattern.frontCons
      (NatP.suc-injective lengthEq)
      restLegal)

afterPrefixPlainFromLegalScan
    (Local.plain oldFirst
      ∷ Local.plain oldSecond
      ∷ Local.plain oldThird ∷ beforeRest)
    (Local.plain newFirst ∷ newSecond ∷ afterRest)
    (WF.plainCons
      (WF.plainCons
        (WF.plainCons restPlain)))
    oldLeftPlain Pattern.frontCons lengthEq
    (Whole.allCons firstLegal restLegal)
  with Pattern.legalPlainTripleNewLeftPlainForcesMiddlePlain
    firstLegal Pattern.is-plain
... | Pattern.is-plain =
  WF.plainCons
    (afterPrefixPlainFromLegalScan
      (Local.plain oldSecond ∷ Local.plain oldThird ∷ beforeRest)
      (Local.plain newSecond ∷ afterRest)
      (WF.plainCons (WF.plainCons restPlain))
      oldLeftPlain
      Pattern.frontCons
      (NatP.suc-injective lengthEq)
      restLegal)

------------------------------------------------------------------------
-- The suffix is proved from its final cell backwards. For a suffix of
-- length >= 2 the second sliding window and the already-proved tail
-- exclude the ghost-head branch at the first suffix cell.
------------------------------------------------------------------------

afterSuffixPlainFromLegalTail :
  ∀ {machine rule oldPrevious oldPreviousTwo newPrevious newPreviousTwo}
    (oldSuffix newSuffix :
      List (Local.TapeCell
        (Local.State machine)
        (Local.Symbol machine))) →
  WF.PlainCells oldSuffix →
  Pattern.IsPlainCell oldPreviousTwo →
  Pattern.EndPlain newSuffix →
  Coordinate.listLength oldSuffix
    ≡ Coordinate.listLength newSuffix →
  Whole.All
    (Pattern.LegalWindowForRule machine rule)
    (Whole.scanWindowsCells machine
      (oldPrevious ∷ oldPreviousTwo ∷ oldSuffix)
      (newPrevious ∷ newPreviousTwo ∷ newSuffix)) →
  WF.PlainCells newSuffix

afterSuffixPlainFromLegalTail
    [] [] WF.plainNil oldSecondPlain Pattern.endNil lengthEq legal =
  WF.plainNil

afterSuffixPlainFromLegalTail
    [] (_ ∷ newRest) WF.plainNil oldSecondPlain endcap () legal

afterSuffixPlainFromLegalTail
    (Local.plain oldSymbol ∷ oldRest) []
    (WF.plainCons oldPlain) oldSecondPlain Pattern.endNil () legal

afterSuffixPlainFromLegalTail
    (Local.plain oldSymbol ∷ [])
    (Local.plain newSymbol ∷ [])
    (WF.plainCons WF.plainNil)
    oldSecondPlain Pattern.endOne lengthEq legal =
  WF.plainCons WF.plainNil

afterSuffixPlainFromLegalTail
    (Local.plain oldSymbol ∷ [])
    (newFirst ∷ newSecond ∷ afterRest)
    (WF.plainCons WF.plainNil)
    oldSecondPlain (Pattern.endMore afterEnd) () legal

afterSuffixPlainFromLegalTail
    (Local.plain oldFirst ∷ Local.plain oldSecond ∷ beforeRest)
    (newFirst ∷ [])
    (WF.plainCons (WF.plainCons beforeRestPlain))
    oldSecondPlain endcap () legal

afterSuffixPlainFromLegalTail
    (Local.plain oldFirst ∷ Local.plain oldSecond ∷ beforeRest)
    (newFirst ∷ newSecond ∷ afterRest)
    (WF.plainCons (WF.plainCons beforeRestPlain))
    Pattern.is-plain (Pattern.endMore tailEnd)
    lengthEq (Whole.allCons firstLegal restLegal)
  with afterSuffixPlainFromLegalTail
    (Local.plain oldSecond ∷ beforeRest)
    (newSecond ∷ afterRest)
    (WF.plainCons beforeRestPlain)
    Pattern.is-plain
    tailEnd
    (NatP.suc-injective lengthEq)
    restLegal
... | WF.plainCons afterTailPlain
  with restLegal
... | Whole.allCons secondLegal otherLegal
  with Pattern.legalPlainTripleNewRightPlainForcesMiddlePlain
    secondLegal Pattern.is-plain
... | Pattern.is-plain =
  WF.plainCons (WF.plainCons afterTailPlain)

------------------------------------------------------------------------
-- Strip aligned prefixes without requiring their symbols to be equal.
------------------------------------------------------------------------

dropAlignedPrefixScan :
  ∀ {machine rule oldLeft oldCenter oldRight newLeft newCenter newRight
      oldSuffix newSuffix}
    (beforePrefix afterPrefix :
      List (Local.TapeCell
        (Local.State machine)
        (Local.Symbol machine))) →
  Coordinate.listLength beforePrefix
    ≡ Coordinate.listLength afterPrefix →
  Whole.All
    (Pattern.LegalWindowForRule machine rule)
    (Whole.scanWindowsCells machine
      (Local.append beforePrefix
        (oldLeft ∷ oldCenter ∷ oldRight ∷ oldSuffix))
      (Local.append afterPrefix
        (newLeft ∷ newCenter ∷ newRight ∷ newSuffix))) →
  Whole.All
    (Pattern.LegalWindowForRule machine rule)
    (Whole.scanWindowsCells machine
      (oldLeft ∷ oldCenter ∷ oldRight ∷ oldSuffix)
      (newLeft ∷ newCenter ∷ newRight ∷ newSuffix))

dropAlignedPrefixScan [] [] refl legal =
  legal
dropAlignedPrefixScan [] (_ ∷ afterPrefix) () legal
dropAlignedPrefixScan (_ ∷ beforePrefix) [] () legal
dropAlignedPrefixScan
    (_ ∷ beforePrefix)
    (_ ∷ afterPrefix)
    lengthEq
    (Whole.allCons current rest) =
  dropAlignedPrefixScan
    beforePrefix afterPrefix
    (NatP.suc-injective lengthEq)
    rest

suffixLengthsFromAlignedDecomposition :
  ∀ {machine rule before after}
    (scan : Whole.GlobalTransitionScan machine rule before after) →
  Coordinate.listLength
    (Center.beforeSuffix
      (Center.centeredOccurrenceFromGlobalScan scan))
  ≡
  Coordinate.listLength
    (Center.afterSuffix
      (Center.centeredOccurrenceFromGlobalScan scan))
suffixLengthsFromAlignedDecomposition scan =
  cancelAligned
    (Center.alignedPrefixLength extracted)
    (trans
      (sym (cong Coordinate.listLength
        (Center.beforeDecomposition extracted)))
      (trans
        (Whole.sameRowLength scan)
        (cong Coordinate.listLength
          (Center.afterDecomposition extracted))))
  where
    extracted =
      Center.centeredOccurrenceFromGlobalScan scan

    cancelAligned :
      ∀ {A : Set}
        {bp ap : List A}
        {ol oc or nl nc nr : A}
        {bs as : List A} →
      Coordinate.listLength bp ≡ Coordinate.listLength ap →
      Coordinate.listLength
        (Local.append bp (ol ∷ oc ∷ or ∷ bs))
      ≡
      Coordinate.listLength
        (Local.append ap (nl ∷ nc ∷ nr ∷ as)) →
      Coordinate.listLength bs
      ≡ Coordinate.listLength as
    cancelAligned {bp = []} {ap = []} prefixLen totalLen =
      NatP.suc-injective
        (NatP.suc-injective
          (NatP.suc-injective totalLen))
    cancelAligned {bp = []} {ap = _ ∷ ap} () totalLen
    cancelAligned {bp = _ ∷ bp} {ap = []} () totalLen
    cancelAligned {bp = _ ∷ bp} {ap = _ ∷ ap}
        prefixLen totalLen =
      cancelAligned
        (NatP.suc-injective prefixLen)
        (NatP.suc-injective totalLen)

------------------------------------------------------------------------
-- Main uniqueness producer.
------------------------------------------------------------------------

globalTransitionScanAfterUnique :
  ∀ {machine rule before after}
    (scan : Whole.GlobalTransitionScan machine rule before after) →
  Character.InteriorHeadConfiguration machine before →
  Pattern.FrontPlain
    (Center.afterPrefix (Center.centeredOccurrenceFromGlobalScan scan)) →
  Pattern.EndPlain
    (Center.afterSuffix (Center.centeredOccurrenceFromGlobalScan scan)) →
  WF.ExactlyOneHead (Local.cells after)
globalTransitionScanAfterUnique scan interior frontGuard endGuard =
  WF.transportExactlyOneHead
    (sym (Center.afterDecomposition extracted))
    localUnique
  where
    extracted =
      Center.centeredOccurrenceFromGlobalScan scan

    beforeUnique :
      WF.ExactlyOneHead (Local.cells before)
    beforeUnique =
      Character.interiorHeadIsUnique interior

    beforeContextPlain :
      WF.PlainCells (Center.beforePrefix extracted)
      × WF.PlainCells (Center.beforeSuffix extracted)
    beforeContextPlain =
      Reconstruct.beforeExtractedContextIsPlain
        scan beforeUnique

    beforePrefixPlain =
      proj₁ beforeContextPlain

    beforeSuffixPlain =
      proj₂ beforeContextPlain

    decomposedLegal :
      Whole.All
        (Pattern.LegalWindowForRule machine rule)
        (Whole.scanWindowsCells machine
          (Local.append
            (Center.beforePrefix extracted)
            (Local.oldLeft (Center.window extracted)
              ∷ Local.oldCenter (Center.window extracted)
              ∷ Local.oldRight (Center.window extracted)
              ∷ Center.beforeSuffix extracted))
          (Local.append
            (Center.afterPrefix extracted)
            (Local.newLeft (Center.window extracted)
              ∷ Local.newCenter (Center.window extracted)
              ∷ Local.newRight (Center.window extracted)
              ∷ Center.afterSuffix extracted)))
    decomposedLegal =
      Prefix.transportAllToDecomposedRows
        (Center.beforeDecomposition extracted)
        (Center.afterDecomposition extracted)
        (Whole.everyWindowLegal scan)

    afterPrefixPlain :
      WF.PlainCells (Center.afterPrefix extracted)
    afterPrefixPlain =
      afterPrefixPlainFromLegalScan
        (Center.beforePrefix extracted)
        (Center.afterPrefix extracted)
        beforePrefixPlain
        (Pattern.configuredOldLeftPlain (Center.configured extracted))
        frontGuard
        (Center.alignedPrefixLength extracted)
        decomposedLegal

    centeredAndTail :
      Whole.All
        (Pattern.LegalWindowForRule machine rule)
        (Whole.scanWindowsCells machine
          (Local.oldLeft (Center.window extracted)
            ∷ Local.oldCenter (Center.window extracted)
            ∷ Local.oldRight (Center.window extracted)
            ∷ Center.beforeSuffix extracted)
          (Local.newLeft (Center.window extracted)
            ∷ Local.newCenter (Center.window extracted)
            ∷ Local.newRight (Center.window extracted)
            ∷ Center.afterSuffix extracted))
    centeredAndTail =
      dropAlignedPrefixScan
        (Center.beforePrefix extracted)
        (Center.afterPrefix extracted)
        (Center.alignedPrefixLength extracted)
        decomposedLegal

    tailLegal :
      Whole.All
        (Pattern.LegalWindowForRule machine rule)
        (Whole.scanWindowsCells machine
          (Local.oldCenter (Center.window extracted)
            ∷ Local.oldRight (Center.window extracted)
            ∷ Center.beforeSuffix extracted)
          (Local.newCenter (Center.window extracted)
            ∷ Local.newRight (Center.window extracted)
            ∷ Center.afterSuffix extracted))
    tailLegal
      with centeredAndTail
    ... | Whole.allCons centered rest =
      rest

    afterSuffixPlain :
      WF.PlainCells (Center.afterSuffix extracted)
    afterSuffixPlain =
      afterSuffixPlainFromLegalTail
        (Center.beforeSuffix extracted)
        (Center.afterSuffix extracted)
        beforeSuffixPlain
        (Pattern.configuredOldRightPlain (Center.configured extracted))
        endGuard
        (suffixLengthsFromAlignedDecomposition scan)
        tailLegal

    localUnique :
      WF.ExactlyOneHead
        (Local.append
          (Center.afterPrefix extracted)
          (Local.newLeft (Center.window extracted)
            ∷ Local.newCenter (Center.window extracted)
            ∷ Local.newRight (Center.window extracted)
            ∷ Center.afterSuffix extracted))
    localUnique
      with Center.configured extracted
    ... | Local.realizes-left =
      WF.prependPlain afterPrefixPlain
        (WF.headHere
          (WF.plainCons
            (WF.plainCons afterSuffixPlain)))
    ... | Local.realizes-stay =
      WF.prependPlain afterPrefixPlain
        (WF.plainBefore
          (WF.headHere
            (WF.plainCons afterSuffixPlain)))
    ... | Local.realizes-right =
      WF.prependPlain afterPrefixPlain
        (WF.plainBefore
          (WF.plainBefore
            (WF.headHere afterSuffixPlain)))

------------------------------------------------------------------------
-- Explicit, proof-relevant anti-phantom boundary contract for the SAME
-- centered occurrence extracted from the original semantic scan.
--
-- The original CNF does not currently carry this record. It must be
-- constructed by the canonical boundary CNF producer, not by a
-- postulate, an inferred record field, or the original old-head margin.
------------------------------------------------------------------------

record NoGhostContextBoundaries
    {machine rule before after}
    (scan : Character.TransitionLocalityScan machine rule before after)
    (interior : Character.InteriorHeadConfiguration machine before) : Set where
  field
    afterPrefixStartsPlain :
      Pattern.FrontPlain
        (Center.afterPrefix
          (Center.centeredOccurrenceFromGlobalScan
            (Character.localityScanToGlobalTransitionScan scan interior)))
    afterSuffixEndsPlain :
      Pattern.EndPlain
        (Center.afterSuffix
          (Center.centeredOccurrenceFromGlobalScan
            (Character.localityScanToGlobalTransitionScan scan interior)))

open NoGhostContextBoundaries public

localityScanWithInteriorGivesWellFormedStep :
  ∀ {machine rule before after}
    (scan : Character.TransitionLocalityScan machine rule before after) →
  (interior : Character.InteriorHeadConfiguration machine before) →
  NoGhostContextBoundaries scan interior →
  WF.WellFormedMachineStep machine before after
localityScanWithInteriorGivesWellFormedStep scan interior boundary =
  Character.localityCharacterizationGivesWellFormedStep
    record
      { Character.beforeInterior = interior
      ; Character.afterUnique =
          globalTransitionScanAfterUnique
            (Character.localityScanToGlobalTransitionScan scan interior)
            interior
            (afterPrefixStartsPlain boundary)
            (afterSuffixEndsPlain boundary)
      ; Character.localityScan = scan
      }

