module DASHI.Mathematics.Complexity.ConcreteTapeAfterUniqueFromLocalityExact where

------------------------------------------------------------------------
-- BEFORE INTERIOR + LEGAL WHOLE-ROW SCAN -> AFTER EXACTLY ONE HEAD
--
-- This removes the extra afterUnique premise from the reverse locality
-- compiler.  Plain old context cells force aligned new context cells plain;
-- the one configured centered window contributes exactly one new head.
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
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalRewriteReconstructionExact as Reconstruct
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
    [] (_ ∷ _) WF.plainNil oldLeftPlain newFront () legal

afterPrefixPlainFromLegalScan
    (_ ∷ _) [] (WF.plainCons _) oldLeftPlain Pattern.frontNil () legal

afterPrefixPlainFromLegalScan
    (Local.plain oldSymbol ∷ [])
    (Local.plain newSymbol ∷ [])
    (WF.plainCons WF.plainNil)
    oldLeftPlain Pattern.frontCons lengthEq legal =
  WF.plainCons WF.plainNil

afterPrefixPlainFromLegalScan
    (Local.plain oldSymbol ∷ [])
    (Local.plain newSymbol ∷ _ ∷ _)
    (WF.plainCons WF.plainNil)
    oldLeftPlain Pattern.frontCons () legal

afterPrefixPlainFromLegalScan
    (Local.plain oldFirst ∷ Local.plain oldSecond ∷ _)
    (Local.plain newFirst ∷ [])
    (WF.plainCons (WF.plainCons _))
    oldLeftPlain Pattern.frontCons () legal

afterPrefixPlainFromLegalScan
    (Local.plain oldFirst ∷ Local.plain oldSecond ∷ [])
    (Local.plain newFirst ∷ newSecond ∷ [])
    (WF.plainCons (WF.plainCons WF.plainNil))
    Pattern.is-plain Pattern.frontCons lengthEq
    (Whole.allCons firstLegal restLegal)
  with Pattern.legalPlainTripleNewLeftPlainForcesMiddlePlain
    firstLegal Pattern.is-plain
... | Pattern.is-plain =
  WF.plainCons
    (afterPrefixPlainFromLegalScan
      (Local.plain oldSecond ∷ [])
      (newSecond ∷ [])
      (WF.plainCons WF.plainNil)
      Pattern.is-plain
      Pattern.frontCons
      (NatP.suc-injective lengthEq)
      restLegal)

afterPrefixPlainFromLegalScan
    (Local.plain oldFirst ∷ Local.plain oldSecond ∷ [])
    (Local.plain newFirst ∷ newSecond ∷ _ ∷ _)
    (WF.plainCons (WF.plainCons WF.plainNil))
    oldLeftPlain Pattern.frontCons () legal

afterPrefixPlainFromLegalScan
    (Local.plain oldFirst ∷ Local.plain oldSecond ∷ Local.plain oldThird ∷ _)
    (Local.plain newFirst ∷ newSecond ∷ [])
    (WF.plainCons (WF.plainCons (WF.plainCons _)))
    oldLeftPlain Pattern.frontCons () legal

afterPrefixPlainFromLegalScan
    (Local.plain oldFirst
      ∷ Local.plain oldSecond
      ∷ Local.plain oldThird ∷ beforeRest)
    (Local.plain newFirst ∷ newSecond ∷ newThird ∷ afterRest)
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
      (newSecond ∷ newThird ∷ afterRest)
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
dropAlignedPrefixScan [] (_ ∷ _) () legal
dropAlignedPrefixScan (_ ∷ _) [] () legal

dropAlignedPrefixScan
    (b1 ∷ [])
    (a1 ∷ [])
    lengthEq
    (Whole.allCons current rest) =
  rest
dropAlignedPrefixScan (b1 ∷ []) (_ ∷ _ ∷ _) () legal
dropAlignedPrefixScan (_ ∷ _ ∷ _) (a1 ∷ []) () legal

dropAlignedPrefixScan
    (b1 ∷ b2 ∷ [])
    (a1 ∷ a2 ∷ [])
    lengthEq
    (Whole.allCons current rest) =
  dropAlignedPrefixScan
    (b2 ∷ [])
    (a2 ∷ [])
    (NatP.suc-injective lengthEq)
    rest
dropAlignedPrefixScan (b1 ∷ b2 ∷ []) (_ ∷ _ ∷ _ ∷ _) () legal
dropAlignedPrefixScan (_ ∷ _ ∷ _ ∷ _) (a1 ∷ a2 ∷ []) () legal

dropAlignedPrefixScan
    (b1 ∷ b2 ∷ b3 ∷ beforeRest)
    (a1 ∷ a2 ∷ a3 ∷ afterRest)
    lengthEq
    (Whole.allCons current rest) =
  dropAlignedPrefixScan
    (b2 ∷ b3 ∷ beforeRest)
    (a2 ∷ a3 ∷ afterRest)
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
globalTransitionScanAfterUnique {machine} {rule} {before} {after} scan interior frontGuard endGuard =
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

    goUnique :
      ∀ {rule' window'} →
      Local.RuleRealizesWindow machine rule' window' →
      WF.ExactlyOneHead
        (Local.append
          (Center.afterPrefix extracted)
          (Local.newLeft window'
            ∷ Local.newCenter window'
            ∷ Local.newRight window'
            ∷ Center.afterSuffix extracted))
    goUnique Local.realizes-left =
      WF.prependPlain afterPrefixPlain
        (WF.headHere
          (WF.plainCons
            (WF.plainCons afterSuffixPlain)))
    goUnique Local.realizes-stay =
      WF.prependPlain afterPrefixPlain
        (WF.plainBefore
          (WF.headHere
            (WF.plainCons afterSuffixPlain)))
    goUnique Local.realizes-right =
      WF.prependPlain afterPrefixPlain
        (WF.plainBefore
          (WF.plainBefore
            (WF.headHere afterSuffixPlain)))

    localUnique :
      WF.ExactlyOneHead
        (Local.append
          (Center.afterPrefix extracted)
          (Local.newLeft (Center.window extracted)
            ∷ Local.newCenter (Center.window extracted)
            ∷ Local.newRight (Center.window extracted)
            ∷ Center.afterSuffix extracted))
    localUnique = goUnique (Center.configured extracted)

localityScanWithInteriorGivesWellFormedStep :
  ∀ {machine rule before after}
    (scan : Character.TransitionLocalityScan machine rule before after) →
  (interior : Character.InteriorHeadConfiguration machine before) →
  Pattern.FrontPlain
    (Center.afterPrefix
      (Center.centeredOccurrenceFromGlobalScan
        (Character.localityScanToGlobalTransitionScan scan interior))) →
  Pattern.EndPlain
    (Center.afterSuffix
      (Center.centeredOccurrenceFromGlobalScan
        (Character.localityScanToGlobalTransitionScan scan interior))) →
  WF.WellFormedMachineStep machine before after
localityScanWithInteriorGivesWellFormedStep scan interior
    frontGuard endGuard =
  Character.localityCharacterizationGivesWellFormedStep
    record
      { beforeInterior = interior
      ; afterUnique =
          globalTransitionScanAfterUnique
            (Character.localityScanToGlobalTransitionScan scan interior)
            interior frontGuard endGuard
      ; localityScan = scan
      }

