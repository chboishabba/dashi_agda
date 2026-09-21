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
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeLocalWindowPatternsExact as Pattern
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeWholeRowLocalityExact as Whole
import DASHI.Mathematics.Complexity.ConcreteTapeCenteredWindowExtractionExact as Center
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalPrefixAgreementExact as Prefix
import DASHI.Mathematics.Complexity.ConcreteTapeOccurrenceCoordinateExact as Coordinate
import DASHI.Mathematics.Complexity.ConcreteTapeLocalityCharacterizationExact as Character

------------------------------------------------------------------------
-- Aligned old-plain prefix forces the new prefix plain.
------------------------------------------------------------------------

afterPrefixPlainFromLegalScan :
  ∀ {machine rule oldLeft oldCenter oldRight newLeft newCenter newRight
      oldSuffix newSuffix}
    (beforePrefix afterPrefix :
      List (Local.TapeCell
        (Local.State machine)
        (Local.Symbol machine))) →
  WF.PlainCells beforePrefix →
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
    [] [] WF.plainNil lengthEq legal =
  WF.plainNil

afterPrefixPlainFromLegalScan
    []
    (_ ∷ afterPrefix)
    WF.plainNil
    ()

afterPrefixPlainFromLegalScan
    (Local.plain oldSymbol ∷ beforePrefix)
    []
    (WF.plainCons beforePlain)
    ()

afterPrefixPlainFromLegalScan
    (Local.plain oldSymbol ∷ beforePrefix)
    (newCell ∷ afterPrefix)
    (WF.plainCons beforePlain)
    lengthEq
    (Whole.allCons firstLegal restLegal)
    with Pattern.legalOldLeftPlainForcesNewLeftPlain firstLegal
... | Pattern.is-plain =
  WF.plainCons
    (afterPrefixPlainFromLegalScan
      beforePrefix afterPrefix
      beforePlain
      (NatP.suc-injective lengthEq)
      restLegal)

------------------------------------------------------------------------
-- Once the centered window is passed, every old suffix cell appears as the
-- right edge of a legal window, hence its aligned new cell is plain.
------------------------------------------------------------------------

afterSuffixPlainFromLegalTail :
  ∀ {machine rule oldPrevious oldPreviousTwo newPrevious newPreviousTwo}
    (oldSuffix newSuffix :
      List (Local.TapeCell
        (Local.State machine)
        (Local.Symbol machine))) →
  WF.PlainCells oldSuffix →
  Coordinate.listLength oldSuffix
    ≡ Coordinate.listLength newSuffix →
  Whole.All
    (Pattern.LegalWindowForRule machine rule)
    (Whole.scanWindowsCells machine
      (oldPrevious ∷ oldPreviousTwo ∷ oldSuffix)
      (newPrevious ∷ newPreviousTwo ∷ newSuffix)) →
  WF.PlainCells newSuffix

afterSuffixPlainFromLegalTail
    [] [] WF.plainNil lengthEq legal =
  WF.plainNil

afterSuffixPlainFromLegalTail
    []
    (_ ∷ newSuffix)
    WF.plainNil
    ()

afterSuffixPlainFromLegalTail
    (Local.plain oldSymbol ∷ oldSuffix)
    []
    (WF.plainCons oldPlain)
    ()

afterSuffixPlainFromLegalTail
    (Local.plain oldSymbol ∷ oldSuffix)
    (newCell ∷ newSuffix)
    (WF.plainCons oldPlain)
    lengthEq
    (Whole.allCons firstLegal restLegal)
    with Pattern.legalOldRightPlainForcesNewRightPlain firstLegal
... | Pattern.is-plain =
  WF.plainCons
    (afterSuffixPlainFromLegalTail
      oldSuffix newSuffix
      oldPlain
      (NatP.suc-injective lengthEq)
      restLegal)

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
  WF.ExactlyOneHead (Local.cells after)
globalTransitionScanAfterUnique scan interior =
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
      DASHI.Mathematics.Complexity.ConcreteTapeCenteredRewriteReconstructionExact.beforeExtractedContextIsPlain
        scan beforeUnique

    beforePrefixPlain =
      Data.Product.proj₁ beforeContextPlain

    beforeSuffixPlain =
      Data.Product.proj₂ beforeContextPlain

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

localityScanWithInteriorGivesWellFormedStep :
  ∀ {machine rule before after}
    (scan : Character.TransitionLocalityScan machine rule before after) →
  (interior : Character.InteriorHeadConfiguration machine before) →
  WF.WellFormedMachineStep machine before after
localityScanWithInteriorGivesWellFormedStep scan interior =
  Character.localityCharacterizationGivesWellFormedStep
    record
      { Character.beforeInterior = interior
      ; Character.afterUnique =
          globalTransitionScanAfterUnique
            (Character.localityScanToGlobalTransitionScan scan interior)
            interior
      ; Character.localityScan = scan
      }

