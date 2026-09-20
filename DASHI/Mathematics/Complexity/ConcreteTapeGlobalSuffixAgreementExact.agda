module DASHI.Mathematics.Complexity.ConcreteTapeGlobalSuffixAgreementExact where

------------------------------------------------------------------------
-- GLOBAL LEGALITY FORCES THE POST-TRANSITION SUFFIX TO BE IDENTICAL
--
-- Once prefix agreement is known, drop the common prefix and the centered
-- transition window.  Each following suffix symbol is then the rightmost cell
-- of the next sliding 2x3 window.  The local grammar proves that whenever both
-- rightmost cells are plain their symbols agree.  Equal row width gives equal
-- suffix length, so induction forces the whole suffixes equal.
--
-- Combining prefix and suffix agreement with the previous reconstruction
-- compiler closes the semantic reverse locality theorem:
--
--   exactly-one-head before/after + GlobalTransitionScan
--     -> WellFormedMachineStep.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥-elim)
import Data.Nat.Properties as NatP
open import Data.Product using (_×_; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeLocalWindowPatternsExact as Pattern
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeWholeRowLocalityExact as Whole
import DASHI.Mathematics.Complexity.ConcreteTapeCenteredWindowExtractionExact as Center
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalRewriteReconstructionExact as Reconstruct
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalPrefixAgreementExact as Prefix
import DASHI.Mathematics.Complexity.ConcreteTapeOccurrenceCoordinateExact as Coordinate

plainSuffixAfterHead :
  ∀ {State Symbol : Set}
    (prefix : List (Local.TapeCell State Symbol))
    {state symbol}
    (suffix : List (Local.TapeCell State Symbol)) →
  WF.ExactlyOneHead
    (Local.append prefix
      (Local.headed state symbol ∷ suffix)) →
  WF.PlainCells suffix
plainSuffixAfterHead [] suffix (WF.headHere suffixPlain) =
  suffixPlain
plainSuffixAfterHead
    (Local.plain prefixSymbol ∷ prefix)
    suffix
    (WF.plainBefore uniqueTail) =
  plainSuffixAfterHead prefix suffix uniqueTail
plainSuffixAfterHead
    (Local.headed prefixState prefixSymbol ∷ prefix)
    suffix
    (WF.headHere restPlain) =
  ⊥-elim
    (Reconstruct.plainCellsCannotContainLaterHead
      prefix suffix restPlain)

afterExtractedSuffixIsPlain :
  ∀ {machine rule before after}
    (scan : Whole.GlobalTransitionScan machine rule before after) →
  WF.ExactlyOneHead (Local.cells after) →
  WF.PlainCells
    (Center.afterSuffix
      (Center.centeredOccurrenceFromGlobalScan scan))
afterExtractedSuffixIsPlain scan afterUnique
    with Center.configured extracted
... | Local.realizes-left {b = written} {rightSymbol = rightSymbol}
    with plainSuffixAfterHead
      (Center.afterPrefix extracted)
      (Local.plain written
        ∷ Local.plain rightSymbol
        ∷ Center.afterSuffix extracted)
      (Prefix.transportUnique
        (Center.afterDecomposition extracted)
        afterUnique)
... | WF.plainCons (WF.plainCons suffixPlain) =
  suffixPlain
  where
    extracted = Center.centeredOccurrenceFromGlobalScan scan

afterExtractedSuffixIsPlain scan afterUnique
    | Local.realizes-stay =
  proj₂
    (Reconstruct.plainContextsAroundCenteredHead
      (Center.afterPrefix extracted)
      (Center.afterSuffix extracted)
      (Prefix.transportUnique
        (Center.afterDecomposition extracted)
        afterUnique))
  where
    extracted = Center.centeredOccurrenceFromGlobalScan scan

afterExtractedSuffixIsPlain scan afterUnique
    | Local.realizes-right {b = written} {leftSymbol = leftSymbol} =
  plainSuffixAfterHead
    (Local.append
      (Center.afterPrefix extracted)
      (Local.plain leftSymbol ∷ Local.plain written ∷ []))
    (Center.afterSuffix extracted)
    (Prefix.transportUnique
      (Center.afterDecomposition extracted)
      afterUnique)
  where
    extracted = Center.centeredOccurrenceFromGlobalScan scan

transportAllToCommonPrefix :
  ∀ {machine rule before after}
    (scan : Whole.GlobalTransitionScan machine rule before after) →
  (prefixEquality :
    Center.beforePrefix
      (Center.centeredOccurrenceFromGlobalScan scan)
    ≡ Center.afterPrefix
      (Center.centeredOccurrenceFromGlobalScan scan)) →
  Whole.All
    (Pattern.LegalWindowForRule machine rule)
    (Whole.scanWindowsCells machine
      (Local.append
        (Center.beforePrefix
          (Center.centeredOccurrenceFromGlobalScan scan))
        (Local.oldLeft
          (Center.window
            (Center.centeredOccurrenceFromGlobalScan scan))
          ∷ Local.oldCenter
            (Center.window
              (Center.centeredOccurrenceFromGlobalScan scan))
          ∷ Local.oldRight
            (Center.window
              (Center.centeredOccurrenceFromGlobalScan scan))
          ∷ Center.beforeSuffix
            (Center.centeredOccurrenceFromGlobalScan scan)))
      (Local.append
        (Center.beforePrefix
          (Center.centeredOccurrenceFromGlobalScan scan))
        (Local.newLeft
          (Center.window
            (Center.centeredOccurrenceFromGlobalScan scan))
          ∷ Local.newCenter
            (Center.window
              (Center.centeredOccurrenceFromGlobalScan scan))
          ∷ Local.newRight
            (Center.window
              (Center.centeredOccurrenceFromGlobalScan scan))
          ∷ Center.afterSuffix
            (Center.centeredOccurrenceFromGlobalScan scan))))
transportAllToCommonPrefix scan refl =
  Prefix.transportAllToDecomposedRows
    (Center.beforeDecomposition extracted)
    (Center.afterDecomposition extracted)
    (Whole.everyWindowLegal scan)
  where
    extracted = Center.centeredOccurrenceFromGlobalScan scan

dropCommonPrefixScan :
  ∀ {machine rule oldLeft oldCenter oldRight newLeft newCenter newRight
      oldSuffix newSuffix}
    (prefix :
      List (Local.TapeCell
        (Local.State machine)
        (Local.Symbol machine))) →
  Whole.All
    (Pattern.LegalWindowForRule machine rule)
    (Whole.scanWindowsCells machine
      (Local.append prefix
        (oldLeft ∷ oldCenter ∷ oldRight ∷ oldSuffix))
      (Local.append prefix
        (newLeft ∷ newCenter ∷ newRight ∷ newSuffix))) →
  Whole.All
    (Pattern.LegalWindowForRule machine rule)
    (Whole.scanWindowsCells machine
      (oldLeft ∷ oldCenter ∷ oldRight ∷ oldSuffix)
      (newLeft ∷ newCenter ∷ newRight ∷ newSuffix))
dropCommonPrefixScan [] legal = legal
dropCommonPrefixScan (cell ∷ prefix) (Whole.allCons firstLegal restLegal) =
  dropCommonPrefixScan prefix restLegal

decomposedRowLengthsAgree :
  ∀ {machine rule before after}
    (scan : Whole.GlobalTransitionScan machine rule before after) →
  Coordinate.listLength
    (Local.append
      (Center.beforePrefix
        (Center.centeredOccurrenceFromGlobalScan scan))
      (Local.oldLeft
        (Center.window
          (Center.centeredOccurrenceFromGlobalScan scan))
        ∷ Local.oldCenter
          (Center.window
            (Center.centeredOccurrenceFromGlobalScan scan))
        ∷ Local.oldRight
          (Center.window
            (Center.centeredOccurrenceFromGlobalScan scan))
        ∷ Center.beforeSuffix
          (Center.centeredOccurrenceFromGlobalScan scan)))
  ≡
  Coordinate.listLength
    (Local.append
      (Center.afterPrefix
        (Center.centeredOccurrenceFromGlobalScan scan))
      (Local.newLeft
        (Center.window
          (Center.centeredOccurrenceFromGlobalScan scan))
        ∷ Local.newCenter
          (Center.window
            (Center.centeredOccurrenceFromGlobalScan scan))
        ∷ Local.newRight
          (Center.window
            (Center.centeredOccurrenceFromGlobalScan scan))
        ∷ Center.afterSuffix
          (Center.centeredOccurrenceFromGlobalScan scan)))
decomposedRowLengthsAgree scan =
  trans
    (sym (cong Coordinate.listLength
      (Center.beforeDecomposition extracted)))
    (trans
      (Whole.sameRowLength scan)
      (cong Coordinate.listLength
        (Center.afterDecomposition extracted)))
  where
    extracted = Center.centeredOccurrenceFromGlobalScan scan

cancelCommonPrefixAndTriple :
  ∀ {A : Set}
    (prefix : List A)
    {oldLeft oldCenter oldRight newLeft newCenter newRight : A}
    {oldSuffix newSuffix : List A} →
  Coordinate.listLength
    (Local.append prefix
      (oldLeft ∷ oldCenter ∷ oldRight ∷ oldSuffix))
  ≡
  Coordinate.listLength
    (Local.append prefix
      (newLeft ∷ newCenter ∷ newRight ∷ newSuffix)) →
  Coordinate.listLength oldSuffix
  ≡ Coordinate.listLength newSuffix
cancelCommonPrefixAndTriple [] equality =
  NatP.suc-injective
    (NatP.suc-injective
      (NatP.suc-injective equality))
cancelCommonPrefixAndTriple (_ ∷ prefix) equality =
  cancelCommonPrefixAndTriple prefix
    (NatP.suc-injective equality)

suffixLengthsAgree :
  ∀ {machine rule before after}
    (scan : Whole.GlobalTransitionScan machine rule before after) →
  (prefixEquality :
    Center.beforePrefix
      (Center.centeredOccurrenceFromGlobalScan scan)
    ≡ Center.afterPrefix
      (Center.centeredOccurrenceFromGlobalScan scan)) →
  Coordinate.listLength
    (Center.beforeSuffix
      (Center.centeredOccurrenceFromGlobalScan scan))
  ≡ Coordinate.listLength
      (Center.afterSuffix
        (Center.centeredOccurrenceFromGlobalScan scan))
suffixLengthsAgree scan refl =
  cancelCommonPrefixAndTriple
    (Center.beforePrefix extracted)
    (decomposedRowLengthsAgree scan)
  where
    extracted = Center.centeredOccurrenceFromGlobalScan scan

suffixesEqualFromLegalTail :
  ∀ {machine rule oldPrevious oldPreviousTwo newPrevious newPreviousTwo}
    (oldSuffix newSuffix :
      List (Local.TapeCell
        (Local.State machine)
        (Local.Symbol machine))) →
  WF.PlainCells oldSuffix →
  WF.PlainCells newSuffix →
  Coordinate.listLength oldSuffix
    ≡ Coordinate.listLength newSuffix →
  Whole.All
    (Pattern.LegalWindowForRule machine rule)
    (Whole.scanWindowsCells machine
      (oldPrevious ∷ oldPreviousTwo ∷ oldSuffix)
      (newPrevious ∷ newPreviousTwo ∷ newSuffix)) →
  oldSuffix ≡ newSuffix

suffixesEqualFromLegalTail
    [] [] WF.plainNil WF.plainNil lengthEqual legal =
  refl

suffixesEqualFromLegalTail
    []
    (Local.plain symbol ∷ newSuffix)
    WF.plainNil
    (WF.plainCons newPlain)
    ()

suffixesEqualFromLegalTail
    (Local.plain symbol ∷ oldSuffix)
    []
    (WF.plainCons oldPlain)
    WF.plainNil
    ()

suffixesEqualFromLegalTail
    (Local.plain oldSymbol ∷ oldSuffix)
    (Local.plain newSymbol ∷ newSuffix)
    (WF.plainCons oldPlain)
    (WF.plainCons newPlain)
    lengthEqual
    (Whole.allCons firstLegal restLegal)
    with Pattern.legalPlainRightSymbolAgreement firstLegal
       | suffixesEqualFromLegalTail
           oldSuffix newSuffix
           oldPlain newPlain
           (NatP.suc-injective lengthEqual)
           restLegal
... | refl | refl = refl

suffixAgreementFromGlobalLegality :
  ∀ {machine rule before after}
    (scan : Whole.GlobalTransitionScan machine rule before after) →
  WF.ExactlyOneHead (Local.cells before) →
  WF.ExactlyOneHead (Local.cells after) →
  (prefixEquality :
    Center.beforePrefix
      (Center.centeredOccurrenceFromGlobalScan scan)
    ≡ Center.afterPrefix
      (Center.centeredOccurrenceFromGlobalScan scan)) →
  Center.beforeSuffix
    (Center.centeredOccurrenceFromGlobalScan scan)
  ≡ Center.afterSuffix
      (Center.centeredOccurrenceFromGlobalScan scan)
suffixAgreementFromGlobalLegality scan beforeUnique afterUnique prefixEquality
    with Reconstruct.beforeExtractedContextIsPlain scan beforeUnique
       | afterExtractedSuffixIsPlain scan afterUnique
       | dropCommonPrefixScan
           (Center.beforePrefix extracted)
           (transportAllToCommonPrefix scan prefixEquality)
... | beforePrefixPlain , beforeSuffixPlain
    | afterSuffixPlain
    | Whole.allCons centeredLegal tailLegal =
  suffixesEqualFromLegalTail
    (Center.beforeSuffix extracted)
    (Center.afterSuffix extracted)
    beforeSuffixPlain
    afterSuffixPlain
    (suffixLengthsAgree scan prefixEquality)
    tailLegal
  where
    extracted = Center.centeredOccurrenceFromGlobalScan scan

outsideAgreementFromGlobalLegality :
  ∀ {machine rule before after}
    (scan : Whole.GlobalTransitionScan machine rule before after) →
  WF.ExactlyOneHead (Local.cells before) →
  WF.ExactlyOneHead (Local.cells after) →
  Reconstruct.CenteredOutsideAgreement scan
outsideAgreementFromGlobalLegality scan beforeUnique afterUnique =
  record
    { Reconstruct.prefixAgreement = prefixEquality
    ; Reconstruct.suffixAgreement =
        suffixAgreementFromGlobalLegality
          scan beforeUnique afterUnique prefixEquality
    }
  where
    prefixEquality =
      Prefix.prefixAgreementFromGlobalLegality
        scan beforeUnique afterUnique

globalTransitionScanToWellFormedStep :
  ∀ {machine rule before after} →
  (scan : Whole.GlobalTransitionScan machine rule before after) →
  WF.ExactlyOneHead (Local.cells before) →
  WF.ExactlyOneHead (Local.cells after) →
  WF.WellFormedMachineStep machine before after
globalTransitionScanToWellFormedStep scan beforeUnique afterUnique =
  Reconstruct.globalScanWithCommonOutsideGivesWellFormedStep
    scan beforeUnique
    (outsideAgreementFromGlobalLegality
      scan beforeUnique afterUnique)

record ConcreteTapeGlobalSuffixAgreementBoundary : Set where
  constructor concrete-tape-global-suffix-agreement-boundary
  field
    bothExtractedSuffixesPlainPaid : Bool
    equalRowWidthGivesEqualSuffixLengthPaid : Bool
    plainRightCellGrammarAgreementPaid : Bool
    recursiveSuffixAgreementPaid : Bool
    globalLegalityForcesSuffixAgreementPaid : Bool
    globalLegalityForcesOutsideAgreementPaid : Bool
    globalTransitionScanToWellFormedStepPaid : Bool
    legalWindowBooleanReflectionPaid : Bool
    canonicalSATWeldPaid : Bool
    runToSATPaid : Bool
    satToRunPaid : Bool
    genericCookLevinPaid : Bool
    pVsNPResolved : Bool

canonicalConcreteTapeGlobalSuffixAgreementBoundary :
  ConcreteTapeGlobalSuffixAgreementBoundary
canonicalConcreteTapeGlobalSuffixAgreementBoundary =
  concrete-tape-global-suffix-agreement-boundary
    true true true true true true true false false false false false false
