module DASHI.Mathematics.Complexity.ConcreteTapeGlobalPrefixAgreementExact where

------------------------------------------------------------------------
-- GLOBAL LEGALITY FORCES THE PRE-TRANSITION PREFIX TO BE IDENTICAL
--
-- The centered-window extractor gives aligned before/after prefixes with equal
-- length.  Unique-head well-formedness makes both prefixes plain.  For a legal
-- local pattern whose left cells are both plain, the exact directional grammar
-- proves those symbols equal.  Recursing down the scan therefore forces the
-- whole prefixes equal.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeLocalWindowPatternsExact as Pattern
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeWholeRowLocalityExact as Whole
import DASHI.Mathematics.Complexity.ConcreteTapeCenteredWindowExtractionExact as Center
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalRewriteReconstructionExact as Reconstruct
import DASHI.Mathematics.Complexity.ConcreteTapeOccurrenceCoordinateExact as Coordinate

plainPrefixBeforeHead :
  ∀ {State Symbol : Set}
    (prefix : List (Local.TapeCell State Symbol))
    {state symbol}
    (suffix : List (Local.TapeCell State Symbol)) →
  WF.ExactlyOneHead
    (Local.append prefix
      (Local.headed state symbol ∷ suffix)) →
  WF.PlainCells prefix
plainPrefixBeforeHead [] suffix (WF.headHere restPlain) =
  WF.plainNil
plainPrefixBeforeHead
    (Local.plain prefixSymbol ∷ prefix)
    suffix
    (WF.plainBefore uniqueTail) =
  WF.plainCons
    (plainPrefixBeforeHead prefix suffix uniqueTail)
plainPrefixBeforeHead
    (Local.headed prefixState prefixSymbol ∷ prefix)
    suffix
    (WF.headHere restPlain) =
  Data.Empty.⊥-elim
    (Reconstruct.plainCellsCannotContainLaterHead
      prefix suffix restPlain)
  where
    open import Data.Empty using ()

plainPrefixFromAppend :
  ∀ {State Symbol : Set}
    (prefix tail : List (Local.TapeCell State Symbol)) →
  WF.PlainCells (Local.append prefix tail) →
  WF.PlainCells prefix
plainPrefixFromAppend [] tail allPlain =
  WF.plainNil
plainPrefixFromAppend
    (Local.plain symbol ∷ prefix)
    tail
    (WF.plainCons restPlain) =
  WF.plainCons
    (plainPrefixFromAppend prefix tail restPlain)
plainPrefixFromAppend
    (Local.headed state symbol ∷ prefix)
    tail
    ()

transportUnique :
  ∀ {State Symbol : Set}
    {left right : List (Local.TapeCell State Symbol)} →
  left ≡ right →
  WF.ExactlyOneHead left →
  WF.ExactlyOneHead right
transportUnique refl unique = unique

afterExtractedPrefixIsPlain :
  ∀ {machine rule before after}
    (scan : Whole.GlobalTransitionScan machine rule before after) →
  WF.ExactlyOneHead (Local.cells after) →
  WF.PlainCells
    (Center.afterPrefix
      (Center.centeredOccurrenceFromGlobalScan scan))
afterExtractedPrefixIsPlain scan afterUnique
    with Center.configured extracted
... | Local.realizes-left =
  plainPrefixBeforeHead
    (Center.afterPrefix extracted)
    (Local.plain _
      ∷ Local.plain _
      ∷ Center.afterSuffix extracted)
    (transportUnique
      (Center.afterDecomposition extracted)
      afterUnique)
  where
    extracted = Center.centeredOccurrenceFromGlobalScan scan
... | Local.realizes-stay =
  Data.Product.proj₁
    (Reconstruct.plainContextsAroundCenteredHead
      (Center.afterPrefix extracted)
      (Center.afterSuffix extracted)
      (transportUnique
        (Center.afterDecomposition extracted)
        afterUnique))
  where
    open import Data.Product using ()
    extracted = Center.centeredOccurrenceFromGlobalScan scan
... | Local.realizes-right =
  plainPrefixFromAppend
    (Center.afterPrefix extracted)
    (Local.plain _ ∷ Local.plain _ ∷ [])
    (plainPrefixBeforeHead
      (Local.append
        (Center.afterPrefix extracted)
        (Local.plain _ ∷ Local.plain _ ∷ []))
      (Center.afterSuffix extracted)
      (transportUnique
        (Center.afterDecomposition extracted)
        afterUnique))
  where
    extracted = Center.centeredOccurrenceFromGlobalScan scan

transportAllToDecomposedRows :
  ∀ {machine rule before after beforeCells afterCells} →
  Local.cells before ≡ beforeCells →
  Local.cells after ≡ afterCells →
  Whole.AllWindowsLegal machine rule before after →
  Whole.All
    (Pattern.LegalWindowForRule machine rule)
    (Whole.scanWindowsCells machine beforeCells afterCells)
transportAllToDecomposedRows refl refl legal = legal

plainPrefixesEqualFromLegalScan :
  ∀ {machine rule oldLeft oldCenter oldRight newLeft newCenter newRight
      oldSuffix newSuffix}
    (beforePrefix afterPrefix :
      List (Local.TapeCell
        (Local.State machine)
        (Local.Symbol machine))) →
  WF.PlainCells beforePrefix →
  WF.PlainCells afterPrefix →
  Coordinate.listLength beforePrefix
    ≡ Coordinate.listLength afterPrefix →
  Whole.All
    (Pattern.LegalWindowForRule machine rule)
    (Whole.scanWindowsCells machine
      (Local.append beforePrefix
        (oldLeft ∷ oldCenter ∷ oldRight ∷ oldSuffix))
      (Local.append afterPrefix
        (newLeft ∷ newCenter ∷ newRight ∷ newSuffix))) →
  beforePrefix ≡ afterPrefix

plainPrefixesEqualFromLegalScan
    [] [] WF.plainNil WF.plainNil lengthEqual legal =
  refl

plainPrefixesEqualFromLegalScan
    []
    (Local.plain symbol ∷ afterPrefix)
    WF.plainNil
    (WF.plainCons afterPlain)
    ()

plainPrefixesEqualFromLegalScan
    (Local.plain symbol ∷ beforePrefix)
    []
    (WF.plainCons beforePlain)
    WF.plainNil
    ()

plainPrefixesEqualFromLegalScan
    (Local.plain beforeSymbol ∷ beforePrefix)
    (Local.plain afterSymbol ∷ afterPrefix)
    (WF.plainCons beforePlain)
    (WF.plainCons afterPlain)
    lengthEqual
    (Whole.allCons firstLegal restLegal)
    with Pattern.legalPlainLeftSymbolAgreement firstLegal
       | plainPrefixesEqualFromLegalScan
           beforePrefix afterPrefix
           beforePlain afterPlain
           (NatP.suc-injective lengthEqual)
           restLegal
... | refl | refl = refl

prefixAgreementFromGlobalLegality :
  ∀ {machine rule before after}
    (scan : Whole.GlobalTransitionScan machine rule before after) →
  WF.ExactlyOneHead (Local.cells before) →
  WF.ExactlyOneHead (Local.cells after) →
  Center.beforePrefix
    (Center.centeredOccurrenceFromGlobalScan scan)
  ≡ Center.afterPrefix
    (Center.centeredOccurrenceFromGlobalScan scan)
prefixAgreementFromGlobalLegality scan beforeUnique afterUnique
    with Reconstruct.beforeExtractedContextIsPlain scan beforeUnique
       | afterExtractedPrefixIsPlain scan afterUnique
... | beforePrefixPlain , beforeSuffixPlain
    | afterPrefixPlain =
  plainPrefixesEqualFromLegalScan
    (Center.beforePrefix extracted)
    (Center.afterPrefix extracted)
    beforePrefixPlain
    afterPrefixPlain
    (Center.alignedPrefixLength extracted)
    (transportAllToDecomposedRows
      (Center.beforeDecomposition extracted)
      (Center.afterDecomposition extracted)
      (Whole.everyWindowLegal scan))
  where
    open import Data.Product using (_,_)
    extracted = Center.centeredOccurrenceFromGlobalScan scan

record ConcreteTapeGlobalPrefixAgreementBoundary : Set where
  constructor concrete-tape-global-prefix-agreement-boundary
  field
    bothExtractedPrefixesPlainPaid : Bool
    plainLeftCellGrammarAgreementPaid : Bool
    recursivePrefixAgreementPaid : Bool
    globalLegalityForcesPrefixAgreementPaid : Bool
    globalLegalityForcesSuffixAgreementPaid : Bool
    globalLegalityForcesOutsideAgreementPaid : Bool
    globalTransitionScanToUniqueRewritePaid : Bool
    canonicalSATWeldPaid : Bool
    genericCookLevinPaid : Bool
    pVsNPResolved : Bool

canonicalConcreteTapeGlobalPrefixAgreementBoundary :
  ConcreteTapeGlobalPrefixAgreementBoundary
canonicalConcreteTapeGlobalPrefixAgreementBoundary =
  concrete-tape-global-prefix-agreement-boundary
    true true true true false false false false false false
