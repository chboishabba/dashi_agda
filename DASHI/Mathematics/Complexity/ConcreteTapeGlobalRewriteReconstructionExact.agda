module DASHI.Mathematics.Complexity.ConcreteTapeGlobalRewriteReconstructionExact where

------------------------------------------------------------------------
-- GLOBAL SCAN RECONSTRUCTION, FINAL NONTRIVIAL CUT
--
-- The recursive scanner already extracts an aligned centered rule window.
-- This module proves:
--
--   (1) exactly-one-head on the before row forces the extracted context around
--       that centered rule window to consist entirely of plain tape cells;
--
--   (2) if the aligned before/after prefixes and suffixes agree, the scan
--       reconstructs an actual WellFormedMachineStep, including membership of
--       the rule in the machine transition table.
--
-- Therefore the remaining reverse Cook--Levin locality theorem is exactly:
--
--   every legal overlapping window
--     -> extracted beforePrefix = afterPrefix
--     -> extracted beforeSuffix = afterSuffix.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeWholeRowLocalityExact as Whole
import DASHI.Mathematics.Complexity.ConcreteTapeCenteredWindowExtractionExact as Center

plainCellsCannotContainLaterHead :
  ∀ {State Symbol : Set}
    (prefix : List (Local.TapeCell State Symbol))
    {state : State} {symbol : Symbol}
    (suffix : List (Local.TapeCell State Symbol)) →
  WF.PlainCells
    (Local.append prefix
      (Local.headed state symbol ∷ suffix)) →
  ⊥
plainCellsCannotContainLaterHead [] suffix ()
plainCellsCannotContainLaterHead
    (Local.plain prefixSymbol ∷ prefix)
    suffix
    (WF.plainCons restPlain) =
  plainCellsCannotContainLaterHead prefix suffix restPlain
plainCellsCannotContainLaterHead
    (Local.headed prefixState prefixSymbol ∷ prefix)
    suffix
    ()

plainCellsCannotContainCenteredHead :
  ∀ {State Symbol : Set}
    (prefix : List (Local.TapeCell State Symbol))
    {leftSymbol readSymbol rightSymbol : Symbol}
    {q : State}
    (suffix : List (Local.TapeCell State Symbol)) →
  WF.PlainCells
    (Local.append prefix
      (Local.plain leftSymbol
        ∷ Local.headed q readSymbol
        ∷ Local.plain rightSymbol
        ∷ suffix)) →
  ⊥
plainCellsCannotContainCenteredHead [] suffix (WF.plainCons ())
plainCellsCannotContainCenteredHead
    (Local.plain prefixSymbol ∷ prefix)
    suffix
    (WF.plainCons plain) =
  plainCellsCannotContainCenteredHead prefix suffix plain
plainCellsCannotContainCenteredHead
    (Local.headed prefixState prefixSymbol ∷ prefix)
    suffix
    ()

plainContextsAroundCenteredHead :
  ∀ {State Symbol : Set}
    (prefix : List (Local.TapeCell State Symbol))
    {leftSymbol state readSymbol rightSymbol}
    (suffix : List (Local.TapeCell State Symbol)) →
  WF.ExactlyOneHead
    (Local.append prefix
      (Local.plain leftSymbol
        ∷ Local.headed state readSymbol
        ∷ Local.plain rightSymbol
        ∷ suffix)) →
  WF.PlainCells prefix × WF.PlainCells suffix

plainContextsAroundCenteredHead
    []
    suffix
    (WF.plainBefore
      (WF.headHere
        (WF.plainCons suffixPlain))) =
  WF.plainNil , suffixPlain

plainContextsAroundCenteredHead
    (Local.plain prefixSymbol ∷ prefix)
    suffix
    (WF.plainBefore uniqueTail)
    with plainContextsAroundCenteredHead prefix suffix uniqueTail
... | prefixPlain , suffixPlain =
  WF.plainCons prefixPlain , suffixPlain

plainContextsAroundCenteredHead
    (Local.headed prefixState prefixSymbol ∷ prefix)
    suffix
    (WF.headHere restPlain) =
  ⊥-elim (plainCellsCannotContainCenteredHead prefix suffix restPlain)

record CenteredOutsideAgreement
    {machine : Local.ConcreteTapeMachine}
    {rule : Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine)}
    {before after : Local.TapeRow machine}
    (scan : Whole.GlobalTransitionScan machine rule before after) : Set where
  private
    extracted = Center.centeredOccurrenceFromGlobalScan scan

  field
    prefixAgreement :
      Center.beforePrefix extracted
      ≡ Center.afterPrefix extracted

    suffixAgreement :
      Center.beforeSuffix extracted
      ≡ Center.afterSuffix extracted

open CenteredOutsideAgreement public

transportUnique :
  ∀ {State Symbol : Set}
    {left right : List (Local.TapeCell State Symbol)} →
  left ≡ right →
  WF.ExactlyOneHead left →
  WF.ExactlyOneHead right
transportUnique refl unique = unique

beforeExtractedContextIsPlain :
  ∀ {machine rule before after}
    (scan : Whole.GlobalTransitionScan machine rule before after) →
  WF.ExactlyOneHead (Local.cells before) →
  WF.PlainCells
      (Center.beforePrefix
        (Center.centeredOccurrenceFromGlobalScan scan))
  ×
  WF.PlainCells
      (Center.beforeSuffix
        (Center.centeredOccurrenceFromGlobalScan scan))
beforeExtractedContextIsPlain scan beforeUnique =
  go (Center.beforePrefix extracted)
     (Center.beforeSuffix extracted)
     (Center.configured extracted)
     (transportUnique
       (Center.beforeDecomposition extracted)
       beforeUnique)
  where
    extracted = Center.centeredOccurrenceFromGlobalScan scan

    go :
      ∀ prefix suffix {rule window} →
      Local.RuleRealizesWindow _ rule window →
      WF.ExactlyOneHead
        (Local.append prefix
          (Local.oldLeft window
            ∷ Local.oldCenter window
            ∷ Local.oldRight window
            ∷ suffix)) →
      WF.PlainCells prefix × WF.PlainCells suffix
    go prefix suffix Local.realizes-left unique =
      plainContextsAroundCenteredHead prefix suffix unique
    go prefix suffix Local.realizes-stay unique =
      plainContextsAroundCenteredHead prefix suffix unique
    go prefix suffix Local.realizes-right unique =
      plainContextsAroundCenteredHead prefix suffix unique

transportAfterDecomposition :
  ∀ {machine rule before after}
    (scan : Whole.GlobalTransitionScan machine rule before after) →
  (agreement : CenteredOutsideAgreement scan) →
  Local.cells after
  ≡ Local.append
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
        ∷ Center.beforeSuffix
          (Center.centeredOccurrenceFromGlobalScan scan))
transportAfterDecomposition scan agreement
    rewrite prefixAgreement agreement
          | suffixAgreement agreement =
  Center.afterDecomposition
    (Center.centeredOccurrenceFromGlobalScan scan)

globalScanWithCommonOutsideGivesWellFormedStep :
  ∀ {machine rule before after}
    (scan : Whole.GlobalTransitionScan machine rule before after) →
  WF.ExactlyOneHead (Local.cells before) →
  CenteredOutsideAgreement scan →
  WF.WellFormedMachineStep machine before after
globalScanWithCommonOutsideGivesWellFormedStep
    {machine} {rule} {before} {after}
    scan beforeUnique agreement
    with beforeExtractedContextIsPlain scan beforeUnique
... | prefixPlain , suffixPlain =
  record
    { step =
        record
          { rule = rule
          ; ruleOccursInMachine =
              Whole.ruleOccursInMachine scan
          ; window =
              Center.window extracted
          ; ruleIsConfigured =
              Center.configured extracted
          ; occurrence =
              record
                { prefix =
                    Center.beforePrefix extracted
                ; suffix =
                    Center.beforeSuffix extracted
                ; beforeShape =
                    Center.beforeDecomposition extracted
                ; afterShape =
                    transportAfterDecomposition scan agreement
                }
          }
    ; wellFormedOccurrence =
        record
          { occurrence =
              record
                { prefix =
                    Center.beforePrefix extracted
                ; suffix =
                    Center.beforeSuffix extracted
                ; beforeShape =
                    Center.beforeDecomposition extracted
                ; afterShape =
                    transportAfterDecomposition scan agreement
                }
          ; prefixPlain = prefixPlain
          ; suffixPlain = suffixPlain
          }
    }
  where
    extracted = Center.centeredOccurrenceFromGlobalScan scan

record ConcreteTapeGlobalRewriteReconstructionBoundary : Set where
  constructor concrete-tape-global-rewrite-reconstruction-boundary
  field
    uniqueHeadForcesPlainCenteredContextPaid : Bool
    commonOutsideContextToWellFormedStepPaid : Bool
    transitionTableMembershipPreservedPaid : Bool
    globalLegalityForcesPrefixAgreementPaid : Bool
    globalLegalityForcesSuffixAgreementPaid : Bool
    globalLegalityForcesOutsideAgreementPaid : Bool
    globalTransitionScanToUniqueRewritePaid : Bool
    legalWindowBooleanReflectionPaid : Bool
    canonicalSATWeldPaid : Bool
    genericCookLevinPaid : Bool
    pVsNPResolved : Bool

canonicalConcreteTapeGlobalRewriteReconstructionBoundary :
  ConcreteTapeGlobalRewriteReconstructionBoundary
canonicalConcreteTapeGlobalRewriteReconstructionBoundary =
  concrete-tape-global-rewrite-reconstruction-boundary
    true true true false false false false false false false false
