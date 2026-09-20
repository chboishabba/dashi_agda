module DASHI.Mathematics.Complexity.ConcreteTapeLocalityCharacterizationExact where

------------------------------------------------------------------------
-- BIDIRECTIONAL WHOLE-ROW LOCALITY CHARACTERIZATION
--
-- Boundary convention made explicit:
-- a transition row has one interior head, i.e. at least one tape cell on each
-- side of the head.  This is the standard padded-tableau convention needed by
-- a radius-one Cook--Levin encoding.
--
-- With unchanged windows restricted to plain cells, the window centered on
-- that unique head cannot be an unchanged/overlap case.  Global legality
-- therefore DERIVES a centered rule realization; it is not an extra SAT-side
-- premise.  The previous prefix/suffix reconstruction then yields an actual
-- well-formed machine step.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
import Data.Nat.Properties as NatP
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeLocalWindowPatternsExact as Pattern
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeWholeRowLocalityExact as Whole
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalSuffixAgreementExact as Reverse
import DASHI.Mathematics.Complexity.ConcreteTapeOccurrenceCoordinateExact as Coordinate
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalPrefixAgreementExact as Prefix

record InteriorHeadConfiguration
    (machine : Local.ConcreteTapeMachine)
    (row : Local.TapeRow machine) : Set where
  field
    prefix suffix :
      List (Local.TapeCell
        (Local.State machine)
        (Local.Symbol machine))

    leftSymbol readSymbol rightSymbol :
      Local.Symbol machine

    headState :
      Local.State machine

    prefixPlain :
      WF.PlainCells prefix

    suffixPlain :
      WF.PlainCells suffix

    rowShape :
      Local.cells row
      ≡ Local.append prefix
          (Local.plain leftSymbol
            ∷ Local.headed headState readSymbol
            ∷ Local.plain rightSymbol
            ∷ suffix)

open InteriorHeadConfiguration public

interiorHeadIsUnique :
  ∀ {machine row} →
  InteriorHeadConfiguration machine row →
  WF.ExactlyOneHead (Local.cells row)
interiorHeadIsUnique interior =
  Prefix.transportUnique
    (sym (rowShape interior))
    (WF.prependPlain
      (prefixPlain interior)
      (WF.plainBefore
        (WF.headHere
          (WF.plainCons (suffixPlain interior)))))

wellFormedStepBeforeInterior :
  ∀ {machine before after} →
  WF.WellFormedMachineStep machine before after →
  InteriorHeadConfiguration machine before
wellFormedStepBeforeInterior wellFormed
    with Local.ruleIsConfigured (WF.step wellFormed)
... | Local.realizes-left =
  build
... | Local.realizes-stay =
  build
... | Local.realizes-right =
  build
  where
    occurrenceWitness =
      WF.occurrence (WF.wellFormedOccurrence wellFormed)

    build : InteriorHeadConfiguration _ _
    build = record
      { prefix = Local.prefix occurrenceWitness
      ; suffix = Local.suffix occurrenceWitness
      ; leftSymbol = _
      ; readSymbol = _
      ; rightSymbol = _
      ; headState = _
      ; prefixPlain =
          WF.prefixPlain (WF.wellFormedOccurrence wellFormed)
      ; suffixPlain =
          WF.suffixPlain (WF.wellFormedOccurrence wellFormed)
      ; rowShape =
          Local.beforeShape occurrenceWitness
      }

record TransitionLocalityScan
    (machine : Local.ConcreteTapeMachine)
    (rule : Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine))
    (before after : Local.TapeRow machine) : Set where
  field
    ruleOccursInMachine :
      Local.RuleOccurs rule (Local.rules machine)

    sameRowLength :
      Coordinate.listLength (Local.cells before)
      ≡ Coordinate.listLength (Local.cells after)

    everyWindowLegal :
      Whole.AllWindowsLegal machine rule before after

open TransitionLocalityScan public

wellFormedStepGivesLocalityScan :
  ∀ {machine before after}
    (wellFormed : WF.WellFormedMachineStep machine before after) →
  TransitionLocalityScan
    machine
    (Local.rule (WF.step wellFormed))
    before after
wellFormedStepGivesLocalityScan wellFormed =
  record
    { ruleOccursInMachine =
        Local.ruleOccursInMachine (WF.step wellFormed)
    ; sameRowLength =
        Whole.rewriteOccurrencePreservesLength
          (WF.occurrence (WF.wellFormedOccurrence wellFormed))
    ; everyWindowLegal =
        Whole.machineStepImpliesAllWindowsLegal wellFormed
    }

findCenteredAtInteriorHead :
  ∀ {machine rule state leftSymbol readSymbol rightSymbol}
    (prefix suffix :
      List (Local.TapeCell
        (Local.State machine)
        (Local.Symbol machine)))
    (afterCells :
      List (Local.TapeCell
        (Local.State machine)
        (Local.Symbol machine))) →
  Coordinate.listLength
    (Local.append prefix
      (Local.plain leftSymbol
        ∷ Local.headed state readSymbol
        ∷ Local.plain rightSymbol
        ∷ suffix))
  ≡ Coordinate.listLength afterCells →
  Whole.All
    (Pattern.LegalWindowForRule machine rule)
    (Whole.scanWindowsCells machine
      (Local.append prefix
        (Local.plain leftSymbol
          ∷ Local.headed state readSymbol
          ∷ Local.plain rightSymbol
          ∷ suffix))
      afterCells) →
  Whole.ContainsCenteredRuleWindow machine rule
    (Whole.scanWindowsCells machine
      (Local.append prefix
        (Local.plain leftSymbol
          ∷ Local.headed state readSymbol
          ∷ Local.plain rightSymbol
          ∷ suffix))
      afterCells)

findCenteredAtInteriorHead
    [] suffix [] () legal

findCenteredAtInteriorHead
    [] suffix
    (afterFirst ∷ []) () legal

findCenteredAtInteriorHead
    [] suffix
    (afterFirst ∷ afterSecond ∷ []) () legal

findCenteredAtInteriorHead
    []
    suffix
    (afterLeft ∷ afterCenter ∷ afterRight ∷ afterRest)
    lengthEqual
    (Whole.allCons firstLegal restLegal)
    with firstLegal
... | Pattern.legal-centered configured =
  Whole.centeredHere configured

findCenteredAtInteriorHead
    (beforeHead ∷ prefix)
    suffix
    []
    ()
    legal

findCenteredAtInteriorHead
    (beforeHead ∷ prefix)
    suffix
    (afterHead ∷ afterTail)
    lengthEqual
    (Whole.allCons firstLegal restLegal) =
  Whole.centeredThere
    (findCenteredAtInteriorHead
      prefix suffix afterTail
      (NatP.suc-injective lengthEqual)
      restLegal)

transportLegalityToInteriorShape :
  ∀ {machine rule before after}
    (scan : TransitionLocalityScan machine rule before after)
    (interior : InteriorHeadConfiguration machine before) →
  Whole.All
    (Pattern.LegalWindowForRule machine rule)
    (Whole.scanWindowsCells machine
      (Local.append
        (prefix interior)
        (Local.plain (leftSymbol interior)
          ∷ Local.headed
              (headState interior)
              (readSymbol interior)
          ∷ Local.plain (rightSymbol interior)
          ∷ suffix interior))
      (Local.cells after))
transportLegalityToInteriorShape scan interior
    with rowShape interior
... | refl =
  everyWindowLegal scan

interiorShapeLengthMatchesAfter :
  ∀ {machine rule before after}
    (scan : TransitionLocalityScan machine rule before after)
    (interior : InteriorHeadConfiguration machine before) →
  Coordinate.listLength
    (Local.append
      (prefix interior)
      (Local.plain (leftSymbol interior)
        ∷ Local.headed
            (headState interior)
            (readSymbol interior)
        ∷ Local.plain (rightSymbol interior)
        ∷ suffix interior))
  ≡ Coordinate.listLength (Local.cells after)
interiorShapeLengthMatchesAfter scan interior =
  trans
    (sym (cong Coordinate.listLength (rowShape interior)))
    (sameRowLength scan)

localityScanDerivesCenteredTransition :
  ∀ {machine rule before after}
    (scan : TransitionLocalityScan machine rule before after) →
  (interior : InteriorHeadConfiguration machine before) →
  Whole.ContainsCenteredRuleWindow machine rule
    (Whole.scanWindows machine before after)
localityScanDerivesCenteredTransition scan interior
    with rowShape interior
... | refl =
  findCenteredAtInteriorHead
    (prefix interior)
    (suffix interior)
    (Local.cells _)
    (interiorShapeLengthMatchesAfter scan interior)
    (transportLegalityToInteriorShape scan interior)

localityScanToGlobalTransitionScan :
  ∀ {machine rule before after}
    (scan : TransitionLocalityScan machine rule before after) →
  InteriorHeadConfiguration machine before →
  Whole.GlobalTransitionScan machine rule before after
localityScanToGlobalTransitionScan scan interior = record
  { Whole.ruleOccursInMachine =
      ruleOccursInMachine scan
  ; Whole.sameRowLength =
      sameRowLength scan
  ; Whole.everyWindowLegal =
      everyWindowLegal scan
  ; Whole.centeredTransitionOccurs =
      localityScanDerivesCenteredTransition scan interior
  }

record LocalityCharacterization
    (machine : Local.ConcreteTapeMachine)
    (rule : Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine))
    (before after : Local.TapeRow machine) : Set where
  field
    beforeInterior :
      InteriorHeadConfiguration machine before

    afterUnique :
      WF.ExactlyOneHead (Local.cells after)

    localityScan :
      TransitionLocalityScan machine rule before after

open LocalityCharacterization public

wellFormedStepGivesLocalityCharacterization :
  ∀ {machine before after}
    (wellFormed : WF.WellFormedMachineStep machine before after) →
  LocalityCharacterization
    machine
    (Local.rule (WF.step wellFormed))
    before after
wellFormedStepGivesLocalityCharacterization wellFormed = record
  { beforeInterior =
      wellFormedStepBeforeInterior wellFormed
  ; afterUnique =
      WF.afterExactlyOneHead wellFormed
  ; localityScan =
      wellFormedStepGivesLocalityScan wellFormed
  }

localityCharacterizationGivesWellFormedStep :
  ∀ {machine rule before after} →
  LocalityCharacterization machine rule before after →
  WF.WellFormedMachineStep machine before after
localityCharacterizationGivesWellFormedStep characterization =
  Reverse.globalTransitionScanToWellFormedStep
    (localityScanToGlobalTransitionScan
      (localityScan characterization)
      (beforeInterior characterization))
    (interiorHeadIsUnique
      (beforeInterior characterization))
    (afterUnique characterization)

record ConcreteTapeLocalityCharacterizationBoundary : Set where
  constructor concrete-tape-locality-characterization-boundary
  field
    interiorHeadBoundaryConventionPaid : Bool
    unchangedHeadWindowExcludedPaid : Bool
    centeredTransitionDerivedFromLegalityPaid : Bool
    forwardWholeRowLocalityPaid : Bool
    reverseWholeRowLocalityPaid : Bool
    semanticWholeRowLocalityIffPaid : Bool
    booleanLocalRecognizerPaid : Bool
    canonicalSATWeldPaid : Bool
    runToSATPaid : Bool
    satToRunPaid : Bool
    genericCookLevinPaid : Bool
    pVsNPResolved : Bool

canonicalConcreteTapeLocalityCharacterizationBoundary :
  ConcreteTapeLocalityCharacterizationBoundary
canonicalConcreteTapeLocalityCharacterizationBoundary =
  concrete-tape-locality-characterization-boundary
    true true true true true true false false false false false false
