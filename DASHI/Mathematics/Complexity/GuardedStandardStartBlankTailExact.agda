module DASHI.Mathematics.Complexity.GuardedStandardStartBlankTailExact where

------------------------------------------------------------------------
-- CANONICAL INPUT <-> FINITELY GUARDED COOK INPUT ON THE SAME INFINITE TAPE
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeLocalityCharacterizationExact as Character
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.ConcreteTapeInputPaddingExact as Padding
import DASHI.Mathematics.Complexity.ConcreteTapeTimeBudgetPaddingExact as Guard
import DASHI.Mathematics.Complexity.ConcreteTapeStandardCanonicalProjectionExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeStandardLanguageEquivalenceExact as Language
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.StandardBlankTailBisimulationExact as BlankTail
import DASHI.Mathematics.Complexity.CodedStandardCanonicalInputExact as CanonicalInput

------------------------------------------------------------------------
-- 1. Canonical projection of an interior witness.
------------------------------------------------------------------------

interiorInnerUnique :
  ∀ {machine row}
    (interior : Character.InteriorHeadConfiguration machine row) →
  WF.ExactlyOneHead
    (Local.plain (Character.leftSymbol interior)
      ∷ Local.headed
          (Character.headState interior)
          (Character.readSymbol interior)
      ∷ Local.plain (Character.rightSymbol interior)
      ∷ Character.suffix interior)
interiorInnerUnique interior =
  WF.plainBefore
    (WF.headHere
      (WF.plainCons (Character.suffixPlain interior)))

interiorSyntheticUnique :
  ∀ {machine row}
    (interior : Character.InteriorHeadConfiguration machine row) →
  WF.ExactlyOneHead
    (Local.append
      (Character.prefix interior)
      (Local.plain (Character.leftSymbol interior)
        ∷ Local.headed
            (Character.headState interior)
            (Character.readSymbol interior)
        ∷ Local.plain (Character.rightSymbol interior)
        ∷ Character.suffix interior))
interiorSyntheticUnique interior =
  WF.prependPlain
    (Character.prefixPlain interior)
    (interiorInnerUnique interior)

canonicalProjectionOfInterior :
  ∀ {machine row}
    (interior : Character.InteriorHeadConfiguration machine row) →
  Canonical.canonicalProjection (Character.interiorHeadIsUnique interior)
  ≡
  Canonical.foldPlainPrefixFarLeft
    (Character.prefixPlain interior)
    (Canonical.appendSymbolFarLeft
      (Character.leftSymbol interior)
      (Standard.standard-configuration
        []
        (Character.headState interior)
        (Character.readSymbol interior)
        (Character.rightSymbol interior
          ∷ Canonical.plainCellsToSymbols
              (Character.suffixPlain interior))))
canonicalProjectionOfInterior interior =
  trans
    (Canonical.canonicalProjection_transport
      (Character.rowShape interior)
      (Character.interiorHeadIsUnique interior)
      (interiorSyntheticUnique interior))
    (Canonical.projectPlainPrefix
      (Character.prefixPlain interior)
      (interiorInnerUnique interior))

------------------------------------------------------------------------
-- 2. Blank-tail algebra.
------------------------------------------------------------------------

configBlankTailEqTrans :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {left middle right : Standard.StandardConfiguration machine} →
  BlankTail.ConfigurationBlankTailEq left middle →
  BlankTail.ConfigurationBlankTailEq middle right →
  BlankTail.ConfigurationBlankTailEq left right
configBlankTailEqTrans first second = record
  { BlankTail.stateEq =
      trans (BlankTail.stateEq first) (BlankTail.stateEq second)
  ; BlankTail.scannedEq =
      trans (BlankTail.scannedEq first) (BlankTail.scannedEq second)
  ; BlankTail.leftEq = λ n →
      trans (BlankTail.leftEq first n) (BlankTail.leftEq second n)
  ; BlankTail.rightEq = λ n →
      trans (BlankTail.rightEq first n) (BlankTail.rightEq second n)
  }

listAtEmpty :
  ∀ {Symbol : Set}
    (blank : Symbol)
    (n : Nat) →
  BlankTail.listAtBlankDefault blank n [] ≡ blank
listAtEmpty blank zero = refl
listAtEmpty blank (suc n) = refl

appendFarBlankEq :
  ∀ {Symbol : Set}
    (blank : Symbol)
    (xs : List Symbol) →
  BlankTail.ListBlankTailEq
    blank
    xs
    (Local.append xs (blank ∷ []))
appendFarBlankEq blank [] zero = refl
appendFarBlankEq blank [] (suc n)
  rewrite listAtEmpty blank n = refl
appendFarBlankEq blank (x ∷ xs) zero = refl
appendFarBlankEq blank (x ∷ xs) (suc n) =
  appendFarBlankEq blank xs n

appendFarBlankConfigEq :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    (configuration : Standard.StandardConfiguration machine) →
  BlankTail.ConfigurationBlankTailEq
    configuration
    (Canonical.appendSymbolFarLeft
      (Standard.blank machine)
      configuration)
appendFarBlankConfigEq {machine = machine} configuration = record
  { BlankTail.stateEq = refl
  ; BlankTail.scannedEq = refl
  ; BlankTail.leftEq =
      appendFarBlankEq
        (Standard.blank machine)
        (Standard.left configuration)
  ; BlankTail.rightEq =
      BlankTail.listBlankTailEqRefl
        (Standard.blank machine)
        (Standard.right configuration)
  }

foldBlankPrefixEq :
  ∀ {machine : Local.ConcreteTapeMachine}
    (steps : Nat)
    (configuration : Standard.StandardConfiguration
      (Standard.standardControlOfConcrete machine)) →
  BlankTail.ConfigurationBlankTailEq
    configuration
    (Canonical.foldPlainPrefixFarLeft
      (Padding.replicateBlankPlain steps)
      configuration)
foldBlankPrefixEq zero configuration =
  BlankTail.configurationBlankTailEqRefl configuration
foldBlankPrefixEq (suc steps) configuration =
  configBlankTailEqTrans
    (foldBlankPrefixEq steps configuration)
    (appendFarBlankConfigEq
      (Canonical.foldPlainPrefixFarLeft
        (Padding.replicateBlankPlain steps)
        configuration))

replicateSymbols :
  ∀ {Symbol : Set} →
  Symbol → Nat → List Symbol
replicateSymbols blank zero = []
replicateSymbols blank (suc n) =
  blank ∷ replicateSymbols blank n

appendAssoc :
  ∀ {A : Set}
    (xs ys zs : List A) →
  Local.append (Local.append xs ys) zs
  ≡ Local.append xs (Local.append ys zs)
appendAssoc [] ys zs = refl
appendAssoc (x ∷ xs) ys zs
  rewrite appendAssoc xs ys zs = refl

appendBlankTailEq :
  ∀ {Symbol : Set}
    (blank : Symbol)
    (xs : List Symbol)
    (n : Nat) →
  BlankTail.ListBlankTailEq
    blank
    xs
    (Local.append xs (replicateSymbols blank n))
appendBlankTailEq blank [] zero k = refl
appendBlankTailEq blank [] (suc n) zero = refl
appendBlankTailEq blank [] (suc n) (suc k) =
  appendBlankTailEq blank [] n k
appendBlankTailEq blank (x ∷ xs) n zero = refl
appendBlankTailEq blank (x ∷ xs) n (suc k) =
  appendBlankTailEq blank xs n k

plainAppendSymbols :
  ∀ {State Symbol : Set}
    {xs ys : List (Local.TapeCell State Symbol)}
    (left : WF.PlainCells xs)
    (right : WF.PlainCells ys) →
  Canonical.plainCellsToSymbols (Guard.plainAppend left right)
  ≡ Local.append
      (Canonical.plainCellsToSymbols left)
      (Canonical.plainCellsToSymbols right)
plainAppendSymbols WF.plainNil right = refl
plainAppendSymbols (WF.plainCons left) right
  rewrite plainAppendSymbols left right = refl

replicateBlankSymbols :
  ∀ {machine : Local.ConcreteTapeMachine}
    (steps : Nat) →
  Canonical.plainCellsToSymbols
    (Padding.replicateBlankPlain {machine} steps)
  ≡ replicateSymbols (Local.blank machine) steps
replicateBlankSymbols zero = refl
replicateBlankSymbols (suc steps)
  rewrite replicateBlankSymbols steps = refl

appendPlainBlankSymbols :
  ∀ {machine : Local.ConcreteTapeMachine}
    (symbols : List (Local.Symbol machine)) →
  Canonical.plainCellsToSymbols
    (Input.appendPlainBlankArePlain {machine} symbols)
  ≡ Local.append symbols (Local.blank machine ∷ [])
appendPlainBlankSymbols [] = refl
appendPlainBlankSymbols (symbol ∷ rest)
  rewrite appendPlainBlankSymbols rest = refl

------------------------------------------------------------------------
-- 3. The literal guarded start and canonical start denote the same infinite tape.
------------------------------------------------------------------------

guardedReadSymbol :
  ∀ {machine : Local.ConcreteTapeMachine}
    (input : Input.InputWord machine)
    (steps : Nat) →
  Character.readSymbol (Guard.guardedInitialInterior input steps)
  ≡ Input.inputHeadSymbol input
guardedReadSymbol [] steps = refl
guardedReadSymbol (symbol ∷ rest) steps = refl

guardedLeftSymbol :
  ∀ {machine : Local.ConcreteTapeMachine}
    (input : Input.InputWord machine)
    (steps : Nat) →
  Character.leftSymbol (Guard.guardedInitialInterior input steps)
  ≡ Local.blank machine
guardedLeftSymbol [] steps = refl
guardedLeftSymbol (symbol ∷ rest) steps = refl

guardedRightSymbolsShape :
  ∀ {machine : Local.ConcreteTapeMachine}
    (input : Input.InputWord machine)
    (steps : Nat) →
  Character.rightSymbol (Guard.guardedInitialInterior input steps)
    ∷ Canonical.plainCellsToSymbols
        (Character.suffixPlain (Guard.guardedInitialInterior input steps))
  ≡ Local.append
      (Input.inputTail input)
      (replicateSymbols (Local.blank machine) (suc steps))
guardedRightSymbolsShape {machine} [] steps
  rewrite plainAppendSymbols
            WF.plainNil
            (Padding.replicateBlankPlain steps)
        | replicateBlankSymbols {machine} steps =
  refl
guardedRightSymbolsShape {machine} (symbol ∷ []) steps
  rewrite plainAppendSymbols
            WF.plainNil
            (Padding.replicateBlankPlain steps)
        | replicateBlankSymbols {machine} steps =
  refl
guardedRightSymbolsShape {machine} (symbol ∷ next ∷ rest) steps
  rewrite plainAppendSymbols
            (Input.appendPlainBlankArePlain rest)
            (Padding.replicateBlankPlain steps)
        | appendPlainBlankSymbols {machine} rest
        | replicateBlankSymbols {machine} steps
        | appendAssoc
            rest
            (Local.blank machine ∷ [])
            (replicateSymbols (Local.blank machine) steps) =
  refl

canonicalStateInitial :
  ∀ {machine : Local.ConcreteTapeMachine}
    (input : Input.InputWord machine) →
  Standard.state (CanonicalInput.canonicalStandardStart input)
  ≡ Local.initialState machine
canonicalStateInitial [] = refl
canonicalStateInitial (symbol ∷ rest) = refl

canonicalScannedHead :
  ∀ {machine : Local.ConcreteTapeMachine}
    (input : Input.InputWord machine) →
  Standard.scanned (CanonicalInput.canonicalStandardStart input)
  ≡ Input.inputHeadSymbol input
canonicalScannedHead [] = refl
canonicalScannedHead (symbol ∷ rest) = refl

canonicalRightTail :
  ∀ {machine : Local.ConcreteTapeMachine}
    (input : Input.InputWord machine) →
  Standard.right (CanonicalInput.canonicalStandardStart input)
  ≡ Input.inputTail input
canonicalRightTail [] = refl
canonicalRightTail (symbol ∷ rest) = refl

innerGuardedConfig :
  ∀ {machine : Local.ConcreteTapeMachine} →
  Input.InputWord machine → Nat →
  Standard.StandardConfiguration (Standard.standardControlOfConcrete machine)
innerGuardedConfig input steps =
  Standard.standard-configuration
    []
    (Character.headState (Guard.guardedInitialInterior input steps))
    (Character.readSymbol (Guard.guardedInitialInterior input steps))
    (Character.rightSymbol (Guard.guardedInitialInterior input steps)
      ∷ Canonical.plainCellsToSymbols
          (Character.suffixPlain (Guard.guardedInitialInterior input steps)))

canonicalToInnerGuardedEq :
  ∀ {machine : Local.ConcreteTapeMachine}
    (input : Input.InputWord machine)
    (steps : Nat) →
  BlankTail.ConfigurationBlankTailEq
    (CanonicalInput.canonicalStandardStart input)
    (innerGuardedConfig input steps)
canonicalToInnerGuardedEq {machine} input steps = record
  { BlankTail.stateEq =
      trans
        (canonicalStateInitial input)
        (sym (Guard.guardedInitialState input steps))
  ; BlankTail.scannedEq =
      trans
        (canonicalScannedHead input)
        (sym (guardedReadSymbol input steps))
  ; BlankTail.leftEq =
      BlankTail.listBlankTailEqRefl (Local.blank machine) []
  ; BlankTail.rightEq = rightEq
  }
  where
    rightEq :
      BlankTail.ListBlankTailEq
        (Local.blank machine)
        (Standard.right (CanonicalInput.canonicalStandardStart input))
        (Standard.right (innerGuardedConfig input steps))
    rightEq n
      rewrite canonicalRightTail input
            | guardedRightSymbolsShape input steps =
      appendBlankTailEq
        (Local.blank machine)
        (Input.inputTail input)
        (suc steps)
        n

guardedStandardStartBlankTailEq :
  ∀ {machine : Local.ConcreteTapeMachine}
    (input : Input.InputWord machine)
    (steps : Nat) →
  BlankTail.ConfigurationBlankTailEq
    (CanonicalInput.canonicalStandardStart input)
    (Language.guardedStandardStart input steps)
guardedStandardStartBlankTailEq {machine} input steps
  rewrite canonicalProjectionOfInterior
    (Guard.guardedInitialInterior input steps)
        | guardedLeftSymbol input steps =
  configBlankTailEqTrans
    (canonicalToInnerGuardedEq input steps)
    (configBlankTailEqTrans
      (appendFarBlankConfigEq (innerGuardedConfig input steps))
      (foldBlankPrefixEq steps
        (Canonical.appendSymbolFarLeft
          (Local.blank machine)
          (innerGuardedConfig input steps))))

record GuardedStartBlankTailBoundary : Set where
  constructor guarded-start-blank-tail-boundary
  field
    canonicalInputIndependentOfCookPadding : Bool
    sameInfiniteTapeStartPaid : Bool
    paddingOnlyMaterialisesBlankTails : Bool
    paddingChoosesRuntime : Bool

canonicalGuardedStartBlankTailBoundary : GuardedStartBlankTailBoundary
canonicalGuardedStartBlankTailBoundary =
  guarded-start-blank-tail-boundary true true true false
