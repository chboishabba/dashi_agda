module DASHI.Reasoning.Trialectic369OutgoingSheet9ActionRestrictionCompilerExact where

------------------------------------------------------------------------
-- OUTGOING SHEET9 ACTION-RESTRICTION COMPILER
--
-- DASHI CONTRIBUTION
--
-- The canonical mixed-radix compiler already transports any actual Fin90
-- multiplicity action to:
--
--   Fine10 x SecondarySheet9.
--
-- To restrict that action to the outgoing trialectic Sheet9, the only genuinely
-- new datum required is preservation of ONE Fine10 fibre:
--
--   {selectedFine} x SecondarySheet9.
--
-- Once this is supplied, the induced Codec.Sheet9 action is forced by
-- projection and the full OutgoingSheet9ActualActionRestriction record is
-- compiler output.
--
-- Therefore the scientific wall is reduced from
--
--   "construct a Sheet9 action and prove intertwining"
--
-- to
--
--   "recognize an invariant Fine10 fibre for the actual multiplicity action".
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Codec.TriadicPAdicCodec as Codec
import DASHI.Foundations.Base369PointedAppraisalFibreExact as Pointed
import DASHI.Moonshine.Base369Monster3BActualActionRecognitionBidiExact as Action
import DASHI.Moonshine.Base369Monster3BMultiplicityInertiaTwelveSeventyEightBidiExact as Actual
import DASHI.Moonshine.Base369Monster3BMultiplicityTenByNineBidiExact as Ninety
import DASHI.Moonshine.Base369Monster3BMultiplicityCompletedTenTritSquareCompilerExact as Compiler
import DASHI.Reasoning.Trialectic369OutgoingSheet9MultiplicityRecognitionExact as Outgoing

------------------------------------------------------------------------
-- 1. The only non-compiler datum: one invariant Fine10 fibre.
------------------------------------------------------------------------

record SelectedFineFibreInvariant
    {source : Action.ActualMonster3BActionRecognition}
    (inertiaAttachment :
      Actual.ActualMultiplicityInertiaAttachment source)
    : Set₁ where
  field
    selectedFine :
      Pointed.Fine10

    selectedFinePreserved :
      (inertia : Actual.MultiplicityInertia inertiaAttachment) ->
      (sheet : Codec.Sheet9) ->
      proj₁
        (Compiler.compiledTenByNineAct
          inertiaAttachment
          inertia
          (Outgoing.embedSecondaryAt selectedFine sheet))
      ≡ selectedFine

open SelectedFineFibreInvariant public

------------------------------------------------------------------------
-- 2. The induced Sheet9 action is forced by projection.
------------------------------------------------------------------------

compiledSheetAct :
  ∀ {source}
    {inertiaAttachment :
      Actual.ActualMultiplicityInertiaAttachment source} ->
  SelectedFineFibreInvariant inertiaAttachment ->
  Actual.MultiplicityInertia inertiaAttachment ->
  Codec.Sheet9 ->
  Codec.Sheet9
compiledSheetAct invariant inertia sheet =
  Outgoing.projectSecondary
    (Compiler.compiledTenByNineAct
      _
      inertia
      (Outgoing.embedSecondaryAt
        (selectedFine invariant)
        sheet))

compiledSheetActionIsProjection :
  ∀ {source}
    {inertiaAttachment :
      Actual.ActualMultiplicityInertiaAttachment source}
    (invariant : SelectedFineFibreInvariant inertiaAttachment)
    (inertia : Actual.MultiplicityInertia inertiaAttachment)
    (sheet : Codec.Sheet9) ->
  Outgoing.projectSecondary
    (Compiler.compiledTenByNineAct
      inertiaAttachment
      inertia
      (Outgoing.embedSecondaryAt
        (selectedFine invariant)
        sheet))
  ≡ compiledSheetAct invariant inertia sheet
compiledSheetActionIsProjection invariant inertia sheet = refl

------------------------------------------------------------------------
-- 3. Compile the full old restriction record automatically.
------------------------------------------------------------------------

compiledOutgoingRestriction :
  ∀ {source}
    {inertiaAttachment :
      Actual.ActualMultiplicityInertiaAttachment source} ->
  (invariant : SelectedFineFibreInvariant inertiaAttachment) ->
  Outgoing.OutgoingSheet9ActualActionRestriction
    inertiaAttachment
    (Compiler.compiledTenByNineAttachment inertiaAttachment)
compiledOutgoingRestriction invariant =
  record
    { selectedFine = selectedFine invariant
    ; sheetAct = compiledSheetAct invariant
    ; selectedFinePreserved = selectedFinePreserved invariant
    ; sameActualSheetAction =
        compiledSheetActionIsProjection invariant
    }

------------------------------------------------------------------------
-- 4. Strong form: the actual 10x9 action on the selected fibre is exactly
--    the embedding of the compiled Sheet9 action.
------------------------------------------------------------------------

compiledActionStaysInSelectedFibre :
  ∀ {source}
    {inertiaAttachment :
      Actual.ActualMultiplicityInertiaAttachment source}
    (invariant : SelectedFineFibreInvariant inertiaAttachment)
    (inertia : Actual.MultiplicityInertia inertiaAttachment)
    (sheet : Codec.Sheet9) ->
  Compiler.compiledTenByNineAct
    inertiaAttachment
    inertia
    (Outgoing.embedSecondaryAt
      (selectedFine invariant)
      sheet)
  ≡
  Outgoing.embedSecondaryAt
    (selectedFine invariant)
    (compiledSheetAct invariant inertia sheet)
compiledActionStaysInSelectedFibre
  {inertiaAttachment = inertiaAttachment}
  invariant inertia sheet
  with Compiler.compiledTenByNineAct
        inertiaAttachment
        inertia
        (Outgoing.embedSecondaryAt
          (selectedFine invariant)
          sheet)
... | fine , secondary
  rewrite selectedFinePreserved invariant inertia sheet
        | Outgoing.secondaryCodecRoundTrip secondary = refl

------------------------------------------------------------------------
-- 5. Conversely every old restriction yields the reduced invariant datum.
------------------------------------------------------------------------

restrictionToFineInvariant :
  ∀ {source}
    {inertiaAttachment :
      Actual.ActualMultiplicityInertiaAttachment source} ->
  (restriction :
    Outgoing.OutgoingSheet9ActualActionRestriction
      inertiaAttachment
      (Compiler.compiledTenByNineAttachment inertiaAttachment)) ->
  SelectedFineFibreInvariant inertiaAttachment
restrictionToFineInvariant restriction =
  record
    { selectedFine = Outgoing.selectedFine restriction
    ; selectedFinePreserved =
        Outgoing.selectedFinePreserved restriction
    }

------------------------------------------------------------------------
-- 6. The compiler preserves the selected-fibre datum exactly.
------------------------------------------------------------------------

compiledRestrictionReturnsFine :
  ∀ {source}
    {inertiaAttachment :
      Actual.ActualMultiplicityInertiaAttachment source}
    (invariant : SelectedFineFibreInvariant inertiaAttachment) ->
  selectedFine
    (restrictionToFineInvariant
      (compiledOutgoingRestriction invariant))
  ≡ selectedFine invariant
compiledRestrictionReturnsFine invariant = refl

------------------------------------------------------------------------
-- 7. Firewall.
------------------------------------------------------------------------

data Fine10CountSelectsInvariantFibre : Set where
data CompilerCreatesInvariantFibre : Set where
data InvariantFibreCreatesMonsterAuthority : Set where

fineCountDoesNotSelectInvariantFibre :
  Fine10CountSelectsInvariantFibre -> ⊥
fineCountDoesNotSelectInvariantFibre ()

compilerDoesNotCreateInvariantFibre :
  CompilerCreatesInvariantFibre -> ⊥
compilerDoesNotCreateInvariantFibre ()

invariantFibreDoesNotCreateMonsterAuthority :
  InvariantFibreCreatesMonsterAuthority -> ⊥
invariantFibreDoesNotCreateMonsterAuthority ()

record Trialectic369OutgoingSheet9ActionRestrictionCompilerBoundary : Set where
  constructor trialectic-369-outgoing-sheet9-action-restriction-compiler-boundary
  field
    mixedRadixActualTenByNineActionReused : Bool
    selectedFineFibreInvariantIsOnlyNewDatum : Bool
    sheetActionGeneratedByProjection : Bool
    oldRestrictionRecordGenerated : Bool
    strongSelectedFibreIntertwiningGenerated : Bool
    oldRestrictionReducesBackToFineInvariant : Bool
    invariantFineFibreRecognizedHere : Bool
    monsterAuthorityCreatedByCompiler : Bool

canonicalTrialectic369OutgoingSheet9ActionRestrictionCompilerBoundary :
  Trialectic369OutgoingSheet9ActionRestrictionCompilerBoundary
canonicalTrialectic369OutgoingSheet9ActionRestrictionCompilerBoundary =
  trialectic-369-outgoing-sheet9-action-restriction-compiler-boundary
    true true true true true true false false
