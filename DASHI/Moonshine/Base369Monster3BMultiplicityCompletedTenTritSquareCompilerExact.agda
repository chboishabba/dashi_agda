module DASHI.Moonshine.Base369Monster3BMultiplicityCompletedTenTritSquareCompilerExact where

------------------------------------------------------------------------
-- FIN 90 -> COMPLETED10 x T^2 COMPILER
--
-- The remaining carrier recognition is not scientific data.  Data.Fin already
-- provides the mixed-radix equivalence
--
--   Fin (10 * 9) <-> Fin 10 x Fin 9
--
-- by remQuot/combine.  Composing that with the already-owned Base369 charts
--
--   Fin 10 <-> Completed10,
--   Fin 9  <-> T^2
--
-- yields a two-sided
--
--   Fin 90 <-> Completed10 x T^2.
--
-- Given any actual multiplicity inertia attachment, its action on Fin 90 is
-- transported through this chart by construction.  What remains nontrivial is
-- whether that transported action FACTORS through separate actions on the
-- Completed10 and T^2 coordinates; equivariant carrier recognition itself is
-- compiler output.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin.Base using (Fin)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import Data.Fin.Base as FinBase
import Data.Fin.Properties as FinP

import DASHI.Foundations.Base369PointedAppraisalFibreExact as Pointed
import DASHI.Moonshine.Base369CompletedTenTritSquareMultiplicityBidiExact as Completed
import DASHI.Moonshine.Base369Monster3BMultiplicityTenByNineBidiExact as Ninety
import DASHI.Moonshine.Base369Monster3BMultiplicityInertiaTwelveSeventyEightBidiExact as Actual
import DASHI.Moonshine.Base369Monster3BActualActionRecognitionBidiExact as Action

------------------------------------------------------------------------
-- 1. Canonical mixed-radix Fin 90 <-> Fin 10 x Fin 9.
------------------------------------------------------------------------

FinTenByNine : Set
FinTenByNine = Pointed.Fine10 × Pointed.SecondarySheet9

fin90ToTenByNine : Fin 90 → FinTenByNine
fin90ToTenByNine multiplicity = FinBase.remQuot 9 multiplicity

tenByNineToFin90 : FinTenByNine → Fin 90
tenByNineToFin90 (fine , sheet) = FinBase.combine fine sheet

tenByNineAfterFin90 :
  (multiplicity : Fin 90) →
  tenByNineToFin90 (fin90ToTenByNine multiplicity) ≡ multiplicity
tenByNineAfterFin90 multiplicity =
  FinP.combine-remQuot 9 multiplicity

fin90AfterTenByNine :
  (surface : FinTenByNine) →
  fin90ToTenByNine (tenByNineToFin90 surface) ≡ surface
fin90AfterTenByNine (fine , sheet) =
  FinP.remQuot-combine fine sheet

------------------------------------------------------------------------
-- 2. Compose with the semantic Base369 charts.
------------------------------------------------------------------------

fin90ToCompleted : Fin 90 → Completed.CompletedTenTritSquare
fin90ToCompleted multiplicity =
  Completed.toCompletedTenTritSquare (fin90ToTenByNine multiplicity)

completedToFin90 : Completed.CompletedTenTritSquare → Fin 90
completedToFin90 surface =
  tenByNineToFin90 (Completed.fromCompletedTenTritSquare surface)

completedAfterFin90 :
  (multiplicity : Fin 90) →
  completedToFin90 (fin90ToCompleted multiplicity) ≡ multiplicity
completedAfterFin90 multiplicity =
  trans
    (cong tenByNineToFin90
      (Completed.fromAfterToCompleted (fin90ToTenByNine multiplicity)))
    (tenByNineAfterFin90 multiplicity)

fin90AfterCompleted :
  (surface : Completed.CompletedTenTritSquare) →
  fin90ToCompleted (completedToFin90 surface) ≡ surface
fin90AfterCompleted surface =
  trans
    (cong Completed.toCompletedTenTritSquare
      (fin90AfterTenByNine (Completed.fromCompletedTenTritSquare surface)))
    (Completed.toAfterFromCompleted surface)

------------------------------------------------------------------------
-- 3. Transport the ACTUAL multiplicity action through this exact chart.
------------------------------------------------------------------------

completedActualAct :
  ∀ {source : Action.ActualMonster3BActionRecognition} →
  (attachment : Actual.ActualMultiplicityInertiaAttachment source) →
  Actual.MultiplicityInertia attachment →
  Completed.CompletedTenTritSquare →
  Completed.CompletedTenTritSquare
completedActualAct attachment inertia surface =
  fin90ToCompleted
    (Actual.multiplicityAct attachment inertia (completedToFin90 surface))

completedActualActionIntertwines :
  ∀ {source : Action.ActualMonster3BActionRecognition} →
  (attachment : Actual.ActualMultiplicityInertiaAttachment source) →
  (inertia : Actual.MultiplicityInertia attachment) →
  (multiplicity : Fin 90) →
  fin90ToCompleted
    (Actual.multiplicityAct attachment inertia multiplicity)
  ≡ completedActualAct attachment inertia (fin90ToCompleted multiplicity)
completedActualActionIntertwines attachment inertia multiplicity
  rewrite completedAfterFin90 multiplicity = refl

------------------------------------------------------------------------
-- 4. Package the old 10 x 9 attachment as compiler output.
------------------------------------------------------------------------

compiledTenByNineAct :
  ∀ {source : Action.ActualMonster3BActionRecognition} →
  (attachment : Actual.ActualMultiplicityInertiaAttachment source) →
  Actual.MultiplicityInertia attachment →
  FinTenByNine → FinTenByNine
compiledTenByNineAct attachment inertia surface =
  fin90ToTenByNine
    (Actual.multiplicityAct attachment inertia (tenByNineToFin90 surface))

compiledTenByNineIntertwines :
  ∀ {source : Action.ActualMonster3BActionRecognition} →
  (attachment : Actual.ActualMultiplicityInertiaAttachment source) →
  (inertia : Actual.MultiplicityInertia attachment) →
  (multiplicity : Fin 90) →
  fin90ToTenByNine
    (Actual.multiplicityAct attachment inertia multiplicity)
  ≡ compiledTenByNineAct attachment inertia (fin90ToTenByNine multiplicity)
compiledTenByNineIntertwines attachment inertia multiplicity
  rewrite tenByNineAfterFin90 multiplicity = refl

compiledTenByNineAttachment :
  ∀ {source : Action.ActualMonster3BActionRecognition} →
  (attachment : Actual.ActualMultiplicityInertiaAttachment source) →
  Ninety.ActualMultiplicityTenByNineAttachment attachment
compiledTenByNineAttachment attachment =
  record
    { toTenByNine = fin90ToTenByNine
    ; fromTenByNine = tenByNineToFin90
    ; fromAfterTo = tenByNineAfterFin90
    ; toAfterFrom = fin90AfterTenByNine
    ; tenByNineAct = compiledTenByNineAct attachment
    ; sameActualMultiplicityAction = compiledTenByNineIntertwines attachment
    }

------------------------------------------------------------------------
-- 5. Package the completed semantic attachment as compiler output too.
------------------------------------------------------------------------

completedChartIntertwinesCompiled :
  ∀ {source : Action.ActualMonster3BActionRecognition} →
  (attachment : Actual.ActualMultiplicityInertiaAttachment source) →
  (inertia : Actual.MultiplicityInertia attachment) →
  (surface : Ninety.TenByNineMultiplicity) →
  Completed.toCompletedTenTritSquare
    (compiledTenByNineAct attachment inertia surface)
  ≡ completedActualAct attachment inertia
      (Completed.toCompletedTenTritSquare surface)
completedChartIntertwinesCompiled attachment inertia surface
  rewrite Completed.fromAfterToCompleted surface = refl

compiledCompletedAttachment :
  ∀ {source : Action.ActualMonster3BActionRecognition} →
  (attachment : Actual.ActualMultiplicityInertiaAttachment source) →
  Completed.ActualMultiplicityCompletedTenTritSquareAttachment attachment
compiledCompletedAttachment attachment =
  record
    { tenByNineAttachment = compiledTenByNineAttachment attachment
    ; completedAct = completedActualAct attachment
    ; completedChartIntertwines = completedChartIntertwinesCompiled attachment
    }

------------------------------------------------------------------------
-- 6. Boundary: factorwise dynamics are the remaining scientific question.
------------------------------------------------------------------------

record CompletedMultiplicityCompilerBoundary : Set where
  constructor completedMultiplicityCompilerBoundary
  field
    mixedRadixFin90ToFin10TimesFin9Owned : Bool
    completedTenAndTritSquareChartsAlreadyOwned : Bool
    fin90ToCompletedTenTimesTritSquareTwoSided : Bool
    actualInertiaActionTransportedByConstruction : Bool
    oldTenByNineAttachmentGenerated : Bool
    oldCompletedAttachmentGenerated : Bool
    separateEquivariantCarrierRecognitionStillScientific : Bool
    factorwiseTenAndTritSquareActionAlreadyProved : Bool
    factorwiseActionIsNextScientificTest : Bool

canonicalCompletedMultiplicityCompilerBoundary :
  CompletedMultiplicityCompilerBoundary
canonicalCompletedMultiplicityCompilerBoundary =
  completedMultiplicityCompilerBoundary
    true true true true true true false false true
