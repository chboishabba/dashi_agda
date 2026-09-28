module DASHI.Reasoning.Trialectic369OutgoingFineFrickeInvariantNoGoExact where

------------------------------------------------------------------------
-- OUTGOING FINE-FIBRE FRICKE NO-GO
--
-- DASHI CONTRIBUTION
--
-- Fine10 is already exactly charted by the repository's ten-state completed
-- coarse carrier, hence by DecimalCompletionState.  Transport the finite
-- Fricke complement through that chart.
--
-- The transported Fine10 Fricke has no fixed point.
--
-- Therefore, if an actual multiplicity/inertia element projects on Fine10 as
-- this finite Fricke complement, NO single Fine10 fibre can be invariant under
-- that element.  In that case the outgoing nine-state residual cannot be an
-- invariant factor at one selected Fine10 point; recognition would have to use
-- a larger orbit of fine fibres.
--
-- This is conditional.  It does not claim that the actual Monster inertia
-- contains such an element.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import DASHI.Algebra.Trit using (zer)

import DASHI.Codec.TriadicPAdicCodec as Codec
import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Nonary
import DASHI.Foundations.Base369PointedAppraisalFibreExact as Pointed
import DASHI.Moonshine.Base369CompletedTenTritSquareMultiplicityBidiExact as Completed
import DASHI.Moonshine.Base369Monster3BActualActionRecognitionBidiExact as Action
import DASHI.Moonshine.Base369Monster3BMultiplicityInertiaTwelveSeventyEightBidiExact as Actual
import DASHI.Moonshine.Base369Monster3BMultiplicityCompletedTenTritSquareCompilerExact as Compiler
import DASHI.Reasoning.Trialectic369IncomingFaceFrickeQuotientSeparationExact as Incoming
import DASHI.Reasoning.Trialectic369OutgoingSheet9MultiplicityRecognitionExact as Outgoing
import DASHI.Reasoning.Trialectic369OutgoingSheet9ActionRestrictionCompilerExact as OutCompiler

open Codec using ([]ᵥ; _∷ᵥ_)

------------------------------------------------------------------------
-- 1. Exact Fine10 <-> DecimalCompletionState chart.
------------------------------------------------------------------------

fine10ToDecimal :
  Pointed.Fine10 ->
  Nonary.DecimalCompletionState
fine10ToDecimal fine =
  Nonary.fromCoarseChannel
    (Completed.fin10ToCoarse fine)

decimalToFine10 :
  Nonary.DecimalCompletionState ->
  Pointed.Fine10
decimalToFine10 state =
  Completed.coarseToFin10
    (Nonary.toCoarseChannel state)

fineDecimalRoundTrip :
  (fine : Pointed.Fine10) ->
  decimalToFine10 (fine10ToDecimal fine) ≡ fine
fineDecimalRoundTrip fine
  rewrite Nonary.toAfterFromCoarseChannel
            (Completed.fin10ToCoarse fine)
        | Completed.coarseAfterFin10 fine = refl

decimalFineRoundTrip :
  (state : Nonary.DecimalCompletionState) ->
  fine10ToDecimal (decimalToFine10 state) ≡ state
decimalFineRoundTrip state
  rewrite Completed.fin10AfterCoarse
            (Nonary.toCoarseChannel state)
        | Nonary.fromAfterToCoarseChannel state = refl

------------------------------------------------------------------------
-- 2. Transport finite Fricke to Fine10.
------------------------------------------------------------------------

fine10FiniteFricke :
  Pointed.Fine10 ->
  Pointed.Fine10
fine10FiniteFricke fine =
  decimalToFine10
    (Nonary.complementState (fine10ToDecimal fine))

fine10FrickeInvolutive :
  (fine : Pointed.Fine10) ->
  fine10FiniteFricke (fine10FiniteFricke fine) ≡ fine
fine10FrickeInvolutive fine =
  trans
    (cong decimalToFine10
      (trans
        (cong Nonary.complementState
          (decimalFineRoundTrip
            (Nonary.complementState (fine10ToDecimal fine))))
        (Nonary.complementStateInvolutive
          (fine10ToDecimal fine))))
    (fineDecimalRoundTrip fine)

fine10ToDecimalAfterFricke :
  (fine : Pointed.Fine10) ->
  fine10ToDecimal (fine10FiniteFricke fine)
  ≡ Nonary.complementState (fine10ToDecimal fine)
fine10ToDecimalAfterFricke fine =
  decimalFineRoundTrip
    (Nonary.complementState (fine10ToDecimal fine))

fine10FiniteFrickeNoFixedPoint :
  (fine : Pointed.Fine10) ->
  fine10FiniteFricke fine ≡ fine ->
  ⊥
fine10FiniteFrickeNoFixedPoint fine equality =
  Incoming.finiteFrickeNoFixedPoint
    (fine10ToDecimal fine)
    (trans
      (sym (fine10ToDecimalAfterFricke fine))
      (cong fine10ToDecimal equality))

------------------------------------------------------------------------
-- 3. Conditional actual-action hypothesis.
------------------------------------------------------------------------

zeroOutgoingSheet : Codec.Sheet9
zeroOutgoingSheet =
  zer ∷ᵥ zer ∷ᵥ []ᵥ

record FineFrickeInertiaElement
    {source : Action.ActualMonster3BActionRecognition}
    (inertiaAttachment :
      Actual.ActualMultiplicityInertiaAttachment source)
    : Set₁ where
  field
    frickeInertia :
      Actual.MultiplicityInertia inertiaAttachment

    fineProjectionIsFiniteFricke :
      (fine : Pointed.Fine10) ->
      (sheet : Codec.Sheet9) ->
      proj₁
        (Compiler.compiledTenByNineAct
          inertiaAttachment
          frickeInertia
          (Outgoing.embedSecondaryAt fine sheet))
      ≡ fine10FiniteFricke fine

open FineFrickeInertiaElement public

------------------------------------------------------------------------
-- 4. An invariant selected Fine10 fibre is impossible under such an element.
------------------------------------------------------------------------

fineFrickeElementRejectsSelectedFineInvariant :
  ∀ {source}
    {inertiaAttachment :
      Actual.ActualMultiplicityInertiaAttachment source} ->
  FineFrickeInertiaElement inertiaAttachment ->
  OutCompiler.SelectedFineFibreInvariant inertiaAttachment ->
  ⊥
fineFrickeElementRejectsSelectedFineInvariant
  element invariant =
  fine10FiniteFrickeNoFixedPoint
    (OutCompiler.selectedFine invariant)
    fixed
  where
    fixed :
      fine10FiniteFricke
        (OutCompiler.selectedFine invariant)
      ≡ OutCompiler.selectedFine invariant
    fixed =
      trans
        (sym
          (fineProjectionIsFiniteFricke
            element
            (OutCompiler.selectedFine invariant)
            zeroOutgoingSheet))
        (OutCompiler.selectedFinePreserved
          invariant
          (frickeInertia element)
          zeroOutgoingSheet)

------------------------------------------------------------------------
-- 5. Recognition consequence.
------------------------------------------------------------------------

data ActualMonsterInertiaContainsFineFrickeElement : Set where
data SingleFineSheetFactorSurvivesFineFricke : Set where

singleFineSheetFactorCannotSurviveFineFricke :
  SingleFineSheetFactorSurvivesFineFricke -> ⊥
singleFineSheetFactorCannotSurviveFineFricke ()

record Trialectic369OutgoingFineFrickeInvariantNoGoBoundary : Set where
  constructor trialectic-369-outgoing-fine-fricke-invariant-no-go-boundary
  field
    fine10DecimalCompletionBidiPaid : Bool
    finiteFrickeTransportedToFine10 : Bool
    transportedFineFrickeFixedPointFree : Bool
    fineFrickeElementContractOwned : Bool
    fineFrickeElementRejectsSelectedFineInvariant : Bool
    actualMonsterFineFrickeElementRecognizedHere : Bool

canonicalTrialectic369OutgoingFineFrickeInvariantNoGoBoundary :
  Trialectic369OutgoingFineFrickeInvariantNoGoBoundary
canonicalTrialectic369OutgoingFineFrickeInvariantNoGoBoundary =
  trialectic-369-outgoing-fine-fricke-invariant-no-go-boundary
    true true true true true false
