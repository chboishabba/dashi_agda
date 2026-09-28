module DASHI.Reasoning.Trialectic369OutgoingSheet9MultiplicityRecognitionExact where

------------------------------------------------------------------------
-- OUTGOING RESIDUAL SHEET9 -> BASE369 SECONDARY SHEET9 RECOGNITION
--
-- DASHI CONTRIBUTION
--
-- The participant-centered outgoing residual is already identified with the
-- canonical TriadicPAdicCodec.Sheet9.  Existing Base369 multiplicity machinery
-- uses a second nine-state carrier:
--
--   SecondarySheet9 = Fin 9.
--
-- The completed 10x9 owner already proves:
--
--   SecondarySheet9 <-> literal TritSquare.
--
-- This module closes the remaining carrier seam:
--
--   Codec.Sheet9 <-> TritSquare <-> SecondarySheet9.
--
-- The actual Monster-3B inertia action is still carried by the WHOLE
-- Fine10 x SecondarySheet9 surface.  A separate restriction/intertwining
-- witness is required before the outgoing residual may be called an invariant
-- inertia factor.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.Fin.Base using (Fin)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Codec.TriadicPAdicCodec as Codec
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369NonaryTritSquareExact as Square
import DASHI.Foundations.Base369PointedAppraisalFibreExact as Pointed
import DASHI.Moonshine.Base369CompletedTenTritSquareMultiplicityBidiExact as Completed
import DASHI.Moonshine.Base369Monster3BMultiplicityTenByNineBidiExact as Ninety
import DASHI.Moonshine.Base369Monster3BActualActionRecognitionBidiExact as Action
import DASHI.Moonshine.Base369Monster3BMultiplicityInertiaTwelveSeventyEightBidiExact as Actual

open Codec using ([]ᵥ; _∷ᵥ_)

------------------------------------------------------------------------
-- 1. Codec Sheet9 <-> literal TritSquare.
------------------------------------------------------------------------

codecSheet9ToTritSquare :
  Codec.Sheet9 ->
  Square.TritSquare
codecSheet9ToTritSquare
  (left ∷ᵥ right ∷ᵥ []ᵥ) =
  Square.tritSquare
    (SSP.fromTrit left)
    (SSP.fromTrit right)

tritSquareToCodecSheet9 :
  Square.TritSquare ->
  Codec.Sheet9
tritSquareToCodecSheet9
  (Square.tritSquare left right) =
  SSP.toTrit left
  ∷ᵥ SSP.toTrit right
  ∷ᵥ []ᵥ

codecSquareRoundTrip :
  (sheet : Codec.Sheet9) ->
  tritSquareToCodecSheet9
    (codecSheet9ToTritSquare sheet)
  ≡ sheet
codecSquareRoundTrip
  (left ∷ᵥ right ∷ᵥ []ᵥ)
  rewrite SSP.toTrit-fromTrit left
        | SSP.toTrit-fromTrit right = refl

squareCodecRoundTrip :
  (square : Square.TritSquare) ->
  codecSheet9ToTritSquare
    (tritSquareToCodecSheet9 square)
  ≡ square
squareCodecRoundTrip
  (Square.tritSquare left right)
  rewrite SSP.fromTrit-toTrit left
        | SSP.fromTrit-toTrit right = refl

------------------------------------------------------------------------
-- 2. Codec Sheet9 <-> Base369 SecondarySheet9.
------------------------------------------------------------------------

codecSheet9ToSecondary :
  Codec.Sheet9 ->
  Pointed.SecondarySheet9
codecSheet9ToSecondary sheet =
  Completed.tritSquareToFin9
    (codecSheet9ToTritSquare sheet)

secondaryToCodecSheet9 :
  Pointed.SecondarySheet9 ->
  Codec.Sheet9
secondaryToCodecSheet9 secondary =
  tritSquareToCodecSheet9
    (Completed.fin9ToTritSquare secondary)

codecSecondaryRoundTrip :
  (sheet : Codec.Sheet9) ->
  secondaryToCodecSheet9
    (codecSheet9ToSecondary sheet)
  ≡ sheet
codecSecondaryRoundTrip sheet =
  trans
    (cong
      tritSquareToCodecSheet9
      (Completed.fin9AfterTritSquare
        (codecSheet9ToTritSquare sheet)))
    (codecSquareRoundTrip sheet)

secondaryCodecRoundTrip :
  (secondary : Pointed.SecondarySheet9) ->
  codecSheet9ToSecondary
    (secondaryToCodecSheet9 secondary)
  ≡ secondary
secondaryCodecRoundTrip secondary =
  trans
    (cong
      Completed.tritSquareToFin9
      (squareCodecRoundTrip
        (Completed.fin9ToTritSquare secondary)))
    (Completed.tritSquareAfterFin9 secondary)

------------------------------------------------------------------------
-- 3. The existing 10 x 9 surface contains this exact sheet carrier.
------------------------------------------------------------------------

TenByNineSurface : Set
TenByNineSurface =
  Ninety.TenByNineMultiplicity

embedSecondaryAt :
  Pointed.Fine10 ->
  Codec.Sheet9 ->
  TenByNineSurface
embedSecondaryAt fine sheet =
  fine , codecSheet9ToSecondary sheet

projectSecondary :
  TenByNineSurface ->
  Codec.Sheet9
projectSecondary (fine , secondary) =
  secondaryToCodecSheet9 secondary

projectEmbeddedSecondary :
  (fine : Pointed.Fine10) ->
  (sheet : Codec.Sheet9) ->
  projectSecondary (embedSecondaryAt fine sheet)
  ≡ sheet
projectEmbeddedSecondary fine sheet =
  codecSecondaryRoundTrip sheet

------------------------------------------------------------------------
-- 4. Exact action-restriction payment still required.
--
-- The actual ten-by-nine action may in principle mix Fine10 and the sheet.
-- To recognize our outgoing residual as an actual invariant factor, require:
--
--   * a chosen fine fibre;
--   * an induced action on Codec.Sheet9;
--   * preservation of that fibre by the whole 10x9 action;
--   * exact intertwining through the embedding.
------------------------------------------------------------------------

record OutgoingSheet9ActualActionRestriction
    {source : Action.ActualMonster3BActionRecognition}
    (inertiaAttachment :
      Actual.ActualMultiplicityInertiaAttachment source)
    (tenByNineAttachment :
      Ninety.ActualMultiplicityTenByNineAttachment inertiaAttachment)
    : Set₁ where
  field
    selectedFine :
      Pointed.Fine10

    sheetAct :
      Actual.MultiplicityInertia inertiaAttachment ->
      Codec.Sheet9 ->
      Codec.Sheet9

    selectedFinePreserved :
      (inertia : Actual.MultiplicityInertia inertiaAttachment) ->
      (sheet : Codec.Sheet9) ->
      Data.Product.proj₁
        (Ninety.tenByNineAct
          tenByNineAttachment
          inertia
          (embedSecondaryAt selectedFine sheet))
      ≡ selectedFine

    sameActualSheetAction :
      (inertia : Actual.MultiplicityInertia inertiaAttachment) ->
      (sheet : Codec.Sheet9) ->
      projectSecondary
        (Ninety.tenByNineAct
          tenByNineAttachment
          inertia
          (embedSecondaryAt selectedFine sheet))
      ≡ sheetAct inertia sheet

open OutgoingSheet9ActualActionRestriction public

------------------------------------------------------------------------
-- 5. Firewall.
------------------------------------------------------------------------

data CarrierBidiCreatesActualMonsterInertiaFactor : Set where
data NineStateCountAloneSelectsFineFibre : Set where

carrierBidiDoesNotCreateActualInertiaFactor :
  CarrierBidiCreatesActualMonsterInertiaFactor -> ⊥
carrierBidiDoesNotCreateActualInertiaFactor ()

countDoesNotSelectFineFibre :
  NineStateCountAloneSelectsFineFibre -> ⊥
countDoesNotSelectFineFibre ()

record Trialectic369OutgoingSheet9MultiplicityRecognitionBoundary : Set where
  constructor trialectic-369-outgoing-sheet9-multiplicity-recognition-boundary
  field
    codecSheet9TritSquareBidiPaid : Bool
    tritSquareSecondarySheet9BidiReused : Bool
    codecSheet9SecondarySheet9BidiPaid : Bool
    outgoingResidualLivesOnExistingTenByNineSheetCarrier : Bool
    actualActionRestrictionContractOwned : Bool
    actualActionRestrictionInhabitedHere : Bool
    carrierCountAlonePromotesInertiaRecognition : Bool

canonicalTrialectic369OutgoingSheet9MultiplicityRecognitionBoundary :
  Trialectic369OutgoingSheet9MultiplicityRecognitionBoundary
canonicalTrialectic369OutgoingSheet9MultiplicityRecognitionBoundary =
  trialectic-369-outgoing-sheet9-multiplicity-recognition-boundary
    true true true true true false false
