module DASHI.Foundations.UBP.ObservableAlgebraBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat) renaming (_+_ to _+ᴺ_)
open import Data.Integer using (ℤ; +_)
open import Data.Rational using (ℚ; _+_; _-_; _*_; _/_; 0ℚ)
import Data.Rational.Tactic.RingSolver as ℚRing

import DASHI.Core.AuthorityNonPromotionCore as Authority
import DASHI.Core.GenericReceipt as GenericReceipt

1ℚ 2ℚ 4ℚ 9ℚ 16ℚ : ℚ
1ℚ = + 1 / 1
2ℚ = + 2 / 1
4ℚ = + 4 / 1
9ℚ = + 9 / 1
16ℚ = + 16 / 1

------------------------------------------------------------------------
-- Exact algebra internal to the declared UBP observables.
--
-- These theorems retain the valid mathematical content of the supplied
-- perturbation/cascade calculations while refusing the unsupported jump from
-- an internal identity to a physical activation, vacuum, force, or
-- manifestation theorem.

oneEighth :
  ℚ
oneEighth =
  + 1 / 8

oneHalf :
  ℚ
oneHalf =
  + 1 / 2

threeQuarters :
  ℚ
threeQuarters =
  + 3 / 4

symmetryTax :
  ℚ →
  ℚ →
  ℚ →
  ℚ
symmetryTax y support normSquared =
  support * y + normSquared * oneEighth

activationQuantum :
  ℚ →
  ℚ →
  ℚ
activationQuantum y coordinateSquare =
  y + coordinateSquare * oneEighth

deexcitationQuantum :
  ℚ →
  ℚ →
  ℚ
deexcitationQuantum y coordinateSquare =
  0ℚ - activationQuantum y coordinateSquare

open import Data.List using (_∷_; [])

activationDifferenceIdentity :
  (y support normSquared coordinateSquare : ℚ) →
  symmetryTax
    y
    (support + 1ℚ)
    (normSquared + coordinateSquare)
  - symmetryTax y support normSquared
  ≡
  activationQuantum y coordinateSquare
activationDifferenceIdentity y support normSquared coordinateSquare =
  helper y support normSquared coordinateSquare
  where
    helper : (y support normSquared coordinateSquare : ℚ) →
      ((support + 1ℚ) * y + (normSquared + coordinateSquare) * oneEighth)
      - (support * y + normSquared * oneEighth)
      ≡ y + coordinateSquare * oneEighth
    helper y support normSquared coordinateSquare =
      ℚRing.solve (y ∷ support ∷ normSquared ∷ coordinateSquare ∷ [])

deexcitationDifferenceIdentity :
  (y support normSquared coordinateSquare : ℚ) →
  symmetryTax
    y
    (support - 1ℚ)
    (normSquared - coordinateSquare)
  - symmetryTax y support normSquared
  ≡
  deexcitationQuantum y coordinateSquare
deexcitationDifferenceIdentity y support normSquared coordinateSquare =
  helper y support normSquared coordinateSquare
  where
    helper : (y support normSquared coordinateSquare : ℚ) →
      ((support - 1ℚ) * y + (normSquared - coordinateSquare) * oneEighth)
      - (support * y + normSquared * oneEighth)
      ≡ 0ℚ - (y + coordinateSquare * oneEighth)
    helper y support normSquared coordinateSquare =
      ℚRing.solve (y ∷ support ∷ normSquared ∷ coordinateSquare ∷ [])

unitActivationIdentity :
  (y : ℚ) →
  activationQuantum y 1ℚ
  ≡
  y + oneEighth
unitActivationIdentity y =
  refl

classADeexcitationIdentity :
  (y : ℚ) →
  deexcitationQuantum y 16ℚ
  ≡
  0ℚ - (y + 16ℚ * oneEighth)
classADeexcitationIdentity y =
  refl

classBDeexcitationIdentity :
  (y : ℚ) →
  deexcitationQuantum y 4ℚ
  ≡
  0ℚ - (y + 4ℚ * oneEighth)
classBDeexcitationIdentity y =
  refl

classCThreeDeexcitationIdentity :
  (y : ℚ) →
  deexcitationQuantum y 9ℚ
  ≡
  0ℚ - (y + 9ℚ * oneEighth)
classCThreeDeexcitationIdentity y =
  refl

longCycleCancellationIdentity :
  (y : ℚ) →
  2ℚ * activationQuantum y 1ℚ
  + 2ℚ * deexcitationQuantum y 4ℚ
  ≡
  0ℚ - threeQuarters
longCycleCancellationIdentity y =
  helper y
  where
    helper : (y : ℚ) →
      2ℚ * (y + 1ℚ * oneEighth) + 2ℚ * (0ℚ - (y + 4ℚ * oneEighth))
      ≡ 0ℚ - threeQuarters
    helper y = ℚRing.solve (y ∷ [])

oneEighthIsOneOverEight :
  oneEighth ≡ + 1 / 8
oneEighthIsOneOverEight =
  refl

oneHalfIsOneOverTwo :
  oneHalf ≡ + 1 / 2
oneHalfIsOneOverTwo =
  refl

threeQuartersIsThreeOverFour :
  threeQuarters ≡ + 3 / 4
threeQuartersIsThreeOverFour =
  refl

------------------------------------------------------------------------
-- NRCI half-threshold is a normalization identity.

nrci :
  Nat →
  ℚ
nrci tax =
  + 10 / (10 +ᴺ tax)

nrciAtTaxTen :
  nrci 10 ≡ oneHalf
nrciAtTaxTen =
  refl

record CoherenceThresholdStatus : Set where
  constructor coherenceThresholdStatus
  field
    thresholdLabel :
      String

    halfThresholdAtTaxTenProved :
      Bool

    halfThresholdAtTaxTenProvedIsTrue :
      halfThresholdAtTaxTenProved ≡ true

    thresholdFollowsFromDeclaredNormalization :
      Bool

    thresholdFollowsFromDeclaredNormalizationIsTrue :
      thresholdFollowsFromDeclaredNormalization ≡ true

    independentlyEmergentPhysicalThresholdEstablished :
      Bool

    independentlyEmergentPhysicalThresholdEstablishedIsFalse :
      independentlyEmergentPhysicalThresholdEstablished ≡ false

    thresholdReading :
      String

open CoherenceThresholdStatus public

canonicalCoherenceThresholdStatus :
  CoherenceThresholdStatus
canonicalCoherenceThresholdStatus =
  coherenceThresholdStatus
    "NRCI one-half threshold"
    true
    refl
    true
    refl
    false
    refl
    "NRCI(10) = 1/2 follows exactly from NRCI(t) = 10/(10+t); an independently selected physical phase threshold requires external evidence"

------------------------------------------------------------------------
-- State observables are endpoint functions.

record EndpointObservable {State : Set} : Set where
  constructor endpointObservable
  field
    supportOf :
      State →
      ℚ

    normSquaredOf :
      State →
      ℚ

    observerConstant :
      ℚ

open EndpointObservable public

endpointTax :
  ∀ {State : Set} →
  EndpointObservable {State} →
  State →
  ℚ
endpointTax observable state =
  symmetryTax
    (observerConstant observable)
    (supportOf observable state)
    (normSquaredOf observable state)

open import Relation.Binary.PropositionalEquality using (cong₂)

endpointTaxExtensional :
  ∀ {State : Set} →
  (observable : EndpointObservable {State}) →
  (left right : State) →
  supportOf observable left ≡ supportOf observable right →
  normSquaredOf observable left ≡ normSquaredOf observable right →
  endpointTax observable left ≡ endpointTax observable right
endpointTaxExtensional observable left right supEq normEq =
  cong₂ (symmetryTax (observerConstant observable)) supEq normEq

------------------------------------------------------------------------
-- Existing DASHI authority integration.

observableAlgebraAuthorityBoundary :
  Authority.AuthorityNonPromotionBundle
observableAlgebraAuthorityBoundary =
  Authority.mkClosedAuthorityNonPromotionBundle
    "UBP observable algebra authority boundary"

observableAlgebraReceipt :
  GenericReceipt.GenericReceipt
observableAlgebraReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "UBP observable algebra boundary"
    "DASHI.Foundations.UBP.ObservableAlgebraBoundary"
    "symmetryTax activation deexcitation long-cycle and NRCI normalization identities"
    "exact rational algebra proves the activation/deexcitation differences, Y-independent minus-three-quarters cancellation, endpoint extensionality, and NRCI(10)=1/2"
    "physical activation, vacuum, force, manifestation, phase-transition, and empirical-threshold authority remain outside these internal identities"
    "agda -i . DASHI/Foundations/UBP/ObservableAlgebraBoundary.agda"

observableAlgebraReceiptNonPromoting :
  GenericReceipt.promotesClaim observableAlgebraReceipt ≡ false
observableAlgebraReceiptNonPromoting =
  GenericReceipt.promotesClaimIsFalse observableAlgebraReceipt
