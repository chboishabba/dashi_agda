module DASHI.Foundations.UBP.ObservableAlgebraBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Rational using (ℚ; _+_; _-_; _*_; _/_; 0ℚ)
import Data.Rational.Tactic.RingSolver as ℚRing

import DASHI.Core.AuthorityNonPromotionCore as Authority
import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- Exact algebra internal to the declared UBP observables.
--
-- These theorems retain the valid mathematical content of the supplied
-- perturbation/cascade calculations while refusing the unsupported jump from
-- an internal identity to a physical activation, vacuum, force, or
-- manifestation theorem.

symmetryTax :
  ℚ →
  ℚ →
  ℚ →
  ℚ
symmetryTax y support normSquared =
  support * y + normSquared / 8

activationQuantum :
  ℚ →
  ℚ →
  ℚ
activationQuantum y coordinateSquare =
  y + coordinateSquare / 8

deexcitationQuantum :
  ℚ →
  ℚ →
  ℚ
deexcitationQuantum y coordinateSquare =
  0ℚ - activationQuantum y coordinateSquare

activationDifferenceIdentity :
  (y support normSquared coordinateSquare : ℚ) →
  symmetryTax
    y
    (support + 1)
    (normSquared + coordinateSquare)
  - symmetryTax y support normSquared
  ≡
  activationQuantum y coordinateSquare
activationDifferenceIdentity y support normSquared coordinateSquare =
  ℚRing.solve

deexcitationDifferenceIdentity :
  (y support normSquared coordinateSquare : ℚ) →
  symmetryTax
    y
    (support - 1)
    (normSquared - coordinateSquare)
  - symmetryTax y support normSquared
  ≡
  deexcitationQuantum y coordinateSquare
deexcitationDifferenceIdentity y support normSquared coordinateSquare =
  ℚRing.solve

unitActivationIdentity :
  (y : ℚ) →
  activationQuantum y 1
  ≡
  y + 1 / 8
unitActivationIdentity y =
  refl

classADeexcitationIdentity :
  (y : ℚ) →
  deexcitationQuantum y 16
  ≡
  0ℚ - (y + 16 / 8)
classADeexcitationIdentity y =
  refl

classBDeexcitationIdentity :
  (y : ℚ) →
  deexcitationQuantum y 4
  ≡
  0ℚ - (y + 4 / 8)
classBDeexcitationIdentity y =
  refl

classCThreeDeexcitationIdentity :
  (y : ℚ) →
  deexcitationQuantum y 9
  ≡
  0ℚ - (y + 9 / 8)
classCThreeDeexcitationIdentity y =
  refl

longCycleCancellationIdentity :
  (y : ℚ) →
  2 * activationQuantum y 1
  + 2 * deexcitationQuantum y 4
  ≡
  0ℚ - 3 / 4
longCycleCancellationIdentity y =
  ℚRing.solve

------------------------------------------------------------------------
-- NRCI half-threshold is a normalization identity.

nrci :
  ℚ →
  ℚ
nrci tax =
  10 / (10 + tax)

nrciAtTaxTen :
  nrci 10 ≡ 1 / 2
nrciAtTaxTen =
  ℚRing.solve

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

endpointTaxExtensional :
  ∀ {State : Set} →
  (observable : EndpointObservable {State}) →
  (left right : State) →
  supportOf observable left ≡ supportOf observable right →
  normSquaredOf observable left ≡ normSquaredOf observable right →
  endpointTax observable left ≡ endpointTax observable right
endpointTaxExtensional observable left right refl refl =
  refl

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
