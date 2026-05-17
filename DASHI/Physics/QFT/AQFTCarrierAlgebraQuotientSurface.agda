module DASHI.Physics.QFT.AQFTCarrierAlgebraQuotientSurface where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.AQFTTypedNetSurface as AQFT

------------------------------------------------------------------------
-- AQFT local algebra from carrier receipts: quotient target surface.
--
-- This module records the next construction target after the abstract
-- Haag-Kastler net socket:
--
--   A(O) = promoted receipts over the carrier restricted to O,
--          quotiented by transport equivalence.
--
-- It intentionally keeps the restricted carrier, promoted-receipt predicate,
-- quotient carrier, and algebra operations abstract.  It does not construct a
-- C*-algebra, GNS state, Born-rule adapter, interacting QFT, Standard Model
-- net, or GRQFT promotion receipt.

data AQFTCarrierAlgebraQuotientStatus : Set where
  quotientSurfaceOnlyNoAQFTPromotion :
    AQFTCarrierAlgebraQuotientStatus

data AQFTCarrierAlgebraQuotientOpenObligation : Set where
  missingRestrictedCarrier :
    AQFTCarrierAlgebraQuotientOpenObligation

  missingTransportEquivalenceLaws :
    AQFTCarrierAlgebraQuotientOpenObligation

  missingPromotedReceiptPredicate :
    AQFTCarrierAlgebraQuotientOpenObligation

  missingQuotientConstruction :
    AQFTCarrierAlgebraQuotientOpenObligation

  missingAlgebraOperationsOnQuotient :
    AQFTCarrierAlgebraQuotientOpenObligation

  missingIsotonyFromCarrierTransport :
    AQFTCarrierAlgebraQuotientOpenObligation

data AQFTCarrierAlgebraPromotionAuthorityToken : Set where

record AQFTCarrierAlgebraQuotientSurface : Setω where
  field
    status :
      AQFTCarrierAlgebraQuotientStatus

    typedNetSurface :
      AQFT.AQFTTypedNetSurface

    RestrictedCarrier :
      AQFT.Region →
      Set

    TransportEquivalent :
      {region : AQFT.Region} →
      RestrictedCarrier region →
      RestrictedCarrier region →
      Set

    transportRefl :
      {region : AQFT.Region} →
      (x : RestrictedCarrier region) →
      TransportEquivalent x x

    transportSym :
      {region : AQFT.Region} →
      {x y : RestrictedCarrier region} →
      TransportEquivalent x y →
      TransportEquivalent y x

    transportTrans :
      {region : AQFT.Region} →
      {x y z : RestrictedCarrier region} →
      TransportEquivalent x y →
      TransportEquivalent y z →
      TransportEquivalent x z

    PromotedReceipt :
      {region : AQFT.Region} →
      RestrictedCarrier region →
      Set

    promotedReceiptTransport :
      {region : AQFT.Region} →
      {x y : RestrictedCarrier region} →
      TransportEquivalent x y →
      PromotedReceipt x →
      PromotedReceipt y

    PromotedReceiptQuotient :
      AQFT.Region →
      Set

    quotientIntro :
      {region : AQFT.Region} →
      (x : RestrictedCarrier region) →
      PromotedReceipt x →
      PromotedReceiptQuotient region

    quotientTransportStable :
      {region : AQFT.Region} →
      {x y : RestrictedCarrier region} →
      (eq : TransportEquivalent x y) →
      (receipt : PromotedReceipt x) →
      quotientIntro x receipt
      ≡
      quotientIntro y (promotedReceiptTransport eq receipt)

    localAlgebraIsPromotedReceiptQuotient :
      (region : AQFT.Region) →
      AQFT.AQFTTypedNetSurface.Algebra typedNetSurface region
      ≡
      PromotedReceiptQuotient region

    openObligations :
      List AQFTCarrierAlgebraQuotientOpenObligation

    aqftPromoted :
      Bool

    aqftPromotedIsFalse :
      aqftPromoted ≡ false

    noPromotionWithoutAuthority :
      AQFTCarrierAlgebraPromotionAuthorityToken →
      ⊥

    quotientBoundary :
      List String

open AQFTCarrierAlgebraQuotientSurface public

postulate
  abstractRestrictedCarrier :
    AQFT.Region →
    Set

  abstractTransportEquivalent :
    {region : AQFT.Region} →
    abstractRestrictedCarrier region →
    abstractRestrictedCarrier region →
    Set

  abstractTransportRefl :
    {region : AQFT.Region} →
    (x : abstractRestrictedCarrier region) →
    abstractTransportEquivalent x x

  abstractTransportSym :
    {region : AQFT.Region} →
    {x y : abstractRestrictedCarrier region} →
    abstractTransportEquivalent x y →
    abstractTransportEquivalent y x

  abstractTransportTrans :
    {region : AQFT.Region} →
    {x y z : abstractRestrictedCarrier region} →
    abstractTransportEquivalent x y →
    abstractTransportEquivalent y z →
    abstractTransportEquivalent x z

  abstractPromotedReceipt :
    {region : AQFT.Region} →
    abstractRestrictedCarrier region →
    Set

  abstractPromotedReceiptTransport :
    {region : AQFT.Region} →
    {x y : abstractRestrictedCarrier region} →
    abstractTransportEquivalent x y →
    abstractPromotedReceipt x →
    abstractPromotedReceipt y

  abstractPromotedReceiptQuotient :
    AQFT.Region →
    Set

  abstractQuotientIntro :
    {region : AQFT.Region} →
    (x : abstractRestrictedCarrier region) →
    abstractPromotedReceipt x →
    abstractPromotedReceiptQuotient region

  abstractQuotientTransportStable :
    {region : AQFT.Region} →
    {x y : abstractRestrictedCarrier region} →
    (eq : abstractTransportEquivalent x y) →
    (receipt : abstractPromotedReceipt x) →
    abstractQuotientIntro x receipt
    ≡
    abstractQuotientIntro
      y
      (abstractPromotedReceiptTransport eq receipt)

  abstractLocalAlgebraIsPromotedReceiptQuotient :
    (region : AQFT.Region) →
    AQFT.AQFTTypedNetSurface.Algebra
      AQFT.canonicalAQFTTypedNetSurface
      region
    ≡
    abstractPromotedReceiptQuotient region

canonicalAQFTCarrierAlgebraQuotientSurface :
  AQFTCarrierAlgebraQuotientSurface
canonicalAQFTCarrierAlgebraQuotientSurface =
  record
    { status =
        quotientSurfaceOnlyNoAQFTPromotion
    ; typedNetSurface =
        AQFT.canonicalAQFTTypedNetSurface
    ; RestrictedCarrier =
        abstractRestrictedCarrier
    ; TransportEquivalent =
        abstractTransportEquivalent
    ; transportRefl =
        abstractTransportRefl
    ; transportSym =
        abstractTransportSym
    ; transportTrans =
        abstractTransportTrans
    ; PromotedReceipt =
        abstractPromotedReceipt
    ; promotedReceiptTransport =
        abstractPromotedReceiptTransport
    ; PromotedReceiptQuotient =
        abstractPromotedReceiptQuotient
    ; quotientIntro =
        abstractQuotientIntro
    ; quotientTransportStable =
        abstractQuotientTransportStable
    ; localAlgebraIsPromotedReceiptQuotient =
        abstractLocalAlgebraIsPromotedReceiptQuotient
    ; openObligations =
        missingRestrictedCarrier
        ∷ missingTransportEquivalenceLaws
        ∷ missingPromotedReceiptPredicate
        ∷ missingQuotientConstruction
        ∷ missingAlgebraOperationsOnQuotient
        ∷ missingIsotonyFromCarrierTransport
        ∷ []
    ; aqftPromoted =
        false
    ; aqftPromotedIsFalse =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; quotientBoundary =
        "A(O) is staged as promoted receipts over the carrier restricted to O, quotiented by transport equivalence"
        ∷ "restricted carriers, transport equivalence, promoted receipts, and quotient operations are abstract here"
        ∷ "this surface does not construct a concrete C*-algebra, GNS state, Born-rule adapter, or interacting AQFT net"
        ∷ "this surface does not promote Standard Model, stress-energy, GRQFT, or full unification claims"
        ∷ []
    }
