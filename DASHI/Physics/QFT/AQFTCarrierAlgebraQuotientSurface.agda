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

  missingCauchyEvolutionReceipt :
    AQFTCarrierAlgebraQuotientOpenObligation

  missingDepthFilteredColimitAlgebra :
    AQFTCarrierAlgebraQuotientOpenObligation

data AQFTCarrierAlgebraPromotionAuthorityToken : Set where

data CauchyEvolutionStatus : Set where
  cauchyEvolutionTargetOnlyNoTimeSliceProof :
    CauchyEvolutionStatus

data CauchyEvolutionOpenObligation : Set where
  missingCarrierDataOnCauchySurface :
    CauchyEvolutionOpenObligation

  missingCarrierEvolutionMap :
    CauchyEvolutionOpenObligation

  missingEvolutionDeterminesRegion :
    CauchyEvolutionOpenObligation

  missingTimeSliceMorphismFromEvolution :
    CauchyEvolutionOpenObligation

canonicalCauchyEvolutionOpenObligations :
  List CauchyEvolutionOpenObligation
canonicalCauchyEvolutionOpenObligations =
  missingCarrierDataOnCauchySurface
  ∷ missingCarrierEvolutionMap
  ∷ missingEvolutionDeterminesRegion
  ∷ missingTimeSliceMorphismFromEvolution
  ∷ []

data CauchyEvolutionPromotionAuthorityToken : Set where

data DepthFilteredAlgebraStatus : Set where
  depthFilteredColimitTargetOnlyNoCStarConstruction :
    DepthFilteredAlgebraStatus

data DepthFilteredAlgebraOpenObligation : Set where
  missingDepthOrder :
    DepthFilteredAlgebraOpenObligation

  missingDepthIndexedLocalAlgebras :
    DepthFilteredAlgebraOpenObligation

  missingDepthRefinementMorphisms :
    DepthFilteredAlgebraOpenObligation

  missingFilteredColimitConstruction :
    DepthFilteredAlgebraOpenObligation

  missingColimitAlgebraOperations :
    DepthFilteredAlgebraOpenObligation

  missingColimitMatchesAQFTLocalAlgebra :
    DepthFilteredAlgebraOpenObligation

canonicalDepthFilteredAlgebraOpenObligations :
  List DepthFilteredAlgebraOpenObligation
canonicalDepthFilteredAlgebraOpenObligations =
  missingDepthOrder
  ∷ missingDepthIndexedLocalAlgebras
  ∷ missingDepthRefinementMorphisms
  ∷ missingFilteredColimitConstruction
  ∷ missingColimitAlgebraOperations
  ∷ missingColimitMatchesAQFTLocalAlgebra
  ∷ []

data DepthFilteredAlgebraPromotionAuthorityToken : Set where

record DepthFilteredLocalAlgebraSurface : Setω where
  field
    status :
      DepthFilteredAlgebraStatus

    typedNetSurface :
      AQFT.AQFTTypedNetSurface

    Depth :
      Set

    _≤Depth_ :
      Depth →
      Depth →
      Set

    A_d :
      Depth →
      AQFT.Region →
      Set

    depthMap :
      {d e : Depth} →
      d ≤Depth e →
      {region : AQFT.Region} →
      A_d d region →
      A_d e region

    A_colim :
      AQFT.Region →
      Set

    colimIntro :
      (d : Depth) →
      {region : AQFT.Region} →
      A_d d region →
      A_colim region

    colimIdentifiesDepthMap :
      {d e : Depth} →
      (d≤e : d ≤Depth e) →
      {region : AQFT.Region} →
      (x : A_d d region) →
      colimIntro e (depthMap d≤e x)
      ≡
      colimIntro d x

    colimMatchesLocalAlgebra :
      (region : AQFT.Region) →
      AQFT.AQFTTypedNetSurface.Algebra typedNetSurface region
      ≡
      A_colim region

    openDepthFilteredAlgebraObligations :
      List DepthFilteredAlgebraOpenObligation

    openDepthFilteredAlgebraObligationsAreCanonical :
      openDepthFilteredAlgebraObligations
      ≡
      canonicalDepthFilteredAlgebraOpenObligations

    cstarConstructionPromoted :
      Bool

    cstarConstructionPromotedIsFalse :
      cstarConstructionPromoted ≡ false

    noDepthColimitPromotionWithoutAuthority :
      DepthFilteredAlgebraPromotionAuthorityToken →
      ⊥

    depthFilteredBoundary :
      List String

open DepthFilteredLocalAlgebraSurface public

record CauchyEvolutionReceiptTarget : Setω where
  field
    status :
      CauchyEvolutionStatus

    typedNetSurface :
      AQFT.AQFTTypedNetSurface

    CauchyCarrierData :
      AQFT.Region →
      Set

    cauchyEvolution :
      {source target : AQFT.Region} →
      AQFT.TimeSliceCover source target →
      CauchyCarrierData source →
      CauchyCarrierData target

    evolutionDeterminesTarget :
      {source target : AQFT.Region} →
      AQFT.TimeSliceCover source target →
      CauchyCarrierData source →
      Set

    timeSliceMorphismFromEvolution :
      {source target : AQFT.Region} →
      AQFT.TimeSliceCover source target →
      AQFT.AlgebraMorphism source target

    openCauchyEvolutionObligations :
      List CauchyEvolutionOpenObligation

    openCauchyEvolutionObligationsAreCanonical :
      openCauchyEvolutionObligations
      ≡
      canonicalCauchyEvolutionOpenObligations

    timeSlicePromoted :
      Bool

    timeSlicePromotedIsFalse :
      timeSlicePromoted ≡ false

    noTimeSlicePromotionWithoutAuthority :
      CauchyEvolutionPromotionAuthorityToken →
      ⊥

    cauchyEvolutionBoundary :
      List String

open CauchyEvolutionReceiptTarget public

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

  abstractDepth :
    Set

  abstractDepthOrder :
    abstractDepth →
    abstractDepth →
    Set

  abstractDepthLocalAlgebra :
    abstractDepth →
    AQFT.Region →
    Set

  abstractDepthMap :
    {d e : abstractDepth} →
    abstractDepthOrder d e →
    {region : AQFT.Region} →
    abstractDepthLocalAlgebra d region →
    abstractDepthLocalAlgebra e region

  abstractDepthColimit :
    AQFT.Region →
    Set

  abstractDepthColimitIntro :
    (d : abstractDepth) →
    {region : AQFT.Region} →
    abstractDepthLocalAlgebra d region →
    abstractDepthColimit region

  abstractDepthColimitIdentifiesDepthMap :
    {d e : abstractDepth} →
    (d≤e : abstractDepthOrder d e) →
    {region : AQFT.Region} →
    (x : abstractDepthLocalAlgebra d region) →
    abstractDepthColimitIntro e (abstractDepthMap d≤e x)
    ≡
    abstractDepthColimitIntro d x

  abstractDepthColimitMatchesLocalAlgebra :
    (region : AQFT.Region) →
    AQFT.AQFTTypedNetSurface.Algebra
      AQFT.canonicalAQFTTypedNetSurface
      region
    ≡
    abstractDepthColimit region

  abstractCauchyCarrierData :
    AQFT.Region →
    Set

  abstractCauchyEvolution :
    {source target : AQFT.Region} →
    AQFT.TimeSliceCover source target →
    abstractCauchyCarrierData source →
    abstractCauchyCarrierData target

  abstractEvolutionDeterminesTarget :
    {source target : AQFT.Region} →
    AQFT.TimeSliceCover source target →
    abstractCauchyCarrierData source →
    Set

  abstractTimeSliceMorphismFromEvolution :
    {source target : AQFT.Region} →
    AQFT.TimeSliceCover source target →
    AQFT.AlgebraMorphism source target

canonicalCauchyEvolutionReceiptTarget :
  CauchyEvolutionReceiptTarget
canonicalCauchyEvolutionReceiptTarget =
  record
    { status =
        cauchyEvolutionTargetOnlyNoTimeSliceProof
    ; typedNetSurface =
        AQFT.canonicalAQFTTypedNetSurface
    ; CauchyCarrierData =
        abstractCauchyCarrierData
    ; cauchyEvolution =
        abstractCauchyEvolution
    ; evolutionDeterminesTarget =
        abstractEvolutionDeterminesTarget
    ; timeSliceMorphismFromEvolution =
        abstractTimeSliceMorphismFromEvolution
    ; openCauchyEvolutionObligations =
        canonicalCauchyEvolutionOpenObligations
    ; openCauchyEvolutionObligationsAreCanonical =
        refl
    ; timeSlicePromoted =
        false
    ; timeSlicePromotedIsFalse =
        refl
    ; noTimeSlicePromotionWithoutAuthority =
        λ ()
    ; cauchyEvolutionBoundary =
        "CauchyEvolutionReceiptTarget is the Paper 3a time-slice theorem target"
        ∷ "it must show carrier data on a Cauchy surface determines the target region"
        ∷ "this target does not construct a time-slice proof, interacting AQFT net, or GRQFT receipt"
        ∷ []
    }

canonicalDepthFilteredLocalAlgebraSurface :
  DepthFilteredLocalAlgebraSurface
canonicalDepthFilteredLocalAlgebraSurface =
  record
    { status =
        depthFilteredColimitTargetOnlyNoCStarConstruction
    ; typedNetSurface =
        AQFT.canonicalAQFTTypedNetSurface
    ; Depth =
        abstractDepth
    ; _≤Depth_ =
        abstractDepthOrder
    ; A_d =
        abstractDepthLocalAlgebra
    ; depthMap =
        abstractDepthMap
    ; A_colim =
        abstractDepthColimit
    ; colimIntro =
        abstractDepthColimitIntro
    ; colimIdentifiesDepthMap =
        abstractDepthColimitIdentifiesDepthMap
    ; colimMatchesLocalAlgebra =
        abstractDepthColimitMatchesLocalAlgebra
    ; openDepthFilteredAlgebraObligations =
        canonicalDepthFilteredAlgebraOpenObligations
    ; openDepthFilteredAlgebraObligationsAreCanonical =
        refl
    ; cstarConstructionPromoted =
        false
    ; cstarConstructionPromotedIsFalse =
        refl
    ; noDepthColimitPromotionWithoutAuthority =
        λ ()
    ; depthFilteredBoundary =
        "A_d(O) and colim_d A_d(O) are staged as depth-filtered local algebra targets"
        ∷ "the filtered colimit, algebra operations, C*-completion, and local-algebra equality are abstract here"
        ∷ "this surface does not construct an AF algebra, interacting AQFT net, Standard Model, or GRQFT receipt"
        ∷ []
    }

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
        ∷ missingCauchyEvolutionReceipt
        ∷ missingDepthFilteredColimitAlgebra
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
        ∷ "A_d(O) and colim_d A_d(O) remain blocked on DepthFilteredLocalAlgebraSurface"
        ∷ "time-slice remains blocked on CauchyEvolutionReceiptTarget"
        ∷ "this surface does not construct a concrete C*-algebra, GNS state, Born-rule adapter, or interacting AQFT net"
        ∷ "this surface does not promote Standard Model, stress-energy, GRQFT, or full unification claims"
        ∷ []
    }
