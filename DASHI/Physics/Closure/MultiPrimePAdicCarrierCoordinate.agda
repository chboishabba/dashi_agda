module DASHI.Physics.Closure.MultiPrimePAdicCarrierCoordinate where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

open import MonsterOntos using
  ( SSP
  ; p2
  ; p3
  ; p5
  ; p7
  ; p11
  ; p13
  ; p17
  ; p19
  ; p23
  ; p29
  ; p31
  ; p41
  ; p47
  ; p59
  ; p71
  )
import Ontology.GodelLattice as GL

------------------------------------------------------------------------
-- Vec15 adelic tuple carrier coordinate receipt.
--
-- This module records the fifteen prime-lane / p-adic coordinates as a
-- carrier tuple only.  It deliberately does not promote the tuple to an
-- analytic adele ring, a global field construction, or a physics closure.

data PAdicCoordinateStatus : Set where
  formalPrimeLaneCoordinate :
    PAdicCoordinateStatus

  pAdicCompletionNotConstructed :
    PAdicCoordinateStatus

  adelicProductLawNotConstructed :
    PAdicCoordinateStatus

canonicalPAdicCoordinateStatus : List PAdicCoordinateStatus
canonicalPAdicCoordinateStatus =
  formalPrimeLaneCoordinate
  ∷ pAdicCompletionNotConstructed
  ∷ adelicProductLawNotConstructed
  ∷ []

record PAdicCarrierCoordinate : Set where
  field
    coordinatePrime :
      SSP

    coordinateOrdinal :
      Nat

    coordinateLabel :
      String

    coordinateRole :
      String

    valuationExponent :
      Nat

    residuePlaceholder :
      String

    coordinateStatus :
      List PAdicCoordinateStatus

    coordinateStatusIsCanonical :
      coordinateStatus ≡ canonicalPAdicCoordinateStatus

    analyticPAdicFieldConstructed :
      Bool

    analyticPAdicFieldConstructedIsFalse :
      analyticPAdicFieldConstructed ≡ false

    pAdicNormConstructed :
      Bool

    pAdicNormConstructedIsFalse :
      pAdicNormConstructed ≡ false

open PAdicCarrierCoordinate public

mkFormalPAdicCoordinate :
  SSP →
  Nat →
  String →
  PAdicCarrierCoordinate
mkFormalPAdicCoordinate p ordinal label =
  record
    { coordinatePrime =
        p
    ; coordinateOrdinal =
        ordinal
    ; coordinateLabel =
        label
    ; coordinateRole =
        "formal p-adic prime-lane coordinate in the Vec15 adelic carrier tuple"
    ; valuationExponent =
        0
    ; residuePlaceholder =
        "residue data intentionally not supplied by this carrier receipt"
    ; coordinateStatus =
        canonicalPAdicCoordinateStatus
    ; coordinateStatusIsCanonical =
        refl
    ; analyticPAdicFieldConstructed =
        false
    ; analyticPAdicFieldConstructedIsFalse =
        refl
    ; pAdicNormConstructed =
        false
    ; pAdicNormConstructedIsFalse =
        refl
    }

Vec15PAdicCarrierTuple : Set
Vec15PAdicCarrierTuple =
  GL.Vec15 PAdicCarrierCoordinate

canonicalVec15PAdicCarrierTuple :
  Vec15PAdicCarrierTuple
canonicalVec15PAdicCarrierTuple =
  GL.v15
    (mkFormalPAdicCoordinate p2 0 "p2")
    (mkFormalPAdicCoordinate p3 1 "p3")
    (mkFormalPAdicCoordinate p5 2 "p5")
    (mkFormalPAdicCoordinate p7 3 "p7")
    (mkFormalPAdicCoordinate p11 4 "p11")
    (mkFormalPAdicCoordinate p13 5 "p13")
    (mkFormalPAdicCoordinate p17 6 "p17")
    (mkFormalPAdicCoordinate p19 7 "p19")
    (mkFormalPAdicCoordinate p23 8 "p23")
    (mkFormalPAdicCoordinate p29 9 "p29")
    (mkFormalPAdicCoordinate p31 10 "p31")
    (mkFormalPAdicCoordinate p41 11 "p41")
    (mkFormalPAdicCoordinate p47 12 "p47")
    (mkFormalPAdicCoordinate p59 13 "p59")
    (mkFormalPAdicCoordinate p71 14 "p71")

canonicalVec15PAdicCarrierExponentSkeleton :
  GL.FactorVec
canonicalVec15PAdicCarrierExponentSkeleton =
  GL.v15
    0 0 0 0 0
    0 0 0 0 0
    0 0 0 0 0

record Vec15PAdicCarrierMetadata : Set where
  field
    carrierName :
      String

    tupleArity :
      Nat

    primeLaneCount :
      Nat

    coordinateTuple :
      Vec15PAdicCarrierTuple

    exponentSkeleton :
      GL.FactorVec

    metadataBoundary :
      List String

open Vec15PAdicCarrierMetadata public

canonicalVec15PAdicCarrierMetadata :
  Vec15PAdicCarrierMetadata
canonicalVec15PAdicCarrierMetadata =
  record
    { carrierName =
        "Vec15 multi-prime p-adic carrier coordinate tuple"
    ; tupleArity =
        15
    ; primeLaneCount =
        15
    ; coordinateTuple =
        canonicalVec15PAdicCarrierTuple
    ; exponentSkeleton =
        canonicalVec15PAdicCarrierExponentSkeleton
    ; metadataBoundary =
        "fifteen coordinates are indexed by the supersingular prime lane order"
        ∷ "the tuple is carrier metadata, not an analytic adelic object"
        ∷ "all valuation exponents are neutral placeholders until supplied by a separate witness"
        ∷ []
    }

record Vec15NonPromotionFlags : Set where
  field
    promotesToAnalyticPAdicFields :
      Bool

    promotesToAnalyticPAdicFieldsIsFalse :
      promotesToAnalyticPAdicFields ≡ false

    promotesToAdeleRing :
      Bool

    promotesToAdeleRingIsFalse :
      promotesToAdeleRing ≡ false

    promotesToGlobalField :
      Bool

    promotesToGlobalFieldIsFalse :
      promotesToGlobalField ≡ false

    promotesToProductFormula :
      Bool

    promotesToProductFormulaIsFalse :
      promotesToProductFormula ≡ false

    promotesToPhysicsClosure :
      Bool

    promotesToPhysicsClosureIsFalse :
      promotesToPhysicsClosure ≡ false

open Vec15NonPromotionFlags public

canonicalVec15NonPromotionFlags :
  Vec15NonPromotionFlags
canonicalVec15NonPromotionFlags =
  record
    { promotesToAnalyticPAdicFields =
        false
    ; promotesToAnalyticPAdicFieldsIsFalse =
        refl
    ; promotesToAdeleRing =
        false
    ; promotesToAdeleRingIsFalse =
        refl
    ; promotesToGlobalField =
        false
    ; promotesToGlobalFieldIsFalse =
        refl
    ; promotesToProductFormula =
        false
    ; promotesToProductFormulaIsFalse =
        refl
    ; promotesToPhysicsClosure =
        false
    ; promotesToPhysicsClosureIsFalse =
        refl
    }

data Vec15PAdicCarrierPromotionReceipt : Set where

vec15PAdicCarrierPromotionImpossibleHere :
  Vec15PAdicCarrierPromotionReceipt →
  ⊥
vec15PAdicCarrierPromotionImpossibleHere ()

record Vec15PAdicCarrierCoordinateReceipt : Set where
  field
    metadata :
      Vec15PAdicCarrierMetadata

    metadataIsCanonical :
      metadata ≡ canonicalVec15PAdicCarrierMetadata

    nonPromotionFlags :
      Vec15NonPromotionFlags

    nonPromotionFlagsAreCanonical :
      nonPromotionFlags ≡ canonicalVec15NonPromotionFlags

    p2LanePrimeIsP2 :
      coordinatePrime (GL.Vec15.e2 (coordinateTuple metadata)) ≡ p2

    p3LanePrimeIsP3 :
      coordinatePrime (GL.Vec15.e3 (coordinateTuple metadata)) ≡ p3

    p5LanePrimeIsP5 :
      coordinatePrime (GL.Vec15.e5 (coordinateTuple metadata)) ≡ p5

    p7LanePrimeIsP7 :
      coordinatePrime (GL.Vec15.e7 (coordinateTuple metadata)) ≡ p7

    p11LanePrimeIsP11 :
      coordinatePrime (GL.Vec15.e11 (coordinateTuple metadata)) ≡ p11

    p13LanePrimeIsP13 :
      coordinatePrime (GL.Vec15.e13 (coordinateTuple metadata)) ≡ p13

    p17LanePrimeIsP17 :
      coordinatePrime (GL.Vec15.e17 (coordinateTuple metadata)) ≡ p17

    p19LanePrimeIsP19 :
      coordinatePrime (GL.Vec15.e19 (coordinateTuple metadata)) ≡ p19

    p23LanePrimeIsP23 :
      coordinatePrime (GL.Vec15.e23 (coordinateTuple metadata)) ≡ p23

    p29LanePrimeIsP29 :
      coordinatePrime (GL.Vec15.e29 (coordinateTuple metadata)) ≡ p29

    p31LanePrimeIsP31 :
      coordinatePrime (GL.Vec15.e31 (coordinateTuple metadata)) ≡ p31

    p41LanePrimeIsP41 :
      coordinatePrime (GL.Vec15.e41 (coordinateTuple metadata)) ≡ p41

    p47LanePrimeIsP47 :
      coordinatePrime (GL.Vec15.e47 (coordinateTuple metadata)) ≡ p47

    p59LanePrimeIsP59 :
      coordinatePrime (GL.Vec15.e59 (coordinateTuple metadata)) ≡ p59

    p71LanePrimeIsP71 :
      coordinatePrime (GL.Vec15.e71 (coordinateTuple metadata)) ≡ p71

    promotionReceipts :
      List Vec15PAdicCarrierPromotionReceipt

    promotionReceiptsAreEmpty :
      promotionReceipts ≡ []

    nonPromotionBoundary :
      List String

open Vec15PAdicCarrierCoordinateReceipt public

canonicalVec15PAdicCarrierCoordinateReceipt :
  Vec15PAdicCarrierCoordinateReceipt
canonicalVec15PAdicCarrierCoordinateReceipt =
  record
    { metadata =
        canonicalVec15PAdicCarrierMetadata
    ; metadataIsCanonical =
        refl
    ; nonPromotionFlags =
        canonicalVec15NonPromotionFlags
    ; nonPromotionFlagsAreCanonical =
        refl
    ; p2LanePrimeIsP2 =
        refl
    ; p3LanePrimeIsP3 =
        refl
    ; p5LanePrimeIsP5 =
        refl
    ; p7LanePrimeIsP7 =
        refl
    ; p11LanePrimeIsP11 =
        refl
    ; p13LanePrimeIsP13 =
        refl
    ; p17LanePrimeIsP17 =
        refl
    ; p19LanePrimeIsP19 =
        refl
    ; p23LanePrimeIsP23 =
        refl
    ; p29LanePrimeIsP29 =
        refl
    ; p31LanePrimeIsP31 =
        refl
    ; p41LanePrimeIsP41 =
        refl
    ; p47LanePrimeIsP47 =
        refl
    ; p59LanePrimeIsP59 =
        refl
    ; p71LanePrimeIsP71 =
        refl
    ; promotionReceipts =
        []
    ; promotionReceiptsAreEmpty =
        refl
    ; nonPromotionBoundary =
        "Vec15 p-adic carrier coordinates are fully enumerated"
        ∷ "no p-adic completions, norms, product formula, global field, or adele ring are constructed here"
        ∷ "the receipt is fail-closed: promotion requires an external inhabited promotion receipt"
        ∷ []
    }

vec15PAdicCarrierDoesNotPromoteToAdeleRing :
  promotesToAdeleRing
    (nonPromotionFlags canonicalVec15PAdicCarrierCoordinateReceipt)
  ≡
  false
vec15PAdicCarrierDoesNotPromoteToAdeleRing =
  refl

vec15PAdicCarrierDoesNotPromoteToPhysicsClosure :
  promotesToPhysicsClosure
    (nonPromotionFlags canonicalVec15PAdicCarrierCoordinateReceipt)
  ≡
  false
vec15PAdicCarrierDoesNotPromoteToPhysicsClosure =
  refl
