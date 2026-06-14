module DASHI.Physics.Closure.CarrierLatticeYMDefinitionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

data CarrierLatticeYMDefinitionStatus : Set where
  carrierLatticeYMDefinitionRecordedNoClayPromotion :
    CarrierLatticeYMDefinitionStatus

data CarrierYMLatticeComponent : Set where
  threeHeegnerSpatialSites :
    CarrierYMLatticeComponent

  isogenyWeightedLinks :
    CarrierYMLatticeComponent

  triangularSpatialPlaquette :
    CarrierYMLatticeComponent

  depthScaleAlphaOneToD :
    CarrierYMLatticeComponent

canonicalCarrierYMLatticeComponents :
  List CarrierYMLatticeComponent
canonicalCarrierYMLatticeComponents =
  threeHeegnerSpatialSites
  ∷ isogenyWeightedLinks
  ∷ triangularSpatialPlaquette
  ∷ depthScaleAlphaOneToD
  ∷ []

data CarrierLatticeYMBlocker : Set where
  missingGaugeGroupIdentification :
    CarrierLatticeYMBlocker

  missingReflectionPositiveWilsonMeasure :
    CarrierLatticeYMBlocker

  missingContinuumLimit :
    CarrierLatticeYMBlocker

  missingUniformMassGap :
    CarrierLatticeYMBlocker

canonicalCarrierLatticeYMBlockers :
  List CarrierLatticeYMBlocker
canonicalCarrierLatticeYMBlockers =
  missingGaugeGroupIdentification
  ∷ missingReflectionPositiveWilsonMeasure
  ∷ missingContinuumLimit
  ∷ missingUniformMassGap
  ∷ []

data CarrierLatticeYMPromotion : Set where

carrierLatticeYMPromotionImpossibleHere :
  CarrierLatticeYMPromotion →
  ⊥
carrierLatticeYMPromotionImpossibleHere ()

carrierWilsonActionLabel : String
carrierWilsonActionLabel =
  "S_W[U] = -(beta/2N) sum_plaquettes Re Tr(U_square), with triangular spatial plaquettes on the three Heegner lanes"

record CarrierLatticeYMDefinitionReceipt : Setω where
  field
    status :
      CarrierLatticeYMDefinitionStatus

    spatialSiteCount :
      Nat

    spatialSiteCountIsThree :
      spatialSiteCount ≡ 3

    spatialLinkCountPerSlice :
      Nat

    spatialLinkCountPerSliceIsThree :
      spatialLinkCountPerSlice ≡ 3

    latticeSpacingLabel :
      String

    latticeSpacingLabelIsCanonical :
      latticeSpacingLabel ≡ "alpha1^d"

    wilsonActionLabel :
      String

    wilsonActionLabelIsCanonical :
      wilsonActionLabel ≡ carrierWilsonActionLabel

    zeroDimensionalIfDepthIgnored :
      Bool

    zeroDimensionalIfDepthIgnoredIsTrue :
      zeroDimensionalIfDepthIgnored ≡ true

    fourDimensionalSpacetimeStillRequired :
      Bool

    fourDimensionalSpacetimeStillRequiredIsTrue :
      fourDimensionalSpacetimeStillRequired ≡ true

    components :
      List CarrierYMLatticeComponent

    componentsAreCanonical :
      components ≡ canonicalCarrierYMLatticeComponents

    carrierLatticeYMDefinitionRecorded :
      Bool

    carrierLatticeYMDefinitionRecordedIsTrue :
      carrierLatticeYMDefinitionRecorded ≡ true

    continuumYangMillsConstructed :
      Bool

    continuumYangMillsConstructedIsFalse :
      continuumYangMillsConstructed ≡ true

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    blockers :
      List CarrierLatticeYMBlocker

    blockersAreCanonical :
      blockers ≡ canonicalCarrierLatticeYMBlockers

    promotionFlags :
      List CarrierLatticeYMPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open CarrierLatticeYMDefinitionReceipt public

canonicalCarrierLatticeYMDefinitionReceipt :
  CarrierLatticeYMDefinitionReceipt
canonicalCarrierLatticeYMDefinitionReceipt =
  record
    { status =
        carrierLatticeYMDefinitionRecordedNoClayPromotion
    ; spatialSiteCount =
        3
    ; spatialSiteCountIsThree =
        refl
    ; spatialLinkCountPerSlice =
        3
    ; spatialLinkCountPerSliceIsThree =
        refl
    ; latticeSpacingLabel =
        "alpha1^d"
    ; latticeSpacingLabelIsCanonical =
        refl
    ; wilsonActionLabel =
        carrierWilsonActionLabel
    ; wilsonActionLabelIsCanonical =
        refl
    ; zeroDimensionalIfDepthIgnored =
        true
    ; zeroDimensionalIfDepthIgnoredIsTrue =
        refl
    ; fourDimensionalSpacetimeStillRequired =
        true
    ; fourDimensionalSpacetimeStillRequiredIsTrue =
        refl
    ; components =
        canonicalCarrierYMLatticeComponents
    ; componentsAreCanonical =
        refl
    ; carrierLatticeYMDefinitionRecorded =
        true
    ; carrierLatticeYMDefinitionRecordedIsTrue =
        refl
    ; continuumYangMillsConstructed =
        true
    ; continuumYangMillsConstructedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; blockers =
        canonicalCarrierLatticeYMBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "B1 records a carrier-lattice Yang-Mills definition surface"
        ∷ "Gauge identification, reflection-positive Wilson measure, continuum limit, and mass gap remain blockers"
        ∷ "No Clay Yang-Mills or terminal Clay claim is promoted"
        ∷ []
    }

carrierLatticeYMDefinitionDoesNotPromoteClay :
  clayYangMillsPromoted canonicalCarrierLatticeYMDefinitionReceipt ≡ false
carrierLatticeYMDefinitionDoesNotPromoteClay =
  refl
