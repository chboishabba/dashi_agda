module DASHI.Physics.Closure.WilsonActionOn3PlusOneLatticeReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.SpacetimeLatticeFromCarrierDepthReceipt as Space

data WilsonActionOn3PlusOneLatticeStatus : Set where
  wilsonActionCarrierLatticeRecordedNoClayPromotion :
    WilsonActionOn3PlusOneLatticeStatus

data WilsonPlaquetteKind : Set where
  spatialTrianglePlaquette :
    WilsonPlaquetteKind

  spatialTemporalSquarePlaquette :
    WilsonPlaquetteKind

canonicalWilsonPlaquetteKinds : List WilsonPlaquetteKind
canonicalWilsonPlaquetteKinds =
  spatialTrianglePlaquette
  ∷ spatialTemporalSquarePlaquette
  ∷ []

data WilsonActionBlocker : Set where
  missingGaugeGroupRepresentation :
    WilsonActionBlocker

  missingHaarMeasureAndPartitionFunction :
    WilsonActionBlocker

  missingReflectionPositivityProof :
    WilsonActionBlocker

  missingUniformMassGapEstimate :
    WilsonActionBlocker

  missingContinuumWightmanReconstruction :
    WilsonActionBlocker

canonicalWilsonActionBlockers :
  List WilsonActionBlocker
canonicalWilsonActionBlockers =
  missingGaugeGroupRepresentation
  ∷ missingHaarMeasureAndPartitionFunction
  ∷ missingReflectionPositivityProof
  ∷ missingUniformMassGapEstimate
  ∷ missingContinuumWightmanReconstruction
  ∷ []

data WilsonActionPromotion : Set where

wilsonActionPromotionImpossibleHere :
  WilsonActionPromotion →
  ⊥
wilsonActionPromotionImpossibleHere ()

spatialTemporalPlaquetteLabel : String
spatialTemporalPlaquetteLabel =
  "U_ij(d) U_j(d,d+1) U_ij(d+1)^dagger U_i(d,d+1)^dagger"

record WilsonActionOn3PlusOneLatticeReceipt : Setω where
  field
    status :
      WilsonActionOn3PlusOneLatticeStatus

    spacetimeReceipt :
      Space.SpacetimeLatticeFromCarrierDepthReceipt

    depthTimeCandidate :
      Space.euclideanTimeFromDepth spacetimeReceipt ≡ true

    spatialPlaquetteRecorded :
      Bool

    spatialPlaquetteRecordedIsTrue :
      spatialPlaquetteRecorded ≡ true

    temporalPlaquetteLabel :
      String

    temporalPlaquetteLabelIsCanonical :
      temporalPlaquetteLabel ≡ spatialTemporalPlaquetteLabel

    wilsonActionDefinedOnCarrierLattice :
      Bool

    wilsonActionDefinedOnCarrierLatticeIsTrue :
      wilsonActionDefinedOnCarrierLattice ≡ true

    continuumWilsonMeasureConstructed :
      Bool

    continuumWilsonMeasureConstructedIsFalse :
      continuumWilsonMeasureConstructed ≡ false

    plaquetteKinds :
      List WilsonPlaquetteKind

    plaquetteKindsAreCanonical :
      plaquetteKinds ≡ canonicalWilsonPlaquetteKinds

    reflectionPositivityProved :
      Bool

    reflectionPositivityProvedIsFalse :
      reflectionPositivityProved ≡ false

    uniformMassGapProved :
      Bool

    uniformMassGapProvedIsFalse :
      uniformMassGapProved ≡ false

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
      List WilsonActionBlocker

    blockersAreCanonical :
      blockers ≡ canonicalWilsonActionBlockers

    promotionFlags :
      List WilsonActionPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open WilsonActionOn3PlusOneLatticeReceipt public

canonicalWilsonActionOn3PlusOneLatticeReceipt :
  WilsonActionOn3PlusOneLatticeReceipt
canonicalWilsonActionOn3PlusOneLatticeReceipt =
  record
    { status =
        wilsonActionCarrierLatticeRecordedNoClayPromotion
    ; spacetimeReceipt =
        Space.canonicalSpacetimeLatticeFromCarrierDepthReceipt
    ; depthTimeCandidate =
        refl
    ; spatialPlaquetteRecorded =
        true
    ; spatialPlaquetteRecordedIsTrue =
        refl
    ; temporalPlaquetteLabel =
        spatialTemporalPlaquetteLabel
    ; temporalPlaquetteLabelIsCanonical =
        refl
    ; wilsonActionDefinedOnCarrierLattice =
        true
    ; wilsonActionDefinedOnCarrierLatticeIsTrue =
        refl
    ; continuumWilsonMeasureConstructed =
        false
    ; continuumWilsonMeasureConstructedIsFalse =
        refl
    ; plaquetteKinds =
        canonicalWilsonPlaquetteKinds
    ; plaquetteKindsAreCanonical =
        refl
    ; reflectionPositivityProved =
        false
    ; reflectionPositivityProvedIsFalse =
        refl
    ; uniformMassGapProved =
        false
    ; uniformMassGapProvedIsFalse =
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
        canonicalWilsonActionBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "B3 records spatial and temporal plaquette targets for a Wilson action on the candidate 3+1 carrier lattice"
        ∷ "Measure construction, reflection positivity, uniform mass gap, and continuum reconstruction remain blockers"
        ∷ "No Clay Yang-Mills or terminal Clay claim is promoted"
        ∷ []
    }

wilsonActionOn3PlusOneLatticeDoesNotPromoteClay :
  clayYangMillsPromoted canonicalWilsonActionOn3PlusOneLatticeReceipt
  ≡
  false
wilsonActionOn3PlusOneLatticeDoesNotPromoteClay =
  refl
