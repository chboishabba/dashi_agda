module DASHI.Physics.Closure.YMFramingCorrectionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Geometry.CausalForcesLorentz31 as Lorentz31
import DASHI.Physics.Closure.CarrierLatticeYMDefinitionReceipt as Carrier
import DASHI.Physics.Closure.SpacetimeLatticeFromCarrierDepthReceipt as Space
import DASHI.Physics.Closure.WilsonActionOn3PlusOneLatticeReceipt as Wilson

data YMFramingCorrectionStatus : Set where
  managerCYMReframeCorrectedNoClayPromotion :
    YMFramingCorrectionStatus

data YMFramingCorrectionEstablishedItem : Set where
  carrierLorentz31SignatureRecorded :
    YMFramingCorrectionEstablishedItem

  candidateSpacetimeLatticeFromCarrierDepthRecorded :
    YMFramingCorrectionEstablishedItem

  wilsonActionOnCandidate3PlusOneLatticeRecorded :
    YMFramingCorrectionEstablishedItem

  threeHeegnerSpatialSitesRecorded :
    YMFramingCorrectionEstablishedItem

canonicalYMFramingCorrectionEstablishedItems :
  List YMFramingCorrectionEstablishedItem
canonicalYMFramingCorrectionEstablishedItems =
  carrierLorentz31SignatureRecorded
  ∷ candidateSpacetimeLatticeFromCarrierDepthRecorded
  ∷ wilsonActionOnCandidate3PlusOneLatticeRecorded
  ∷ threeHeegnerSpatialSitesRecorded
  ∷ []

data YMFramingCorrectionBlocker : Set where
  missingSpatialRefinement :
    YMFramingCorrectionBlocker

  missingUniversalityClassProof :
    YMFramingCorrectionBlocker

  missingTightnessProof :
    YMFramingCorrectionBlocker

canonicalYMFramingCorrectionBlockers :
  List YMFramingCorrectionBlocker
canonicalYMFramingCorrectionBlockers =
  missingSpatialRefinement
  ∷ missingUniversalityClassProof
  ∷ missingTightnessProof
  ∷ []

data YMFramingCorrectionPromotion : Set where

ymFramingCorrectionPromotionImpossibleHere :
  YMFramingCorrectionPromotion →
  ⊥
ymFramingCorrectionPromotionImpossibleHere ()

productLatticeRetirementStatement : String
productLatticeRetirementStatement =
  "The product lattice workaround is retired because it introduced non-carrier structure."

managerCYMFramingCorrectionStatement : String
managerCYMFramingCorrectionStatement =
  "Manager C YM reframe correction: the carrier has 3+1 Lorentz signature, the candidate spacetime lattice and Wilson action are recorded on the carrier-depth receipt chain, and the three Heegner sites remain the spatial carrier sites; spatial refinement, universality, and tightness remain open."

record YMFramingCorrectionReceipt : Setω where
  field
    status :
      YMFramingCorrectionStatus

    carrierLatticeReceipt :
      Carrier.CarrierLatticeYMDefinitionReceipt

    carrierSpatialSiteCountThree :
      Carrier.spatialSiteCount carrierLatticeReceipt ≡ 3

    spacetimeLatticeReceipt :
      Space.SpacetimeLatticeFromCarrierDepthReceipt

    spacetimeCarrierSiteCountThree :
      Carrier.spatialSiteCount
        (Space.carrierLatticeReceipt spacetimeLatticeReceipt)
      ≡ 3

    wilsonActionReceipt :
      Wilson.WilsonActionOn3PlusOneLatticeReceipt

    wilsonActionDefinedOnCarrierLattice :
      Wilson.wilsonActionDefinedOnCarrierLattice wilsonActionReceipt
      ≡ true

    lorentz31GeometryReferenced :
      Bool

    lorentz31GeometryReferencedIsTrue :
      lorentz31GeometryReferenced ≡ true

    carrierHasLorentz31Signature :
      Bool

    carrierHasLorentz31SignatureIsTrue :
      carrierHasLorentz31Signature ≡ true

    candidate3PlusOneSpacetimeLattice :
      Bool

    candidate3PlusOneSpacetimeLatticeIsTrue :
      candidate3PlusOneSpacetimeLattice ≡ true

    wilsonActionRecorded :
      Bool

    wilsonActionRecordedIsTrue :
      wilsonActionRecorded ≡ true

    threeHeegnerSpatialSites :
      Bool

    threeHeegnerSpatialSitesIsTrue :
      threeHeegnerSpatialSites ≡ true

    establishedItems :
      List YMFramingCorrectionEstablishedItem

    establishedItemsAreCanonical :
      establishedItems ≡ canonicalYMFramingCorrectionEstablishedItems

    spatialRefinementConstructed :
      Bool

    spatialRefinementConstructedIsFalse :
      spatialRefinementConstructed ≡ false

    universalityClassProofConstructed :
      Bool

    universalityClassProofConstructedIsFalse :
      universalityClassProofConstructed ≡ false

    tightnessProofConstructed :
      Bool

    tightnessProofConstructedIsFalse :
      tightnessProofConstructed ≡ false

    productLatticeWorkaroundRetired :
      Bool

    productLatticeWorkaroundRetiredIsTrue :
      productLatticeWorkaroundRetired ≡ true

    productLatticeRetiredBecauseNonCarrierStructure :
      Bool

    productLatticeRetiredBecauseNonCarrierStructureIsTrue :
      productLatticeRetiredBecauseNonCarrierStructure ≡ true

    productLatticeRetirementReason :
      String

    productLatticeRetirementReasonIsCanonical :
      productLatticeRetirementReason
      ≡ productLatticeRetirementStatement

    blockers :
      List YMFramingCorrectionBlocker

    blockersAreCanonical :
      blockers ≡ canonicalYMFramingCorrectionBlockers

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

    correctionStatement :
      String

    correctionStatementIsCanonical :
      correctionStatement ≡ managerCYMFramingCorrectionStatement

    promotionFlags :
      List YMFramingCorrectionPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open YMFramingCorrectionReceipt public

canonicalYMFramingCorrectionReceipt :
  YMFramingCorrectionReceipt
canonicalYMFramingCorrectionReceipt =
  let _ = Lorentz31.admissible31 in
  record
    { status =
        managerCYMReframeCorrectedNoClayPromotion
    ; carrierLatticeReceipt =
        Carrier.canonicalCarrierLatticeYMDefinitionReceipt
    ; carrierSpatialSiteCountThree =
        refl
    ; spacetimeLatticeReceipt =
        Space.canonicalSpacetimeLatticeFromCarrierDepthReceipt
    ; spacetimeCarrierSiteCountThree =
        refl
    ; wilsonActionReceipt =
        Wilson.canonicalWilsonActionOn3PlusOneLatticeReceipt
    ; wilsonActionDefinedOnCarrierLattice =
        refl
    ; lorentz31GeometryReferenced =
        true
    ; lorentz31GeometryReferencedIsTrue =
        refl
    ; carrierHasLorentz31Signature =
        true
    ; carrierHasLorentz31SignatureIsTrue =
        refl
    ; candidate3PlusOneSpacetimeLattice =
        true
    ; candidate3PlusOneSpacetimeLatticeIsTrue =
        refl
    ; wilsonActionRecorded =
        true
    ; wilsonActionRecordedIsTrue =
        refl
    ; threeHeegnerSpatialSites =
        true
    ; threeHeegnerSpatialSitesIsTrue =
        refl
    ; establishedItems =
        canonicalYMFramingCorrectionEstablishedItems
    ; establishedItemsAreCanonical =
        refl
    ; spatialRefinementConstructed =
        false
    ; spatialRefinementConstructedIsFalse =
        refl
    ; universalityClassProofConstructed =
        false
    ; universalityClassProofConstructedIsFalse =
        refl
    ; tightnessProofConstructed =
        false
    ; tightnessProofConstructedIsFalse =
        refl
    ; productLatticeWorkaroundRetired =
        true
    ; productLatticeWorkaroundRetiredIsTrue =
        refl
    ; productLatticeRetiredBecauseNonCarrierStructure =
        true
    ; productLatticeRetiredBecauseNonCarrierStructureIsTrue =
        refl
    ; productLatticeRetirementReason =
        productLatticeRetirementStatement
    ; productLatticeRetirementReasonIsCanonical =
        refl
    ; blockers =
        canonicalYMFramingCorrectionBlockers
    ; blockersAreCanonical =
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
    ; correctionStatement =
        managerCYMFramingCorrectionStatement
    ; correctionStatementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Corrects Manager C's YM reframe to keep the carrier 3+1 Lorentz framing"
        ∷ "Uses the carrier-depth spacetime lattice receipt, Wilson 3+1 lattice receipt, and three Heegner spatial carrier sites"
        ∷ "Spatial refinement, universality class proof, and tightness proof remain missing"
        ∷ "The product lattice workaround is retired because it introduced non-carrier structure"
        ∷ "No Clay Yang-Mills or terminal Clay claim is promoted"
        ∷ []
    }

ymFramingCorrectionDoesNotPromoteClay :
  clayYangMillsPromoted canonicalYMFramingCorrectionReceipt
  ≡
  false
ymFramingCorrectionDoesNotPromoteClay =
  refl
