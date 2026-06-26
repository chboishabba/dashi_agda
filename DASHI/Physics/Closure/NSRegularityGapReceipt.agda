module DASHI.Physics.Closure.NSRegularityGapReceipt where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ClayMillenniumClosureTargetReceipt as Clay
import DASHI.Physics.Closure.NavierStokesRegularityTowerReceipt as Tower

data NSRegularityGapStatus : Set where
  finiteDepthControlsRecordedContinuumRegularityOpen :
    NSRegularityGapStatus

data NSRegularityGapItem : Set where
  explicitCandidatePacketRecorded :
    NSRegularityGapItem
  cknEssLrtSpineRecorded :
    NSRegularityGapItem
  a1A3A4A5A9BridgeRecorded :
    NSRegularityGapItem
  theoremShapeGrammarGapClosed :
    NSRegularityGapItem
  missingPromotionEvidence :
    NSRegularityGapItem
  missingRefereeGradeAcceptance :
    NSRegularityGapItem
  finiteDepthVorticityEquation :
    NSRegularityGapItem
  missingUniformBKMControl :
    NSRegularityGapItem
  missingContinuumSmoothRegularity :
    NSRegularityGapItem

canonicalNSRegularityGapItems :
  List NSRegularityGapItem
canonicalNSRegularityGapItems =
  explicitCandidatePacketRecorded
  ∷ cknEssLrtSpineRecorded
  ∷ a1A3A4A5A9BridgeRecorded
  ∷ theoremShapeGrammarGapClosed
  ∷ missingPromotionEvidence
  ∷ missingRefereeGradeAcceptance
  ∷ finiteDepthVorticityEquation
  ∷ missingUniformBKMControl
  ∷ missingContinuumSmoothRegularity
  ∷ []

nsRegularityGapStatement : String
nsRegularityGapStatement =
  "The explicit candidate self-contained NS packet around CKN, ESS, LRT, A1/A3, A4, and A5-A9 is recorded, so theorem-shape grammar is not the live gap. The remaining fail-closed burden is promotion evidence, referee-grade acceptance, finite-depth-to-continuum vorticity/BKM closure, global smooth regularity, and Clay closure."

record NSRegularityGapReceipt : Setω where
  field
    status :
      NSRegularityGapStatus

    regularityTower :
      Tower.NavierStokesRegularityTowerReceipt

    towerContinuumLiftFalse :
      Tower.continuumRegularityLiftConstructed regularityTower ≡ false

    towerClayFalse :
      Tower.continuumClayNavierStokesPromoted regularityTower ≡ false

    clayTargetReceipt :
      Clay.CarrierBKMControlTargetReceipt

    uniformVorticityControlFalse :
      Clay.uniformVorticityLInfinityControlConstructed
        clayTargetReceipt
      ≡
      false

    continuumBKMRegularityPassageFalse :
      Clay.continuumBKMRegularityPassageConstructed
        clayTargetReceipt
      ≡
      false

    gapItems :
      List NSRegularityGapItem

    gapItemsAreCanonical :
      gapItems ≡ canonicalNSRegularityGapItems

    candidateSelfContainedPacketRecorded :
      Bool

    candidateSelfContainedPacketRecordedIsTrue :
      candidateSelfContainedPacketRecorded ≡ true

    theoremShapeGrammarGapClosedFlag :
      Bool

    theoremShapeGrammarGapClosedFlagIsTrue :
      theoremShapeGrammarGapClosedFlag ≡ true

    promotionEvidenceOutstanding :
      Bool

    promotionEvidenceOutstandingIsTrue :
      promotionEvidenceOutstanding ≡ true

    refereeGradeAcceptanceOutstanding :
      Bool

    refereeGradeAcceptanceOutstandingIsTrue :
      refereeGradeAcceptanceOutstanding ≡ true

    energyRungRecorded :
      Bool

    energyRungRecordedIsTrue :
      energyRungRecorded ≡ true

    vorticityRungRecorded :
      Bool

    vorticityRungRecordedIsTrue :
      vorticityRungRecorded ≡ true

    bkmRungRecorded :
      Bool

    bkmRungRecordedIsTrue :
      bkmRungRecorded ≡ true

    finiteDepthRegularityRungsRecorded :
      Bool

    finiteDepthRegularityRungsRecordedIsTrue :
      finiteDepthRegularityRungsRecorded ≡ true

    globalSmoothRegularityProved :
      Bool

    globalSmoothRegularityProvedIsFalse :
      globalSmoothRegularityProved ≡ true

    bkmVorticityControlClosed :
      Bool

    bkmVorticityControlClosedIsFalse :
      bkmVorticityControlClosed ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsRegularityGapStatement

    receiptBoundary :
      List String

open NSRegularityGapReceipt public

canonicalNSRegularityGapReceipt :
  NSRegularityGapReceipt
canonicalNSRegularityGapReceipt =
  record
    { status =
        finiteDepthControlsRecordedContinuumRegularityOpen
    ; regularityTower =
        Tower.canonicalNavierStokesRegularityTowerReceipt
    ; towerContinuumLiftFalse =
        refl
    ; towerClayFalse =
        refl
    ; clayTargetReceipt =
        Clay.canonicalCarrierBKMControlTargetReceipt
    ; uniformVorticityControlFalse =
        refl
    ; continuumBKMRegularityPassageFalse =
        refl
    ; gapItems =
        canonicalNSRegularityGapItems
    ; gapItemsAreCanonical =
        refl
    ; candidateSelfContainedPacketRecorded =
        true
    ; candidateSelfContainedPacketRecordedIsTrue =
        refl
    ; theoremShapeGrammarGapClosedFlag =
        true
    ; theoremShapeGrammarGapClosedFlagIsTrue =
        refl
    ; promotionEvidenceOutstanding =
        true
    ; promotionEvidenceOutstandingIsTrue =
        refl
    ; refereeGradeAcceptanceOutstanding =
        true
    ; refereeGradeAcceptanceOutstandingIsTrue =
        refl
    ; energyRungRecorded =
        true
    ; energyRungRecordedIsTrue =
        refl
    ; vorticityRungRecorded =
        true
    ; vorticityRungRecordedIsTrue =
        refl
    ; bkmRungRecorded =
        true
    ; bkmRungRecordedIsTrue =
        refl
    ; finiteDepthRegularityRungsRecorded =
        true
    ; finiteDepthRegularityRungsRecordedIsTrue =
        refl
    ; globalSmoothRegularityProved =
        true
    ; globalSmoothRegularityProvedIsFalse =
        refl
    ; bkmVorticityControlClosed =
        false
    ; bkmVorticityControlClosedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; statement =
        nsRegularityGapStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "The candidate self-contained packet is recorded around CKN, ESS, LRT, A1/A3, A4, and A5-A9"
        ∷ "Theorem-shape grammar is treated as present rather than as the live NS gap"
        ∷ "Promotion evidence and referee-grade acceptance remain outstanding"
        ∷ "Uniform vorticity Linfinity control, continuum BKM passage, and global smooth regularity remain false"
        ∷ "Clay Navier-Stokes promotion remains false"
        ∷ []
    }

nsRegularityGapKeepsClayFalse :
  clayNavierStokesPromoted canonicalNSRegularityGapReceipt ≡ false
nsRegularityGapKeepsClayFalse =
  refl
