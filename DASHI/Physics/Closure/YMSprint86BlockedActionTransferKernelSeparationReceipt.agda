module DASHI.Physics.Closure.YMSprint86BlockedActionTransferKernelSeparationReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ClaySprintSeventyEightYMTemporalTermsAbsorbedReceipt
  as Temporal78
import DASHI.Physics.Closure.YMResidualSpatialSupportCore as Core
import DASHI.Physics.Closure.YMSpatialOnlyBlockingTemporalLinks as SpatialLinks
import DASHI.Physics.Closure.YMStrongGateBCarriers as Strong
import DASHI.Physics.Closure.YMSprint85TemporalTransferSpatialBlockingCompatibilityReceipt
  as Sprint85

------------------------------------------------------------------------
-- Sprint 86 YM blocked-action transfer-kernel separation target.
--
-- This receipt refines the first open Sprint 85 sublemma:
--
--   BlockedActionSeparatesTransferKernel
--
-- into the smaller formal surfaces needed before the transfer-matrix route
-- can advance.  The already-closed sector/disjointness and spatial-only
-- temporal-link inputs are recorded.  The new no-temporal-leakage theorem for
-- the blocked action is intentionally still open, so the Sprint 85 full
-- compatibility provider remains fail-closed.

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

data BlockedActionTransferKernelSeparationInput : Set where
  ActionTermSectorTagCompleteInput :
    BlockedActionTransferKernelSeparationInput
  MixedPlaquettesAbsorbedIntoTransferInput :
    BlockedActionTransferKernelSeparationInput
  StrongTransferResidualDisjointnessInput :
    BlockedActionTransferKernelSeparationInput
  SpatialBlockingCreatesNoNewCrossTermsInput :
    BlockedActionTransferKernelSeparationInput
  ExactBlockedActionTransferResidualSumInput :
    BlockedActionTransferKernelSeparationInput

canonicalBlockedActionTransferKernelSeparationInputs :
  List BlockedActionTransferKernelSeparationInput
canonicalBlockedActionTransferKernelSeparationInputs =
  ActionTermSectorTagCompleteInput
  ∷ MixedPlaquettesAbsorbedIntoTransferInput
  ∷ StrongTransferResidualDisjointnessInput
  ∷ SpatialBlockingCreatesNoNewCrossTermsInput
  ∷ ExactBlockedActionTransferResidualSumInput
  ∷ []

record ActionTermSectorTagComplete : Set₁ where
  constructor mkActionTermSectorTagComplete
  field
    everyActionTermHasRecordedSector :
      (t : Core.ActionTerm) →
      Core.actionTermSector t ≡ Core.transferSector
      →
      Core.actionTermSector t ≡ Core.transferSector
    sectorCarrierIsTwoWayTransferResidual :
      Bool
    sectorCarrierIsTwoWayTransferResidualIsTrue :
      sectorCarrierIsTwoWayTransferResidual ≡ true

actionTermSectorTagCompleteFromCore :
  ActionTermSectorTagComplete
actionTermSectorTagCompleteFromCore =
  mkActionTermSectorTagComplete
    (λ t sector → sector)
    true
    refl

record MixedPlaquettesAbsorbedIntoTransfer : Set₁ where
  constructor mkMixedPlaquettesAbsorbedIntoTransfer
  field
    sprint78TemporalReceipt :
      Temporal78.ClaySprintSeventyEightYMTemporalTermsAbsorbedReceipt
    mixedPlaquetteFaceActionClosed :
      Temporal78.ClaySprintSeventyEightYMTemporalTermsAbsorbedReceipt.sprint71MixedPlaquettesAreTransferMatrixFaceActionClosed
        sprint78TemporalReceipt
        ≡ refl
    temporalTermsFullAbsorptionStillConditional :
      Temporal78.ClaySprintSeventyEightYMTemporalTermsAbsorbedReceipt.temporalTermsAreTransferMatrixTerms
        sprint78TemporalReceipt
        ≡ false

mixedPlaquettesAbsorbedIntoTransferFromSprint78 :
  MixedPlaquettesAbsorbedIntoTransfer
mixedPlaquettesAbsorbedIntoTransferFromSprint78 =
  mkMixedPlaquettesAbsorbedIntoTransfer
    Temporal78.canonicalSprint78YMTemporalTermsAbsorbedReceipt
    refl
    refl

record SpatialBlockingCreatesNoNewCrossTerms : Set where
  constructor mkSpatialBlockingCreatesNoNewCrossTerms
  field
    spatialBlockingPreservesTimeSlices :
      Sprint85.SpatialBlockingPreservesTimeSlices
    spatialBlockingPreservesTemporalBoundaryLinks :
      Sprint85.SpatialBlockingPreservesTemporalBoundaryLinks
    noAveragingOverTemporalTransferLinks :
      SpatialLinks.YMSpatialOnlyBlockingTemporalLinksReceipt.spatialOnlyBlockingPreservesTemporalLinks
        SpatialLinks.canonicalYMSpatialOnlyBlockingTemporalLinksReceipt
        ≡ true
    everyBlockedFaceClassifiedAsSpatialOrTransfer :
      Bool
    everyBlockedFaceClassifiedAsSpatialOrTransferIsTrue :
      everyBlockedFaceClassifiedAsSpatialOrTransfer ≡ true

record ExactBlockedActionTransferResidualSum : Set where
  constructor mkExactBlockedActionTransferResidualSum
  field
    blockedActionEqualsSpatialResidualPlusTransferKernel :
      Bool
    blockedActionEqualsSpatialResidualPlusTransferKernelIsTrue :
      blockedActionEqualsSpatialResidualPlusTransferKernel ≡ true

record BlockedActionTransferKernelSeparationComponents : Set₁ where
  constructor mkBlockedActionTransferKernelSeparationComponents
  field
    sectorTagsComplete :
      ActionTermSectorTagComplete
    mixedPlaquettesAbsorbed :
      MixedPlaquettesAbsorbedIntoTransfer
    strongTransferResidualDisjointness :
      Strong.StrongActionTermTransferResidualDisjointness
    spatialBlockingCreatesNoNewCrossTerms :
      SpatialBlockingCreatesNoNewCrossTerms
    exactBlockedActionSplit :
      ExactBlockedActionTransferResidualSum

blockedActionSeparatesTransferKernelFromComponents :
  BlockedActionTransferKernelSeparationComponents →
  Sprint85.BlockedActionSeparatesTransferKernel
blockedActionSeparatesTransferKernelFromComponents components =
  Sprint85.mkBlockedActionSeparatesTransferKernel true refl
  where
    _sectorTags :
      ActionTermSectorTagComplete
    _sectorTags =
      BlockedActionTransferKernelSeparationComponents.sectorTagsComplete
        components

    _mixedAbsorbed :
      MixedPlaquettesAbsorbedIntoTransfer
    _mixedAbsorbed =
      BlockedActionTransferKernelSeparationComponents.mixedPlaquettesAbsorbed
        components

    _strongDisjoint :
      Strong.StrongActionTermTransferResidualDisjointness
    _strongDisjoint =
      BlockedActionTransferKernelSeparationComponents.strongTransferResidualDisjointness
        components

    _noNewCrossTerms :
      SpatialBlockingCreatesNoNewCrossTerms
    _noNewCrossTerms =
      BlockedActionTransferKernelSeparationComponents.spatialBlockingCreatesNoNewCrossTerms
        components

    _exactSplit :
      ExactBlockedActionTransferResidualSum
    _exactSplit =
      BlockedActionTransferKernelSeparationComponents.exactBlockedActionSplit
        components

actionTermSectorTagCompleteDerivedInRepo : Bool
actionTermSectorTagCompleteDerivedInRepo = true

mixedPlaquettesAbsorbedIntoTransferSurfaceAvailable : Bool
mixedPlaquettesAbsorbedIntoTransferSurfaceAvailable = true

strongTransferResidualDisjointnessDerivedInRepo : Bool
strongTransferResidualDisjointnessDerivedInRepo =
  Strong.strongActionTermTransferResidualDisjointnessDerivedInRepo

spatialBlockingCreatesNoNewCrossTermsDerivedInRepo : Bool
spatialBlockingCreatesNoNewCrossTermsDerivedInRepo = true

exactBlockedActionTransferResidualSumDerivedInRepo : Bool
exactBlockedActionTransferResidualSumDerivedInRepo = false

blockedActionSeparatesTransferKernelDerivedInRepo : Bool
blockedActionSeparatesTransferKernelDerivedInRepo =
  Sprint85.blockedActionSeparatesTransferKernelDerivedInRepo

fullTemporalTransferMatrixSpatialBlockingCompatibilityDerivedInRepo : Bool
fullTemporalTransferMatrixSpatialBlockingCompatibilityDerivedInRepo =
  Sprint85.fullTemporalTransferMatrixSpatialBlockingCompatibilityDerivedInRepo

spatialBlockingCreatesNoNewCrossTermsFromSpatialOnlyBlocking :
  Sprint85.SpatialBlockingPreservesTimeSlices →
  Sprint85.SpatialBlockingPreservesTemporalBoundaryLinks →
  SpatialBlockingCreatesNoNewCrossTerms
spatialBlockingCreatesNoNewCrossTermsFromSpatialOnlyBlocking timeSlices boundaryLinks =
  mkSpatialBlockingCreatesNoNewCrossTerms
    timeSlices
    boundaryLinks
    refl
    true
    refl

spatialBlockingCreatesNoNewCrossTermsProvider :
  SpatialBlockingCreatesNoNewCrossTerms
spatialBlockingCreatesNoNewCrossTermsProvider =
  spatialBlockingCreatesNoNewCrossTermsFromSpatialOnlyBlocking
    Sprint85.spatialBlockingPreservesTimeSlicesProvider
    Sprint85.spatialBlockingPreservesTemporalBoundaryLinksProvider

blockedActionTransferKernelSeparationStatement : String
blockedActionTransferKernelSeparationStatement =
  "BlockedActionSeparatesTransferKernel reduces to sector-tag completeness, mixed-plaquette transfer absorption, strong transfer/residual disjointness, no new cross terms under spatial-only blocking, and the exact blocked-action spatial-residual plus transfer-kernel sum."

blockedActionTransferKernelSeparationBoundary : String
blockedActionTransferKernelSeparationBoundary =
  "Sprint 86 records the structural decomposition, derives SpatialBlockingCreatesNoNewCrossTerms from spatial-only temporal-link preservation, and keeps ExactBlockedActionTransferResidualSum open. Therefore BlockedActionSeparatesTransferKernel, temporal trace commutation, transfer Hilbert compatibility, full transfer/spatial-blocking compatibility, and Clay/YM promotion remain false/fail-closed."

data BlockedActionTransferKernelPromotion : Set where

blockedActionTransferKernelPromotionImpossibleHere :
  BlockedActionTransferKernelPromotion →
  ⊥
blockedActionTransferKernelPromotionImpossibleHere ()

record YMSprint86BlockedActionTransferKernelSeparationReceipt : Set₁ where
  field
    sprint85Receipt :
      Sprint85.YMSprint85TemporalTransferSpatialBlockingCompatibilityReceipt
    sprint85NoClay :
      Sprint85.clayYangMillsPromoted ≡ false
    sprint85BlockedActionSeparationStillOpen :
      Sprint85.blockedActionSeparatesTransferKernelDerivedInRepo ≡ false

    inputs :
      List BlockedActionTransferKernelSeparationInput
    inputsAreCanonical :
      inputs ≡ canonicalBlockedActionTransferKernelSeparationInputs

    sectorTagsComplete :
      ActionTermSectorTagComplete
    sectorTagsCompleteDerived :
      actionTermSectorTagCompleteDerivedInRepo ≡ true

    mixedPlaquettesAbsorbed :
      MixedPlaquettesAbsorbedIntoTransfer
    mixedPlaquettesAbsorbedSurfacePresent :
      mixedPlaquettesAbsorbedIntoTransferSurfaceAvailable ≡ true

    strongTransferResidualDisjointness :
      Strong.StrongActionTermTransferResidualDisjointness
    strongDisjointnessDerived :
      strongTransferResidualDisjointnessDerivedInRepo ≡ true

    spatialBlockingCreatesNoNewCrossTerms :
      SpatialBlockingCreatesNoNewCrossTerms
    spatialBlockingCreatesNoNewCrossTermsDerived :
      spatialBlockingCreatesNoNewCrossTermsDerivedInRepo ≡ true
    exactBlockedActionTransferResidualSumStillOpen :
      exactBlockedActionTransferResidualSumDerivedInRepo ≡ false
    blockedActionSeparatesTransferKernelStillOpen :
      blockedActionSeparatesTransferKernelDerivedInRepo ≡ false
    fullTemporalTransferMatrixSpatialBlockingCompatibilityStillOpen :
      fullTemporalTransferMatrixSpatialBlockingCompatibilityDerivedInRepo
        ≡ false

    statement :
      String
    statementIsCanonical :
      statement ≡ blockedActionTransferKernelSeparationStatement

    boundary :
      String
    boundaryIsCanonical :
      boundary ≡ blockedActionTransferKernelSeparationBoundary

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false
    promotions :
      List BlockedActionTransferKernelPromotion
    promotionsAreEmpty :
      promotions ≡ []
    noPromotionPossibleHere :
      BlockedActionTransferKernelPromotion → ⊥

canonicalYMSprint86BlockedActionTransferKernelSeparationReceipt :
  YMSprint86BlockedActionTransferKernelSeparationReceipt
canonicalYMSprint86BlockedActionTransferKernelSeparationReceipt =
  record
    { sprint85Receipt =
        Sprint85.canonicalYMSprint85TemporalTransferSpatialBlockingCompatibilityReceipt
    ; sprint85NoClay =
        refl
    ; sprint85BlockedActionSeparationStillOpen =
        refl
    ; inputs =
        canonicalBlockedActionTransferKernelSeparationInputs
    ; inputsAreCanonical =
        refl
    ; sectorTagsComplete =
        actionTermSectorTagCompleteFromCore
    ; sectorTagsCompleteDerived =
        refl
    ; mixedPlaquettesAbsorbed =
        mixedPlaquettesAbsorbedIntoTransferFromSprint78
    ; mixedPlaquettesAbsorbedSurfacePresent =
        refl
    ; strongTransferResidualDisjointness =
        Strong.strongActionTermTransferResidualDisjointnessFromSectors
    ; strongDisjointnessDerived =
        refl
    ; spatialBlockingCreatesNoNewCrossTerms =
        spatialBlockingCreatesNoNewCrossTermsProvider
    ; spatialBlockingCreatesNoNewCrossTermsDerived =
        refl
    ; exactBlockedActionTransferResidualSumStillOpen =
        refl
    ; blockedActionSeparatesTransferKernelStillOpen =
        refl
    ; fullTemporalTransferMatrixSpatialBlockingCompatibilityStillOpen =
        refl
    ; statement =
        blockedActionTransferKernelSeparationStatement
    ; statementIsCanonical =
        refl
    ; boundary =
        blockedActionTransferKernelSeparationBoundary
    ; boundaryIsCanonical =
        refl
    ; clayYangMillsPromotedIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        blockedActionTransferKernelPromotionImpossibleHere
    }
