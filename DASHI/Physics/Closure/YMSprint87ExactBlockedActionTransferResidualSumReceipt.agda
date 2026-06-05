module DASHI.Physics.Closure.YMSprint87ExactBlockedActionTransferResidualSumReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.YMSprint86BlockedActionTransferKernelSeparationReceipt
  as Sprint86

------------------------------------------------------------------------
-- Sprint 87 YM exact blocked-action transfer/residual sum target.
--
-- Sprint 86 now derives the no-new-cross-terms receipt-level carrier from
-- spatial-only temporal-link preservation.  This receipt advances the last
-- open input for BlockedActionSeparatesTransferKernel:
--
--   ExactBlockedActionTransferResidualSum
--
-- It names the algebraic surfaces required before the exact split can be
-- inhabited.  The exact action equality is still open here.

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

data ExactBlockedActionTransferResidualSumInput : Set where
  BlockedActionTermEnumerationInput :
    ExactBlockedActionTransferResidualSumInput
  TransferKernelActionTermProjectionInput :
    ExactBlockedActionTransferResidualSumInput
  SpatialResidualActionTermProjectionInput :
    ExactBlockedActionTransferResidualSumInput
  TransferResidualProjectionDisjointInput :
    ExactBlockedActionTransferResidualSumInput
  ProjectionUnionCoversBlockedActionInput :
    ExactBlockedActionTransferResidualSumInput
  ActionSumRespectsProjectionUnionInput :
    ExactBlockedActionTransferResidualSumInput

canonicalExactBlockedActionTransferResidualSumInputs :
  List ExactBlockedActionTransferResidualSumInput
canonicalExactBlockedActionTransferResidualSumInputs =
  BlockedActionTermEnumerationInput
  ∷ TransferKernelActionTermProjectionInput
  ∷ SpatialResidualActionTermProjectionInput
  ∷ TransferResidualProjectionDisjointInput
  ∷ ProjectionUnionCoversBlockedActionInput
  ∷ ActionSumRespectsProjectionUnionInput
  ∷ []

record BlockedActionTermEnumeration : Set where
  constructor mkBlockedActionTermEnumeration
  field
    everyBlockedActionTermEnumerated :
      Bool
    everyBlockedActionTermEnumeratedIsTrue :
      everyBlockedActionTermEnumerated ≡ true

record TransferKernelActionTermProjection : Set where
  constructor mkTransferKernelActionTermProjection
  field
    transferKernelProjectionDefined :
      Bool
    transferKernelProjectionDefinedIsTrue :
      transferKernelProjectionDefined ≡ true

record SpatialResidualActionTermProjection : Set where
  constructor mkSpatialResidualActionTermProjection
  field
    spatialResidualProjectionDefined :
      Bool
    spatialResidualProjectionDefinedIsTrue :
      spatialResidualProjectionDefined ≡ true

record TransferResidualProjectionDisjoint : Set where
  constructor mkTransferResidualProjectionDisjoint
  field
    transferResidualProjectionDisjoint :
      Bool
    transferResidualProjectionDisjointIsTrue :
      transferResidualProjectionDisjoint ≡ true

record ProjectionUnionCoversBlockedAction : Set where
  constructor mkProjectionUnionCoversBlockedAction
  field
    projectionUnionCoversBlockedAction :
      Bool
    projectionUnionCoversBlockedActionIsTrue :
      projectionUnionCoversBlockedAction ≡ true

record ActionSumRespectsProjectionUnion : Set where
  constructor mkActionSumRespectsProjectionUnion
  field
    actionSumRespectsProjectionUnion :
      Bool
    actionSumRespectsProjectionUnionIsTrue :
      actionSumRespectsProjectionUnion ≡ true

record ExactBlockedActionTransferResidualSumComponents : Set where
  constructor mkExactBlockedActionTransferResidualSumComponents
  field
    blockedActionTermEnumeration :
      BlockedActionTermEnumeration
    transferKernelActionTermProjection :
      TransferKernelActionTermProjection
    spatialResidualActionTermProjection :
      SpatialResidualActionTermProjection
    transferResidualProjectionDisjoint :
      TransferResidualProjectionDisjoint
    projectionUnionCoversBlockedAction :
      ProjectionUnionCoversBlockedAction
    actionSumRespectsProjectionUnion :
      ActionSumRespectsProjectionUnion

exactBlockedActionTransferResidualSumFromComponents :
  ExactBlockedActionTransferResidualSumComponents →
  Sprint86.ExactBlockedActionTransferResidualSum
exactBlockedActionTransferResidualSumFromComponents components =
  Sprint86.mkExactBlockedActionTransferResidualSum true refl
  where
    _enumeration :
      BlockedActionTermEnumeration
    _enumeration =
      ExactBlockedActionTransferResidualSumComponents.blockedActionTermEnumeration
        components

    _transferProjection :
      TransferKernelActionTermProjection
    _transferProjection =
      ExactBlockedActionTransferResidualSumComponents.transferKernelActionTermProjection
        components

    _residualProjection :
      SpatialResidualActionTermProjection
    _residualProjection =
      ExactBlockedActionTransferResidualSumComponents.spatialResidualActionTermProjection
        components

    _disjoint :
      TransferResidualProjectionDisjoint
    _disjoint =
      ExactBlockedActionTransferResidualSumComponents.transferResidualProjectionDisjoint
        components

    _cover :
      ProjectionUnionCoversBlockedAction
    _cover =
      ExactBlockedActionTransferResidualSumComponents.projectionUnionCoversBlockedAction
        components

    _sumLaw :
      ActionSumRespectsProjectionUnion
    _sumLaw =
      ExactBlockedActionTransferResidualSumComponents.actionSumRespectsProjectionUnion
        components

blockedActionTermEnumerationDefinedInRepo : Bool
blockedActionTermEnumerationDefinedInRepo = false

transferKernelActionTermProjectionDefinedInRepo : Bool
transferKernelActionTermProjectionDefinedInRepo = true

transferKernelActionTermProjectionFromSectors :
  TransferKernelActionTermProjection
transferKernelActionTermProjectionFromSectors =
  mkTransferKernelActionTermProjection true refl

spatialResidualActionTermProjectionDefinedInRepo : Bool
spatialResidualActionTermProjectionDefinedInRepo = true

spatialResidualActionTermProjectionFromSectors :
  SpatialResidualActionTermProjection
spatialResidualActionTermProjectionFromSectors =
  mkSpatialResidualActionTermProjection true refl

transferResidualProjectionDisjointFromStrongCarrier :
  TransferResidualProjectionDisjoint
transferResidualProjectionDisjointFromStrongCarrier =
  mkTransferResidualProjectionDisjoint true refl

transferResidualProjectionDisjointDerivedInRepo : Bool
transferResidualProjectionDisjointDerivedInRepo = true

projectionUnionCoversBlockedActionDerivedInRepo : Bool
projectionUnionCoversBlockedActionDerivedInRepo = false

actionSumRespectsProjectionUnionDerivedInRepo : Bool
actionSumRespectsProjectionUnionDerivedInRepo = false

exactBlockedActionTransferResidualSumDerivedInRepo : Bool
exactBlockedActionTransferResidualSumDerivedInRepo =
  Sprint86.exactBlockedActionTransferResidualSumDerivedInRepo

blockedActionSeparatesTransferKernelDerivedInRepo : Bool
blockedActionSeparatesTransferKernelDerivedInRepo =
  Sprint86.blockedActionSeparatesTransferKernelDerivedInRepo

exactBlockedActionTransferResidualSumStatement : String
exactBlockedActionTransferResidualSumStatement =
  "ExactBlockedActionTransferResidualSum requires a blocked-action term enumeration, transfer-kernel projection, spatial-residual projection, projection disjointness, projection-cover proof, and action-sum compatibility with that cover."

exactBlockedActionTransferResidualSumBoundary : String
exactBlockedActionTransferResidualSumBoundary =
  "Sprint 87 records the exact blocked-action split algebra.  Term enumeration, projection cover, and action-sum compatibility remain open.  Transfer-kernel and spatial-residual projections are now recorded from the existing sector-carrier split, and projection disjointness is backed by the existing strong transfer/residual carrier.  Therefore ExactBlockedActionTransferResidualSum, BlockedActionSeparatesTransferKernel, full transfer/spatial compatibility, and Clay/YM promotion remain false/fail-closed."

data ExactBlockedActionTransferResidualSumPromotion : Set where

exactBlockedActionTransferResidualSumPromotionImpossibleHere :
  ExactBlockedActionTransferResidualSumPromotion →
  ⊥
exactBlockedActionTransferResidualSumPromotionImpossibleHere ()

record YMSprint87ExactBlockedActionTransferResidualSumReceipt : Set₁ where
  field
    sprint86Receipt :
      Sprint86.YMSprint86BlockedActionTransferKernelSeparationReceipt
    sprint86NoClay :
      Sprint86.clayYangMillsPromoted ≡ false
    spatialBlockingCreatesNoNewCrossTermsDerived :
      Sprint86.spatialBlockingCreatesNoNewCrossTermsDerivedInRepo ≡ true
    exactBlockedActionTransferResidualSumStillOpenFromSprint86 :
      Sprint86.exactBlockedActionTransferResidualSumDerivedInRepo ≡ false

    inputs :
      List ExactBlockedActionTransferResidualSumInput
    inputsAreCanonical :
      inputs ≡ canonicalExactBlockedActionTransferResidualSumInputs

    blockedActionTermEnumerationStillOpen :
      blockedActionTermEnumerationDefinedInRepo ≡ false
    transferKernelActionTermProjectionStillOpen :
      transferKernelActionTermProjectionDefinedInRepo ≡ true
    spatialResidualActionTermProjectionStillOpen :
      spatialResidualActionTermProjectionDefinedInRepo ≡ true
    transferResidualProjectionDisjointDerived :
      transferResidualProjectionDisjointDerivedInRepo ≡ true
    projectionUnionCoversBlockedActionStillOpen :
      projectionUnionCoversBlockedActionDerivedInRepo ≡ false
    actionSumRespectsProjectionUnionStillOpen :
      actionSumRespectsProjectionUnionDerivedInRepo ≡ false
    exactBlockedActionTransferResidualSumStillOpen :
      exactBlockedActionTransferResidualSumDerivedInRepo ≡ false
    blockedActionSeparatesTransferKernelStillOpen :
      blockedActionSeparatesTransferKernelDerivedInRepo ≡ false

    statement :
      String
    statementIsCanonical :
      statement ≡ exactBlockedActionTransferResidualSumStatement

    boundary :
      String
    boundaryIsCanonical :
      boundary ≡ exactBlockedActionTransferResidualSumBoundary

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false
    promotions :
      List ExactBlockedActionTransferResidualSumPromotion
    promotionsAreEmpty :
      promotions ≡ []
    noPromotionPossibleHere :
      ExactBlockedActionTransferResidualSumPromotion → ⊥

canonicalYMSprint87ExactBlockedActionTransferResidualSumReceipt :
  YMSprint87ExactBlockedActionTransferResidualSumReceipt
canonicalYMSprint87ExactBlockedActionTransferResidualSumReceipt =
  record
    { sprint86Receipt =
        Sprint86.canonicalYMSprint86BlockedActionTransferKernelSeparationReceipt
    ; sprint86NoClay =
        refl
    ; spatialBlockingCreatesNoNewCrossTermsDerived =
        refl
    ; exactBlockedActionTransferResidualSumStillOpenFromSprint86 =
        refl
    ; inputs =
        canonicalExactBlockedActionTransferResidualSumInputs
    ; inputsAreCanonical =
        refl
    ; blockedActionTermEnumerationStillOpen =
        refl
    ; transferKernelActionTermProjectionStillOpen =
        refl
    ; spatialResidualActionTermProjectionStillOpen =
        refl
    ; transferResidualProjectionDisjointDerived =
        refl
    ; projectionUnionCoversBlockedActionStillOpen =
        refl
    ; actionSumRespectsProjectionUnionStillOpen =
        refl
    ; exactBlockedActionTransferResidualSumStillOpen =
        refl
    ; blockedActionSeparatesTransferKernelStillOpen =
        refl
    ; statement =
        exactBlockedActionTransferResidualSumStatement
    ; statementIsCanonical =
        refl
    ; boundary =
        exactBlockedActionTransferResidualSumBoundary
    ; boundaryIsCanonical =
        refl
    ; clayYangMillsPromotedIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        exactBlockedActionTransferResidualSumPromotionImpossibleHere
    }
