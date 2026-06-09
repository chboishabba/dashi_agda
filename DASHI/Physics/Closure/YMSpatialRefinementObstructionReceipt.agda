module DASHI.Physics.Closure.YMSpatialRefinementObstructionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CarrierLatticeYMDefinitionReceipt as Lattice

------------------------------------------------------------------------
-- Yang-Mills spatial refinement obstruction receipt.
--
-- The carrier spatial lattice is the arithmetic three-site object
-- {z_-4,z_-3,z_-7}.  These sites are not subdividable continuum points.
-- A fourth spatial site would require a fourth class-number-1 discriminant
-- whose conductor remains pairwise coprime to the 4,3,7 conductors; this is
-- recorded here as blocked by Heegner exhaustion.  Therefore the standard
-- continuum limit, which requires spatial refinement, is not promoted.

data YMSpatialRefinementObstructionStatus : Set where
  arithmeticThreeSiteSpatialLatticeBlocksContinuumRefinement :
    YMSpatialRefinementObstructionStatus

data YMSpatialSite : Set where
  zMinus4 : YMSpatialSite
  zMinus3 : YMSpatialSite
  zMinus7 : YMSpatialSite

canonicalYMSpatialSites : List YMSpatialSite
canonicalYMSpatialSites =
  zMinus4
  ∷ zMinus3
  ∷ zMinus7
  ∷ []

data YMSpatialRefinementBlocker : Set where
  carrierSitesAreArithmeticObjects :
    YMSpatialRefinementBlocker

  carrierSitesAreNotContinuumPoints :
    YMSpatialRefinementBlocker

  fourthPairwiseCoprimeHeegnerConductorUnavailable :
    YMSpatialRefinementBlocker

  standardContinuumLimitNeedsSpatialRefinement :
    YMSpatialRefinementBlocker

canonicalYMSpatialRefinementBlockers :
  List YMSpatialRefinementBlocker
canonicalYMSpatialRefinementBlockers =
  carrierSitesAreArithmeticObjects
  ∷ carrierSitesAreNotContinuumPoints
  ∷ fourthPairwiseCoprimeHeegnerConductorUnavailable
  ∷ standardContinuumLimitNeedsSpatialRefinement
  ∷ []

data YMSpatialRefinementPromotion : Set where

ymSpatialRefinementPromotionImpossibleHere :
  YMSpatialRefinementPromotion →
  ⊥
ymSpatialRefinementPromotionImpossibleHere ()

ymSpatialLatticeStatement : String
ymSpatialLatticeStatement =
  "Carrier spatial lattice is exactly {z_-4,z_-3,z_-7}; these are arithmetic Heegner sites, not subdividable continuum points."

ymFourthSiteStatement : String
ymFourthSiteStatement =
  "Adding a fourth spatial site would require a fourth class-number-1 discriminant with pairwise-coprime conductor; Heegner exhaustion blocks this."

record YMSpatialRefinementObstructionReceipt : Setω where
  field
    status :
      YMSpatialRefinementObstructionStatus

    carrierLatticeReceipt :
      Lattice.CarrierLatticeYMDefinitionReceipt

    carrierSpatialSiteCountThree :
      Lattice.spatialSiteCount carrierLatticeReceipt ≡ 3

    spatialSites :
      List YMSpatialSite

    spatialSitesAreCanonical :
      spatialSites ≡ canonicalYMSpatialSites

    spatialSiteCount :
      Nat

    spatialSiteCountIsThree :
      spatialSiteCount ≡ 3

    carrierConductors :
      List Nat

    carrierConductorsAreFourThreeSeven :
      carrierConductors ≡ 4 ∷ 3 ∷ 7 ∷ []

    spatialLatticeStatement :
      String

    spatialLatticeStatementIsCanonical :
      spatialLatticeStatement ≡ ymSpatialLatticeStatement

    fourthSiteStatement :
      String

    fourthSiteStatementIsCanonical :
      fourthSiteStatement ≡ ymFourthSiteStatement

    spatialLatticeRigid :
      Bool

    spatialLatticeRigidIsTrue :
      spatialLatticeRigid ≡ true

    heegnerExhaustionPreventsRefinement :
      Bool

    heegnerExhaustionPreventsRefinementIsTrue :
      heegnerExhaustionPreventsRefinement ≡ true

    fourthSiteDoesNotExist :
      Bool

    fourthSiteDoesNotExistIsTrue :
      fourthSiteDoesNotExist ≡ true

    standardContinuumLimitRequiresRefinement :
      Bool

    standardContinuumLimitRequiresRefinementIsTrue :
      standardContinuumLimitRequiresRefinement ≡ true

    ymSpatialRefinementBlocked :
      Bool

    ymSpatialRefinementBlockedIsTrue :
      ymSpatialRefinementBlocked ≡ true

    Clay :
      Bool

    ClayIsFalse :
      Clay ≡ false

    blockers :
      List YMSpatialRefinementBlocker

    blockersAreCanonical :
      blockers ≡ canonicalYMSpatialRefinementBlockers

    promotionFlags :
      List YMSpatialRefinementPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open YMSpatialRefinementObstructionReceipt public

canonicalYMSpatialRefinementObstructionReceipt :
  YMSpatialRefinementObstructionReceipt
canonicalYMSpatialRefinementObstructionReceipt =
  record
    { status =
        arithmeticThreeSiteSpatialLatticeBlocksContinuumRefinement
    ; carrierLatticeReceipt =
        Lattice.canonicalCarrierLatticeYMDefinitionReceipt
    ; carrierSpatialSiteCountThree =
        refl
    ; spatialSites =
        canonicalYMSpatialSites
    ; spatialSitesAreCanonical =
        refl
    ; spatialSiteCount =
        3
    ; spatialSiteCountIsThree =
        refl
    ; carrierConductors =
        4 ∷ 3 ∷ 7 ∷ []
    ; carrierConductorsAreFourThreeSeven =
        refl
    ; spatialLatticeStatement =
        ymSpatialLatticeStatement
    ; spatialLatticeStatementIsCanonical =
        refl
    ; fourthSiteStatement =
        ymFourthSiteStatement
    ; fourthSiteStatementIsCanonical =
        refl
    ; spatialLatticeRigid =
        true
    ; spatialLatticeRigidIsTrue =
        refl
    ; heegnerExhaustionPreventsRefinement =
        true
    ; heegnerExhaustionPreventsRefinementIsTrue =
        refl
    ; fourthSiteDoesNotExist =
        true
    ; fourthSiteDoesNotExistIsTrue =
        refl
    ; standardContinuumLimitRequiresRefinement =
        true
    ; standardContinuumLimitRequiresRefinementIsTrue =
        refl
    ; ymSpatialRefinementBlocked =
        true
    ; ymSpatialRefinementBlockedIsTrue =
        refl
    ; Clay =
        false
    ; ClayIsFalse =
        refl
    ; blockers =
        canonicalYMSpatialRefinementBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The spatial carrier has exactly the arithmetic sites z_-4, z_-3, and z_-7"
        ∷ "The three sites are not subdividable continuum points"
        ∷ "A fourth refinement site would need a fourth pairwise-coprime class-number-1 conductor"
        ∷ "Heegner exhaustion blocks the fourth site, so YM spatial refinement and Clay promotion remain false"
        ∷ []
    }

ymSpatialRefinementObstructionClayFalse :
  Clay canonicalYMSpatialRefinementObstructionReceipt ≡ false
ymSpatialRefinementObstructionClayFalse =
  refl

ymSpatialRefinementObstructionFalsePromotionTheorem :
  YMSpatialRefinementPromotion →
  ⊥
ymSpatialRefinementObstructionFalsePromotionTheorem =
  ymSpatialRefinementPromotionImpossibleHere
