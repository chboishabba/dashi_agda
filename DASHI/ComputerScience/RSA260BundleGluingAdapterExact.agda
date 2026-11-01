module DASHI.ComputerScience.RSA260BundleGluingAdapterExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.ComputerScience.RSA260AdaptiveReducerHyperfabricExact as RSA

------------------------------------------------------------------------
-- RSA-260 STATUS AGAINST THE CANONICAL BUNDLESHEAF PROMOTION BAR
--
-- The adaptive reducer owner has requirement closure, conflict selection,
-- largest admissible closed-batch selection and a globally commuting composed
-- action.  It does not currently provide a BundleSheaf-style exact restriction
-- of the global glued object back to each declared local section.
------------------------------------------------------------------------

record RSA260BundleStatus : Set where
  constructor rsa260BundleStatusRecord
  field
    requirementClosureRepresented : Bool
    conflictSelectionRepresented : Bool
    closedBatchSelectionRepresented : Bool
    globalEquivarianceRepresented : Bool
    localRestrictionRoundTripLocated : Bool
    bundleSheafPromotionPaid : Bool

open RSA260BundleStatus public

rsa260BundleStatus : RSA260BundleStatus
rsa260BundleStatus =
  rsa260BundleStatusRecord
    (RSA.RSA260AdaptiveHyperfabricRoadmapBoundary.multiComponentRequirementClosureRepresented
      RSA.currentRSA260AdaptiveHyperfabricRoadmapBoundary)
    (RSA.RSA260AdaptiveHyperfabricRoadmapBoundary.crossComponentConflictSelectionRepresented
      RSA.currentRSA260AdaptiveHyperfabricRoadmapBoundary)
    (RSA.RSA260AdaptiveHyperfabricRoadmapBoundary.largestClosedBatchSelectionRepresented
      RSA.currentRSA260AdaptiveHyperfabricRoadmapBoundary)
    (RSA.RSA260AdaptiveHyperfabricRoadmapBoundary.selectedBatchGlobalEquivarianceRepresented
      RSA.currentRSA260AdaptiveHyperfabricRoadmapBoundary)
    false
    false

bundlePromotionStillUnpaid :
  bundleSheafPromotionPaid rsa260BundleStatus ≡ false
bundlePromotionStillUnpaid = refl
