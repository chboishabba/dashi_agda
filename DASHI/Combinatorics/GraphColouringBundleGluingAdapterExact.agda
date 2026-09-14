module DASHI.Combinatorics.GraphColouringBundleGluingAdapterExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Combinatorics.GraphColouringRecolourPantsSnowballExact as Colouring

------------------------------------------------------------------------
-- GRAPH COLOURING STATUS AGAINST THE CANONICAL BUNDLESHEAF PROMOTION BAR
--
-- The existing owner has a typed local->boundary->seam->recursive chain and
-- explicitly rejects local recolour => global compatibility.  It does not yet
-- supply a BundleSheaf local-family/glue/restrict-exact witness.
------------------------------------------------------------------------

record GraphColouringBundleStatus : Set where
  constructor graphColouringBundleStatusRecord
  field
    localRecolourStageTracked : Bool
    boundaryRestrictionStageTracked : Bool
    seamCompatibilityStageTracked : Bool
    recursiveGluingStageTracked : Bool
    backwardColourLiftRequired : Bool
    localRecolourAutomaticallyGlobal : Bool
    bundleSheafPromotionPaid : Bool

open GraphColouringBundleStatus public

graphColouringBundleStatus : GraphColouringBundleStatus
graphColouringBundleStatus =
  graphColouringBundleStatusRecord
    true
    true
    true
    true
    (Colouring.GraphColouringPantsBoundary.reductionRequiresBackwardColourLift
      Colouring.canonicalGraphColouringPantsBoundary)
    (Colouring.GraphColouringPantsBoundary.localRecolourImpliesGlobalGluingCompatibility
      Colouring.canonicalGraphColouringPantsBoundary)
    false

bundlePromotionStillUnpaid :
  bundleSheafPromotionPaid graphColouringBundleStatus ≡ false
bundlePromotionStillUnpaid = refl
