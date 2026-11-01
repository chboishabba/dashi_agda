module DASHI.Governance.CouncilBundleGluingCalculusAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.StageValuationBundleAtlas as Stage
import DASHI.Governance.LocalGlobalCouncilGluing as Council
import DASHI.Interop.LocalGlobalBundleGluingExact as Gluing

------------------------------------------------------------------------
-- KNOWN-GOOD BUNDLESHEAF CONSUMER
--
-- This adapter adds no new council or sheaf semantics.  It instantiates the
-- cross-domain wrapper on the existing fully paid council BundleSheaf so the
-- promotion bar has a positive control alongside partial graph/RSA/wave lanes.
------------------------------------------------------------------------

canonicalCouncilRestrictionViaGenericSurface :
  (point : Council.CouncilBasePoint) →
  Stage.BundleSheaf.restrict
    Council.rceppCouncilBundleSheaf
    (Stage.BundleSheaf.glue
      Council.rceppCouncilBundleSheaf
      Council.canonicalLocalCouncilFamily
      Council.canonicalCouncilCompatibility)
    point
  ≡ Council.canonicalLocalCouncilFamily point
canonicalCouncilRestrictionViaGenericSurface point =
  Gluing.compatibleLocalFamilyGluesAndRestricts
    Council.rceppCouncilBundleSheaf
    Council.canonicalLocalCouncilFamily
    Council.canonicalCouncilCompatibility
    point

canonicalCouncilGlobalIsExistingGlue :
  Stage.BundleSheaf.glue
    Council.rceppCouncilBundleSheaf
    Council.canonicalLocalCouncilFamily
    Council.canonicalCouncilCompatibility
  ≡ Council.canonicalGlobalCouncilSection
canonicalCouncilGlobalIsExistingGlue = refl

record CouncilBundleGluingCalculusBoundary : Set where
  constructor councilBundleGluingCalculusBoundary
  field
    existingBundleSheafReused : Bool
    compatibilityWitnessReused : Bool
    genericRestrictionBackTheoremInhabited : Bool
    newPoliticalAuthorityCreated : Bool

canonicalCouncilBundleGluingCalculusBoundary :
  CouncilBundleGluingCalculusBoundary
canonicalCouncilBundleGluingCalculusBoundary =
  councilBundleGluingCalculusBoundary true true true false

canonicalCouncilUsesExistingBundleSheaf : Bool
canonicalCouncilUsesExistingBundleSheaf =
  CouncilBundleGluingCalculusBoundary.existingBundleSheafReused
    canonicalCouncilBundleGluingCalculusBoundary
