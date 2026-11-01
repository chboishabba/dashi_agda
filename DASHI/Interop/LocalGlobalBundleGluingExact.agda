module DASHI.Interop.LocalGlobalBundleGluingExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.StageValuationBundleAtlas as Stage

------------------------------------------------------------------------
-- EXISTING BUNDLESHEAF AS THE LOCAL -> GLOBAL GLUING KERNEL
--
-- We do not define another sheaf/gluing ontology here.  BundleSheaf already
-- carries restriction, compatibility, gluing, and exact restriction after glue.
-- This owner exposes the theorem-shaped surface used by cross-domain adapters.
------------------------------------------------------------------------

compatibleLocalFamilyGluesAndRestricts :
  ∀ {BasePoint LocalSection GlobalSection : Set}
    (sheaf : Stage.BundleSheaf BasePoint LocalSection GlobalSection)
    (locals : BasePoint → LocalSection)
    (witness : Stage.BundleSheaf.compatible sheaf locals)
    (point : BasePoint) →
  Stage.BundleSheaf.restrict sheaf
    (Stage.BundleSheaf.glue sheaf locals witness)
    point
  ≡ locals point
compatibleLocalFamilyGluesAndRestricts sheaf locals witness point =
  Stage.BundleSheaf.glueRestricts sheaf locals witness point

record LocalGlobalGluingBoundary : Set where
  constructor localGlobalGluingBoundary
  field
    localFamilyMustBeRepresented : Bool
    compatibilityWitnessRequired : Bool
    glueOperationRequired : Bool
    exactRestrictionBackRequiredForPromotion : Bool
    localValidityAutomaticallyCreatesGlobalSection : Bool
    pairwiseCompatibilityAutomaticallyProvesAllGlobalObligations : Bool

canonicalLocalGlobalGluingBoundary : LocalGlobalGluingBoundary
canonicalLocalGlobalGluingBoundary =
  localGlobalGluingBoundary
    true
    true
    true
    true
    false
    false
