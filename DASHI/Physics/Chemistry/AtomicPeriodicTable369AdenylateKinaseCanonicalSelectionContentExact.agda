module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCanonicalSelectionContentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Geometry.RigidMotionSemidirectProductExact as SE3
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseAtomisticConfigurationExact as Config
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCOMGeometryExact as Geometry
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCVProjectionNonFactorabilityExact as Collision
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSourceAtomSelectionExact as Selection

------------------------------------------------------------------------
-- TRANSPARENT CANONICAL SELECTED-CONTENT SURFACE
--
-- Attribution boundary:
-- * Li-Liu-Ji 2015 pays the AdK source-facing selection roles.
-- * Prohaska et al. pays the mass convention referenced by canonical rows.
-- * scripts/adk_selection_content.py defines the DASHI executable row syntax.
-- * The content-extensional COM and three-CV equalities below are DASHI-original
--   mathematics. They are not scientific-source claims and are not paid by a
--   DOI, PDB identifier, mirror object, or hash value.
------------------------------------------------------------------------

selectionContentSchema : String
selectionContentSchema = "dashi.adk.selection_content.v1"

selectionContentScriptPath : String
selectionContentScriptPath = "scripts/adk_selection_content.py"

selectionContentRegressionPath : String
selectionContentRegressionPath = "scripts/test_adk_selection_content.py"

massSourceDOI : String
massSourceDOI = "10.1515/pac-2019-0603"

record CanonicalSelectionContent : Set where
  constructor canonical-selection-content
  field
    schema : String
    rowCount : Nat
    massConventionReference : String
    canonicalRows : List String
open CanonicalSelectionContent public

record CanonicalSelectionContentReceipt : Set where
  constructor canonical-selection-content-receipt
  field
    content : CanonicalSelectionContent
    payloadSha256 : String
    executableReference : String
    provenanceReference : String
    executionObserved : Bool
open CanonicalSelectionContentReceipt public

------------------------------------------------------------------------
-- A content-sound COM model exposes the canonical selected-content packet used
-- for each configuration/selection and proves that equal packets imply equal
-- centers of mass. This is the only semantic bridge needed from transparent
-- payload equality into the existing SelectionExtensionalCOMModel surface.
------------------------------------------------------------------------

record CanonicalContentCOMModel
  {rigidModel : SE3.RigidMotionModel}
  (geometry : Geometry.AdKCOMGeometryModel rigidModel) : Set₁ where
  constructor canonical-content-com-model
  field
    selectionContentOf :
      Config.AtomisticConfiguration →
      Selection.AtomSelectionSpec →
      CanonicalSelectionContent

    centerOfMassContentExtensional :
      (left right : Config.AtomisticConfiguration) →
      (selection : Selection.AtomSelectionSpec) →
      selectionContentOf left selection ≡ selectionContentOf right selection →
      Geometry.centerOfMass geometry left selection
      ≡ Geometry.centerOfMass geometry right selection
open CanonicalContentCOMModel public

contentExtensionalCOMModel :
  {rigidModel : SE3.RigidMotionModel} →
  {geometry : Geometry.AdKCOMGeometryModel rigidModel} →
  CanonicalContentCOMModel geometry →
  Collision.SelectionExtensionalCOMModel geometry
contentExtensionalCOMModel contentModel =
  Collision.selection-extensional-com-model
    (λ left right selection →
      selectionContentOf contentModel left selection
      ≡ selectionContentOf contentModel right selection)
    (centerOfMassContentExtensional contentModel)

------------------------------------------------------------------------
-- Equality over exactly the source-facing selections used by the three-CV map.
------------------------------------------------------------------------

selections : Selection.AdKThreeCVSelections
selections = Selection.canonicalAdKThreeCVSelections

record CanonicalThreeCVContentAgreement
  {rigidModel : SE3.RigidMotionModel}
  {geometry : Geometry.AdKCOMGeometryModel rigidModel}
  (contentModel : CanonicalContentCOMModel geometry)
  (left right : Config.AtomisticConfiguration) : Set₁ where
  constructor canonical-three-cv-content-agreement
  field
    thetaOneFirstContentEqual :
      selectionContentOf contentModel left (Selection.thetaOneFirst selections)
      ≡ selectionContentOf contentModel right (Selection.thetaOneFirst selections)
    thetaOneVertexContentEqual :
      selectionContentOf contentModel left (Selection.thetaOneVertex selections)
      ≡ selectionContentOf contentModel right (Selection.thetaOneVertex selections)
    thetaOneThirdContentEqual :
      selectionContentOf contentModel left (Selection.thetaOneThird selections)
      ≡ selectionContentOf contentModel right (Selection.thetaOneThird selections)
    thetaTwoFirstContentEqual :
      selectionContentOf contentModel left (Selection.thetaTwoFirst selections)
      ≡ selectionContentOf contentModel right (Selection.thetaTwoFirst selections)
    thetaTwoVertexContentEqual :
      selectionContentOf contentModel left (Selection.thetaTwoVertex selections)
      ≡ selectionContentOf contentModel right (Selection.thetaTwoVertex selections)
    thetaTwoThirdContentEqual :
      selectionContentOf contentModel left (Selection.thetaTwoThird selections)
      ≡ selectionContentOf contentModel right (Selection.thetaTwoThird selections)
    dLnFirstContentEqual :
      selectionContentOf contentModel left (Selection.dLnFirst selections)
      ≡ selectionContentOf contentModel right (Selection.dLnFirst selections)
    dLnSecondContentEqual :
      selectionContentOf contentModel left (Selection.dLnSecond selections)
      ≡ selectionContentOf contentModel right (Selection.dLnSecond selections)
open CanonicalThreeCVContentAgreement public

canonicalContentAgreementToSelectionEquivalence :
  {rigidModel : SE3.RigidMotionModel} →
  {geometry : Geometry.AdKCOMGeometryModel rigidModel} →
  (contentModel : CanonicalContentCOMModel geometry) →
  (left right : Config.AtomisticConfiguration) →
  CanonicalThreeCVContentAgreement contentModel left right →
  Collision.ThreeCVSelectionEquivalent
    (contentExtensionalCOMModel contentModel) left right
canonicalContentAgreementToSelectionEquivalence contentModel left right agreement =
  Collision.three-cv-selection-equivalent
    (thetaOneFirstContentEqual agreement)
    (thetaOneVertexContentEqual agreement)
    (thetaOneThirdContentEqual agreement)
    (thetaTwoFirstContentEqual agreement)
    (thetaTwoVertexContentEqual agreement)
    (thetaTwoThirdContentEqual agreement)
    (dLnFirstContentEqual agreement)
    (dLnSecondContentEqual agreement)

canonicalContentAgreementToThreeCVEquality :
  {rigidModel : SE3.RigidMotionModel} →
  {geometry : Geometry.AdKCOMGeometryModel rigidModel} →
  (contentModel : CanonicalContentCOMModel geometry) →
  (left right : Config.AtomisticConfiguration) →
  CanonicalThreeCVContentAgreement contentModel left right →
  Collision.projectThreeCV geometry left ≡ Collision.projectThreeCV geometry right
canonicalContentAgreementToThreeCVEquality contentModel left right agreement =
  Collision.threeCVSelectionEquivalentProjectsEqual
    (contentExtensionalCOMModel contentModel)
    left right
    (canonicalContentAgreementToSelectionEquivalence
      contentModel left right agreement)

------------------------------------------------------------------------
-- Hashes and byte manifestations remain audit/provenance coordinates only.
------------------------------------------------------------------------

data EqualPayloadHashesCreateContentEquality : Set where
data ExecutableCanonicalisationCreatesScientificAuthority : Set where
data EqualCanonicalRowsCreatePDBIdentity : Set where

equalPayloadHashesDoNotCreateContentEquality :
  EqualPayloadHashesCreateContentEquality → ⊥
equalPayloadHashesDoNotCreateContentEquality ()

executableCanonicalisationDoesNotCreateScientificAuthority :
  ExecutableCanonicalisationCreatesScientificAuthority → ⊥
executableCanonicalisationDoesNotCreateScientificAuthority ()

equalCanonicalRowsDoNotCreatePDBIdentity :
  EqualCanonicalRowsCreatePDBIdentity → ⊥
equalCanonicalRowsDoNotCreatePDBIdentity ()

record AdKCanonicalSelectionContentBoundary : Set where
  constructor adk-canonical-selection-content-boundary
  field
    transparentCanonicalRowsRetained : Bool
    massSourceAttributionRetained : Bool
    contentEqualityDefinesSelectionEquivalence : Bool
    contentSoundCOMCreatesThreeCVEquality : Bool
    payloadHashRetainedAsAuditCoordinate : Bool
    hashEqualityCreatesContentEquality : Bool
    executableCanonicalisationCreatesScientificAuthority : Bool
    equalCanonicalRowsCreatePDBIdentity : Bool
open AdKCanonicalSelectionContentBoundary public

canonicalAdKCanonicalSelectionContentBoundary : AdKCanonicalSelectionContentBoundary
canonicalAdKCanonicalSelectionContentBoundary =
  adk-canonical-selection-content-boundary
    true true true true true
    false false false
