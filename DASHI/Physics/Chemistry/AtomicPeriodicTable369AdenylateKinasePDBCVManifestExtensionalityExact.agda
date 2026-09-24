module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinasePDBCVManifestExtensionalityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Geometry.RigidMotionSemidirectProductExact as SE3
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseAtomisticConfigurationExact as Config
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCOMGeometryExact as Geometry
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCVProjectionNonFactorabilityExact as Collision
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinasePDBCVScriptManifestExact as Script
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSourceAtomSelectionExact as Selection

------------------------------------------------------------------------
-- EXECUTABLE MANIFEST -> FORMAL SELECTION EXTENSIONALITY WELD
--
-- Attribution boundary:
-- * Li-Liu-Ji 2015 source-pay the AdK theta1/theta2/dLN selection roles.
-- * Prohaska et al. source-pay the atomic-mass convention used by the script.
-- * scripts/adk_pdb_cv_fixture.py emits DASHI executable evidence receipts.
-- * The bridge from an explicit selected-content witness to COM/CV equality is
--   DASHI-original mathematics reusing CVProjectionNonFactorabilityExact.
--
-- SHA-256 equality is deliberately NOT used as an injectivity theorem. A hash
-- agreement is retained as an audit coordinate alongside a separate proof that
-- the selected mass/coordinate content is equivalent for the supplied model.
------------------------------------------------------------------------

attributionReading : String
attributionReading =
  "Li-Liu-Ji pays selection roles; Prohaska pays the mass convention; executable manifests are DASHI evidence; manifest-to-extensionality compilation is DASHI-original"

record ManifestBackedSelectionAgreement
  {rigidModel : SE3.RigidMotionModel}
  {geometry : Geometry.AdKCOMGeometryModel rigidModel}
  (extensional : Collision.SelectionExtensionalCOMModel geometry)
  (left right : Config.AtomisticConfiguration)
  (selection : Selection.AtomSelectionSpec) : Set₁ where
  constructor manifest-backed-selection-agreement
  field
    leftManifest : Script.PDBCVSelectionManifestReceipt
    rightManifest : Script.PDBCVSelectionManifestReceipt
    identityHashAgreement :
      Script.identitySha256 leftManifest ≡ Script.identitySha256 rightManifest
    massCoordinateHashAgreement :
      Script.massCoordinateSha256 leftManifest ≡ Script.massCoordinateSha256 rightManifest
    massSourceDOIAgreement :
      Script.massSourceDOI leftManifest ≡ Script.massSourceDOI rightManifest
    selectedContentEquivalent :
      Collision.SelectionEquivalent extensional left right selection
open ManifestBackedSelectionAgreement public

manifestBackedSelectionToSelectionEquivalence :
  {rigidModel : SE3.RigidMotionModel} →
  {geometry : Geometry.AdKCOMGeometryModel rigidModel} →
  {extensional : Collision.SelectionExtensionalCOMModel geometry} →
  {left right : Config.AtomisticConfiguration} →
  {selection : Selection.AtomSelectionSpec} →
  ManifestBackedSelectionAgreement extensional left right selection →
  Collision.SelectionEquivalent extensional left right selection
manifestBackedSelectionToSelectionEquivalence agreement =
  selectedContentEquivalent agreement

selections : Selection.AdKThreeCVSelections
selections = Selection.canonicalAdKThreeCVSelections

record ManifestBackedThreeCVAgreement
  {rigidModel : SE3.RigidMotionModel}
  {geometry : Geometry.AdKCOMGeometryModel rigidModel}
  (extensional : Collision.SelectionExtensionalCOMModel geometry)
  (left right : Config.AtomisticConfiguration) : Set₁ where
  constructor manifest-backed-three-cv-agreement
  field
    thetaOneFirstAgreement :
      ManifestBackedSelectionAgreement extensional left right
        (Selection.thetaOneFirst selections)
    thetaOneVertexAgreement :
      ManifestBackedSelectionAgreement extensional left right
        (Selection.thetaOneVertex selections)
    thetaOneThirdAgreement :
      ManifestBackedSelectionAgreement extensional left right
        (Selection.thetaOneThird selections)
    thetaTwoFirstAgreement :
      ManifestBackedSelectionAgreement extensional left right
        (Selection.thetaTwoFirst selections)
    thetaTwoVertexAgreement :
      ManifestBackedSelectionAgreement extensional left right
        (Selection.thetaTwoVertex selections)
    thetaTwoThirdAgreement :
      ManifestBackedSelectionAgreement extensional left right
        (Selection.thetaTwoThird selections)
    dLnFirstAgreement :
      ManifestBackedSelectionAgreement extensional left right
        (Selection.dLnFirst selections)
    dLnSecondAgreement :
      ManifestBackedSelectionAgreement extensional left right
        (Selection.dLnSecond selections)
open ManifestBackedThreeCVAgreement public

manifestBackedThreeCVToSelectionEquivalence :
  {rigidModel : SE3.RigidMotionModel} →
  {geometry : Geometry.AdKCOMGeometryModel rigidModel} →
  (extensional : Collision.SelectionExtensionalCOMModel geometry) →
  (left right : Config.AtomisticConfiguration) →
  ManifestBackedThreeCVAgreement extensional left right →
  Collision.ThreeCVSelectionEquivalent extensional left right
manifestBackedThreeCVToSelectionEquivalence extensional left right agreement =
  Collision.three-cv-selection-equivalent
    (selectedContentEquivalent (thetaOneFirstAgreement agreement))
    (selectedContentEquivalent (thetaOneVertexAgreement agreement))
    (selectedContentEquivalent (thetaOneThirdAgreement agreement))
    (selectedContentEquivalent (thetaTwoFirstAgreement agreement))
    (selectedContentEquivalent (thetaTwoVertexAgreement agreement))
    (selectedContentEquivalent (thetaTwoThirdAgreement agreement))
    (selectedContentEquivalent (dLnFirstAgreement agreement))
    (selectedContentEquivalent (dLnSecondAgreement agreement))

manifestBackedThreeCVToThreeCVEquality :
  {rigidModel : SE3.RigidMotionModel} →
  {geometry : Geometry.AdKCOMGeometryModel rigidModel} →
  (extensional : Collision.SelectionExtensionalCOMModel geometry) →
  (left right : Config.AtomisticConfiguration) →
  ManifestBackedThreeCVAgreement extensional left right →
  Collision.projectThreeCV geometry left ≡ Collision.projectThreeCV geometry right
manifestBackedThreeCVToThreeCVEquality extensional left right agreement =
  Collision.threeCVSelectionEquivalentProjectsEqual
    extensional left right
    (manifestBackedThreeCVToSelectionEquivalence
      extensional left right agreement)

record DifferentSourceBytesSameThreeCVRelevantContent
  {rigidModel : SE3.RigidMotionModel}
  {geometry : Geometry.AdKCOMGeometryModel rigidModel}
  (extensional : Collision.SelectionExtensionalCOMModel geometry) : Set₁ where
  constructor different-source-bytes-same-three-cv-content
  field
    leftConfiguration : Config.AtomisticConfiguration
    rightConfiguration : Config.AtomisticConfiguration
    leftSourceSha256 : String
    rightSourceSha256 : String
    sourceByteHashesDiffer : leftSourceSha256 ≡ rightSourceSha256 → ⊥
    manifestAgreement :
      ManifestBackedThreeCVAgreement
        extensional leftConfiguration rightConfiguration
open DifferentSourceBytesSameThreeCVRelevantContent public

differentSourceBytesMayProjectToSameThreeCV :
  {rigidModel : SE3.RigidMotionModel} →
  {geometry : Geometry.AdKCOMGeometryModel rigidModel} →
  (extensional : Collision.SelectionExtensionalCOMModel geometry) →
  (witness : DifferentSourceBytesSameThreeCVRelevantContent extensional) →
  Collision.projectThreeCV geometry (leftConfiguration witness)
  ≡ Collision.projectThreeCV geometry (rightConfiguration witness)
differentSourceBytesMayProjectToSameThreeCV extensional witness =
  manifestBackedThreeCVToThreeCVEquality
    extensional
    (leftConfiguration witness)
    (rightConfiguration witness)
    (manifestAgreement witness)

data EqualHashesCreateSelectionContentWitness : Set where
data ExecutableReceiptCreatesScientificSourceAuthority : Set where
data DifferentByteHashesCreateDifferentConfiguration : Set where
data SameThreeCVCreatesSameSourceBytes : Set where

equalHashesDoNotCreateSelectionContentWitness :
  EqualHashesCreateSelectionContentWitness → ⊥
equalHashesDoNotCreateSelectionContentWitness ()

executableReceiptDoesNotCreateScientificSourceAuthority :
  ExecutableReceiptCreatesScientificSourceAuthority → ⊥
executableReceiptDoesNotCreateScientificSourceAuthority ()

differentByteHashesDoNotCreateDifferentConfiguration :
  DifferentByteHashesCreateDifferentConfiguration → ⊥
differentByteHashesDoNotCreateDifferentConfiguration ()

sameThreeCVDoesNotCreateSameSourceBytes :
  SameThreeCVCreatesSameSourceBytes → ⊥
sameThreeCVDoesNotCreateSameSourceBytes ()

record AdKPDBCVManifestExtensionalityBoundary : Set where
  constructor adk-pdb-cv-manifest-extensionality-boundary
  field
    identityManifestHashesRetained : Bool
    massCoordinateManifestHashesRetained : Bool
    selectionContentWitnessRequired : Bool
    manifestBackedSelectionCreatesSelectionEquivalence : Bool
    manifestBackedThreeCVCreatesThreeCVEquality : Bool
    differentSourceBytesMayShareThreeCVRelevantContent : Bool
    liLiuJiSelectionAttributionRetained : Bool
    prohaskaMassAttributionRetained : Bool
    dashiBridgeTheoremAttributionExplicit : Bool
    hashInjectivityAssumed : Bool
    executableReceiptCreatesScientificSourceAuthority : Bool
    differentBytesCreateDifferentConfiguration : Bool
    sameThreeCVCreatesSameSourceBytes : Bool
open AdKPDBCVManifestExtensionalityBoundary public

canonicalAdKPDBCVManifestExtensionalityBoundary :
  AdKPDBCVManifestExtensionalityBoundary
canonicalAdKPDBCVManifestExtensionalityBoundary =
  adk-pdb-cv-manifest-extensionality-boundary
    true true true true true true true true true
    false false false false
