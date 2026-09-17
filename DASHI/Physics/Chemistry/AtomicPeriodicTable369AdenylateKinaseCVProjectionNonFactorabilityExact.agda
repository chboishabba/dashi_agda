module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCVProjectionNonFactorabilityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.CoarseFineFabricCalculusExact as Coarse
import DASHI.Core.FactorisationSpineCrosswalkExact as Crosswalk
import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Geometry.RigidMotionSemidirectProductExact as SE3
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseAtomisticConfigurationExact as Config
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseAtomisticCVProjectionExact as Projection
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCOMGeometryExact as Geometry
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSourceAtomSelectionExact as Selection
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSIQuantityBridgeExact as SIAdK
import DASHI.Physics.Units.SI as SI

------------------------------------------------------------------------
-- DASHI-ORIGINAL EXTENSIONALITY / INFORMATION-LOSS THEOREM
--
-- Attribution boundary:
-- * Li-Liu-Ji 2015 source-pay the named theta1/theta2/dLN selection roles
--   already encoded in SourceAtomSelectionExact.
-- * Prohaska et al. source-pay the atomic-mass convention consumed by a
--   supplied COM evaluator, already encoded in AtomisticConfigurationExact.
-- * The extensionality relation, projection collision, and non-factorability
--   compiler below are DASHI bridge mathematics.  They are not claims made by
--   either scientific source and are not promoted from DOI/PDB identifiers.
------------------------------------------------------------------------

sourceSelectionAttributionRole : String
sourceSelectionAttributionRole =
  "Li-Liu-Ji 2015 pays the residue/domain selection roles only; the extensionality and non-factorability theorems here are DASHI-original"

massAttributionRole : String
massAttributionRole =
  "Prohaska et al. pays the mass convention only; mass-source attribution does not create a projection theorem"

------------------------------------------------------------------------
-- A COM evaluator is selection-extensional when its result depends only on
-- the selected mass/coordinate content relevant to that selection.
--
-- We deliberately leave SelectionEquivalent model-parametric.  Concrete PDB
-- evaluators may instantiate it by exact selected atom identity, masses and
-- coordinates; other evaluators may use a stronger relation.  The theorem
-- therefore does not smuggle one parser or byte representation into geometry.
------------------------------------------------------------------------

record SelectionExtensionalCOMModel
  {rigidModel : SE3.RigidMotionModel}
  (geometry : Geometry.AdKCOMGeometryModel rigidModel) : Set₁ where
  constructor selection-extensional-com-model
  field
    SelectionEquivalent :
      Config.AtomisticConfiguration →
      Config.AtomisticConfiguration →
      Selection.AtomSelectionSpec →
      Set

    centerOfMassExtensional :
      (left right : Config.AtomisticConfiguration) →
      (selection : Selection.AtomSelectionSpec) →
      SelectionEquivalent left right selection →
      Geometry.centerOfMass geometry left selection
      ≡ Geometry.centerOfMass geometry right selection
open SelectionExtensionalCOMModel public

selections : Selection.AdKThreeCVSelections
selections = Selection.canonicalAdKThreeCVSelections

------------------------------------------------------------------------
-- Equality on exactly the source-facing selection surface used by the three
-- CV projection.  Nothing here says the full configurations are equal.
------------------------------------------------------------------------

record ThreeCVSelectionEquivalent
  {rigidModel : SE3.RigidMotionModel}
  {geometry : Geometry.AdKCOMGeometryModel rigidModel}
  (extensional : SelectionExtensionalCOMModel geometry)
  (left right : Config.AtomisticConfiguration) : Set₁ where
  constructor three-cv-selection-equivalent
  field
    thetaOneFirstEquivalent :
      SelectionEquivalent extensional left right
        (Selection.thetaOneFirst selections)
    thetaOneVertexEquivalent :
      SelectionEquivalent extensional left right
        (Selection.thetaOneVertex selections)
    thetaOneThirdEquivalent :
      SelectionEquivalent extensional left right
        (Selection.thetaOneThird selections)
    thetaTwoFirstEquivalent :
      SelectionEquivalent extensional left right
        (Selection.thetaTwoFirst selections)
    thetaTwoVertexEquivalent :
      SelectionEquivalent extensional left right
        (Selection.thetaTwoVertex selections)
    thetaTwoThirdEquivalent :
      SelectionEquivalent extensional left right
        (Selection.thetaTwoThird selections)
    dLnFirstEquivalent :
      SelectionEquivalent extensional left right
        (Selection.dLnFirst selections)
    dLnSecondEquivalent :
      SelectionEquivalent extensional left right
        (Selection.dLnSecond selections)
open ThreeCVSelectionEquivalent public

------------------------------------------------------------------------
-- Concrete three-CV surface used for collision/non-factorability machinery.
------------------------------------------------------------------------

record ThreeCVSurface : Set where
  constructor three-cv-surface
  field
    thetaOneDegrees : Nat
    thetaTwoDegrees : Nat
    dLn : SI.Quantity SI.Length SIAdK.angstromScale
open ThreeCVSurface public

projectThreeCV :
  {rigidModel : SE3.RigidMotionModel} →
  (geometry : Geometry.AdKCOMGeometryModel rigidModel) →
  Config.AtomisticConfiguration →
  ThreeCVSurface
projectThreeCV geometry configuration =
  three-cv-surface
    (Geometry.angleOfThreeCOMs geometry configuration
      (Selection.thetaOneFirst selections)
      (Selection.thetaOneVertex selections)
      (Selection.thetaOneThird selections))
    (Geometry.angleOfThreeCOMs geometry configuration
      (Selection.thetaTwoFirst selections)
      (Selection.thetaTwoVertex selections)
      (Selection.thetaTwoThird selections))
    (Geometry.distanceOfTwoCOMs geometry configuration
      (Selection.dLnFirst selections)
      (Selection.dLnSecond selections))

threeCVSelectionEquivalentProjectsEqual :
  {rigidModel : SE3.RigidMotionModel} →
  {geometry : Geometry.AdKCOMGeometryModel rigidModel} →
  (extensional : SelectionExtensionalCOMModel geometry) →
  (left right : Config.AtomisticConfiguration) →
  ThreeCVSelectionEquivalent extensional left right →
  projectThreeCV geometry left ≡ projectThreeCV geometry right
threeCVSelectionEquivalentProjectsEqual extensional left right equivalent
  rewrite centerOfMassExtensional extensional left right
            (Selection.thetaOneFirst selections)
            (thetaOneFirstEquivalent equivalent)
        | centerOfMassExtensional extensional left right
            (Selection.thetaOneVertex selections)
            (thetaOneVertexEquivalent equivalent)
        | centerOfMassExtensional extensional left right
            (Selection.thetaOneThird selections)
            (thetaOneThirdEquivalent equivalent)
        | centerOfMassExtensional extensional left right
            (Selection.thetaTwoFirst selections)
            (thetaTwoFirstEquivalent equivalent)
        | centerOfMassExtensional extensional left right
            (Selection.thetaTwoVertex selections)
            (thetaTwoVertexEquivalent equivalent)
        | centerOfMassExtensional extensional left right
            (Selection.thetaTwoThird selections)
            (thetaTwoThirdEquivalent equivalent)
        | centerOfMassExtensional extensional left right
            (Selection.dLnFirst selections)
            (dLnFirstEquivalent equivalent)
        | centerOfMassExtensional extensional left right
            (Selection.dLnSecond selections)
            (dLnSecondEquivalent equivalent) = refl

------------------------------------------------------------------------
-- A witnessed distinct pair with equal CV-relevant selected geometry is an
-- explicit projection collision.  The pair can later be instantiated by real
-- PDB configurations, a parser-level mutation outside all selected groups, or
-- any other concrete same-selection witness.
------------------------------------------------------------------------

record DistinctSameCVSelectionPair
  {rigidModel : SE3.RigidMotionModel}
  {geometry : Geometry.AdKCOMGeometryModel rigidModel}
  (extensional : SelectionExtensionalCOMModel geometry) : Set₁ where
  constructor distinct-same-cv-selection-pair
  field
    leftConfiguration : Config.AtomisticConfiguration
    rightConfiguration : Config.AtomisticConfiguration
    selectedGeometryEquivalent :
      ThreeCVSelectionEquivalent extensional leftConfiguration rightConfiguration
    configurationsDiffer : leftConfiguration ≡ rightConfiguration → ⊥
open DistinctSameCVSelectionPair public

distinctSameSelectionPairCreatesCollision :
  {rigidModel : SE3.RigidMotionModel} →
  {geometry : Geometry.AdKCOMGeometryModel rigidModel} →
  (extensional : SelectionExtensionalCOMModel geometry) →
  DistinctSameCVSelectionPair extensional →
  Coarse.ProjectionCollision
    (projectThreeCV geometry)
    (λ configuration → configuration)
distinctSameSelectionPairCreatesCollision extensional pair =
  Coarse.projectionCollision
    (leftConfiguration pair)
    (rightConfiguration pair)
    (threeCVSelectionEquivalentProjectsEqual
      extensional
      (leftConfiguration pair)
      (rightConfiguration pair)
      (selectedGeometryEquivalent pair))
    (configurationsDiffer pair)

distinctSameSelectionPairCreatesNonFactorability :
  {rigidModel : SE3.RigidMotionModel} →
  {geometry : Geometry.AdKCOMGeometryModel rigidModel} →
  (extensional : SelectionExtensionalCOMModel geometry) →
  DistinctSameCVSelectionPair extensional →
  NonFactor.NonFactorabilityWitness
    (projectThreeCV geometry)
    (λ configuration → configuration)
distinctSameSelectionPairCreatesNonFactorability extensional pair =
  Crosswalk.projectionCollisionToNonFactorability
    (distinctSameSelectionPairCreatesCollision extensional pair)

threeCVCannotRecoverEveryConfiguration :
  {rigidModel : SE3.RigidMotionModel} →
  {geometry : Geometry.AdKCOMGeometryModel rigidModel} →
  (extensional : SelectionExtensionalCOMModel geometry) →
  (pair : DistinctSameCVSelectionPair extensional) →
  NonFactor.FactorsThrough
    (projectThreeCV geometry)
    (λ configuration → configuration) →
  ⊥
threeCVCannotRecoverEveryConfiguration extensional pair factor =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (distinctSameSelectionPairCreatesNonFactorability extensional pair)
    factor

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data SourceAttributionCreatesDASHITheorem : Set where
data ThreeCVRecoversFullConfiguration : Set where
data MirrorByteEqualityFollowsFromCVEquality : Set where

sourceAttributionDoesNotCreateDASHITheorem :
  SourceAttributionCreatesDASHITheorem → ⊥
sourceAttributionDoesNotCreateDASHITheorem ()

threeCVDoesNotRecoverFullConfiguration :
  ThreeCVRecoversFullConfiguration → ⊥
threeCVDoesNotRecoverFullConfiguration ()

cvEqualityDoesNotCreateMirrorByteEquality :
  MirrorByteEqualityFollowsFromCVEquality → ⊥
cvEqualityDoesNotCreateMirrorByteEquality ()

record AdKCVProjectionNonFactorabilityBoundary : Set where
  constructor adk-cv-projection-nonfactorability-boundary
  field
    selectionExtensionalCOMRequired : Bool
    threeCVSelectionEquivalenceExplicit : Bool
    sameSelectedGeometryCreatesSameThreeCV : Bool
    distinctSameCVPairCreatesProjectionCollision : Bool
    projectionCollisionReusesCanonicalFactorisationSpine : Bool
    sourceSelectionAttributionRetained : Bool
    massAttributionRetained : Bool
    sourceAttributionCreatesDASHITheorem : Bool
    threeCVRecoversFullConfiguration : Bool
    cvEqualityCreatesMirrorByteEquality : Bool
open AdKCVProjectionNonFactorabilityBoundary public

canonicalAdKCVProjectionNonFactorabilityBoundary :
  AdKCVProjectionNonFactorabilityBoundary
canonicalAdKCVProjectionNonFactorabilityBoundary =
  adk-cv-projection-nonfactorability-boundary
    true true true true true true true
    false false false
