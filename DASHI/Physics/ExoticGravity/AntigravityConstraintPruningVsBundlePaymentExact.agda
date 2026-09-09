module DASHI.Physics.ExoticGravity.AntigravityConstraintPruningVsBundlePaymentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.ExoticGravity.SuperconductingGravityExperimentalConstraintRegistryExact as Registry
import DASHI.Physics.ExoticGravity.SuperconductingConstraintObservationRouteExact as Route
import DASHI.Physics.ExoticGravity.SuperconductingConstraintSourceAttributionMigrationExact as SourceMigration
import DASHI.Physics.ExoticGravity.AntigravityResearchPromotionCutExact as Promotion

------------------------------------------------------------------------
-- LEGACY CONSTRAINTS PRUNE MODEL SPACE; THEY DO NOT PAY A SAME-APPARATUS CUT
--
-- The public constraint registry contains several scientifically relevant
-- experiments, but they are distinct apparatus/configuration carriers.  Their
-- results can constrain candidate mechanisms and discriminator choice without
-- being spliced into the four same-apparatus bundle receipts required by the
-- antigravity research-promotion cut.
------------------------------------------------------------------------

data ConstraintUse : Set where
  modelSpacePruning : ConstraintUse
  artifactConfounderGuidance : ConstraintUse
  transitionDiscriminatorGuidance : ConstraintUse
  magnitudeUpperBound : ConstraintUse
  sameApparatusBundlePayment : ConstraintUse

useForConstraintKind : Registry.ConstraintKind → ConstraintUse
useForConstraintKind Registry.nullReplication = modelSpacePruning
useForConstraintKind Registry.artifactAttributed = artifactConfounderGuidance
useForConstraintKind Registry.transitionMismatch = transitionDiscriminatorGuidance
useForConstraintKind Registry.largeTheoryUpperBound = magnitudeUpperBound
useForConstraintKind Registry.unresolvedSignal = transitionDiscriminatorGuidance

record ConstraintPruningReceipt : Set where
  constructor constraint-pruning-receipt
  field
    constraint : Registry.ExperimentalConstraint
    use : ConstraintUse
    useMatchesKind : useForConstraintKind (Registry.kind constraint) ≡ use
    typedObservationRoute : Route.ConstraintObservationRouteReceipt
    sourceCandidate : SourceMigration.ConstraintSourceCandidate
    exactPruningScope : String

open ConstraintPruningReceipt public

hathawayNullPruning : ConstraintPruningReceipt
hathawayNullPruning = constraint-pruning-receipt
  Registry.hathawayReplication
  modelSpacePruning
  refl
  Route.hathawayReplicationRoute
  SourceMigration.hathawaySourceCandidate
  "constrains Podkletnov-style weight/gravity-modification claims in the Hathaway apparatus/configuration; does not prove universal zero coupling"

tajmarTransitionPruning : ConstraintPruningReceipt
tajmarTransitionPruning = constraint-pruning-receipt
  Registry.tajmarTransitionMismatch
  transitionDiscriminatorGuidance
  refl
  Route.tajmarTransitionMismatchRoute
  SourceMigration.tajmarTransitionSourceCandidate
  "constrains simple superconducting-transition-locked interpretations because the reported onset did not coincide with the superconducting transition; retained as angular-sensor guidance"

tajmarMagnitudePruning : ConstraintPruningReceipt
tajmarMagnitudePruning = constraint-pruning-receipt
  Registry.tajmarLargeTheoryBound
  magnitudeUpperBound
  refl
  Route.tajmarLargeTheoryBoundRoute
  SourceMigration.tajmarLargeTheoryBoundSourceCandidate
  "constrains theories predicting very large frame-dragging-like responses in the Tajmar configuration; does not establish exact zero coupling"

nasaRFArtifactGuidance : ConstraintPruningReceipt
nasaRFArtifactGuidance = constraint-pruning-receipt
  Registry.nasaRFArrtifact
  artifactConfounderGuidance
  refl
  Route.nasaRFArtifactRoute
  SourceMigration.nasaRFArtifactSourceCandidate
  "retains the RF/instrumentation-artifact history as a mandatory ordinary-confounder design consideration rather than a gravity detection"

------------------------------------------------------------------------
-- Apparatus identity remains a first-class missing coordinate.
------------------------------------------------------------------------

data LegacyConstraintApparatus : Set where
  nasaStaticApparatus : LegacyConstraintApparatus
  nasaRFApparatus : LegacyConstraintApparatus
  hathawayRotatingDiskApparatus : LegacyConstraintApparatus
  tajmarSpinningRingApparatus : LegacyConstraintApparatus

apparatusForConstraint : Registry.ExperimentalConstraint → LegacyConstraintApparatus
apparatusForConstraint Registry.nasaStaticYBCO = nasaStaticApparatus
apparatusForConstraint Registry.nasaRFArrtifact = nasaRFApparatus
apparatusForConstraint Registry.hathawayReplication = hathawayRotatingDiskApparatus
apparatusForConstraint Registry.tajmarTransitionMismatch = tajmarSpinningRingApparatus
apparatusForConstraint Registry.tajmarLargeTheoryBound = tajmarSpinningRingApparatus

nasaAndHathawayApparatusDistinct :
  apparatusForConstraint Registry.nasaStaticYBCO
    ≡ apparatusForConstraint Registry.hathawayReplication → ⊥
nasaAndHathawayApparatusDistinct ()

hathawayAndTajmarApparatusDistinct :
  apparatusForConstraint Registry.hathawayReplication
    ≡ apparatusForConstraint Registry.tajmarTransitionMismatch → ⊥
hathawayAndTajmarApparatusDistinct ()

nasaRFAndTajmarApparatusDistinct :
  apparatusForConstraint Registry.nasaRFArrtifact
    ≡ apparatusForConstraint Registry.tajmarTransitionMismatch → ⊥
nasaRFAndTajmarApparatusDistinct ()

------------------------------------------------------------------------
-- No authority exists to concatenate heterogeneous legacy constraints into the
-- current same-apparatus experimental cut.  This is the exact no-stitch rule.
------------------------------------------------------------------------

data CrossExperimentBundleSynthesisAuthority : Set where

legacyConstraintRegistryCannotManufactureSameApparatusCut :
  CrossExperimentBundleSynthesisAuthority → Promotion.SameApparatusExperimentalCut
legacyConstraintRegistryCannotManufactureSameApparatusCut ()

record ConstraintPruningVsBundleBoundary : Set where
  constructor constraint-pruning-vs-bundle-boundary
  field
    legacyConstraintsMayPruneCandidateModels : Bool
    artifactHistoryMayRefineBackgroundControls : Bool
    transitionMismatchMayRefinePhaseDiscriminator : Bool
    upperBoundMayConstrainCandidateMagnitude : Bool
    heterogeneousExperimentsMayBeStitchedIntoOneApparatusReceipt : Bool
    nullReplicationAutomaticallyPaysCurrentReplicationBundle : Bool
    legacyConstraintAutomaticallyPaysCurrentSourceGeometryBundle : Bool
    pruningReceiptAutomaticallyProvesAntigravityFalse : Bool
    pruningReceiptAutomaticallyProvesAntigravityTrue : Bool

canonicalConstraintPruningVsBundleBoundary : ConstraintPruningVsBundleBoundary
canonicalConstraintPruningVsBundleBoundary =
  constraint-pruning-vs-bundle-boundary
    true true true true false false false false false
