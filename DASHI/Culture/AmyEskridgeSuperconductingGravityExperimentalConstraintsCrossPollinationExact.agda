module DASHI.Culture.AmyEskridgeSuperconductingGravityExperimentalConstraintsCrossPollinationExact where

open import DASHI.Core.Prelude

import DASHI.Culture.AmyEskridgeLiTorrSourceConstitutiveCrossPollinationExact as X
import DASHI.Physics.ExoticGravity.SuperconductingGravityExperimentalConstraintRegistryExact as E
import DASHI.Physics.ExoticGravity.SuperconductingConstraintObservationRouteExact as Route
import DASHI.Physics.ExoticGravity.SuperconductingConstraintSourceAttributionMigrationExact as SourceMig
import DASHI.Physics.ExoticGravity.SuperconductingSourceConstitutiveEvidenceBidiExact as B
import DASHI.Physics.GR.GravitationalObservationBidiExact as Obs

------------------------------------------------------------------------
-- ESKRIDGE x PUBLIC EXPERIMENTAL CONSTRAINTS
--
-- Public advocacy and historical mechanism interest are not promoted by later
-- experimental claims.  Typed observation routing and source-attribution
-- migration remain owned by the physics lane; Amy consumes them as constraints.
------------------------------------------------------------------------

record ExperimentalCrossPollination : Set where
  constructor experimental-cross-pollination
  field
    nullReplicationsImportedAsConstraints : Bool
    nullReplicationsImportedAsConstraintsIsTrue :
      nullReplicationsImportedAsConstraints ≡ true

    artifactAttributionsImportedAsConstraints : Bool
    artifactAttributionsImportedAsConstraintsIsTrue :
      artifactAttributionsImportedAsConstraints ≡ true

    transitionMismatchImportedAsDiscriminator : Bool
    transitionMismatchImportedAsDiscriminatorIsTrue :
      transitionMismatchImportedAsDiscriminator ≡ true

    largeEnhancementModelsConstrained : Bool
    largeEnhancementModelsConstrainedIsTrue :
      largeEnhancementModelsConstrained ≡ true

    experimentalConstraintsProveEskridgeWrong : Bool
    experimentalConstraintsProveEskridgeWrongIsFalse :
      experimentalConstraintsProveEskridgeWrong ≡ false

    experimentalConstraintsEstablishNonzeroEtaC : Bool
    experimentalConstraintsEstablishNonzeroEtaCIsFalse :
      experimentalConstraintsEstablishNonzeroEtaC ≡ false

canonicalExperimentalCrossPollination : ExperimentalCrossPollination
canonicalExperimentalCrossPollination = experimental-cross-pollination
  true refl
  true refl
  true refl
  true refl
  false refl
  false refl

------------------------------------------------------------------------
-- Exact reuse of typed physics-side observation routing.
------------------------------------------------------------------------

hathawayStaticWeightRoute : Route.ConstraintObservationRouteReceipt
hathawayStaticWeightRoute = Route.hathawayReplicationRoute

hathawayRoutesToStaticLoad :
  Route.route hathawayStaticWeightRoute
    ≡ Route.typedGravityConstraint Obs.staticLoadOrWeight
hathawayRoutesToStaticLoad = refl

tajmarAngularRoute : Route.ConstraintObservationRouteReceipt
tajmarAngularRoute = Route.tajmarTransitionMismatchRoute

tajmarRemainsCompositeAngular :
  Route.route tajmarAngularRoute ≡ Route.compositeAngularSensorConstraint
tajmarRemainsCompositeAngular = refl

------------------------------------------------------------------------
-- Partial source attribution is also retained exactly.  Neither candidate is a
-- complete ObservationAttributedSource yet.
------------------------------------------------------------------------

hathawaySourceCandidate : SourceMig.ConstraintSourceCandidate
hathawaySourceCandidate = SourceMig.hathawaySourceCandidate

tajmarSourceCandidate : SourceMig.ConstraintSourceCandidate
tajmarSourceCandidate = SourceMig.tajmarTransitionSourceCandidate

tajmarStableIdentifierRetained :
  SourceMig.stableIdentifier tajmarSourceCandidate
    ≡ SourceMig.stableIdentifierKnown "arXiv:0707.3806"
tajmarStableIdentifierRetained = refl

record AmyConstraintObservationBoundary : Set where
  constructor amy-constraint-observation-boundary
  field
    amyLaneMayConsumePhysicsConstraintRouting : Bool
    amyLaneMayConsumePartialSourceCandidates : Bool
    legacyMeasuredChannelStringIsObservationReceipt : Bool
    legacySourceReferenceStringIsCompleteAttributedSource : Bool
    staticWeightConstraintEqualsFreeFallConstraint : Bool
    tajmarAngularConstraintMayBeCoercedToStaticWeight : Bool
    typedConstraintRouteRetroactivelyCreatesAmyStatement : Bool
    partialConstraintSourceRetroactivelyCreatesAmyStatement : Bool

canonicalAmyConstraintObservationBoundary : AmyConstraintObservationBoundary
canonicalAmyConstraintObservationBoundary =
  amy-constraint-observation-boundary
    true true false false false false false false

experimentalFrontier : B.EvidenceLeaf
experimentalFrontier = B.currentFirstOpenEvidenceLeaf
