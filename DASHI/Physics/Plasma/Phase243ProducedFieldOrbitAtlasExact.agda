module DASHI.Physics.Plasma.Phase243ProducedFieldOrbitAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.Phase243FreeBoundarySixExact as FB6
import DASHI.Physics.Plasma.ZeroBouncePopulationExact as ZeroBounce

------------------------------------------------------------------------
-- P6: PRODUCED-FIELD ORBIT ATLAS
--
-- An orbit row can only be constructed from a solved P5 free-boundary case.
-- Target-surface fields, current-potential inversions, and rejected P5 cases
-- have no constructor here.
------------------------------------------------------------------------

record OrbitProtocol : Set₁ where
  constructor orbit-protocol
  field
    population : ZeroBounce.DeclaredParticlePopulation
    pitchGridReceipt : Set
    radialGridReceipt : Set
    energyGridReceipt : Set
    launchPhaseReceipt : Set
    timeHorizonReceipt : Set
    collisionModelReceipt : Set
    integratorReceipt : Set
    toleranceReceipt : Set
    normalizationReceipt : Set
    protocolReference : String

open OrbitProtocol public

record ProducedFieldOrbitRow (candidate : FB6.Candidate6) : Set₁ where
  constructor produced-field-orbit-row
  field
    equilibrium : FB6.SolvedFreeBoundaryCase candidate
    protocol : OrbitProtocol

    totalFieldFromEquilibriumUsedReceipt : Set
    noTargetFieldSubstitutionReceipt : Set

    mirrorTurningObservation : Set
    continuousPassingObservation : Set
    trappedFractionObservation : Set
    parallelInvariantObservation : Set
    bounceAveragedRadialDriftObservation : Set
    maximumJObservation : Set
    effectiveRippleObservation : Set
    finiteOrbitWidthObservation : Set
    curvatureGradBDriftObservation : Set
    energeticParticleLossObservation : Set
    collisionRobustnessObservation : Set
    orbitProvenance : String

open ProducedFieldOrbitRow public

record ProducedFieldOrbitComparison
    (left right : FB6.Candidate6) : Set₁ where
  constructor produced-field-orbit-comparison
  field
    leftRow : ProducedFieldOrbitRow left
    rightRow : ProducedFieldOrbitRow right
    sameProtocolReceipt : Set
    sameIntegratorReceipt : Set
    sameNormalizationReceipt : Set
    samePopulationReceipt : Set
    comparisonReceipt : Set
    comparisonReference : String

open ProducedFieldOrbitComparison public

record ProducedFieldOrbitBoundary : Set where
  constructor produced-field-orbit-boundary
  field
    rejectedFreeBoundaryCaseCanEnterOrbitAtlas : Bool
    rejectedFreeBoundaryCaseCanEnterOrbitAtlasIsFalse :
      rejectedFreeBoundaryCaseCanEnterOrbitAtlas ≡ false
    targetSurfaceFieldCanReplaceProducedTotalField : Bool
    targetSurfaceFieldCanReplaceProducedTotalFieldIsFalse :
      targetSurfaceFieldCanReplaceProducedTotalField ≡ false
    sameProtocolRequiredForRanking : Bool
    sameProtocolRequiredForRankingIsTrue : sameProtocolRequiredForRanking ≡ true
    zeroMirrorTurningAlonePaysFullConfinement : Bool
    zeroMirrorTurningAlonePaysFullConfinementIsFalse :
      zeroMirrorTurningAlonePaysFullConfinement ≡ false
    orbitArtifactBecomesExperimentalObservation : Bool
    orbitArtifactBecomesExperimentalObservationIsFalse :
      orbitArtifactBecomesExperimentalObservation ≡ false

canonicalProducedFieldOrbitBoundary : ProducedFieldOrbitBoundary
canonicalProducedFieldOrbitBoundary =
  produced-field-orbit-boundary
    false refl
    false refl
    true refl
    false refl
    false refl

p6AcceptanceRule : String
p6AcceptanceRule =
  "Only a SolvedFreeBoundaryCase may enter P6. Orbit metrics must be recomputed on that case's B_total under one declared population/integrator/normalization protocol. Zero mirror turning is necessary for the declared zero-bounce target but does not replace drift, FOW, energetic-particle, collision, turbulence or engineering consumers."
