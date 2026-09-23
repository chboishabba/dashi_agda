#!/usr/bin/env bash
set -euo pipefail

CORE="DASHI/Core/WorldRepresentationSeparationExact.agda"
UNDER="DASHI/Core/TheoryUnderdeterminationExperimentExact.agda"
BRIDGE="DASHI/Biology/WorldRegularityHyperformalismCrossPollinationExact.agda"
EVO="DASHI/Biology/Evolution/EvolutionaryWorldCouplingTheoryBoundaryExact.agda"
LAW="DASHI/Physics/Laws/WorldLawStateTheorySeparationExact.agda"

for file in "$CORE" "$UNDER" "$BRIDGE" "$EVO" "$LAW"; do
  [[ -f "$file" ]] || { echo "missing world/theory separation source: $file" >&2; exit 1; }
done

require() {
  local needle="$1"
  local file="$2"
  grep -Fq "$needle" "$file" || {
    echo "missing required world/theory separation term: $needle ($file)" >&2
    exit 1
  }
}

require "worldRegularityDoesNotRequireRepresentation" "$CORE"
require "theoryRevisionDoesNotRequireWorldRevision" "$CORE"
require "gravityObservationNonFactorability" "$CORE"
require "coarseFallCannotExhaustGravityRegularity" "$CORE"
require "fallQueryFactorsThroughObservation" "$CORE"
require "consumerQueryCanFactorWhileWorldRegularityDoesNot" "$CORE"
require "birdLikeGravityCoupling" "$CORE"
require "canonicalWorldRepresentationBoundary" "$CORE"

require "WorldTheoryHyperfabricCell" "$BRIDGE"
require "birdFlightGravityCell" "$BRIDGE"
require "newtonianGravityCell" "$BRIDGE"
require "relativisticGravityCellSameWorld" "$BRIDGE"
require "wrongTypeBoundary" "$BRIDGE"
require "gravityNonFactorability" "$BRIDGE"
require "canonicalWorldTheoryHyperfabricBoundary" "$BRIDGE"

echo "world/theory separation cross-pollination static contract: OK"

require "sharedRegimeAgreement" "$UNDER"
require "discriminatingRegimeSeparates" "$UNDER"
require "coarseEvidenceNotPointIdentifiable" "$UNDER"
require "discriminatingEvidenceAIsPointIdentifiable" "$UNDER"
require "canonicalTheoryUnderdeterminationBoundary" "$UNDER"

require "adaptationDoesNotRequireExplicitTheory" "$EVO"
require "fitnessDoesNotManufactureAgentBelief" "$EVO"
require "canonicalEvolutionaryWorldCouplingBoundary" "$EVO"

require "worldDoesNotDefinitionallyEqualLaw" "$LAW"
require "lawDoesNotDefinitionallyEqualInitialCondition" "$LAW"
require "stateChangeDoesNotRequireLawChange" "$LAW"
require "canonicalTheoryRecoveryBoundary" "$LAW"
require "canonicalGravityPreTheoryBoundary" "$LAW"
