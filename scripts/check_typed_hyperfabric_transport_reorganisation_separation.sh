#!/usr/bin/env bash
set -euo pipefail

owner="DASHI/Reasoning/TypedHyperfabricTransportReorganisationSeparationExact.agda"

[[ -f "$owner" ]]

grep -q 'WithinFabricTransportSurface' "$owner"
grep -q 'CrossFabricReorganisationSurface' "$owner"
grep -q 'ruinReorganisationChangesIncidenceWithoutStalkErasure' "$owner"
grep -q 'sameEndpointDoesNotDetermineTransportedPhase' "$owner"
grep -q 'withinFabricTransportDoesNotAutomaticallyConstructCrossFabricReorganisation' "$owner"
grep -q 'provenancePreservationDoesNotForceIncidencePreservation' "$owner"
grep -q 'canonicalTransportReorganisationBoundary' "$owner"
