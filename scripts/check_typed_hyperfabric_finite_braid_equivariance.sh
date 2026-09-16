#!/usr/bin/env bash
set -euo pipefail

owner="DASHI/Reasoning/TypedHyperfabricFiniteBraidEquivarianceExact.agda"
validation="DASHI/Reasoning/TypedHyperfabricFiniteBraidEquivarianceValidation.agda"
rolemap="DASHI/Reasoning/LocalFibreHyperfabricExact.agda"

require() {
  local needle="$1"
  local file="$2"
  grep -Fq "$needle" "$file" || {
    echo "missing required contract: $needle in $file" >&2
    exit 1
  }
}

require "TypedHyperfabricBraidEquivariance" "$owner"
require "vertexStalkIso" "$owner"
require "edgeStalkIso" "$owner"
require "actIncidence" "$owner"
require "restrictionEquivariant" "$owner"
require "TypedHyperfabricBraidSectionTransport" "$owner"
require "finiteTwoStrandSectionTransportConstructed" "$owner"
require "actionTraceAlonePaysHyperfabricBraidTransportIsFalse" "$owner"
require "arbitraryTypedHyperfabricAutomaticallyBraidEquivariantIsFalse" "$owner"
require "braidEquivarianceAutomaticallyAuthorizesConsumerQuotientIsFalse" "$owner"

require "finiteBraidOwnsDeformationAuthority" "$validation"
require "actionTraceAloneDoesNotPayBraidTransport" "$validation"
require "arbitraryFabricDoesNotAutomaticallyAdmitBraid" "$validation"

require "FiniteBraidRhizomeCalculus" "$rolemap"
require "TypedHyperfabricFiniteBraidEquivarianceExact" "$rolemap"
require "braidDeformationLiftedToGenericHyperfabricTransport" "$rolemap"
require "generic braidDeformationLiftedToGenericHyperfabricTransport remains unpaid" "$rolemap"

echo "typed hyperfabric finite braid equivariance static contract: source surface present"
