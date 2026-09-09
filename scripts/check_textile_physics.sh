#!/usr/bin/env bash
set -euo pipefail

AGDA_BIN="${AGDA_BIN:-agda}"
AGDA_STDLIB="${AGDA_STDLIB:-/usr/share/agda/lib/stdlib}"

"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Textile/TextileMechanicalDimensionExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Textile/TextileMechanicalFibreExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Textile/LinearElasticTextileLawExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Textile/QuasiStaticTextileLoadTransferExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Textile/TextileFailureSlipPredicateExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Textile/FiniteTextileEquilibriumNetworkExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Topology/TextileStitchHyperfabricExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Topology/TextileStitchOperationalSemanticsExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Topology/CircularKnittingHelicalLoopBridgeExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Topology/CrochetHookMicroSemanticsExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Textile/JacquardPhysicalFibreBridgeExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Textile/StitchPhysicalFibreBridgeExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/TextilePhysicsValidation.agda
