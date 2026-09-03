#!/usr/bin/env bash
set -euo pipefail

ROOT="DASHI/Cognition/PNF/ContextualFractranHyperformalismEverything.agda"

echo "[contextual-fractran] checking ${ROOT}"
agda -i . "${ROOT}"
echo "[contextual-fractran] OK"
