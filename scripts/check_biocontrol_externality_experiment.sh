#!/usr/bin/env bash
set -euo pipefail

FILES=(
  DASHI/Environment/BiocontrolExternalityExperimentRegression.agda
  DASHI/Environment/WaterHyacinthLESRegression.agda
  DASHI/Environment/BiocontrolActiveExperimentSearchRegression.agda
  DASHI/Environment/BiocontrolExternalityExperimentExact.agda
  DASHI/Environment/WaterHyacinthLESExact.agda
  DASHI/Environment/BiocontrolActiveExperimentSearchExact.agda
)

for file in "${FILES[@]}"; do
  test -f "$file"
done

for file in "${FILES[@]}"; do
  agda -i . "$file"
done
