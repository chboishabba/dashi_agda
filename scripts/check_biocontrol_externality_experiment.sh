#!/usr/bin/env bash
set -euo pipefail

FILES=(
  DASHI/Environment/BiocontrolExternalityExperimentRegression.agda
  DASHI/Environment/WaterHyacinthLESRegression.agda
  DASHI/Environment/BiocontrolActiveExperimentSearchRegression.agda
  DASHI/Environment/BiocontrolCostedExperimentChoiceRegression.agda
  DASHI/Environment/BiocontrolAttributionSnowballRegression.agda
  DASHI/Environment/BiocontrolSIQuantityRegression.agda
  DASHI/Environment/BiocontrolChemistry369IndexRegression.agda
  DASHI/Environment/SpringfieldLakesAquaticWeedMechanicalRemovalRegression.agda
  DASHI/Environment/BiocontrolFirstImplementationRegression.agda
  DASHI/Environment/BiocontrolExternalityExperimentExact.agda
  DASHI/Environment/BiocontrolExternalityExperimentSourceAtlasExact.agda
  DASHI/Environment/WaterHyacinthLESExact.agda
  DASHI/Environment/BiocontrolActiveExperimentSearchExact.agda
  DASHI/Environment/BiocontrolCostedExperimentChoiceExact.agda
  DASHI/Environment/BiocontrolSIQuantityExact.agda
  DASHI/Environment/BiocontrolChemistry369IndexExact.agda
  DASHI/Environment/SpringfieldLakesAquaticWeedMechanicalRemovalExact.agda
  DASHI/Environment/BiocontrolFirstImplementationExact.agda
)

for file in "${FILES[@]}"; do
  test -f "$file"
done

for file in "${FILES[@]}"; do
  agda -i . "$file"
done
