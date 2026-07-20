module Ontology.DNA.ChemistrySheetTowerBoundaryRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import Ontology.DNA.ChemistrySheetTowerBoundary

canonical-growth-is-fixed-four-way :
  canonicalDNACarrierGrowth ≡ fixedFourWayNesting
canonical-growth-is-fixed-four-way = refl

existing-uv-is-base-coordinate-pair :
  existingUVRepresentation ≡ baseCoordinatePair
existing-uv-is-base-coordinate-pair = refl

existing-surface-does-not-claim-multiscale-reconstruction :
  ExistingChemistryCoordinateSurface.multiscaleReconstructionProvided
    existingChemistryCoordinateSurface
  ≡ false
existing-surface-does-not-claim-multiscale-reconstruction = refl

existing-surface-does-not-claim-tetration :
  ExistingChemistryCoordinateSurface.tetrationalTowerProvided
    existingChemistryCoordinateSurface
  ≡ false
existing-surface-does-not-claim-tetration = refl

heatmap-alone-does-not-promote :
  heatmapAlonePromotesToSheetTower ≡ false
heatmap-alone-does-not-promote = refl

ragged-lengths-do-not-fix-growth-law :
  raggedLengthsAloneDetermineGrowthLaw ≡ false
ragged-lengths-do-not-fix-growth-law = refl
