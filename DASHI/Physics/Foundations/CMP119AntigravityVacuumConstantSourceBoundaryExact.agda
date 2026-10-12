{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityVacuumConstantSourceBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- PRIMARY-SOURCE BOUNDARY FOR THE VACUUM CONSTANT
--
-- Bałaban, CMP 109 (1987), 249--301, source extract:
--   Docs/support/reference/balaban-source-extracts/
--   cmp109-effective-actions-part-i.txt
--   DOI: 10.1007/BF01215223
--
-- The extract says an additional vacuum-energy counterterm is needed and is
-- contained in the normalization factors in the fluctuation integrals.
--
-- Bałaban, CMP 119 (1988), 243--285, source extract:
--   Docs/support/reference/balaban-source-extracts/
--   cmp119-rg-lattice-gauge-i.txt
--   DOI: 10.1007/BF01217741
--
-- The extract explicitly names the vacuum-energy counterterm and gives bounds
-- for it.  This supports the role "vacuum-energy constant / normalization
-- coordinate".  It does NOT provide in this repo a selected numerical V_k,
-- a metric derivative, a cosmological renormalization convention, or an
-- identification with gravitational Lambda.
------------------------------------------------------------------------

cmp109SourcePath : String
cmp109SourcePath =
  "Docs/support/reference/balaban-source-extracts/cmp109-effective-actions-part-i.txt"

cmp109DOI : String
cmp109DOI = "10.1007/BF01215223"

cmp119SourcePath : String
cmp119SourcePath =
  "Docs/support/reference/balaban-source-extracts/cmp119-rg-lattice-gauge-i.txt"

cmp119DOI : String
cmp119DOI = "10.1007/BF01217741"

cmp109VacuumCountertermContainedInNormalizationFactors : Bool
cmp109VacuumCountertermContainedInNormalizationFactors = true

cmp119NamesVacuumEnergyCounterterm : Bool
cmp119NamesVacuumEnergyCounterterm = true

preferredScalarVacuumRepresentationSourceSupported : Bool
preferredScalarVacuumRepresentationSourceSupported = true

sourceFixesVacuumNumericValue : Bool
sourceFixesVacuumNumericValue = false

sourceIdentifiesVacuumConstantWithPhysicalLambda : Bool
sourceIdentifiesVacuumConstantWithPhysicalLambda = false

sourceProvesMetricResponseOfVacuumConstant : Bool
sourceProvesMetricResponseOfVacuumConstant = false

record VacuumConstantSourceBoundary : Set where
  constructor vacuum-constant-source-boundary
  field
    vacuumCountertermIsNormalizationCoordinate : Bool
    sourceSupportsConstantSemanticRole : Bool
    selectedNumericVacuumSequencePaidBySourceExcerpt : Bool
    gravitationalLambdaIdentificationPaidBySourceExcerpt : Bool
    metricVariationPaidBySourceExcerpt : Bool

canonicalVacuumConstantSourceBoundary : VacuumConstantSourceBoundary
canonicalVacuumConstantSourceBoundary =
  vacuum-constant-source-boundary true true false false false
