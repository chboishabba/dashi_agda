module DASHI.Programmes.DashiQCarbonConstantsHistoricalSourceBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Programmes.ResearchProgrammeExact as Programme
import DASHI.Programmes.QuantumExact as Quantum
import DASHI.Chemistry.CarbonChemicalSuitabilityLifeBoundaryExact as Carbon
import DASHI.Physics.Foundations.FundamentalConstantViabilityFibreExact as Viability

------------------------------------------------------------------------
-- HISTORICAL DASHIQ SOURCE BRIDGE
--
-- The dashiQ README/CONTEXT historical synthesis explicitly records the earlier
-- programme sequence:
--   periodic-table/kernel filling -> carbon suitability/"inevitability" claim
--   -> structure versus numerical scale -> constants
--   -> multiverse versus attractors -> MDL over universes -> cosmology.
--
-- This source bridge recovers that provenance while correcting claim strength.
-- The historical phrase "inevitability of carbon" is retained as a source
-- label, not promoted to a theorem that carbon abundance, life, or cosmic
-- inevitability follows from the periodic-table skeleton alone.
------------------------------------------------------------------------

record DashiQHistoricalSource : Set where
  constructor dashiq-historical-source
  field
    repository : String
    sourceSurface : String
    carbonHistoricalClaim : String
    constantsHistoricalClaim : String
    multiverseAttractorHistoricalClaim : String
    explicitOpenBoundary : String

canonicalDashiQCarbonConstantsSource : DashiQHistoricalSource
canonicalDashiQCarbonConstantsSource =
  dashiq-historical-source
    "github.com/chboishabba/dashiQ"
    "README.md / CONTEXT.md historical synthesis"
    "Periodic-table/kernel-filling discussion records valence skeleton, group recurrence, carbon/tetrahedral-bonding suitability and the historical phrase 'inevitability of carbon'."
    "Structure-versus-scale discussion records that exact numerical constants and exact energies were not derived; numerical scale-setting remained open."
    "Cosmology discussion explicitly explored multiverse versus attractors and MDL over universes as hypotheses/selection pictures."
    "The same historical source explicitly lists absolute numerical constants, exact masses/couplings, Planck-scale value and fine nuclear structure as open rather than proved."

quantumProgramme : Programme.ResearchProgramme
quantumProgramme = Quantum.dashiQProgramme

carbonBoundary : Carbon.CarbonChemicalSuitabilityBoundary
carbonBoundary = Carbon.canonicalCarbonChemicalSuitabilityBoundary

viabilityBoundary : Viability.FundamentalConstantViabilityBoundary
viabilityBoundary = Viability.canonicalFundamentalConstantViabilityBoundary

record DashiQCarbonConstantsSourceBoundary : Set where
  constructor dashiq-carbon-constants-source-boundary
  field
    historicalInevitabilityPhraseIsExactCarbonAbundanceTheorem : Bool
    historicalInevitabilityPhraseIsExactCarbonAbundanceTheoremIsFalse :
      historicalInevitabilityPhraseIsExactCarbonAbundanceTheorem ≡ false
    historicalCarbonSuitabilityProvesAbiogenesis : Bool
    historicalCarbonSuitabilityProvesAbiogenesisIsFalse :
      historicalCarbonSuitabilityProvesAbiogenesis ≡ false
    historicalConstantsDiscussionDerivedExactConstants : Bool
    historicalConstantsDiscussionDerivedExactConstantsIsFalse :
      historicalConstantsDiscussionDerivedExactConstants ≡ false
    multiverseVersusAttractorDiscussionProvesEitherOntology : Bool
    multiverseVersusAttractorDiscussionProvesEitherOntologyIsFalse :
      multiverseVersusAttractorDiscussionProvesEitherOntology ≡ false
    historicalSourceCanSeedCurrentBidiDiscriminatorProgramme : Bool
    historicalSourceCanSeedCurrentBidiDiscriminatorProgrammeIsTrue :
      historicalSourceCanSeedCurrentBidiDiscriminatorProgramme ≡ true

canonicalDashiQCarbonConstantsSourceBoundary : DashiQCarbonConstantsSourceBoundary
canonicalDashiQCarbonConstantsSourceBoundary =
  dashiq-carbon-constants-source-boundary
    false refl
    false refl
    false refl
    false refl
    true refl
