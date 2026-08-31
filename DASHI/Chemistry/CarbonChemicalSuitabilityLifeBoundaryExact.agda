module DASHI.Chemistry.CarbonChemicalSuitabilityLifeBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Foundations.AtomicValenceFermionBridgeExact as Atomic

------------------------------------------------------------------------
-- CARBON CHEMICAL SUITABILITY / LIFE BOUNDARY
--
-- Cross-pollinates the historical dashiQ chemistry discussion with the current
-- prebiotic/Levin BIDI lane.  Carbon's tetravalence and unusually broad stable
-- covalent chemistry make it a strong candidate carrier for complex aqueous
-- chemistry; that does not by itself prove carbon is uniquely necessary, that
-- life follows from carbon chemistry, or that life is cosmically inevitable.
--
-- Existing DASHI atomic theory already supplies the key anti-collapse:
-- valence class alone does not predict all chemistry.  This owner therefore
-- treats periodic/valence structure as an upstream constraint, not a complete
-- carbon-chemistry theorem.
--
-- External calibration (not proof authority):
--  * The Astrobiology Primer v2.0 (2016), PMCID PMC5008114: carbon supports a
--    very broad covalent chemistry and all known terrestrial biochemistry is
--    carbon-based.
--  * Epelbaum et al., PRL 110, 112502 (2013), DOI
--    10.1103/PhysRevLett.110.112502: carbon/oxygen production through the
--    triple-alpha channel remains sensitive to fundamental-parameter changes.
------------------------------------------------------------------------

data BackboneCandidate : Set where
  carbonBackbone siliconBackbone otherBackbone : BackboneCandidate

data ChemicalSuitabilityCoordinate : Set where
  tetravalentBonding
  catenation
  multipleBondSupport
  aqueousStabilityReactivityBalance
  heteroatomDiversity
  redoxRange
  macromolecularCombinatorics
  : ChemicalSuitabilityCoordinate

record CarbonSuitabilityReceipt : Set where
  constructor carbon-suitability-receipt
  field
    valenceReference : String
    bondDiversityReference : String
    catenationReference : String
    solventContextReference : String
    temperaturePressureReference : String
    redoxReference : String
    competingBackboneReference : String
    molecularDiversityReference : String
    observationProvenanceReference : String
    validationReference : String

atomicValenceBoundary : Atomic.AtomicValenceFermionBoundary
atomicValenceBoundary = Atomic.canonicalAtomicValenceFermionBoundary

valenceClassAloneDoesNotPredictAllChemistry :
  Atomic.valenceClassAlonePredictsAllChemistry atomicValenceBoundary ≡ false
valenceClassAloneDoesNotPredictAllChemistry = refl

record CarbonChemicalSuitabilityBoundary : Set where
  constructor carbon-chemical-suitability-boundary
  field
    carbonSupportsRichChemistry : Bool
    carbonSupportsRichChemistryIsTrue : carbonSupportsRichChemistry ≡ true
    carbonRichChemistryImpliesLife : Bool
    carbonRichChemistryImpliesLifeIsFalse : carbonRichChemistryImpliesLife ≡ false
    carbonSuitabilityProvesCarbonUniqueForAllPossibleLife : Bool
    carbonSuitabilityProvesCarbonUniqueForAllPossibleLifeIsFalse :
      carbonSuitabilityProvesCarbonUniqueForAllPossibleLife ≡ false
    periodicTableStructureAloneFixesExactCarbonAbundance : Bool
    periodicTableStructureAloneFixesExactCarbonAbundanceIsFalse :
      periodicTableStructureAloneFixesExactCarbonAbundance ≡ false
    valenceClassAloneFixesCarbonChemistry : Bool
    valenceClassAloneFixesCarbonChemistryIsFalse :
      valenceClassAloneFixesCarbonChemistry ≡ false
    stellarCarbonProductionEqualsChemicalSuitability : Bool
    stellarCarbonProductionEqualsChemicalSuitabilityIsFalse :
      stellarCarbonProductionEqualsChemicalSuitability ≡ false
    carbonSuitabilityAndCarbonProductionRequireDifferentReceipts : Bool
    carbonSuitabilityAndCarbonProductionRequireDifferentReceiptsIsTrue :
      carbonSuitabilityAndCarbonProductionRequireDifferentReceipts ≡ true
    oneCarbonBasedBiosphereProvesLifeInevitable : Bool
    oneCarbonBasedBiosphereProvesLifeInevitableIsFalse :
      oneCarbonBasedBiosphereProvesLifeInevitable ≡ false
    reading : String

canonicalCarbonChemicalSuitabilityBoundary : CarbonChemicalSuitabilityBoundary
canonicalCarbonChemicalSuitabilityBoundary =
  carbon-chemical-suitability-boundary
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    false refl
    "Carbon's chemical suitability is downstream of atomic/valence constraints but is not fixed by valence class alone. It remains separate from stellar production abundance, abiogenesis, uniqueness among every possible substrate, consciousness, and any claim that life is inevitable."
