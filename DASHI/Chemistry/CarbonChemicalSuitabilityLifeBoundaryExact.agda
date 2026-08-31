module DASHI.Chemistry.CarbonChemicalSuitabilityLifeBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- CARBON CHEMICAL SUITABILITY / LIFE BOUNDARY
--
-- Cross-pollinates the historical dashiQ chemistry discussion with the current
-- prebiotic/Levin BIDI lane.  Carbon's tetravalence and unusually broad stable
-- covalent chemistry make it a strong candidate carrier for complex aqueous
-- chemistry; that does not by itself prove carbon is uniquely necessary, that
-- life follows from carbon chemistry, or that life is cosmically inevitable.
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
    true refl
    false refl
    "Carbon's chemical suitability is a chemistry claim about reachable molecular structure under an environment. It is kept separate from stellar production abundance, abiogenesis, uniqueness among every possible substrate, consciousness, and any claim that life is inevitable."
