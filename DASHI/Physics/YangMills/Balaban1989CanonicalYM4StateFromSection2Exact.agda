module DASHI.Physics.YangMills.Balaban1989CanonicalYM4StateFromSection2Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- DASHI CONTRIBUTION
--
-- Remove an unnecessary degree of freedom from the complete-density dictionary.
-- A caller no longer supplies an arbitrary repository YM4 state and six
-- unrelated implications.  Instead it supplies the six scalar coordinates
-- extracted from the SAME Sect.-2 density and their source bounds; the
-- repository state is then canonical by construction.
--
-- This does not manufacture the physical estimates.  The remaining source
-- work is exactly to extract the scalar coordinates in the repository norm
-- conventions from CMP119/CMP122/CMP99 and the coupling history.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989Theorem1UVStabilityExact as Source
import DASHI.Physics.YangMills.Balaban1989CompleteDensityToYM4RegionExact as Direct
import DASHI.Physics.YangMills.BalabanYM4RGInvariantRegionPhysicalGapExact as RG

record Section2CanonicalYM4Coordinates
    {Coupling Density : Set}
    {flow : Source.Balaban1989EffectiveDensityFlow Coupling Density}
    (parameters : RG.YM4RGRegionParameters) : Set₁ where
  field
    couplingCoordinate : Nat → ℚ
    smallFieldCoordinate : Nat → ℚ
    largeFieldCoordinate : Nat → ℚ
    covarianceCoordinate : Nat → ℚ
    latticeDecayCoordinate : Nat → ℚ
    inverseSpacingCoordinate : Nat → ℚ

    section2FormCouplingBound : ∀ scale →
      Source.InSection2DensityClass flow scale (Source.densityAt flow scale) →
      couplingCoordinate scale ≤ RG.couplingCap parameters

    section2SmallFieldBound : ∀ scale →
      Source.Section2ConditionsAndBounds flow scale (Source.densityAt flow scale) →
      smallFieldCoordinate scale ≤ RG.smallFieldCap parameters

    section2LargeFieldBound : ∀ scale →
      Source.Section2ConditionsAndBounds flow scale (Source.densityAt flow scale) →
      largeFieldCoordinate scale ≤ RG.largeFieldCap parameters

    section2CovarianceBound : ∀ scale →
      Source.Section2ConditionsAndBounds flow scale (Source.densityAt flow scale) →
      covarianceCoordinate scale ≤ RG.covarianceCap parameters

    section2DecayNonnegative : ∀ scale →
      Source.Section2ConditionsAndBounds flow scale (Source.densityAt flow scale) →
      0ℚ ≤ latticeDecayCoordinate scale

    sourceInverseSpacingNonnegative : ∀ scale →
      0ℚ ≤ inverseSpacingCoordinate scale

open Section2CanonicalYM4Coordinates public

canonicalYM4State :
  ∀ {Coupling Density parameters}
    {flow : Source.Balaban1989EffectiveDensityFlow Coupling Density} →
  Section2CanonicalYM4Coordinates {flow = flow} parameters →
  Nat → RG.YM4RGState
canonicalYM4State coordinates scale =
  RG.rgState
    (couplingCoordinate coordinates scale)
    (smallFieldCoordinate coordinates scale)
    (largeFieldCoordinate coordinates scale)
    (covarianceCoordinate coordinates scale)
    (latticeDecayCoordinate coordinates scale)
    (inverseSpacingCoordinate coordinates scale)

asCompleteDensityYM4RegionDictionary :
  ∀ {Coupling Density parameters}
    {flow : Source.Balaban1989EffectiveDensityFlow Coupling Density} →
  (coordinates : Section2CanonicalYM4Coordinates {flow = flow} parameters) →
  Direct.CompleteDensityYM4RegionDictionary {flow = flow} parameters
asCompleteDensityYM4RegionDictionary coordinates = record
  { Direct.CompleteDensityYM4RegionDictionary.stateAt =
      canonicalYM4State coordinates
  ; Direct.CompleteDensityYM4RegionDictionary.sourceFormGivesCouplingCap =
      section2FormCouplingBound coordinates
  ; Direct.CompleteDensityYM4RegionDictionary.sourceBoundsGiveSmallFieldCap =
      section2SmallFieldBound coordinates
  ; Direct.CompleteDensityYM4RegionDictionary.sourceBoundsGiveLargeFieldCap =
      section2LargeFieldBound coordinates
  ; Direct.CompleteDensityYM4RegionDictionary.sourceBoundsGiveCovarianceCap =
      section2CovarianceBound coordinates
  ; Direct.CompleteDensityYM4RegionDictionary.sourceBoundsGiveDecayNonnegative =
      section2DecayNonnegative coordinates
  ; Direct.CompleteDensityYM4RegionDictionary.sourceGeometryGivesInverseSpacingNonnegative =
      sourceInverseSpacingNonnegative coordinates
  }

sourceTheoremGivesCanonicalYM4InvariantRegion :
  ∀ {Coupling Density parameters}
    {flow : Source.Balaban1989EffectiveDensityFlow Coupling Density}
    (coordinates : Section2CanonicalYM4Coordinates {flow = flow} parameters)
    (theorem1 : Source.Balaban1989Theorem1Witness flow)
    scale →
  RG.InYM4RGInvariantRegion parameters
    (canonicalYM4State coordinates scale)
sourceTheoremGivesCanonicalYM4InvariantRegion coordinates theorem1 =
  Direct.sourceTheoremGivesYM4InvariantRegion
    (asCompleteDensityYM4RegionDictionary coordinates)
    theorem1

balaban1989CanonicalYM4StateConstructionLevel : ProofLevel
balaban1989CanonicalYM4StateConstructionLevel = machineChecked

balaban1989CanonicalSection2ToYM4RegionLevel : ProofLevel
balaban1989CanonicalSection2ToYM4RegionLevel = machineChecked

-- Remaining physical seam: extract these six coordinates from the literal
-- complete-density objects in the exact repository norm/spacing conventions.
balaban1989Section2ScalarCoordinateExtractionLevel : ProofLevel
balaban1989Section2ScalarCoordinateExtractionLevel = conditional
