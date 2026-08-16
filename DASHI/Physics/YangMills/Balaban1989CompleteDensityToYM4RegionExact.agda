module DASHI.Physics.YangMills.Balaban1989CompleteDensityToYM4RegionExact where

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
-- for the R Operation",
-- Communications in Mathematical Physics 122 (1989), 355--392.
-- DOI: 10.1007/BF01238433.
--
-- DASHI CONTRIBUTION
--
-- Give the published complete-density theorem a direct target in the rational
-- YM4 invariant region, rather than forcing every published Sect.-2 estimate
-- back through an independently reconstructed one-step proof.
--
-- CMP119 Sect. 2 describes, on one common density:
--   * the small-field regular/localized E-sector,
--   * the strongly decaying R-sector (2.31),
--   * analytic localized boundary terms (2.40)--(2.42),
--   * regular background fields and their common analytic domains.
-- CMP122 Theorem 1 proves preservation of that complete inductive class when
-- the effective couplings remain sufficiently small.
--
-- Therefore, if a literal dictionary extracts the six scalar coordinates used
-- by DASHI's rational RG region from those SAME source bounds, all six region
-- fields hold at every source scale.  The proof below is pure conjunction
-- assembly; the remaining work is exactly the source/repository dictionary.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (0ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989Theorem1UVStabilityExact as Source
import DASHI.Physics.YangMills.BalabanYM4RGInvariantRegionPhysicalGapExact as RG

record CompleteDensityYM4RegionDictionary
    {Coupling Density : Set}
    {flow : Source.Balaban1989EffectiveDensityFlow Coupling Density}
    (parameters : RG.YM4RGRegionParameters) : Set₁ where
  field
    stateAt : Nat → RG.YM4RGState

    sourceFormGivesCouplingCap : ∀ scale →
      Source.InSection2DensityClass flow scale (Source.densityAt flow scale) →
      RG.runningCoupling (stateAt scale) ≤ RG.couplingCap parameters

    sourceBoundsGiveSmallFieldCap : ∀ scale →
      Source.Section2ConditionsAndBounds flow scale (Source.densityAt flow scale) →
      RG.smallFieldPolymerNorm (stateAt scale) ≤ RG.smallFieldCap parameters

    sourceBoundsGiveLargeFieldCap : ∀ scale →
      Source.Section2ConditionsAndBounds flow scale (Source.densityAt flow scale) →
      RG.largeFieldActivity (stateAt scale) ≤ RG.largeFieldCap parameters

    sourceBoundsGiveCovarianceCap : ∀ scale →
      Source.Section2ConditionsAndBounds flow scale (Source.densityAt flow scale) →
      RG.conditionalCovarianceNorm (stateAt scale) ≤ RG.covarianceCap parameters

    sourceBoundsGiveDecayNonnegative : ∀ scale →
      Source.Section2ConditionsAndBounds flow scale (Source.densityAt flow scale) →
      0ℚ ≤ RG.latticeDecayExponent (stateAt scale)

    sourceGeometryGivesInverseSpacingNonnegative : ∀ scale →
      0ℚ ≤ RG.inversePhysicalSpacing (stateAt scale)

open CompleteDensityYM4RegionDictionary public

sourceTheoremGivesYM4InvariantRegion :
  ∀ {Coupling Density parameters}
    {flow : Source.Balaban1989EffectiveDensityFlow Coupling Density}
    (dictionary : CompleteDensityYM4RegionDictionary {flow = flow} parameters)
    (theorem1 : Source.Balaban1989Theorem1Witness flow)
    scale →
  RG.InYM4RGInvariantRegion parameters (stateAt dictionary scale)
sourceTheoremGivesYM4InvariantRegion dictionary theorem1 scale = record
  { RG.InYM4RGInvariantRegion.couplingControlled =
      sourceFormGivesCouplingCap dictionary scale
        (Source.effectiveDensitiesPreserveSection2Form theorem1 scale)
  ; RG.InYM4RGInvariantRegion.smallFieldControlled =
      sourceBoundsGiveSmallFieldCap dictionary scale
        (Source.effectiveDensitiesSatisfySection2Bounds theorem1 scale)
  ; RG.InYM4RGInvariantRegion.largeFieldControlled =
      sourceBoundsGiveLargeFieldCap dictionary scale
        (Source.effectiveDensitiesSatisfySection2Bounds theorem1 scale)
  ; RG.InYM4RGInvariantRegion.covarianceControlled =
      sourceBoundsGiveCovarianceCap dictionary scale
        (Source.effectiveDensitiesSatisfySection2Bounds theorem1 scale)
  ; RG.InYM4RGInvariantRegion.latticeDecayNonnegative =
      sourceBoundsGiveDecayNonnegative dictionary scale
        (Source.effectiveDensitiesSatisfySection2Bounds theorem1 scale)
  ; RG.InYM4RGInvariantRegion.inverseSpacingNonnegative =
      sourceGeometryGivesInverseSpacingNonnegative dictionary scale
  }

balabanCompleteDensityToYM4RegionAssemblyLevel : ProofLevel
balabanCompleteDensityToYM4RegionAssemblyLevel = machineChecked

-- This is now the strongest source-reuse seam for Gate 4.  A successful literal
-- dictionary would make separate reconstructions of RG1a/RG1b/boundary closure
-- optional diagnostics rather than prerequisites to source-level UV stability.
balabanCompleteDensityYM4RegionDictionaryLevel : ProofLevel
balabanCompleteDensityYM4RegionDictionaryLevel = conditional
