module DASHI.Physics.YangMills.Balaban1989LiteralCompleteDensityStateCoordinatesExact where

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
-- Make the L5 state extraction SAME-OBJECT by construction.  The canonical
-- state has the six quantitative coordinates used by the downstream physical
-- argument
--
--        (g_k, K_k, L_k, C_k, mu_k, a_k^{-1}).
--
-- The running coupling is definitionally the coupling of the existing literal
-- CMP122 flow.  The remaining five coordinates are definitionally extracted
-- from the SAME complete density p_k.  Consequently there are no independent
-- equality fields of the form `repositoryK = sourceK`: all projection theorems
-- reduce to refl.  The only source-facing work left is to instantiate the five
-- extractor functions with the literal Sect.-2 quantities and their norms.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989Theorem1UVStabilityExact as Source

record CanonicalPhysicalRGState (Coupling Bound : Set) : Set where
  constructor physicalRGState
  field
    g : Coupling
    K L C mu aInverse : Bound
open CanonicalPhysicalRGState public

record CompleteDensityCoordinateMeaning
    {Coupling Density Bound : Set}
    (flow : Source.Balaban1989EffectiveDensityFlow Coupling Density) : Set₁ where
  field
    smallFieldPolymerNorm : Nat → Density → Bound
    largeFieldActivityNorm : Nat → Density → Bound
    conditionalCovarianceNorm : Nat → Density → Bound
    localizationExponent : Nat → Density → Bound
    inverseLatticeSpacing : Nat → Density → Bound

open CompleteDensityCoordinateMeaning public

stateFromCompleteDensity :
  ∀ {Coupling Density Bound}
    {flow : Source.Balaban1989EffectiveDensityFlow Coupling Density} →
  CompleteDensityCoordinateMeaning flow → Nat →
  CanonicalPhysicalRGState Coupling Bound
stateFromCompleteDensity {flow = flow} meaning scale = record
  { g = Source.couplingAt flow scale
  ; K = smallFieldPolymerNorm meaning scale (Source.densityAt flow scale)
  ; L = largeFieldActivityNorm meaning scale (Source.densityAt flow scale)
  ; C = conditionalCovarianceNorm meaning scale (Source.densityAt flow scale)
  ; mu = localizationExponent meaning scale (Source.densityAt flow scale)
  ; aInverse = inverseLatticeSpacing meaning scale (Source.densityAt flow scale)
  }

couplingIsLiteralFlowCoupling :
  ∀ {Coupling Density Bound}
    {flow : Source.Balaban1989EffectiveDensityFlow Coupling Density}
    (meaning : CompleteDensityCoordinateMeaning flow) scale →
  g (stateFromCompleteDensity meaning scale) ≡ Source.couplingAt flow scale
couplingIsLiteralFlowCoupling meaning scale = refl

smallFieldCoordinateIsLiteralDensityNorm :
  ∀ {Coupling Density Bound}
    {flow : Source.Balaban1989EffectiveDensityFlow Coupling Density}
    (meaning : CompleteDensityCoordinateMeaning flow) scale →
  K (stateFromCompleteDensity meaning scale)
  ≡ smallFieldPolymerNorm meaning scale (Source.densityAt flow scale)
smallFieldCoordinateIsLiteralDensityNorm meaning scale = refl

largeFieldCoordinateIsLiteralDensityNorm :
  ∀ {Coupling Density Bound}
    {flow : Source.Balaban1989EffectiveDensityFlow Coupling Density}
    (meaning : CompleteDensityCoordinateMeaning flow) scale →
  L (stateFromCompleteDensity meaning scale)
  ≡ largeFieldActivityNorm meaning scale (Source.densityAt flow scale)
largeFieldCoordinateIsLiteralDensityNorm meaning scale = refl

covarianceCoordinateIsLiteralDensityNorm :
  ∀ {Coupling Density Bound}
    {flow : Source.Balaban1989EffectiveDensityFlow Coupling Density}
    (meaning : CompleteDensityCoordinateMeaning flow) scale →
  C (stateFromCompleteDensity meaning scale)
  ≡ conditionalCovarianceNorm meaning scale (Source.densityAt flow scale)
covarianceCoordinateIsLiteralDensityNorm meaning scale = refl

localizationCoordinateIsLiteralDensityExponent :
  ∀ {Coupling Density Bound}
    {flow : Source.Balaban1989EffectiveDensityFlow Coupling Density}
    (meaning : CompleteDensityCoordinateMeaning flow) scale →
  mu (stateFromCompleteDensity meaning scale)
  ≡ localizationExponent meaning scale (Source.densityAt flow scale)
localizationCoordinateIsLiteralDensityExponent meaning scale = refl

inverseSpacingCoordinateIsLiteralDensityScale :
  ∀ {Coupling Density Bound}
    {flow : Source.Balaban1989EffectiveDensityFlow Coupling Density}
    (meaning : CompleteDensityCoordinateMeaning flow) scale →
  aInverse (stateFromCompleteDensity meaning scale)
  ≡ inverseLatticeSpacing meaning scale (Source.densityAt flow scale)
inverseSpacingCoordinateIsLiteralDensityScale meaning scale = refl

balaban1989CanonicalStateConstructionLevel : ProofLevel
balaban1989CanonicalStateConstructionLevel = machineChecked

balaban1989LiteralCouplingSameObjectLevel : ProofLevel
balaban1989LiteralCouplingSameObjectLevel = machineChecked

-- This is now the actual L5 source leaf: identify the five extractor functions
-- with the quantities and norms printed in CMP119/CMP122 Sect. 2.
balaban1989LiteralFiveCoordinateExtractorInstantiationLevel : ProofLevel
balaban1989LiteralFiveCoordinateExtractorInstantiationLevel = conditional
