module DASHI.Physics.Plasma.ToroidalZeroBounceTernary27ConeSearchExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.Ternary27SpectralGeometryCarrierExact as Carrier
import DASHI.Physics.Plasma.ToroidalZeroBounceAdmissibleConeSearchExact as Cone
import DASHI.Physics.Plasma.ToroidalZeroBounceContinuationExact as Continuation
import DASHI.Physics.Plasma.ToroidalZeroBounceGeometryParetoExact as Pareto
import DASHI.Physics.Plasma.ZeroBouncePopulationExact as ZeroBounce

------------------------------------------------------------------------
-- TERNARY-27 ADMISSIBLE-CONE SEARCH
--
-- Broad chart first: 27 typed spectral/design coordinates.
-- Physics search second: project into the hard-constraint tangent/nullspace,
-- intersect active inequality cones, retain only C_(3^n)-compatible modes,
-- continue in delta_C, then Pareto-rank surviving admissible patches.
------------------------------------------------------------------------

record Ternary27ConeSearch
    (population : ZeroBounce.DeclaredParticlePopulation) : Set₁ where
  constructor ternary27-cone-search
  field
    Coefficient PhysicalPerturbation : Set
    realization : Carrier.Ternary27PhysicalRealization Coefficient PhysicalPerturbation
    admissibleSearch : Cone.ToroidalAdmissibleConeSearch population
    continuation : Continuation.AdmissibleContinuationPath admissibleSearch

    ambientTwentySevenCoordinateReceipt : Set
    equalityNullspaceCompressionReceipt : Set
    activeInequalityConeCompressionReceipt : Set
    c3nSpectralCompressionReceipt : Set
    disconnectedPatchReceipt : Set
    paretoAfterAdmissibilityReceipt : Set
    sameZeroBounceConsumerReceipt : Set
    sameBestKnownReferenceConsumerReceipt : Set
    searchReference : String

open Ternary27ConeSearch public

record Ternary27ConeSearchBoundary : Set where
  constructor ternary27-cone-search-boundary
  field
    moreAmbientCoordinatesAutomaticallyMeanHarderSearch : Bool
    moreAmbientCoordinatesAutomaticallyMeanHarderSearchIsFalse :
      moreAmbientCoordinatesAutomaticallyMeanHarderSearch ≡ false

    severeConstraintsMayReduceEffectiveSearchDimension : Bool
    severeConstraintsMayReduceEffectiveSearchDimensionIsTrue :
      severeConstraintsMayReduceEffectiveSearchDimension ≡ true

    zeroDimensionalTangentConeIsUsefulNoGoInformation : Bool
    zeroDimensionalTangentConeIsUsefulNoGoInformationIsTrue :
      zeroDimensionalTangentConeIsUsefulNoGoInformation ≡ true

    disconnectedConesMayBeSearchedAsSeparateHyperfabricPatches : Bool
    disconnectedConesMayBeSearchedAsSeparateHyperfabricPatchesIsTrue :
      disconnectedConesMayBeSearchedAsSeparateHyperfabricPatches ≡ true

    numericalTwentySevenCoordinateSearchProvesGlobalOptimum : Bool
    numericalTwentySevenCoordinateSearchProvesGlobalOptimumIsFalse :
      numericalTwentySevenCoordinateSearchProvesGlobalOptimum ≡ false

canonicalTernary27ConeSearchBoundary : Ternary27ConeSearchBoundary
canonicalTernary27ConeSearchBoundary =
  ternary27-cone-search-boundary
    false refl
    true refl
    true refl
    true refl
    false refl

pythonReplayReference : String
pythonReplayReference =
  "scripts/ternary27_routeC_search.py / scripts/test_ternary27_routeC_search.py"
