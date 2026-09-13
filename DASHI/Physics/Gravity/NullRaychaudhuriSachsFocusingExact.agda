module DASHI.Physics.Gravity.NullRaychaudhuriSachsFocusingExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Physics.Gravity.Penrose1965NullGeodesicIncompletenessExact as Penrose

------------------------------------------------------------------------
-- Source-bounded null-congruence focusing bridge.
--
-- This owner keeps three layers separate:
--   local optical/Raychaudhuri evolution,
--   finite-affine focusing/conjugate-point consequences,
--   Penrose's global null-geodesic incompleteness theorem.
--
-- The continuum equation and focusing theorem are recorded as authority-backed
-- targets.  This module does not derive Lorentzian differential geometry from
-- finite DASHI machinery and does not replace the global Penrose hypotheses.
------------------------------------------------------------------------

Raychaudhuri1955SourceReceipt : Source.AttributedSource
Raychaudhuri1955SourceReceipt =
  Source.mkDOISource
    "Amalkumar Raychaudhuri"
    "Relativistic Cosmology. I"
    "Physical Review 98, 1123"
    "1955"
    "10.1103/PhysRev.98.1123"
    "https://doi.org/10.1103/PhysRev.98.1123"
    Source.academicArticleSource
    "foundational convergence-equation source; used here for historical/source attribution, not as an imported formal proof of the null optical equation"
    Source.publicAttribution

Sachs1961SourceReceipt : Source.AttributedSource
Sachs1961SourceReceipt =
  Source.mkDOISource
    "R. K. Sachs"
    "Gravitational waves in general relativity. VI. The outgoing radiation condition"
    "Proceedings of the Royal Society of London A 264, 309-338"
    "1961"
    "10.1098/rspa.1961.0202"
    "https://doi.org/10.1098/rspa.1961.0202"
    Source.academicArticleSource
    "primary null-congruence/optical-equation lineage source; citation records provenance and does not import the continuum proof"
    Source.publicAttribution

record NullFocusingSourceBoundary : Set where
  field
    raychaudhuriCitationImportsProof : Bool
    raychaudhuriCitationImportsProofIsFalse :
      raychaudhuriCitationImportsProof ≡ false
    sachsCitationImportsProof : Bool
    sachsCitationImportsProofIsFalse :
      sachsCitationImportsProof ≡ false
    sourceAtlasCreatesContinuumAuthority : Bool
    sourceAtlasCreatesContinuumAuthorityIsFalse :
      sourceAtlasCreatesContinuumAuthority ≡ false

open NullFocusingSourceBoundary public

canonicalNullFocusingSourceBoundary : NullFocusingSourceBoundary
canonicalNullFocusingSourceBoundary = record
  { raychaudhuriCitationImportsProof = false
  ; raychaudhuriCitationImportsProofIsFalse = refl
  ; sachsCitationImportsProof = false
  ; sachsCitationImportsProofIsFalse = refl
  ; sourceAtlasCreatesContinuumAuthority = false
  ; sourceAtlasCreatesContinuumAuthorityIsFalse = refl
  }

------------------------------------------------------------------------
-- Local null optical evolution and finite-affine focusing target.
------------------------------------------------------------------------

record NullOpticalFocusingBoundary : Set where
  field
    nullRaychaudhuriEquationTarget : String
    hypersurfaceOrthogonalTwistVanishes : Bool
    hypersurfaceOrthogonalTwistVanishesIsTrue :
      hypersurfaceOrthogonalTwistVanishes ≡ true

    nullConvergenceAndShearForceNonIncreasingExpansion : Bool
    nullConvergenceAndShearForceNonIncreasingExpansionIsTrue :
      nullConvergenceAndShearForceNonIncreasingExpansion ≡ true

    negativeExpansionForcesFiniteAffineFocusing : Bool
    negativeExpansionForcesFiniteAffineFocusingIsTrue :
      negativeExpansionForcesFiniteAffineFocusing ≡ true

    finiteAffineFocusingBound : String

    trappedSurfaceMeansBothFutureNullExpansionsNegative : Bool
    trappedSurfaceMeansBothFutureNullExpansionsNegativeIsTrue :
      trappedSurfaceMeansBothFutureNullExpansionsNegative ≡ true

    focusingOwnerInternallyDerivesContinuumEquation : Bool
    focusingOwnerInternallyDerivesContinuumEquationIsFalse :
      focusingOwnerInternallyDerivesContinuumEquation ≡ false

open NullOpticalFocusingBoundary public

canonicalNullOpticalFocusingBoundary : NullOpticalFocusingBoundary
canonicalNullOpticalFocusingBoundary = record
  { nullRaychaudhuriEquationTarget =
      "for an affinely parametrized null geodesic congruence in four spacetime dimensions: d theta / d lambda = -(1/2) theta^2 - sigma_ab sigma^ab + omega_ab omega^ab - R_ab k^a k^b"
  ; hypersurfaceOrthogonalTwistVanishes = true
  ; hypersurfaceOrthogonalTwistVanishesIsTrue = refl
  ; nullConvergenceAndShearForceNonIncreasingExpansion = true
  ; nullConvergenceAndShearForceNonIncreasingExpansionIsTrue = refl
  ; negativeExpansionForcesFiniteAffineFocusing = true
  ; negativeExpansionForcesFiniteAffineFocusingIsTrue = refl
  ; finiteAffineFocusingBound =
      "under hypersurface orthogonality and R_ab k^a k^b >= 0, initial theta_0 < 0 gives a conjugate/focal point no later than affine parameter increment 2 / |theta_0| in four dimensions"
  ; trappedSurfaceMeansBothFutureNullExpansionsNegative = true
  ; trappedSurfaceMeansBothFutureNullExpansionsNegativeIsTrue = refl
  ; focusingOwnerInternallyDerivesContinuumEquation = false
  ; focusingOwnerInternallyDerivesContinuumEquationIsFalse = refl
  }

------------------------------------------------------------------------
-- WrongType / theorem-composition firewalls.
------------------------------------------------------------------------

record NullFocusingCompositionBoundary : Set where
  field
    localFocusingDoesNotEqualGlobalGeodesicIncompleteness : Bool
    localFocusingDoesNotEqualGlobalGeodesicIncompletenessIsTrue :
      localFocusingDoesNotEqualGlobalGeodesicIncompleteness ≡ true

    nullEnergyConditionIsNotNullConvergenceWithoutEinsteinEquation : Bool
    nullEnergyConditionIsNotNullConvergenceWithoutEinsteinEquationIsTrue :
      nullEnergyConditionIsNotNullConvergenceWithoutEinsteinEquation ≡ true

    conjugatePointIsNotSpacetimeSingularity : Bool
    conjugatePointIsNotSpacetimeSingularityIsTrue :
      conjugatePointIsNotSpacetimeSingularity ≡ true

    trappedSurfaceAloneDoesNotPayPenroseConclusion : Bool
    trappedSurfaceAloneDoesNotPayPenroseConclusionIsTrue :
      trappedSurfaceAloneDoesNotPayPenroseConclusion ≡ true

    globalCauchyTopologyStillRequired : Bool
    globalCauchyTopologyStillRequiredIsTrue :
      globalCauchyTopologyStillRequired ≡ true

open NullFocusingCompositionBoundary public

canonicalNullFocusingCompositionBoundary : NullFocusingCompositionBoundary
canonicalNullFocusingCompositionBoundary = record
  { localFocusingDoesNotEqualGlobalGeodesicIncompleteness = true
  ; localFocusingDoesNotEqualGlobalGeodesicIncompletenessIsTrue = refl
  ; nullEnergyConditionIsNotNullConvergenceWithoutEinsteinEquation = true
  ; nullEnergyConditionIsNotNullConvergenceWithoutEinsteinEquationIsTrue = refl
  ; conjugatePointIsNotSpacetimeSingularity = true
  ; conjugatePointIsNotSpacetimeSingularityIsTrue = refl
  ; trappedSurfaceAloneDoesNotPayPenroseConclusion = true
  ; trappedSurfaceAloneDoesNotPayPenroseConclusionIsTrue = refl
  ; globalCauchyTopologyStillRequired = true
  ; globalCauchyTopologyStillRequiredIsTrue = refl
  }

------------------------------------------------------------------------
-- Explicit composition back into the Penrose theorem-boundary owner.
------------------------------------------------------------------------

penroseBoundaryConsumer : Set
penroseBoundaryConsumer = Penrose.Penrose1965TheoremBoundary

focusingBridgePromotesPenroseConclusion : Bool
focusingBridgePromotesPenroseConclusion = false

focusingBridgePromotesPenroseConclusionIsFalse :
  focusingBridgePromotesPenroseConclusion ≡ false
focusingBridgePromotesPenroseConclusionIsFalse = refl
