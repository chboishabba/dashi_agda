module DASHI.Physics.Optics.DashiRTXAdaptiveTransportSourceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Foundations.PathIntegralExperimentalSourceRegistryExact as Sources

------------------------------------------------------------------------
-- SOURCE ATTRIBUTION / OWNERSHIP BOUNDARY
--
-- Kajiya is retained as external authority for the rendering equation and its
-- Monte-Carlo / hierarchical-sampling context.  dashiRTX's signed-frontier,
-- importance-weighted MDL refresh mask, persistent-state penalty, metric
-- regularisation, quadtree refinement and benchmark protocol are DASHI
-- computational constructions/experiments and are not attributed to Kajiya.
------------------------------------------------------------------------

kajiyaRenderingEquation1986 : Sources.SourceReference
kajiyaRenderingEquation1986 = Sources.sourceReference
  "James T. Kajiya"
  "The Rendering Equation"
  "ACM SIGGRAPH Computer Graphics 20(4), 143-150"
  1986
  "10.1145/15886.15902"
  "authority for the rendering-equation light-transport integral formulation and Monte-Carlo/hierarchical-sampling context; does not state DASHI's PDA/MDL adaptive refresh objective or quadtree policy"

record DashiRTXArtifactReference : Set₁ where
  constructor dashi-rtx-artifact-reference
  field
    repository : String
    revision : String
    executablePath : String
    artifactDigestOrCommit : String
    boundedReading : String
    excludedPromotion : String

open DashiRTXArtifactReference public

canonicalDashiRTXAdaptiveTransportArtifact : DashiRTXArtifactReference
canonicalDashiRTXAdaptiveTransportArtifact =
  dashi-rtx-artifact-reference
    "chboishabba/dashiRTX"
    "master"
    "pda_mdl_light_transport_test_fixed.py"
    "repository commit / artifact digest supplied by producer"
    "DASHI experimental implementation of reprojection-error measurement, signed frontier, importance weighting, persistent-state penalty, learned refresh allocation and MDL-style adaptive light-transport refinement"
    "Does not by itself establish unbiased physical radiative transfer, botanical canopy optics, universal optimality, or photosynthetic benefit."

record DashiRTXSourceBoundary : Set where
  constructor dashi-rtx-source-boundary
  field
    renderingEquationSourceDistinctFromDashiOptimizer : Bool
    renderingEquationSourceDistinctFromDashiOptimizerIsTrue :
      renderingEquationSourceDistinctFromDashiOptimizer ≡ true
    executableBenchmarkIsExternalScientificAuthority : Bool
    executableBenchmarkIsExternalScientificAuthorityIsFalse :
      executableBenchmarkIsExternalScientificAuthority ≡ false
    adaptiveAllocationNeedsAuthoritativeTransportKernel : Bool
    adaptiveAllocationNeedsAuthoritativeTransportKernelIsTrue :
      adaptiveAllocationNeedsAuthoritativeTransportKernel ≡ true

canonicalDashiRTXSourceBoundary : DashiRTXSourceBoundary
canonicalDashiRTXSourceBoundary =
  dashi-rtx-source-boundary true refl false refl true refl
