module DASHI.Physics.GR.GravitationalWavePolarizationSourceAttributionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Interop.SourceAttributionShapePolicyExact as Shape

------------------------------------------------------------------------
-- GRAVITATIONAL-WAVE POLARIZATION SOURCE ATTRIBUTION
--
-- Carrier-sensitive source rule:
--   published scientific/empirical claim -> attributed source + exact scope;
--   DASHI sign/polarity reconstruction -> internal proof lineage, not a fresh
--   external citation and not a claim that the paper proved our BIDI theorem.
------------------------------------------------------------------------

gw170814PolarizationSource : Source.AttributedSource
gw170814PolarizationSource = Source.mkDOISource
  "B. P. Abbott et al. (LIGO Scientific Collaboration and Virgo Collaboration)"
  "GW170814: A Three-Detector Observation of Gravitational Waves from a Binary Black Hole Coalescence"
  "Physical Review Letters 119, 141101"
  "2017"
  "10.1103/PhysRevLett.119.141101"
  "https://journals.aps.org/prl/abstract/10.1103/PhysRevLett.119.141101"
  Source.academicArticleSource
  "source-entitled for the bounded statements that GR gravitational waves have two tensor polarizations and that the GW170814 three-detector analysis strongly favored purely tensor polarization over purely vector or scalar alternatives; it does not state that plus/cross labels are positive/negative polarities, does not identify the sign of Newton's G, and does not prove DASHI's polarization/sign BIDI"
  Source.publicAttribution

data PolarizationSourceClaim : Set where
  grHasTwoTensorPolarizations : PolarizationSourceClaim
  gw170814FavoursTensorOverPureVectorScalar : PolarizationSourceClaim

claimScope : PolarizationSourceClaim → String
claimScope grHasTwoTensorPolarizations =
  "In GR, gravitational waves have two tensor polarization modes, conventionally called plus and cross."
claimScope gw170814FavoursTensorOverPureVectorScalar =
  "The GW170814 three-detector analysis strongly favored purely tensor polarization over purely vector or purely scalar alternatives."

record PolarizationSourceEntitlement (claim : PolarizationSourceClaim) : Set where
  constructor polarization-source-entitlement
  field
    attributedSource : Source.AttributedSource
    sourceMatchesCanonical : attributedSource ≡ gw170814PolarizationSource
    entitledClaimScope : String
    entitledClaimScopeMatches : entitledClaimScope ≡ claimScope claim

open PolarizationSourceEntitlement public

canonicalPolarizationSourceEntitlement :
  (claim : PolarizationSourceClaim) → PolarizationSourceEntitlement claim
canonicalPolarizationSourceEntitlement claim =
  polarization-source-entitlement gw170814PolarizationSource refl (claimScope claim) refl

publishedPolarizationAttributionShape : Shape.RequiredAttributionShape
publishedPolarizationAttributionShape =
  Shape.requiredAttributionShape Shape.publishedEmpiricalClaim

record GravitationalWavePolarizationAttributionBoundary : Set where
  constructor gravitational-wave-polarization-attribution-boundary
  field
    publishedPolarizationClaimUsesAttributedSource : Bool
    doiPinnedWhenAvailable : Bool
    citationImportsDASHIBidiProof : Bool
    plusLabelMeansPositivePolarityByCitation : Bool
    crossLabelMeansNegativePolarityByCitation : Bool
    tensorPolarizationObservationDeterminesGSign : Bool
    dashiSignReconstructionIsExternalSourceClaim : Bool

canonicalGravitationalWavePolarizationAttributionBoundary :
  GravitationalWavePolarizationAttributionBoundary
canonicalGravitationalWavePolarizationAttributionBoundary =
  gravitational-wave-polarization-attribution-boundary
    true true false false false false false
