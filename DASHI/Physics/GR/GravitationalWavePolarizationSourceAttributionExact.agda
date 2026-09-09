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
--   official technical detector formula -> stable document identity + scope;
--   DASHI sign/polarity reconstruction -> internal proof lineage, not a fresh
--   external citation and not a claim that the source proved our BIDI theorem.
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

ligoDetectorPolarizationResponseSource : Source.AttributedSource
ligoDetectorPolarizationResponseSource = Source.mkNoDOISource
  "Pinkesh Patel; Xavier Siemens; Rejean J. Dupuis"
  "Implementation of Barycentric Resampling for Continuous Wave Searches in Gravitational-Wave Data"
  "LIGO DCC Technical Note LIGO-T090003-00-Z"
  "2009"
  "https://dcc.ligo.org/public/0028/T090003/000/T090003-00.pdf"
  Source.technicalStandardSource
  "official LIGO technical carrier for the bounded detector-response decomposition using h_plus, h_cross, F_plus, F_cross, polarization angle and waveform phase; it does not identify waveform sign with polarization-basis name or with the sign of Newton's G"
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

data DetectorResponseSourceClaim : Set where
  detectorResponseSeparatesPolarizationsAndAntennaFactors : DetectorResponseSourceClaim
  detectorResponseDependsOnPolarizationAngleAndPhase : DetectorResponseSourceClaim

detectorResponseClaimScope : DetectorResponseSourceClaim → String
detectorResponseClaimScope detectorResponseSeparatesPolarizationsAndAntennaFactors =
  "The detector strain response is composed from plus/cross waveform components and their detector antenna-response factors rather than from a single polarization-sign scalar."
detectorResponseClaimScope detectorResponseDependsOnPolarizationAngleAndPhase =
  "The detector response depends on polarization angle and waveform phase as separate coordinates."

record DetectorResponseSourceEntitlement (claim : DetectorResponseSourceClaim) : Set where
  constructor detector-response-source-entitlement
  field
    attributedSource : Source.AttributedSource
    sourceMatchesCanonical : attributedSource ≡ ligoDetectorPolarizationResponseSource
    entitledClaimScope : String
    entitledClaimScopeMatches : entitledClaimScope ≡ detectorResponseClaimScope claim

open DetectorResponseSourceEntitlement public

canonicalDetectorResponseSourceEntitlement :
  (claim : DetectorResponseSourceClaim) → DetectorResponseSourceEntitlement claim
canonicalDetectorResponseSourceEntitlement claim =
  detector-response-source-entitlement
    ligoDetectorPolarizationResponseSource refl (detectorResponseClaimScope claim) refl

publishedPolarizationAttributionShape : Shape.RequiredAttributionShape
publishedPolarizationAttributionShape =
  Shape.requiredAttributionShape Shape.publishedEmpiricalClaim

technicalDetectorAttributionShape : Shape.RequiredAttributionShape
technicalDetectorAttributionShape =
  Shape.requiredAttributionShape Shape.localArchiveOrCodeContract

record GravitationalWavePolarizationAttributionBoundary : Set where
  constructor gravitational-wave-polarization-attribution-boundary
  field
    publishedPolarizationClaimUsesAttributedSource : Bool
    doiPinnedWhenAvailable : Bool
    officialTechnicalCarrierMayUseStableDocumentIdentity : Bool
    citationImportsDASHIBidiProof : Bool
    plusLabelMeansPositivePolarityByCitation : Bool
    crossLabelMeansNegativePolarityByCitation : Bool
    tensorPolarizationObservationDeterminesGSign : Bool
    dashiSignReconstructionIsExternalSourceClaim : Bool

canonicalGravitationalWavePolarizationAttributionBoundary :
  GravitationalWavePolarizationAttributionBoundary
canonicalGravitationalWavePolarizationAttributionBoundary =
  gravitational-wave-polarization-attribution-boundary
    true true true false false false false false
