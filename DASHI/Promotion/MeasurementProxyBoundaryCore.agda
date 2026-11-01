module DASHI.Promotion.MeasurementProxyBoundaryCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Promotion.AuthorityBoundaryCore as Authority

------------------------------------------------------------------------
-- Cross-domain measurement / proxy / inference / authority boundary.

data EpistemicSurface : Set where
  directMeasurementSurface : EpistemicSurface
  processedProxySurface : EpistemicSurface
  latentInferenceSurface : EpistemicSurface
  causalClaimSurface : EpistemicSurface
  diagnosticClassificationSurface : EpistemicSurface
  interventionAuthoritySurface : EpistemicSurface

record MeasurementProxyRow : Set where
  constructor mkMeasurementProxyRow
  field
    rowLabel : String
    surface : EpistemicSurface
    observationBearing : Bool
    proxyBearing : Bool
    causalAuthority : Bool
    diagnosticAuthority : Bool
    interventionAuthority : Bool

open MeasurementProxyRow public

canonicalMeasurementProxyRows : List MeasurementProxyRow
canonicalMeasurementProxyRows =
  mkMeasurementProxyRow "direct measurement" directMeasurementSurface true false false false false
  ∷ mkMeasurementProxyRow "processed proxy" processedProxySurface true true false false false
  ∷ mkMeasurementProxyRow "latent inference" latentInferenceSurface false true false false false
  ∷ mkMeasurementProxyRow "causal claim" causalClaimSurface false false true false false
  ∷ mkMeasurementProxyRow "diagnostic classification" diagnosticClassificationSurface false false false true false
  ∷ mkMeasurementProxyRow "intervention authority" interventionAuthoritySurface false false false false true
  ∷ []

record MeasurementProxyBoundary : Set where
  constructor mkMeasurementProxyBoundary
  field
    rows : List MeasurementProxyRow
    empiricalAuthorityReceipt : Authority.AuthorityBoundaryReceipt
    clinicalAuthorityReceipt : Authority.AuthorityBoundaryReceipt
    measurementIsNotLatentState : Bool
    proxyIsNotCause : Bool
    associationIsNotCausation : Bool
    inferenceIsNotDiagnosis : Bool
    diagnosisIsNotInterventionAuthority : Bool
    boundaryHolds : Bool
    boundaryHoldsIsTrue : boundaryHolds ≡ true

open MeasurementProxyBoundary public

canonicalMeasurementProxyBoundary : MeasurementProxyBoundary
canonicalMeasurementProxyBoundary =
  mkMeasurementProxyBoundary
    canonicalMeasurementProxyRows
    Authority.canonicalBioactiveAuthorityBoundaryReceipt
    Authority.canonicalClinicalAuthorityBoundaryReceipt
    true true true true true true refl
