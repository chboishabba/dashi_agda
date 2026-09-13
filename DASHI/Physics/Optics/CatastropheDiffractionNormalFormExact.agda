module DASHI.Physics.Optics.CatastropheDiffractionNormalFormExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- PROVENANCE / SCOPE
--
-- Berry & Upstill (1980), Catastrophe Optics, Progress in Optics 18,
-- DOI 10.1016/S0079-6638(08)70215-4, is the canonical source already carried
-- in-repo for diffraction structure near optical caustics.
--
-- This module does not evaluate Airy or Pearcey integrals.  It provides the
-- exact typed seam by which a geometric caustic classification is promoted to
-- a local wave-optics normal-form model under an explicit source/scale receipt.
------------------------------------------------------------------------

catastropheOpticsDOI : String
catastropheOpticsDOI = "10.1016/S0079-6638(08)70215-4"

data CausticClass : Set where
  foldCaustic : CausticClass
  cuspCaustic : CausticClass
  higherCatastrophe : CausticClass

data CanonicalDiffractionFamily : Set where
  airyFamily : CanonicalDiffractionFamily
  pearceyFamily : CanonicalDiffractionFamily
  higherCanonicalIntegral : CanonicalDiffractionFamily

canonicalFamilyFor : CausticClass → CanonicalDiffractionFamily
canonicalFamilyFor foldCaustic = airyFamily
canonicalFamilyFor cuspCaustic = pearceyFamily
canonicalFamilyFor higherCatastrophe = higherCanonicalIntegral

record GeometricCausticClassification : Set where
  constructor geometric-caustic-classification
  field
    causticClass : CausticClass
    projectionCriticalityEvidence : String
    jacobianDegeneracyEvidence : String
    classificationAuthority : String

open GeometricCausticClassification public

record CatastropheDiffractionReceipt
    (geometric : GeometricCausticClassification) : Set where
  constructor catastrophe-diffraction-receipt
  field
    diffractionFamily : CanonicalDiffractionFamily
    familyMatchesClass :
      diffractionFamily ≡ canonicalFamilyFor (causticClass geometric)

    wavelengthScaleEvidence : String
    localCoordinateReduction : String
    asymptoticOrUniformApproximationAuthority : String
    predictedWaveField : String
    residualOrValidityRegion : String

open CatastropheDiffractionReceipt public

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data BrightFeatureDeterminesCatastropheClass : Set where
brightFeatureDoesNotDetermineCatastropheClass :
  BrightFeatureDeterminesCatastropheClass → ⊥
brightFeatureDoesNotDetermineCatastropheClass ()

data GeometricCausticAloneDeterminesWavePattern : Set where
geometricCausticAloneDoesNotDetermineWavePattern :
  GeometricCausticAloneDeterminesWavePattern → ⊥
geometricCausticAloneDoesNotDetermineWavePattern ()

data AiryFamilyIsUniversalForAllCaustics : Set where
airyFamilyIsNotUniversalForAllCaustics :
  AiryFamilyIsUniversalForAllCaustics → ⊥
airyFamilyIsNotUniversalForAllCaustics ()
