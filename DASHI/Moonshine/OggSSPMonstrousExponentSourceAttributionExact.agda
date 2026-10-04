module DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact where

------------------------------------------------------------------------
-- OGG / SSP / MONSTROUS-EXPONENT SOURCE ATTRIBUTION
--
-- This module is provenance only.  It does not import proofs or promote any
-- source claim.  It makes the claim boundary used by the J/369 cross-
-- pollination modules explicit and typed.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Interop.SourceAttributionShapePolicyExact as Shape

------------------------------------------------------------------------
-- 1. External sources.
------------------------------------------------------------------------

oggSource : Attribution.AttributedSource
oggSource =
  Attribution.mkNoDOISource
    "Andrew P. Ogg"
    "Automorphismes de courbes modulaires"
    "Seminaire Delange-Pisot-Poitou 16 (1974-1975), expose 7, pp. 1-8; MR 417184"
    "1974-1975"
    "https://www.numdam.org/"
    Attribution.academicArticleSource
    "source context for the genus-zero/supersingular-prime coincidence; does not supply DASHI Base369 carriers or residual groupoids"
    Attribution.publicAttribution

duncanOnoSource : Attribution.AttributedSource
duncanOnoSource =
  Attribution.mkDOISource
    "John F. R. Duncan and Ken Ono"
    "The Jack Daniels Problem"
    "Journal of Number Theory 161, 230-239"
    "2016"
    "10.1016/j.jnt.2015.06.001"
    "https://doi.org/10.1016/j.jnt.2015.06.001"
    Attribution.academicArticleSource
    "source context for the Monster-module/supersingular-j relationship and the fifteen Ogg primes; does not state the DASHI 369/gluing construction"
    Attribution.publicAttribution

duncanSwisherSource : Attribution.AttributedSource
duncanSwisherSource =
  Attribution.mkDOISource
    "John F. R. Duncan and Holly Swisher"
    "Modular Functions and the Monstrous Exponents"
    "arXiv:2602.09135"
    "2026"
    "10.48550/arXiv.2602.09135"
    "https://arxiv.org/abs/2602.09135"
    Attribution.academicArticleSource
    "source for the p>3 monstrous-exponent modular valuation formula and the exceptional small-characteristic right-hand-side values used upstream; does not state the DASHI Base369 residual decomposition"
    Attribution.publicAttribution

oggSSPMonstrousExponentSourceAtlas : Attribution.AttributedSourceAtlas
oggSSPMonstrousExponentSourceAtlas =
  Attribution.mkSourceAtlas
    "Ogg / SSP / monstrous-exponent source atlas"
    "DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact"
    (oggSource ∷ duncanOnoSource ∷ duncanSwisherSource ∷ [])
    "external provenance for Ogg-prime support, supersingular-j context, and Duncan-Swisher monstrous-exponent arithmetic; all 369, Fibonacci, gluing, groupoid, orbit/stabilizer and residual-recognition constructions remain separately identified DASHI extensions"

------------------------------------------------------------------------
-- 2. Claim-origin tags used downstream.
------------------------------------------------------------------------

data ClaimOrigin : Set where
  externalOggSourceClaim : ClaimOrigin
  externalDuncanOnoSourceClaim : ClaimOrigin
  externalDuncanSwisherSourceClaim : ClaimOrigin
  repositoryFormalReconstruction : ClaimOrigin
  repositoryCrossModuleInference : ClaimOrigin
  repositoryNewExtension : ClaimOrigin
  openRecognitionConjecture : ClaimOrigin

monsterExponentArithmeticOrigin : ClaimOrigin
monsterExponentArithmeticOrigin = externalDuncanSwisherSourceClaim

oggPrimeSupportOrigin : ClaimOrigin
oggPrimeSupportOrigin = externalOggSourceClaim

sspMoonshineContextOrigin : ClaimOrigin
sspMoonshineContextOrigin = externalDuncanOnoSourceClaim

threeSixNineCountComparisonOrigin : ClaimOrigin
threeSixNineCountComparisonOrigin = repositoryCrossModuleInference

smallCharacteristicResidualGroupoidOrigin : ClaimOrigin
smallCharacteristicResidualGroupoidOrigin = repositoryNewExtension

arithmeticGeometricSameObjectRecognitionOrigin : ClaimOrigin
arithmeticGeometricSameObjectRecognitionOrigin = openRecognitionConjecture

------------------------------------------------------------------------
-- 3. Attribution shape and promotion firewalls.
------------------------------------------------------------------------

publishedTheoremAttributionShape :
  Shape.RequiredAttributionShape
publishedTheoremAttributionShape =
  Shape.requiredAttributionShape Shape.publishedScientificTheorem

publishedTheoremNeedsAttributedTheoremMatch :
  publishedTheoremAttributionShape ≡ Shape.attributedSourcePlusTheoremMatch
publishedTheoremNeedsAttributedTheoremMatch = refl

internalExtensionAttributionShape :
  Shape.RequiredAttributionShape
internalExtensionAttributionShape =
  Shape.requiredAttributionShape Shape.internalDerivedTheorem

internalExtensionUsesProofLineage :
  internalExtensionAttributionShape ≡ Shape.proofLineageNoNewExternalCitation
internalExtensionUsesProofLineage = refl

data CitationCreatesResidualGroupoidRecognition : Set where
data OggSourceClaimsBase369Construction : Set where
data DuncanSwisherClaimsDASHI369Decomposition : Set where

citationDoesNotCreateResidualGroupoidRecognition :
  CitationCreatesResidualGroupoidRecognition → ⊥
citationDoesNotCreateResidualGroupoidRecognition ()

oggDoesNotGetAttributedDASHIBase369Construction :
  OggSourceClaimsBase369Construction → ⊥
oggDoesNotGetAttributedDASHIBase369Construction ()

duncanSwisherDoesNotGetAttributedDASHI369Decomposition :
  DuncanSwisherClaimsDASHI369Decomposition → ⊥
duncanSwisherDoesNotGetAttributedDASHI369Decomposition ()

record OggSSPMonstrousExponentAttributionBoundary : Set where
  constructor ogg-ssp-monstrous-exponent-attribution-boundary
  field
    oggSupportSourceIdentified : Bool
    duncanOnoSSPContextSourceIdentified : Bool
    duncanSwisherExponentSourceIdentified : Bool
    sourceClaimsSeparatedFromFormalReconstruction : Bool
    crossModule369InferenceMarkedRepositoryNative : Bool
    residualGroupoidMarkedRepositoryExtension : Bool
    sameObjectRecognitionStillOpen : Bool
    citationsCreateProof : Bool
    citationsCreateAuthority : Bool

canonicalOggSSPMonstrousExponentAttributionBoundary :
  OggSSPMonstrousExponentAttributionBoundary
canonicalOggSSPMonstrousExponentAttributionBoundary =
  ogg-ssp-monstrous-exponent-attribution-boundary
    true true true true true true true false false
