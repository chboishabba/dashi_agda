module DASHI.Moonshine.JInvariantImageFractalSourceAtlasExact where

------------------------------------------------------------------------
-- SOURCE-ALIGNED J-IMAGE FRACTAL / PHASE ATLAS
--
-- Source identity, exact source claim, local interpretation and kernel proof
-- remain separate coordinates.  These Wikimedia file-description pages are
-- secondary descriptive carriers for the rendered images; they are not used
-- as theorem proofs and their use on a String theory page is not itself a
-- string-theory semantic bridge.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.ProofDebtRouterExact as Debt

realImageSource : Debt.SourceIdentity
realImageSource =
  Debt.source-identity
    "Linas Vepstas / Wikimedia Commons contributors"
    "Klein's J-invariant, real part"
    "Commons File:J-inv-real.jpeg"
    "https://commons.wikimedia.org/wiki/File:J-inv-real.jpeg"
    "original upload 2005-02-15; Commons description inspected 2026-09-09"

phaseImageSource : Debt.SourceIdentity
phaseImageSource =
  Debt.source-identity
    "Linas Vepstas / Wikimedia Commons contributors"
    "Klein's J-invariant, phase portrait"
    "Commons File:J-inv-phase.jpeg"
    "https://commons.wikimedia.org/wiki/File:J-inv-phase.jpeg"
    "original upload 2005-02-15; Commons description inspected 2026-09-09"

kleinComplexImageSource : Debt.SourceIdentity
kleinComplexImageSource =
  Debt.source-identity
    "Jan Homann / Wikimedia Commons contributors"
    "KleinInvariantJ.jpg"
    "Commons File:KleinInvariantJ.jpg"
    "https://commons.wikimedia.org/wiki/File:KleinInvariantJ.jpg"
    "upload 2007-08-03; Commons description inspected 2026-09-09"

record JImageClaim : Set where
  constructor j-image-claim
  field
    source : Debt.SourceIdentity
    exactSourceClaim : String
    localUseScope : String
    sourceEntitlesKernelProof : Bool

open JImageClaim public

phaseTripleWindingClaim : JImageClaim
phaseTripleWindingClaim =
  j-image-claim phaseImageSource
    "The phase portrait uses arctan(Im j / Re j); tri-corner intersections wrap phase three times, for total winding 6*pi, indicating third-power zeros."
    "source-aligned phase/winding coordinate; no Base369 identification supplied by the source"
    false

modularFractalClaim : JImageClaim
modularFractalClaim =
  j-image-claim phaseImageSource
    "The fractal self-similarity is that of the modular group; the image illustrates tessellation of the Poincare disk by modular-group fundamental domains."
    "source-aligned modular self-similarity coordinate for scale-indexed observer search"
    false

realImageModularFractalClaim : JImageClaim
realImageModularFractalClaim =
  j-image-claim realImageSource
    "The real-part image description likewise attributes the function's fractal self-similarity to the modular group and explains the hyperbolic fundamental-region geometry."
    "independent image-description cross-check of the modular self-similarity coordinate"
    false

complexPlaneCarrierClaim : JImageClaim
complexPlaneCarrierClaim =
  j-image-claim kleinComplexImageSource
    "The image depicts KleinInvariantJ[z] = g2^3 / Delta in the complex plane."
    "rendered complex-plane carrier description only"
    false

record JImageAttributionBoundary : Set where
  constructor j-image-attribution-boundary
  field
    fractalSelfSimilaritySourceDescribed : Bool
    triplePhaseWindingSourceDescribed : Bool
    imageUsedOnStringTheoryPage : Bool
    imageUsageImpliesStringTheoryBridge : Bool
    sourceDescriptionImpliesBase369Bridge : Bool
    sourceDescriptionImpliesMonsterRepresentation : Bool

canonicalJImageAttributionBoundary : JImageAttributionBoundary
canonicalJImageAttributionBoundary =
  j-image-attribution-boundary
    true true true false false false

stringTheoryUsageDoesNotPromoteBridge :
  JImageAttributionBoundary.imageUsageImpliesStringTheoryBridge
    canonicalJImageAttributionBoundary ≡ false
stringTheoryUsageDoesNotPromoteBridge = refl
