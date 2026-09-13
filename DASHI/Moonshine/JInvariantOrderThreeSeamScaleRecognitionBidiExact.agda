module DASHI.Moonshine.JInvariantOrderThreeSeamScaleRecognitionBidiExact where

------------------------------------------------------------------------
-- ORDER-THREE j-SEAM SCALE RECOGNITION
--
-- The seam word is already L^k T and the orbit owner already provides the
-- exact denominator scale
--
--     D_k = k^2 + k + 1.
--
-- This module makes that forward map canonical and isolates the genuinely
-- missing inverse: recognising which rendered/refinement scale corresponds to
-- which modular-word index k on the same analytic seam.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.JInvariantOrderThreeOrbitBalancedTernaryBidiExact as Orbit
import DASHI.Moonshine.JInvariantOrderThreeSeamModularWordExact as Word

seamScale : Nat → Nat
seamScale = Orbit.orbitNorm

record SeamScaleIndexedPoint : Set where
  constructor seam-scale-indexed-point
  field
    index : Nat
    scale : Nat
    scaleIsOrbitNorm : scale ≡ seamScale index

open SeamScaleIndexedPoint public

canonicalScalePoint : Nat → SeamScaleIndexedPoint
canonicalScalePoint k = seam-scale-indexed-point k (seamScale k) refl

k0Scale : scale (canonicalScalePoint 0) ≡ 1
k0Scale = refl

k1Scale : scale (canonicalScalePoint 1) ≡ 3
k1Scale = refl

k2Scale : scale (canonicalScalePoint 2) ≡ 7
k2Scale = refl

k3Scale : scale (canonicalScalePoint 3) ≡ 13
k3Scale = refl

k4Scale : scale (canonicalScalePoint 4) ≡ 21
k4Scale = refl

k5Scale : scale (canonicalScalePoint 5) ≡ 31
k5Scale = refl

k6Scale : scale (canonicalScalePoint 6) ≡ 43
k6Scale = refl

k7Scale : scale (canonicalScalePoint 7) ≡ 57
k7Scale = refl

-- The modular word and scale index are the same Nat coordinate by
-- construction.  No rendered-image identification is hidden here.
record WordScaleSameIndexReceipt (k : Nat) : Set where
  constructor word-scale-same-index-receipt
  field
    wordIndex : Nat
    scaleIndex : Nat
    wordIndexIsK : wordIndex ≡ k
    scaleIndexIsK : scaleIndex ≡ k

canonicalWordScaleSameIndex :
  (k : Nat) → WordScaleSameIndexReceipt k
canonicalWordScaleSameIndex k =
  word-scale-same-index-receipt k k refl refl

-- Candidate recogniser interface.  Inhabiting this from the actual rendered
-- or analytic refinement carrier is the next geometric proof obligation.
record SeamScaleRecognizer (RenderedScale : Set) : Set where
  field
    recogniseIndex : RenderedScale → Nat
    recognisedScale : RenderedScale → Nat
    recognitionLaw :
      (s : RenderedScale) →
      recognisedScale s ≡ seamScale (recogniseIndex s)

------------------------------------------------------------------------
-- Frontier.
------------------------------------------------------------------------

data SeamScaleResidual : Set where
  missingRenderedScaleCarrier : SeamScaleResidual
  missingRenderedScaleToOrbitNormMap : SeamScaleResidual
  missingSameObjectIndexRecognition : SeamScaleResidual
  missingRefinementGluingTransportAtRecognisedIndex : SeamScaleResidual

record SeamScaleFrontier : Set where
  constructor seam-scale-frontier
  field
    modularWordIndexExact : Bool
    forwardOrbitScaleExact : Bool
    wordAndScaleShareIndex : Bool
    renderedScaleRecognised : Bool
    firstResidual : SeamScaleResidual

canonicalSeamScaleFrontier : SeamScaleFrontier
canonicalSeamScaleFrontier =
  seam-scale-frontier
    true true true false
    missingRenderedScaleCarrier
