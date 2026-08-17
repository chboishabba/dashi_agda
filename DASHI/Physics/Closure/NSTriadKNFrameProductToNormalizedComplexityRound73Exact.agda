module DASHI.Physics.Closure.NSTriadKNFrameProductToNormalizedComplexityRound73Exact where

------------------------------------------------------------------------
-- ROUND73 / FRAME PRODUCT -> NORMALIZED EFFECTIVE COMPLEXITY
--
-- PRIMARY SOURCE / CONTEXT
--
-- Author: Ole Christensen.
-- Title: "An Introduction to Frames and Riesz Bases".
-- DOI: 10.1007/978-3-319-25613-9.
--
-- Round73 retains both a general physical frame estimate
--
--      W <= B * E_phys
--
-- and the favorable normalized concentration branch
--
--      W <= 1  =>  mu^2 <= Q.
--
-- These are not separate physical obligations.  If the SAME frame certificate
-- additionally proves
--
--      B * E_phys <= 1,
--
-- then transitivity gives W<=1 and the normalized square-charge compiler
-- applies immediately.
--
-- Thus the strongest physical target may be phrased as one scale-dependent
-- frame-product theorem.  When the product is <=1 it removes effective-
-- complexity loss entirely; when it is larger, the general frame theorem still
-- records the quantitative loss instead of pretending normalization.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; 1ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSTriadKNFactorizedEffectiveComplexityCauchyRound72Exact as Effective
import DASHI.Physics.Closure.NSTriadKNStructuredTriadicFactorizationOverlayRound72Exact as Overlay
import DASHI.Physics.Closure.NSTriadKNLocalizedPDEStructuredAtomsRound62Exact as Structured
import DASHI.Physics.Closure.NSTriadKNPhysicalFrameComplexityRound73Exact as Frame
import DASHI.Physics.Closure.NSTriadKNNormalizedEffectiveComplexityConcentrationRound73Exact as Normalized

record NormalizingFrameProduct
    (factors : List Effective.FactorizedContribution)
    (physicalEnergy frameBound : ℚ) : Set where
  field
    frameCertificate :
      Frame.PhysicalFrameComplexityCertificate factors physicalEnergy frameBound
    frameProductBelowOne : frameBound * physicalEnergy ≤ 1ℚ

open NormalizingFrameProduct public

frameProductNormalizesFactors :
  ∀ {factors physicalEnergy frameBound} →
  NormalizingFrameProduct factors physicalEnergy frameBound →
  Effective.effectiveComplexity factors ≤ 1ℚ
frameProductNormalizesFactors witness =
  ℚP.≤-trans
    (Frame.frameControlsEffectiveComplexity (frameCertificate witness))
    (frameProductBelowOne witness)

record NormalizingOverlayFrame
    {atoms : List Structured.LocalizedPDEAtom}
    (overlay : Overlay.TriadicFactorizationOverlay atoms)
    (physicalEnergy frameBound : ℚ) : Set where
  field
    normalizingProduct :
      NormalizingFrameProduct
        (Overlay.overlayFactors overlay)
        physicalEnergy frameBound

open NormalizingOverlayFrame public

normalizingOverlayFrameGivesNormalizedComplexity :
  ∀ {atoms overlay physicalEnergy frameBound} →
  NormalizingOverlayFrame {atoms} overlay physicalEnergy frameBound →
  Normalized.NormalizedEffectiveComplexity overlay
normalizingOverlayFrameGivesNormalizedComplexity witness = record
  { Normalized.complexityBelowOne =
      frameProductNormalizesFactors (normalizingProduct witness)
  }

round73FrameProductBelowOneCompilesToNormalizedComplexity : Bool
round73FrameProductBelowOneCompilesToNormalizedComplexity = true

round73FrameAndNormalizedLanesAreOneQuantitativeHierarchy : Bool
round73FrameAndNormalizedLanesAreOneQuantitativeHierarchy = true

round73PhysicalNormalizingFrameProductConstructed : Bool
round73PhysicalNormalizingFrameProductConstructed = false

round73FrameProductBelowOneCompilesToNormalizedComplexityIsTrue :
  round73FrameProductBelowOneCompilesToNormalizedComplexity ≡ true
round73FrameProductBelowOneCompilesToNormalizedComplexityIsTrue = refl

round73PhysicalNormalizingFrameProductConstructedIsFalse :
  round73PhysicalNormalizingFrameProductConstructed ≡ false
round73PhysicalNormalizingFrameProductConstructedIsFalse = refl
