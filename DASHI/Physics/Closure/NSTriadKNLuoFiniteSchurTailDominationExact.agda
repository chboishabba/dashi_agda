module DASHI.Physics.Closure.NSTriadKNLuoFiniteSchurTailDominationExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Loukas Grafakos; Rodolfo H. Torres.
-- Title: "A Multilinear Schur Test and Multiplier Operators".
-- Journal of Functional Analysis 187 (2001), 1--24.
-- DOI: 10.1006/jfan.2001.3804.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Upgrade pointwise domination by the canonical Schur kernel to quantitative
-- finite-extension bounds.  Shifting the low-shell index by J extracts
-- (1/4)^J; shifting the gap index by D extracts (1/32)^D.  The existing exact
-- 128/93 rectangle theorem then gives
--
--   low exterior <= (128/93)(1/4)^J C,
--   gap exterior <= (128/93)(1/32)^D C.
--
-- This is the finite Cauchy-tail estimate needed before an infinite resonant
-- fibre can be constructed by completion.  A mere cutoff-uniform prefix bound
-- would not provide this decay.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNOutputRelocationPositiveKernelMajorant as Majorant
import DASHI.Physics.Closure.NSTriadKNLuoFinitePhysicalSchurSummationExact as Schur
import DASHI.Physics.Closure.NSTriadKNLuoCanonicalSchurTailExact as Tail

lowShift :
  (Nat → Nat → ℚ) → Nat → Nat → Nat → ℚ
lowShift family start lowShell gap = family (start + lowShell) gap

gapShift :
  (Nat → Nat → ℚ) → Nat → Nat → Nat → ℚ
gapShift family start lowShell gap = family lowShell (start + gap)

lowExteriorRectangle :
  (Nat → Nat → ℚ) → Nat → Nat → Nat → ℚ
lowExteriorRectangle family start lowTailCutoff gapCutoff =
  Majorant.rectangleSum
    (lowShift family start)
    lowTailCutoff
    gapCutoff

gapExteriorRectangle :
  (Nat → Nat → ℚ) → Nat → Nat → Nat → ℚ
gapExteriorRectangle family start gapTailCutoff lowCutoff =
  Majorant.rectangleSum
    (gapShift family start)
    lowCutoff
    gapTailCutoff

record FiniteSchurTailData : Set where
  constructor finite-schur-tail
  field
    pairMagnitude : Nat → Nat → ℚ
    commonFactor : ℚ
    commonFactorNonnegative : 0ℚ ≤ commonFactor

    pointwiseTailDomination :
      (lowShell gap : Nat) →
      pairMagnitude lowShell gap
      ≤ Majorant.canonicalKernel lowShell gap * commonFactor

open FiniteSchurTailData public

lowTailScale : FiniteSchurTailData → Nat → ℚ
lowTailScale data start =
  Geo.pow Geo.quarter start * commonFactor data

gapTailScale : FiniteSchurTailData → Nat → ℚ
gapTailScale data start =
  Geo.pow Geo.thirtySecond start * commonFactor data

lowTailScaleNonnegative :
  (data : FiniteSchurTailData) →
  (start : Nat) →
  0ℚ ≤ lowTailScale data start
lowTailScaleNonnegative data start =
  let
    instance
      powerIsNonnegative = nonNegative
        (Geo.powNonnegative Geo.quarter start Geo.quarterNonnegative)
      commonIsNonnegative = nonNegative (commonFactorNonnegative data)
      productIsNonnegative =
        ℚₚ.nonNeg*nonNeg⇒nonNeg
          (Geo.pow Geo.quarter start)
          (commonFactor data)
  in
  ℚₚ.nonNegative⁻¹ (lowTailScale data start)

gapTailScaleNonnegative :
  (data : FiniteSchurTailData) →
  (start : Nat) →
  0ℚ ≤ gapTailScale data start
gapTailScaleNonnegative data start =
  let
    instance
      powerIsNonnegative = nonNegative
        (Geo.powNonnegative
          Geo.thirtySecond start Geo.thirtySecondNonnegative)
      commonIsNonnegative = nonNegative (commonFactorNonnegative data)
      productIsNonnegative =
        ℚₚ.nonNeg*nonNeg⇒nonNeg
          (Geo.pow Geo.thirtySecond start)
          (commonFactor data)
  in
  ℚₚ.nonNegative⁻¹ (gapTailScale data start)

lowShiftedPointwiseDomination :
  (data : FiniteSchurTailData) →
  (start lowShell gap : Nat) →
  lowShift (pairMagnitude data) start lowShell gap
  ≤ Majorant.canonicalKernel lowShell gap
      * lowTailScale data start
lowShiftedPointwiseDomination data start lowShell gap =
  let
    raw = pointwiseTailDomination data (start + lowShell) gap

    targetMeaning :
      Majorant.canonicalKernel (start + lowShell) gap
        * commonFactor data
      ≡ Majorant.canonicalKernel lowShell gap
        * lowTailScale data start
    targetMeaning
      rewrite Tail.powAdd Geo.quarter start lowShell =
      solve
        ( Geo.pow Geo.quarter start
        ∷ Geo.pow Geo.quarter lowShell
        ∷ Geo.pow Geo.thirtySecond gap
        ∷ commonFactor data
        ∷ []
        )
  in
  subst
    (λ upper →
      lowShift (pairMagnitude data) start lowShell gap ≤ upper)
    targetMeaning
    raw

gapShiftedPointwiseDomination :
  (data : FiniteSchurTailData) →
  (start lowShell gap : Nat) →
  gapShift (pairMagnitude data) start lowShell gap
  ≤ Majorant.canonicalKernel lowShell gap
      * gapTailScale data start
gapShiftedPointwiseDomination data start lowShell gap =
  let
    raw = pointwiseTailDomination data lowShell (start + gap)

    targetMeaning :
      Majorant.canonicalKernel lowShell (start + gap)
        * commonFactor data
      ≡ Majorant.canonicalKernel lowShell gap
        * gapTailScale data start
    targetMeaning
      rewrite Tail.powAdd Geo.thirtySecond start gap =
      solve
        ( Geo.pow Geo.quarter lowShell
        ∷ Geo.pow Geo.thirtySecond start
        ∷ Geo.pow Geo.thirtySecond gap
        ∷ commonFactor data
        ∷ []
        )
  in
  subst
    (λ upper →
      gapShift (pairMagnitude data) start lowShell gap ≤ upper)
    targetMeaning
    raw

finiteLowExteriorTailBound :
  (data : FiniteSchurTailData) →
  (start lowTailCutoff gapCutoff : Nat) →
  lowExteriorRectangle (pairMagnitude data)
    start lowTailCutoff gapCutoff
  ≤ (Geo.pow Geo.quarter start
      * Geo.oneTwentyEightNinetyThirds)
      * commonFactor data
finiteLowExteriorTailBound data start lowTailCutoff gapCutoff =
  let
    scale = lowTailScale data start

    pointwiseToRectangle :
      Majorant.rectangleSum
        (lowShift (pairMagnitude data) start)
        lowTailCutoff gapCutoff
      ≤ Majorant.rectangleSum
          (λ lowShell gap →
            Majorant.canonicalKernel lowShell gap * scale)
          lowTailCutoff gapCutoff
    pointwiseToRectangle =
      Schur.rectangleSumMonotone
        (lowShift (pairMagnitude data) start)
        (λ lowShell gap →
          Majorant.canonicalKernel lowShell gap * scale)
        lowTailCutoff gapCutoff
        (lowShiftedPointwiseDomination data start)

    scaledKernelBound :
      Majorant.rectangleSum
        Majorant.canonicalKernel lowTailCutoff gapCutoff * scale
      ≤ Geo.oneTwentyEightNinetyThirds * scale
    scaledKernelBound =
      let instance scaleIsNonnegative =
        nonNegative (lowTailScaleNonnegative data start)
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        scale
        (Majorant.canonicalKernelCutoffUniformBound
          lowTailCutoff gapCutoff)

    factoredTarget :
      Geo.oneTwentyEightNinetyThirds * scale
      ≡ (Geo.pow Geo.quarter start
          * Geo.oneTwentyEightNinetyThirds)
          * commonFactor data
    factoredTarget =
      solve
        ( Geo.pow Geo.quarter start
        ∷ Geo.oneTwentyEightNinetyThirds
        ∷ commonFactor data
        ∷ []
        )
  in
  ℚₚ.≤-trans
    (subst
      (λ upper →
        lowExteriorRectangle (pairMagnitude data)
          start lowTailCutoff gapCutoff ≤ upper)
      (Schur.rectangleRightScale
        Majorant.canonicalKernel scale lowTailCutoff gapCutoff)
      pointwiseToRectangle)
    (subst
      (λ upper →
        Majorant.rectangleSum
          Majorant.canonicalKernel lowTailCutoff gapCutoff * scale
        ≤ upper)
      factoredTarget
      scaledKernelBound)

finiteGapExteriorTailBound :
  (data : FiniteSchurTailData) →
  (start gapTailCutoff lowCutoff : Nat) →
  gapExteriorRectangle (pairMagnitude data)
    start gapTailCutoff lowCutoff
  ≤ (Geo.pow Geo.thirtySecond start
      * Geo.oneTwentyEightNinetyThirds)
      * commonFactor data
finiteGapExteriorTailBound data start gapTailCutoff lowCutoff =
  let
    scale = gapTailScale data start

    pointwiseToRectangle :
      Majorant.rectangleSum
        (gapShift (pairMagnitude data) start)
        lowCutoff gapTailCutoff
      ≤ Majorant.rectangleSum
          (λ lowShell gap →
            Majorant.canonicalKernel lowShell gap * scale)
          lowCutoff gapTailCutoff
    pointwiseToRectangle =
      Schur.rectangleSumMonotone
        (gapShift (pairMagnitude data) start)
        (λ lowShell gap →
          Majorant.canonicalKernel lowShell gap * scale)
        lowCutoff gapTailCutoff
        (gapShiftedPointwiseDomination data start)

    scaledKernelBound :
      Majorant.rectangleSum
        Majorant.canonicalKernel lowCutoff gapTailCutoff * scale
      ≤ Geo.oneTwentyEightNinetyThirds * scale
    scaledKernelBound =
      let instance scaleIsNonnegative =
        nonNegative (gapTailScaleNonnegative data start)
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        scale
        (Majorant.canonicalKernelCutoffUniformBound
          lowCutoff gapTailCutoff)

    factoredTarget :
      Geo.oneTwentyEightNinetyThirds * scale
      ≡ (Geo.pow Geo.thirtySecond start
          * Geo.oneTwentyEightNinetyThirds)
          * commonFactor data
    factoredTarget =
      solve
        ( Geo.pow Geo.thirtySecond start
        ∷ Geo.oneTwentyEightNinetyThirds
        ∷ commonFactor data
        ∷ []
        )
  in
  ℚₚ.≤-trans
    (subst
      (λ upper →
        gapExteriorRectangle (pairMagnitude data)
          start gapTailCutoff lowCutoff ≤ upper)
      (Schur.rectangleRightScale
        Majorant.canonicalKernel scale lowCutoff gapTailCutoff)
      pointwiseToRectangle)
    (subst
      (λ upper →
        Majorant.rectangleSum
          Majorant.canonicalKernel lowCutoff gapTailCutoff * scale
        ≤ upper)
      factoredTarget
      scaledKernelBound)

finiteSchurLowExteriorTailClosed : Bool
finiteSchurLowExteriorTailClosed = true

finiteSchurGapExteriorTailClosed : Bool
finiteSchurGapExteriorTailClosed = true

finiteSchurLowExteriorTailClosedIsTrue :
  finiteSchurLowExteriorTailClosed ≡ true
finiteSchurLowExteriorTailClosedIsTrue = refl

finiteSchurGapExteriorTailClosedIsTrue :
  finiteSchurGapExteriorTailClosed ≡ true
finiteSchurGapExteriorTailClosedIsTrue = refl
