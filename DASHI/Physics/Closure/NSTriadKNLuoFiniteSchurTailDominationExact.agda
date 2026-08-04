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
-- Turn the canonical quantitative tail theorem into a tail theorem for an
-- arbitrary nonnegative interaction family satisfying the pointwise Schur
-- domination
--
--   A(j,d) <= (1/4)^j (1/32)^d C.
--
-- Every finite low-shell exterior strip and every finite gap exterior strip
-- is bounded by a geometrically decaying expression:
--
--   low exterior <= (128/93)(1/4)^J C,
--   gap exterior <= (128/93)(1/32)^D C.
--
-- This is the missing finite-extension estimate required before the uniform
-- rectangle bounds can be promoted to an infinite Cauchy family.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality as Eq
  using (cong; cong₂; subst; sym; trans)
open Eq.≡-Reasoning

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNOutputRelocationPositiveKernelMajorant as Majorant
import DASHI.Physics.Closure.NSTriadKNLuoFinitePhysicalSchurSummationExact as Schur
import DASHI.Physics.Closure.NSTriadKNLuoCanonicalSchurTailExact as Tail

lowTailRectangle :
  (Nat → Nat → ℚ) → Nat → Nat → Nat → ℚ
lowTailRectangle family start lowTailCutoff gapCutoff =
  Majorant.sumTo
    (λ offset → Majorant.rowSum family (start + offset) gapCutoff)
    lowTailCutoff

gapTailRow :
  (Nat → Nat → ℚ) → Nat → Nat → Nat → ℚ
gapTailRow family lowShell start gapTailCutoff =
  Majorant.sumTo
    (λ offset → family lowShell (start + offset))
    gapTailCutoff

gapTailRectangle :
  (Nat → Nat → ℚ) → Nat → Nat → Nat → ℚ
gapTailRectangle family start gapTailCutoff lowCutoff =
  Majorant.sumTo
    (λ lowShell → gapTailRow family lowShell start gapTailCutoff)
    lowCutoff

canonicalRowMeaning :
  (lowShell gapCutoff : Nat) →
  Majorant.rowSum Majorant.canonicalKernel lowShell gapCutoff
  ≡ Geo.pow Geo.quarter lowShell
      * Geo.partialSum Geo.thirtySecond gapCutoff
canonicalRowMeaning lowShell gapCutoff =
  trans
    (Majorant.scaleSum
      (Geo.pow Geo.quarter lowShell)
      (Geo.pow Geo.thirtySecond)
      gapCutoff)
    (cong
      (Geo.pow Geo.quarter lowShell *_)
      (Majorant.powerSumMeaning Geo.thirtySecond gapCutoff))

canonicalLowTailFactorization :
  (start lowTailCutoff gapCutoff : Nat) →
  lowTailRectangle Majorant.canonicalKernel
    start lowTailCutoff gapCutoff
  ≡ Tail.lowExteriorStrip start lowTailCutoff gapCutoff
canonicalLowTailFactorization start lowTailCutoff gapCutoff =
  begin
    lowTailRectangle Majorant.canonicalKernel
      start lowTailCutoff gapCutoff
  ≡⟨ Tail.sumToCong
       (λ offset →
         Majorant.rowSum Majorant.canonicalKernel
           (start + offset) gapCutoff)
       (λ offset →
         Geo.pow Geo.quarter (start + offset)
           * Geo.partialSum Geo.thirtySecond gapCutoff)
       lowTailCutoff
       (λ offset → canonicalRowMeaning (start + offset) gapCutoff) ⟩
    Majorant.sumTo
      (λ offset →
        Geo.pow Geo.quarter (start + offset)
          * Geo.partialSum Geo.thirtySecond gapCutoff)
      lowTailCutoff
  ≡⟨ Majorant.rightScaleSum
       (λ offset → Geo.pow Geo.quarter (start + offset))
       (Geo.partialSum Geo.thirtySecond gapCutoff)
       lowTailCutoff ⟩
    Tail.shiftedPowerSum Geo.quarter start lowTailCutoff
      * Geo.partialSum Geo.thirtySecond gapCutoff
  ≡⟨ refl ⟩
    Tail.lowExteriorStrip start lowTailCutoff gapCutoff
  ∎

canonicalGapTailRowMeaning :
  (lowShell start gapTailCutoff : Nat) →
  gapTailRow Majorant.canonicalKernel
    lowShell start gapTailCutoff
  ≡ Geo.pow Geo.quarter lowShell
      * Tail.shiftedPowerSum Geo.thirtySecond start gapTailCutoff
canonicalGapTailRowMeaning lowShell start gapTailCutoff =
  trans
    (Tail.sumToCong
      (λ offset →
        Majorant.canonicalKernel lowShell (start + offset))
      (λ offset →
        Geo.pow Geo.quarter lowShell
          * Geo.pow Geo.thirtySecond (start + offset))
      gapTailCutoff
      (λ offset → refl))
    (Majorant.scaleSum
      (Geo.pow Geo.quarter lowShell)
      (λ offset → Geo.pow Geo.thirtySecond (start + offset))
      gapTailCutoff)

canonicalGapTailFactorization :
  (start gapTailCutoff lowCutoff : Nat) →
  gapTailRectangle Majorant.canonicalKernel
    start gapTailCutoff lowCutoff
  ≡ Tail.gapExteriorStrip start gapTailCutoff lowCutoff
canonicalGapTailFactorization start gapTailCutoff lowCutoff =
  begin
    gapTailRectangle Majorant.canonicalKernel
      start gapTailCutoff lowCutoff
  ≡⟨ Tail.sumToCong
       (λ lowShell →
         gapTailRow Majorant.canonicalKernel
           lowShell start gapTailCutoff)
       (λ lowShell →
         Geo.pow Geo.quarter lowShell
           * Tail.shiftedPowerSum Geo.thirtySecond
               start gapTailCutoff)
       lowCutoff
       (λ lowShell →
         canonicalGapTailRowMeaning
           lowShell start gapTailCutoff) ⟩
    Majorant.sumTo
      (λ lowShell →
        Geo.pow Geo.quarter lowShell
          * Tail.shiftedPowerSum Geo.thirtySecond
              start gapTailCutoff)
      lowCutoff
  ≡⟨ Majorant.rightScaleSum
       (Geo.pow Geo.quarter)
       (Tail.shiftedPowerSum Geo.thirtySecond start gapTailCutoff)
       lowCutoff ⟩
    Majorant.sumTo (Geo.pow Geo.quarter) lowCutoff
      * Tail.shiftedPowerSum Geo.thirtySecond start gapTailCutoff
  ≡⟨ cong
       (λ lowPrefix →
         lowPrefix
         * Tail.shiftedPowerSum Geo.thirtySecond
             start gapTailCutoff)
       (Majorant.powerSumMeaning Geo.quarter lowCutoff) ⟩
    Geo.partialSum Geo.quarter lowCutoff
      * Tail.shiftedPowerSum Geo.thirtySecond start gapTailCutoff
  ≡⟨ refl ⟩
    Tail.gapExteriorStrip start gapTailCutoff lowCutoff
  ∎

lowTailRectangleMonotone :
  (left right : Nat → Nat → ℚ) →
  (start lowTailCutoff gapCutoff : Nat) →
  ((lowShell gap : Nat) → left lowShell gap ≤ right lowShell gap) →
  lowTailRectangle left start lowTailCutoff gapCutoff
  ≤ lowTailRectangle right start lowTailCutoff gapCutoff
lowTailRectangleMonotone left right start lowTailCutoff gapCutoff
  pointwise =
  Majorant.sumToMonotone
    (λ offset → Majorant.rowSum left (start + offset) gapCutoff)
    (λ offset → Majorant.rowSum right (start + offset) gapCutoff)
    lowTailCutoff
    (λ offset →
      Majorant.sumToMonotone
        (left (start + offset))
        (right (start + offset))
        gapCutoff
        (pointwise (start + offset)))

gapTailRectangleMonotone :
  (left right : Nat → Nat → ℚ) →
  (start gapTailCutoff lowCutoff : Nat) →
  ((lowShell gap : Nat) → left lowShell gap ≤ right lowShell gap) →
  gapTailRectangle left start gapTailCutoff lowCutoff
  ≤ gapTailRectangle right start gapTailCutoff lowCutoff
gapTailRectangleMonotone left right start gapTailCutoff lowCutoff
  pointwise =
  Majorant.sumToMonotone
    (λ lowShell → gapTailRow left lowShell start gapTailCutoff)
    (λ lowShell → gapTailRow right lowShell start gapTailCutoff)
    lowCutoff
    (λ lowShell →
      Majorant.sumToMonotone
        (λ offset → left lowShell (start + offset))
        (λ offset → right lowShell (start + offset))
        gapTailCutoff
        (λ offset → pointwise lowShell (start + offset)))

lowTailRightScale :
  (kernel : Nat → Nat → ℚ) →
  (scale : ℚ) →
  (start lowTailCutoff gapCutoff : Nat) →
  lowTailRectangle
    (λ lowShell gap → kernel lowShell gap * scale)
    start lowTailCutoff gapCutoff
  ≡ lowTailRectangle kernel start lowTailCutoff gapCutoff * scale
lowTailRightScale kernel scale start zero gapCutoff =
  Majorant.rightScaleSum (kernel start) scale gapCutoff
lowTailRightScale kernel scale start (suc lowTailCutoff) gapCutoff =
  begin
    lowTailRectangle
      (λ lowShell gap → kernel lowShell gap * scale)
      start (suc lowTailCutoff) gapCutoff
  ≡⟨ refl ⟩
    Majorant.rowSum
      (λ lowShell gap → kernel lowShell gap * scale)
      (start + suc lowTailCutoff) gapCutoff
    + lowTailRectangle
        (λ lowShell gap → kernel lowShell gap * scale)
        start lowTailCutoff gapCutoff
  ≡⟨ cong₂ _+_
       (Majorant.rightScaleSum
         (kernel (start + suc lowTailCutoff)) scale gapCutoff)
       (lowTailRightScale
         kernel scale start lowTailCutoff gapCutoff) ⟩
    Majorant.rowSum kernel (start + suc lowTailCutoff) gapCutoff * scale
    + lowTailRectangle kernel start lowTailCutoff gapCutoff * scale
  ≡⟨ Majorant.rightScaleSumAux
       (Majorant.rowSum kernel (start + suc lowTailCutoff) gapCutoff)
       (lowTailRectangle kernel start lowTailCutoff gapCutoff)
       scale ⟩
    lowTailRectangle kernel start (suc lowTailCutoff) gapCutoff * scale
  ∎

gapTailRightScale :
  (kernel : Nat → Nat → ℚ) →
  (scale : ℚ) →
  (start gapTailCutoff lowCutoff : Nat) →
  gapTailRectangle
    (λ lowShell gap → kernel lowShell gap * scale)
    start gapTailCutoff lowCutoff
  ≡ gapTailRectangle kernel start gapTailCutoff lowCutoff * scale
gapTailRightScale kernel scale start gapTailCutoff zero =
  Majorant.rightScaleSum
    (λ offset → kernel zero (start + offset))
    scale
    gapTailCutoff
gapTailRightScale kernel scale start gapTailCutoff (suc lowCutoff) =
  begin
    gapTailRectangle
      (λ lowShell gap → kernel lowShell gap * scale)
      start gapTailCutoff (suc lowCutoff)
  ≡⟨ refl ⟩
    gapTailRow
      (λ lowShell gap → kernel lowShell gap * scale)
      (suc lowCutoff) start gapTailCutoff
    + gapTailRectangle
        (λ lowShell gap → kernel lowShell gap * scale)
        start gapTailCutoff lowCutoff
  ≡⟨ cong₂ _+_
       (Majorant.rightScaleSum
         (λ offset → kernel (suc lowCutoff) (start + offset))
         scale gapTailCutoff)
       (gapTailRightScale
         kernel scale start gapTailCutoff lowCutoff) ⟩
    gapTailRow kernel (suc lowCutoff) start gapTailCutoff * scale
    + gapTailRectangle kernel start gapTailCutoff lowCutoff * scale
  ≡⟨ Majorant.rightScaleSumAux
       (gapTailRow kernel (suc lowCutoff) start gapTailCutoff)
       (gapTailRectangle kernel start gapTailCutoff lowCutoff)
       scale ⟩
    gapTailRectangle kernel start gapTailCutoff (suc lowCutoff) * scale
  ∎

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

finiteLowExteriorTailBound :
  (data : FiniteSchurTailData) →
  (start lowTailCutoff gapCutoff : Nat) →
  lowTailRectangle (pairMagnitude data)
    start lowTailCutoff gapCutoff
  ≤ (Geo.pow Geo.quarter start
      * Geo.oneTwentyEightNinetyThirds)
      * commonFactor data
finiteLowExteriorTailBound data start lowTailCutoff gapCutoff =
  let
    toScaledKernel =
      lowTailRectangleMonotone
        (pairMagnitude data)
        (λ lowShell gap →
          Majorant.canonicalKernel lowShell gap * commonFactor data)
        start lowTailCutoff gapCutoff
        (pointwiseTailDomination data)

    factorScale =
      lowTailRightScale
        Majorant.canonicalKernel
        (commonFactor data)
        start lowTailCutoff gapCutoff

    canonicalBound =
      let instance commonIsNonnegative =
        nonNegative (commonFactorNonnegative data)
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        (commonFactor data)
        (subst
          (λ left →
            left
            ≤ Geo.pow Geo.quarter start
                * Geo.oneTwentyEightNinetyThirds)
          (canonicalLowTailFactorization start lowTailCutoff gapCutoff)
          (Tail.lowExteriorStripBound
            start lowTailCutoff gapCutoff))
  in
  ℚₚ.≤-trans
    (subst
      (λ upper →
        lowTailRectangle (pairMagnitude data)
          start lowTailCutoff gapCutoff
        ≤ upper)
      factorScale
      toScaledKernel)
    canonicalBound

finiteGapExteriorTailBound :
  (data : FiniteSchurTailData) →
  (start gapTailCutoff lowCutoff : Nat) →
  gapTailRectangle (pairMagnitude data)
    start gapTailCutoff lowCutoff
  ≤ (Geo.pow Geo.thirtySecond start
      * Geo.oneTwentyEightNinetyThirds)
      * commonFactor data
finiteGapExteriorTailBound data start gapTailCutoff lowCutoff =
  let
    toScaledKernel =
      gapTailRectangleMonotone
        (pairMagnitude data)
        (λ lowShell gap →
          Majorant.canonicalKernel lowShell gap * commonFactor data)
        start gapTailCutoff lowCutoff
        (pointwiseTailDomination data)

    factorScale =
      gapTailRightScale
        Majorant.canonicalKernel
        (commonFactor data)
        start gapTailCutoff lowCutoff

    canonicalBound =
      let instance commonIsNonnegative =
        nonNegative (commonFactorNonnegative data)
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        (commonFactor data)
        (subst
          (λ left →
            left
            ≤ Geo.pow Geo.thirtySecond start
                * Geo.oneTwentyEightNinetyThirds)
          (canonicalGapTailFactorization start gapTailCutoff lowCutoff)
          (Tail.gapExteriorStripBound
            start gapTailCutoff lowCutoff))
  in
  ℚₚ.≤-trans
    (subst
      (λ upper →
        gapTailRectangle (pairMagnitude data)
          start gapTailCutoff lowCutoff
        ≤ upper)
      factorScale
      toScaledKernel)
    canonicalBound

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
