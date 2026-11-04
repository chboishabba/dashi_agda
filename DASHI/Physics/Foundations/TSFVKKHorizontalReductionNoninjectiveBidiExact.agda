{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.TSFVKKHorizontalReductionNoninjectiveBidiExact where

------------------------------------------------------------------------
-- P08/P11 EXACT BACKWARD STEELMAN: 4D HORIZONTAL KK METRIC
-- CANNOT UNIQUELY RECOVER THE 5D RADION / FIBRE METRIC.
--
-- Reuses the ACTUAL earlier 5D metric constructor and genuine
-- horizontal-reduction theorem, not a new abstract metric witness.
--
-- Given ANY g4 and ANY U(1) KK connection A, two distinct radii
-- b1²,b2² have exactly the SAME horizontal 4D bilinear g4.
-- Nevertheless the whole five-metrics differ: the vertical probe
-- (v,1-A(v)) and (w,1-A(w)) reads g4(v,w)+b², hence recovers
-- the otherwise lost b² from the selected original five-bilinear.
-- No function extensionality, UIP or invented physical g4 needed.
--
-- The distinction between two physically ADMISSIBLE positive radii
-- is a physical/source input; the theorem is generic for any given
-- inequivalent radii. A real 5D Einstein/radion solution and a
-- *measured* fifth-sector observable remain OPEN. This theorem
-- forbids claiming unique 5D origin from the 4D metric alone.
--
-- Sources: Kaluza--Klein; existing DASHI #1241 donor and
-- TSFVKKSelectedHorizontalMetricSchurExact (PR #1460);
-- P11 inverse-source identification and negative-control contract.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)
import Data.Rational.Tactic.RingSolver as Ring

import DASHI.Physics.Foundations.TSFVKKSelectedHorizontalMetricSchurExact as KK

-- The original horizontal reduction is EXACTLY independent of radius.
-- No extra equality of reduced 4D metric carriers is assumed.
sameOriginalFourBilinearForAnyTwoRadii :
  ∀ {V : Set}
    (g4 : V → V → ℚ)
    (connection : V → ℚ)
    (radius1 radius2 : ℚ)
    (v w : V) →
  KK.KK5Bilinear g4 connection radius1
    v (KK.horizontalCircleComponent connection v)
    w (KK.horizontalCircleComponent connection w)
  ≡
  KK.KK5Bilinear g4 connection radius2
    v (KK.horizontalCircleComponent connection v)
    w (KK.horizontalCircleComponent connection w)
sameOriginalFourBilinearForAnyTwoRadii
    g4 connection radius1 radius2 v w =
  trans
    (KK.actualKKHorizontalReductionIsOriginalFourMetric
      g4 connection radius1 v w)
    (sym
      (KK.actualKKHorizontalReductionIsOriginalFourMetric
        g4 connection radius2 v w))

-- The SAME physical connection A supplies the vertical reference
-- vectors. A unit fibre displacement produces g4(v,w)+b²,
-- and subtraction of the matched original g4 leaves exactly b².
originalFiveMetricVerticalProbeReadsFibreRadius :
  ∀ {V : Set}
    (g4 : V → V → ℚ)
    (connection : V → ℚ)
    (radiusSquared : ℚ)
    (v w : V) →
    KK.KK5Bilinear g4 connection radiusSquared
      v (1ℚ - connection v)
      w (1ℚ - connection w)
    - g4 v w
    ≡ radiusSquared
originalFiveMetricVerticalProbeReadsFibreRadius
    g4 connection radiusSquared v w =
  Ring.solve-∀
    (g4 v w) (connection v) (connection w) radiusSquared

-- Exact result: IF the original full 5D metrics were pointwise equal,
-- their fibre-radius readouts would have to agree. This is the
-- missing reverse BIDI discriminator in the existing KK programme.
originalFiveMetricEqualityForcesSameFibreRadius :
  ∀ {V : Set}
    (g4 : V → V → ℚ)
    (connection : V → ℚ)
    (radius1 radius2 : ℚ)
    (v w : V) →
    (∀ x fibreX y fibreY →
       KK.KK5Bilinear g4 connection radius1
         x fibreX y fibreY
       ≡
       KK.KK5Bilinear g4 connection radius2
         x fibreX y fibreY) →
    radius1 ≡ radius2
originalFiveMetricEqualityForcesSameFibreRadius
    g4 connection radius1 radius2 v w same =
  trans
    (sym
      (originalFiveMetricVerticalProbeReadsFibreRadius
        g4 connection radius1 v w))
    (trans
      (cong
        (λ z → z - g4 v w)
        (same
          v (1ℚ - connection v)
          w (1ℚ - connection w)))
      (originalFiveMetricVerticalProbeReadsFibreRadius
        g4 connection radius2 v w))

-- Distinct fifth-circle radii NEVER imply distinct 4D reduced
-- metric: the reverse-map noninjectivity holds for every matched
-- observer g4 and connection, as soon as a chosen tangent pair exists.
originalFourMetricCannotUniquelyLiftFibreRadius :
  ∀ {V : Set}
    (g4 : V → V → ℚ)
    (connection : V → ℚ)
    (radius1 radius2 : ℚ)
    (v w : V) →
    (radius1 ≡ radius2 → ⊥) →
    (∀ x fibreX y fibreY →
      KK.KK5Bilinear g4 connection radius1
        x fibreX y fibreY
      ≡
      KK.KK5Bilinear g4 connection radius2
        x fibreX y fibreY) →
    ⊥
originalFourMetricCannotUniquelyLiftFibreRadius
    g4 connection radius1 radius2 v w different same =
  different
    (originalFiveMetricEqualityForcesSameFibreRadius
      g4 connection radius1 radius2 v w same)

-- The same proof leaves room for valid effective KK physics: a
-- fifth-sector observable and actual 5D fields can distinguish the
-- lifts, but the original 4D observer quadratic alone cannot.
