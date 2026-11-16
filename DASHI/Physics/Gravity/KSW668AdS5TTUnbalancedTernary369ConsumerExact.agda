module DASHI.Physics.Gravity.KSW668AdS5TTUnbalancedTernary369ConsumerExact where

------------------------------------------------------------------------
-- ORIGINAL KSW668 a=t Poincare AdS5 spin-2 yy source.
--
-- This is an exact *consumer* of the pre-existing Base369.TriTruth
-- unsigned/unbalanced rank 0/1/2, NOT an invented ternary physical
-- amplitude, Monster action, cyclic physical symmetry or 3/6/9
-- effective-dimensional gravity theorem.
--
-- Original angular tensor symbol:
--   S_yy/|k|^4=(mu^4+6mu^2+1)/8
--       =(2/5)P0(mu)+(4/7)P2(mu)+(1/35)P4(mu).
-- The three rank slots q=0,1,2 encode ell=2q=0,2,4, and
-- the independent exact radial FV/evolution has dimension d=3+4q
-- =3,7,11. Rotation of slot labels does NOT commute with the
-- physical radial operators: Delta_d(r^2)=2d yields 6!=14!=22.
--
-- Amplitude vectors are arbitrarily real/complex, NOT ternary-valued.
-- Source-to-Weyl boundary trace, physical signal and Agda 2.9
-- kernel verification remain OPEN.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _*_; -_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

import Base369 as Base
import DASHI.Physics.Gravity.KSW668AdS5TTMultipoleAngularRationalExact as TT

data OriginalEvenHarmonic : Set where
  harmonic0 harmonic2 harmonic4 : OriginalEvenHarmonic

toUnsignedTernary : OriginalEvenHarmonic → Base.TriTruth
toUnsignedTernary harmonic0 = Base.tri-low
toUnsignedTernary harmonic2 = Base.tri-mid
toUnsignedTernary harmonic4 = Base.tri-high

fromUnsignedTernary : Base.TriTruth → OriginalEvenHarmonic
fromUnsignedTernary Base.tri-low = harmonic0
fromUnsignedTernary Base.tri-mid = harmonic2
fromUnsignedTernary Base.tri-high = harmonic4

harmonicTernaryRoundTrip : (h : OriginalEvenHarmonic) →
  fromUnsignedTernary (toUnsignedTernary h) ≡ h
harmonicTernaryRoundTrip harmonic0 = refl
harmonicTernaryRoundTrip harmonic2 = refl
harmonicTernaryRoundTrip harmonic4 = refl

ternaryHarmonicRoundTrip : (q : Base.TriTruth) →
  toUnsignedTernary (fromUnsignedTernary q) ≡ q
ternaryHarmonicRoundTrip Base.tri-low = refl
ternaryHarmonicRoundTrip Base.tri-mid = refl
ternaryHarmonicRoundTrip Base.tri-high = refl

originalEll : Base.TriTruth → Nat
originalEll q = 2 * Base.tri-index q

originalEffectiveRadialDimension : Base.TriTruth → Nat
originalEffectiveRadialDimension q = TT.effRadialDimension (originalEll q)

q0Ell : originalEll Base.tri-low ≡ 0
q0Ell = refl

q1Ell : originalEll Base.tri-mid ≡ 2
q1Ell = refl

q2Ell : originalEll Base.tri-high ≡ 4
q2Ell = refl

q0Dimension : originalEffectiveRadialDimension Base.tri-low ≡ 3
q0Dimension = refl

q1Dimension : originalEffectiveRadialDimension Base.tri-mid ≡ 7
q1Dimension = refl

q2Dimension : originalEffectiveRadialDimension Base.tri-high ≡ 11
q2Dimension = refl

originalWeightedLegendreAt : Base.TriTruth → ℚ → ℚ
originalWeightedLegendreAt Base.tri-low  μ = ((+ 2) / 5) * TT.p0 μ
originalWeightedLegendreAt Base.tri-mid  μ = ((+ 4) / 7) * TT.p2 μ
originalWeightedLegendreAt Base.tri-high μ = ((+ 1) / 35) * TT.p4 μ

originalTernaryLegendreSum : ℚ → ℚ
originalTernaryLegendreSum μ =
  originalWeightedLegendreAt Base.tri-low μ
  + originalWeightedLegendreAt Base.tri-mid μ
  + originalWeightedLegendreAt Base.tri-high μ

originalAngularSourceViaExistingBase369 :
  (μ : ℚ) → TT.originalTTYYAngular μ ≡ originalTernaryLegendreSum μ
originalAngularSourceViaExistingBase369 μ =
  TT.originalTTThreeMultipoles μ

-- At receiver axis mu=1, all three P_l(1)=1 and the
-- separately evolved mode contributions add linearly.
originalThreeModeAxisWeightIsOne :
  originalTernaryLegendreSum 1ℚ ≡ 1ℚ
originalThreeModeAxisWeightIsOne = ℚRing.solve []

-- The native Base369 cyclic label rotation is perfectly valid as a
-- *CODEC operation*, but is NOT a symmetry of the physical radial PDE.
-- Already for the lowest labelled channel, the dimension changes 3->7.
originalCyclicLabelRotatesEffectiveDimension :
  originalEffectiveRadialDimension (Base.rotateTri Base.tri-low) ≡ 7
originalCyclicLabelRotatesEffectiveDimension = refl

originalCyclicLabelFailsPhysicalRadialDimension :
  originalEffectiveRadialDimension (Base.rotateTri Base.tri-low)
  ≡ originalEffectiveRadialDimension Base.tri-low → ⊥
originalCyclicLabelFailsPhysicalRadialDimension ()

-- The more physically discriminating first-cell r^2 witness is
-- Delta_d(r^2)=2d; for q=0->q=1, 6 vs 14.
originalFirstCellQuadraticLow : 2 * originalEffectiveRadialDimension Base.tri-low ≡ 6
originalFirstCellQuadraticLow = refl

originalFirstCellQuadraticMid : 2 * originalEffectiveRadialDimension Base.tri-mid ≡ 14
originalFirstCellQuadraticMid = refl

originalCyclicLabelFailsQuadraticRadialAction :
  2 * originalEffectiveRadialDimension (Base.rotateTri Base.tri-low)
  ≡ 2 * originalEffectiveRadialDimension Base.tri-low → ⊥
originalCyclicLabelFailsQuadraticRadialAction ()

-- The original complete source-to-both-Weyl receiver remains a
-- 3-channel linear map subject to independent per-channel convergence
-- and real-metric constraint validation; no measured graviton claimed.
