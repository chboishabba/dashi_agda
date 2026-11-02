{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLorentz31DirectionalKKHodgeExact where

-- Source-first bridge to YM Voyager #1444 and KK/E6 #1241.
-- REUSE: YMClayVoyagerR4HodgeBasisExact (classical Euclidean *^2=+1),
-- YMClayVoyagerDimensionSignatureForkExact (Euclidean/KK/stochastic separation),
-- and Lorentz31DirectionalProbeExact (independent finite arrow input).
--
-- Conventional signed-basis Hodge mathematics belongs to Hodge and the
-- standard differential-geometry literature. This finite proof expression
-- is DASHI's; no continuum star, OS Wick rotation, KK metric/action
-- reduction, or physical YM mass gap is inferred.

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.Lorentz31DirectionalProbeExact as L31
import DASHI.Physics.YangMills.YMClayVoyagerR4HodgeBasisExact as Eu
import DASHI.Physics.YangMills.YMClayVoyagerDimensionSignatureForkExact as Dim

-- On an oriented orthonormal Lorentzian (3+1) basis, *^2=-1 on 2-forms.
-- This explicit finite convention is compatible with the usual signature
-- (-,+,+,+), orientation and signed-basis convention. It is NOT a Wick map.
negateSigned : Eu.SignedBasisTwoForm → Eu.SignedBasisTwoForm
negateSigned (Eu.signed s b) = Eu.signed (Eu.flip s) b

lorentzStar : Eu.SignedBasisTwoForm → Eu.SignedBasisTwoForm
lorentzStar (Eu.signed s Eu.e01) = Eu.signed s Eu.e23
lorentzStar (Eu.signed s Eu.e02) = Eu.signed (Eu.flip s) Eu.e13
lorentzStar (Eu.signed s Eu.e03) = Eu.signed s Eu.e12
lorentzStar (Eu.signed s Eu.e12) = Eu.signed (Eu.flip s) Eu.e03
lorentzStar (Eu.signed s Eu.e13) = Eu.signed s Eu.e02
lorentzStar (Eu.signed s Eu.e23) = Eu.signed (Eu.flip s) Eu.e01

lorentzStarSquareIsNegative :
  (b : Eu.SignedBasisTwoForm) →
  lorentzStar (lorentzStar b) ≡ negateSigned b
lorentzStarSquareIsNegative (Eu.signed Eu.plus Eu.e01) = refl
lorentzStarSquareIsNegative (Eu.signed Eu.minus Eu.e01) = refl
lorentzStarSquareIsNegative (Eu.signed Eu.plus Eu.e02) = refl
lorentzStarSquareIsNegative (Eu.signed Eu.minus Eu.e02) = refl
lorentzStarSquareIsNegative (Eu.signed Eu.plus Eu.e03) = refl
lorentzStarSquareIsNegative (Eu.signed Eu.minus Eu.e03) = refl
lorentzStarSquareIsNegative (Eu.signed Eu.plus Eu.e12) = refl
lorentzStarSquareIsNegative (Eu.signed Eu.minus Eu.e12) = refl
lorentzStarSquareIsNegative (Eu.signed Eu.plus Eu.e13) = refl
lorentzStarSquareIsNegative (Eu.signed Eu.minus Eu.e13) = refl
lorentzStarSquareIsNegative (Eu.signed Eu.plus Eu.e23) = refl
lorentzStarSquareIsNegative (Eu.signed Eu.minus Eu.e23) = refl

-- YM source-owner square remains the *Euclidean* +1 law. The two are
-- deliberately distinct; the same carrier does not prove a continuation.
euclideanStarSquareIsPositive :
  ∀ b → Eu.euclideanHodgeStar (Eu.euclideanHodgeStar b) ≡ b
euclideanStarSquareIsPositive = Eu.hodgeSquareOnSignedBasis

euclideanAndLorentzStarNotDefinitionallySame :
  (∀ b → Eu.euclideanHodgeStar b ≡ lorentzStar b) → L31.⊥
euclideanAndLorentzStarNotDefinitionallySame same
  with same (Eu.signed Eu.plus Eu.e23)
... | ()

-- A physical same-object interface to the ORIGINAL KK branch, not a
-- fabricated implementation of its selected action, Einstein source,
-- OS reconstruction, SU2 Haar measure or 5D anomaly cancellation.
record SameSourceKKYMContinuation : Set₁ where
  field
    Metric4D : Set
    Metric5D : Set
    Euclidean4DYM : Set

    selectedMetric5D : Metric5D
    reduceKKMetric : Metric5D → Metric4D
    selectedMetric4D : Metric4D
    selectedMetricIsKKReduction :
      reduceKKMetric selectedMetric5D ≡ selectedMetric4D

    signatureProbe : L31.Axis → Agda.Builtin.Bool.Bool
    signatureSigns : L31.Axis → L31.AxisSign
    observedDirectionalEvidence : L31.DirectionalProbe signatureProbe
    sameMetricCalibration : L31.AxisCalibration signatureProbe signatureSigns

    selectedEuclideanYM : Euclidean4DYM
    OSReconstructsSelectedLorentzMetric :
      Euclidean4DYM → Metric4D → Set
    selectedOSContinuation :
      OSReconstructsSelectedLorentzMetric selectedEuclideanYM selectedMetric4D

    SelectedKKStress : Metric5D → Set
    SelectedYMStress : Euclidean4DYM → Set
    SameMetricVariation : Metric5D → Euclidean4DYM → Set
    actualKKStress : SelectedKKStress selectedMetric5D
    actualYMStress : SelectedYMStress selectedEuclideanYM
    physicalStressAgreement :
      SameMetricVariation selectedMetric5D selectedEuclideanYM

sameSourceDirectionalLorentzSignature :
  (w : SameSourceKKYMContinuation) →
  L31.actualAxisCounts
    (SameSourceKKYMContinuation.signatureSigns w)
  ≡ L31.signature 3 1
sameSourceDirectionalLorentzSignature w =
  L31.calibratedProbeForcesThreePlusOne
    (SameSourceKKYMContinuation.observedDirectionalEvidence w)
    (SameSourceKKYMContinuation.sameMetricCalibration w)

