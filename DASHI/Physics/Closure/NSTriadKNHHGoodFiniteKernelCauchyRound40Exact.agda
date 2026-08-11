module DASHI.Physics.Closure.NSTriadKNHHGoodFiniteKernelCauchyRound40Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier--Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Result: finite weighted Cauchy--Schwarz inequality.
-- DOI: not applicable to the classical inequality.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- Close the finite shell/PV Cauchy step that sits immediately after residual
-- preservation and before time/viscosity absorption.  A kernel sample carries
-- a nonnegative magnitude k_i and an HH-good stretching scalar s_i satisfying
--
--   s_i^2 <= delta W_i.
--
-- Then the already machine-checked weighted Gram identity gives
--
--   (sum k_i s_i)^2
--      <= (sum k_i) (sum k_i s_i^2)
--      <= delta (sum k_i) (sum k_i W_i).
--
-- If the shell-localized periodized kernel has L1 mass at most C, this yields
--
--   (sum k_i s_i)^2 <= C delta (sum k_i W_i).
--
-- Thus the fixed directional threshold is harmless *after shell localization*:
-- the singular full kernel is never absolutely integrated.  What remains for
-- A3/A4 is to identify the actual shell-localized strain kernel with these
-- samples and feed the weighted local quantity into the time/dissipation
-- owner estimate uniformly in the cutoff.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoFiniteWeightedCauchyExact as Cauchy
import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold

record HHGoodKernelSample
    (parameter : Threshold.PositiveThreshold) : Set where
  constructor hh-good-kernel-sample
  field
    kernelMagnitude : ℚ
    stretch : ℚ
    localWeight : ℚ
    kernelMagnitudeNonnegative : 0ℚ ≤ kernelMagnitude
    localWeightNonnegative : 0ℚ ≤ localWeight
    localGoodStretchSquare :
      L2.square stretch
      ≤ Threshold.threshold parameter * localWeight

open HHGoodKernelSample public

asWeightedPair :
  ∀ {parameter} → HHGoodKernelSample parameter → Cauchy.WeightedPair
asWeightedPair sample =
  Cauchy.weighted-pair
    (kernelMagnitude sample)
    1ℚ
    (stretch sample)
    (kernelMagnitudeNonnegative sample)

mapWeightedPairs :
  ∀ {parameter} → List (HHGoodKernelSample parameter) →
  List Cauchy.WeightedPair
mapWeightedPairs [] = []
mapWeightedPairs (sample ∷ rest) =
  asWeightedPair sample ∷ mapWeightedPairs rest

kernelMass :
  ∀ {parameter} → List (HHGoodKernelSample parameter) → ℚ
kernelMass [] = 0ℚ
kernelMass (sample ∷ rest) =
  kernelMagnitude sample + kernelMass rest

weightedStretch :
  ∀ {parameter} → List (HHGoodKernelSample parameter) → ℚ
weightedStretch [] = 0ℚ
weightedStretch (sample ∷ rest) =
  kernelMagnitude sample * stretch sample + weightedStretch rest

weightedStretchSquareMass :
  ∀ {parameter} → List (HHGoodKernelSample parameter) → ℚ
weightedStretchSquareMass [] = 0ℚ
weightedStretchSquareMass (sample ∷ rest) =
  kernelMagnitude sample * L2.square (stretch sample)
  + weightedStretchSquareMass rest

weightedLocalMass :
  ∀ {parameter} → List (HHGoodKernelSample parameter) → ℚ
weightedLocalMass [] = 0ℚ
weightedLocalMass (sample ∷ rest) =
  kernelMagnitude sample * localWeight sample + weightedLocalMass rest

kernelMassNonnegative :
  ∀ {parameter}
    (samples : List (HHGoodKernelSample parameter)) →
  0ℚ ≤ kernelMass samples
kernelMassNonnegative [] = ℚP.≤-refl
kernelMassNonnegative (sample ∷ rest) =
  L2.addNonnegative
    (kernelMagnitudeNonnegative sample)
    (kernelMassNonnegative rest)

weightedLocalMassNonnegative :
  ∀ {parameter}
    (samples : List (HHGoodKernelSample parameter)) →
  0ℚ ≤ weightedLocalMass samples
weightedLocalMassNonnegative [] = ℚP.≤-refl
weightedLocalMassNonnegative (sample ∷ rest) =
  L2.addNonnegative
    (let
      instance
        kNN = nonNegative (kernelMagnitudeNonnegative sample)
        wNN = nonNegative (localWeightNonnegative sample)
        pNN = ℚP.nonNeg*nonNeg⇒nonNeg
          (kernelMagnitude sample) (localWeight sample)
     in ℚP.nonNegative⁻¹
          (kernelMagnitude sample * localWeight sample))
    (weightedLocalMassNonnegative rest)

leftEnergyIsKernelMass :
  ∀ {parameter} (samples : List (HHGoodKernelSample parameter)) →
  Cauchy.leftEnergy (mapWeightedPairs samples) ≡ kernelMass samples
leftEnergyIsKernelMass [] = refl
leftEnergyIsKernelMass (sample ∷ rest)
  rewrite leftEnergyIsKernelMass rest =
  solve (kernelMagnitude sample ∷ kernelMass rest ∷ [])

pairingIsWeightedStretch :
  ∀ {parameter} (samples : List (HHGoodKernelSample parameter)) →
  Cauchy.weightedPairing (mapWeightedPairs samples) ≡ weightedStretch samples
pairingIsWeightedStretch [] = refl
pairingIsWeightedStretch (sample ∷ rest)
  rewrite pairingIsWeightedStretch rest =
  solve
    (kernelMagnitude sample ∷ stretch sample ∷ weightedStretch rest ∷ [])

rightEnergyIsStretchSquareMass :
  ∀ {parameter} (samples : List (HHGoodKernelSample parameter)) →
  Cauchy.rightEnergy (mapWeightedPairs samples)
  ≡ weightedStretchSquareMass samples
rightEnergyIsStretchSquareMass [] = refl
rightEnergyIsStretchSquareMass (sample ∷ rest)
  rewrite rightEnergyIsStretchSquareMass rest = refl

weightedStretchSquareBelowThresholdLocalMass :
  ∀ {parameter}
    (samples : List (HHGoodKernelSample parameter)) →
  weightedStretchSquareMass samples
  ≤ Threshold.threshold parameter * weightedLocalMass samples
weightedStretchSquareBelowThresholdLocalMass {parameter} [] =
  subst
    (λ upper → 0ℚ ≤ upper)
    (solve (Threshold.threshold parameter ∷ []))
    ℚP.≤-refl
weightedStretchSquareBelowThresholdLocalMass
    {parameter} (sample ∷ rest) =
  let
    sampleScaled :
      kernelMagnitude sample * L2.square (stretch sample)
      ≤ kernelMagnitude sample
          * (Threshold.threshold parameter * localWeight sample)
    sampleScaled =
      let instance kernelNN = nonNegative (kernelMagnitudeNonnegative sample)
      in ℚP.*-monoˡ-≤-nonNeg
        (kernelMagnitude sample) (localGoodStretchSquare sample)

    restBound = weightedStretchSquareBelowThresholdLocalMass rest
    added = ℚP.+-mono-≤ sampleScaled restBound

    rightMeaning :
      kernelMagnitude sample
          * (Threshold.threshold parameter * localWeight sample)
      + Threshold.threshold parameter * weightedLocalMass rest
      ≡ Threshold.threshold parameter
          * weightedLocalMass (sample ∷ rest)
    rightMeaning = solve
      ( kernelMagnitude sample
      ∷ Threshold.threshold parameter
      ∷ localWeight sample
      ∷ weightedLocalMass rest
      ∷ [])
  in
  subst
    (λ upper → weightedStretchSquareMass (sample ∷ rest) ≤ upper)
    rightMeaning
    added

finiteKernelWeightedCauchy :
  ∀ {parameter}
    (samples : List (HHGoodKernelSample parameter)) →
  L2.square (weightedStretch samples)
  ≤ kernelMass samples * weightedStretchSquareMass samples
finiteKernelWeightedCauchy samples =
  let
    raw = Cauchy.finiteWeightedCauchy (mapWeightedPairs samples)
    upperChanged =
      subst
        (λ upper →
          L2.square (Cauchy.weightedPairing (mapWeightedPairs samples))
          ≤ upper)
        (cong₂ _*_
          (leftEnergyIsKernelMass samples)
          (rightEnergyIsStretchSquareMass samples))
        raw
  in
  subst
    (λ lower →
      lower ≤ kernelMass samples * weightedStretchSquareMass samples)
    (cong L2.square (pairingIsWeightedStretch samples))
    upperChanged

finiteHHGoodKernelThresholdBound :
  ∀ {parameter}
    (samples : List (HHGoodKernelSample parameter)) →
  L2.square (weightedStretch samples)
  ≤ kernelMass samples
      * (Threshold.threshold parameter * weightedLocalMass samples)
finiteHHGoodKernelThresholdBound {parameter} samples =
  let
    cauchy = finiteKernelWeightedCauchy samples
    local = weightedStretchSquareBelowThresholdLocalMass samples
    scaled :
      kernelMass samples * weightedStretchSquareMass samples
      ≤ kernelMass samples
          * (Threshold.threshold parameter * weightedLocalMass samples)
    scaled =
      let instance massNNI = nonNegative (kernelMassNonnegative samples)
      in ℚP.*-monoˡ-≤-nonNeg (kernelMass samples) local
  in
  ℚP.≤-trans cauchy scaled

record UniformShellKernelMassCertificate
    {parameter : Threshold.PositiveThreshold}
    (samples : List (HHGoodKernelSample parameter)) : Set where
  field
    uniformKernelConstant : ℚ
    uniformKernelConstantNonnegative : 0ℚ ≤ uniformKernelConstant
    kernelMassBelowUniformConstant :
      kernelMass samples ≤ uniformKernelConstant

open UniformShellKernelMassCertificate public

finiteHHGoodUniformKernelBound :
  ∀ {parameter}
    {samples : List (HHGoodKernelSample parameter)} →
  (certificate : UniformShellKernelMassCertificate samples) →
  L2.square (weightedStretch samples)
  ≤ uniformKernelConstant certificate
      * (Threshold.threshold parameter * weightedLocalMass samples)
finiteHHGoodUniformKernelBound {parameter} {samples} certificate =
  let
    first = finiteHHGoodKernelThresholdBound samples

    thresholdLocalNN :
      0ℚ ≤ Threshold.threshold parameter * weightedLocalMass samples
    thresholdLocalNN =
      let
        instance
          thresholdNNI = nonNegative (Threshold.thresholdNonnegative parameter)
          localNNI = nonNegative (weightedLocalMassNonnegative samples)
          productNNI = ℚP.nonNeg*nonNeg⇒nonNeg
            (Threshold.threshold parameter) (weightedLocalMass samples)
      in
      ℚP.nonNegative⁻¹
        (Threshold.threshold parameter * weightedLocalMass samples)

    second :
      kernelMass samples
        * (Threshold.threshold parameter * weightedLocalMass samples)
      ≤ uniformKernelConstant certificate
        * (Threshold.threshold parameter * weightedLocalMass samples)
    second =
      let instance productNNI = nonNegative thresholdLocalNN
      in ℚP.*-monoʳ-≤-nonNeg
        (Threshold.threshold parameter * weightedLocalMass samples)
        (kernelMassBelowUniformConstant certificate)
  in
  ℚP.≤-trans first second

hhGoodFiniteKernelCauchyClosed : Bool
hhGoodFiniteKernelCauchyClosed = true

physicalShellLocalizedStrainKernelSamplesConstructed : Bool
physicalShellLocalizedStrainKernelSamplesConstructed = false

physicalHHGoodTimeDissipationAbsorptionConstructed : Bool
physicalHHGoodTimeDissipationAbsorptionConstructed = false

hhGoodFiniteKernelCauchyClosedIsTrue :
  hhGoodFiniteKernelCauchyClosed ≡ true
hhGoodFiniteKernelCauchyClosedIsTrue = refl
