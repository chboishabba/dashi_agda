module DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalRateGapExact where

------------------------------------------------------------------------
-- S2b2d1b2 / PHYSICAL CELL-RATE GAP ON THE LIVE RATIONAL FOURIER CARRIER
--
-- The open covariance theorem should not retain an abstract rate function.
-- On the literal Galerkin carrier
--
--   rho(m) = nu |m|^2,
--   r(tau) = rho(p_tau) + rho(q_tau).
--
-- R571/S2b2c2a already proves, for every additive rational integer embedding E,
--
--   |m|^2_live = c^2 N(m),   c = E(1),
--
-- where N(m) is the literal integer-lattice squared norm embedded in Q.
-- Therefore
--
--   r_alpha - r_beta
--     = nu c^2
--       [N(p_alpha)+N(q_alpha)-N(p_beta)-N(q_beta)].
--
-- This file closes that exact same-object transport and its absolute-value
-- version.  No shell bound or state estimate is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using
  (ℚ; 0ℚ; Positive; _+_; _-_; _*_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinWaleffeAmplitudeTangentRound94Exact as R94
import DASHI.Physics.Closure.NSTriadKNRationalIntegerEmbeddingModeNormScaleExact as Scale

F : C3.RealField _
F = Rational.rationalRealField

module PhysicalRateGap
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (viscosityPositive : Positive (Field30.viscosity physicalSystem)) where

  E : C3.IntegerEmbedding F
  E = Field30.physicalEmbedding physicalSystem

  I : C3.ModeInverseSquare F E
  I = Field30.physicalInverseSquare physicalSystem

  nu : ℚ
  nu = Field30.viscosity physicalSystem

  nuNonnegative : 0ℚ ≤ nu
  nuNonnegative = ℚP.<⇒≤ (ℚP.positive⁻¹ nu)

  embeddingScaleSquare : ℚ
  embeddingScaleSquare = Scale.unitSquare E

  embeddingScaleSquareNonnegative :
    0ℚ ≤ embeddingScaleSquare
  embeddingScaleSquareNonnegative =
    Scale.unitSquareNonnegative E

  modeFrequency : Physical.PhysicalTriadIncidence → ℚ
  modeFrequency tau =
    Scale.modeNatNormAsRational (Physical.p tau)
    + Scale.modeNatNormAsRational (Physical.q tau)

  physicalCellRate : Physical.PhysicalTriadIncidence → ℚ
  physicalCellRate tau =
    R94.physicalDecayRate physicalSystem (Physical.p tau)
    + R94.physicalDecayRate physicalSystem (Physical.q tau)

  cellRateNormalized :
    (tau : Physical.PhysicalTriadIncidence) →
    physicalCellRate tau
    ≡
    (nu * embeddingScaleSquare) * modeFrequency tau
  cellRateNormalized tau =
    let
      pScale =
        Scale.modeNormCommonSquareScale
          E I (Physical.p tau)
      qScale =
        Scale.modeNormCommonSquareScale
          E I (Physical.q tau)
      np = Scale.modeNatNormAsRational (Physical.p tau)
      nq = Scale.modeNatNormAsRational (Physical.q tau)
      c2 = embeddingScaleSquare
    in
    trans
      (cong₂ _+_
        (cong (nu *_) pScale)
        (cong (nu *_) qScale))
      (solve (nu ∷ c2 ∷ np ∷ nq ∷ []))

  latticeFrequencyGap :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence →
    ℚ
  latticeFrequencyGap alpha beta =
    modeFrequency alpha - modeFrequency beta

  physicalCellRateGap :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence →
    ℚ
  physicalCellRateGap alpha beta =
    physicalCellRate alpha - physicalCellRate beta

  cellRateGapNormalized :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    physicalCellRateGap alpha beta
    ≡
    (nu * embeddingScaleSquare)
      * latticeFrequencyGap alpha beta
  cellRateGapNormalized alpha beta =
    let
      a = modeFrequency alpha
      b = modeFrequency beta
      scale = nu * embeddingScaleSquare
    in
    trans
      (cong₂ _-_ (cellRateNormalized alpha) (cellRateNormalized beta))
      (solve (scale ∷ a ∷ b ∷ []))

  physicalScaleNonnegative :
    0ℚ ≤ nu * embeddingScaleSquare
  physicalScaleNonnegative =
    let
      instance
        nuNN = Data.Rational.Base.nonNegative nuNonnegative
        cNN = Data.Rational.Base.nonNegative embeddingScaleSquareNonnegative
    in
    ℚP.nonNegative⁻¹ (nu * embeddingScaleSquare)

  cellRateGapMagnitudeNormalized :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    ∣ physicalCellRateGap alpha beta ∣
    ≡
    (nu * embeddingScaleSquare)
      * ∣ latticeFrequencyGap alpha beta ∣
  cellRateGapMagnitudeNormalized alpha beta =
    let
      scale = nu * embeddingScaleSquare
      gap = latticeFrequencyGap alpha beta
    in
    trans
      (cong ∣_∣ (cellRateGapNormalized alpha beta))
      (trans
        (ℚP.∣p*q∣≡∣p∣*∣q∣ scale gap)
        (cong (_* ∣ gap ∣)
          (ℚP.0≤p⇒∣p∣≡p physicalScaleNonnegative)))

physicalRateGapSameObjectClosed : Bool
physicalRateGapSameObjectClosed = true

abstractRateDifferenceRequiredAfterNormalization : Bool
abstractRateDifferenceRequiredAfterNormalization = false

shellOrStateEstimateUsedHere : Bool
shellOrStateEstimateUsedHere = false

clayPromotion : Bool
clayPromotion = false

physicalRateGapSameObjectClosedIsTrue :
  physicalRateGapSameObjectClosed ≡ true
physicalRateGapSameObjectClosedIsTrue = refl

abstractRateDifferenceRequiredAfterNormalizationIsFalse :
  abstractRateDifferenceRequiredAfterNormalization ≡ false
abstractRateDifferenceRequiredAfterNormalizationIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
