module DASHI.Physics.Closure.NSTriadKNPhysicalCenteredCovarianceSecondMomentExact where

------------------------------------------------------------------------
-- PERIODIC B / LITERAL CENTERED COVARIANCE PAIR -> R571 M2 SAMPLE
--
-- On the exact rational Fourier carrier, the centered-square multiplier has
-- the integer-scale form
--
--   C_E(alpha) - C_E(beta)
--     = c^2 (n_alpha - n_beta).
--
-- For a NONZERO integer defect choose
--
--   d  = |n_alpha - n_beta|_Q,
--   A1 = c^2.
--
-- Then d >= 1, so the discrete state-side theorem supplies
--
--   |g_+ - g_-| <= d * (2 G1)
--
-- with no Fourier differentiability.  The preceding centered-covariance M2
-- bridge therefore constructs an actual first-order R571 sample with
--
--   multiplierDifference = C_E(alpha)-C_E(beta),
--   workDifference       = Re<X_+,D>-Re<X_-,D>,
--   displacement         = d,
--   transportGradient    = c^2,
--   stateGradient        = 2 G1.
--
-- If the integer centered-square defect is zero, the physical multiplier
-- difference itself is exactly zero, so the signed covariance pair vanishes
-- before any absolute-value observer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteIntegerModeNorm as ModeNorm
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRationalIntegerEmbeddingModeNormScaleExact as Scale
import DASHI.Physics.Closure.NSTriadKNFixedOutputViscousRateDifferenceFactorizationExact as Rate
import DASHI.Physics.Closure.NSTriadKNCenteredSquareIntegerScaleExact as SquareScale
import DASHI.Physics.Closure.NSTriadKNCenteredSquareIntegerGapExact as Gap
import DASHI.Physics.Closure.NSTriadKNR571HermitianScalarizedOppositePairExact as G0
import DASHI.Physics.Closure.NSTriadKNR571HermitianStateAmplitudeEnvelopeExact as G1
import DASHI.Physics.Closure.NSTriadKNR571DiscreteG2FromG1Exact as G2
import DASHI.Physics.Closure.NSTriadKNLuoFinitePairedCommutatorSecondMomentBoundExact as Moment
import DASHI.Physics.Closure.NSTriadKNCenteredCovarianceToSecondMomentExact as CovM2

F : C3.RealField _
F = Rational.rationalRealField

integerCenteredNorm :
  Physical.PhysicalTriadIncidence → Nat
integerCenteredNorm tau =
  ModeNorm.modeNatNormSquared
    (SquareScale.differenceMode (Physical.p tau) (Physical.q tau))

integerCenteredGap :
  Physical.PhysicalTriadIncidence →
  Physical.PhysicalTriadIncidence → ℚ
integerCenteredGap alpha beta =
  Gap.natGapRational
    (integerCenteredNorm alpha)
    (integerCenteredNorm beta)

centeredMultiplierDifference :
  (E : C3.IntegerEmbedding F) →
  Physical.PhysicalTriadIncidence →
  Physical.PhysicalTriadIncidence → ℚ
centeredMultiplierDifference E alpha beta =
  Rate.centeredSquare E (Physical.p alpha) (Physical.q alpha)
  - Rate.centeredSquare E (Physical.p beta) (Physical.q beta)

centeredMultiplierAbsoluteExact :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (alpha beta : Physical.PhysicalTriadIncidence) →
  ∣ centeredMultiplierDifference E alpha beta ∣
  ≡ Scale.unitSquare E * integerCenteredGap alpha beta
centeredMultiplierAbsoluteExact E I alpha beta =
  let
    nA = integerCenteredNorm alpha
    nB = integerCenteredNorm beta

    scaled :
      centeredMultiplierDifference E alpha beta
      ≡ Scale.unitSquare E
          * (Scale.natAsRational nA - Scale.natAsRational nB)
    scaled =
      SquareScale.centeredSquareDifferenceIntegerScale
        E I
        (Physical.p alpha) (Physical.q alpha)
        (Physical.p beta) (Physical.q beta)

    productAbs :
      ∣ Scale.unitSquare E
          * (Scale.natAsRational nA - Scale.natAsRational nB) ∣
      ≡
      ∣ Scale.unitSquare E ∣
        * ∣ Scale.natAsRational nA - Scale.natAsRational nB ∣
    productAbs =
      ℚP.∣p*q∣≡∣p∣*∣q∣
        (Scale.unitSquare E)
        (Scale.natAsRational nA - Scale.natAsRational nB)

    unitAbs :
      ∣ Scale.unitSquare E ∣ ≡ Scale.unitSquare E
    unitAbs =
      ℚP.0≤p⇒∣p∣≡p (Scale.unitSquareNonnegative E)

    gapAbs :
      ∣ Scale.natAsRational nA - Scale.natAsRational nB ∣
      ≡ integerCenteredGap alpha beta
    gapAbs = Gap.natDifferenceAbsoluteIsGap nA nB
  in
  trans
    (cong ∣_∣ scaled)
    (trans productAbs (cong₂ _*_ unitAbs gapAbs))

record NonzeroPhysicalCenteredCovariancePair
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (alpha beta : Physical.PhysicalTriadIncidence)
    (XPlus XMinus D : C3.Complex3 F) : Set₁ where
  field
    weight : ℚ
    weightNonnegative : 0ℚ ≤ weight
    sameOutput : Physical.k alpha ≡ Physical.k beta
    centeredNormsUnequal :
      integerCenteredNorm alpha ≡ integerCenteredNorm beta → ⊥

open NonzeroPhysicalCenteredCovariancePair public

physicalCovarianceSecondMomentPair :
  ∀ {E I alpha beta XPlus XMinus D} →
  NonzeroPhysicalCenteredCovariancePair
    E I alpha beta XPlus XMinus D →
  CovM2.CenteredCovarianceSecondMomentPair
physicalCovarianceSecondMomentPair
    {E} {I} {alpha} {beta} {XPlus} {XMinus} {D} P =
  let
    d = integerCenteredGap alpha beta
    A1 = Scale.unitSquare E
    envelope = G1.stateAmplitudeEnvelope XPlus XMinus D
    G2value = G2.two * envelope

    dNN : 0ℚ ≤ d
    dNN =
      Scale.natAsRationalNonnegative
        (Gap.natGap
          (integerCenteredNorm alpha)
          (integerCenteredNorm beta))

    A1NN : 0ℚ ≤ A1
    A1NN = Scale.unitSquareNonnegative E

    oneNN : 0ℚ ≤ 1ℚ
    oneNN = ℚP.<⇒≤ (ℚP.positive⁻¹ 1ℚ)

    twoNN : 0ℚ ≤ G2.two
    twoNN = ℚP.+-mono-≤ oneNN oneNN

    envelopeNN : 0ℚ ≤ envelope
    envelopeNN = G1.stateAmplitudeEnvelopeNonnegative XPlus XMinus D

    G2NN : 0ℚ ≤ G2value
    G2NN = Moment.productNonnegative G2.two envelope twoNN envelopeNN

    dAtLeastOne : 1ℚ ≤ d
    dAtLeastOne =
      Gap.natGapRationalAtLeastOne
        (integerCenteredNorm alpha)
        (integerCenteredNorm beta)
        (centeredNormsUnequal P)

    multiplierExact :
      ∣ centeredMultiplierDifference E alpha beta ∣
      ≡ d * A1
    multiplierExact =
      trans
        (centeredMultiplierAbsoluteExact E I alpha beta)
        (solve (A1 ∷ d ∷ []))

    workBound :
      ∣ G0.hermitianScalar XPlus D - G0.hermitianScalar XMinus D ∣
      ≤ d * G2value
    workBound =
      G2.discreteHermitianG2
        XPlus XMinus D d dAtLeastOne
  in
  CovM2.centered-covariance-second-moment-pair
    (weight P)
    d
    (centeredMultiplierDifference E alpha beta)
    (G0.hermitianScalar XPlus D - G0.hermitianScalar XMinus D)
    A1
    G2value
    (weightNonnegative P)
    dNN
    A1NN
    G2NN
    (subst
      (∣ centeredMultiplierDifference E alpha beta ∣ ≤_)
      multiplierExact
      ℚP.≤-refl)
    workBound

physicalSignedCovariancePairBelowM2 :
  ∀ {E I alpha beta XPlus XMinus D} →
  (P : NonzeroPhysicalCenteredCovariancePair
    E I alpha beta XPlus XMinus D) →
  CovM2.signedCovariancePair
      (physicalCovarianceSecondMomentPair P)
  ≤
  Moment.weightedSecondMoment
      (CovM2.covarianceSecondMomentSample
        (physicalCovarianceSecondMomentPair P))
    *
    ( Scale.unitSquare E
      * (G2.two * G1.stateAmplitudeEnvelope XPlus XMinus D))
physicalSignedCovariancePairBelowM2 P =
  CovM2.signedCovariancePairBelowWeightedSecondMoment
    (physicalCovarianceSecondMomentPair P)

equalIntegerCenteredNormsGiveZeroMultiplier :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (alpha beta : Physical.PhysicalTriadIncidence) →
  integerCenteredNorm alpha ≡ integerCenteredNorm beta →
  centeredMultiplierDifference E alpha beta ≡ 0ℚ
equalIntegerCenteredNormsGiveZeroMultiplier E I alpha beta equalNorms =
  let
    nA = integerCenteredNorm alpha
    nB = integerCenteredNorm beta

    scaled =
      SquareScale.centeredSquareDifferenceIntegerScale
        E I
        (Physical.p alpha) (Physical.q alpha)
        (Physical.p beta) (Physical.q beta)

    natEqual :
      Scale.natAsRational nA ≡ Scale.natAsRational nB
    natEqual = cong Scale.natAsRational equalNorms
  in
  trans scaled
    (subst
      (λ right →
        Scale.unitSquare E
          * (Scale.natAsRational nA - right)
        ≡ 0ℚ)
      natEqual
      (solve (Scale.unitSquare E ∷ Scale.natAsRational nA ∷ [])))

equalIntegerCenteredNormsGiveZeroSignedPair :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (alpha beta : Physical.PhysicalTriadIncidence) →
  (weight workDifference : ℚ) →
  integerCenteredNorm alpha ≡ integerCenteredNorm beta →
  weight
    * (centeredMultiplierDifference E alpha beta * workDifference)
  ≡ 0ℚ
equalIntegerCenteredNormsGiveZeroSignedPair
    E I alpha beta weight workDifference equalNorms
  rewrite equalIntegerCenteredNormsGiveZeroMultiplier
    E I alpha beta equalNorms =
  solve (weight ∷ workDifference ∷ [])

physicalCenteredCovarianceNonzeroPairM2Closed : Bool
physicalCenteredCovarianceNonzeroPairM2Closed = true

physicalCenteredCovarianceZeroDefectVanishingClosed : Bool
physicalCenteredCovarianceZeroDefectVanishingClosed = true

physicalCenteredCovarianceRequiresFrequencyDifferentiability : Bool
physicalCenteredCovarianceRequiresFrequencyDifferentiability = false

clayPromotion : Bool
clayPromotion = false
