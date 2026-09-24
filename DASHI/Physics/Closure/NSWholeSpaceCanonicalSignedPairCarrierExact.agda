module DASHI.Physics.Closure.NSWholeSpaceCanonicalSignedPairCarrierExact where

------------------------------------------------------------------------
-- A / CANONICAL SIGNED SAME-OUTPUT PAIR CARRIER
--
-- Use CanonicalPairSaturationData itself as the interaction carrier.
--
-- To respect the existing SignedFrequencyCarrier interface (whose split uses
-- propositional equality) define
--
--   common   := a^{-1} Gram
--   centered := [(a+s)^{-1} a^{-1} s] Gram
--   weighted := common - centered.
--
-- Then the signed split is definitionally refl.
--
-- Separately, in the Bishop-real setoid, prove the physical resolvent identity
--
--   common - centered ~= (a+s)^{-1} Gram.
--
-- This avoids converting Bishop setoid equality into Agda propositional
-- equality while retaining the literal physical pair-resolvent meaning.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Inverse as BishopInverse
import Real as BishopReal
import RealProperties as BishopP

import DASHI.Physics.Closure.NSTriadKNSignedFrequencyCarrierExact as Core
import DASHI.Physics.Closure.NSCanonicalEuclideanPeriodicSemanticCarriersExact as Canonical
import DASHI.Physics.Closure.NSTriadKNEuclideanPhysicalFourierNSExact as Physical
import DASHI.Physics.Closure.NSTriadKNEuclideanViscousHeatRateExact as Heat
import DASHI.Physics.Closure.NSWholeSpaceCanonicalPairSaturationOriginExact as Pair

commonFlux :
  ∀ {S trajectory fluid} →
  Pair.CanonicalPairSaturationData
    {S} (trajectory : Physical.EuclideanFourierTrajectory S) fluid →
  BishopReal.ℝ
commonFlux D =
  BishopReal._*_
    (Pair.outputResolvent D)
    (Pair.pairGram D)

centeredFlux :
  ∀ {S trajectory fluid} →
  Pair.CanonicalPairSaturationData
    {S} (trajectory : Physical.EuclideanFourierTrajectory S) fluid →
  BishopReal.ℝ
centeredFlux D =
  Pair.centeredCorrection D

weightedFlux :
  ∀ {S trajectory fluid} →
  Pair.CanonicalPairSaturationData
    {S} (trajectory : Physical.EuclideanFourierTrajectory S) fluid →
  BishopReal.ℝ
weightedFlux D =
  BishopReal._-_ (commonFlux D) (centeredFlux D)

pairResolventInverseLaw :
  ∀ {S trajectory fluid} →
  (D :
    Pair.CanonicalPairSaturationData
      {S} (trajectory : Physical.EuclideanFourierTrajectory S) fluid) →
  BishopReal._≃_
    (BishopReal._*_
      (Pair.pairResolvent D)
      (BishopReal._+_
        (Pair.heatRate D)
        (Pair.residual D)))
    BishopReal.1ℝ
pairResolventInverseLaw D =
  BishopInverse.*-inverseˡ
    (BishopReal._+_
      (Pair.heatRate D)
      (Pair.residual D))
    (Pair.heatPlusResidualNonzero D)

outputResolventInverseLaw :
  ∀ {S trajectory fluid} →
  (D :
    Pair.CanonicalPairSaturationData
      {S} (trajectory : Physical.EuclideanFourierTrajectory S) fluid) →
  BishopReal._≃_
    (BishopReal._*_
      (Pair.outputResolvent D)
      (Pair.heatRate D))
    BishopReal.1ℝ
outputResolventInverseLaw D =
  BishopInverse.*-inverseˡ
    (Pair.heatRate D)
    (Pair.heatNonzero D)

commonMinusCenteredCoefficientIsPairResolvent :
  ∀ {S trajectory fluid} →
  (D :
    Pair.CanonicalPairSaturationData
      {S} (trajectory : Physical.EuclideanFourierTrajectory S) fluid) →
  BishopReal._≃_
    (BishopReal._-_
      (Pair.outputResolvent D)
      (Pair.centeredCoefficient D))
    (Pair.pairResolvent D)
commonMinusCenteredCoefficientIsPairResolvent D =
  let
    o = Pair.outputResolvent D
    p = Pair.pairResolvent D
    a = Pair.heatRate D
    s = Pair.residual D

    pairLaw = pairResolventInverseLaw D
    outputLaw = outputResolventInverseLaw D

    expandOne :
      BishopReal._≃_
        (BishopReal._-_
          o
          (BishopReal._*_
            p
            (BishopReal._*_ o s)))
        (BishopReal._-_
          (BishopReal._*_
            o
            (BishopReal._*_
              p
              (BishopReal._+_ a s)))
          (BishopReal._*_
            p
            (BishopReal._*_ o s)))
    expandOne =
      BishopP.-cong
        (BishopP.≃-symm
          (BishopP.≃-trans
            (BishopP.*-congˡ pairLaw)
            (BishopP.*-identityʳ o)))
        BishopP.≃-refl

    cancelResidual :
      BishopReal._≃_
        (BishopReal._-_
          (BishopReal._*_
            o
            (BishopReal._*_
              p
              (BishopReal._+_ a s)))
          (BishopReal._*_
            p
            (BishopReal._*_ o s)))
        (BishopReal._*_
          p
          (BishopReal._*_ o a))
    cancelResidual =
      let open BishopP.ℝ-Solver
      in solve 4
        (λ o' p' a' s' →
          o' ⊗ (p' ⊗ (a' ⊕ s'))
          ⊖ p' ⊗ (o' ⊗ s')
          ⊜
          p' ⊗ (o' ⊗ a'))
        BishopP.≃-refl
        o p a s

    collapseOutput :
      BishopReal._≃_
        (BishopReal._*_
          p
          (BishopReal._*_ o a))
        p
    collapseOutput =
      BishopP.≃-trans
        (BishopP.*-congˡ outputLaw)
        (BishopP.*-identityʳ p)
  in
  BishopP.≃-trans
    expandOne
    (BishopP.≃-trans
      cancelResidual
      collapseOutput)

weightedFluxIsPairResolventGram :
  ∀ {S trajectory fluid} →
  (D :
    Pair.CanonicalPairSaturationData
      {S} (trajectory : Physical.EuclideanFourierTrajectory S) fluid) →
  BishopReal._≃_
    (weightedFlux D)
    (BishopReal._*_
      (Pair.pairResolvent D)
      (Pair.pairGram D))
weightedFluxIsPairResolventGram D =
  let
    o = Pair.outputResolvent D
    c = Pair.centeredCoefficient D
    g = Pair.pairGram D

    factor :
      BishopReal._≃_
        (BishopReal._-_
          (BishopReal._*_ o g)
          (BishopReal._*_ c g))
        (BishopReal._*_
          (BishopReal._-_ o c)
          g)
    factor =
      let open BishopP.ℝ-Solver
      in solve 3
        (λ o' c' g' →
          o' ⊗ g' ⊖ c' ⊗ g'
          ⊜
          (o' ⊖ c') ⊗ g')
        BishopP.≃-refl
        o c g
  in
  BishopP.≃-trans
    factor
    (BishopP.*-congʳ
      (commonMinusCenteredCoefficientIsPairResolvent D))

canonicalSignedPairCarrier :
  ∀ {S trajectory fluid} →
  Core.SignedFrequencyCarrier
canonicalSignedPairCarrier
    {S} {trajectory = trajectory} {fluid = fluid} = record
  { Core.Interaction =
      Pair.CanonicalPairSaturationData
        {S} trajectory fluid
  ; Core.Scalar = BishopReal.ℝ
  ; Core._minus_ = BishopReal._-_
  ; Core.weightedFlux = weightedFlux
  ; Core.commonResolventFlux = commonFlux
  ; Core.centeredResolventCorrection = centeredFlux
  ; Core.pointwiseCenteredResolventSplit =
      λ D → refl
  }

signedSplitDefinitional : Bool
signedSplitDefinitional = true

weightedFluxHasLiteralPairResolventMeaning : Bool
weightedFluxHasLiteralPairResolventMeaning = true

bishopSetoidEqualityCoercedToPropositionalEquality : Bool
bishopSetoidEqualityCoercedToPropositionalEquality = false

abstractResolventSplitAuthorityRequired : Bool
abstractResolventSplitAuthorityRequired = false

clayPromotion : Bool
clayPromotion = false

signedSplitDefinitionalIsTrue :
  signedSplitDefinitional ≡ true
signedSplitDefinitionalIsTrue = refl

weightedFluxHasLiteralPairResolventMeaningIsTrue :
  weightedFluxHasLiteralPairResolventMeaning ≡ true
weightedFluxHasLiteralPairResolventMeaningIsTrue = refl

bishopSetoidEqualityCoercedToPropositionalEqualityIsFalse :
  bishopSetoidEqualityCoercedToPropositionalEquality ≡ false
bishopSetoidEqualityCoercedToPropositionalEqualityIsFalse = refl

abstractResolventSplitAuthorityRequiredIsFalse :
  abstractResolventSplitAuthorityRequired ≡ false
abstractResolventSplitAuthorityRequiredIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
