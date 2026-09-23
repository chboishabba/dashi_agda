{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNOrbitResolvedSignedOverlapRound621Exact where

------------------------------------------------------------------------
-- ROUND621 / TOTAL ORBIT-RESOLVED SELF/EXTERNAL SPLIT ON R584 SIGNED OVERLAP
--
-- R613 proves, on the unrestricted R573 carrier,
--
--   Nested(tau) = Self(tau) + External(tau).
--
-- R619/R620 replace the historical nonfixed-only R112 external carrier by a
-- total fixed/nonfixed orbit-resolved carrier, preserving the exact fixed-orbit
-- multiplicity correction.
--
-- This module pushes that total representation through R584's ACTUAL signed
-- Hermitian overlap before any norm:
--
--   <Nested_L,Nested_R>
--     = <Self_L,Self_R>
--       + <Self_L,External_R>
--       + <External_L,Self_R>
--       + <External_L,External_R>.
--
-- No absolute value, Young/Cauchy bound, shell estimate, or spacetime payment
-- is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNR573SelfExternalNestedCompanionSplitRound613Exact as R613
import DASHI.Physics.Closure.NSTriadKNR573OrbitResolvedExternalNestedRound620Exact as R620
import DASHI.Physics.Closure.NSTriadKNExternalWaleffeOrbitResolvedRound619Exact as R619
import DASHI.Physics.Closure.NSTriadKNUnrestrictedNestedSignedOverlapRound584Exact as R584

F : C3.RealField _
F = Rational.rationalRealField

module OrbitResolvedSignedOverlap621
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (O : Leray.RationalInverseNormOrder E I)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (H : R142.HelicalHalfCalibration S)
    (W : R294.SwapInvariantCellWeight F)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode)) where

  module Split =
    R613.NestedNetworkSplit W S L H system velocityTransverse

  module External =
    R620.OrbitResolvedExternalNested W S L H system velocityTransverse

  module Signed =
    R584.UnrestrictedNested584
      E I O system S L H W velocityTransverse

  selfCell :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  selfCell = Split.selfNestedWeightedCompanionCell

  externalCell :
    (tau : Physical.PhysicalTriadIncidence) →
    R619.ThreeLegOrbitResolvedSelection system tau →
    C3.Complex3 F
  externalCell = External.externalResolvedNestedWeightedCompanionCell

  literalNestedCellSplitsOrbitResolved :
    (tau : Physical.PhysicalTriadIncidence) →
    (orbit : R619.ThreeLegOrbitResolvedSelection system tau) →
    Signed.literalNestedCell584 tau
    ≡ C3.complex3Add (selfCell tau) (externalCell tau orbit)
  literalNestedCellSplitsOrbitResolved tau orbit =
    trans
      (Split.nestedWeightedCompanionSplitsSelfExternal tau)
      (cong
        (C3.complex3Add (selfCell tau))
        (External.externalNestedWeightedCompanionIsOrbitResolved tau orbit))

  selfSelfOverlap :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence →
    Rational.ℚ
  selfSelfOverlap left right =
    R179.realHermitianCross (selfCell left) (selfCell right)

  selfExternalOverlap :
    (left right : Physical.PhysicalTriadIncidence) →
    R619.ThreeLegOrbitResolvedSelection system right →
    Rational.ℚ
  selfExternalOverlap left right rightOrbit =
    R179.realHermitianCross (selfCell left) (externalCell right rightOrbit)

  externalSelfOverlap :
    (left right : Physical.PhysicalTriadIncidence) →
    R619.ThreeLegOrbitResolvedSelection system left →
    Rational.ℚ
  externalSelfOverlap left right leftOrbit =
    R179.realHermitianCross (externalCell left leftOrbit) (selfCell right)

  externalExternalOverlap :
    (left right : Physical.PhysicalTriadIncidence) →
    R619.ThreeLegOrbitResolvedSelection system left →
    R619.ThreeLegOrbitResolvedSelection system right →
    Rational.ℚ
  externalExternalOverlap left right leftOrbit rightOrbit =
    R179.realHermitianCross
      (externalCell left leftOrbit)
      (externalCell right rightOrbit)

  signedOverlapSplitsFourOrbitResolvedChannels :
    (left right : Physical.PhysicalTriadIncidence) →
    (leftOrbit : R619.ThreeLegOrbitResolvedSelection system left) →
    (rightOrbit : R619.ThreeLegOrbitResolvedSelection system right) →
    Signed.signedOverlap584 left right
    ≡
      (selfSelfOverlap left right
        + selfExternalOverlap left right rightOrbit)
      +
      (externalSelfOverlap left right leftOrbit
        + externalExternalOverlap left right leftOrbit rightOrbit)
  signedOverlapSplitsFourOrbitResolvedChannels
      left right leftOrbit rightOrbit =
    let
      leftSplit =
        literalNestedCellSplitsOrbitResolved left leftOrbit
      rightSplit =
        literalNestedCellSplitsOrbitResolved right rightOrbit

      expose :
        Signed.signedOverlap584 left right
        ≡
        R179.realHermitianCross
          (C3.complex3Add
            (selfCell left) (externalCell left leftOrbit))
          (C3.complex3Add
            (selfCell right) (externalCell right rightOrbit))
      expose =
        trans
          (cong
            (λ value →
              R179.realHermitianCross
                value
                (Signed.literalNestedCell584 right))
            leftSplit)
          (cong
            (R179.realHermitianCross
              (C3.complex3Add
                (selfCell left) (externalCell left leftOrbit)))
            rightSplit)

      expandLeft =
        R291.realCrossAddLeft
          (selfCell left)
          (externalCell left leftOrbit)
          (C3.complex3Add
            (selfCell right) (externalCell right rightOrbit))

      expandRight =
        cong₂ _+_
          (R291.realCrossAddRight
            (selfCell left)
            (selfCell right)
            (externalCell right rightOrbit))
          (R291.realCrossAddRight
            (externalCell left leftOrbit)
            (selfCell right)
            (externalCell right rightOrbit))
    in
    trans expose (trans expandLeft expandRight)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round621R584SignedOverlapOrbitResolvedSplitClosed : Bool
round621R584SignedOverlapOrbitResolvedSplitClosed = true

round621FixedOrbitMultiplicityCorrectionReachesSignedConsumer : Bool
round621FixedOrbitMultiplicityCorrectionReachesSignedConsumer = true

round621LegacyGlobalR112WitnessFamilyRequired : Bool
round621LegacyGlobalR112WitnessFamilyRequired = false

round621IntroducesNormOrAbsoluteValue : Bool
round621IntroducesNormOrAbsoluteValue = false

round621IntroducesEstimate : Bool
round621IntroducesEstimate = false

round621ExternalAnalyticPaymentClosed : Bool
round621ExternalAnalyticPaymentClosed = false

round621R584SignedOverlapOrbitResolvedSplitClosedIsTrue :
  round621R584SignedOverlapOrbitResolvedSplitClosed ≡ true
round621R584SignedOverlapOrbitResolvedSplitClosedIsTrue = refl

round621FixedOrbitMultiplicityCorrectionReachesSignedConsumerIsTrue :
  round621FixedOrbitMultiplicityCorrectionReachesSignedConsumer ≡ true
round621FixedOrbitMultiplicityCorrectionReachesSignedConsumerIsTrue = refl

round621LegacyGlobalR112WitnessFamilyRequiredIsFalse :
  round621LegacyGlobalR112WitnessFamilyRequired ≡ false
round621LegacyGlobalR112WitnessFamilyRequiredIsFalse = refl

round621IntroducesNormOrAbsoluteValueIsFalse :
  round621IntroducesNormOrAbsoluteValue ≡ false
round621IntroducesNormOrAbsoluteValueIsFalse = refl

round621IntroducesEstimateIsFalse :
  round621IntroducesEstimate ≡ false
round621IntroducesEstimateIsFalse = refl

round621ExternalAnalyticPaymentClosedIsFalse :
  round621ExternalAnalyticPaymentClosed ≡ false
round621ExternalAnalyticPaymentClosedIsFalse = refl
