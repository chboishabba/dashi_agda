module DASHI.Physics.Closure.NSTriadKNLiteralFixedOutputCovarianceM2PaymentExact where

------------------------------------------------------------------------
-- PERIODIC B / ENTIRE LITERAL FIXED-OUTPUT COVARIANCE -> PHYSICAL R571 M2
--
-- Previous owners prove:
--
--   * the exact fixed-output covariance is an unordered pair sum
--       sum_{alpha<beta} (C_alpha-C_beta)(W_alpha-W_beta);
--   * W_M(A) = 2 Re<M,A>;
--   * C_alpha-C_beta is c^2 times an INTEGER squared-norm defect;
--   * a nonzero integer defect has a canonical displacement d >= 1;
--   * such a pair constructs an R571 second-moment sample with
--       A1 = c^2, G2 = 2 G1;
--   * an equal integer defect makes the multiplier difference exactly zero.
--
-- This owner performs the actual finite recursion on the literal output fibre.
-- Every unordered pair is handled:
--
--   equal centered integer norm  -> exact zero contribution;
--   unequal centered integer norm -> physical R571 M2 payment.
--
-- The result is a cardinality-free upper bound for the ENTIRE signed centered
-- covariance by an explicit sum of local second-moment budgets.  No pair is
-- discarded and no Taylor-curvature/A2 term is charged.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (_++_)
open import Agda.Builtin.Nat using (Nat)
import Data.Empty as Empty
open import Data.Nat.Properties as NatP using (_≟_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedCommutatorDampedTangentExact as D1a
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredCovarianceFactorExact as Centered
import DASHI.Physics.Closure.NSTriadKNCoherentWorkHermitianScalarizationExact as Scalar
import DASHI.Physics.Closure.NSTriadKNR571HermitianScalarizedOppositePairExact as G0
import DASHI.Physics.Closure.NSTriadKNPhysicalCenteredCovarianceSecondMomentExact as PhysicalM2
import DASHI.Physics.Closure.NSTriadKNCenteredCovarianceToSecondMomentExact as CovM2
import DASHI.Physics.Closure.NSTriadKNCenteredSquareIntegerGapExact as Gap
import DASHI.Physics.Closure.NSTriadKNLuoFinitePairedCommutatorSecondMomentBoundExact as Moment
import DASHI.Physics.Closure.NSTriadKNLuoFiniteCenteredCommutatorBudgetExact as Sum
import DASHI.Physics.Closure.NSTriadKNRationalIntegerEmbeddingModeNormScaleExact as Scale
import DASHI.Physics.Closure.NSTriadKNR571HermitianStateAmplitudeEnvelopeExact as G1
import DASHI.Physics.Closure.NSTriadKNR571DiscreteG2FromG1Exact as G2

F : C3.RealField _
F = Rational.rationalRealField

two : ℚ
two = 1ℚ + 1ℚ

oneNN : 0ℚ ≤ 1ℚ
oneNN = ℚP.<⇒≤ (ℚP.positive⁻¹ 1ℚ)

twoNN : 0ℚ ≤ two
twoNN = ℚP.+-mono-≤ oneNN oneNN

module LiteralFixedOutputCovarianceM2
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (cutoff : Nat)
    (output : Z3.FourierMode) where

  items : List Physical.PhysicalTriadIncidence
  items = Output.physicalOutputFiber cutoff output

  value :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  value = D1a.mixedProductCell S velocity

  mixed : C3.Complex3 F
  mixed = R224.foldVector value items

  work : Physical.PhysicalTriadIncidence → ℚ
  work = Work.cellWork mixed value

  pairTerm :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  pairTerm alpha beta =
    PhysicalM2.centeredMultiplierDifference E alpha beta
      * (work alpha - work beta)

  nonzeroPairData :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    ( PhysicalM2.integerCenteredNorm alpha
      ≡ PhysicalM2.integerCenteredNorm beta → Empty.⊥) →
    PhysicalM2.NonzeroPhysicalCenteredCovariancePair
      E I alpha beta (value alpha) (value beta) mixed
  nonzeroPairData alpha beta unequal = record
    { PhysicalM2.weight = two
    ; PhysicalM2.weightNonnegative = twoNN
    ; PhysicalM2.centeredNormsUnequal = unequal
    }

  nonzeroPairSignedCovarianceIsLiteralTerm :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    (unequal :
      PhysicalM2.integerCenteredNorm alpha
      ≡ PhysicalM2.integerCenteredNorm beta → Empty.⊥) →
    CovM2.signedCovariancePair
      (PhysicalM2.physicalCovarianceSecondMomentPair
        (nonzeroPairData alpha beta unequal))
    ≡ pairTerm alpha beta
  nonzeroPairSignedCovarianceIsLiteralTerm alpha beta unequal =
    let
      multiplier =
        PhysicalM2.centeredMultiplierDifference E alpha beta
      gA = G0.hermitianScalar (value alpha) mixed
      gB = G0.hermitianScalar (value beta) mixed
    in
    rewrite
      Scalar.coherentWorkDifferenceIsTwoHermitianDifference
        mixed (value alpha) (value beta)
    =
      solve (multiplier ∷ gA ∷ gB ∷ [])

  nonzeroPairBound :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    (unequal :
      PhysicalM2.integerCenteredNorm alpha
      ≡ PhysicalM2.integerCenteredNorm beta → Empty.⊥) →
    pairTerm alpha beta
    ≤
    Moment.weightedSecondMoment
      (CovM2.covarianceSecondMomentSample
        (PhysicalM2.physicalCovarianceSecondMomentPair
          (nonzeroPairData alpha beta unequal)))
      *
      ( Scale.unitSquare E
        * (G2.two
          * G1.stateAmplitudeEnvelope
              (value alpha) (value beta) mixed))
  nonzeroPairBound alpha beta unequal =
    subst
      (_≤
        Moment.weightedSecondMoment
          (CovM2.covarianceSecondMomentSample
            (PhysicalM2.physicalCovarianceSecondMomentPair
              (nonzeroPairData alpha beta unequal)))
          *
          ( Scale.unitSquare E
            * (G2.two
              * G1.stateAmplitudeEnvelope
                  (value alpha) (value beta) mixed)))
      )
      (nonzeroPairSignedCovarianceIsLiteralTerm alpha beta unequal)
      (PhysicalM2.physicalSignedCovariancePairBelowM2
        (nonzeroPairData alpha beta unequal))

  nonzeroPairAbsoluteBound :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    (unequal :
      PhysicalM2.integerCenteredNorm alpha
      ≡ PhysicalM2.integerCenteredNorm beta → Empty.⊥) →
    ∣ pairTerm alpha beta ∣
    ≤
    Moment.weightedSecondMoment
      (CovM2.covarianceSecondMomentSample
        (PhysicalM2.physicalCovarianceSecondMomentPair
          (nonzeroPairData alpha beta unequal)))
      *
      ( Scale.unitSquare E
        * (G2.two
          * G1.stateAmplitudeEnvelope
              (value alpha) (value beta) mixed))
  nonzeroPairAbsoluteBound alpha beta unequal =
    let
      P = PhysicalM2.physicalCovarianceSecondMomentPair
        (nonzeroPairData alpha beta unequal)
      exact = nonzeroPairSignedCovarianceIsLiteralTerm alpha beta unequal
      magnitudeExact = CovM2.covarianceSampleMagnitudeMeaning P

      signedAbsToMagnitude :
        ∣ CovM2.signedCovariancePair P ∣
        ≡ Moment.pairedMagnitude (CovM2.covarianceSecondMomentSample P)
      signedAbsToMagnitude =
        let
          w = CovM2.weight P
          dm = CovM2.multiplierDifference P
          dw = CovM2.workDifference P
          wNN = CovM2.weightNonnegative P
          wAbs = ℚP.0≤p⇒∣p∣≡p wNN
          productAbs =
            ℚP.∣p*q∣≡∣p∣*∣q∣ dm dw
          outerAbs =
            ℚP.∣p*q∣≡∣p∣*∣q∣ w (dm * dw)
        in
        trans outerAbs
          (trans
            (cong (λ selected → selected * ∣ dm * dw ∣) wAbs)
            (trans
              (cong (w *_) productAbs)
              (sym magnitudeExact)))
    in
    subst
      (λ left →
        left
        ≤ Moment.weightedSecondMoment
            (CovM2.covarianceSecondMomentSample P)
            *
            ( Scale.unitSquare E
              * (G2.two
                * G1.stateAmplitudeEnvelope
                    (value alpha) (value beta) mixed)))
      (cong ∣_∣ exact)
      (CovM2.covarianceSampleFirstOrderBound P)

  covariancePaymentSample :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence →
    Moment.PairedSecondMomentSample
  covariancePaymentSample alpha beta
    with NatP._≟_
      (PhysicalM2.integerCenteredNorm alpha)
      (PhysicalM2.integerCenteredNorm beta)
  ... | yes equalNorms =
    Moment.paired-second-moment-sample
      0ℚ 0ℚ
      0ℚ 0ℚ
      0ℚ 0ℚ
      0ℚ 0ℚ
      ℚP.≤-refl ℚP.≤-refl
      ℚP.≤-refl ℚP.≤-refl
      ℚP.≤-refl ℚP.≤-refl
      ℚP.≤-refl ℚP.≤-refl
  ... | no unequal =
    let
      d = PhysicalM2.integerCenteredGap alpha beta
      envelope =
        G1.stateAmplitudeEnvelope
          (value alpha) (value beta) mixed
      stateCoefficient = G2.two * envelope
      stateCoefficientNN =
        Moment.productNonnegative
          G2.two envelope
          (ℚP.+-mono-≤ oneNN oneNN)
          (G1.stateAmplitudeEnvelopeNonnegative
            (value alpha) (value beta) mixed)
      scaledState = Scale.unitSquare E * stateCoefficient
      scaledStateNN =
        Moment.productNonnegative
          (Scale.unitSquare E) stateCoefficient
          (Scale.unitSquareNonnegative E)
          stateCoefficientNN
      paymentWeight = two * scaledState
      paymentWeightNN =
        Moment.productNonnegative
          two scaledState twoNN scaledStateNN
      dNN =
        Scale.natAsRationalNonnegative
          (Gap.natGap
            (PhysicalM2.integerCenteredNorm alpha)
            (PhysicalM2.integerCenteredNorm beta))
    in
    Moment.paired-second-moment-sample
      paymentWeight d
      0ℚ 0ℚ
      0ℚ 0ℚ
      0ℚ 0ℚ
      paymentWeightNN dNN
      ℚP.≤-refl ℚP.≤-refl
      ℚP.≤-refl ℚP.≤-refl
      ℚP.≤-refl ℚP.≤-refl

  pairBudget :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  pairBudget alpha beta
    with NatP._≟_
      (PhysicalM2.integerCenteredNorm alpha)
      (PhysicalM2.integerCenteredNorm beta)
  ... | yes equalNorms = 0ℚ
  ... | no unequal =
    Moment.weightedSecondMoment
      (CovM2.covarianceSecondMomentSample
        (PhysicalM2.physicalCovarianceSecondMomentPair
          (nonzeroPairData alpha beta unequal)))
      *
      ( Scale.unitSquare E
        * (G2.two
          * G1.stateAmplitudeEnvelope
              (value alpha) (value beta) mixed))

  covariancePaymentSampleM2Meaning :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    Moment.weightedSecondMoment
      (covariancePaymentSample alpha beta)
    ≡ pairBudget alpha beta
  covariancePaymentSampleM2Meaning alpha beta
    with NatP._≟_
      (PhysicalM2.integerCenteredNorm alpha)
      (PhysicalM2.integerCenteredNorm beta)
  ... | yes equalNorms = refl
  ... | no unequal =
    let
      d = PhysicalM2.integerCenteredGap alpha beta
      envelope =
        G1.stateAmplitudeEnvelope
          (value alpha) (value beta) mixed
      stateCoefficient = G2.two * envelope
      oldSample =
        PhysicalM2.physicalCovarianceSecondMomentPair
          (nonzeroPairData alpha beta unequal)
    in
    solve
      ( two
      ∷ Scale.unitSquare E
      ∷ stateCoefficient
      ∷ d
      ∷ [])

  literalPairTermBelowBudget :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    pairTerm alpha beta ≤ pairBudget alpha beta
  literalPairTermBelowBudget alpha beta
    with NatP._≟_
      (PhysicalM2.integerCenteredNorm alpha)
      (PhysicalM2.integerCenteredNorm beta)
  ... | yes equalNorms
    rewrite
      PhysicalM2.equalIntegerCenteredNormsGiveZeroMultiplier
        E I alpha beta equalNorms
    =
      ℚP.≤-refl
  ... | no unequal =
    nonzeroPairBound alpha beta unequal

  samplesAgainstHead :
    Physical.PhysicalTriadIncidence →
    List Physical.PhysicalTriadIncidence →
    List Moment.PairedSecondMomentSample
  samplesAgainstHead head [] = []
  samplesAgainstHead head (x ∷ xs) =
    covariancePaymentSample head x ∷ samplesAgainstHead head xs

  covarianceSamples :
    List Physical.PhysicalTriadIncidence →
    List Moment.PairedSecondMomentSample
  covarianceSamples [] = []
  covarianceSamples (head ∷ xs) =
    samplesAgainstHead head xs ++ covarianceSamples xs

  sampleM2AgainstHeadMeaning :
    (head : Physical.PhysicalTriadIncidence) →
    (xs : List Physical.PhysicalTriadIncidence) →
    Sum.sumBy (samplesAgainstHead head xs) Moment.weightedSecondMoment
    ≡ budgetAgainstHead head xs
  sampleM2AgainstHeadMeaning head [] = refl
  sampleM2AgainstHeadMeaning head (x ∷ xs)
    rewrite covariancePaymentSampleM2Meaning head x
          | sampleM2AgainstHeadMeaning head xs = refl

  budgetAgainstHead :
    Physical.PhysicalTriadIncidence →
    List Physical.PhysicalTriadIncidence → ℚ
  budgetAgainstHead head [] = 0ℚ
  budgetAgainstHead head (x ∷ xs) =
    pairBudget head x + budgetAgainstHead head xs

  totalM2Budget :
    List Physical.PhysicalTriadIncidence → ℚ
  totalM2Budget [] = 0ℚ
  totalM2Budget (head ∷ xs) =
    budgetAgainstHead head xs + totalM2Budget xs

  sumByAppend :
    (left right : List Moment.PairedSecondMomentSample) →
    Sum.sumBy (left ++ right) Moment.weightedSecondMoment
    ≡
    Sum.sumBy left Moment.weightedSecondMoment
      + Sum.sumBy right Moment.weightedSecondMoment
  sumByAppend [] right = refl
  sumByAppend (sample ∷ rest) right
    rewrite sumByAppend rest right = refl

  covarianceSamplesM2Meaning :
    (xs : List Physical.PhysicalTriadIncidence) →
    Sum.sumBy (covarianceSamples xs) Moment.weightedSecondMoment
    ≡ totalM2Budget xs
  covarianceSamplesM2Meaning [] = refl
  covarianceSamplesM2Meaning (head ∷ xs) =
    trans
      (sumByAppend
        (samplesAgainstHead head xs)
        (covarianceSamples xs))
      (trans
        (cong
          (_+ Sum.sumBy (covarianceSamples xs)
              Moment.weightedSecondMoment)
          (sampleM2AgainstHeadMeaning head xs))
        (cong
          (budgetAgainstHead head xs +_)
          (covarianceSamplesM2Meaning xs)))

  literalCovarianceSamplesM2Meaning :
    Sum.sumBy (covarianceSamples items) Moment.weightedSecondMoment
    ≡ totalM2Budget items
  literalCovarianceSamplesM2Meaning =
    covarianceSamplesM2Meaning items

  centeredAgainstHeadBelowM2 :
    (head : Physical.PhysicalTriadIncidence) →
    (xs : List Physical.PhysicalTriadIncidence) →
    Centered.centeredAgainstHead E work head xs
    ≤ budgetAgainstHead head xs
  centeredAgainstHeadBelowM2 head [] = ℚP.≤-refl
  centeredAgainstHeadBelowM2 head (x ∷ xs) =
    ℚP.+-mono-≤
      (literalPairTermBelowBudget head x)
      (centeredAgainstHeadBelowM2 head xs)

  centeredPairSumBelowM2 :
    (xs : List Physical.PhysicalTriadIncidence) →
    Centered.centeredPairDifferenceWorkSum E work xs
    ≤ totalM2Budget xs
  centeredPairSumBelowM2 [] = ℚP.≤-refl
  centeredPairSumBelowM2 (head ∷ xs) =
    ℚP.+-mono-≤
      (centeredAgainstHeadBelowM2 head xs)
      (centeredPairSumBelowM2 xs)

  absolutePairTermBelowBudget :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    ∣ pairTerm alpha beta ∣ ≤ pairBudget alpha beta
  absolutePairTermBelowBudget alpha beta
    with NatP._≟_
      (PhysicalM2.integerCenteredNorm alpha)
      (PhysicalM2.integerCenteredNorm beta)
  ... | yes equalNorms
    rewrite
      PhysicalM2.equalIntegerCenteredNormsGiveZeroMultiplier
        E I alpha beta equalNorms
    =
      ℚP.≤-refl
  ... | no unequal =
    nonzeroPairAbsoluteBound alpha beta unequal

  absoluteAgainstHead :
    Physical.PhysicalTriadIncidence →
    List Physical.PhysicalTriadIncidence → ℚ
  absoluteAgainstHead head [] = 0ℚ
  absoluteAgainstHead head (x ∷ xs) =
    ∣ pairTerm head x ∣ + absoluteAgainstHead head xs

  absolutePairSum :
    List Physical.PhysicalTriadIncidence → ℚ
  absolutePairSum [] = 0ℚ
  absolutePairSum (head ∷ xs) =
    absoluteAgainstHead head xs + absolutePairSum xs

  absoluteAgainstHeadBelowM2 :
    (head : Physical.PhysicalTriadIncidence) →
    (xs : List Physical.PhysicalTriadIncidence) →
    absoluteAgainstHead head xs ≤ budgetAgainstHead head xs
  absoluteAgainstHeadBelowM2 head [] = ℚP.≤-refl
  absoluteAgainstHeadBelowM2 head (x ∷ xs) =
    ℚP.+-mono-≤
      (absolutePairTermBelowBudget head x)
      (absoluteAgainstHeadBelowM2 head xs)

  absolutePairSumBelowM2 :
    (xs : List Physical.PhysicalTriadIncidence) →
    absolutePairSum xs ≤ totalM2Budget xs
  absolutePairSumBelowM2 [] = ℚP.≤-refl
  absolutePairSumBelowM2 (head ∷ xs) =
    ℚP.+-mono-≤
      (absoluteAgainstHeadBelowM2 head xs)
      (absolutePairSumBelowM2 xs)

  signedPairSumBelowAbsolutePairSum :
    (xs : List Physical.PhysicalTriadIncidence) →
    ∣ Centered.centeredPairDifferenceWorkSum E work xs ∣
    ≤ absolutePairSum xs
  signedPairSumBelowAbsolutePairSum [] = ℚP.≤-refl
  signedPairSumBelowAbsolutePairSum (head ∷ xs) =
    let
      triangle =
        ℚP.∣p+q∣≤∣p∣+∣q∣
          (Centered.centeredAgainstHead E work head xs)
          (Centered.centeredPairDifferenceWorkSum E work xs)
      headBound :
        ∣ Centered.centeredAgainstHead E work head xs ∣
        ≤ absoluteAgainstHead head xs
      headBound = signedAgainstHeadBelowAbsolute head xs
      tailBound = signedPairSumBelowAbsolutePairSum xs
    in
    ℚP.≤-trans triangle (ℚP.+-mono-≤ headBound tailBound)
    where
    signedAgainstHeadBelowAbsolute :
      (head : Physical.PhysicalTriadIncidence) →
      (rest : List Physical.PhysicalTriadIncidence) →
      ∣ Centered.centeredAgainstHead E work head rest ∣
      ≤ absoluteAgainstHead head rest
    signedAgainstHeadBelowAbsolute head [] = ℚP.≤-refl
    signedAgainstHeadBelowAbsolute head (x ∷ rest) =
      ℚP.≤-trans
        (ℚP.∣p+q∣≤∣p∣+∣q∣
          (pairTerm head x)
          (Centered.centeredAgainstHead E work head rest))
        (ℚP.+-mono-≤
          ℚP.≤-refl
          (signedAgainstHeadBelowAbsolute head rest))

  literalFixedOutputCenteredCovarianceAbsoluteBelowM2 :
    ∣ Centered.centeredPairDifferenceWorkSum E work items ∣
    ≤ totalM2Budget items
  literalFixedOutputCenteredCovarianceAbsoluteBelowM2 =
    ℚP.≤-trans
      (signedPairSumBelowAbsolutePairSum items)
      (absolutePairSumBelowM2 items)

  literalFixedOutputCenteredCovarianceBelowM2 :
    Centered.centeredPairDifferenceWorkSum E work items
    ≤ totalM2Budget items
  literalFixedOutputCenteredCovarianceBelowM2 =
    centeredPairSumBelowM2 items

literalFixedOutputCovarianceM2PaymentClosed : Bool
literalFixedOutputCovarianceM2PaymentClosed = true

literalFixedOutputCovarianceM2AddsCardinalityFactor : Bool
literalFixedOutputCovarianceM2AddsCardinalityFactor = false

literalFixedOutputCovarianceM2UsesTaylorCurvature : Bool
literalFixedOutputCovarianceM2UsesTaylorCurvature = false

clayPromotion : Bool
clayPromotion = false
