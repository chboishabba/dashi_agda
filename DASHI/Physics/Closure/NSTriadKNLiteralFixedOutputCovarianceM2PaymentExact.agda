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
open import Agda.Builtin.Nat using (Nat)
import Data.Empty as Empty
open import Data.Nat.Properties as NatP using (_≟_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
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
import DASHI.Physics.Closure.NSTriadKNLuoFinitePairedCommutatorSecondMomentBoundExact as Moment
import DASHI.Physics.Closure.NSTriadKNRationalIntegerEmbeddingModeNormScaleExact as Scale
import DASHI.Physics.Closure.NSTriadKNR571HermitianStateAmplitudeEnvelopeExact as G1
import DASHI.Physics.Closure.NSTriadKNR571DiscreteG2FromG1Exact as G2

F : C3.RealField _
F = Rational.rationalRealField

two : ℚ
two = 1ℚ + 1ℚ

twoNN : 0ℚ ≤ two
twoNN = ℚP.+-mono-≤ ℚP.≤-refl ℚP.≤-refl

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

      workDifference :
        work alpha - work beta
        ≡ two * (gA - gB)
      workDifference =
        Scalar.coherentWorkDifferenceIsTwoHermitianDifference
          mixed (value alpha) (value beta)
    in
    trans
      (solve (multiplier ∷ gA ∷ gB ∷ []))
      (sym (cong (multiplier *_) workDifference))

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

  literalPairTermBelowBudget :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    pairTerm alpha beta ≤ pairBudget alpha beta
  literalPairTermBelowBudget alpha beta
    with NatP._≟_
      (PhysicalM2.integerCenteredNorm alpha)
      (PhysicalM2.integerCenteredNorm beta)
  ... | yes equalNorms =
    subst
      (_≤ 0ℚ)
      (sym
        (trans
          (cong
            (λ multiplier →
              multiplier * (work alpha - work beta))
            (PhysicalM2.equalIntegerCenteredNormsGiveZeroMultiplier
              E I alpha beta equalNorms))
          (solve (work alpha ∷ work beta ∷ []))))
      ℚP.≤-refl
  ... | no unequal =
    nonzeroPairBound alpha beta unequal

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
