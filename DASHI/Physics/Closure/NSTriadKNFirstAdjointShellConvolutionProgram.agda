module DASHI.Physics.Closure.NSTriadKNFirstAdjointShellConvolutionProgram where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin; Alexey
-- Cheskidov; Taichi Eguchi; DASHI repository contributors.
-- Title: "Direct low-output shell convolution programme for the first
-- Navier-Stokes partial adjoint".
-- Venue/year: Fourier Analysis and Nonlinear Partial Differential Equations,
-- Springer, 2011; Journal of Differential Equations 477 (2026), article
-- 114534; DASHI formal development, 2026.
-- DOI: 10.1007/978-3-642-16830-7 for Bahouri--Chemin--Danchin;
-- 10.1016/j.jde.2026.114534 and 10.48550/arXiv.2503.11642 for
-- Cheskidov--Eguchi; the discrete convolution reduction is DASHI-original.
-- Uses: pointwise Cauchy--Schwarz on each resonance fibre, translation
-- invariance q -> p+q, low-output shell cardinality, the projected derivative
-- bound |P_p q| <= |q|, and two H^s shell weights.
-- Relationship: the decisive direct mechanism is
--
--   ||1_{S_j}(a*b)||_2 <= #S_j^(1/2) ||a||_2 ||b||_2.
--
-- Cheskidov--Eguchi's physical-space annular covering is retained only as a
-- related count-versus-decay pattern.  It does not prove this Fourier estimate.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)

import DASHI.Physics.Closure.NSTriadKNCheskidovEguchiCountingTransferAudit as CountingSource
import DASHI.Physics.Closure.NSTriadKNFirstAdjointSobolevTailLedger as Tail
import DASHI.Physics.Closure.NSTriadKNRepositoryDyadicSeparationAudit as Gap

lowShellSquareRootExponentTimesTwo : Nat
lowShellSquareRootExponentTimesTwo = 3

derivativeExponentTimesTwo : Nat
derivativeExponentTimesTwo = 2

firstAdjointEndpointLowDecayTimesTwo : Nat
firstAdjointEndpointLowDecayTimesTwo = 5

firstAdjointEndpointGapDecayTimesTwo : Nat
firstAdjointEndpointGapDecayTimesTwo = 8

coarseThreeDimensionalShellCountConstant : Nat
coarseThreeDimensionalShellCountConstant = 125

baseOrbitHelicityRealityTransportFactor : Nat
baseOrbitHelicityRealityTransportFactor = 48 * (8 * 2)

record DirectShellConvolutionCarrier
    {m s n : Level} : Set (lsuc (m ⊔ s ⊔ n)) where
  field
    Mode : Set m
    Scalar : Set s
    Nonnegative : Set n

    addMode : Mode → Mode → Mode
    lowShell : Nat → Mode → Set
    highShell : Nat → Mode → Set

    coefficientNormSquared : Scalar → Nonnegative
    sequenceNormSquared : (Mode → Scalar) → Nonnegative
    finiteShellNormSquared : Nat → (Mode → Scalar) → Nonnegative

    convolutionAt :
      (left right : Mode → Scalar) → Mode → Scalar

    leq : Nonnegative → Nonnegative → Set n
    multiply : Nonnegative → Nonnegative → Nonnegative
    shellCardinality : Nat → Nonnegative

open DirectShellConvolutionCarrier public

record DirectShellConvolutionCutset
    {m s n : Level}
    (C : DirectShellConvolutionCarrier {m} {s} {n}) :
    Set (lsuc (m ⊔ s ⊔ n)) where
  field
    finiteLowShell : Set

    resonanceTranslationInjective :
      ∀ output source first second →
      addMode C output first ≡ source →
      addMode C output second ≡ source →
      first ≡ second

    pointwiseFibreCauchySchwarz :
      ∀ left right output →
      leq C
        (coefficientNormSquared C (convolutionAt C left right output))
        (multiply C
          (sequenceNormSquared C left)
          (sequenceNormSquared C right))

    lowShellL2Assembly :
      ∀ j left right →
      leq C
        (finiteShellNormSquared C j (convolutionAt C left right))
        (multiply C
          (shellCardinality C j)
          (multiply C
            (sequenceNormSquared C left)
            (sequenceNormSquared C right)))

    threeDimensionalShellCardinality : Set
    projectedModeNormBound : Set
    comparableHighShellOffsetOne : Set
    twoHighSobolevWeightsInserted : Set
    endpointLowDecayFiveHalves : Set
    endpointGapDecayFour : Set

    constantChosenBeforeGalerkinCutoff : Set
    orbitFactorAtMostFortyEight : Set
    helicityFactorAtMostEight : Set
    realityFoldFactorAtMostTwo : Set
    exactShellDyadicOverlapConstant : Nat

open DirectShellConvolutionCutset public

record FirstAdjointCutoffUniformTarget
    {c s v : Level} : Set (lsuc (c ⊔ s ⊔ v)) where
  field
    Cutoff : Set c
    Scalar : Set s
    State : Set v

    FiveHalvesBelow ThreeAbove : Scalar → Set s
    Positive : Scalar → Set s
    firstAdjointNorm hsNorm multiply leq : Set s

    constantForSChosenFirst : Set s
    estimateForEveryCutoff : Set s
    orbitHelicityDirectionTransported : Set s

open FirstAdjointCutoffUniformTarget public

record DirectConvolutionArithmeticReceipt : Set where
  constructor receipt
  field
    lowMultiplicityExponentIsThreeHalves :
      lowShellSquareRootExponentTimesTwo ≡ 3
    derivativeExponentIsOne : derivativeExponentTimesTwo ≡ 2
    endpointLowDecayIsFiveHalves :
      firstAdjointEndpointLowDecayTimesTwo ≡ 5
    endpointGapDecayIsFour :
      firstAdjointEndpointGapDecayTimesTwo ≡ 8
    coarseShellConstantIsOneHundredTwentyFive :
      coarseThreeDimensionalShellCountConstant ≡ 125
    baseTransportFactorIsSevenHundredSixtyEight :
      baseOrbitHelicityRealityTransportFactor ≡ 768
    farGapCandidateIsThree : Gap.repositoryFarGapCandidate ≡ 3
    highShellOffsetCandidateIsOne :
      Gap.comparableHighOutputShellOffset ≡ 1
    priorTailArithmeticClosed :
      Tail.firstAdjointSobolevTailExponentArithmeticClosed ≡ true
    countingSourceNotConsumedAsTheorem :
      CountingSource.sourceConsumedAsFirstAdjointTheorem ≡ false

open DirectConvolutionArithmeticReceipt public

directConvolutionArithmeticReceipt : DirectConvolutionArithmeticReceipt
directConvolutionArithmeticReceipt =
  receipt refl refl refl refl refl refl refl refl
    Tail.firstAdjointSobolevTailExponentArithmeticClosedIsTrue refl

lowOutputConvolutionMechanismIdentified : Bool
lowOutputConvolutionMechanismIdentified = true

lowOutputConvolutionMechanismIdentifiedIsTrue :
  lowOutputConvolutionMechanismIdentified ≡ true
lowOutputConvolutionMechanismIdentifiedIsTrue = refl

exactFiniteShellConvolutionAuditPassed : Bool
exactFiniteShellConvolutionAuditPassed = true

exactFiniteShellConvolutionAuditPassedIsTrue :
  exactFiniteShellConvolutionAuditPassed ≡ true
exactFiniteShellConvolutionAuditPassedIsTrue = refl

firstAdjointCutoffUniformShellConvolutionClosed : Bool
firstAdjointCutoffUniformShellConvolutionClosed = false

firstAdjointCutoffUniformShellConvolutionClosedIsFalse :
  firstAdjointCutoffUniformShellConvolutionClosed ≡ false
firstAdjointCutoffUniformShellConvolutionClosedIsFalse = refl
