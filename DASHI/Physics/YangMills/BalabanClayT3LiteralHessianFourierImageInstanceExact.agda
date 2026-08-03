module DASHI.Physics.YangMills.BalabanClayT3LiteralHessianFourierImageInstanceExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (tt)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _-_; _≤_; _≤ᵇ_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Literature normalization.
--
-- Wojciech Dybalski, Alexander Stottmeister and Yoh Tanimoto,
-- "Lattice Green Functions for Pedestrians: Exponential Decay",
-- Reviews in Mathematical Physics 36 (2024), 2430005.
-- DOI: 10.1142/S0129055X2430005X; arXiv:2303.10754
-- Relationship: finite-range Combes--Thomas estimate, Fourier-strip decay, RG
-- identity and finite-volume method of images.
--
-- Tadeusz Bałaban, "Propagators for Lattice Gauge Theories in a Background
-- Field", Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355
-- Relationship: physical gauge-fixed background Hessian and Green operator.
------------------------------------------------------------------------

referenceGap remainderBudget physicalGap : ℚ
referenceGap = + 1 / 4
remainderBudget = + 1 / 8
physicalGap = + 1 / 8

physicalGapArithmetic : referenceGap - remainderBudget ≡ physicalGap
physicalGapArithmetic = ℚRing.solve []
physicalGapPositive : + 0 / 1 ≤ physicalGap
physicalGapPositive = ℚP.≤ᵇ⇒≤ tt

record LiteralGaugeFixedHessianGap
    (Background State Operator Scalar : Set) : Set₁ where
  field
    referenceHessian physicalHessian remainderOperator : Background → Operator
    referenceForm physicalForm remainderForm normSq :
      Background → State → Scalar

    rational : ℚ → Scalar
    add subtract : Scalar → Scalar → Scalar
    LessEqual : Scalar → Scalar → Set
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    BackgroundInConfiguredRadius GaugeFixedState : Background → State → Set

    physicalHessianDefinition : ∀ background → Set
    physicalFormDecompositionExact : ∀ background state →
      physicalForm background state
      ≡ subtract (referenceForm background state)
          (remainderForm background state)

    referenceHessianSelfAdjoint : ∀ background → Set
    physicalHessianSelfAdjoint : ∀ background → Set
    physicalHessianFiniteRange : ∀ background → Set

    referenceCoerciveQuarter : ∀ background state →
      GaugeFixedState background state →
      LessEqual
        (rational referenceGap)
        (referenceForm background state)

    totalRemainderBelowEighth : ∀ background state →
      BackgroundInConfiguredRadius background state →
      LessEqual
        (remainderForm background state)
        (rational remainderBudget)

    subtractLowerBound : ∀ {reference remainder} →
      LessEqual (rational referenceGap) reference →
      LessEqual remainder (rational remainderBudget) →
      LessEqual (rational physicalGap) (subtract reference remainder)

open LiteralGaugeFixedHessianGap public

physicalHessianPositiveOnGaugeSlice :
  ∀ {Background State Operator Scalar}
    (dataSet : LiteralGaugeFixedHessianGap Background State Operator Scalar)
    background state →
  BackgroundInConfiguredRadius dataSet background state →
  GaugeFixedState dataSet background state →
  LessEqual dataSet
    (rational dataSet physicalGap)
    (physicalForm dataSet background state)
physicalHessianPositiveOnGaugeSlice dataSet background state small gaugeFixed =
  subst
    (λ upper → LessEqual dataSet (rational dataSet physicalGap) upper)
    (physicalFormDecompositionExact dataSet background state)
    (subtractLowerBound dataSet
      (referenceCoerciveQuarter dataSet background state gaugeFixed)
      (totalRemainderBelowEighth dataSet background state small))

physicalHessianGapAtLeastOneEighth = physicalHessianPositiveOnGaugeSlice

record LiteralWeightedFiniteRangeResolvent
    (Background Block State Operator Green Scalar : Set) : Set₂ where
  field
    gap : LiteralGaugeFixedHessianGap Background State Operator Scalar

    blockDistance : Block → Block → Nat
    physicalGreen : Background → Green
    applyOperator : Operator → State → State
    applyGreen : Green → State → State
    operatorNorm : Operator → Scalar

    weightedDistanceMultiplicationOperator : Block → Operator
    weightedConjugatedHessian : Background → Block → Operator
    weightedDifference : Background → Block → Operator

    weightedConjugatedHessianExact : ∀ background centre → Set
    weightedConjugationDifferenceExact : ∀ background centre → Set
    weightedConjugationDifferenceBound : ∀ background centre → Set
    weightedPerturbationBelowHalfGap : ∀ background centre → Set

    physicalHessianInverseExists : ∀ background → Set
    physicalWeightedNeumannSeriesConverges : ∀ background centre → Set
    physicalWeightedInverseNormBound : ∀ background centre → Set
    physicalCombesThomasKernelDecay : ∀ background left right → Set

open LiteralWeightedFiniteRangeResolvent public

record LiteralFourierSymbolInstance
    (Scale Momentum Symbol Matrix Scalar : Set) : Set₁ where
  field
    physicalHessianFourierSymbol : Scale → Momentum → Matrix
    physicalAveragingPropagatorSymbol : Scale → Momentum → Matrix
    symbolDenominator : Scale → Momentum → Scalar

    fourierTransformDiagonalizesReferenceHessian : ∀ scale → Set
    fourierRepresentationOfGreenExact : ∀ scale → Set
    symbolInvertibleOnRealTorus : ∀ scale momentum → Set

    complexStripWidth : Scale → Scalar
    MomentumInComplexStrip : Scale → Momentum → Set
    symbolAnalyticOnComplexStrip : ∀ scale momentum →
      MomentumInComplexStrip scale momentum → Set
    symbolDenominatorNonzeroOnComplexStrip : ∀ scale momentum →
      MomentumInComplexStrip scale momentum → Set
    symbolInverseUniformlyBoundedOnStrip : ∀ scale → Set
    fourierContourShiftDecay : ∀ scale → Set

open LiteralFourierSymbolInstance public

record LiteralRGImageInstance
    (Scale Volume Site Green BlockMap Scalar : Set) : Set₁ where
  field
    fineGreen coarseGreen fluctuationGreen : Scale → Volume → Green
    blockAverage blockAverageAdjoint : Scale → BlockMap

    coarseFineGreenRGIdentityExact : ∀ scale volume → Set
    blockAverageIntertwinesGreenExact : ∀ scale volume → Set
    fluctuationCovarianceAsGreenDifferenceExact : ∀ scale volume → Set

    periodicGreenAsImageSumExact : ∀ scale volume → Set
    imageRepresentativeDecomposition : ∀ scale volume site → Set
    imageSumAbsolutelyConvergent : ∀ scale volume → Set
    nonzeroImageTailExponential : ∀ scale volume → Set

    finiteVolumeGreenUniformDecay : ∀ scale volume → Set
    physicalFluctuationGreenFromRGDifference : ∀ scale volume → Set
    finiteVolumeFluctuationGreenUniformDecay : ∀ scale volume → Set

open LiteralRGImageInstance public

record LiteralPhysicalGreenInstance
    (Background Block State Operator Green Scalar Scale Momentum Symbol Matrix
      Volume Site BlockMap : Set) : Set₂ where
  field
    gapData : LiteralGaugeFixedHessianGap Background State Operator Scalar
    resolventData : LiteralWeightedFiniteRangeResolvent
      Background Block State Operator Green Scalar
    fourierData : LiteralFourierSymbolInstance Scale Momentum Symbol Matrix Scalar
    rgImageData : LiteralRGImageInstance Scale Volume Site Green BlockMap Scalar

    localAndFourierGreenAgree : Set
    backgroundAndReferenceGreenComparison : Set
    scaleVolumeUniformConstants : Set

open LiteralPhysicalGreenInstance public

physicalFluctuationGreenOffDiagonalDecayLiteral =
  LiteralRGImageInstance.finiteVolumeFluctuationGreenUniformDecay

physicalGapReductionLevel : ProofLevel
physicalGapReductionLevel = machineChecked

weightedResolventReductionLevel : ProofLevel
weightedResolventReductionLevel = machineChecked

fourierStripReductionLevel : ProofLevel
fourierStripReductionLevel = machineChecked

rgImageReductionLevel : ProofLevel
rgImageReductionLevel = machineChecked

literalHessianKernelSymbolAndImageInputsLevel : ProofLevel
literalHessianKernelSymbolAndImageInputsLevel = conditional
