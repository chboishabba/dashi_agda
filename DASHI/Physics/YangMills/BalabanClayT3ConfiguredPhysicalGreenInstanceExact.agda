module DASHI.Physics.YangMills.BalabanClayT3ConfiguredPhysicalGreenInstanceExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (tt)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _*_; _≤_; _≤ᵇ_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT3PhysicalGreenCombesThomasExact as Green

------------------------------------------------------------------------
-- Literature normalization.
--
-- Wojciech Dybalski, Alexander Stottmeister and Yoh Tanimoto,
-- "Lattice Green Functions for Pedestrians: Exponential Decay",
-- Reviews in Mathematical Physics 36 (2024), article 2430005.
-- DOI: 10.1142/S0129055X2430005X; arXiv:2303.10754
-- Relationship: Theorem A / Theorem 2.25; local Combes--Thomas decay,
-- Fourier-strip analyticity, RG identity and method of images.
--
-- Jean-Michel Combes and Lawrence Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473
-- Relationship: weighted-conjugation resolvent estimate.
--
-- The rational parameters below are deliberately conservative DASHI choices.
------------------------------------------------------------------------

configuredGreenGap configuredHopping configuredDecay : ℚ
configuredGreenGap = + 1 / 8
configuredHopping = + 1 / 64
configuredDecay = + 1 / 64

configuredExpIncrementUpper configuredHalfGap : ℚ
configuredExpIncrementUpper = + 1 / 32
configuredHalfGap = + 1 / 16

configuredWeightedPerturbationUpper : ℚ
configuredWeightedPerturbationUpper =
  configuredHopping * configuredExpIncrementUpper

configuredWeightedPerturbationBelowHalfGap :
  configuredWeightedPerturbationUpper ≤ configuredHalfGap
configuredWeightedPerturbationBelowHalfGap = ℚP.≤ᵇ⇒≤ tt

configuredGapTwiceHalfExact :
  configuredHalfGap + configuredHalfGap ≡ configuredGreenGap
configuredGapTwiceHalfExact = ℚRing.solve []
record ConfiguredGreenScalarAuthority (Scalar : Set) : Set₁ where
  field
    rational : ℚ → Scalar
    zero one : Scalar
    add multiply subtract exponential : Scalar → Scalar → Scalar
    LessEqual StrictLess : Scalar → Scalar → Set

    rationalOrderEmbedding : ∀ {left right} →
      left ≤ right → LessEqual (rational left) (rational right)

    configuredDecayPositive :
      StrictLess zero (rational configuredDecay)

    expDecayRangeIncrementBound :
      LessEqual
        (subtract
          (exponential (rational configuredDecay) one)
          one)
        (rational configuredExpIncrementUpper)

open ConfiguredGreenScalarAuthority public

record ConfiguredLocalPhysicalHessian
    (Block State Scalar Operator GreenOperator : Set) : Set₂ where
  field
    scalar : ConfiguredGreenScalarAuthority Scalar

    blockDistance : Block → Block → Nat
    operator : Operator
    green : GreenOperator

    supportedInBlock : State → Block → Set
    norm2 pairing : State → State → Scalar
    applyGreen : GreenOperator → State → State
    natScalar : Nat → Scalar

    finiteRangeOperator : Set
    interactionRangeOne : Set

    gaugeFixedSpectralGap : Set
    spectralGapEqualsConfigured : Set
    inverseOnGaugeFixedSpace : Set

    weightedConjugationDifferenceExact : ∀ centre → Set
    weightedConjugationDifferenceBelowHoppingIncrement : ∀ centre → Set

    weightedPerturbationBound : ∀ centre → Set
    perturbationBelowHalfGap : Set
    weightedNeumannResolventConverges : ∀ centre → Set
    weightedInverseNormBound : ∀ centre → Set

    configuredL2Prefactor : Scalar
    localBlockL2Decay : ∀ left right leftState rightState →
      supportedInBlock leftState left →
      supportedInBlock rightState right →
      LessEqual scalar
        (pairing rightState (applyGreen green leftState))
        (multiply scalar configuredL2Prefactor
          (multiply scalar
            (exponential scalar
              (subtract scalar (zero scalar)
                (multiply scalar (rational scalar configuredDecay)
                  (natScalar (blockDistance left right))))
              (one scalar))
            (multiply scalar (norm2 rightState rightState)
              (norm2 leftState leftState))))

open ConfiguredLocalPhysicalHessian public

asLocalCombesThomasBlockEstimate :
  ∀ {Block State Scalar Operator GreenOperator} →
  ConfiguredLocalPhysicalHessian Block State Scalar Operator GreenOperator →
  Green.LocalCombesThomasBlockEstimate Block State Scalar Operator GreenOperator
asLocalCombesThomasBlockEstimate dataSet = record
  { blockDistance = blockDistance dataSet
  ; zero = zero (scalar dataSet)
  ; one = one (scalar dataSet)
  ; multiply = multiply (scalar dataSet)
  ; subtract = subtract (scalar dataSet)
  ; exponential = λ x → exponential (scalar dataSet) x (one (scalar dataSet))
  ; natScalar = natScalar dataSet
  ; LessEqual = LessEqual (scalar dataSet)
  ; StrictLess = StrictLess (scalar dataSet)
  ; operator = operator dataSet
  ; green = green dataSet
  ; spectralGap = rational (scalar dataSet) configuredGreenGap
  ; hoppingBound = rational (scalar dataSet) configuredHopping
  ; interactionRange = one (scalar dataSet)
  ; decayRate = rational (scalar dataSet) configuredDecay
  ; l2Prefactor = configuredL2Prefactor dataSet
  ; supportedInBlock = supportedInBlock dataSet
  ; norm2 = norm2 dataSet
  ; pairing = pairing dataSet
  ; applyGreen = applyGreen dataSet
  ; finiteRangeOperator = finiteRangeOperator dataSet
  ; gaugeFixedSpectralGap = gaugeFixedSpectralGap dataSet
  ; inverseOnGaugeFixedSpace = inverseOnGaugeFixedSpace dataSet
  ; weightedConjugationDifferenceExact = weightedConjugationDifferenceExact dataSet
  ; weightedPerturbationBound = weightedPerturbationBound dataSet
  ; decayRatePositive = configuredDecayPositive (scalar dataSet)
  ; perturbationBelowHalfGap = perturbationBelowHalfGap dataSet
  ; weightedNeumannResolventConverges = weightedNeumannResolventConverges dataSet
  ; weightedInverseNormBound = weightedInverseNormBound dataSet
  ; localBlockL2Decay = localBlockL2Decay dataSet
  }

record ConfiguredFourierRGImageInstance
    (Scale Volume Site Function Scalar GreenOperator Symbol : Set) : Set₂ where
  field
    scalar : ConfiguredGreenScalarAuthority Scalar

    distance : Site → Site → Nat
    distanceToSupport : Site → Function → Nat
    supNorm : Function → Scalar
    applyGreen : GreenOperator → Function → Site → Scalar
    natScalar : Nat → Scalar

    averagingGreen : Scale → GreenOperator
    FourierSymbol : Scale → Symbol
    averagingKernel : GreenOperator → Site → Site → Scalar

    FourierRepresentationExact : ∀ scale → Set
    FourierSymbolAnalyticInUniformStrip : ∀ scale → Set
    FourierSymbolBoundedInUniformStrip : ∀ scale → Set

    fourierPrefactor : Scalar
    infiniteLatticeExponentialDecay : ∀ scale left right →
      LessEqual scalar
        (averagingKernel (averagingGreen scale) left right)
        (multiply scalar fourierPrefactor
          (exponential scalar
            (subtract scalar (zero scalar)
              (multiply scalar (rational scalar configuredDecay)
                (natScalar (distance left right))))
            (one scalar)))

    finiteVolumeGreen fluctuationGreen : Scale → Volume → GreenOperator
    dimensionFactor finiteVolumePrefactor : Scalar

    localCombesThomasInput : ∀ scale volume → Set
    infiniteLatticeFourierInput : ∀ scale → Set
    renormalizationGroupEquationExact : ∀ scale volume → Set
    methodOfImagesExact : ∀ scale volume → Set
    imageSumAbsolutelyConvergent : ∀ scale volume → Set
    imageTailExponential : ∀ scale volume → Set

    theoremAUniformSupNormDecay : ∀ scale volume function point →
      LessEqual scalar
        (applyGreen (finiteVolumeGreen scale volume) function point)
        (multiply scalar finiteVolumePrefactor
          (multiply scalar dimensionFactor
            (multiply scalar
              (exponential scalar
                (subtract scalar (zero scalar)
                  (multiply scalar (rational scalar configuredDecay)
                    (natScalar (distanceToSupport point function))))
                (one scalar))
              (supNorm function))))

    fluctuationGreenFromRGDifferenceExact : ∀ scale volume → Set
    fluctuationGreenUniformSupNormDecay : ∀ scale volume function point →
      LessEqual scalar
        (applyGreen (fluctuationGreen scale volume) function point)
        (multiply scalar finiteVolumePrefactor
          (multiply scalar dimensionFactor
            (multiply scalar
              (exponential scalar
                (subtract scalar (zero scalar)
                  (multiply scalar (rational scalar configuredDecay)
                    (natScalar (distanceToSupport point function))))
                (one scalar))
              (supNorm function))))

open ConfiguredFourierRGImageInstance public

physicalFluctuationGreenOffDiagonalDecayConfigured =
  fluctuationGreenUniformSupNormDecay

patchUniformGreenDecayConfigured =
  physicalFluctuationGreenOffDiagonalDecayConfigured
scaleUniformGreenDecayConfigured =
  physicalFluctuationGreenOffDiagonalDecayConfigured
volumeUniformGreenDecayConfigured =
  physicalFluctuationGreenOffDiagonalDecayConfigured

configuredCombesThomasArithmeticLevel : ProofLevel
configuredCombesThomasArithmeticLevel = machineChecked

configuredLocalGreenAdapterLevel : ProofLevel
configuredLocalGreenAdapterLevel = machineChecked

configuredFourierRGImageReductionLevel : ProofLevel
configuredFourierRGImageReductionLevel = machineChecked

literalFiniteRangeGapAndFourierImageInputsLevel : ProofLevel
literalFiniteRangeGapAndFourierImageInputsLevel = conditional
