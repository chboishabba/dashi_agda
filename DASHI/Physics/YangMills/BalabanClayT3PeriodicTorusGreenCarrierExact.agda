module DASHI.Physics.YangMills.BalabanClayT3PeriodicTorusGreenCarrierExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (ℤ)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ ; 0ℝ ; _+ℝ_ ; _*ℝ_ )
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
import DASHI.Physics.YangMills.BalabanClayT3LiteralHessianFourierImageInstanceExact as Literal

------------------------------------------------------------------------
-- Literal carrier binding for the configured Green lane.
--
-- Wojciech Dybalski, Alexander Stottmeister and Yoh Tanimoto,
-- "Lattice Green Functions for Pedestrians: Exponential Decay",
-- Reviews in Mathematical Physics 36 (2024), 2430005.
-- DOI: 10.1142/S0129055X2430005X; arXiv:2303.10754.
--
-- Tadeusz Bałaban, "Propagators for Lattice Gauge Theories in a Background
-- Field", Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Relationship: this module fixes the actual finite torus, positive-bond field,
-- bond-kernel, dual momentum and image-lattice carriers consumed by the abstract
-- Combes--Thomas/Fourier/RG/image package.  Only the physical kernel identities
-- and analytic estimates remain authority inputs.
------------------------------------------------------------------------

PeriodicBlock : Nat → Set
PeriodicBlock = periodicTorus4Definition

PeriodicMomentum : Nat → Set
PeriodicMomentum = dualPeriodicTorus4Definition

PeriodicEdgeField : Nat → Set
PeriodicEdgeField L = BondField L ℝ

record BondKernel (L : Nat) : Set where
  constructor bondKernel
  field
    entry : PositiveBond L → PositiveBond L → ℝ

open BondKernel public

sumℝ : List ℝ → ℝ
sumℝ [] = 0ℝ
sumℝ (x ∷ xs) = x +ℝ sumℝ xs

allPositiveBonds : ∀ L → List (PositiveBond L)
allPositiveBonds L =
  cartesian
    (FiniteEnumeration.elements (periodicTorus4Finite L))
    (allCyclicIndices four)

applyBondKernel : ∀ {L} → BondKernel L → PeriodicEdgeField L → PeriodicEdgeField L
applyBondKernel {L} kernel field outputBond =
  sumℝ
    (map
      (λ inputBond → entry kernel outputBond inputBond *ℝ field inputBond)
      (allPositiveBonds L))

record ComplexPair : Set where
  constructor complexPair
  field
    realPart imaginaryPart : ℝ

open ComplexPair public

Matrix4 : Set
Matrix4 = Axis4 → Axis4 → ComplexPair

Integer4 : Set
Integer4 = Fourfold ℤ

record PeriodicBondDistance (L : Nat) : Set₁ where
  field
    blockDistance : PeriodicBlock L → PeriodicBlock L → Nat
    bondBlock : PositiveBond L → PeriodicBlock L
    distanceReflexive : ∀ block → blockDistance block block ≡ 0
    distanceSymmetric : ∀ left right →
      blockDistance left right ≡ blockDistance right left
    distanceTriangle : ∀ left middle right → Set

open PeriodicBondDistance public

record PeriodicGaugeFixedHessianKernel
    (L : Nat) (Background : Set) : Set₁ where
  field
    distance : PeriodicBondDistance L

    referenceKernel remainderKernel physicalKernel : Background → BondKernel L

    physicalKernelEntryExact : ∀ background output input →
      entry (physicalKernel background) output input
      ≡ entry (referenceKernel background) output input
        +ℝ entry (remainderKernel background) output input

    referenceKernelSelfAdjoint : ∀ background left right →
      entry (referenceKernel background) left right
      ≡ entry (referenceKernel background) right left

    remainderKernelSelfAdjoint : ∀ background left right →
      entry (remainderKernel background) left right
      ≡ entry (remainderKernel background) right left

    physicalKernelSelfAdjoint : ∀ background left right →
      entry (physicalKernel background) left right
      ≡ entry (physicalKernel background) right left

    interactionRange : Nat
    physicalKernelFiniteRange : ∀ background left right →
      Set

    gaugeFixedState : Background → PeriodicEdgeField L → Set
    backgroundInConfiguredRadius : Background → Set

    referenceQuadraticForm physicalQuadraticForm remainderQuadraticForm :
      Background → PeriodicEdgeField L → ℝ

    physicalQuadraticFormExact : ∀ background state → Set
    referenceCoerciveQuarter : ∀ background state →
      gaugeFixedState background state → Set
    remainderBelowEighth : ∀ background state →
      backgroundInConfiguredRadius background → Set

open PeriodicGaugeFixedHessianKernel public

record PeriodicWeightedResolventData
    (L : Nat) (Background : Set) : Set₁ where
  field
    hessian : PeriodicGaugeFixedHessianKernel L Background
    greenKernel : Background → BondKernel L

    weightedKernel : Background → PeriodicBlock L → BondKernel L
    weightedDifferenceKernel : Background → PeriodicBlock L → BondKernel L

    weightedKernelEntryExact : ∀ background centre left right → Set
    weightedDifferenceEntryExact : ∀ background centre left right → Set
    finiteRangeDistanceDifferenceBound : ∀ background centre left right → Set
    weightedHoppingSumBelowConfigured : ∀ background centre → Set
    weightedPerturbationBelowHalfGap : ∀ background centre → Set
    weightedNeumannSeriesConverges : ∀ background centre → Set
    weightedInverseKernelBound : ∀ background centre → Set
    combesThomasEntryDecay : ∀ background left right → Set

open PeriodicWeightedResolventData public

record PeriodicFourierSymbolData (L : Nat) : Set₁ where
  field
    referenceSymbol averagingSymbol : PeriodicMomentum L → Matrix4
    symbolDenominator : PeriodicMomentum L → ComplexPair

    hatMomentum : PeriodicMomentum L → Axis4 → ComplexPair
    hatMomentumDefinition : ∀ momentum axis → Set

    finiteFourierTransform : PeriodicEdgeField L →
      Axis4 → PeriodicMomentum L → ComplexPair

    fourierTransformDiagonalizesReferenceKernel : Set
    finiteFourierInversionExact : Set
    greenSymbolIsMatrixInverse : Set
    symbolInvertibleOnRealTorus : ∀ momentum → Set

    complexMomentum : Set
    complexStripWidth : ℝ
    complexifiedReferenceSymbol : complexMomentum → Matrix4
    momentumInComplexStrip : complexMomentum → Set
    symbolAnalyticOnComplexStrip : ∀ momentum →
      momentumInComplexStrip momentum → Set
    complexSymbolPerturbationBelowSixteenth : ∀ momentum →
      momentumInComplexStrip momentum → Set
    symbolNonzeroOnComplexStrip : ∀ momentum →
      momentumInComplexStrip momentum → Set
    symbolInverseNormBelowSixteen : ∀ momentum →
      momentumInComplexStrip momentum → Set
    contourShiftExponentialDecay : Set

open PeriodicFourierSymbolData public

record PeriodicRGImageData (L : Nat) : Set₁ where
  field
    fineGreen coarseGreen fluctuationGreen : Nat → BondKernel L
    blockAverage blockAverageAdjoint : Nat → BondKernel L

    coarseFineGreenRGIdentityExact : ∀ scale → Set
    blockAverageIntertwinesGreenExact : ∀ scale → Set
    fluctuationCovarianceAsGreenDifferenceExact : ∀ scale → Set

    infiniteKernel : Nat → Integer4 → Integer4 → ℝ
    periodicRepresentative : Integer4 → PeriodicBlock L
    imageTranslation : Integer4 → Integer4 → Integer4
    imageRepresentatives : List Integer4

    imageRepresentativeDecomposition : ∀ site → Set
    periodicGreenAsImageSumExact : ∀ scale left right → Set
    imageSumAbsolutelyConvergent : ∀ scale left right → Set
    nonzeroImageTailExponential : ∀ scale left right → Set
    finiteVolumeGreenUniformDecay : ∀ scale left right → Set
    finiteVolumeFluctuationGreenUniformDecay : ∀ scale left right → Set

open PeriodicRGImageData public

record PeriodicTorusPhysicalGreenPackage
    (L : Nat) (Background : Set) : Set₁ where
  field
    hessian : PeriodicGaugeFixedHessianKernel L Background
    resolvent : PeriodicWeightedResolventData L Background
    fourier : PeriodicFourierSymbolData L
    rgImages : PeriodicRGImageData L

    localGreenAgreesWithFourierGreen : Set
    referenceAndBackgroundGreenComparison : Set
    constantsUniformInScaleAndVolume : Set

open PeriodicTorusPhysicalGreenPackage public

periodicTorusKernelCarrierLevel : ProofLevel
periodicTorusKernelCarrierLevel = machineChecked

periodicBondKernelApplicationLevel : ProofLevel
periodicBondKernelApplicationLevel = machineChecked

periodicTorusFourierImageCarrierLevel : ProofLevel
periodicTorusFourierImageCarrierLevel = machineChecked

literalPeriodicHessianSymbolImageInputsLevel : ProofLevel
literalPeriodicHessianSymbolImageInputsLevel = conditional
