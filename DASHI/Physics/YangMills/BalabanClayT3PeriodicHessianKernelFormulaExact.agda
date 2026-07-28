module DASHI.Physics.YangMills.BalabanClayT3PeriodicHessianKernelFormulaExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Foundations.RealAnalysisAxioms as Real
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
import DASHI.Physics.YangMills.BalabanClayT3PeriodicTorusGreenCarrierExact as Carrier
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Literal finite-volume Hessian, Fourier and image formulas.
--
-- Tadeusz Bałaban, "Propagators for Lattice Gauge Theories in a Background
-- Field", Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Wojciech Dybalski, Alexander Stottmeister and Yoh Tanimoto,
-- "Lattice Green Functions for Pedestrians: Exponential Decay",
-- Reviews in Mathematical Physics 36 (2024), 2430005.
-- DOI: 10.1142/S0129055X2430005X; arXiv:2303.10754.
--
-- The definitions below fix the kernel algebra, weighted conjugation, matrix
-- symbol and Schur/image conventions.  Spectral and strip inequalities remain
-- explicit physical theorems; no numerical hopping constant is assumed by
-- definition.
------------------------------------------------------------------------

zeroKernel : ∀ {L} → Carrier.BondKernel L
zeroKernel = Carrier.bondKernel (λ _ _ → Real.0ℝ)

addKernel : ∀ {L} → Carrier.BondKernel L → Carrier.BondKernel L → Carrier.BondKernel L
addKernel left right = Carrier.bondKernel
  (λ output input →
    Real._+ℝ_ (Carrier.entry left output input)
      (Carrier.entry right output input))

subKernel : ∀ {L} → Carrier.BondKernel L → Carrier.BondKernel L → Carrier.BondKernel L
subKernel left right = Carrier.bondKernel
  (λ output input →
    Real._-ℝ_ (Carrier.entry left output input)
      (Carrier.entry right output input))

scaleKernel : ∀ {L} → Real.ℝ → Carrier.BondKernel L → Carrier.BondKernel L
scaleKernel scalar kernel = Carrier.bondKernel
  (λ output input →
    Real._*ℝ_ scalar (Carrier.entry kernel output input))

transposeKernel : ∀ {L} → Carrier.BondKernel L → Carrier.BondKernel L
transposeKernel kernel = Carrier.bondKernel
  (λ output input → Carrier.entry kernel input output)

kernelEntryAddExact :
  ∀ {L} (left right : Carrier.BondKernel L) output input →
  Carrier.entry (addKernel left right) output input
  ≡ Real._+ℝ_ (Carrier.entry left output input)
      (Carrier.entry right output input)
kernelEntryAddExact left right output input = refl

record ReferenceHessianComponents (L : Nat) (Background : Set) : Set₁ where
  field
    wilsonKernel gaugeFixingKernel blockPenaltyKernel :
      Background → Carrier.BondKernel L

    wilsonSelfAdjoint : ∀ background left right →
      Carrier.entry (wilsonKernel background) left right
      ≡ Carrier.entry (wilsonKernel background) right left

    gaugeFixingSelfAdjoint : ∀ background left right →
      Carrier.entry (gaugeFixingKernel background) left right
      ≡ Carrier.entry (gaugeFixingKernel background) right left

    blockPenaltySelfAdjoint : ∀ background left right →
      Carrier.entry (blockPenaltyKernel background) left right
      ≡ Carrier.entry (blockPenaltyKernel background) right left

    interactionRange : Nat
    wilsonFiniteRange : ∀ background left right → Set
    gaugeFixingFiniteRange : ∀ background left right → Set
    blockPenaltyFiniteRange : ∀ background left right → Set

open ReferenceHessianComponents public

referenceHessianKernel :
  ∀ {L Background} →
  ReferenceHessianComponents L Background →
  Background → Carrier.BondKernel L
referenceHessianKernel components background =
  addKernel (wilsonKernel components background)
    (addKernel (gaugeFixingKernel components background)
      (blockPenaltyKernel components background))

referenceHessianEntryExact :
  ∀ {L Background}
    (components : ReferenceHessianComponents L Background)
    background output input →
  Carrier.entry (referenceHessianKernel components background) output input
  ≡ Real._+ℝ_
      (Carrier.entry (wilsonKernel components background) output input)
      (Real._+ℝ_
        (Carrier.entry (gaugeFixingKernel components background) output input)
        (Carrier.entry (blockPenaltyKernel components background) output input))
referenceHessianEntryExact components background output input = refl

cong₂ :
  ∀ {A B C : Set} {a a' : A} {b b' : B} →
  (f : A → B → C) → a ≡ a' → b ≡ b' → f a b ≡ f a' b'
cong₂ f refl refl = refl

referenceHessianSelfAdjoint :
  ∀ {L Background}
    (components : ReferenceHessianComponents L Background)
    background left right →
  Carrier.entry (referenceHessianKernel components background) left right
  ≡ Carrier.entry (referenceHessianKernel components background) right left
referenceHessianSelfAdjoint components background left right =
  cong₂ Real._+ℝ_
    (wilsonSelfAdjoint components background left right)
    (cong₂ Real._+ℝ_
      (gaugeFixingSelfAdjoint components background left right)
      (blockPenaltySelfAdjoint components background left right))

record PhysicalHessianFormula (L : Nat) (Background : Set) : Set₁ where
  field
    reference : ReferenceHessianComponents L Background
    backgroundRemainder : Background → Carrier.BondKernel L
    backgroundRemainderSelfAdjoint : ∀ background left right →
      Carrier.entry (backgroundRemainder background) left right
      ≡ Carrier.entry (backgroundRemainder background) right left
    backgroundRemainderFiniteRange : ∀ background left right → Set

open PhysicalHessianFormula public

physicalHessianKernel :
  ∀ {L Background} →
  PhysicalHessianFormula L Background →
  Background → Carrier.BondKernel L
physicalHessianKernel formula background =
  addKernel
    (referenceHessianKernel (reference formula) background)
    (backgroundRemainder formula background)

physicalHessianEntryExact :
  ∀ {L Background} (formula : PhysicalHessianFormula L Background)
    background output input →
  Carrier.entry (physicalHessianKernel formula background) output input
  ≡ Real._+ℝ_
      (Carrier.entry
        (referenceHessianKernel (reference formula) background)
        output input)
      (Carrier.entry (backgroundRemainder formula background) output input)
physicalHessianEntryExact formula background output input = refl

physicalHessianSelfAdjoint :
  ∀ {L Background} (formula : PhysicalHessianFormula L Background)
    background left right →
  Carrier.entry (physicalHessianKernel formula background) left right
  ≡ Carrier.entry (physicalHessianKernel formula background) right left
physicalHessianSelfAdjoint formula background left right =
  cong₂ Real._+ℝ_
    (referenceHessianSelfAdjoint (reference formula) background left right)
    (backgroundRemainderSelfAdjoint formula background left right)

------------------------------------------------------------------------
-- Weighted conjugation.  The row-sum estimate is now applied to this exact
-- entry formula, so an unrealistically small C_hop cannot be hidden in notation.
------------------------------------------------------------------------

record ExponentialWeightData (L : Nat) : Set₁ where
  field
    distance : Carrier.PeriodicBondDistance L
    exponential : Real.ℝ → Real.ℝ
    alpha : Real.ℝ
    natToReal : Nat → Real.ℝ
    weight inverseWeight :
      Carrier.PeriodicBlock L → PositiveBond L → Real.ℝ

    weightDefinition : ∀ centre bond → Set
    inverseWeightDefinition : ∀ centre bond → Set
    weightTimesInverse : ∀ centre bond →
      Real._*ℝ_ (weight centre bond) (inverseWeight centre bond) ≡ Real.1ℝ

open ExponentialWeightData public

weightedKernel :
  ∀ {L} → ExponentialWeightData L → Carrier.PeriodicBlock L →
  Carrier.BondKernel L → Carrier.BondKernel L
weightedKernel weights centre kernel = Carrier.bondKernel
  (λ output input →
    Real._*ℝ_ (weight weights centre output)
      (Real._*ℝ_ (Carrier.entry kernel output input)
        (inverseWeight weights centre input)))

weightedDifferenceKernel :
  ∀ {L} → ExponentialWeightData L → Carrier.PeriodicBlock L →
  Carrier.BondKernel L → Carrier.BondKernel L
weightedDifferenceKernel weights centre kernel =
  subKernel (weightedKernel weights centre kernel) kernel

weightedKernelEntryExact :
  ∀ {L} (weights : ExponentialWeightData L) centre
    (kernel : Carrier.BondKernel L) output input →
  Carrier.entry (weightedKernel weights centre kernel) output input
  ≡ Real._*ℝ_ (weight weights centre output)
      (Real._*ℝ_ (Carrier.entry kernel output input)
        (inverseWeight weights centre input))
weightedKernelEntryExact weights centre kernel output input = refl

weightedDifferenceEntryExact :
  ∀ {L} (weights : ExponentialWeightData L) centre
    (kernel : Carrier.BondKernel L) output input →
  Carrier.entry (weightedDifferenceKernel weights centre kernel) output input
  ≡ Real._-ℝ_
      (Real._*ℝ_ (weight weights centre output)
        (Real._*ℝ_ (Carrier.entry kernel output input)
          (inverseWeight weights centre input)))
      (Carrier.entry kernel output input)
weightedDifferenceEntryExact weights centre kernel output input = refl

record LiteralWeightedHoppingEstimate
    (L : Nat) (Background : Set)
    (formula : PhysicalHessianFormula L Background)
    (weights : ExponentialWeightData L) : Set₁ where
  field
    rowAbsoluteSum : Background → PositiveBond L → Real.ℝ
    weightedDifferenceRowAbsoluteSum :
      Background → Carrier.PeriodicBlock L → PositiveBond L → Real.ℝ

    physicalRowSumDefinition : ∀ background output → Set
    weightedDifferenceRowSumDefinition : ∀ background centre output → Set

    hoppingConstant : Real.ℝ
    physicalHessianRowSumBound : ∀ background output →
      Real._≤ℝ_ (rowAbsoluteSum background output) hoppingConstant

    finiteRangeDistanceDifferenceBound : ∀ background centre output input → Set
    exponentialRangeFactorBound : Set
    weightedDifferenceRowSumBound : ∀ background centre output → Set

    spectralGap : Real.ℝ
    halfGap : Real.ℝ
    weightedPerturbationBelowHalfGap : ∀ background centre → Set
    weightedNeumannSeriesConverges : ∀ background centre → Set
    combesThomasEntryDecay : ∀ background left right → Set

open LiteralWeightedHoppingEstimate public

------------------------------------------------------------------------
-- Literal complex-pair Fourier symbol.
------------------------------------------------------------------------

complexZero complexOne : Carrier.ComplexPair
complexZero = Carrier.complexPair Real.0ℝ Real.0ℝ
complexOne = Carrier.complexPair Real.1ℝ Real.0ℝ

complexAdd complexSub complexMul :
  Carrier.ComplexPair → Carrier.ComplexPair → Carrier.ComplexPair
complexAdd left right = Carrier.complexPair
  (Real._+ℝ_ (Carrier.realPart left) (Carrier.realPart right))
  (Real._+ℝ_ (Carrier.imaginaryPart left) (Carrier.imaginaryPart right))
complexSub left right = Carrier.complexPair
  (Real._-ℝ_ (Carrier.realPart left) (Carrier.realPart right))
  (Real._-ℝ_ (Carrier.imaginaryPart left) (Carrier.imaginaryPart right))
complexMul left right = Carrier.complexPair
  (Real._-ℝ_
    (Real._*ℝ_ (Carrier.realPart left) (Carrier.realPart right))
    (Real._*ℝ_ (Carrier.imaginaryPart left) (Carrier.imaginaryPart right)))
  (Real._+ℝ_
    (Real._*ℝ_ (Carrier.realPart left) (Carrier.imaginaryPart right))
    (Real._*ℝ_ (Carrier.imaginaryPart left) (Carrier.realPart right)))

complexConjugate : Carrier.ComplexPair → Carrier.ComplexPair
complexConjugate value =
  Carrier.complexPair (Carrier.realPart value) (Real.-ℝ_ (Carrier.imaginaryPart value))

realComplex : Real.ℝ → Carrier.ComplexPair
realComplex value = Carrier.complexPair value Real.0ℝ

axisDelta : Axis4 → Axis4 → Carrier.ComplexPair
axisDelta left right with cyclicIndexDecidableEquality left right
... | yes refl = complexOne
... | no _ = complexZero

record ReferenceFourierFormula (L : Nat) : Set₁ where
  field
    hatMomentum : Carrier.PeriodicMomentum L → Axis4 → Carrier.ComplexPair
    hatMomentumSquared : Carrier.PeriodicMomentum L → Carrier.ComplexPair
    averagingSymbol : Carrier.PeriodicMomentum L → Carrier.Matrix4
    gaugeCoefficient blockCoefficient : Real.ℝ

    hatMomentumDefinition : ∀ momentum axis → Set
    hatMomentumSquaredDefinition : ∀ momentum → Set
    averagingSymbolDefinition : ∀ momentum left right → Set

open ReferenceFourierFormula public

referenceSymbolEntry :
  ∀ {L} → ReferenceFourierFormula L →
  Carrier.PeriodicMomentum L → Axis4 → Axis4 → Carrier.ComplexPair
referenceSymbolEntry formula momentum left right =
  complexAdd
    (complexMul (hatMomentumSquared formula momentum) (axisDelta left right))
    (complexAdd
      (complexMul
        (realComplex (gaugeCoefficient formula))
        (complexMul
          (hatMomentum formula momentum left)
          (complexConjugate (hatMomentum formula momentum right))))
      (complexMul
        (realComplex (blockCoefficient formula))
        (averagingSymbol formula momentum left right)))

referenceSymbol : ∀ {L} → ReferenceFourierFormula L →
  Carrier.PeriodicMomentum L → Carrier.Matrix4
referenceSymbol formula momentum = referenceSymbolEntry formula momentum

referenceSymbolEntryExact :
  ∀ {L} (formula : ReferenceFourierFormula L) momentum left right →
  referenceSymbol formula momentum left right
  ≡ referenceSymbolEntry formula momentum left right
referenceSymbolEntryExact formula momentum left right = refl

record LiteralFourierStripEstimate (L : Nat)
    (formula : ReferenceFourierFormula L) : Set₁ where
  field
    finiteFourierTransform : Carrier.PeriodicEdgeField L →
      Axis4 → Carrier.PeriodicMomentum L → Carrier.ComplexPair
    finiteFourierInversionExact : Set
    fourierTransformDiagonalizesReferenceHessian : Set

    complexMomentum : Set
    complexStripWidth : Real.ℝ
    complexifiedHatMomentum : complexMomentum → Axis4 → Carrier.ComplexPair
    complexifiedReferenceSymbol : complexMomentum → Carrier.Matrix4
    momentumInComplexStrip : complexMomentum → Set

    complexHatMomentumPerturbationBound : ∀ momentum →
      momentumInComplexStrip momentum → Set
    complexReferenceSymbolPerturbationBound : ∀ momentum →
      momentumInComplexStrip momentum → Set
    complexSymbolPerturbationBelowSixteenth : ∀ momentum →
      momentumInComplexStrip momentum → Set
    symbolNonzeroOnComplexStrip : ∀ momentum →
      momentumInComplexStrip momentum → Set
    symbolInverseNormBelowSixteen : ∀ momentum →
      momentumInComplexStrip momentum → Set
    contourShiftExponentialDecay : Set

open LiteralFourierStripEstimate public

------------------------------------------------------------------------
-- Exact finite kernel composition and the RG Green-difference convention.
------------------------------------------------------------------------

composeKernel : ∀ {L} → Carrier.BondKernel L → Carrier.BondKernel L → Carrier.BondKernel L
composeKernel {L} left right = Carrier.bondKernel
  (λ output input →
    Carrier.sumℝ
      (map
        (λ middle →
          Real._*ℝ_ (Carrier.entry left output middle)
            (Carrier.entry right middle input))
        (Carrier.allPositiveBonds L)))
  where
  map : ∀ {A B : Set} → (A → B) → List A → List B
  map f [] = []
  map f (x ∷ xs) = f x ∷ map f xs

fluctuationGreenFromDifference :
  ∀ {L} → Carrier.BondKernel L → Carrier.BondKernel L →
  Carrier.BondKernel L → Carrier.BondKernel L
fluctuationGreenFromDifference fine coarse blockAverage =
  subKernel fine
    (composeKernel (transposeKernel blockAverage)
      (composeKernel coarse blockAverage))

fluctuationGreenDifferenceExact :
  ∀ {L} (fine coarse blockAverage : Carrier.BondKernel L) →
  fluctuationGreenFromDifference fine coarse blockAverage
  ≡ subKernel fine
      (composeKernel (transposeKernel blockAverage)
        (composeKernel coarse blockAverage))
fluctuationGreenDifferenceExact fine coarse blockAverage = refl

record LiteralRGIdentity (L : Nat) : Set₁ where
  field
    fineGreen coarseGreen blockAverage : Nat → Carrier.BondKernel L
    coarseHessian : Nat → Carrier.BondKernel L

    blockAverageAdjointExact : ∀ scale → Set
    coarseHessianSchurComplementExact : ∀ scale → Set
    coarseGreenSchurInverseExact : ∀ scale → Set
    blockAverageIntertwinesGreenExact : ∀ scale → Set

open LiteralRGIdentity public

fluctuationGreen : ∀ {L} → LiteralRGIdentity L → Nat → Carrier.BondKernel L
fluctuationGreen dataSet scale =
  fluctuationGreenFromDifference
    (fineGreen dataSet scale)
    (coarseGreen dataSet scale)
    (blockAverage dataSet scale)

fluctuationCovarianceAsGreenDifferenceExact :
  ∀ {L} (dataSet : LiteralRGIdentity L) scale →
  fluctuationGreen dataSet scale
  ≡ fluctuationGreenFromDifference
      (fineGreen dataSet scale)
      (coarseGreen dataSet scale)
      (blockAverage dataSet scale)
fluctuationCovarianceAsGreenDifferenceExact dataSet scale = refl

record LiteralPeriodicImageFormula (L : Nat) : Set₁ where
  field
    infiniteKernel : Nat → Carrier.Integer4 → Carrier.Integer4 → Real.ℝ
    periodicRepresentative : Carrier.Integer4 → Carrier.PeriodicBlock L
    imageTranslation : Carrier.Integer4 → Carrier.Integer4 → Carrier.Integer4
    imageExhaustion : Nat → List Carrier.Integer4

    integer4EuclideanDivisionByPeriod : ∀ site → Set
    periodicRepresentativeUnique : ∀ site → Set
    integer4ImageDecomposition : ∀ site → Set

    finiteImageSum : Nat → Nat → PositiveBond L → PositiveBond L → Real.ℝ
    finiteImageSumDefinition : ∀ depth scale left right → Set
    finiteImageSumsCauchy : ∀ scale left right → Set
    imageSumLimit : Nat → PositiveBond L → PositiveBond L → Real.ℝ
    imageSumLimitExact : ∀ scale left right → Set

    periodizedKernelSolvesPeriodicEquation : ∀ scale → Set
    periodicGreenUniqueness : ∀ scale → Set
    periodicGreenAsImageSumExact : ∀ scale left right → Set
    imageSumAbsolutelyConvergent : ∀ scale left right → Set
    nonzeroImageTailExponential : ∀ scale left right → Set
    finiteVolumeGreenUniformDecay : ∀ scale left right → Set

open LiteralPeriodicImageFormula public

literalPeriodicKernelAlgebraLevel : ProofLevel
literalPeriodicKernelAlgebraLevel = machineChecked

literalWeightedConjugationFormulaLevel : ProofLevel
literalWeightedConjugationFormulaLevel = machineChecked

literalFourierSymbolFormulaLevel : ProofLevel
literalFourierSymbolFormulaLevel = machineChecked

literalRGGreenDifferenceLevel : ProofLevel
literalRGGreenDifferenceLevel = machineChecked

literalHoppingStripAndImageInputsLevel : ProofLevel
literalHoppingStripAndImageInputsLevel = conditional
