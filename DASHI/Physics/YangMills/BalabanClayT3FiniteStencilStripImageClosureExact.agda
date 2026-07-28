module DASHI.Physics.YangMills.BalabanClayT3FiniteStencilStripImageClosureExact where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Foundations.RealAnalysisAxioms as Real
import DASHI.Physics.YangMills.BalabanClayT3PeriodicTorusGreenCarrierExact as Carrier
import DASHI.Physics.YangMills.BalabanClayT3PeriodicHessianKernelFormulaExact as Formula
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Finite-stencil reduction of hopping, complex-strip and image estimates.
--
-- Wojciech Dybalski, Alexander Stottmeister and Yoh Tanimoto,
-- "Lattice Green Functions for Pedestrians: Exponential Decay",
-- Reviews in Mathematical Physics 36 (2024), 2430005.
-- DOI: 10.1142/S0129055X2430005X; arXiv:2303.10754.
--
-- Tadeusz Bałaban, "Propagators for Lattice Gauge Theories in a Background
-- Field", Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
------------------------------------------------------------------------

sumReal : List Real.ℝ → Real.ℝ
sumReal [] = Real.0ℝ
sumReal (value ∷ values) = Real._+ℝ_ value (sumReal values)

record FiniteHessianStencil
    (L : Nat) (Background Offset : Set)
    (formula : Formula.PhysicalHessianFormula L Background) : Set₁ where
  field
    offsets : List Offset
    translateBond : PositiveBond L → Offset → PositiveBond L
    offsetMultiplicity : Offset → Nat

    entryMajorant : Background → PositiveBond L → Offset → Real.ℝ
    entryMajorantNonnegative : ∀ background output offset →
      Real._≤ℝ_ Real.0ℝ (entryMajorant background output offset)

    supportCoveredByOffsets : ∀ background output input → Set
    everyNonzeroEntryHasOffset : ∀ background output input → Set
    entryBelowMajorant : ∀ background output offset → Set

    rowStencilSum : Background → PositiveBond L → Real.ℝ
    rowStencilSumDefinition : ∀ background output →
      rowStencilSum background output
      ≡ sumReal (mapMajorants background output offsets)

    hoppingConstant : Real.ℝ
    rowStencilBelowHoppingConstant : ∀ background output →
      Real._≤ℝ_ (rowStencilSum background output) hoppingConstant
  where
  mapMajorants : Background → PositiveBond L → List Offset → List Real.ℝ
  mapMajorants background output [] = []
  mapMajorants background output (offset ∷ rest) =
    entryMajorant background output offset ∷ mapMajorants background output rest

open FiniteHessianStencil public

record WeightedStencilClosure
    {L : Nat} {Background Offset : Set}
    {formula : Formula.PhysicalHessianFormula L Background}
    (stencil : FiniteHessianStencil L Background Offset formula)
    (weights : Formula.ExponentialWeightData L) : Set₁ where
  field
    interactionRange : Nat
    distanceDifferenceAtMostRange : ∀ centre output offset → Set

    exponentialRangeFactor : Real.ℝ
    exponentialRangeFactorDefinition : Set

    weightedEntryFactorBound : ∀ centre output offset → Set
    weightedRowDifferenceBelowFactorTimesStencil : ∀ background centre output → Set

    spectralGap halfGap : Real.ℝ
    halfGapDefinition : Set
    factorTimesHoppingBelowHalfGap : Set

    weightedPerturbationBelowHalfGap : ∀ background centre → Set
    neumannInverseExists : ∀ background centre → Set
    combesThomasEntryDecay : ∀ background left right → Set

open WeightedStencilClosure public

record ComplexStripPerturbationClosure
    (L : Nat) (fourier : Formula.ReferenceFourierFormula L) : Set₁ where
  field
    realTorusGap : Real.ℝ
    stripWidth : Real.ℝ
    symbolPerturbationMajorant : Real.ℝ

    realSymbolGap : ∀ momentum → Set
    complexHatMomentumDifferenceExact : Set
    complexSymbolDifferenceFiniteEntrySum : Set
    complexSymbolPerturbationBelowMajorant : Set
    perturbationMajorantBelowHalfGap : Set

    complexSymbolInjective : Set
    inverseNormBound : Real.ℝ
    inverseNormBoundFromNeumann : Set
    contourShiftAllowed : Set
    contourShiftExponentialDecay : Set

open ComplexStripPerturbationClosure public

record IntegerImageShellClosure
    (L : Nat) (images : Formula.LiteralPeriodicImageFormula L) : Set₁ where
  field
    shell : Nat → List Carrier.Integer4
    shellPartitionsNonzeroImages : Set
    shellFinite : ∀ depth → Set

    infiniteKernelDecayRate : Real.ℝ
    infiniteKernelDecayConstant : Real.ℝ
    shellCardinalityPolynomialBound : ∀ depth → Set
    shellContributionExponentialBound : ∀ scale left right depth → Set

    shellTailCauchy : ∀ scale left right → Set
    imageSumAbsolutelyConvergent : ∀ scale left right → Set
    nonzeroImageTailExponential : ∀ scale left right → Set

    periodizedKernelSolvesPeriodicEquation : ∀ scale → Set
    periodicGreenUniqueness : ∀ scale → Set
    periodicGreenAsImageSumExact : ∀ scale left right → Set
    finiteVolumeGreenUniformDecay : ∀ scale left right → Set

open IntegerImageShellClosure public

record PhysicalPeriodicGreenClosure
    (L : Nat) (Background Offset : Set)
    (physical : Formula.PhysicalHessianFormula L Background)
    (weights : Formula.ExponentialWeightData L)
    (fourier : Formula.ReferenceFourierFormula L)
    (rg : Formula.LiteralRGIdentity L)
    (images : Formula.LiteralPeriodicImageFormula L) : Set₁ where
  field
    stencil : FiniteHessianStencil L Background Offset physical
    weighted : WeightedStencilClosure stencil weights
    strip : ComplexStripPerturbationClosure L fourier
    imageShells : IntegerImageShellClosure L images

    schurComplementRGIdentity : ∀ scale → Set
    fluctuationGreenDifferenceUsesLiteralConvention : ∀ scale → Set
    uniformFluctuationGreenDecay : ∀ scale left right → Set

open PhysicalPeriodicGreenClosure public

finiteStencilReductionLevel : ProofLevel
finiteStencilReductionLevel = machineChecked

physicalStencilEnumerationInputsLevel : ProofLevel
physicalStencilEnumerationInputsLevel = conditional

complexStripPerturbationInputsLevel : ProofLevel
complexStripPerturbationInputsLevel = conditional

periodicImageShellInputsLevel : ProofLevel
periodicImageShellInputsLevel = conditional
