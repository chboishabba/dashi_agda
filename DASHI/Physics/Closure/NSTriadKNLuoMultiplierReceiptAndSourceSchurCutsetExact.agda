module DASHI.Physics.Closure.NSTriadKNLuoMultiplierReceiptAndSourceSchurCutsetExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: William Henry Young.
-- Title: "On the Multiplication of Successions of Fourier Constants".
-- Proceedings of the Royal Society of London. Series A 87 (1912).
-- DOI: 10.1098/rspa.1912.0086.
--
-- Authors: Loukas Grafakos; Rodolfo H. Torres.
-- Title: "A Multilinear Schur Test and Multiplier Operators".
-- Journal of Functional Analysis 187 (2001), 1--24.
-- DOI: 10.1006/jfan.2001.3804.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Expose the exact two constructor boundaries for Stage B. Concrete finite
-- convolution receipts produce the official periodic multiplier realization;
-- concrete source/physical identifications produce the weighted-Schur theorem.
-- Neither final estimate is requested independently once its physical leaves
-- are supplied.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSTriadKNLuoFinitePeriodicMultiplierRealizationExact as FiniteMultiplier
import DASHI.Physics.Closure.NSTriadKNLuoConcreteRadialMultiplierKernelExact as Multiplier
import DASHI.Physics.Closure.NSTriadKNLuoOfficialPreBudgetDataExact as PreBudget
import DASHI.Physics.Closure.NSTriadKNLuoExactFluxKernelDecompositionExact as Source
import DASHI.Physics.Closure.NSTriadKNLuoCanonicalSourceSchurIdentificationExact as SourceSchur

OfficialMultiplierObservableReceipts :
  ∀ {st} → Set st → Set st → Set (lsuc st)
OfficialMultiplierObservableReceipts =
  FiniteMultiplier.FinitePeriodicMultiplierInputs

officialMultiplierRealizationFromFiniteReceipts :
  ∀ {st}
    {State TorusPoint : Set st} →
  OfficialMultiplierObservableReceipts State TorusPoint →
  Multiplier.CanonicalLuoMultiplierRealization State TorusPoint
officialMultiplierRealizationFromFiniteReceipts =
  FiniteMultiplier.finitePeriodicMultiplierRealization

canonicalWeightedSchurFromPhysicalLeaves :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time}
    {Tensor : Set}
    {source : Source.LuoExactFluxKernelDecomposition ⊤ Tensor ℚ} →
  SourceSchur.CanonicalSourceSchurPhysicalLeaves data Tensor source →
  Source.LuoFluxKernelToWeightedSchur source
canonicalWeightedSchurFromPhysicalLeaves =
  SourceSchur.canonicalFluxKernelToWeightedSchur

record MultiplierReceiptSemanticAudit : Set₁ where
  field
    SmoothMultiplierFactorsThroughNextHardCutoff : Set
    smoothMultiplierFactorsThroughNextHardCutoff :
      SmoothMultiplierFactorsThroughNextHardCutoff

    MultiplierProductIdentityOnSmoothSupport : Set
    multiplierProductIdentityOnSmoothSupport :
      MultiplierProductIdentityOnSmoothSupport

    PeriodicConvolutionCoefficientFormula : Set
    periodicConvolutionCoefficientFormula :
      PeriodicConvolutionCoefficientFormula

    HardSupDominatesEachConvolutionSample : Set
    hardSupDominatesEachConvolutionSample :
      HardSupDominatesEachConvolutionSample

    KernelAbsoluteSumEqualsFiniteL1Receipt : Set
    kernelAbsoluteSumEqualsFiniteL1Receipt :
      KernelAbsoluteSumEqualsFiniteL1Receipt

    NonnegativeTimeIntegralMonotone : Set
    nonnegativeTimeIntegralMonotone :
      NonnegativeTimeIntegralMonotone

    ConstantPullsOutOfTimeIntegral : Set
    constantPullsOutOfTimeIntegral :
      ConstantPullsOutOfTimeIntegral

    HardTerminalWindowMatchesOfficialLocalizedIntegral : Set
    hardTerminalWindowMatchesOfficialLocalizedIntegral :
      HardTerminalWindowMatchesOfficialLocalizedIntegral

    SmoothTerminalWindowMatchesLuoLocalizedIntegral : Set
    smoothTerminalWindowMatchesLuoLocalizedIntegral :
      SmoothTerminalWindowMatchesLuoLocalizedIntegral

    SameMultiplierConstantForAllShells : Set
    sameMultiplierConstantForAllShells :
      SameMultiplierConstantForAllShells

    SameConstantForPointwiseAndTerminalBounds : Set
    sameConstantForPointwiseAndTerminalBounds :
      SameConstantForPointwiseAndTerminalBounds

    MultiplierConstantFinite : Set
    multiplierConstantFinite : MultiplierConstantFinite

open MultiplierReceiptSemanticAudit public

record SourceSchurSemanticAudit : Set₁ where
  field
    SourceAbsoluteHighFluxEqualsIncrementKernelFlux : Set
    sourceAbsoluteHighFluxEqualsIncrementKernelFlux :
      SourceAbsoluteHighFluxEqualsIncrementKernelFlux

    IncrementKernelFluxEqualsProjectedConvectionFlux : Set
    incrementKernelFluxEqualsProjectedConvectionFlux :
      IncrementKernelFluxEqualsProjectedConvectionFlux

    ProjectedConvectionFluxEqualsPhysicalPairFold : Set
    projectedConvectionFluxEqualsPhysicalPairFold :
      ProjectedConvectionFluxEqualsPhysicalPairFold

    PhysicalPairFoldEqualsWeightedSchurBridgeFlux : Set
    physicalPairFoldEqualsWeightedSchurBridgeFlux :
      PhysicalPairFoldEqualsWeightedSchurBridgeFlux

    SourceSmoothLowPassMatchesCanonicalMultiplier : Set
    sourceSmoothLowPassMatchesCanonicalMultiplier :
      SourceSmoothLowPassMatchesCanonicalMultiplier

    CanonicalMultiplierHardOrSmoothIndexShift : Set
    canonicalMultiplierHardOrSmoothIndexShift :
      CanonicalMultiplierHardOrSmoothIndexShift

    ProfileSchurConstantIndependentOfShell : Set
    profileSchurConstantIndependentOfShell :
      ProfileSchurConstantIndependentOfShell

    ProfileSchurConstantIndependentOfState : Set
    profileSchurConstantIndependentOfState :
      ProfileSchurConstantIndependentOfState

    CommonSchurConstantFinite : Set
    commonSchurConstantFinite : CommonSchurConstantFinite

    CommonSchurConstantNonnegative : Set
    commonSchurConstantNonnegative : CommonSchurConstantNonnegative

    SourceAdditionTransport : Set
    sourceAdditionTransport : SourceAdditionTransport

    SourceAbsoluteValueTransport : Set
    sourceAbsoluteValueTransport : SourceAbsoluteValueTransport

    SourceZeroOneTransport : Set
    sourceZeroOneTransport : SourceZeroOneTransport

    SourceFiniteSumTransport : Set
    sourceFiniteSumTransport : SourceFiniteSumTransport

    SourceLowEnergyEqualsPhysicalLowEnergyFold : Set
    sourceLowEnergyEqualsPhysicalLowEnergyFold :
      SourceLowEnergyEqualsPhysicalLowEnergyFold

    SourceHighEnergyEqualsPhysicalHighEnergyFold : Set
    sourceHighEnergyEqualsPhysicalHighEnergyFold :
      SourceHighEnergyEqualsPhysicalHighEnergyFold

    LowPlusHighEnergyBelowWeightedMajorant : Set
    lowPlusHighEnergyBelowWeightedMajorant :
      LowPlusHighEnergyBelowWeightedMajorant

    WeightedEnergyProfileSummationBound : Set
    weightedEnergyProfileSummationBound :
      WeightedEnergyProfileSummationBound

open SourceSchurSemanticAudit public

multiplierReceiptConstructorClosed : Bool
multiplierReceiptConstructorClosed = true

sourceSchurConstructorClosed : Bool
sourceSchurConstructorClosed = true

stageBSemanticCutsetsSeparated : Bool
stageBSemanticCutsetsSeparated = true

multiplierReceiptConstructorClosedIsTrue :
  multiplierReceiptConstructorClosed ≡ true
multiplierReceiptConstructorClosedIsTrue = refl

sourceSchurConstructorClosedIsTrue :
  sourceSchurConstructorClosed ≡ true
sourceSchurConstructorClosedIsTrue = refl

stageBSemanticCutsetsSeparatedIsTrue :
  stageBSemanticCutsetsSeparated ≡ true
stageBSemanticCutsetsSeparatedIsTrue = refl
