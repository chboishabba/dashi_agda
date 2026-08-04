module DASHI.Physics.Closure.NSTriadKNLuoPhysicalBlockDecayReductionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Express the physical fixed-shift bootstrap as an implication chain from the
-- integrated cutoff estimate and correction comparison to block decay, shell
-- decay, Sobolev regularity and continuation regularity.  The algebraic block
-- induction is not requested as a fresh physical theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)

record PhysicalBlockDecayPrimitiveInputs : Set₁ where
  field
    IntegratedCutoffEnergyInequality : Set
    integratedCutoffEnergyInequality :
      IntegratedCutoffEnergyInequality

    FluxCorrectionBelowExplicitMajorant : Set
    fluxCorrectionBelowExplicitMajorant :
      FluxCorrectionBelowExplicitMajorant

    ExplicitMajorantBelowDyadicDecayTarget : Set
    explicitMajorantBelowDyadicDecayTarget :
      ExplicitMajorantBelowDyadicDecayTarget

    FixedShiftRecursion : Set
    fixedShiftRecursionFromPhysicalInequalities :
      IntegratedCutoffEnergyInequality →
      FluxCorrectionBelowExplicitMajorant →
      ExplicitMajorantBelowDyadicDecayTarget →
      FixedShiftRecursion

    BaseBlockFinite : Set
    baseBlockFinite : BaseBlockFinite

    BaseBlockUniformBound : Set
    baseBlockUniformBound : BaseBlockFinite → BaseBlockUniformBound

    RecursionCoefficientStrictlyBelowOne : Set
    recursionCoefficientStrictlyBelowOne :
      RecursionCoefficientStrictlyBelowOne

    CorrectionDecayCompatibleWithTarget : Set
    correctionDecayCompatibleWithTarget :
      CorrectionDecayCompatibleWithTarget

    PhysicalBlockDecayCertificate : Set
    blockInductionCloses :
      FixedShiftRecursion →
      BaseBlockUniformBound →
      RecursionCoefficientStrictlyBelowOne →
      CorrectionDecayCompatibleWithTarget →
      PhysicalBlockDecayCertificate

    ShellUniformDyadicDecay : Set
    blockDecayGivesShellUniformDyadicDecay :
      PhysicalBlockDecayCertificate → ShellUniformDyadicDecay

    ShellL2Decay : Set
    energyDecayImpliesShellL2Decay :
      ShellUniformDyadicDecay → ShellL2Decay

    GradientShellDecay : Set
    dissipationDecayImpliesGradientShellDecay :
      ShellUniformDyadicDecay → GradientShellDecay

    AlphaAboveOneSummability : Set
    alphaAboveOneSummability : AlphaAboveOneSummability

    RequiredContinuationRegularity : Set
    shellDecayAndSummabilityGiveRequiredRegularity :
      ShellL2Decay →
      GradientShellDecay →
      AlphaAboveOneSummability →
      RequiredContinuationRegularity

open PhysicalBlockDecayPrimitiveInputs public

derivedFixedShiftRecursion :
  (inputs : PhysicalBlockDecayPrimitiveInputs) →
  FixedShiftRecursion inputs
derivedFixedShiftRecursion inputs =
  fixedShiftRecursionFromPhysicalInequalities inputs
    (integratedCutoffEnergyInequality inputs)
    (fluxCorrectionBelowExplicitMajorant inputs)
    (explicitMajorantBelowDyadicDecayTarget inputs)

derivedBaseBlockUniformBound :
  (inputs : PhysicalBlockDecayPrimitiveInputs) →
  BaseBlockUniformBound inputs
derivedBaseBlockUniformBound inputs =
  baseBlockUniformBound inputs (baseBlockFinite inputs)

derivedPhysicalBlockDecayCertificate :
  (inputs : PhysicalBlockDecayPrimitiveInputs) →
  PhysicalBlockDecayCertificate inputs
derivedPhysicalBlockDecayCertificate inputs =
  blockInductionCloses inputs
    (derivedFixedShiftRecursion inputs)
    (derivedBaseBlockUniformBound inputs)
    (recursionCoefficientStrictlyBelowOne inputs)
    (correctionDecayCompatibleWithTarget inputs)

derivedShellUniformDyadicDecay :
  (inputs : PhysicalBlockDecayPrimitiveInputs) →
  ShellUniformDyadicDecay inputs
derivedShellUniformDyadicDecay inputs =
  blockDecayGivesShellUniformDyadicDecay inputs
    (derivedPhysicalBlockDecayCertificate inputs)

derivedRequiredContinuationRegularity :
  (inputs : PhysicalBlockDecayPrimitiveInputs) →
  RequiredContinuationRegularity inputs
derivedRequiredContinuationRegularity inputs =
  shellDecayAndSummabilityGiveRequiredRegularity inputs
    (energyDecayImpliesShellL2Decay inputs
      (derivedShellUniformDyadicDecay inputs))
    (dissipationDecayImpliesGradientShellDecay inputs
      (derivedShellUniformDyadicDecay inputs))
    (alphaAboveOneSummability inputs)

record PhysicalBlockDecayReceipt : Set₁ where
  field
    primitiveInputs : PhysicalBlockDecayPrimitiveInputs
    fixedShiftRecursion : FixedShiftRecursion primitiveInputs
    blockDecayCertificate :
      PhysicalBlockDecayCertificate primitiveInputs
    shellUniformDecay : ShellUniformDyadicDecay primitiveInputs
    continuationRegularity :
      RequiredContinuationRegularity primitiveInputs

open PhysicalBlockDecayReceipt public

physicalBlockDecayReceipt :
  PhysicalBlockDecayPrimitiveInputs → PhysicalBlockDecayReceipt
physicalBlockDecayReceipt inputs = record
  { primitiveInputs = inputs
  ; fixedShiftRecursion = derivedFixedShiftRecursion inputs
  ; blockDecayCertificate =
      derivedPhysicalBlockDecayCertificate inputs
  ; shellUniformDecay = derivedShellUniformDyadicDecay inputs
  ; continuationRegularity =
      derivedRequiredContinuationRegularity inputs
  }

physicalBlockDecayReductionConstructed : Bool
physicalBlockDecayReductionConstructed = true

continuationRegularityDerivedFromPhysicalDecay : Bool
continuationRegularityDerivedFromPhysicalDecay = true

physicalBlockDecayReductionConstructedIsTrue :
  physicalBlockDecayReductionConstructed ≡ true
physicalBlockDecayReductionConstructedIsTrue = refl

continuationRegularityDerivedFromPhysicalDecayIsTrue :
  continuationRegularityDerivedFromPhysicalDecay ≡ true
continuationRegularityDerivedFromPhysicalDecayIsTrue = refl
