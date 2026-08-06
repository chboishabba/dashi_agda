module DASHI.Physics.YangMills.BalabanP33StageIStageIISpectralBoundaryExact where

------------------------------------------------------------------------
-- PRIMARY / SCOPE SOURCES
--
-- Toby S. Cubitt, David Pérez-García and Michael M. Wolf,
-- "Undecidability of the Spectral Gap", Forum of Mathematics, Pi 10
-- (2022), e14. DOI: 10.1017/fmp.2021.15.
-- Short version: Nature 528 (2015), 207--211.
-- DOI: 10.1038/nature16059.
--
-- Volker Bach, Thomas Chen, Jürg Fröhlich and Israel Michael Sigal,
-- "Smooth Feshbach Map and Operator-Theoretic Renormalization Group
-- Methods", Journal of Functional Analysis 203 (2003), 44--92.
-- DOI: 10.1016/S0022-1236(03)00057-0.
--
-- Tadeusz Bałaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. II", Communications in Mathematical Physics 96 (1984), 223--250.
-- DOI: 10.1007/BF01240221.
--
-- DASHI CONTRIBUTION
--
-- Make the Stage-I / Stage-II distinction type-visible.  The Cubitt--
-- Pérez-García--Wolf result is used only as a scope boundary: it is not
-- imported as an Agda theorem and does not prove any statement about this
-- particular Yang--Mills model.  It rules out presenting a completely generic
-- finite-description-to-thermodynamic-gap algorithm as the missing argument.
--
-- Stage I is fixed-volume physical Hessian coercivity and its finite
-- Combes--Thomas consequences.  Stage II is a separate structure-specific RG
-- theorem.  Its named producers are:
--
--   1. exact effective-action second derivative / block Hessian;
--   2. a uniform fluctuation inverse C^-1;
--   3. a uniform coarse--fine coupling B bound;
--   4. explicit norm/scaling normalization;
--   5. a signed effective remainder estimate;
--   6. a strict discounted loss margin.
--
-- In particular, B is not hidden inside the remainder.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Distinct theorem stages.
------------------------------------------------------------------------

data SpectralStage : Set where
  finiteVolumeStageI : SpectralStage
  thermodynamicRGStageII : SpectralStage
  continuumOSStageIII : SpectralStage

data StageIIProducer : Set where
  effectiveActionSecondDerivative : StageIIProducer
  fluctuationInverseControl : StageIIProducer
  coarseFineCouplingControl : StageIIProducer
  scalingNormalization : StageIIProducer
  signedEffectiveRemainder : StageIIProducer
  strictDiscountedMargin : StageIIProducer

producerCount : StageIIProducer → Bool
producerCount effectiveActionSecondDerivative = true
producerCount fluctuationInverseControl = true
producerCount coarseFineCouplingControl = true
producerCount scalingNormalization = true
producerCount signedEffectiveRemainder = true
producerCount strictDiscountedMargin = true

------------------------------------------------------------------------
-- Authority boundary.  These fields are deliberately negative claims about
-- what the already checked finite-volume algebra does not establish.
------------------------------------------------------------------------

record StageIStageIIBoundary : Set where
  constructor stageIStageIIBoundary
  field
    finiteCoercivityAutomaticallyGivesThermodynamicGap : Bool
    finiteCoercivityAutomaticallyGivesThermodynamicGapIsFalse :
      finiteCoercivityAutomaticallyGivesThermodynamicGap ≡ false

    finiteCombesThomasAutomaticallyGivesContinuumMassGap : Bool
    finiteCombesThomasAutomaticallyGivesContinuumMassGapIsFalse :
      finiteCombesThomasAutomaticallyGivesContinuumMassGap ≡ false

    spectralUndecidabilityIsImportedAsYangMillsTheorem : Bool
    spectralUndecidabilityIsImportedAsYangMillsTheoremIsFalse :
      spectralUndecidabilityIsImportedAsYangMillsTheorem ≡ false

    stageIIRequiresStructureSpecificProducers : Bool
    stageIIRequiresStructureSpecificProducersIsTrue :
      stageIIRequiresStructureSpecificProducers ≡ true

    coarseFineCouplingMayBeHiddenInRemainder : Bool
    coarseFineCouplingMayBeHiddenInRemainderIsFalse :
      coarseFineCouplingMayBeHiddenInRemainder ≡ false

    nonStrictGapSurvivalImpliesPositiveLimitGap : Bool
    nonStrictGapSurvivalImpliesPositiveLimitGapIsFalse :
      nonStrictGapSurvivalImpliesPositiveLimitGap ≡ false

open StageIStageIIBoundary public

canonicalStageIStageIIBoundary : StageIStageIIBoundary
canonicalStageIStageIIBoundary =
  stageIStageIIBoundary
    false refl
    false refl
    false refl
    true refl
    false refl
    false refl

------------------------------------------------------------------------
-- The present proof-status surface.
------------------------------------------------------------------------

stageIFiniteHessianCoercivityLevel : ProofLevel
stageIFiniteHessianCoercivityLevel = conditional

stageIFiniteCombesThomasAlgebraLevel : ProofLevel
stageIFiniteCombesThomasAlgebraLevel = machineChecked

stageIIEffectiveActionDerivativeLevel : ProofLevel
stageIIEffectiveActionDerivativeLevel = conditional

stageIIFluctuationInverseUniformityLevel : ProofLevel
stageIIFluctuationInverseUniformityLevel = conditional

stageIICoarseFineCouplingUniformityLevel : ProofLevel
stageIICoarseFineCouplingUniformityLevel = conditional

stageIIScalingNormalizationLevel : ProofLevel
stageIIScalingNormalizationLevel = conditional

stageIISignedRemainderLevel : ProofLevel
stageIISignedRemainderLevel = conditional

stageIIStrictMarginLevel : ProofLevel
stageIIStrictMarginLevel = conditional

spectralGapUndecidabilityScopeLevel : ProofLevel
spectralGapUndecidabilityScopeLevel = standardImported
