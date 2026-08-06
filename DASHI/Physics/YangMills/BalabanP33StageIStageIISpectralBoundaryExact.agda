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
-- John Cardy,
-- "Scaling and Renormalization in Statistical Physics",
-- Cambridge University Press, 1996.
-- DOI: 10.1017/CBO9781316036440.
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
-- theorem.  Its hard producers are:
--
--   1. exact effective-action second derivative / block Hessian;
--   2. a scale-uniform fluctuation inverse C^-1;
--   3. a scale-uniform coarse--fine coupling B bound;
--   4. compatibility of the physical transfer/Hessian gap with dyadic
--      blocking, including the actual one-step loss relation;
--   5. a signed effective remainder estimate;
--   6. a strict discounted loss margin.
--
-- The rational corollary
--
--   m_coarse = 2 m_fine,
--   a_coarse = 2 a_fine
--     => m_coarse/a_coarse = m_fine/a_fine
--
-- is no longer classified as a conditional producer: its division-free form is
-- checked in BalabanP33PhysicalGapScaleInvarianceExact.  The conditional content
-- is proving the simultaneous physical doubling/transfer relation for the
-- actual RG construction.  In particular, B is not hidden inside the remainder.
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
  physicalDyadicGapCompatibility : StageIIProducer
  signedEffectiveRemainder : StageIIProducer
  strictDiscountedMargin : StageIIProducer

producerCount : StageIIProducer → Bool
producerCount effectiveActionSecondDerivative = true
producerCount fluctuationInverseControl = true
producerCount coarseFineCouplingControl = true
producerCount physicalDyadicGapCompatibility = true
producerCount signedEffectiveRemainder = true
producerCount strictDiscountedMargin = true

------------------------------------------------------------------------
-- Authority boundary.
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

    scaleAlgebraAutomaticallyProvesPhysicalDoubling : Bool
    scaleAlgebraAutomaticallyProvesPhysicalDoublingIsFalse :
      scaleAlgebraAutomaticallyProvesPhysicalDoubling ≡ false

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

stageIIScaleNormalizationAlgebraLevel : ProofLevel
stageIIScaleNormalizationAlgebraLevel = machineChecked

stageIIPhysicalDyadicCompatibilityLevel : ProofLevel
stageIIPhysicalDyadicCompatibilityLevel = conditional

stageIISignedRemainderLevel : ProofLevel
stageIISignedRemainderLevel = conditional

stageIIStrictMarginLevel : ProofLevel
stageIIStrictMarginLevel = conditional

spectralGapUndecidabilityScopeLevel : ProofLevel
spectralGapUndecidabilityScopeLevel = standardImported
