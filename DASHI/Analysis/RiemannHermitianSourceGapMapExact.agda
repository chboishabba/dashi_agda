module DASHI.Analysis.RiemannHermitianSourceGapMapExact where

------------------------------------------------------------------------
-- TOP-DOWN SOURCE OWNERSHIP MAP
--
-- Primary calibration:
-- Levent Alpöge and Ralph Furman,
-- "More than two thirds of the zeta zeros are simple and on the critical line",
-- arXiv:2608.13637 (2026), DOI 10.48550/arXiv.2608.13637.
--
-- Machine-checked source audit: `anthropics/zeta-23-lean`.
--
-- Each G1--G4 lane is split into source/native connections already available
-- and the FIRST genuinely new bridge needed by the Hermitian defect route.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)

------------------------------------------------------------------------
-- G1: COMPLEX POISSON + FINITE RETENTION
--
-- Existing source:
--   P1 real-argument BILINEAR Gabor Poisson summation,
--   P2 complex-argument phiHat definition and compact-support decay,
--   P3 strip bound |phiHat(r-iy)| <= exp(L/4) C1 |r-iy|^-2,
--   P4 real/even taper structure,
--   P5 finite ZERO-SIDE tail machinery.
--
-- DASHI reduction now shows the desired Hermitian norm identity is not an
-- independent theorem: complex bilinear Poisson at (z,conj z), together with
-- real/even Fourier symmetry, derives it exactly.  Thus the first genuinely
-- new Poisson theorem is just the complex-parameter bilinear extension.
------------------------------------------------------------------------

record G1ExistingSource : Set₁ where
  field
    RealBilinearPoissonIdentity : Set
    ComplexPhiHatDefinition : Set
    ComplexStripDecay : Set
    RealEvenTaperStructure : Set
    SourceZeroSideTail : Set
    realBilinearPoissonIdentity : RealBilinearPoissonIdentity
    complexPhiHatDefinition : ComplexPhiHatDefinition
    complexStripDecay : ComplexStripDecay
    realEvenTaperStructure : RealEvenTaperStructure
    sourceZeroSideTail : SourceZeroSideTail

record G1NewBridge (owned : G1ExistingSource) : Set₁ where
  field
    RealEvenFourierConjugateSymmetry : Set
    ComplexBilinearPoissonExtension : Set
    PhiImaginaryAxisAlphaSquaredCoercivity : Set
    FiniteKGridHermitianRetention : Set
    realEvenFourierConjugateSymmetry : RealEvenFourierConjugateSymmetry
    complexBilinearPoissonExtension : ComplexBilinearPoissonExtension
    phiImaginaryAxisAlphaSquaredCoercivity : PhiImaginaryAxisAlphaSquaredCoercivity
    finiteKGridHermitianRetention : FiniteKGridHermitianRetention

------------------------------------------------------------------------
-- G2: MIXED OFF-DIAGONAL INTERFERENCE
--
-- Exact DASHI algebra:
--
--   2[(a.d)^2+(b.c)^2] = (Im S)^2 + (Im H)^2.
--
-- Therefore after G1 identifies S/H with difference/sum Phi kernels, the
-- entire mixed loss factors through a complex Phi-kernel envelope.  Existing
-- source owns local zero counts and Montgomery--Vaughan.  The remaining bridge
-- is a representation/decay/summation theorem showing that envelope lies below
-- the non-target diagonal reservoir.
------------------------------------------------------------------------

record G2ExistingSource : Set₁ where
  field
    MixedLossEqualsImaginaryKernelEnergy : Set
    KernelEnvelopeToAlmostOrthogonality : Set
    LocalZeroCount : Set
    MontgomeryVaughanHilbert : Set
    mixedLossEqualsImaginaryKernelEnergy : MixedLossEqualsImaginaryKernelEnergy
    kernelEnvelopeToAlmostOrthogonality : KernelEnvelopeToAlmostOrthogonality
    localZeroCount : LocalZeroCount
    montgomeryVaughanHilbert : MontgomeryVaughanHilbert

record G2NewBridge (owned : G2ExistingSource) : Set₁ where
  field
    SHToComplexPhiKernelIdentification : Set
    OffDiagonalPhiKernelDecay : Set
    PairwiseKernelEnvelopeSumBound : Set
    InterferenceBelowNonTargetDiagonal : Set
    sHToComplexPhiKernelIdentification : SHToComplexPhiKernelIdentification
    offDiagonalPhiKernelDecay : OffDiagonalPhiKernelDecay
    pairwiseKernelEnvelopeSumBound : PairwiseKernelEnvelopeSumBound
    interferenceBelowNonTargetDiagonal : InterferenceBelowNonTargetDiagonal

------------------------------------------------------------------------
-- G3: PRIME-SIDE NORMALIZED EXCESS
------------------------------------------------------------------------

record G3ExistingSource : Set₁ where
  field
    RawSecondTraceAsymptotic : Set
    PrimeSideErrorScale : Set
    rawSecondTraceAsymptotic : RawSecondTraceAsymptotic
    primeSideErrorScale : PrimeSideErrorScale

record G3NewBridge (owned : G3ExistingSource) : Set₁ where
  field
    CriticalCompatibleMainTermIdentification : Set
    RetainedHermitianExcessAlignment : Set
    NormalizedExcessErrorBound : Set
    criticalCompatibleMainTermIdentification : CriticalCompatibleMainTermIdentification
    retainedHermitianExcessAlignment : RetainedHermitianExcessAlignment
    normalizedExcessErrorBound : NormalizedExcessErrorBound

------------------------------------------------------------------------
-- G4: CROSS THE ERROR FLOOR
--
-- All three routes must manufacture the SAME terminal certificate:
-- targetPairDefect > arithmeticErrorBudget.
------------------------------------------------------------------------

record G4ExistingConnections : Set₁ where
  field
    SourceWindowAndTailControl : Set
    DashiPowerAmplificationAlgebra : Set
    FunctionalEquationReflection : Set
    sourceWindowAndTailControl : SourceWindowAndTailControl
    dashiPowerAmplificationAlgebra : DashiPowerAmplificationAlgebra
    functionalEquationReflection : FunctionalEquationReflection

record G4LocalizationBridge (owned : G4ExistingConnections) : Set₁ where
  field
    PairIsolationWindow : Set
    LeakageBelowPairGap : Set
    pairIsolationWindow : PairIsolationWindow
    leakageBelowPairGap : LeakageBelowPairGap

record G4HigherMomentBridge (owned : G4ExistingConnections) : Set₁ where
  field
    HermitianPowerIdentifiesHigherTrace : Set
    PrimeSideHigherTraceEstimate : Set
    AmplifiedPairBeatsHigherMomentError : Set
    hermitianPowerIdentifiesHigherTrace : HermitianPowerIdentifiesHigherTrace
    primeSideHigherTraceEstimate : PrimeSideHigherTraceEstimate
    amplifiedPairBeatsHigherMomentError : AmplifiedPairBeatsHigherMomentError

record G4ArithmeticRigidityBridge (owned : G4ExistingConnections) : Set₁ where
  field
    ArithmeticCompatibilityObservable : Set
    ReflectionPlusArithmeticForcesAlphaZero : Set
    arithmeticCompatibilityObservable : ArithmeticCompatibilityObservable
    reflectionPlusArithmeticForcesAlphaZero : ReflectionPlusArithmeticForcesAlphaZero

record HermitianSourceGapBoundary : Set where
  field
    realBilinearPoissonSourceOwned : Bool
    complexPhiHatStripDecaySourceOwned : Bool
    realEvenTaperSourceOwned : Bool
    sourceZeroTailOwned : Bool
    hermitianNormReducedToComplexBilinearPoisson : Bool
    complexBilinearPoissonStillNew : Bool
    mixedLossKernelReductionOwned : Bool
    kernelEnvelopeReductionOwned : Bool
    localZeroCountSourceOwned : Bool
    montgomeryVaughanSourceOwned : Bool
    mixedKernelSummationStillNew : Bool
    rawSecondTraceSourceOwned : Bool
    normalizedHermitianAlignmentStillNew : Bool
    windowTailConnectionOwned : Bool
    scalarPowerAmplificationOwned : Bool
    reflectionSymmetryOwned : Bool
    rhStrengthErrorFloorCloserStillNew : Bool

hermitianSourceGapBoundary : HermitianSourceGapBoundary
hermitianSourceGapBoundary = record
  { realBilinearPoissonSourceOwned = true
  ; complexPhiHatStripDecaySourceOwned = true
  ; realEvenTaperSourceOwned = true
  ; sourceZeroTailOwned = true
  ; hermitianNormReducedToComplexBilinearPoisson = true
  ; complexBilinearPoissonStillNew = true
  ; mixedLossKernelReductionOwned = true
  ; kernelEnvelopeReductionOwned = true
  ; localZeroCountSourceOwned = true
  ; montgomeryVaughanSourceOwned = true
  ; mixedKernelSummationStillNew = true
  ; rawSecondTraceSourceOwned = true
  ; normalizedHermitianAlignmentStillNew = true
  ; windowTailConnectionOwned = true
  ; scalarPowerAmplificationOwned = true
  ; reflectionSymmetryOwned = true
  ; rhStrengthErrorFloorCloserStillNew = true
  }
