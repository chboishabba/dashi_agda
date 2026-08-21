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
-- This module does not mark a lane "open" merely because the final theorem is
-- absent.  It factors each G1--G4 producer into the source-native input that is
-- already available and the FIRST genuinely new bridge needed by the Hermitian
-- transverse-defect route.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)

------------------------------------------------------------------------
-- G1: COMPLEX POISSON + FINITE RETENTION
--
-- Existing source:
--   P1 real-argument Gabor Poisson summation (`Zeta23/Poisson.lean`),
--   P2 complex-argument phiHat definition and C^2 compact-support decay,
--   P3 strip bound |phiHat(r-iy)| <= exp(L/4) C1 |r-iy|^-2,
--   P4 finite zero-side tail machinery (`Zeta23/Tail.lean`).
--
-- First new bridge:
--   extend the real bilinear Poisson identity to the conjugate/Hermitian
--   complex pair needed at z=gamma-i alpha.  After that, prove the resulting
--   Phi(-2 i alpha)-Phi(0) excess controls alpha^2 and align the source tail
--   estimate with the finite k-compression used by this new identity.
------------------------------------------------------------------------

record G1ExistingSource : Set₁ where
  field
    RealPoissonIdentity : Set
    ComplexPhiHatDefinition : Set
    ComplexStripDecay : Set
    SourceZeroSideTail : Set
    realPoissonIdentity : RealPoissonIdentity
    complexPhiHatDefinition : ComplexPhiHatDefinition
    complexStripDecay : ComplexStripDecay
    sourceZeroSideTail : SourceZeroSideTail

record G1NewBridge (owned : G1ExistingSource) : Set₁ where
  field
    ComplexHermitianPoissonContinuation : Set
    PhiImaginaryAxisAlphaSquaredCoercivity : Set
    FiniteKGridHermitianRetention : Set
    complexHermitianPoissonContinuation : ComplexHermitianPoissonContinuation
    phiImaginaryAxisAlphaSquaredCoercivity : PhiImaginaryAxisAlphaSquaredCoercivity
    finiteKGridHermitianRetention : FiniteKGridHermitianRetention

------------------------------------------------------------------------
-- G2: MIXED OFF-DIAGONAL INTERFERENCE
--
-- Existing DASHI algebra has reduced
--
--   2[(a.d)^2+(b.c)^2] = (Im S)^2 + (Im H)^2.
--
-- Existing source additionally owns local zero counts and the
-- Montgomery--Vaughan weighted Hilbert inequality.  Neither alone proves the
-- desired cross-sum estimate: a NEW alignment must first rewrite/control the
-- complex difference/sum Phi kernels in a summable separated-frequency form.
------------------------------------------------------------------------

record G2ExistingSource : Set₁ where
  field
    MixedLossEqualsImaginaryKernelEnergy : Set
    LocalZeroCount : Set
    MontgomeryVaughanHilbert : Set
    mixedLossEqualsImaginaryKernelEnergy : MixedLossEqualsImaginaryKernelEnergy
    localZeroCount : LocalZeroCount
    montgomeryVaughanHilbert : MontgomeryVaughanHilbert

record G2NewBridge (owned : G2ExistingSource) : Set₁ where
  field
    SHToComplexPhiKernelIdentification : Set
    OffDiagonalPhiKernelDecay : Set
    PairwiseKernelSumBound : Set
    InterferenceBelowNonTargetDiagonal : Set
    sHToComplexPhiKernelIdentification : SHToComplexPhiKernelIdentification
    offDiagonalPhiKernelDecay : OffDiagonalPhiKernelDecay
    pairwiseKernelSumBound : PairwiseKernelSumBound
    interferenceBelowNonTargetDiagonal : InterferenceBelowNonTargetDiagonal

------------------------------------------------------------------------
-- G3: PRIME-SIDE NORMALIZED EXCESS
--
-- Existing source owns the raw second-trace asymptotic and explicit error
-- scale.  What it does NOT source-own is the new statement that, after
-- subtracting the critical-compatible main term, the remainder is exactly the
-- retained Hermitian transverse excess constructed by G1/G2.
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
-- Existing connections are three partial routes, not three completed proofs:
--   localization: windows/tails already exist, but not arbitrary pair isolation;
--   amplification: DASHI owns exact scalar power residual amplification, but
--                  the source does not thereby own higher trace estimates;
--   rigidity: functional-equation reflection is owned, but there is no proved
--             zero <-> Satake/unitarity identification.
--
-- The common target of every route is the SAME strict inequality/certificate:
--       targetPairDefect > arithmeticErrorBudget.
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

------------------------------------------------------------------------
-- FIRST-GAP SUMMARY.  These Booleans describe the audit, not theorem evidence;
-- all theorem-bearing producer fields stay in the records above.
------------------------------------------------------------------------

record HermitianSourceGapBoundary : Set where
  field
    realPoissonSourceOwned : Bool
    complexPhiHatStripDecaySourceOwned : Bool
    sourceZeroTailOwned : Bool
    complexHermitianPoissonStillNew : Bool
    mixedLossKernelReductionOwned : Bool
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
  { realPoissonSourceOwned = true
  ; complexPhiHatStripDecaySourceOwned = true
  ; sourceZeroTailOwned = true
  ; complexHermitianPoissonStillNew = true
  ; mixedLossKernelReductionOwned = true
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
