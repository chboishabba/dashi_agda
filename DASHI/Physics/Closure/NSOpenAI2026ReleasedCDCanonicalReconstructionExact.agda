module DASHI.Physics.Closure.NSOpenAI2026ReleasedCDCanonicalReconstructionExact where

------------------------------------------------------------------------
-- RELEASED C/D -> CANONICAL LITERAL C/D RECONSTRUCTION COMPILERS
--
-- The external released theorem is not re-proved here.  This owner closes the
-- INTERNAL semantic ambiguity identified in the four-lane audit:
--
--   a released theorem may inhabit literal Clay C/D only after its concrete
--   field, forcing, regularity/decay predicates, PDE semantics, and no-global-
--   solution conclusion have been transported to the canonical R^3 field
--   types from NSCanonicalEuclideanPeriodicSemanticCarriersExact.
--
-- The records below are deliberately exact same-object reconstruction
-- obligations.  Once populated from the released development, the compilers
-- produce the literal NSClayLiteralABCDExact C/D witnesses without any freedom
-- to redefine the carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import Real as BishopReal

import DASHI.Physics.Closure.NSClayLiteralABCDExact as Clay
import DASHI.Physics.Closure.NSCanonicalEuclideanPeriodicSemanticCarriersExact as Canonical
import DASHI.Physics.Closure.NSOpenAI2026ComparatorClayCDSourceExactAlignment as Source

------------------------------------------------------------------------
-- C / whole-space forced breakdown.
------------------------------------------------------------------------

record ReleasedCanonicalCReconstruction
    (S : Canonical.CanonicalNSSemantics)
    (viscosity : BishopReal.ℝ) : Set₁ where
  field
    initial : Canonical.SpatialVectorField
    forcing : Canonical.ForcingHistory

    initialSmooth : Canonical.SmoothSpatialVector S initial
    initialDivergenceFree : Canonical.DivergenceFreeSpatial S initial
    initialRapidDecay : Canonical.RapidSpatialDecay S initial

    forcingSmooth : Canonical.SmoothForcingHistory S forcing
    forcingRapidSpaceTimeDecay :
      Canonical.RapidSpaceTimeDecay S forcing

    noGlobalBoundedEnergySmoothSolution :
      Clay.FeffermanEuclideanForcedGlobalSolution
        (Canonical.canonicalEuclideanC S)
        viscosity initial forcing → ⊥

open ReleasedCanonicalCReconstruction public

compileReleasedCanonicalC :
  (S : Canonical.CanonicalNSSemantics) →
  (viscosity : BishopReal.ℝ) →
  ReleasedCanonicalCReconstruction S viscosity →
  Clay.FeffermanEuclideanForcedBreakdownWitness
    (Canonical.canonicalEuclideanC S) viscosity
compileReleasedCanonicalC S viscosity R = record
  { Clay.initialC = initial R
  ; Clay.forcingC = forcing R
  ; Clay.initialSmoothC = initialSmooth R
  ; Clay.initialDivergenceFreeC = initialDivergenceFree R
  ; Clay.initialRapidDecayC = initialRapidDecay R
  ; Clay.forcingSmoothC = forcingSmooth R
  ; Clay.forcingRapidDecayC = forcingRapidSpaceTimeDecay R
  ; Clay.noGlobalBoundedEnergySmoothSolutionC =
      noGlobalBoundedEnergySmoothSolution R
  }

releasedCanonicalCStatement :
  (S : Canonical.CanonicalNSSemantics) →
  ((viscosity : BishopReal.ℝ) →
    Canonical.PositiveReal S viscosity →
    ReleasedCanonicalCReconstruction S viscosity) →
  Clay.FeffermanEuclideanClayStatementC
    (Canonical.canonicalEuclideanC S)
releasedCanonicalCStatement S reconstruct viscosity viscosityPositive =
  compileReleasedCanonicalC S viscosity
    (reconstruct viscosity viscosityPositive)

------------------------------------------------------------------------
-- D / periodic forced breakdown.
------------------------------------------------------------------------

record ReleasedCanonicalDReconstruction
    (S : Canonical.CanonicalNSSemantics)
    (viscosity : BishopReal.ℝ) : Set₁ where
  field
    initial : Canonical.SpatialVectorField
    forcing : Canonical.ForcingHistory

    initialSmooth : Canonical.SmoothSpatialVector S initial
    initialDivergenceFree : Canonical.DivergenceFreeSpatial S initial
    initialPeriodic : Canonical.UnitPeriodicSpatialVector S initial

    forcingSmooth : Canonical.SmoothForcingHistory S forcing
    forcingPeriodic : Canonical.UnitPeriodicForcing S forcing
    forcingRapidTimeDecay :
      Canonical.RapidTimeDecayAllForcingDerivatives S forcing

    noGlobalSmoothPeriodicSolution :
      Clay.FeffermanPeriodicForcedGlobalSolution
        (Canonical.canonicalPeriodicD S)
        viscosity initial forcing → ⊥

open ReleasedCanonicalDReconstruction public

compileReleasedCanonicalD :
  (S : Canonical.CanonicalNSSemantics) →
  (viscosity : BishopReal.ℝ) →
  ReleasedCanonicalDReconstruction S viscosity →
  Clay.FeffermanPeriodicForcedBreakdownWitness
    (Canonical.canonicalPeriodicD S) viscosity
compileReleasedCanonicalD S viscosity R = record
  { Clay.initialD = ReleasedCanonicalDReconstruction.initial R
  ; Clay.forcingD = ReleasedCanonicalDReconstruction.forcing R
  ; Clay.initialSmoothD = ReleasedCanonicalDReconstruction.initialSmooth R
  ; Clay.initialDivergenceFreeD =
      ReleasedCanonicalDReconstruction.initialDivergenceFree R
  ; Clay.initialPeriodicD = initialPeriodic R
  ; Clay.forcingSmoothD = ReleasedCanonicalDReconstruction.forcingSmooth R
  ; Clay.forcingPeriodicD = forcingPeriodic R
  ; Clay.forcingRapidTimeDecayD = forcingRapidTimeDecay R
  ; Clay.noGlobalSmoothPeriodicSolutionD =
      noGlobalSmoothPeriodicSolution R
  }

releasedCanonicalDStatement :
  (S : Canonical.CanonicalNSSemantics) →
  ((viscosity : BishopReal.ℝ) →
    Canonical.PositiveReal S viscosity →
    ReleasedCanonicalDReconstruction S viscosity) →
  Clay.FeffermanPeriodicClayStatementD
    (Canonical.canonicalPeriodicD S)
releasedCanonicalDStatement S reconstruct viscosity viscosityPositive =
  compileReleasedCanonicalD S viscosity
    (reconstruct viscosity viscosityPositive)

------------------------------------------------------------------------
-- Source alignment is a prerequisite, not a theorem inhabitant.
------------------------------------------------------------------------

releasedSourceAlignmentAvailable : Bool
releasedSourceAlignmentAvailable = true

canonicalCReconstructionCompilerClosed : Bool
canonicalCReconstructionCompilerClosed = true

canonicalDReconstructionCompilerClosed : Bool
canonicalDReconstructionCompilerClosed = true

releasedCConcreteSameObjectMapClosedHere : Bool
releasedCConcreteSameObjectMapClosedHere = false

releasedDConcreteSameObjectMapClosedHere : Bool
releasedDConcreteSameObjectMapClosedHere = false

externalLeanTheoremAutomaticallyBecomesAgdaProof : Bool
externalLeanTheoremAutomaticallyBecomesAgdaProof = false

clayPromotion : Bool
clayPromotion = false

canonicalCReconstructionCompilerClosedIsTrue :
  canonicalCReconstructionCompilerClosed ≡ true
canonicalCReconstructionCompilerClosedIsTrue = refl

canonicalDReconstructionCompilerClosedIsTrue :
  canonicalDReconstructionCompilerClosed ≡ true
canonicalDReconstructionCompilerClosedIsTrue = refl

externalLeanTheoremAutomaticallyBecomesAgdaProofIsFalse :
  externalLeanTheoremAutomaticallyBecomesAgdaProof ≡ false
externalLeanTheoremAutomaticallyBecomesAgdaProofIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
