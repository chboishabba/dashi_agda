module DASHI.Physics.YangMills.BalabanContinuumOSLimit where

------------------------------------------------------------------------
-- Continuum Osterwalder--Schrader limit.
--
-- The cutoff family, convergence topology, and closure of OS0--OS5 are kept
-- distinct.  Once the cutoff axioms and the corresponding closure theorems are
-- supplied, the continuum Schwinger system is assembled without importing the
-- desired conclusion as a single field.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OSGap

record SchwingerLimitProblem
    (Cutoff Observable Point Scalar : Set) : Set₁ where
  field
    cutoffSchwinger : Cutoff → Observable → Point → Point → Scalar
    continuumSchwinger : Observable → Point → Point → Scalar

    ConvergesToContinuum : Set
    convergesToContinuum : ConvergesToContinuum

    OS0AtCutoff : Cutoff → Set
    OS1AtCutoff : Cutoff → Set
    OS2AtCutoff : Cutoff → Set
    OS3AtCutoff : Cutoff → Set
    OS4AtCutoff : Cutoff → Set
    OS5AtCutoff : Cutoff → Set

    cutoffOS0 : ∀ cutoff → OS0AtCutoff cutoff
    cutoffOS1 : ∀ cutoff → OS1AtCutoff cutoff
    cutoffOS2 : ∀ cutoff → OS2AtCutoff cutoff
    cutoffOS3 : ∀ cutoff → OS3AtCutoff cutoff
    cutoffOS4 : ∀ cutoff → OS4AtCutoff cutoff
    cutoffOS5 : ∀ cutoff → OS5AtCutoff cutoff

    OS0AtLimit : Set
    OS1AtLimit : Set
    OS2AtLimit : Set
    OS3AtLimit : Set
    OS4AtLimit : Set
    OS5AtLimit : Set

open SchwingerLimitProblem public

record OSAxiomsClosedUnderLimit
    {Cutoff Observable Point Scalar : Set}
    (problem : SchwingerLimitProblem Cutoff Observable Point Scalar) : Set₁ where
  field
    os0Closed : ConvergesToContinuum problem →
      (∀ cutoff → OS0AtCutoff problem cutoff) → OS0AtLimit problem
    os1Closed : ConvergesToContinuum problem →
      (∀ cutoff → OS1AtCutoff problem cutoff) → OS1AtLimit problem
    os2Closed : ConvergesToContinuum problem →
      (∀ cutoff → OS2AtCutoff problem cutoff) → OS2AtLimit problem
    os3Closed : ConvergesToContinuum problem →
      (∀ cutoff → OS3AtCutoff problem cutoff) → OS3AtLimit problem
    os4Closed : ConvergesToContinuum problem →
      (∀ cutoff → OS4AtCutoff problem cutoff) → OS4AtLimit problem
    os5Closed : ConvergesToContinuum problem →
      (∀ cutoff → OS5AtCutoff problem cutoff) → OS5AtLimit problem

open OSAxiomsClosedUnderLimit public

continuumOSFromLimit :
  ∀ {Cutoff Observable Point Scalar : Set} →
  (problem : SchwingerLimitProblem Cutoff Observable Point Scalar) →
  OSAxiomsClosedUnderLimit problem →
  OSGap.ContinuumSchwingerSystem Observable Point Scalar
continuumOSFromLimit problem closure = record
  { schwinger = continuumSchwinger problem
  ; OS0Regularity = OS0AtLimit problem
  ; OS1EuclideanCovariance = OS1AtLimit problem
  ; OS2ReflectionPositivity = OS2AtLimit problem
  ; OS3PermutationSymmetry = OS3AtLimit problem
  ; OS4Clustering = OS4AtLimit problem
  ; OS5GrowthControl = OS5AtLimit problem
  ; os0 = os0Closed closure
      (convergesToContinuum problem) (cutoffOS0 problem)
  ; os1 = os1Closed closure
      (convergesToContinuum problem) (cutoffOS1 problem)
  ; os2 = os2Closed closure
      (convergesToContinuum problem) (cutoffOS2 problem)
  ; os3 = os3Closed closure
      (convergesToContinuum problem) (cutoffOS3 problem)
  ; os4 = os4Closed closure
      (convergesToContinuum problem) (cutoffOS4 problem)
  ; os5 = os5Closed closure
      (convergesToContinuum problem) (cutoffOS5 problem)
  }

continuumOSLimitAssemblyLevel : ProofLevel
continuumOSLimitAssemblyLevel = machineChecked

osAxiomLimitClosureAuthorityLevel : ProofLevel
osAxiomLimitClosureAuthorityLevel = standardImported

continuumSchwingerConvergenceInputsLevel : ProofLevel
continuumSchwingerConvergenceInputsLevel = conjectural
