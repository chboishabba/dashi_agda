module DASHI.Physics.Closure.NSTriadKNPhysicalSpectralFrontier where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_; _<_; _*_)

------------------------------------------------------------------------
-- Finite exact reconnaissance and the cutoff-uniform theorem are separate.
------------------------------------------------------------------------

record FiniteExactSpectralExperiment : Set₁ where
  constructor finite-exact-spectral-experiment
  field
    cutoff : Nat
    Index : Set
    matrixEntry : Index → Index → Nat
    CandidateState : Set
    quadraticForm : CandidateState → Nat
    exactFiniteUpperBound : Nat
    finiteBoundCertified :
      (state : CandidateState) →
      quadraticForm state ≤ exactFiniteUpperBound

open FiniteExactSpectralExperiment public

record UniformPhysicalSpectralGap : Set₁ where
  constructor uniform-physical-spectral-gap
  field
    Cutoff State : Set
    scaleSquare : Cutoff → Nat

    qBase qError strongNormSquared :
      Cutoff → State → Nat

    baseConstant errorConstant : Nat

    baseCoercive :
      (N : Cutoff) → (state : State) →
      baseConstant * strongNormSquared N state
      ≤ scaleSquare N * qBase N state

    errorControlled :
      (N : Cutoff) → (state : State) →
      scaleSquare N * qError N state
      ≤ errorConstant * strongNormSquared N state

    strictConstantGap : errorConstant < baseConstant

    CutoffUniform : Set
    cutoffUniform : CutoffUniform

open UniformPhysicalSpectralGap public

record PhysicalSpectralGapHandoff : Set₁ where
  constructor physical-spectral-gap-handoff
  field
    gap : UniformPhysicalSpectralGap
    exactPhysicalKernelUsed : Set
    kernelIdentificationProof : exactPhysicalKernelUsed

open PhysicalSpectralGapHandoff public

finiteExactSpectralExperimentInterfaceImplemented : Bool
finiteExactSpectralExperimentInterfaceImplemented = true

finiteExactSpectralExperimentInterfaceImplementedIsTrue :
  finiteExactSpectralExperimentInterfaceImplemented ≡ true
finiteExactSpectralExperimentInterfaceImplementedIsTrue = refl

uniformPhysicalSpectralGapClosed : Bool
uniformPhysicalSpectralGapClosed = false

uniformPhysicalSpectralGapClosedIsFalse :
  uniformPhysicalSpectralGapClosed ≡ false
uniformPhysicalSpectralGapClosedIsFalse = refl

exactPhysicalKernelToSpectralGapHandoffClosed : Bool
exactPhysicalKernelToSpectralGapHandoffClosed = false

exactPhysicalKernelToSpectralGapHandoffClosedIsFalse :
  exactPhysicalKernelToSpectralGapHandoffClosed ≡ false
exactPhysicalKernelToSpectralGapHandoffClosedIsFalse = refl
