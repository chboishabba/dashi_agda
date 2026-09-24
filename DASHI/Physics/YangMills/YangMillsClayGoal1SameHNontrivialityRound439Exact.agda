{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayGoal1SameHNontrivialityRound439Exact where

------------------------------------------------------------------------
-- GOAL 1 / ROUND439: MAKE THE ROUND78 NONTRIVIALITY CONSEQUENCE CONCRETE
--
-- Round78 packages nontriviality as a "standard same-H consequence".  The repo
-- already contains the actual logical/spectral proof in Round77:
--
--   SAME-family local Gaussian Ward kernel
--     -> exact Maxwell coefficient classification
--     -> gauge-invariant gapless Maxwell composite sector
--   SAME reconstructed H has positive gap
--     -> contradiction
--     -> non-Gaussian/interacting witness.
--
-- This owner wires that exact theorem into Round78.  The only remaining
-- semantic seam is interpreting the resulting same-system interacting witness
-- as the literal Clay predicates IsNontrivialQuantumYangMills and
-- NontrivialityPreservedInLimit.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayTopDownFiveTheoremClosureExact as Five
import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound78TopDownThreeAnalyticFrontierExact as R78
import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound77FiveAnalyticCutsetExact as R77
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS
import DASHI.Physics.YangMills.YangMillsContinuumOPEStressWardGaussianKernelExact as Local

record Goal1SameHNontrivialityBridge
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    (ContinuumFamily Observable Point Scalar : Set)
    : Set₂ where
  field
    system :
      Top.CompactSimpleGroup C →
      OS.ContinuumSchwingerSystem Observable Point Scalar

    localPackageFromC :
      Five.CutoffUniformPhysicalMassGap Y →
      Five.ContinuumLocalFieldOPEStressWard Y →
      ∀ group →
      Local.SameFamilyOPEStressWardGaussianKernel
        ContinuumFamily
        (Top.CurvaturePolynomial C)
        (Top.LocalOperator C)
        (Top.Position C)
        (Top.OPECoefficient C)
        (Top.StressTensor C)
        (Top.Hamiltonian C)
        Observable Point Scalar
        (system group)

    sameHBridgeFromB :
      (gap : Five.CutoffUniformPhysicalMassGap Y) →
      (local : Five.ContinuumLocalFieldOPEStressWard Y) →
      ∀ group →
      R77.StandardGaussianMaxwellSameHGapBridge
        (localPackageFromC gap local group)

    interactingWitnessIsLiteralNontrivial :
      ∀ gap local group →
      OS.InteractingContinuumWitness
        Observable Point Scalar
        (system group) →
      Top.IsNontrivialQuantumYangMills S group
        (Top.continuumMeasure Y group)
        (Top.schwinger Y group)

    interactingWitnessPreservedInLiteralLimit :
      ∀ gap local group →
      OS.InteractingContinuumWitness
        Observable Point Scalar
        (system group) →
      Top.NontrivialityPreservedInLimit S group
        (Top.continuumMeasure Y group)

open Goal1SameHNontrivialityBridge public

interactingWitness :
  ∀ {C S Y ContinuumFamily Observable Point Scalar}
    (bridge :
      Goal1SameHNontrivialityBridge
        {C = C} {S = S} Y
        ContinuumFamily Observable Point Scalar)
    (gap : Five.CutoffUniformPhysicalMassGap Y)
    (local : Five.ContinuumLocalFieldOPEStressWard Y)
    group →
  OS.InteractingContinuumWitness
    Observable Point Scalar
    (system bridge group)
interactingWitness bridge gap local group =
  R77.round77InteractingWitnessFromLocalAndGap
    (localPackageFromC bridge gap local group)
    (sameHBridgeFromB bridge gap local group)

deriveInteracting :
  ∀ {C S Y ContinuumFamily Observable Point Scalar} →
  Goal1SameHNontrivialityBridge
    {C = C} {S = S} Y
    ContinuumFamily Observable Point Scalar →
  Five.CutoffUniformPhysicalMassGap Y →
  Five.ContinuumLocalFieldOPEStressWard Y →
  Five.InteractingContinuumNontriviality Y
deriveInteracting bridge gap local = record
  { Five.InteractingContinuumNontriviality.nontrivialQuantumYangMills =
      λ group →
        interactingWitnessIsLiteralNontrivial bridge
          gap local group
          (interactingWitness bridge gap local group)
  ; Five.InteractingContinuumNontriviality.nontrivialityPreservedInLimit =
      λ group →
        interactingWitnessPreservedInLiteralLimit bridge
          gap local group
          (interactingWitness bridge gap local group)
  }

asRound78StandardSameHConsequence :
  ∀ {C S Y ContinuumFamily Observable Point Scalar} →
  Goal1SameHNontrivialityBridge
    {C = C} {S = S} Y
    ContinuumFamily Observable Point Scalar →
  R78.StandardSameHGaussianNontrivialityConsequence Y
asRound78StandardSameHConsequence bridge = record
  { R78.StandardSameHGaussianNontrivialityConsequence.deriveInteracting =
      deriveInteracting bridge
  }

round439GaussianWardGapContradictionCompilerLevel : ProofLevel
round439GaussianWardGapContradictionCompilerLevel =
  R77.round77NontrivialityDependencyCompilerLevel

round439Round78NontrivialityCompilerLevel : ProofLevel
round439Round78NontrivialityCompilerLevel = machineChecked

-- G2 is no longer an opaque fourth analytic theorem.  The open Goal-1 content
-- is the SAME-system semantic bridge:
-- * C under a Gaussian hypothesis really supplies the local Ward kernel;
-- * B's positive gap is on that exact reconstructed H/physical sector;
-- * the resulting interacting witness has the literal Clay nontriviality
--   semantics on Y.
literalRound439SameSystemSemanticBridgeLevel : ProofLevel
literalRound439SameSystemSemanticBridgeLevel = conditional
