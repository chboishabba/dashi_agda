{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayMinimalH6NontrivialityRound550Exact where

------------------------------------------------------------------------
-- GOAL-1 / ROUND550:
-- H6 NONTRIVIALITY WITHOUT FULL C1-C4 ON THE CRITICAL PATH
--
-- The shortest same-system reductio consumes:
--
--   * the literal continuum Schwinger system;
--   * the SAME-H positive-gap package from B;
--   * a minimal Gaussian two-derivative Ward kernel on that system.
--
-- It does NOT consume the entire ContinuumLocalFieldOPEStressWard record.
-- Rich local curvature/OPE/stress closure remains required on the conservative
-- Clay existence layer, but is no longer a prerequisite for proving that the
-- SAME continuum theory is interacting/non-Gaussian.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayTopDownFiveTheoremClosureExact as Five
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS
import DASHI.Physics.YangMills.YangMillsMinimalWardGapNontrivialityRound549Exact as R549

record Goal1MinimalH6Bridge
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    (Observable Point Scalar : Set)
    : Set₂ where
  field
    system :
      Top.CompactSimpleGroup C →
      OS.ContinuumSchwingerSystem Observable Point Scalar

    minimalWardKernel :
      ∀ group →
      R549.MinimalSameFamilyGaussianWardKernel (system group)

    sameHGapBridge :
      Five.CutoffUniformPhysicalMassGap Y →
      ∀ group →
      R549.MinimalSameHGapBridge (minimalWardKernel group)

    interactingWitnessIsLiteralNontrivial :
      ∀ gap group →
      OS.InteractingContinuumWitness
        Observable Point Scalar
        (system group) →
      Top.IsNontrivialQuantumYangMills S group
        (Top.continuumMeasure Y group)
        (Top.schwinger Y group)

    interactingWitnessPreservedInLiteralLimit :
      ∀ gap group →
      OS.InteractingContinuumWitness
        Observable Point Scalar
        (system group) →
      Top.NontrivialityPreservedInLimit S group
        (Top.continuumMeasure Y group)

open Goal1MinimalH6Bridge public

minimalSameSystemInteractingWitness :
  ∀ {C S Y Observable Point Scalar}
    (bridge :
      Goal1MinimalH6Bridge
        {C = C} {S = S} Y Observable Point Scalar)
    (gap : Five.CutoffUniformPhysicalMassGap Y)
    group →
  OS.InteractingContinuumWitness
    Observable Point Scalar
    (system bridge group)
minimalSameSystemInteractingWitness bridge gap group =
  R549.minimalInteractingWitness
    (minimalWardKernel bridge group)
    (sameHGapBridge bridge gap group)

deriveMinimalInteractingContinuumNontriviality :
  ∀ {C S Y Observable Point Scalar} →
  Goal1MinimalH6Bridge
    {C = C} {S = S} Y Observable Point Scalar →
  Five.CutoffUniformPhysicalMassGap Y →
  Five.InteractingContinuumNontriviality Y
deriveMinimalInteractingContinuumNontriviality bridge gap = record
  { Five.InteractingContinuumNontriviality.nontrivialQuantumYangMills =
      λ group →
        interactingWitnessIsLiteralNontrivial
          bridge gap group
          (minimalSameSystemInteractingWitness bridge gap group)
  ; Five.InteractingContinuumNontriviality.nontrivialityPreservedInLimit =
      λ group →
        interactingWitnessPreservedInLiteralLimit
          bridge gap group
          (minimalSameSystemInteractingWitness bridge gap group)
  }

round550MinimalH6CompilerLevel : ProofLevel
round550MinimalH6CompilerLevel =
  R549.round549MinimalNontrivialityCompilerLevel

round550FullLocalOPEStressRecordRequiredForNontriviality : Agda.Builtin.Bool.Bool
round550FullLocalOPEStressRecordRequiredForNontriviality = Agda.Builtin.Bool.false

-- The physical local input is now the narrow same-family Ward-kernel theorem.
literalRound550MinimalWardKernelLevel : ProofLevel
literalRound550MinimalWardKernelLevel =
  R549.literalRound549MinimalSameFamilyWardKernelLevel
