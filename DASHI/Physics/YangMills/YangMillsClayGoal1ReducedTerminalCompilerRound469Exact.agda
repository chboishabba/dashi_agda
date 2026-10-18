{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayGoal1ReducedTerminalCompilerRound469Exact where

------------------------------------------------------------------------
-- GOAL-1 / ROUND469: REDUCED TERMINAL CLAY COMPILER.
--
-- After R454--R468, three of the five top-down theorem roles have preferred
-- modern adapters:
--
--   T2 mass gap        <- R458 same-object gap semantics
--   T4 local QFT       <- R437 same-completed-state local source
--   T5 nontriviality   <- R468 same-system Gaussian/Ward/gap semantics
--
-- T1 finite weak-coupling RG and T3 continuum/OS remain explicit because they
-- contain the genuine global construction/source instantiations.
--
-- This module proves that NOTHING ELSE is needed downstream: once T1/T3 and
-- those three modern attachments are inhabited on one literal Y, the exact
-- ClayYangMillsSolution follows mechanically.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayProblemContractExact as Clay
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayTopDownFiveTheoremClosureExact as Five
import DASHI.Physics.YangMills.YangMillsClayGoal1MassGapSemanticAttachmentRound458Exact as R458
import DASHI.Physics.YangMills.YangMillsClayGoal1CanonicalCSourceRound437Exact as R437
import DASHI.Physics.YangMills.YangMillsClayGoal1NontrivialityAttachmentRound468Exact as R468

record ReducedGoal1TerminalInputs
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S) : Set₂ where
  field
    structural : Five.LiteralClayStructuralBase Y

    -- T1 remains a real construction theorem.
    weakCouplingRG : Five.LiteralWeakCouplingRGConstruction Y

    -- T3 remains the common continuum/OS theorem.
    continuum : Five.UnifiedContinuumYMConstruction Y

    -- Modern adapters for T2/T4/T5.
    massGapAttachment : R458.Goal1MassGapSemanticAttachment Y
    localSource : R437.Goal1CanonicalCSource Y
    nontrivialityAttachment : R468.Goal1NontrivialitySemanticAttachment Y

open ReducedGoal1TerminalInputs public

physicalMassGap :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  ReducedGoal1TerminalInputs Y →
  Five.CutoffUniformPhysicalMassGap Y
physicalMassGap inputs =
  R458.asCutoffUniformPhysicalMassGap (massGapAttachment inputs)

localQFT :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  ReducedGoal1TerminalInputs Y →
  Five.ContinuumLocalFieldOPEStressWard Y
localQFT inputs =
  R437.asContinuumLocalFieldOPEStressWard (localSource inputs)

interacting :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  ReducedGoal1TerminalInputs Y →
  Five.InteractingContinuumNontriviality Y
interacting inputs =
  R468.asInteractingContinuumNontriviality
    (nontrivialityAttachment inputs)

literalClayEvidence :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  ReducedGoal1TerminalInputs Y →
  Top.LiteralClayEvidence Y
literalClayEvidence {Y = Y} inputs =
  Five.literalClayEvidenceFromFiveTheorems
    Y
    (structural inputs)
    (weakCouplingRG inputs)
    (physicalMassGap inputs)
    (continuum inputs)
    (localQFT inputs)
    (interacting inputs)

literalClaySolution :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  ReducedGoal1TerminalInputs Y →
  Clay.ClayYangMillsSolution (Top.literalClayVocabulary Y)
literalClaySolution {Y = Y} inputs =
  Five.literalClaySolutionFromFiveTheorems
    Y
    (structural inputs)
    (weakCouplingRG inputs)
    (physicalMassGap inputs)
    (continuum inputs)
    (localQFT inputs)
    (interacting inputs)

round469ReducedTerminalCompilerLevel : ProofLevel
round469ReducedTerminalCompilerLevel = machineChecked

-- There is no further terminal proof obligation after this record is inhabited.
-- All remaining debt lies in the physical/source construction of its fields.
literalRound469ReducedTerminalInstantiationLevel : ProofLevel
literalRound469ReducedTerminalInstantiationLevel = conditional
