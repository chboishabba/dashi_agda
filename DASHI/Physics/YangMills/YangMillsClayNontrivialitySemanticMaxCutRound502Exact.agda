{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayNontrivialitySemanticMaxCutRound502Exact where

------------------------------------------------------------------------
-- GOAL-1 G2 / ROUND502: NONTRIVIALITY SEMANTIC MAX-CUT
--
-- Round77 already constructs the interacting witness.  R468's remaining
-- literal endpoint interpretation consists of two independent predicates:
--
--   N1 witness -> IsNontrivialQuantumYangMills on the literal same system;
--   N2 witness -> NontrivialityPreservedInLimit on that same limit.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayGoal1NontrivialityAttachmentRound468Exact as R468

round502GaussianWardGapCompilerLevel : ProofLevel
round502GaussianWardGapCompilerLevel =
  R468.round468GaussianWardGapCompilerLevel

literalRound502WitnessIsLiteralNontrivialityLevel : ProofLevel
literalRound502WitnessIsLiteralNontrivialityLevel = conditional

literalRound502WitnessPreservedInLiteralLimitLevel : ProofLevel
literalRound502WitnessPreservedInLiteralLimitLevel = conditional
