{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayGoal1NontrivialityAttachmentRound468Exact where

------------------------------------------------------------------------
-- GOAL-1 G2 / ROUND468:
-- SAME-SYSTEM GAUSSIAN/WARD/GAP CONTRADICTION -> LITERAL CLAY T5 SEMANTICS.
--
-- Round77 already proves the mathematical reductio:
--
--   same-family local Ward kernel under Gaussianity
--       -> exact Maxwell quadratic classification
--       -> standard gauge-invariant gapless Maxwell composite sector
--   + positive gap on the SAME reconstructed H
--       -> contradiction
--       -> InteractingContinuumWitness.
--
-- The top-down Clay compiler, however, consumes opaque semantic predicates
--   IsNontrivialQuantumYangMills
--   NontrivialityPreservedInLimit.
--
-- This module isolates exactly that final semantic interpretation.  It does not
-- introduce a new fourth cumulant, a new Hamiltonian, or another nontriviality
-- estimate.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS
import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound77FiveAnalyticCutsetExact as R77
import DASHI.Physics.YangMills.YangMillsContinuumOPEStressWardGaussianKernelExact as Local
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayTopDownFiveTheoremClosureExact as Five

record Goal1NontrivialitySemanticAttachment
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    : Set₂ where
  field
    Observable Point Scalar : Set

    systemFor :
      Top.CompactSimpleGroup C →
      OS.ContinuumSchwingerSystem Observable Point Scalar

    ContinuumFamily CurvaturePolynomial LocalOperator Position
      OPECoefficient StressTensor Hamiltonian : Set

    localPackage :
      ∀ G →
      Local.SameFamilyOPEStressWardGaussianKernel
        ContinuumFamily CurvaturePolynomial LocalOperator Position
        OPECoefficient StressTensor Hamiltonian Observable Point Scalar
        (systemFor G)

    sameHBridge :
      ∀ G →
      R77.StandardGaussianMaxwellSameHGapBridge (localPackage G)

    -- Same-object interpretation: the Round77 witness belongs to the literal
    -- continuum measure/Schwinger pair carried by Y for this G.
    interactingWitnessIsLiteralClayNontriviality :
      ∀ G →
      OS.InteractingContinuumWitness
        Observable Point Scalar (systemFor G) →
      Top.IsNontrivialQuantumYangMills S G
        (Top.continuumMeasure Y G)
        (Top.schwinger Y G)

    -- The same witness is obtained on the actual limiting system, hence the
    -- interaction/nontriviality property is not lost in the limit.
    interactingWitnessIsPreservedInLiteralLimit :
      ∀ G →
      OS.InteractingContinuumWitness
        Observable Point Scalar (systemFor G) →
      Top.NontrivialityPreservedInLimit S G
        (Top.continuumMeasure Y G)

open Goal1NontrivialitySemanticAttachment public

round77Witness :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S}
    (attachment : Goal1NontrivialitySemanticAttachment Y)
    G →
  OS.InteractingContinuumWitness
    (Observable attachment)
    (Point attachment)
    (Scalar attachment)
    (systemFor attachment G)
round77Witness attachment G =
  R77.round77InteractingWitnessFromLocalAndGap
    (localPackage attachment G)
    (sameHBridge attachment G)

asInteractingContinuumNontriviality :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  Goal1NontrivialitySemanticAttachment Y →
  Five.InteractingContinuumNontriviality Y
asInteractingContinuumNontriviality attachment = record
  { Five.InteractingContinuumNontriviality.nontrivialQuantumYangMills =
      λ G →
        interactingWitnessIsLiteralClayNontriviality
          attachment G (round77Witness attachment G)
  ; Five.InteractingContinuumNontriviality.nontrivialityPreservedInLimit =
      λ G →
        interactingWitnessIsPreservedInLiteralLimit
          attachment G (round77Witness attachment G)
  }

round468GaussianWardGapCompilerLevel : ProofLevel
round468GaussianWardGapCompilerLevel =
  R77.round77NontrivialityDependencyCompilerLevel

round468StandardGaussianSameHBridgeAuthorityLevel : ProofLevel
round468StandardGaussianSameHBridgeAuthorityLevel =
  R77.standardGaussianMaxwellSameHGapBridgeLevel

-- G2's remaining Goal-1 payment is now only the same-object interpretation of
-- the Round77 witness as the literal Y continuum system and its limit.
literalRound468SameSystemNontrivialitySemanticsLevel : ProofLevel
literalRound468SameSystemNontrivialitySemanticsLevel = conditional
