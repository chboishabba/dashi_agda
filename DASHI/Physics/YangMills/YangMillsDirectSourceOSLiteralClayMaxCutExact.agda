{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsDirectSourceOSLiteralClayMaxCutExact where

------------------------------------------------------------------------
-- DIRECT SOURCE -> OS -> LITERAL CLAY MAX-CUT
--
-- This is the endpoint-facing composition corresponding to the direct-source
-- manuscript and the current R467/R474 max-cut.  It deliberately does NOT
-- resurrect the historical seven-family scheduler.
--
-- H1  lives upstream in R467: literal published selected CMP116 localization
--     plus physical source-envelope calibration.  The direct R467 -> transfer
--     gap compiler is BalabanCMP116PublishedLiteralSelectedGapExact.
--
-- H2+H3 are represented here by ONE LiteralContinuumSameObjectBridge:
--     actual finite-family continuum construction
--       + literal Schwinger identity
--       + accepted OS axioms
--       + reconstructed Hilbert/Hamiltonian SAME-OBJECT weld.
--
-- H5 is enforced by the endpoint's all-G structural/finite-RG objects: there is
-- no SU(2)-to-all-G promotion step in this compiler.
--
-- H6 is the same-system Round77 nontriviality attachment.
--
-- The literal Clay contract additionally asks for local curvature/OPE/stress
-- semantics.  These are supplied by the current minimal same-family local
-- source owner rather than conflated with the mass-gap min-cut.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayProblemContractExact as Clay
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayTopDownFiveTheoremClosureExact as Five
import DASHI.Physics.YangMills.YMClayContinuumConstructionSameObjectBridgeExact as Continuum
import DASHI.Physics.YangMills.YangMillsClayGoal1MassGapSemanticAttachmentRound458Exact as H3Gap
import DASHI.Physics.YangMills.YangMillsClayGoal1CanonicalCSourceRound437Exact as Local
import DASHI.Physics.YangMills.YangMillsClayGoal1NontrivialityAttachmentRound468Exact as H6
import DASHI.Physics.YangMills.YangMillsClayGoal1ReducedTerminalCompilerRound469Exact as Terminal

record DirectSourceOSLiteralClayInputs
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    : Set₂ where
  field
    --------------------------------------------------------------------
    -- Structural/all-group endpoint data.
    --------------------------------------------------------------------
    structural :
      Five.LiteralClayStructuralBase Y

    --------------------------------------------------------------------
    -- Finite literal YM construction, quantified over the SAME compact-simple
    -- group carrier used by Y.  Current R472/A1/A2 source-first producers are
    -- the preferred way to inhabit this theorem; historical BC1/BC2 are not
    -- observed here.
    --------------------------------------------------------------------
    finiteRG :
      Five.LiteralWeakCouplingRGConstruction Y

    --------------------------------------------------------------------
    -- H2 + H3: one continuum family, one Schwinger family, one reconstructed H.
    --------------------------------------------------------------------
    continuumSameObject :
      Continuum.LiteralContinuumSameObjectBridge Y

    --------------------------------------------------------------------
    -- H1 -> H3 endpoint interpretation.
    --
    -- R467 + the direct R387 gap compiler supply the mathematical gap.
    -- This attachment says that that SAME gap is the literal Y Hamiltonian /
    -- vacuum / mass-gap object.  It contains no new clustering estimate.
    --------------------------------------------------------------------
    sameHamiltonianGap :
      H3Gap.Goal1MassGapSemanticAttachment Y

    --------------------------------------------------------------------
    -- Minimal endpoint local-QFT supplement.  OPE/stress is not counted as an
    -- extra mass-gap inequality, but the literal Clay contract observes it.
    --------------------------------------------------------------------
    localSameFamily :
      Local.Goal1CanonicalCSource Y

    --------------------------------------------------------------------
    -- H6: same continuum family + same reconstructed Hamiltonian.
    --------------------------------------------------------------------
    nontrivialSameSystem :
      H6.Goal1NontrivialitySemanticAttachment Y

open DirectSourceOSLiteralClayInputs public

compiledContinuum :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  DirectSourceOSLiteralClayInputs Y →
  Five.UnifiedContinuumYMConstruction Y
compiledContinuum inputs =
  Continuum.unifiedContinuumYMFromSameObjectBridge
    (continuumSameObject inputs)

compiledMassGap :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  DirectSourceOSLiteralClayInputs Y →
  Five.CutoffUniformPhysicalMassGap Y
compiledMassGap inputs =
  H3Gap.asCutoffUniformPhysicalMassGap
    (sameHamiltonianGap inputs)

compiledLocalQFT :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  DirectSourceOSLiteralClayInputs Y →
  Five.ContinuumLocalFieldOPEStressWard Y
compiledLocalQFT inputs =
  Local.asContinuumLocalFieldOPEStressWard
    (localSameFamily inputs)

compiledNontriviality :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  DirectSourceOSLiteralClayInputs Y →
  Five.InteractingContinuumNontriviality Y
compiledNontriviality inputs =
  H6.asInteractingContinuumNontriviality
    (nontrivialSameSystem inputs)

asReducedTerminalInputs :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  DirectSourceOSLiteralClayInputs Y →
  Terminal.ReducedGoal1TerminalInputs Y
asReducedTerminalInputs inputs = record
  { Terminal.ReducedGoal1TerminalInputs.structural =
      structural inputs
  ; Terminal.ReducedGoal1TerminalInputs.weakCouplingRG =
      finiteRG inputs
  ; Terminal.ReducedGoal1TerminalInputs.continuum =
      compiledContinuum inputs
  ; Terminal.ReducedGoal1TerminalInputs.massGapAttachment =
      sameHamiltonianGap inputs
  ; Terminal.ReducedGoal1TerminalInputs.localSource =
      localSameFamily inputs
  ; Terminal.ReducedGoal1TerminalInputs.nontrivialityAttachment =
      nontrivialSameSystem inputs
  }

literalClayEvidence :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  DirectSourceOSLiteralClayInputs Y →
  Top.LiteralClayEvidence Y
literalClayEvidence inputs =
  Terminal.literalClayEvidence
    (asReducedTerminalInputs inputs)

literalClaySolution :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  DirectSourceOSLiteralClayInputs Y →
  Clay.ClayYangMillsSolution (Top.literalClayVocabulary Y)
literalClaySolution inputs =
  Terminal.literalClaySolution
    (asReducedTerminalInputs inputs)

directSourceOSLiteralClayCompilerLevel : ProofLevel
directSourceOSLiteralClayCompilerLevel = machineChecked

-- This module is a compiler/max-cut, not an unconditional Clay claim.
-- Its fields are exactly the remaining physical same-object/construction
-- theorems on the one literal Y.
directSourceOSLiteralClayPhysicalInstantiationLevel : ProofLevel
directSourceOSLiteralClayPhysicalInstantiationLevel = conditional
