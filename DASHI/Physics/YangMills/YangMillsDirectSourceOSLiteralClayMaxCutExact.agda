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
import DASHI.Physics.YangMills.YangMillsDirectSourceOSSameHGapExact as H1H3
import DASHI.Physics.YangMills.YangMillsDirectSourceOSSelectedWilsonH2Exact as H2Wilson
import DASHI.Physics.YangMills.YangMillsDirectSourceOSReconstructedSpectrumH3Exact as H3OS
import DASHI.Physics.YangMills.YangMillsDirectSourceOSCompactSimpleH5Exact as H5
import DASHI.Physics.YangMills.YangMillsClayGoal1CanonicalCSourceRound437Exact as Local
import DASHI.Physics.YangMills.YangMillsDirectSourceOSSameSystemH6Exact as H6

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
    -- H1 + H2(ii) + H3 + H5 on one all-group source theorem.
    --
    -- For each quantitative compact-simple package this continuation returns
    -- the ACTUAL literal R467 application, selected Wilson convergence
    -- presentation, and same-OS spectrum package.  Classification/package
    -- lookup then covers every literal endpoint G.
    --------------------------------------------------------------------
    compactSimpleDirectSource :
      H5.LiteralCompactSimpleDirectSourceContinuation Y

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
      H6.LiteralDirectSourceSameSystemNontriviality
        Y compactSimpleDirectSource

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
  H1H3.asCutoffUniformPhysicalMassGap
    (H5.sameHGapForEveryLiteralGroup
      (compactSimpleDirectSource inputs))

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

literalClayEvidence :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  DirectSourceOSLiteralClayInputs Y →
  Top.LiteralClayEvidence Y
literalClayEvidence {Y = Y} inputs =
  Five.literalClayEvidenceFromFiveTheorems
    Y
    (structural inputs)
    (finiteRG inputs)
    (compiledMassGap inputs)
    (compiledContinuum inputs)
    (compiledLocalQFT inputs)
    (compiledNontriviality inputs)

literalClaySolution :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  DirectSourceOSLiteralClayInputs Y →
  Clay.ClayYangMillsSolution (Top.literalClayVocabulary Y)
literalClaySolution {Y = Y} inputs =
  Five.literalClaySolutionFromFiveTheorems
    Y
    (structural inputs)
    (finiteRG inputs)
    (compiledMassGap inputs)
    (compiledContinuum inputs)
    (compiledLocalQFT inputs)
    (compiledNontriviality inputs)

directSourceOSLiteralClayCompilerLevel : ProofLevel
directSourceOSLiteralClayCompilerLevel = machineChecked

-- This module is a compiler/max-cut, not an unconditional Clay claim.
-- Its fields are exactly the remaining physical same-object/construction
-- theorems on the one literal Y.
directSourceOSLiteralClayPhysicalInstantiationLevel : ProofLevel
directSourceOSLiteralClayPhysicalInstantiationLevel = conditional
