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
import DASHI.Physics.YangMills.YangMillsClayGoal1CanonicalCSourceRound437Exact as Local
import DASHI.Physics.YangMills.YangMillsClayGoal1NontrivialityAttachmentRound468Exact as H6

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
      H1H3.LiteralDirectSourceSameHMassGap Y

    --------------------------------------------------------------------
    -- H2(ii): the EXACT tests inside the H1/H3 package are literal bounded
    -- Wilson-cylinder products.  All three selected expectation limits are
    -- compiler output from this one presentation.
    --------------------------------------------------------------------
    selectedWilsonConvergence :
      ∀ G →
      H2Wilson.LiteralSelectedWilsonExpectationApplication
        (H1H3.forGroup sameHamiltonianGap G)

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
  H1H3.asCutoffUniformPhysicalMassGap
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
