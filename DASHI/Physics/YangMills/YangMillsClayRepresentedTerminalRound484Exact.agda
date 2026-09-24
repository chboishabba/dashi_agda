{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayRepresentedTerminalRound484Exact where

------------------------------------------------------------------------
-- GOAL-1 / ROUND484: REPRESENTATION-FIRST TERMINAL CLAY COMPILER
--
-- R469 proves that structural + T1 + T3 + modern T2/T4/T5 attachments suffice
-- for the literal Clay endpoint.  R483 makes the literal construction itself
-- representation-first.  This owner composes them: the terminal Clay solution
-- is therefore built on continuum objects that originate in actual represented
-- countably-additive measures for every G.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayProblemContractExact as Clay
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsClayRepresentedLiteralConstructionRound483Exact as R483
import DASHI.Physics.YangMills.YangMillsClayGoal1ReducedTerminalCompilerRound469Exact as R469

record RepresentedTerminalInputs
    (G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient StressTensor Hilbert Hamiltonian Vacuum : Set)
    (S :
      Top.LiteralYangMillsSemantics
        (Physical.physicalLiteralCarriers
          G X Agda.Builtin.Nat.Nat Configuration
          DASHI.Foundations.RealAnalysisAxioms.ℝ
          (Configuration → DASHI.Foundations.RealAnalysisAxioms.ℝ)
          Position CurvaturePolynomial LocalOperator OPECoefficient StressTensor
          Hilbert Hamiltonian Vacuum))
    : Set₂ where
  field
    representedConstruction :
      R483.RepresentedLiteralYMConstruction
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum S

    terminal :
      R469.ReducedGoal1TerminalInputs
        (R483.asLiteralConstruction representedConstruction)

open RepresentedTerminalInputs public

literalClaySolution :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum S} →
  (inputs :
    RepresentedTerminalInputs
      G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum S) →
  Clay.ClayYangMillsSolution
    (Top.literalClayVocabulary
      (R483.asLiteralConstruction
        (representedConstruction inputs)))
literalClaySolution inputs =
  R469.literalClaySolution (terminal inputs)

round484RepresentedTerminalCompilerLevel : ProofLevel
round484RepresentedTerminalCompilerLevel = machineChecked

bareExpectationFunctionalTerminalRequired : Bool
bareExpectationFunctionalTerminalRequired = false

independentContinuumAndSchwingerChoicesRequired : Bool
independentContinuumAndSchwingerChoicesRequired = false
