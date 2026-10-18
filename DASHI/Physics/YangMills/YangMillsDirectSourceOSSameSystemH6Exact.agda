{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsDirectSourceOSSameSystemH6Exact where

------------------------------------------------------------------------
-- H6 SOURCE-FIRST: NONTRIVIALITY ON THE EXACT H3 OS SYSTEM.
--
-- Do not choose a second continuum Schwinger system for the Gaussian reductio.
-- For every literal compact-simple group, instantiate the existing Round77
-- local Ward / Gaussian / Maxwell contradiction on H3.sourceOSSystem from the
-- SAME H1/H2/H3/H5 package.
------------------------------------------------------------------------

open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayTopDownFiveTheoremClosureExact as Five
import DASHI.Physics.YangMills.YangMillsDirectSourceOSCompactSimpleH5Exact as H5
import DASHI.Physics.YangMills.YangMillsDirectSourceOSReconstructedSpectrumH3Exact as H3
import DASHI.Physics.YangMills.YangMillsDirectSourceOSRationalContinuumH2Exact as H2Continuum
import DASHI.Physics.YangMills.YangMillsContinuumOPEStressWardGaussianKernelExact as Local
import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound77FiveAnalyticCutsetExact as R77
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS

record LiteralDirectSourceSameSystemNontriviality
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    (source : H5.LiteralCompactSimpleDirectSourceContinuation Y)
    : Set₂ where
  field
    ContinuumFamily CurvaturePolynomial LocalOperator Position
      OPECoefficient StressTensor Hamiltonian : Set

    localPackageFromLiteralC :
      Five.CutoffUniformPhysicalMassGap Y →
      Five.ContinuumLocalFieldOPEStressWard Y →
      ∀ G →
      let sameOS = H5.h3ForEveryLiteralGroup source G in
      Local.SameFamilyOPEStressWardGaussianKernel
        ContinuumFamily CurvaturePolynomial LocalOperator Position
        OPECoefficient StressTensor Hamiltonian
        (Top.Observable C)
        (Top.Position C)
        ℚ
        (H2Continuum.generatedSystem (H5.continuum source) G)

    sameHBridgeFromLiteralBC :
      (gap : Five.CutoffUniformPhysicalMassGap Y) →
      (local : Five.ContinuumLocalFieldOPEStressWard Y) →
      ∀ G →
      R77.StandardGaussianMaxwellSameHGapBridge
        (localPackageFromLiteralC gap local G)

    interactingWitnessIsLiteralClayNontriviality :
      ∀ gap local G →
      let sameOS = H5.h3ForEveryLiteralGroup source G in
      OS.InteractingContinuumWitness
        (Top.Observable C)
        (Top.Position C)
        ℚ
        (H2Continuum.generatedSystem (H5.continuum source) G) →
      Top.IsNontrivialQuantumYangMills S G
        (Top.continuumMeasure Y G)
        (Top.schwinger Y G)

    interactingWitnessIsPreservedInLiteralLimit :
      ∀ gap local G →
      let sameOS = H5.h3ForEveryLiteralGroup source G in
      OS.InteractingContinuumWitness
        (Top.Observable C)
        (Top.Position C)
        ℚ
        (H2Continuum.generatedSystem (H5.continuum source) G) →
      Top.NontrivialityPreservedInLimit S G
        (Top.continuumMeasure Y G)

open LiteralDirectSourceSameSystemNontriviality public

round77Witness :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S}
    {source : H5.LiteralCompactSimpleDirectSourceContinuation Y}
    (nontrivial :
      LiteralDirectSourceSameSystemNontriviality Y source)
    (gap : Five.CutoffUniformPhysicalMassGap Y)
    (local : Five.ContinuumLocalFieldOPEStressWard Y)
    G →
  let sameOS = H5.h3ForEveryLiteralGroup source G in
  OS.InteractingContinuumWitness
    (Top.Observable C)
    (Top.Position C)
    ℚ
    (H2Continuum.generatedSystem (H5.continuum source) G)
round77Witness nontrivial gap local G =
  R77.round77InteractingWitnessFromLocalAndGap
    (localPackageFromLiteralC nontrivial gap local G)
    (sameHBridgeFromLiteralBC nontrivial gap local G)

asInteractingContinuumNontriviality :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S}
    {source : H5.LiteralCompactSimpleDirectSourceContinuation Y} →
  LiteralDirectSourceSameSystemNontriviality Y source →
  Five.CutoffUniformPhysicalMassGap Y →
  Five.ContinuumLocalFieldOPEStressWard Y →
  Five.InteractingContinuumNontriviality Y
asInteractingContinuumNontriviality nontrivial gap local = record
  { Five.InteractingContinuumNontriviality.nontrivialQuantumYangMills =
      λ G →
        interactingWitnessIsLiteralClayNontriviality
          nontrivial gap local G
          (round77Witness nontrivial gap local G)
  ; Five.InteractingContinuumNontriviality.nontrivialityPreservedInLimit =
      λ G →
        interactingWitnessIsPreservedInLiteralLimit
          nontrivial gap local G
          (round77Witness nontrivial gap local G)
  }

directH6GaussianWardGapCompilerLevel : ProofLevel
directH6GaussianWardGapCompilerLevel =
  R77.round77NontrivialityDependencyCompilerLevel

-- H6 physical payment: a same-system semantic bridge saying the already
-- constructed literal C theorem supplies the Gaussian Ward kernel on the exact
-- H3 OS system and the already constructed B theorem supplies its SAME-H gap,
-- plus interpretation of the resulting interacting witness in literal Y.
directH6SameSystemPhysicalInstantiationLevel : ProofLevel
directH6SameSystemPhysicalInstantiationLevel = conditional
